//! Bit-vectors combined with the other theories by bit-blasting into the
//! Boolean structure, the way z3's `theory_bv` lives inside the SMT kernel:
//! every bit-vector term becomes a vector of Boolean formulas over fresh bit
//! constants (`bit_blaster`), so bit-vector atoms are plain propositional
//! formulas the DPLL(T) core decides together with arithmetic and
//! uninterpreted functions.
//!
//! The terms the other theories see — a bit-vector argument of an
//! uninterpreted function, record constructor or predicate, and a
//! bit-vector-valued application of one — are abstracted into a fresh
//! uninterpreted sort per width (the shadow functions take and return those
//! sorts). They are tied to their bits as `theory_bv` ties its e-graph
//! nodes: for every pair of them, `a = b ⇔ bits(a) = bits(b)`. Equal
//! arguments thus force equal bits of the applications (congruence), and
//! distinct classes have distinct values, so a model of the reduced goal is
//! one of the original goal.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec::Vec;

use super::Context;
use crate::ast::AstId;
use crate::ast::bv::BvOp;
use crate::smt::{Model, SmtResult, Value};
use crate::util::symbol::Symbol;

/// The widest bit-vector the reduction blasts.
const MAX_WIDTH: usize = 64;
/// The most terms per width tied pairwise to their bits.
const MAX_SHARED: usize = 48;
/// The most gates built before giving up.
const MAX_GATES: usize = 100_000;

/// The state of one reduction.
#[derive(Default)]
struct Reduce {
    /// Non-bit-vector terms translated.
    tr: BTreeMap<AstId, AstId>,
    /// Bit-vector terms blasted: their bits, least significant first.
    bits: BTreeMap<AstId, Vec<AstId>>,
    /// The blasted constants and applications, whose bits are fresh
    /// Boolean constants.
    leaves: Vec<AstId>,
    /// Bit-vector terms abstracted into the per-width sorts.
    abs: BTreeMap<AstId, AstId>,
    /// Per width: the abstracted terms `(original, abstraction)`.
    shared: BTreeMap<u32, Vec<(AstId, AstId)>>,
    /// The per-width abstract sorts.
    sorts: BTreeMap<u32, AstId>,
    /// Shadow declarations of functions with a bit-vector in their signature.
    shadow: BTreeMap<AstId, AstId>,
    /// Applications rebuilt over shadow functions: `(original, shadow)`.
    rebuilt: Vec<(AstId, AstId)>,
    gates: usize,
    /// The declarations treated as uninterpreted: the user's functions and
    /// the record constructors and selectors (whose axioms the goal carries).
    ufs: BTreeSet<AstId>,
}

impl Context {
    /// Decide a goal mixing bit-vectors with arithmetic, uninterpreted
    /// functions or records by bit-blasting its bit-vector part into the
    /// Boolean structure (see the module documentation). `None` outside the
    /// fragment (quantifiers, conversions between bit-vectors and integers,
    /// arrays over bit-vectors, opaque markers, too wide or too many shared
    /// terms) or when the goal is already being reduced.
    pub(super) fn decide_bv_bool_combined(
        &mut self,
        goal: AstId,
    ) -> Option<(SmtResult, Option<Model>)> {
        if self.in_bv_bool {
            return None;
        }
        let mut st = Reduce {
            ufs: self.funcs.values().copied().collect(),
            ..Default::default()
        };
        for (c, sels) in self.records.values() {
            st.ufs.insert(*c);
            st.ufs.extend(sels.iter().copied());
        }
        // The record axioms over the original functions (surjectivity names
        // every field of a record term, so the model reads them off bits).
        let mut ax = self.record_axioms(goal);
        let goal = if ax.is_empty() {
            goal
        } else {
            ax.push(goal);
            self.m.mk_and(&ax)
        };
        let g = self.bvb_tr(&mut st, goal)?;
        let mut parts = alloc::vec![g];
        for (_, terms) in st.shared.clone() {
            if terms.len() > MAX_SHARED {
                return None;
            }
            for i in 0..terms.len() {
                for j in i + 1..terms.len() {
                    let (a, b) = (terms[i], terms[j]);
                    let same = self.bvb_bits_eq(&mut st, a.0, b.0)?;
                    let eq = self.m.mk_eq(a.1, b.1);
                    let iff = self.m.mk_eq(eq, same);
                    parts.push(iff);
                }
            }
        }
        let reduced = if parts.len() == 1 {
            parts[0]
        } else {
            self.m.mk_and(&parts)
        };
        self.in_bv_bool = true;
        let (r, m) = self.decide(reduced);
        self.in_bv_bool = false;
        match r {
            SmtResult::Sat => {
                let mut md = m?;
                self.bvb_model(&st, &mut md);
                Some((SmtResult::Sat, Some(md)))
            }
            SmtResult::Unsat => Some((SmtResult::Unsat, None)),
            SmtResult::Unknown => None,
        }
    }

    /// Fill `md` (a model of the reduced goal) with the values of the
    /// blasted bit-vector terms and of the applications rebuilt over shadow
    /// functions.
    fn bvb_model(&mut self, st: &Reduce, md: &mut Model) {
        for &t in &st.leaves {
            let bits = &st.bits[&t];
            let mut v = puremp::Int::from(0);
            for &b in bits.iter().rev() {
                v = v.mul(&puremp::Int::from(2));
                // A bit the reduced goal lost is unconstrained: false.
                if md.assigned_bool(b) == Some(true) {
                    v = v.add(&puremp::Int::from(1));
                }
            }
            md.pin_value(t, Value::Bv(v, bits.len() as u32));
        }
        for &(orig, sh) in &st.rebuilt {
            let s = self.m.get_sort(orig);
            if self.m.is_bool_sort(s) || self.m.is_arith_sort(s) {
                let v = md.eval_value(&self.m, sh);
                md.pin_value(orig, v);
            } else if self.m.bv_sort_width(s).is_none() {
                md.pin_equal(&self.m, orig, sh);
            }
        }
    }

    /// Is `t` an application of an uninterpreted function (`st.ufs`)?
    fn bvb_is_uf(&self, st: &Reduce, t: AstId) -> bool {
        self.m.app(t).is_some_and(|a| st.ufs.contains(&a.decl))
    }

    /// The translation of the non-bit-vector term `t`: bit-vector atoms as
    /// formulas over bits, bit-vector arguments abstracted.
    fn bvb_tr(&mut self, st: &mut Reduce, t: AstId) -> Option<AstId> {
        if let Some(&r) = st.tr.get(&t) {
            return Some(r);
        }
        if self.m.is_quantifier(t) || self.m.is_var(t) || !self.m.is_app(t) {
            return None;
        }
        if self.str_symbolic.contains(&t) || self.is_opaque_fp_marker(t) {
            return None;
        }
        let args = self.m.app_args(t).to_vec();
        let bv_arg = |m: &crate::ast::manager::AstManager, a: AstId| {
            m.bv_sort_width(m.get_sort(a)).is_some()
        };
        let r = if args.is_empty() {
            t
        } else if self.m.is_eq(t) && bv_arg(&self.m, args[0]) {
            self.bvb_bits_eq(st, args[0], args[1])?
        } else if let Some(op) = self.m.bv_op(t) {
            let a = self.bvb_blast(st, args[0])?;
            let b = self.bvb_blast(st, args[1])?;
            match op {
                BvOp::Ult => self.bvb_ult(st, &a, &b),
                BvOp::Uleq => {
                    let lt = self.bvb_ult(st, &b, &a);
                    self.m.mk_not(lt)
                }
                BvOp::Slt | BvOp::Sleq => {
                    let (mut a, mut b) = (a, b);
                    let top = a.len() - 1;
                    a[top] = self.bvb_not(a[top]);
                    b[top] = self.bvb_not(b[top]);
                    if op == BvOp::Slt {
                        self.bvb_ult(st, &a, &b)
                    } else {
                        let lt = self.bvb_ult(st, &b, &a);
                        self.m.mk_not(lt)
                    }
                }
                _ => return None,
            }
        } else if args.iter().any(|&a| bv_arg(&self.m, a)) {
            // A declared function (or record constructor) over bit-vectors:
            // its shadow over the abstract sorts.
            if !self.bvb_is_uf(st, t) {
                return None;
            }
            let mut nargs = Vec::with_capacity(args.len());
            for &a in &args {
                nargs.push(if bv_arg(&self.m, a) {
                    self.bvb_abs(st, a)?
                } else {
                    self.bvb_tr(st, a)?
                });
            }
            let d = self.bvb_shadow(st, self.m.app_decl(t))?;
            let sh = self.m.mk_app(d, &nargs);
            st.rebuilt.push((t, sh));
            sh
        } else {
            let mut nargs = Vec::with_capacity(args.len());
            for &a in &args {
                nargs.push(self.bvb_tr(st, a)?);
            }
            if nargs == args {
                t
            } else {
                self.m.mk_app(self.m.app_decl(t), &nargs)
            }
        };
        st.tr.insert(t, r);
        Some(r)
    }

    /// The abstract sort of width `w`.
    fn bvb_sort(&mut self, st: &mut Reduce, w: u32) -> AstId {
        if let Some(&s) = st.sorts.get(&w) {
            return s;
        }
        let name = alloc::format!("!bv!{w}");
        let s = self.m.mk_uninterpreted_sort(Symbol::new(&name));
        st.sorts.insert(w, s);
        s
    }

    /// The shadow of the declaration `d`: bit-vector sorts in its signature
    /// replaced by the abstract sorts.
    fn bvb_shadow(&mut self, st: &mut Reduce, d: AstId) -> Option<AstId> {
        if let Some(&s) = st.shadow.get(&d) {
            return Some(s);
        }
        let fd = self.m.func_decl(d)?.clone();
        let mut dom = Vec::with_capacity(fd.domain.len());
        for &s in &fd.domain {
            dom.push(match self.m.bv_sort_width(s) {
                Some(w) => self.bvb_sort(st, w),
                None => s,
            });
        }
        let range = match self.m.bv_sort_width(fd.range) {
            Some(w) => self.bvb_sort(st, w),
            None => fd.range,
        };
        let name = alloc::format!("!bvsh!{}", self.fresh_counter);
        self.fresh_counter += 1;
        let s = self.m.mk_func_decl(Symbol::new(&name), &dom, range);
        st.shadow.insert(d, s);
        Some(s)
    }

    /// The abstraction of the bit-vector term `t` seen by the other
    /// theories, registered with its bits.
    fn bvb_abs(&mut self, st: &mut Reduce, t: AstId) -> Option<AstId> {
        if let Some(&a) = st.abs.get(&t) {
            return Some(a);
        }
        let w = self.m.bv_sort_width(self.m.get_sort(t))?;
        let a = if self.bvb_is_uf(st, t) && !self.m.app_args(t).is_empty() {
            if self.str_symbolic.contains(&t) || self.is_opaque_fp_marker(t) {
                return None;
            }
            let args = self.m.app_args(t).to_vec();
            let mut nargs = Vec::with_capacity(args.len());
            for &x in &args {
                nargs.push(if self.m.bv_sort_width(self.m.get_sort(x)).is_some() {
                    self.bvb_abs(st, x)?
                } else {
                    self.bvb_tr(st, x)?
                });
            }
            let d = self.bvb_shadow(st, self.m.app_decl(t))?;
            self.m.mk_app(d, &nargs)
        } else {
            let s = self.bvb_sort(st, w);
            self.fresh_const(s)
        };
        st.abs.insert(t, a);
        st.shared.entry(w).or_default().push((t, a));
        // Its bits (an application's are fresh).
        self.bvb_blast(st, t)?;
        Some(a)
    }

    /// The bits of the bit-vector term `t`.
    fn bvb_blast(&mut self, st: &mut Reduce, t: AstId) -> Option<Vec<AstId>> {
        if let Some(b) = st.bits.get(&t) {
            return Some(b.clone());
        }
        let w = self.m.bv_sort_width(self.m.get_sort(t))? as usize;
        if w > MAX_WIDTH || st.gates > MAX_GATES {
            return None;
        }
        let args = if self.m.is_app(t) {
            self.m.app_args(t).to_vec()
        } else {
            return None;
        };
        let bits: Vec<AstId> = if let Some(v) = self.m.bv_numeral_value(t) {
            (0..w).map(|i| self.mk_bool(v.bit(i as u64))).collect()
        } else if let Some(op) = self.m.bv_op(t) {
            let mut bs = Vec::with_capacity(args.len());
            for &a in &args {
                bs.push(self.bvb_blast(st, a)?);
            }
            let fls = self.m.mk_false();
            match op {
                BvOp::BNot => bs[0].iter().map(|&b| self.bvb_not(b)).collect(),
                BvOp::BAnd | BvOp::BOr | BvOp::BXor => {
                    let mut acc = bs[0].clone();
                    for b in &bs[1..] {
                        acc = (0..w)
                            .map(|i| match op {
                                BvOp::BAnd => self.bvb_and(st, acc[i], b[i]),
                                BvOp::BOr => self.bvb_or(st, acc[i], b[i]),
                                _ => self.bvb_xor(st, acc[i], b[i]),
                            })
                            .collect();
                    }
                    acc
                }
                BvOp::Add => {
                    let mut acc = bs[0].clone();
                    for b in &bs[1..] {
                        acc = self.bvb_add(st, &acc, b, fls);
                    }
                    acc
                }
                BvOp::Sub => {
                    let nb: Vec<AstId> = bs[1].iter().map(|&b| self.bvb_not(b)).collect();
                    let tru = self.m.mk_true();
                    self.bvb_add(st, &bs[0], &nb, tru)
                }
                BvOp::Neg => {
                    let na: Vec<AstId> = bs[0].iter().map(|&b| self.bvb_not(b)).collect();
                    let zero = alloc::vec![fls; w];
                    let tru = self.m.mk_true();
                    self.bvb_add(st, &na, &zero, tru)
                }
                BvOp::Mul => {
                    let mut acc = bs[0].clone();
                    for b in &bs[1..] {
                        acc = self.bvb_mul(st, &acc, b);
                    }
                    acc
                }
                BvOp::Udiv => self.bvb_udivrem(st, &bs[0], &bs[1]).0,
                BvOp::Urem => self.bvb_udivrem(st, &bs[0], &bs[1]).1,
                BvOp::Shl => self.bvb_shift(st, &bs[0], &bs[1], true, fls),
                BvOp::Lshr => self.bvb_shift(st, &bs[0], &bs[1], false, fls),
                BvOp::Ashr => {
                    let sign = *bs[0].last()?;
                    self.bvb_shift(st, &bs[0], &bs[1], false, sign)
                }
                BvOp::Concat => {
                    // The first argument is the most significant.
                    let mut out = Vec::with_capacity(w);
                    for b in bs.iter().rev() {
                        out.extend_from_slice(b);
                    }
                    out
                }
                BvOp::Extract => {
                    let (hi, lo) = self.m.bv_extract_params(t)?;
                    bs[0][lo as usize..=hi as usize].to_vec()
                }
                BvOp::ZeroExt => {
                    let mut a = bs[0].clone();
                    a.resize(w, fls);
                    a
                }
                BvOp::SignExt => {
                    let mut a = bs[0].clone();
                    let sign = *a.last()?;
                    a.resize(w, sign);
                    a
                }
                _ => return None,
            }
        } else if self.m.is_ite(t) {
            let c = self.bvb_tr(st, args[0])?;
            let a = self.bvb_blast(st, args[1])?;
            let b = self.bvb_blast(st, args[2])?;
            self.bvb_mux(st, c, &a, &b)
        } else if self.m.is_uninterp_const(t) || (self.bvb_is_uf(st, t) && !args.is_empty()) {
            if self.str_symbolic.contains(&t) || self.is_opaque_fp_marker(t) {
                return None;
            }
            let b = self.m.mk_bool_sort();
            let bits: Vec<AstId> = (0..w).map(|_| self.fresh_const(b)).collect();
            st.bits.insert(t, bits.clone());
            st.leaves.push(t);
            if !args.is_empty() {
                // An application: the other theories give it congruence.
                self.bvb_abs(st, t)?;
            }
            return Some(bits);
        } else {
            return None;
        };
        if bits.len() != w {
            return None;
        }
        st.bits.insert(t, bits.clone());
        Some(bits)
    }

    /// `bits(a) = bits(b)`.
    fn bvb_bits_eq(&mut self, st: &mut Reduce, a: AstId, b: AstId) -> Option<AstId> {
        let x = self.bvb_blast(st, a)?;
        let y = self.bvb_blast(st, b)?;
        let mut eqs = Vec::with_capacity(x.len());
        for i in 0..x.len() {
            let d = self.bvb_xor(st, x[i], y[i]);
            eqs.push(self.bvb_not(d));
        }
        Some(self.bvb_and_all(st, &eqs))
    }

    fn bvb_not(&mut self, a: AstId) -> AstId {
        if self.m.is_true(a) {
            self.m.mk_false()
        } else if self.m.is_false(a) {
            self.m.mk_true()
        } else if self.m.is_not(a) {
            self.m.app_args(a)[0]
        } else {
            self.m.mk_not(a)
        }
    }

    fn bvb_and(&mut self, st: &mut Reduce, a: AstId, b: AstId) -> AstId {
        if self.m.is_false(a) || self.m.is_false(b) {
            return self.m.mk_false();
        }
        if self.m.is_true(a) || a == b {
            return b;
        }
        if self.m.is_true(b) {
            return a;
        }
        st.gates += 1;
        self.m.mk_and(&[a, b])
    }

    fn bvb_or(&mut self, st: &mut Reduce, a: AstId, b: AstId) -> AstId {
        if self.m.is_true(a) || self.m.is_true(b) {
            return self.m.mk_true();
        }
        if self.m.is_false(a) || a == b {
            return b;
        }
        if self.m.is_false(b) {
            return a;
        }
        st.gates += 1;
        self.m.mk_or(&[a, b])
    }

    fn bvb_xor(&mut self, st: &mut Reduce, a: AstId, b: AstId) -> AstId {
        if self.m.is_false(a) {
            return b;
        }
        if self.m.is_false(b) {
            return a;
        }
        if self.m.is_true(a) {
            return self.bvb_not(b);
        }
        if self.m.is_true(b) {
            return self.bvb_not(a);
        }
        if a == b {
            return self.m.mk_false();
        }
        st.gates += 1;
        self.m.mk_xor(a, b)
    }

    fn bvb_and_all(&mut self, st: &mut Reduce, xs: &[AstId]) -> AstId {
        let mut acc = self.m.mk_true();
        for &x in xs {
            acc = self.bvb_and(st, acc, x);
        }
        acc
    }

    fn bvb_or_all(&mut self, st: &mut Reduce, xs: &[AstId]) -> AstId {
        let mut acc = self.m.mk_false();
        for &x in xs {
            acc = self.bvb_or(st, acc, x);
        }
        acc
    }

    /// `c ? a : b` bitwise.
    fn bvb_mux(&mut self, st: &mut Reduce, c: AstId, a: &[AstId], b: &[AstId]) -> Vec<AstId> {
        if self.m.is_true(c) {
            return a.to_vec();
        }
        if self.m.is_false(c) {
            return b.to_vec();
        }
        let nc = self.bvb_not(c);
        (0..a.len())
            .map(|i| {
                if a[i] == b[i] {
                    return a[i];
                }
                let x = self.bvb_and(st, c, a[i]);
                let y = self.bvb_and(st, nc, b[i]);
                self.bvb_or(st, x, y)
            })
            .collect()
    }

    /// Sum and carry of a full adder.
    fn bvb_full_add(&mut self, st: &mut Reduce, a: AstId, b: AstId, c: AstId) -> (AstId, AstId) {
        let axb = self.bvb_xor(st, a, b);
        let sum = self.bvb_xor(st, axb, c);
        let ab = self.bvb_and(st, a, b);
        let cx = self.bvb_and(st, c, axb);
        (sum, self.bvb_or(st, ab, cx))
    }

    /// `a + b + cin` (mod 2^n), ripple-carry.
    fn bvb_add(&mut self, st: &mut Reduce, a: &[AstId], b: &[AstId], cin: AstId) -> Vec<AstId> {
        let mut c = cin;
        let mut out = Vec::with_capacity(a.len());
        for i in 0..a.len() {
            let (s, c2) = self.bvb_full_add(st, a[i], b[i], c);
            out.push(s);
            c = c2;
        }
        out
    }

    /// `a · b` (mod 2^n), shift-and-add.
    fn bvb_mul(&mut self, st: &mut Reduce, a: &[AstId], b: &[AstId]) -> Vec<AstId> {
        let n = a.len();
        let fls = self.m.mk_false();
        let mut acc = alloc::vec![fls; n];
        for i in 0..n {
            if self.m.is_false(b[i]) {
                continue;
            }
            let partial: Vec<AstId> = (0..n)
                .map(|j| {
                    if j >= i {
                        self.bvb_and(st, a[j - i], b[i])
                    } else {
                        fls
                    }
                })
                .collect();
            acc = self.bvb_add(st, &acc, &partial, fls);
        }
        acc
    }

    /// `a <u b`: no carry out of `a + ¬b + 1`.
    fn bvb_ult(&mut self, st: &mut Reduce, a: &[AstId], b: &[AstId]) -> AstId {
        let mut c = self.m.mk_true();
        for i in 0..a.len() {
            let nb = self.bvb_not(b[i]);
            c = self.bvb_full_add(st, a[i], nb, c).1;
        }
        self.bvb_not(c)
    }

    /// A barrel shifter (`fill` shifted in).
    fn bvb_shift(
        &mut self,
        st: &mut Reduce,
        a: &[AstId],
        b: &[AstId],
        left: bool,
        fill: AstId,
    ) -> Vec<AstId> {
        let n = a.len();
        let mut acc = a.to_vec();
        for (i, &sel) in b.iter().enumerate() {
            let sh = 1usize.checked_shl(i as u32).unwrap_or(usize::MAX);
            let shifted: Vec<AstId> = if sh >= n {
                alloc::vec![fill; n]
            } else if left {
                (0..n)
                    .map(|j| if j >= sh { acc[j - sh] } else { fill })
                    .collect()
            } else {
                (0..n)
                    .map(|j| if j + sh < n { acc[j + sh] } else { fill })
                    .collect()
            };
            acc = self.bvb_mux(st, sel, &shifted, &acc);
        }
        acc
    }

    /// Unsigned quotient and remainder by restoring division (SMT-LIB
    /// division by zero: all ones, and the dividend).
    fn bvb_udivrem(
        &mut self,
        st: &mut Reduce,
        a: &[AstId],
        b: &[AstId],
    ) -> (Vec<AstId>, Vec<AstId>) {
        let n = a.len();
        let fls = self.m.mk_false();
        let tru = self.m.mk_true();
        let mut rem = alloc::vec![fls; n];
        let mut quot = alloc::vec![fls; n];
        for i in (0..n).rev() {
            let mut shifted = Vec::with_capacity(n + 1);
            shifted.push(a[i]);
            shifted.extend_from_slice(&rem);
            let mut bx = b.to_vec();
            bx.push(fls);
            let mut c = tru;
            let mut diff = Vec::with_capacity(n + 1);
            for j in 0..=n {
                let nb = self.bvb_not(bx[j]);
                let (s, c2) = self.bvb_full_add(st, shifted[j], nb, c);
                diff.push(s);
                c = c2;
            }
            let r = self.bvb_mux(st, c, &diff, &shifted);
            rem = r[..n].to_vec();
            quot[i] = c;
        }
        let nz = self.bvb_or_all(st, b);
        let z = self.bvb_not(nz);
        let ones = alloc::vec![tru; n];
        let q = self.bvb_mux(st, z, &ones, &quot);
        let r = self.bvb_mux(st, z, a, &rem);
        (q, r)
    }
}
