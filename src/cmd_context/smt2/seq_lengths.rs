//! Sequences of unbounded length, decided through their length abstraction
//! (z3's `theory_seq` length reasoning and `branch_variable` by length).
//!
//! The length abstraction replaces every sequence term by the integer
//! variable of its length, with z3's length axioms: a concatenation's length
//! is the sum of its parts', a unit has length 1, an `extract` the clamped
//! window `min(n, len s − i)` (0 out of range), an `ite` the length of the
//! branch it takes. An equation between sequences becomes a fresh Boolean
//! that implies equal lengths, `prefixof`/`suffixof`/`contains` one that
//! implies the length order, and any other term over sequences (`nth`, an
//! unknown operation) a fresh variable. The abstraction is implied by the
//! goal, so its refutation refutes the goal.
//!
//! Otherwise a model of the abstraction proposes a length for each sequence
//! variable; at fixed lengths the goal is decided exactly by its elements
//! ([`Context::seq_bounded_search`]): a confirmed model is `sat`, an element
//! refutation excludes that length vector and the abstraction proposes the
//! next. When the abstraction runs out of length vectors, every one having
//! been refuted, the goal is `unsat`.

use alloc::boxed::Box;
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec::Vec;

use super::{Context, Model, SmtResult, Value};
use crate::ast::AstId;

/// The length vectors the abstraction may propose before giving up.
const MAX_ROUNDS: usize = 24;

/// The caps on a variable's length tried in turn: the element problem grows
/// with the lengths, so short vectors are proposed first.
const CAPS: [i64; 2] = [4, 8];

/// The length abstraction under construction.
struct Abs {
    /// Each sequence term's length variable.
    len: BTreeMap<AstId, AstId>,
    /// Each abstracted Boolean or arithmetic term.
    memo: BTreeMap<AstId, AstId>,
    /// The length axioms.
    axioms: Vec<AstId>,
}

/// What the length-guided search concluded about a goal.
enum Cegar {
    /// A confirmed model, at this length vector.
    Sat(Vec<i64>, Box<Option<Model>>),
    /// Every length vector refuted.
    Unsat,
    /// Undecided.
    Unknown,
}

impl Context {
    /// Decide ground goals over sequence variables of unbounded length by
    /// their length abstraction (see the module documentation), one group of
    /// assertions sharing no constant with the others at a time: one group
    /// refuted refutes the goal, and the groups' length vectors together are
    /// tried on the whole. `None` outside that fragment or when undecided.
    pub(super) fn check_sat_seq_lengths(&mut self) -> Option<(SmtResult, Option<Model>)> {
        self.seq_bounded_pins_found.clear();
        if self.seq_sorts.is_empty() || !self.universals.is_empty() {
            return None;
        }
        let roots = self.assertions.clone();
        let mut vars: Vec<AstId> = Vec::new();
        for t in self.m.postorder_many(&roots) {
            if self.m.is_quantifier(t) {
                return None;
            }
            let s = self.m.get_sort(t);
            if self.seq_elem_sort(s).is_some() && self.is_str_seq_var(t) && !vars.contains(&t) {
                if !self.is_user_constant_or_bits(t) {
                    return None;
                }
                vars.push(t);
            }
        }
        if vars.is_empty() {
            return None;
        }
        // Groups of assertions linked by shared constants.
        let mut groups: Vec<(BTreeSet<AstId>, Vec<AstId>)> = Vec::new();
        for &a in &roots {
            let consts: BTreeSet<AstId> = self
                .m
                .postorder(a)
                .into_iter()
                .filter(|&t| self.m.is_uninterp_const(t))
                .collect();
            let mut merged = (consts, alloc::vec![a]);
            let mut rest = Vec::new();
            for g in groups {
                if g.0.is_disjoint(&merged.0) {
                    rest.push(g);
                } else {
                    merged.0.extend(g.0);
                    merged.1.extend(g.1);
                }
            }
            rest.push(merged);
            groups = rest;
        }
        if groups.len() == 1 {
            return match self.seq_lengths_cegar(&roots, &vars) {
                Cegar::Sat(_, m) => Some((SmtResult::Sat, *m)),
                Cegar::Unsat => Some((SmtResult::Unsat, None)),
                Cegar::Unknown => None,
            };
        }
        let saved = self.assertions.clone();
        let mut lengths: BTreeMap<AstId, i64> = BTreeMap::new();
        let mut undecided = false;
        for (consts, group) in &groups {
            let gvars: Vec<AstId> = vars
                .iter()
                .copied()
                .filter(|v| consts.contains(v))
                .collect();
            if gvars.is_empty() {
                continue;
            }
            self.assertions = group.clone();
            let r = self.seq_lengths_cegar(group, &gvars);
            self.assertions = saved.clone();
            match r {
                Cegar::Unsat => return Some((SmtResult::Unsat, None)),
                Cegar::Sat(vector, _) => lengths.extend(gvars.iter().copied().zip(vector)),
                Cegar::Unknown => undecided = true,
            }
        }
        if undecided {
            return None;
        }
        let ranges: Vec<(AstId, i64, i64)> = vars
            .iter()
            .map(|&v| lengths.get(&v).map(|&n| (v, n, n)))
            .collect::<Option<_>>()?;
        match self.seq_bounded_search(&roots, &[], &vars, &ranges) {
            Some((SmtResult::Sat, m)) => Some((SmtResult::Sat, m)),
            _ => None,
        }
    }

    /// The length-guided search over the assertions `roots` (also
    /// `self.assertions`) and their sequence variables `vars`.
    fn seq_lengths_cegar(&mut self, roots: &[AstId], vars: &[AstId]) -> Cegar {
        let mut abs = Abs {
            len: BTreeMap::new(),
            memo: BTreeMap::new(),
            axioms: Vec::new(),
        };
        let mut parts = Vec::with_capacity(roots.len());
        for &a in roots {
            match self.seq_abs_term(a, &mut abs) {
                Some(t) => parts.push(t),
                None => return Cegar::Unknown,
            }
        }
        let mut lens = Vec::with_capacity(vars.len());
        for &v in vars {
            match self.seq_abs_len(v, &mut abs) {
                Some(l) => lens.push(l),
                None => return Cegar::Unknown,
            }
        }
        parts.extend(abs.axioms.iter().copied());
        let base = self.m.mk_and(&parts);
        let mut blocks: Vec<AstId> = Vec::new();
        // Some proposed vector was not decided: no refutation then.
        let mut incomplete = false;
        let mut rounds = 0;
        for &cap in &CAPS {
            loop {
                if rounds == MAX_ROUNDS {
                    return Cegar::Unknown;
                }
                rounds += 1;
                let k = self.m.mk_int(cap);
                let mut q = alloc::vec![base];
                q.extend(blocks.iter().copied());
                q.extend(lens.iter().map(|&l| self.m.mk_le(l, k)));
                let g = self.m.mk_and(&q);
                let (r, model) = self.decide(g);
                let mut md = match (r, model) {
                    (SmtResult::Unsat, _) => break,
                    (SmtResult::Sat, Some(md)) => md,
                    _ => return Cegar::Unknown,
                };
                let mut vector = Vec::with_capacity(lens.len());
                for &l in &lens {
                    match md.eval(&self.m, l) {
                        Value::Num(n, _) => match n.to_integer().and_then(|i| i.to_i64()) {
                            Some(n) => vector.push(n),
                            None => return Cegar::Unknown,
                        },
                        _ => return Cegar::Unknown,
                    }
                }
                let ranges: Vec<(AstId, i64, i64)> =
                    vars.iter().zip(&vector).map(|(&v, &n)| (v, n, n)).collect();
                match self.seq_bounded_search(roots, &[], vars, &ranges) {
                    Some((SmtResult::Sat, m)) => return Cegar::Sat(vector, Box::new(m)),
                    Some((SmtResult::Unsat, _)) => {}
                    _ => incomplete = true,
                }
                // Exclude this length vector.
                let differs: Vec<AstId> = lens
                    .iter()
                    .zip(&vector)
                    .map(|(&l, &n)| {
                        let nv = self.m.mk_int(n);
                        let eq = self.m.mk_eq(l, nv);
                        self.m.mk_not(eq)
                    })
                    .collect();
                blocks.push(self.mk_disjunction(&differs));
            }
        }
        if incomplete {
            return Cegar::Unknown;
        }
        // Every vector within the caps is refuted: `unsat` when no longer one
        // satisfies the abstraction either.
        let k = self.m.mk_int(CAPS[CAPS.len() - 1]);
        let longer: Vec<AstId> = lens.iter().map(|&l| self.m.mk_gt(l, k)).collect();
        let mut q = alloc::vec![base];
        q.extend(blocks.iter().copied());
        q.push(self.mk_disjunction(&longer));
        let g = self.m.mk_and(&q);
        if self.decide(g).0 == SmtResult::Unsat {
            Cegar::Unsat
        } else {
            Cegar::Unknown
        }
    }

    /// Refute a goal over strings by the same length abstraction (string
    /// lengths: concatenation sums, clamped `substr`/`at` windows, the
    /// lengths a constant regex's words can have, equal leading and trailing
    /// characters of equations). `None` unless refuted.
    pub(super) fn check_sat_str_lengths_refute(&mut self) -> Option<(SmtResult, Option<Model>)> {
        let string_sort = self.string_sort?;
        if !self.universals.is_empty() {
            return None;
        }
        let roots = self.assertions.clone();
        let mut any = false;
        for t in self.m.postorder_many(&roots) {
            if self.m.is_quantifier(t) {
                return None;
            }
            any |= self.m.get_sort(t) == string_sort;
        }
        if !any {
            return None;
        }
        let mut abs = Abs {
            len: BTreeMap::new(),
            memo: BTreeMap::new(),
            axioms: Vec::new(),
        };
        let mut parts = Vec::with_capacity(roots.len() + 1);
        for &a in &roots {
            parts.push(self.seq_abs_term(a, &mut abs)?);
        }
        parts.extend(abs.axioms.iter().copied());
        parts.push(self.m.mk_true());
        let g = self.m.mk_and(&parts);
        (self.decide(g).0 == SmtResult::Unsat).then_some((SmtResult::Unsat, None))
    }

    /// Is `s` a sequence or the string sort?
    fn seq_like_sort(&self, s: AstId) -> bool {
        self.seq_elem_sort(s).is_some() || self.string_sort == Some(s)
    }

    /// The known length of a concrete sequence or string literal.
    fn seq_like_known_len(&self, t: AstId) -> Option<usize> {
        self.seq_of
            .get(&t)
            .map(Vec::len)
            .or_else(|| self.str_value(t).map(|v| v.len()))
    }

    /// The sequence operation `t` applies, string operations under their
    /// sequence names (`str.substr` is `seq.extract`).
    fn seq_like_op(&self, t: AstId) -> Option<&'static str> {
        let d = self.m.app(t)?.decl;
        if let Some(op) = self.seqop_ops.get(&d) {
            return Some(match op.as_str() {
                "seq.++" => "seq.++",
                "seq.extract" => "seq.extract",
                "seq.at" => "seq.at",
                "seq.prefixof" => "seq.prefixof",
                "seq.suffixof" => "seq.suffixof",
                "seq.contains" => "seq.contains",
                _ => "",
            });
        }
        Some(match self.str_op_decls.get(&d)?.as_str() {
            "str.++" => "seq.++",
            "str.substr" => "seq.extract",
            "str.at" => "seq.at",
            "str.prefixof" => "seq.prefixof",
            "str.suffixof" => "seq.suffixof",
            "str.contains" => "seq.contains",
            "str.in_re" | "str.in.re" => "str.in_re",
            _ => "",
        })
    }

    /// The length variable of the sequence term `t`, with its length axioms
    /// (once per term).
    fn seq_abs_len(&mut self, t: AstId, abs: &mut Abs) -> Option<AstId> {
        if let Some(&l) = abs.len.get(&t) {
            return Some(l);
        }
        let int_sort = self.m.mk_int_sort();
        let l = self.fresh_const(int_sort);
        abs.len.insert(t, l);
        let zero = self.m.mk_int(0);
        abs.axioms.push(self.m.mk_ge(l, zero));
        if let Some(n) = self.seq_like_known_len(t) {
            let n = self.m.mk_int(n as i64);
            abs.axioms.push(self.m.mk_eq(l, n));
            return Some(l);
        }
        if self.m.is_ite(t) {
            let a = self.m.app_args(t).to_vec();
            let c = self.seq_abs_term(a[0], abs)?;
            let (lt, le) = (self.seq_abs_len(a[1], abs)?, self.seq_abs_len(a[2], abs)?);
            let v = self.m.mk_ite(c, lt, le);
            abs.axioms.push(self.m.mk_eq(l, v));
            return Some(l);
        }
        let op = self.seq_like_op(t);
        let args = self.m.app_args(t).to_vec();
        match op {
            Some("seq.++") => {
                let mut sum = Vec::with_capacity(args.len());
                for &a in &args {
                    sum.push(self.seq_abs_len(a, abs)?);
                }
                let s = self.m.mk_add(&sum);
                abs.axioms.push(self.m.mk_eq(l, s));
            }
            Some(op @ ("seq.extract" | "seq.at")) => {
                // z3's extract axioms: the window `[i, i + n)` clamped to `s`.
                let ls = self.seq_abs_len(args[0], abs)?;
                let i = self.seq_abs_term(args[1], abs)?;
                let n = if op == "seq.at" {
                    self.m.mk_int(1)
                } else {
                    self.seq_abs_term(args[2], abs)?
                };
                let i_neg = self.m.mk_lt(i, zero);
                let n_nonpos = self.m.mk_le(n, zero);
                let oob = self.m.mk_ge(i, ls);
                let out = self.m.mk_or(&[i_neg, n_nonpos, oob]);
                let len_zero = self.m.mk_eq(l, zero);
                abs.axioms.push(self.m.mk_implies(out, len_zero));
                let i_ok = self.m.mk_ge(i, zero);
                let n_pos = self.m.mk_gt(n, zero);
                let inb = self.m.mk_lt(i, ls);
                let avail = self.m.mk_sub(&[ls, i]);
                let enough = self.m.mk_ge(avail, n);
                let c1 = self.m.mk_and(&[i_ok, n_pos, inb, enough]);
                let len_n = self.m.mk_eq(l, n);
                abs.axioms.push(self.m.mk_implies(c1, len_n));
                let short = self.m.mk_lt(avail, n);
                let c2 = self.m.mk_and(&[i_ok, n_pos, inb, short]);
                let len_avail = self.m.mk_eq(l, avail);
                abs.axioms.push(self.m.mk_implies(c2, len_avail));
            }
            // A variable or another operation: any length.
            _ => {}
        }
        Some(l)
    }

    /// The factors of the sequence term `t`: the elements of its known
    /// units (`Some`) and the other factors (`None`), flattening `seq.++`.
    fn seq_abs_factors(&mut self, t: AstId, out: &mut Vec<Option<AstId>>) {
        if let Some(elems) = self.seq_of.get(&t) {
            out.extend(elems.iter().map(|&e| Some(e)));
            return;
        }
        // A string literal's characters, as their code points.
        if let Some(cps) = self.str_value(t) {
            for c in cps {
                out.push(Some(self.m.mk_int(i64::from(c))));
            }
            return;
        }
        if let Some(app) = self.m.app(t).cloned()
            && self.seq_like_op(t) == Some("seq.++")
        {
            for &a in &app.args.clone() {
                self.seq_abs_factors(a, out);
            }
            return;
        }
        out.push(None);
    }

    /// Under `p`, `a` and `b` agree element by element on their leading
    /// (`heads`) and trailing (`tails`) known units, as far as both sides
    /// have them (z3's `solve_eqs` stripping common unit prefixes and
    /// suffixes): `[1]·x = [2]·y` is refuted by its heads.
    fn seq_abs_aligned(
        &mut self,
        p: AstId,
        a: AstId,
        b: AstId,
        heads: bool,
        tails: bool,
        abs: &mut Abs,
    ) -> Option<()> {
        let (mut fa, mut fb) = (Vec::new(), Vec::new());
        self.seq_abs_factors(a, &mut fa);
        self.seq_abs_factors(b, &mut fb);
        let mut pairs: Vec<(AstId, AstId)> = Vec::new();
        if heads {
            for (x, y) in fa.iter().zip(&fb) {
                match (x, y) {
                    (Some(x), Some(y)) => pairs.push((*x, *y)),
                    _ => break,
                }
            }
        }
        if tails {
            for (x, y) in fa.iter().rev().zip(fb.iter().rev()) {
                match (x, y) {
                    (Some(x), Some(y)) => pairs.push((*x, *y)),
                    _ => break,
                }
            }
        }
        for (x, y) in pairs {
            let (x, y) = (self.seq_abs_term(x, abs)?, self.seq_abs_term(y, abs)?);
            let eq = self.m.mk_eq(x, y);
            abs.axioms.push(self.m.mk_implies(p, eq));
        }
        Some(())
    }

    /// `t` (a Boolean or arithmetic term) with every sequence term replaced
    /// by its length abstraction. `None` for a term of another sort over
    /// sequences.
    fn seq_abs_term(&mut self, t: AstId, abs: &mut Abs) -> Option<AstId> {
        if let Some(&r) = abs.memo.get(&t) {
            return Some(r);
        }
        let sort = self.m.get_sort(t);
        let over_seq = |me: &Self, u: AstId| {
            me.m.app_args(u)
                .iter()
                .any(|&a| me.seq_like_sort(me.m.get_sort(a)))
        };
        let r = if !self.m.is_app(t) || self.m.app_args(t).is_empty() {
            t
        } else if self.m.is_bool_sort(sort) && over_seq(self, t) {
            // An atom over sequences: a fresh Boolean implying the length
            // relation the atom entails.
            let p = self.fresh_const(sort);
            let args = self.m.app_args(t).to_vec();
            let op = self.seq_like_op(t);
            let rel = if self.m.is_eq(t) && args.len() == 2 {
                // An equation with an `ite` side holds as the branch taken.
                if let Some(k) = (0..2).find(|&k| self.m.is_ite(args[k])) {
                    let ite = self.m.app_args(args[k]).to_vec();
                    let other = args[1 - k];
                    let c = self.seq_abs_term(ite[0], abs)?;
                    let et = self.m.mk_eq(other, ite[1]);
                    let ee = self.m.mk_eq(other, ite[2]);
                    let (pt, pe) = (self.seq_abs_term(et, abs)?, self.seq_abs_term(ee, abs)?);
                    let branch = self.m.mk_ite(c, pt, pe);
                    abs.axioms.push(self.m.mk_implies(p, branch));
                }
                self.seq_abs_aligned(p, args[0], args[1], true, true, abs)?;
                let (a, b) = (
                    self.seq_abs_len(args[0], abs)?,
                    self.seq_abs_len(args[1], abs)?,
                );
                Some(self.m.mk_eq(a, b))
            } else {
                match op {
                    Some(op @ ("seq.prefixof" | "seq.suffixof")) if args.len() == 2 => {
                        let prefix = op == "seq.prefixof";
                        self.seq_abs_aligned(p, args[0], args[1], prefix, !prefix, abs)?;
                        let (a, b) = (
                            self.seq_abs_len(args[0], abs)?,
                            self.seq_abs_len(args[1], abs)?,
                        );
                        Some(self.m.mk_le(a, b))
                    }
                    Some("seq.contains") if args.len() == 2 => {
                        let (a, b) = (
                            self.seq_abs_len(args[0], abs)?,
                            self.seq_abs_len(args[1], abs)?,
                        );
                        Some(self.m.mk_le(b, a))
                    }
                    // A membership in a constant regex: the word's length is
                    // one its words can have (exact up to a bound).
                    Some("str.in_re") if args.len() == 2 => {
                        const MAX: usize = 32;
                        let lens = self.regex_of.get(&args[1]).and_then(|r| r.lengths(MAX));
                        match lens {
                            Some(v) => {
                                let ls = self.seq_abs_len(args[0], abs)?;
                                let mut ok: Vec<AstId> = (0..=MAX)
                                    .filter(|&n| v[n])
                                    .map(|n| {
                                        let nv = self.m.mk_int(n as i64);
                                        self.m.mk_eq(ls, nv)
                                    })
                                    .collect();
                                let top = self.m.mk_int(MAX as i64);
                                ok.push(self.m.mk_gt(ls, top));
                                Some(self.mk_disjunction(&ok))
                            }
                            None => None,
                        }
                    }
                    _ => None,
                }
            };
            if let Some(rel) = rel {
                abs.axioms.push(self.m.mk_implies(p, rel));
            }
            p
        } else if self.m.is_arith_sort(sort)
            && (self.seq_len_decls.contains(&self.m.app_decl(t))
                || self.str_len_decl == Some(self.m.app_decl(t)))
            && self.m.app_args(t).len() == 1
        {
            let s = self.m.app_args(t)[0];
            self.seq_abs_len(s, abs)?
        } else if over_seq(self, t) {
            // Another term over sequences (`nth`, `indexof`): free.
            if self.seq_like_sort(sort) {
                return None;
            }
            self.fresh_const(sort)
        } else {
            let app = self.m.app(t)?.clone();
            let mut args = Vec::with_capacity(app.args.len());
            for &a in &app.args {
                args.push(self.seq_abs_term(a, abs)?);
            }
            if args == app.args {
                t
            } else {
                self.m.mk_app(app.decl, &args)
            }
        };
        abs.memo.insert(t, r);
        Some(r)
    }
}
