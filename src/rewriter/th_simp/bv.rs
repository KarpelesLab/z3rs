//! `bv_rewriter` (`z3/src/ast/rewriter/bv_rewriter.cpp`, MIT) for the
//! theory rewriter port, with z3's defaults: `hi_div0`, `elim_sign_ext`,
//! `bit2bool`, `bv_sort_ac`, `bv_le2extract` on; `mul2concat`,
//! `blast_eq_value`, `split_concat_eq`, `bv_extract_prop`, `bv_le_extra`,
//! `bv_not_simpl`, `bv_ite2id` off.

use alloc::vec;
use alloc::vec::Vec;

use puremp::Int;

use super::{BvOp, Op, Simp, Sort, St, T};

/// `2^k`.
fn pow2(k: u32) -> Int {
    Int::from(2).pow(u64::from(k))
}

/// The value `v` (in `[0, 2^w)`) read as a signed `w`-bit number.
fn to_signed(v: &Int, w: u32) -> Int {
    if w > 0 && v >= &pow2(w - 1) {
        v - &pow2(w)
    } else {
        v.clone()
    }
}

/// `v mod 2^w`, in `[0, 2^w)`.
fn norm(v: &Int, w: u32) -> Int {
    v.rem_euclid(&pow2(w))
}

impl Simp {
    /// A bit-vector numeral's value and width.
    fn bv_num(&self, t: T) -> Option<(Int, u32)> {
        match (&self.nodes[t].op, &self.nodes[t].sort) {
            (Op::BvNum(v), Sort::Bv(w)) => Some((v.clone(), *w)),
            _ => None,
        }
    }

    fn mk_bv(&mut self, v: &Int, w: u32) -> T {
        let v = norm(v, w);
        self.mk_bv_num(&v, w)
    }

    fn bv_zero(&mut self, w: u32) -> T {
        self.mk_bv(&Int::from(0), w)
    }

    fn bv_ones(&mut self, w: u32) -> T {
        let v = &pow2(w) - &Int::from(1);
        self.mk_bv(&v, w)
    }

    fn bvop(&mut self, op: BvOp, args: Vec<T>) -> T {
        self.mk(Op::Bv(op), args)
    }

    fn is_bvop(&self, t: T, op: BvOp) -> bool {
        self.nodes[t].op == Op::Bv(op)
    }

    /// `mk_extract_proc`: `((_ extract h l) x)`, folding nested extracts and
    /// the full-width extract.
    pub(super) fn mk_extract(&mut self, high: u32, low: u32, arg: T) -> T {
        let (mut high, mut low, mut arg) = (high, low, arg);
        while let Op::Extract(_, l) = self.nodes[arg].op {
            low += l;
            high += l;
            arg = self.arg(arg, 0);
        }
        if low == 0 && high + 1 == self.bv_width(arg) {
            return arg;
        }
        self.mk(Op::Extract(high, low), vec![arg])
    }

    fn mk_concat(&mut self, args: Vec<T>) -> T {
        self.bvop(BvOp::Concat, args)
    }

    /// `bv_rewriter::mk_app_core` for the bit-vector operators.
    pub(super) fn bv_app(&mut self, op: &Op, args: &[T]) -> Option<St> {
        let s = self.nodes[args[0]].sort.clone();
        match op {
            Op::Bv(b) => match b {
                BvOp::Ule => self.leq_core(false, args[0], args[1]),
                BvOp::Uge => Some(self.ge_via_le(false, args[1], args[0])),
                BvOp::Ult => {
                    let le = self.bvop(BvOp::Ule, vec![args[1], args[0]]);
                    Some(St::Rw(self.mk_not(le), 2))
                }
                BvOp::Ugt => {
                    let le = self.bvop(BvOp::Ule, vec![args[0], args[1]]);
                    Some(St::Rw(self.mk_not(le), 2))
                }
                BvOp::Sle => self.leq_core(true, args[0], args[1]),
                BvOp::Sge => Some(self.ge_via_le(true, args[1], args[0])),
                BvOp::Slt => {
                    let le = self.bvop(BvOp::Sle, vec![args[1], args[0]]);
                    Some(St::Rw(self.mk_not(le), 2))
                }
                BvOp::Sgt => {
                    let le = self.bvop(BvOp::Sle, vec![args[0], args[1]]);
                    Some(St::Rw(self.mk_not(le), 2))
                }
                BvOp::Add => self.bv_add(args, &s),
                BvOp::Mul => self.bv_mul(args, &s),
                BvOp::Sub => Some(self.p_sub(args, &s)),
                BvOp::Neg => Some(self.p_uminus(args[0], &s)),
                BvOp::Shl => self.bv_shl(args[0], args[1]),
                BvOp::Lshr => self.bv_lshr(args[0], args[1]),
                BvOp::Ashr => self.bv_ashr(args[0], args[1]),
                BvOp::Udiv | BvOp::UdivI => self.bv_udiv(args[0], args[1]),
                BvOp::Sdiv | BvOp::SdivI => self.bv_sdiv(args[0], args[1]),
                BvOp::Urem | BvOp::UremI => self.bv_urem(args[0], args[1]),
                BvOp::Srem | BvOp::SremI => self.bv_srem(args[0], args[1]),
                BvOp::Smod | BvOp::SmodI => self.bv_smod(args[0], args[1]),
                BvOp::Concat => self.bv_concat(args),
                BvOp::Or => self.bv_or(args),
                BvOp::Xor => self.bv_xor(args),
                BvOp::Not => self.bv_not(args[0]),
                BvOp::And => {
                    if let Some(r) = self.factor_zero_extensions(BvOp::And, args) {
                        return Some(St::Rw(r, 2));
                    }
                    let ns: Vec<T> = args
                        .iter()
                        .map(|&a| self.bvop(BvOp::Not, vec![a]))
                        .collect();
                    let o = self.bvop(BvOp::Or, ns);
                    Some(St::Rw(self.bvop(BvOp::Not, vec![o]), 3))
                }
                BvOp::Nand => {
                    let ns: Vec<T> = args
                        .iter()
                        .map(|&a| self.bvop(BvOp::Not, vec![a]))
                        .collect();
                    Some(St::Rw(self.bvop(BvOp::Or, ns), 2))
                }
                BvOp::Nor => {
                    let o = self.bvop(BvOp::Or, args.to_vec());
                    Some(St::Rw(self.bvop(BvOp::Not, vec![o]), 2))
                }
                BvOp::Xnor => {
                    if args.len() != 2 {
                        return None;
                    }
                    let x = self.bvop(BvOp::Xor, args.to_vec());
                    Some(St::Rw(self.bvop(BvOp::Not, vec![x]), 2))
                }
                BvOp::Comp => {
                    let (a, b) = (args[0], args[1]);
                    if a == b {
                        return Some(St::Done(self.mk_bv(&Int::from(1), 1)));
                    }
                    if self.bv_num(a).is_some() && self.bv_num(b).is_some() {
                        return Some(St::Done(self.bv_zero(1)));
                    }
                    let eq = self.mk_eq(a, b);
                    let one = self.mk_bv(&Int::from(1), 1);
                    let zero = self.bv_zero(1);
                    Some(St::Rw(self.mk_ite(eq, one, zero), 2))
                }
            },
            Op::Extract(h, l) => self.bv_extract(*h, *l, args[0]),
            Op::ZeroExt(n) => {
                if *n == 0 {
                    return Some(St::Done(args[0]));
                }
                let z = self.bv_zero(*n);
                Some(St::Rw(self.mk_concat(vec![z, args[0]]), 1))
            }
            Op::SignExt(n) => self.bv_sign_extend(*n, args[0]),
            Op::Repeat(n) => {
                if *n == 1 {
                    return Some(St::Done(args[0]));
                }
                let cs = vec![args[0]; *n as usize];
                Some(St::Rw(self.mk_concat(cs), 1))
            }
            Op::RotL(n) => Some(self.rotate_left(*n, args[0])),
            Op::RotR(n) => {
                let sz = self.bv_width(args[0]);
                let n = n % sz;
                Some(self.rotate_left(sz - n, args[0]))
            }
            _ => None,
        }
    }

    /// `mk_uge`/`mk_sge`: `a >= b` as `b <= a`.
    fn ge_via_le(&mut self, signed: bool, b: T, a: T) -> St {
        match self.leq_core(signed, b, a) {
            Some(st) => st,
            None => {
                let op = if signed { BvOp::Sle } else { BvOp::Ule };
                St::Done(self.bvop(op, vec![b, a]))
            }
        }
    }

    fn rotate_left(&mut self, n: u32, arg: T) -> St {
        let sz = self.bv_width(arg);
        let n = n % sz;
        if n == 0 || sz == 1 {
            return St::Done(arg);
        }
        let a = self.mk_extract(sz - n - 1, 0, arg);
        let b = self.mk_extract(sz - 1, sz - n, arg);
        St::Rw(self.mk_concat(vec![a, b]), 2)
    }

    /// `is_zero_bit`: is bit `idx` of `x` known to be zero?
    fn is_zero_bit(&self, x: T, idx: u32) -> bool {
        let (mut x, mut idx) = (x, idx);
        loop {
            if let Some((v, _)) = self.bv_num(x) {
                return v.is_zero() || !v.bit(u64::from(idx));
            }
            if self.is_bvop(x, BvOp::Concat) {
                let mut found = None;
                for &y in self.nodes[x].args.iter().rev() {
                    let w = self.bv_width(y);
                    if w <= idx {
                        idx -= w;
                    } else {
                        found = Some(y);
                        break;
                    }
                }
                match found {
                    Some(y) => {
                        x = y;
                        continue;
                    }
                    None => return false,
                }
            }
            return false;
        }
    }

    /// `is_zero_extended`: `(concat 0 x)`.
    fn is_zero_extended(&self, e: T) -> Option<T> {
        if self.is_bvop(e, BvOp::Concat) && self.nodes[e].args.len() == 2 {
            let z = self.arg(e, 0);
            if self.bv_num(z).is_some_and(|(v, _)| v.is_zero()) {
                return Some(self.arg(e, 1));
            }
        }
        None
    }

    /// `is_sign_extended`: `(concat x[n-1] … x[n-1] x)`.
    fn is_sign_extended(&self, e: T) -> Option<T> {
        if let Op::SignExt(_) = self.nodes[e].op {
            return Some(self.arg(e, 0));
        }
        if !self.is_bvop(e, BvOp::Concat) || self.nodes[e].args.len() < 2 {
            return None;
        }
        let args = &self.nodes[e].args;
        let x = *args.last().unwrap();
        let sz = self.bv_width(x);
        for &sign in &args[..args.len() - 1] {
            if self.nodes[sign].op != Op::Extract(sz - 1, sz - 1) || self.arg(sign, 0) != x {
                return None;
            }
        }
        Some(x)
    }

    fn factor_zero_extensions(&mut self, k: BvOp, args: &[T]) -> Option<T> {
        if args.len() < 2 {
            return None;
        }
        let x = self.is_zero_extended(args[0])?;
        let inner_size = self.bv_width(x);
        let mut inner = vec![x];
        for &a in &args[1..] {
            let y = self.is_zero_extended(a)?;
            if self.bv_width(y) != inner_size {
                return None;
            }
            inner.push(y);
        }
        let i = self.bvop(k, inner);
        let n = self.bv_width(args[0]) - inner_size;
        Some(self.mk(Op::ZeroExt(n), vec![i]))
    }

    fn num_leading_zero_bits(&self, e: T) -> u32 {
        if let Some((v, sz)) = self.bv_num(e) {
            let mut sz = sz;
            let mut v = v;
            while !v.is_zero() && !v.is_negative() {
                sz -= 1;
                v = v.div_floor(&Int::from(2));
            }
            return sz;
        }
        if self.is_bvop(e, BvOp::Concat) {
            let a0 = self.arg(e, 0);
            let sz1 = self.bv_width(a0);
            let mut nb1 = self.num_leading_zero_bits(a0);
            if sz1 == nb1 && self.nodes[e].args.len() > 1 {
                nb1 += self.num_leading_zero_bits(self.arg(e, 1));
            }
            return nb1;
        }
        0
    }

    /// `structural is_sorted`.
    fn is_sorted(&self, args: &[T]) -> bool {
        args.windows(2).all(|w| !self.lt(w[1], w[0]))
    }

    /// `bv_rewriter::mk_leq_core`.
    fn leq_core(&mut self, signed: bool, a: T, b: T) -> Option<St> {
        let sz = self.bv_width(a);
        let n1 = self.bv_num(a).map(|(v, _)| v);
        let n2 = self.bv_num(b).map(|(v, _)| v);
        if a == b {
            return Some(St::Done(self.mk_true()));
        }
        if signed
            && let (Some(x), Some(y)) = (self.is_zero_extended(a), self.is_zero_extended(b))
            && self.bv_width(x) == self.bv_width(y)
        {
            return Some(St::Rw(self.bvop(BvOp::Ule, vec![x, y]), 2));
        }
        let nm = |v: &Int| if signed { to_signed(v, sz) } else { v.clone() };
        let r1 = n1.as_ref().map(nm);
        let r2 = n2.as_ref().map(nm);
        if let (Some(r1), Some(r2)) = (&r1, &r2) {
            return Some(St::Done(self.mk_bool(r1 <= r2)));
        }
        let (lower, upper) = if signed {
            (-&pow2(sz - 1), &pow2(sz - 1) - &Int::from(1))
        } else {
            (Int::from(0), &pow2(sz) - &Int::from(1))
        };
        if let Some(r2) = &r2 {
            if *r2 == lower {
                return Some(St::Rw(self.mk_eq(a, b), 1));
            }
            if *r2 == upper {
                return Some(St::Done(self.mk_true()));
            }
        }
        if let Some(r1) = &r1 {
            if *r1 == lower {
                return Some(St::Done(self.mk_true()));
            }
            if *r1 == upper {
                return Some(St::Rw(self.mk_eq(a, b), 1));
            }
        }
        // (bvule r1 (+ r2 a)) → (bvule a (2^n - r2 - 1)) [∧/∨ (bvule r1-r2 a)]
        if !signed
            && let Some(r1) = &r1
            && self.is_bvop(b, BvOp::Add)
            && self.nodes[b].args.len() == 2
            && let Some((r2, _)) = self.bv_num(self.arg(b, 0))
        {
            let a2 = self.arg(b, 1);
            let k = &(-&r2) - &Int::from(1);
            let kn = self.mk_bv(&k, sz);
            let mut r = self.bvop(BvOp::Ule, vec![a2, kn]);
            if *r1 != r2 {
                let d = self.mk_bv(&(r1 - &r2), sz);
                let le = self.bvop(BvOp::Ule, vec![d, a2]);
                r = if *r1 > r2 {
                    self.mk_and2(r, le)
                } else {
                    self.mk_or2(r, le)
                };
            }
            return Some(St::Rw(r, 2));
        }
        if !signed {
            let last_non_zero = |s: &Self, x: T| (0..sz).rev().find(|&i| !s.is_zero_bit(x, i));
            match last_non_zero(self, b) {
                None => {
                    let z = self.bv_zero(sz);
                    return Some(St::Rw(self.mk_eq(a, z), 1));
                }
                Some(lnz) if lnz < sz - 1 => {
                    let e1 = self.mk_extract(sz - 1, lnz + 1, a);
                    let e2 = self.bv_zero(sz - lnz - 1);
                    let e3 = self.mk_extract(lnz, 0, a);
                    let e4 = self.mk_extract(lnz, 0, b);
                    let e5 = self.bvop(BvOp::Ule, vec![e3, e4]);
                    let eq = self.mk_eq(e1, e2);
                    return Some(St::Rw(self.mk_and2(eq, e5), 3));
                }
                _ => {}
            }
            match last_non_zero(self, a) {
                None => return Some(St::Done(self.mk_true())),
                Some(lnz) if lnz < sz - 1 => {
                    let e1 = self.mk_extract(sz - 1, lnz + 1, b);
                    let e2 = self.bv_zero(sz - lnz - 1);
                    let eq = self.mk_eq(e1, e2);
                    let e3 = self.mk_extract(lnz, 0, a);
                    let e4 = self.mk_extract(lnz, 0, b);
                    let le = self.bvop(BvOp::Ule, vec![e3, e4]);
                    let imp = self.mk(Op::Implies, vec![eq, le]);
                    return Some(St::Rw(imp, super::FULL));
                }
                _ => {}
            }
        }
        None
    }

    /// `bv_rewriter::mk_extract`.
    fn bv_extract(&mut self, high: u32, low: u32, arg: T) -> Option<St> {
        let sz = self.bv_width(arg);
        if low == 0 && high == sz - 1 {
            return Some(St::Done(arg));
        }
        if let Some((v, _)) = self.bv_num(arg) {
            let r = norm(&v.div_floor(&pow2(low)), high - low + 1);
            return Some(St::Done(self.mk_bv(&r, high - low + 1)));
        }
        if let Op::Extract(_, low2) = self.nodes[arg].op {
            let x = self.arg(arg, 0);
            return Some(St::Done(self.mk_extract(high + low2, low + low2, x)));
        }
        if self.is_bvop(arg, BvOp::Concat) {
            let kids = self.nodes[arg].args.clone();
            let mut idx = sz;
            for (i, &curr) in kids.iter().enumerate() {
                let curr_sz = self.bv_width(curr);
                idx -= curr_sz;
                if idx > high {
                    continue;
                }
                if idx <= low {
                    if low == idx && high - idx == curr_sz - 1 {
                        return Some(St::Done(curr));
                    }
                    return Some(St::Rw(self.mk_extract(high - idx, low - idx, curr), 1));
                }
                let mut new_args = Vec::new();
                let mut used_extract = false;
                if high - idx == curr_sz - 1 {
                    new_args.push(curr);
                } else {
                    used_extract = true;
                    new_args.push(self.mk_extract(high - idx, 0, curr));
                }
                for &c in &kids[i + 1..] {
                    let csz = self.bv_width(c);
                    idx -= csz;
                    if idx > low {
                        new_args.push(c);
                        continue;
                    }
                    if idx == low {
                        new_args.push(c);
                        let r = self.mk_concat(new_args);
                        return Some(if used_extract {
                            St::Rw(r, 2)
                        } else {
                            St::Done(r)
                        });
                    }
                    new_args.push(self.mk_extract(csz - 1, low - idx, c));
                    return Some(St::Rw(self.mk_concat(new_args), 2));
                }
                return None;
            }
            return None;
        }
        if low == 0 {
            let k = self.nodes[arg].op.clone();
            let unsigned = matches!(k, Op::Bv(BvOp::UdivI | BvOp::UremI));
            let signed = matches!(k, Op::Bv(BvOp::SdivI | BvOp::SremI));
            if (unsigned || signed) && self.nodes[arg].args.len() == 2 {
                let (a, b) = (self.arg(arg, 0), self.arg(arg, 1));
                let xy = if unsigned {
                    self.is_zero_extended(a).zip(self.is_zero_extended(b))
                } else {
                    self.is_sign_extended(a).zip(self.is_sign_extended(b))
                };
                if let Some((x, y)) = xy
                    && high + 1 == self.bv_width(x)
                    && self.bv_width(x) == self.bv_width(y)
                {
                    return Some(St::Rw(self.mk(k, vec![x, y]), 1));
                }
            }
        }
        if self.is_bvop(arg, BvOp::Not)
            || self.is_bvop(arg, BvOp::Or)
            || self.is_bvop(arg, BvOp::Xor)
            || (low == 0 && (self.is_bvop(arg, BvOp::Add) || self.is_bvop(arg, BvOp::Mul)))
        {
            let op = self.nodes[arg].op.clone();
            let kids = self.nodes[arg].args.clone();
            let ns: Vec<T> = kids
                .iter()
                .map(|&c| self.mk_extract(high, low, c))
                .collect();
            return Some(St::Rw(self.mk(op, ns), 2));
        }
        if let Some((c, t, e)) = self.is_ite(arg)
            && (self.fresh(t)
                || self.fresh(e)
                || self.is_ite(t).is_none()
                || self.is_ite(e).is_none())
        {
            let a = self.mk_extract(high, low, t);
            let b = self.mk_extract(high, low, e);
            return Some(St::Rw(self.mk_ite(c, a, b), 2));
        }
        if low == 0
            && self.is_bvop(arg, BvOp::Ashr)
            && let Some((v, _)) = self.bv_num(self.arg(arg, 1))
            && Int::from(high) < &Int::from(sz) - &v
        {
            let k = v.to_u64().unwrap_or(0) as u32;
            let t = self.arg(arg, 0);
            return Some(St::Rw(self.mk_extract(high + k, low + k, t), 1));
        }
        None
    }

    fn bv_shl(&mut self, a: T, b: T) -> Option<St> {
        let sz = self.bv_width(a);
        if let Some((r2, _)) = self.bv_num(b) {
            if r2.is_zero() {
                return Some(St::Done(a));
            }
            if r2 >= Int::from(sz) {
                return Some(St::Done(self.bv_zero(sz)));
            }
            let k = r2.to_u64().unwrap() as u32;
            if let Some((r1, _)) = self.bv_num(a) {
                let r = norm(&(&r1 * &pow2(k)), sz);
                return Some(St::Done(self.mk_bv(&r, sz)));
            }
            let e = self.mk_extract(sz - k - 1, 0, a);
            let z = self.bv_zero(k);
            return Some(St::Rw(self.mk_concat(vec![e, z]), 2));
        }
        if self.is_bvop(a, BvOp::Shl) {
            let (x, y) = (self.arg(a, 0), self.arg(a, 1));
            let sum = self.bvop(BvOp::Add, vec![y, b]);
            let cond = self.bvop(BvOp::Ule, vec![y, sum]);
            let sh = self.bvop(BvOp::Shl, vec![x, sum]);
            let z = self.bv_zero(sz);
            return Some(St::Rw(self.mk_ite(cond, sh, z), 3));
        }
        None
    }

    fn bv_lshr(&mut self, a: T, b: T) -> Option<St> {
        let sz = self.bv_width(a);
        if let Some((r2, _)) = self.bv_num(b) {
            if r2.is_zero() {
                return Some(St::Done(a));
            }
            if r2 >= Int::from(sz) {
                return Some(St::Done(self.bv_zero(sz)));
            }
            let k = r2.to_u64().unwrap() as u32;
            if let Some((r1, _)) = self.bv_num(a) {
                let r = r1.div_floor(&pow2(k));
                return Some(St::Done(self.mk_bv(&r, sz)));
            }
            let z = self.bv_zero(k);
            let e = self.mk_extract(sz - 1, k, a);
            return Some(St::Rw(self.mk_concat(vec![z, e]), 2));
        }
        if a == b {
            return Some(St::Done(self.bv_zero(sz)));
        }
        None
    }

    fn bv_ashr(&mut self, a: T, b: T) -> Option<St> {
        let sz = self.bv_width(a);
        let n2 = self.bv_num(b).map(|(v, _)| v);
        if n2.as_ref().is_some_and(|v| v.is_zero()) {
            return Some(St::Done(a));
        }
        let n1 = self.bv_num(a).map(|(v, _)| v);
        if let (Some(r1), Some(r2)) = (&n1, &n2) {
            let neg = r1.bit(u64::from(sz - 1));
            if *r2 >= Int::from(sz) {
                let r = if neg {
                    &pow2(sz) - &Int::from(1)
                } else {
                    Int::from(0)
                };
                return Some(St::Done(self.mk_bv(&r, sz)));
            }
            let k = r2.to_u64().unwrap() as u32;
            let r = to_signed(r1, sz).div_floor(&pow2(k));
            return Some(St::Done(self.mk_bv(&r, sz)));
        }
        if let Some(r2) = &n2
            && self.is_bvop(a, BvOp::Ashr)
            && let Some((r1, _)) = self.bv_num(self.arg(a, 1))
        {
            let mut r = &r1 + r2;
            if r > Int::from(sz) {
                r = Int::from(sz);
            }
            let x = self.arg(a, 0);
            let k = self.mk_bv(&r, sz);
            return Some(St::Rw(self.bvop(BvOp::Ashr, vec![x, k]), 1));
        }
        if let Some(r2) = &n2
            && self.num_leading_zero_bits(a) > 0
        {
            if *r2 >= Int::from(sz) {
                return Some(St::Done(self.bv_zero(sz)));
            }
            let k = r2.to_u64().unwrap() as u32;
            let z = self.bv_zero(k);
            let e = self.mk_extract(sz - 1, k, a);
            return Some(St::Rw(self.mk_concat(vec![z, e]), 2));
        }
        None
    }

    fn bv_udiv(&mut self, a: T, b: T) -> Option<St> {
        let sz = self.bv_width(a);
        if let Some((r2, _)) = self.bv_num(b) {
            if r2.is_zero() {
                return Some(St::Done(self.bv_ones(sz)));
            }
            if r2.is_one() {
                return Some(St::Done(a));
            }
            if let Some((r1, _)) = self.bv_num(a) {
                let q = r1.div_floor(&r2);
                return Some(St::Done(self.mk_bv(&q, sz)));
            }
            if let Some(shift) = power_of_two(&r2) {
                let k = self.mk_bv(&Int::from(shift), sz);
                return Some(St::Rw(self.bvop(BvOp::Lshr, vec![a, k]), 1));
            }
        }
        Some(St::Done(self.bvop(BvOp::UdivI, vec![a, b])))
    }

    fn bv_sdiv(&mut self, a: T, b: T) -> Option<St> {
        let sz = self.bv_width(a);
        if let Some((v2, _)) = self.bv_num(b) {
            let r2 = to_signed(&v2, sz);
            if r2.is_zero() {
                let z = self.bv_zero(sz);
                let slt = self.bvop(BvOp::Slt, vec![a, z]);
                let one = self.mk_bv(&Int::from(1), sz);
                let ones = self.bv_ones(sz);
                return Some(St::Rw(self.mk_ite(slt, one, ones), 2));
            }
            if r2.is_one() {
                return Some(St::Done(a));
            }
            if let Some((v1, _)) = self.bv_num(a) {
                let r1 = to_signed(&v1, sz);
                let q = r1.div_rem_trunc(&r2).0;
                return Some(St::Done(self.mk_bv(&q, sz)));
            }
        }
        Some(St::Done(self.bvop(BvOp::SdivI, vec![a, b])))
    }

    fn bv_srem(&mut self, a: T, b: T) -> Option<St> {
        let sz = self.bv_width(a);
        if let Some((v2, _)) = self.bv_num(b) {
            let r2 = to_signed(&v2, sz);
            if r2.is_zero() {
                return Some(St::Done(a));
            }
            if r2.is_one() || r2 == Int::from(-1) {
                return Some(St::Done(self.bv_zero(sz)));
            }
            if self.is_bvop(a, BvOp::SremI)
                && let Some((dv, dsz)) = self.bv_num(self.arg(a, 1))
            {
                let d = to_signed(&dv, dsz);
                if !d.is_zero() && d.div_rem_trunc(&r2).1.is_zero() {
                    let x = self.arg(a, 0);
                    return Some(St::Rw(self.bvop(BvOp::SremI, vec![x, b]), 1));
                }
            }
            if let Some((v1, _)) = self.bv_num(a) {
                let r1 = to_signed(&v1, sz);
                let r = r1.div_rem_trunc(&r2).1;
                return Some(St::Done(self.mk_bv(&r, sz)));
            }
        }
        Some(St::Done(self.bvop(BvOp::SremI, vec![a, b])))
    }

    fn bv_urem(&mut self, a: T, b: T) -> Option<St> {
        let sz = self.bv_width(a);
        let n1 = self.bv_num(a).map(|(v, _)| v);
        if let Some((r2, _)) = self.bv_num(b) {
            if r2.is_zero() {
                return Some(St::Done(a));
            }
            if r2.is_one() {
                return Some(St::Done(self.bv_zero(sz)));
            }
            if let Some(r1) = &n1 {
                let r = r1.rem_euclid(&r2);
                return Some(St::Done(self.mk_bv(&r, sz)));
            }
            if let Some(shift) = power_of_two(&r2) {
                let z = self.bv_zero(sz - shift);
                let e = self.mk_extract(shift - 1, 0, a);
                return Some(St::Rw(self.mk_concat(vec![z, e]), 2));
            }
            return Some(St::Done(self.bvop(BvOp::UremI, vec![a, b])));
        }
        if n1.as_ref().is_some_and(|v| v.is_zero()) {
            return Some(St::Done(a));
        }
        if self.is_x_minus_one(a) == Some(b) {
            return Some(St::Done(a));
        }
        Some(St::Done(self.bvop(BvOp::UremI, vec![a, b])))
    }

    /// `is_x_minus_one`: `(bvadd -1 x)` / `(bvadd x -1)`.
    fn is_x_minus_one(&self, a: T) -> Option<T> {
        if !self.is_bvop(a, BvOp::Add) || self.nodes[a].args.len() != 2 {
            return None;
        }
        let ones = |s: &Self, t: T| {
            s.bv_num(t)
                .is_some_and(|(v, w)| v == &pow2(w) - &Int::from(1))
        };
        if ones(self, self.arg(a, 0)) {
            return Some(self.arg(a, 1));
        }
        if ones(self, self.arg(a, 1)) {
            return Some(self.arg(a, 0));
        }
        None
    }

    fn bv_smod(&mut self, a: T, b: T) -> Option<St> {
        let sz = self.bv_width(a);
        let r1 = self.bv_num(a).map(|(v, _)| to_signed(&v, sz));
        if r1.as_ref().is_some_and(|v| v.is_zero()) {
            return Some(St::Rw(self.bvop(BvOp::Urem, vec![a, b]), 1));
        }
        if let Some((v2, _)) = self.bv_num(b) {
            let r2 = to_signed(&v2, sz);
            if r2.is_zero() {
                return Some(St::Done(a));
            }
            if let Some(r1) = &r1 {
                let abs1 = norm(&r1.abs(), sz);
                let abs2 = norm(&r2.abs(), sz);
                let u = norm(&abs1.rem_euclid(&abs2), sz);
                let pos1 = !r1.is_negative() && !r1.is_zero();
                let pos2 = !r2.is_negative() && !r2.is_zero();
                let r = if u.is_zero() || (pos1 && pos2) {
                    u
                } else if r1.is_negative() && pos2 {
                    norm(&(&r2 - &u), sz)
                } else if pos1 && r2.is_negative() {
                    norm(&(&u + &r2), sz)
                } else {
                    norm(&(-&u), sz)
                };
                return Some(St::Done(self.mk_bv(&r, sz)));
            }
            if r2.is_one() {
                return Some(St::Rw(self.bv_zero(sz), 2));
            }
        }
        Some(St::Done(self.bvop(BvOp::SmodI, vec![a, b])))
    }

    fn bv_sign_extend(&mut self, n: u32, arg: T) -> Option<St> {
        if n == 0 {
            return Some(St::Done(arg));
        }
        if let Some((v, sz)) = self.bv_num(arg) {
            let r = to_signed(&v, sz);
            return Some(St::Done(self.mk_bv(&r, sz + n)));
        }
        let sz = self.bv_width(arg);
        let sign = self.mk_extract(sz - 1, sz - 1, arg);
        let mut args = vec![sign; n as usize];
        args.push(arg);
        Some(St::Rw(self.mk_concat(args), 2))
    }

    /// `bv_rewriter::mk_concat`.
    fn bv_concat(&mut self, args: &[T]) -> Option<St> {
        let mut new_args: Vec<T> = Vec::new();
        let mut fused_numeral = false;
        let mut expanded = false;
        let mut fused_extract = false;
        let mut eq_args = true;
        for (i, &arg) in args.iter().enumerate() {
            let prev = if i > 0 {
                new_args.last().copied()
            } else {
                None
            };
            if let Some(p) = prev {
                eq_args &= p == arg;
            }
            if let (Some((v1, sz1)), Some((v2, sz2))) =
                (self.bv_num(arg), prev.and_then(|p| self.bv_num(p)))
            {
                let v = &(&v2 * &pow2(sz1)) + &v1;
                new_args.pop();
                new_args.push(self.mk_bv(&v, sz1 + sz2));
                fused_numeral = true;
            } else if self.is_bvop(arg, BvOp::Concat) {
                new_args.extend_from_slice(&self.nodes[arg].args.clone());
                expanded = true;
            } else if let (Op::Extract(h2, _), Some(p)) = (&self.nodes[arg].op, prev)
                && let Op::Extract(h1, l1) = self.nodes[p].op
                && self.arg(arg, 0) == self.arg(p, 0)
                && l1 == h2 + 1
            {
                let Op::Extract(_, l2) = self.nodes[arg].op else {
                    unreachable!()
                };
                let x = self.arg(arg, 0);
                let e = self.mk_extract(h1, l2, x);
                new_args.pop();
                new_args.push(e);
                fused_extract = true;
            } else {
                new_args.push(arg);
            }
        }
        if !fused_numeral && !expanded && !fused_extract {
            if eq_args && let Some((x, y, z)) = self.is_ite(*new_args.last().unwrap()) {
                let a1 = self.mk_concat(vec![y; new_args.len()]);
                let a2 = self.mk_concat(vec![z; new_args.len()]);
                return Some(St::Rw(self.mk_ite(x, a1, a2), 2));
            }
            return None;
        }
        if new_args.len() == 1 {
            let r = new_args[0];
            return Some(if fused_extract {
                St::Rw(r, 1)
            } else {
                St::Done(r)
            });
        }
        let r = self.mk_concat(new_args);
        Some(if fused_extract {
            St::Rw(r, 2)
        } else if expanded {
            St::Rw(r, 1)
        } else {
            St::Done(r)
        })
    }

    /// `bv_rewriter::mk_bv_or`.
    fn bv_or(&mut self, args: &[T]) -> Option<St> {
        if args.len() == 1 {
            return Some(St::Done(args[0]));
        }
        if let Some(r) = self.factor_zero_extensions(BvOp::Or, args) {
            return Some(St::Rw(r, 2));
        }
        let sz = self.bv_width(args[0]);
        let mut flat = Vec::new();
        for &a in args {
            if self.is_bvop(a, BvOp::Or) {
                flat.extend_from_slice(&self.nodes[a].args.clone());
            } else {
                flat.push(a);
            }
        }
        let flattened = flat.len() != args.len();
        let args: &[T] = &flat;
        let ones = &pow2(sz) - &Int::from(1);
        let mut new_args = Vec::new();
        let mut pos = alloc::collections::BTreeSet::new();
        let mut neg = alloc::collections::BTreeSet::new();
        let mut merged = false;
        let mut num_coeffs = 0;
        let mut v1 = Int::from(0);
        for &arg in args {
            if let Some((v2, _)) = self.bv_num(arg) {
                num_coeffs += 1;
                v1 = &v1 | &v2;
                continue;
            }
            if self.is_bvop(arg, BvOp::Not) {
                let atom = self.arg(arg, 0);
                if pos.contains(&atom) {
                    return Some(St::Done(self.mk_bv(&ones, sz)));
                }
                if neg.contains(&atom) {
                    merged = true;
                    continue;
                }
                neg.insert(atom);
                new_args.push(arg);
            } else {
                if pos.contains(&arg) {
                    merged = true;
                    continue;
                }
                if neg.contains(&arg) {
                    return Some(St::Done(self.mk_bv(&ones, sz)));
                }
                pos.insert(arg);
                new_args.push(arg);
            }
        }
        if v1 == ones {
            return Some(St::Done(self.mk_bv(&v1, sz)));
        }
        if new_args.len() == 2
            && num_coeffs == 0
            && self.is_bvop(new_args[0], BvOp::Concat)
            && self.is_bvop(new_args[1], BvOp::Concat)
        {
            let (c1, c2) = (new_args[0], new_args[1]);
            if (0..sz).all(|i| self.is_zero_bit(c1, i) || self.is_zero_bit(c2, i)) {
                let mut parts = Vec::new();
                let mut j = sz as i64 - 1;
                while j >= 0 {
                    let high = j;
                    while j >= 0 && self.is_zero_bit(c1, j as u32) {
                        j -= 1;
                    }
                    if j != high {
                        parts.push(self.mk_extract(high as u32, (j + 1) as u32, c2));
                    }
                    let high = j;
                    while j >= 0 && self.is_zero_bit(c2, j as u32) {
                        j -= 1;
                    }
                    if j != high {
                        parts.push(self.mk_extract(high as u32, (j + 1) as u32, c1));
                    }
                }
                return Some(St::Rw(self.mk_concat(parts), 2));
            }
        }
        if !v1.is_zero() && new_args.len() == 1 {
            let t = new_args[0];
            let mut v = v1.clone();
            let mut exs = Vec::new();
            let (mut low, mut i) = (0u32, 0u32);
            while i < sz {
                while i < sz && v.bit(0) {
                    i += 1;
                    v = v.div_floor(&Int::from(2));
                }
                if i != low {
                    let n = i - low;
                    let k = &pow2(n) - &Int::from(1);
                    exs.push(self.mk_bv(&k, n));
                    low = i;
                }
                while i < sz && !v.bit(0) {
                    i += 1;
                    v = v.div_floor(&Int::from(2));
                }
                if i != low {
                    exs.push(self.mk_extract(i - 1, low, t));
                    low = i;
                }
            }
            exs.reverse();
            return Some(St::Rw(self.mk_concat(exs), 2));
        }
        if !flattened
            && !merged
            && (num_coeffs == 0 || (num_coeffs == 1 && !v1.is_zero()))
            && self.is_sorted(args)
        {
            return None;
        }
        if !v1.is_zero() {
            new_args.push(self.mk_bv(&v1, sz));
        }
        match new_args.len() {
            0 => Some(St::Done(self.bv_zero(sz))),
            1 => Some(St::Done(new_args[0])),
            _ => {
                new_args.sort_by(|&x, &y| self.ast_cmp(x, y));
                if let Some(r) = self.distribute_concat(BvOp::Or, &new_args) {
                    return Some(St::Rw(r, 3));
                }
                Some(St::Done(self.bvop(BvOp::Or, new_args)))
            }
        }
    }

    /// `bv_rewriter::mk_bv_xor`.
    fn bv_xor(&mut self, args: &[T]) -> Option<St> {
        if args.len() == 1 {
            return Some(St::Done(args[0]));
        }
        let sz = self.bv_width(args[0]);
        let mut flat = Vec::new();
        for &a in args {
            if self.is_bvop(a, BvOp::Xor) {
                flat.extend_from_slice(&self.nodes[a].args.clone());
            } else {
                flat.push(a);
            }
        }
        let flattened = flat.len() != args.len();
        let args: &[T] = &flat;
        let ones = &pow2(sz) - &Int::from(1);
        let mut pos = alloc::collections::BTreeSet::new();
        let mut neg = alloc::collections::BTreeSet::new();
        let mut merged = false;
        let mut v1 = Int::from(0);
        let mut num_coeffs = 0;
        for &arg in args {
            if let Some((v2, _)) = self.bv_num(arg) {
                v1 = &v1 ^ &v2;
                num_coeffs += 1;
                continue;
            }
            if self.is_bvop(arg, BvOp::Not) {
                let atom = self.arg(arg, 0);
                if neg.remove(&atom) {
                    merged = true;
                } else if pos.remove(&atom) {
                    merged = true;
                    v1 = &v1 ^ &ones;
                } else {
                    neg.insert(atom);
                }
            } else if pos.remove(&arg) {
                merged = true;
            } else if neg.remove(&arg) {
                merged = true;
                v1 = &v1 ^ &ones;
            } else {
                pos.insert(arg);
            }
        }
        if !v1.is_zero() && num_coeffs == args.len() - 1 {
            let t = *args.iter().find(|&&a| self.bv_num(a).is_none()).unwrap();
            let not_t = self.bvop(BvOp::Not, vec![t]);
            let mut v = v1.clone();
            let mut exs = Vec::new();
            let (mut low, mut i) = (0u32, 0u32);
            while i < sz {
                while i < sz && v.bit(0) {
                    i += 1;
                    v = v.div_floor(&Int::from(2));
                }
                if i != low {
                    exs.push(self.mk_extract(i - 1, low, not_t));
                    low = i;
                }
                while i < sz && !v.bit(0) {
                    i += 1;
                    v = v.div_floor(&Int::from(2));
                }
                if i != low {
                    exs.push(self.mk_extract(i - 1, low, t));
                    low = i;
                }
            }
            exs.reverse();
            let r = if exs.len() == 1 {
                exs[0]
            } else {
                self.mk_concat(exs)
            };
            return Some(St::Rw(r, 3));
        }
        if !merged
            && !flattened
            && (num_coeffs == 0 || (num_coeffs == 1 && !v1.is_zero() && v1 != ones))
            && self.is_sorted(args)
        {
            if let Some(r) = self.distribute_concat(BvOp::Xor, args) {
                return Some(St::Rw(r, 3));
            }
            return None;
        }
        let mut new_args = Vec::new();
        if !v1.is_zero() {
            new_args.push(self.mk_bv(&v1, sz));
        }
        for &arg in args {
            if self.bv_num(arg).is_some() {
                continue;
            }
            if self.is_bvop(arg, BvOp::Not) {
                let atom = self.arg(arg, 0);
                if neg.remove(&atom) {
                    new_args.push(arg);
                }
            } else if pos.remove(&arg) {
                new_args.push(arg);
            }
        }
        match new_args.len() {
            0 => Some(St::Done(self.bv_zero(sz))),
            1 => Some(St::Done(new_args[0])),
            n => {
                if n == 2 && self.bv_num(new_args[0]).is_some_and(|(v, _)| v == ones) {
                    return Some(St::Done(self.bvop(BvOp::Not, vec![new_args[1]])));
                }
                new_args.sort_by(|&x, &y| self.ast_cmp(x, y));
                if let Some(r) = self.distribute_concat(BvOp::Xor, &new_args) {
                    return Some(St::Rw(r, 3));
                }
                Some(St::Done(self.bvop(BvOp::Xor, new_args)))
            }
        }
    }

    /// `distribute_concat`: split a bitwise operation along the first
    /// concatenation argument's top part.
    fn distribute_concat(&mut self, k: BvOp, args: &[T]) -> Option<T> {
        for &arg in args {
            if self.is_bvop(arg, BvOp::Concat) {
                let e = self.arg(arg, 0);
                let sz1 = self.bv_width(e);
                let sz2 = self.bv_width(arg);
                if sz1 == sz2 {
                    return Some(self.bvop(k, args.to_vec()));
                }
                let a1: Vec<T> = args
                    .iter()
                    .map(|&a| self.mk_extract(sz2 - 1, sz2 - sz1, a))
                    .collect();
                let a2: Vec<T> = args
                    .iter()
                    .map(|&a| self.mk_extract(sz2 - sz1 - 1, 0, a))
                    .collect();
                let x = self.bvop(k, a1);
                let y = self.bvop(k, a2);
                return Some(self.mk_concat(vec![x, y]));
            }
        }
        None
    }

    /// `bv_rewriter::mk_bv_not`.
    fn bv_not(&mut self, arg: T) -> Option<St> {
        if self.is_bvop(arg, BvOp::Not) {
            return Some(St::Done(self.arg(arg, 0)));
        }
        if let Some((v, w)) = self.bv_num(arg) {
            let r = &(&pow2(w) - &Int::from(1)) - &v;
            return Some(St::Done(self.mk_bv(&r, w)));
        }
        if self.is_bvop(arg, BvOp::Concat) {
            let kids = self.nodes[arg].args.clone();
            let ns: Vec<T> = kids
                .iter()
                .map(|&a| self.bvop(BvOp::Not, vec![a]))
                .collect();
            return Some(St::Rw(self.mk_concat(ns), 2));
        }
        if let Some((x, y, z)) = self.is_ite(arg) {
            if let Some((v, w)) = self.bv_num(y) {
                let n = self.mk_bv(&(&(&pow2(w) - &Int::from(1)) - &v), w);
                let nz = self.bvop(BvOp::Not, vec![z]);
                return Some(St::Rw(self.mk_ite(x, n, nz), 2));
            }
            if let Some((v, w)) = self.bv_num(z) {
                let ny = self.bvop(BvOp::Not, vec![y]);
                let n = self.mk_bv(&(&(&pow2(w) - &Int::from(1)) - &v), w);
                return Some(St::Rw(self.mk_ite(x, ny, n), 2));
            }
        }
        None
    }

    /// `bv_rewriter::mk_bv_add`.
    fn bv_add(&mut self, args: &[T], s: &Sort) -> Option<St> {
        if args.len() == 1 {
            return Some(St::Done(args[0]));
        }
        let st = self.flat_add(args, s);
        let terms: Vec<T> = match &st {
            None => args.to_vec(),
            Some(St::Done(r)) if self.is_bvop(*r, BvOp::Add) => self.nodes[*r].args.clone(),
            _ => return st,
        };
        if terms.len() < 2 {
            return st;
        }
        let sz = self.bv_width(terms[0]);
        for i in 0..sz {
            let mut found = false;
            for &t in &terms {
                if !self.is_zero_bit(t, i) {
                    if found {
                        return st;
                    }
                    found = true;
                }
            }
        }
        Some(St::Rw(self.bvop(BvOp::Or, terms), 1))
    }

    /// `bv_rewriter::mk_bv_mul`.
    fn bv_mul(&mut self, args: &[T], s: &Sort) -> Option<St> {
        if args.len() == 1 {
            return Some(St::Done(args[0]));
        }
        let st = self.flat_mul(args, s);
        match &st {
            Some(St::Rw(..)) => st,
            Some(St::Done(r)) => {
                if self.is_bvop(*r, BvOp::Mul) {
                    let kids = self.nodes[*r].args.clone();
                    if let Some(h) = self.mul_hoist(&kids) {
                        return Some(h);
                    }
                }
                st
            }
            None => self.mul_hoist(args),
        }
    }

    /// `mk_mul_hoist`: `(bvmul (bvshl z u) x) → (bvshl (bvmul z x) u)`.
    fn mul_hoist(&mut self, args: &[T]) -> Option<St> {
        if args.len() <= 1 {
            return None;
        }
        for (i, &a) in args.iter().enumerate() {
            if self.is_bvop(a, BvOp::Shl) {
                let (z, u) = (self.arg(a, 0), self.arg(a, 1));
                let mut new_args = args.to_vec();
                new_args[i] = z;
                let m = self.bvop(BvOp::Mul, new_args);
                return Some(St::Rw(self.bvop(BvOp::Shl, vec![m, u]), 2));
            }
        }
        None
    }

    /// `bv_rewriter::mk_ite_core` (before the Boolean `ite` rules).
    pub(super) fn bv_ite(&mut self, c: T, t: T, e: T) -> Option<St> {
        if t == e {
            return Some(St::Rw(e, 1));
        }
        if let Some(c2) = self.is_not(c) {
            return Some(St::Rw(self.mk_ite(c2, e, t), 1));
        }
        if let (Some(x), Some(y)) = (self.is_zero_extended(t), self.is_zero_extended(e))
            && self.bv_width(x) == self.bv_width(y)
        {
            let n = self.bv_width(t) - self.bv_width(x);
            let i = self.mk_ite(c, x, y);
            return Some(St::Rw(self.mk(Op::ZeroExt(n), vec![i]), 2));
        }
        if let (Some(x), Some(y)) = (self.is_sign_extended(t), self.is_sign_extended(e))
            && self.bv_width(x) == self.bv_width(y)
        {
            let n = self.bv_width(t) - self.bv_width(x);
            let i = self.mk_ite(c, x, y);
            return Some(St::Rw(self.mk(Op::SignExt(n), vec![i]), 2));
        }
        if let Some((x, bit1)) = self.is_eq_bit(c)
            && let (Some(bit2), Some(bit3)) = (self.bit(t), self.bit(e))
        {
            if bit1 == bit2 && bit3 != bit2 {
                return Some(St::Done(x));
            }
            if bit1 == bit3 && bit3 != bit2 {
                return Some(St::Rw(self.bvop(BvOp::Not, vec![x]), 1));
            }
        }
        None
    }

    /// A 1-bit numeral's value.
    fn bit(&self, t: T) -> Option<bool> {
        match self.bv_num(t) {
            Some((v, 1)) => Some(v.is_one()),
            _ => None,
        }
    }

    /// `is_eq_bit`: `(= x #bN)` / `(= #bN x)`.
    pub(super) fn is_eq_bit(&self, t: T) -> Option<(T, bool)> {
        if !self.is_op(t, &Op::Eq) {
            return None;
        }
        let (l, r) = (self.arg(t, 0), self.arg(t, 1));
        if let Some(b) = self.bit(l) {
            return Some((r, b));
        }
        if let Some(b) = self.bit(r) {
            return Some((l, b));
        }
        None
    }

    /// `bv_rewriter::mk_distinct`.
    pub(super) fn bv_distinct(&mut self, args: &[T]) -> Option<St> {
        if args.len() <= 1 {
            return Some(St::Done(self.mk_true()));
        }
        let sz = self.bv_width(args[0]);
        if sz >= 32 || args.len() <= (1usize << sz) {
            return None;
        }
        Some(St::Done(self.mk_false()))
    }

    /// `bv_rewriter::mk_eq_core`.
    pub(super) fn bv_eq(&mut self, lhs: T, rhs: T) -> Option<St> {
        let (mut lhs, mut rhs) = (lhs, rhs);
        if lhs == rhs {
            return Some(St::Done(self.mk_true()));
        }
        if self.bv_num(lhs).is_some() && self.bv_num(rhs).is_some() {
            return Some(St::Done(self.mk_false()));
        }
        let mut swapped = false;
        if self.bv_num(lhs).is_some() {
            swapped = true;
            core::mem::swap(&mut lhs, &mut rhs);
        }
        if let Some(st) = self.bit2bool_eq(lhs, rhs) {
            return Some(st);
        }
        if let Some(st) = self.mul_eq(lhs, rhs) {
            return Some(st);
        }
        if let Some(st) = self.mul_eq(rhs, lhs) {
            return Some(st);
        }
        if matches!(self.nodes[lhs].op, Op::Bv(BvOp::Urem | BvOp::UremI))
            && let Some((rv, _)) = self.bv_num(rhs)
            && let Some((dv, dsz)) = self.bv_num(self.arg(lhs, 1))
        {
            if !dv.is_zero() && rv >= dv {
                return Some(St::Done(self.mk_false()));
            }
            if &dv + &rv >= pow2(dsz) {
                let d = self.arg(lhs, 0);
                return Some(St::Rw(self.mk_eq(d, rhs), 2));
            }
        }
        let is_am = |s: &Self, t: T| s.is_bvop(t, BvOp::Add) || s.is_bvop(t, BvOp::Mul);
        if is_am(self, lhs) || is_am(self, rhs) {
            let cancelled = self.cancel_monomials(lhs, rhs);
            if let Some((l, r)) = cancelled {
                if self.bv_num(l).is_some() && self.bv_num(r).is_some() {
                    return Some(St::Done(self.mk_bool(l == r)));
                }
                lhs = l;
                rhs = r;
            }
            if let Some(r) = self.isolate_term(lhs, rhs) {
                return Some(St::Rw(r, 2));
            }
            if self.is_concat_target(lhs, rhs) {
                return Some(self.eq_concat(lhs, rhs));
            }
            if cancelled.is_some() {
                return Some(St::Done(self.mk_eq(lhs, rhs)));
            }
        }
        if self.is_concat_target(lhs, rhs) {
            return Some(self.eq_concat(lhs, rhs));
        }
        if swapped {
            return Some(St::Done(self.mk_eq(lhs, rhs)));
        }
        None
    }

    /// `mk_bit2bool` on an equality of 1-bit vectors.
    fn bit2bool_eq(&mut self, lhs: T, rhs: T) -> Option<St> {
        if self.bv_width(lhs) != 1 {
            return None;
        }
        let (mut lhs, mut rhs) = (lhs, rhs);
        if self.bv_num(lhs).is_some() {
            core::mem::swap(&mut lhs, &mut rhs);
        }
        let (v, _) = self.bv_num(rhs)?;
        if self.bv_num(lhs).is_some() {
            return Some(St::Done(self.mk_bool(lhs == rhs)));
        }
        if let Some((a, b, c)) = self.is_ite(lhs) {
            let e1 = self.mk_eq_rw(b, rhs);
            let e2 = self.mk_eq_rw(c, rhs);
            let r = match self.bool_ite(a, e1, e2) {
                Some(St::Done(r)) | Some(St::Rw(r, _)) => r,
                None => self.mk_ite(a, e1, e2),
            };
            return Some(St::Rw(r, 2));
        }
        if self.is_bvop(lhs, BvOp::Not) {
            let a = self.arg(lhs, 0);
            let n = self.mk_bv(&(&Int::from(1) - &v), 1);
            return Some(St::Rw(self.mk_eq(a, n), 1));
        }
        let is_one = v.is_one();
        if self.is_bvop(lhs, BvOp::Or) || self.is_bvop(lhs, BvOp::Xor) {
            let bit1 = if is_one {
                rhs
            } else {
                self.mk_bv(&Int::from(1), 1)
            };
            let kids = self.nodes[lhs].args.clone();
            let eqs: Vec<T> = kids.iter().map(|&k| self.mk_eq(k, bit1)).collect();
            let r = if self.is_bvop(lhs, BvOp::Or) {
                self.mk_or_app(eqs)
            } else {
                let mut acc = eqs[0];
                for &e in &eqs[1..] {
                    acc = self.mk(Op::Xor, vec![acc, e]);
                }
                acc
            };
            if is_one {
                return Some(St::Rw(r, 2));
            }
            return Some(St::Rw(self.mk_not(r), 3));
        }
        None
    }

    /// `c` has a multiplicative inverse modulo `2^w`: it, else `None`.
    fn mult_inverse(c: &Int, w: u32) -> Option<Int> {
        if !c.bit(0) {
            return None;
        }
        let m = pow2(w);
        // Newton iteration on odd c: x ← x(2 − cx) doubles the correct bits.
        let mut x = Int::from(1);
        for _ in 0..8 {
            let cx = norm(&(c * &x), w);
            x = norm(&(&x * &(&Int::from(2) - &cx)), w);
        }
        debug_assert!(norm(&(c * &x), w).is_one() || m.is_zero());
        Some(x)
    }

    /// `is_add_mul_const`: a sum of numerals and `(bvmul c x)` terms.
    fn is_add_mul_const(&self, e: T) -> bool {
        self.is_bvop(e, BvOp::Add)
            && self.nodes[e].args.iter().all(|&a| {
                self.bv_num(a).is_some()
                    || (self.is_bvop(a, BvOp::Mul)
                        && self.nodes[a].args.len() == 2
                        && self.bv_num(self.arg(a, 0)).is_some())
            })
    }

    /// `bv_rewriter::mk_mul_eq`.
    fn mul_eq(&mut self, lhs: T, rhs: T) -> Option<St> {
        let sz = self.bv_width(lhs);
        if self.is_bvop(lhs, BvOp::Mul)
            && self.nodes[lhs].args.len() == 2
            && let Some((cv, _)) = self.bv_num(self.arg(lhs, 0))
            && let Some(cinv) = Self::mult_inverse(&cv, sz)
        {
            let x = self.arg(lhs, 1);
            if let Some((rv, _)) = self.bv_num(rhs) {
                let n = self.mk_bv(&(&cinv * &rv), sz);
                return Some(St::Rw(self.mk_eq(x, n), 1));
            }
            if self.is_bvop(rhs, BvOp::Mul)
                && self.nodes[rhs].args.len() == 2
                && let Some((c2, _)) = self.bv_num(self.arg(rhs, 0))
            {
                let x2 = self.arg(rhs, 1);
                let nc2 = norm(&(&cinv * &c2), sz);
                let r = if nc2.is_one() {
                    self.mk_eq(x, x2)
                } else {
                    let k = self.mk_bv(&nc2, sz);
                    let m = self.bvop(BvOp::Mul, vec![k, x2]);
                    self.mk_eq(x, m)
                };
                return Some(St::Rw(r, 1));
            }
            if self.is_add_mul_const(rhs) {
                let k = self.mk_bv(&cinv, sz);
                let m = self.bvop(BvOp::Mul, vec![k, rhs]);
                return Some(St::Rw(self.mk_eq(x, m), 2));
            }
        }
        if let Some((cv, _)) = self.bv_num(lhs)
            && self.is_add_mul_const(rhs)
        {
            let found = self.nodes[rhs].args.iter().find_map(|&a| {
                if self.is_bvop(a, BvOp::Mul) && self.nodes[a].args.len() == 2 {
                    let (c2, _) = self.bv_num(self.arg(a, 0))?;
                    Self::mult_inverse(&c2, sz)
                } else {
                    None
                }
            });
            if let Some(c2inv) = found {
                let l = self.mk_bv(&(&c2inv * &cv), sz);
                let k = self.mk_bv(&c2inv, sz);
                let m = self.bvop(BvOp::Mul, vec![k, rhs]);
                return Some(St::Rw(self.mk_eq(l, m), 3));
            }
        }
        None
    }

    /// `isolate_term`: `c = t1 + t2` → `t1 = c - t2`.
    fn isolate_term(&mut self, lhs: T, rhs: T) -> Option<T> {
        let (mut lhs, mut rhs) = (lhs, rhs);
        if self.bv_num(lhs).is_none() || !self.is_bvop(rhs, BvOp::Add) {
            core::mem::swap(&mut lhs, &mut rhs);
        }
        if self.bv_num(lhs).is_none() || !self.is_bvop(rhs, BvOp::Add) {
            return None;
        }
        let kids = self.nodes[rhs].args.clone();
        let t1 = kids[0];
        let t2 = if kids.len() > 2 {
            self.bvop(BvOp::Add, kids[1..].to_vec())
        } else {
            kids[1]
        };
        let minus_one_times = self.is_bvop(t1, BvOp::Mul)
            && self.nodes[t1].args.len() == 2
            && self
                .bv_num(self.arg(t1, 0))
                .is_some_and(|(v, w)| v == &pow2(w) - &Int::from(1));
        Some(if minus_one_times {
            let d = self.bvop(BvOp::Sub, vec![lhs, t1]);
            self.mk_eq(t2, d)
        } else {
            let d = self.bvop(BvOp::Sub, vec![lhs, t2]);
            self.mk_eq(t1, d)
        })
    }

    fn is_concat_split_target(&self, t: T) -> bool {
        self.is_bvop(t, BvOp::Concat) || self.bv_num(t).is_some() || self.is_bvop(t, BvOp::Or)
    }

    fn is_concat_target(&self, l: T, r: T) -> bool {
        (self.is_bvop(l, BvOp::Concat) && self.is_concat_split_target(r))
            || (self.is_bvop(r, BvOp::Concat) && self.is_concat_split_target(l))
    }

    /// `bv_rewriter::mk_eq_concat`.
    fn eq_concat(&mut self, lhs: T, rhs: T) -> St {
        let a1 = if self.is_bvop(lhs, BvOp::Concat) {
            self.nodes[lhs].args.clone()
        } else {
            vec![lhs]
        };
        let a2 = if self.is_bvop(rhs, BvOp::Concat) {
            self.nodes[rhs].args.clone()
        } else {
            vec![rhs]
        };
        let mut eqs = Vec::new();
        let (mut low1, mut low2) = (0u32, 0u32);
        let (mut i1, mut i2) = (a1.len(), a2.len());
        while i1 > 0 && i2 > 0 {
            let (x, y) = (a1[i1 - 1], a2[i2 - 1]);
            let (sz1, sz2) = (self.bv_width(x), self.bv_width(y));
            let (rsz1, rsz2) = (sz1 - low1, sz2 - low2);
            if rsz1 == rsz2 {
                let e1 = self.mk_extract(sz1 - 1, low1, x);
                let e2 = self.mk_extract(sz2 - 1, low2, y);
                eqs.push(self.mk_eq(e1, e2));
                low1 = 0;
                low2 = 0;
                i1 -= 1;
                i2 -= 1;
            } else if rsz1 < rsz2 {
                let e1 = self.mk_extract(sz1 - 1, low1, x);
                let e2 = self.mk_extract(rsz1 + low2 - 1, low2, y);
                eqs.push(self.mk_eq(e1, e2));
                low1 = 0;
                low2 += rsz1;
                i1 -= 1;
            } else {
                let e1 = self.mk_extract(rsz2 + low1 - 1, low1, x);
                let e2 = self.mk_extract(sz2 - 1, low2, y);
                eqs.push(self.mk_eq(e1, e2));
                low1 += rsz2;
                low2 = 0;
                i2 -= 1;
            }
        }
        St::Rw(self.mk_and_app(eqs), 3)
    }
}

/// `k` with `v = 2^k`, if `v` is a power of two.
fn power_of_two(v: &Int) -> Option<u32> {
    if v.is_zero() || v.is_negative() {
        return None;
    }
    let mut k = 0u32;
    let mut x = v.clone();
    while !x.bit(0) {
        x = x.div_floor(&Int::from(2));
        k += 1;
    }
    x.is_one().then_some(k)
}
