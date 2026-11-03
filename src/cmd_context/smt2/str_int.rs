//! The axioms of `str.to_int` and `str.from_int` (z3's `seq_axioms`
//! `stoi_axiom` / `itos_axiom`), instantiated over the terms of a goal.
//!
//! For `str.to_int s`: its value is at least `-1`, it is `-1` on the empty
//! string, and a non-negative value needs a non-empty `s` whose first
//! character is a digit. For `str.from_int n`: it is empty exactly when `n`
//! is negative, its length is the number of decimal digits of `n`, it is
//! `"0"` for `n = 0` and does not start with `0` otherwise, and its first
//! character is a digit. Both are related to every string literal of the
//! goal they may equal (a literal is the decimal of at most one value) and
//! to the containment atoms that would put a non-digit character into a
//! digit string.

use alloc::collections::BTreeSet;
use alloc::string::String;
use alloc::vec::Vec;

use super::Context;
use crate::ast::AstId;

/// Lengths of `str.from_int` bounded by digit counts up to this many digits.
const MAX_DIGITS: u32 = 9;

impl Context {
    /// The `str.to_int` / `str.from_int` axioms over `present` (the terms of
    /// a goal); the digit literals they introduce are added to `extra_lits`.
    pub(super) fn str_int_axioms(
        &mut self,
        present: &[AstId],
        extra_lits: &mut BTreeSet<AstId>,
    ) -> Vec<AstId> {
        let op_of = |me: &Self, t: AstId| -> Option<&str> {
            if !me.m.is_app(t) || me.m.app_args(t).len() != 1 {
                return None;
            }
            match me.str_op_decls.get(&me.m.app_decl(t)).map(String::as_str) {
                Some("str.to_int" | "str.to-int") => Some("stoi"),
                Some("str.from_int" | "str.from-int") => Some("itos"),
                _ => None,
            }
        };
        let mut stoi: Vec<(AstId, AstId)> = Vec::new();
        let mut itos: Vec<(AstId, AstId)> = Vec::new();
        for &t in present {
            match op_of(self, t) {
                Some("stoi") => stoi.push((t, self.m.app_args(t)[0])),
                Some("itos") => itos.push((t, self.m.app_args(t)[0])),
                _ => {}
            }
        }
        if stoi.is_empty() && itos.is_empty() {
            return Vec::new();
        }
        let lits: Vec<(AstId, Vec<u32>)> = present
            .iter()
            .filter_map(|&t| self.str_value(t).map(|v| (t, v)))
            .collect();
        let digit_value = |v: &[u32]| -> Option<i64> {
            if v.is_empty() || v.len() > 18 || !v.iter().all(|&c| (0x30..=0x39).contains(&c)) {
                return None;
            }
            Some(
                v.iter()
                    .fold(0i64, |acc, &c| acc * 10 + i64::from(c - 0x30)),
            )
        };
        let mut ax = Vec::new();
        let zero = self.m.mk_int(0);
        let neg1 = self.m.mk_int(-1);
        let empty = self.mk_str_lit("");
        extra_lits.insert(empty);
        let digits: Vec<AstId> = (0..10u32)
            .map(|d| {
                let l = self.mk_str_lit(&alloc::format!("{d}"));
                extra_lits.insert(l);
                l
            })
            .collect();
        let lenf = self.str_len_fn();
        // The first (last) character of `s` is a digit, when a literal end
        // of `s` decides it. (Not as `str.at` atoms: opaque terms that would
        // keep a concrete candidate from confirming a model.)
        let end_digit = |me: &mut Self, s: AstId, first: bool| -> Option<AstId> {
            let c = me.str_end_char(s, first)?;
            Some(me.mk_bool((0x30..=0x39).contains(&c)))
        };
        for &(t, s) in &stoi {
            ax.push(self.m.mk_ge(t, neg1));
            let is_empty = self.m.mk_eq(s, empty);
            let minus = self.m.mk_eq(t, neg1);
            ax.push(self.m.mk_implies(is_empty, minus));
            let nonneg = self.m.mk_ge(t, zero);
            let len = self.m.mk_app(lenf, &[s]);
            let one = self.m.mk_int(1);
            let long = self.m.mk_ge(len, one);
            ax.push(self.m.mk_implies(nonneg, long));
            if let Some(fd) = end_digit(self, s, true) {
                ax.push(self.m.mk_implies(nonneg, fd));
            }
            // A literal is the decimal of one value (or of none: -1).
            for (l, v) in &lits {
                let val = match digit_value(v) {
                    Some(k) => self.m.mk_int(k),
                    None if v.iter().all(|&c| (0x30..=0x39).contains(&c)) && !v.is_empty() => {
                        continue; // too long to evaluate here
                    }
                    None => neg1,
                };
                let eq = self.m.mk_eq(s, *l);
                let tv = self.m.mk_eq(t, val);
                ax.push(self.m.mk_implies(eq, tv));
            }
        }
        for &(e, n) in &itos {
            let is_empty = self.m.mk_eq(e, empty);
            let neg = self.m.mk_lt(n, zero);
            ax.push(self.m.mk_eq(is_empty, neg));
            let len = self.m.mk_app(lenf, &[e]);
            // The number of digits.
            let mut p: i64 = 1;
            for i in 1..=MAX_DIGITS {
                p *= 10;
                let pi = self.m.mk_int(p);
                let below = self.m.mk_lt(n, pi);
                let ik = self.m.mk_int(i64::from(i));
                let short = self.m.mk_le(len, ik);
                ax.push(self.m.mk_implies(below, short));
                let ik1 = self.m.mk_int(i64::from(i) + 1);
                let long = self.m.mk_ge(len, ik1);
                let above = self.m.mk_ge(n, pi);
                ax.push(self.m.mk_implies(above, long));
            }
            let nonneg = self.m.mk_ge(n, zero);
            let one = self.m.mk_int(1);
            let long = self.m.mk_ge(len, one);
            ax.push(self.m.mk_implies(nonneg, long));
            let is_zero = self.m.mk_eq(n, zero);
            let e0 = self.m.mk_eq(e, digits[0]);
            ax.push(self.m.mk_eq(is_zero, e0));
            // Its first and last characters are digits: so are those of a
            // term it equals (a concatenation with a literal end decides them).
            for &q in present {
                if !self.m.is_eq(q) {
                    continue;
                }
                let (l, r) = (self.m.app_args(q)[0], self.m.app_args(q)[1]);
                let other = if l == e {
                    r
                } else if r == e {
                    l
                } else {
                    continue;
                };
                let both = self.m.mk_and(&[q, nonneg]);
                if let Some(fd) = end_digit(self, other, true) {
                    ax.push(self.m.mk_implies(both, fd));
                }
                if let Some(ld) = end_digit(self, other, false) {
                    ax.push(self.m.mk_implies(both, ld));
                }
            }
            // A literal it may equal: the canonical decimal of one value.
            for (l, v) in &lits {
                let eq = self.m.mk_eq(e, *l);
                if v.is_empty() {
                    continue;
                }
                let canonical = v.len() == 1 || v[0] != 0x30;
                match digit_value(v).filter(|_| canonical) {
                    Some(k) => {
                        let kv = self.m.mk_int(k);
                        let nk = self.m.mk_eq(n, kv);
                        ax.push(self.m.mk_eq(eq, nk));
                    }
                    None if canonical && v.iter().all(|&c| (0x30..=0x39).contains(&c)) => {}
                    None => ax.push(self.m.mk_not(eq)),
                }
            }
        }
        // A digit string contains no non-digit character: the containment
        // atoms of the goal that would put one into `str.from_int n` (or
        // into an `s` whose `str.to_int` is non-negative) fail.
        let non_digit = |v: &[u32]| v.iter().any(|&c| !(0x30..=0x39).contains(&c));
        for &p in present {
            if !self.m.is_app(p) || self.m.app_args(p).len() != 2 {
                continue;
            }
            let (x, l) = match self
                .str_op_decls
                .get(&self.m.app_decl(p))
                .map(String::as_str)
            {
                Some("str.contains") => (self.m.app_args(p)[0], self.m.app_args(p)[1]),
                Some("str.prefixof" | "str.suffixof") => {
                    (self.m.app_args(p)[1], self.m.app_args(p)[0])
                }
                _ => continue,
            };
            if !self.str_value(l).is_some_and(|v| non_digit(&v)) {
                continue;
            }
            if itos.iter().any(|&(e, _)| e == x) {
                ax.push(self.m.mk_not(p));
            }
            for &(t, s) in &stoi {
                if s == x {
                    let nonneg = self.m.mk_ge(t, zero);
                    let np = self.m.mk_not(p);
                    ax.push(self.m.mk_implies(nonneg, np));
                }
            }
        }
        ax
    }

    /// The first (`first`) or last character of the string term `s` when a
    /// literal fixes it: `s` a non-empty literal, or a concatenation whose
    /// first (last) part is one.
    fn str_end_char(&self, s: AstId, first: bool) -> Option<u32> {
        let mut t = s;
        loop {
            if let Some(v) = self.str_value(t) {
                return if first { v.first() } else { v.last() }.copied();
            }
            if !self.m.is_app(t)
                || self
                    .str_op_decls
                    .get(&self.m.app_decl(t))
                    .map(String::as_str)
                    != Some("str.++")
            {
                return None;
            }
            let args = self.m.app_args(t);
            t = if first { *args.first()? } else { *args.last()? };
            if self.str_value(t).is_some_and(|v| v.is_empty()) {
                return None;
            }
        }
    }
}
