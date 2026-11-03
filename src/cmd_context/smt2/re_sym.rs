//! Membership in a regex over symbolic strings, rewritten into string
//! constraints.
//!
//! A regex built with `str.to_re t` of a non-literal `t` has no automaton,
//! but its top-level structure unfolds into equivalent word constraints,
//! as z3's sequence rewriter and the symbolic derivatives of its regex
//! solver do:
//!
//! - `s ∈ R₁ ∪ R₂` is `s ∈ R₁ ∨ s ∈ R₂`, `∩` a conjunction, `comp` a
//!   negation, `re.diff` both, `re.opt R` is `s = "" ∨ s ∈ R`;
//! - `s ∈ to_re(t) · R` is `t ⊑ s ∧ s[|t|..] ∈ R` (`str.prefixof`), and a
//!   leading part whose words all have one length `k` reads `s[..k]`; the
//!   same at the end (`str.suffixof`);
//! - a bounded loop is the union of its finitely many powers;
//! - the empty word is in every star.
//!
//! Every step is an equivalence, so the rewritten membership may be used
//! wherever the original occurs; what does not unfold (a star over a
//! symbolic regex) stays an opaque membership.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec::Vec;

use super::{Context, Model, SmtResult};
use crate::ast::AstId;

/// The longest bounded loop unfolded into its powers.
const MAX_LOOP: usize = 3;

impl Context {
    /// Decide the assertions with each string constant an asserted equality
    /// `x = "w"` fixes replaced by `"w"` (z3's `solve-eqs`), when a regex
    /// over symbolic strings mentions such a constant: the regex then has a
    /// structure (`str.to_re "w"`) and its memberships fold or reach the
    /// regex procedures. Equivalent: the equalities are kept. `None` when no
    /// such regex mentions a fixed constant.
    pub(super) fn check_sat_str_fixed(&mut self) -> Option<(SmtResult, Option<Model>)> {
        if self.regex_recipe.is_empty() || !self.universals.is_empty() {
            return None;
        }
        let mut conjuncts: Vec<AstId> = Vec::new();
        let mut stack: Vec<AstId> = self.assertions.iter().rev().copied().collect();
        while let Some(t) = stack.pop() {
            if self.m.is_and(t) {
                stack.extend(self.m.app_args(t).iter().rev().copied());
            } else {
                conjuncts.push(t);
            }
        }
        let mut fixed: BTreeMap<AstId, AstId> = BTreeMap::new();
        for &t in &conjuncts {
            if !self.m.is_eq(t) {
                continue;
            }
            let (l, r) = (self.m.app_args(t)[0], self.m.app_args(t)[1]);
            for (x, w) in [(l, r), (r, l)] {
                if self.str_value(w).is_some()
                    && self.string_sort == Some(self.m.get_sort(x))
                    && self.m.is_uninterp_const(x)
                    && self.is_user_constant_or_bits(x)
                {
                    fixed.entry(x).or_insert(w);
                }
            }
        }
        if fixed.is_empty() {
            return None;
        }
        // A symbolic regex (its recipe's arguments) over a fixed constant.
        let mut seen = BTreeSet::new();
        let mut todo: Vec<AstId> = self
            .m
            .postorder_many(&self.assertions)
            .into_iter()
            .filter(|t| self.regex_recipe.contains_key(t))
            .collect();
        let mut hit = false;
        while let Some(r) = todo.pop() {
            if hit || !seen.insert(r) {
                continue;
            }
            let Some((_, args, _)) = self.regex_recipe.get(&r).cloned() else {
                continue;
            };
            for a in args {
                if self.regex_recipe.contains_key(&a) {
                    todo.push(a);
                } else if self.m.postorder(a).iter().any(|u| fixed.contains_key(u)) {
                    hit = true;
                }
            }
        }
        if !hit {
            return None;
        }
        let pairs: Vec<(AstId, AstId)> = fixed.iter().map(|(&x, &w)| (x, w)).collect();
        let mut goal: Vec<AstId> = Vec::new();
        for a in self.assertions.clone() {
            let b = self.subst_seq(a, &pairs);
            let mut memo = BTreeMap::new();
            let b = self.refold_str_markers(b, &mut memo);
            goal.push(crate::rewriter::simplify(&mut self.m, b));
        }
        for &(x, w) in &pairs {
            goal.push(self.m.mk_eq(x, w));
        }
        let saved = core::mem::replace(&mut self.assertions, goal);
        let r = self.check_sat();
        self.assertions = saved;
        Some(r)
    }

    /// `(str.in_re s r)` rewritten into string constraints when `r` is a
    /// regex over symbolic strings whose structure unfolds (see the module
    /// documentation); `None` otherwise.
    pub(super) fn in_re_symbolic(&mut self, s: AstId, r: AstId) -> Option<AstId> {
        let (op, args, idx) = self.regex_recipe.get(&r).cloned()?;
        let mem = |me: &mut Self, s: AstId, r: AstId| me.string_op("str.in_re", &[s, r]).ok();
        match op.as_str() {
            "re.union" => {
                let mut ds = Vec::with_capacity(args.len());
                for a in args {
                    ds.push(mem(self, s, a)?);
                }
                Some(self.m.mk_or(&ds))
            }
            "re.inter" => {
                let mut cs = Vec::with_capacity(args.len());
                for a in args {
                    cs.push(mem(self, s, a)?);
                }
                Some(self.m.mk_and(&cs))
            }
            "re.comp" if args.len() == 1 => {
                let m = mem(self, s, args[0])?;
                Some(self.m.mk_not(m))
            }
            "re.diff" if args.len() == 2 => {
                let a = mem(self, s, args[0])?;
                let b = mem(self, s, args[1])?;
                let nb = self.m.mk_not(b);
                Some(self.m.mk_and(&[a, nb]))
            }
            "re.opt" if args.len() == 1 => {
                let empty = self.mk_str_lit("");
                let e = self.m.mk_eq(s, empty);
                let m = mem(self, s, args[0])?;
                Some(self.m.mk_or(&[e, m]))
            }
            "re.loop" if args.len() == 1 => {
                let lo = *idx.first()?;
                let Some(&hi) = idx.get(1) else {
                    // `lo` or more: `lo` copies, then the star.
                    if lo == 0 || lo > MAX_LOOP {
                        return None;
                    }
                    let mut parts = alloc::vec![args[0]; lo];
                    parts.push(self.regex_op("re.*", &args).ok()?);
                    return self.in_re_concat(s, &parts);
                };
                if hi < lo || hi > MAX_LOOP {
                    return None;
                }
                let mut ds = Vec::new();
                for k in lo..=hi {
                    ds.push(match k {
                        0 => {
                            let empty = self.mk_str_lit("");
                            self.m.mk_eq(s, empty)
                        }
                        1 => mem(self, s, args[0])?,
                        _ => {
                            let pow = self.regex_op("re.++", &alloc::vec![args[0]; k]).ok()?;
                            mem(self, s, pow)?
                        }
                    });
                }
                Some(if ds.len() == 1 {
                    ds[0]
                } else {
                    self.m.mk_or(&ds)
                })
            }
            "re.+" if args.len() == 1 => {
                let star = self.regex_op("re.*", &args).ok()?;
                self.in_re_concat(s, &[args[0], star])
            }
            // The empty word is in every star (a candidate `s = ""` of a
            // witness search folds); other words keep the membership opaque.
            "re.*" if args.len() == 1 && self.str_value(s).is_some_and(|w| w.is_empty()) => {
                Some(self.m.mk_true())
            }
            "re.++" if args.len() >= 2 => self.in_re_concat(s, &args),
            _ => None,
        }
    }

    /// `s ∈ r₁ · … · rₙ` split at a leading or trailing part of known
    /// length: a `str.to_re t` or a regex whose words all have one length.
    fn in_re_concat(&mut self, s: AstId, parts: &[AstId]) -> Option<AstId> {
        let n = parts.len();
        let rest_of = |me: &mut Self, rs: &[AstId]| -> Option<AstId> {
            if rs.len() == 1 {
                Some(rs[0])
            } else {
                me.regex_op("re.++", rs).ok()
            }
        };
        let len_s = self.string_op("str.len", &[s]).ok()?;
        // At the front.
        if let Some(head) = self.re_part_len(parts[0]) {
            let rest = rest_of(self, &parts[1..])?;
            return match head {
                PartLen::Word(t) => {
                    let pre = self.string_op("str.prefixof", &[t, s]).ok()?;
                    let lt = self.string_op("str.len", &[t]).ok()?;
                    let rlen = self.apply("-", alloc::vec![len_s, lt]).ok()?;
                    let tail = self.string_op("str.substr", &[s, lt, rlen]).ok()?;
                    let m = self.string_op("str.in_re", &[tail, rest]).ok()?;
                    Some(self.m.mk_and(&[pre, m]))
                }
                PartLen::Fixed(k) => {
                    let kt = self.m.mk_int(k as i64);
                    let long = self.apply(">=", alloc::vec![len_s, kt]).ok()?;
                    let zero = self.m.mk_int(0);
                    let head = self.string_op("str.substr", &[s, zero, kt]).ok()?;
                    let m1 = self.string_op("str.in_re", &[head, parts[0]]).ok()?;
                    let rlen = self.apply("-", alloc::vec![len_s, kt]).ok()?;
                    let tail = self.string_op("str.substr", &[s, kt, rlen]).ok()?;
                    let m2 = self.string_op("str.in_re", &[tail, rest]).ok()?;
                    Some(self.m.mk_and(&[long, m1, m2]))
                }
            };
        }
        // At the back.
        let last = self.re_part_len(parts[n - 1])?;
        let init = rest_of(self, &parts[..n - 1])?;
        let zero = self.m.mk_int(0);
        match last {
            PartLen::Word(t) => {
                let suf = self.string_op("str.suffixof", &[t, s]).ok()?;
                let lt = self.string_op("str.len", &[t]).ok()?;
                let ilen = self.apply("-", alloc::vec![len_s, lt]).ok()?;
                let front = self.string_op("str.substr", &[s, zero, ilen]).ok()?;
                let m = self.string_op("str.in_re", &[front, init]).ok()?;
                Some(self.m.mk_and(&[suf, m]))
            }
            PartLen::Fixed(k) => {
                let kt = self.m.mk_int(k as i64);
                let long = self.apply(">=", alloc::vec![len_s, kt]).ok()?;
                let ilen = self.apply("-", alloc::vec![len_s, kt]).ok()?;
                let front = self.string_op("str.substr", &[s, zero, ilen]).ok()?;
                let m1 = self.string_op("str.in_re", &[front, init]).ok()?;
                let back = self.string_op("str.substr", &[s, ilen, kt]).ok()?;
                let m2 = self.string_op("str.in_re", &[back, parts[n - 1]]).ok()?;
                Some(self.m.mk_and(&[long, m1, m2]))
            }
        }
    }

    /// How the length of the words of the concatenation part `r` is known:
    /// `str.to_re t` matches exactly `t`; a constant regex may have words of
    /// a single length.
    fn re_part_len(&self, r: AstId) -> Option<PartLen> {
        if let Some(&t) = self.regex_to_re_arg.get(&r) {
            return Some(PartLen::Word(t));
        }
        let re = self.regex_of.get(&r)?;
        let max = re.max_len()?;
        let lens = re.lengths(max)?;
        let mut it = lens.iter().enumerate().filter(|(_, b)| **b).map(|(k, _)| k);
        let k = it.next()?;
        it.next().is_none().then_some(PartLen::Fixed(k))
    }
}

/// The known length of a concatenation part (see
/// [`Context::re_part_len`]).
enum PartLen {
    /// The words are exactly this string term.
    Word(AstId),
    /// Every word has this length.
    Fixed(usize),
}
