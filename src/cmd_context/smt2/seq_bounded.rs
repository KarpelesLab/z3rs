//! Sequence variables of bounded length, decided by their elements.
//!
//! When the assertions bound the length of every sequence variable to a
//! small range (`lo <= seq.len s <= hi` at the top level, or a bound the
//! solver proves by refuting every longer value), each combination
//! of lengths is tried: a variable of length `n` becomes the concrete
//! sequence of `n` fresh element constants, the sequence operations fold
//! over it (reads at symbolic positions by cases, out-of-range reads through
//! z3's `seq.nth_u`), and the element problem is decided. Some combination
//! `sat` gives a model (the elements' values, confirmed on the original
//! assertions); every combination `unsat` refutes the goal, the lengths being
//! exhausted. A variable with no bound is tried at short lengths only, for a
//! model: then only `sat` is concluded.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec::Vec;

use super::{Context, Model, SmtResult, Value};
use crate::ast::AstId;
use crate::ast::arith::ArithOp;

/// The most length combinations tried.
const MAX_COMBOS: usize = 64;
/// The longest sequence built.
const MAX_LEN: i64 = 8;
/// The length bound tried for a variable without an asserted one.
const MAX_DERIVED: i64 = 4;
/// The longest value tried for a variable without a length bound (for a
/// model only).
const MAX_SHORT: i64 = 2;

impl Context {
    /// Decide goals whose sequence variables all have small length bounds
    /// (or find a model with short values). `None` outside that fragment or
    /// when undecided.
    pub(super) fn check_sat_seq_bounded(&mut self) -> Option<(SmtResult, Option<Model>)> {
        if self.seq_sorts.is_empty() {
            return None;
        }
        let roots = self.assertions.clone();
        let universals = self.universals.clone();
        let mut all_roots = roots.clone();
        all_roots.extend(universals.iter().map(|(_, b)| *b));
        let mut vars: Vec<AstId> = Vec::new();
        for t in self.m.postorder_many(&all_roots) {
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
        // Top-level length bounds.
        let mut bounds: BTreeMap<AstId, (i64, i64)> =
            vars.iter().map(|&v| (v, (0, i64::MAX))).collect();
        for &a in &roots {
            let Some((v, lo, hi)) = self.seq_len_bound(a) else {
                continue;
            };
            if let Some(b) = bounds.get_mut(&v) {
                b.0 = b.0.max(lo);
                b.1 = b.1.min(hi);
            }
        }
        // A variable without an asserted bound may still have one: when the
        // assertions refute every longer value (the solver's length
        // reasoning), the bound is proven.
        for v in vars.clone() {
            let b = bounds[&v];
            if b.1 <= MAX_LEN {
                continue;
            }
            if b.0 > MAX_DERIVED {
                continue;
            }
            let len = self.seq_op("seq.len", &[v]).ok()?;
            let k = self.m.mk_int(MAX_DERIVED);
            let longer = self.m.mk_gt(len, k);
            let mut goal = roots.clone();
            goal.push(longer);
            let saved = core::mem::replace(&mut self.assertions, goal);
            let (r, _) = self.check_sat_split();
            self.assertions = saved;
            if r == SmtResult::Unsat {
                bounds.get_mut(&v)?.1 = MAX_DERIVED;
            }
        }
        let mut ranges: Vec<(AstId, i64, i64)> = Vec::new();
        let mut exact = true;
        for (&v, &(lo, hi)) in &bounds {
            if hi < lo {
                return Some((SmtResult::Unsat, None));
            }
            if hi > MAX_LEN {
                // Unbounded: only short values are tried, for a model.
                if lo > MAX_SHORT {
                    return None;
                }
                exact = false;
                ranges.push((v, lo, MAX_SHORT));
            } else {
                ranges.push((v, lo, hi));
            }
        }
        let combos = ranges.iter().fold(1usize, |c, &(_, lo, hi)| {
            c.saturating_mul((hi - lo + 1) as usize)
        });
        if combos > MAX_COMBOS {
            return None;
        }
        let r = self.seq_bounded_search(&roots, &universals, &vars, &ranges)?;
        (exact || r.0 == SmtResult::Sat).then_some(r)
    }

    /// Try every combination of the lengths `ranges` of the sequence
    /// variables `vars`: `sat` (a confirmed model) at the first combination
    /// that has one, `unsat` when none has, `None` when one is undecided.
    #[allow(clippy::type_complexity)]
    fn seq_bounded_search(
        &mut self,
        roots: &[AstId],
        universals: &[(Vec<AstId>, AstId)],
        vars: &[AstId],
        ranges: &[(AstId, i64, i64)],
    ) -> Option<(SmtResult, Option<Model>)> {
        let combos = ranges.iter().fold(1usize, |c, &(_, lo, hi)| {
            c.saturating_mul((hi - lo + 1) as usize)
        });
        let mut undecided = false;
        for idx in 0..combos {
            let mut rem = idx;
            let mut pairs: Vec<(AstId, AstId)> = Vec::new();
            let mut elems: Vec<(AstId, Vec<AstId>)> = Vec::new();
            for &(v, lo, hi) in ranges {
                let span = (hi - lo + 1) as usize;
                let n = lo as usize + rem % span;
                rem /= span;
                let sort = self.m.get_sort(v);
                let es = self.seq_elem_sort(sort)?;
                let xs: Vec<AstId> = (0..n).map(|_| self.fresh_const(es)).collect();
                let s = self.mk_seq_sorted(sort, xs.clone());
                pairs.push((v, s));
                elems.push((v, xs));
            }
            let mut goal = Vec::with_capacity(roots.len());
            let mut memo = BTreeMap::new();
            for &a in roots {
                let g = crate::rewriter::substitute(&mut self.m, a, &pairs);
                // Reads at symbolic positions of the now concrete sequences
                // by cases.
                let g = self.refold_str_markers_rec(g, &mut memo);
                goal.push(crate::rewriter::simplify(&mut self.m, g));
            }
            if goal.iter().any(|&g| self.m.is_false(g)) {
                continue;
            }
            let mut univ = Vec::with_capacity(universals.len());
            for (vs, b) in universals {
                let g = crate::rewriter::substitute(&mut self.m, *b, &pairs);
                let g = self.refold_str_markers(g, &mut memo);
                univ.push((vs.clone(), crate::rewriter::simplify(&mut self.m, g)));
            }
            // The folded goal must be free of the sequence variables.
            let left: BTreeSet<AstId> = vars.iter().copied().collect();
            let mut folded = goal.clone();
            folded.extend(univ.iter().map(|(_, b)| *b));
            if self
                .m
                .postorder_many(&folded)
                .iter()
                .any(|t| left.contains(t))
            {
                return None;
            }
            let saved = core::mem::replace(&mut self.assertions, goal);
            let saved_u = core::mem::replace(&mut self.universals, univ);
            let (r, model) = self.check_sat_split();
            self.universals = saved_u;
            let found = match (r, model) {
                (SmtResult::Sat, Some(mut md)) => self.seq_bounded_pins(&elems, &mut md),
                _ => None,
            };
            self.assertions = saved;
            match r {
                SmtResult::Unsat => {}
                SmtResult::Unknown => undecided = true,
                SmtResult::Sat => {
                    let Some(pins) = found else {
                        undecided = true;
                        continue;
                    };
                    if let Some(res) = self.seq_bounded_confirm(&pins) {
                        return Some(res);
                    }
                    undecided = true;
                }
            }
        }
        if undecided {
            None
        } else {
            Some((SmtResult::Unsat, None))
        }
    }

    /// `lo <= seq.len v`, `seq.len v <= hi`, `seq.len v = k` (and the strict
    /// and flipped forms) as `(v, lo, hi)`.
    fn seq_len_bound(&self, a: AstId) -> Option<(AstId, i64, i64)> {
        let app = self.m.app(a)?;
        if app.args.len() != 2 {
            return None;
        }
        let len_of = |t: AstId| -> Option<AstId> {
            let ap = self.m.app(t)?;
            (self.seq_len_decls.contains(&ap.decl) && ap.args.len() == 1).then(|| ap.args[0])
        };
        let num = |t: AstId| self.m.as_numeral(t).and_then(|r| r.to_i64());
        let (x, y) = (app.args[0], app.args[1]);
        if self.m.is_eq(a) {
            if let (Some(v), Some(k)) = (len_of(x), num(y)) {
                return Some((v, k, k));
            }
            if let (Some(v), Some(k)) = (len_of(y), num(x)) {
                return Some((v, k, k));
            }
            return None;
        }
        let op = self.m.arith_op(a)?;
        // `len v OP k`
        if let (Some(v), Some(k)) = (len_of(x), num(y)) {
            return match op {
                ArithOp::Le => Some((v, 0, k)),
                ArithOp::Lt => Some((v, 0, k - 1)),
                ArithOp::Ge => Some((v, k, i64::MAX)),
                ArithOp::Gt => Some((v, k + 1, i64::MAX)),
                _ => None,
            };
        }
        // `k OP len v`
        if let (Some(v), Some(k)) = (len_of(y), num(x)) {
            return match op {
                ArithOp::Le => Some((v, k, i64::MAX)),
                ArithOp::Lt => Some((v, k + 1, i64::MAX)),
                ArithOp::Ge => Some((v, 0, k)),
                ArithOp::Gt => Some((v, 0, k - 1)),
                _ => None,
            };
        }
        None
    }

    /// Each sequence variable's value (its elements' values in `md`) and the
    /// values of the other user constants, as pins.
    fn seq_bounded_pins(
        &mut self,
        elems: &[(AstId, Vec<AstId>)],
        md: &mut Model,
    ) -> Option<Vec<(AstId, AstId)>> {
        let lit = |ctx: &mut Self, md: &mut Model, t: AstId| -> Option<AstId> {
            Some(match md.eval(&ctx.m, t) {
                Value::Bool(b) => ctx.mk_bool(b),
                Value::Num(r, is_int) => ctx.m.mk_numeral(r, is_int),
                Value::Bv(v, w) => ctx.m.mk_bv_numeral(v, w),
                Value::Uninterp(..) => return None,
            })
        };
        let mut pins = Vec::new();
        for (v, xs) in elems {
            let mut vals = Vec::with_capacity(xs.len());
            for &x in xs {
                vals.push(lit(self, md, x)?);
            }
            let sort = self.m.get_sort(*v);
            let s = self.mk_seq_sorted(sort, vals);
            pins.push((*v, s));
        }
        let roots = self.assertions.clone();
        for t in self.m.postorder_many(&roots) {
            if self.m.is_uninterp_const(t)
                && self.is_user_constant_or_bits(t)
                && self.seq_elem_sort(self.m.get_sort(t)).is_none()
            {
                let v = lit(self, md, t)?;
                pins.push((t, v));
            }
        }
        Some(pins)
    }

    /// Check the original assertions under `pins` (every one folding to
    /// `true`) and return the pinned model.
    fn seq_bounded_confirm(
        &mut self,
        pins: &[(AstId, AstId)],
    ) -> Option<(SmtResult, Option<Model>)> {
        let mut memo = BTreeMap::new();
        let mut checked = self.assertions.clone();
        checked.extend(self.universals.iter().map(|(_, b)| *b));
        for a in checked {
            let g = crate::rewriter::substitute(&mut self.m, a, pins);
            let g = self.refold_str_markers(g, &mut memo);
            let g = crate::rewriter::simplify(&mut self.m, g);
            if !self.m.is_true(g) {
                // Out-of-range reads stay open: let the solver confirm.
                let eqs: Vec<AstId> = pins.iter().map(|&(v, s)| self.m.mk_eq(v, s)).collect();
                let mut goal = self.assertions.clone();
                goal.extend(eqs);
                let saved = core::mem::replace(&mut self.assertions, goal);
                let (r, m) = self.check_sat_split();
                self.assertions = saved;
                return (r == SmtResult::Sat).then_some((SmtResult::Sat, m));
            }
        }
        let eqs: Vec<AstId> = pins.iter().map(|&(v, s)| self.m.mk_eq(v, s)).collect();
        let saved = core::mem::replace(&mut self.assertions, eqs);
        let saved_u = core::mem::take(&mut self.universals);
        let (r, m) = self.check_sat_split();
        self.universals = saved_u;
        self.assertions = saved;
        (r == SmtResult::Sat).then_some((SmtResult::Sat, m))
    }
}
