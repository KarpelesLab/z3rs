//! String-valued user functions in string constraints, by purification: each
//! application `g(t…)` of a user function whose range is `String` becomes a
//! fresh string constant, with Ackermann's congruence implications between
//! two applications of the same function (`t… = u… → k₁ = k₂`). The purified
//! problem is equisatisfiable and lies in the string solver's fragment; its
//! model gives each application a string literal, from which `g`'s
//! interpretation is read (z3's string solver treats such applications as
//! string variables the same way).

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::String;
use alloc::vec::Vec;

use super::{Context, Model, SmtResult};
use crate::ast::AstId;

impl Context {
    /// Decide the assertions after purifying their String-valued user-function
    /// applications. `None` when there are none, a universal is present, or
    /// the purified problem stays undecided.
    pub(super) fn check_sat_str_uf(&mut self) -> Option<(SmtResult, Option<Model>)> {
        if self.str_uf_active || !self.universals.is_empty() {
            return None;
        }
        let string_sort = self.string_sort?;
        let user: BTreeSet<AstId> = self.funcs.values().copied().collect();
        // The applications, arguments before the applications containing them.
        let mut apps: Vec<AstId> = Vec::new();
        for &a in &self.assertions {
            for t in self.m.postorder(a) {
                if self.m.is_quantifier(t) || self.m.is_var(t) {
                    return None;
                }
                if let Some(app) = self.m.app(t)
                    && !app.args.is_empty()
                    && user.contains(&app.decl)
                    && self.m.get_sort(t) == string_sort
                    && !apps.contains(&t)
                {
                    apps.push(t);
                }
            }
        }
        if apps.is_empty() {
            return None;
        }
        let mut pairs: Vec<(AstId, AstId)> = Vec::new();
        // (application, its constant, its purified arguments)
        let mut purified: Vec<(AstId, AstId, Vec<AstId>)> = Vec::new();
        for &t in &apps {
            let args: Vec<AstId> = self.m.app_args(t).to_vec();
            let pargs: Vec<AstId> = args
                .iter()
                .map(|&x| crate::rewriter::substitute(&mut self.m, x, &pairs))
                .collect();
            let k = self.fresh_const(string_sort);
            pairs.push((t, k));
            purified.push((t, k, pargs));
        }
        let mut goal: Vec<AstId> = Vec::new();
        for a in self.assertions.clone() {
            goal.push(crate::rewriter::substitute(&mut self.m, a, &pairs));
        }
        for i in 0..purified.len() {
            for j in i + 1..purified.len() {
                let (ti, ki, ai) = &purified[i];
                let (tj, kj, aj) = &purified[j];
                if self.m.app_decl(*ti) != self.m.app_decl(*tj) {
                    continue;
                }
                let (ki, kj, ai, aj) = (*ki, *kj, ai.clone(), aj.clone());
                let eqs: Vec<AstId> = ai
                    .iter()
                    .zip(&aj)
                    .map(|(&x, &y)| self.m.mk_eq(x, y))
                    .collect();
                let same = if eqs.len() == 1 {
                    eqs[0]
                } else {
                    self.m.mk_and(&eqs)
                };
                let keq = self.m.mk_eq(ki, kj);
                goal.push(self.m.mk_implies(same, keq));
            }
        }
        let saved = core::mem::replace(&mut self.assertions, goal);
        self.str_uf_active = true;
        let (r, model) = self.check_sat();
        // The string witness of the purified problem: each constant's literal.
        let (r, model) = self.finish_str_model(r, model, &[]);
        let mut pins: Vec<(AstId, AstId)> = Vec::new();
        let mut vals: BTreeMap<AstId, String> = BTreeMap::new();
        if r == SmtResult::Sat {
            for (t, k, _) in &purified {
                let lit = self
                    .str_witness
                    .iter()
                    .find(|(w, _)| w == k)
                    .map(|&(_, v)| v)
                    .filter(|&v| self.str_value(v).is_some());
                let Some(v) = lit else {
                    pins.clear();
                    break;
                };
                let text: String = self
                    .str_value(v)
                    .unwrap_or_default()
                    .into_iter()
                    .filter_map(char::from_u32)
                    .collect();
                vals.insert(*t, text);
                pins.push((*t, v));
            }
        }
        self.str_uf_active = false;
        self.assertions = saved;
        match r {
            SmtResult::Unsat => Some((SmtResult::Unsat, None)),
            SmtResult::Sat if pins.len() == purified.len() => {
                self.str_witness.extend(pins);
                self.str_uf_vals = vals;
                Some((SmtResult::Sat, model))
            }
            SmtResult::Sat | SmtResult::Unknown => None,
        }
    }
}
