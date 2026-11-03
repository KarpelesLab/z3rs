//! Arrays built from variables, `store`, constant arrays, `ite` and
//! `(_ map f)` over an infinite index sort, decided by reduction to their
//! elements (the combinatory array logic decision procedure of de Moura and
//! Bjørner, which z3's array solver implements with its map/const axioms).
//!
//! Only the indices the formula mentions matter: the index terms of its
//! reads and stores, one witness index per array equality, and one default
//! index standing for every other index. An array variable becomes one
//! element variable per index term (equal index terms giving equal
//! elements), a store, constant array, map or `ite` its pointwise value, and
//! an array equality the conjunction of the elementwise equalities at all
//! those indices. The element problem is equisatisfiable: every model of the
//! arrays gives one (each equality atom's witness picks a differing index
//! when the atom is false), and every model of the elements gives arrays
//! that are constant outside the mentioned indices (the default index being
//! apart from them all). A `sat` is confirmed by pinning the arrays to those
//! values and re-deciding the original assertions.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec::Vec;

use super::{Context, Model, SmtResult, Value};
use crate::ast::AstId;

/// The most index terms (with witnesses) handled.
const MAX_INDICES: usize = 24;

struct Cal {
    /// Translated non-array terms.
    memo: BTreeMap<AstId, AstId>,
    /// `(array variable, index term)` → its element variable.
    elems: BTreeMap<(AstId, AstId), AstId>,
    /// The translated index terms, witnesses and the default index.
    indices: Vec<AstId>,
    /// The default index.
    default: AstId,
}

impl Context {
    /// Decide array goals of the map/store/const fragment over an infinite
    /// index sort by their element reduction. `None` outside the fragment.
    pub(super) fn check_sat_array_cal(&mut self) -> Option<(SmtResult, Option<Model>)> {
        if !self.universals.is_empty() || self.assertions.is_empty() {
            return None;
        }
        let roots = self.assertions.clone();
        // Every subterm, the operands of maps (held aside) included.
        let mut all: Vec<AstId> = Vec::new();
        let mut seen: BTreeSet<AstId> = BTreeSet::new();
        let mut todo = roots.clone();
        while let Some(t) = todo.pop() {
            if !seen.insert(t) {
                continue;
            }
            all.push(t);
            if let Some((_, ops)) = self.maps.get(&t) {
                todo.extend(ops.iter().copied());
            }
            if let Some(app) = self.m.app(t) {
                todo.extend(app.args.iter().copied());
            }
        }
        let mut index_sort = None;
        let mut index_terms: Vec<AstId> = Vec::new();
        let mut eq_atoms = 0usize;
        let mut any_map = false;
        for &t in &all {
            if self.m.is_quantifier(t) || self.m.is_var(t) {
                return None;
            }
            let s = self.m.get_sort(t);
            if let Some((is, es)) = self.m.array_sort_params(s) {
                if self.m.is_array_sort(es) || !self.cal_array_term(t) {
                    return None;
                }
                if *index_sort.get_or_insert(is) != is {
                    return None;
                }
                any_map |= self.maps.contains_key(&t);
            }
            if self.m.is_select(t) || self.m.is_store(t) {
                let k = self.m.app_args(t)[1];
                if !index_terms.contains(&k) {
                    index_terms.push(k);
                }
            }
            if self.m.is_eq(t) && self.m.is_array_sort(self.m.get_sort(self.m.app_args(t)[0])) {
                eq_atoms += 1;
            }
            if self.m.is_distinct(t) && self.m.is_array_sort(self.m.get_sort(self.m.app_args(t)[0]))
            {
                return None;
            }
        }
        let index_sort = index_sort?;
        // An infinite index sort keeps the default index apart from the others.
        if !self.m.is_arith_sort(index_sort) || !any_map {
            return None;
        }
        if index_terms.len() + eq_atoms + 1 > MAX_INDICES {
            return None;
        }
        let default = self.fresh_const(index_sort);
        let mut cal = Cal {
            memo: BTreeMap::new(),
            elems: BTreeMap::new(),
            indices: Vec::new(),
            default,
        };
        for &k in &index_terms {
            let tk = self.cal_term(&mut cal, k)?;
            if !cal.indices.contains(&tk) {
                cal.indices.push(tk);
            }
        }
        for _ in 0..eq_atoms {
            let w = self.fresh_const(index_sort);
            cal.indices.push(w);
        }
        cal.indices.push(default);
        let mut goal: Vec<AstId> = Vec::new();
        for &a in &roots {
            goal.push(self.cal_term(&mut cal, a)?);
        }
        // Equal index terms read equal elements of a variable.
        let mut by_var: BTreeMap<AstId, Vec<(AstId, AstId)>> = BTreeMap::new();
        for (&(v, i), &e) in &cal.elems {
            by_var.entry(v).or_default().push((i, e));
        }
        for list in by_var.values() {
            for (n, &(i1, e1)) in list.iter().enumerate() {
                for &(i2, e2) in &list[n + 1..] {
                    if i1 == default || i2 == default {
                        continue;
                    }
                    let same = self.m.mk_eq(i1, i2);
                    let eq = self.m.mk_eq(e1, e2);
                    goal.push(self.m.mk_implies(same, eq));
                }
            }
        }
        // The default index differs from every other index.
        for &i in &cal.indices {
            if i != default {
                let eq = self.m.mk_eq(i, default);
                goal.push(self.m.mk_not(eq));
            }
        }
        let saved = core::mem::replace(&mut self.assertions, goal);
        let (r, model) = self.check_sat_split();
        let pins = match (r, model) {
            (SmtResult::Sat, Some(mut md)) => self.cal_pins(&cal, &mut md),
            _ => None,
        };
        self.assertions = saved;
        match r {
            SmtResult::Unsat => Some((SmtResult::Unsat, None)),
            SmtResult::Sat => {
                // Confirm on the original assertions with the arrays and the
                // other constants pinned to the element model's values.
                let pins = pins?;
                let env: BTreeMap<AstId, AstId> = pins
                    .iter()
                    .map(|&p| {
                        let a = self.m.app_args(p);
                        (a[0], a[1])
                    })
                    .collect();
                let mut memo = BTreeMap::new();
                for a in self.assertions.clone() {
                    let v = self.cal_eval(a, &env, &mut memo)?;
                    if !self.m.is_true(v) {
                        return None;
                    }
                }
                // The model: the constants pinned to their values.
                let saved = core::mem::replace(&mut self.assertions, pins);
                let (r2, m2) = self.check_sat_split();
                self.assertions = saved;
                (r2 == SmtResult::Sat).then_some((SmtResult::Sat, m2))
            }
            SmtResult::Unknown => None,
        }
    }

    /// The value of the scalar term `t` with the constants of `env` replaced
    /// by their values: a Boolean or numeral literal, or `None`.
    fn cal_eval(
        &mut self,
        t: AstId,
        env: &BTreeMap<AstId, AstId>,
        memo: &mut BTreeMap<AstId, AstId>,
    ) -> Option<AstId> {
        if let Some(&r) = memo.get(&t) {
            return Some(r);
        }
        let r = if let Some(&v) = env.get(&t) {
            v
        } else if self.m.is_select(t) {
            let args = self.m.app_args(t).to_vec();
            let (entries, def) = self.cal_arr_val(args[0], env, memo)?;
            let k = self.cal_eval(args[1], env, memo)?;
            entries
                .iter()
                .find(|(i, _)| *i == k)
                .map_or(def, |&(_, v)| v)
        } else if self.m.is_eq(t) && self.m.is_array_sort(self.m.get_sort(self.m.app_args(t)[0])) {
            let args = self.m.app_args(t).to_vec();
            let (e1, d1) = self.cal_arr_val(args[0], env, memo)?;
            let (e2, d2) = self.cal_arr_val(args[1], env, memo)?;
            let read = |es: &[(AstId, AstId)], d: AstId, k: AstId| {
                es.iter().find(|(i, _)| *i == k).map_or(d, |&(_, v)| v)
            };
            let same = d1 == d2
                && e1
                    .iter()
                    .chain(&e2)
                    .all(|&(k, _)| read(&e1, d1, k) == read(&e2, d2, k));
            self.mk_bool(same)
        } else if let Some(app) = self.m.app(t)
            && !app.args.is_empty()
        {
            let decl = app.decl;
            let args = app.args.clone();
            let mut vals = Vec::with_capacity(args.len());
            for a in args {
                vals.push(self.cal_eval(a, env, memo)?);
            }
            let r = self.m.mk_app(decl, &vals);
            crate::rewriter::simplify(&mut self.m, r)
        } else {
            t
        };
        if self.m.app(r).is_none_or(|a| !a.args.is_empty())
            || (self.m.is_uninterp_const(r) && !env.contains_key(&t))
        {
            return None;
        }
        memo.insert(t, r);
        Some(r)
    }

    /// The value of the array term `arr` under `env`: its entries (index
    /// value, element value) and its default element.
    #[allow(clippy::type_complexity)]
    fn cal_arr_val(
        &mut self,
        arr: AstId,
        env: &BTreeMap<AstId, AstId>,
        memo: &mut BTreeMap<AstId, AstId>,
    ) -> Option<(Vec<(AstId, AstId)>, AstId)> {
        let arr = env.get(&arr).copied().unwrap_or(arr);
        if self.m.is_store(arr) {
            let args = self.m.app_args(arr).to_vec();
            let (mut es, d) = self.cal_arr_val(args[0], env, memo)?;
            let k = self.cal_eval(args[1], env, memo)?;
            let v = self.cal_eval(args[2], env, memo)?;
            es.retain(|&(i, _)| i != k);
            es.push((k, v));
            return Some((es, d));
        }
        if self.m.is_const_array(arr) {
            let v = self.m.app_args(arr)[0];
            let d = self.cal_eval(v, env, memo)?;
            return Some((Vec::new(), d));
        }
        if self.m.is_ite(arr) {
            let args = self.m.app_args(arr).to_vec();
            let c = self.cal_eval(args[0], env, memo)?;
            if self.m.is_true(c) {
                return self.cal_arr_val(args[1], env, memo);
            }
            if self.m.is_false(c) {
                return self.cal_arr_val(args[2], env, memo);
            }
            return None;
        }
        if let Some((f, ops)) = self.maps.get(&arr).cloned() {
            let mut vals = Vec::with_capacity(ops.len());
            for o in ops {
                vals.push(self.cal_arr_val(o, env, memo)?);
            }
            let mut keys: Vec<AstId> = Vec::new();
            for (es, _) in &vals {
                for &(k, _) in es {
                    if !keys.contains(&k) {
                        keys.push(k);
                    }
                }
            }
            let apply_at = |ctx: &mut Self, k: Option<AstId>| -> Option<AstId> {
                let args: Vec<AstId> = vals
                    .iter()
                    .map(|(es, d)| {
                        k.and_then(|k| es.iter().find(|(i, _)| *i == k).map(|&(_, v)| v))
                            .unwrap_or(*d)
                    })
                    .collect();
                let r = ctx.apply(&f, args).ok()?;
                let r = crate::rewriter::simplify(&mut ctx.m, r);
                ctx.m.app(r).is_some_and(|a| a.args.is_empty()).then_some(r)
            };
            let d = apply_at(self, None)?;
            let mut es = Vec::with_capacity(keys.len());
            for k in keys {
                es.push((k, apply_at(self, Some(k))?));
            }
            return Some((es, d));
        }
        None
    }

    /// Is `t` an array term of the fragment: a user variable, `store`,
    /// constant array, map or `ite`?
    fn cal_array_term(&self, t: AstId) -> bool {
        self.m.is_store(t)
            || self.m.is_const_array(t)
            || self.maps.contains_key(&t)
            || self.m.is_ite(t)
            || (self.m.is_uninterp_const(t) && self.is_user_constant_or_bits(t))
    }

    /// The translation of the non-array term `t`.
    fn cal_term(&mut self, cal: &mut Cal, t: AstId) -> Option<AstId> {
        if let Some(&r) = cal.memo.get(&t) {
            return Some(r);
        }
        let r = if self.m.is_select(t) {
            let args = self.m.app_args(t).to_vec();
            let k = self.cal_term(cal, args[1])?;
            self.cal_elem(cal, args[0], k)?
        } else if self.m.is_eq(t) && self.m.is_array_sort(self.m.get_sort(self.m.app_args(t)[0])) {
            let args = self.m.app_args(t).to_vec();
            let mut eqs = Vec::new();
            for i in cal.indices.clone() {
                let x = self.cal_elem(cal, args[0], i)?;
                let y = self.cal_elem(cal, args[1], i)?;
                eqs.push(self.m.mk_eq(x, y));
            }
            if eqs.len() == 1 {
                eqs[0]
            } else {
                self.m.mk_and(&eqs)
            }
        } else if self.m.is_array_sort(self.m.get_sort(t)) {
            return None;
        } else if let Some(app) = self.m.app(t)
            && !app.args.is_empty()
        {
            let decl = app.decl;
            let args = app.args.clone();
            let mut nargs = Vec::with_capacity(args.len());
            for a in args {
                nargs.push(self.cal_term(cal, a)?);
            }
            self.m.mk_app(decl, &nargs)
        } else {
            t
        };
        cal.memo.insert(t, r);
        Some(r)
    }

    /// The element of the array term `arr` at the translated index `i`.
    fn cal_elem(&mut self, cal: &mut Cal, arr: AstId, i: AstId) -> Option<AstId> {
        if self.m.is_store(arr) {
            let args = self.m.app_args(arr).to_vec();
            let k = self.cal_term(cal, args[1])?;
            let v = self.cal_term(cal, args[2])?;
            if k == i {
                return Some(v);
            }
            let rest = self.cal_elem(cal, args[0], i)?;
            let c = self.m.mk_eq(i, k);
            return Some(self.m.mk_ite(c, v, rest));
        }
        if self.m.is_const_array(arr) {
            let v = self.m.app_args(arr)[0];
            return self.cal_term(cal, v);
        }
        if let Some((f, ops)) = self.maps.get(&arr).cloned() {
            let mut vals = Vec::with_capacity(ops.len());
            for o in ops {
                vals.push(self.cal_elem(cal, o, i)?);
            }
            return self.apply(&f, vals).ok();
        }
        if self.m.is_ite(arr) {
            let args = self.m.app_args(arr).to_vec();
            let c = self.cal_term(cal, args[0])?;
            let t = self.cal_elem(cal, args[1], i)?;
            let e = self.cal_elem(cal, args[2], i)?;
            return Some(self.m.mk_ite(c, t, e));
        }
        if self.m.is_uninterp_const(arr) {
            if let Some(&e) = cal.elems.get(&(arr, i)) {
                return Some(e);
            }
            let (_, es) = self.m.array_sort_params(self.m.get_sort(arr))?;
            let e = self.fresh_const(es);
            cal.elems.insert((arr, i), e);
            return Some(e);
        }
        None
    }

    /// Pins of every array variable (a `store` chain over a constant array
    /// of its default element) and every other constant of the assertions to
    /// their values in the element model `md`.
    fn cal_pins(&mut self, cal: &Cal, md: &mut Model) -> Option<Vec<AstId>> {
        let lit = |ctx: &mut Self, md: &mut Model, t: AstId| -> Option<AstId> {
            Some(match md.eval(&ctx.m, t) {
                Value::Bool(b) => ctx.mk_bool(b),
                Value::Num(r, is_int) => ctx.m.mk_numeral(r, is_int),
                Value::Bv(v, w) => ctx.m.mk_bv_numeral(v, w),
                Value::Uninterp(..) => return None,
            })
        };
        let mut pins = Vec::new();
        let vars: BTreeSet<AstId> = cal.elems.keys().map(|&(v, _)| v).collect();
        for v in vars {
            let sort = self.m.get_sort(v);
            // A variable never read at the default index (no equality
            // mentions it) is free there: its first element serves.
            let def = cal
                .elems
                .get(&(v, cal.default))
                .or_else(|| cal.elems.iter().find(|((w, _), _)| *w == v).map(|(_, e)| e))
                .copied()?;
            let dv = lit(self, md, def)?;
            let mut arr = self.m.mk_const_array(sort, dv);
            let mut done: Vec<AstId> = Vec::new();
            for (&(w, i), &e) in &cal.elems {
                if w != v || i == cal.default {
                    continue;
                }
                let iv = lit(self, md, i)?;
                if done.contains(&iv) {
                    continue;
                }
                done.push(iv);
                let ev = lit(self, md, e)?;
                if ev != dv {
                    arr = self.m.mk_store(arr, iv, ev);
                }
            }
            pins.push(self.m.mk_eq(v, arr));
        }
        // The other user constants of the assertions keep their values.
        let roots = self.assertions.clone();
        for t in self.m.postorder_many(&roots) {
            if self.m.is_uninterp_const(t)
                && self.is_user_constant_or_bits(t)
                && !self.m.is_array_sort(self.m.get_sort(t))
                && let Some(&tr) = cal.memo.get(&t)
            {
                let v = lit(self, md, tr)?;
                pins.push(self.m.mk_eq(t, v));
            }
        }
        Some(pins)
    }
}
