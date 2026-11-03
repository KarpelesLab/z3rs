//! Model values of the declared array constants, as z3 prints them:
//! `((as const (Array I E)) v)` overlaid with `store`s.
//!
//! The solver decides arrays through their reads (the array axioms and
//! congruence), so a model knows an array only at the indices it reads. Its
//! interpretation is completed the way z3's `theory_array_base::mk_value`
//! and model completion do:
//!
//! - an array constant the assertions define at top level (`a = t`, z3's
//!   `solve-eqs`) takes the value of its definition;
//! - every other one is a table: one entry per read `select(t, j)` that
//!   reaches it through `t` (stores at other indices, `ite` branches the
//!   model takes), and an `else` value — the constant array's value when one
//!   is equal to it, else, when the problem has no `store` or constant array
//!   left, the result that occurs most often among its entries
//!   (`func_interp::get_max_occ_result`), else a fresh value of the element
//!   sort (`mk_extra_fresh_value`);
//! - the arrays an equality the model makes true joins share the `else`
//!   value, and each side's reads are propagated to the other at the
//!   indices neither side overwrites (`propagate_selects`).
//!
//! The values are only used when every assertion evaluates to `true` with
//! all constants replaced by their values (arrays by these interpretations),
//! so a printed model is always a model.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::String;
use alloc::vec::Vec;

use super::{Context, Model};
use crate::ast::AstId;

/// An array value: its `(index, element)` entries (in insertion order, each
/// index once) and its `else` element. All are value terms.
type ArrVal = (Vec<(AstId, AstId)>, AstId);

/// What reading an array term at a concrete index gives.
enum Read {
    /// A known element value.
    Known(AstId),
    /// The (so far unknown) entry of a table array constant at an index.
    Base(AstId, AstId),
    /// The read cannot be followed (an unsupported array term).
    Opaque,
}

/// Which reads give the table arrays their entries.
#[derive(Clone, Copy, PartialEq, Eq)]
enum Reads {
    /// The reads of the assertions the model has a value for.
    Asserted,
    /// Those and the reads of the model's e-graph (the array axioms'
    /// instances).
    Solver,
    /// Those and the other reads of the assertions, at their evaluated
    /// values.
    Evaluated,
}

/// Where an array term's `store` chain ends.
enum Base {
    /// A table array constant.
    Free(AstId),
    /// A constant array with this element value.
    Const(AstId),
    /// An unsupported array term.
    Opaque,
}

impl Context {
    /// Can values of `s` be index or element values of a printed array?
    fn array_model_scalar_sort(&self, s: AstId) -> bool {
        self.m.is_bool_sort(s)
            || self.m.is_arith_sort(s)
            || self.m.bv_sort_width(s).is_some()
            || self.enums.contains_key(&s)
    }

    /// Is `t` a value term: a numeral, `true`/`false`, a bit-vector literal
    /// or an enumeration constructor?
    fn array_model_is_value(&self, t: AstId) -> bool {
        self.m.app(t).is_some_and(|a| a.args.is_empty())
            && (self.m.as_numeral(t).is_some()
                || self.m.bv_numeral_value(t).is_some()
                || self.m.is_true(t)
                || self.m.is_false(t)
                || self
                    .enums
                    .get(&self.m.get_sort(t))
                    .is_some_and(|cs| cs.contains(&t)))
    }

    /// The interpretations of the declared array constants under `model`
    /// (see the module documentation), computed once per model: constant
    /// term → ground value term. `None` when they cannot be built or do not
    /// satisfy the assertions.
    pub(super) fn array_model_values(
        &mut self,
        model: &mut Model,
    ) -> Option<BTreeMap<AstId, AstId>> {
        if let Some(v) = model.array_values() {
            return v.cloned();
        }
        // The array equalities the model makes true: the asserted ones and
        // those it assigns; the truth of the others (the solver decided a
        // rewritten form) is guessed, each guess checked.
        let (holding, open) = self.array_model_eq_atoms(model);
        let guesses: usize = if open.len() <= 4 { 1 << open.len() } else { 1 };
        let mut v = None;
        'search: for mask in 0..guesses {
            let mut holds = holding.clone();
            holds.extend(
                open.iter()
                    .enumerate()
                    .filter(|(i, _)| mask >> i & 1 == 1)
                    .map(|(_, &t)| t),
            );
            // The reads of the assertions first (z3 interprets the relevant
            // reads), the solver's own (axiom instances) only when needed,
            // and last the evaluation of reads the model has no value for
            // (an unconstrained read eliminated before solving).
            for reads in [Reads::Asserted, Reads::Solver, Reads::Evaluated] {
                v = self.build_array_model_values(model, reads, &holds);
                if v.is_some() {
                    break 'search;
                }
            }
        }
        model.set_array_values(v.clone());
        v
    }

    /// The quantifier-free array equality atoms of the assertions: those
    /// that hold in `model` (asserted, or assigned `true`), and those whose
    /// truth the model does not record.
    fn array_model_eq_atoms(&mut self, model: &mut Model) -> (BTreeSet<AstId>, Vec<AstId>) {
        let mut conjuncts: BTreeSet<AstId> = BTreeSet::new();
        let mut stack: Vec<AstId> = self.assertions.clone();
        while let Some(t) = stack.pop() {
            if self.m.is_and(t) {
                stack.extend(self.m.app_args(t).iter().copied());
            } else {
                conjuncts.insert(t);
            }
        }
        let mut holding = BTreeSet::new();
        let mut open = Vec::new();
        for a in self.assertions.clone() {
            for t in self.m.postorder(a) {
                if self.m.is_quantifier(t)
                    || !self.m.is_eq(t)
                    || !self.m.is_array_sort(self.m.get_sort(self.m.app_args(t)[0]))
                    || holding.contains(&t)
                    || open.contains(&t)
                {
                    continue;
                }
                if conjuncts.contains(&t) {
                    holding.insert(t);
                    continue;
                }
                let known = if model.knows(&self.m, t) {
                    Some(t)
                } else {
                    let s = crate::rewriter::simplify(&mut self.m, t);
                    model.knows(&self.m, s).then_some(s)
                };
                match known {
                    Some(k) => {
                        if self
                            .eval_value_term(model, k)
                            .is_some_and(|v| self.m.is_true(v))
                        {
                            holding.insert(t);
                        }
                    }
                    None => open.push(t),
                }
            }
        }
        (holding, open)
    }

    /// [`Self::array_model_values`], uncached, from the reads `reads` and
    /// with the array equalities `holds` true.
    fn build_array_model_values(
        &mut self,
        model: &mut Model,
        reads_from: Reads,
        holds: &BTreeSet<AstId>,
    ) -> Option<BTreeMap<AstId, AstId>> {
        // The declared array constants the assertions mention.
        let mut arrays: Vec<AstId> = Vec::new();
        let mut scalars: Vec<AstId> = Vec::new();
        let mut unmentioned: BTreeMap<AstId, AstId> = BTreeMap::new();
        let mut seen = BTreeSet::new();
        let mentioned: BTreeSet<AstId> = self
            .m
            .postorder_many(&self.assertions)
            .into_iter()
            .collect();
        for name in self.decl_order.clone() {
            if !seen.insert(name.clone()) {
                continue;
            }
            let d = self.funcs[&name];
            let Some(fd) = self.m.func_decl(d) else {
                continue;
            };
            if !fd.domain.is_empty() {
                continue;
            }
            let range = fd.range;
            let c = self.m.mk_const(d);
            if let Some((i, e)) = self.m.array_sort_params(range) {
                if !mentioned.contains(&c) {
                    // Unconstrained: z3's `get_some_value` of the array sort,
                    // the constant array of the element sort's.
                    if self.array_model_scalar_sort(i)
                        && let Some(v) = self.array_model_some_value(e)
                    {
                        let t = self.m.mk_const_array(range, v);
                        unmentioned.insert(c, t);
                    }
                    continue;
                }
                if !self.array_model_scalar_sort(i) || !self.array_model_scalar_sort(e) {
                    return None;
                }
                arrays.push(c);
            } else if self.array_model_scalar_sort(range) {
                scalars.push(c);
            }
        }
        if arrays.is_empty() {
            return (!unmentioned.is_empty()).then_some(unmentioned);
        }
        // A universal over an array is not checked here.
        for (_, body) in self.universals.clone() {
            if self
                .m
                .postorder(body)
                .iter()
                .any(|&t| self.m.is_array_sort(self.m.get_sort(t)))
            {
                return None;
            }
        }
        // The scalar constants' values.
        let mut env: BTreeMap<AstId, AstId> = BTreeMap::new();
        for &c in &scalars {
            if let Some(v) = self.eval_value_term(model, c) {
                env.insert(c, v);
            }
        }
        // Top-level definitions `a = t` (z3's solve-eqs).
        let mut conjuncts: Vec<AstId> = Vec::new();
        let mut stack: Vec<AstId> = self.assertions.iter().rev().copied().collect();
        while let Some(t) = stack.pop() {
            if self.m.is_and(t) {
                stack.extend(self.m.app_args(t).iter().rev().copied());
            } else {
                conjuncts.push(t);
            }
        }
        let mut defs: BTreeMap<AstId, AstId> = BTreeMap::new();
        let mut def_atoms: BTreeSet<AstId> = BTreeSet::new();
        for &t in &conjuncts {
            if !self.m.is_eq(t) || !self.m.is_array_sort(self.m.get_sort(self.m.app_args(t)[0])) {
                continue;
            }
            let (l, r) = (self.m.app_args(t)[0], self.m.app_args(t)[1]);
            for (x, body) in [(l, r), (r, l)] {
                if arrays.contains(&x) && !defs.contains_key(&x) {
                    let exp = self.array_model_expand(body, &defs);
                    if !self.m.postorder(exp).contains(&x) {
                        defs.insert(x, body);
                        def_atoms.insert(t);
                        break;
                    }
                }
            }
        }
        let free: Vec<AstId> = arrays
            .iter()
            .copied()
            .filter(|a| !defs.contains_key(a))
            .collect();
        // The reads: of the assertions, then of the model's e-graph.
        let mut reads: Vec<AstId> = Vec::new();
        let mut read_set = BTreeSet::new();
        for &a in &self.assertions.clone() {
            for t in self.m.postorder(a) {
                if self.m.is_quantifier(t) {
                    continue;
                }
                if self.m.is_select(t) && read_set.insert(t) {
                    reads.push(t);
                }
            }
        }
        if reads_from != Reads::Asserted {
            for &t in model.euf_terms() {
                if self.m.is_select(t) && read_set.insert(t) {
                    reads.push(t);
                }
            }
        }
        let mut entries: BTreeMap<AstId, Vec<(AstId, AstId)>> =
            free.iter().map(|&a| (a, Vec::new())).collect();
        for s in reads {
            let args = self.m.app_args(s).to_vec();
            if args.len() != 2 {
                continue;
            }
            // A read the solver never saw (not even in its simplified form)
            // has no value of its own.
            let known = if model.knows(&self.m, s) {
                s
            } else {
                crate::rewriter::simplify(&mut self.m, s)
            };
            if !model.knows(&self.m, known) && reads_from != Reads::Evaluated {
                continue;
            }
            let idx = self.array_model_expand(args[1], &defs);
            let (Some(k), Some(v)) = (
                self.array_model_scalar(model, idx, &entries),
                self.eval_value_term(model, known),
            ) else {
                continue;
            };
            let arr = self.array_model_expand(args[0], &defs);
            if let Read::Base(a, k) = self.array_model_read(model, arr, k, &entries)
                && let Some(es) = entries.get_mut(&a)
            {
                es.push((k, v));
            }
        }
        // The array equalities the model makes true.
        let mut eqs: Vec<(AstId, AstId)> = Vec::new();
        let mut eq_seen = BTreeSet::new();
        for &a in &self.assertions.clone() {
            for t in self.m.postorder(a) {
                if self.m.is_quantifier(t)
                    || !self.m.is_eq(t)
                    || def_atoms.contains(&t)
                    || !eq_seen.insert(t)
                {
                    continue;
                }
                let args = self.m.app_args(t).to_vec();
                if !self.m.is_array_sort(self.m.get_sort(args[0])) {
                    continue;
                }
                if holds.contains(&t) {
                    let l = self.array_model_expand(args[0], &defs);
                    let r = self.array_model_expand(args[1], &defs);
                    eqs.push((l, r));
                }
            }
        }
        // Classes of table arrays sharing an `else` value, and their constant
        // defaults.
        let mut class: BTreeMap<AstId, AstId> = free.iter().map(|&a| (a, a)).collect();
        fn find(class: &BTreeMap<AstId, AstId>, mut a: AstId) -> AstId {
            while class[&a] != a {
                a = class[&a];
            }
            a
        }
        let mut class_default: BTreeMap<AstId, AstId> = BTreeMap::new();
        let set_default = |class: &BTreeMap<AstId, AstId>,
                           cd: &mut BTreeMap<AstId, AstId>,
                           a: AstId,
                           v: AstId| {
            let r = find(class, a);
            match cd.get(&r) {
                Some(&w) if w != v => false,
                _ => {
                    cd.insert(r, v);
                    true
                }
            }
        };
        for _round in 0..32 {
            let mut changed = false;
            for &(l, r) in &eqs {
                let (bl, ol) = self.array_model_base(model, l, &entries);
                let (br, or) = self.array_model_base(model, r, &entries);
                match (&bl, &br) {
                    (Base::Free(a), Base::Free(b)) => {
                        let (ra, rb) = (find(&class, *a), find(&class, *b));
                        if ra != rb {
                            let da = class_default.remove(&ra);
                            class.insert(ra, rb);
                            if let Some(v) = da
                                && !set_default(&class, &mut class_default, rb, v)
                            {
                                return None;
                            }
                            changed = true;
                        }
                    }
                    (Base::Free(a), Base::Const(v)) | (Base::Const(v), Base::Free(a)) => {
                        let r0 = find(&class, *a);
                        if class_default.get(&r0) != Some(v) {
                            if !set_default(&class, &mut class_default, *a, *v) {
                                return None;
                            }
                            changed = true;
                        }
                    }
                    _ => {}
                }
                let mut keys: Vec<AstId> = ol;
                keys.extend(or);
                for b in [&bl, &br] {
                    if let Base::Free(a) = b {
                        keys.extend(entries[a].iter().map(|&(k, _)| k));
                    }
                }
                let mut done = BTreeSet::new();
                for k in keys {
                    if !done.insert(k) {
                        continue;
                    }
                    let rl = self.array_model_read(model, l, k, &entries);
                    let rr = self.array_model_read(model, r, k, &entries);
                    match (rl, rr) {
                        (Read::Known(x), Read::Known(y)) if x != y => return None,
                        (Read::Known(v), Read::Base(b, i)) | (Read::Base(b, i), Read::Known(v)) => {
                            entries.get_mut(&b)?.push((i, v));
                            changed = true;
                        }
                        _ => {}
                    }
                }
            }
            if !changed {
                break;
            }
        }
        // `else` values.
        // (A `store` or constant array left once the definitions are gone.)
        let rest: Vec<AstId> = conjuncts
            .iter()
            .copied()
            .filter(|t| !def_atoms.contains(t))
            .collect();
        let any_store = self
            .m
            .postorder_many(&rest)
            .into_iter()
            .any(|t| self.m.is_store(t) || self.m.is_const_array(t));
        let mut used: BTreeSet<AstId> = env.values().copied().collect();
        for es in entries.values() {
            for &(k, v) in es {
                used.insert(k);
                used.insert(v);
            }
        }
        used.extend(class_default.values().copied());
        for a in self.assertions.clone() {
            for t in self.m.postorder(a) {
                if self.array_model_is_value(t) {
                    used.insert(t);
                }
            }
        }
        let mut class_else: BTreeMap<AstId, AstId> = BTreeMap::new();
        for &a in &free {
            let r = find(&class, a);
            if class_else.contains_key(&r) {
                continue;
            }
            let (_, elem) = self.m.array_sort_params(self.m.get_sort(a))?;
            let v = if let Some(&v) = class_default.get(&r) {
                v
            } else if !any_store {
                // The most frequent result among the class's entries (each
                // index once).
                let mut counts: BTreeMap<AstId, usize> = BTreeMap::new();
                let mut best: Option<(AstId, usize)> = None;
                let mut keys = BTreeSet::new();
                for &b in &free {
                    if find(&class, b) != r {
                        continue;
                    }
                    for &(k, v) in &entries[&b] {
                        if !keys.insert(k) {
                            continue;
                        }
                        let c = counts.entry(v).or_insert(0);
                        *c += 1;
                        if best.is_none_or(|(_, m)| *c > m) {
                            best = Some((v, *c));
                        }
                    }
                }
                match best {
                    Some((v, _)) => v,
                    None => self.array_model_some_value(elem)?,
                }
            } else {
                self.array_model_fresh_value(elem, &mut used)?
            };
            class_else.insert(r, v);
        }
        // The value terms.
        let mut values: BTreeMap<AstId, AstId> = BTreeMap::new();
        // The arrays of a class list their indices in one order: the order
        // they first occur in the class.
        let mut class_keys: BTreeMap<AstId, Vec<AstId>> = BTreeMap::new();
        for &a in &free {
            let ks = class_keys.entry(find(&class, a)).or_default();
            for &(k, _) in &entries[&a] {
                if !ks.contains(&k) {
                    ks.push(k);
                }
            }
        }
        for &a in &free {
            let r = find(&class, a);
            let els = class_else[&r];
            let mut es: Vec<(AstId, AstId)> = Vec::new();
            for &(k, v) in &entries[&a] {
                if !es.iter().any(|&(k2, _)| k2 == k) {
                    es.push((k, v));
                }
            }
            let order = &class_keys[&r];
            es.sort_by_key(|&(k, _)| order.iter().position(|&x| x == k));
            let sort = self.m.get_sort(a);
            let t = self.array_model_term(sort, &(es, els));
            values.insert(a, t);
        }
        env.extend(values.iter().map(|(&a, &v)| (a, v)));
        // Defined arrays: their definitions' values (in definition order of
        // dependency, by repeated passes).
        for _ in 0..=defs.len() {
            let mut progress = false;
            for (&x, &body) in &defs {
                if env.contains_key(&x) {
                    continue;
                }
                let mut memo = BTreeMap::new();
                if let Some(val) = self.array_model_arr(model, body, &env, &mut memo) {
                    let t = self.array_model_term(self.m.get_sort(x), &val);
                    env.insert(x, t);
                    values.insert(x, t);
                    progress = true;
                }
            }
            if !progress {
                break;
            }
        }
        if values.len() != arrays.len() {
            return None;
        }
        values.extend(unmentioned);
        // Every assertion must hold.
        let mut memo = BTreeMap::new();
        for a in self.assertions.clone() {
            let v = self.array_model_eval(model, a, &env, &mut memo)?;
            if !self.m.is_true(v) {
                return None;
            }
        }
        Some(values)
    }

    /// `t` with the defined array constants replaced by their definitions,
    /// recursively, simplified.
    fn array_model_expand(&mut self, t: AstId, defs: &BTreeMap<AstId, AstId>) -> AstId {
        let mut cur = t;
        for _ in 0..=defs.len() {
            let pairs: Vec<(AstId, AstId)> = self
                .m
                .postorder(cur)
                .into_iter()
                .filter_map(|x| defs.get(&x).map(|&d| (x, d)))
                .collect();
            if pairs.is_empty() {
                break;
            }
            cur = crate::rewriter::substitute(&mut self.m, cur, &pairs);
        }
        // Simplified as the solver sees it (`store(a, i, a[i])` is `a`).
        crate::rewriter::simplify(&mut self.m, cur)
    }

    /// Read the (expanded) array term `arr` at the index value `k` under
    /// `model`, the table arrays' entries so far being `entries`.
    fn array_model_read(
        &mut self,
        model: &mut Model,
        mut arr: AstId,
        k: AstId,
        entries: &BTreeMap<AstId, Vec<(AstId, AstId)>>,
    ) -> Read {
        loop {
            if self.m.is_store(arr) {
                let args = self.m.app_args(arr).to_vec();
                let Some(i) = self.array_model_scalar(model, args[1], entries) else {
                    return Read::Opaque;
                };
                if i == k {
                    // The stored value; a read of a table entry not known
                    // yet is that entry.
                    let v = args[2];
                    if let Some(v) = self.array_model_scalar(model, v, entries) {
                        return Read::Known(v);
                    }
                    if self.m.is_select(v) {
                        let va = self.m.app_args(v).to_vec();
                        if let Some(k2) = self.array_model_scalar(model, va[1], entries) {
                            return self.array_model_read(model, va[0], k2, entries);
                        }
                    }
                    return Read::Opaque;
                }
                arr = args[0];
            } else if self.m.is_const_array(arr) {
                let v = self.m.app_args(arr)[0];
                return match self.array_model_scalar(model, v, entries) {
                    Some(v) => Read::Known(v),
                    None => Read::Opaque,
                };
            } else if self.m.is_ite(arr) {
                let args = self.m.app_args(arr).to_vec();
                match self.array_model_scalar(model, args[0], entries) {
                    Some(c) if self.m.is_true(c) => arr = args[1],
                    Some(c) if self.m.is_false(c) => arr = args[2],
                    _ => return Read::Opaque,
                }
            } else if let Some(es) = entries.get(&arr) {
                return match es.iter().find(|&&(i, _)| i == k) {
                    Some(&(_, v)) => Read::Known(v),
                    None => Read::Base(arr, k),
                };
            } else {
                return Read::Opaque;
            }
        }
    }

    /// Where the `store` chain of the (expanded) array term `arr` ends under
    /// `model` (reads taken from `entries` first), and the index values it
    /// overwrites.
    fn array_model_base(
        &mut self,
        model: &mut Model,
        mut arr: AstId,
        entries: &BTreeMap<AstId, Vec<(AstId, AstId)>>,
    ) -> (Base, Vec<AstId>) {
        let mut over = Vec::new();
        loop {
            if self.m.is_store(arr) {
                let args = self.m.app_args(arr).to_vec();
                match self.array_model_scalar(model, args[1], entries) {
                    Some(i) => over.push(i),
                    None => return (Base::Opaque, over),
                }
                arr = args[0];
            } else if self.m.is_const_array(arr) {
                let v = self.m.app_args(arr)[0];
                return match self.array_model_scalar(model, v, entries) {
                    Some(v) => (Base::Const(v), over),
                    None => (Base::Opaque, over),
                };
            } else if self.m.is_ite(arr) {
                let args = self.m.app_args(arr).to_vec();
                match self.array_model_scalar(model, args[0], entries) {
                    Some(c) if self.m.is_true(c) => arr = args[1],
                    Some(c) if self.m.is_false(c) => arr = args[2],
                    _ => return (Base::Opaque, over),
                }
            } else if self.is_decl_const(arr) {
                return (Base::Free(arr), over);
            } else {
                return (Base::Opaque, over);
            }
        }
    }

    /// The value of the scalar term `t` (of an expanded array term) under
    /// `model`: a read through the tables `entries` when they know it, else
    /// the model's value of `t` (or of its simplified form) when the model
    /// records one, else `t`'s operator applied to its arguments' values.
    fn array_model_scalar(
        &mut self,
        model: &mut Model,
        t: AstId,
        entries: &BTreeMap<AstId, Vec<(AstId, AstId)>>,
    ) -> Option<AstId> {
        if self.array_model_is_value(t) {
            return Some(t);
        }
        if self.m.is_select(t) {
            let args = self.m.app_args(t).to_vec();
            if let Some(k) = self.array_model_scalar(model, args[1], entries)
                && let Read::Known(v) = self.array_model_read(model, args[0], k, entries)
            {
                return Some(v);
            }
        }
        let known = if model.knows(&self.m, t) {
            t
        } else {
            crate::rewriter::simplify(&mut self.m, t)
        };
        let app = self.m.app(t)?.clone();
        if model.knows(&self.m, known) || app.args.is_empty() {
            return self.eval_value_term(model, known);
        }
        if self.m.is_select(t)
            || app
                .args
                .iter()
                .any(|&a| self.m.is_array_sort(self.m.get_sort(a)))
        {
            return None;
        }
        let mut vals = Vec::with_capacity(app.args.len());
        for &a in &app.args {
            vals.push(self.array_model_scalar(model, a, entries)?);
        }
        let r = self.m.mk_app(app.decl, &vals);
        let r = crate::rewriter::simplify(&mut self.m, r);
        if self.array_model_is_value(r) {
            Some(r)
        } else if self.funcs.values().any(|&d| d == app.decl) {
            self.eval_value_term(model, r)
        } else {
            None
        }
    }

    /// z3's `get_some_value` of a finite element sort (or `0` of an infinite
    /// one): `false`, `0`, the zero bit-vector, the first constructor.
    fn array_model_some_value(&mut self, sort: AstId) -> Option<AstId> {
        if self.m.is_bool_sort(sort) {
            Some(self.m.mk_false())
        } else if self.m.is_arith_sort(sort) {
            let int = self.m.is_int_sort(sort);
            Some(self.m.mk_numeral(puremp::Rational::from(0), int))
        } else if let Some(w) = self.m.bv_sort_width(sort) {
            Some(self.m.mk_bv_numeral(puremp::Int::from(0), w))
        } else {
            self.enums.get(&sort).and_then(|cs| cs.first().copied())
        }
    }

    /// A value of `sort` not in `used` (then added to it): the least
    /// non-negative numeral for an infinite sort or a wide enough
    /// bit-vector sort, else z3's `get_some_value`.
    fn array_model_fresh_value(
        &mut self,
        sort: AstId,
        used: &mut BTreeSet<AstId>,
    ) -> Option<AstId> {
        let width = self.m.bv_sort_width(sort);
        if !self.m.is_arith_sort(sort) && width.is_none_or(|w| w < 8) {
            return self.array_model_some_value(sort);
        }
        let int = self.m.is_int_sort(sort);
        for n in 0i64.. {
            let v = match width {
                Some(w) => self.m.mk_bv_numeral(puremp::Int::from(n), w),
                None => self.m.mk_numeral(puremp::Rational::from(n), int),
            };
            if used.insert(v) {
                return Some(v);
            }
        }
        None
    }

    /// The value term `store(… store(const(else), k₁, v₁) …, kₙ, vₙ)` of an
    /// array value of sort `sort`, entries equal to the `else` value left out.
    fn array_model_term(&mut self, sort: AstId, val: &ArrVal) -> AstId {
        let (es, els) = val;
        let mut t = self.m.mk_const_array(sort, *els);
        for &(k, v) in es {
            if v != *els {
                t = self.m.mk_store(t, k, v);
            }
        }
        t
    }

    /// The value of the array term `arr` with the constants of `env`
    /// replaced by their values.
    fn array_model_arr(
        &mut self,
        model: &mut Model,
        arr: AstId,
        env: &BTreeMap<AstId, AstId>,
        memo: &mut BTreeMap<AstId, AstId>,
    ) -> Option<ArrVal> {
        let arr = env.get(&arr).copied().unwrap_or(arr);
        if self.m.is_store(arr) {
            let args = self.m.app_args(arr).to_vec();
            let (mut es, d) = self.array_model_arr(model, args[0], env, memo)?;
            let k = self.array_model_eval(model, args[1], env, memo)?;
            let v = self.array_model_eval(model, args[2], env, memo)?;
            match es.iter_mut().find(|(i, _)| *i == k) {
                Some(e) => e.1 = v,
                None => es.push((k, v)),
            }
            return Some((es, d));
        }
        if self.m.is_const_array(arr) {
            let v = self.m.app_args(arr)[0];
            let d = self.array_model_eval(model, v, env, memo)?;
            return Some((Vec::new(), d));
        }
        if self.m.is_ite(arr) {
            let args = self.m.app_args(arr).to_vec();
            let c = self.array_model_eval(model, args[0], env, memo)?;
            return if self.m.is_true(c) {
                self.array_model_arr(model, args[1], env, memo)
            } else if self.m.is_false(c) {
                self.array_model_arr(model, args[2], env, memo)
            } else {
                None
            };
        }
        None
    }

    /// The value of the scalar term `t` with the constants of `env` replaced
    /// by their values, an uninterpreted function's application by its
    /// model value at the arguments' values: a value term, or `None`.
    pub(super) fn array_model_eval(
        &mut self,
        model: &mut Model,
        t: AstId,
        env: &BTreeMap<AstId, AstId>,
        memo: &mut BTreeMap<AstId, AstId>,
    ) -> Option<AstId> {
        if let Some(&r) = memo.get(&t) {
            return Some(r);
        }
        let read = |es: &[(AstId, AstId)], d: AstId, k: AstId| {
            es.iter().find(|(i, _)| *i == k).map_or(d, |&(_, v)| v)
        };
        let r = if let Some(&v) = env.get(&t) {
            v
        } else if self.array_model_is_value(t) {
            t
        } else if self.m.is_quantifier(t) || self.m.is_var(t) {
            return None;
        } else if self.m.is_select(t) {
            let args = self.m.app_args(t).to_vec();
            let (es, d) = self.array_model_arr(model, args[0], env, memo)?;
            let k = self.array_model_eval(model, args[1], env, memo)?;
            read(&es, d, k)
        } else if (self.m.is_eq(t) || self.m.is_distinct(t))
            && self.m.is_array_sort(self.m.get_sort(self.m.app_args(t)[0]))
        {
            let args = self.m.app_args(t).to_vec();
            let mut vals = Vec::with_capacity(args.len());
            for a in args {
                vals.push(self.array_model_arr(model, a, env, memo)?);
            }
            let same = |(e1, d1): &ArrVal, (e2, d2): &ArrVal| {
                d1 == d2
                    && e1
                        .iter()
                        .chain(e2)
                        .all(|&(k, _)| read(e1, *d1, k) == read(e2, *d2, k))
            };
            let b = if self.m.is_eq(t) {
                vals.windows(2).all(|w| same(&w[0], &w[1]))
            } else {
                (0..vals.len()).all(|i| (i + 1..vals.len()).all(|j| !same(&vals[i], &vals[j])))
            };
            self.mk_bool(b)
        } else if self.m.is_ite(t) {
            let args = self.m.app_args(t).to_vec();
            let c = self.array_model_eval(model, args[0], env, memo)?;
            if self.m.is_true(c) {
                self.array_model_eval(model, args[1], env, memo)?
            } else if self.m.is_false(c) {
                self.array_model_eval(model, args[2], env, memo)?
            } else {
                return None;
            }
        } else if let Some(app) = self.m.app(t)
            && !app.args.is_empty()
        {
            let decl = app.decl;
            let args = app.args.clone();
            let mut vals = Vec::with_capacity(args.len());
            for a in args {
                if self.m.is_array_sort(self.m.get_sort(a)) {
                    return None;
                }
                vals.push(self.array_model_eval(model, a, env, memo)?);
            }
            let r = self.m.mk_app(decl, &vals);
            let r = crate::rewriter::simplify(&mut self.m, r);
            if self.array_model_is_value(r) {
                r
            } else if self.funcs.values().any(|&d| d == decl) {
                // A user function at value arguments: its model value.
                self.eval_value_term(model, r)?
            } else {
                return None;
            }
        } else {
            // An uninterpreted constant outside `env`.
            return None;
        };
        if !self.array_model_is_value(r) {
            return None;
        }
        memo.insert(t, r);
        Some(r)
    }

    /// Does the Boolean term `t`, which mentions arrays, evaluate to `true`
    /// under `model` with the array constants taking their
    /// [`Self::array_model_values`]?
    pub(super) fn array_model_holds(&mut self, model: &mut Model, t: AstId) -> bool {
        self.array_model_value_of(model, t)
            .is_some_and(|v| self.m.is_true(v))
    }

    /// The value of the term `t` under `model` with the array constants
    /// taking their [`Self::array_model_values`]: a value term (scalar) or a
    /// ground `store`/`const` term (array). `None` when `t` mentions no
    /// array, the arrays have no values, or `t` does not evaluate.
    pub(super) fn array_model_value_of(&mut self, model: &mut Model, t: AstId) -> Option<AstId> {
        if !self
            .m
            .postorder(t)
            .iter()
            .any(|&x| self.m.is_array_sort(self.m.get_sort(x)))
        {
            return None;
        }
        let values = self.array_model_values(model)?;
        let mut env: BTreeMap<AstId, AstId> = values;
        for x in self.m.postorder(t) {
            if self.is_decl_const(x)
                && !env.contains_key(&x)
                && self.array_model_scalar_sort(self.m.get_sort(x))
                && let Some(v) = self.eval_value_term(model, x)
            {
                env.insert(x, v);
            }
        }
        let mut memo = BTreeMap::new();
        let sort = self.m.get_sort(t);
        if self.m.is_array_sort(sort) {
            let val = self.array_model_arr(model, t, &env, &mut memo)?;
            Some(self.array_model_term(sort, &val))
        } else {
            self.array_model_eval(model, t, &env, &mut memo)
        }
    }

    /// Render a value term of [`Self::array_model_value_of`] as z3 prints
    /// it: `((as const (Array I E)) v)` under `store`s, or the scalar value.
    pub(super) fn array_model_render(&mut self, model: &mut Model, t: AstId) -> String {
        if self.m.is_store(t) {
            let args = self.m.app_args(t).to_vec();
            let a = self.array_model_render(model, args[0]);
            let k = self.array_model_render(model, args[1]);
            let v = self.array_model_render(model, args[2]);
            return alloc::format!("(store {a} {k} {v})");
        }
        if self.m.is_const_array(t) {
            let v = self.m.app_args(t)[0];
            let sort = self.sort_display(self.m.get_sort(t));
            let v = self.array_model_render(model, v);
            return alloc::format!("((as const {sort}) {v})");
        }
        self.model_value_str(model, t)
    }
}
