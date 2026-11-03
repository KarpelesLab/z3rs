//! Relevancy-guided E-matching rounds — the shape of z3's quantifier engine
//! (`smt_quantifier.cpp`, `mam.cpp`, `qi_queue.cpp`, `smt_relevancy.cpp`)
//! on top of the ground decision procedure.
//!
//! z3 matches patterns only against the terms that are *relevant* under the
//! current assignment (relevancy level 2: a true disjunction makes one true
//! disjunct relevant, a false conjunction one false conjunct, an `ite` its
//! condition and the branch taken, every other application its arguments),
//! modulo the congruence closure of the equalities that assignment asserts.
//! New instances join the search and the loop repeats until a conflict
//! (`unsat`) or no new instance (E-matching is complete only up to its
//! triggers, so that is no `sat`).
//!
//! Here each round takes the relevant terms and their congruence classes
//! from a model of the ground goal with the instances so far, and adds every
//! instance the triggers match among them. Instances are consequences of the
//! universals, so an `unsat` round is a refutation. Within the fragment of
//! Booleans, arithmetic and uninterpreted functions the rounds run inside one
//! persistent search ([`crate::smt::SmtCore`], see
//! `Context::online_ematch_refute`): each final check's model drives a
//! round, whose instances are preprocessed and internalized on the fly and the
//! search resumes with what it learnt. Elsewhere each round decides the goal
//! afresh.

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec::Vec;

use super::{Context, LiftCtx};
use crate::ast::AstId;
use crate::ast::arith::ArithOp;
use crate::rewriter::substitute;
use crate::smt::SmtCore;
use crate::smt::{Model, SmtResult, Value};

/// The most bindings one trigger set may produce in one round.
const MAX_BINDINGS: usize = 20_000;

/// Union-find over terms (path-halving, no ranks: the sets stay small).
fn find(parent: &mut BTreeMap<AstId, AstId>, x: AstId) -> AstId {
    let mut r = x;
    while let Some(&p) = parent.get(&r) {
        if p == r {
            break;
        }
        r = p;
    }
    let mut c = x;
    while c != r {
        let next = parent[&c];
        parent.insert(c, r);
        c = next;
    }
    r
}

/// Merge the classes of `a` and `b`; `false` when they already coincide.
fn union(parent: &mut BTreeMap<AstId, AstId>, a: AstId, b: AstId) -> bool {
    parent.entry(a).or_insert(a);
    parent.entry(b).or_insert(b);
    let (ra, rb) = (find(parent, a), find(parent, b));
    if ra == rb {
        return false;
    }
    parent.insert(ra, rb);
    true
}

/// The memo of [`Context::online_preprocess`] across formulas.
struct OnlinePre {
    /// The finite function tables: rewritten terms, and each replaced
    /// constant-argument application with its constant.
    table_memo: BTreeMap<AstId, AstId>,
    table: BTreeMap<AstId, AstId>,
    /// The functions tabled.
    table_decls: BTreeSet<AstId>,
    /// The term-`ite` lifting.
    lift: LiftCtx,
}

/// The instantiation state shared by the rounds of one refutation.
#[derive(Default)]
struct Rounds {
    /// The instances so far, in creation order.
    instances: Vec<AstId>,
    seen: BTreeSet<AstId>,
    /// Every binding instantiated so far, as (universal, binder terms):
    /// like z3's fingerprints, a binding is new only modulo the classes.
    done: Vec<(usize, Vec<AstId>)>,
}

impl Context {
    /// The user functions and the quantifier abstractions: a relevant
    /// abstraction `P(t)` triggers its definitions `∀xs. P(t) ⇒ φ` and
    /// `¬P(t) ⇒ ¬φ[sk(t)]`, as z3 instantiates a nested quantifier whose
    /// atom holds and skolemizes one whose atom fails.
    fn ematch_user_decls(&self) -> BTreeSet<AstId> {
        let mut user_decls: BTreeSet<AstId> = self.funcs.values().copied().collect();
        user_decls.extend(self.quant_pred_decls.iter().copied());
        user_decls
    }

    /// One E-matching round over `model`: the instances of the universals
    /// (with their trigger sets `trigs`) at the bindings the relevant terms
    /// of the assertions and the instances so far match, new modulo the
    /// model's congruence classes. They join `st.instances`; returns how many.
    /// `known` holds the truth values the search assigned to formulas,
    /// read before the model's evaluation.
    fn ematch_round(
        &mut self,
        universals: &[(Vec<AstId>, AstId)],
        trigs: &[Vec<Vec<AstId>>],
        user_decls: &BTreeSet<AstId>,
        model: &mut Model,
        known: BTreeMap<AstId, bool>,
        st: &mut Rounds,
    ) -> usize {
        let mut roots = self.assertions.clone();
        roots.extend(st.instances.iter().copied());
        let mut memo = known;
        let terms = self.relevant_terms(&roots, model, &mut memo);
        let by_decl = self.relevant_classes(&terms, model, user_decls, &mut memo);
        let before = st.instances.len();
        let mut fingerprints: BTreeSet<(usize, Vec<AstId>)> = st
            .done
            .iter()
            .map(|(ui, ts)| (*ui, ts.iter().map(|&t| self.class_rep(t)).collect()))
            .collect();
        for (ui, (vars, body)) in universals.iter().enumerate() {
            let vs: BTreeSet<AstId> = vars.iter().copied().collect();
            for set in &trigs[ui] {
                for binding in self.search_ematch_set(set, &vs, &by_decl) {
                    // New only modulo the classes (z3's fingerprints);
                    // instantiated with the matched terms.
                    let terms: Vec<AstId> = vars.iter().map(|v| binding[v]).collect();
                    let key: Vec<AstId> = terms.iter().map(|&t| self.class_rep(t)).collect();
                    if !fingerprints.insert((ui, key)) {
                        continue;
                    }
                    st.done.push((ui, terms.clone()));
                    let subst: Vec<(AstId, AstId)> = vars.iter().copied().zip(terms).collect();
                    let raw = substitute(&mut self.m, *body, &subst);
                    let mut inst = crate::rewriter::simplify(&mut self.m, raw);
                    for _ in 0..3 {
                        let folded = self.dt_fold(inst);
                        let next = crate::rewriter::simplify(&mut self.m, folded);
                        if next == inst {
                            break;
                        }
                        inst = next;
                    }
                    if self.m.is_true(inst) || !st.seen.insert(inst) {
                        continue;
                    }
                    st.instances.push(inst);
                }
            }
        }
        st.instances.len() - before
    }

    /// Relevancy-guided E-matching inside one persistent search (z3's
    /// `smt::context` with its quantifier manager): the ground goal is
    /// internalized once into an [`SmtCore`], and each final check's model
    /// drives an E-matching round whose instances are internalized into the
    /// same search, which resumes with every clause it learnt (a round no
    /// longer re-decides the goal from scratch). Each formula goes through the
    /// per-term preprocessing of [`Self::decide_combined`] incrementally: the
    /// finite function tables and the term-`ite` lifting keep their memo
    /// across instances, so a term shared by two instances is preprocessed
    /// once. `None` outside the fragment this preprocessing covers (Booleans,
    /// linear arithmetic and uninterpreted functions over uninterpreted sorts,
    /// where [`Self::decide_combined`] adds nothing else); else whether the
    /// universals were refuted.
    fn online_ematch_refute(
        &mut self,
        universals: &[(Vec<AstId>, AstId)],
        trigs: &[Vec<Vec<AstId>>],
        user_decls: &BTreeSet<AstId>,
    ) -> Option<Option<SmtResult>> {
        const MAX_ROUNDS: usize = 60;
        const MAX_INSTANCES: usize = 20_000;
        // Each round reads the relevant terms of every instance so far: past
        // this many instances read in total the search gives up (`unknown`).
        const MAX_WORK: usize = 600_000;
        let base = self.conjunction();
        let mut roots = alloc::vec![base];
        roots.extend(universals.iter().map(|&(_, b)| b));
        if !self.online_fragment(&roots) {
            return None;
        }
        let members = self.datatype_member_decls();
        let table_decls: BTreeSet<AstId> = self
            .funcs
            .values()
            .copied()
            .filter(|d| !members.contains(d))
            .collect();
        let mut pre = OnlinePre {
            table_memo: BTreeMap::new(),
            table: BTreeMap::new(),
            lift: LiftCtx {
                defs: Vec::new(),
                cache: BTreeMap::new(),
                dm: BTreeMap::new(),
                toint: BTreeMap::new(),
                rdiv: BTreeMap::new(),
                zero_divs: Vec::new(),
                zero_rdivs: Vec::new(),
                sqrt: BTreeMap::new(),
                lin_facts: Vec::new(),
            },
            table_decls,
        };
        let mut core = SmtCore::new();
        core.eager_equalities();
        core.resume_searches();
        let goal = self.online_preprocess(base, &mut pre);
        let goal = self.with_axioms(goal);
        core.assert(&self.m, goal);
        let mut st = Rounds::default();
        // Decide `false` first, as z3 does: an atom left open by the search
        // then keeps what it guards irrelevant.
        use core::sync::atomic::Ordering::Relaxed;
        let saved_phase = crate::sat::solver::DECIDE_FALSE_FIRST.swap(true, Relaxed);
        let mut verdict = None;
        let mut work = 0;
        for _ in 0..MAX_ROUNDS {
            let (res, model) = core.check(&self.m);
            match res {
                SmtResult::Unsat => {
                    verdict = Some(SmtResult::Unsat);
                    break;
                }
                SmtResult::Unknown => break,
                SmtResult::Sat => {}
            }
            let Some(mut model) = model else { break };
            // The applications replaced by their table entries take those values.
            for (&app, &v) in &pre.table {
                match model.eval_value(&self.m, v) {
                    Value::Uninterp(..) => model.pin_equal(&self.m, app, v),
                    val => model.pin_value(app, val),
                }
            }
            let before = st.instances.len();
            // The search's truth values, also for the original form of each
            // preprocessed formula.
            let mut known = core.assigned();
            for (&t, &tabled) in &pre.table_memo {
                let lifted = pre.lift.cache.get(&tabled).copied().unwrap_or(tabled);
                if t != lifted
                    && let Some(&v) = known.get(&lifted)
                {
                    known.insert(t, v);
                }
            }
            if self.ematch_round(universals, trigs, user_decls, &mut model, known, &mut st) == 0 {
                break;
            }
            for i in before..st.instances.len() {
                let inst = st.instances[i];
                let p = self.online_preprocess(inst, &mut pre);
                core.assert(&self.m, p);
            }
            work += st.instances.len();
            if st.instances.len() > MAX_INSTANCES || work > MAX_WORK {
                break;
            }
        }
        crate::sat::solver::DECIDE_FALSE_FIRST.store(saved_phase, Relaxed);
        Some(verdict)
    }

    /// The formula `f` ready for the search: the finite function tables and
    /// the term-`ite` lifting of [`Self::decide_combined`], with the memo of
    /// both kept in `pre` across formulas, and the lifting's new definitions.
    fn online_preprocess(&mut self, f: AstId, pre: &mut OnlinePre) -> AstId {
        let mut table: BTreeMap<AstId, AstId> = core::mem::take(&mut pre.table);
        let decls = core::mem::take(&mut pre.table_decls);
        let tabled = self.table_rw(f, &decls, &mut pre.table_memo, &mut table);
        pre.table = table;
        pre.table_decls = decls;
        let mark = pre.lift.defs.len();
        // Inner terms first (constant stack on deep goals).
        for t in self.m.postorder_ltr(tabled, |_| true) {
            self.lift_terms(t, &mut pre.lift);
        }
        let lifted = self.lift_terms(tabled, &mut pre.lift);
        if pre.lift.defs.len() == mark {
            lifted
        } else {
            let mut parts = pre.lift.defs[mark..].to_vec();
            parts.push(lifted);
            self.m.mk_and(&parts)
        }
    }

    /// Are the `roots` within the fragment [`Self::online_ematch_refute`]
    /// preprocesses: Boolean connectives, arithmetic over `Int` and `Real`
    /// (products of variables opaque), equalities, and uninterpreted functions and constants over
    /// `Bool`, the arithmetic sorts and plain uninterpreted sorts?
    fn online_fragment(&self, roots: &[AstId]) -> bool {
        let mut decls: BTreeSet<AstId> = self.funcs.values().copied().collect();
        decls.extend(self.quant_pred_decls.iter().copied());
        self.m
            .postorder_many(roots)
            .into_iter()
            .all(|t| self.online_term(t, &decls))
    }

    /// Is the term `t` itself (not its arguments) in the fragment of
    /// [`Self::online_fragment`], `decls` being the user functions and the
    /// quantifier abstractions?
    fn online_term(&self, t: AstId, decls: &BTreeSet<AstId>) -> bool {
        let m = &self.m;
        let Some(app) = m.app(t) else {
            return false;
        };
        let s = m.get_sort(t);
        if !(m.is_bool_sort(s) || m.is_arith_sort(s) || self.is_plain_uninterp_sort(s))
            || self.str_symbolic.contains(&t)
            || self.quant_atoms.contains(&t)
        {
            return false;
        }
        if m.is_true(t)
            || m.is_false(t)
            || m.is_and(t)
            || m.is_or(t)
            || m.is_not(t)
            || m.is_implies(t)
            || m.is_xor(t)
            || m.is_ite(t)
            || m.is_eq(t)
        {
            return true;
        }
        match m.arith_op(t) {
            // A nonlinear product is an opaque term to the search (an
            // abstraction: its refutations stand).
            Some(
                ArithOp::Num
                | ArithOp::Le
                | ArithOp::Ge
                | ArithOp::Lt
                | ArithOp::Gt
                | ArithOp::Add
                | ArithOp::Sub
                | ArithOp::Uminus
                | ArithOp::Mul,
            ) => return true,
            Some(_) => return false,
            None => {}
        }
        if app.args.is_empty() {
            return m.is_uninterp_const(t);
        }
        // The user functions, quantifier abstractions and their skolems.
        decls.contains(&app.decl)
            || self
                .decl_name(app.decl)
                .is_some_and(|n| n.starts_with("!sk!"))
    }

    /// Refute the universals by relevancy-guided E-matching rounds (see the
    /// module documentation). `Some(Unsat)` on a refutation; `None` when the
    /// matching reaches a fixpoint, the ground decision is not definite, or
    /// the round / instance budget runs out.
    pub(super) fn relevant_ematch_refute(&mut self) -> Option<SmtResult> {
        if self.universals.is_empty() || !self.fp_deferred_decls.is_empty() {
            return None;
        }
        // An undecided goal over quantifier abstractions is retried with
        // their definitions (`check_sat_quant_defs`): the matching waits for
        // those, which it needs to instantiate the nested quantifiers.
        if !self.in_quant_defs && !self.quant_defs.is_empty() {
            let mut roots: Vec<AstId> = self.universals.iter().map(|&(_, b)| b).collect();
            roots.extend(self.assertions.iter().copied());
            if self
                .m
                .postorder_many(&roots)
                .iter()
                .any(|&t| self.is_quant_atom(t))
            {
                return None;
            }
        }
        let universals = self.universals.clone();
        let user_decls = self.ematch_user_decls();
        let trigs: Vec<Vec<Vec<AstId>>> = universals
            .iter()
            .map(|(vars, body)| self.search_triggers(vars, *body, &user_decls))
            .collect();
        if trigs.iter().all(Vec::is_empty) {
            return None;
        }
        let saved_class = core::mem::take(&mut self.ematch_class);
        let saved_members = core::mem::take(&mut self.ematch_members);
        let verdict = match self.online_ematch_refute(&universals, &trigs, &user_decls) {
            Some(v) => v,
            None => self.ematch_rounds_afresh(&universals, &trigs, &user_decls),
        };
        self.ematch_class = saved_class;
        self.ematch_members = saved_members;
        verdict
    }

    /// The E-matching rounds outside [`Self::online_ematch_refute`]'s
    /// fragment: each round decides the ground goal with the instances so far
    /// afresh with [`Self::decide_combined`].
    fn ematch_rounds_afresh(
        &mut self,
        universals: &[(Vec<AstId>, AstId)],
        trigs: &[Vec<Vec<AstId>>],
        user_decls: &BTreeSet<AstId>,
    ) -> Option<SmtResult> {
        const MAX_ROUNDS: usize = 40;
        const MAX_INSTANCES: usize = 6000;
        // Each round decides the whole goal afresh, so the rounds together
        // cost about the sum of the goals' sizes: past this many nodes the
        // search gives up (a sound `unknown`) rather than run unboundedly.
        const MAX_WORK: usize = 100_000;
        let base = self.conjunction();
        let mut st = Rounds::default();
        let mut work = 0;
        for _ in 0..MAX_ROUNDS {
            let goal = if st.instances.is_empty() {
                base
            } else {
                let mut conj = alloc::vec![base];
                conj.extend(st.instances.iter().copied());
                self.m.mk_and(&conj)
            };
            work += self.m.postorder(goal).len();
            if work > MAX_WORK {
                break;
            }
            // Decide `false` first, as z3 does: an atom left open by the
            // search then keeps what it guards irrelevant.
            use core::sync::atomic::Ordering::Relaxed;
            let saved_phase = crate::sat::solver::DECIDE_FALSE_FIRST.swap(true, Relaxed);
            let (res, model, _) = self.decide_combined(goal);
            crate::sat::solver::DECIDE_FALSE_FIRST.store(saved_phase, Relaxed);
            match res {
                SmtResult::Unsat => return Some(SmtResult::Unsat),
                SmtResult::Unknown => break,
                SmtResult::Sat => {}
            }
            let Some(mut model) = model else { break };
            if self.ematch_round(
                universals,
                trigs,
                user_decls,
                &mut model,
                BTreeMap::new(),
                &mut st,
            ) == 0
                || st.instances.len() > MAX_INSTANCES
            {
                break;
            }
        }
        None
    }

    /// The representative of `t`'s E-matching class: its oldest (smallest)
    /// member, or `t` itself outside every class.
    fn class_rep(&self, t: AstId) -> AstId {
        self.ematch_class
            .get(&t)
            .and_then(|&c| self.ematch_members[c].iter().min().copied())
            .unwrap_or(t)
    }

    /// The truth value of the Boolean term `t` in `model`, memoized, folding
    /// the connectives over their arguments' values.
    fn relevancy_value(
        &self,
        t: AstId,
        model: &mut Model,
        memo: &mut BTreeMap<AstId, bool>,
    ) -> bool {
        if let Some(&b) = memo.get(&t) {
            return b;
        }
        let m = &self.m;
        let args: Vec<AstId> = m.app(t).map(|a| a.args.to_vec()).unwrap_or_default();
        let v = if m.is_true(t) {
            true
        } else if m.is_false(t) {
            false
        } else if m.is_not(t) {
            !self.relevancy_value(args[0], model, memo)
        } else if m.is_and(t) {
            args.iter().all(|&a| self.relevancy_value(a, model, memo))
        } else if m.is_or(t) {
            args.iter().any(|&a| self.relevancy_value(a, model, memo))
        } else if m.is_implies(t) {
            !self.relevancy_value(args[0], model, memo)
                || self.relevancy_value(args[1], model, memo)
        } else if m.is_ite(t) && m.is_bool_sort(m.get_sort(t)) {
            if self.relevancy_value(args[0], model, memo) {
                self.relevancy_value(args[1], model, memo)
            } else {
                self.relevancy_value(args[2], model, memo)
            }
        } else {
            matches!(model.eval_value(m, t), Value::Bool(true))
        };
        memo.insert(t, v);
        v
    }

    /// The terms relevant in `model` from the asserted `roots` (z3's relevancy
    /// propagation, see the module documentation), in discovery order, with
    /// the truth values found in `memo`. Quantifiers are not entered.
    fn relevant_terms(
        &self,
        roots: &[AstId],
        model: &mut Model,
        memo: &mut BTreeMap<AstId, bool>,
    ) -> Vec<AstId> {
        let mut seen: BTreeSet<AstId> = BTreeSet::new();
        let mut out = Vec::new();
        let mut stack: Vec<AstId> = roots.iter().rev().copied().collect();
        while let Some(t) = stack.pop() {
            if !seen.insert(t) || self.m.is_quantifier(t) {
                continue;
            }
            out.push(t);
            let Some(app) = self.m.app(t) else { continue };
            let args = app.args.to_vec();
            if args.is_empty() {
                continue;
            }
            let m = &self.m;
            let boolean = m.is_bool_sort(m.get_sort(t));
            let pick = |want: bool, ctx: &Self, model: &mut Model, memo: &mut _| {
                args.iter()
                    .copied()
                    .find(|&a| ctx.relevancy_value(a, model, memo) == want)
            };
            let next: Vec<AstId> = if m.is_ite(t) {
                let c = self.relevancy_value(args[0], model, memo);
                alloc::vec![args[0], if c { args[1] } else { args[2] }]
            } else if boolean && (m.is_and(t) || m.is_or(t)) {
                let v = self.relevancy_value(t, model, memo);
                // A true disjunction / false conjunction needs one witness.
                if v == m.is_or(t) {
                    pick(v, self, model, memo).into_iter().collect()
                } else {
                    args
                }
            } else if boolean && m.is_implies(t) {
                if self.relevancy_value(t, model, memo) {
                    if !self.relevancy_value(args[0], model, memo) {
                        alloc::vec![args[0]]
                    } else {
                        alloc::vec![args[1]]
                    }
                } else {
                    args
                }
            } else {
                args
            };
            stack.extend(next.into_iter().rev());
        }
        out
    }

    /// Install as the E-matching classes the congruence closure of the
    /// equalities between the relevant `terms` that hold in `model` (or by
    /// `memo`), and
    /// return the relevant user-function applications by declaration.
    fn relevant_classes(
        &mut self,
        terms: &[AstId],
        model: &mut Model,
        user_decls: &BTreeSet<AstId>,
        memo: &mut BTreeMap<AstId, bool>,
    ) -> BTreeMap<AstId, BTreeSet<AstId>> {
        let mut parent: BTreeMap<AstId, AstId> = BTreeMap::new();
        let mut by_decl: BTreeMap<AstId, BTreeSet<AstId>> = BTreeMap::new();
        for &t in terms {
            let Some(app) = self.m.app(t) else { continue };
            if user_decls.contains(&app.decl) {
                by_decl.entry(app.decl).or_default().insert(t);
            }
            if !self.m.is_eq(t) {
                continue;
            }
            let (a, b) = (app.args[0], app.args[1]);
            if self.m.is_bool_sort(self.m.get_sort(a)) || !self.relevancy_value(t, model, memo) {
                continue;
            }
            union(&mut parent, a, b);
        }
        // Model-based theory combination (z3's `assume_eqs`): arithmetic
        // terms with one value in the model are merged.
        let mut by_value: BTreeMap<alloc::string::String, AstId> = BTreeMap::new();
        for &t in terms {
            let s = self.m.get_sort(t);
            if !self.m.is_arith_sort(s) || !self.m.is_app(t) {
                continue;
            }
            let key = alloc::format!("{s:?} {:?}", model.eval_value(&self.m, t));
            match by_value.get(&key) {
                Some(&u) => {
                    union(&mut parent, u, t);
                }
                None => {
                    by_value.insert(key, t);
                }
            }
        }
        // Congruence: equal arguments make equal applications.
        loop {
            let mut changed = false;
            let mut sig: BTreeMap<(AstId, Vec<AstId>), AstId> = BTreeMap::new();
            for &t in terms {
                let Some(app) = self.m.app(t) else { continue };
                if app.args.is_empty() || self.m.is_bool_sort(self.m.get_sort(t)) {
                    continue;
                }
                let (decl, args) = (app.decl, app.args.to_vec());
                let key = (decl, args.iter().map(|&a| find(&mut parent, a)).collect());
                match sig.get(&key) {
                    Some(&u) => changed |= union(&mut parent, u, t),
                    None => {
                        sig.insert(key, t);
                    }
                }
            }
            if !changed {
                break;
            }
        }
        self.ematch_class.clear();
        self.ematch_members.clear();
        let mut root_idx: BTreeMap<AstId, usize> = BTreeMap::new();
        let keys: Vec<AstId> = parent.keys().copied().collect();
        for t in keys {
            let r = find(&mut parent, t);
            let c = *root_idx.entry(r).or_insert_with(|| {
                self.ematch_members.push(Vec::new());
                self.ematch_members.len() - 1
            });
            self.ematch_members[c].push(t);
            self.ematch_class.insert(t, c);
        }
        by_decl
    }

    /// The trigger sets of `∀vars. body` for the search: the user patterns,
    /// else the patterns z3's `pattern_inference` infers, else
    /// [`Self::trigger_sets`]'s. A definition of a quantifier abstraction
    /// (`∀fs xs. P(fs) ⇒ φ`, `∀fs. ¬P(fs) ⇒ ψ`) is the nested quantifier
    /// z3 instantiates once the outer variables `fs` are bound: its triggers
    /// are `P(fs)` followed by the nested quantifier's patterns over `xs`.
    fn search_triggers(
        &self,
        vars: &[AstId],
        body: AstId,
        user_decls: &BTreeSet<AstId>,
    ) -> Vec<Vec<AstId>> {
        if let Some((guard, phi)) = self.definition_guard(body) {
            let fs: BTreeSet<AstId> = self
                .m
                .app(guard)
                .map(|a| a.args.iter().copied().collect())
                .unwrap_or_default();
            let xs: BTreeSet<AstId> = vars.iter().copied().filter(|v| !fs.contains(v)).collect();
            if vars.iter().all(|v| xs.contains(v) || fs.contains(v)) {
                if xs.is_empty() {
                    return alloc::vec![alloc::vec![guard]];
                }
                let mut sets: Vec<Vec<AstId>> = self
                    .def_patterns
                    .get(&body)
                    .cloned()
                    .unwrap_or_default()
                    .into_iter()
                    .filter(|set| {
                        set.iter()
                            .all(|&t| self.m.app(t).is_some_and(|a| user_decls.contains(&a.decl)))
                            && xs.iter().all(|v| {
                                set.iter().any(|&t| self.pattern_mentions(t, &[*v].into()))
                            })
                    })
                    .collect();
                if sets.is_empty() {
                    sets = self.infer_patterns(&xs, phi, &[], user_decls);
                }
                if sets.is_empty() {
                    sets = self.trigger_sets(&xs, phi, user_decls);
                }
                for set in &mut sets {
                    set.insert(0, guard);
                }
                return sets;
            }
        }
        let vs: BTreeSet<AstId> = vars.iter().copied().collect();
        if !self.universal_patterns.contains_key(&body) {
            let found = self.infer_patterns(&vs, body, &[], user_decls);
            if !found.is_empty() {
                return found;
            }
        }
        self.trigger_sets(&vs, body, user_decls)
    }

    /// For a definition of a quantifier abstraction, `P(fs) ⇒ φ` or
    /// `¬P(fs) ⇒ φ`: the guard `P(fs)` and `φ`.
    fn definition_guard(&self, body: AstId) -> Option<(AstId, AstId)> {
        if !self.m.is_implies(body) {
            return None;
        }
        let args = self.m.app_args(body);
        let (g, phi) = (args[0], args[1]);
        let g = if self.m.is_not(g) {
            self.m.app_args(g)[0]
        } else {
            g
        };
        let app = self.m.app(g)?;
        (self.quant_pred_decls.contains(&app.decl) && !app.args.is_empty()).then_some((g, phi))
    }

    /// z3's `pattern_inference_cfg::mk_patterns` with arithmetic forbidden
    /// (`pi.arith` conservative): the candidates are the non-ground
    /// applications of user functions whose arguments are binders, ground
    /// terms or candidates themselves, other than the `no_pats`; looping
    /// candidates (an instance of another one over the same binders) and
    /// those containing a smaller candidate over the same binders are dropped;
    /// each remaining candidate covering every binder is a pattern, and
    /// without one the first greedy cover of the candidates (most binders,
    /// then smallest, first) is a multi-pattern.
    fn infer_patterns(
        &self,
        vars: &BTreeSet<AstId>,
        body: AstId,
        no_pats: &[AstId],
        user_decls: &BTreeSet<AstId>,
    ) -> Vec<Vec<AstId>> {
        // Per subterm: `None` forbidden, else (binders, size).
        type Info = Option<(BTreeSet<AstId>, usize)>;
        fn walk(
            ctx: &Context,
            t: AstId,
            vars: &BTreeSet<AstId>,
            user_decls: &BTreeSet<AstId>,
            memo: &mut BTreeMap<AstId, Info>,
            cands: &mut Vec<AstId>,
        ) -> Info {
            if let Some(i) = memo.get(&t) {
                return i.clone();
            }
            let info = if vars.contains(&t) {
                Some(([t].into(), 1))
            } else if let Some(app) = ctx.m.app(t) {
                let mut vs = BTreeSet::new();
                let mut size = 1;
                let mut ok = true;
                for &a in &app.args {
                    match walk(ctx, a, vars, user_decls, memo, cands) {
                        Some((v, sz)) => {
                            vs.extend(v);
                            size += sz;
                        }
                        None => ok = false,
                    }
                }
                if !ok {
                    // A ground term is never forbidden.
                    if ctx.pattern_mentions(t, vars) {
                        None
                    } else {
                        Some((BTreeSet::new(), size))
                    }
                } else if vs.is_empty() || user_decls.contains(&app.decl) {
                    if !vs.is_empty() {
                        cands.push(t);
                    }
                    Some((vs, size))
                } else {
                    None
                }
            } else {
                None
            };
            memo.insert(t, info.clone());
            info
        }
        let mut memo: BTreeMap<AstId, Info> = BTreeMap::new();
        let mut cands: Vec<AstId> = Vec::new();
        walk(self, body, vars, user_decls, &mut memo, &mut cands);
        cands.retain(|c| !no_pats.contains(c));
        let info = |t: AstId| memo[&t].clone().unwrap_or_default();
        // Looping patterns: `c1` generalizes another candidate `c2`.
        let kept: Vec<AstId> = cands
            .iter()
            .copied()
            .filter(|&c1| {
                !cands.iter().any(|&c2| {
                    c1 != c2
                        && info(c1).0 == info(c2).0
                        && self.pattern_generalizes(c1, c2, vars, &mut BTreeMap::new())
                        && !self.pattern_generalizes(c2, c1, vars, &mut BTreeMap::new())
                })
            })
            .collect();
        // Bigger patterns: containing a candidate over the same binders.
        let kept: Vec<AstId> = kept
            .iter()
            .copied()
            .filter(|&c| {
                let mine = info(c).0;
                !kept
                    .iter()
                    .any(|&d| d != c && info(d).0 == mine && self.proper_subterm(d, c))
            })
            .collect();
        let unary: Vec<Vec<AstId>> = kept
            .iter()
            .filter(|&&c| info(c).0.len() == vars.len())
            .map(|&c| alloc::vec![c])
            .collect();
        if !unary.is_empty() {
            return unary;
        }
        let mut rest = kept;
        rest.sort_by(|&a, &b| {
            let (ia, ib) = (info(a), info(b));
            ib.0.len().cmp(&ia.0.len()).then(ia.1.cmp(&ib.1))
        });
        let mut covered: BTreeSet<AstId> = BTreeSet::new();
        let mut set = Vec::new();
        for c in rest {
            let vs = info(c).0;
            if !vs.is_subset(&covered) {
                covered.extend(vs);
                set.push(c);
                if covered.len() == vars.len() {
                    return alloc::vec![set];
                }
            }
        }
        Vec::new()
    }

    /// Is `p2` an instance of `p1`, its binders (`vars`) bound consistently in
    /// `binding` (z3's `smaller_pattern`)?
    fn pattern_generalizes(
        &self,
        p1: AstId,
        p2: AstId,
        vars: &BTreeSet<AstId>,
        binding: &mut BTreeMap<AstId, AstId>,
    ) -> bool {
        if vars.contains(&p1) {
            return *binding.entry(p1).or_insert(p2) == p2;
        }
        match (self.m.app(p1), self.m.app(p2)) {
            (Some(a), Some(b)) if a.decl == b.decl && a.args.len() == b.args.len() => {
                let pairs: Vec<(AstId, AstId)> =
                    a.args.iter().copied().zip(b.args.iter().copied()).collect();
                pairs
                    .into_iter()
                    .all(|(x, y)| self.pattern_generalizes(x, y, vars, binding))
            }
            _ => p1 == p2,
        }
    }

    /// Is `d` a proper subterm of `c`?
    fn proper_subterm(&self, d: AstId, c: AstId) -> bool {
        self.m
            .app(c)
            .is_some_and(|a| a.args.iter().any(|&x| x == d || self.proper_subterm(d, x)))
    }

    /// All complete binder substitutions matching the trigger `set` against
    /// the applications in `by_decl` (see [`Self::ematch`]), the per-trigger
    /// bindings joined modulo the E-matching classes. Unlike
    /// [`Self::ematch_set`] no binding is dropped below [`MAX_BINDINGS`].
    fn search_ematch_set(
        &self,
        set: &[AstId],
        vars: &BTreeSet<AstId>,
        by_decl: &BTreeMap<AstId, BTreeSet<AstId>>,
    ) -> Vec<BTreeMap<AstId, AstId>> {
        let mut acc: Vec<BTreeMap<AstId, AstId>> = alloc::vec![BTreeMap::new()];
        for &trig in set {
            let Some(grounds) = by_decl.get(&self.m.app_decl(trig)) else {
                return Vec::new();
            };
            let mut partials: Vec<BTreeMap<AstId, AstId>> = Vec::new();
            // Each application of the trigger's function is matched itself:
            // its class members of that function are in `grounds` too (only
            // the arguments match modulo the classes).
            let pa = self.m.app_args(trig);
            for &g in grounds {
                let ga = self.m.app_args(g);
                let mut b = BTreeMap::new();
                if pa.len() == ga.len()
                    && pa
                        .iter()
                        .zip(ga)
                        .all(|(&p, &q)| self.ematch(p, q, vars, &mut b))
                {
                    partials.push(b);
                }
            }
            let mut next: Vec<BTreeMap<AstId, AstId>> = Vec::new();
            'join: for a in &acc {
                for p in &partials {
                    if a.iter()
                        .all(|(k, v)| p.get(k).is_none_or(|w| self.ematch_equal(*w, *v)))
                    {
                        let mut m = p.clone();
                        m.extend(a.iter().map(|(&k, &v)| (k, v)));
                        next.push(m);
                        if next.len() >= MAX_BINDINGS {
                            break 'join;
                        }
                    }
                }
            }
            acc = next;
            if acc.is_empty() {
                return Vec::new();
            }
        }
        acc.retain(|b| vars.iter().all(|v| b.contains_key(v)));
        acc
    }
}
