//! A lazy SMT solver for quantifier-free equality + uninterpreted functions and
//! linear arithmetic over the reals and integers (QF_UF / QF_LRA / QF_LIA).
//!
//! This is the offline (lazy) DPLL(T) loop — the conceptual core of
//! `z3/src/smt/smt_context` (Z3 4.17.0, MIT), in its simplest complete form: the
//! SAT engine ([`Solver`]) decides the Boolean skeleton (via
//! [`encode_tracking`]); the theory solvers check the implied atoms — the
//! [`Egraph`] for equality/congruence over uninterpreted sorts, and the
//! Fourier–Motzkin core ([`crate::smt::arith`]) for the linear-arithmetic
//! atoms — and a theory-conflict blocking clause drives the next round.
//!
//! Integer-sorted variables are handled by branch-and-bound on top of the LRA
//! relaxation, so integrality constraints (`QF_LIA`) are decided too.
//!
//! Every equality (of any sort) feeds the congruence closure, so uninterpreted
//! functions get congruence even at arithmetic range sorts, and Boolean-valued
//! predicate applications get it too. The theories are combined à la
//! Nelson–Oppen with **bidirectional** equality sharing, iterated to a fixpoint:
//! equalities the arithmetic theory *entails* between shared (interface) terms
//! (e.g. `x = y` from `x ≤ y ∧ y ≤ x`) are added to the congruence closure, and
//! equalities congruence induces between interface terms are added back to the
//! arithmetic constraints. Entailment is decided convexly (a single equality per
//! pair), complete for QF_UFLRA and sound for QF_UFLIA. A shared work budget
//! bounds the (worst-case exponential) disequality split and branch-and-bound,
//! yielding a sound `unknown` on exhaustion. Minimized explanations and online
//! propagation come next. Non-arithmetic, non-equality atoms remain free
//! Booleans.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use crate::ast::AstId;
use crate::ast::arith::ArithOp;
use crate::ast::manager::AstManager;
use crate::sat::literal::Lit;
use crate::sat::solver::{SatResult, Solver};
use crate::sat::tseitin::encode_tracking;
use crate::smt::arith::{
    Assignment, Constraint, LinExpr, Rel, SolveOutcome, model_with_diseqs_budgeted, project,
};
use crate::smt::euf::Egraph;

use alloc::collections::BTreeSet;

use puremp::{Int, Rational};

/// The result of an SMT check.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum SmtResult {
    /// Satisfiable.
    Sat,
    /// Unsatisfiable.
    Unsat,
    /// Could not be decided (an incomplete procedure gave up — e.g.
    /// branch-and-bound exhausted its budget on an unbounded integer problem).
    /// Returned instead of guessing, so a definite `Sat`/`Unsat` is always sound.
    Unknown,
}

/// Decide satisfiability of a quantifier-free formula over equality +
/// uninterpreted functions and/or linear arithmetic (QF_UF / QF_LRA / QF_LIA,
/// and their union when the theories do not share terms).
pub fn check(m: &AstManager, formula: AstId) -> SmtResult {
    check_model(m, formula).0
}

/// Like [`check`], but also returns a satisfying [`Model`] when the formula is
/// satisfiable (`None` when unsat). The model can evaluate terms via
/// [`Model::eval`], backing `(get-value …)` / `(get-model)`.
pub fn check_model(m: &AstManager, formula: AstId) -> (SmtResult, Option<Model>) {
    let mut sat = Solver::new();
    let (top, atoms) = encode_tracking(m, formula, &mut sat);
    sat.add_clause(&[top]);

    // Classify theory atoms. *Every* equality feeds the EUF congruence closure,
    // so uninterpreted functions get congruence regardless of their range sort
    // (an equality `(f x) = (f y)` between Int-sorted applications still yields a
    // congruence conflict when `x = y`). Arithmetic-sorted equalities and the
    // comparisons additionally feed the LRA/LIA theory.
    let mut euf_eq: Vec<(Lit, AstId, AstId)> = Vec::new();
    let mut euf_roots: Vec<AstId> = Vec::new();
    let mut arith_atoms: Vec<ArithAtom> = Vec::new();
    // Boolean-sorted uninterpreted applications (predicates): congruent instances
    // must share a truth value, so they need the congruence closure too.
    let mut pred_atoms: Vec<(Lit, AstId)> = Vec::new();
    for (&atom, &lit) in &atoms {
        if m.is_eq(atom) {
            let args = m.app_args(atom);
            let (a, b) = (args[0], args[1]);
            euf_eq.push((lit, a, b));
            euf_roots.push(a);
            euf_roots.push(b);
            if m.is_arith_sort(m.get_sort(a)) {
                arith_atoms.push(ArithAtom::eq(lit, a, b));
            }
        } else if let Some(op) = m.arith_op(atom)
            && matches!(op, ArithOp::Le | ArithOp::Lt | ArithOp::Ge | ArithOp::Gt)
        {
            let args = m.app_args(atom);
            arith_atoms.push(ArithAtom::cmp(lit, op, args[0], args[1]));
            // The compared terms are EUF terms too, so uninterpreted applications
            // among them (e.g. f(a) in f(a) > f(b)) get congruence.
            euf_roots.push(args[0]);
            euf_roots.push(args[1]);
        } else if m.is_app(atom) && !m.app_args(atom).is_empty() {
            // A predicate application p(…): a congruence term whose truth is `lit`.
            pred_atoms.push((lit, atom));
            euf_roots.push(atom);
        }
    }

    let has_theory = !euf_eq.is_empty() || !arith_atoms.is_empty() || !pred_atoms.is_empty();
    // The offline lazy loop enumerates theory-atom assignments via blocking
    // clauses; that is worst-case exponential, so cap the number of rounds and
    // return a sound `unknown` on exhaustion (rather than looping indefinitely).
    let mut rounds: u32 = 0;
    // A single work budget shared across *all* theory checks in this decision, so
    // the whole call terminates in bounded time even when many blocking-clause
    // rounds each face an expensive (blow-up-prone) theory check.
    let mut budget = BB_WORK_BUDGET;
    loop {
        rounds += 1;
        if rounds > DPLL_ROUND_LIMIT {
            return (SmtResult::Unknown, None);
        }
        match sat.solve() {
            SatResult::Unsat => return (SmtResult::Unsat, None),
            SatResult::Sat => {
                // The Boolean assignment of every tracked atom.
                let bools: BTreeMap<AstId, bool> = atoms
                    .iter()
                    .map(|(&a, &l)| (a, sat.model_holds(l)))
                    .collect();
                if !has_theory {
                    let model = Model {
                        bools,
                        arith: BTreeMap::new(),
                        euf: Egraph::new(m, &[]),
                        bv: BTreeMap::new(),
                    };
                    return (SmtResult::Sat, Some(model));
                }
                match theory_check(
                    m,
                    &euf_eq,
                    &euf_roots,
                    &arith_atoms,
                    &pred_atoms,
                    &sat,
                    &mut budget,
                ) {
                    // Both theories consistent under this assignment → SAT.
                    TheoryOutcome::Sat(arith, euf) => {
                        let model = Model {
                            bools,
                            arith,
                            euf,
                            bv: BTreeMap::new(),
                        };
                        return (SmtResult::Sat, Some(model));
                    }
                    // Undecidable here: neither confirm SAT nor soundly block.
                    TheoryOutcome::Unknown => return (SmtResult::Unknown, None),
                    // Definitively inconsistent → block this assignment and retry.
                    TheoryOutcome::Unsat => {
                        let mut block: Vec<Lit> =
                            euf_eq.iter().map(|&(lit, _, _)| flip(lit, &sat)).collect();
                        block.extend(arith_atoms.iter().map(|a| flip(a.lit, &sat)));
                        block.extend(pred_atoms.iter().map(|&(lit, _)| flip(lit, &sat)));
                        sat.add_clause(&block);
                    }
                }
            }
        }
    }
}

/// A satisfying assignment, able to evaluate terms to concrete [`Value`]s.
pub struct Model {
    /// Truth value of each tracked atom (Boolean constants + theory atoms).
    bools: BTreeMap<AstId, bool>,
    /// Rational value of each arithmetic leaf variable.
    arith: Assignment,
    /// Congruence classes over the uninterpreted terms (equal terms share an id).
    euf: Egraph,
    /// Concrete `(value, width)` of blasted bit-vector terms (QF_BV models).
    bv: BTreeMap<AstId, (Int, u32)>,
}

/// A concrete value in a [`Model`].
#[derive(Clone, Debug)]
pub enum Value {
    /// A Boolean.
    Bool(bool),
    /// A numeral and whether it belongs to the `Int` sort (vs `Real`).
    Num(Rational, bool),
    /// An element of an uninterpreted sort, identified by its congruence class.
    Uninterp(AstId, usize),
    /// A bit-vector value `(value, width)`.
    Bv(Int, u32),
}

impl Model {
    /// A bit-vector-only model: the concrete value of each blasted term.
    pub fn from_bv(bv: BTreeMap<AstId, (Int, u32)>) -> Model {
        Model {
            bools: BTreeMap::new(),
            arith: BTreeMap::new(),
            euf: Egraph::new_empty(),
            bv,
        }
    }

    /// Evaluate `t` under this model.
    pub fn eval(&mut self, m: &AstManager, t: AstId) -> Value {
        let s = m.get_sort(t);
        if let Some(width) = m.bv_sort_width(s) {
            let v = self.eval_bv(m, t);
            Value::Bv(v, width)
        } else if m.is_bool_sort(s) {
            Value::Bool(self.eval_bool(m, t))
        } else if m.is_arith_sort(s) {
            Value::Num(ast_to_lin(m, t).eval(&self.arith), m.is_int_sort(s))
        } else {
            let class = self.euf.class_of(m, t);
            Value::Uninterp(s, class)
        }
    }

    /// The value of a bit-vector term. Blasted terms (every subterm of the
    /// checked formula, so every declared constant) are read from the satisfying
    /// assignment; a bit-vector `ite` and numerals are evaluated directly.
    fn eval_bv(&mut self, m: &AstManager, t: AstId) -> Int {
        if let Some((v, _)) = self.bv.get(&t) {
            return v.clone();
        }
        if let Some(v) = m.bv_numeral_value(t) {
            return v;
        }
        if m.is_ite(t) {
            let a = m.app_args(t).to_vec();
            return if self.eval_bool(m, a[0]) {
                self.eval_bv(m, a[1])
            } else {
                self.eval_bv(m, a[2])
            };
        }
        Int::from(0)
    }

    /// Render `t`'s value as an SMT-LIB2 term (`true`, `5`, `(/ 1.0 2.0)`, …).
    pub fn value_string(&mut self, m: &AstManager, t: AstId) -> alloc::string::String {
        self.eval(m, t).render(m)
    }

    fn eval_bool(&mut self, m: &AstManager, t: AstId) -> bool {
        if let Some(&b) = self.bools.get(&t) {
            return b;
        }
        if m.is_true(t) {
            return true;
        }
        if m.is_false(t) {
            return false;
        }
        if m.is_not(t) {
            return !self.eval_bool(m, m.app_args(t)[0]);
        }
        if m.is_and(t) {
            return m.app_args(t).to_vec().iter().all(|&a| self.eval_bool(m, a));
        }
        if m.is_or(t) {
            return m.app_args(t).to_vec().iter().any(|&a| self.eval_bool(m, a));
        }
        if m.is_ite(t) {
            let a = m.app_args(t).to_vec();
            return if self.eval_bool(m, a[0]) {
                self.eval_bool(m, a[1])
            } else {
                self.eval_bool(m, a[2])
            };
        }
        if m.is_eq(t) {
            let a = m.app_args(t).to_vec();
            return self.values_eq(m, a[0], a[1]);
        }
        false // an untracked atom we cannot resolve; default to false
    }

    /// Do `a` and `b` evaluate to the same value?
    /// Do `a` and `b` evaluate to the same value under this model?
    pub fn terms_equal(&mut self, m: &AstManager, a: AstId, b: AstId) -> bool {
        self.values_eq(m, a, b)
    }

    fn values_eq(&mut self, m: &AstManager, a: AstId, b: AstId) -> bool {
        match (self.eval(m, a), self.eval(m, b)) {
            (Value::Bool(x), Value::Bool(y)) => x == y,
            (Value::Num(x, _), Value::Num(y, _)) => x == y,
            (Value::Uninterp(_, x), Value::Uninterp(_, y)) => x == y,
            (Value::Bv(x, _), Value::Bv(y, _)) => x == y,
            _ => false,
        }
    }
}

impl Value {
    /// Render as an SMT-LIB2 value term.
    pub fn render(&self, m: &AstManager) -> alloc::string::String {
        use alloc::string::ToString;
        match self {
            Value::Bool(b) => if *b { "true" } else { "false" }.to_string(),
            Value::Num(r, is_int) => render_numeral(r, *is_int),
            Value::Uninterp(sort, class) => {
                let name = m.sort(*sort).and_then(|s| s.name.as_str()).unwrap_or("U");
                alloc::format!("{name}!val!{class}")
            }
            Value::Bv(v, width) => render_bv(v, *width),
        }
    }
}

/// Render a bit-vector value as `#x…` when the width is a multiple of 4, else
/// `#b…` (matching Z3's output convention).
fn render_bv(v: &Int, width: u32) -> alloc::string::String {
    let v = v.mod_2k(width);
    if width > 0 && width.is_multiple_of(4) {
        let mut s = alloc::string::String::from("#x");
        for nibble in (0..width / 4).rev() {
            let mut d = 0u8;
            for b in 0..4 {
                if v.bit(nibble * 4 + b) {
                    d |= 1 << b;
                }
            }
            s.push(char::from_digit(d as u32, 16).unwrap());
        }
        s
    } else {
        let mut s = alloc::string::String::from("#b");
        for i in (0..width).rev() {
            s.push(if v.bit(i) { '1' } else { '0' });
        }
        s
    }
}

/// Render a rational as an SMT-LIB2 numeral: integers as `n` / `(- n)`, reals as
/// `n.0` or `(/ p.0 q.0)` (each factor sign-wrapped like Z3).
fn render_numeral(r: &Rational, is_int: bool) -> alloc::string::String {
    if is_int {
        return render_signed_int(r.numerator());
    }
    if r.is_integer() {
        return decorate_sign(r.numerator(), |n| alloc::format!("{n}.0"));
    }
    let num = r.numerator();
    let den = r.denominator(); // always positive in normalized form
    decorate_sign(num, |n| alloc::format!("(/ {n}.0 {den}.0)"))
}

/// `n` or `(- |n|)`.
fn render_signed_int(n: &Int) -> alloc::string::String {
    decorate_sign(n, |a| alloc::format!("{a}"))
}

/// Apply `body` to `|n|` and wrap the whole thing in `(- …)` when `n < 0`.
fn decorate_sign(
    n: &Int,
    body: impl FnOnce(&Int) -> alloc::string::String,
) -> alloc::string::String {
    if *n < Int::from(0) {
        let abs = -n;
        alloc::format!("(- {})", body(&abs))
    } else {
        body(n)
    }
}

fn flip(lit: Lit, sat: &Solver) -> Lit {
    if sat.model_holds(lit) { !lit } else { lit }
}

/// The shared (interface) terms of a combined problem: the arithmetic-sorted
/// terms occurring in the EUF universe (function arguments, compared or equated
/// terms, and their arithmetic subterms). These are exactly the terms both
/// theories reason about, whose equalities they exchange in Nelson–Oppen —
/// including compound terms like `(- y)`, not just leaf variables.
fn interface_terms(m: &AstManager, euf_roots: &[AstId]) -> Vec<AstId> {
    let mut euf_universe: BTreeSet<AstId> = BTreeSet::new();
    for &r in euf_roots {
        for t in m.postorder(r) {
            euf_universe.insert(t);
        }
    }
    euf_universe
        .into_iter()
        .filter(|&t| m.is_arith_sort(m.get_sort(t)))
        .collect()
}

/// An arithmetic theory atom: either a comparison or an equality.
struct ArithAtom {
    lit: Lit,
    op: ArithOp, // Le/Lt/Ge/Gt for comparisons, Eq is stored as `is_eq`
    a: AstId,
    b: AstId,
    is_eq: bool,
}

impl ArithAtom {
    fn cmp(lit: Lit, op: ArithOp, a: AstId, b: AstId) -> ArithAtom {
        ArithAtom {
            lit,
            op,
            a,
            b,
            is_eq: false,
        }
    }
    fn eq(lit: Lit, a: AstId, b: AstId) -> ArithAtom {
        ArithAtom {
            lit,
            op: ArithOp::Le,
            a,
            b,
            is_eq: true,
        }
    }
}

/// The outcome of an integer-arithmetic consistency check: a satisfying
/// assignment, definitive infeasibility, or "gave up" (an incomplete search
/// exhausted its budget without deciding).
enum Feas {
    Sat(Assignment),
    Unsat,
    Unknown,
}

/// If `goal` is a conjunction of linear (in)equalities (`and`, `≤`/`<`/`≥`/`>`,
/// or arithmetic `=`), the equivalent list of [`Constraint`]s; `None` if it has
/// any other structure (disjunctions, negations, non-arithmetic atoms). Used by
/// the optimizer to build the LP for a linear objective.
pub fn linear_constraints(m: &AstManager, goal: AstId) -> Option<Vec<Constraint>> {
    if m.is_true(goal) {
        return Some(Vec::new());
    }
    if m.is_and(goal) {
        let mut out = Vec::new();
        for &a in m.app_args(goal) {
            out.extend(linear_constraints(m, a)?);
        }
        return Some(out);
    }
    if m.is_eq(goal) {
        let args = m.app_args(goal);
        if !m.is_arith_sort(m.get_sort(args[0])) {
            return None;
        }
        let diff = ast_to_lin(m, args[0]).sub(&ast_to_lin(m, args[1]));
        return Some(alloc::vec![Constraint::eq(diff)]);
    }
    if let Some(op) = m.arith_op(goal)
        && matches!(op, ArithOp::Le | ArithOp::Lt | ArithOp::Ge | ArithOp::Gt)
    {
        let args = m.app_args(goal);
        let diff = ast_to_lin(m, args[0]).sub(&ast_to_lin(m, args[1]));
        return Some(alloc::vec![comparison_constraint(op, true, diff)]);
    }
    None
}

/// The arithmetic constraint system for the current atom assignment: equality /
/// comparison constraints, disequalities (`expr ≠ 0`), and the integer-sorted
/// leaf variables.
struct ArithSystem {
    cons: Vec<Constraint>,
    diseqs: Vec<LinExpr>,
    int_set: BTreeSet<AstId>,
}

fn build_arith_system(m: &AstManager, atoms: &[ArithAtom], sat: &Solver) -> ArithSystem {
    let mut cons: Vec<Constraint> = Vec::new();
    let mut diseqs: Vec<LinExpr> = Vec::new();
    for atom in atoms {
        let diff = ast_to_lin(m, atom.a).sub(&ast_to_lin(m, atom.b)); // a - b
        let holds = sat.model_holds(atom.lit);
        if atom.is_eq {
            if holds {
                cons.push(Constraint::eq(diff)); // a = b
            } else {
                diseqs.push(diff); // a ≠ b (disjunctive)
            }
        } else {
            cons.push(comparison_constraint(atom.op, holds, diff));
        }
    }
    let mut int_set: BTreeSet<AstId> = BTreeSet::new();
    for c in &cons {
        collect_int_vars(m, &c.expr, &mut int_set);
    }
    for d in &diseqs {
        collect_int_vars(m, d, &mut int_set);
    }
    ArithSystem {
        cons,
        diseqs,
        int_set,
    }
}

/// Decide feasibility of an [`ArithSystem`] (LRA relaxation + integer B&B, with
/// the gcd/divisibility precheck for all-integer equalities). `budget` bounds
/// total work (shared with any surrounding [`theory_check`]).
fn arith_feasible(sys: &ArithSystem, budget: &mut u64) -> Feas {
    // Sound necessary condition: an all-integer equality with no integer
    // solution (by the gcd/divisibility test) is infeasible — this decides
    // parity-style conflicts like 2x = 2y + 1 that branch-and-bound cannot.
    for c in &sys.cons {
        if c.rel == Rel::Eq
            && c.expr.vars().all(|v| sys.int_set.contains(&v))
            && c.expr.integer_equality_infeasible()
        {
            return Feas::Unsat;
        }
    }
    // Integer strict-inequality tightening: `expr < 0` over integer variables is
    // `expr ≤ -1`. This lets Fourier–Motzkin decide many QF_LIA systems directly
    // (e.g. x < y ∧ y < x+1 becomes x+1 ≤ y ∧ y ≤ x, immediately infeasible)
    // instead of relying on branch-and-bound.
    // Also GCD-tighten all-integer `≤`/`<` constraints: dividing by the gcd of
    // the variable coefficients rounds the bound (Omega-test tightening), so
    // Fourier–Motzkin decides integer-infeasible-but-real-feasible systems like
    // `3x−3y ≥ 1 ∧ 3x−3y ≤ 2`. This preserves the integer solution set exactly
    // and is local to the feasibility check (it never feeds interface reasoning).
    let cons: Vec<Constraint> = sys
        .cons
        .iter()
        .map(|c| {
            let all_int = !c.expr.is_constant() && c.expr.vars().all(|v| sys.int_set.contains(&v));
            match c.rel {
                Rel::Lt if all_int => {
                    let le = c.expr.integer_strict_tighten();
                    Constraint::le(le.integer_gcd_tighten_le().unwrap_or(le))
                }
                Rel::Le if all_int => Constraint::le(
                    c.expr
                        .integer_gcd_tighten_le()
                        .unwrap_or_else(|| c.expr.clone()),
                ),
                _ => c.clone(),
            }
        })
        .collect();
    let int_vars: Vec<AstId> = sys.int_set.iter().copied().collect();
    // Branch-and-bound cannot converge on an unbounded Diophantine system
    // (e.g. `6a+4b=2`). Try to construct an integer witness first — it uses no
    // budget and is *verified* against every constraint, so it only ever yields a
    // genuine `Sat` and cannot introduce unsoundness. Running it before B&B also
    // preserves the shared budget for the Nelson–Oppen interface phase.
    if let Some(a) = dioph_witness(&cons, &sys.diseqs, &int_vars) {
        return Feas::Sat(a);
    }
    // Branch-and-bound runs on a *copy* of the budget: on an unbounded system it
    // can otherwise drain the shared budget the Nelson–Oppen interface phase
    // needs, turning an Omega-decided `sat` into a spurious `unknown`. Per-call
    // and per-round bounds still guarantee termination.
    let mut bb_budget = *budget;
    let feas = integer_feasible(&cons, &sys.diseqs, &int_vars, &mut bb_budget, 0);
    // Omega-style last resort when B&B gave up on a pure-integer system:
    // eliminate every variable by Fourier–Motzkin, GCD-tightening the residual
    // constraints after each step. Because tightening preserves the integer
    // solutions and FM preserves real feasibility, a derived contradiction proves
    // genuine integer infeasibility (unbounded systems B&B cannot refute). Runs
    // only on the hard `unknown` cases, with its own bounded budget.
    if matches!(feas, Feas::Unknown) {
        let all_integer = cons
            .iter()
            .all(|c| c.expr.vars().all(|v| sys.int_set.contains(&v)));
        if all_integer {
            let mut fm_budget: u64 = 60_000;
            if integer_fm_unsat(&cons, &int_vars, &mut fm_budget) {
                return Feas::Unsat;
            }
            // Dark-shadow SAT: a verified witness upgrades unknown → sat for
            // unbounded feasible systems B&B cannot converge on.
            let mut dark_budget: u64 = 60_000;
            if let Some(a) = omega_dark_witness(&cons, &sys.diseqs, &int_vars, &mut dark_budget) {
                return Feas::Sat(a);
            }
        }
    }
    feas
}

/// Omega-test **dark shadow** witness for a pure-integer system: try to prove
/// satisfiability by eliminating every variable with the dark-shadow projection
/// (Fourier–Motzkin plus the `(α−1)(β−1)` tightening term that guarantees an
/// integer between the bounds), then back-substituting to build a concrete
/// assignment. The returned assignment is **verified against every original
/// constraint and disequality**, so — exactly like [`dioph_witness`] — a bug in
/// the shadow logic can only cost completeness (a missed `sat`), never
/// soundness. `None` when the dark shadow is infeasible (the tight cases that
/// need the gray shadow), the budget is exhausted, or the witness fails to
/// verify.
fn omega_dark_witness(
    cons: &[Constraint],
    diseqs: &[LinExpr],
    int_vars: &[AstId],
    budget: &mut u64,
) -> Option<Assignment> {
    let zero = Rational::from_integer(Int::from(0));
    let one = Rational::from_integer(Int::from(1));
    let neg_one = one.neg();
    let int_set: BTreeSet<AstId> = int_vars.iter().copied().collect();
    let coeff = |e: &LinExpr, x: AstId| -> Rational {
        e.terms()
            .find(|(v, _)| *v == x)
            .map(|(_, c)| c.clone())
            .unwrap_or_else(|| zero.clone())
    };
    // Eliminate equalities FIRST by substitution: a unit-coefficient integer
    // variable, or a lone variable `a·x + k = 0` when `a | k`. The dark shadow's
    // interval widening is valid only for genuine inequalities, so equalities
    // must be removed first (else e.g. `2b = 6` yields a spurious `1 ≤ 0`). Bail
    // (a sound missed `sat`) on any equality this cannot eliminate.
    let mut eqs: Vec<LinExpr> = cons
        .iter()
        .filter(|c| c.rel == Rel::Eq)
        .map(|c| c.expr.clone())
        .collect();
    let mut work: Vec<LinExpr> = cons
        .iter()
        .filter(|c| c.rel != Rel::Eq)
        .map(|c| match c.rel {
            Rel::Lt => c.expr.integer_strict_tighten(),
            _ => c.expr.clone(),
        })
        .collect();
    let mut eq_subs: Vec<(AstId, LinExpr)> = Vec::new();
    let mut eliminated: BTreeSet<AstId> = BTreeSet::new();
    'elim: loop {
        for i in 0..eqs.len() {
            // Choose how to solve equation `i` for one of its variables:
            // a ±1-coefficient variable, or a lone variable `a·x + k = 0` with
            // integral `x = −k/a`. Compute `(v, v_expr)` before mutating `eqs`.
            let choice: Option<(AstId, LinExpr)> = {
                let e = &eqs[i];
                if let Some((v, cv)) = e
                    .terms()
                    .find(|(v, c)| int_set.contains(v) && (**c == one || **c == neg_one))
                    .map(|(v, c)| (v, c.clone()))
                {
                    let rest = e.sub(&LinExpr::var(v).scale(&cv));
                    Some((v, rest.scale(&cv.neg().recip())))
                } else if e.vars().count() == 1 {
                    let (v, a) = e.terms().next().map(|(v, c)| (v, c.clone())).unwrap();
                    let xval = &e.const_term().neg() / &a;
                    (int_set.contains(&v) && xval.is_integer())
                        .then(|| (v, LinExpr::constant(xval)))
                } else {
                    None
                }
            };
            if let Some((v, v_expr)) = choice {
                eqs.remove(i);
                for eq in &mut eqs {
                    *eq = substitute_lin(eq, v, &v_expr);
                }
                for e in &mut work {
                    *e = substitute_lin(e, v, &v_expr);
                }
                for (_, se) in &mut eq_subs {
                    *se = substitute_lin(se, v, &v_expr);
                }
                eliminated.insert(v);
                eq_subs.push((v, v_expr));
                continue 'elim;
            }
        }
        break;
    }
    // Any equality left must be the trivial `0 = 0`; otherwise we cannot decide.
    for e in &eqs {
        if e.as_constant() != Some(zero.clone()) {
            return None;
        }
    }
    // Eliminate each remaining (non-equality-bound) variable by the dark shadow,
    // recording its lower/upper bounds for back-substitution.
    let mut steps: Vec<(AstId, Vec<LinExpr>, Vec<LinExpr>)> = Vec::new();
    for &x in int_vars {
        if eliminated.contains(&x) {
            continue;
        }
        let (mut lower, mut upper, mut rest) = (Vec::new(), Vec::new(), Vec::new());
        for e in &work {
            let c = coeff(e, x);
            if c.is_zero() {
                rest.push(e.clone());
            } else if c < zero {
                lower.push(e.clone());
            } else {
                upper.push(e.clone());
            }
        }
        for l in &lower {
            let alpha = coeff(l, x).neg(); // α > 0 (−coeff)
            for u in &upper {
                if *budget == 0 {
                    return None;
                }
                *budget -= 1;
                let beta = coeff(u, x); // β > 0
                // Real resolvent β·l + α·u cancels x; the dark-shadow term
                // (α−1)(β−1) makes an integer between the bounds sufficient.
                let mut r = l.scale(&beta).add(&u.scale(&alpha));
                let extra = &(&alpha - &one) * &(&beta - &one);
                r = r.add(&LinExpr::constant(extra.clone()));
                rest.push(r);
            }
        }
        steps.push((x, lower, upper));
        work = rest;
    }
    // Dark shadow infeasible if a constant residual is positive, or (defensively)
    // if a non-constant residual remains (some variable was not integer).
    if work
        .iter()
        .any(|e| e.as_constant().is_none_or(|k| k > zero))
    {
        return None;
    }
    // Back-substitute in reverse elimination order: each variable's bounds now
    // involve only already-assigned variables.
    let mut a: Assignment = int_vars.iter().map(|&v| (v, zero.clone())).collect();
    for (x, lower, upper) in steps.iter().rev() {
        let at_zero = |e: &LinExpr| -> Rational {
            let mut t = a.clone();
            t.insert(*x, zero.clone());
            e.eval(&t)
        };
        // Lower bounds: −αx + l₀ ≤ 0 ⟹ x ≥ ⌈l₀/α⌉.
        let mut lo: Option<Rational> = None;
        for l in lower {
            let alpha = coeff(l, *x).neg();
            let b = Rational::from_integer((&at_zero(l) / &alpha).ceil());
            lo = Some(lo.map_or_else(
                || b.clone(),
                |m: Rational| if b > m { b.clone() } else { m },
            ));
        }
        // Upper bounds: βx + u₀ ≤ 0 ⟹ x ≤ ⌊−u₀/β⌋.
        let mut hi: Option<Rational> = None;
        for u in upper {
            let beta = coeff(u, *x);
            let b = Rational::from_integer((&at_zero(u).neg() / &beta).floor());
            hi = Some(hi.map_or_else(
                || b.clone(),
                |m: Rational| if b < m { b.clone() } else { m },
            ));
        }
        let x_val = lo.or(hi).unwrap_or_else(|| zero.clone());
        a.insert(*x, x_val);
    }
    // Assign the equality-eliminated variables from their substitutions (each is
    // now in terms of the dark-shadow-assigned variables).
    for (v, v_expr) in eq_subs.iter().rev() {
        let val = v_expr.eval(&a);
        a.insert(*v, val);
    }
    // Safety net: accept only a genuinely satisfying assignment.
    let ok = cons.iter().all(|c| {
        let v = c.expr.eval(&a);
        match c.rel {
            Rel::Le => v <= zero,
            Rel::Lt => v < zero,
            Rel::Eq => v == zero,
        }
    }) && diseqs.iter().all(|d| d.eval(&a) != zero);
    ok.then_some(a)
}

/// A sound (incomplete) integer-infeasibility test for an all-integer system:
/// project every variable out by Fourier–Motzkin, GCD-tightening the residual
/// `≤` constraints after each elimination. Returns `true` only when a constant
/// contradiction (`k ≤ 0` with `k > 0`) is derived — which, because every step
/// is integer-solution-preserving, proves the system has no integer solution.
/// Returns `false` (undecided) if the budget is exhausted or no contradiction
/// appears.
fn integer_fm_unsat(cons: &[Constraint], int_vars: &[AstId], budget: &mut u64) -> bool {
    // Normalize to `expr ≤ 0`: equalities become two inequalities; strict
    // inequalities are integer-tightened to `≤`.
    let mut work: Vec<Constraint> = Vec::new();
    for c in cons {
        match c.rel {
            Rel::Le => work.push(c.clone()),
            Rel::Lt => work.push(Constraint::le(c.expr.integer_strict_tighten())),
            Rel::Eq => {
                work.push(Constraint::le(c.expr.clone()));
                work.push(Constraint::le(c.expr.neg()));
            }
        }
    }
    fn tighten(work: &mut [Constraint]) {
        for c in work.iter_mut() {
            if let Some(t) = c.expr.integer_gcd_tighten_le() {
                *c = Constraint::le(t);
            }
        }
    }
    // A constant `k ≤ 0` with `k > 0` is a contradiction.
    fn contradiction(work: &[Constraint]) -> bool {
        let zero = Rational::from_integer(Int::from(0));
        work.iter()
            .filter_map(|c| c.expr.as_constant())
            .any(|k| k > zero)
    }
    tighten(&mut work);
    if contradiction(&work) {
        return true;
    }
    for &v in int_vars {
        match project(&work, v, budget) {
            Some(w) => work = w,
            None => return false, // budget exhausted: undecided
        }
        tighten(&mut work);
        if contradiction(&work) {
            return true;
        }
    }
    false
}

/// Extended Euclid: returns `(g, x, y)` with `a·x + b·y = g = gcd(a,b)`.
fn egcd(a: i128, b: i128) -> (i128, i128, i128) {
    if b == 0 {
        (a, 1, 0)
    } else {
        let (g, x, y) = egcd(b, a % b);
        (g, y, x - (a / b) * y)
    }
}

fn gcd_i128(a: i128, b: i128) -> i128 {
    if b == 0 { a.abs() } else { gcd_i128(b, a % b) }
}

/// A particular integer solution of `Σ coeffs[i]·xᵢ = target`, or `None` if the
/// gcd of the coefficients does not divide `target` (unsolvable) or an
/// intermediate product overflows `i128`.
fn solve_dioph(coeffs: &[i128], target: i128) -> Option<Vec<i128>> {
    match coeffs {
        [] => (target == 0).then(Vec::new),
        [a] => {
            if *a == 0 {
                (target == 0).then(|| alloc::vec![0])
            } else {
                (target % a == 0).then(|| alloc::vec![target / a])
            }
        }
        [a, rest @ ..] => {
            let a = *a;
            let g_rest = rest.iter().fold(0i128, |g, &x| gcd_i128(g, x));
            let (g, s, _) = egcd(a, g_rest);
            if g == 0 || target % g != 0 {
                return None;
            }
            let mult = target / g;
            let x1 = s.checked_mul(mult)?;
            let remaining = target.checked_sub(a.checked_mul(x1)?)?;
            let mut sol = alloc::vec![x1];
            sol.extend(solve_dioph(rest, remaining)?);
            Some(sol)
        }
    }
}

/// Try to build a verified integer witness for a system whose only equality is a
/// two-variable linear Diophantine `c₁·v₁ + c₂·v₂ + k = 0`. Searches the general
/// solution `(v₁,v₂) = (x₀,y₀) + t·(c₂/g, −c₁/g)` over a bounded `t`, sets the
/// other integer variables to 0, and returns the first assignment that satisfies
/// every constraint and disequality. `None` if the pattern doesn't match or no
/// witness verifies.
fn dioph_witness(
    cons: &[Constraint],
    diseqs: &[LinExpr],
    int_vars: &[AstId],
) -> Option<Assignment> {
    let int_set: BTreeSet<AstId> = int_vars.iter().copied().collect();
    let mut eqs: Vec<LinExpr> = cons
        .iter()
        .filter(|c| c.rel == Rel::Eq)
        .map(|c| c.expr.clone())
        .collect();
    if eqs.is_empty() {
        return None;
    }
    let one = Rational::from_integer(Int::from(1));
    let neg_one = Rational::from_integer(Int::from(-1));
    let zero = Rational::from_integer(Int::from(0));

    // Eliminate integer variables that occur with coefficient ±1 in some
    // equation: solve that equation for the variable and substitute it into the
    // remaining equations (and prior substitutions). This reduces a system to a
    // single residual Diophantine equation the witness search below can handle.
    let mut subs: Vec<(AstId, LinExpr)> = Vec::new();
    loop {
        let found = eqs.iter().enumerate().find_map(|(i, e)| {
            e.terms()
                .find(|(v, c)| int_set.contains(v) && (**c == one || **c == neg_one))
                .map(|(v, c)| (i, v, c.clone()))
        });
        let Some((i, v, cv)) = found else { break };
        let e = eqs.remove(i);
        let rest = e.sub(&LinExpr::var(v).scale(&cv)); // e = cv·v + rest
        let v_expr = rest.scale(if cv == one { &neg_one } else { &one }); // v = -rest/cv
        for eq in &mut eqs {
            *eq = substitute_lin(eq, v, &v_expr);
        }
        for (_, se) in &mut subs {
            *se = substitute_lin(se, v, &v_expr);
        }
        subs.push((v, v_expr));
    }
    // A residual equation that is a nonzero constant is infeasible on this path.
    if eqs
        .iter()
        .any(|e| e.is_constant() && e.as_constant().map(|c| !c.is_zero()) == Some(true))
    {
        return None;
    }
    eqs.retain(|e| !e.is_constant()); // drop trivial 0 = 0
    if eqs.len() > 1 {
        return None; // more than one residual equation: too complex here
    }

    // Assemble and verify: place values for the residual equation's variables,
    // back-substitute the eliminated variables, set the rest to 0, and check
    // every constraint (including integrality of the eliminated variables).
    let verify = |free: &BTreeMap<AstId, i128>| -> Option<Assignment> {
        if free.values().any(|&x| i64::try_from(x).is_err()) {
            return None;
        }
        let mut a: Assignment = int_vars.iter().map(|&v| (v, zero.clone())).collect();
        for (&v, &x) in free {
            a.insert(v, Rational::from_integer(Int::from(x as i64)));
        }
        for (v, e) in &subs {
            let val = e.eval(&a);
            if int_set.contains(v) && !val.is_integer() {
                return None;
            }
            a.insert(*v, val);
        }
        let ok = cons.iter().all(|c| {
            let val = c.expr.eval(&a);
            match c.rel {
                Rel::Le => val <= zero,
                Rel::Lt => val < zero,
                Rel::Eq => val == zero,
            }
        }) && diseqs.iter().all(|d| d.eval(&a) != zero);
        ok.then_some(a)
    };

    let as_i128 = |r: &Rational| -> Option<i128> {
        r.is_integer()
            .then(|| r.to_integer())
            .flatten()
            .and_then(|i| i.to_i64())
            .map(|n| n as i128)
    };
    if eqs.is_empty() {
        return verify(&BTreeMap::new()); // fully determined by the substitutions
    }
    let e = &eqs[0];
    let terms: Vec<(AstId, i128)> = e
        .terms()
        .map(|(v, c)| as_i128(c).map(|n| (v, n)))
        .collect::<Option<_>>()?;
    if terms.is_empty() || terms.iter().any(|&(_, c)| c == 0) {
        return None;
    }
    let k = as_i128(e.const_term())?;
    let rhs = -k;
    let vars: Vec<AstId> = terms.iter().map(|&(v, _)| v).collect();
    let coeffs: Vec<i128> = terms.iter().map(|&(_, c)| c).collect();
    if terms.len() == 2 {
        let (c1, c2) = (coeffs[0], coeffs[1]);
        let (g, s, t_e) = egcd(c1, c2);
        let gg = g.abs();
        if gg == 0 || rhs % gg != 0 {
            return None;
        }
        let mult = rhs / (c1 * s + c2 * t_e);
        let (x0, y0) = (s * mult, t_e * mult);
        let (dx, dy) = (c2 / gg, -(c1 / gg));
        for t in -256i128..=256 {
            let free = BTreeMap::from([(vars[0], x0 + dx * t), (vars[1], y0 + dy * t)]);
            if let Some(a) = verify(&free) {
                return Some(a);
            }
        }
        None
    } else {
        let sol = solve_dioph(&coeffs, rhs)?;
        verify(&vars.iter().copied().zip(sol).collect())
    }
}

/// Replace variable `v` in `e` by the linear expression `v_expr`.
fn substitute_lin(e: &LinExpr, v: AstId, v_expr: &LinExpr) -> LinExpr {
    match e.terms().find(|(u, _)| *u == v).map(|(_, c)| c.clone()) {
        Some(c) => e.sub(&LinExpr::var(v).scale(&c)).add(&v_expr.scale(&c)),
        None => e.clone(),
    }
}

/// Does the arithmetic system *entail* `u = v`? `Some(true)` iff neither `u < v`
/// nor `u > v` is consistent with it — i.e. every solution has `u = v`. `None` if
/// the shared work `budget` was exhausted. Used to share implied equalities with
/// the EUF theory (Nelson–Oppen).
fn arith_entails_eq(
    m: &AstManager,
    sys: &ArithSystem,
    u: AstId,
    v: AstId,
    budget: &mut u64,
) -> Option<bool> {
    let diff = ast_to_lin(m, u).sub(&ast_to_lin(m, v)); // u - v
    let mut lt = sys.cons.clone();
    lt.push(Constraint::lt(diff.clone())); // u - v < 0
    match model_with_diseqs_budgeted(&lt, &sys.diseqs, budget) {
        SolveOutcome::Sat(_) => return Some(false), // u < v possible ⇒ not entailed
        SolveOutcome::Exhausted => return None,
        SolveOutcome::Unsat => {}
    }
    let mut gt = sys.cons.clone();
    gt.push(Constraint::lt(diff.neg())); // v - u < 0  ⟺  u - v > 0
    match model_with_diseqs_budgeted(&gt, &sys.diseqs, budget) {
        SolveOutcome::Sat(_) => Some(false),
        SolveOutcome::Exhausted => None,
        SolveOutcome::Unsat => Some(true), // neither side possible ⇒ entailed
    }
}

/// The result of the combined theory check for one Boolean assignment.
enum TheoryOutcome {
    /// Consistent: a rational assignment plus the congruence closure (for models).
    Sat(Assignment, Egraph),
    /// Definitively inconsistent — the assignment must be blocked.
    Unsat,
    /// Inconclusive (the arithmetic search gave up).
    Unknown,
}

/// The combined EUF + arithmetic theory check for one Boolean assignment.
///
/// The theories exchange implied equalities between shared (interface) terms in
/// both directions until a fixpoint (deterministic Nelson–Oppen). arith → EUF:
/// an equality the arithmetic theory *entails* is added to the congruence closure
/// (so implied equalities fire congruence). EUF → arith: two interface terms that
/// congruence puts in one class have their equality added to the arithmetic
/// constraints. Each direction only adds genuinely new equalities, so the loop
/// converges.
fn theory_check(
    m: &AstManager,
    euf_eq: &[(Lit, AstId, AstId)],
    euf_roots: &[AstId],
    arith_atoms: &[ArithAtom],
    pred_atoms: &[(Lit, AstId)],
    sat: &Solver,
    budget: &mut u64,
) -> TheoryOutcome {
    // EUF equalities / disequalities implied by the assignment.
    let mut eqs = Vec::new();
    let mut diseqs = Vec::new();
    for &(lit, a, b) in euf_eq {
        if sat.model_holds(lit) {
            eqs.push((a, b));
        } else {
            diseqs.push((a, b));
        }
    }
    let base = build_arith_system(m, arith_atoms, sat);
    let interface = interface_terms(m, euf_roots);

    // Equalities shared across the theory boundary, grown to a fixpoint.
    let mut euf_extra: Vec<(AstId, AstId)> = Vec::new(); // arith → EUF
    let mut arith_extra: Vec<Constraint> = Vec::new(); // EUF → arith
    // Each round adds at least one new equality (bounded by the interface pairs),
    // so this cap is only a backstop against surprises.
    let max_rounds = interface.len() * interface.len() + 4;
    // `budget` (shared across the whole decision) bounds the arithmetic
    // feasibility check and every Nelson–Oppen entailment query.

    for _ in 0..max_rounds {
        // Arithmetic system augmented with the EUF-implied equalities so far.
        let mut sys = ArithSystem {
            cons: base.cons.clone(),
            diseqs: base.diseqs.clone(),
            int_set: base.int_set.clone(),
        };
        sys.cons.extend(arith_extra.iter().cloned());
        let arith = arith_feasible(&sys, &mut *budget);
        if matches!(arith, Feas::Unsat) {
            return TheoryOutcome::Unsat;
        }
        // Congruence closure augmented with the arithmetic-implied equalities.
        let mut all_eqs = eqs.clone();
        all_eqs.extend(euf_extra.iter().cloned());
        let mut g = Egraph::new(m, euf_roots);
        if !g.is_consistent(m, &all_eqs, &diseqs) {
            return TheoryOutcome::Unsat;
        }
        // Predicate congruence: two congruent predicate applications (same class)
        // must have the same truth value; a clash is a conflict.
        for i in 0..pred_atoms.len() {
            for j in (i + 1)..pred_atoms.len() {
                let (li, ti) = pred_atoms[i];
                let (lj, tj) = pred_atoms[j];
                if g.class_of(m, ti) == g.class_of(m, tj)
                    && sat.model_holds(li) != sat.model_holds(lj)
                {
                    return TheoryOutcome::Unsat;
                }
            }
        }

        let mut changed = false;
        for i in 0..interface.len() {
            for j in (i + 1)..interface.len() {
                let (u, v) = (interface[i], interface[j]);
                let same_class = g.class_of(m, u) == g.class_of(m, v);
                let entailed = match arith_entails_eq(m, &sys, u, v, &mut *budget) {
                    Some(e) => e,
                    None => return TheoryOutcome::Unknown, // work budget exhausted
                };
                if entailed && !same_class {
                    euf_extra.push((u, v)); // arith → EUF
                    changed = true;
                } else if same_class && !entailed {
                    // EUF → arith: add u − v = 0.
                    let diff = ast_to_lin(m, u).sub(&ast_to_lin(m, v));
                    arith_extra.push(Constraint::eq(diff));
                    changed = true;
                }
            }
        }
        if !changed {
            return match arith {
                Feas::Sat(assign) => TheoryOutcome::Sat(assign, g),
                Feas::Unknown => TheoryOutcome::Unknown,
                Feas::Unsat => unreachable!(),
            };
        }
    }
    TheoryOutcome::Unknown // did not converge within the round budget
}

/// Record the integer-sorted variables of `e` into `set`.
fn collect_int_vars(m: &AstManager, e: &LinExpr, set: &mut BTreeSet<AstId>) {
    for v in e.vars() {
        if m.is_int_sort(m.get_sort(v)) {
            set.insert(v);
        }
    }
}

/// A cap on lazy DPLL(T) conflict rounds (blocking-clause iterations). Bounds the
/// worst-case exponential enumeration of theory-atom assignments; on exhaustion
/// the result is a sound [`SmtResult::Unknown`].
const DPLL_ROUND_LIMIT: u32 = 5_000;

/// A total work budget for the integer feasibility search: the number of base
/// `model` solves permitted across all branch-and-bound nodes *and* the
/// disequality case split (both worst-case exponential). Bounding their shared
/// total guarantees termination; on exhaustion the search returns
/// [`Feas::Unknown`] rather than guessing, so the verdict stays sound. A complete
/// integer procedure (Omega/Cooper, or B&B with derived bounds) is future work.
const BB_WORK_BUDGET: u64 = 300_000;

/// A depth cap for branch-and-bound recursion, keeping the stack bounded
/// independently of the work budget (a single deep chain must not overflow).
const BB_DEPTH_CAP: u32 = 800;

/// Decide integer feasibility of `cons` ∧ `diseqs` with `int_vars` integral, by
/// branch-and-bound over the LRA relaxation. `budget` (shared with the
/// disequality split) bounds total work; `depth` bounds recursion for stack
/// safety. On exhaustion of either the result is [`Feas::Unknown`].
fn integer_feasible(
    cons: &[Constraint],
    diseqs: &[LinExpr],
    int_vars: &[AstId],
    budget: &mut u64,
    depth: u32,
) -> Feas {
    if depth >= BB_DEPTH_CAP {
        return Feas::Unknown; // stack budget exhausted: don't guess
    }
    let model = match model_with_diseqs_budgeted(cons, diseqs, budget) {
        SolveOutcome::Sat(m) => m,
        SolveOutcome::Unsat => return Feas::Unsat,
        SolveOutcome::Exhausted => return Feas::Unknown,
    };
    // Find an integer variable whose relaxed value is fractional.
    let fractional = int_vars.iter().find_map(|&v| {
        let val = model.get(&v).cloned().unwrap_or_else(rat_zero);
        (!val.is_integer()).then_some((v, val))
    });
    let Some((v, val)) = fractional else {
        return Feas::Sat(model); // all integer variables are already integral
    };
    // Branch: v ≤ ⌊val⌋  OR  v ≥ ⌈val⌉.
    let floor = Rational::from_integer(val.floor());
    let ceil = Rational::from_integer(val.ceil());
    let mut low = cons.to_vec();
    low.push(Constraint::le(
        LinExpr::var(v).sub(&LinExpr::constant(floor)),
    )); // v - ⌊val⌋ ≤ 0
    let lo = integer_feasible(&low, diseqs, int_vars, budget, depth + 1);
    if let Feas::Sat(a) = lo {
        return Feas::Sat(a);
    }
    let mut high = cons.to_vec();
    high.push(Constraint::le(
        LinExpr::constant(ceil).sub(&LinExpr::var(v)),
    )); // ⌈val⌉ - v ≤ 0
    let hi = integer_feasible(&high, diseqs, int_vars, budget, depth + 1);
    match hi {
        Feas::Sat(a) => Feas::Sat(a),
        // Both branches exhausted with no witness: unsat only if *both* were
        // definitively infeasible; otherwise the result is inconclusive.
        Feas::Unsat => lo, // lo is Unsat or Unknown here
        Feas::Unknown => Feas::Unknown,
    }
}

fn rat_zero() -> Rational {
    Rational::from_integer(Int::from(0))
}

/// The linear constraint for `(op a b)` (with `diff = a - b`) at truth `holds`.
fn comparison_constraint(op: ArithOp, holds: bool, diff: LinExpr) -> Constraint {
    // Each row: the constraint on `diff` for the atom being true, then negated.
    let (expr, strict) = match (op, holds) {
        (ArithOp::Le, true) => (diff, false),        // a ≤ b : diff ≤ 0
        (ArithOp::Le, false) => (diff.neg(), true),  // a > b : -diff < 0
        (ArithOp::Lt, true) => (diff, true),         // a < b : diff < 0
        (ArithOp::Lt, false) => (diff.neg(), false), // a ≥ b : -diff ≤ 0
        (ArithOp::Ge, true) => (diff.neg(), false),  // a ≥ b : -diff ≤ 0
        (ArithOp::Ge, false) => (diff, true),        // a < b : diff < 0
        (ArithOp::Gt, true) => (diff.neg(), true),   // a > b : -diff < 0
        (ArithOp::Gt, false) => (diff, false),       // a ≤ b : diff ≤ 0
        _ => (diff, false),
    };
    if strict {
        Constraint::lt(expr)
    } else {
        Constraint::le(expr)
    }
}

/// Convert an arithmetic AST term to a linear expression. Non-linear or
/// non-arithmetic subterms are treated as opaque variables (sound: they become
/// unconstrained).
pub fn ast_to_lin(m: &AstManager, t: AstId) -> LinExpr {
    if let Some(r) = m.as_numeral(t) {
        return LinExpr::constant(r);
    }
    let Some(op) = m.arith_op(t) else {
        return LinExpr::var(t); // uninterpreted constant / variable
    };
    let args = m.app_args(t);
    match op {
        ArithOp::Add => args
            .iter()
            .fold(LinExpr::new(), |e, &a| e.add(&ast_to_lin(m, a))),
        ArithOp::Sub if args.len() == 1 => ast_to_lin(m, args[0]).neg(),
        ArithOp::Sub => {
            let mut e = ast_to_lin(m, args[0]);
            for &a in &args[1..] {
                e = e.sub(&ast_to_lin(m, a));
            }
            e
        }
        ArithOp::Uminus => ast_to_lin(m, args[0]).neg(),
        // to_real preserves the numeric value, so it is the identity map on the
        // linear representation.
        ArithOp::ToReal => ast_to_lin(m, args[0]),
        ArithOp::Mul => {
            let mut scalar = one();
            let mut nonconst: Option<LinExpr> = None;
            for &a in args {
                let e = ast_to_lin(m, a);
                match e.as_constant() {
                    Some(c) => scalar = &scalar * &c,
                    None if nonconst.is_none() => nonconst = Some(e),
                    None => return LinExpr::var(t), // nonlinear: two variable factors
                }
            }
            match nonconst {
                Some(e) => e.scale(&scalar),
                None => LinExpr::constant(scalar),
            }
        }
        _ => LinExpr::var(t), // to_real/div/mod/… : opaque for now
    }
}

fn one() -> puremp::Rational {
    puremp::Rational::from_integer(puremp::Int::from(1))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::symbol::Symbol;

    fn constant(m: &mut AstManager, name: &str, sort: AstId) -> AstId {
        let d = m.mk_func_decl(Symbol::new(name), &[], sort);
        m.mk_const(d)
    }

    #[test]
    fn transitivity_is_unsat() {
        let mut m = AstManager::new();
        let s = m.mk_uninterpreted_sort(Symbol::new("S"));
        let a = constant(&mut m, "a", s);
        let b = constant(&mut m, "b", s);
        let c = constant(&mut m, "c", s);
        // (and (= a b) (= b c) (not (= a c)))
        let ab = m.mk_eq(a, b);
        let bc = m.mk_eq(b, c);
        let ac = m.mk_eq(a, c);
        let nac = m.mk_not(ac);
        let f = m.mk_and(&[ab, bc, nac]);
        assert_eq!(check(&m, f), SmtResult::Unsat);
    }

    #[test]
    fn consistent_equalities_are_sat() {
        let mut m = AstManager::new();
        let s = m.mk_uninterpreted_sort(Symbol::new("S"));
        let a = constant(&mut m, "a", s);
        let b = constant(&mut m, "b", s);
        let c = constant(&mut m, "c", s);
        // (and (= a b) (not (= a c)))
        let ab = m.mk_eq(a, b);
        let ac = m.mk_eq(a, c);
        let nac = m.mk_not(ac);
        let f = m.mk_and(&[ab, nac]);
        assert_eq!(check(&m, f), SmtResult::Sat);
    }

    #[test]
    fn congruence_is_unsat() {
        let mut m = AstManager::new();
        let s = m.mk_uninterpreted_sort(Symbol::new("S"));
        let a = constant(&mut m, "a", s);
        let b = constant(&mut m, "b", s);
        let f = m.mk_func_decl(Symbol::new("f"), &[s], s);
        let fa = m.mk_app(f, &[a]);
        let fb = m.mk_app(f, &[b]);
        // (and (= a b) (not (= (f a) (f b))))
        let ab = m.mk_eq(a, b);
        let fab = m.mk_eq(fa, fb);
        let nfab = m.mk_not(fab);
        let formula = m.mk_and(&[ab, nfab]);
        assert_eq!(check(&m, formula), SmtResult::Unsat);
    }

    #[test]
    fn disjunctive_case_split() {
        let mut m = AstManager::new();
        let s = m.mk_uninterpreted_sort(Symbol::new("S"));
        let a = constant(&mut m, "a", s);
        let b = constant(&mut m, "b", s);
        let c = constant(&mut m, "c", s);
        // (and (or (= a b) (= a c)) (not (= a b)) (not (= a c))) — unsat via both
        // branches; exercises the SAT case-split + theory blocking loop.
        let ab = m.mk_eq(a, b);
        let ac = m.mk_eq(a, c);
        let or = m.mk_or(&[ab, ac]);
        let nab = m.mk_not(ab);
        let nac = m.mk_not(ac);
        let f = m.mk_and(&[or, nab, nac]);
        assert_eq!(check(&m, f), SmtResult::Unsat);

        // Replace the second disequality's target so a=c becomes possible → sat.
        let g = m.mk_and(&[or, nab]);
        assert_eq!(check(&m, g), SmtResult::Sat);
    }

    #[test]
    fn pure_propositional_still_decided() {
        let mut m = AstManager::new();
        let p = m.mk_bool_const("p");
        let np = m.mk_not(p);
        let f = m.mk_and(&[p, np]);
        assert_eq!(check(&m, f), SmtResult::Unsat);
    }

    #[test]
    fn qf_lra_contradictory_bounds() {
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let five = m.mk_int(5);
        let six = m.mk_int(6);
        // (and (<= x 5) (>= x 6))
        let le = m.mk_le(x, five);
        let ge = m.mk_ge(x, six);
        let f = m.mk_and(&[le, ge]);
        assert_eq!(check(&m, f), SmtResult::Unsat);
    }

    #[test]
    fn qf_lra_satisfiable_bounds() {
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let three = m.mk_int(3);
        let five = m.mk_int(5);
        let ge = m.mk_ge(x, three);
        let le = m.mk_le(x, five);
        let f = m.mk_and(&[ge, le]);
        assert_eq!(check(&m, f), SmtResult::Sat);
    }

    #[test]
    fn qf_lra_sum_bound_unsat() {
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let y = m.mk_int_const("y");
        let one = m.mk_int(1);
        // (and (>= x 1) (>= y 1) (<= (+ x y) 1))
        let gx = m.mk_ge(x, one);
        let gy = m.mk_ge(y, one);
        let sum = m.mk_add(&[x, y]);
        let le = m.mk_le(sum, one);
        let f = m.mk_and(&[gx, gy, le]);
        assert_eq!(check(&m, f), SmtResult::Unsat);
    }

    #[test]
    fn qf_lra_strict_cycle_unsat() {
        let mut m = AstManager::new();
        let x = m.mk_real_const("x");
        let y = m.mk_real_const("y");
        // (and (< x y) (< y x))
        let xy = m.mk_lt(x, y);
        let yx = m.mk_lt(y, x);
        let f = m.mk_and(&[xy, yx]);
        assert_eq!(check(&m, f), SmtResult::Unsat);
    }

    #[test]
    fn qf_lra_disequality_case_split() {
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let five = m.mk_int(5);
        // (and (<= x 5) (>= x 5) (not (= x 5))) — pins x=5 then forbids it → unsat
        let le = m.mk_le(x, five);
        let ge = m.mk_ge(x, five);
        let eq = m.mk_eq(x, five);
        let neq = m.mk_not(eq);
        let f = m.mk_and(&[le, ge, neq]);
        assert_eq!(check(&m, f), SmtResult::Unsat);
    }

    #[test]
    fn qf_lra_disjunction_forces_conflict() {
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let zero = m.mk_int(0);
        let ten = m.mk_int(10);
        let five = m.mk_int(5);
        // (and (or (<= x 0) (>= x 10)) (= x 5)) — x=5 refutes both disjuncts → unsat
        let le0 = m.mk_le(x, zero);
        let ge10 = m.mk_ge(x, ten);
        let or = m.mk_or(&[le0, ge10]);
        let eq5 = m.mk_eq(x, five);
        let f = m.mk_and(&[or, eq5]);
        assert_eq!(check(&m, f), SmtResult::Unsat);
    }

    #[test]
    fn qf_lia_no_integer_between_zero_and_one() {
        // (and (< 0 x) (< x 1)) with x : Int — real-feasible but integer-infeasible.
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let zero = m.mk_int(0);
        let one = m.mk_int(1);
        let lo = m.mk_lt(zero, x);
        let hi = m.mk_lt(x, one);
        let f = m.mk_and(&[lo, hi]);
        assert_eq!(check(&m, f), SmtResult::Unsat);
    }

    #[test]
    fn qf_lia_fractional_relaxation_has_integer_point() {
        // (and (<= 3 (* 2 x)) (<= (* 2 x) 5)) with x : Int — x ∈ [1.5, 2.5], so
        // x = 2 witnesses satisfiability though the relaxation corner is fractional.
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let two = m.mk_int(2);
        let three = m.mk_int(3);
        let five = m.mk_int(5);
        let twox = m.mk_mul(&[two, x]);
        let lo = m.mk_le(three, twox);
        let hi = m.mk_le(twox, five);
        let f = m.mk_and(&[lo, hi]);
        assert_eq!(check(&m, f), SmtResult::Sat);
    }

    #[test]
    fn real_variable_between_zero_and_one_is_sat() {
        // The same bounds over Real are satisfiable (x = 1/2): no integrality.
        let mut m = AstManager::new();
        let x = m.mk_real_const("x");
        let zero = m.mk_int(0);
        let one = m.mk_int(1);
        let lo = m.mk_lt(zero, x);
        let hi = m.mk_lt(x, one);
        let f = m.mk_and(&[lo, hi]);
        assert_eq!(check(&m, f), SmtResult::Sat);
    }

    #[test]
    fn model_assigns_consistent_arith_value() {
        // (and (>= x 3) (<= x 5)) with x : Int — the model must satisfy both.
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let three = m.mk_int(3);
        let five = m.mk_int(5);
        let ge = m.mk_ge(x, three);
        let le = m.mk_le(x, five);
        let f = m.mk_and(&[ge, le]);
        let (res, model) = check_model(&m, f);
        assert_eq!(res, SmtResult::Sat);
        let mut model = model.unwrap();
        match model.eval(&m, x) {
            Value::Num(v, true) => {
                assert!(v >= rat(&m, 3) && v <= rat(&m, 5) && v.is_integer());
            }
            other => panic!("expected an Int value, got {other:?}"),
        }
    }

    #[test]
    fn model_renders_bool_and_real() {
        let mut m = AstManager::new();
        let p = m.mk_bool_const("p");
        let r = m.mk_real_const("r");
        let half = m.mk_numeral(
            puremp::Rational::new(puremp::Int::from(1), puremp::Int::from(2)),
            false,
        );
        let eq = m.mk_eq(r, half);
        let f = m.mk_and(&[p, eq]);
        let (res, model) = check_model(&m, f);
        assert_eq!(res, SmtResult::Sat);
        let mut model = model.unwrap();
        assert_eq!(model.value_string(&m, p), "true");
        assert_eq!(model.value_string(&m, r), "(/ 1.0 2.0)");
    }

    #[test]
    fn model_shares_class_for_equal_uninterp() {
        // a = b, a ≠ c → a and b share a class; c differs.
        let mut m = AstManager::new();
        let s = m.mk_uninterpreted_sort(Symbol::new("S"));
        let a = constant(&mut m, "a", s);
        let b = constant(&mut m, "b", s);
        let c = constant(&mut m, "c", s);
        let ab = m.mk_eq(a, b);
        let ac = m.mk_eq(a, c);
        let nac = m.mk_not(ac);
        let f = m.mk_and(&[ab, nac]);
        let (res, model) = check_model(&m, f);
        assert_eq!(res, SmtResult::Sat);
        let mut model = model.unwrap();
        assert_eq!(model.value_string(&m, a), model.value_string(&m, b));
        assert_ne!(model.value_string(&m, a), model.value_string(&m, c));
    }

    fn rat(_m: &AstManager, n: i64) -> puremp::Rational {
        puremp::Rational::from_integer(puremp::Int::from(n))
    }

    #[test]
    fn congruence_on_int_range_function_unsat() {
        // f : Int -> Int, (and (= x y) (not (= (f x) (f y)))). Even though the
        // equality of applications is arithmetic-sorted, EUF congruence must
        // still fire from x = y. (Regression: previously reported sat.)
        let mut m = AstManager::new();
        let int = m.mk_int_sort();
        let x = m.mk_int_const("x");
        let y = m.mk_int_const("y");
        let f = m.mk_func_decl(Symbol::new("f"), &[int], int);
        let fx = m.mk_app(f, &[x]);
        let fy = m.mk_app(f, &[y]);
        let eq = m.mk_eq(x, y);
        let feq = m.mk_eq(fx, fy);
        let nfeq = m.mk_not(feq);
        let f = m.mk_and(&[eq, nfeq]);
        assert_eq!(check(&m, f), SmtResult::Unsat);
    }

    #[test]
    fn congruence_on_int_range_function_sat() {
        // Without x = y, distinct f(x), f(y) is fine.
        let mut m = AstManager::new();
        let int = m.mk_int_sort();
        let x = m.mk_int_const("x");
        let y = m.mk_int_const("y");
        let f = m.mk_func_decl(Symbol::new("f"), &[int], int);
        let fx = m.mk_app(f, &[x]);
        let fy = m.mk_app(f, &[y]);
        let feq = m.mk_eq(fx, fy);
        let nfeq = m.mk_not(feq);
        assert_eq!(check(&m, nfeq), SmtResult::Sat);
    }

    #[test]
    fn nelson_oppen_implied_equality_unsat() {
        // (<= x y) ∧ (<= y x) forces x = y in the arithmetic theory; that shared
        // equality must propagate to EUF so congruence gives f(x) = f(y) = a,
        // contradicting f(y) ≠ a. Requires Nelson–Oppen equality sharing.
        let mut m = AstManager::new();
        let s = m.mk_uninterpreted_sort(Symbol::new("S"));
        let int = m.mk_int_sort();
        let x = m.mk_int_const("x");
        let y = m.mk_int_const("y");
        let a = constant(&mut m, "a", s);
        let f = m.mk_func_decl(Symbol::new("f"), &[int], s);
        let fx = m.mk_app(f, &[x]);
        let fy = m.mk_app(f, &[y]);
        let le1 = m.mk_le(x, y);
        let le2 = m.mk_le(y, x);
        let e1 = m.mk_eq(fx, a);
        let e2 = m.mk_eq(fy, a);
        let ne2 = m.mk_not(e2);
        let formula = m.mk_and(&[le1, le2, e1, ne2]);
        assert_eq!(check(&m, formula), SmtResult::Unsat);
    }

    #[test]
    fn predicate_congruence_unsat() {
        // p : U -> Bool, a = b, p(a), ¬p(b): congruence forces p(a) = p(b),
        // so the truth values clash. Requires predicate congruence.
        let mut m = AstManager::new();
        let s = m.mk_uninterpreted_sort(Symbol::new("U"));
        let bool_s = m.mk_bool_sort();
        let a = constant(&mut m, "a", s);
        let b = constant(&mut m, "b", s);
        let p = m.mk_func_decl(Symbol::new("p"), &[s], bool_s);
        let pa = m.mk_app(p, &[a]);
        let pb = m.mk_app(p, &[b]);
        let ab = m.mk_eq(a, b);
        let npb = m.mk_not(pb);
        let formula = m.mk_and(&[ab, pa, npb]);
        assert_eq!(check(&m, formula), SmtResult::Unsat);
    }

    #[test]
    fn nelson_oppen_euf_to_arith_unsat() {
        // a = b ⇒ f(a) = f(b) by congruence; with f(a) = x, f(b) = y that forces
        // x = y in the arithmetic theory, contradicting x > y. Requires the
        // EUF→arith direction of equality sharing.
        let mut m = AstManager::new();
        let s = m.mk_uninterpreted_sort(Symbol::new("S"));
        let int = m.mk_int_sort();
        let a = constant(&mut m, "a", s);
        let b = constant(&mut m, "b", s);
        let x = m.mk_int_const("x");
        let y = m.mk_int_const("y");
        let f = m.mk_func_decl(Symbol::new("f"), &[s], int);
        let fa = m.mk_app(f, &[a]);
        let fb = m.mk_app(f, &[b]);
        let ab = m.mk_eq(a, b);
        let e1 = m.mk_eq(fa, x);
        let e2 = m.mk_eq(fb, y);
        let gt = m.mk_gt(x, y);
        let formula = m.mk_and(&[ab, e1, e2, gt]);
        assert_eq!(check(&m, formula), SmtResult::Unsat);
    }

    #[test]
    fn nelson_oppen_no_forced_equality_sat() {
        // With only (<= x y), x = y is not entailed, so f(x) and f(y) may differ.
        let mut m = AstManager::new();
        let s = m.mk_uninterpreted_sort(Symbol::new("S"));
        let int = m.mk_int_sort();
        let x = m.mk_int_const("x");
        let y = m.mk_int_const("y");
        let a = constant(&mut m, "a", s);
        let f = m.mk_func_decl(Symbol::new("f"), &[int], s);
        let fx = m.mk_app(f, &[x]);
        let fy = m.mk_app(f, &[y]);
        let le1 = m.mk_le(x, y);
        let e1 = m.mk_eq(fx, a);
        let e2 = m.mk_eq(fy, a);
        let ne2 = m.mk_not(e2);
        let formula = m.mk_and(&[le1, e1, ne2]);
        assert_eq!(check(&m, formula), SmtResult::Sat);
    }

    #[test]
    fn parity_equation_unsat() {
        // 2x = 2y + 1 has no integer solution (even = odd); the gcd test decides
        // it where branch-and-bound would diverge. Previously wrongly sat.
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let y = m.mk_int_const("y");
        let two = m.mk_int(2);
        let one = m.mk_int(1);
        let twox = m.mk_mul(&[two, x]);
        let twoy = m.mk_mul(&[two, y]);
        let rhs = m.mk_add(&[twoy, one]);
        let eq = m.mk_eq(twox, rhs);
        assert_eq!(check(&m, eq), SmtResult::Unsat);
    }

    #[test]
    fn divisibility_equation_unsat() {
        // 3x = 7 has no integer solution (3 ∤ 7).
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let three = m.mk_int(3);
        let seven = m.mk_int(7);
        let tx = m.mk_mul(&[three, x]);
        let e = m.mk_eq(tx, seven);
        assert_eq!(check(&m, e), SmtResult::Unsat);
    }

    #[test]
    fn divisibility_equation_sat() {
        // 3x = 9 has the solution x = 3.
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let three = m.mk_int(3);
        let nine = m.mk_int(9);
        let tx = m.mk_mul(&[three, x]);
        let e = m.mk_eq(tx, nine);
        assert_eq!(check(&m, e), SmtResult::Sat);
    }

    #[test]
    fn qf_lra_disjunction_sat() {
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let zero = m.mk_int(0);
        let ten = m.mk_int(10);
        let twelve = m.mk_int(12);
        // (and (or (<= x 0) (>= x 10)) (<= x 12)) — satisfiable via 10 ≤ x ≤ 12
        let le0 = m.mk_le(x, zero);
        let ge10 = m.mk_ge(x, ten);
        let or = m.mk_or(&[le0, ge10]);
        let le12 = m.mk_le(x, twelve);
        let f = m.mk_and(&[or, le12]);
        assert_eq!(check(&m, f), SmtResult::Sat);
    }
}
