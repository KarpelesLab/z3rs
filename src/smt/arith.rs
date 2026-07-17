//! A linear real arithmetic theory core — Fourier–Motzkin variable elimination.
//!
//! Decides feasibility of a conjunction of linear constraints over the rationals
//! (the LRA relaxation): each constraint is `Σ cᵢ·xᵢ + k  ⋈  0` with `⋈ ∈ {≤, <,
//! =}`. This is the sound, complete theory check the DPLL(T) loop will call for
//! arithmetic atoms (the counterpart of Z3's `theory_lra` / `simplex`); it is
//! exponential in the worst case but simple and exact. A simplex core replaces
//! it later for performance.
//!
//! Over the integers this decides the real relaxation: it is sound for
//! detecting unsatisfiability but not complete for `Int` (a real solution need
//! not be integral).

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::vec::Vec;

use puremp::{Int, Rational};

use crate::ast::AstId;

fn zero() -> Rational {
    Rational::from_integer(Int::from(0))
}

/// A linear expression `Σ coeffs[v]·v + constant` over rational coefficients.
/// Variables are identified by [`AstId`].
#[derive(Clone, Debug, Default)]
pub struct LinExpr {
    coeffs: BTreeMap<AstId, Rational>,
    constant: Rational,
}

impl LinExpr {
    /// The zero expression.
    pub fn new() -> LinExpr {
        LinExpr {
            coeffs: BTreeMap::new(),
            constant: zero(),
        }
    }

    /// A constant expression.
    pub fn constant(c: Rational) -> LinExpr {
        LinExpr {
            coeffs: BTreeMap::new(),
            constant: c,
        }
    }

    /// The single variable `v` (coefficient 1).
    pub fn var(v: AstId) -> LinExpr {
        let mut e = LinExpr::new();
        e.coeffs.insert(v, Rational::from_integer(Int::from(1)));
        e
    }

    /// Add `k·other` into `self`.
    fn add_scaled(&mut self, other: &LinExpr, k: &Rational) {
        for (v, c) in &other.coeffs {
            let entry = self.coeffs.entry(*v).or_insert_with(zero);
            *entry = &*entry + &(c * k);
            if entry.is_zero() {
                self.coeffs.remove(v);
            }
        }
        self.constant = &self.constant + &(&other.constant * k);
    }

    /// `self + other`.
    pub fn add(&self, other: &LinExpr) -> LinExpr {
        let mut r = self.clone();
        r.add_scaled(other, &Rational::from_integer(Int::from(1)));
        r
    }

    /// `self - other`.
    pub fn sub(&self, other: &LinExpr) -> LinExpr {
        let mut r = self.clone();
        r.add_scaled(other, &Rational::from_integer(Int::from(-1)));
        r
    }

    /// `k · self`.
    pub fn scale(&self, k: &Rational) -> LinExpr {
        let mut r = LinExpr::new();
        r.add_scaled(self, k);
        r
    }

    /// `-self`.
    pub fn neg(&self) -> LinExpr {
        self.scale(&Rational::from_integer(Int::from(-1)))
    }

    fn coeff(&self, v: AstId) -> Rational {
        self.coeffs.get(&v).cloned().unwrap_or_else(zero)
    }

    /// The coefficient of `v` (0 if absent) — public accessor.
    pub fn coeff_of(&self, v: AstId) -> Rational {
        self.coeff(v)
    }

    /// Is this a constant (no variables)?
    pub fn is_constant(&self) -> bool {
        self.coeffs.is_empty()
    }

    /// The constant value if this expression has no variables.
    pub fn as_constant(&self) -> Option<Rational> {
        self.is_constant().then(|| self.constant.clone())
    }

    /// The variables (with nonzero coefficient) mentioned by this expression.
    pub fn vars(&self) -> impl Iterator<Item = AstId> + '_ {
        self.coeffs.keys().copied()
    }

    /// The `(variable, coefficient)` terms.
    pub fn terms(&self) -> impl Iterator<Item = (AstId, &Rational)> + '_ {
        self.coeffs.iter().map(|(&v, c)| (v, c))
    }

    /// The constant term.
    pub fn const_term(&self) -> &Rational {
        &self.constant
    }

    /// Assuming every variable ranges over the integers, is the equation
    /// `self = 0` unsatisfiable? A linear Diophantine equation `Σ aᵢ·xᵢ = -b`
    /// (integer coefficients) has a solution iff `gcd(aᵢ)` divides `b`. Clearing
    /// denominators first makes the coefficients integral. This is a sound
    /// necessary condition — it catches, e.g., `2x − 2y − 1 = 0` (parity) — but
    /// is not by itself complete for systems of equations.
    pub fn integer_equality_infeasible(&self) -> bool {
        if self.coeffs.is_empty() {
            return !self.constant.is_zero();
        }
        // Multiply through by the lcm of all denominators to get integers.
        let mut l = Int::from(1);
        for c in self.coeffs.values() {
            l = l.lcm(c.denominator());
        }
        l = l.lcm(self.constant.denominator());
        let scaled = |r: &Rational| -> Int {
            let factor = l.div_trunc(r.denominator()); // exact: denominator | l
            r.numerator() * &factor
        };
        let mut g = Int::from(0);
        for c in self.coeffs.values() {
            g = g.gcd(&scaled(c));
        }
        let b = scaled(&self.constant);
        if g.is_zero() {
            return !b.is_zero();
        }
        !b.rem_euclid(&g).is_zero()
    }

    /// The left-hand side of the integer-tightened form of a strict constraint
    /// `self < 0`. Over the integers (all variables integral) `self < 0` is
    /// equivalent to `L·self ≤ -1`, i.e. `L·self + 1 ≤ 0`, where `L` clears the
    /// coefficient denominators so `L·self` is integer-valued. Returns that
    /// `L·self + 1`, so the caller can assert it as a non-strict `≤ 0`.
    pub fn integer_strict_tighten(&self) -> LinExpr {
        let mut l = Int::from(1);
        for c in self.coeffs.values() {
            l = l.lcm(c.denominator());
        }
        l = l.lcm(self.constant.denominator());
        let mut e = self.scale(&Rational::from_integer(l));
        e.constant = &e.constant + &Rational::from_integer(Int::from(1));
        e
    }

    /// GCD-tighten the non-strict constraint `self ≤ 0`, assuming every variable
    /// ranges over the integers. With `g = gcd` of the (denominator-cleared)
    /// variable coefficients, `Σ aᵢ·xᵢ ≤ -c` is `Σ(aᵢ/g)·xᵢ ≤ ⌊-c/g⌋` because the
    /// left side is an integer — a strictly tighter bound whenever `g ∤ c`. This
    /// is the Omega-test inequality tightening: it makes Fourier–Motzkin decide
    /// systems like `3x−3y ≥ 1 ∧ 3x−3y ≤ 2` (integer-infeasible though the real
    /// relaxation is feasible). Returns the tightened LHS, or `None` when there
    /// is nothing to tighten (no variables, or the coefficients are already
    /// coprime). Preserves the exact set of integer solutions.
    pub fn integer_gcd_tighten_le(&self) -> Option<LinExpr> {
        if self.coeffs.is_empty() {
            return None;
        }
        // Clear denominators so the coefficients and constant are integers.
        let mut l = Int::from(1);
        for c in self.coeffs.values() {
            l = l.lcm(c.denominator());
        }
        l = l.lcm(self.constant.denominator());
        let e = self.scale(&Rational::from_integer(l));
        // g = gcd of the (now integer) variable coefficients.
        let mut g = Int::from(0);
        for c in e.coeffs.values() {
            g = g.gcd(c.numerator());
        }
        if g <= Int::from(1) {
            return None; // coprime coefficients: nothing to tighten
        }
        // Divide through by g and round the constant up (⌈c/g⌉ = −⌊−c/g⌋).
        let mut out = e.scale(&Rational::from_integer(g).recip());
        out.constant = Rational::from_integer(out.constant.ceil());
        Some(out)
    }

    /// Evaluate the expression at `assign` (variables absent from the map read
    /// as zero).
    pub fn eval(&self, assign: &Assignment) -> Rational {
        let mut acc = self.constant.clone();
        for (v, c) in &self.coeffs {
            let val = assign.get(v).cloned().unwrap_or_else(zero);
            acc = &acc + &(c * &val);
        }
        acc
    }
}

/// Is the conjunction of `constraints` and `disequalities` (each `expr ≠ 0`)
/// satisfiable? Disequalities are handled by case-splitting `expr < 0` vs
/// `expr > 0` (exponential in the number of disequalities, but exact).
pub fn feasible_with_diseqs(constraints: &[Constraint], diseqs: &[LinExpr]) -> bool {
    model_with_diseqs(constraints, diseqs).is_some()
}

/// A satisfying assignment of variables to rational values, as produced by
/// [`model`] / [`model_with_diseqs`]. Variables absent from the map are
/// unconstrained and may take any value (the caller conventionally reads them
/// as zero).
pub type Assignment = BTreeMap<AstId, Rational>;

/// The outcome of a budgeted feasibility search.
pub enum SolveOutcome {
    /// A satisfying rational assignment.
    Sat(Assignment),
    /// Definitely infeasible.
    Unsat,
    /// The work budget was exhausted before deciding.
    Exhausted,
}

/// Like [`model_with_diseqs`], but bounds total work: `budget` counts the
/// remaining `model` solves and is decremented per leaf; on exhaustion the search
/// returns [`SolveOutcome::Exhausted`] instead of continuing the (worst-case
/// exponential) disequality case split. This keeps callers terminating.
pub fn model_with_diseqs_budgeted(
    constraints: &[Constraint],
    diseqs: &[LinExpr],
    budget: &mut u64,
) -> SolveOutcome {
    // Model-guided disequality splitting. Instead of eagerly case-splitting every
    // disequality (`< 0` vs `> 0`, 2^n leaves), first solve the constraints
    // *ignoring* the disequalities, then case-split only on a disequality the
    // resulting model actually violates (its expression is pinned to exactly 0).
    // A generic LRA vertex satisfies almost every disequality, so in practice this
    // does a handful of solves rather than an exponential number — while remaining
    // exact: constraints ∧ (d ≠ 0) is feasible iff (constraints ∧ d < 0) or
    // (constraints ∧ d > 0) is, and every unviolated disequality already holds at
    // the model. The shared `budget` (decremented per FM resolvent and once per
    // split node) keeps the whole search terminating with a sound `Exhausted`.
    if *budget == 0 {
        return SolveOutcome::Exhausted;
    }
    *budget -= 1;
    // FM elimination shares the same budget so a single blow-up can't hang.
    let model = match model_budgeted(constraints, budget) {
        SolveOutcome::Sat(m) => m,
        other => return other, // Unsat or Exhausted
    };
    // A disequality violated by this model is pinned to 0; split on it. Unviolated
    // disequalities are satisfied at `model`, so if none is violated the model is a
    // witness for the full system.
    let Some(d) = diseqs.iter().find(|d| d.eval(&model).is_zero()) else {
        return SolveOutcome::Sat(model);
    };
    let mut lt = constraints.to_vec();
    lt.push(Constraint::lt(d.clone()));
    match model_with_diseqs_budgeted(&lt, diseqs, budget) {
        SolveOutcome::Unsat => {
            let mut gt = constraints.to_vec();
            gt.push(Constraint::lt(d.neg())); // -d < 0  ⟺  d > 0
            model_with_diseqs_budgeted(&gt, diseqs, budget)
        }
        other => other, // Sat or Exhausted short-circuits
    }
}

/// Like [`feasible_with_diseqs`], but returns a concrete satisfying assignment
/// (over the rationals) when one exists.
pub fn model_with_diseqs(constraints: &[Constraint], diseqs: &[LinExpr]) -> Option<Assignment> {
    match diseqs.split_first() {
        None => model(constraints),
        Some((d, rest)) => {
            let mut lt = constraints.to_vec();
            lt.push(Constraint::lt(d.clone()));
            if let Some(a) = model_with_diseqs(&lt, rest) {
                return Some(a);
            }
            let mut gt = constraints.to_vec();
            gt.push(Constraint::lt(d.neg())); // -d < 0  ⟺  d > 0
            model_with_diseqs(&gt, rest)
        }
    }
}

/// A normalized constraint `expr ⋈ 0`, where `⋈` is `<` if `strict`, else `≤`.
#[derive(Clone, Debug)]
struct Ineq {
    expr: LinExpr,
    strict: bool,
}

/// The relation of a linear atom.
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub enum Rel {
    /// `expr ≤ 0`
    Le,
    /// `expr < 0`
    Lt,
    /// `expr = 0`
    Eq,
}

/// A linear constraint `expr ⋈ 0`.
#[derive(Clone, Debug)]
pub struct Constraint {
    /// The left-hand side (right-hand side is 0).
    pub expr: LinExpr,
    /// The relation.
    pub rel: Rel,
}

impl Constraint {
    /// `expr ≤ 0`.
    pub fn le(expr: LinExpr) -> Constraint {
        Constraint { expr, rel: Rel::Le }
    }
    /// `expr < 0`.
    pub fn lt(expr: LinExpr) -> Constraint {
        Constraint { expr, rel: Rel::Lt }
    }
    /// `expr = 0`.
    pub fn eq(expr: LinExpr) -> Constraint {
        Constraint { expr, rel: Rel::Eq }
    }

    fn to_ineqs(&self) -> Vec<Ineq> {
        match self.rel {
            Rel::Le => alloc::vec![Ineq {
                expr: self.expr.clone(),
                strict: false
            }],
            Rel::Lt => alloc::vec![Ineq {
                expr: self.expr.clone(),
                strict: true
            }],
            // e = 0  ⟺  e ≤ 0 ∧ -e ≤ 0
            Rel::Eq => alloc::vec![
                Ineq {
                    expr: self.expr.clone(),
                    strict: false
                },
                Ineq {
                    expr: self.expr.neg(),
                    strict: false
                },
            ],
        }
    }
}

/// Is the conjunction of `constraints` satisfiable over the rationals?
pub fn feasible(constraints: &[Constraint]) -> bool {
    model(constraints).is_some()
}

/// Work budget for [`feasible_core`]'s Fourier–Motzkin elimination. On exhaustion
/// the search returns `None` (no core), so the caller falls back to the always
/// sound full-assignment block — a bounded blow-up can only weaken a lemma.
const FEASIBLE_CORE_BUDGET: u64 = 200_000;

/// Provenance-tracked Fourier–Motzkin: like [`feasible`] over the rationals, but
/// when the system is infeasible via a **direct FM false derivation** it returns
/// the set of original constraint indices whose Farkas combination produced the
/// contradiction — the conflict core (Z3's `theory_arith` conflict = the
/// constraints with a nonzero Farkas coefficient). `None` when no rational
/// contradiction is derived.
///
/// **MVP scope:** only the pure `≤ / < / =` case over the RATIONALS (the direct FM
/// false derivation). It does NOT core disequality splits or integer-only (Omega)
/// infeasibility — for a system that is rational-feasible (so FM derives no
/// contradiction) it returns `None` even if the integer test would refute it, and
/// the caller then uses the full block. [`feasible`]/[`feasible_with_diseqs`] are
/// left untouched and remain the sound/complete deciders.
///
/// Provenance: each original constraint `i`'s ineqs start tagged `{i}`; when a
/// lower and an upper bound are combined during elimination the resolvent's tag is
/// the UNION of the two operands' tags — exactly which original constraints the
/// Farkas combination used. A derived constant ineq that is unsatisfiable (`c ≤ 0`
/// with `c > 0`, or `c < 0` with `c ≥ 0`, over an empty variable set) is the
/// contradiction; its tag is the returned core.
pub fn feasible_core(constraints: &[Constraint]) -> Option<Vec<usize>> {
    // A provenance-tagged inequality `expr ⋈ 0` plus the set of original
    // constraint indices it descends from.
    struct IneqP {
        expr: LinExpr,
        strict: bool,
        origin: BTreeSet<usize>,
    }
    // A trivially-false constant ineq is a contradiction; report its origin set.
    fn false_core(iq: &IneqP) -> Option<Vec<usize>> {
        if iq.expr.is_constant() {
            let k = iq.expr.const_term();
            let violated = if iq.strict { *k >= zero() } else { *k > zero() };
            if violated {
                return Some(iq.origin.iter().copied().collect());
            }
        }
        None
    }

    let mut ineqs: Vec<IneqP> = Vec::new();
    for (i, c) in constraints.iter().enumerate() {
        for iq in c.to_ineqs() {
            let mut origin = BTreeSet::new();
            origin.insert(i);
            let tagged = IneqP {
                expr: iq.expr,
                strict: iq.strict,
                origin,
            };
            if let Some(core) = false_core(&tagged) {
                return Some(core);
            }
            ineqs.push(tagged);
        }
    }

    let mut budget = FEASIBLE_CORE_BUDGET;
    // Eliminate variables one at a time (Fourier–Motzkin), unioning provenance.
    while let Some(v) = ineqs.iter().find_map(|i| i.expr.vars().next()) {
        let mut upper = Vec::new(); // coeff(v) > 0
        let mut lower = Vec::new(); // coeff(v) < 0
        let mut next: Vec<IneqP> = Vec::new(); // coeff(v) == 0
        for iq in ineqs {
            let c = iq.expr.coeff(v);
            if c.is_zero() {
                next.push(iq);
            } else if c > zero() {
                upper.push(iq);
            } else {
                lower.push(iq);
            }
        }
        for u in &upper {
            let au = u.expr.coeff(v); // > 0
            for l in &lower {
                if budget == 0 {
                    return None; // FM blow-up: no core, caller uses the full block
                }
                budget -= 1;
                let al = l.expr.coeff(v); // < 0
                // resolvent = (-al)·U + (au)·L  (v cancels), keeping strictness.
                let mut e = u.expr.scale(&al.neg());
                e.add_scaled(&l.expr, &au);
                let mut origin = u.origin.clone();
                origin.extend(l.origin.iter().copied());
                let tagged = IneqP {
                    expr: e,
                    strict: u.strict || l.strict,
                    origin,
                };
                if let Some(core) = false_core(&tagged) {
                    return Some(core);
                }
                next.push(tagged);
            }
        }
        ineqs = next;
    }

    // No variables remain and no false constant ineq was ever derived: the system
    // is feasible over the rationals — no rational conflict core.
    None
}

/// Decide feasibility of `constraints` over the rationals and, if satisfiable,
/// return a concrete satisfying assignment.
///
/// This runs Fourier–Motzkin elimination while recording, for each eliminated
/// variable, the inequalities that mentioned it. Because FM projection is exact,
/// a feasible system always admits a witness, reconstructed by back-substitution
/// in reverse elimination order: with every later variable already fixed, each
/// remaining bound on the current variable evaluates to a rational, and any point
/// in the resulting interval works.
pub fn model(constraints: &[Constraint]) -> Option<Assignment> {
    let mut unbounded = u64::MAX;
    match model_budgeted(constraints, &mut unbounded) {
        SolveOutcome::Sat(a) => Some(a),
        _ => None, // Unsat (Exhausted is unreachable with an unbounded budget)
    }
}

/// Like [`model`], but bounds the (worst-case doubly-exponential) Fourier–Motzkin
/// elimination: `budget` is decremented per resolvent generated, and on
/// exhaustion the search returns [`SolveOutcome::Exhausted`] rather than
/// continuing. This keeps a single feasibility check terminating even when the
/// constraint system blows up.
pub fn model_budgeted(constraints: &[Constraint], budget: &mut u64) -> SolveOutcome {
    let mut ineqs: Vec<Ineq> = constraints.iter().flat_map(|c| c.to_ineqs()).collect();

    // The inequalities that constrained each eliminated variable, newest last.
    let mut history: Vec<(AstId, Vec<Ineq>)> = Vec::new();

    // Eliminate variables one at a time (Fourier–Motzkin).
    while let Some(v) = ineqs
        .iter()
        .find_map(|i| i.expr.coeffs.keys().next().copied())
    {
        let mut upper = Vec::new(); // coeff(v) > 0
        let mut lower = Vec::new(); // coeff(v) < 0
        let mut rest = Vec::new(); // coeff(v) == 0
        for i in ineqs {
            let c = i.expr.coeff(v);
            if c.is_zero() {
                rest.push(i);
            } else if c > zero() {
                upper.push(i);
            } else {
                lower.push(i);
            }
        }
        let mut next = rest;
        for u in &upper {
            let au = u.expr.coeff(v); // > 0
            for l in &lower {
                if *budget == 0 {
                    return SolveOutcome::Exhausted; // FM blow-up: give up
                }
                *budget -= 1;
                let al = l.expr.coeff(v); // < 0
                // resolvent = (-al)·U + (au)·L  (v cancels), keeping strictness.
                let mut e = u.expr.scale(&al.neg());
                e.add_scaled(&l.expr, &au);
                next.push(Ineq {
                    expr: e,
                    strict: u.strict || l.strict,
                });
            }
        }
        // Record v's bounds for reconstruction, then continue on the rest.
        let mut mentioning = upper;
        mentioning.extend(lower);
        history.push((v, mentioning));
        ineqs = next;
    }

    // No variables remain: every ineq is `k ≤ 0` or `k < 0`. Infeasible if some
    // constant violates its relation.
    for i in &ineqs {
        let k = &i.expr.constant;
        let violated = if i.strict { *k >= zero() } else { *k > zero() };
        if violated {
            return SolveOutcome::Unsat;
        }
    }

    // Feasible: back-substitute in reverse elimination order.
    let mut assign: Assignment = BTreeMap::new();
    for (v, bounds) in history.into_iter().rev() {
        let mut lo: Option<(Rational, bool)> = None; // (value, strict)
        let mut hi: Option<(Rational, bool)> = None;
        for i in &bounds {
            let cv = i.expr.coeff(v); // nonzero
            // Evaluate the rest of the row (everything but v) at the fixed vars.
            let mut r = i.expr.constant.clone();
            for (u, c) in &i.expr.coeffs {
                if *u != v {
                    let uv = assign.get(u).cloned().unwrap_or_else(zero);
                    r = &r + &(c * &uv);
                }
            }
            // cv·v + r ⋈ 0  ⟺  v ⋈' -r/cv, flipping ⋈ when cv < 0.
            let bound = &r.neg() / &cv;
            if cv > zero() {
                // v ≤ bound (or <)
                hi = Some(match hi {
                    Some((h, hs)) if h < bound || (h == bound && !hs) => (h, hs),
                    _ => (bound, i.strict),
                });
            } else {
                // v ≥ bound (or >)
                lo = Some(match lo {
                    Some((l, ls)) if l > bound || (l == bound && !ls) => (l, ls),
                    _ => (bound, i.strict),
                });
            }
        }
        assign.insert(v, pick_between(lo, hi));
    }
    SolveOutcome::Sat(assign)
}

/// Project the variable `x` out of a conjunction of linear `constraints` by
/// Fourier–Motzkin elimination, returning the equivalent `x`-free conjunction
/// (`∃x. ⋀ constraints`). `None` if the FM resolution exceeds `budget`.
pub fn project(constraints: &[Constraint], x: AstId, budget: &mut u64) -> Option<Vec<Constraint>> {
    let ineqs: Vec<Ineq> = constraints.iter().flat_map(|c| c.to_ineqs()).collect();
    let mut upper = Vec::new(); // coeff(x) > 0
    let mut lower = Vec::new(); // coeff(x) < 0
    let mut rest = Vec::new(); // x-free
    for i in ineqs {
        let c = i.expr.coeff(x);
        if c.is_zero() {
            rest.push(i);
        } else if c > zero() {
            upper.push(i);
        } else {
            lower.push(i);
        }
    }
    for u in &upper {
        let au = u.expr.coeff(x);
        for l in &lower {
            if *budget == 0 {
                return None;
            }
            *budget -= 1;
            let al = l.expr.coeff(x);
            // resolvent = (-al)·U + (au)·L, cancelling x, keeping strictness.
            let mut e = u.expr.scale(&al.neg());
            e.add_scaled(&l.expr, &au);
            rest.push(Ineq {
                expr: e,
                strict: u.strict || l.strict,
            });
        }
    }
    Some(
        rest.into_iter()
            .map(|i| {
                if i.strict {
                    Constraint::lt(i.expr)
                } else {
                    Constraint::le(i.expr)
                }
            })
            .collect(),
    )
}

/// The result of optimizing a linear objective over a feasible constraint set.
#[derive(Clone, Debug, PartialEq)]
pub enum OptOutcome {
    /// The optimum value, attained by some feasible point.
    Attained(Rational),
    /// The value is a supremum/infimum not attained (a strict bound).
    Bound(Rational),
    /// The objective is unbounded in the optimizing direction.
    Unbounded,
    /// Fourier–Motzkin blew past the budget.
    Exhausted,
}

/// Optimize the linear objective `obj` over `constraints` (assumed feasible),
/// with `z` a fresh variable identifier standing for the objective. Introduces
/// `z = obj` and eliminates every other variable by Fourier–Motzkin, leaving the
/// tightest bound on `z`.
pub fn optimize(
    constraints: &[Constraint],
    obj: &LinExpr,
    z: AstId,
    maximize: bool,
    budget: &mut u64,
) -> OptOutcome {
    // z - obj = 0.
    let mut cons = constraints.to_vec();
    cons.push(Constraint::eq(LinExpr::var(z).sub(obj)));
    let mut ineqs: Vec<Ineq> = cons.iter().flat_map(|c| c.to_ineqs()).collect();

    // Eliminate every variable except z.
    while let Some(v) = ineqs
        .iter()
        .find_map(|i| i.expr.coeffs.keys().find(|&&k| k != z).copied())
    {
        let mut upper = Vec::new();
        let mut lower = Vec::new();
        let mut next = Vec::new();
        for i in ineqs {
            let c = i.expr.coeff(v);
            if c.is_zero() {
                next.push(i);
            } else if c > zero() {
                upper.push(i);
            } else {
                lower.push(i);
            }
        }
        for u in &upper {
            let au = u.expr.coeff(v);
            for l in &lower {
                if *budget == 0 {
                    return OptOutcome::Exhausted;
                }
                *budget -= 1;
                let al = l.expr.coeff(v);
                let mut e = u.expr.scale(&al.neg());
                e.add_scaled(&l.expr, &au);
                next.push(Ineq {
                    expr: e,
                    strict: u.strict || l.strict,
                });
            }
        }
        ineqs = next;
    }

    // Remaining rows are in `z` (and constants) only: collect the tightest
    // upper/lower bound on z. For `cz·z + k ⋈ 0`: z ⋈' -k/cz (flip if cz < 0).
    let mut upper: Option<(Rational, bool)> = None; // z ≤ bound
    let mut lower: Option<(Rational, bool)> = None; // z ≥ bound
    for i in &ineqs {
        let cz = i.expr.coeff(z);
        if cz.is_zero() {
            continue; // constant row (feasibility already assumed)
        }
        let bound = &i.expr.constant.neg() / &cz;
        if cz > zero() {
            upper = Some(match upper {
                Some((h, hs)) if h < bound || (h == bound && !hs) => (h, hs),
                _ => (bound, i.strict),
            });
        } else {
            lower = Some(match lower {
                Some((l, ls)) if l > bound || (l == bound && !ls) => (l, ls),
                _ => (bound, i.strict),
            });
        }
    }
    let chosen = if maximize { upper } else { lower };
    match chosen {
        None => OptOutcome::Unbounded,
        Some((b, true)) => OptOutcome::Bound(b),
        Some((b, false)) => OptOutcome::Attained(b),
    }
}

/// Choose a rational strictly (or non-strictly) inside `(lo, hi)`. Feasibility
/// guarantees such a point exists; when both bounds are present the midpoint is
/// always valid, and one-sided bounds step off by one.
fn pick_between(lo: Option<(Rational, bool)>, hi: Option<(Rational, bool)>) -> Rational {
    let one = Rational::from_integer(Int::from(1));
    let two = Rational::from_integer(Int::from(2));
    match (lo, hi) {
        (None, None) => zero(),
        (Some((l, _)), None) => &l + &one,
        (None, Some((h, _))) => &h - &one,
        (Some((l, ls)), Some((h, hs))) => {
            if l == h {
                debug_assert!(!ls && !hs, "empty interval in a feasible system");
                l
            } else {
                &(&l + &h) / &two // midpoint: strictly between l and h
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::AstId;

    fn rat(n: i64) -> Rational {
        Rational::from_integer(Int::from(n))
    }

    // Distinct opaque variable ids.
    fn x() -> AstId {
        AstId(1000)
    }
    fn y() -> AstId {
        AstId(1001)
    }
    fn z() -> AstId {
        AstId(1002)
    }

    #[test]
    fn core_contradictory_bounds() {
        // 0: x ≤ 1  (x - 1 ≤ 0);  1: x ≥ 2  (2 - x ≤ 0).  Core = {0, 1}.
        let x_le1 = Constraint::le(LinExpr::var(x()).sub(&LinExpr::constant(rat(1))));
        let x_ge2 = Constraint::le(LinExpr::constant(rat(2)).sub(&LinExpr::var(x())));
        assert_eq!(feasible_core(&[x_le1, x_ge2]), Some(alloc::vec![0, 1]));
    }

    #[test]
    fn core_three_constraint_farkas() {
        // 0: x + y ≤ 0;  1: x ≥ 1 (-x + 1 ≤ 0);  2: y ≥ 1 (-y + 1 ≤ 0).
        // Sum of all three: 2 ≤ 0, infeasible. Core = {0, 1, 2}.
        let sum_le0 = Constraint::le(LinExpr::var(x()).add(&LinExpr::var(y())));
        let x_ge1 = Constraint::le(LinExpr::var(x()).neg().add(&LinExpr::constant(rat(1))));
        let y_ge1 = Constraint::le(LinExpr::var(y()).neg().add(&LinExpr::constant(rat(1))));
        assert_eq!(
            feasible_core(&[sum_le0, x_ge1, y_ge1]),
            Some(alloc::vec![0, 1, 2])
        );
    }

    #[test]
    fn core_excludes_irrelevant_constraint() {
        // 0: x ≤ 1;  1: x ≥ 2 (contradictory);  2: z ≤ 5 (irrelevant).
        // Core must be {0, 1} and must NOT contain 2.
        let x_le1 = Constraint::le(LinExpr::var(x()).sub(&LinExpr::constant(rat(1))));
        let x_ge2 = Constraint::le(LinExpr::constant(rat(2)).sub(&LinExpr::var(x())));
        let z_le5 = Constraint::le(LinExpr::var(z()).sub(&LinExpr::constant(rat(5))));
        let core = feasible_core(&[x_le1, x_ge2, z_le5]).expect("infeasible");
        assert_eq!(core, alloc::vec![0, 1]);
        assert!(!core.contains(&2));
    }

    #[test]
    fn core_none_when_feasible() {
        // x ≥ 0, y ≥ 0, x + y ≤ 1 is feasible → no rational conflict core.
        let x_ge0 = Constraint::le(LinExpr::var(x()).neg());
        let y_ge0 = Constraint::le(LinExpr::var(y()).neg());
        let sum = LinExpr::var(x())
            .add(&LinExpr::var(y()))
            .sub(&LinExpr::constant(rat(1)));
        assert_eq!(feasible_core(&[x_ge0, y_ge0, Constraint::le(sum)]), None);
    }

    #[test]
    fn contradictory_bounds_infeasible() {
        // x ≥ 0  (i.e. -x ≤ 0)  and  x ≤ -1  (x + 1 ≤ 0)
        let ge0 = Constraint::le(LinExpr::var(x()).neg());
        let le_m1 = Constraint::le(LinExpr::var(x()).add(&LinExpr::constant(rat(1))));
        assert!(!feasible(&[ge0, le_m1]));
    }

    #[test]
    fn satisfiable_system() {
        // x ≥ 0, y ≥ 0, x + y ≤ 1
        let x_ge0 = Constraint::le(LinExpr::var(x()).neg());
        let y_ge0 = Constraint::le(LinExpr::var(y()).neg());
        let sum = LinExpr::var(x())
            .add(&LinExpr::var(y()))
            .sub(&LinExpr::constant(rat(1)));
        let sum_le1 = Constraint::le(sum);
        assert!(feasible(&[x_ge0, y_ge0, sum_le1]));
    }

    #[test]
    fn strict_cycle_infeasible() {
        // x < y and y < x  ⟺  x - y < 0 and y - x < 0
        let xy = LinExpr::var(x()).sub(&LinExpr::var(y()));
        let yx = LinExpr::var(y()).sub(&LinExpr::var(x()));
        assert!(!feasible(&[Constraint::lt(xy), Constraint::lt(yx)]));
    }

    #[test]
    fn equality_pins_a_value() {
        // x = 2 and x ≤ 1  → infeasible
        let x_eq2 = Constraint::eq(LinExpr::var(x()).sub(&LinExpr::constant(rat(2))));
        let x_le1 = Constraint::le(LinExpr::var(x()).sub(&LinExpr::constant(rat(1))));
        assert!(!feasible(&[x_eq2.clone(), x_le1]));
        // x = 2 and x ≥ 1  → feasible
        let x_ge1 = Constraint::le(LinExpr::constant(rat(1)).sub(&LinExpr::var(x())));
        assert!(feasible(&[x_eq2, x_ge1]));
    }

    /// Evaluate `expr` at `assign` (unassigned variables read as zero).
    fn eval(expr: &LinExpr, assign: &Assignment) -> Rational {
        let mut acc = expr.constant.clone();
        for (v, c) in &expr.coeffs {
            let val = assign.get(v).cloned().unwrap_or_else(zero);
            acc = &acc + &(c * &val);
        }
        acc
    }

    /// Assert `assign` satisfies every constraint.
    fn check_sat(cs: &[Constraint], assign: &Assignment) {
        for c in cs {
            let v = eval(&c.expr, assign);
            let ok = match c.rel {
                Rel::Le => v <= zero(),
                Rel::Lt => v < zero(),
                Rel::Eq => v == zero(),
            };
            assert!(ok, "constraint {:?} violated: lhs = {v:?}", c.rel);
        }
    }

    #[test]
    fn model_satisfies_bounded_system() {
        // 0 ≤ x, 0 ≤ y, x + y ≤ 1, and x - y = 0 (encoded via constraints).
        let x_ge0 = Constraint::le(LinExpr::var(x()).neg());
        let y_ge0 = Constraint::le(LinExpr::var(y()).neg());
        let sum = LinExpr::var(x())
            .add(&LinExpr::var(y()))
            .sub(&LinExpr::constant(rat(1)));
        let sum_le1 = Constraint::le(sum);
        let eq = Constraint::eq(LinExpr::var(x()).sub(&LinExpr::var(y())));
        let cs = [x_ge0, y_ge0, sum_le1, eq];
        let m = model(&cs).expect("feasible");
        check_sat(&cs, &m);
    }

    #[test]
    fn model_respects_strict_bounds() {
        // 0 < x < 1 — witness must be strictly inside, e.g. 1/2.
        let gt0 = Constraint::lt(LinExpr::var(x()).neg()); // -x < 0
        let lt1 = Constraint::lt(LinExpr::var(x()).sub(&LinExpr::constant(rat(1))));
        let cs = [gt0, lt1];
        let m = model(&cs).expect("feasible");
        check_sat(&cs, &m);
        let xv = m.get(&x()).cloned().unwrap_or_else(zero);
        assert!(xv > zero() && xv < rat(1));
    }

    #[test]
    fn model_with_disequality() {
        // x ≤ 5, x ≥ 5, x ≠ 5 → infeasible; x ≤ 6, x ≥ 5, x ≠ 5 → x in (5,6].
        let le5 = Constraint::le(LinExpr::var(x()).sub(&LinExpr::constant(rat(5))));
        let ge5 = Constraint::le(LinExpr::constant(rat(5)).sub(&LinExpr::var(x())));
        let ne5 = LinExpr::var(x()).sub(&LinExpr::constant(rat(5)));
        assert!(model_with_diseqs(&[le5, ge5.clone()], core::slice::from_ref(&ne5)).is_none());
        let le6 = Constraint::le(LinExpr::var(x()).sub(&LinExpr::constant(rat(6))));
        let cs = [le6, ge5];
        let m = model_with_diseqs(&cs, &[ne5]).expect("feasible");
        check_sat(&cs, &m);
        assert_ne!(m.get(&x()).cloned().unwrap_or_else(zero), rat(5));
    }

    #[test]
    fn non_strict_boundary_is_feasible() {
        // x ≤ 0 and x ≥ 0  → x = 0 feasible; but x < 0 and x ≥ 0 infeasible.
        let le0 = Constraint::le(LinExpr::var(x()));
        let ge0 = Constraint::le(LinExpr::var(x()).neg());
        assert!(feasible(&[le0.clone(), ge0.clone()]));
        let lt0 = Constraint::lt(LinExpr::var(x()));
        assert!(!feasible(&[lt0, ge0]));
    }
}
