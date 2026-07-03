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

use alloc::collections::BTreeMap;
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
            return None;
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
    Some(assign)
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
        assert!(model_with_diseqs(&[le5, ge5.clone()], &[ne5.clone()]).is_none());
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
