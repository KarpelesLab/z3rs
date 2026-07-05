//! Univariate real-algebraic decision procedure — a 1-D specialisation of Z3's
//! `nlsat` + `realclosure` (`z3/src/nlsat`, `z3/src/math/realclosure`,
//! Z3 4.17.0, MIT).
//!
//! For a conjunction of polynomial constraints `pᵢ(x) ⋈ 0` in a **single**
//! variable, the satisfying set is a union of sign-invariant cells delimited by
//! the real roots of the `pᵢ`. This module builds those cells via **Sturm
//! sequences** (exact real-root isolation over the rationals) and tests one
//! representative point per cell — an *exact and complete* decision for the
//! univariate fragment: it returns a definite `sat`/`unsat` matching Z3, never a
//! guess.
//!
//! Representatives:
//! - open cells → a rational strictly between consecutive roots (exact eval);
//! - root cells → the (possibly irrational) root itself, whose truth under each
//!   `pᵢ` is read from the sign of `pᵢ` on the root's isolating interval and a
//!   sign-change (squarefree) test for `pᵢ(root) = 0`.

use alloc::vec;
use alloc::vec::Vec;

use puremp::Rational;

use crate::math::polynomial::{Polynomial, Var};
use crate::nlsat::icp::Rel;

fn zero() -> Rational {
    Rational::from_integer(0.into())
}
fn one() -> Rational {
    Rational::from_integer(1.into())
}

/// A dense univariate polynomial over the rationals: `coeffs[i]` is the
/// coefficient of `xⁱ`. Kept normalised (no trailing-zero high coefficients),
/// so the empty vector is the zero polynomial.
#[derive(Clone, Debug, PartialEq, Eq)]
struct UPoly {
    coeffs: Vec<Rational>,
}

impl UPoly {
    fn zero() -> UPoly {
        UPoly { coeffs: Vec::new() }
    }

    fn from_coeffs(mut coeffs: Vec<Rational>) -> UPoly {
        while coeffs.last().is_some_and(|c| c.is_zero()) {
            coeffs.pop();
        }
        UPoly { coeffs }
    }

    fn is_zero(&self) -> bool {
        self.coeffs.is_empty()
    }

    /// Degree; the zero polynomial has degree 0 by convention here.
    fn degree(&self) -> usize {
        self.coeffs.len().saturating_sub(1)
    }

    fn lead(&self) -> Rational {
        self.coeffs.last().cloned().unwrap_or_else(zero)
    }

    fn eval(&self, x: &Rational) -> Rational {
        // Horner's rule.
        let mut acc = zero();
        for c in self.coeffs.iter().rev() {
            acc = acc.mul(x).add(c);
        }
        acc
    }

    /// The sign of `p(x)`: -1, 0, +1.
    fn sign_at(&self, x: &Rational) -> i32 {
        self.eval(x).signum()
    }

    fn deriv(&self) -> UPoly {
        if self.coeffs.len() <= 1 {
            return UPoly::zero();
        }
        let mut c = Vec::with_capacity(self.coeffs.len() - 1);
        for (i, coeff) in self.coeffs.iter().enumerate().skip(1) {
            c.push(coeff.mul(&Rational::from_integer((i as i64).into())));
        }
        UPoly::from_coeffs(c)
    }

    fn scale(&self, s: &Rational) -> UPoly {
        if s.is_zero() {
            return UPoly::zero();
        }
        UPoly::from_coeffs(self.coeffs.iter().map(|c| c.mul(s)).collect())
    }

    fn neg(&self) -> UPoly {
        UPoly::from_coeffs(self.coeffs.iter().map(|c| c.neg()).collect())
    }

    fn sub(&self, other: &UPoly) -> UPoly {
        let n = self.coeffs.len().max(other.coeffs.len());
        let mut c = vec![zero(); n];
        for (i, a) in self.coeffs.iter().enumerate() {
            c[i] = c[i].add(a);
        }
        for (i, b) in other.coeffs.iter().enumerate() {
            c[i] = c[i].sub(b);
        }
        UPoly::from_coeffs(c)
    }

    fn mul(&self, other: &UPoly) -> UPoly {
        if self.is_zero() || other.is_zero() {
            return UPoly::zero();
        }
        let mut c = vec![zero(); self.coeffs.len() + other.coeffs.len() - 1];
        for (i, a) in self.coeffs.iter().enumerate() {
            for (j, b) in other.coeffs.iter().enumerate() {
                c[i + j] = c[i + j].add(&a.mul(b));
            }
        }
        UPoly::from_coeffs(c)
    }

    /// Polynomial remainder `self mod divisor` over the rationals (exact, since
    /// the rationals are a field).
    fn rem(&self, divisor: &UPoly) -> UPoly {
        debug_assert!(!divisor.is_zero());
        let mut r = self.clone();
        let d_deg = divisor.degree();
        let d_lead = divisor.lead();
        while !r.is_zero() && r.degree() >= d_deg {
            let shift = r.degree() - d_deg;
            let factor = r.lead().div(&d_lead);
            // r -= factor * x^shift * divisor
            let mut sub = vec![zero(); shift + divisor.coeffs.len()];
            for (i, c) in divisor.coeffs.iter().enumerate() {
                sub[i + shift] = c.mul(&factor);
            }
            r = r.sub(&UPoly::from_coeffs(sub));
        }
        r
    }

    /// Monic GCD via the Euclidean algorithm.
    fn gcd(&self, other: &UPoly) -> UPoly {
        let mut a = self.clone();
        let mut b = other.clone();
        while !b.is_zero() {
            let r = a.rem(&b);
            a = b;
            b = r;
        }
        if a.is_zero() {
            a
        } else {
            let lead = a.lead();
            a.scale(&lead.recip())
        }
    }

    /// The squarefree part `p / gcd(p, p')` (same roots, all simple).
    fn squarefree(&self) -> UPoly {
        if self.degree() == 0 {
            return self.clone();
        }
        let g = self.gcd(&self.deriv());
        if g.degree() == 0 {
            return self.clone();
        }
        self.div_exact(&g)
    }

    /// Exact quotient `self / divisor` (divisor must divide self).
    fn div_exact(&self, divisor: &UPoly) -> UPoly {
        let mut r = self.clone();
        let d_deg = divisor.degree();
        let d_lead = divisor.lead();
        let mut q = vec![zero(); self.degree().saturating_sub(d_deg) + 1];
        while !r.is_zero() && r.degree() >= d_deg {
            let shift = r.degree() - d_deg;
            let factor = r.lead().div(&d_lead);
            q[shift] = factor.clone();
            let mut sub = vec![zero(); shift + divisor.coeffs.len()];
            for (i, c) in divisor.coeffs.iter().enumerate() {
                sub[i + shift] = c.mul(&factor);
            }
            r = r.sub(&UPoly::from_coeffs(sub));
        }
        UPoly::from_coeffs(q)
    }

    /// A Cauchy bound `M` such that every real root lies in `(-M, M)`.
    fn root_bound(&self) -> Rational {
        if self.degree() == 0 {
            return one();
        }
        let lead = self.lead().abs();
        let mut m = zero();
        for c in &self.coeffs[..self.coeffs.len() - 1] {
            let ratio = c.abs().div(&lead);
            if ratio > m {
                m = ratio;
            }
        }
        m.add(&one())
    }
}

/// The Sturm sequence of `p`: `s₀ = p`, `s₁ = p'`, `sᵢ₊₁ = -(sᵢ₋₁ mod sᵢ)`.
fn sturm_chain(p: &UPoly) -> Vec<UPoly> {
    let mut chain = vec![p.clone(), p.deriv()];
    while !chain.last().unwrap().is_zero() {
        let n = chain.len();
        let r = chain[n - 2].rem(&chain[n - 1]);
        if r.is_zero() {
            break;
        }
        chain.push(r.neg());
    }
    chain
}

/// Sign variations of the Sturm chain evaluated at `x` (zeros skipped).
fn variations(chain: &[UPoly], x: &Rational) -> usize {
    let mut last = 0i32;
    let mut count = 0;
    for s in chain {
        let sg = s.sign_at(x);
        if sg == 0 {
            continue;
        }
        if last != 0 && sg != last {
            count += 1;
        }
        last = sg;
    }
    count
}

/// Number of distinct real roots of `p` (squarefree) in the half-open `(a, b]`.
fn root_count(chain: &[UPoly], a: &Rational, b: &Rational) -> i64 {
    variations(chain, a) as i64 - variations(chain, b) as i64
}

/// Isolate the real roots of squarefree `p` into disjoint `(lo, hi)` intervals,
/// each containing exactly one root and with **non-root endpoints**, sorted
/// ascending. Split points are nudged off any root they land on, so an interval
/// endpoint never coincides with a root (which would corrupt the sign analysis
/// in [`root_sign`]).
fn isolate_roots(p: &UPoly) -> Vec<(Rational, Rational)> {
    if p.degree() == 0 {
        return Vec::new();
    }
    let chain = sturm_chain(p);
    let m = p.root_bound();
    let two = Rational::from_integer(2.into());
    let mut out = Vec::new();
    let mut stack = vec![(m.neg(), m)];
    let mut guard = 0;
    while let Some((a, b)) = stack.pop() {
        guard += 1;
        if guard > 200_000 {
            break;
        }
        // Count of roots in (a, b] with non-root endpoints ⇒ roots in (a, b).
        let n = root_count(&chain, &a, &b);
        if n <= 0 {
            continue;
        }
        if n == 1 {
            out.push((a, b));
            continue;
        }
        // Split at a non-root midpoint (nudge off `p`'s roots if necessary).
        let mut mid = a.add(&b).div(&two);
        let step = b.sub(&a).div(&Rational::from_integer(1024.into()));
        let mut tries = 0;
        while p.sign_at(&mid) == 0 && tries < 2048 {
            mid = mid.add(&step);
            tries += 1;
        }
        stack.push((a, mid.clone()));
        stack.push((mid, b));
    }
    out.sort_by(|x, y| x.0.cmp(&y.0));
    out
}

/// Convert a multivariate [`Polynomial`] known to involve only `var` into a
/// dense univariate coefficient vector.
fn to_upoly(p: &Polynomial, var: Var) -> UPoly {
    let mut coeffs: Vec<Rational> = Vec::new();
    for (c, m) in p.terms() {
        let d = m.degree_of(var) as usize;
        if coeffs.len() <= d {
            coeffs.resize(d + 1, zero());
        }
        coeffs[d] = coeffs[d].add(c);
    }
    UPoly::from_coeffs(coeffs)
}

/// Does the value with sign `s` (`p(x)` sign; `s == 0` means `p(x)=0`) satisfy
/// `p REL 0`?
fn sign_satisfies(s: i32, rel: Rel) -> bool {
    match rel {
        Rel::Lt => s < 0,
        Rel::Le => s <= 0,
        Rel::Gt => s > 0,
        Rel::Ge => s >= 0,
        Rel::Eq => s == 0,
        Rel::Ne => s != 0,
    }
}

/// Decide a conjunction of univariate polynomial constraints over the reals.
/// Returns `Some(true)` for SAT, `Some(false)` for UNSAT, or `None` if some
/// constraint is not genuinely univariate in `var` (caller falls back).
pub fn decide(constraints: &[(Polynomial, Rel)], var: Var) -> Option<bool> {
    // All constraints must be univariate in `var` (no other variable present).
    let mut ups: Vec<(UPoly, Rel)> = Vec::new();
    for (p, rel) in constraints {
        for v in p.vars() {
            if v != var {
                return None;
            }
        }
        // Cap the degree: root isolation on very high-degree polynomials is slow
        // and could hit the iteration guard, so decline (sound `unknown`) rather
        // than risk an incomplete/late answer.
        if p.degree_of(var) > 24 {
            return None;
        }
        ups.push((to_upoly(p, var), *rel));
    }
    if ups.is_empty() {
        return Some(true);
    }

    // Critical points = roots of the squarefree product of all constraint polys.
    let mut prod = UPoly::from_coeffs(vec![one()]);
    for (p, _) in &ups {
        if !p.is_zero() {
            prod = prod.mul(&p.squarefree());
        }
    }
    let roots = if prod.degree() == 0 {
        Vec::new()
    } else {
        isolate_roots(&prod.squarefree())
    };

    // Sample points: below all roots, between consecutive roots, above all roots,
    // plus each root itself. Each open-cell sample is a rational; each root is
    // handled via sign analysis on its isolating interval.
    let mut open_samples: Vec<Rational> = Vec::new();
    if roots.is_empty() {
        open_samples.push(zero());
    } else {
        let two = Rational::from_integer(2.into());
        open_samples.push(roots[0].0.sub(&one())); // below the first root
        for w in roots.windows(2) {
            // strictly between root_i (in (w0.0,w0.1)) and root_{i+1} (in (w1.0,w1.1)):
            let a = &w[0].1; // hi of left isolating interval
            let b = &w[1].0; // lo of right isolating interval
            open_samples.push(a.add(b).div(&two));
        }
        open_samples.push(roots.last().unwrap().1.add(&one())); // above the last root
    }

    // Try open-cell samples: exact rational evaluation.
    for q in &open_samples {
        if ups
            .iter()
            .all(|(p, rel)| sign_satisfies(p.sign_at(q), *rel))
        {
            return Some(true);
        }
    }

    // Try each root cell.
    for (a, b) in &roots {
        if ups.iter().all(|(p, rel)| {
            let s = root_sign(p, a, b);
            sign_satisfies(s, *rel)
        }) {
            return Some(true);
        }
    }

    // No cell satisfies every constraint ⇒ unsatisfiable (complete for 1-D).
    Some(false)
}

/// Integer roots of `p` (univariate in `var`) via the rational-root theorem: an
/// integer root divides the constant coefficient (after clearing denominators).
/// Returns `None` if the constant term is too large to factor cheaply.
fn integer_roots(p: &Polynomial, var: Var) -> Option<Vec<i64>> {
    let up = to_upoly(p, var);
    if up.is_zero() || up.degree() == 0 {
        return Some(Vec::new());
    }
    // Clear denominators to integer coefficients.
    let mut denom = puremp::Int::from(1);
    for c in &up.coeffs {
        denom = lcm_int(&denom, c.denominator());
    }
    let int_coeffs: Vec<puremp::Int> = up
        .coeffs
        .iter()
        .map(|c| {
            c.mul(&Rational::from_integer(denom.clone()))
                .numerator()
                .clone()
        })
        .collect();
    let mut cands: Vec<i64> = Vec::new();
    // The lowest-order nonzero coefficient. If it is not `int_coeffs[0]` the
    // polynomial has `x^m` as a factor, so `0` is a root *and* the remaining
    // roots divide that lowest nonzero coefficient (rational-root theorem on the
    // depressed polynomial). Missing this made `x² − 7x` (constant term 0)
    // report only the root 0, not 7.
    let m = int_coeffs.iter().position(|c| !c.is_zero());
    let Some(m) = m else {
        return Some(Vec::new()); // the zero polynomial
    };
    if m > 0 {
        cands.push(0);
    }
    let a0 = int_coeffs[m].abs();
    let Some(a0_i) = i64_of(&a0) else {
        return None; // too large to factor
    };
    if a0_i > 20_000_000 {
        return None;
    }
    let mut d = 1i64;
    while d * d <= a0_i {
        if a0_i % d == 0 {
            cands.push(d);
            cands.push(-d);
            cands.push(a0_i / d);
            cands.push(-(a0_i / d));
        }
        d += 1;
    }
    // Keep only genuine roots.
    let zero_r = zero();
    let mut roots: Vec<i64> = cands
        .into_iter()
        .filter(|&c| {
            let x = Rational::from_integer(puremp::Int::from(c));
            up.eval(&x) == zero_r
        })
        .collect();
    roots.sort_unstable();
    roots.dedup();
    Some(roots)
}

fn lcm_int(a: &puremp::Int, b: &puremp::Int) -> puremp::Int {
    if a.is_zero() || b.is_zero() {
        return puremp::Int::from(0);
    }
    let g = a.gcd(b);
    a.div_exact(&g).mul(b).abs()
}

fn i64_of(n: &puremp::Int) -> Option<i64> {
    n.to_i64()
}

/// Decide a conjunction of univariate polynomial constraints over the
/// **integers**. Sound and complete when an equality constraint is present (it
/// pins `x` to a finite set of integer roots); otherwise falls back to `None`.
pub fn decide_int(constraints: &[(Polynomial, Rel)], var: Var) -> Option<bool> {
    for (p, _) in constraints {
        for v in p.vars() {
            if v != var {
                return None;
            }
        }
    }
    // Over-approximate by the reals: real-UNSAT ⇒ integer-UNSAT.
    if decide(constraints, var) == Some(false) {
        return Some(false);
    }
    // If a *genuine* equality in `x` is present (degree ≥ 1 in the variable),
    // integer `x` must be an integer root of it. A constant/trivial equality
    // (e.g. `x = x` ⇒ the zero polynomial) does not constrain `x` and is skipped,
    // so it never spuriously empties the candidate set.
    let mut candidates: Option<Vec<i64>> = None;
    for (p, rel) in constraints {
        if *rel == Rel::Eq && p.degree_of(var) >= 1 {
            let roots = integer_roots(p, var)?;
            candidates = Some(match candidates {
                None => roots,
                Some(prev) => prev.into_iter().filter(|r| roots.contains(r)).collect(),
            });
        }
    }
    let Some(cands) = candidates else {
        return None; // no equality to bound the integer search
    };
    for c in cands {
        let x = Rational::from_integer(puremp::Int::from(c));
        if constraints.iter().all(|(p, rel)| {
            sign_satisfies(
                p.eval(&|v| if v == var { x.clone() } else { zero() })
                    .signum(),
                *rel,
            )
        }) {
            return Some(true);
        }
    }
    Some(false)
}

/// The sign of `p` at the unique root of the critical product isolated in
/// `(a, b)`: `0` if `p` vanishes there (its squarefree part changes sign across
/// the interval), else the constant sign `p` holds on the interval.
fn root_sign(p: &UPoly, a: &Rational, b: &Rational) -> i32 {
    if p.is_zero() {
        return 0;
    }
    let sf = p.squarefree();
    let sa = sf.sign_at(a);
    let sb = sf.sign_at(b);
    if sa != sb {
        // A sign change of the squarefree part ⇒ `p` has its root here.
        return 0;
    }
    // No root of `p` in (a,b): `p` is sign-constant; read it at an endpoint
    // (endpoints are not roots of the product, so `p` is nonzero there).
    let ea = p.sign_at(a);
    if ea != 0 { ea } else { p.sign_at(b) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::math::polynomial::Monomial;

    fn r(n: i64) -> Rational {
        Rational::from_integer(n.into())
    }
    fn term(coeff: i64, deg: u32) -> (Rational, Monomial) {
        (r(coeff), Monomial::from_powers(&[(0, deg)]))
    }
    // Build a univariate polynomial in x0 from (coeff, degree) terms.
    fn poly(terms: &[(i64, u32)]) -> Polynomial {
        Polynomial::from_terms(terms.iter().map(|&(c, d)| term(c, d)).collect())
    }

    // x^2 = 4  is SAT over the reals (x = ±2).
    #[test]
    fn square_eq_four_sat() {
        let c = vec![(poly(&[(1, 2), (-4, 0)]), Rel::Eq)];
        assert_eq!(decide(&c, 0), Some(true));
    }

    // x^2 = 2 is SAT over the reals (x = ±√2, irrational — handled via roots).
    #[test]
    fn square_eq_two_sat() {
        let c = vec![(poly(&[(1, 2), (-2, 0)]), Rel::Eq)];
        assert_eq!(decide(&c, 0), Some(true));
    }

    // x^2 = -1 is UNSAT over the reals.
    #[test]
    fn square_eq_negative_unsat() {
        let c = vec![(poly(&[(1, 2), (1, 0)]), Rel::Eq)];
        assert_eq!(decide(&c, 0), Some(false));
    }

    // x^2 = 9  ∧  x > 0  is SAT (x = 3).
    #[test]
    fn square_eq_nine_positive_sat() {
        let c = vec![
            (poly(&[(1, 2), (-9, 0)]), Rel::Eq),
            (poly(&[(1, 1)]), Rel::Gt),
        ];
        assert_eq!(decide(&c, 0), Some(true));
    }

    // x^2 = 9  ∧  x > 0  ∧  x < 0  is UNSAT.
    #[test]
    fn contradictory_bounds_unsat() {
        let c = vec![
            (poly(&[(1, 2), (-9, 0)]), Rel::Eq),
            (poly(&[(1, 1)]), Rel::Gt),
            (poly(&[(1, 1)]), Rel::Lt),
        ];
        assert_eq!(decide(&c, 0), Some(false));
    }

    // x^2 < 4  is SAT (the open interval (-2, 2)).
    #[test]
    fn square_lt_four_sat() {
        let c = vec![(poly(&[(1, 2), (-4, 0)]), Rel::Lt)];
        assert_eq!(decide(&c, 0), Some(true));
    }

    // x^2 > 4 ∧ x < 2 ∧ x > -2 is UNSAT (the regions are disjoint).
    #[test]
    fn square_gt_and_between_unsat() {
        let c = vec![
            (poly(&[(1, 2), (-4, 0)]), Rel::Gt),
            (poly(&[(1, 1), (-2, 0)]), Rel::Lt),
            (poly(&[(1, 1), (2, 0)]), Rel::Gt),
        ];
        assert_eq!(decide(&c, 0), Some(false));
    }

    // Cubic: x^3 - x = 0 has roots {-1, 0, 1}; with x > 0 ∧ x < 1 there is no
    // root, but the equality forces a root ⇒ UNSAT.
    #[test]
    fn cubic_roots_constrained_unsat() {
        let c = vec![
            (poly(&[(1, 3), (-1, 1)]), Rel::Eq),
            (poly(&[(1, 1)]), Rel::Gt),
            (poly(&[(1, 1), (-1, 0)]), Rel::Lt),
        ];
        assert_eq!(decide(&c, 0), Some(false));
    }

    // Non-univariate input is declined.
    #[test]
    fn multivariate_declined() {
        let p = Polynomial::from_terms(vec![(r(1), Monomial::from_powers(&[(0, 1), (1, 1)]))]);
        assert_eq!(decide(&[(p, Rel::Eq)], 0), None);
    }

    // Integer decisions: x^2 = 9 has integer roots ±3 ⇒ sat; x^2 = 2 has none ⇒
    // unsat; a perfect-square bound picks x = 4.
    #[test]
    fn integer_square_roots() {
        assert_eq!(
            decide_int(&[(poly(&[(1, 2), (-9, 0)]), Rel::Eq)], 0),
            Some(true)
        );
        assert_eq!(
            decide_int(&[(poly(&[(1, 2), (-2, 0)]), Rel::Eq)], 0),
            Some(false)
        );
        // x^2 = 9 ∧ x > 0 ⇒ x = 3.
        assert_eq!(
            decide_int(
                &[
                    (poly(&[(1, 2), (-9, 0)]), Rel::Eq),
                    (poly(&[(1, 1)]), Rel::Gt)
                ],
                0
            ),
            Some(true)
        );
        // x^2 = 9 ∧ x > 0 ∧ x < 3 ⇒ only integer root 3 excluded ⇒ unsat.
        assert_eq!(
            decide_int(
                &[
                    (poly(&[(1, 2), (-9, 0)]), Rel::Eq),
                    (poly(&[(1, 1)]), Rel::Gt),
                    (poly(&[(1, 1), (-3, 0)]), Rel::Lt),
                ],
                0
            ),
            Some(false)
        );
    }

    // A real-unsat system is integer-unsat regardless of equalities.
    #[test]
    fn integer_inherits_real_unsat() {
        // x^2 = -1 (real-unsat) ⇒ int-unsat.
        assert_eq!(
            decide_int(&[(poly(&[(1, 2), (1, 0)]), Rel::Eq)], 0),
            Some(false)
        );
    }

    // Regression: a polynomial with a zero constant term (`x² − 7x = x(x−7)`)
    // must find BOTH integer roots 0 and 7 — earlier only 0 was found.
    #[test]
    fn integer_roots_with_zero_constant() {
        // x² - 7x = 0 ∧ x > 0  ⇒ x = 7 (sat).
        let c = vec![
            (poly(&[(1, 2), (-7, 1)]), Rel::Eq),
            (poly(&[(1, 1)]), Rel::Gt),
        ];
        assert_eq!(decide_int(&c, 0), Some(true));
    }

    // A trivial equality (zero polynomial) must NOT force unsat: x^2 = 4 alone is
    // sat, and adding a vacuous `0 = 0` constraint keeps it sat.
    #[test]
    fn integer_trivial_equality_not_unsat() {
        let zero_eq = Polynomial::zero(); // 0 = 0
        assert_eq!(
            decide_int(
                &[(poly(&[(1, 2), (-4, 0)]), Rel::Eq), (zero_eq, Rel::Eq)],
                0
            ),
            Some(true)
        );
    }
}
