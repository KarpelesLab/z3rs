//! Real algebraic numbers — the ordered field of real algebraic numbers, the
//! sample-point arithmetic underlying CAD.
//!
//! Ported from Z3's `math/realclosure` (Z3 4.17.0, MIT), specialised to what a
//! textbook-correct CAD needs (no infinitesimals). A real algebraic number is
//! either an exact [`Rational`], or an irrational represented by a **squarefree**
//! defining polynomial `p` (rational coefficients) together with an **isolating
//! open interval** `(lo, hi)` that contains exactly one real root of `p` and has
//! non-root endpoints of opposite sign. Every operation keeps that invariant.
//!
//! The workhorse is [`Alg::sign_of`]: the exact sign of a rational-coefficient
//! polynomial evaluated at an algebraic number, computed by (a) testing whether
//! the number is a common root via `gcd`, and otherwise (b) refining the
//! isolating interval until the polynomial is sign-constant on it. This is what
//! lets CAD determine the sign of every constraint at each sample point.

use alloc::vec::Vec;

use puremp::Rational;

use crate::math::interval::Interval;
use crate::math::polynomial::{Polynomial, Var};
use crate::math::resultant::resultant;
use crate::math::upoly::{self, UPoly};
use crate::nlsat::elim::subst_var;
use crate::nlsat::icp::eval_interval;

fn two() -> Rational {
    Rational::from_integer(2.into())
}

/// The `UPoly` in variable `var` as a multivariate [`Polynomial`].
pub(crate) fn upoly_to_poly(u: &UPoly, var: Var) -> Polynomial {
    use crate::math::polynomial::Monomial;
    let terms = u
        .coeffs()
        .iter()
        .enumerate()
        .filter(|(_, c)| !c.is_zero())
        .map(|(k, c)| (c.clone(), Monomial::from_powers(&[(var, k as u32)])))
        .collect();
    Polynomial::from_terms(terms)
}

/// A [`Polynomial`] known to be univariate in `var` as a [`UPoly`].
pub(crate) fn poly_to_upoly(p: &Polynomial, var: Var) -> UPoly {
    let deg = p.degree_of(var) as usize;
    let mut coeffs = alloc::vec![Rational::from_integer(0.into()); deg + 1];
    for (k, slot) in coeffs.iter_mut().enumerate() {
        // The coefficient of var^k must be a constant (all other vars are gone).
        *slot = p
            .coeff_of_var(var, k as u32)
            .as_constant()
            .unwrap_or_else(|| Rational::from_integer(0.into()));
    }
    UPoly::from_coeffs(coeffs)
}

/// Build a univariate integer/rational polynomial `R(z)` that has the value
/// `p(point)` as a root, by introducing a fresh variable `z` for the value and
/// eliminating every coordinate: `R(z) = Res(z − p, q_1, …, q_k)` where `q_i` is
/// the defining polynomial of `point[i]` (rational coordinates are substituted
/// directly). See the CAD spec §3.3 / realclosure spec §2.5.
fn eliminate_to_univariate(p: &Polynomial, point: &[Alg]) -> Option<UPoly> {
    let n = point.len();
    let z = n as Var; // fresh variable index, above all coordinates
    // f = z - p
    let mut f = Polynomial::var(z).sub(p);
    for (i, coord) in point.iter().enumerate() {
        match coord {
            Alg::Rational(r) => {
                f = subst_var(&f, i as Var, &Polynomial::constant(r.clone()));
            }
            Alg::Irrational { poly, .. } => {
                let qi = upoly_to_poly(poly, i as Var);
                f = resultant(&f, &qi, i as Var)?; // inexact Bareiss ⇒ decline
            }
        }
    }
    Some(poly_to_upoly(&f, z))
}

/// A rational `L > 0` such that every **nonzero** root `ρ` of `r` has `|ρ| ≥ L`
/// (a conservative Cauchy-style lower bound on the smallest nonzero root
/// magnitude). Used to certify that a suspected-zero value is exactly zero.
fn nonzero_root_lower_bound(r: &UPoly) -> Rational {
    let coeffs = r.coeffs();
    // Lowest-order nonzero coefficient.
    let m = coeffs.iter().position(|c| !c.is_zero());
    let Some(m) = m else {
        return Rational::from_integer(1.into()); // zero polynomial: vacuous
    };
    let am = coeffs[m].abs();
    let mut maxabs = Rational::from_integer(0.into());
    for c in coeffs {
        let a = c.abs();
        if a > maxabs {
            maxabs = a;
        }
    }
    // L = |a_m| / (|a_m| + max|a_i|)  ≤  true bound (conservative ⇒ sound).
    am.div(&am.add(&maxabs))
}

/// The strict sign of a value interval: `Some(+1)` if wholly positive, `Some(-1)`
/// if wholly negative, `None` if it contains (or touches) zero.
fn strict_interval_sign(iv: &Interval) -> Option<i32> {
    let (lo, hi) = iv.bounds()?;
    use crate::math::interval::Bound;
    // Wholly positive: lower endpoint value > 0.
    if let Bound::Finite { value, .. } = lo
        && value.is_positive()
    {
        return Some(1);
    }
    if let Bound::Finite { value, .. } = hi
        && value.is_negative()
    {
        return Some(-1);
    }
    None
}

/// Whether `iv ⊆ (−l, l)` (used to certify a value is within the nonzero-root
/// gap, hence exactly zero).
fn interval_within(iv: &Interval, l: &Rational) -> bool {
    use crate::math::interval::Bound;
    let Some((lo, hi)) = iv.bounds() else {
        return true; // empty interval is trivially inside
    };
    let lo_ok = matches!(lo, Bound::Finite { value, .. } if value > &l.neg());
    let hi_ok = matches!(hi, Bound::Finite { value, .. } if value < l);
    lo_ok && hi_ok
}

/// The isolating interval box for a sample point: each rational coordinate is a
/// degenerate point, each irrational its current isolating interval.
fn boxes_of(point: &[Alg]) -> Vec<Interval> {
    point
        .iter()
        .map(|a| {
            let (lo, hi) = a.interval();
            if lo == hi {
                Interval::point(lo)
            } else {
                Interval::closed(lo, hi)
            }
        })
        .collect()
}

/// The exact sign of a multivariate polynomial `p` at a sample point whose
/// coordinates are algebraic numbers (`point[i]` is the value of variable `i`).
/// Interval arithmetic decides the easy cases; a resultant certification decides
/// a suspected zero exactly. Sound and terminating (CAD spec §3.3).
pub fn sign_at_point(p: &Polynomial, point: &[Alg]) -> Option<i32> {
    // Indices whose coordinate is irrational (refinable).
    let refinable: Vec<usize> = (0..point.len())
        .filter(|&i| matches!(point[i], Alg::Irrational { .. }))
        .collect();
    let mut pt = point.to_vec();

    // Phase 1: interval evaluation with refinement.
    for _ in 0..64 {
        let boxes = boxes_of(&pt);
        let val = eval_interval(p, &boxes);
        if let Some(s) = strict_interval_sign(&val) {
            return Some(s);
        }
        if refinable.is_empty() {
            // Fully rational: the value is exact; read it off directly.
            return Some(exact_rational_sign(p, &pt));
        }
        for &i in &refinable {
            pt[i].refine();
        }
    }

    // Phase 2: certify a suspected zero via the resultant lower bound. If the
    // elimination resultant cannot be formed (inexact Bareiss division), decline.
    let r = eliminate_to_univariate(p, &pt)?;
    if r.is_zero() {
        return Some(0); // p is identically zero along this fiber
    }
    let l = nonzero_root_lower_bound(&r);
    for _ in 0..400 {
        let boxes = boxes_of(&pt);
        let val = eval_interval(p, &boxes);
        if let Some(s) = strict_interval_sign(&val) {
            return Some(s);
        }
        if interval_within(&val, &l) {
            return Some(0); // |value| < L but value is a root of R ⇒ value = 0
        }
        for &i in &refinable {
            pt[i].refine();
        }
    }
    Some(0)
}

/// Exact sign of `p` at an all-rational point.
fn exact_rational_sign(p: &Polynomial, point: &[Alg]) -> i32 {
    let assign = |v: Var| match point.get(v as usize) {
        Some(Alg::Rational(r)) => r.clone(),
        _ => Rational::from_integer(0.into()),
    };
    p.eval(&assign).signum()
}

/// A real algebraic number.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Alg {
    /// An exact rational.
    Rational(Rational),
    /// An irrational root of `poly` isolated in `(lo, hi)`: `poly` is squarefree,
    /// `poly(lo)` and `poly(hi)` are nonzero and of opposite sign, and `(lo, hi)`
    /// contains exactly that one root of `poly`.
    Irrational {
        poly: UPoly,
        lo: Rational,
        hi: Rational,
    },
}

impl Alg {
    /// An algebraic number from a rational.
    pub fn rational(r: Rational) -> Alg {
        Alg::Rational(r)
    }

    /// Isolate all real roots of `p` as algebraic numbers, ascending. A root that
    /// happens to be rational is returned as [`Alg::Rational`].
    pub fn roots_of(p: &UPoly) -> Vec<Alg> {
        let sf = p.squarefree();
        let intervals = upoly::isolate_roots(&sf);
        let mut out = Vec::new();
        for (lo, hi) in intervals {
            out.push(Alg::from_isolation(sf.clone(), lo, hi));
        }
        out
    }

    /// Build from a squarefree polynomial and an isolating interval, collapsing to
    /// a [`Rational`] if an endpoint or the exact midpoint turns out to be the
    /// root (rare, but keeps the representation canonical).
    fn from_isolation(poly: UPoly, lo: Rational, hi: Rational) -> Alg {
        // If the polynomial is linear, the root is rational.
        if poly.degree() == 1 {
            // a*x + b = 0 → x = -b/a
            let a = poly.coeffs()[1].clone();
            let b = poly.coeffs()[0].clone();
            return Alg::Rational(b.neg().div(&a));
        }
        Alg::Irrational { poly, lo, hi }
    }

    /// A rational strictly inside the isolating interval (or the value itself for
    /// a rational) — useful as an approximation and for ordering.
    pub fn approx(&self) -> Rational {
        match self {
            Alg::Rational(r) => r.clone(),
            Alg::Irrational { lo, hi, .. } => lo.add(hi).div(&two()),
        }
    }

    /// Refine an irrational's isolating interval by one bisection, keeping the
    /// unique root. If the midpoint is exactly the root, collapse to a rational.
    pub fn refine(&mut self) {
        if let Alg::Irrational { poly, lo, hi } = self {
            let mid = lo.add(hi).div(&two());
            let sm = poly.sign_at(&mid);
            if sm == 0 {
                *self = Alg::Rational(mid);
                return;
            }
            // Keep the half where the sign change (the root) lies.
            if poly.sign_at(lo) == sm {
                *lo = mid;
            } else {
                *hi = mid;
            }
        }
    }

    /// The exact sign of `q(self)` ∈ {−1, 0, +1}, where `q` has rational
    /// coefficients.
    pub fn sign_of(&self, q: &UPoly) -> i32 {
        match self {
            Alg::Rational(r) => q.sign_at(r),
            Alg::Irrational { poly, lo, hi } => {
                if q.is_zero() {
                    return 0;
                }
                // (a) Is `self` a common root of `poly` and `q`? Then q(self)=0.
                // `self` is a root of g = gcd(poly, q) iff g changes sign across
                // the isolating interval (endpoints are non-roots of poly ⊇ g).
                let g = poly.gcd(q);
                if g.degree() >= 1 {
                    let sl = g.sign_at(lo);
                    let sh = g.sign_at(hi);
                    if sl != 0 && sh != 0 && sl != sh {
                        return 0;
                    }
                }
                // (b) q(self) ≠ 0: refine until q is sign-constant on the
                // isolating interval, then read its sign at an endpoint.
                let mut a = lo.clone();
                let mut b = hi.clone();
                let ps = poly.clone();
                for _ in 0..256 {
                    let qa = q.sign_at(&a);
                    let qb = q.sign_at(&b);
                    if qa != 0 && qa == qb {
                        return qa; // constant sign on [a,b] ⇒ that is q(self)'s sign
                    }
                    // Bisect keeping the root of `poly`.
                    let mid = a.add(&b).div(&two());
                    let sm = ps.sign_at(&mid);
                    if sm == 0 {
                        // `mid` is the root exactly (rational): evaluate q there.
                        return q.sign_at(&mid);
                    }
                    if ps.sign_at(&a) == sm {
                        a = mid;
                    } else {
                        b = mid;
                    }
                }
                // Fallback (should not happen for well-separated roots): use the
                // interval midpoint's sign as a best effort.
                q.sign_at(&a.add(&b).div(&two()))
            }
        }
    }

    /// Where a rational `r` lies relative to `self`: `Less` if `r < self`,
    /// `Greater` if `r > self`, `Equal` if `r == self`.
    pub fn locate(&self, r: &Rational) -> core::cmp::Ordering {
        use core::cmp::Ordering;
        match self {
            Alg::Rational(v) => r.cmp(v),
            Alg::Irrational { poly, lo, hi } => {
                if r <= lo {
                    return Ordering::Less;
                }
                if r >= hi {
                    return Ordering::Greater;
                }
                let sr = poly.sign_at(r);
                if sr == 0 {
                    return Ordering::Equal;
                }
                // The root lies where `poly` changes from its sign at `lo`; if `r`
                // still has that sign, the root is above `r`, so `r < self`.
                if sr == poly.sign_at(lo) {
                    Ordering::Less
                } else {
                    Ordering::Greater
                }
            }
        }
    }

    /// The isolating interval `(lo, hi)` (a degenerate point for a rational).
    pub fn interval(&self) -> (Rational, Rational) {
        match self {
            Alg::Rational(r) => (r.clone(), r.clone()),
            Alg::Irrational { lo, hi, .. } => (lo.clone(), hi.clone()),
        }
    }

    /// Total order on algebraic numbers (realclosure spec §4). Equality is only
    /// declared when one number's isolating interval provably **contains** the
    /// other's *and* it is a root of that defining polynomial — so distinct but
    /// close roots are never wrongly merged (which would be unsound for CAD).
    pub fn compare(&self, other: &Alg) -> core::cmp::Ordering {
        use core::cmp::Ordering;
        match (self, other) {
            (Alg::Rational(a), Alg::Rational(b)) => return a.cmp(b),
            (Alg::Rational(a), _) => return other.locate(a),
            (_, Alg::Rational(b)) => return self.locate(b).reverse(),
            _ => {}
        }
        let mut a = self.clone();
        let mut b = other.clone();
        for _ in 0..2000 {
            let (alo, ahi) = a.interval();
            let (blo, bhi) = b.interval();
            if ahi <= blo {
                return Ordering::Less;
            }
            if bhi <= alo {
                return Ordering::Greater;
            }
            // Overlapping: check provable equality (containment + shared root).
            if let Alg::Irrational { poly: pa, .. } = &a
                && blo >= alo
                && bhi <= ahi
                && b.sign_of(pa) == 0
            {
                return Ordering::Equal;
            }
            if let Alg::Irrational { poly: pb, .. } = &b
                && alo >= blo
                && ahi <= bhi
                && a.sign_of(pb) == 0
            {
                return Ordering::Equal;
            }
            a.refine();
            b.refine();
        }
        a.approx().cmp(&b.approx())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn r(n: i64) -> Rational {
        Rational::from_integer(n.into())
    }
    fn p(cs: &[i64]) -> UPoly {
        UPoly::from_coeffs(cs.iter().map(|&c| r(c)).collect())
    }

    // Roots of x^2 - 2 are ±√2 (irrational).
    #[test]
    fn isolates_sqrt2() {
        let roots = Alg::roots_of(&p(&[-2, 0, 1]));
        assert_eq!(roots.len(), 2);
        // Both irrational, one negative one positive.
        assert!(roots[0].approx() < r(0));
        assert!(roots[1].approx() > r(0));
        assert!(matches!(roots[0], Alg::Irrational { .. }));
    }

    // A rational root is recognised as rational.
    #[test]
    fn rational_root_is_rational() {
        // 2x - 6 = 0 → x = 3.
        let roots = Alg::roots_of(&p(&[-6, 2]));
        assert_eq!(roots, vec![Alg::Rational(r(3))]);
    }

    // sign of q at √2: q = x^2 - 2 vanishes; q = x - 1 is positive (√2 > 1);
    // q = x - 2 is negative (√2 < 2).
    #[test]
    fn sign_at_sqrt2() {
        let sqrt2 = Alg::roots_of(&p(&[-2, 0, 1]))
            .into_iter()
            .find(|a| a.approx() > r(0))
            .unwrap();
        assert_eq!(sqrt2.sign_of(&p(&[-2, 0, 1])), 0); // x^2 - 2 = 0 at √2
        assert_eq!(sqrt2.sign_of(&p(&[-1, 1])), 1); // √2 - 1 > 0
        assert_eq!(sqrt2.sign_of(&p(&[-2, 1])), -1); // √2 - 2 < 0
        // x^2 - 3 at √2 = 2 - 3 = -1 < 0.
        assert_eq!(sqrt2.sign_of(&p(&[-3, 0, 1])), -1);
    }

    // Locating a rational relative to √2: 1 < √2 < 2, and x^2-2's root value.
    #[test]
    fn locate_rationals() {
        use core::cmp::Ordering;
        let sqrt2 = Alg::roots_of(&p(&[-2, 0, 1]))
            .into_iter()
            .find(|a| a.approx() > r(0))
            .unwrap();
        assert_eq!(sqrt2.locate(&r(1)), Ordering::Less); // 1 < √2
        assert_eq!(sqrt2.locate(&r(2)), Ordering::Greater); // 2 > √2
        assert_eq!(
            sqrt2.locate(&Rational::new(3.into(), 2.into())),
            Ordering::Greater
        ); // 1.5 > √2 (1.5² = 2.25 > 2)
        assert_eq!(
            sqrt2.locate(&Rational::new(7.into(), 5.into())),
            Ordering::Less
        ); // 1.4 < √2 (1.4² = 1.96 < 2)
    }

    // sign_at_point on multivariate polynomials at algebraic sample points.
    #[test]
    fn sign_at_algebraic_point() {
        use crate::math::polynomial::Monomial;
        let sqrt2 = Alg::roots_of(&p(&[-2, 0, 1]))
            .into_iter()
            .find(|a| a.approx() > r(0))
            .unwrap();
        // g = x^2 + y^2 - 3, at (x=1, y=√2): 1 + 2 - 3 = 0.
        let g = Polynomial::from_terms(alloc::vec![
            (r(1), Monomial::from_powers(&[(0, 2)])),
            (r(1), Monomial::from_powers(&[(1, 2)])),
            (r(-3), Monomial::one()),
        ]);
        assert_eq!(
            sign_at_point(&g, &[Alg::Rational(r(1)), sqrt2.clone()]).unwrap(),
            0
        );
        // At (x=1, y=√2): x^2+y^2-2 = 1 ⇒ +1.
        let g2 = Polynomial::from_terms(alloc::vec![
            (r(1), Monomial::from_powers(&[(0, 2)])),
            (r(1), Monomial::from_powers(&[(1, 2)])),
            (r(-2), Monomial::one()),
        ]);
        assert_eq!(
            sign_at_point(&g2, &[Alg::Rational(r(1)), sqrt2.clone()]).unwrap(),
            1
        );
        // At (x=1, y=√2): x^2+y^2-4 = -1 ⇒ -1.
        let g3 = Polynomial::from_terms(alloc::vec![
            (r(1), Monomial::from_powers(&[(0, 2)])),
            (r(1), Monomial::from_powers(&[(1, 2)])),
            (r(-4), Monomial::one()),
        ]);
        assert_eq!(
            sign_at_point(&g3, &[Alg::Rational(r(1)), sqrt2.clone()]).unwrap(),
            -1
        );
        // Two algebraic coords: x=√2, y=√2 ; x*y - 2 = 2 - 2 = 0.
        let g4 = Polynomial::from_terms(alloc::vec![
            (r(1), Monomial::from_powers(&[(0, 1), (1, 1)])),
            (r(-2), Monomial::one()),
        ]);
        assert_eq!(
            sign_at_point(&g4, &[sqrt2.clone(), sqrt2.clone()]).unwrap(),
            0
        );
        // x*y - 1 at (√2,√2) = 2 - 1 = 1 ⇒ +1.
        let g5 = Polynomial::from_terms(alloc::vec![
            (r(1), Monomial::from_powers(&[(0, 1), (1, 1)])),
            (r(-1), Monomial::one()),
        ]);
        assert_eq!(sign_at_point(&g5, &[sqrt2.clone(), sqrt2]).unwrap(), 1);
    }
}
