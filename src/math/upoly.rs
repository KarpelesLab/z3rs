//! Dense univariate polynomials over the exact rationals — the polynomial
//! foundation shared by the nonlinear-arithmetic machinery (`nlsat::univariate`,
//! `nlsat::realclosure`, `nlsat::cad`).
//!
//! Ported from the univariate parts of Z3's `math/polynomial` and the polynomial
//! remainder sequences in `math/realclosure` (Z3 4.17.0, MIT). A [`UPoly`] is the
//! coefficient vector `[c₀, c₁, …, cₙ]` for `c₀ + c₁x + … + cₙxⁿ`, kept
//! normalised (no trailing-zero high coefficients), so the empty vector is the
//! zero polynomial and the leading coefficient is always nonzero.

use alloc::vec;
use alloc::vec::Vec;

use puremp::Rational;

fn zero() -> Rational {
    Rational::from_integer(0.into())
}
fn one() -> Rational {
    Rational::from_integer(1.into())
}

/// A dense univariate polynomial over `Rational`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct UPoly {
    coeffs: Vec<Rational>,
}

impl UPoly {
    /// The zero polynomial.
    pub fn zero() -> UPoly {
        UPoly { coeffs: Vec::new() }
    }

    /// A constant polynomial.
    pub fn constant(c: Rational) -> UPoly {
        UPoly::from_coeffs(vec![c])
    }

    /// The monomial `x`.
    pub fn x() -> UPoly {
        UPoly::from_coeffs(vec![zero(), one()])
    }

    /// Build from a coefficient vector (ascending degree), normalising away
    /// trailing zero coefficients.
    pub fn from_coeffs(mut coeffs: Vec<Rational>) -> UPoly {
        while coeffs.last().is_some_and(|c| c.is_zero()) {
            coeffs.pop();
        }
        UPoly { coeffs }
    }

    /// The coefficient vector (ascending degree); empty for the zero polynomial.
    pub fn coeffs(&self) -> &[Rational] {
        &self.coeffs
    }

    /// Is this the zero polynomial?
    pub fn is_zero(&self) -> bool {
        self.coeffs.is_empty()
    }

    /// Degree; the zero polynomial has degree 0 by convention here.
    pub fn degree(&self) -> usize {
        self.coeffs.len().saturating_sub(1)
    }

    /// The leading coefficient (0 for the zero polynomial).
    pub fn lead(&self) -> Rational {
        self.coeffs.last().cloned().unwrap_or_else(zero)
    }

    /// Evaluate `p(x)` via Horner's rule.
    pub fn eval(&self, x: &Rational) -> Rational {
        let mut acc = zero();
        for c in self.coeffs.iter().rev() {
            acc = acc.mul(x).add(c);
        }
        acc
    }

    /// The sign of `p(x)`: -1, 0, +1.
    pub fn sign_at(&self, x: &Rational) -> i32 {
        self.eval(x).signum()
    }

    /// The formal derivative.
    pub fn deriv(&self) -> UPoly {
        if self.coeffs.len() <= 1 {
            return UPoly::zero();
        }
        let mut c = Vec::with_capacity(self.coeffs.len() - 1);
        for (i, coeff) in self.coeffs.iter().enumerate().skip(1) {
            c.push(coeff.mul(&Rational::from_integer((i as i64).into())));
        }
        UPoly::from_coeffs(c)
    }

    /// Multiply by a scalar.
    pub fn scale(&self, s: &Rational) -> UPoly {
        if s.is_zero() {
            return UPoly::zero();
        }
        UPoly::from_coeffs(self.coeffs.iter().map(|c| c.mul(s)).collect())
    }

    /// Negate.
    pub fn neg(&self) -> UPoly {
        UPoly::from_coeffs(self.coeffs.iter().map(|c| c.neg()).collect())
    }

    /// Add.
    pub fn add(&self, other: &UPoly) -> UPoly {
        let n = self.coeffs.len().max(other.coeffs.len());
        let mut c = vec![zero(); n];
        for (i, a) in self.coeffs.iter().enumerate() {
            c[i] = c[i].add(a);
        }
        for (i, b) in other.coeffs.iter().enumerate() {
            c[i] = c[i].add(b);
        }
        UPoly::from_coeffs(c)
    }

    /// Subtract.
    pub fn sub(&self, other: &UPoly) -> UPoly {
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

    /// Multiply.
    pub fn mul(&self, other: &UPoly) -> UPoly {
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

    /// Raise to a nonnegative power.
    pub fn pow(&self, n: u32) -> UPoly {
        let mut acc = UPoly::constant(one());
        let mut base = self.clone();
        let mut e = n;
        while e > 0 {
            if e & 1 == 1 {
                acc = acc.mul(&base);
            }
            e >>= 1;
            if e > 0 {
                base = base.mul(&base);
            }
        }
        acc
    }

    /// Polynomial remainder `self mod divisor` over the rationals (exact).
    pub fn rem(&self, divisor: &UPoly) -> UPoly {
        debug_assert!(!divisor.is_zero());
        let mut r = self.clone();
        let d_deg = divisor.degree();
        let d_lead = divisor.lead();
        while !r.is_zero() && r.degree() >= d_deg {
            let shift = r.degree() - d_deg;
            let factor = r.lead().div(&d_lead);
            let mut sub = vec![zero(); shift + divisor.coeffs.len()];
            for (i, c) in divisor.coeffs.iter().enumerate() {
                sub[i + shift] = c.mul(&factor);
            }
            r = r.sub(&UPoly::from_coeffs(sub));
        }
        r
    }

    /// Quotient and remainder `self = q·divisor + r`.
    pub fn div_rem(&self, divisor: &UPoly) -> (UPoly, UPoly) {
        debug_assert!(!divisor.is_zero());
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
        (UPoly::from_coeffs(q), r)
    }

    /// Exact quotient (assumes `divisor` divides `self`).
    pub fn div_exact(&self, divisor: &UPoly) -> UPoly {
        self.div_rem(divisor).0
    }

    /// Monic GCD via the Euclidean algorithm (the zero polynomial's GCD with `p`
    /// is the monic form of `p`).
    pub fn gcd(&self, other: &UPoly) -> UPoly {
        let mut a = self.clone();
        let mut b = other.clone();
        while !b.is_zero() {
            let r = a.rem(&b);
            a = b;
            b = r;
        }
        a.monic()
    }

    /// The monic associate `p / lead(p)` (the zero polynomial is unchanged).
    pub fn monic(&self) -> UPoly {
        if self.is_zero() {
            return self.clone();
        }
        let lead = self.lead();
        self.scale(&lead.recip())
    }

    /// The squarefree part `p / gcd(p, p')` (same roots, all simple).
    pub fn squarefree(&self) -> UPoly {
        if self.degree() == 0 {
            return self.clone();
        }
        let g = self.gcd(&self.deriv());
        if g.degree() == 0 {
            return self.monic();
        }
        self.div_exact(&g)
    }

    /// A Cauchy bound `M` with every real root in `(-M, M)`.
    pub fn root_bound(&self) -> Rational {
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

/// The Sturm sequence of `p`: `s₀ = p`, `s₁ = p'`, `sᵢ₊₁ = −(sᵢ₋₁ mod sᵢ)`.
pub fn sturm_chain(p: &UPoly) -> Vec<UPoly> {
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

/// Sign variations of the Sturm chain at `x` (zeros skipped).
pub fn variations(chain: &[UPoly], x: &Rational) -> usize {
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

/// Number of distinct real roots of `p` in the half-open interval `(a, b]`,
/// where `chain = sturm_chain(p)`.
pub fn root_count(chain: &[UPoly], a: &Rational, b: &Rational) -> i64 {
    variations(chain, a) as i64 - variations(chain, b) as i64
}

/// Isolate the real roots of `p` into disjoint open `(lo, hi)` intervals, each
/// containing exactly one root and with **non-root endpoints**, sorted
/// ascending. `p` is treated via its squarefree part so all roots are simple.
pub fn isolate_roots(p: &UPoly) -> Vec<(Rational, Rational)> {
    let sf = p.squarefree();
    if sf.degree() == 0 {
        return Vec::new();
    }
    let chain = sturm_chain(&sf);
    let m = sf.root_bound();
    let two = Rational::from_integer(2.into());
    let mut out = Vec::new();
    let mut stack = vec![(m.neg(), m)];
    let mut guard = 0;
    while let Some((a, b)) = stack.pop() {
        guard += 1;
        if guard > 200_000 {
            break;
        }
        let n = root_count(&chain, &a, &b);
        if n <= 0 {
            continue;
        }
        if n == 1 {
            out.push((a, b));
            continue;
        }
        // Split at a non-root midpoint (nudge off `sf`'s roots if necessary).
        let mut mid = a.add(&b).div(&two);
        let step = b.sub(&a).div(&Rational::from_integer(1024.into()));
        let mut tries = 0;
        while sf.sign_at(&mid) == 0 && tries < 2048 {
            mid = mid.add(&step);
            tries += 1;
        }
        stack.push((a, mid.clone()));
        stack.push((mid, b));
    }
    out.sort_by(|x, y| x.0.cmp(&y.0));
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    fn r(n: i64) -> Rational {
        Rational::from_integer(n.into())
    }
    // c₀ + c₁x + … from integer coeffs.
    fn p(cs: &[i64]) -> UPoly {
        UPoly::from_coeffs(cs.iter().map(|&c| r(c)).collect())
    }

    #[test]
    fn arithmetic_and_eval() {
        let a = p(&[1, 2, 1]); // (x+1)^2
        assert_eq!(a.eval(&r(2)), r(9));
        assert_eq!(a.degree(), 2);
        let b = p(&[-1, 1]); // x-1
        assert_eq!(a.mul(&b), p(&[-1, -1, 1, 1])); // (x+1)^2 (x-1)
        assert_eq!(a.deriv(), p(&[2, 2])); // 2x+2
    }

    #[test]
    fn gcd_and_squarefree() {
        // (x-1)^2 (x+2) : gcd with derivative reveals the repeated factor.
        let poly = p(&[2, -3, 0, 1]); // x^3 - 3x + 2 = (x-1)^2(x+2)
        let sf = poly.squarefree();
        // squarefree part has roots {1, -2}, degree 2, monic.
        assert_eq!(sf.degree(), 2);
        assert_eq!(sf.eval(&r(1)), r(0));
        assert_eq!(sf.eval(&r(-2)), r(0));
        assert!(!sf.eval(&r(0)).is_zero());
    }

    #[test]
    fn div_rem_exact() {
        let a = p(&[-1, 0, 1]); // x^2 - 1
        let b = p(&[-1, 1]); // x - 1
        let (q, rem) = a.div_rem(&b);
        assert_eq!(q, p(&[1, 1])); // x + 1
        assert!(rem.is_zero());
    }

    #[test]
    fn isolates_roots() {
        // x^3 - 2x = x(x^2-2): roots -√2, 0, √2 → three isolating intervals.
        let poly = p(&[0, -2, 0, 1]);
        let roots = isolate_roots(&poly);
        assert_eq!(roots.len(), 3);
        // The middle interval brackets 0.
        assert!(roots.iter().any(|(a, b)| a < &r(0) && b > &r(0)));
        // √2 ≈ 1.414 is bracketed by one interval.
        assert!(roots.iter().any(|(a, b)| a < &r(2) && b > &r(1) && a > &r(0)));
    }

    #[test]
    fn sturm_counts_roots() {
        // x^2 - 2 has exactly 2 real roots in a wide interval.
        let poly = p(&[-2, 0, 1]);
        let chain = sturm_chain(&poly);
        assert_eq!(root_count(&chain, &r(-10), &r(10)), 2);
        assert_eq!(root_count(&chain, &r(0), &r(10)), 1);
    }
}
