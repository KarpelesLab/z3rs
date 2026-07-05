//! Multivariate polynomials over the exact rationals.
//!
//! Ported from Z3's `math/polynomial` (`z3/src/math/polynomial/polynomial.{h,cpp}`,
//! Z3 4.17.0, MIT). Z3's `polynomial::manager` stores dense-exponent monomials
//! and coefficients in a memory-managed pool; here we keep the same *semantics*
//! (canonical, fully-expanded sum of monomials with nonzero rational
//! coefficients) using ordinary owned `Vec`s and `puremp::Rational`, which is
//! sufficient for the interval/Gröbner/nlsat consumers that manipulate exact
//! polynomials symbolically.
//!
//! A [`Monomial`] is a canonical product of powers `x_i^{e_i}` with `e_i > 0`,
//! stored as a list of `(var, exponent)` pairs sorted by variable. A
//! [`Polynomial`] is a canonical sum of `coeff · monomial` terms sorted by the
//! monomial order, with no zero coefficients and no repeated monomials — so two
//! polynomials are equal *iff* their term vectors are equal (structural `Eq`).

use alloc::vec;
use alloc::vec::Vec;
use core::cmp::Ordering;

use puremp::Rational;

/// A variable is identified by a small nonnegative index (like Z3's `polynomial::var`).
pub type Var = u32;

/// A canonical monomial: the product of `var^exp` for each entry, with every
/// `exp > 0` and entries sorted ascending by `var` (so the representation is
/// unique). The empty vector is the constant monomial `1`.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Monomial {
    powers: Vec<(Var, u32)>,
}

impl Monomial {
    /// The constant monomial `1`.
    pub fn one() -> Monomial {
        Monomial { powers: Vec::new() }
    }

    /// The monomial `var^1`.
    pub fn var(v: Var) -> Monomial {
        Monomial {
            powers: vec![(v, 1)],
        }
    }

    /// Build from arbitrary `(var, exp)` pairs, summing exponents of repeated
    /// variables and dropping zero exponents, then canonicalising.
    pub fn from_powers(pairs: &[(Var, u32)]) -> Monomial {
        let mut powers: Vec<(Var, u32)> = Vec::new();
        for &(v, e) in pairs {
            if e == 0 {
                continue;
            }
            match powers.iter().position(|(pv, _)| *pv == v) {
                Some(i) => powers[i].1 += e,
                None => powers.push((v, e)),
            }
        }
        powers.sort_by_key(|&(v, _)| v);
        Monomial { powers }
    }

    /// Is this the constant monomial `1`?
    pub fn is_one(&self) -> bool {
        self.powers.is_empty()
    }

    /// The total degree (sum of all exponents).
    pub fn total_degree(&self) -> u32 {
        self.powers.iter().map(|&(_, e)| e).sum()
    }

    /// The exponent of `v` in this monomial (0 if absent).
    pub fn degree_of(&self, v: Var) -> u32 {
        self.powers
            .iter()
            .find(|&&(pv, _)| pv == v)
            .map_or(0, |&(_, e)| e)
    }

    /// The variables occurring in this monomial, ascending.
    pub fn vars(&self) -> impl Iterator<Item = Var> + '_ {
        self.powers.iter().map(|&(v, _)| v)
    }

    /// Multiply two monomials (adds exponents).
    pub fn mul(&self, other: &Monomial) -> Monomial {
        let mut powers = self.powers.clone();
        for &(v, e) in &other.powers {
            match powers.iter().position(|(pv, _)| *pv == v) {
                Some(i) => powers[i].1 += e,
                None => powers.push((v, e)),
            }
        }
        powers.sort_by_key(|&(v, _)| v);
        Monomial { powers }
    }

    /// Evaluate `∏ var^exp` at the given assignment (missing vars ⇒ error).
    fn eval(&self, assign: &dyn Fn(Var) -> Rational) -> Rational {
        let mut acc = Rational::from_integer(1.into());
        for &(v, e) in &self.powers {
            acc = acc.mul(&assign(v).pow(e as i32));
        }
        acc
    }

    /// Graded lexicographic order: higher total degree first, then lexicographic
    /// on `(var, exp)` pairs. Matches the usual admissible monomial order used
    /// for canonicalisation and (later) Gröbner reduction.
    fn grlex_cmp(&self, other: &Monomial) -> Ordering {
        match self.total_degree().cmp(&other.total_degree()) {
            Ordering::Equal => self.powers.cmp(&other.powers),
            ord => ord,
        }
    }

    /// Divide `self` by `other` if `other` divides it (every exponent of `other`
    /// is ≤ the corresponding exponent of `self`); otherwise `None`.
    pub fn checked_div(&self, other: &Monomial) -> Option<Monomial> {
        let mut powers: Vec<(Var, u32)> = Vec::new();
        for &(v, e) in &self.powers {
            let oe = other.degree_of(v);
            if oe > e {
                return None;
            }
            if e - oe > 0 {
                powers.push((v, e - oe));
            }
        }
        // `other` must not require a variable absent from `self`.
        for &(v, oe) in &other.powers {
            if oe > 0 && self.degree_of(v) == 0 {
                return None;
            }
        }
        Some(Monomial { powers })
    }
}

/// A canonical multivariate polynomial: a sorted list of `(coeff, monomial)`
/// terms with nonzero coefficients and distinct monomials. The empty term list
/// is the zero polynomial.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Polynomial {
    /// Sorted descending by [`Monomial::grlex_cmp`] (leading term first).
    terms: Vec<(Rational, Monomial)>,
}

impl Polynomial {
    /// The zero polynomial.
    pub fn zero() -> Polynomial {
        Polynomial { terms: Vec::new() }
    }

    /// A constant polynomial.
    pub fn constant(c: Rational) -> Polynomial {
        if c.is_zero() {
            Polynomial::zero()
        } else {
            Polynomial {
                terms: vec![(c, Monomial::one())],
            }
        }
    }

    /// The polynomial equal to a single variable `v`.
    pub fn var(v: Var) -> Polynomial {
        Polynomial {
            terms: vec![(Rational::from_integer(1.into()), Monomial::var(v))],
        }
    }

    /// Build from arbitrary `(coeff, monomial)` terms, combining like monomials
    /// and dropping zeros — the canonicalising constructor.
    pub fn from_terms(terms: Vec<(Rational, Monomial)>) -> Polynomial {
        let mut p = Polynomial { terms: Vec::new() };
        for (c, m) in terms {
            p.add_term(c, m);
        }
        p.canonicalize();
        p
    }

    fn add_term(&mut self, c: Rational, m: Monomial) {
        if c.is_zero() {
            return;
        }
        match self.terms.iter_mut().find(|(_, tm)| *tm == m) {
            Some(slot) => {
                slot.0 = slot.0.add(&c);
            }
            None => self.terms.push((c, m)),
        }
    }

    fn canonicalize(&mut self) {
        self.terms.retain(|(c, _)| !c.is_zero());
        self.terms.sort_by(|(_, a), (_, b)| b.grlex_cmp(a)); // leading (largest) first
    }

    /// Is this the zero polynomial?
    pub fn is_zero(&self) -> bool {
        self.terms.is_empty()
    }

    /// Is this a constant (degree 0 or zero)?
    pub fn is_constant(&self) -> bool {
        self.terms.is_empty() || (self.terms.len() == 1 && self.terms[0].1.is_one())
    }

    /// If this is a constant polynomial, its value.
    pub fn as_constant(&self) -> Option<Rational> {
        match self.terms.as_slice() {
            [] => Some(Rational::from_integer(0.into())),
            [(c, m)] if m.is_one() => Some(c.clone()),
            _ => None,
        }
    }

    /// The number of terms (monomials with nonzero coefficient).
    pub fn num_terms(&self) -> usize {
        self.terms.len()
    }

    /// Read-only view of the canonical terms (leading term first).
    pub fn terms(&self) -> &[(Rational, Monomial)] {
        &self.terms
    }

    /// The total degree of the polynomial (the max total degree of any term);
    /// the zero polynomial has degree 0 by convention.
    pub fn total_degree(&self) -> u32 {
        self.terms
            .iter()
            .map(|(_, m)| m.total_degree())
            .max()
            .unwrap_or(0)
    }

    /// The degree of the polynomial in a single variable `v`.
    pub fn degree_of(&self, v: Var) -> u32 {
        self.terms
            .iter()
            .map(|(_, m)| m.degree_of(v))
            .max()
            .unwrap_or(0)
    }

    /// View the polynomial as a univariate polynomial in `v` with polynomial
    /// coefficients: return the coefficient of `v^k` as a [`Polynomial`] in the
    /// remaining variables (the `v`-power stripped from each contributing term).
    pub fn coeff_of_var(&self, v: Var, k: u32) -> Polynomial {
        let terms = self
            .terms
            .iter()
            .filter(|(_, m)| m.degree_of(v) == k)
            .map(|(c, m)| {
                let powers: Vec<(Var, u32)> = m
                    .vars()
                    .filter(|&x| x != v)
                    .map(|x| (x, m.degree_of(x)))
                    .collect();
                (c.clone(), Monomial::from_powers(&powers))
            })
            .collect();
        Polynomial::from_terms(terms)
    }

    /// Whether the polynomial is linear (total degree ≤ 1).
    pub fn is_linear(&self) -> bool {
        self.total_degree() <= 1
    }

    /// The partial derivative with respect to variable `v`.
    pub fn deriv_var(&self, v: Var) -> Polynomial {
        let terms = self
            .terms
            .iter()
            .filter(|(_, m)| m.degree_of(v) >= 1)
            .map(|(c, m)| {
                let d = m.degree_of(v);
                let powers: Vec<(Var, u32)> = m
                    .vars()
                    .map(|x| {
                        if x == v {
                            (x, d - 1)
                        } else {
                            (x, m.degree_of(x))
                        }
                    })
                    .collect();
                (
                    c.mul(&Rational::from_integer((d as i64).into())),
                    Monomial::from_powers(&powers),
                )
            })
            .collect();
        Polynomial::from_terms(terms)
    }

    /// Negate every coefficient.
    pub fn neg(&self) -> Polynomial {
        Polynomial {
            terms: self
                .terms
                .iter()
                .map(|(c, m)| (c.neg(), m.clone()))
                .collect(),
        }
    }

    /// Add two polynomials.
    pub fn add(&self, other: &Polynomial) -> Polynomial {
        let mut p = self.clone();
        for (c, m) in &other.terms {
            p.add_term(c.clone(), m.clone());
        }
        p.canonicalize();
        p
    }

    /// Subtract `other` from `self`.
    pub fn sub(&self, other: &Polynomial) -> Polynomial {
        self.add(&other.neg())
    }

    /// Multiply two polynomials (full distribution).
    pub fn mul(&self, other: &Polynomial) -> Polynomial {
        let mut p = Polynomial { terms: Vec::new() };
        for (ca, ma) in &self.terms {
            for (cb, mb) in &other.terms {
                p.add_term(ca.mul(cb), ma.mul(mb));
            }
        }
        p.canonicalize();
        p
    }

    /// Exact quotient `self / divisor`, assuming `divisor` divides `self`
    /// exactly (multivariate long division by leading terms in graded-lex order;
    /// used by the fraction-free Bareiss determinant, which guarantees
    /// exactness). Panics if a leading-term division is not possible.
    pub fn div_exact(&self, divisor: &Polynomial) -> Polynomial {
        debug_assert!(!divisor.is_zero());
        let (dc, dm) = divisor.terms[0].clone(); // graded-lex leading term
        let mut rem = self.clone();
        let mut quot = Polynomial::zero();
        while let Some((rc, rm)) = rem.terms.first().cloned() {
            let qm = rm
                .checked_div(&dm)
                .expect("div_exact: leading term not divisible (inexact division)");
            let qc = rc.div(&dc);
            let qterm = Polynomial {
                terms: vec![(qc, qm)],
            };
            quot = quot.add(&qterm);
            rem = rem.sub(&divisor.mul(&qterm));
        }
        quot
    }

    /// Multiply by a scalar rational.
    pub fn scale(&self, c: &Rational) -> Polynomial {
        if c.is_zero() {
            return Polynomial::zero();
        }
        Polynomial {
            terms: self
                .terms
                .iter()
                .map(|(tc, m)| (tc.mul(c), m.clone()))
                .collect(),
        }
    }

    /// Raise to a nonnegative integer power.
    pub fn pow(&self, n: u32) -> Polynomial {
        let mut acc = Polynomial::constant(Rational::from_integer(1.into()));
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

    /// Evaluate at an assignment of every occurring variable to a rational.
    pub fn eval(&self, assign: &dyn Fn(Var) -> Rational) -> Rational {
        let mut acc = Rational::from_integer(0.into());
        for (c, m) in &self.terms {
            acc = acc.add(&c.mul(&m.eval(assign)));
        }
        acc
    }

    /// The set of variables occurring anywhere, ascending & deduplicated.
    pub fn vars(&self) -> Vec<Var> {
        let mut vs: Vec<Var> = self.terms.iter().flat_map(|(_, m)| m.vars()).collect();
        vs.sort_unstable();
        vs.dedup();
        vs
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn r(n: i64) -> Rational {
        Rational::from_integer(n.into())
    }
    fn rat(n: i64, d: i64) -> Rational {
        Rational::new(n.into(), d.into())
    }

    // (x + 1)(x - 1) == x^2 - 1
    #[test]
    fn difference_of_squares() {
        let x = Polynomial::var(0);
        let one = Polynomial::constant(r(1));
        let lhs = x.add(&one).mul(&x.sub(&one));
        let rhs = x.mul(&x).sub(&one);
        assert_eq!(lhs, rhs);
        assert_eq!(lhs.total_degree(), 2);
    }

    // (x + y)^2 == x^2 + 2xy + y^2, checked structurally and by evaluation.
    #[test]
    fn square_of_sum() {
        let x = Polynomial::var(0);
        let y = Polynomial::var(1);
        let expanded = x.add(&y).pow(2);
        let manual = Polynomial::from_terms(vec![
            (r(1), Monomial::from_powers(&[(0, 2)])),
            (r(2), Monomial::from_powers(&[(0, 1), (1, 1)])),
            (r(1), Monomial::from_powers(&[(1, 2)])),
        ]);
        assert_eq!(expanded, manual);
    }

    // Differential check: for many random rational assignments, the factored and
    // expanded forms of a polynomial identity agree numerically — an independent
    // oracle for the symbolic algebra above.
    #[test]
    fn eval_matches_factored_form() {
        // p = (2x - 3y + 1)(x + y) ; q = 2x^2 - xy - 3y^2 + x + y
        let x = Polynomial::var(0);
        let y = Polynomial::var(1);
        let p = x
            .scale(&r(2))
            .sub(&y.scale(&r(3)))
            .add(&Polynomial::constant(r(1)))
            .mul(&x.add(&y));
        // Deterministic pseudo-random sample points (no RNG dependency).
        let samples = [
            (3i64, 5i64),
            (-2, 7),
            (11, -4),
            (1, 1),
            (-9, -9),
            (0, 6),
            (8, 0),
        ];
        for (a, b) in samples {
            let want = {
                // 2a^2 - ab - 3b^2 + a + b, computed in Rational directly.
                let a = r(a);
                let b = r(b);
                let two_a2 = a.mul(&a).mul(&r(2));
                let ab = a.mul(&b);
                let three_b2 = b.mul(&b).mul(&r(3));
                two_a2.sub(&ab).sub(&three_b2).add(&a).add(&b)
            };
            let got = p.eval(&|v| if v == 0 { r(a) } else { r(b) });
            assert_eq!(got, want, "mismatch at ({a},{b})");
        }
    }

    #[test]
    fn scaling_and_zero() {
        let x = Polynomial::var(0);
        assert!(x.scale(&r(0)).is_zero());
        assert_eq!(x.scale(&rat(1, 2)).scale(&r(2)), x);
        assert!(x.sub(&x).is_zero());
    }

    #[test]
    fn constant_recognition() {
        let c = Polynomial::constant(rat(7, 3));
        assert!(c.is_constant());
        assert_eq!(c.as_constant(), Some(rat(7, 3)));
        assert!(Polynomial::var(0).as_constant().is_none());
        assert_eq!(Polynomial::zero().as_constant(), Some(r(0)));
    }

    #[test]
    fn degree_queries() {
        // 5 x0^3 x1 + x1^2
        let p = Polynomial::from_terms(vec![
            (r(5), Monomial::from_powers(&[(0, 3), (1, 1)])),
            (r(1), Monomial::from_powers(&[(1, 2)])),
        ]);
        assert_eq!(p.total_degree(), 4);
        assert_eq!(p.degree_of(0), 3);
        assert_eq!(p.degree_of(1), 2);
        assert_eq!(p.degree_of(2), 0);
        assert!(!p.is_linear());
        assert_eq!(p.vars(), vec![0, 1]);
    }
}
