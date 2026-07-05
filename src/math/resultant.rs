//! Resultants and discriminants of multivariate polynomials with respect to one
//! variable — the projection primitives for Cylindrical Algebraic Decomposition.
//!
//! Ported from the resultant/discriminant machinery in Z3's `math/polynomial`
//! (Z3 4.17.0, MIT). Viewing `p, q ∈ ℚ[x₁,…,xₙ]` as univariate polynomials in a
//! chosen variable `v` whose coefficients are polynomials in the remaining
//! variables, the **resultant** `Res_v(p, q)` is the determinant of their
//! Sylvester matrix — a polynomial in the remaining variables that vanishes
//! exactly where `p` and `q` share a common root in `v` (for those parameter
//! values). The **discriminant** `disc_v(p) = Res_v(p, ∂p/∂v)` vanishes where `p`
//! has a repeated root in `v`. These are the polynomials CAD's projection adds to
//! keep the decomposition sign-invariant.
//!
//! The determinant is computed by cofactor (Laplace) expansion over the
//! polynomial coefficient ring — no division needed, valid over any commutative
//! ring — which is fine for the small, low-degree matrices CAD produces (callers
//! cap the degree and fall back to a sound `unknown` otherwise).

use alloc::vec::Vec;

use crate::math::polynomial::{Polynomial, Var};

/// `Res_v(p, q)`: the resultant of `p` and `q` with respect to variable `v`, a
/// polynomial in the remaining variables. `Res(p, q) = 0` iff `p` and `q` have a
/// common root in `v` or both leading coefficients (in `v`) vanish.
pub fn resultant(p: &Polynomial, q: &Polynomial, v: Var) -> Polynomial {
    if p.is_zero() || q.is_zero() {
        return Polynomial::zero();
    }
    let m = p.degree_of(v) as usize;
    let n = q.degree_of(v) as usize;
    // Degenerate cases: a constant (in v) c has Res(c, q) = c^n and Res(p, c)=c^m.
    if m == 0 {
        return p.coeff_of_var(v, 0).pow(n as u32);
    }
    if n == 0 {
        return q.coeff_of_var(v, 0).pow(m as u32);
    }
    // Sylvester matrix: (m+n)×(m+n). Coefficients highest-degree first.
    let p_co: Vec<Polynomial> = (0..=m).rev().map(|i| p.coeff_of_var(v, i as u32)).collect();
    let q_co: Vec<Polynomial> = (0..=n).rev().map(|j| q.coeff_of_var(v, j as u32)).collect();
    let size = m + n;
    let mut mat = alloc::vec![alloc::vec![Polynomial::zero(); size]; size];
    // First n rows are shifts of p's coefficients.
    for (i, row) in mat.iter_mut().take(n).enumerate() {
        for (k, c) in p_co.iter().enumerate() {
            row[i + k] = c.clone();
        }
    }
    // Next m rows are shifts of q's coefficients.
    for j in 0..m {
        for (k, c) in q_co.iter().enumerate() {
            mat[n + j][j + k] = c.clone();
        }
    }
    determinant(&mat)
}

/// `Res_v(p, ∂p/∂v)`: vanishes exactly where `p` has a repeated root in `v`. This
/// equals the classical discriminant up to a nonzero factor (`±1/lc_v(p)`), so it
/// has the same vanishing set — which is all CAD's projection requires.
pub fn discriminant(p: &Polynomial, v: Var) -> Polynomial {
    resultant(p, &p.deriv_var(v), v)
}

/// The determinant of a square matrix of polynomials, by the fraction-free
/// **Bareiss algorithm** — `O(n³)` ring operations with exact divisions
/// (valid over the integral domain of polynomials), rather than the `O(n!)`
/// cofactor expansion, which is essential to keep resultants tractable.
fn determinant(mat: &[Vec<Polynomial>]) -> Polynomial {
    let n = mat.len();
    if n == 0 {
        return Polynomial::constant(1.into());
    }
    let mut m: Vec<Vec<Polynomial>> = mat.to_vec();
    let mut sign = 1i32;
    let mut prev = Polynomial::constant(1.into());
    for k in 0..n - 1 {
        // Pivot: if the diagonal entry is zero, swap in a nonzero row below.
        if m[k][k].is_zero() {
            match (k + 1..n).find(|&i| !m[i][k].is_zero()) {
                Some(piv) => {
                    m.swap(k, piv);
                    sign = -sign;
                }
                None => return Polynomial::zero(), // singular column ⇒ det 0
            }
        }
        let pivot = m[k][k].clone();
        for i in (k + 1)..n {
            for j in (k + 1)..n {
                let num = m[i][j].mul(&pivot).sub(&m[i][k].mul(&m[k][j]));
                m[i][j] = if prev.as_constant() == Some(1.into()) {
                    num
                } else {
                    num.div_exact(&prev)
                };
            }
        }
        prev = pivot;
    }
    let det = m[n - 1][n - 1].clone();
    if sign < 0 { det.neg() } else { det }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::math::polynomial::Monomial;
    use puremp::Rational;

    fn r(n: i64) -> Rational {
        Rational::from_integer(n.into())
    }
    fn mono(pairs: &[(Var, u32)]) -> Monomial {
        Monomial::from_powers(pairs)
    }
    // Univariate in x0 from (coeff, degree) pairs.
    fn uni(cs: &[(i64, u32)]) -> Polynomial {
        Polynomial::from_terms(cs.iter().map(|&(c, d)| (r(c), mono(&[(0, d)]))).collect())
    }

    // Res(x-1, x-2) w.r.t x = (1-2) up to sign = ±1 (they share no root).
    #[test]
    fn resultant_coprime_linear_nonzero() {
        let a = uni(&[(-1, 0), (1, 1)]); // x - 1
        let b = uni(&[(-2, 0), (1, 1)]); // x - 2
        let res = resultant(&a, &b, 0);
        assert!(res.as_constant().is_some());
        assert!(!res.as_constant().unwrap().is_zero()); // no common root
    }

    // Res(x-1, x^2-1) w.r.t x = 0 (they share the root x=1).
    #[test]
    fn resultant_common_root_is_zero() {
        let a = uni(&[(-1, 0), (1, 1)]); // x - 1
        let b = uni(&[(-1, 0), (0, 1), (1, 2)]); // x^2 - 1
        let res = resultant(&a, &b, 0);
        assert_eq!(res.as_constant(), Some(r(0)));
    }

    // Discriminant of x^2 + b x + c (in x) = b^2 - 4c  (as a polynomial in b,c).
    #[test]
    fn discriminant_of_quadratic() {
        // variables: x=0, b=1, c=2 ; p = x^2 + b*x + c
        let p = Polynomial::from_terms(alloc::vec![
            (r(1), mono(&[(0, 2)])),
            (r(1), mono(&[(0, 1), (1, 1)])),
            (r(1), mono(&[(2, 1)])),
        ]);
        let disc = discriminant(&p, 0);
        // The classical discriminant is b^2 - 4c; Res(p, p') equals it up to a
        // nonzero factor (here −1), so match up to sign.
        let expect = Polynomial::from_terms(alloc::vec![
            (r(1), mono(&[(1, 2)])),
            (r(-4), mono(&[(2, 1)])),
        ]);
        assert!(disc == expect || disc == expect.neg(), "got {disc:?}");
    }

    // Res of two bivariate polynomials eliminating y gives a polynomial in x:
    // Res_y(y - x, y^2 - 2) = x^2 - 2  (substituting y = x into y^2 - 2).
    #[test]
    fn resultant_eliminates_variable() {
        // x = 0, y = 1
        let a = Polynomial::from_terms(alloc::vec![
            (r(1), mono(&[(1, 1)])),  // y
            (r(-1), mono(&[(0, 1)])), // -x
        ]);
        let b = Polynomial::from_terms(alloc::vec![
            (r(1), mono(&[(1, 2)])), // y^2
            (r(-2), Monomial::one()),
        ]);
        let res = resultant(&a, &b, 1); // eliminate y
        // x^2 - 2 (up to sign).
        let expect = Polynomial::from_terms(alloc::vec![
            (r(1), mono(&[(0, 2)])),
            (r(-2), Monomial::one()),
        ]);
        assert!(res == expect || res == expect.neg(), "got {res:?}");
    }
}
