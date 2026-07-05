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
pub fn resultant(p: &Polynomial, q: &Polynomial, v: Var) -> Option<Polynomial> {
    if p.is_zero() || q.is_zero() {
        return Some(Polynomial::zero());
    }
    let m = p.degree_of(v) as usize;
    let n = q.degree_of(v) as usize;
    // Degenerate cases: a constant (in v) c has Res(c, q) = c^n and Res(p, c)=c^m.
    if m == 0 {
        return Some(p.coeff_of_var(v, 0).pow(n as u32));
    }
    if n == 0 {
        return Some(q.coeff_of_var(v, 0).pow(m as u32));
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

/// Principal subresultant coefficients of `p` and `q` with respect to `v`:
/// `[s₀, s₁, …, s_k]` with `k = min(deg_v p, deg_v q)`. Each `sᵢ` is a polynomial
/// in the remaining variables — the leading (degree-`i`) coefficient of the `i`-th
/// subresultant of `p, q` — computed as a determinant of a submatrix of their
/// Sylvester matrix (via the fraction-free Bareiss determinant, exact over the
/// polynomial domain).
///
/// `s₀` equals the resultant `Res_v(p, q)` (up to sign). When the resultant
/// vanishes identically — `p` and `q` share a factor in `v`, the case McCallum's
/// projection cannot handle — the *first nonzero* `sᵢ` past `s₀` certifies the
/// degree of that common factor and delineates where it changes. Adding the whole
/// chain is what makes Collins' complete projection order/sign-invariant in the
/// degenerate cases (proportional or common-factor pairs) where the bare
/// resultant is `0` and carries no information.
///
/// Constant/scalar factors and overall sign are irrelevant: CAD uses these
/// polynomials only for their real zero sets to delineate cells.
pub fn principal_subresultant_coeffs(
    p: &Polynomial,
    q: &Polynomial,
    v: Var,
) -> Option<Vec<Polynomial>> {
    if p.is_zero() || q.is_zero() {
        return Some(Vec::new());
    }
    // Order so that deg_v P ≥ deg_v Q (subresultants are symmetric up to sign).
    let (p, q) = if p.degree_of(v) >= q.degree_of(v) {
        (p, q)
    } else {
        (q, p)
    };
    let m = p.degree_of(v) as usize;
    let n = q.degree_of(v) as usize;
    if n == 0 {
        // q is a constant c in v: the only subresultant coefficient is s₀ = Res = c^m.
        return Some(alloc::vec![q.coeff_of_var(v, 0).pow(m as u32)]);
    }
    // Sylvester matrix Syl(P,Q): n rows of P-shifts then m rows of Q-shifts, size m+n.
    // Column c (0-indexed) corresponds to the power v^{m+n-1-c}.
    let p_co: Vec<Polynomial> = (0..=m).rev().map(|i| p.coeff_of_var(v, i as u32)).collect(); // p_m..p_0
    let q_co: Vec<Polynomial> = (0..=n).rev().map(|j| q.coeff_of_var(v, j as u32)).collect(); // q_n..q_0
    let size = m + n;
    let mut syl = alloc::vec![alloc::vec![Polynomial::zero(); size]; size];
    for (r, row) in syl.iter_mut().take(n).enumerate() {
        for (k, c) in p_co.iter().enumerate() {
            row[r + k] = c.clone();
        }
    }
    for r in 0..m {
        for (k, c) in q_co.iter().enumerate() {
            syl[n + r][r + k] = c.clone();
        }
    }
    // For i = 0..=n: sᵢ = det of the submatrix using
    //   rows  = P-rows 0..(n-i-1) and Q-rows 0..(m-i-1)   [(m+n-2i) rows],
    //   cols  = 0..(size-2i-2) and column (size-1-i)      [the v^i column].
    // i=0 recovers the full Sylvester determinant = Res.
    let mut out = Vec::with_capacity(n + 1);
    for i in 0..=n {
        let dim = (m + n) - 2 * i; // = (n-i) + (m-i)
        if dim == 0 {
            out.push(Polynomial::constant(1.into()));
            continue;
        }
        let mut rows: Vec<usize> = Vec::with_capacity(dim);
        for r in 0..(n - i) {
            rows.push(r);
        }
        for r in 0..(m - i) {
            rows.push(n + r);
        }
        let mut cols: Vec<usize> = Vec::with_capacity(dim);
        for c in 0..(dim - 1) {
            cols.push(c);
        }
        cols.push(size - 1 - i);
        let sub: Vec<Vec<Polynomial>> = rows
            .iter()
            .map(|&ri| cols.iter().map(|&ci| syl[ri][ci].clone()).collect())
            .collect();
        out.push(determinant(&sub)?);
    }
    Some(out)
}

/// `Res_v(p, ∂p/∂v)`: vanishes exactly where `p` has a repeated root in `v`. This
/// equals the classical discriminant up to a nonzero factor (`±1/lc_v(p)`), so it
/// has the same vanishing set — which is all CAD's projection requires.
pub fn discriminant(p: &Polynomial, v: Var) -> Option<Polynomial> {
    resultant(p, &p.deriv_var(v), v)
}

/// The determinant of a square matrix of polynomials, by the fraction-free
/// **Bareiss algorithm** — `O(n³)` ring operations with exact divisions
/// (valid over the integral domain of polynomials), rather than the `O(n!)`
/// cofactor expansion, which is essential to keep resultants tractable.
fn determinant(mat: &[Vec<Polynomial>]) -> Option<Polynomial> {
    // Bareiss is fast but its exact-division invariant can break on a
    // degenerate/pivoted matrix; fall back to (division-free) cofactor expansion
    // for small matrices so the CAD stays *complete*, not just sound, there.
    bareiss_determinant(mat).or_else(|| cofactor_determinant(mat))
}

/// Laplace/cofactor expansion — division-free, hence always exact, but `O(n!)`;
/// used only as a fallback for the small matrices where Bareiss declines.
fn cofactor_determinant(mat: &[Vec<Polynomial>]) -> Option<Polynomial> {
    let n = mat.len();
    if n > 7 {
        return None; // too expensive; caller declines
    }
    if n == 0 {
        return Some(Polynomial::constant(1.into()));
    }
    if n == 1 {
        return Some(mat[0][0].clone());
    }
    let mut det = Polynomial::zero();
    for j in 0..n {
        if mat[0][j].is_zero() {
            continue;
        }
        let minor: Vec<Vec<Polynomial>> = mat[1..]
            .iter()
            .map(|row| {
                row.iter()
                    .enumerate()
                    .filter(|(c, _)| *c != j)
                    .map(|(_, p)| p.clone())
                    .collect()
            })
            .collect();
        let sub = cofactor_determinant(&minor)?;
        let term = mat[0][j].mul(&sub);
        det = if j % 2 == 0 {
            det.add(&term)
        } else {
            det.sub(&term)
        };
    }
    Some(det)
}

fn bareiss_determinant(mat: &[Vec<Polynomial>]) -> Option<Polynomial> {
    let n = mat.len();
    if n == 0 {
        return Some(Polynomial::constant(1.into()));
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
                None => return Some(Polynomial::zero()), // singular column ⇒ det 0
            }
        }
        let pivot = m[k][k].clone();
        for i in (k + 1)..n {
            for j in (k + 1)..n {
                let num = m[i][j].mul(&pivot).sub(&m[i][k].mul(&m[k][j]));
                m[i][j] = if prev.as_constant() == Some(1.into()) {
                    num
                } else {
                    // Exact division should hold; if a degenerate/pivoted matrix
                    // breaks the Bareiss invariant, decline rather than crash.
                    num.div_exact(&prev)?
                };
            }
        }
        prev = pivot;
    }
    let det = m[n - 1][n - 1].clone();
    Some(if sign < 0 { det.neg() } else { det })
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
        let res = resultant(&a, &b, 0).unwrap();
        assert!(res.as_constant().is_some());
        assert!(!res.as_constant().unwrap().is_zero()); // no common root
    }

    // Res(x-1, x^2-1) w.r.t x = 0 (they share the root x=1).
    #[test]
    fn resultant_common_root_is_zero() {
        let a = uni(&[(-1, 0), (1, 1)]); // x - 1
        let b = uni(&[(-1, 0), (0, 1), (1, 2)]); // x^2 - 1
        let res = resultant(&a, &b, 0).unwrap();
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
        let disc = discriminant(&p, 0).unwrap();
        // The classical discriminant is b^2 - 4c; Res(p, p') equals it up to a
        // nonzero factor (here −1), so match up to sign.
        let expect = Polynomial::from_terms(alloc::vec![
            (r(1), mono(&[(1, 2)])),
            (r(-4), mono(&[(2, 1)])),
        ]);
        assert!(disc == expect || disc == expect.neg(), "got {disc:?}");
    }

    // Subresultant chain, coprime pair: s0 = Res ≠ 0.
    #[test]
    fn psc_coprime() {
        let a = uni(&[(-1, 0), (1, 1)]); // x - 1
        let b = uni(&[(-2, 0), (1, 1)]); // x - 2
        let s = principal_subresultant_coeffs(&a, &b, 0).unwrap();
        // min degree = 1 ⇒ [s0, s1]; s0 = Res(x-1,x-2) = ±1 (nonzero).
        assert_eq!(s.len(), 2);
        assert!(!s[0].is_zero());
    }

    // Subresultant chain, gcd of degree 1: s0 = Res = 0 but s1 ≠ 0.
    #[test]
    fn psc_common_factor_degree1() {
        // P = (x-1)(x-2) = x^2 - 3x + 2 ; Q = (x-1)(x-3) = x^2 - 4x + 3.
        let p = uni(&[(2, 0), (-3, 1), (1, 2)]);
        let q = uni(&[(3, 0), (-4, 1), (1, 2)]);
        let s = principal_subresultant_coeffs(&p, &q, 0).unwrap();
        assert_eq!(s.len(), 3); // [s0, s1, s2]
        assert!(s[0].is_zero(), "s0 (resultant) should vanish: {:?}", s[0]);
        assert!(!s[1].is_zero(), "s1 should be nonzero for gcd deg 1");
    }

    // Proportional pair (same variety): the whole chain (below the top) vanishes.
    #[test]
    fn psc_proportional() {
        let p = uni(&[(-1, 0), (0, 1), (1, 2)]); // x^2 - 1
        let q = uni(&[(-2, 0), (0, 1), (2, 2)]); // 2x^2 - 2
        let s = principal_subresultant_coeffs(&p, &q, 0).unwrap();
        assert!(
            s[0].is_zero() && s[1].is_zero(),
            "proportional ⇒ s0=s1=0: {s:?}"
        );
    }

    // s0 equals the resultant (up to sign) for a bivariate elimination.
    #[test]
    fn psc_s0_is_resultant() {
        let a = Polynomial::from_terms(alloc::vec![
            (r(1), mono(&[(1, 1)])),  // y
            (r(-1), mono(&[(0, 1)])), // -x
        ]);
        let b = Polynomial::from_terms(alloc::vec![
            (r(1), mono(&[(1, 2)])), // y^2
            (r(-2), Monomial::one()),
        ]);
        let res = resultant(&a, &b, 1).unwrap();
        let s = principal_subresultant_coeffs(&a, &b, 1).unwrap();
        assert!(
            s[0] == res || s[0] == res.neg(),
            "s0 vs Res: {:?} {:?}",
            s[0],
            res
        );
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
        let res = resultant(&a, &b, 1).unwrap(); // eliminate y
        // x^2 - 2 (up to sign).
        let expect = Polynomial::from_terms(alloc::vec![
            (r(1), mono(&[(0, 2)])),
            (r(-2), Monomial::one()),
        ]);
        assert!(res == expect || res == expect.neg(), "got {res:?}");
    }
}
