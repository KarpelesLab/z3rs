//! Multivariate polynomial GCD and (partial) factorization over ℚ.
//!
//! Ported in spirit from `z3/src/math/polynomial/polynomial.cpp` (`gcd`,
//! `content`, `pp`, `factor_core`, `factor_sqf_pp`; MIT). The GCD is the
//! recursive primitive-PRS algorithm: split off the content in the main
//! variable, run pseudo-remainders on the primitive parts. Factorization is
//! z3's `factor_core`: content in the least-degree variable (factored
//! recursively), square-free decomposition (Yun), then each square-free part
//! is split further when univariate (Berlekamp–Zassenhaus via `puremp`) or
//! quadratic with a perfect-square discriminant; other parts are kept whole
//! (z3's multivariate Hensel lifting is not ported). Every factor is
//! normalized: primitive integer coefficients, positive leading coefficient.
//!
//! The factors are only used for their zero sets (projection in nlsat), so a
//! coarser factorization is always sound, merely less effective.

use alloc::vec::Vec;

use puremp::{Int, Rational};

use crate::math::polynomial::{Monomial, Polynomial, Var};

/// `p` scaled by a nonzero rational to primitive integer coefficients with a
/// positive leading (first canonical) coefficient; zero stays zero.
pub fn normalize(p: &Polynomial) -> Polynomial {
    if p.is_zero() {
        return p.clone();
    }
    let mut den = Int::from(1);
    for (c, _) in p.terms() {
        let d = c.denominator();
        let g = den.gcd(d);
        den = den.mul(d).div_exact(&g);
    }
    let mut num = Int::from(0);
    for (c, _) in p.terms() {
        let n = c
            .mul(&Rational::from_integer(den.clone()))
            .numerator()
            .clone();
        num = num.gcd(&n);
    }
    let mut scale = Rational::new(den, num.abs());
    if p.terms()[0].0.is_negative() {
        scale = scale.neg();
    }
    p.scale(&scale)
}

fn max_var(p: &Polynomial) -> Option<Var> {
    p.terms().iter().flat_map(|(_, m)| m.vars()).max()
}

/// The leading coefficient of `p` in `x`.
fn lc(p: &Polynomial, x: Var) -> Polynomial {
    p.coeff_of_var(x, p.degree_of(x))
}

fn xpow(x: Var, j: u32) -> Polynomial {
    Polynomial::from_terms(alloc::vec![(
        Rational::from_integer(1.into()),
        Monomial::from_powers(&[(x, j)])
    )])
}

/// The pseudo-remainder of `p` by `q` in `x` (`deg_x q ≥ 1`), up to a nonzero
/// factor.
fn prem(p: &Polynomial, q: &Polynomial, x: Var) -> Polynomial {
    let db = q.degree_of(x);
    let lb = lc(q, x);
    let rb = q.sub(&lb.mul(&xpow(x, db)));
    let mut r = p.clone();
    loop {
        let dr = r.degree_of(x);
        if r.is_zero() || db > dr {
            return r;
        }
        let lr = r.coeff_of_var(x, dr);
        let red = r.sub(&lr.mul(&xpow(x, dr)));
        r = lb.mul(&red).sub(&lr.mul(&xpow(x, dr - db)).mul(&rb));
    }
}

/// Work budget for one top-level call (roughly, term operations).
struct Budget(u64);

impl Budget {
    fn spend(&mut self) -> Option<()> {
        self.charge(1)
    }
    fn charge(&mut self, n: u64) -> Option<()> {
        self.0 = self.0.checked_sub(n)?;
        Some(())
    }
}

/// The size of `p`'s largest coefficient, in 64-bit limbs.
fn limbs(p: &Polynomial) -> u64 {
    let bits = p
        .terms()
        .iter()
        .map(|(c, _)| c.numerator().bit_len() + c.denominator().bit_len())
        .max()
        .unwrap_or(0);
    u64::from(bits / 64 + 1)
}

/// `p` as a dense univariate polynomial in `x` (every other variable absent).
fn to_upoly(p: &Polynomial, x: Var) -> crate::math::upoly::UPoly {
    let d = p.degree_of(x);
    crate::math::upoly::UPoly::from_coeffs(
        (0..=d)
            .map(|k| {
                p.coeff_of_var(x, k)
                    .as_constant()
                    .unwrap_or_else(|| Rational::from_integer(0.into()))
            })
            .collect(),
    )
}

fn from_upoly(u: &crate::math::upoly::UPoly, x: Var) -> Polynomial {
    Polynomial::from_terms(
        u.coeffs()
            .iter()
            .enumerate()
            .filter(|(_, c)| !c.is_zero())
            .map(|(k, c)| (c.clone(), Monomial::from_powers(&[(x, k as u32)])))
            .collect(),
    )
}

/// The content of `p` in `x`: the GCD of its coefficients as a polynomial in
/// `x` (normalized).
fn content(p: &Polynomial, x: Var, b: &mut Budget) -> Option<Polynomial> {
    let d = p.degree_of(x);
    let mut g = Polynomial::zero();
    for k in (0..=d).rev() {
        let c = p.coeff_of_var(x, k);
        if c.is_zero() {
            continue;
        }
        g = gcd_core(&g, &c, b)?;
        if g.is_constant() {
            return Some(Polynomial::constant(Rational::from_integer(1.into())));
        }
    }
    Some(g)
}

fn gcd_core(a: &Polynomial, b: &Polynomial, bud: &mut Budget) -> Option<Polynomial> {
    bud.spend()?;
    if a.is_zero() {
        return Some(normalize(b));
    }
    if b.is_zero() {
        return Some(normalize(a));
    }
    let one = || Polynomial::constant(Rational::from_integer(1.into()));
    if a.is_constant() || b.is_constant() {
        return Some(one());
    }
    let x = max_var(a).max(max_var(b)).expect("nonconstant");
    let (da, db) = (a.degree_of(x), b.degree_of(x));
    let univ = |p: &Polynomial| p.terms().iter().all(|(_, m)| m.vars().all(|v| v == x));
    if univ(a) && univ(b) {
        bud.charge(u64::from(da + 1) * u64::from(db + 1) * (limbs(a) + limbs(b)))?;
        return Some(normalize(&from_upoly(
            &to_upoly(a, x).gcd(&to_upoly(b, x)),
            x,
        )));
    }
    if da == 0 {
        let cb = content(b, x, bud)?;
        return gcd_core(a, &cb, bud);
    }
    if db == 0 {
        let ca = content(a, x, bud)?;
        return gcd_core(&ca, b, bud);
    }
    let ca = content(a, x, bud)?;
    let cb = content(b, x, bud)?;
    let c = gcd_core(&ca, &cb, bud)?;
    let pa = a.div_exact(&ca)?;
    let pb = b.div_exact(&cb)?;
    let (mut r0, mut r1) = if da >= db { (pa, pb) } else { (pb, pa) };
    loop {
        bud.charge(
            (r0.num_terms() * r1.num_terms()) as u64
                * u64::from(r0.degree_of(x) + 1)
                * (limbs(&r0) + limbs(&r1)),
        )?;
        let r = prem(&r0, &r1, x);
        if r.is_zero() {
            break;
        }
        if r.degree_of(x) == 0 {
            return Some(c);
        }
        let cr = content(&r, x, bud)?;
        r0 = r1;
        r1 = r.div_exact(&cr)?;
    }
    let cr = content(&r1, x, bud)?;
    let g = r1.div_exact(&cr)?;
    Some(normalize(&c.mul(&g)))
}

/// The GCD of `a` and `b` (normalized), `None` past the work budget.
pub fn gcd(a: &Polynomial, b: &Polynomial) -> Option<Polynomial> {
    gcd_core(a, b, &mut Budget(200_000))
}

/// The variable of `p` of least positive degree (z3's `get_min_degree_var`).
fn min_degree_var(p: &Polynomial) -> Var {
    let mut best: Option<(u32, Var)> = None;
    for v in p.vars() {
        let d = p.degree_of(v);
        if best.is_none_or(|(bd, _)| d < bd) {
            best = Some((d, v));
        }
    }
    best.expect("nonconstant").1
}

/// Push `f` (normalized) unless already present.
fn push_factor(out: &mut Vec<Polynomial>, f: &Polynomial) {
    let f = normalize(f);
    if !f.is_constant() && !out.contains(&f) {
        out.push(f);
    }
}

/// The square-free primitive `p` (degree ≥ 1 in `x`) split further where
/// cheap (`factor_sqf_pp`). A content in another variable (a factor free
/// of it) is split off first.
fn factor_sqf_pp(
    p: &Polynomial,
    x: Var,
    out: &mut Vec<Polynomial>,
    bud: &mut Budget,
) -> Option<()> {
    let vars = p.vars();
    for &y in &vars {
        if y == x {
            continue;
        }
        let c = content(p, y, bud)?;
        if !c.is_constant() {
            factor_core(&c, out, bud)?;
            return factor_core(&p.div_exact(&c)?, out, bud);
        }
    }
    // Univariate factoring (Berlekamp–Zassenhaus) only while it is cheap.
    if vars.len() == 1 && p.degree_of(x) >= 2 && p.degree_of(x) <= 24 && limbs(p) <= 4 {
        let d = p.degree_of(x);
        let coeffs: Vec<Rational> = (0..=d)
            .map(|k| {
                p.coeff_of_var(x, k)
                    .as_constant()
                    .unwrap_or_else(|| Rational::from_integer(0.into()))
            })
            .collect();
        let fs = puremp::Poly::new(coeffs).factor();
        for (f, _) in fs {
            let terms = f
                .coeffs()
                .iter()
                .enumerate()
                .filter(|(_, c)| !c.is_zero())
                .map(|(k, c)| (c.clone(), Monomial::from_powers(&[(x, k as u32)])))
                .collect();
            push_factor(out, &Polynomial::from_terms(terms));
        }
        return Some(());
    }
    if p.degree_of(x) == 2
        && let Some((f1, f2)) = split_quadratic(p, x)
    {
        push_factor(out, &f1);
        push_factor(out, &f2);
        return Some(());
    }
    push_factor(out, p);
    Some(())
}

/// `a·x² + b·x + c = (2ax + b − s)(2ax + b + s) / 4a` when the discriminant
/// `b² − 4ac` is a perfect square `s²` (`factor_2_sqf_pp`); the factors'
/// contents in `x` are dropped.
fn split_quadratic(p: &Polynomial, x: Var) -> Option<(Polynomial, Polynomial)> {
    let a = p.coeff_of_var(x, 2);
    let b = p.coeff_of_var(x, 1);
    let c = p.coeff_of_var(x, 0);
    let four = Rational::from_integer(4.into());
    let disc = b.mul(&b).sub(&a.mul(&c).scale(&four));
    let s = sqrt(&disc)?;
    let two_ax_b = a
        .mul(&Polynomial::var(x))
        .scale(&Rational::from_integer(2.into()))
        .add(&b);
    let mut bud = Budget(50_000);
    let f1 = two_ax_b.sub(&s);
    let f2 = two_ax_b.add(&s);
    let c1 = content(&f1, x, &mut bud)?;
    let c2 = content(&f2, x, &mut bud)?;
    Some((f1.div_exact(&c1)?, f2.div_exact(&c2)?))
}

/// The polynomial square root of `p`, when `p` is a perfect square (by
/// recursion on the main variable: the root's coefficients come from the
/// leading ones downwards).
pub fn sqrt(p: &Polynomial) -> Option<Polynomial> {
    if p.is_zero() {
        return Some(Polynomial::zero());
    }
    if let Some(c) = p.as_constant() {
        if c.is_negative() {
            return None;
        }
        let n = c.numerator().sqrt_exact()?;
        let d = c.denominator().sqrt_exact()?;
        return Some(Polynomial::constant(Rational::new(n, d)));
    }
    let x = max_var(p).expect("nonconstant");
    let d = p.degree_of(x);
    if d % 2 == 1 {
        return None;
    }
    let m = d / 2;
    // s = Σ s_k x^k, s_m = √lc; then s_k from the coefficient of x^(m+k).
    let sm = sqrt(&p.coeff_of_var(x, d))?;
    if sm.is_zero() {
        return None;
    }
    let mut s = sm.mul(&xpow(x, m));
    let two_sm = sm.scale(&Rational::from_integer(2.into()));
    for k in (0..m).rev() {
        // The x^(m+k) coefficient of p − s² is 2·s_m·s_k (+ known terms).
        let r = p.sub(&s.mul(&s));
        let rk = r.coeff_of_var(x, m + k);
        let sk = rk.div_exact(&two_sm)?;
        s = s.add(&sk.mul(&xpow(x, k)));
    }
    (s.mul(&s) == *p).then_some(s)
}

/// The distinct non-constant factors of `p` (normalized), from a partial
/// factorization (`factor_core`); `[p]` (normalized) past the work budget.
pub fn factors(p: &Polynomial) -> Vec<Polynomial> {
    let mut out = Vec::new();
    if p.is_constant() {
        return out;
    }
    if factor_core(p, &mut out, &mut Budget(200_000)).is_none() {
        out.clear();
        push_factor(&mut out, p);
    }
    out
}

fn factor_core(p: &Polynomial, out: &mut Vec<Polynomial>, bud: &mut Budget) -> Option<()> {
    if p.is_constant() {
        return Some(());
    }
    let x = min_degree_var(p);
    let c = content(p, x, bud)?;
    factor_core(&c, out, bud)?;
    let pp = p.div_exact(&c)?;
    // Yun's square-free decomposition of the primitive part in `x`.
    let dp = pp.deriv_var(x);
    let b0 = gcd_core(&pp, &dp, bud)?;
    if b0.is_constant() {
        factor_sqf_pp(&pp, x, out, bud)?;
        return Some(());
    }
    let mut a = pp.div_exact(&b0)?;
    let mut b = b0;
    while !a.is_constant() {
        bud.spend()?;
        let d = gcd_core(&a, &b, bud)?;
        let cj = a.div_exact(&d)?;
        if !cj.is_constant() {
            factor_sqf_pp(&cj, x, out, bud)?;
        }
        b = b.div_exact(&d)?;
        a = d;
    }
    // What is left in `b` is free of `x` only when the decomposition is
    // complete; anything else is a factor too.
    if !b.is_constant() {
        factor_core(&b, out, bud)?;
    }
    Some(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn r(n: i64) -> Rational {
        Rational::from_integer(n.into())
    }
    fn poly(terms: &[(i64, &[(Var, u32)])]) -> Polynomial {
        Polynomial::from_terms(
            terms
                .iter()
                .map(|&(c, m)| (r(c), Monomial::from_powers(m)))
                .collect(),
        )
    }

    #[test]
    fn gcd_of_products() {
        // (x + y)(x − 2y + 1) and (x + y)(y² + 3)
        let f = poly(&[(1, &[(0, 1)]), (1, &[(1, 1)])]);
        let g = poly(&[(1, &[(0, 1)]), (-2, &[(1, 1)]), (1, &[])]);
        let h = poly(&[(1, &[(1, 2)]), (3, &[])]);
        let d = gcd(&f.mul(&g), &f.mul(&h)).unwrap();
        assert_eq!(d, normalize(&f));
    }

    #[test]
    fn factors_cover_and_split() {
        // x²y² − 1 = (xy − 1)(xy + 1), times (x − 1)² · 3
        let a = poly(&[(1, &[(0, 2), (1, 2)]), (-1, &[])]);
        let b = poly(&[(1, &[(0, 1)]), (-1, &[])]);
        let p = a.mul(&b).mul(&b).scale(&r(3));
        let fs = factors(&p);
        assert_eq!(fs.len(), 3, "{fs:?}");
        let prod = fs
            .iter()
            .fold(Polynomial::constant(r(1)), |acc, f| acc.mul(f));
        // Same zero set: the product of the distinct factors divides p and
        // p divides a power of it.
        assert!(p.div_exact(&prod).is_some());
    }

    /// Random products: every factor divides `p`, and the product of the
    /// factors (with enough multiplicity) is divisible by `p`'s square-free
    /// part — the zero sets agree.
    #[test]
    fn random_factorizations() {
        let mut seed = 5u64;
        let mut next = |n: u64| {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (seed >> 33) % n
        };
        for _ in 0..150 {
            let mut p = Polynomial::constant(r(1));
            for _ in 0..1 + next(3) {
                let mut terms = Vec::new();
                for _ in 0..1 + next(3) {
                    let mut pw = Vec::new();
                    for v in 0..3u32 {
                        pw.push((v, next(3) as u32));
                    }
                    terms.push((r(next(7) as i64 - 3), Monomial::from_powers(&pw)));
                }
                let f = Polynomial::from_terms(terms);
                if !f.is_zero() {
                    p = p.mul(&f);
                }
            }
            if p.is_constant() {
                continue;
            }
            let fs = factors(&p);
            let mut prod = Polynomial::constant(r(1));
            for f in &fs {
                assert!(p.div_exact(f).is_some(), "{f:?} ∤ {p:?}");
                prod = prod.mul(f);
            }
            assert!(p.div_exact(&prod).is_some(), "{p:?} {fs:?}");
            // Dividing every factor out as often as possible leaves a constant.
            let mut q = p.clone();
            for f in &fs {
                while let Some(d) = q.div_exact(f) {
                    q = d;
                }
            }
            assert!(q.is_constant(), "{p:?} {fs:?} left {q:?}");
        }
    }

    #[test]
    fn quadratic_split() {
        // x² − y² = (x − y)(x + y)
        let p = poly(&[(1, &[(0, 2)]), (-1, &[(1, 2)])]);
        assert_eq!(factors(&p).len(), 2);
    }
}
