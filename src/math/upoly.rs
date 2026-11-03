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

use puremp::{Int, Rational};

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
        if self.is_zero() || other.is_zero() || self.degree() == 0 || other.degree() == 0 {
            let mut a = self.clone();
            let mut b = other.clone();
            while !b.is_zero() {
                let r = a.rem(&b);
                a = b;
                b = r;
            }
            return a.monic();
        }
        // Over the integers by the subresultant PRS (no rational arithmetic).
        let g = gcd_int(&int_coeffs(self), &int_coeffs(other));
        UPoly::from_coeffs(g.into_iter().map(Rational::from_integer).collect()).monic()
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

/// Exact rational roots and isolating intervals of the other real roots.
pub type RootIsolation = (Vec<Rational>, Vec<(Rational, Rational)>);

/// Integer coefficients proportional to `p`'s by a positive factor.
pub fn int_coeffs(p: &UPoly) -> Vec<Int> {
    let mut l = Int::from(1);
    for c in &p.coeffs {
        let d = c.denominator();
        let g = l.gcd(d);
        l = l.mul(d).div_exact(&g);
    }
    let lr = Rational::from_integer(l);
    p.coeffs
        .iter()
        .map(|c| c.mul(&lr).numerator().clone())
        .collect()
}

/// The GCD of the integer coefficients (0 for none).
fn int_content(a: &[Int]) -> Int {
    let mut g = Int::from(0);
    for c in a {
        g = g.gcd(c);
        if g.is_one() {
            break;
        }
    }
    g
}

/// `a` divided by its content.
fn int_pp(a: &[Int]) -> Vec<Int> {
    let c = int_content(a);
    if c.is_zero() || c.is_one() {
        return a.to_vec();
    }
    a.iter().map(|x| x.div_exact(&c)).collect()
}

/// The pseudo-remainder `lc(b)^(deg a − deg b + 1) · a mod b` of dense
/// integer polynomials (ascending, no trailing zeros, `deg a ≥ deg b`).
fn int_prem(a: &[Int], b: &[Int]) -> Vec<Int> {
    let db = b.len() - 1;
    let lb = &b[db];
    let mut r = a.to_vec();
    let mut steps = a.len() - b.len() + 1;
    while r.len() > db && !r.is_empty() {
        let dr = r.len() - 1;
        let lr = r[dr].clone();
        for c in r.iter_mut() {
            *c = c.mul(lb);
        }
        let shift = dr - db;
        for (i, bc) in b.iter().enumerate() {
            let t = r[shift + i].sub(&lr.mul(bc));
            r[shift + i] = t;
        }
        steps -= 1;
        while r.last().is_some_and(|c| c.is_zero()) {
            r.pop();
        }
    }
    if steps > 0 {
        let f = lb.pow(steps as u64);
        for c in r.iter_mut() {
            *c = c.mul(&f);
        }
    }
    r
}

/// The GCD (up to a constant) of nonconstant integer polynomials, by the
/// subresultant PRS (Knuth, TAOCP 4.6.1, Algorithm C).
fn gcd_int(a: &[Int], b: &[Int]) -> Vec<Int> {
    let (a, b) = if a.len() >= b.len() { (a, b) } else { (b, a) };
    let d = int_content(a).gcd(&int_content(b));
    let mut u = int_pp(a);
    let mut v = int_pp(b);
    let mut g = Int::from(1);
    let mut h = Int::from(1);
    loop {
        let delta = (u.len() - v.len()) as u64;
        let r = int_prem(&u, &v);
        if r.is_empty() {
            break;
        }
        if r.len() == 1 {
            return alloc::vec![d];
        }
        u = v;
        let div = g.mul(&h.pow(delta));
        v = r.iter().map(|c| c.div_exact(&div)).collect();
        g = u.last().expect("nonzero").clone();
        // h ← g^δ / h^(δ−1)
        h = if delta == 0 {
            h
        } else {
            g.pow(delta).div_exact(&h.pow(delta - 1))
        };
    }
    int_pp(&v).into_iter().map(|c| c.mul(&d)).collect()
}

/// Sign variations of a coefficient sequence (zeros skipped).
fn sign_variations(cs: &[Int]) -> usize {
    let mut last = 0;
    let mut n = 0;
    for c in cs {
        let s = c.signum();
        if s == 0 {
            continue;
        }
        if last != 0 && s != last {
            n += 1;
        }
        last = s;
    }
    n
}

/// `q(x) ↦ q(x + 1)` in place (ascending coefficients).
fn taylor_shift_1(a: &mut [Int]) {
    let n = a.len();
    for i in 0..n.saturating_sub(1) {
        for j in (i..n - 1).rev() {
            let t = a[j].add(&a[j + 1]);
            a[j] = t;
        }
    }
}

/// Descartes' bound on the roots of `q` in `(0, 1)`: the sign variations of
/// `(x + 1)ⁿ q(1 / (x + 1))`.
fn descartes_01(q: &[Int]) -> usize {
    let mut r: Vec<Int> = q.iter().rev().cloned().collect();
    taylor_shift_1(&mut r);
    sign_variations(&r)
}

/// The real roots of the squarefree `p`, by Descartes' rule of signs with
/// bisection (the Vincent–Collins–Akritas method z3's `upolynomial` uses), in
/// exact integer arithmetic: the rational roots met at bisection points (and
/// zero) exactly, and an isolating open interval for each other root, whose
/// endpoints are roots of `p` only when listed among the exact ones. `None`
/// past the iteration guard.
pub fn isolate_roots_vca(p: &UPoly) -> Option<RootIsolation> {
    let mut exact = Vec::new();
    let mut ivs = Vec::new();
    if p.degree() == 0 {
        return Some((exact, ivs));
    }
    let mut cs = int_coeffs(p);
    if cs[0].is_zero() {
        exact.push(zero());
        cs.remove(0);
    }
    // 2^k bounds every root's magnitude strictly (Cauchy).
    let lead = cs.last().expect("nonconstant").abs();
    let mut maxc = Int::from(0);
    for c in &cs[..cs.len() - 1] {
        let a = c.abs();
        if a > maxc {
            maxc = a;
        }
    }
    let bound = maxc.div_floor(&lead).add(&Int::from(2));
    let k = bound.bit_len() as u64;
    for negative in [false, true] {
        if cs.len() <= 1 {
            break;
        }
        // q(x) = P(±2^k x): its roots in (0, 1) are P's in (0, ±2^k).
        let q: Vec<Int> = cs
            .iter()
            .enumerate()
            .map(|(i, c)| {
                let c = c.mul_2k(k * i as u64);
                if negative && i % 2 == 1 { c.neg() } else { c }
            })
            .collect();
        // Nodes: (q, c, j) for the interval (c / 2^j, (c + 1) / 2^j) · 2^k.
        let mut stack: Vec<(Vec<Int>, Int, u64)> = alloc::vec![(q, Int::from(0), 0)];
        let mut guard = 0usize;
        let to_rat = |c: &Int, j: u64| -> Rational {
            let v = if j >= k {
                Rational::new(c.clone(), Int::from(1).mul_2k(j - k))
            } else {
                Rational::from_integer(c.mul_2k(k - j))
            };
            if negative { v.neg() } else { v }
        };
        while let Some((q, c, j)) = stack.pop() {
            guard += 1;
            if guard > 100_000 || j > 4000 {
                return None;
            }
            if q.len() <= 1 {
                continue;
            }
            let v = descartes_01(&q);
            if v == 0 {
                continue;
            }
            if v == 1 {
                let lo = to_rat(&c, j);
                let hi = to_rat(&c.add(&Int::from(1)), j);
                ivs.push(if negative { (hi, lo) } else { (lo, hi) });
                continue;
            }
            // Halves: q1(x) = 2^n q(x/2) on (0, 1/2), q2(x) = q1(x + 1).
            let n = q.len() - 1;
            let mut q1: Vec<Int> = q
                .iter()
                .enumerate()
                .map(|(i, a)| a.mul_2k((n - i) as u64))
                .collect();
            let mut q2 = q1.clone();
            taylor_shift_1(&mut q2);
            let c2 = c.mul_2k(1);
            if q2[0].is_zero() {
                // The midpoint is a root: record it, divide it out of both.
                exact.push(to_rat(&c2.add(&Int::from(1)), j + 1));
                q2.remove(0);
                // q1 = (x − 1)·s: s_{i−1} = −(a_i... ) by synthetic division.
                let mut s = alloc::vec![Int::from(0); n];
                let mut carry = Int::from(0);
                for i in (1..=n).rev() {
                    carry = carry.add(&q1[i]);
                    s[i - 1] = carry.clone();
                }
                debug_assert!(carry.add(&q1[0]).is_zero());
                q1 = s;
            }
            stack.push((q2, c2.add(&Int::from(1)), j + 1));
            stack.push((q1, c2, j + 1));
        }
    }
    exact.sort();
    ivs.sort_by(|a, b| a.0.cmp(&b.0));
    Some((exact, ivs))
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

    /// The integer subresultant GCD equals the monic rational Euclidean one.
    #[test]
    fn int_gcd_matches_euclid() {
        let mut seed = 3u64;
        let mut next = |n: u64| {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (seed >> 33) % n
        };
        let rnd = |next: &mut dyn FnMut(u64) -> u64| {
            let deg = next(5) as usize;
            UPoly::from_coeffs((0..=deg).map(|_| r(next(9) as i64 - 4)).collect())
        };
        for _ in 0..300 {
            let c = rnd(&mut next);
            let a = rnd(&mut next).mul(&c);
            let b = rnd(&mut next).mul(&c);
            let fast = a.gcd(&b);
            let mut x = a.clone();
            let mut y = b.clone();
            while !y.is_zero() {
                let t = x.rem(&y);
                x = y;
                y = t;
            }
            assert_eq!(fast, x.monic(), "{a:?} {b:?}");
        }
    }

    /// The Descartes isolation agrees with the Sturm counts: every interval
    /// holds exactly one root and has non-root endpoints after dividing the
    /// exact roots out, and the totals match.
    #[test]
    fn vca_matches_sturm() {
        let mut seed = 11u64;
        let mut next = |n: u64| {
            seed = seed
                .wrapping_mul(6364136223846793005)
                .wrapping_add(1442695040888963407);
            (seed >> 33) % n
        };
        for _ in 0..400 {
            let deg = 1 + next(8) as usize;
            let mut cs: Vec<Rational> = (0..=deg).map(|_| r(next(11) as i64 - 5)).collect();
            if next(3) == 0 {
                cs[0] = r(0);
            }
            let mut poly = UPoly::from_coeffs(cs);
            // Rational roots: multiply by (2x − 1)(x + 3) sometimes.
            if next(2) == 0 {
                poly = poly.mul(&p(&[-1, 2])).mul(&p(&[3, 1]));
            }
            if poly.degree() == 0 {
                continue;
            }
            let sf = poly.squarefree();
            let (exact, ivs) = isolate_roots_vca(&sf).expect("terminates");
            let chain = sturm_chain(&sf);
            let m = sf.root_bound();
            let total = root_count(&chain, &m.neg(), &m);
            assert_eq!(total as usize, exact.len() + ivs.len(), "{sf:?}");
            for e in &exact {
                assert_eq!(sf.sign_at(e), 0);
            }
            let mut def = sf.clone();
            for e in &exact {
                def = def.div_exact(&UPoly::from_coeffs(vec![e.neg(), one()]));
            }
            for (lo, hi) in &ivs {
                assert!(lo < hi);
                assert_ne!(def.sign_at(lo), 0, "{sf:?} {lo:?}");
                assert_ne!(def.sign_at(hi), 0);
                let at_hi = i64::from(sf.sign_at(hi) == 0);
                assert_eq!(
                    root_count(&chain, lo, hi) - at_hi,
                    1,
                    "{sf:?} ({lo:?}, {hi:?})"
                );
            }
        }
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
        assert!(
            roots
                .iter()
                .any(|(a, b)| a < &r(2) && b > &r(1) && a > &r(0))
        );
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
