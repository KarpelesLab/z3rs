//! Rigorous rational enclosures of transcendental functions at rational points.
//!
//! z3 5.3's nlsat evaluates `sin`/`exp`/… at rational points to decide atoms
//! over ground transcendental terms (`nlsat/transcendental_eval.cpp`, which uses
//! `double`s with a safety margin). This port computes exact rational Taylor
//! sums with explicit remainder bounds instead, rounding outward to dyadics of
//! [`PREC`] bits, so every result `(lo, hi)` satisfies `lo ≤ f(x) ≤ hi`.
//!
//! Each function returns `None` outside its (real) domain or for arguments too
//! large to reduce cheaply.

use puremp::{Int, Rational};

/// Dyadic precision (bits) of the rounded endpoints.
const PREC: i32 = 96;

/// Largest `|x|` accepted (argument reduction cost grows with it).
const MAX_ARG: i64 = 1 << 20;

/// A closed enclosure `[lo, hi]`.
pub type Enc = (Rational, Rational);

fn scale() -> Rational {
    Rational::power_of_two(PREC)
}

fn rdown(r: &Rational) -> Rational {
    Rational::new(r.mul(&scale()).floor(), Int::from(1)).div(&scale())
}

fn rup(r: &Rational) -> Rational {
    Rational::new(r.mul(&scale()).ceil(), Int::from(1)).div(&scale())
}

fn outward(lo: &Rational, hi: &Rational) -> Enc {
    (rdown(lo), rup(hi))
}

fn tiny() -> Rational {
    Rational::power_of_two(-(PREC + 8))
}

fn small_enough(x: &Rational) -> bool {
    x.abs() <= Rational::from(MAX_ARG)
}

fn mul_enc(a: &Enc, b: &Enc) -> Enc {
    let c = [a.0.mul(&b.0), a.0.mul(&b.1), a.1.mul(&b.0), a.1.mul(&b.1)];
    let lo = c.iter().min().unwrap().clone();
    let hi = c.iter().max().unwrap().clone();
    outward(&lo, &hi)
}

fn recip_enc(a: &Enc) -> Option<Enc> {
    if a.0.signum() * a.1.signum() <= 0 {
        return None;
    }
    Some(outward(&a.1.recip(), &a.0.recip()))
}

/// `Σ_k t_k` where `t_0 = first`, `t_{k+1} = t_k · ratio(k)`, summed until
/// `|t_k| < tiny`; the tail is bounded by `tail · |t_k|` for the first
/// neglected term.
fn series(first: Rational, ratio: impl Fn(u32) -> Rational, tail: Rational) -> Enc {
    let mut sum = Rational::from(0);
    let mut t = first;
    let mut k = 0u32;
    while t.abs() >= tiny() {
        sum = sum.add(&t);
        t = rdown_keep(&t.mul(&ratio(k)));
        k += 1;
    }
    let err = t.abs().mul(&tail).add(&tiny());
    outward(&sum.sub(&err), &sum.add(&err))
}

/// Terms are kept exact while small, rounding only once their size grows
/// (the rounding error is far below `tiny`, folded into the final slack).
fn rdown_keep(t: &Rational) -> Rational {
    if t.denominator().bit_len() > (PREC as u32) * 3 {
        // Round to nearest at 2·PREC bits: error ≤ 2^-(2·PREC), well under tiny.
        let s = Rational::power_of_two(2 * PREC);
        Rational::new(t.mul(&s).round(), Int::from(1)).div(&s)
    } else {
        t.clone()
    }
}

/// `e^y` for `|y| ≤ 1/2` (term ratio ≤ 1/2 past the first, tail ≤ 2·next).
fn exp_small(y: &Rational) -> Enc {
    let y = y.clone();
    series(
        Rational::from(1),
        move |k| y.div(&Rational::from(k as i64 + 1)),
        Rational::from(2),
    )
}

/// `e^x`.
pub fn exp(x: &Rational) -> Option<Enc> {
    if !small_enough(x) {
        return None;
    }
    let half = Rational::new(Int::from(1), Int::from(2));
    let mut k = 0i32;
    let mut y = x.clone();
    while y.abs() > half {
        y = y.div(&Rational::from(2));
        k += 1;
    }
    let mut e = exp_small(&y);
    for _ in 0..k {
        e = mul_enc(&e, &e);
    }
    Some(e)
}

/// `atanh z` for `|z| ≤ 1/3`: `Σ z^(2k+1)/(2k+1)`, tail ≤ (9/8)·next.
fn atanh_series(z: &Rational) -> Enc {
    let z2 = z.mul(z);
    let mut sum = Rational::from(0);
    let mut p = z.clone();
    let mut k = 0i64;
    loop {
        let t = p.div(&Rational::from(2 * k + 1));
        if t.abs() < tiny() {
            let err = t
                .abs()
                .mul(&Rational::new(Int::from(9), Int::from(8)))
                .add(&tiny());
            return outward(&sum.sub(&err), &sum.add(&err));
        }
        sum = sum.add(&t);
        p = rdown_keep(&p.mul(&z2));
        k += 1;
    }
}

fn ln2() -> Enc {
    let a = atanh_series(&Rational::new(Int::from(1), Int::from(3)));
    outward(&a.0.mul(&Rational::from(2)), &a.1.mul(&Rational::from(2)))
}

/// `ln x` for `x > 0`.
pub fn ln(x: &Rational) -> Option<Enc> {
    if !x.is_positive() {
        return None;
    }
    let e = x.numerator().bit_len() as i32 - x.denominator().bit_len() as i32;
    let m = x.div(&Rational::power_of_two(e));
    let z = m.sub(&Rational::from(1)).div(&m.add(&Rational::from(1)));
    let a = atanh_series(&z);
    let l2 = ln2();
    let ef = Rational::from(e as i64);
    let (l2lo, l2hi) = if e >= 0 {
        (l2.0.mul(&ef), l2.1.mul(&ef))
    } else {
        (l2.1.mul(&ef), l2.0.mul(&ef))
    };
    let two = Rational::from(2);
    Some(outward(
        &a.0.mul(&two).add(&l2lo),
        &a.1.mul(&two).add(&l2hi),
    ))
}

/// `atan y` for `|y| ≤ 1/2`: alternating series, tail ≤ next term.
fn atan_series(y: &Rational) -> Enc {
    let y2 = y.mul(y).neg();
    let mut sum = Rational::from(0);
    let mut p = y.clone();
    let mut k = 0i64;
    loop {
        let t = p.div(&Rational::from(2 * k + 1));
        if t.abs() < tiny() {
            let err = t.abs().add(&tiny());
            return outward(&sum.sub(&err), &sum.add(&err));
        }
        sum = sum.add(&t);
        p = rdown_keep(&p.mul(&y2));
        k += 1;
    }
}

/// `π` by Machin's formula `16·atan(1/5) − 4·atan(1/239)`.
pub fn pi() -> Enc {
    let a = atan_series(&Rational::new(Int::from(1), Int::from(5)));
    let b = atan_series(&Rational::new(Int::from(1), Int::from(239)));
    let (s16, s4) = (Rational::from(16), Rational::from(4));
    outward(
        &a.0.mul(&s16).sub(&b.1.mul(&s4)),
        &a.1.mul(&s16).sub(&b.0.mul(&s4)),
    )
}

fn scale_enc(e: &Enc, k: &Rational) -> Enc {
    if k.is_negative() {
        outward(&e.1.mul(k), &e.0.mul(k))
    } else {
        outward(&e.0.mul(k), &e.1.mul(k))
    }
}

fn add_enc(a: &Enc, b: &Enc) -> Enc {
    outward(&a.0.add(&b.0), &a.1.add(&b.1))
}

fn neg_enc(a: &Enc) -> Enc {
    (a.1.neg(), a.0.neg())
}

/// `atan x`.
pub fn atan(x: &Rational) -> Option<Enc> {
    if x.is_negative() {
        return atan(&x.neg()).map(|e| neg_enc(&e));
    }
    let half = Rational::new(Int::from(1), Int::from(2));
    let one = Rational::from(1);
    if *x > one {
        // π/2 − atan(1/x)
        let a = atan(&x.recip())?;
        let p2 = scale_enc(&pi(), &half);
        return Some(add_enc(&p2, &neg_enc(&a)));
    }
    if *x > half {
        // π/4 + atan((x−1)/(x+1)), the argument in (−1/3, 0].
        let y = x.sub(&one).div(&x.add(&one));
        let p4 = scale_enc(&pi(), &Rational::new(Int::from(1), Int::from(4)));
        return Some(add_enc(&p4, &atan_series(&y)));
    }
    Some(atan_series(x))
}

/// `sin r` and `cos r` for `|r| < 1` (alternating series, tail ≤ next term).
fn sin_cos_small(r: &Rational) -> (Enc, Enc) {
    let r2 = r.mul(r).neg();
    let r2a = r2.clone();
    let s = series(
        r.clone(),
        move |k| r2a.div(&Rational::from((2 * k as i64 + 2) * (2 * k as i64 + 3))),
        Rational::from(1),
    );
    let c = series(
        Rational::from(1),
        move |k| r2.div(&Rational::from((2 * k as i64 + 1) * (2 * k as i64 + 2))),
        Rational::from(1),
    );
    (s, c)
}

/// `(sin x, cos x)`.
fn sin_cos(x: &Rational) -> Option<(Enc, Enc)> {
    if !small_enough(x) {
        return None;
    }
    // x = q·(π/2) + r with q = round(x / (π/2)), r ∈ [r_lo, r_hi].
    let p = pi();
    let half = Rational::new(Int::from(1), Int::from(2));
    let q = x.div(&p.0.mul(&half)).round();
    let qr = Rational::new(q.clone(), Int::from(1));
    let hp = scale_enc(&p, &half.mul(&qr));
    let (r_lo, r_hi) = (x.sub(&hp.1), x.sub(&hp.0));
    if r_lo.abs() >= Rational::from(1) || r_hi.abs() >= Rational::from(1) {
        return None;
    }
    // Lipschitz-1: evaluate at r_lo and widen by the reduction width.
    let (s, c) = sin_cos_small(&r_lo);
    let w = r_hi.sub(&r_lo);
    let widen = |e: Enc| outward(&e.0.sub(&w), &e.1.add(&w));
    let (s, c) = (widen(s), widen(c));
    let quadrant = q.rem_euclid_i64(4);
    Some(match quadrant {
        0 => (s, c),
        1 => (c, neg_enc(&s)),
        2 => (neg_enc(&s), neg_enc(&c)),
        _ => (neg_enc(&c), s),
    })
}

trait RemEuclid4 {
    fn rem_euclid_i64(&self, m: i64) -> i64;
}

impl RemEuclid4 for Int {
    fn rem_euclid_i64(&self, m: i64) -> i64 {
        let r = Rational::new(self.clone(), Int::from(1)).rem_euclid(&Rational::from(m));
        r.to_i64().unwrap_or(0)
    }
}

fn clamp_unit(e: Enc) -> Enc {
    let (one, neg1) = (Rational::from(1), Rational::from(-1));
    (e.0.max(neg1), e.1.min(one))
}

/// `sin x`.
pub fn sin(x: &Rational) -> Option<Enc> {
    sin_cos(x).map(|(s, _)| clamp_unit(s))
}

/// `cos x`.
pub fn cos(x: &Rational) -> Option<Enc> {
    sin_cos(x).map(|(_, c)| clamp_unit(c))
}

/// `tan x` (`None` near a pole).
pub fn tan(x: &Rational) -> Option<Enc> {
    let (s, c) = sin_cos(x)?;
    Some(mul_enc(&s, &recip_enc(&c)?))
}

/// `sinh x = (e^x − e^−x)/2`.
pub fn sinh(x: &Rational) -> Option<Enc> {
    let e = exp(x)?;
    let inv = recip_enc(&e)?;
    let d = add_enc(&e, &neg_enc(&inv));
    Some(scale_enc(&d, &Rational::new(Int::from(1), Int::from(2))))
}

/// `cosh x = (e^|x| + e^−|x|)/2` (increasing in `e^|x| ≥ 1`).
pub fn cosh(x: &Rational) -> Option<Enc> {
    let e = exp(&x.abs())?;
    let lo = e.0.add(&e.0.recip());
    let hi = e.1.add(&e.1.recip());
    let half = Rational::new(Int::from(1), Int::from(2));
    let one = Rational::from(1);
    let (lo, hi) = outward(&lo.mul(&half), &hi.mul(&half));
    Some((lo.max(one), hi))
}

/// `tanh x = 1 − 2/(e^2x + 1)`.
pub fn tanh(x: &Rational) -> Option<Enc> {
    let e = exp(&x.mul(&Rational::from(2)))?;
    let one = Rational::from(1);
    let two = Rational::from(2);
    let lo = one.sub(&two.div(&e.0.add(&one)));
    let hi = one.sub(&two.div(&e.1.add(&one)));
    Some(clamp_unit(outward(&lo, &hi)))
}

/// `√r` for `r ≥ 0`.
fn sqrt(r: &Rational) -> Enc {
    let s2 = Rational::power_of_two(2 * PREC);
    let lo_i = r.mul(&s2).floor().isqrt();
    let hi_i = r.mul(&s2).ceil().isqrt().add(&Int::from(1));
    (
        Rational::new(lo_i, Int::from(1)).div(&scale()),
        Rational::new(hi_i, Int::from(1)).div(&scale()),
    )
}

/// `f` increasing: enclose `f([lo, hi])` from point enclosures at the ends.
fn increasing(e: &Enc, f: impl Fn(&Rational) -> Option<Enc>) -> Option<Enc> {
    Some((f(&e.0)?.0, f(&e.1)?.1))
}

/// `asin x` for `|x| ≤ 1`, as `atan(x / √(1 − x²))`.
pub fn asin(x: &Rational) -> Option<Enc> {
    let one = Rational::from(1);
    if x.abs() > one {
        return None;
    }
    if x.abs() == one {
        let p2 = scale_enc(
            &pi(),
            &Rational::new(Int::from(x.signum() as i64), Int::from(2)),
        );
        return Some(p2);
    }
    let s = sqrt(&one.sub(&x.mul(x)));
    if !s.0.is_positive() {
        return None;
    }
    let t = if x.is_negative() {
        (x.div(&s.0), x.div(&s.1))
    } else {
        (x.div(&s.1), x.div(&s.0))
    };
    increasing(&t, atan)
}

/// `acos x = π/2 − asin x`.
pub fn acos(x: &Rational) -> Option<Enc> {
    let a = asin(x)?;
    let p2 = scale_enc(&pi(), &Rational::new(Int::from(1), Int::from(2)));
    Some(add_enc(&p2, &neg_enc(&a)))
}

/// `atanh x = ½·ln((1+x)/(1−x))` for `|x| < 1`.
pub fn atanh(x: &Rational) -> Option<Enc> {
    let one = Rational::from(1);
    if x.abs() >= one {
        return None;
    }
    let l = ln(&one.add(x).div(&one.sub(x)))?;
    Some(scale_enc(&l, &Rational::new(Int::from(1), Int::from(2))))
}

/// `asinh x = ln(x + √(x²+1))` (odd).
pub fn asinh(x: &Rational) -> Option<Enc> {
    if x.is_negative() {
        return asinh(&x.neg()).map(|e| neg_enc(&e));
    }
    if !small_enough(x) {
        return None;
    }
    let s = sqrt(&x.mul(x).add(&Rational::from(1)));
    increasing(&(x.add(&s.0), x.add(&s.1)), ln)
}

/// `acosh x = ln(x + √(x²−1))` for `x ≥ 1`.
pub fn acosh(x: &Rational) -> Option<Enc> {
    if *x < Rational::from(1) || !small_enough(x) {
        return None;
    }
    let s = sqrt(&x.mul(x).sub(&Rational::from(1)));
    increasing(&(x.add(&s.0), x.add(&s.1)), ln)
}

/// The enclosure of the named unary transcendental at `x`.
pub fn eval(name: &str, x: &Rational) -> Option<Enc> {
    match name {
        "sin" => sin(x),
        "cos" => cos(x),
        "tan" => tan(x),
        "asin" => asin(x),
        "acos" => acos(x),
        "atan" => atan(x),
        "sinh" => sinh(x),
        "cosh" => cosh(x),
        "tanh" => tanh(x),
        "asinh" => asinh(x),
        "acosh" => acosh(x),
        "atanh" => atanh(x),
        "exp" => exp(x),
        "log" => ln(x),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn r(n: i64, d: i64) -> Rational {
        Rational::new(Int::from(n), Int::from(d))
    }

    fn check(name: &str, x: (i64, i64), f: fn(f64) -> f64) {
        let xf = x.0 as f64 / x.1 as f64;
        let expect = f(xf);
        let (lo, hi) = eval(name, &r(x.0, x.1)).unwrap();
        assert!(lo <= hi, "{name}({xf})");
        let width = hi.sub(&lo).to_f64();
        assert!(width < 1e-20, "{name}({xf}) width {width}");
        let mid = lo.to_f64();
        assert!(
            (mid - expect).abs() <= 1e-12 * expect.abs().max(1.0),
            "{name}({xf}) = {mid}, expected {expect}"
        );
    }

    #[test]
    fn enclosures_match_libm() {
        for &x in &[
            (0, 1),
            (1, 4),
            (-7, 10),
            (1, 1),
            (5, 2),
            (-15, 4),
            (10, 1),
            (100, 1),
        ] {
            check("sin", x, f64::sin);
            check("cos", x, f64::cos);
            check("atan", x, f64::atan);
            check("tanh", x, f64::tanh);
            check("asinh", x, f64::asinh);
            let y = (x.0, x.1 * 10);
            check("sinh", y, f64::sinh);
            check("cosh", y, f64::cosh);
            check("exp", y, f64::exp);
        }
        for &x in &[(1, 1000), (1, 2), (1, 1), (2, 1), (1000, 1)] {
            check("log", x, f64::ln);
        }
        for &x in &[(-1, 1), (-1, 2), (0, 1), (3, 10), (999, 1000)] {
            check("asin", x, f64::asin);
            check("acos", x, f64::acos);
        }
        for &x in &[(-9, 10), (0, 1), (1, 2)] {
            check("atanh", x, f64::atanh);
        }
        check("acosh", (3, 1), f64::acosh);
        check("tan", (6, 5), f64::tan);
        let (lo, hi) = pi();
        assert!(lo.to_f64() <= core::f64::consts::PI && core::f64::consts::PI <= hi.to_f64());
        assert!(eval("log", &r(0, 1)).is_none());
        assert!(eval("asin", &r(3, 2)).is_none());
    }
}
