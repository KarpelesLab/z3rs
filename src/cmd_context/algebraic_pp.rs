//! Decimal pretty-printing of concrete real algebraic constants for `pp.decimal`.
//!
//! Under `:pp.decimal true`, z3's `(simplify …)` prints an irrational algebraic
//! constant — e.g. `(^ 2.0 (/ 1.0 2.0))` = √2 — as a truncated decimal with a
//! trailing `?` (`1.4142135623?`), where the number of fractional digits is
//! `:pp.decimal-precision` (default 10). z3rs otherwise leaves the `^` term
//! opaque.
//!
//! This module evaluates a *ground* real expression (numerals combined with
//! `+ - * / ^ abs to_real`) to either an exact `Rational` or a high-precision
//! `Float`, and — only when the value is genuinely irrational — formats it
//! exactly the way z3 does. The formatter is a port of
//! `mpbq_manager::display_decimal` (`z3/src/util/mpbq.cpp`): base-10 long
//! division truncated (never rounded) to `precision` fractional digits, with `?`
//! appended iff a nonzero remainder survives all `precision` digits.
//!
//! Only the irrational case is emitted; rational-real results fall through to the
//! normal printer so already-passing output is never disturbed.

use crate::ast::AstId;
use crate::ast::arith::ArithOp;
use crate::ast::manager::AstManager;
use alloc::format;
use alloc::string::{String, ToString};
use alloc::vec::Vec;
use core::cmp::Ordering;
use puremp::{Algebraic, Float, Int, Poly, Rational, RoundingMode};

const RM: RoundingMode = RoundingMode::Nearest;

/// A ground real value: exactly rational, or a high-precision irrational.
enum RealVal {
    Rat(Rational),
    Irr(Float),
}

impl RealVal {
    fn to_float(&self, bits: u64) -> Float {
        match self {
            RealVal::Rat(r) => Float::from_rational(r, bits, RM),
            RealVal::Irr(f) => f.clone(),
        }
    }
}

/// The `pp.decimal` rendering of a simplified term `s`, or `None` when `s` is not
/// a ground irrational real (in which case the caller prints it normally).
pub fn format_pp_decimal(m: &AstManager, s: AstId, precision: u32) -> Option<String> {
    // Enough base-2 guard bits to make the first `precision` decimal digits of an
    // irrational reliably correct (~3.33 bits/digit, plus a wide margin).
    let bits = (precision as u64 + 40) * 4 + 64;
    match eval_real(m, s, bits)? {
        // Leave rationals to the normal printer.
        RealVal::Rat(_) => None,
        RealVal::Irr(f) => {
            let v = f.to_rational()?;
            let (neg, body) = format_trunc(&v, precision);
            Some(if neg { format!("(- {body})") } else { body })
        }
    }
}

/// Like [`format_pp_decimal`] but recurses through an arithmetic term so that an
/// irrational algebraic *subterm* prints as its decimal while the surrounding
/// structure is preserved — e.g. `(/ (^ 2.0 (/ 1.0 2.0)) 0.0)` (a division by
/// zero that stays symbolic) renders as `(/ 1.4142135623? 0.0)`. Returns `None`
/// if `s` contains no irrational algebraic subterm (the caller prints normally).
/// Only rebuilds through `+ - * / ^` whose SMT form is a plain prefix application,
/// so an unchanged subterm's `m.pp` output is reproduced exactly; rational
/// numerals are never reformatted, so no already-passing output changes.
pub fn format_pp_decimal_rec(m: &AstManager, s: AstId, precision: u32) -> Option<String> {
    if let Some(d) = format_pp_decimal(m, s, precision) {
        return Some(d);
    }
    // Recurse only through arithmetic / power heads printed as `(op args…)`.
    let head = arith_prefix_head(m, s)?;
    let args = m.app_args(s);
    let mut parts = Vec::with_capacity(args.len());
    let mut changed = false;
    for &a in args {
        match format_pp_decimal_rec(m, a, precision) {
            Some(fa) => {
                changed = true;
                parts.push(fa);
            }
            None => parts.push(m.pp(a)),
        }
    }
    changed.then(|| format!("({head} {})", parts.join(" ")))
}

/// The prefix head symbol (`+ - * / ^`) if `s` is such an application, else
/// `None`. These are exactly the heads z3rs prints as `(sym arg…)`.
fn arith_prefix_head(m: &AstManager, s: AstId) -> Option<&'static str> {
    if let Some(op) = m.arith_op(s) {
        return match op {
            ArithOp::Add => Some("+"),
            ArithOp::Sub | ArithOp::Uminus => Some("-"),
            ArithOp::Mul => Some("*"),
            ArithOp::Div => Some("/"),
            ArithOp::Power => Some("^"),
            _ => None,
        };
    }
    // The opaque `(^ base exp)` power UF.
    (m.app(s)?.args.len() == 2 && m.func_decl(m.app_decl(s))?.name.as_str()? == "^").then_some("^")
}

/// Evaluates a ground real term, or `None` if it contains a variable / an
/// unsupported operator / a division by zero.
fn eval_real(m: &AstManager, s: AstId, bits: u64) -> Option<RealVal> {
    if let Some(r) = m.as_numeral(s) {
        return Some(RealVal::Rat(r));
    }
    // `(^ base exp)` with a non-integer exponent is kept as an opaque UF named
    // "^" (not an arith-family `Power` op), so match it by decl name.
    if let Some((base_t, exp_t)) = power_uf_args(m, s) {
        let base = eval_real(m, base_t, bits)?;
        let e = match eval_real(m, exp_t, bits)? {
            RealVal::Rat(r) => r,
            RealVal::Irr(_) => return None,
        };
        return power(base, &e, bits);
    }
    let op = m.arith_op(s)?;
    let args = m.app_args(s);
    match op {
        ArithOp::ToReal => eval_real(m, *args.first()?, bits),
        ArithOp::Abs => {
            let v = eval_real(m, *args.first()?, bits)?;
            Some(match v {
                RealVal::Rat(r) => RealVal::Rat(r.abs()),
                RealVal::Irr(f) => {
                    if f.is_sign_negative() {
                        RealVal::Irr(Float::zero(bits).sub(&f, bits, RM))
                    } else {
                        RealVal::Irr(f)
                    }
                }
            })
        }
        ArithOp::Uminus => {
            let v = eval_real(m, *args.first()?, bits)?;
            Some(negate(v, bits))
        }
        ArithOp::Add => {
            let mut acc = eval_real(m, *args.first()?, bits)?;
            for &a in &args[1..] {
                acc = add(acc, eval_real(m, a, bits)?, bits);
            }
            Some(acc)
        }
        ArithOp::Sub => {
            let mut acc = eval_real(m, *args.first()?, bits)?;
            if args.len() == 1 {
                return Some(negate(acc, bits));
            }
            for &a in &args[1..] {
                let rhs = negate(eval_real(m, a, bits)?, bits);
                acc = add(acc, rhs, bits);
            }
            Some(acc)
        }
        ArithOp::Mul => {
            let mut acc = eval_real(m, *args.first()?, bits)?;
            for &a in &args[1..] {
                acc = mul(acc, eval_real(m, a, bits)?, bits);
            }
            Some(acc)
        }
        ArithOp::Div => {
            let mut acc = eval_real(m, *args.first()?, bits)?;
            for &a in &args[1..] {
                acc = div(acc, eval_real(m, a, bits)?, bits)?;
            }
            Some(acc)
        }
        ArithOp::Power => {
            let base = eval_real(m, *args.first()?, bits)?;
            // The exponent must be an exact rational (it is often an unfolded
            // `(/ 1.0 2.0)` division node rather than a single numeral).
            let e = match eval_real(m, *args.get(1)?, bits)? {
                RealVal::Rat(r) => r,
                RealVal::Irr(_) => return None,
            };
            power(base, &e, bits)
        }
        _ => None,
    }
}

/// The two arguments of an opaque `(^ base exp)` power UF, if `s` is one.
fn power_uf_args(m: &AstManager, s: AstId) -> Option<(AstId, AstId)> {
    let a = m.app(s)?;
    if a.args.len() != 2 {
        return None;
    }
    if m.func_decl(m.app_decl(s))?.name.as_str()? == "^" {
        Some((a.args[0], a.args[1]))
    } else {
        None
    }
}

fn negate(v: RealVal, bits: u64) -> RealVal {
    match v {
        RealVal::Rat(r) => RealVal::Rat(-r),
        RealVal::Irr(f) => RealVal::Irr(Float::zero(bits).sub(&f, bits, RM)),
    }
}

fn add(a: RealVal, b: RealVal, bits: u64) -> RealVal {
    match (a, b) {
        (RealVal::Rat(x), RealVal::Rat(y)) => RealVal::Rat(&x + &y),
        (a, b) => RealVal::Irr(a.to_float(bits).add(&b.to_float(bits), bits, RM)),
    }
}

fn mul(a: RealVal, b: RealVal, bits: u64) -> RealVal {
    match (a, b) {
        (RealVal::Rat(x), RealVal::Rat(y)) => RealVal::Rat(&x * &y),
        (a, b) => RealVal::Irr(a.to_float(bits).mul(&b.to_float(bits), bits, RM)),
    }
}

fn div(a: RealVal, b: RealVal, bits: u64) -> Option<RealVal> {
    Some(match (a, b) {
        (RealVal::Rat(x), RealVal::Rat(y)) => {
            if y.is_zero() {
                return None;
            }
            RealVal::Rat(&x / &y)
        }
        (a, b) => {
            let bf = b.to_float(bits);
            if bf.to_rational().map(|r| r.is_zero()).unwrap_or(true) {
                return None;
            }
            RealVal::Irr(a.to_float(bits).div(&bf, bits, RM))
        }
    })
}

/// `base ^ e` for a rational exponent `e`. Rational only when exactly rational
/// (integer exponent, or an exact `q`-th root); otherwise a high-precision float
/// via `exp(e·ln base)` (requires `base > 0`).
fn power(base: RealVal, e: &Rational, bits: u64) -> Option<RealVal> {
    if let RealVal::Rat(r) = &base
        && let Some(exact) = exact_rational_power(r, e)
    {
        return Some(RealVal::Rat(exact));
    }
    // Irrational (or an irrational base): float power. Only real for base > 0.
    let bf = base.to_float(bits);
    if bf.is_sign_negative() || bf.is_zero() {
        return None;
    }
    let ef = Float::from_rational(e, bits, RM);
    Some(RealVal::Irr(bf.pow(&ef, bits, RM)))
}

/// `r ^ (p/q)` as an exact rational, or `None` if it is irrational.
fn exact_rational_power(r: &Rational, e: &Rational) -> Option<Rational> {
    let p = e.numerator().to_i64()?;
    if p > i32::MAX as i64 || p < i32::MIN as i64 {
        return None;
    }
    let rp = r.pow(p as i32); // r^p, exact (handles negative p)
    let q = e.denominator();
    if q.is_one() {
        return Some(rp);
    }
    // q-th root of rp = q-th root of numerator over q-th root of denominator.
    let qn = q.to_u64()?;
    if qn == 0 || qn > u32::MAX as u64 {
        return None;
    }
    if rp.is_negative() {
        return None; // real q-th root of a negative rational: skip (unused here)
    }
    let rn = rp.numerator().nth_root_exact(qn as u32)?;
    let rd = rp.denominator().nth_root_exact(qn as u32)?;
    Some(Rational::new(rn, rd))
}

/// z3's `mpbq_manager::display_decimal`: integer part, `.`, then up to
/// `precision` fractional digits by truncating base-10 long division; a `?` is
/// appended iff the remainder is still nonzero after `precision` digits.
/// Returns `(is_negative, unsigned-decimal-string)`.
fn format_trunc(v: &Rational, precision: u32) -> (bool, String) {
    let neg = v.is_negative();
    let a = v.abs();
    let num = a.numerator();
    let den = a.denominator();
    let (ip, mut rem) = num.div_rem_floor(den);
    let mut out = ip.to_string();
    if rem.is_zero() {
        return (neg, out);
    }
    out.push('.');
    let ten = Int::from_i64(10);
    let mut trailing = false;
    for _ in 0..precision {
        let scaled = &rem * &ten;
        let (digit, r) = scaled.div_rem_floor(den);
        out.push_str(&digit.to_string());
        rem = r;
        if rem.is_zero() {
            trailing = false;
            break;
        }
        trailing = true;
    }
    if trailing {
        out.push('?');
    }
    (neg, out)
}

// ---------------------------------------------------------------------------
// Exact algebraic comparison folding.
//
// z3's `simplify` decides a comparison / equality between two ground real
// constants — e.g. `(< (^ 2.0 (/ 1.0 2.0)) 2.0)` → `true` — using exact
// algebraic-number arithmetic. z3rs leaves the `^` opaque, so the comparison
// survives. `fold_real_comparison` reproduces the decision exactly via
// `puremp::Algebraic`, so no floating-point rounding can give a wrong verdict.
// ---------------------------------------------------------------------------

/// A ground real value carried exactly: rational until an irrational root forces
/// a lift to a full algebraic number.
enum AlgVal {
    Rat(Rational),
    Alg(Algebraic),
}

impl AlgVal {
    fn into_algebraic(self) -> Algebraic {
        match self {
            AlgVal::Rat(r) => Algebraic::from_rational(r),
            AlgVal::Alg(a) => a,
        }
    }
}

/// `true`/`false` if `s` is a comparison or equality of two ground real
/// constants; `None` otherwise (a variable, an unsupported operator, or a
/// non-real comparison — left to the normal printer).
pub fn fold_real_comparison(m: &AstManager, s: AstId) -> Option<bool> {
    if m.is_eq(s) {
        let args = m.app_args(s);
        if args.len() != 2 || !m.is_arith_sort(m.get_sort(args[0])) {
            return None;
        }
        let a = eval_algebraic(m, args[0])?.into_algebraic();
        let b = eval_algebraic(m, args[1])?.into_algebraic();
        return Some(a == b);
    }
    let op = m.arith_op(s)?;
    let args = m.app_args(s);
    if args.len() != 2 {
        return None;
    }
    let ord = eval_algebraic(m, args[0])?
        .into_algebraic()
        .cmp(&eval_algebraic(m, args[1])?.into_algebraic());
    Some(match op {
        ArithOp::Lt => ord == Ordering::Less,
        ArithOp::Le => ord != Ordering::Greater,
        ArithOp::Gt => ord == Ordering::Greater,
        ArithOp::Ge => ord != Ordering::Less,
        _ => return None,
    })
}

/// Exact algebraic value of a ground real term, or `None` for a variable / an
/// unsupported operator / a real root that is not real (e.g. even root of a
/// negative) / a q-th root of an irrational.
fn eval_algebraic(m: &AstManager, s: AstId) -> Option<AlgVal> {
    if let Some(r) = m.as_numeral(s) {
        return Some(AlgVal::Rat(r));
    }
    if let Some((base_t, exp_t)) = power_uf_args(m, s) {
        let base = eval_algebraic(m, base_t)?;
        let e = eval_rational(m, exp_t)?;
        return alg_power(base, &e);
    }
    let op = m.arith_op(s)?;
    let args = m.app_args(s);
    match op {
        ArithOp::ToReal => eval_algebraic(m, *args.first()?),
        ArithOp::Abs => Some(alg_abs(eval_algebraic(m, *args.first()?)?)),
        ArithOp::Uminus => Some(alg_neg(eval_algebraic(m, *args.first()?)?)),
        ArithOp::Add => {
            let mut acc = eval_algebraic(m, *args.first()?)?;
            for &a in &args[1..] {
                acc = alg_add(acc, eval_algebraic(m, a)?);
            }
            Some(acc)
        }
        ArithOp::Sub => {
            let mut acc = eval_algebraic(m, *args.first()?)?;
            if args.len() == 1 {
                return Some(alg_neg(acc));
            }
            for &a in &args[1..] {
                acc = alg_sub(acc, eval_algebraic(m, a)?);
            }
            Some(acc)
        }
        ArithOp::Mul => {
            let mut acc = eval_algebraic(m, *args.first()?)?;
            for &a in &args[1..] {
                acc = alg_mul(acc, eval_algebraic(m, a)?);
            }
            Some(acc)
        }
        ArithOp::Div => {
            let mut acc = eval_algebraic(m, *args.first()?)?;
            for &a in &args[1..] {
                acc = alg_div(acc, eval_algebraic(m, a)?)?;
            }
            Some(acc)
        }
        ArithOp::Power => {
            let base = eval_algebraic(m, *args.first()?)?;
            let e = eval_rational(m, *args.get(1)?)?;
            alg_power(base, &e)
        }
        _ => None,
    }
}

fn eval_rational(m: &AstManager, s: AstId) -> Option<Rational> {
    match eval_real(m, s, 128)? {
        RealVal::Rat(r) => Some(r),
        RealVal::Irr(_) => None,
    }
}

fn alg_neg(v: AlgVal) -> AlgVal {
    match v {
        AlgVal::Rat(r) => AlgVal::Rat(-r),
        AlgVal::Alg(a) => AlgVal::Alg(a.neg()),
    }
}

fn alg_abs(v: AlgVal) -> AlgVal {
    match v {
        AlgVal::Rat(r) => AlgVal::Rat(r.abs()),
        AlgVal::Alg(a) if a.signum() < 0 => AlgVal::Alg(a.neg()),
        AlgVal::Alg(a) => AlgVal::Alg(a),
    }
}

fn alg_add(a: AlgVal, b: AlgVal) -> AlgVal {
    match (a, b) {
        (AlgVal::Rat(x), AlgVal::Rat(y)) => AlgVal::Rat(&x + &y),
        (a, b) => AlgVal::Alg(a.into_algebraic().add(&b.into_algebraic())),
    }
}

fn alg_sub(a: AlgVal, b: AlgVal) -> AlgVal {
    match (a, b) {
        (AlgVal::Rat(x), AlgVal::Rat(y)) => AlgVal::Rat(&x - &y),
        (a, b) => AlgVal::Alg(a.into_algebraic().sub(&b.into_algebraic())),
    }
}

fn alg_mul(a: AlgVal, b: AlgVal) -> AlgVal {
    match (a, b) {
        (AlgVal::Rat(x), AlgVal::Rat(y)) => AlgVal::Rat(&x * &y),
        (a, b) => AlgVal::Alg(a.into_algebraic().mul(&b.into_algebraic())),
    }
}

fn alg_div(a: AlgVal, b: AlgVal) -> Option<AlgVal> {
    Some(match (a, b) {
        (AlgVal::Rat(x), AlgVal::Rat(y)) => {
            if y.is_zero() {
                return None;
            }
            AlgVal::Rat(&x / &y)
        }
        (a, b) => {
            let ba = b.into_algebraic();
            if ba.signum() == 0 {
                return None;
            }
            AlgVal::Alg(a.into_algebraic().div(&ba))
        }
    })
}

/// `base ^ (p/q)` exactly. Rational base: `q`-th root of `base^p`. Irrational
/// base: integer exponents, and a square root (`q = 2`) of a non-negative value
/// via `Algebraic::sqrt`; other roots of an irrational are unsupported.
fn alg_power(base: AlgVal, e: &Rational) -> Option<AlgVal> {
    let p = e.numerator().to_i64()?;
    if p > i32::MAX as i64 || p < i32::MIN as i64 {
        return None;
    }
    let q = e.denominator().to_u64()?;
    if q == 0 || q > 128 {
        return None;
    }
    match base {
        AlgVal::Rat(r) => {
            let rp = r.pow(p as i32);
            if q == 1 {
                Some(AlgVal::Rat(rp))
            } else {
                Some(AlgVal::Alg(algebraic_nth_root(&rp, q as u32)?))
            }
        }
        AlgVal::Alg(a) => {
            let bp = alg_powi(&a, p as i32)?;
            if q == 2 {
                // Principal (non-negative) square root; real only for bp ≥ 0.
                if bp.signum() < 0 {
                    return None;
                }
                return Some(AlgVal::Alg(bp.sqrt()));
            }
            if q != 1 {
                return None;
            }
            Some(AlgVal::Alg(bp))
        }
    }
}

/// The positive real `q`-th root of a positive rational `c`, as an exact
/// algebraic number (root of `T^q − c`). `None` for a negative `c`.
fn algebraic_nth_root(c: &Rational, q: u32) -> Option<Algebraic> {
    if c.is_zero() {
        return Some(Algebraic::from_int(Int::from_i64(0)));
    }
    if c.is_negative() {
        return None;
    }
    let mut coeffs: Vec<Rational> = Vec::with_capacity(q as usize + 1);
    coeffs.push(-c.clone());
    for _ in 1..q {
        coeffs.push(Rational::from_integer(Int::from_i64(0)));
    }
    coeffs.push(Rational::from_integer(Int::from_i64(1)));
    let poly = Poly::new(coeffs);
    Algebraic::real_roots_of(&poly)
        .into_iter()
        .find(|r| r.signum() > 0)
}

/// `a ^ p` for an integer `p` (repeated multiplication; reciprocal if negative).
fn alg_powi(a: &Algebraic, p: i32) -> Option<Algebraic> {
    if p == 0 {
        return Some(Algebraic::from_int(Int::from_i64(1)));
    }
    let n = p.unsigned_abs();
    let mut acc = a.clone();
    for _ in 1..n {
        acc = acc.mul(a);
    }
    Some(if p < 0 { acc.recip() } else { acc })
}

// ---------------------------------------------------------------------------
// Trigonometric values at rational multiples of π.
//
// z3's `simplify` evaluates `cos`/`sin`/`tan` at a rational multiple of π to the
// exact algebraic number (`cos(π/4)` = 1/√2, `tan(π/3)` = √3, `cos(π/3)` = 1/2).
// `cos(kπ/n)` is a root of the Chebyshev polynomial equation `T_n(x) = (−1)^k`;
// we build `T_n(x) − (−1)^k`, isolate its real roots exactly, and select the one
// matching the numeric value. `sin(cπ) = cos((1/2 − c)π)`; `tan = sin / cos`.
// ---------------------------------------------------------------------------

/// The `pp.decimal` rendering of `fn(c·π)` for `fn ∈ {cos, sin, tan}`, or `None`
/// when the value is unsupported / `tan` hits a pole.
pub fn trig_pp_decimal(fname: &str, c: &Rational, precision: u32) -> Option<String> {
    let half = Rational::new(Int::from_i64(1), Int::from_i64(2));
    match fname {
        // cos(cπ) and sin(cπ) = cos((1/2 − c)π) are exact algebraic values.
        "cos" => format_trig_decimal(cos_pi(c)?, precision),
        "sin" => format_trig_decimal(cos_pi(&(&half - c))?, precision),
        "tan" => tan_pp_decimal(c, precision),
        _ => None,
    }
}

/// The `pp.decimal` rendering of tan(c·π). By Niven's theorem the only rational
/// values are 0 (at integer multiples of π) and ±1 (at π/4 + kπ/2); everything
/// else is irrational and printed from a high-precision `Float::tan`. `tan` at a
/// pole (c ≡ 1/2 mod 1) is left unevaluated. This avoids algebraic division,
/// which puremp 0.2.0 mishandles for a rational divisor.
fn tan_pp_decimal(c: &Rational, precision: u32) -> Option<String> {
    // Pole at c ≡ 1/2 mod 1.
    let r = c - &Rational::from_integer(c.floor());
    if r == Rational::new(Int::from_i64(1), Int::from_i64(2)) {
        return None;
    }
    // Rational values (0, ±1) print as `N.0`.
    if let Some(rat) = tan_rational(c) {
        return Some(render_real_rational(&rat));
    }
    // Irrational: high-precision float value.
    let bits = (precision as u64 + 40) * 4 + 64;
    let pi = Float::pi(bits, RM);
    let v = Float::from_rational(c, bits, RM)
        .mul(&pi, bits, RM)
        .tan(bits, RM);
    let neg = v.is_sign_negative();
    let mag = if neg {
        Float::zero(bits).sub(&v, bits, RM)
    } else {
        v
    };
    let body = format_trunc(&mag.to_rational()?, precision).1;
    Some(if neg { format!("(- {body})") } else { body })
}

/// The `pp.decimal` rendering of an exact trig value: an integer rational prints
/// as `N.0`, a non-integer rational as its terminating decimal, an irrational as
/// a truncated decimal with `?`. A negative value is wrapped `(- …)`.
fn format_trig_decimal(v: AlgVal, precision: u32) -> Option<String> {
    let (neg, body) = match v {
        AlgVal::Rat(r) => {
            let neg = r.is_negative();
            let a = r.abs();
            let body = match a.to_integer() {
                Some(i) => format!("{i}.0"),
                None => format_trunc(&a, precision).1,
            };
            (neg, body)
        }
        AlgVal::Alg(a) => {
            let neg = a.signum() < 0;
            let mag = if neg { a.neg() } else { a };
            let bits = (precision as u64 + 40) * 4 + 64;
            let fr = mag.to_float(bits, RM).to_rational()?;
            (neg, format_trunc(&fr, precision).1)
        }
    };
    Some(if neg { format!("(- {body})") } else { body })
}

/// `cos(c·π)` / `sin(c·π)` rendered as z3 does without `:pp.decimal`: an exact
/// real rational, or a `root-obj` for the irrational algebraic value. `tan` is not
/// handled here (its algebraic form needs division, which puremp mishandles); a
/// `tan` term is then left opaque.
pub fn trig_exact(fname: &str, c: &Rational) -> Option<String> {
    let half = Rational::new(Int::from_i64(1), Int::from_i64(2));
    let v = match fname {
        "cos" => cos_pi(c)?,
        "sin" => cos_pi(&(&half - c))?,
        // tan's rational values (0, ±1) are exact; its irrational values need a
        // minimal polynomial we cannot form without algebraic division, so those
        // stay opaque (no corpus file needs tan `root-obj`).
        "tan" => return Some(render_real_rational(&tan_rational(c)?)),
        _ => return None,
    };
    Some(match v {
        AlgVal::Rat(r) => render_real_rational(&r),
        AlgVal::Alg(a) => root_obj_string(&a)?,
    })
}

/// The exact rational value of tan(c·π) when it is rational — 0 at integer
/// multiples of π, ±1 at π/4 + kπ/2 (Niven's theorem) — else `None` (an
/// irrational value or the pole at c ≡ 1/2 mod 1).
fn tan_rational(c: &Rational) -> Option<Rational> {
    let r = c - &Rational::from_integer(c.floor()); // c mod 1 (period π)
    if r.is_zero() {
        return Some(Rational::from_integer(Int::from_i64(0)));
    }
    let quarter = Rational::new(Int::from_i64(1), Int::from_i64(4));
    let three_q = Rational::new(Int::from_i64(3), Int::from_i64(4));
    if r == quarter {
        return Some(Rational::from_integer(Int::from_i64(1)));
    }
    if r == three_q {
        return Some(Rational::from_integer(Int::from_i64(-1)));
    }
    None
}

/// A rational rendered as a z3 real numeral: `N.0`, `(/ p.0 q.0)`, with a negative
/// value wrapped `(- …)` (z3 never puts the sign inside the numerator).
fn render_real_rational(r: &Rational) -> String {
    let a = r.abs();
    let body = match a.to_integer() {
        Some(i) => format!("{i}.0"),
        None => format!("(/ {}.0 {}.0)", a.numerator(), a.denominator()),
    };
    if r.is_negative() {
        format!("(- {body})")
    } else {
        body
    }
}

/// z3's `(root-obj <poly> <index>)` for an irrational algebraic number: its
/// primitive integer minimal polynomial (positive leading coefficient) and the
/// 1-based index of this root among that polynomial's real roots in increasing
/// order. Uses only root isolation, factoring and polynomial evaluation — never
/// algebraic arithmetic (which puremp 0.2.0 mishandles on crowded polynomials).
fn root_obj_string(a: &Algebraic) -> Option<String> {
    // Tighten the isolating interval so it excludes every other root of the
    // defining polynomial (adjacent factors, incl. a spurious `x`/root-0 factor);
    // otherwise an endpoint sitting on another root mis-selects the factor.
    let mut aa = a.clone();
    aa.refine_below(&Rational::power_of_two(-48));
    let (lo, hi) = aa.interval();
    // Minimal polynomial = the irreducible factor of the (squarefree) defining
    // polynomial whose real root lies in this root's isolating interval.
    let min_poly = a
        .defining_polynomial()
        .factor()
        .into_iter()
        .map(|(f, _)| f)
        .find(|f| factor_has_root_in(f, lo, hi))?;
    let ints = primitive_integer_coeffs(&min_poly)?;
    // Index of this root among the factor's real roots (increasing order).
    let af = a.to_f64();
    let roots = Algebraic::real_roots_of(&min_poly);
    let mut best_i = 0usize;
    let mut best = f64::INFINITY;
    for (i, r) in roots.iter().enumerate() {
        let d = (r.to_f64() - af).abs();
        if d < best {
            best = d;
            best_i = i;
        }
    }
    Some(format!("(root-obj {} {})", poly_to_smt(&ints), best_i + 1))
}

/// Whether polynomial `f` has a real root within `[lo, hi]` (a sign change or a
/// zero at an endpoint).
fn factor_has_root_in(f: &Poly<Rational>, lo: &Rational, hi: &Rational) -> bool {
    let sl = f.eval(lo).signum();
    let sh = f.eval(hi).signum();
    sl == 0 || sh == 0 || sl != sh
}

/// The coefficients of `p` cleared to primitive integers with a positive leading
/// coefficient, in ascending degree order.
fn primitive_integer_coeffs(p: &Poly<Rational>) -> Option<Vec<Int>> {
    let coeffs = p.coeffs();
    if coeffs.is_empty() {
        return None;
    }
    let mut den_lcm = Int::from_i64(1);
    for c in coeffs {
        den_lcm = den_lcm.lcm(c.denominator());
    }
    let mut ints: Vec<Int> = coeffs
        .iter()
        .map(|c| {
            let scale = den_lcm.div_rem_trunc(c.denominator()).0;
            c.numerator() * &scale
        })
        .collect();
    let mut g = Int::from_i64(0);
    for x in &ints {
        g = g.gcd(x);
    }
    if g.is_zero() {
        return None;
    }
    for x in &mut ints {
        *x = x.div_rem_trunc(&g).0;
    }
    if ints.last()?.is_negative() {
        ints = ints.iter().map(|x| -x).collect();
    }
    Some(ints)
}

/// Formats integer polynomial coefficients (ascending degree) as z3's SMT sum
/// `(+ (* c (^ x d)) … const)`, highest degree first.
fn poly_to_smt(ints: &[Int]) -> String {
    let mut terms: Vec<String> = Vec::new();
    for d in (0..ints.len()).rev() {
        let c = &ints[d];
        if c.is_zero() {
            continue;
        }
        let coeff = if c.is_negative() {
            format!("(- {})", -c)
        } else {
            format!("{c}")
        };
        terms.push(if d == 0 {
            coeff
        } else if d == 1 {
            format!("(* {coeff} x)")
        } else {
            format!("(* {coeff} (^ x {d}))")
        });
    }
    format!("(+ {})", terms.join(" "))
}

/// cos(c·π) as an exact rational-or-algebraic value.
fn cos_pi(c: &Rational) -> Option<AlgVal> {
    let n = c.denominator().to_u64()?;
    if n == 0 || n > 200 {
        return None;
    }
    let n = n as u32;
    // cos(kπ/n) is a root of `T_n(x) = (−1)^k`.
    let sign = if c.numerator().is_even() { 1 } else { -1 };
    let poly = chebyshev_t(n).sub(&Poly::constant(Rational::from_integer(Int::from_i64(sign))));
    let target = float_cos_pi(c, 200);
    let mut best: Option<Algebraic> = None;
    let mut best_d = f64::INFINITY;
    for r in Algebraic::real_roots_of(&poly) {
        let d = (r.to_f64() - target).abs();
        if d < best_d {
            best_d = d;
            best = Some(r);
        }
    }
    let a = best?;
    Some(if a.is_rational() {
        AlgVal::Rat(a.interval().0.clone())
    } else {
        AlgVal::Alg(a)
    })
}

/// A `f64` approximation of cos(c·π), used only to select the right isolated root.
fn float_cos_pi(c: &Rational, bits: u64) -> f64 {
    let pi = Float::pi(bits, RM);
    let arg = Float::from_rational(c, bits, RM).mul(&pi, bits, RM);
    arg.cos(bits, RM).to_f64()
}

/// The Chebyshev polynomial of the first kind `T_n(x)` over ℚ.
fn chebyshev_t(n: u32) -> Poly<Rational> {
    let one = Rational::from_integer(Int::from_i64(1));
    let mut prev = Poly::constant(one.clone()); // T_0 = 1
    if n == 0 {
        return prev;
    }
    let mut cur = Poly::monomial(one, 1); // T_1 = x
    let two_x = Poly::monomial(Rational::from_integer(Int::from_i64(2)), 1);
    for _ in 1..n {
        let next = two_x.mul(&cur).sub(&prev); // T_{m+1} = 2x·T_m − T_{m−1}
        prev = cur;
        cur = next;
    }
    cur
}

#[cfg(test)]
mod tests {
    use super::format_trunc;
    use puremp::{Int, Rational};

    fn rat(n: i64, d: i64) -> Rational {
        Rational::new(Int::from_i64(n), Int::from_i64(d))
    }

    #[test]
    fn trig_exact_root_obj_and_rational() {
        use super::trig_exact;
        use puremp::{Int, Rational};
        let r = |n: i64, d: i64| Rational::new(Int::from_i64(n), Int::from_i64(d));
        // cos(π/4) = 1/√2 → root 2 of 2x²−1.
        assert_eq!(
            trig_exact("cos", &r(1, 4)).unwrap(),
            "(root-obj (+ (* 2 (^ x 2)) (- 1)) 2)"
        );
        // sin(π/3) = √3/2 → root 2 of 4x²−3.
        assert_eq!(
            trig_exact("sin", &r(1, 3)).unwrap(),
            "(root-obj (+ (* 4 (^ x 2)) (- 3)) 2)"
        );
        // cos(2π/3) = −1/2 (rational).
        assert_eq!(trig_exact("cos", &r(2, 3)).unwrap(), "(- (/ 1.0 2.0))");
        // tan(π/4) = 1; tan(0) = 0.
        assert_eq!(trig_exact("tan", &r(1, 4)).unwrap(), "1.0");
        assert_eq!(trig_exact("tan", &r(0, 1)).unwrap(), "0.0");
    }

    #[test]
    fn nonterminating_gets_question_mark() {
        // 1/3 = 0.3333… → ten digits then `?`.
        assert_eq!(
            format_trunc(&rat(1, 3), 10),
            (false, "0.3333333333?".into())
        );
    }

    #[test]
    fn terminating_has_no_question_mark() {
        assert_eq!(format_trunc(&rat(1, 2), 10), (false, "0.5".into()));
        assert_eq!(format_trunc(&rat(1, 8), 10), (false, "0.125".into()));
    }

    #[test]
    fn truncates_never_rounds() {
        // 2/3 = 0.6666…7 — the 11th digit (6) must be dropped, not rounded up.
        assert_eq!(
            format_trunc(&rat(2, 3), 10),
            (false, "0.6666666666?".into())
        );
    }

    #[test]
    fn negative_reports_sign_and_magnitude() {
        // Caller wraps a negative as `(- …)`; the body is the magnitude.
        assert_eq!(
            format_trunc(&rat(-1, 3), 10),
            (true, "0.3333333333?".into())
        );
    }

    #[test]
    fn integer_part_and_precision_zero() {
        // A value with an integer part, precision 4.
        assert_eq!(format_trunc(&rat(7, 3), 4), (false, "2.3333?".into()));
    }

    #[test]
    fn exactly_precision_digits_then_stop() {
        // 1/16 = 0.0625 terminates in 4 digits → no `?` even at precision 10.
        assert_eq!(format_trunc(&rat(1, 16), 10), (false, "0.0625".into()));
    }
}
