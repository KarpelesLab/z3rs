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
use puremp::{Float, Int, Rational, RoundingMode};

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

#[cfg(test)]
mod tests {
    use super::format_trunc;
    use puremp::{Int, Rational};

    fn rat(n: i64, d: i64) -> Rational {
        Rational::new(Int::from_i64(n), Int::from_i64(d))
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
