//! A minimal SMT-LIB 2 front end — the QF_UF subset of `z3/src/cmd_context` +
//! `z3/src/parsers/smt2` (Z3 4.17.0, MIT).
//!
//! Supports: `set-logic`/`set-info`/`set-option` (ignored), `declare-sort`
//! (arity 0), `declare-fun`, `declare-const`, `assert`, `check-sat`,
//! `get-value`, `get-model`, `push`/`pop`/`reset`, and `exit`; the
//! `Bool`/`Int`/`Real` sorts, integer and decimal numerals, the core Boolean
//! operators, equality/`distinct`, `ite`, `let`, linear arithmetic
//! (`+ - * / <= < >= >`, `div`/`mod`/`abs`/`to_real`/`to_int`, with constant
//! folding), uninterpreted functions, arrays (`(Array I E)`, `select`, `store`,
//! `(as const …)`), and bit-vectors (`(_ BitVec n)`, `#x`/`#b`/`(_ bvN w)`
//! literals, `bvand/bvor/bvxor/bvnot`, `bvadd/bvsub/bvneg`,
//! `bvult/bvule/bvugt/bvuge`). Runs QF_UF / QF_LRA / QF_LIA / QF_A through
//! [`crate::smt::check_model`] and QF_BV through [`crate::smt::check_bv`]
//! (bit-blasting), and reports models via `get-value`/`get-model`.
//! Term-level (non-Boolean) `ite`s are lifted to fresh constants and the array
//! read-over-write axioms are instantiated before solving, so the theory reasons
//! about them exactly. (Nonlinear terms remain opaque — a known incompleteness
//! pending `nlsat`.)

use alloc::boxed::Box;
use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::{String, ToString};
use alloc::vec::Vec;

use puremp::{Int, Rational};

use crate::ast::AstId;
use crate::ast::arith::ArithOp;
use crate::ast::manager::AstManager;
use crate::rewriter::substitute;
use crate::smt::{
    Constraint, LinExpr, Model, OptOutcome, Rel, SmtResult, Value, arith_optimize, ast_to_lin,
    check_bv_model, check_model, feasible, linear_constraints, project, substitute_lin,
};

/// The result of optimizing a real-valued objective.
enum RealOpt {
    /// A proven-exact attained optimum.
    Attained(Rational),
    /// A strict supremum/infimum (the bound value, not attained).
    Supremum(Rational),
    /// Unbounded in the optimizing direction.
    Unbounded,
    /// Not determined exactly (non-linear or verification failed).
    Unknown,
}

/// Render a rational as an SMT-LIB real term always keeping the fractional part
/// (`n.0`, `(- n.0)`, `(/ p.0 q.0)`), matching z3's epsilon expressions.
fn render_real(r: &Rational) -> String {
    let real = |n: &Int| -> String {
        if *n < Int::from(0) {
            alloc::format!("(- {}.0)", n.abs())
        } else {
            alloc::format!("{n}.0")
        }
    };
    if r.is_integer() {
        real(r.numerator())
    } else {
        alloc::format!("(/ {} {})", real(r.numerator()), real(r.denominator()))
    }
}

/// Render a rational as an SMT-LIB real term (`n.0`, `(- n.0)`, or `(/ p.0 q.0)`).
fn render_rational(r: &Rational) -> String {
    let real = |n: &Int| -> String {
        if *n < Int::from(0) {
            alloc::format!("(- {}.0)", n.abs())
        } else {
            alloc::format!("{n}.0")
        }
    };
    if r.is_integer() {
        // z3 prints an integer-valued real without the fractional part.
        render_int(&r.numerator().clone())
    } else {
        alloc::format!("(/ {} {})", real(r.numerator()), real(r.denominator()))
    }
}

/// The result of optimizing one objective.
enum OptResult {
    /// The proven optimal integer value.
    Optimum(Int),
    /// The objective is unbounded in the optimizing direction.
    Unbounded,
    /// Could not determine within budget.
    Unknown,
}

/// Substitute sort-macro parameters (atoms) by their argument s-expressions in
/// a `define-sort` body.
fn subst_sort(body: &SExpr, subst: &[(String, SExpr)]) -> SExpr {
    match body {
        SExpr::Atom(a) => subst
            .iter()
            .find(|(p, _)| p == a)
            .map(|(_, arg)| arg.clone())
            .unwrap_or_else(|| body.clone()),
        SExpr::List(l) => SExpr::List(l.iter().map(|e| subst_sort(e, subst)).collect()),
    }
}

/// The `(exponent bits, significand bits)` of a named floating-point format.
fn fp_format(name: &str) -> Option<(u32, u32)> {
    match name {
        "Float16" => Some((5, 11)),
        "Float32" => Some((8, 24)),
        "Float64" => Some((11, 53)),
        "Float128" => Some((15, 113)),
        _ => None,
    }
}

/// Whether `name` is a `RoundingMode` constant.
fn is_rm_name(name: &str) -> bool {
    matches!(
        name,
        "RNE"
            | "RNA"
            | "RTP"
            | "RTN"
            | "RTZ"
            | "roundNearestTiesToEven"
            | "roundNearestTiesToAway"
            | "roundTowardPositive"
            | "roundTowardNegative"
            | "roundTowardZero"
    )
}

/// Left-fold a non-empty list of regexes with a binary combinator.
fn fold_regex(mut parts: Vec<Regex>, f: impl Fn(Regex, Regex) -> Regex) -> Regex {
    let mut acc = parts.remove(0);
    for p in parts {
        acc = f(acc, p);
    }
    acc
}

/// A Rust string from a slice of Unicode code points.
fn code_points_to_string(cps: &[u32]) -> String {
    cps.iter().filter_map(|&c| char::from_u32(c)).collect()
}

/// An atom of a word equation for the Nielsen transformation: either a concrete
/// character or a string variable (identified by a small stable id).
#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
enum WAtom {
    Char(u32),
    Var(u32),
}

/// Fold a Boolean string predicate over literal operands' code points.
fn fold_string_pred(op: &str, parts: &[Vec<u32>]) -> bool {
    let (a, b) = (&parts[0], &parts[1]);
    match op {
        // (str.contains s sub): does `s` (=a) contain `sub` (=b)?
        "str.contains" => a.windows(b.len().max(1)).any(|w| w == b.as_slice()) || b.is_empty(),
        // (str.prefixof s t): is `s` (=a) a prefix of `t` (=b)?
        "str.prefixof" => a.len() <= b.len() && b[..a.len()] == a[..],
        // (str.suffixof s t): is `s` (=a) a suffix of `t` (=b)?
        "str.suffixof" => a.len() <= b.len() && b[b.len() - a.len()..] == a[..],
        // Lexicographic (code-point) order.
        "str.<" => a < b,
        "str.<=" => a <= b,
        _ => false,
    }
}

/// First index ≥ `from` at which `sub` occurs contiguously in `seq` (elements
/// compared by their hash-consed id). `None` if absent. Empty `sub` matches at
/// `from` (clamped to the length).
fn find_sub(seq: &[AstId], sub: &[AstId], from: usize) -> Option<usize> {
    if sub.is_empty() {
        return Some(from.min(seq.len()));
    }
    if sub.len() > seq.len() {
        return None;
    }
    (from..=seq.len() - sub.len()).find(|&i| seq[i..i + sub.len()] == sub[..])
}

/// Replace the first contiguous occurrence of `from` in `seq` with `to`.
fn replace_first_seq(seq: &[AstId], from: &[AstId], to: &[AstId]) -> Vec<AstId> {
    match find_sub(seq, from, 0) {
        Some(i) if !from.is_empty() => {
            let mut out = seq[..i].to_vec();
            out.extend_from_slice(to);
            out.extend_from_slice(&seq[i + from.len()..]);
            out
        }
        _ => seq.to_vec(),
    }
}

/// `2^w` as an arbitrary-precision integer.
fn pow2(w: u32) -> Int {
    let mut r = Int::from(1);
    let two = Int::from(2);
    for _ in 0..w {
        r = r.mul(&two);
    }
    r
}

/// `(str.replace_all s from to)` — replace every non-overlapping occurrence.
fn replace_all(s: &[u32], from: &[u32], to: &[u32]) -> String {
    if from.is_empty() || from.len() > s.len() {
        return code_points_to_string(s);
    }
    let mut out: Vec<u32> = Vec::new();
    let mut i = 0;
    while i < s.len() {
        if i + from.len() <= s.len() && s[i..i + from.len()] == from[..] {
            out.extend_from_slice(to);
            i += from.len();
        } else {
            out.push(s[i]);
            i += 1;
        }
    }
    code_points_to_string(&out)
}

/// `(str.replace s from to)` — replace the first occurrence of `from` in `s`.
fn replace_first(s: &[u32], from: &[u32], to: &[u32]) -> String {
    if from.is_empty() {
        let mut out = to.to_vec();
        out.extend_from_slice(s);
        return code_points_to_string(&out);
    }
    if from.len() <= s.len() {
        for i in 0..=s.len() - from.len() {
            if s[i..i + from.len()] == from[..] {
                let mut out = s[..i].to_vec();
                out.extend_from_slice(to);
                out.extend_from_slice(&s[i + from.len()..]);
                return code_points_to_string(&out);
            }
        }
    }
    code_points_to_string(s)
}

/// Interpret an unsigned `w`-bit value as a two's-complement signed integer.
fn to_signed(v: &Int, w: u32) -> Int {
    if w == 0 {
        return v.clone();
    }
    let half = Int::from(2).pow(w - 1);
    if *v >= half {
        v.sub(&Int::from(2).pow(w))
    } else {
        v.clone()
    }
}

/// Render an integer as an SMT-LIB term (`n` or `(- n)`).
fn render_int(v: &Int) -> String {
    if *v < Int::from(0) {
        alloc::format!("(- {})", v.abs())
    } else {
        alloc::format!("{v}")
    }
}
use crate::util::symbol::Symbol;

/// Parse an SMT-LIB numeral: `42` → `(Int, 42)`, `1.5` → `(Real, 3/2)`.
fn parse_numeral(s: &str) -> Option<(Rational, bool)> {
    // z3 leniently accepts a negative literal such as `-1` or `-2.5` (strict
    // SMT-LIB writes these as `(- 1)`); accept it too for compatibility.
    if let Some(rest) = s.strip_prefix('-')
        && !rest.is_empty()
    {
        let (r, is_int) = parse_numeral(rest)?;
        return Some((r.neg(), is_int));
    }
    let is_digits = |t: &str| !t.is_empty() && t.bytes().all(|b| b.is_ascii_digit());
    if is_digits(s) {
        let i = Int::from_str_radix(s, 10).ok()?;
        return Some((Rational::from_integer(i), true));
    }
    let (int_part, frac_part) = s.split_once('.')?;
    let ip = if int_part.is_empty() { "0" } else { int_part };
    if !is_digits(ip) || !is_digits(frac_part) {
        return None;
    }
    // value = intpart.frac = (ip·10^k + frac) / 10^k
    let denom_str = alloc::format!("1{}", "0".repeat(frac_part.len()));
    let denom = Int::from_str_radix(&denom_str, 10).ok()?;
    let ip_i = Int::from_str_radix(ip, 10).ok()?;
    let frac_i = Int::from_str_radix(frac_part, 10).ok()?;
    let num = &(&ip_i * &denom) + &frac_i;
    Some((Rational::new(num, denom), false))
}

/// A rational from a small integer.
fn rat(n: i64) -> Rational {
    Rational::from_integer(Int::from(n))
}

/// The Boolean "the sign bit of the bit-vector `x` is set".
fn bv_sign(m: &mut AstManager, x: AstId) -> AstId {
    let n = m.bv_sort_width(m.get_sort(x)).expect("bv_sign: not a bv");
    let msb = m.mk_bv_extract(n - 1, n - 1, x);
    let one = m.mk_bv(1, 1);
    m.mk_eq(msb, one)
}

/// `|x|` as a bit-vector: `ite(sign, -x, x)`.
fn bv_abs(m: &mut AstManager, x: AstId) -> AstId {
    let s = bv_sign(m, x);
    let neg = m.mk_bvneg(x);
    m.mk_ite(s, neg, x)
}

/// `(bvsdiv s t)` — signed division (round toward zero), per the SMT-LIB theory
/// definition in terms of `bvudiv`/`bvneg` and the operand signs.
/// Zero-extend `a` by `k` high bits.
fn zero_ext(m: &mut AstManager, a: AstId, k: u32) -> AstId {
    if k == 0 {
        return a;
    }
    let z = m.mk_bv(0, k);
    m.mk_bv_concat(z, a)
}

/// Sign-extend `a` (width `w`) by `k` high bits.
fn sign_ext(m: &mut AstManager, a: AstId, k: u32, w: u32) -> AstId {
    if k == 0 {
        return a;
    }
    let sign = m.mk_bv_extract(w - 1, w - 1, a);
    let mut top = sign;
    for _ in 1..k {
        top = m.mk_bv_concat(top, sign);
    }
    m.mk_bv_concat(top, a)
}

/// The most-significant (sign) bit of `a` equals `#b1`.
fn msb_set(m: &mut AstManager, a: AstId, w: u32) -> AstId {
    let s = m.mk_bv_extract(w - 1, w - 1, a);
    let one = m.mk_bv(1, 1);
    m.mk_eq(s, one)
}

/// Bit-vector overflow predicates (Bool), matching z3's `bvXovo` operators.
fn bv_overflow(m: &mut AstManager, op: &str, a: AstId, b: AstId, w: u32) -> AstId {
    match op {
        // Unsigned add: carry out of the (w+1)-bit sum.
        "bvuaddo" => {
            let (za, zb) = (zero_ext(m, a, 1), zero_ext(m, b, 1));
            let s = m.mk_bvadd(za, zb);
            let top = m.mk_bv_extract(w, w, s);
            let one = m.mk_bv(1, 1);
            m.mk_eq(top, one)
        }
        // Signed add: operands same sign, result differs.
        "bvsaddo" => {
            let (sa, sb) = (msb_set(m, a, w), msb_set(m, b, w));
            let sum = m.mk_bvadd(a, b);
            let ssum = msb_set(m, sum, w);
            let same = m.mk_eq(sa, sb);
            let ne = m.mk_eq(ssum, sa);
            let ne = m.mk_not(ne);
            m.mk_and(&[same, ne])
        }
        // Unsigned subtract: borrow, i.e. a <u b.
        "bvusubo" => m.mk_bvult(a, b),
        // Signed subtract: operands differ in sign, result differs from a.
        "bvssubo" => {
            let (sa, sb) = (msb_set(m, a, w), msb_set(m, b, w));
            let diff = m.mk_bvsub(a, b);
            let sd = msb_set(m, diff, w);
            let opp = m.mk_eq(sa, sb);
            let opp = m.mk_not(opp);
            let ne = m.mk_eq(sd, sa);
            let ne = m.mk_not(ne);
            m.mk_and(&[opp, ne])
        }
        // Signed negation: a is the minimum value (100…0).
        "bvnego" => {
            let lo = m.mk_bv(0, w - 1);
            let hi = m.mk_bv(1, 1);
            let min = m.mk_bv_concat(hi, lo);
            m.mk_eq(a, min)
        }
        // Unsigned multiply: high `w` bits of the 2w-bit product are nonzero.
        "bvumulo" => {
            let (za, zb) = (zero_ext(m, a, w), zero_ext(m, b, w));
            let p = m.mk_bvmul(za, zb);
            let hi = m.mk_bv_extract(2 * w - 1, w, p);
            let zero = m.mk_bv(0, w);
            let eqz = m.mk_eq(hi, zero);
            m.mk_not(eqz)
        }
        // Signed multiply: the top w+1 bits of the 2w-bit product are not all
        // equal (not a clean sign extension of the low w bits).
        "bvsmulo" => {
            let (sa2, sb2) = (sign_ext(m, a, w, w), sign_ext(m, b, w, w));
            let p = m.mk_bvmul(sa2, sb2);
            let hi = m.mk_bv_extract(2 * w - 1, w - 1, p); // w+1 bits
            let zero = m.mk_bv(0, w + 1);
            let ones = m.mk_bvnot(zero);
            let is0 = m.mk_eq(hi, zero);
            let is1 = m.mk_eq(hi, ones);
            let clean = m.mk_or(&[is0, is1]);
            m.mk_not(clean)
        }
        // Signed division: only INT_MIN / -1 overflows.
        "bvsdivo" => {
            let lo = m.mk_bv(0, w - 1);
            let hi = m.mk_bv(1, 1);
            let min = m.mk_bv_concat(hi, lo);
            let a_min = m.mk_eq(a, min);
            let zero = m.mk_bv(0, w);
            let neg1 = m.mk_bvnot(zero);
            let b_neg1 = m.mk_eq(b, neg1);
            m.mk_and(&[a_min, b_neg1])
        }
        _ => m.mk_false(),
    }
}

fn bv_sdiv(m: &mut AstManager, s: AstId, t: AstId) -> AstId {
    let (ss, st) = (bv_sign(m, s), bv_sign(m, t));
    let (ns, nt) = (m.mk_bvneg(s), m.mk_bvneg(t));
    let d_pp = m.mk_bvudiv(s, t); // ¬ss ∧ ¬st
    let u_np = m.mk_bvudiv(ns, t);
    let d_np = m.mk_bvneg(u_np); // ss ∧ ¬st
    let u_pn = m.mk_bvudiv(s, nt);
    let d_pn = m.mk_bvneg(u_pn); // ¬ss ∧ st
    let d_nn = m.mk_bvudiv(ns, nt); // ss ∧ st
    let ss_true = m.mk_ite(st, d_nn, d_np);
    let ss_false = m.mk_ite(st, d_pn, d_pp);
    m.mk_ite(ss, ss_true, ss_false)
}

/// `(bvsrem s t)` — signed remainder (sign follows the dividend `s`).
fn bv_srem(m: &mut AstManager, s: AstId, t: AstId) -> AstId {
    let (ss, st) = (bv_sign(m, s), bv_sign(m, t));
    let (ns, nt) = (m.mk_bvneg(s), m.mk_bvneg(t));
    let r_pp = m.mk_bvurem(s, t);
    let u_np = m.mk_bvurem(ns, t);
    let r_np = m.mk_bvneg(u_np);
    let r_pn = m.mk_bvurem(s, nt);
    let u_nn = m.mk_bvurem(ns, nt);
    let r_nn = m.mk_bvneg(u_nn);
    let ss_true = m.mk_ite(st, r_nn, r_np);
    let ss_false = m.mk_ite(st, r_pn, r_pp);
    m.mk_ite(ss, ss_true, ss_false)
}

/// `(bvsmod s t)` — signed modulo (sign follows the divisor `t`).
fn bv_smod(m: &mut AstManager, s: AstId, t: AstId) -> AstId {
    let (ss, st) = (bv_sign(m, s), bv_sign(m, t));
    let abs_s = bv_abs(m, s);
    let abs_t = bv_abs(m, t);
    let u = m.mk_bvurem(abs_s, abs_t);
    let neg_u = m.mk_bvneg(u);
    let n = m.bv_sort_width(m.get_sort(s)).expect("bvsmod: not a bv");
    let zero = m.mk_bv(0, n);
    let u_zero = m.mk_eq(u, zero);
    let neg_u_plus_t = m.mk_bvadd(neg_u, t); // ss ∧ ¬st
    let u_plus_t = m.mk_bvadd(u, t); // ¬ss ∧ st
    let ss_true = m.mk_ite(st, neg_u, neg_u_plus_t);
    let ss_false = m.mk_ite(st, u_plus_t, u);
    let nonzero = m.mk_ite(ss, ss_true, ss_false);
    m.mk_ite(u_zero, u, nonzero)
}

/// Parse a bit-vector literal `#x1a` (hex, 4 bits/digit) or `#b101` (binary,
/// 1 bit/digit) into `(value, width)`.
fn parse_bv_literal(s: &str) -> Option<(Int, u32)> {
    if let Some(hex) = s.strip_prefix("#x") {
        if hex.is_empty() || !hex.bytes().all(|b| b.is_ascii_hexdigit()) {
            return None;
        }
        Some((Int::from_str_radix(hex, 16).ok()?, hex.len() as u32 * 4))
    } else if let Some(bin) = s.strip_prefix("#b") {
        if bin.is_empty() || !bin.bytes().all(|b| b == b'0' || b == b'1') {
            return None;
        }
        Some((Int::from_str_radix(bin, 2).ok()?, bin.len() as u32))
    } else {
        None
    }
}

/// The rational values of `args` if *every* one is a numeral, else `None`.
fn all_numerals(m: &AstManager, args: &[AstId]) -> Option<Vec<Rational>> {
    args.iter().map(|&a| m.as_numeral(a)).collect()
}

/// Are all of `args` integer-sorted (so a folded result stays `Int`)?
fn all_int(m: &AstManager, args: &[AstId]) -> bool {
    args.iter().all(|&a| m.is_int_sort(m.get_sort(a)))
}

/// If both terms are integer numerals, return them as [`Int`]s.
fn int_pair(m: &AstManager, a: AstId, b: AstId) -> Option<(Int, Int)> {
    let ai = m.as_numeral(a)?.to_integer()?;
    let bi = m.as_numeral(b)?.to_integer()?;
    Some((ai, bi))
}

/// Euclidean division and remainder (SMT-LIB `div`/`mod`): `a = b·q + r` with
/// `0 ≤ r < |b|`. `b` must be non-zero.
fn euclid_div_mod(a: &Int, b: &Int) -> (Int, Int) {
    let (q, r) = a.div_rem_trunc(b); // truncated: r has the sign of a
    if r < Int::from(0) {
        if *b > Int::from(0) {
            (&q - &Int::from(1), &r + b)
        } else {
            (&q + &Int::from(1), &r - b)
        }
    } else {
        (q, r)
    }
}

/// The SMT-LIB response word for a verdict.
fn verdict_word(res: SmtResult) -> &'static str {
    match res {
        SmtResult::Sat => "sat",
        SmtResult::Unsat => "unsat",
        SmtResult::Unknown => "unknown",
    }
}

/// The content of an SMT-LIB string literal token (`"…"`), with the surrounding
/// quotes removed and doubled `""` collapsed to a single quote. Non-string tokens
/// are returned unchanged.
fn unquote_string(tok: &str) -> String {
    if tok.len() >= 2 && tok.starts_with('"') && tok.ends_with('"') {
        tok[1..tok.len() - 1].replace("\"\"", "\"")
    } else {
        tok.to_string()
    }
}

/// The `:named` label of an assertion written `(! term :named name …)`, if any.
fn named_label(s: &SExpr) -> Option<String> {
    let SExpr::List(l) = s else { return None };
    if l.first().and_then(|h| match h {
        SExpr::Atom(a) => Some(a.as_str()),
        _ => None,
    }) != Some("!")
    {
        return None;
    }
    // Scan for `:named <name>`.
    let mut it = l[1..].iter();
    while let Some(part) = it.next() {
        if let SExpr::Atom(k) = part
            && k == ":named"
            && let Some(SExpr::Atom(name)) = it.next()
        {
            return Some(name.clone());
        }
    }
    None
}

/// Working state for [`Context::lift_terms`]: the defining constraints collected
/// so far, a memo of already-lifted subterms, and a memo of `(a, divisor)` pairs
/// sharing a `(quotient, remainder)`.
struct LiftCtx {
    defs: Vec<AstId>,
    cache: BTreeMap<AstId, AstId>,
    dm: BTreeMap<(AstId, AstId), (AstId, AstId)>,
    /// Memo of `(to_int a)` arguments → their integer result constant.
    toint: BTreeMap<AstId, AstId>,
}

/// An s-expression.
#[derive(Clone, Debug, PartialEq, Eq)]
enum SExpr {
    Atom(String),
    List(Vec<SExpr>),
}

/// Run an SMT-LIB `script`, returning one response line per `check-sat`
/// (`"sat"`, `"unsat"`, or `"unknown"`). Accepts both SMT-LIB 2 command scripts
/// and the older SMT-LIB 1.2 `(benchmark …)` format.
pub fn run(script: &str) -> Result<Vec<String>, String> {
    let forms = parse(script)?;
    // SMT-LIB 1.2: a single top-level (benchmark …) form.
    if let [SExpr::List(l)] = forms.as_slice()
        && matches!(l.first(), Some(SExpr::Atom(a)) if a == "benchmark")
    {
        return run_v1(l);
    }
    let mut ctx = Context::new();
    let mut out = Vec::new();
    for form in forms {
        if let Some(resp) = ctx.command(&form)? {
            out.push(resp);
        }
    }
    Ok(out)
}

/// A persistent SMT-LIB2 session. Unlike [`run`], declarations, assertions, the
/// push/pop stack, and options carry across [`Session::eval`] calls, so a caller
/// can drive the solver incrementally (the C API's solver object builds on it).
pub struct Session {
    ctx: Context,
}

impl Default for Session {
    fn default() -> Session {
        Session::new()
    }
}

impl Session {
    /// A fresh session with no declarations or assertions.
    pub fn new() -> Session {
        Session {
            ctx: Context::new(),
        }
    }

    /// Interpret more SMT-LIB2 `script` against the accumulated state, returning
    /// one response line per command that produces output (e.g. `check-sat`,
    /// `get-value`).
    pub fn eval(&mut self, script: &str) -> Result<Vec<String>, String> {
        let forms = parse(script)?;
        let mut out = Vec::new();
        for form in forms {
            if let Some(resp) = self.ctx.command(&form)? {
                out.push(resp);
            }
        }
        Ok(out)
    }
}

/// Interpret an SMT-LIB 1.2 `(benchmark name :attr value …)`: declare its
/// sorts/functions/predicates, assert the assumptions and formula, and return
/// the single `check-sat` verdict. Quantifiers are out of scope.
fn run_v1(l: &[SExpr]) -> Result<Vec<String>, String> {
    let mut ctx = Context::new();
    let mut asserts: Vec<SExpr> = Vec::new();
    // l[0] = "benchmark", l[1] = name, then :keyword value pairs.
    let mut i = 2;
    while i < l.len() {
        let key = Context::sym(&l[i])?.to_string();
        let val = l
            .get(i + 1)
            .ok_or_else(|| alloc::format!("benchmark: {key} has no value"))?;
        match key.as_str() {
            ":extrasorts" => {
                for s in as_list(val)? {
                    let name = Context::sym(s)?.to_string();
                    let sort = ctx.m.mk_uninterpreted_sort(Symbol::new(&name));
                    ctx.sorts.insert(name, sort);
                }
            }
            ":extrafuns" => {
                for f in as_list(val)? {
                    // (name dom… range)
                    let parts = as_list(f)?;
                    let name = Context::sym(&parts[0])?.to_string();
                    let range = ctx.resolve_sort(&parts[parts.len() - 1])?;
                    let domain: Vec<AstId> = parts[1..parts.len() - 1]
                        .iter()
                        .map(|s| ctx.resolve_sort(s))
                        .collect::<Result<_, _>>()?;
                    let d = ctx.m.mk_func_decl(Symbol::new(&name), &domain, range);
                    ctx.funcs.insert(name, d);
                }
            }
            ":extrapreds" => {
                for p in as_list(val)? {
                    // (name dom…) — range Bool
                    let parts = as_list(p)?;
                    let name = Context::sym(&parts[0])?.to_string();
                    let bool_s = ctx.m.mk_bool_sort();
                    let domain: Vec<AstId> = parts[1..]
                        .iter()
                        .map(|s| ctx.resolve_sort(s))
                        .collect::<Result<_, _>>()?;
                    let d = ctx.m.mk_func_decl(Symbol::new(&name), &domain, bool_s);
                    ctx.funcs.insert(name, d);
                }
            }
            ":assumption" | ":formula" => asserts.push(v1_to_v2(val)),
            // :logic, :status, :notes, :source, :difficulty, :category, … ignored.
            _ => {}
        }
        i += 2;
    }
    for a in &asserts {
        let t = ctx.term(a)?;
        ctx.assertions.push(t);
    }
    let goal = ctx.goal();
    let (res, _) = ctx.decide(goal);
    Ok(alloc::vec![verdict_word(res).to_string()])
}

/// The integer value following the keyword `key` in a command's tail, if any
/// (e.g. `:weight 5`).
fn attr_int(list: &[SExpr], key: &str) -> Option<i64> {
    let pos = list
        .iter()
        .position(|s| matches!(s, SExpr::Atom(a) if a == key))?;
    match list.get(pos + 1) {
        Some(SExpr::Atom(a)) => a.parse().ok(),
        _ => None,
    }
}

/// If `s` is a top-level `(forall …)` or `(exists …)`, its keyword.
/// Peel nested `forall` binders (and transparent `!` annotations) from a
/// quantifier body, returning the extra binders and the innermost body. So
/// `∀y.∀z. φ` contributes `[y, z]` and `φ`.
/// Substitute atom names by S-expressions throughout `e` (no capture avoidance —
/// used for Skolemization, where the replacements are fresh applications).
fn subst_sexpr(e: &SExpr, subst: &[(String, SExpr)]) -> SExpr {
    match e {
        SExpr::Atom(a) => {
            for (n, r) in subst {
                if n == a {
                    return r.clone();
                }
            }
            e.clone()
        }
        SExpr::List(l) => SExpr::List(l.iter().map(|x| subst_sexpr(x, subst)).collect()),
    }
}

fn flatten_foralls(body: &SExpr) -> (Vec<SExpr>, SExpr) {
    let mut extra: Vec<SExpr> = Vec::new();
    let mut cur = body.clone();
    loop {
        let step = match &cur {
            SExpr::List(l) if l.len() >= 2 && matches!(&l[0], SExpr::Atom(a) if a == "!") => {
                Some(l[1].clone())
            }
            SExpr::List(l) if l.len() == 3 && matches!(&l[0], SExpr::Atom(a) if a == "forall") => {
                if let SExpr::List(bs) = &l[1] {
                    extra.extend(bs.iter().cloned());
                    Some(l[2].clone())
                } else {
                    None
                }
            }
            _ => None,
        };
        match step {
            Some(n) => cur = n,
            None => break,
        }
    }
    (extra, cur)
}

fn top_level_quantifier(s: &SExpr) -> Option<&'static str> {
    if let SExpr::List(l) = s
        && l.len() == 3
        && let SExpr::Atom(h) = &l[0]
    {
        return match h.as_str() {
            "forall" => Some("forall"),
            "exists" => Some("exists"),
            _ => None,
        };
    }
    None
}

/// The elements of a list s-expression.
fn as_list(s: &SExpr) -> Result<&[SExpr], String> {
    match s {
        SExpr::List(l) => Ok(l),
        SExpr::Atom(_) => Err("expected a list".to_string()),
    }
}

/// Rewrite an SMT-LIB 1.2 formula into the equivalent SMT-LIB 2 s-expression:
/// `implies`→`=>`, `if_then_else`→`ite`, `iff`→`=`, and the single-binding
/// `(let (v t) b)` / `(flet (v f) b)` into `(let ((v t)) b)`.
fn v1_to_v2(s: &SExpr) -> SExpr {
    let SExpr::List(l) = s else {
        return s.clone();
    };
    let head = match l.first() {
        Some(SExpr::Atom(a)) => a.as_str(),
        _ => return SExpr::List(l.iter().map(v1_to_v2).collect()),
    };
    let atom = |s: &str| SExpr::Atom(String::from(s));
    match head {
        "implies" if l.len() == 3 => {
            SExpr::List(alloc::vec![atom("=>"), v1_to_v2(&l[1]), v1_to_v2(&l[2])])
        }
        "if_then_else" if l.len() == 4 => SExpr::List(alloc::vec![
            atom("ite"),
            v1_to_v2(&l[1]),
            v1_to_v2(&l[2]),
            v1_to_v2(&l[3]),
        ]),
        "iff" if l.len() == 3 => {
            SExpr::List(alloc::vec![atom("="), v1_to_v2(&l[1]), v1_to_v2(&l[2])])
        }
        "let" | "flet" if l.len() == 3 => {
            // (let (v t) body) → (let ((v t)) body)
            if let SExpr::List(bind) = &l[1]
                && bind.len() == 2
            {
                let inner = SExpr::List(alloc::vec![bind[0].clone(), v1_to_v2(&bind[1])]);
                let binds = SExpr::List(alloc::vec![inner]);
                return SExpr::List(alloc::vec![atom("let"), binds, v1_to_v2(&l[2])]);
            }
            SExpr::List(l.iter().map(v1_to_v2).collect())
        }
        _ => SExpr::List(l.iter().map(v1_to_v2).collect()),
    }
}

// --- tokenizer + parser ---------------------------------------------------

fn tokenize(input: &str) -> Vec<String> {
    let mut toks = Vec::new();
    let mut chars = input.chars().peekable();
    while let Some(&c) = chars.peek() {
        match c {
            ';' => {
                // comment to end of line
                for c in chars.by_ref() {
                    if c == '\n' {
                        break;
                    }
                }
            }
            c if c.is_whitespace() => {
                chars.next();
            }
            '(' | ')' => {
                toks.push(c.to_string());
                chars.next();
            }
            '{' => {
                // SMT-LIB v1 annotation block `{ … }` (e.g. :source); depth-matched
                // and kept as one opaque token.
                chars.next();
                let mut s = String::from("{");
                let mut depth = 1;
                for c in chars.by_ref() {
                    if c == '{' {
                        depth += 1;
                    } else if c == '}' {
                        depth -= 1;
                        if depth == 0 {
                            break;
                        }
                    }
                    s.push(c);
                }
                s.push('}');
                toks.push(s);
            }
            '"' => {
                // String literal "…"; a doubled "" is an embedded quote. Kept
                // with its surrounding quotes so it stays a single, recognizable
                // token.
                chars.next(); // opening quote
                let mut s = String::from("\"");
                while let Some(&c) = chars.peek() {
                    chars.next();
                    if c == '"' {
                        if chars.peek() == Some(&'"') {
                            s.push('"');
                            s.push('"');
                            chars.next();
                            continue;
                        }
                        break;
                    }
                    s.push(c);
                }
                s.push('"'); // closing quote
                toks.push(s);
            }
            '|' => {
                // quoted symbol |...|
                chars.next();
                let mut s = String::new();
                for c in chars.by_ref() {
                    if c == '|' {
                        break;
                    }
                    s.push(c);
                }
                toks.push(s);
            }
            _ => {
                let mut s = String::new();
                while let Some(&c) = chars.peek() {
                    if c.is_whitespace() || c == '(' || c == ')' || c == ';' {
                        break;
                    }
                    s.push(c);
                    chars.next();
                }
                toks.push(s);
            }
        }
    }
    toks
}

fn parse(input: &str) -> Result<Vec<SExpr>, String> {
    let toks = tokenize(input);
    let mut pos = 0;
    let mut forms = Vec::new();
    while pos < toks.len() {
        forms.push(parse_one(&toks, &mut pos)?);
    }
    Ok(forms)
}

/// Render an s-expression back to its textual form (used to echo `get-value`
/// query terms).
fn render_sexpr(s: &SExpr) -> String {
    match s {
        SExpr::Atom(a) => a.clone(),
        SExpr::List(l) => {
            let inner: Vec<String> = l.iter().map(render_sexpr).collect();
            alloc::format!("({})", inner.join(" "))
        }
    }
}

fn parse_one(toks: &[String], pos: &mut usize) -> Result<SExpr, String> {
    let tok = &toks[*pos];
    *pos += 1;
    match tok.as_str() {
        "(" => {
            let mut list = Vec::new();
            loop {
                if *pos >= toks.len() {
                    return Err("unexpected end of input (missing `)`)".to_string());
                }
                if toks[*pos] == ")" {
                    *pos += 1;
                    break;
                }
                list.push(parse_one(toks, pos)?);
            }
            Ok(SExpr::List(list))
        }
        ")" => Err("unexpected `)`".to_string()),
        atom => Ok(SExpr::Atom(atom.to_string())),
    }
}

// --- interpreter ----------------------------------------------------------

/// A saved assertion-stack level (`push` records one; `pop` restores it),
/// capturing the sizes of the assertion and declaration lists so that `pop`
/// discards everything asserted or declared since the matching `push` — SMT-LIB
/// scopes declarations, not just assertions.
struct Scope {
    assertions: usize,
    decls: usize,
    sorts: usize,
    universals: usize,
}

struct Context {
    m: AstManager,
    sorts: BTreeMap<String, AstId>,
    funcs: BTreeMap<String, AstId>,
    assertions: Vec<AstId>,
    /// The `:named` label of each assertion (parallel to `assertions`), if any —
    /// used to report an unsat core.
    assert_names: Vec<Option<String>>,
    /// The verdict of the most recent `check-sat`.
    last_verdict: Option<SmtResult>,
    /// Saved scope levels (for `pop` to restore).
    scope_stack: Vec<Scope>,
    /// Active `let`/macro-parameter binding scopes (innermost last).
    scopes: Vec<Vec<(String, AstId)>>,
    /// `define-fun` macros: name → (parameter names, body).
    macros: BTreeMap<String, (Vec<String>, SExpr)>,
    /// Declared constants/functions in declaration order (for `get-model` and
    /// declaration scoping).
    decl_order: Vec<String>,
    /// Declared (uninterpreted) sort names in declaration order, for scoping.
    sort_order: Vec<String>,
    /// The model from the most recent satisfiable `check-sat`, if still current.
    last_model: Option<Model>,
    /// Counter for the fresh constants introduced by term-ITE elimination.
    fresh_counter: u32,
    /// Boolean sentinels standing in for (not-yet-decided) quantified formulas;
    /// a goal that mentions any of these is answered `unknown` (see `decide`).
    quant_atoms: BTreeSet<AstId>,
    /// Enumeration datatypes: sort → its constructor constants. Reasoned about
    /// as a finite uninterpreted sort with distinct elements and a domain axiom.
    enums: BTreeMap<AstId, Vec<AstId>>,
    /// Record/tuple datatypes (a single constructor with fields): sort →
    /// `(constructor decl, selector decls)`. Reasoned about with the
    /// selector-over-constructor and constructor-surjectivity (eta) axioms.
    records: BTreeMap<AstId, (AstId, Vec<AstId>)>,
    /// General datatypes with ≥2 constructors that have fields:
    /// sort → per-constructor `(constructor decl, selector decls, tester decl)`.
    datatypes: BTreeMap<AstId, Vec<(AstId, Vec<AstId>, AstId)>>,
    /// For each recursive datatype, an uninterpreted `depth : DT → Int` used to
    /// enforce acyclicity (a constructor is strictly deeper than its recursive
    /// children, so no term can be its own descendant).
    dt_depth: BTreeMap<AstId, AstId>,
    /// Constructor name → its tester declaration (for `((_ is C) t)`).
    tester_of: BTreeMap<String, AstId>,
    /// Parametric (polymorphic) datatype templates: name → (type parameters,
    /// constructor s-expressions). Monomorphized on use, e.g. `(Pair Int Bool)`.
    param_datatypes: BTreeMap<String, (Vec<String>, Vec<SExpr>)>,
    /// Array `lambda` closures: array term → (bound-variable placeholders, body).
    /// `(select (lambda ((x S)) body) i)` beta-reduces to `body[x:=i]`.
    lambdas: BTreeMap<AstId, (Vec<AstId>, AstId)>,
    /// Array `(_ map f)` combinators: array term → (function name, source arrays).
    /// `(select ((_ map f) a…) i)` rewrites to `f((select a i)…)`.
    maps: BTreeMap<AstId, (String, Vec<AstId>)>,
    /// `(_ as-array f)` values: array term → the function declaration.
    /// `(select (_ as-array f) i)` rewrites to `f(i)`.
    as_arrays: BTreeMap<AstId, AstId>,
    /// Top-level universal (`forall`) assertions as `(bound-var placeholders,
    /// body)`; instantiated over ground terms at each `check-sat`.
    universals: Vec<(Vec<AstId>, AstId)>,
    /// Optimization objectives as `(term, maximize?, display text)`.
    objectives: Vec<(AstId, bool, String)>,
    /// The rendered optimal value of each objective after the last `check-sat`.
    objective_values: Vec<String>,
    /// Soft constraints (`assert-soft`) as `(penalty indicator bool, weight)`;
    /// `check-sat` minimizes the total weight of the violated ones (MaxSAT).
    soft: Vec<(AstId, i64)>,
    /// The interned `String` sort, once used.
    string_sort: Option<AstId>,
    /// String literal text → its distinct constant of the `String` sort.
    str_lits: BTreeMap<String, AstId>,
    /// The `str.len : String → Int` function declaration, once used.
    str_len_decl: Option<AstId>,
    /// Symbolic (non-constant-folded) string-producing operations. A goal that
    /// mentions any is answered `unknown` (their word semantics aren't solved),
    /// keeping every definite verdict sound.
    str_symbolic: BTreeSet<AstId>,
    /// The concrete `(string var → literal)` assignment from the last successful
    /// string-witness search, so `get-value`/`get-model` report a concrete string
    /// (e.g. `"aaa"`) rather than an uninterpreted placeholder.
    str_witness: Vec<(AstId, AstId)>,
    /// Length links for symbolic string predicates: `(pred_app, longer, shorter)`
    /// asserts `pred_app ⇒ str.len(longer) ≥ str.len(shorter)` — sound for
    /// `str.contains`/`str.prefixof`/`str.suffixof`, and enough to refute e.g.
    /// `str.contains x "a" ∧ str.len x = 0`.
    str_pred_len: Vec<(AstId, AstId, AstId)>,
    /// Constant upper bounds on a string marker's length: `(marker, k)` asserts
    /// `str.len(marker) ≤ k` (e.g. `str.at` yields ≤ 1 character).
    str_len_ub: Vec<(AstId, i64)>,
    /// Each symbolic string marker's declaration → the string op it stands for,
    /// so a candidate assignment can *re-fold* it concretely during the bounded
    /// string-witness search (the `sat` direction).
    str_op_decls: BTreeMap<AstId, String>,
    /// The interned `RegLan` (regular language) sort, once used.
    reglan_sort: Option<AstId>,
    /// Regex terms whose structure is fully constant, for `str.in_re` folding.
    regex_of: BTreeMap<AstId, Regex>,
    /// Parametric sort macros from `define-sort`: name → (params, body).
    sort_defs: BTreeMap<String, (Vec<String>, SExpr)>,
    /// Floating-point sorts `(_ FloatingPoint eb sb)`, keyed by `(eb, sb)`.
    fp_sorts: BTreeMap<(u32, u32), AstId>,
    /// The `RoundingMode` sort, once used.
    rm_sort: Option<AstId>,
    /// Floating-point constants: term → `(raw bits, eb, sb)`. Only `Float64`
    /// `(eb, sb) = (11, 53)` constants are folded (via `f64`); other formats and
    /// symbolic values are gated to a sound `unknown`.
    fp_of: BTreeMap<AstId, (u64, u32, u32)>,
    /// Bit-vector representation of a symbolic FP term (`fp_to_bv`), so equality
    /// and the classification predicates bit-blast through the QF_BV engine.
    fp_bv: BTreeMap<AstId, AstId>,
    /// `(Seq E)` sorts, keyed by element sort.
    seq_sorts: BTreeMap<AstId, AstId>,
    /// Sequence terms with a known element list (built from `seq.unit`/`++`/
    /// `empty`), for structural folding of `seq.len`/`nth`/`at`/`extract`/`=`.
    seq_of: BTreeMap<AstId, Vec<AstId>>,
    /// Canonical empty sequence per sequence sort, so all `(as seq.empty S)`
    /// share one constant and `seq.len(s)=0 ⇒ s=empty` is enforceable.
    seq_empty: BTreeMap<AstId, AstId>,
    /// Symbolic divisor terms from `div`/`mod` (the non-numeral `b` in
    /// `div(a,b)`), collected during lifting so the SAT direction can witness by
    /// enumerating small divisor values.
    symbolic_divisors: BTreeSet<AstId>,
    /// Per symbolic-divisor `div`/`mod` abstraction: `(dividend, divisor, q, r)`
    /// where `q`/`r` are the fresh quotient/remainder. Lets the complete-UNSAT
    /// check reason about the constant-dividend class after lifting has replaced
    /// the div/mod terms with `q`/`r`.
    symbolic_divmod: Vec<(AstId, AstId, AstId, AstId)>,
    /// `seq.len` function declarations (one per element sort), tracked so a
    /// non-negativity axiom can be attached to each application.
    seq_len_decls: BTreeSet<AstId>,
    /// Symbolic `seq.++` markers with their parts, so the additive length axiom
    /// `len(s ++ t) = len(s) + len(t)` can be attached.
    seq_concat: Vec<(AstId, Vec<AstId>)>,
    /// The operation name behind each symbolic sequence marker declaration, so a
    /// marker can be re-folded once its arguments become concrete (witness search).
    seqop_ops: BTreeMap<AstId, String>,
    /// The pre-axiom goal for the string/seq witness (set around `decide`), so the
    /// witness substitutes into a clean formula rather than the axiom-laden one.
    witness_base: Option<AstId>,
    /// Solver options set via `(set-option …)`, retrievable by `(get-option …)`.
    params: crate::util::Params,
    /// Uninterpreted sort *constructors* of arity ≥ 1 from `(declare-sort P n)`.
    /// Each application `(P s…)` monomorphizes to a distinct cached sort.
    sort_ctors: BTreeMap<String, usize>,
}

/// A constant regular expression (the decidable, fully-literal fragment). Used
/// to fold `(str.in_re "literal" r)` by matching.
#[derive(Clone, Debug)]
enum Regex {
    /// Matches exactly this code-point sequence (`str.to_re` of a literal).
    Lit(Vec<u32>),
    /// Any single code point in `[lo, hi]` (`re.range`).
    Range(u32, u32),
    /// Any single code point (`re.allchar`).
    AllChar,
    /// Every string (`re.all`).
    All,
    /// No string (`re.none`).
    None,
    Concat(Box<Regex>, Box<Regex>),
    Union(Box<Regex>, Box<Regex>),
    Inter(Box<Regex>, Box<Regex>),
    /// Complement (`re.comp`): every string the inner regex does *not* match.
    Comp(Box<Regex>),
    Star(Box<Regex>),
}

impl Regex {
    /// The set of end positions after matching `self` in `s` starting at `from`.
    fn ends(&self, s: &[u32], from: usize) -> BTreeSet<usize> {
        let mut out = BTreeSet::new();
        match self {
            Regex::Lit(l) => {
                if from + l.len() <= s.len() && s[from..from + l.len()] == l[..] {
                    out.insert(from + l.len());
                }
            }
            Regex::Range(lo, hi) => {
                if from < s.len() && (*lo..=*hi).contains(&s[from]) {
                    out.insert(from + 1);
                }
            }
            Regex::AllChar => {
                if from < s.len() {
                    out.insert(from + 1);
                }
            }
            Regex::All => {
                for p in from..=s.len() {
                    out.insert(p);
                }
            }
            Regex::None => {}
            Regex::Concat(a, b) => {
                for mid in a.ends(s, from) {
                    out.extend(b.ends(s, mid));
                }
            }
            Regex::Union(a, b) => {
                out.extend(a.ends(s, from));
                out.extend(b.ends(s, from));
            }
            Regex::Inter(a, b) => {
                let ea = a.ends(s, from);
                for p in b.ends(s, from) {
                    if ea.contains(&p) {
                        out.insert(p);
                    }
                }
            }
            Regex::Comp(r) => {
                // s[from..p] matches the complement iff it does not match `r`.
                let er = r.ends(s, from);
                for p in from..=s.len() {
                    if !er.contains(&p) {
                        out.insert(p);
                    }
                }
            }
            Regex::Star(r) => {
                // Reachable end positions by repeating `r` zero or more times;
                // the visited set prevents looping on empty matches.
                out.insert(from);
                let mut frontier = alloc::vec![from];
                while let Some(p) = frontier.pop() {
                    for q in r.ends(s, p) {
                        if out.insert(q) {
                            frontier.push(q);
                        }
                    }
                }
            }
        }
        out
    }

    /// Does `self` match the whole string `s`?
    fn matches(&self, s: &[u32]) -> bool {
        self.ends(s, 0).contains(&s.len())
    }

    /// Which lengths `0..=max` a matching word can have — *exact* for the
    /// supported constructors. `None` when the length set cannot be computed
    /// exactly (`re.inter`/`re.comp`), so callers fall back to a sound `unknown`.
    fn lengths(&self, max: usize) -> Option<Vec<bool>> {
        let mut v = alloc::vec![false; max + 1];
        match self {
            Regex::Lit(l) => {
                if l.len() <= max {
                    v[l.len()] = true;
                }
            }
            Regex::Range(_, _) | Regex::AllChar => {
                if max >= 1 {
                    v[1] = true;
                }
            }
            Regex::All => v.iter_mut().for_each(|b| *b = true),
            Regex::None => {}
            Regex::Concat(a, b) => {
                let (la, lb) = (a.lengths(max)?, b.lengths(max)?);
                for i in 0..=max {
                    if la[i] {
                        for j in 0..=(max - i) {
                            if lb[j] {
                                v[i + j] = true;
                            }
                        }
                    }
                }
            }
            Regex::Union(a, b) => {
                let (la, lb) = (a.lengths(max)?, b.lengths(max)?);
                for i in 0..=max {
                    v[i] = la[i] || lb[i];
                }
            }
            Regex::Star(a) => {
                let la = a.lengths(max)?;
                v[0] = true;
                for i in 0..=max {
                    if v[i] {
                        for u in 1..=(max - i) {
                            if la[u] {
                                v[i + u] = true;
                            }
                        }
                    }
                }
            }
            Regex::Inter(a, b) => {
                // `lengths(A ∩ B) ⊆ lengths(A) ∩ lengths(B)` — a string of length k
                // in the intersection is in both, so the set-intersection is a sound
                // over-approximation (an unknown side is "all lengths").
                match (a.lengths(max), b.lengths(max)) {
                    (Some(la), Some(lb)) => {
                        for i in 0..=max {
                            v[i] = la[i] && lb[i];
                        }
                    }
                    (Some(la), None) => v = la,
                    (None, Some(lb)) => v = lb,
                    (None, None) => return None,
                }
            }
            Regex::Comp(_) => return None,
        }
        Some(v)
    }
}

impl Context {
    fn new() -> Context {
        let mut m = AstManager::new();
        let bool_sort = m.mk_bool_sort();
        let int_sort = m.mk_int_sort();
        let real_sort = m.mk_real_sort();
        let mut sorts = BTreeMap::new();
        sorts.insert("Bool".to_string(), bool_sort);
        sorts.insert("Int".to_string(), int_sort);
        sorts.insert("Real".to_string(), real_sort);
        Context {
            m,
            sorts,
            funcs: BTreeMap::new(),
            assertions: Vec::new(),
            assert_names: Vec::new(),
            last_verdict: None,
            scope_stack: Vec::new(),
            scopes: Vec::new(),
            macros: BTreeMap::new(),
            decl_order: Vec::new(),
            sort_order: Vec::new(),
            last_model: None,
            fresh_counter: 0,
            quant_atoms: BTreeSet::new(),
            enums: BTreeMap::new(),
            records: BTreeMap::new(),
            datatypes: BTreeMap::new(),
            dt_depth: BTreeMap::new(),
            tester_of: BTreeMap::new(),
            param_datatypes: BTreeMap::new(),
            lambdas: BTreeMap::new(),
            maps: BTreeMap::new(),
            as_arrays: BTreeMap::new(),
            params: crate::util::Params::new(),
            sort_ctors: BTreeMap::new(),
            universals: Vec::new(),
            objectives: Vec::new(),
            objective_values: Vec::new(),
            soft: Vec::new(),
            string_sort: None,
            str_lits: BTreeMap::new(),
            str_len_decl: None,
            str_symbolic: BTreeSet::new(),
            str_witness: Vec::new(),
            str_pred_len: Vec::new(),
            str_len_ub: Vec::new(),
            str_op_decls: BTreeMap::new(),
            reglan_sort: None,
            regex_of: BTreeMap::new(),
            sort_defs: BTreeMap::new(),
            fp_sorts: BTreeMap::new(),
            rm_sort: None,
            fp_of: BTreeMap::new(),
            fp_bv: BTreeMap::new(),
            seq_sorts: BTreeMap::new(),
            seq_of: BTreeMap::new(),
            seq_empty: BTreeMap::new(),
            symbolic_divisors: BTreeSet::new(),
            symbolic_divmod: Vec::new(),
            seq_len_decls: BTreeSet::new(),
            seq_concat: Vec::new(),
            seqop_ops: BTreeMap::new(),
            witness_base: None,
        }
    }

    /// The optional level count for `push`/`pop` (defaults to 1).
    fn level_arg(list: &[SExpr]) -> Result<u32, String> {
        match list.get(1) {
            None => Ok(1),
            Some(SExpr::Atom(a)) => a
                .parse::<u32>()
                .map_err(|_| alloc::format!("expected a level count, found {a:?}")),
            Some(_) => Err("expected a numeric level count".to_string()),
        }
    }

    fn sym(s: &SExpr) -> Result<&str, String> {
        match s {
            SExpr::Atom(a) => Ok(a),
            SExpr::List(_) => Err("expected a symbol, found a list".to_string()),
        }
    }

    /// Does a tactic expression mention `name` anywhere (as a leaf tactic or
    /// inside a combinator like `(then …)`)?
    fn tactic_mentions(t: &SExpr, name: &str) -> bool {
        match t {
            SExpr::Atom(a) => a == name,
            SExpr::List(l) => l.iter().any(|s| Self::tactic_mentions(s, name)),
        }
    }

    fn resolve_sort(&mut self, s: &SExpr) -> Result<AstId, String> {
        match s {
            SExpr::Atom(name) if name == "String" => Ok(self.string_sort()),
            SExpr::Atom(name) if name == "RegLan" => Ok(self.reglan_sort()),
            SExpr::Atom(name) if name == "RoundingMode" => Ok(self.rm_sort()),
            SExpr::Atom(name) if fp_format(name).is_some() => {
                let (eb, sb) = fp_format(name).unwrap();
                Ok(self.fp_sort(eb, sb))
            }
            SExpr::Atom(name) => self
                .sorts
                .get(name)
                .copied()
                .ok_or_else(|| alloc::format!("unknown sort {name:?}")),
            SExpr::List(l) if !l.is_empty() => {
                // Parametric sort application, e.g. (Array I E) or (_ BitVec n).
                match Self::sym(&l[0])? {
                    "Array" if l.len() == 3 => {
                        let index = self.resolve_sort(&l[1])?;
                        let elem = self.resolve_sort(&l[2])?;
                        Ok(self.m.mk_array_sort(index, elem))
                    }
                    "_" if l.len() == 3 && Self::sym(&l[1])? == "BitVec" => {
                        let w: u32 = Self::sym(&l[2])?
                            .parse()
                            .map_err(|_| "BitVec: bad width".to_string())?;
                        Ok(self.m.mk_bv_sort(w))
                    }
                    "Seq" if l.len() == 2 => {
                        let e = self.resolve_sort(&l[1])?;
                        Ok(self.seq_sort(e))
                    }
                    // A set is its characteristic function: (Set T) = (Array T Bool).
                    "Set" if l.len() == 2 => {
                        let e = self.resolve_sort(&l[1])?;
                        let b = self.m.mk_bool_sort();
                        Ok(self.m.mk_array_sort(e, b))
                    }
                    "_" if l.len() == 4 && Self::sym(&l[1])? == "FloatingPoint" => {
                        let eb: u32 = Self::sym(&l[2])?
                            .parse()
                            .map_err(|_| "bad eb".to_string())?;
                        let sb: u32 = Self::sym(&l[3])?
                            .parse()
                            .map_err(|_| "bad sb".to_string())?;
                        Ok(self.fp_sort(eb, sb))
                    }
                    name if self.sort_defs.contains_key(name) => {
                        // A parametric sort macro (define-sort): substitute the
                        // arguments for the parameters in the body, then resolve.
                        let (params, body) = self.sort_defs[name].clone();
                        if params.len() != l.len() - 1 {
                            return Err(alloc::format!("sort {name}: wrong arity"));
                        }
                        let subst: Vec<(String, SExpr)> =
                            params.into_iter().zip(l[1..].iter().cloned()).collect();
                        let expanded = subst_sort(&body, &subst);
                        self.resolve_sort(&expanded)
                    }
                    name if self.param_datatypes.contains_key(name) => {
                        self.monomorphize_datatype(name, &l[1..])
                    }
                    name if self.sort_ctors.get(name) == Some(&(l.len() - 1)) => {
                        // An arity-N uninterpreted sort constructor: each distinct
                        // argument tuple is a distinct (cached) uninterpreted sort.
                        let args: Vec<AstId> = l[1..]
                            .iter()
                            .map(|a| self.resolve_sort(a))
                            .collect::<Result<_, _>>()?;
                        let key = alloc::format!("{name}!{args:?}");
                        if let Some(&s) = self.sorts.get(&key) {
                            return Ok(s);
                        }
                        let s = self.m.mk_uninterpreted_sort(Symbol::new(&key));
                        self.sorts.insert(key, s);
                        Ok(s)
                    }
                    other => Err(alloc::format!("unsupported sort constructor {other:?}")),
                }
            }
            _ => Err("expected a sort".to_string()),
        }
    }

    /// Interpret a top-level command, returning any textual response.
    fn command(&mut self, form: &SExpr) -> Result<Option<String>, String> {
        let list = match form {
            SExpr::List(l) if !l.is_empty() => l,
            _ => return Err("expected a command list".to_string()),
        };
        match Self::sym(&list[0])? {
            "set-option" => {
                // (set-option :name value) — store the option so get-option can
                // return it. The value is one of the SMT-LIB scalar forms.
                if list.len() >= 3
                    && let Ok(name) = Self::sym(&list[1])
                {
                    let name = name.to_string();
                    if let SExpr::Atom(v) = &list[2] {
                        use crate::util::ParamValue;
                        let pv = match v.as_str() {
                            "true" => ParamValue::Bool(true),
                            "false" => ParamValue::Bool(false),
                            s => {
                                if let Ok(u) = s.parse::<u64>() {
                                    ParamValue::UInt(u)
                                } else if let Ok(d) = s.parse::<f64>() {
                                    ParamValue::Double(d)
                                } else {
                                    ParamValue::Str(s.to_string())
                                }
                            }
                        };
                        self.params.set(&name, pv);
                    }
                }
                Ok(None)
            }
            "get-option" => {
                // (get-option :name) — the stored value, or "unsupported".
                use crate::util::ParamValue;
                let name = Self::sym(&list[1])?;
                Ok(Some(match self.params.get(name) {
                    Some(ParamValue::Bool(b)) => b.to_string(),
                    Some(ParamValue::UInt(u)) => u.to_string(),
                    Some(ParamValue::Double(d)) => d.to_string(),
                    Some(ParamValue::Str(s)) => s.clone(),
                    None => "unsupported".to_string(),
                }))
            }
            "get-assertions" => {
                // The current assertion stack, as an s-expr list.
                let body = self
                    .assertions
                    .iter()
                    .map(|&a| alloc::format!("\n  {}", self.m.pp(a)))
                    .collect::<String>();
                Ok(Some(alloc::format!("({body})")))
            }
            "set-logic" | "set-info" | "exit" => Ok(None),
            "echo" => Ok(Some(match list.get(1) {
                Some(SExpr::Atom(a)) => unquote_string(a),
                _ => String::new(),
            })),
            "get-info" => match list.get(1) {
                Some(SExpr::Atom(k)) if k == ":version" => Ok(Some(alloc::format!(
                    "(:version \"{}\")",
                    env!("CARGO_PKG_VERSION")
                ))),
                Some(SExpr::Atom(k)) if k == ":name" => Ok(Some("(:name \"z3rs\")".to_string())),
                Some(SExpr::Atom(k)) if k == ":authors" => {
                    Ok(Some("(:authors \"z3rs\")".to_string()))
                }
                Some(SExpr::Atom(k)) if k == ":error-behavior" => {
                    Ok(Some("(:error-behavior continued-execution)".to_string()))
                }
                Some(SExpr::Atom(k)) if k == ":reason-unknown" => {
                    // Why the most recent check returned `unknown` (empty if it
                    // was decided), mirroring z3's response shape.
                    let r = if self.last_verdict == Some(SmtResult::Unknown) {
                        "incomplete"
                    } else {
                        ""
                    };
                    Ok(Some(alloc::format!("(:reason-unknown \"{r}\")")))
                }
                _ => Ok(None),
            },
            "push" => {
                let n = Self::level_arg(list)?;
                for _ in 0..n {
                    self.scope_stack.push(Scope {
                        assertions: self.assertions.len(),
                        decls: self.decl_order.len(),
                        sorts: self.sort_order.len(),
                        universals: self.universals.len(),
                    });
                }
                self.last_model = None;
                Ok(None)
            }
            "pop" => {
                let n = Self::level_arg(list)?;
                for _ in 0..n {
                    let mark = self
                        .scope_stack
                        .pop()
                        .ok_or_else(|| "pop with no matching push".to_string())?;
                    self.assertions.truncate(mark.assertions); // discard scoped assertions
                    self.assert_names.truncate(mark.assertions);
                    self.universals.truncate(mark.universals);
                    // Undeclare constants/functions and sorts made since the push.
                    for name in self.decl_order.drain(mark.decls..) {
                        self.funcs.remove(&name);
                    }
                    for name in self.sort_order.drain(mark.sorts..) {
                        self.sorts.remove(&name);
                    }
                }
                self.last_model = None;
                Ok(None)
            }
            "reset" => {
                self.assertions.clear();
                self.assert_names.clear();
                self.universals.clear();
                self.objectives.clear();
                self.objective_values.clear();
                self.soft.clear();
                self.scope_stack.clear();
                self.last_model = None;
                self.last_verdict = None;
                Ok(None)
            }
            "reset-assertions" => {
                // Drop assertions and the assertion stack, but keep declarations
                // and options (unlike `reset`).
                self.assertions.clear();
                self.assert_names.clear();
                self.universals.clear();
                self.objectives.clear();
                self.objective_values.clear();
                self.soft.clear();
                self.scope_stack.clear();
                self.last_model = None;
                self.last_verdict = None;
                Ok(None)
            }
            "declare-sort" => {
                let name = Self::sym(&list[1])?.to_string();
                // Optional arity (default 0). Arity ≥ 1 is a sort constructor,
                // applied as `(Name s…)` and monomorphized in resolve_sort.
                let arity: usize = list
                    .get(2)
                    .and_then(|a| Self::sym(a).ok())
                    .and_then(|s| s.parse().ok())
                    .unwrap_or(0);
                if arity == 0 {
                    let s = self.m.mk_uninterpreted_sort(Symbol::new(&name));
                    self.sorts.insert(name.clone(), s);
                    self.sort_order.push(name);
                } else {
                    self.sort_ctors.insert(name, arity);
                }
                Ok(None)
            }
            "define-sort" => {
                // (define-sort Name (params…) body) — a sort macro.
                let name = Self::sym(&list[1])?.to_string();
                let params: Vec<String> = as_list(&list[2])?
                    .iter()
                    .map(|p| Self::sym(p).map(str::to_string))
                    .collect::<Result<_, _>>()?;
                if params.is_empty() {
                    let s = self.resolve_sort(&list[3])?;
                    self.sorts.insert(name.clone(), s);
                    self.sort_order.push(name);
                } else {
                    self.sort_defs.insert(name, (params, list[3].clone()));
                }
                Ok(None)
            }
            "declare-datatypes" => {
                self.declare_datatypes(&list[1], &list[2])?;
                self.last_model = None;
                Ok(None)
            }
            "declare-datatype" => {
                // (declare-datatype Name (ctor…)) — the single-datatype form.
                let name = Self::sym(&list[1])?.to_string();
                let sort_decls = SExpr::List(alloc::vec![SExpr::List(alloc::vec![
                    SExpr::Atom(name),
                    SExpr::Atom("0".to_string()),
                ])]);
                let bodies = SExpr::List(alloc::vec![list[2].clone()]);
                self.declare_datatypes(&sort_decls, &bodies)?;
                self.last_model = None;
                Ok(None)
            }
            "simplify" => {
                // (simplify term [:opt v …]) — return the simplified term.
                let t = self.term(&list[1])?;
                let folded = self.dt_fold(t);
                let s = crate::rewriter::simplify(&mut self.m, folded);
                Ok(Some(self.m.pp(s)))
            }
            "apply" => {
                // (apply tactic) — apply a goal-transforming tactic and print the
                // residual subgoal. Recognized leaves: `nnf` (negation normal
                // form) and the simplifying tactics (simplify / ctx-simplify /
                // propagate-values); combinators (then / and-then / par-then / …)
                // are traversed for their leaves. Trivially-true assertions are
                // dropped and a false one collapses the goal.
                let use_nnf = list
                    .get(1)
                    .map(|t| Self::tactic_mentions(t, "nnf"))
                    .unwrap_or(false);
                let use_ctx = list
                    .get(1)
                    .map(|t| Self::tactic_mentions(t, "ctx-solver-simplify"))
                    .unwrap_or(false);
                let asserts = self.assertions.clone();
                let mut lines: Vec<String> = Vec::new();
                // Pass 1: per-formula rewriting (nnf + theory simplification).
                let mut simplified: Vec<AstId> = Vec::new();
                let mut collapsed = false;
                for a in asserts {
                    let mut s = self.dt_fold(a);
                    if use_nnf {
                        s = crate::rewriter::to_nnf(&mut self.m, s);
                    }
                    s = crate::rewriter::simplify(&mut self.m, s);
                    if self.m.is_false(s) {
                        collapsed = true;
                        break;
                    }
                    if !self.m.is_true(s) {
                        simplified.push(s);
                    }
                }
                // Pass 2 (ctx-solver-simplify): drop each formula that the
                // conjunction of the others already entails, and detect a
                // context-level contradiction — using the solver as the oracle.
                if use_ctx && !collapsed {
                    match self.ctx_solver_simplify(&simplified) {
                        None => collapsed = true,
                        Some(residual) => simplified = residual,
                    }
                }
                if collapsed {
                    lines = alloc::vec!["false".to_string()];
                } else {
                    for s in simplified {
                        lines.push(self.m.pp(s));
                    }
                }
                let body = lines
                    .iter()
                    .map(|l| alloc::format!("\n  {l}"))
                    .collect::<String>();
                Ok(Some(alloc::format!(
                    "(goals\n(goal{body}\n  :precision precise :depth 1)\n)"
                )))
            }
            "eval" => {
                // (eval term) — the value of `term` in the current model.
                if self.last_model.is_none() {
                    return Err("eval requires a preceding satisfiable check-sat".to_string());
                }
                let id = self.term(&list[1])?;
                let mut model = self.last_model.take().unwrap();
                let v = self
                    .enum_value_name(&mut model, id)
                    .unwrap_or_else(|| model.value_string(&self.m, id));
                self.last_model = Some(model);
                Ok(Some(v))
            }
            "declare-const" => {
                // (declare-const c S)
                let name = Self::sym(&list[1])?.to_string();
                let range = self.resolve_sort(&list[2])?;
                let d = self.m.mk_func_decl(Symbol::new(&name), &[], range);
                self.funcs.insert(name.clone(), d);
                self.decl_order.push(name);
                self.last_model = None;
                Ok(None)
            }
            "declare-fun" => {
                // (declare-fun f (D...) R)
                let name = Self::sym(&list[1])?.to_string();
                let domain: Vec<AstId> = match &list[2] {
                    SExpr::List(ds) => ds
                        .iter()
                        .map(|d| self.resolve_sort(d))
                        .collect::<Result<_, _>>()?,
                    _ => return Err("declare-fun: expected a domain list".to_string()),
                };
                let range = self.resolve_sort(&list[3])?;
                let d = self.m.mk_func_decl(Symbol::new(&name), &domain, range);
                self.funcs.insert(name.clone(), d);
                self.decl_order.push(name);
                self.last_model = None;
                Ok(None)
            }
            "define-fun" => {
                // (define-fun name ((p S) ...) R body)
                let name = Self::sym(&list[1])?.to_string();
                let params: Vec<String> = match &list[2] {
                    SExpr::List(ps) => ps
                        .iter()
                        .map(|p| match p {
                            SExpr::List(pair) if !pair.is_empty() => {
                                Ok(Self::sym(&pair[0])?.to_string())
                            }
                            _ => Err("define-fun: bad parameter".to_string()),
                        })
                        .collect::<Result<_, _>>()?,
                    _ => return Err("define-fun: expected a parameter list".to_string()),
                };
                self.macros.insert(name, (params, list[4].clone()));
                Ok(None)
            }
            "define-const" => {
                // (define-const name S body) ≡ (define-fun name () S body).
                let name = Self::sym(&list[1])?.to_string();
                self.macros.insert(name, (Vec::new(), list[3].clone()));
                Ok(None)
            }
            "define-fun-rec" => {
                // (define-fun-rec name ((p S)...) R body): a possibly-recursive
                // definition. Declare `name` uninterpreted and add the defining
                // axiom ∀p. name(p) = body as a universal — instantiation unfolds
                // it on demand (which cannot be done by macro inlining).
                self.declare_rec_fun(&list[1], &list[2], &list[3])?;
                self.add_rec_axiom(&list[1], &list[2], &list[4])?;
                self.last_model = None;
                Ok(None)
            }
            "define-funs-rec" => {
                // (define-funs-rec ((f1 (params) R1) …) (body1 …)) — mutual
                // recursion. Declare every function first (so bodies can refer to
                // all of them), then add each defining axiom.
                let decls = as_list(&list[1])?;
                let bodies = as_list(&list[2])?;
                if decls.len() != bodies.len() {
                    return Err("define-funs-rec: decl/body count mismatch".to_string());
                }
                for d in decls {
                    let dl = as_list(d)?;
                    self.declare_rec_fun(&dl[0], &dl[1], &dl[2])?;
                }
                for (d, body) in decls.iter().zip(bodies) {
                    let dl = as_list(d)?;
                    self.add_rec_axiom(&dl[0], &dl[1], body)?;
                }
                self.last_model = None;
                Ok(None)
            }
            "assert" => {
                // A top-level quantifier gets real (sound) handling: `exists` is
                // skolemized (its body asserted with fresh constants), `forall` is
                // recorded for ground instantiation at check-sat. Quantifiers
                // nested inside a formula fall back to the `unknown` sentinel.
                if let Some(kind) = top_level_quantifier(&list[1]) {
                    let ql = as_list(&list[1])?;
                    // Flatten `∀x.∀y.φ` into a single `∀x,y.φ` so E-matching /
                    // instantiation handle it instead of gating the inner
                    // quantifier to `unknown`.
                    if kind == "exists" {
                        // Skolemize the existential block as fresh constants, then
                        // handle an inner universal block (∃x.∀y.φ): the assertion
                        // is satisfiable iff the eliminated/instantiated ∀y.φ[k] is.
                        let mut scope = Vec::new();
                        for b in as_list(&ql[1])? {
                            let pair = as_list(b)?;
                            let nm = Self::sym(&pair[0])?.to_string();
                            let s = self.resolve_sort(&pair[1])?;
                            scope.push((nm, self.fresh_const(s)));
                        }
                        self.scopes.push(scope);
                        let (fbinders, inner) = flatten_foralls(&ql[2]);
                        if fbinders.is_empty() {
                            let body = self.term(&inner);
                            self.scopes.pop();
                            self.assertions.push(body?);
                            self.assert_names.push(None);
                        } else {
                            let blist = SExpr::List(fbinders);
                            let parsed = self.parse_quantifier(&blist, &inner);
                            self.scopes.pop();
                            let (vars, body) = parsed?;
                            if let Some(qf) = self.qe_forall(&vars, body) {
                                self.assertions.push(qf);
                                self.assert_names.push(None);
                            } else {
                                self.universals.push((vars, body));
                            }
                        }
                        self.last_model = None;
                        self.last_verdict = None;
                        return Ok(None);
                    }
                    // forall: flatten nested universals, then eliminate/instantiate.
                    let (binders, inner) = {
                        let (extra, inner) = flatten_foralls(&ql[2]);
                        if extra.is_empty() {
                            (ql[1].clone(), ql[2].clone())
                        } else {
                            let mut bs = as_list(&ql[1])?.to_vec();
                            bs.extend(extra);
                            (SExpr::List(bs), inner)
                        }
                    };
                    // Real linear `∀x. ∃y. φ`: eliminate `∃y` (exact Fourier–Motzkin
                    // over the reals) then decide the residual `∀x. ψ` by real QE —
                    // a complete decision for that fragment (both directions).
                    if let Some(qf) = self.try_forall_exists_qe(&binders, &inner) {
                        self.assertions.push(qf);
                        self.assert_names.push(None);
                        self.last_model = None;
                        self.last_verdict = None;
                        return Ok(None);
                    }
                    // Skolemize positive existentials in the body so `∀x. ∃y. P`
                    // becomes a purely universal `∀x. P[y := f(x)]` the
                    // instantiation engine can use.
                    let univ: Vec<(String, SExpr)> = as_list(&binders)?
                        .iter()
                        .map(|b| {
                            let p = as_list(b)?;
                            Ok::<_, String>((Self::sym(&p[0])?.to_string(), p[1].clone()))
                        })
                        .collect::<Result<_, _>>()?;
                    let inner = self.skolemize_body(&inner, &univ, true)?;
                    let (vars, body) = self.parse_quantifier(&binders, &inner)?;
                    if let Some(qf) = self.qe_forall(&vars, body) {
                        self.assertions.push(qf);
                        self.assert_names.push(None);
                    } else {
                        self.universals.push((vars, body));
                    }
                    self.last_model = None;
                    self.last_verdict = None;
                    return Ok(None);
                }
                let t = self.term(&list[1])?;
                let name = named_label(&list[1]);
                self.assertions.push(t);
                self.assert_names.push(name);
                self.last_model = None;
                self.last_verdict = None;
                Ok(None)
            }
            "maximize" | "minimize" => {
                let t = self.term(&list[1])?;
                let maximize = matches!(&list[0], SExpr::Atom(a) if a == "maximize");
                let text = render_sexpr(&list[1]);
                self.objectives.push((t, maximize, text));
                self.last_model = None;
                Ok(None)
            }
            "assert-soft" => {
                // (assert-soft F [:weight w] [:id g]) — prefer F. Hard-assert
                // (F ∨ pᵢ) with a fresh penalty bool pᵢ; check-sat minimizes the
                // total weight of the softs whose pᵢ is forced true.
                let f = self.term(&list[1])?;
                let weight = attr_int(list, ":weight").unwrap_or(1);
                let name = alloc::format!("!soft!{}", self.fresh_counter);
                self.fresh_counter += 1;
                let b = self.m.mk_bool_sort();
                let pdecl = self.m.mk_func_decl(Symbol::new(&name), &[], b);
                let penalty = self.m.mk_const(pdecl);
                let relaxed = self.m.mk_or(&[f, penalty]);
                self.assertions.push(relaxed);
                self.assert_names.push(None);
                self.soft.push((penalty, weight));
                self.last_model = None;
                Ok(None)
            }
            "get-objectives" => Ok(Some(self.get_objectives())),
            // check-sat-using (tactic …) picks a solving strategy but yields the
            // same verdict; the tactic argument is advisory, so run a plain check.
            "check-sat" | "check-sat-using" => {
                let (res, model) = if self.objectives.is_empty() && self.soft.is_empty() {
                    self.check_sat()
                } else {
                    self.optimize()
                };
                self.last_model = model;
                self.last_verdict = Some(res);
                Ok(Some(verdict_word(res).to_string()))
            }
            "check-sat-assuming" => {
                // (check-sat-assuming (a1 a2 …)) — decide the assertions together
                // with the assumption literals, without adding them permanently.
                let assumptions = match list.get(1) {
                    Some(SExpr::List(a)) => a.clone(),
                    _ => return Err("check-sat-assuming: expected a literal list".to_string()),
                };
                let mut conj = alloc::vec![self.conjunction()];
                for a in &assumptions {
                    conj.push(self.term(a)?);
                }
                let base = self.m.mk_and(&conj);
                let goal = self.lift(base);
                let (res, model) = self.decide(goal);
                self.last_model = model;
                self.last_verdict = Some(res);
                Ok(Some(verdict_word(res).to_string()))
            }
            "get-value" => self.get_value(list).map(Some),
            "get-model" => self.get_model().map(Some),
            "get-unsat-core" => self.get_unsat_core().map(Some),
            "get-proof" => self.get_proof().map(Some),
            other => Err(alloc::format!("unsupported command {other:?}")),
        }
    }

    /// Lift theory terms the linear core cannot reason about opaquely into fresh
    /// constants with defining constraints (pushed onto `ctx.defs`), keeping the
    /// result equisatisfiable. A non-Boolean `(ite c a b)` becomes `k` with
    /// `(=> c (= k a))` and `(=> ¬c (= k b))`. A `(div a n)` or `(mod a n)` with a
    /// constant divisor `n ≠ 0` becomes `q` / `r` with `a = n·q + r` and
    /// `0 ≤ r < |n|` (Euclidean). `ctx.dm` memoizes each `(a, n)` so `div` and
    /// `mod` of the same operands share one `(q, r)` pair.
    fn lift_terms(&mut self, t: AstId, ctx: &mut LiftCtx) -> AstId {
        if let Some(&r) = ctx.cache.get(&t) {
            return r;
        }
        let result = if self.m.is_app(t) {
            let decl = self.m.app_decl(t);
            let args = self.m.app_args(t).to_vec();
            let new_args: Vec<AstId> = args.iter().map(|&a| self.lift_terms(a, ctx)).collect();
            let rebuilt = if new_args == args {
                t
            } else {
                self.m.mk_app(decl, &new_args)
            };
            if self.m.is_ite(rebuilt) && !self.m.is_bool_sort(self.m.get_sort(rebuilt)) {
                self.lift_ite(rebuilt, &mut ctx.defs)
            } else if let Some((q, r)) = self.divmod_pieces(rebuilt, ctx) {
                // Return q for div, r for mod.
                match self.m.arith_op(rebuilt) {
                    Some(ArithOp::Idiv) => q,
                    _ => r,
                }
            } else if let Some(k) = self.lift_to_int(rebuilt, ctx) {
                k
            } else {
                rebuilt
            }
        } else {
            t
        };
        ctx.cache.insert(t, result);
        result
    }

    /// Lift a non-Boolean `ite` to a fresh constant, returning it.
    fn lift_ite(&mut self, ite: AstId, defs: &mut Vec<AstId>) -> AstId {
        let a = self.m.app_args(ite).to_vec(); // [cond, then, else]
        let sort = self.m.get_sort(ite);
        let k = self.fresh_const(sort);
        let eq_t = self.m.mk_eq(k, a[1]);
        let eq_e = self.m.mk_eq(k, a[2]);
        let imp_t = self.m.mk_implies(a[0], eq_t);
        let nc = self.m.mk_not(a[0]);
        let imp_e = self.m.mk_implies(nc, eq_e);
        defs.push(imp_t);
        defs.push(imp_e);
        k
    }

    /// If `t` is `(div a n)` or `(mod a n)` with a constant integer divisor
    /// `n ≠ 0`, return the shared `(q, r)` for `a`,`n`, creating and constraining
    /// them (`a = n·q + r`, `0 ≤ r < |n|`) on first use.
    fn divmod_pieces(&mut self, t: AstId, ctx: &mut LiftCtx) -> Option<(AstId, AstId)> {
        let op = self.m.arith_op(t)?;
        if !matches!(op, ArithOp::Idiv | ArithOp::Mod) {
            return None;
        }
        let args = self.m.app_args(t).to_vec();
        let (a, b) = (args[0], args[1]);
        if let Some(&pair) = ctx.dm.get(&(a, b)) {
            return Some(pair);
        }
        let int = self.m.mk_int_sort();
        let q = self.fresh_const(int);
        let r = self.fresh_const(int);
        let zero = self.m.mk_int(0);
        match self.m.as_numeral(b).and_then(|v| v.to_integer()) {
            Some(n) if !n.is_zero() => {
                // Constant nonzero divisor: unconditional `a = n·q + r ∧ 0 ≤ r < |n|`.
                let nq = self.m.mk_mul(&[b, q]);
                let sum = self.m.mk_add(&[nq, r]);
                ctx.defs.push(self.m.mk_eq(a, sum));
                ctx.defs.push(self.m.mk_ge(r, zero));
                let abs_n = self.m.mk_numeral(Rational::from_integer(n.abs()), true);
                ctx.defs.push(self.m.mk_lt(r, abs_n));
            }
            Some(_) => {
                // Division by the literal 0 is unconstrained in SMT-LIB: q, r free.
            }
            None => {
                // For a *compound* divisor expression, alias it to a fresh
                // variable `dv` (`dv = b`) and reason about `dv`. Then the
                // single-variable divisor-witness / complete-UNSAT decision also
                // covers `div a (+ x y)`, `div a (* 2 y)`, … — substituting a
                // value for `dv` linearises both the Euclidean `dv·q` and the
                // `dv = b` link.
                let divv = if self.m.is_uninterp_const(b) {
                    b
                } else {
                    let dv = self.fresh_const(int);
                    let link = self.m.mk_eq(dv, b);
                    ctx.defs.push(link);
                    dv
                };
                self.symbolic_divisors.insert(divv);
                self.symbolic_divmod.push((a, divv, q, r));
                // Symbolic divisor: the Euclidean identity holds only for dv ≠ 0
                // (div/mod by 0 are unconstrained). `|dv| = ite(dv≥0, dv, −dv)`.
                // Push the three facts as *separate* guarded implications rather
                // than one bundled body, so the linear engine can use the range
                // `0 ≤ r < |dv|` even when the nonlinear identity `a = dv·q + r`
                // is opaque to it (e.g. refuting `mod(x,y) ≥ y ∧ y > 0`).
                let beq0 = self.m.mk_eq(divv, zero);
                let bne0 = self.m.mk_not(beq0);
                let nq = self.m.mk_mul(&[divv, q]);
                let sum = self.m.mk_add(&[nq, r]);
                let eq = self.m.mk_eq(a, sum);
                ctx.defs.push(self.m.mk_implies(bne0, eq));
                let ge = self.m.mk_ge(r, zero);
                ctx.defs.push(self.m.mk_implies(bne0, ge));
                // `r < |dv|`, split by the sign of `dv` to avoid an `ite` the
                // linear engine won't resolve: `dv>0 ⇒ r<dv` and `dv<0 ⇒ r<−dv`.
                let bgt0 = self.m.mk_gt(divv, zero);
                let ltb = self.m.mk_lt(r, divv);
                ctx.defs.push(self.m.mk_implies(bgt0, ltb));
                let blt0 = self.m.mk_lt(divv, zero);
                let neg1 = self.m.mk_int(-1);
                let negb = self.m.mk_mul(&[neg1, divv]);
                let ltnegb = self.m.mk_lt(r, negb);
                ctx.defs.push(self.m.mk_implies(blt0, ltnegb));
                // Same dividend and divisor: `div(t,t)=1 ∧ mod(t,t)=0` for `t≠0`
                // (the nonlinear identity alone doesn't pin this for the linear
                // engine). Decides e.g. `mod(x,x) > 9 ∧ x > 0` (unsat).
                if a == b {
                    let one = self.m.mk_int(1);
                    let q1 = self.m.mk_eq(q, one);
                    ctx.defs.push(self.m.mk_implies(bne0, q1));
                    let r0 = self.m.mk_eq(r, zero);
                    ctx.defs.push(self.m.mk_implies(bne0, r0));
                }
            }
        }
        ctx.dm.insert((a, b), (q, r));
        Some((q, r))
    }

    /// If `t` is `(to_int a)`, return a fresh integer `k` with `k ≤ a < k + 1`
    /// (i.e. `k = ⌊a⌋`), memoized per argument. Constant arguments are folded
    /// earlier, so this handles the symbolic case.
    fn lift_to_int(&mut self, t: AstId, ctx: &mut LiftCtx) -> Option<AstId> {
        if self.m.arith_op(t)? != ArithOp::ToInt {
            return None;
        }
        let a = self.m.app_args(t)[0];
        if let Some(&k) = ctx.toint.get(&a) {
            return Some(k);
        }
        let int = self.m.mk_int_sort();
        let k = self.fresh_const(int);
        let le = self.m.mk_le(k, a); // k ≤ a
        let one = self.m.mk_int(1);
        let kp1 = self.m.mk_add(&[k, one]);
        let lt = self.m.mk_lt(a, kp1); // a < k + 1
        ctx.defs.push(le);
        ctx.defs.push(lt);
        ctx.toint.insert(a, k);
        Some(k)
    }

    /// `(declare-datatypes sort_decls bodies)` — currently the enumeration case
    /// (all constructors nullary). Supports both the SMT-LIB 2.6 form
    /// `((T 0)…) ((( c1 )( c2 ))…)` and the legacy `() ((T c1 c2 …)…)`.
    fn declare_datatypes(&mut self, sort_decls: &SExpr, bodies: &SExpr) -> Result<(), String> {
        let sort_decls = as_list(sort_decls)?;
        let bodies = as_list(bodies)?;
        // Pass 1: register every datatype sort name up front, so a constructor
        // field may reference a mutually-recursive sibling (e.g. T referencing F
        // before F is fully declared).
        for (i, body) in bodies.iter().enumerate() {
            let (name, arity) = if sort_decls.is_empty() {
                (Self::sym(&as_list(body)?[0])?.to_string(), 0usize)
            } else {
                let sd = as_list(&sort_decls[i])?;
                let ar = Self::sym(&sd[1])?.parse().unwrap_or(0);
                (Self::sym(&sd[0])?.to_string(), ar)
            };
            // A parametric datatype (arity > 0) has no concrete sort of its own;
            // it is monomorphized on use.
            if arity == 0 && !self.sorts.contains_key(&name) {
                let sort = self.m.mk_uninterpreted_sort(Symbol::new(&name));
                self.sorts.insert(name.clone(), sort);
                self.sort_order.push(name);
            }
        }
        // Pass 2: build each datatype's constructors, selectors, and axioms —
        // or, for a parametric datatype, store its template for monomorphization.
        for (i, body) in bodies.iter().enumerate() {
            let bodyl = as_list(body)?;
            let (name, ctors): (String, &[SExpr]) = if sort_decls.is_empty() {
                (Self::sym(&bodyl[0])?.to_string(), &bodyl[1..]) // legacy (T c1 c2 …)
            } else {
                let sd = as_list(&sort_decls[i])?;
                (Self::sym(&sd[0])?.to_string(), bodyl) // 2.6: name from (T k)
            };
            // Parametric form: (par (A B …) (ctors…)). Store the template.
            if let Some(first) = ctors.first()
                && matches!(first, SExpr::Atom(a) if a == "par")
            {
                let par = ctors; // [par, (params), (ctors)]
                let params: Vec<String> = as_list(&par[1])?
                    .iter()
                    .map(Self::sym)
                    .collect::<Result<Vec<_>, _>>()?
                    .into_iter()
                    .map(str::to_string)
                    .collect();
                let ctor_list = as_list(&par[2])?.to_vec();
                self.param_datatypes.insert(name, (params, ctor_list));
                continue;
            }
            let sort = self.sorts[&name];
            self.build_datatype(sort, ctors)?;
        }
        Ok(())
    }

    /// Monomorphize a parametric datatype at the given argument sorts, e.g.
    /// `(Pair Int Bool)`. Creates (once) a concrete sort named `Name!arg1!arg2…`
    /// with its type parameters substituted by the argument sort expressions,
    /// then builds its constructors. Returns the concrete sort.
    fn monomorphize_datatype(&mut self, name: &str, args: &[SExpr]) -> Result<AstId, String> {
        let (params, ctors) = self.param_datatypes[name].clone();
        if params.len() != args.len() {
            return Err(alloc::format!("datatype {name}: wrong arity"));
        }
        // A distinct concrete name per instantiation (resolve args to canonical
        // sort ids first, so `(Pair Int Bool)` always maps to the same instance).
        let arg_sorts: Vec<AstId> = args
            .iter()
            .map(|a| self.resolve_sort(a))
            .collect::<Result<_, _>>()?;
        let mut mono = name.to_string();
        for &s in &arg_sorts {
            mono.push_str(&alloc::format!("!{}", s.0));
        }
        if let Some(&sort) = self.sorts.get(&mono) {
            return Ok(sort); // already built
        }
        let sort = self.m.mk_uninterpreted_sort(Symbol::new(&mono));
        self.sorts.insert(mono.clone(), sort);
        self.sort_order.push(mono);
        // Substitute the type parameters by the concrete argument sort exprs in
        // every constructor field, then build the instance.
        let subst: Vec<(String, SExpr)> = params.into_iter().zip(args.iter().cloned()).collect();
        let mono_ctors: Vec<SExpr> = ctors.iter().map(|c| subst_sort(c, &subst)).collect();
        self.build_datatype(sort, &mono_ctors)?;
        Ok(sort)
    }

    /// Build the constructors, selectors, testers, and axioms of a monomorphic
    /// datatype `sort` from its constructor s-expressions.
    fn build_datatype(&mut self, sort: AstId, ctors: &[SExpr]) -> Result<(), String> {
        {
            // Parse each constructor into (name, [(field name, field sort sexpr)]).
            let mut parsed: Vec<(String, Vec<(String, SExpr)>)> = Vec::new();
            for c in ctors {
                match c {
                    SExpr::Atom(a) => parsed.push((a.clone(), Vec::new())),
                    SExpr::List(cl) if !cl.is_empty() => {
                        let cname = Self::sym(&cl[0])?.to_string();
                        let mut fields = Vec::new();
                        for f in &cl[1..] {
                            let fl = as_list(f)?;
                            fields.push((Self::sym(&fl[0])?.to_string(), fl[1].clone()));
                        }
                        parsed.push((cname, fields));
                    }
                    _ => return Err("declare-datatypes: malformed constructor".to_string()),
                }
            }
            let all_nullary = parsed.iter().all(|(_, f)| f.is_empty());
            if all_nullary {
                // Enumeration: distinct constants, domain axiom.
                let mut ctor_ids = Vec::new();
                for (cname, _) in &parsed {
                    let d = self.m.mk_func_decl(Symbol::new(cname), &[], sort);
                    let cid = self.m.mk_const(d);
                    self.funcs.insert(cname.clone(), d);
                    self.decl_order.push(cname.clone());
                    ctor_ids.push(cid);
                }
                self.enums.insert(sort, ctor_ids);
            } else if parsed.len() == 1 {
                // Record/tuple: one constructor with fields, plus selectors.
                let (cname, fields) = &parsed[0];
                let field_sorts: Vec<AstId> = fields
                    .iter()
                    .map(|(_, s)| self.resolve_sort(s))
                    .collect::<Result<_, _>>()?;
                let cdecl = self.m.mk_func_decl(Symbol::new(cname), &field_sorts, sort);
                self.funcs.insert(cname.clone(), cdecl);
                self.decl_order.push(cname.clone());
                let mut sel_decls = Vec::new();
                for ((fname, _), &fsort) in fields.iter().zip(&field_sorts) {
                    let sdecl = self.m.mk_func_decl(Symbol::new(fname), &[sort], fsort);
                    self.funcs.insert(fname.clone(), sdecl);
                    self.decl_order.push(fname.clone());
                    sel_decls.push(sdecl);
                }
                self.records.insert(sort, (cdecl, sel_decls));
            } else {
                // General non-recursive datatype: ≥2 constructors, some with
                // fields. Each gets a constructor, its selectors, and a tester
                // predicate `is-C : sort → Bool`.
                let bool_sort = self.m.mk_bool_sort();
                let mut ctor_infos = Vec::new();
                for (cname, fields) in &parsed {
                    let field_sorts: Vec<AstId> = fields
                        .iter()
                        .map(|(_, s)| self.resolve_sort(s))
                        .collect::<Result<_, _>>()?;
                    let cdecl = self.m.mk_func_decl(Symbol::new(cname), &field_sorts, sort);
                    self.funcs.insert(cname.clone(), cdecl);
                    self.decl_order.push(cname.clone());
                    let mut sel_decls = Vec::new();
                    for ((fname, _), &fsort) in fields.iter().zip(&field_sorts) {
                        let sdecl = self.m.mk_func_decl(Symbol::new(fname), &[sort], fsort);
                        self.funcs.insert(fname.clone(), sdecl);
                        self.decl_order.push(fname.clone());
                        sel_decls.push(sdecl);
                    }
                    let tname = alloc::format!("is-{cname}");
                    let tdecl = self.m.mk_func_decl(Symbol::new(&tname), &[sort], bool_sort);
                    self.tester_of.insert(cname.clone(), tdecl);
                    ctor_infos.push((cdecl, sel_decls, tdecl));
                }
                // Give the datatype a depth measure if it has any field of a
                // non-primitive sort — the field's sort is itself (direct
                // recursion) or another datatype (mutual recursion), both of which
                // need the acyclicity depth constraints. A depth measure is sound
                // for any datatype, so over-creating (e.g. a field of an unrelated
                // uninterpreted sort) is harmless.
                let recursive = ctor_infos.iter().flat_map(|(_, sels, _)| sels).any(|&sd| {
                    self.m.func_decl(sd).map(|d| d.range).is_some_and(|r| {
                        !self.m.is_arith_sort(r)
                            && !self.m.is_bool_sort(r)
                            && self.m.bv_sort_width(r).is_none()
                    })
                });
                if recursive {
                    let int_sort = self.m.mk_int_sort();
                    let name = alloc::format!("depth!{}", self.fresh_counter);
                    self.fresh_counter += 1;
                    let depth = self.m.mk_func_decl(Symbol::new(&name), &[sort], int_sort);
                    self.dt_depth.insert(sort, depth);
                }
                self.datatypes.insert(sort, ctor_infos);
            }
        }
        Ok(())
    }

    /// If `id` is a string that equals a known string literal under `model`,
    /// render that literal's text (so `x = "hi"` prints `"hi"`, not a placeholder).
    fn str_model_value(&self, model: &mut Model, id: AstId) -> Option<String> {
        if Some(self.m.get_sort(id)) != self.string_sort {
            return None;
        }
        for (text, &c) in &self.str_lits {
            if c == id || model.terms_equal(&self.m, id, c) {
                return Some(alloc::format!("\"{text}\""));
            }
        }
        None
    }

    /// If `id` has an enum sort, the name of the constructor it equals under
    /// `model` (so `get-value` prints `green`, not `Color!val!2`).
    fn enum_value_name(&self, model: &mut Model, id: AstId) -> Option<String> {
        let ctors = self.enums.get(&self.m.get_sort(id))?;
        for &c in ctors {
            if model.terms_equal(&self.m, id, c) {
                let decl = self.m.app_decl(c);
                let name = self.m.func_decl(decl)?.name.as_str()?;
                return Some(name.to_string());
            }
        }
        None
    }

    /// Axioms for general (multi-constructor, non-recursive) datatypes in `goal`.
    /// For each datatype term `t`: exhaustiveness (`t` is one of the
    /// constructors), pairwise tester exclusivity, and each tester's definition
    /// `is-Cᵢ(t) ⇒ t = Cᵢ(sel(t)…)`. For each constructor application `Cᵢ(a…)`:
    /// its own tester holds, the others fail, and `selᵢⱼ(Cᵢ(a…)) = aⱼ`.
    /// Inline `v = <ground constructor term>` datatype bindings by substituting
    /// `v` with the term, so selectors/testers over `v` fold to concrete values
    /// (`l = cons 1 (cons 2 nl) ∧ is-nl (tl (tl l))` becomes decidable). Sound: `v`
    /// is exactly the term. Only ground right-hand sides, never a `v` in its own
    /// binding (a cycle — handled by the occurs-check).
    fn inline_ground_dt_bindings(&mut self, goal: AstId) -> AstId {
        if self.datatypes.is_empty() {
            return goal;
        }
        let is_dt_var = |m: &AstManager, u: AstId| -> bool {
            // A 0-ary datatype term that is *not* a nullary constructor.
            m.is_app(u)
                && m.app_args(u).is_empty()
                && self
                    .datatypes
                    .get(&m.get_sort(u))
                    .is_some_and(|cs| !cs.iter().any(|(cd, _, _)| *cd == m.app_decl(u)))
        };
        let is_ground_ctor = |m: &AstManager, t: AstId| -> bool {
            m.is_app(t)
                && self
                    .datatypes
                    .get(&m.get_sort(t))
                    .is_some_and(|cs| cs.iter().any(|(cd, _, _)| *cd == m.app_decl(t)))
                && m.postorder(t).iter().all(|&u| !is_dt_var(m, u))
        };
        let mut conj: Vec<AstId> = Vec::new();
        let mut stack = alloc::vec![goal];
        while let Some(t) = stack.pop() {
            if self.m.is_and(t) {
                for &a in self.m.app_args(t) {
                    stack.push(a);
                }
            } else {
                conj.push(t);
            }
        }
        let mut subst: Vec<(AstId, AstId)> = Vec::new();
        let mut bound: BTreeSet<AstId> = BTreeSet::new();
        for &c in &conj {
            if !self.m.is_eq(c) {
                continue;
            }
            let a = self.m.app_args(c);
            if a.len() != 2 {
                continue;
            }
            for (v, t) in [(a[0], a[1]), (a[1], a[0])] {
                if is_dt_var(&self.m, v) && !bound.contains(&v) && is_ground_ctor(&self.m, t) {
                    subst.push((v, t));
                    bound.insert(v);
                }
            }
        }
        if subst.is_empty() {
            return goal;
        }
        let g = crate::rewriter::substitute(&mut self.m, goal, &subst);
        crate::rewriter::simplify(&mut self.m, g)
    }

    /// Sound occurs-check refutation for cyclic datatype equalities among
    /// variables: from the asserted `v = C(… w …)` facts, `v` is strictly deeper
    /// than every datatype variable `w` in the constructor expression. Variables
    /// tied by `v = w` share a depth. A strict cycle (`v > … > v`) is impossible in
    /// a finite datatype, so the goal is UNSAT — catching `p = cons(0,q) ∧
    /// q = cons(0,p)` where the depth axioms miss the multi-variable cycle.
    fn datatype_occurs_unsat(&self, goal: AstId) -> bool {
        if self.datatypes.is_empty() {
            return false;
        }
        let is_dt_var = |m: &AstManager, t: AstId| {
            m.is_app(t) && m.app_args(t).is_empty() && self.datatypes.contains_key(&m.get_sort(t))
        };
        let is_ctor = |m: &AstManager, t: AstId| {
            m.is_app(t)
                && self
                    .datatypes
                    .get(&m.get_sort(t))
                    .is_some_and(|cs| cs.iter().any(|(cd, _, _)| *cd == m.app_decl(t)))
        };
        // Collect the top-level conjuncts (asserted facts).
        let mut conj: Vec<AstId> = Vec::new();
        let mut stack = alloc::vec![goal];
        while let Some(t) = stack.pop() {
            if self.m.is_and(t) {
                for &a in self.m.app_args(t) {
                    stack.push(a);
                }
            } else {
                conj.push(t);
            }
        }
        // Union-find over datatype variables tied by `v = w`.
        let mut rep: BTreeMap<AstId, AstId> = BTreeMap::new();
        fn find(rep: &mut BTreeMap<AstId, AstId>, x: AstId) -> AstId {
            let mut r = x;
            while let Some(&p) = rep.get(&r) {
                if p == r {
                    break;
                }
                r = p;
            }
            r
        }
        let touch = |rep: &mut BTreeMap<AstId, AstId>, x: AstId| {
            rep.entry(x).or_insert(x);
        };
        // Strict edges `v → w` (v deeper than w).
        let mut edges: Vec<(AstId, AstId)> = Vec::new();
        for &c in &conj {
            if !self.m.is_eq(c) {
                continue;
            }
            let args = self.m.app_args(c);
            if args.len() != 2 {
                continue;
            }
            let (a, b) = (args[0], args[1]);
            if is_dt_var(&self.m, a) && is_dt_var(&self.m, b) {
                touch(&mut rep, a);
                touch(&mut rep, b);
                let (ra, rb) = (find(&mut rep, a), find(&mut rep, b));
                if ra != rb {
                    rep.insert(ra, rb);
                }
                continue;
            }
            // `v = C(… )`: every datatype variable in the constructor expression is
            // strictly shallower than `v`.
            for (v, expr) in [(a, b), (b, a)] {
                if is_dt_var(&self.m, v) && is_ctor(&self.m, expr) {
                    touch(&mut rep, v);
                    for sub in self.m.postorder(expr) {
                        if sub != v && is_dt_var(&self.m, sub) {
                            touch(&mut rep, sub);
                            edges.push((v, sub));
                        }
                    }
                }
            }
        }
        if edges.is_empty() {
            return false;
        }
        // A strict cycle over the union-find components is unsatisfiable.
        let comp_edges: Vec<(AstId, AstId)> = edges
            .iter()
            .map(|&(v, w)| (find(&mut rep, v), find(&mut rep, w)))
            .collect();
        // DFS cycle detection (including self-loops).
        let mut nodes: Vec<AstId> = Vec::new();
        for &(v, w) in &comp_edges {
            for x in [v, w] {
                if !nodes.contains(&x) {
                    nodes.push(x);
                }
            }
        }
        let mut color: BTreeMap<AstId, u8> = BTreeMap::new();
        fn dfs(
            node: AstId,
            comp_edges: &[(AstId, AstId)],
            color: &mut BTreeMap<AstId, u8>,
        ) -> bool {
            color.insert(node, 1); // gray
            for &(v, w) in comp_edges {
                if v == node {
                    match color.get(&w).copied().unwrap_or(0) {
                        1 => return true, // back-edge → cycle
                        0 if dfs(w, comp_edges, color) => return true,
                        _ => {}
                    }
                }
            }
            color.insert(node, 2); // black
            false
        }
        for &n in &nodes {
            if color.get(&n).copied().unwrap_or(0) == 0 && dfs(n, &comp_edges, &mut color) {
                return true;
            }
        }
        false
    }

    /// Array extensionality refutation: an asserted `∀i. select a i = select b i`
    /// forces `a = b`, so a co-asserted `a ≠ b` is UNSAT. Instantiation alone can't
    /// see this (extensionality is not a ground-instance rule).
    fn extensionality_unsat(&self, goal: AstId) -> bool {
        // Array pairs forced equal by a `∀i. a[i] = b[i]` assertion.
        let mut pairs: Vec<(AstId, AstId)> = Vec::new();
        for (binders, body) in &self.universals {
            if binders.len() != 1 || !self.m.is_eq(*body) {
                continue;
            }
            let i = binders[0];
            let ba = self.m.app_args(*body);
            if ba.len() != 2 || !self.m.is_select(ba[0]) || !self.m.is_select(ba[1]) {
                continue;
            }
            let (l, r) = (self.m.app_args(ba[0]), self.m.app_args(ba[1]));
            if l.len() == 2 && r.len() == 2 && l[1] == i && r[1] == i && l[0] != r[0] {
                pairs.push((l[0], r[0]));
            }
        }
        if pairs.is_empty() {
            return false;
        }
        // Does the goal assert `a ≠ b` for such a pair?
        let mut conj: Vec<AstId> = Vec::new();
        let mut stack = alloc::vec![goal];
        while let Some(t) = stack.pop() {
            if self.m.is_and(t) {
                for &a in self.m.app_args(t) {
                    stack.push(a);
                }
            } else {
                conj.push(t);
            }
        }
        for c in conj {
            let inner = if self.m.is_not(c) {
                self.m.app_args(c).first().copied()
            } else {
                None
            };
            if let Some(e) = inner
                && self.m.is_eq(e)
            {
                let a = self.m.app_args(e);
                if a.len() == 2 {
                    for &(x, y) in &pairs {
                        if (a[0] == x && a[1] == y) || (a[0] == y && a[1] == x) {
                            return true;
                        }
                    }
                }
            }
        }
        false
    }

    fn datatype_axioms(&mut self, goal: AstId) -> Vec<AstId> {
        if self.datatypes.is_empty() {
            return Vec::new();
        }
        let terms = self.m.postorder(goal);
        let mut ax = Vec::new();
        for &t in &terms {
            let s = self.m.get_sort(t);
            if let Some(ctors) = self.datatypes.get(&s).cloned() {
                // Testers applied to t, and the exhaustiveness/exclusivity axioms.
                let testers: Vec<AstId> = ctors
                    .iter()
                    .map(|(_, _, td)| self.m.mk_app(*td, &[t]))
                    .collect();
                ax.push(self.m.mk_or(&testers));
                for i in 0..testers.len() {
                    for j in i + 1..testers.len() {
                        let both = self.m.mk_and(&[testers[i], testers[j]]);
                        ax.push(self.m.mk_not(both));
                    }
                }
                // is-Cᵢ(t) ⇒ t = Cᵢ(sel₁(t), …).
                for (idx, (cdecl, sels, _)) in ctors.iter().enumerate() {
                    let applied: Vec<AstId> =
                        sels.iter().map(|&sd| self.m.mk_app(sd, &[t])).collect();
                    let ct = self.m.mk_app(*cdecl, &applied);
                    let eq = self.m.mk_eq(t, ct);
                    let imp = self.m.mk_implies(testers[idx], eq);
                    ax.push(imp);
                }
                // Acyclicity: for a recursive datatype, a constructor is strictly
                // deeper than each recursive child, so no term is its own
                // descendant.
                if let Some(&depth) = self.dt_depth.get(&s) {
                    let dt = self.m.mk_app(depth, &[t]);
                    let zero = self.m.mk_int(0);
                    let ge0 = self.m.mk_ge(dt, zero);
                    ax.push(ge0);
                    for (idx, (_, sels, _)) in ctors.iter().enumerate() {
                        for &sd in sels {
                            // A child whose sort is *any* datatype with a depth
                            // measure must be strictly shallower — including
                            // cross-sort children of mutually-recursive datatypes
                            // (otherwise `x = nodeA(nodeB(x))` is not refuted).
                            let child_sort = match self.m.func_decl(sd).map(|d| d.range) {
                                Some(cs) => cs,
                                None => continue,
                            };
                            let child_depth = match self.dt_depth.get(&child_sort) {
                                Some(&d) => d,
                                None => continue, // non-recursive child sort (e.g. Int, enum)
                            };
                            let child = self.m.mk_app(sd, &[t]);
                            let dc = self.m.mk_app(child_depth, &[child]);
                            let gt = self.m.mk_gt(dt, dc);
                            let imp = self.m.mk_implies(testers[idx], gt);
                            ax.push(imp);
                        }
                    }
                }
            }
            // Constructor application: fix its testers and selectors. Only when
            // `t` is genuinely built by one of the constructors — a plain
            // datatype variable is not, and must stay free to be any constructor.
            if self.m.is_app(t) {
                let decl = self.m.app_decl(t);
                let sort = self.m.get_sort(t);
                if let Some(ctors) = self.datatypes.get(&sort).cloned()
                    && ctors.iter().any(|(cd, _, _)| *cd == decl)
                {
                    for (cdecl, sels, tdecl) in &ctors {
                        let is_this = *cdecl == decl;
                        let applied = self.m.mk_app(*tdecl, &[t]);
                        ax.push(if is_this {
                            applied
                        } else {
                            self.m.mk_not(applied)
                        });
                        if is_this {
                            let args = self.m.app_args(t).to_vec();
                            for (k, &sd) in sels.iter().enumerate() {
                                let sel_app = self.m.mk_app(sd, &[t]);
                                ax.push(self.m.mk_eq(sel_app, args[k]));
                            }
                        }
                    }
                }
            }
        }
        ax
    }

    /// Axioms for record/tuple datatypes mentioned in `goal`: selector-over-
    /// constructor (`selᵢ(C(a₁,…,aₙ)) = aᵢ` for each constructor application) and
    /// constructor surjectivity (`t = C(sel₁(t),…,selₙ(t))` for each record term,
    /// sound because the single constructor is total).
    fn record_axioms(&mut self, goal: AstId) -> Vec<AstId> {
        if self.records.is_empty() {
            return Vec::new();
        }
        let terms = self.m.postorder(goal);
        let mut ax = Vec::new();
        for &t in &terms {
            let s = self.m.get_sort(t);
            if let Some((cdecl, selectors)) = self.records.get(&s).cloned() {
                // Surjectivity: t = C(sel₁(t), …, selₙ(t)).
                let sels: Vec<AstId> = selectors
                    .iter()
                    .map(|&sd| self.m.mk_app(sd, &[t]))
                    .collect();
                let ct = self.m.mk_app(cdecl, &sels);
                ax.push(self.m.mk_eq(t, ct));
            }
            // Selector-over-constructor for a constructor application.
            if self.m.is_app(t) {
                let decl = self.m.app_decl(t);
                if let Some((_, selectors)) =
                    self.records.values().find(|(cd, _)| *cd == decl).cloned()
                {
                    let args = self.m.app_args(t).to_vec();
                    for (k, &sd) in selectors.iter().enumerate() {
                        let sel_app = self.m.mk_app(sd, &[t]);
                        ax.push(self.m.mk_eq(sel_app, args[k]));
                    }
                }
            }
        }
        ax
    }

    /// Axioms for the declared enumeration datatypes: the constructors of each
    /// enum are pairwise distinct, and every term of an enum sort in `goal`
    /// equals one of that enum's constructors (the domain axiom).
    fn enum_axioms(&mut self, goal: AstId) -> Vec<AstId> {
        if self.enums.is_empty() {
            return Vec::new();
        }
        let mut ax = Vec::new();
        // Constructor distinctness — always sound, independent of the goal.
        // Expanded to pairwise disequality (a bare `distinct` node is opaque to
        // the theory solvers).
        for ctors in self.enums.values().cloned().collect::<Vec<_>>() {
            for i in 0..ctors.len() {
                for j in i + 1..ctors.len() {
                    let eq = self.m.mk_eq(ctors[i], ctors[j]);
                    ax.push(self.m.mk_not(eq));
                }
            }
        }
        // Domain axiom for each enum-sorted term the goal mentions.
        for t in self.m.postorder(goal) {
            let s = self.m.get_sort(t);
            if let Some(ctors) = self.enums.get(&s).cloned() {
                let eqs: Vec<AstId> = ctors.iter().map(|&c| self.m.mk_eq(t, c)).collect();
                ax.push(self.m.mk_or(&eqs));
            }
        }
        ax
    }

    /// Axioms for the string literals mentioned in `goal`: each literal's length
    /// equals its code-point count, and distinct literals are unequal.
    fn string_axioms(&mut self, goal: AstId) -> Vec<AstId> {
        let present: Vec<AstId> = self.m.postorder(goal);
        let present_set: BTreeSet<AstId> = present.iter().copied().collect();
        let mut ax = Vec::new();
        // Non-negativity: `str.len(t) ≥ 0` for every length application in the
        // goal (a string has no negative length). Without this a symbolic
        // `str.len` is an unconstrained UF and `(= (str.len s) -1)` looks sat.
        let len_decls: BTreeSet<AstId> = self
            .str_len_decl
            .into_iter()
            .chain(self.seq_len_decls.iter().copied())
            .collect();
        if !len_decls.is_empty() {
            let zero = self.m.mk_int(0);
            // Emptiness: `str.len(s) = 0 ⇒ s = ""` — without it a symbolic `s`
            // with `len(s)=0 ∧ s≠""` looks sat (unsound).
            let str_len = self.str_len_decl;
            let empty = self.mk_str_lit("");
            for &t in &present {
                if self.m.is_app(t) && len_decls.contains(&self.m.app_decl(t)) {
                    let ge = self.m.mk_ge(t, zero);
                    ax.push(ge);
                    // Emptiness biconditional `len(s)=0 ⇔ s=empty` (both
                    // directions: catches `len=0 ∧ s≠empty` and `s=empty ∧ len>0`).
                    let empty_of = if str_len == Some(self.m.app_decl(t)) {
                        Some(empty)
                    } else if self.seq_len_decls.contains(&self.m.app_decl(t)) {
                        let s = self.m.app_args(t)[0];
                        Some(self.seq_empty_of(self.m.get_sort(s)))
                    } else {
                        None
                    };
                    if let Some(e) = empty_of {
                        let s = self.m.app_args(t)[0];
                        let len_zero = self.m.mk_eq(t, zero);
                        let is_empty = self.m.mk_eq(s, e);
                        let iff = self.m.mk_eq(len_zero, is_empty);
                        ax.push(iff);
                    }
                }
            }
        }
        // Concrete sequence lengths: `seq.len(u) = |elements|` for every
        // known-element sequence term `u` in the goal, so a variable bound to it
        // (`s = (seq.unit 1)`) inherits the length by congruence (else a
        // conflicting `seq.len(s)` looked sat).
        let seq_terms: Vec<(AstId, usize)> = present
            .iter()
            .filter_map(|&t| self.seq_of.get(&t).map(|l| (t, l.len())))
            .collect();
        for (u, n) in seq_terms {
            let d = self.seq_len_decl_for(self.m.get_sort(u));
            let lenu = self.m.mk_app(d, &[u]);
            let nv = self.m.mk_int(n as i64);
            let eq = self.m.mk_eq(lenu, nv);
            ax.push(eq);
        }
        // Additive length for symbolic concatenation: `len(s ++ t) = len s + len t`.
        // Refutes `s ++ t = seq.unit(x) ∧ len s > 0 ∧ len t > 0` (a unit has length 1).
        for (app, parts) in self.seq_concat.clone() {
            if !present_set.contains(&app) {
                continue;
            }
            let d = self.seq_len_decl_for(self.m.get_sort(app));
            let total = self.m.mk_app(d, &[app]);
            let part_lens: Vec<AstId> = parts
                .iter()
                .map(|&p| {
                    let dp = self.seq_len_decl_for(self.m.get_sort(p));
                    self.m.mk_app(dp, &[p])
                })
                .collect();
            let sum = if part_lens.len() == 1 {
                part_lens[0]
            } else {
                self.m.mk_add(&part_lens)
            };
            let eq = self.m.mk_eq(total, sum);
            ax.push(eq);
        }
        // Length links for symbolic predicates present in the goal:
        // `str.contains(s,sub) ⇒ len(s) ≥ len(sub)` etc.
        let links = self.str_pred_len.clone();
        for (app, longer, shorter) in links {
            if !present_set.contains(&app) {
                continue;
            }
            let lenf = self.str_len_fn();
            let ll = self.m.mk_app(lenf, &[longer]);
            let ls = self.m.mk_app(lenf, &[shorter]);
            let ge = self.m.mk_ge(ll, ls);
            let imp = self.m.mk_implies(app, ge);
            ax.push(imp);
        }
        // Substring/prefix/suffix monotonicity. Each `contains(x,s)`,
        // `prefixof(s,x)`, `suffixof(s,x)` (literal `s`) implies `x ⊇ s`, hence
        // `contains(x,t)` for every substring `t ⊑ s`; a prefix `s` also implies
        // `prefixof(t,x)` for prefixes `t` of `s`, symmetrically for suffixes.
        // Refutes e.g. `prefixof("ab",x) ∧ ¬contains(x,"a")`. Kind 0=contains,
        // 1=prefix, 2=suffix.
        let preds: Vec<(AstId, AstId, Vec<u32>, u8)> = present
            .iter()
            .filter_map(|&t| {
                if !self.m.is_app(t) {
                    return None;
                }
                let kind = match self
                    .str_op_decls
                    .get(&self.m.app_decl(t))
                    .map(String::as_str)
                {
                    Some("str.contains") => 0u8,
                    Some("str.prefixof") => 1,
                    Some("str.suffixof") => 2,
                    _ => return None,
                };
                let args = self.m.app_args(t);
                if args.len() != 2 {
                    return None;
                }
                let (x, lit_arg) = if kind == 0 {
                    (args[0], args[1])
                } else {
                    (args[1], args[0])
                };
                self.str_value(lit_arg).map(|lit| (t, x, lit, kind))
            })
            .collect();
        let is_sub = |t: &[u32], s: &[u32]| t.is_empty() || s.windows(t.len()).any(|w| w == t);
        for (ai, xi, si, ki) in &preds {
            for (aj, xj, sj, kj) in &preds {
                if ai == aj || xi != xj {
                    continue;
                }
                let implies = match kj {
                    0 => is_sub(sj, si),
                    1 => *ki == 1 && sj.len() <= si.len() && si[..sj.len()] == sj[..],
                    _ => *ki == 2 && sj.len() <= si.len() && si[si.len() - sj.len()..] == sj[..],
                };
                if implies {
                    let imp = self.m.mk_implies(*ai, *aj);
                    ax.push(imp);
                }
            }
        }
        // Resolve a predicate against a concrete `x` fixed by `x = L` (L literal):
        // `(x = L) ⇒ [¬]pred`. Refutes `x = "hello" ∧ ¬contains(x, "ell")`.
        let str_eqs: Vec<(AstId, AstId, Vec<u32>)> = present
            .iter()
            .filter_map(|&t| {
                if !self.m.is_eq(t) {
                    return None;
                }
                let a = self.m.app_args(t);
                if a.len() != 2 {
                    return None;
                }
                for (v, lit) in [(a[0], a[1]), (a[1], a[0])] {
                    if let Some(l) = self.str_value(lit) {
                        return Some((t, v, l));
                    }
                }
                None
            })
            .collect();
        for (app, x, lit, kind) in &preds {
            for (eq, v, l) in &str_eqs {
                if v != x {
                    continue;
                }
                let holds = match kind {
                    0 => is_sub(lit, l),
                    1 => lit.len() <= l.len() && l[..lit.len()] == lit[..],
                    _ => lit.len() <= l.len() && l[l.len() - lit.len()..] == lit[..],
                };
                let concl = if holds { *app } else { self.m.mk_not(*app) };
                let imp = self.m.mk_implies(*eq, concl);
                ax.push(imp);
            }
        }
        // Regex membership length restriction: `in_re(x, r) ⇒ len x ∈ L(r)` for a
        // constant regex `r`, expressed as a disjunction over the achievable
        // lengths ≤ MAX (with a `> MAX` escape). Refutes `x ∈ (ab)* ∧ len x = 3`.
        const RLMAX: usize = 24;
        let in_res: Vec<(AstId, AstId, AstId)> = present
            .iter()
            .filter_map(|&t| {
                if self.m.is_app(t)
                    && self
                        .str_op_decls
                        .get(&self.m.app_decl(t))
                        .map(String::as_str)
                        == Some("str.in_re")
                {
                    let a = self.m.app_args(t);
                    if a.len() == 2 {
                        return Some((t, a[0], a[1]));
                    }
                }
                None
            })
            .collect();
        for (app, x, r) in &in_res {
            // Only refute against a length the goal pins `x` to (avoids a costly
            // membership disjunction): if `x ∈ r` yet `len x = k` is unachievable,
            // add `in_re(x,r) ⇒ len x ≠ k`.
            let Some(k) = self.str_exact_len(goal, *x) else {
                continue;
            };
            if k > RLMAX {
                continue;
            }
            let Some(regex) = self.regex_of.get(r).cloned() else {
                continue;
            };
            let Some(lens) = regex.lengths(RLMAX) else {
                continue;
            };
            if !lens[k] {
                let lenf = self.str_len_fn();
                let lx = self.m.mk_app(lenf, &[*x]);
                let kv = self.m.mk_int(k as i64);
                let eq = self.m.mk_eq(lx, kv);
                let ne = self.m.mk_not(eq);
                let imp = self.m.mk_implies(*app, ne);
                ax.push(imp);
            }
        }
        // `str.at` bounds: `str.at x k` is a single character when `0 ≤ k < len x`
        // and the empty string otherwise. Refutes `str.at x 3 = "a" ∧ len x = 2`.
        let ats: Vec<(AstId, AstId, i64)> = present
            .iter()
            .filter_map(|&t| {
                if self.m.is_app(t)
                    && self
                        .str_op_decls
                        .get(&self.m.app_decl(t))
                        .map(String::as_str)
                        == Some("str.at")
                {
                    let a = self.m.app_args(t);
                    if a.len() == 2
                        && let Some(k) = self
                            .m
                            .as_numeral(a[1])
                            .and_then(|r| r.to_integer())
                            .and_then(|i| i.to_i64())
                    {
                        return Some((t, a[0], k));
                    }
                }
                None
            })
            .collect();
        for (app, x, k) in &ats {
            let lenf = self.str_len_fn();
            let lx = self.m.mk_app(lenf, &[*x]);
            let atlen = self.m.mk_app(lenf, &[*app]);
            let zero = self.m.mk_int(0);
            if *k < 0 {
                // Negative index ⇒ empty ⇒ `len(app) = 0`.
                let e = self.m.mk_eq(atlen, zero);
                ax.push(e);
            } else {
                let kv = self.m.mk_int(*k);
                // Out of bounds `k ≥ len x ⇒ len(app) = 0` (a non-empty `str.at x k`
                // then contradicts by length congruence).
                let oob = self.m.mk_ge(kv, lx);
                let empty_len = self.m.mk_eq(atlen, zero);
                ax.push(self.m.mk_implies(oob, empty_len));
                // In bounds `k < len x ⇒ len(app) = 1`.
                let kv2 = self.m.mk_int(*k);
                let inb = self.m.mk_lt(kv2, lx);
                let one = self.m.mk_int(1);
                let len_one = self.m.mk_eq(atlen, one);
                ax.push(self.m.mk_implies(inb, len_one));
            }
        }
        // `str.prefixof p x ⇒ str.at x k = p[k]` for a literal `p` and constant
        // `k < len p` — the prefix pins the first `len p` characters. Refutes
        // `str.at x 0 = "a" ∧ str.prefixof "b" x`.
        let prefs: Vec<(AstId, Vec<u32>, AstId)> = present
            .iter()
            .filter_map(|&t| {
                if self.m.is_app(t)
                    && self
                        .str_op_decls
                        .get(&self.m.app_decl(t))
                        .map(String::as_str)
                        == Some("str.prefixof")
                {
                    let a = self.m.app_args(t);
                    if a.len() == 2
                        && let Some(p) = self.str_value(a[0])
                    {
                        return Some((t, p, a[1]));
                    }
                }
                None
            })
            .collect();
        for (pm, pchars, px) in &prefs {
            for (am, ax_x, k) in &ats {
                if px == ax_x && *k >= 0 && (*k as usize) < pchars.len() {
                    let ch = self.mk_str_lit(&code_points_to_string(&[pchars[*k as usize]]));
                    let eq = self.m.mk_eq(*am, ch);
                    ax.push(self.m.mk_implies(*pm, eq));
                }
            }
        }
        // `str.substr x i n` length (constant `i ≥ 0`, `n`): the extracted length
        // is `min(n, max(0, len x − i))`. Refutes `str.substr x 0 2 = "ab" ∧ len x = 1`.
        let subs: Vec<(AstId, AstId, i64, i64)> = present
            .iter()
            .filter_map(|&t| {
                if self.m.is_app(t)
                    && self
                        .str_op_decls
                        .get(&self.m.app_decl(t))
                        .map(String::as_str)
                        == Some("str.substr")
                {
                    let a = self.m.app_args(t);
                    let num = |u: AstId| {
                        self.m
                            .as_numeral(u)
                            .and_then(|r| r.to_integer())
                            .and_then(|i| i.to_i64())
                    };
                    if a.len() == 3
                        && let (Some(i), Some(nn)) = (num(a[1]), num(a[2]))
                    {
                        return Some((t, a[0], i, nn));
                    }
                }
                None
            })
            .collect();
        for (app, x, i, nn) in &subs {
            let lenf = self.str_len_fn();
            let lx = self.m.mk_app(lenf, &[*x]);
            let sublen = self.m.mk_app(lenf, &[*app]);
            let zero = self.m.mk_int(0);
            if *i < 0 || *nn <= 0 {
                let e = self.m.mk_eq(sublen, zero);
                ax.push(e);
                continue;
            }
            let iv = self.m.mk_int(*i);
            let nv = self.m.mk_int(*nn);
            // i ≥ len x ⇒ len(sub) = 0.
            let oob = self.m.mk_ge(iv, lx);
            let e0 = self.m.mk_eq(sublen, zero);
            ax.push(self.m.mk_implies(oob, e0));
            // i < len x ∧ len x − i ≥ n ⇒ len(sub) = n.
            let iv2 = self.m.mk_int(*i);
            let inb = self.m.mk_lt(iv2, lx);
            let iv3 = self.m.mk_int(*i);
            let avail = self.m.mk_sub(&[lx, iv3]); // len x − i
            let enough = self.m.mk_ge(avail, nv);
            let c1 = self.m.mk_and(&[inb, enough]);
            let en = self.m.mk_eq(sublen, nv);
            ax.push(self.m.mk_implies(c1, en));
            // i < len x ∧ len x − i < n ⇒ len(sub) = len x − i.
            let iv4 = self.m.mk_int(*i);
            let inb2 = self.m.mk_lt(iv4, lx);
            let iv5 = self.m.mk_int(*i);
            let avail2 = self.m.mk_sub(&[lx, iv5]);
            let iv6 = self.m.mk_int(*i);
            let avail3 = self.m.mk_sub(&[lx, iv6]);
            let short = self.m.mk_lt(avail2, nv);
            let c2 = self.m.mk_and(&[inb2, short]);
            let eavail = self.m.mk_eq(sublen, avail3);
            ax.push(self.m.mk_implies(c2, eavail));
        }
        // `str.to_code x`: a valid code (≥ 0) requires a single character, so
        // `str.to_code x ≥ 0 ⇒ len x = 1`. Refutes `str.to_code x = 97 ∧ len x = 2`.
        // `str.indexof x t i`: a found index (≥ 0) leaves room for the needle, so
        // `idx ≥ 0 ⇒ idx + len t ≤ len x`. Refutes `indexof x "a" 0 = 5 ∧ len x = 3`.
        let ops: Vec<(AstId, String, Vec<AstId>)> = present
            .iter()
            .filter_map(|&t| {
                if !self.m.is_app(t) {
                    return None;
                }
                self.str_op_decls.get(&self.m.app_decl(t)).and_then(|op| {
                    matches!(op.as_str(), "str.to_code" | "str.to-code" | "str.indexof")
                        .then(|| (t, op.clone(), self.m.app_args(t).to_vec()))
                })
            })
            .collect();
        for (app, op, args) in &ops {
            let lenf = self.str_len_fn();
            let zero = self.m.mk_int(0);
            if op.starts_with("str.to") && !args.is_empty() {
                let lx = self.m.mk_app(lenf, &[args[0]]);
                let one = self.m.mk_int(1);
                let nonneg = self.m.mk_ge(*app, zero);
                let len1 = self.m.mk_eq(lx, one);
                ax.push(self.m.mk_implies(nonneg, len1));
            } else if op == "str.indexof" && args.len() >= 2 {
                let lx = self.m.mk_app(lenf, &[args[0]]);
                let lt = if let Some(v) = self.str_value(args[1]) {
                    self.m.mk_int(v.len() as i64)
                } else {
                    self.m.mk_app(lenf, &[args[1]])
                };
                let end = self.m.mk_add(&[*app, lt]);
                let fits = self.m.mk_le(end, lx);
                let found = self.m.mk_ge(*app, zero);
                ax.push(self.m.mk_implies(found, fits));
            }
        }
        // `str.contains x t ⟺ str.indexof x t 0 ≥ 0`: a match exists iff its first
        // index is found. Refutes `indexof x "z" 0 = −1 ∧ contains x "z"`.
        let pred_of = |m: &AstManager, t: AstId, name: &str| -> Option<Vec<AstId>> {
            (m.is_app(t) && self.str_op_decls.get(&m.app_decl(t)).map(String::as_str) == Some(name))
                .then(|| m.app_args(t).to_vec())
        };
        let contains_m: Vec<(AstId, AstId, AstId)> = present
            .iter()
            .filter_map(|&t| {
                pred_of(&self.m, t, "str.contains")
                    .and_then(|a| (a.len() == 2).then_some((t, a[0], a[1])))
            })
            .collect();
        let indexof0_m: Vec<(AstId, AstId, AstId)> = present
            .iter()
            .filter_map(|&t| {
                pred_of(&self.m, t, "str.indexof").and_then(|a| {
                    (a.len() == 3
                        && self
                            .m
                            .as_numeral(a[2])
                            .and_then(|r| r.to_integer())
                            .and_then(|i| i.to_i64())
                            == Some(0))
                    .then_some((t, a[0], a[1]))
                })
            })
            .collect();
        for (cm, cx, ct) in &contains_m {
            for (im, ix, it) in &indexof0_m {
                if cx == ix && ct == it {
                    let zero = self.m.mk_int(0);
                    let ge = self.m.mk_ge(*im, zero);
                    ax.push(self.m.mk_eq(*cm, ge));
                }
            }
        }
        // `str.<` is a strict order: antisymmetry `(a<b) ⇒ ¬(b<a)` and transitivity
        // `(a<b) ∧ (b<c) ⇒ (a<c)`. Refutes `x<y ∧ y<x` and cyclic `x<y<z<x`.
        let lts: Vec<(AstId, AstId, AstId)> = present
            .iter()
            .filter_map(|&t| {
                if self.m.is_app(t)
                    && self
                        .str_op_decls
                        .get(&self.m.app_decl(t))
                        .map(String::as_str)
                        == Some("str.<")
                {
                    let a = self.m.app_args(t);
                    if a.len() == 2 {
                        return Some((t, a[0], a[1]));
                    }
                }
                None
            })
            .collect();
        if !lts.is_empty() {
            // Each `str.<` occurrence is a content-fresh marker, so reuse the goal's
            // marker for an existing edge and build a *consistent* one (shared decl,
            // interned by args) for a derived edge, keyed in `edge`.
            let lt_decl = self.m.app_decl(lts[0].0);
            let mut edge: BTreeMap<(AstId, AstId), AstId> =
                lts.iter().map(|(m, a, b)| ((*a, *b), *m)).collect();
            let mut nodes: Vec<AstId> = Vec::new();
            for (_, a, b) in &lts {
                for x in [a, b] {
                    if !nodes.contains(x) {
                        nodes.push(*x);
                    }
                }
            }
            if nodes.len() <= 8 {
                for ai in 0..nodes.len() {
                    for bi in 0..nodes.len() {
                        if ai == bi {
                            continue;
                        }
                        let (a, b) = (nodes[ai], nodes[bi]);
                        let mab = *edge
                            .entry((a, b))
                            .or_insert_with(|| self.m.mk_app(lt_decl, &[a, b]));
                        let mba = *edge
                            .entry((b, a))
                            .or_insert_with(|| self.m.mk_app(lt_decl, &[b, a]));
                        // antisymmetry: `(a<b) ⇒ ¬(b<a)`
                        let nba = self.m.mk_not(mba);
                        ax.push(self.m.mk_implies(mab, nba));
                        // strictness: `(a<b) ⇒ a ≠ b`
                        let eqab = self.m.mk_eq(a, b);
                        let neqab = self.m.mk_not(eqab);
                        ax.push(self.m.mk_implies(mab, neqab));
                        // transitivity: `(a<b) ∧ (b<c) ⇒ (a<c)`
                        for (ci, &c) in nodes.iter().enumerate() {
                            if ci == ai || ci == bi {
                                continue;
                            }
                            let mbc = *edge
                                .entry((b, c))
                                .or_insert_with(|| self.m.mk_app(lt_decl, &[b, c]));
                            let mac = *edge
                                .entry((a, c))
                                .or_insert_with(|| self.m.mk_app(lt_decl, &[a, c]));
                            let and = self.m.mk_and(&[mab, mbc]);
                            ax.push(self.m.mk_implies(and, mac));
                        }
                    }
                }
            }
        }
        // `str.<=` is a total order: antisymmetry `(a≤b) ∧ (b≤a) ⇒ a=b`,
        // transitivity `(a≤b) ∧ (b≤c) ⇒ (a≤c)`, and reflexivity `a≤a`. Refutes
        // `x≤y ∧ y≤x ∧ x≠y`.
        let les: Vec<(AstId, AstId, AstId)> = present
            .iter()
            .filter_map(|&t| {
                if self.m.is_app(t)
                    && self
                        .str_op_decls
                        .get(&self.m.app_decl(t))
                        .map(String::as_str)
                        == Some("str.<=")
                {
                    let a = self.m.app_args(t);
                    if a.len() == 2 {
                        return Some((t, a[0], a[1]));
                    }
                }
                None
            })
            .collect();
        if !les.is_empty() {
            let le_decl = self.m.app_decl(les[0].0);
            let mut edge: BTreeMap<(AstId, AstId), AstId> =
                les.iter().map(|(m, a, b)| ((*a, *b), *m)).collect();
            let mut nodes: Vec<AstId> = Vec::new();
            for (_, a, b) in &les {
                for x in [a, b] {
                    if !nodes.contains(x) {
                        nodes.push(*x);
                    }
                }
            }
            if nodes.len() <= 8 {
                for ai in 0..nodes.len() {
                    for bi in 0..nodes.len() {
                        if ai == bi {
                            continue;
                        }
                        let (a, b) = (nodes[ai], nodes[bi]);
                        let mab = *edge
                            .entry((a, b))
                            .or_insert_with(|| self.m.mk_app(le_decl, &[a, b]));
                        let mba = *edge
                            .entry((b, a))
                            .or_insert_with(|| self.m.mk_app(le_decl, &[b, a]));
                        // antisymmetry: `(a≤b) ∧ (b≤a) ⇒ a=b`
                        let and = self.m.mk_and(&[mab, mba]);
                        let eqab = self.m.mk_eq(a, b);
                        ax.push(self.m.mk_implies(and, eqab));
                        // transitivity: `(a≤b) ∧ (b≤c) ⇒ (a≤c)`
                        for (ci, &c) in nodes.iter().enumerate() {
                            if ci == ai || ci == bi {
                                continue;
                            }
                            let mbc = *edge
                                .entry((b, c))
                                .or_insert_with(|| self.m.mk_app(le_decl, &[b, c]));
                            let mac = *edge
                                .entry((a, c))
                                .or_insert_with(|| self.m.mk_app(le_decl, &[a, c]));
                            let and2 = self.m.mk_and(&[mab, mbc]);
                            ax.push(self.m.mk_implies(and2, mac));
                        }
                    }
                }
                // reflexivity `a ≤ a`.
                for &a in &nodes {
                    let maa = *edge
                        .entry((a, a))
                        .or_insert_with(|| self.m.mk_app(le_decl, &[a, a]));
                    ax.push(maa);
                }
            }
        }
        // Cross-link the two orders: `a<b ⇒ a≤b` and `a<b ⇒ ¬(b≤a)`, sharing the
        // `str.<=` decl so the ≤ antisymmetry/transitivity axioms see the derived
        // edges. Refutes `x≤y ∧ y≤z ∧ z<x`.
        if !lts.is_empty() && !les.is_empty() {
            let le_decl = self.m.app_decl(les[0].0);
            for (mlt, a, b) in &lts {
                let mab_le = self.m.mk_app(le_decl, &[*a, *b]);
                ax.push(self.m.mk_implies(*mlt, mab_le));
                let mba_le = self.m.mk_app(le_decl, &[*b, *a]);
                let nba = self.m.mk_not(mba_le);
                ax.push(self.m.mk_implies(*mlt, nba));
            }
        }
        // Constant length upper bounds (`str.len(marker) ≤ k`).
        let ubs = self.str_len_ub.clone();
        for (app, k) in ubs {
            if !present_set.contains(&app) {
                continue;
            }
            let lenf = self.str_len_fn();
            let la = self.m.mk_app(lenf, &[app]);
            let kv = self.m.mk_int(k);
            let le = self.m.mk_le(la, kv);
            ax.push(le);
        }
        if self.str_lits.is_empty() {
            return ax;
        }
        // Literals occurring in the goal, plus every single-character literal
        // (cheap, and covers the per-character literals introduced by the
        // prefix/`str.at` axioms above), with their lengths.
        let lits: Vec<(AstId, i64)> = self
            .str_lits
            .iter()
            .filter(|(text, c)| present_set.contains(*c) || text.chars().count() == 1)
            .map(|(text, &c)| (c, text.chars().count() as i64))
            .collect();
        if !lits.is_empty() {
            let lenf = self.str_len_fn();
            for &(c, n) in &lits {
                let lc = self.m.mk_app(lenf, &[c]);
                let nv = self.m.mk_int(n);
                let eq = self.m.mk_eq(lc, nv);
                ax.push(eq);
            }
            for i in 0..lits.len() {
                for j in i + 1..lits.len() {
                    let eq = self.m.mk_eq(lits[i].0, lits[j].0);
                    ax.push(self.m.mk_not(eq));
                }
            }
        }
        ax
    }

    /// Re-fold symbolic string markers whose arguments have become concrete
    /// (after substituting string variables by literals): a marker `op(a,…)`
    /// with literal args is replaced by `string_op(op, args)` (which folds to a
    /// literal), and a `str.len` of a literal by its concrete length.
    fn refold_str_markers(&mut self, t: AstId, memo: &mut BTreeMap<AstId, AstId>) -> AstId {
        if let Some(&r) = memo.get(&t) {
            return r;
        }
        let out = if self.m.is_app(t) && !self.m.app_args(t).is_empty() {
            let decl = self.m.app_decl(t);
            let raw_args = self.m.app_args(t).to_vec();
            let args: Vec<AstId> = raw_args
                .iter()
                .map(|&a| self.refold_str_markers(a, memo))
                .collect();
            let is_len = self.str_len_decl == Some(decl) || self.seq_len_decls.contains(&decl);
            if is_len && args.len() == 1 {
                if let Some(v) = self.str_value(args[0]) {
                    self.m.mk_int(v.len() as i64)
                } else if let Some(l) = self.seq_of.get(&args[0]) {
                    self.m.mk_int(l.len() as i64)
                } else {
                    self.m.mk_app(decl, &args)
                }
            } else if let Some(op) = self.str_op_decls.get(&decl).cloned() {
                self.string_op(&op, &args)
                    .unwrap_or_else(|_| self.m.mk_app(decl, &args))
            } else if let Some(op) = self.seqop_ops.get(&decl).cloned() {
                self.seq_op(&op, &args)
                    .unwrap_or_else(|_| self.m.mk_app(decl, &args))
            } else {
                self.m.mk_app(decl, &args)
            }
        } else {
            t
        };
        memo.insert(t, out);
        out
    }

    /// Bounded, sound SAT witness for a goal with symbolic `div`/`mod` divisors:
    /// try a small concrete value for each divisor variable; substituting it makes
    /// the Euclidean product `b·q` linear, so a confirmed (non-nonlinear) `sat` is
    /// a real model. Returns `None` if no small divisor works.
    fn try_divmod_witness(&mut self, goal: AstId) -> Option<Model> {
        let present: BTreeSet<AstId> = self.m.postorder(goal).into_iter().collect();
        let divs: Vec<AstId> = self
            .symbolic_divisors
            .iter()
            .copied()
            .filter(|&d| {
                present.contains(&d)
                    && self.m.is_uninterp_const(d)
                    && self.m.is_int_sort(self.m.get_sort(d))
            })
            .collect();
        if divs.is_empty() || divs.len() > 2 {
            return None;
        }
        let mut vals: Vec<i64> = alloc::vec![
            // 0 first: a zero divisor makes `div`/`mod` unconstrained (SMT-LIB
            // leaves them unspecified), so many otherwise-hard goals are satisfied
            // by the divisor being 0 (e.g. `mod(-29,y) ≤ -8`, impossible for y≠0).
            0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, -1, -2, -3, -4, -5, -6, -7,
            -8,
        ];
        // Try divisors derived from the goal's integer constants. A satisfying
        // divisor for `mod(a,y) ⋈ k` typically relates to `a` and `k` — e.g.
        // `mod(-26,y) ≥ 11` needs `y = ±37 = ±(26+11)`, `mod(12,y) ≥ 8 ∧ y<0`
        // needs `y = -13` (any `|y| > 12`). So take each constant with both
        // signs, ±1 around it, and all pairwise sums/differences.
        let mut consts: Vec<i64> = present
            .iter()
            .filter_map(|t| self.m.as_numeral(*t).and_then(|r| r.to_integer()))
            .filter_map(|v| v.to_i64())
            .filter(|n| n.abs() <= 2000)
            .collect();
        consts.sort_unstable();
        consts.dedup();
        consts.truncate(16); // bound the O(n²) pairwise blow-up
        let mut cand_set: Vec<i64> = Vec::new();
        for &a in &consts {
            for d in [a, a + 1, a - 1] {
                cand_set.push(d);
                cand_set.push(-d);
            }
            for &b in &consts {
                for d in [a + b, a - b, a.saturating_add(b) + 1] {
                    cand_set.push(d);
                    cand_set.push(-d);
                }
            }
        }
        for cand in cand_set {
            if vals.len() >= 220 {
                break; // keep the search bounded
            }
            if cand != 0 && cand.abs() <= 4000 && !vals.contains(&cand) {
                vals.push(cand);
            }
        }
        const MAX_TRIES: usize = 800;
        let mut idx = alloc::vec![0usize; divs.len()];
        let mut tries = 0;
        loop {
            if tries >= MAX_TRIES {
                return None;
            }
            tries += 1;
            let subst: Vec<(AstId, AstId)> = divs
                .iter()
                .enumerate()
                .map(|(k, &d)| (d, self.m.mk_int(vals[idx[k]])))
                .collect();
            let g = crate::rewriter::substitute(&mut self.m, goal, &subst);
            let g = crate::rewriter::simplify(&mut self.m, g);
            // Only trust the verdict once the concretised goal is linear (the
            // nonlinear `b·q` is now `value·q`); then a `sat` is a genuine model.
            if !self.arith_nonlinear(g)
                && let (SmtResult::Sat, m) = check_model(&self.m, g)
            {
                return m;
            }
            let mut k = 0;
            loop {
                if k == divs.len() {
                    return None;
                }
                idx[k] += 1;
                if idx[k] < vals.len() {
                    break;
                }
                idx[k] = 0;
                k += 1;
            }
        }
    }

    /// Prove **UNSAT** for a goal whose only symbolic divisor `d` occurs solely
    /// inside `div`/`mod` terms with *constant* dividends. After lifting, each
    /// such term became a quotient `q` / remainder `r` linked by the Euclidean
    /// identity `a = d·q + r`. The quotient `q = div(a,d)` is **constant** for
    /// every `|d| > M = max|dividend|` (`0` if `a ≥ 0`, else `∓1` for the ±∞
    /// tail), so the value set over all `d` is finite: enumerating `|d| ≤ M+1`
    /// concretely, plus the two symbolic tails `d > M` / `d < −M` with each `q`
    /// pinned to its stable value (leaving `r` linearly determined), is a
    /// *complete* decision. Returns `true` only when **every** case is definitely
    /// (and linearly, hence trustworthily) unsatisfiable; otherwise it bails.
    fn divmod_complete_unsat(&mut self, goal: AstId) -> bool {
        // The single symbolic divisor present in the goal.
        let present: BTreeSet<AstId> = self.m.postorder(goal).into_iter().collect();
        let divisors: BTreeSet<AstId> = self
            .symbolic_divmod
            .iter()
            .map(|&(_, b, _, _)| b)
            .filter(|b| present.contains(b))
            .collect();
        if divisors.len() != 1 {
            return false; // exactly one symbolic divisor handled
        }
        let d = *divisors.iter().next().unwrap();
        if !self.m.is_uninterp_const(d) {
            return false;
        }
        // The (dividend, quotient) pairs for this divisor; every dividend must be
        // a concrete integer, and each quotient must actually occur in the goal.
        let mut pairs: Vec<(i64, AstId)> = Vec::new(); // (dividend, quotient q)
        for &(a, b, q, _r) in &self.symbolic_divmod {
            if b != d || !present.contains(&q) {
                continue;
            }
            let Some(av) = self
                .m
                .as_numeral(a)
                .and_then(|r| r.to_integer())
                .and_then(|v| v.to_i64())
            else {
                return false; // non-constant dividend
            };
            pairs.push((av, q));
        }
        if pairs.is_empty() {
            return false;
        }
        let m_max = pairs.iter().map(|&(a, _)| a.abs()).max().unwrap_or(0);
        if m_max > 128 {
            return false; // enumeration would be too wide
        }
        let range = m_max + 1;
        // 1. Finite enumeration of |d| ≤ M+1. Substituting a concrete `d` makes
        //    the Euclidean `d·q` linear (`d = 0` leaves q,r free via the vacuous
        //    guards) — every case must be linearly UNSAT.
        for v in -range..=range {
            let sub = alloc::vec![(d, self.m.mk_int(v))];
            let g = crate::rewriter::substitute(&mut self.m, goal, &sub);
            let g = crate::rewriter::simplify(&mut self.m, g);
            if self.arith_nonlinear(g) {
                return false;
            }
            if check_model(&self.m, g).0 != SmtResult::Unsat {
                return false;
            }
        }
        // 2. The two symbolic tails: pin each quotient to its stable value and
        //    require `d` beyond the stabilisation threshold `M`. The remainders
        //    stay linearly determined by the (now-linear) Euclidean identity.
        for positive in [true, false] {
            let sub: Vec<(AstId, AstId)> = pairs
                .iter()
                .map(|&(a, q)| {
                    let stable = if a >= 0 {
                        0
                    } else if positive {
                        -1
                    } else {
                        1
                    };
                    (q, self.m.mk_int(stable))
                })
                .collect();
            let g = crate::rewriter::substitute(&mut self.m, goal, &sub);
            let bound = if positive {
                let mm = self.m.mk_int(m_max);
                self.m.mk_gt(d, mm)
            } else {
                let mm = self.m.mk_int(-m_max);
                self.m.mk_lt(d, mm)
            };
            let g = self.m.mk_and(&[g, bound]);
            let g = crate::rewriter::simplify(&mut self.m, g);
            if self.arith_nonlinear(g) {
                return false;
            }
            if check_model(&self.m, g).0 != SmtResult::Unsat {
                return false;
            }
        }
        true
    }

    /// If the goal pins string variable `v` to an exact length via
    /// `(= (str.len v) k)`, return `k` — so the witness search can generate
    /// exactly-length-`k` candidates (needed for word equations with a fixed
    /// length, e.g. `len x = 4 ∧ x·y = y·x`).
    fn str_exact_len(&self, goal: AstId, v: AstId) -> Option<usize> {
        let is_len_of = |a: AstId| -> bool {
            self.m.is_app(a) && {
                let d = self.m.app_decl(a);
                (self.str_len_decl == Some(d) || self.seq_len_decls.contains(&d))
                    && self.m.app_args(a).first() == Some(&v)
            }
        };
        for t in self.m.postorder(goal) {
            if !self.m.is_eq(t) {
                continue;
            }
            let args = self.m.app_args(t);
            if args.len() != 2 {
                continue;
            }
            for (a, b) in [(args[0], args[1]), (args[1], args[0])] {
                if is_len_of(a)
                    && let Some(k) = self
                        .m
                        .as_numeral(b)
                        .and_then(|r| r.to_integer())
                        .and_then(|i| i.to_i64())
                    && (0..=64).contains(&k)
                {
                    return Some(k as usize);
                }
            }
        }
        None
    }

    /// Bounded, sound SAT witness for a goal with symbolic **integer sequences**:
    /// substitute short concrete sequences for each symbolic seq variable, re-fold
    /// the sequence markers, and confirm with the core solver. A found witness is a
    /// real `sat`; failure keeps the sound `unknown`.
    fn try_seq_witness(&mut self, goal: AstId) -> Option<Model> {
        let int_sort = self.m.mk_int_sort();
        let mut vars: Vec<AstId> = Vec::new();
        for t in self.m.postorder(goal) {
            if self.m.is_app(t)
                && self.m.app_args(t).is_empty()
                && !self.seq_of.contains_key(&t)
                && self.seq_elem_sort(self.m.get_sort(t)) == Some(int_sort)
                && !vars.contains(&t)
            {
                vars.push(t);
            }
        }
        if vars.is_empty() || vars.len() > 2 {
            return None;
        }
        // Integer element candidates: 0,1,2 plus any small integer literal in the
        // goal (so `nth s 0 = 7` can place the `7`) — including the elements of
        // concrete sequences like `seq.unit 5`, whose value is held in `seq_of`
        // metadata rather than as an AST subterm.
        let mut elems: Vec<i64> = alloc::vec![0, 1, 2];
        let push_elem = |elems: &mut Vec<i64>, v: i64| {
            if (-100..=100).contains(&v) && !elems.contains(&v) && elems.len() < 8 {
                elems.push(v);
            }
        };
        for t in self.m.postorder(goal) {
            if let Some(v) = self
                .m
                .as_numeral(t)
                .and_then(|r| r.to_integer())
                .and_then(|i| i.to_i64())
            {
                push_elem(&mut elems, v);
            }
            if let Some(content) = self.seq_of.get(&t) {
                for &e in content.clone().iter() {
                    if let Some(v) = self
                        .m
                        .as_numeral(e)
                        .and_then(|r| r.to_integer())
                        .and_then(|i| i.to_i64())
                    {
                        push_elem(&mut elems, v);
                    }
                }
            }
        }
        let max_len = if vars.len() == 1 { 4 } else { 2 };
        let mut cands: Vec<Vec<i64>> = alloc::vec![Vec::new()];
        let mut frontier: Vec<Vec<i64>> = alloc::vec![Vec::new()];
        for _ in 0..max_len {
            let mut next = Vec::new();
            for base in &frontier {
                for &e in &elems {
                    let mut s = base.clone();
                    s.push(e);
                    next.push(s);
                }
            }
            cands.extend(next.iter().cloned());
            frontier = next;
        }
        const MAX_TRIES: usize = 900;
        let mut idx = alloc::vec![0usize; vars.len()];
        let mut tries = 0;
        loop {
            if tries >= MAX_TRIES {
                return None;
            }
            tries += 1;
            let subst: Vec<(AstId, AstId)> = vars
                .iter()
                .enumerate()
                .map(|(k, &v)| {
                    let es: Vec<AstId> = cands[idx[k]].iter().map(|&n| self.m.mk_int(n)).collect();
                    (v, self.mk_seq(es))
                })
                .collect();
            let g1 = crate::rewriter::substitute(&mut self.m, goal, &subst);
            let mut memo = BTreeMap::new();
            let g2 = self.refold_str_markers(g1, &mut memo);
            let clean = !self.m.postorder(g2).iter().any(|&t| {
                self.str_symbolic.contains(&t)
                    || (self.m.is_app(t) && self.seqop_ops.contains_key(&self.m.app_decl(t)))
            });
            if clean {
                // Concrete sequences are uninterpreted constants; without (dis)
                // equality axioms `check_model` could equate two *different* ones
                // (a spurious `sat`). Link every pair by content.
                let seqs: Vec<AstId> = self
                    .m
                    .postorder(g2)
                    .into_iter()
                    .filter(|t| self.seq_of.contains_key(t))
                    .collect();
                let mut conj: Vec<AstId> = Vec::new();
                for i in 0..seqs.len() {
                    for j in i + 1..seqs.len() {
                        let same = self.seq_of[&seqs[i]] == self.seq_of[&seqs[j]];
                        let eq = self.m.mk_eq(seqs[i], seqs[j]);
                        conj.push(if same { eq } else { self.m.mk_not(eq) });
                    }
                }
                let g3 = if conj.is_empty() {
                    g2
                } else {
                    conj.push(g2);
                    self.m.mk_and(&conj)
                };
                let (res, m) = check_model(&self.m, g3);
                if res == SmtResult::Sat {
                    // `check_model` may report `sat` without a model when the goal
                    // folded to a ground truth; the assignment still exists.
                    return Some(m.unwrap_or_else(|| Model::from_bv(BTreeMap::new())));
                }
            }
            let mut k = 0;
            loop {
                if k == vars.len() {
                    return None;
                }
                idx[k] += 1;
                if idx[k] < cands.len() {
                    break;
                }
                idx[k] = 0;
                k += 1;
            }
        }
    }

    /// Bounded, sound search for a concrete satisfying assignment to a goal with
    /// symbolic strings: try short candidate strings for each free string
    /// variable, re-fold the markers to concrete values, and confirm with the
    /// core solver. A found witness is a real `sat`; failure returns `None`
    /// (keeping the sound `unknown`).
    /// Verify an abstract model by substituting each string variable's
    /// model-implied literal into `goal`, refolding, and re-checking with the
    /// string axioms — turning a possibly-spurious symbolic `sat` into a confirmed
    /// concrete one. `None` if the model does not pin every string variable.
    fn verify_string_model(&mut self, goal: AstId, model: &mut Model) -> Option<Model> {
        let string_sort = self.string_sort?;
        let lit_consts: BTreeSet<AstId> = self.str_lits.values().copied().collect();
        let mut vars: Vec<AstId> = Vec::new();
        for t in self.m.postorder(goal) {
            if self.m.is_app(t)
                && self.m.app_args(t).is_empty()
                && self.m.get_sort(t) == string_sort
                && !lit_consts.contains(&t)
                && !vars.contains(&t)
            {
                vars.push(t);
            }
        }
        if vars.is_empty() {
            return None;
        }
        let lits: Vec<AstId> = lit_consts.iter().copied().collect();
        let mut subst: Vec<(AstId, AstId)> = Vec::new();
        for &v in &vars {
            // The literal this variable equals under the model (if any).
            let lit = lits.iter().find(|&&l| model.terms_equal(&self.m, v, l))?;
            subst.push((v, *lit));
        }
        let g1 = crate::rewriter::substitute(&mut self.m, goal, &subst);
        let mut memo = BTreeMap::new();
        let g2 = self.refold_str_markers(g1, &mut memo);
        let clean = !self
            .m
            .postorder(g2)
            .iter()
            .any(|t| self.str_symbolic.contains(t) || self.str_op_marker(*t));
        if !clean {
            return None;
        }
        let mut conj = self.string_axioms(g2);
        let g3 = if conj.is_empty() {
            g2
        } else {
            conj.push(g2);
            self.m.mk_and(&conj)
        };
        let (res, m) = check_model(&self.m, g3);
        if res == SmtResult::Sat {
            self.str_witness = subst;
            return Some(m.unwrap_or_else(|| Model::from_bv(BTreeMap::new())));
        }
        None
    }

    fn try_string_witness(&mut self, goal: AstId) -> Option<Model> {
        let string_sort = self.string_sort?;
        let lit_consts: BTreeSet<AstId> = self.str_lits.values().copied().collect();
        let mut vars: Vec<AstId> = Vec::new();
        for t in self.m.postorder(goal) {
            if self.m.is_app(t)
                && self.m.app_args(t).is_empty()
                && self.m.get_sort(t) == string_sort
                && !lit_consts.contains(&t)
                && !vars.contains(&t)
            {
                vars.push(t);
            }
        }
        if vars.is_empty() || vars.len() > 3 {
            return None;
        }
        // Alphabet: characters occurring in string literals, plus two fresh ones.
        let mut alpha: Vec<u32> = Vec::new();
        for text in self.str_lits.keys() {
            for ch in text.chars() {
                let c = ch as u32;
                if !alpha.contains(&c) {
                    alpha.push(c);
                }
            }
        }
        for &c in &[b'a' as u32, b'b' as u32] {
            if !alpha.contains(&c) {
                alpha.push(c);
            }
        }
        alpha.truncate(4);
        // Per-variable candidate strings. A variable pinned to an exact length by
        // `str.len v = k` gets exactly-length-`k` candidates (so length-fixed word
        // equations are witnessed); others use a short default cap. Bounded.
        let default_len = match vars.len() {
            1 => 6,
            2 => 3,
            _ => 2,
        };
        let build = |max_len: usize, exact: bool| -> Vec<Vec<u32>> {
            let mut cur: Vec<Vec<u32>> = alloc::vec![Vec::new()]; // length 0
            let mut out: Vec<Vec<u32>> = if exact { Vec::new() } else { cur.clone() };
            for _ in 1..=max_len {
                let mut next = Vec::new();
                for base in &cur {
                    for &c in &alpha {
                        let mut s = base.clone();
                        s.push(c);
                        next.push(s);
                    }
                }
                cur = next;
                if !exact {
                    out.extend(cur.iter().cloned());
                }
            }
            if exact { cur } else { out }
        };
        let per_var: Vec<Vec<Vec<u32>>> = vars
            .iter()
            .map(|&v| match self.str_exact_len(goal, v) {
                Some(k) if k <= 8 => build(k, true),
                _ => build(default_len, false),
            })
            .collect();
        if per_var.iter().any(|c| c.is_empty()) {
            return None;
        }
        // Cartesian product of candidates over the variables, capped.
        const MAX_TRIES: usize = 3000;
        let mut idx = alloc::vec![0usize; vars.len()];
        let mut tries = 0;
        loop {
            if tries >= MAX_TRIES {
                return None;
            }
            tries += 1;
            let subst: Vec<(AstId, AstId)> = vars
                .iter()
                .enumerate()
                .map(|(k, &v)| {
                    let s = code_points_to_string(&per_var[k][idx[k]]);
                    (v, self.mk_str_lit(&s))
                })
                .collect();
            let g1 = crate::rewriter::substitute(&mut self.m, goal, &subst);
            let mut memo = BTreeMap::new();
            let g2 = self.refold_str_markers(g1, &mut memo);
            // Only trust the result if every symbolic marker folded away.
            let clean = !self
                .m
                .postorder(g2)
                .iter()
                .any(|t| self.str_symbolic.contains(t) || self.str_op_marker(*t));
            if clean {
                // Re-assert the string axioms for the concretised goal: literals
                // are uninterpreted constants, so without the distinctness /
                // length axioms `check_model` could equate two *different* literals
                // (e.g. `"c" = "xyz"`) and report a spurious `sat`.
                let mut conj = self.string_axioms(g2);
                let g3 = if conj.is_empty() {
                    g2
                } else {
                    conj.push(g2);
                    self.m.mk_and(&conj)
                };
                let (res, m) = check_model(&self.m, g3);
                if res == SmtResult::Sat {
                    self.str_witness = subst.clone(); // record for get-value/get-model
                    // `check_model` may report `sat` without a model when the goal
                    // folded to a ground truth; a concrete assignment still exists,
                    // so return an (empty) model rather than a spurious `None`.
                    return Some(m.unwrap_or_else(|| Model::from_bv(BTreeMap::new())));
                }
            }
            // Advance the mixed-radix counter over candidate indices.
            let mut k = 0;
            loop {
                if k == vars.len() {
                    return None; // exhausted
                }
                idx[k] += 1;
                if idx[k] < per_var[k].len() {
                    break;
                }
                idx[k] = 0;
                k += 1;
            }
        }
    }

    /// Is `t` an application of a symbolic string-op marker declaration?
    fn str_op_marker(&self, t: AstId) -> bool {
        self.m.is_app(t) && self.str_op_decls.contains_key(&self.m.app_decl(t))
    }

    /// The `seq.len : (Seq E) → Int` declaration for a sequence sort (interned by
    /// signature, so all length applications on that sort are congruent).
    fn seq_len_decl_for(&mut self, seq_sort: AstId) -> AstId {
        let int = self.m.mk_int_sort();
        let d = self
            .m
            .mk_func_decl(Symbol::new("seq.len"), &[seq_sort], int);
        self.seq_len_decls.insert(d);
        d
    }

    /// The canonical empty sequence of sort `s` (interned, with an empty element
    /// list so structural folding treats it as empty).
    fn seq_empty_of(&mut self, s: AstId) -> AstId {
        if let Some(&e) = self.seq_empty.get(&s) {
            return e;
        }
        let t = self.fresh_const(s);
        self.seq_of.insert(t, Vec::new());
        self.seq_empty.insert(s, t);
        t
    }

    /// The interned `String` sort (registered on first use).
    fn string_sort(&mut self) -> AstId {
        if let Some(s) = self.string_sort {
            return s;
        }
        let s = self.m.mk_uninterpreted_sort(Symbol::new("String"));
        self.string_sort = Some(s);
        self.sorts.insert("String".to_string(), s);
        s
    }

    /// The distinct constant for the string literal `text` (interned).
    fn mk_str_lit(&mut self, text: &str) -> AstId {
        if let Some(&c) = self.str_lits.get(text) {
            return c;
        }
        let sort = self.string_sort();
        let name = alloc::format!("!str!{}", self.str_lits.len());
        let d = self.m.mk_func_decl(Symbol::new(&name), &[], sort);
        let c = self.m.mk_const(d);
        self.str_lits.insert(text.to_string(), c);
        c
    }

    /// The `str.len : String → Int` declaration (created on first use).
    fn str_len_fn(&mut self) -> AstId {
        if let Some(d) = self.str_len_decl {
            return d;
        }
        let s = self.string_sort();
        let int = self.m.mk_int_sort();
        let d = self.m.mk_func_decl(Symbol::new("str.len"), &[s], int);
        self.str_len_decl = Some(d);
        d
    }

    /// The code points of `t` if it is a string literal constant.
    fn str_value(&self, t: AstId) -> Option<Vec<u32>> {
        self.str_lits
            .iter()
            .find(|(_, c)| **c == t)
            .map(|(text, _)| text.chars().map(|ch| ch as u32).collect::<Vec<u32>>())
    }

    /// If `(= a b)` is `(str.++ …) = "literal"` (either way round), expand it to
    /// the disjunction over every way the literal splits among the concatenation
    /// parts — sound and complete for this word-equation fragment. `None` if the
    /// pattern doesn't match.
    /// Bridge an Int↔BV equality involving `bv2int`/`int2bv` and a constant on
    /// the other side, linking the two theories: `(= (bv2int a) c)` becomes
    /// `a = bv(c)` (or `false` if `c` is out of range), and `(= (int2bv x) c)`
    /// becomes `(mod x 2ⁿ) = value(c)`. `None` if the pattern doesn't match.
    fn bv_int_bridge_eq(&mut self, a: AstId, b: AstId) -> Option<AstId> {
        self.bridge_dir(a, b).or_else(|| self.bridge_dir(b, a))
    }

    fn bridge_dir(&mut self, x: AstId, y: AstId) -> Option<AstId> {
        let app = self.m.app(x)?.clone();
        if app.args.len() != 1 {
            return None;
        }
        let nm = self.m.func_decl(app.decl)?.name.as_str()?;
        let arg = app.args[0];
        if matches!(nm, "bv2int" | "bv2nat" | "ubv_to_int" | "sbv_to_int") {
            let c = self.m.as_numeral(y).and_then(|r| r.to_integer())?;
            let w = self.m.bv_sort_width(self.m.get_sort(arg))?;
            let (lo, hi) = if nm == "sbv_to_int" {
                let h = pow2(w - 1);
                (-&h, h)
            } else {
                (Int::from(0), pow2(w))
            };
            if c < lo || c >= hi {
                return Some(self.m.mk_false()); // no bit-vector maps to this integer
            }
            let bv = self.m.mk_bv_numeral(c, w);
            return Some(self.m.mk_eq(arg, bv));
        }
        if nm == "int2bv" {
            let v = self.m.bv_numeral_value(y)?;
            let w = self.m.bv_sort_width(self.m.get_sort(x))?;
            // int2bv(x) = c  ⟺  x ≡ value(c) (mod 2ⁿ).
            let modulus = self.m.mk_numeral(Rational::from_integer(pow2(w)), true);
            let m2 = self.m.mk_mod(arg, modulus);
            let vv = self.m.mk_numeral(Rational::from_integer(v), true);
            return Some(self.m.mk_eq(m2, vv));
        }
        None
    }

    fn try_split_concat_eq(&mut self, a: &SExpr, b: &SExpr) -> Result<Option<AstId>, String> {
        // Flatten a (possibly nested) `str.++` into its sequence of parts.
        fn flatten(s: &SExpr, out: &mut Vec<SExpr>) {
            if let SExpr::List(l) = s
                && l.len() >= 3
                && matches!(&l[0], SExpr::Atom(h) if h == "str.++")
            {
                for p in &l[1..] {
                    flatten(p, out);
                }
            } else {
                out.push(s.clone());
            }
        }
        let concat_parts = |s: &SExpr| -> Option<Vec<SExpr>> {
            match s {
                SExpr::List(l)
                    if l.len() >= 3 && matches!(&l[0], SExpr::Atom(h) if h == "str.++") =>
                {
                    let mut parts = Vec::new();
                    flatten(s, &mut parts);
                    Some(parts)
                }
                _ => None,
            }
        };
        // If either side is a concatenation, flatten both (a bare term is a
        // one-element sequence), cancel a common prefix and suffix (sound
        // left/right cancellation), then decide the residual — so
        // `(str.++ x y) = (str.++ x z)` reduces to `y = z`, `(str.++ x y) = x`
        // reduces to `y = ""`, and concat-vs-literal reuses the split search.
        if concat_parts(a).is_some() || concat_parts(b).is_some() {
            let mut pa = concat_parts(a).unwrap_or_else(|| alloc::vec![a.clone()]);
            let mut pb = concat_parts(b).unwrap_or_else(|| alloc::vec![b.clone()]);
            while !pa.is_empty() && !pb.is_empty() && pa[0] == pb[0] {
                pa.remove(0);
                pb.remove(0);
            }
            while !pa.is_empty() && !pb.is_empty() && pa.last() == pb.last() {
                pa.pop();
                pb.pop();
            }
            return self.concat_residual_eq(&pa, &pb);
        }
        Ok(None)
    }

    /// Decide (or gate) the residual `(str.++ pa…) = (str.++ pb…)` after prefix
    /// and suffix cancellation.
    fn concat_residual_eq(&mut self, pa: &[SExpr], pb: &[SExpr]) -> Result<Option<AstId>, String> {
        let lit = |s: &SExpr| -> Option<Vec<u32>> {
            match s {
                SExpr::Atom(a) if a.starts_with('"') => {
                    Some(unquote_string(a).chars().map(|c| c as u32).collect())
                }
                _ => None,
            }
        };
        // Nothing left on either side: the equation held identically.
        if pa.is_empty() && pb.is_empty() {
            return Ok(Some(self.m.mk_true()));
        }
        // One side empty: every remaining part of the other must be "".
        if pa.is_empty() || pb.is_empty() {
            let rest = if pa.is_empty() { pb } else { pa };
            let empty = self.mk_str_lit("");
            let mut eqs = Vec::new();
            for p in rest {
                let t = self.term(p)?;
                eqs.push(self.m.mk_eq(t, empty));
            }
            return Ok(Some(match eqs.len() {
                1 => eqs[0],
                _ => self.m.mk_and(&eqs),
            }));
        }
        // A single literal against a concatenation: reuse the split search.
        if pa.len() == 1
            && let Some(l) = lit(&pa[0])
        {
            return Ok(Some(self.split_concat_eq(pb, &l)?));
        }
        if pb.len() == 1
            && let Some(l) = lit(&pb[0])
        {
            return Ok(Some(self.split_concat_eq(pa, &l)?));
        }
        // Both reduced to a single term: a direct equality.
        if pa.len() == 1 && pb.len() == 1 {
            let (ta, tb) = (self.term(&pa[0])?, self.term(&pb[0])?);
            return Ok(Some(self.m.mk_eq(ta, tb)));
        }
        // Boundary characters: the first (last) character of each side is
        // determinable up to the first variable from that end. If both sides
        // have a known first (or last) character and they differ, the two
        // concatenations cannot be equal.
        let first_char = |parts: &[SExpr]| -> Option<u32> {
            for p in parts {
                match lit(p) {
                    Some(l) if !l.is_empty() => return Some(l[0]),
                    Some(_) => continue, // empty literal: look further
                    None => return None, // variable: first char unknown
                }
            }
            None
        };
        let last_char = |parts: &[SExpr]| -> Option<u32> {
            for p in parts.iter().rev() {
                match lit(p) {
                    Some(l) if !l.is_empty() => return Some(*l.last().unwrap()),
                    Some(_) => continue,
                    None => return None,
                }
            }
            None
        };
        if let (Some(fa), Some(fb)) = (first_char(pa), first_char(pb))
            && fa != fb
        {
            return Ok(Some(self.m.mk_false()));
        }
        if let (Some(la), Some(lb)) = (last_char(pa), last_char(pb))
            && la != lb
        {
            return Ok(Some(self.m.mk_false()));
        }
        // General concat = concat with variables on both sides: try the Nielsen
        // transformation, which can refute periodicity-style equations
        // (`x·b = a·x`) that the boundary-character test misses. It soundly proves
        // *unsatisfiability*; satisfiable equations fall through to the witness
        // search (gated to `unknown` here).
        let mut vmap: BTreeMap<String, u32> = BTreeMap::new();
        if let (Some(aw), Some(bw)) = (
            Self::parts_to_atoms(pa, &mut vmap),
            Self::parts_to_atoms(pb, &mut vmap),
        ) && Self::nielsen_decide(&aw, &bw) == Some(false)
        {
            return Ok(Some(self.m.mk_false()));
        }
        Ok(None)
    }

    /// Convert `str.++` parts (literals and plain variables) to a word of
    /// [`WAtom`]s — characters for literals, a stable id per variable name from
    /// the *shared* `vmap` (so the same variable on either side maps to one id).
    /// `None` if any part is a compound term (e.g. `str.at`) Nielsen can't model.
    fn parts_to_atoms(parts: &[SExpr], vmap: &mut BTreeMap<String, u32>) -> Option<Vec<WAtom>> {
        let mut out = Vec::new();
        for p in parts {
            match p {
                SExpr::Atom(a) if a.starts_with('"') => {
                    for c in unquote_string(a).chars() {
                        out.push(WAtom::Char(c as u32));
                    }
                }
                SExpr::Atom(a) => {
                    let n = vmap.len() as u32;
                    let id = *vmap.entry(a.clone()).or_insert(n);
                    out.push(WAtom::Var(id));
                }
                _ => return None,
            }
        }
        Some(out)
    }

    /// Cancel the common prefix and suffix of a word equation, then relabel its
    /// variables by first appearance and orient the two sides canonically — so
    /// equations equal up to renaming map to the same state (enabling cycle
    /// detection).
    fn nielsen_normalize(a: &[WAtom], b: &[WAtom]) -> (Vec<WAtom>, Vec<WAtom>) {
        let mut a = a.to_vec();
        let mut b = b.to_vec();
        while !a.is_empty() && !b.is_empty() && a[0] == b[0] {
            a.remove(0);
            b.remove(0);
        }
        while !a.is_empty() && !b.is_empty() && a.last() == b.last() {
            a.pop();
            b.pop();
        }
        let mut ren: BTreeMap<u32, u32> = BTreeMap::new();
        for at in a.iter_mut().chain(b.iter_mut()) {
            if let WAtom::Var(v) = at {
                let n = ren.len() as u32;
                *at = WAtom::Var(*ren.entry(*v).or_insert(n));
            }
        }
        if b < a { (b, a) } else { (a, b) }
    }

    /// Replace every `Var(x)` in `seq` by `rep`.
    fn nielsen_subst(seq: &[WAtom], x: u32, rep: &[WAtom]) -> Vec<WAtom> {
        let mut out = Vec::new();
        for &at in seq {
            match at {
                WAtom::Var(v) if v == x => out.extend_from_slice(rep),
                other => out.push(other),
            }
        }
        out
    }

    /// The Nielsen successor equations of a normalized, both-sides-non-empty state
    /// (empty result ⇒ a dead branch, e.g. a leading-character clash).
    fn nielsen_branches(a: &[WAtom], b: &[WAtom]) -> Vec<(Vec<WAtom>, Vec<WAtom>)> {
        let (a0, b0) = (a[0], b[0]);
        let sub = |x: u32, rep: &[WAtom]| {
            (
                Self::nielsen_subst(a, x, rep),
                Self::nielsen_subst(b, x, rep),
            )
        };
        match (a0, b0) {
            (WAtom::Char(_), WAtom::Char(_)) => Vec::new(), // clash (differ after normalize)
            (WAtom::Var(x), WAtom::Char(c)) | (WAtom::Char(c), WAtom::Var(x)) => {
                alloc::vec![sub(x, &[]), sub(x, &[WAtom::Char(c), WAtom::Var(x)])]
            }
            (WAtom::Var(x), WAtom::Var(y)) => alloc::vec![
                sub(x, &[]),
                sub(y, &[]),
                sub(x, &[WAtom::Var(y), WAtom::Var(x)]),
                sub(y, &[WAtom::Var(x), WAtom::Var(y)]),
            ],
        }
    }

    /// Decide a word equation by Nielsen transformation: enumerate the reachable
    /// normalized states (closed under successors, bounded), mark those trivially
    /// satisfiable, and propagate satisfiability backward to a fixpoint. If the
    /// graph closes within the bound, the start state's mark is exact
    /// (`Some(true)`/`Some(false)`); if the bound is hit, `None`. Sound in both
    /// directions when it converges.
    fn nielsen_decide(a0: &[WAtom], b0: &[WAtom]) -> Option<bool> {
        const CAP: usize = 4000;
        const SIZE: usize = 60;
        let start = Self::nielsen_normalize(a0, b0);
        let mut states: Vec<(Vec<WAtom>, Vec<WAtom>)> = alloc::vec![start.clone()];
        let mut idx: BTreeMap<(Vec<WAtom>, Vec<WAtom>), usize> = BTreeMap::new();
        idx.insert(start, 0);
        let mut succ: Vec<Vec<usize>> = Vec::new();
        let mut base_sat: Vec<bool> = Vec::new();
        let mut i = 0;
        while i < states.len() {
            let (a, b) = states[i].clone();
            // Base classification.
            let (bsat, terminal) = if a.is_empty() && b.is_empty() {
                (true, true)
            } else if a.is_empty() || b.is_empty() {
                let other = if a.is_empty() { &b } else { &a };
                (!other.iter().any(|x| matches!(x, WAtom::Char(_))), true)
            } else {
                (false, false)
            };
            base_sat.push(bsat);
            if terminal {
                succ.push(Vec::new());
                i += 1;
                continue;
            }
            if a.len() + b.len() > SIZE {
                return None; // a growing branch we can't close
            }
            let mut sids = Vec::new();
            for (na, nb) in Self::nielsen_branches(&a, &b) {
                let ns = Self::nielsen_normalize(&na, &nb);
                let id = *idx.entry(ns.clone()).or_insert_with(|| {
                    states.push(ns);
                    states.len() - 1
                });
                sids.push(id);
                if states.len() > CAP {
                    return None;
                }
            }
            succ.push(sids);
            i += 1;
        }
        // Backward fixpoint: sat[i] = base_sat[i] ∨ ∃ successor sat.
        let mut sat = base_sat;
        loop {
            let mut changed = false;
            for i in 0..states.len() {
                if !sat[i] && succ[i].iter().any(|&j| sat[j]) {
                    sat[i] = true;
                    changed = true;
                }
            }
            if !changed {
                break;
            }
        }
        Some(sat[0])
    }

    /// The disjunction over split points of `(str.++ parts…) = lit`.
    fn split_concat_eq(&mut self, parts: &[SExpr], lit: &[u32]) -> Result<AstId, String> {
        if parts.len() == 1 {
            let p = self.term(&parts[0])?;
            let l = self.mk_str_lit(&code_points_to_string(lit));
            return Ok(self.m.mk_eq(p, l));
        }
        // First part takes lit[0..k]; the rest match lit[k..].
        let mut disjuncts = Vec::new();
        for k in 0..=lit.len() {
            let head = self.term(&parts[0])?;
            let prefix = self.mk_str_lit(&code_points_to_string(&lit[..k]));
            let eq_head = self.m.mk_eq(head, prefix);
            let rest = self.split_concat_eq(&parts[1..], &lit[k..])?;
            disjuncts.push(self.m.mk_and(&[eq_head, rest]));
        }
        Ok(match disjuncts.len() {
            0 => self.m.mk_false(),
            1 => disjuncts[0],
            _ => self.m.mk_or(&disjuncts),
        })
    }

    /// Build a string-theory application `(op args…)`, folding when every string
    /// argument is a literal and otherwise producing an uninterpreted term
    /// (marked symbolic so a goal mentioning it is answered `unknown`).
    fn string_op(&mut self, op: &str, raw: &[AstId]) -> Result<AstId, String> {
        // Concrete code points of each argument, if all are string literals.
        let strs: Option<Vec<Vec<u32>>> = raw.iter().map(|&a| self.str_value(a)).collect();
        match op {
            "str.len" => {
                if let Some(v) = self.str_value(raw[0]) {
                    return Ok(self.m.mk_int(v.len() as i64));
                }
                // Symbolic length is a genuine function — sound, not gated.
                let d = self.str_len_fn();
                Ok(self.m.mk_app(d, &[raw[0]]))
            }
            "str.++" => {
                if let Some(parts) = strs {
                    let joined: Vec<u32> = parts.into_iter().flatten().collect();
                    return Ok(self.mk_str_lit(&code_points_to_string(&joined)));
                }
                self.symbolic_string(op, raw)
            }
            "str.at" | "str.substr" | "str.replace" | "str.from_int" | "str.from-int" => {
                if let Some(v) = self.fold_string_producer(op, raw) {
                    return Ok(self.mk_str_lit(&v));
                }
                self.symbolic_string(op, raw)
            }
            "str.contains" | "str.prefixof" | "str.suffixof" | "str.<" | "str.<=" => {
                if let Some(parts) = &strs {
                    let b = fold_string_pred(op, parts);
                    return Ok(if b {
                        self.m.mk_true()
                    } else {
                        self.m.mk_false()
                    });
                }
                // Reflexivity on identical arguments holds regardless of the
                // (possibly symbolic) value: s contains/prefixof/suffixof/≤ s, and
                // s < s is false.
                if raw.len() == 2 && raw[0] == raw[1] {
                    return Ok(if op == "str.<" {
                        self.m.mk_false()
                    } else {
                        self.m.mk_true()
                    });
                }
                // A symbolic string predicate can also be unsound if its string
                // argument is pinned to a literal, so gate via a symbolic marker.
                let atom = self.symbolic_string(op, raw)?;
                Ok(atom)
            }
            "str.replace_all" | "str.replace-all" => {
                if let Some(parts) = &strs {
                    let out = replace_all(&parts[0], &parts[1], &parts[2]);
                    return Ok(self.mk_str_lit(&out));
                }
                self.symbolic_string(op, raw)
            }
            "str.from_code" | "str.from-code" => {
                if let Some(n) = self.int_arg(raw[0]) {
                    let s = char::from_u32(n as u32)
                        .filter(|_| (0..=0x10FFFF).contains(&n))
                        .map(String::from)
                        .unwrap_or_default();
                    return Ok(self.mk_str_lit(&s));
                }
                self.symbolic_string(op, raw)
            }
            "str.is_digit" => {
                if let Some(parts) = &strs {
                    let s = &parts[0];
                    let b = s.len() == 1 && (0x30..=0x39).contains(&s[0]);
                    return Ok(self.mk_bool(b));
                }
                self.symbolic_string(op, raw)
            }
            // str.to_lower / str.to_upper are not part of z3's SMT2 surface (z3
            // treats them as uninterpreted), so folding them would contradict
            // the oracle; keep them a sound `unknown`.
            "str.to_lower" | "str.to_upper" => self.symbolic_string(op, raw),
            "str.indexof" | "str.to_int" | "str.to-int" | "str.to_code" | "str.to-code" => {
                if let Some(v) = self.fold_string_to_int(op, raw) {
                    return Ok(self.m.mk_int(v));
                }
                // Round-trip `str.to_int (str.from_int t) = ite(t ≥ 0, t, −1)`: fold
                // to a pure integer term so the arithmetic solver decides it (no
                // opaque marker, so the `sat` side is decided too).
                if matches!(op, "str.to_int" | "str.to-int")
                    && raw.len() == 1
                    && self.m.is_app(raw[0])
                    && matches!(
                        self.str_op_decls
                            .get(&self.m.app_decl(raw[0]))
                            .map(String::as_str),
                        Some("str.from_int") | Some("str.from-int")
                    )
                {
                    let inner = self.m.app_args(raw[0]);
                    if inner.len() == 1 {
                        let t = inner[0];
                        let zero = self.m.mk_int(0);
                        let neg1 = self.m.mk_int(-1);
                        let nonneg = self.m.mk_ge(t, zero);
                        return Ok(self.m.mk_ite(nonneg, t, neg1));
                    }
                }
                self.symbolic_string(op, raw)
            }
            "str.in_re" | "str.in.re" => {
                // (str.in_re s r): if s is a literal and r a constant regex, match.
                if let (Some(s), Some(r)) = (self.str_value(raw[0]), self.regex_of.get(&raw[1])) {
                    let hit = r.matches(&s);
                    return Ok(if hit {
                        self.m.mk_true()
                    } else {
                        self.m.mk_false()
                    });
                }
                self.symbolic_string(op, raw)
            }
            "str.to_re" | "str.to.re" => self.regex_op(op, raw),
            _ => Err(alloc::format!("unsupported string op {op:?}")),
        }
    }

    /// `(fp sign exp significand)` — a bit-pattern FP literal from three BVs.
    fn mk_fp_literal(&mut self, args: &[AstId]) -> Result<AstId, String> {
        let mut bits: u64 = 0;
        let mut width: u32 = 0;
        // Assemble sign : exponent : significand from most- to least-significant.
        for &a in args {
            let w = self
                .m
                .bv_sort_width(self.m.get_sort(a))
                .ok_or_else(|| "fp: expected bit-vector fields".to_string())?;
            let v = self
                .m
                .bv_numeral_value(a)
                .and_then(|n| n.to_i64())
                .ok_or_else(|| "fp: non-constant field".to_string())? as u64;
            bits = (bits << w) | (v & ((1u128 << w) - 1) as u64);
            width += w;
        }
        // Field widths: sign 1, exponent eb, significand sb-1 ⇒ eb = w1, sb = w2+1.
        let eb = self.m.bv_sort_width(self.m.get_sort(args[1])).unwrap();
        let sb = self.m.bv_sort_width(self.m.get_sort(args[2])).unwrap() + 1;
        debug_assert_eq!(width, eb + sb);
        Ok(self.mk_fp(bits, eb, sb))
    }

    /// A named FP special value (`+oo`/`-oo`/`NaN`/`+zero`/`-zero`) of format
    /// `(eb, sb)`.
    fn fp_special(&mut self, name: &str, eb: u32, sb: u32) -> AstId {
        let mant_bits = sb - 1;
        let exp_ones: u64 = (1u64 << eb) - 1;
        let sign_shift = eb + mant_bits;
        let bits = match name {
            "+oo" => exp_ones << mant_bits,
            "-oo" => (1u64 << sign_shift) | (exp_ones << mant_bits),
            "NaN" => (exp_ones << mant_bits) | (1u64 << (mant_bits - 1)), // canonical qNaN
            "+zero" => 0,
            "-zero" => 1u64 << sign_shift,
            _ => 0,
        };
        self.mk_fp(bits, eb, sb)
    }

    /// The `(_ FloatingPoint eb sb)` sort (interned).
    fn fp_sort(&mut self, eb: u32, sb: u32) -> AstId {
        if let Some(&s) = self.fp_sorts.get(&(eb, sb)) {
            return s;
        }
        let s = self
            .m
            .mk_uninterpreted_sort(Symbol::new(&alloc::format!("FP{eb}_{sb}")));
        self.fp_sorts.insert((eb, sb), s);
        s
    }

    /// The `RoundingMode` sort (interned).
    fn rm_sort(&mut self) -> AstId {
        if let Some(s) = self.rm_sort {
            return s;
        }
        let s = self.m.mk_uninterpreted_sort(Symbol::new("RoundingMode"));
        self.rm_sort = Some(s);
        s
    }

    /// A floating-point constant of the given bits/format, recorded in `fp_of`.
    fn mk_fp(&mut self, bits: u64, eb: u32, sb: u32) -> AstId {
        let sort = self.fp_sort(eb, sb);
        let t = self.fresh_const(sort);
        self.fp_of.insert(t, (bits, eb, sb));
        t
    }

    /// The `f64` value of `t` if it is a `Float64` constant.
    fn fp64(&self, t: AstId) -> Option<f64> {
        match self.fp_of.get(&t) {
            Some(&(bits, 11, 53)) => Some(f64::from_bits(bits)),
            _ => None,
        }
    }

    /// The `(eb, sb)` format of an FP sort, if known.
    fn fp_format_of(&self, sort: AstId) -> Option<(u32, u32)> {
        self.fp_sorts
            .iter()
            .find(|(_, s)| **s == sort)
            .map(|(&fmt, _)| fmt)
    }

    /// The bit-vector representation of an FP term: a constant → its numeral, an
    /// FP variable → a fresh `(eb+sb)`-bit constant (cached), so symbolic FP
    /// equality/classification bit-blast through QF_BV. `None` if the format is
    /// unknown.
    fn fp_to_bv(&mut self, t: AstId) -> Option<AstId> {
        if let Some(&(bits, eb, sb)) = self.fp_of.get(&t) {
            return Some(self.m.mk_bv_numeral(Int::from(bits as i64), eb + sb));
        }
        if let Some(&bv) = self.fp_bv.get(&t) {
            return Some(bv);
        }
        // An opaque symbolic FP operation (e.g. fp.fma/fp.sqrt we cannot fold)
        // has a *determined* value we don't know; representing it as a free
        // bit-vector would be unsound (it would satisfy any equality). Refuse it
        // so the surrounding goal keeps the `unknown` gate instead.
        if self.str_symbolic.contains(&t) {
            return None;
        }
        let (eb, sb) = self.fp_format_of(self.m.get_sort(t))?;
        let bv = self
            .m
            .mk_bv_const(&alloc::format!("!fpbv!{}", self.fresh_counter), eb + sb);
        self.fresh_counter += 1;
        self.fp_bv.insert(t, bv);
        Some(bv)
    }

    /// Symbolic IEEE `fp.eq` as a Boolean over the BV representations: neither
    /// operand is NaN, and either the bits are equal or both are zero (−0 = +0).
    /// Decided by the QF_BV engine. `None` for ops other than `fp.eq`.
    fn fp_compare_bv(&mut self, op: &str, a: AstId, b: AstId) -> Option<AstId> {
        // NaN makes every ordered/equality comparison false.
        let nan_a = self.fp_classify_bv("fp.isNaN", a)?;
        let nan_b = self.fp_classify_bv("fp.isNaN", b)?;
        let not_nan_a = self.m.mk_not(nan_a);
        let not_nan_b = self.m.mk_not(nan_b);
        let no_nan = self.m.mk_and(&[not_nan_a, not_nan_b]);
        let zero_a = self.fp_classify_bv("fp.isZero", a)?;
        let zero_b = self.fp_classify_bv("fp.isZero", b)?;
        let both_zero = self.m.mk_and(&[zero_a, zero_b]);
        let bva = self.fp_to_bv(a)?;
        let bvb = self.fp_to_bv(b)?;
        let bv_eq = self.m.mk_eq(bva, bvb);
        if op == "fp.eq" {
            // `+0 = -0`, so equal bits OR both zero, and neither NaN.
            let val_eq = self.m.mk_or(&[bv_eq, both_zero]);
            return Some(self.m.mk_and(&[val_eq, no_nan]));
        }
        // Ordered comparisons via a DIRECT field comparison — sign bit plus the
        // magnitude (`exp:significand` = the low `w-1` bits, a plain extract).
        // Unlike the monotone-key transform, the magnitude is a near-free
        // variable, so the SAT core refutes e.g. `x<y ∧ y<x` quickly.
        let w = self
            .fp_format_of(self.m.get_sort(a))
            .map(|(eb, sb)| eb + sb)?;
        let lt_ab = self.fp_real_lt(bva, bvb, w); // value(a) < value(b), non-NaN
        Some(match op {
            "fp.lt" => {
                let not_both_zero = self.m.mk_not(both_zero);
                self.m.mk_and(&[no_nan, not_both_zero, lt_ab])
            }
            "fp.gt" => {
                let lt_ba = self.fp_real_lt(bvb, bva, w);
                let not_both_zero = self.m.mk_not(both_zero);
                self.m.mk_and(&[no_nan, not_both_zero, lt_ba])
            }
            "fp.leq" => {
                let eq = self.m.mk_or(&[bv_eq, both_zero]);
                let le = self.m.mk_or(&[lt_ab, eq]);
                self.m.mk_and(&[no_nan, le])
            }
            _ => {
                // fp.geq
                let lt_ba = self.fp_real_lt(bvb, bva, w);
                let eq = self.m.mk_or(&[bv_eq, both_zero]);
                let ge = self.m.mk_or(&[lt_ba, eq]);
                self.m.mk_and(&[no_nan, ge])
            }
        })
    }

    /// Symbolic `fp.min`/`fp.max` as a bit-vector `ite` circuit: the smaller
    /// (resp. larger) value, with NaN yielding the other operand and a ±0 clash
    /// resolving to `-0` for min / `+0` for max (z3's convention). Returns a fresh
    /// FP term whose bit-vector is the result.
    fn fp_min_max_bv(&mut self, op: &str, a: AstId, b: AstId) -> Option<AstId> {
        let (eb, sb) = self.fp_format_of(self.m.get_sort(a))?;
        let w = eb + sb;
        let bva = self.fp_to_bv(a)?;
        let bvb = self.fp_to_bv(b)?;
        let nan_a = self.fp_classify_bv("fp.isNaN", a)?;
        let nan_b = self.fp_classify_bv("fp.isNaN", b)?;
        let zero_a = self.fp_classify_bv("fp.isZero", a)?;
        let zero_b = self.fp_classify_bv("fp.isZero", b)?;
        let both_zero = self.m.mk_and(&[zero_a, zero_b]);
        let one1 = self.m.mk_bv(1, 1);
        let sa = self.m.mk_bv_extract(w - 1, w - 1, bva);
        let sbb = self.m.mk_bv_extract(w - 1, w - 1, bvb);
        let sa1 = self.m.mk_eq(sa, one1);
        let sb1 = self.m.mk_eq(sbb, one1);
        let zeros = self.m.mk_bv(0, w - 1);
        let neg_zero = self.m.mk_bv_concat(one1, zeros);
        let pos_zero = self.m.mk_bv(0, w);
        let lt_ab = self.fp_real_lt(bva, bvb, w);
        let lt_ba = self.fp_real_lt(bvb, bva, w);
        let is_min = op == "fp.min";
        // ±0 clash → the signed zero z3 prefers.
        let zero_res = if is_min {
            let either_neg = self.m.mk_or(&[sa1, sb1]);
            self.m.mk_ite(either_neg, neg_zero, pos_zero)
        } else {
            let nsa1 = self.m.mk_not(sa1);
            let nsb1 = self.m.mk_not(sb1);
            let either_pos = self.m.mk_or(&[nsa1, nsb1]);
            self.m.mk_ite(either_pos, pos_zero, neg_zero)
        };
        let eq_case = self.m.mk_ite(both_zero, zero_res, bva);
        // min: a<b→a, b<a→b; max: a>b→a, b>a→b.
        let (first, second) = if is_min {
            (lt_ab, lt_ba)
        } else {
            (lt_ba, lt_ab)
        };
        let inner = self.m.mk_ite(second, bvb, eq_case);
        let core = self.m.mk_ite(first, bva, inner);
        // NaN operand ⇒ the other operand.
        let r1 = self.m.mk_ite(nan_b, bva, core);
        let result_bv = self.m.mk_ite(nan_a, bvb, r1);
        let fps = self.fp_sort(eb, sb);
        let result = self.fresh_const(fps);
        self.fp_bv.insert(result, result_bv);
        Some(result)
    }

    /// `value(a) < value(b)` for the width-`w` bit-vectors of two **non-NaN**
    /// floats (±0 tie handled by the caller): compare by sign, then by magnitude
    /// (`exp:significand`) — ascending for positives, descending for negatives.
    fn fp_real_lt(&mut self, bva: AstId, bvb: AstId, w: u32) -> AstId {
        let one1 = self.m.mk_bv(1, 1);
        let sa = self.m.mk_bv_extract(w - 1, w - 1, bva);
        let sb = self.m.mk_bv_extract(w - 1, w - 1, bvb);
        let sa1 = self.m.mk_eq(sa, one1); // a is negative
        let sb1 = self.m.mk_eq(sb, one1); // b is negative
        let nsa1 = self.m.mk_not(sa1);
        let nsb1 = self.m.mk_not(sb1);
        let both_neg = self.m.mk_and(&[sa1, sb1]);
        let both_pos = self.m.mk_and(&[nsa1, nsb1]);
        let mag_a = self.m.mk_bv_extract(w - 2, 0, bva);
        let mag_b = self.m.mk_bv_extract(w - 2, 0, bvb);
        let pos_lt = self.m.mk_bvult(mag_a, mag_b); // both ≥ 0: a<b iff |a|<|b|
        let neg_lt = self.m.mk_bvult(mag_b, mag_a); // both < 0: a<b iff |a|>|b|
        // signs differ ⇒ a<b iff a is the negative one (= sa1)
        let inner = self.m.mk_ite(both_pos, pos_lt, sa1);
        self.m.mk_ite(both_neg, neg_lt, inner)
    }

    /// A classification predicate (`fp.isNaN` …) as a Boolean over the bits of
    /// the FP term `t` (format `(eb, sb)`), decided by the QF_BV engine.
    fn fp_classify_bv(&mut self, op: &str, t: AstId) -> Option<AstId> {
        let (eb, sb) = self.fp_format_of(self.m.get_sort(t))?;
        if sb < 2 {
            return None;
        }
        let bv = self.fp_to_bv(t)?;
        let w = eb + sb;
        let exp = self.m.mk_bv_extract(w - 2, sb - 1, bv); // eb bits
        let mant = self.m.mk_bv_extract(sb - 2, 0, bv); // sb-1 bits
        let sign = self.m.mk_bv_extract(w - 1, w - 1, bv); // 1 bit
        let exp_zero = self.m.mk_bv(0, eb);
        let exp_ones = self.m.mk_bvnot(exp_zero);
        let mant_zero = self.m.mk_bv(0, sb - 1);
        let one1 = self.m.mk_bv(1, 1);
        let is_exp_ones = self.m.mk_eq(exp, exp_ones);
        let is_exp_zero = self.m.mk_eq(exp, exp_zero);
        let is_mant_zero = self.m.mk_eq(mant, mant_zero);
        let mant_nz = self.m.mk_not(is_mant_zero);
        let is_nan = self.m.mk_and(&[is_exp_ones, mant_nz]);
        Some(match op {
            "fp.isNaN" => is_nan,
            "fp.isInfinite" => self.m.mk_and(&[is_exp_ones, is_mant_zero]),
            "fp.isZero" => self.m.mk_and(&[is_exp_zero, is_mant_zero]),
            "fp.isSubnormal" => self.m.mk_and(&[is_exp_zero, mant_nz]),
            "fp.isNormal" => {
                let not_zero = self.m.mk_not(is_exp_zero);
                let not_ones = self.m.mk_not(is_exp_ones);
                self.m.mk_and(&[not_zero, not_ones])
            }
            "fp.isNegative" => {
                let neg = self.m.mk_eq(sign, one1);
                let not_nan = self.m.mk_not(is_nan);
                self.m.mk_and(&[neg, not_nan])
            }
            "fp.isPositive" => {
                let zero1 = self.m.mk_bv(0, 1);
                let pos = self.m.mk_eq(sign, zero1);
                let not_nan = self.m.mk_not(is_nan);
                self.m.mk_and(&[pos, not_nan])
            }
            _ => return None,
        })
    }

    // ===================================================================
    // Bit-exact symbolic IEEE-754 `fp.add` / `fp.sub`, bit-blasted to QF_BV.
    // This is a direct port of z3's `fpa2bv_converter` (`mk_add`, `add_core`,
    // `round`, `unpack`, `mk_leading_zeros`, `mk_rounding_decision`) so that the
    // packed result bit-vector is identical to z3's on every input, including
    // NaN, ±inf, ±0, subnormals and overflow-to-inf.
    // ===================================================================

    /// Width (in bits) of a bit-vector term.
    fn bvw(&self, x: AstId) -> u32 {
        self.m.bv_sort_width(self.m.get_sort(x)).unwrap()
    }

    /// The 3-bit `RoundingMode` code (RNE=0 … RTZ=4) of a constant rm term.
    fn rm_code(&self, t: AstId) -> Option<u32> {
        let d = self.m.app_decl(t);
        let name = self.m.func_decl(d)?.name.as_str()?;
        Some(match name {
            "RNE" | "roundNearestTiesToEven" => 0,
            "RNA" | "roundNearestTiesToAway" => 1,
            "RTP" | "roundTowardPositive" => 2,
            "RTN" | "roundTowardNegative" => 3,
            "RTZ" | "roundTowardZero" => 4,
            _ => return None,
        })
    }

    /// A `w`-bit numeral from a raw `u64` bit pattern (reduced mod 2^w).
    fn fp_lit(&mut self, bits: u64, w: u32) -> AstId {
        self.m.mk_bv_numeral(Int::from(bits as i64), w)
    }

    /// A `w`-bit signed numeral from an `i64` value (reduced mod 2^w).
    fn fp_ilit(&mut self, v: i64, w: u32) -> AstId {
        self.m.mk_bv_numeral(Int::from(v), w)
    }

    /// `redor(x)` — 1-bit OR-reduce (`1` iff `x != 0`).
    fn fp_redor(&mut self, x: AstId) -> AstId {
        let w = self.bvw(x);
        let z = self.m.mk_bv(0, w);
        let is_zero = self.m.mk_eq(x, z);
        let one1 = self.m.mk_bv(1, 1);
        let zero1 = self.m.mk_bv(0, 1);
        self.m.mk_ite(is_zero, zero1, one1)
    }

    /// `mk_is_rm(rm, k)` — Boolean `rm == k`.
    fn fp_rm_is(&mut self, rm3: AstId, k: u32) -> AstId {
        let kk = self.m.mk_bv(k as i64, 3);
        self.m.mk_eq(rm3, kk)
    }

    /// `leading_zeros(x, out_w)` — combinational count (z3 `mk_leading_zeros`).
    fn fp_leading_zeros(&mut self, e: AstId, out_w: u32) -> AstId {
        let n = self.bvw(e);
        if n == 1 {
            let nil1 = self.m.mk_bv(0, 1);
            let eq = self.m.mk_eq(e, nil1);
            let one_m = self.m.mk_bv(1, out_w);
            let nil_m = self.m.mk_bv(0, out_w);
            return self.m.mk_ite(eq, one_m, nil_m);
        }
        let h = self.m.mk_bv_extract(n - 1, n / 2, e);
        let l = self.m.mk_bv_extract(n / 2 - 1, 0, e);
        let h_size = n - n / 2;
        let lz_h = self.fp_leading_zeros(h, out_w);
        let lz_l = self.fp_leading_zeros(l, out_w);
        let nil_h = self.m.mk_bv(0, h_size);
        let h_is_zero = self.m.mk_eq(h, nil_h);
        let h_m = self.m.mk_bv(h_size as i64, out_w);
        let sum = self.m.mk_bvadd(h_m, lz_l);
        self.m.mk_ite(h_is_zero, sum, lz_h)
    }

    /// `unbias(e)` — signed unbiased exponent (`e + 1 − 2^(eb−1)`), eb bits.
    fn fp_unbias(&mut self, e: AstId, eb: u32) -> AstId {
        let one = self.m.mk_bv(1, eb);
        let ep1 = self.m.mk_bvadd(e, one);
        let leading = self.m.mk_bv_extract(eb - 1, eb - 1, ep1);
        let n_leading = self.m.mk_bvnot(leading);
        let rest = self.m.mk_bv_extract(eb - 2, 0, ep1);
        self.m.mk_bv_concat(n_leading, rest)
    }

    /// `bias_exp(e)` — biased exponent (`e + 2^(eb−1) − 1`), eb bits.
    fn fp_bias(&mut self, e: AstId, eb: u32) -> AstId {
        let bias = ((1u64 << (eb - 1)) - 1) as i64;
        let b = self.m.mk_bv(bias, eb);
        self.m.mk_bvadd(e, b)
    }

    /// `mk_rounding_decision(rm, sgn, last, round, sticky)` → 1-bit increment.
    fn fp_rounding_decision(
        &mut self,
        rm3: AstId,
        sgn: AstId,
        last: AstId,
        round: AstId,
        sticky: AstId,
    ) -> AstId {
        let l_or_s = self.m.mk_bvor(last, sticky);
        let r_or_s = self.m.mk_bvor(round, sticky);
        let inc_rne = self.m.mk_bvand(round, l_or_s);
        let inc_rna = round;
        let not_sgn = self.m.mk_bvnot(sgn);
        let inc_rtp = self.m.mk_bvand(not_sgn, r_or_s);
        let inc_rtn = self.m.mk_bvand(sgn, r_or_s);
        let nil1 = self.m.mk_bv(0, 1);
        let is_rtn = self.fp_rm_is(rm3, 3);
        let c4 = self.m.mk_ite(is_rtn, inc_rtn, nil1);
        let is_rtp = self.fp_rm_is(rm3, 2);
        let c3 = self.m.mk_ite(is_rtp, inc_rtp, c4);
        let is_rna = self.fp_rm_is(rm3, 1);
        let c2 = self.m.mk_ite(is_rna, inc_rna, c3);
        let is_rne = self.fp_rm_is(rm3, 0);
        self.m.mk_ite(is_rne, inc_rne, c2)
    }

    /// The shared rounder (z3 `round`). `sig` is `sb+4` bits (`[o1 o0 . f][g r s]`),
    /// `exp` is `eb+2` signed bits. Returns the packed `(eb+sb)`-bit result.
    #[allow(clippy::too_many_arguments)]
    fn fp_round(
        &mut self,
        rm3: AstId,
        sgn: AstId,
        sig: AstId,
        exp: AstId,
        eb: u32,
        sb: u32,
    ) -> AstId {
        let one1 = self.m.mk_bv(1, 1);
        let emin_v = 2i64 - (1i64 << (eb - 1)); // -(2^(eb-1)-2)
        let emax_v = ((1u64 << (eb - 1)) - 1) as i64;
        let e_min = self.fp_ilit(emin_v, eb);
        let e_max = self.fp_ilit(emax_v, eb);

        // OVF1 pre-check.
        let h_exp = self.m.mk_bv_extract(eb + 1, eb + 1, exp);
        let e3 = self.m.mk_eq(h_exp, one1);
        let sh_exp = self.m.mk_bv_extract(eb, eb, exp);
        let e2 = self.m.mk_eq(sh_exp, one1);
        let th_exp = self.m.mk_bv_extract(eb - 1, eb - 1, exp);
        let e1 = self.m.mk_eq(th_exp, one1);
        let e21 = self.m.mk_or(&[e2, e1]);
        let ne3 = self.m.mk_not(e3);
        let e_top_three = self.m.mk_and(&[ne3, e21]);
        let ext_emax = self.m.mk_bv_zero_extend(2, e_max);
        let t_sig0 = self.m.mk_bv_extract(sb + 3, sb + 3, sig);
        let e_eq_emax = self.m.mk_eq(ext_emax, exp);
        let sigm1 = self.m.mk_eq(t_sig0, one1);
        let e_eq_emax_and_sigm1 = self.m.mk_and(&[e_eq_emax, sigm1]);
        let ovf1 = self.m.mk_or(&[e_top_three, e_eq_emax_and_sigm1]);

        // Normalization shift.
        let lz = self.fp_leading_zeros(sig, eb + 2);
        let one_e2 = self.m.mk_bv(1, eb + 2);
        let t1 = self.m.mk_bvadd(exp, one_e2);
        let t2 = self.m.mk_bvsub(t1, lz);
        let se_emin = self.m.mk_bv_sign_extend(2, e_min);
        let t3 = self.m.mk_bvsub(t2, se_emin);
        let neg1_e2 = self.fp_ilit(-1, eb + 2);
        let tiny = self.m.mk_bvsle(t3, neg1_e2);

        let exp_m_lz = self.m.mk_bvsub(exp, lz);
        let one_e2b = self.m.mk_bv(1, eb + 2);
        let beta = self.m.mk_bvadd(exp_m_lz, one_e2b);

        let se_emin2 = self.m.mk_bv_sign_extend(2, e_min);
        let sa1 = self.m.mk_bvsub(exp, se_emin2);
        let one_e2c = self.m.mk_bv(1, eb + 2);
        let sigma_add = self.m.mk_bvadd(sa1, one_e2c);
        let sigma = self.m.mk_ite(tiny, sigma_add, lz);

        let sig_size = sb + 4;
        let sigma_size = eb + 2;
        let sigma_neg = self.m.mk_bvneg(sigma);
        let sigma_cap = self.m.mk_bv((sb + 2) as i64, sigma_size);
        let sigma_le_cap = self.m.mk_bvule(sigma_neg, sigma_cap);
        let sigma_neg_capped = self.m.mk_ite(sigma_le_cap, sigma_neg, sigma_cap);
        let neg1_ss = self.fp_ilit(-1, sigma_size);
        let sigma_lt_zero = self.m.mk_bvsle(sigma, neg1_ss);
        let zeros_ss = self.m.mk_bv(0, sig_size);
        let sig_ext = self.m.mk_bv_concat(sig, zeros_ss); // 2*sig_size
        let ext_r = self
            .m
            .mk_bv_zero_extend(2 * sig_size - sigma_size, sigma_neg_capped);
        let rs_sig = self.m.mk_bvlshr(sig_ext, ext_r);
        let ext_l = self.m.mk_bv_zero_extend(2 * sig_size - sigma_size, sigma);
        let ls_sig = self.m.mk_bvshl(sig_ext, ext_l);
        let big_sh = self.m.mk_ite(sigma_lt_zero, rs_sig, ls_sig);
        let low_bit = 2 * sig_size - (sb + 2);
        let sig_a = self.m.mk_bv_extract(2 * sig_size - 1, low_bit, big_sh); // sb+2
        let sticky_bits = self.m.mk_bv_extract(low_bit - 1, 0, big_sh);
        let sticky1 = self.fp_redor(sticky_bits);
        let ext_sticky = self.m.mk_bv_zero_extend(sb + 1, sticky1);
        let sig_b = self.m.mk_bvor(sig_a, ext_sticky); // sb+2
        let ext_emin = self.m.mk_bv_zero_extend(2, e_min);
        let exp_b = self.m.mk_ite(tiny, ext_emin, beta); // eb+2

        // Guard/round/sticky and increment.
        let sticky = self.m.mk_bv_extract(0, 0, sig_b);
        let round = self.m.mk_bv_extract(1, 1, sig_b);
        let last = self.m.mk_bv_extract(2, 2, sig_b);
        let sig_c = self.m.mk_bv_extract(sb + 1, 2, sig_b); // sb bits
        let inc = self.fp_rounding_decision(rm3, sgn, last, round, sticky);
        let sig_c_ext = self.m.mk_bv_zero_extend(1, sig_c);
        let inc_ext = self.m.mk_bv_zero_extend(sb, inc);
        let sig_d = self.m.mk_bvadd(sig_c_ext, inc_ext); // sb+1

        // Post-normalization.
        let sigovf_bit = self.m.mk_bv_extract(sb, sb, sig_d);
        let sigovf = self.m.mk_eq(sigovf_bit, one1);
        let hallbut1 = self.m.mk_bv_extract(sb, 1, sig_d);
        let lallbut1 = self.m.mk_bv_extract(sb - 1, 0, sig_d);
        let sig_e = self.m.mk_ite(sigovf, hallbut1, lallbut1); // sb bits
        let one_e2d = self.m.mk_bv(1, eb + 2);
        let exp_p1 = self.m.mk_bvadd(exp_b, one_e2d);
        let exp_c = self.m.mk_ite(sigovf, exp_p1, exp_b);

        // Exponent biasing + overflow/underflow finalization.
        let exp_low = self.m.mk_bv_extract(eb - 1, 0, exp_c);
        let biased = self.fp_bias(exp_low, eb);
        let all_ones_eb = {
            let z = self.m.mk_bv(0, eb);
            self.m.mk_bvnot(z)
        };
        let preovf2 = self.m.mk_eq(biased, all_ones_eb);
        let ovf2 = self.m.mk_and(&[sigovf, preovf2]);
        let pem2m1 = self.fp_ilit(((1u64 << (eb - 2)) - 1) as i64, eb);
        let biased2 = self.m.mk_ite(ovf2, pem2m1, biased);
        let ovf = self.m.mk_or(&[ovf1, ovf2]);

        let top_exp = all_ones_eb;
        let bot_exp = self.m.mk_bv(0, eb);
        let is_rtz = self.fp_rm_is(rm3, 4);
        let is_rtn = self.fp_rm_is(rm3, 3);
        let is_rtp = self.fp_rm_is(rm3, 2);
        let rm_zero_or_neg = self.m.mk_or(&[is_rtz, is_rtn]);
        let rm_zero_or_pos = self.m.mk_or(&[is_rtz, is_rtp]);
        let zero1 = self.m.mk_bv(0, 1);
        let sgn_is_zero = self.m.mk_eq(sgn, zero1);
        let max_sig = self.fp_ilit(((1u64 << (sb - 1)) - 1) as i64, sb - 1);
        let max_exp = {
            let hi = self.fp_ilit(((1u64 << (eb - 1)) - 1) as i64, eb - 1);
            let lo = self.m.mk_bv(0, 1);
            self.m.mk_bv_concat(hi, lo)
        };
        let inf_sig = self.m.mk_bv(0, sb - 1);
        let inf_exp = top_exp;
        let max_inf_exp_neg = self.m.mk_ite(rm_zero_or_pos, max_exp, inf_exp);
        let max_inf_exp_pos = self.m.mk_ite(rm_zero_or_neg, max_exp, inf_exp);
        let ovfl_exp = self.m.mk_ite(sgn_is_zero, max_inf_exp_pos, max_inf_exp_neg);
        let nd_bit = self.m.mk_bv_extract(sb - 1, sb - 1, sig_e);
        let n_d_check = self.m.mk_eq(nd_bit, zero1);
        let n_d_exp = self.m.mk_ite(n_d_check, bot_exp, biased2);
        let final_exp = self.m.mk_ite(ovf, ovfl_exp, n_d_exp); // eb bits

        let max_inf_sig_neg = self.m.mk_ite(rm_zero_or_pos, max_sig, inf_sig);
        let max_inf_sig_pos = self.m.mk_ite(rm_zero_or_neg, max_sig, inf_sig);
        let ovfl_sig = self.m.mk_ite(sgn_is_zero, max_inf_sig_pos, max_inf_sig_neg);
        let rest_sig = self.m.mk_bv_extract(sb - 2, 0, sig_e); // sb-1 bits
        let final_sig = self.m.mk_ite(ovf, ovfl_sig, rest_sig);

        // pack(sgn, exp, sig).
        let hi = self.m.mk_bv_concat(sgn, final_exp);
        self.m.mk_bv_concat(hi, final_sig)
    }

    /// `unpack(X, normalize=false)` → (sgn, sig[sb], exp[eb]) for add/sub.
    fn fp_unpack_add(&mut self, bv: AstId, eb: u32, sb: u32) -> (AstId, AstId, AstId) {
        let w = eb + sb;
        let sgn = self.m.mk_bv_extract(w - 1, w - 1, bv);
        let exp_f = self.m.mk_bv_extract(w - 2, sb - 1, bv); // eb bits
        let sig_f = self.m.mk_bv_extract(sb - 2, 0, bv); // sb-1 bits
        let exp_zero = self.m.mk_bv(0, eb);
        let exp_ones = self.m.mk_bvnot(exp_zero);
        let is_zero_exp = self.m.mk_eq(exp_f, exp_zero);
        let is_ones_exp = self.m.mk_eq(exp_f, exp_ones);
        let not_zero = self.m.mk_not(is_zero_exp);
        let not_ones = self.m.mk_not(is_ones_exp);
        let is_norm = self.m.mk_and(&[not_zero, not_ones]);
        let one1 = self.m.mk_bv(1, 1);
        let normal_sig = self.m.mk_bv_concat(one1, sig_f); // sb bits
        let normal_exp = self.fp_unbias(exp_f, eb);
        let denormal_sig = self.m.mk_bv_zero_extend(1, sig_f); // sb bits
        let one_eb = self.m.mk_bv(1, eb);
        let denormal_exp = self.fp_unbias(one_eb, eb); // = emin
        let sig = self.m.mk_ite(is_norm, normal_sig, denormal_sig);
        let exp = self.m.mk_ite(is_norm, normal_exp, denormal_exp);
        (sgn, sig, exp)
    }

    /// Round a real (rational) constant to the `(eb, sb)` floating-point format
    /// under rounding mode `rm` (0=RNE,1=RNA,2=RTP,3=RTN,4=RTZ), returning the
    /// packed bit pattern. Handles zero, normals, subnormals, and overflow→inf/
    /// max-finite. `None` for out-of-range magnitudes (huge exponent).
    fn real_to_fp_bits(r: &Rational, eb: u32, sb: u32, rm: u32) -> Option<u64> {
        let w = eb + sb;
        let neg = r.is_negative();
        let sign_bit = if neg { 1u64 << (w - 1) } else { 0 };
        if r.is_zero() {
            return Some(sign_bit);
        }
        let a = r.abs();
        let bias = (1i64 << (eb - 1)) - 1;
        let emin = 1 - bias;
        let two = Rational::from_integer(puremp::Int::from(2));
        let one = Rational::from_integer(puremp::Int::from(1));
        // E = floor(log2 |a|).
        let mut e = 0i64;
        let mut x = a.clone();
        let mut guard = 0u32;
        while x >= two {
            x = x.div(&two);
            e += 1;
            guard += 1;
            if guard > 100_000 {
                return None;
            }
        }
        while x < one {
            x = x.mul(&two);
            e -= 1;
            guard += 1;
            if guard > 100_000 {
                return None;
            }
        }
        let eff_e = e.max(emin);
        let shift = (sb as i64 - 1) - eff_e;
        if shift.unsigned_abs() > 100_000 {
            return None;
        }
        let m_exact = a.mul(&Rational::power_of_two(shift as i32));
        let m_floor = m_exact.floor();
        let m_floor_r = Rational::from_integer(m_floor.clone());
        let frac = m_exact.sub(&m_floor_r); // [0, 1)
        let half = Rational::power_of_two(-1);
        let frac_zero = frac.is_zero();
        let m_floor_u = m_floor.to_i64()? as u64;
        let round_up = match rm {
            0 => frac > half || (frac == half && (m_floor_u & 1 == 1)), // RNE
            1 => frac >= half,                                          // RNA
            2 => !neg && !frac_zero,                                    // RTP
            3 => neg && !frac_zero,                                     // RTN
            4 => false,                                                 // RTZ
            _ => return None,
        };
        let m_u = if round_up { m_floor_u + 1 } else { m_floor_u };
        let exp_field_max = (1u64 << eb) - 1; // all-ones ⇒ inf/nan
        if e >= emin {
            let mut biased_e = e + bias;
            let mut mant = m_u;
            if mant == (1u64 << sb) {
                mant = 1u64 << (sb - 1); // rounding carried into the exponent
                biased_e += 1;
            }
            if biased_e as u64 >= exp_field_max {
                // Overflow → inf (nearest/RNA, or the "toward" direction) else max.
                let to_inf = matches!(rm, 0 | 1) || (rm == 2 && !neg) || (rm == 3 && neg);
                return Some(if to_inf {
                    sign_bit | (exp_field_max << (sb - 1))
                } else {
                    sign_bit | ((exp_field_max - 1) << (sb - 1)) | ((1u64 << (sb - 1)) - 1)
                });
            }
            let frac_bits = mant - (1u64 << (sb - 1));
            Some(sign_bit | ((biased_e as u64) << (sb - 1)) | frac_bits)
        } else if m_u == (1u64 << (sb - 1)) {
            Some(sign_bit | (1u64 << (sb - 1))) // rounded up to the smallest normal
        } else {
            Some(sign_bit | m_u) // subnormal (biased exp 0)
        }
    }

    /// `unpack(normalize=true)` (z3): like [`fp_unpack_add`] but the significand
    /// is left-normalised (leading zeros of a subnormal shifted out) and the
    /// leading-zero count `lz` is returned so the caller adjusts the exponent.
    /// Returns `(sgn[1], sig[sb], exp[eb] unbiased, lz[eb])`. Assumes `eb ≤ sb`.
    fn fp_unpack_norm(&mut self, bv: AstId, eb: u32, sb: u32) -> (AstId, AstId, AstId, AstId) {
        let w = eb + sb;
        let sgn = self.m.mk_bv_extract(w - 1, w - 1, bv);
        let exp_f = self.m.mk_bv_extract(w - 2, sb - 1, bv); // eb bits
        let sig_f = self.m.mk_bv_extract(sb - 2, 0, bv); // sb-1 bits
        let exp_zero = self.m.mk_bv(0, eb);
        let exp_ones = self.m.mk_bvnot(exp_zero);
        let is_zero_exp = self.m.mk_eq(exp_f, exp_zero);
        let is_ones_exp = self.m.mk_eq(exp_f, exp_ones);
        let not_zero = self.m.mk_not(is_zero_exp);
        let not_ones = self.m.mk_not(is_ones_exp);
        let is_norm = self.m.mk_and(&[not_zero, not_ones]);
        let one1 = self.m.mk_bv(1, 1);
        let normal_sig = self.m.mk_bv_concat(one1, sig_f); // sb
        let normal_exp = self.fp_unbias(exp_f, eb);
        let mut denormal_sig = self.m.mk_bv_zero_extend(1, sig_f); // sb
        let one_eb = self.m.mk_bv(1, eb);
        let denormal_exp = self.fp_unbias(one_eb, eb); // emin
        let zero_e = self.m.mk_bv(0, eb);
        // Normalisation: shift a subnormal significand left by its leading zeros.
        let zero_s = self.m.mk_bv(0, sb);
        let is_sig_zero = self.m.mk_eq(zero_s, denormal_sig);
        let lz_d = self.fp_leading_zeros(denormal_sig, eb); // eb bits
        let norm_or_zero = self.m.mk_or(&[is_norm, is_sig_zero]);
        let lz = self.m.mk_ite(norm_or_zero, zero_e, lz_d);
        let shift = self.m.mk_ite(is_sig_zero, zero_e, lz);
        let q = self.m.mk_bv_zero_extend(sb - eb, shift); // sb bits (eb ≤ sb)
        denormal_sig = self.m.mk_bvshl(denormal_sig, q);
        let sig = self.m.mk_ite(is_norm, normal_sig, denormal_sig);
        let exp = self.m.mk_ite(is_norm, normal_exp, denormal_exp);
        (sgn, sig, exp, lz)
    }

    /// `add_core` (z3): `c_exp ≥ d_exp` precondition (ensured by the caller's
    /// swap). Returns `(res_sgn[1], res_sig[sb+4], res_exp[eb+2])`.
    #[allow(clippy::too_many_arguments)]
    fn fp_add_core(
        &mut self,
        eb: u32,
        sb: u32,
        c_sgn: AstId,
        c_sig: AstId,
        c_exp: AstId,
        d_sgn: AstId,
        d_sig: AstId,
        d_exp: AstId,
    ) -> (AstId, AstId, AstId) {
        let mut exp_delta = self.m.mk_bvsub(c_exp, d_exp); // eb bits
        // Cap the delta when it could exceed the significand width.
        let ilog2 = |n: u32| 31 - n.leading_zeros();
        if ilog2(sb + 2) < eb + 2 {
            let cap = self.m.mk_bv((sb + 2) as i64, eb + 2);
            let delta_ext = self.m.mk_bv_zero_extend(2, exp_delta);
            let cap_le = self.m.mk_bvule(cap, delta_ext);
            let capped = self.m.mk_ite(cap_le, cap, delta_ext);
            exp_delta = self.m.mk_bv_extract(eb - 1, 0, capped);
        }
        let z3 = self.m.mk_bv(0, 3);
        let c_sig3 = self.m.mk_bv_concat(c_sig, z3); // sb+3
        let z3b = self.m.mk_bv(0, 3);
        let d_sig3 = self.m.mk_bv_concat(d_sig, z3b); // sb+3
        let z_low = self.m.mk_bv(0, sb + 3);
        let big_d = self.m.mk_bv_concat(d_sig3, z_low); // 2*(sb+3)
        let z_hi = self.m.mk_bv(0, 2 * (sb + 3) - eb);
        let shift_amt = self.m.mk_bv_concat(z_hi, exp_delta); // 2*(sb+3)
        let shifted_big = self.m.mk_bvlshr(big_d, shift_amt);
        let shifted_d = self.m.mk_bv_extract(2 * (sb + 3) - 1, sb + 3, shifted_big); // sb+3
        let sticky_raw = self.m.mk_bv_extract(sb + 2, 0, shifted_big); // sb+3
        let nil_s3 = self.m.mk_bv(0, sb + 3);
        let one_s3 = self.m.mk_bv(1, sb + 3);
        let sticky_eq = self.m.mk_eq(sticky_raw, nil_s3);
        let sticky = self.m.mk_ite(sticky_eq, nil_s3, one_s3);
        let shifted_d = self.m.mk_bvor(shifted_d, sticky);
        let eq_sgn = self.m.mk_eq(c_sgn, d_sgn);
        let c_sig5 = self.m.mk_bv_zero_extend(2, c_sig3); // sb+5
        let shifted_d5 = self.m.mk_bv_zero_extend(2, shifted_d); // sb+5
        let c_plus = self.m.mk_bvadd(c_sig5, shifted_d5);
        let c_minus = self.m.mk_bvsub(c_sig5, shifted_d5);
        let sum = self.m.mk_ite(eq_sgn, c_plus, c_minus); // sb+5
        let sign_bv = self.m.mk_bv_extract(sb + 4, sb + 4, sum);
        let n_sum = self.m.mk_bvneg(sum);
        let not_c = self.m.mk_bvnot(c_sgn);
        let not_d = self.m.mk_bvnot(d_sgn);
        let not_sign = self.m.mk_bvnot(sign_bv);
        let c1 = self.m.mk_bvand(not_c, d_sgn);
        let c1 = self.m.mk_bvand(c1, sign_bv);
        let c2 = self.m.mk_bvand(c_sgn, not_d);
        let c2 = self.m.mk_bvand(c2, not_sign);
        let c3 = self.m.mk_bvand(c_sgn, d_sgn);
        let res_sgn = self.m.mk_bvor(c1, c2);
        let res_sgn = self.m.mk_bvor(res_sgn, c3);
        let one1 = self.m.mk_bv(1, 1);
        let sign_eq_one = self.m.mk_eq(sign_bv, one1);
        let sig_abs = self.m.mk_ite(sign_eq_one, n_sum, sum);
        let res_sig = self.m.mk_bv_extract(sb + 3, 0, sig_abs); // sb+4
        let res_exp = self.m.mk_bv_sign_extend(2, c_exp); // eb+2
        (res_sgn, res_sig, res_exp)
    }

    /// Bit-blast `fp.add`/`fp.sub` on symbolic operands to a fresh FP term whose
    /// bit-vector is z3's exact packed result. `None` (→ gated `unknown`) if the
    /// format/rm is unsupported or an operand's bits are unavailable.
    fn fp_add_bv(&mut self, op: &str, rm: AstId, x: AstId, y: AstId) -> Option<AstId> {
        let (eb, sb) = self.fp_format_of(self.m.get_sort(x))?;
        // z3 asserts ebits <= sbits; bias/round need eb>=2, sb>=2.
        if eb < 2 || sb < 2 || eb > sb {
            return None;
        }
        let rm_c = self.rm_code(rm)?; // constant rounding mode only
        let rm3 = self.m.mk_bv(rm_c as i64, 3);
        let w = eb + sb;
        let bvx = self.fp_to_bv(x)?;
        let bvy0 = self.fp_to_bv(y)?;
        // fp.sub(rm,x,y) = fp.add(rm, x, neg(y)); neg flips the sign bit (NaN is
        // still NaN so the c1 special case is unaffected).
        let bvy = if op == "fp.sub" {
            let one_bit = self.m.mk_bv(1, 1);
            let zeros = self.m.mk_bv(0, w - 1);
            let msb = self.m.mk_bv_concat(one_bit, zeros);
            self.m.mk_bvxor(bvy0, msb)
        } else {
            bvy0
        };

        // Special constants (packed). z3 collapses every NaN to a single value
        // under core `=`, whereas z3rs models FP as bit-vectors with structural
        // equality; to stay consistent with z3rs's own `(_ NaN e s)` literal
        // (`fp_special`, canonical qNaN = top mantissa bit) the result NaN uses
        // that same pattern rather than z3's internal mk_nan (mantissa = 1).
        let mant = sb - 1;
        let exp_ones = ((1u64 << eb) - 1) << mant;
        let sign = 1u64 << (w - 1);
        let nan = self.fp_lit(exp_ones | (1u64 << (mant - 1)), w);
        let pzero = self.fp_lit(0, w);
        let nzero = self.fp_lit(sign, w);

        // Classification bits (pure field tests; is_neg/is_pos are sign-bit only).
        let clas = |ctx: &mut Self, bv: AstId| -> (AstId, AstId, AstId, AstId) {
            let exp = ctx.m.mk_bv_extract(w - 2, sb - 1, bv);
            let sigf = ctx.m.mk_bv_extract(sb - 2, 0, bv);
            let sbit = ctx.m.mk_bv_extract(w - 1, w - 1, bv);
            let ez = ctx.m.mk_bv(0, eb);
            let eo = ctx.m.mk_bvnot(ez);
            let sz = ctx.m.mk_bv(0, sb - 1);
            let exp_ones = ctx.m.mk_eq(exp, eo);
            let exp_zero = ctx.m.mk_eq(exp, ez);
            let sig_zero = ctx.m.mk_eq(sigf, sz);
            let sig_nz = ctx.m.mk_not(sig_zero);
            let is_nan = ctx.m.mk_and(&[exp_ones, sig_nz]);
            let is_inf = ctx.m.mk_and(&[exp_ones, sig_zero]);
            let is_zero = ctx.m.mk_and(&[exp_zero, sig_zero]);
            let one1 = ctx.m.mk_bv(1, 1);
            let is_neg = ctx.m.mk_eq(sbit, one1);
            (is_nan, is_inf, is_zero, is_neg)
        };
        let (x_nan, x_inf, x_zero, x_neg) = clas(self, bvx);
        let (y_nan, y_inf, y_zero, y_neg) = clas(self, bvy);

        // c1: NaN.
        let c1 = self.m.mk_or(&[x_nan, y_nan]);
        let v1 = nan;
        // c2: x infinite.
        let c2 = x_inf;
        let not_x_neg = self.m.mk_not(x_neg);
        let not_y_neg = self.m.mk_not(y_neg);
        let xy_a = self.m.mk_and(&[x_neg, not_y_neg]);
        let xy_b = self.m.mk_and(&[not_x_neg, y_neg]);
        let xy_xor = self.m.mk_or(&[xy_a, xy_b]);
        let inf_xor2 = self.m.mk_and(&[y_inf, xy_xor]);
        let v2 = self.m.mk_ite(inf_xor2, nan, bvx);
        // c3: y infinite.
        let c3 = y_inf;
        let inf_xor3 = self.m.mk_and(&[x_inf, xy_xor]);
        let v3 = self.m.mk_ite(inf_xor3, nan, bvy);
        // c4: both zero.
        let c4 = self.m.mk_and(&[x_zero, y_zero]);
        let signs_and = self.m.mk_and(&[x_neg, y_neg]);
        let rm_is_to_neg = self.fp_rm_is(rm3, 3);
        let rm_and_xor = self.m.mk_and(&[rm_is_to_neg, xy_xor]);
        let neg_cond = self.m.mk_or(&[signs_and, rm_and_xor]);
        let v4a = self.m.mk_ite(neg_cond, nzero, pzero);
        let v4 = self.m.mk_ite(signs_and, bvx, v4a);
        // c5: x zero.
        let c5 = x_zero;
        let v5 = bvy;
        // c6: y zero.
        let c6 = y_zero;
        let v6 = bvx;

        // Core path v7.
        let (a_sgn, a_sig, a_exp) = self.fp_unpack_add(bvx, eb, sb);
        let (b_sgn, b_sig, b_exp) = self.fp_unpack_add(bvy, eb, sb);
        let swap = self.m.mk_bvsle(a_exp, b_exp);
        let c_sgn = self.m.mk_ite(swap, b_sgn, a_sgn);
        let c_sig = self.m.mk_ite(swap, b_sig, a_sig);
        let c_exp = self.m.mk_ite(swap, b_exp, a_exp);
        let d_sgn = self.m.mk_ite(swap, a_sgn, b_sgn);
        let d_sig = self.m.mk_ite(swap, a_sig, b_sig);
        let d_exp = self.m.mk_ite(swap, a_exp, b_exp);
        let (res_sgn, res_sig, res_exp) =
            self.fp_add_core(eb, sb, c_sgn, c_sig, c_exp, d_sgn, d_sig, d_exp);
        let nil_sig = self.m.mk_bv(0, sb + 4);
        let is_zero_sig = self.m.mk_eq(res_sig, nil_sig);
        let zero_case = self.m.mk_ite(rm_is_to_neg, nzero, pzero);
        let rounded = self.fp_round(rm3, res_sgn, res_sig, res_exp, eb, sb);
        let v7 = self.m.mk_ite(is_zero_sig, zero_case, rounded);

        // Reverse-order ite chain (lower index wins).
        let r = self.m.mk_ite(c6, v6, v7);
        let r = self.m.mk_ite(c5, v5, r);
        let r = self.m.mk_ite(c4, v4, r);
        let r = self.m.mk_ite(c3, v3, r);
        let r = self.m.mk_ite(c2, v2, r);
        let result_bv = self.m.mk_ite(c1, v1, r);

        let fps = self.fp_sort(eb, sb);
        let result = self.fresh_const(fps);
        self.fp_bv.insert(result, result_bv);
        Some(result)
    }

    /// Bit-blast `fp.mul` on symbolic operands to z3's exact packed result
    /// (port of `fpa2bv_converter::mk_mul`). `None` (→ gated `unknown`) for an
    /// unsupported format/rm or unavailable operand bits.
    fn fp_mul_bv(&mut self, rm: AstId, x: AstId, y: AstId) -> Option<AstId> {
        let (eb, sb) = self.fp_format_of(self.m.get_sort(x))?;
        if eb < 2 || sb < 4 || eb > sb {
            return None; // sb ≥ 4 for the 4-bit round tail; eb ≤ sb for the shift
        }
        let rm_c = self.rm_code(rm)?;
        let rm3 = self.m.mk_bv(rm_c as i64, 3);
        let w = eb + sb;
        let bvx = self.fp_to_bv(x)?;
        let bvy = self.fp_to_bv(y)?;

        let mant = sb - 1;
        let exp_ones_v = ((1u64 << eb) - 1) << mant;
        let sign = 1u64 << (w - 1);
        let nan = self.fp_lit(exp_ones_v | (1u64 << (mant - 1)), w);
        let pzero = self.fp_lit(0, w);
        let nzero = self.fp_lit(sign, w);
        let pinf = self.fp_lit(exp_ones_v, w);
        let ninf = self.fp_lit(exp_ones_v | sign, w);

        // Classification (nan/inf/zero/neg) of each operand.
        let clas = |ctx: &mut Self, bv: AstId| -> (AstId, AstId, AstId, AstId) {
            let exp = ctx.m.mk_bv_extract(w - 2, sb - 1, bv);
            let sigf = ctx.m.mk_bv_extract(sb - 2, 0, bv);
            let sbit = ctx.m.mk_bv_extract(w - 1, w - 1, bv);
            let ez = ctx.m.mk_bv(0, eb);
            let eo = ctx.m.mk_bvnot(ez);
            let sz = ctx.m.mk_bv(0, sb - 1);
            let exp_ones = ctx.m.mk_eq(exp, eo);
            let exp_zero = ctx.m.mk_eq(exp, ez);
            let sig_zero = ctx.m.mk_eq(sigf, sz);
            let sig_nz = ctx.m.mk_not(sig_zero);
            let is_nan = ctx.m.mk_and(&[exp_ones, sig_nz]);
            let is_inf = ctx.m.mk_and(&[exp_ones, sig_zero]);
            let is_zero = ctx.m.mk_and(&[exp_zero, sig_zero]);
            let one1 = ctx.m.mk_bv(1, 1);
            let is_neg = ctx.m.mk_eq(sbit, one1);
            (is_nan, is_inf, is_zero, is_neg)
        };
        let (x_nan, x_inf, x_zero, x_neg) = clas(self, bvx);
        let (y_nan, y_inf, y_zero, y_neg) = clas(self, bvy);
        let x_pos = self.m.mk_not(x_neg);
        let y_pos = self.m.mk_not(y_neg);

        // c1: NaN.
        let c1 = self.m.mk_or(&[x_nan, y_nan]);
        let v1 = nan;
        // c2: x = +∞ → (y=0 ? NaN : ∞ with y's sign).
        let c2 = self.m.mk_and(&[x_inf, x_pos]);
        let y_sgn_inf = self.m.mk_ite(y_pos, pinf, ninf);
        let v2 = self.m.mk_ite(y_zero, nan, y_sgn_inf);
        // c3: y = +∞ → (x=0 ? NaN : ∞ with x's sign).
        let c3 = self.m.mk_and(&[y_inf, y_pos]);
        let x_sgn_inf = self.m.mk_ite(x_pos, pinf, ninf);
        let v3 = self.m.mk_ite(x_zero, nan, x_sgn_inf);
        // c4: x = −∞ → (y=0 ? NaN : ∞ with −y's sign).
        let c4 = self.m.mk_and(&[x_inf, x_neg]);
        let neg_y_sgn_inf = self.m.mk_ite(y_pos, ninf, pinf);
        let v4 = self.m.mk_ite(y_zero, nan, neg_y_sgn_inf);
        // c5: y = −∞ → (x=0 ? NaN : ∞ with −x's sign).
        let c5 = self.m.mk_and(&[y_inf, y_neg]);
        let neg_x_sgn_inf = self.m.mk_ite(x_pos, ninf, pinf);
        let v5 = self.m.mk_ite(x_zero, nan, neg_x_sgn_inf);
        // c6: x=0 ∨ y=0 → signed zero (sign = x.sign ⊕ y.sign).
        let c6 = self.m.mk_or(&[x_zero, y_zero]);
        let sa = self.m.mk_and(&[x_pos, y_neg]);
        let sb_ = self.m.mk_and(&[x_neg, y_pos]);
        let sign_xor = self.m.mk_or(&[sa, sb_]);
        let v6 = self.m.mk_ite(sign_xor, nzero, pzero);

        // Core multiplication.
        let (a_sgn, a_sig, a_exp, a_lz) = self.fp_unpack_norm(bvx, eb, sb);
        let (b_sgn, b_sig, b_exp, b_lz) = self.fp_unpack_norm(bvy, eb, sb);
        let res_sgn = self.m.mk_bvxor(a_sgn, b_sgn);
        let a_exp_ext = self.m.mk_bv_sign_extend(2, a_exp);
        let b_exp_ext = self.m.mk_bv_sign_extend(2, b_exp);
        let a_lz_ext = self.m.mk_bv_zero_extend(2, a_lz);
        let b_lz_ext = self.m.mk_bv_zero_extend(2, b_lz);
        let ta = self.m.mk_bvsub(a_exp_ext, a_lz_ext);
        let tb = self.m.mk_bvsub(b_exp_ext, b_lz_ext);
        let res_exp = self.m.mk_bvadd(ta, tb); // eb+2
        let a_sig_ext = self.m.mk_bv_zero_extend(sb, a_sig); // 2·sb
        let b_sig_ext = self.m.mk_bv_zero_extend(sb, b_sig);
        let product = self.m.mk_bvmul(a_sig_ext, b_sig_ext); // 2·sb
        let h_p = self.m.mk_bv_extract(2 * sb - 1, sb, product); // sb bits
        // 4 round bits: top 3 of the low half + sticky (OR of the rest).
        let part = self.m.mk_bv_extract(sb - 4, 0, product); // sb-3 bits
        let pz = self.m.mk_bv(0, sb - 3);
        let part_zero = self.m.mk_eq(part, pz);
        let zero1 = self.m.mk_bv(0, 1);
        let one1b = self.m.mk_bv(1, 1);
        let sticky = self.m.mk_ite(part_zero, zero1, one1b);
        let top3 = self.m.mk_bv_extract(sb - 1, sb - 3, product); // 3 bits
        let rbits = self.m.mk_bv_concat(top3, sticky); // 4 bits
        let res_sig = self.m.mk_bv_concat(h_p, rbits); // sb+4
        let v7 = self.fp_round(rm3, res_sgn, res_sig, res_exp, eb, sb);

        // Tie special cases together (lower index wins).
        let r = self.m.mk_ite(c6, v6, v7);
        let r = self.m.mk_ite(c5, v5, r);
        let r = self.m.mk_ite(c4, v4, r);
        let r = self.m.mk_ite(c3, v3, r);
        let r = self.m.mk_ite(c2, v2, r);
        let result_bv = self.m.mk_ite(c1, v1, r);

        let fps = self.fp_sort(eb, sb);
        let result = self.fresh_const(fps);
        self.fp_bv.insert(result, result_bv);
        Some(result)
    }

    /// Bit-blast `fp.div` on symbolic operands to z3's exact packed result
    /// (port of `fpa2bv_converter::mk_div`). `None` (→ gated `unknown`) for an
    /// unsupported format/rm or unavailable operand bits.
    fn fp_div_bv(&mut self, rm: AstId, x: AstId, y: AstId) -> Option<AstId> {
        let (eb, sb) = self.fp_format_of(self.m.get_sort(x))?;
        if eb < 2 || sb < 4 || eb > sb {
            return None;
        }
        let rm_c = self.rm_code(rm)?;
        let rm3 = self.m.mk_bv(rm_c as i64, 3);
        let w = eb + sb;
        let bvx = self.fp_to_bv(x)?;
        let bvy = self.fp_to_bv(y)?;

        let mant = sb - 1;
        let exp_ones_v = ((1u64 << eb) - 1) << mant;
        let sign = 1u64 << (w - 1);
        let nan = self.fp_lit(exp_ones_v | (1u64 << (mant - 1)), w);
        let pzero = self.fp_lit(0, w);
        let nzero = self.fp_lit(sign, w);
        let pinf = self.fp_lit(exp_ones_v, w);
        let ninf = self.fp_lit(exp_ones_v | sign, w);

        let clas = |ctx: &mut Self, bv: AstId| -> (AstId, AstId, AstId, AstId) {
            let exp = ctx.m.mk_bv_extract(w - 2, sb - 1, bv);
            let sigf = ctx.m.mk_bv_extract(sb - 2, 0, bv);
            let sbit = ctx.m.mk_bv_extract(w - 1, w - 1, bv);
            let ez = ctx.m.mk_bv(0, eb);
            let eo = ctx.m.mk_bvnot(ez);
            let sz = ctx.m.mk_bv(0, sb - 1);
            let exp_ones = ctx.m.mk_eq(exp, eo);
            let exp_zero = ctx.m.mk_eq(exp, ez);
            let sig_zero = ctx.m.mk_eq(sigf, sz);
            let sig_nz = ctx.m.mk_not(sig_zero);
            let is_nan = ctx.m.mk_and(&[exp_ones, sig_nz]);
            let is_inf = ctx.m.mk_and(&[exp_ones, sig_zero]);
            let is_zero = ctx.m.mk_and(&[exp_zero, sig_zero]);
            let one1 = ctx.m.mk_bv(1, 1);
            let is_neg = ctx.m.mk_eq(sbit, one1);
            (is_nan, is_inf, is_zero, is_neg)
        };
        let (x_nan, x_inf, x_zero, x_neg) = clas(self, bvx);
        let (y_nan, y_inf, y_zero, y_neg) = clas(self, bvy);
        let x_pos = self.m.mk_not(x_neg);
        let y_pos = self.m.mk_not(y_neg);
        let sa = self.m.mk_and(&[x_pos, y_neg]);
        let sb2 = self.m.mk_and(&[x_neg, y_pos]);
        let signs_xor = self.m.mk_or(&[sa, sb2]);
        let xy_zero = self.m.mk_ite(signs_xor, nzero, pzero);

        // c1: NaN.
        let c1 = self.m.mk_or(&[x_nan, y_nan]);
        let v1 = nan;
        // c2: x=+∞ → (y=∞ ? NaN : ∞ with y's sign).
        let c2 = self.m.mk_and(&[x_inf, x_pos]);
        let y_sgn_inf = self.m.mk_ite(y_pos, pinf, ninf);
        let v2 = self.m.mk_ite(y_inf, nan, y_sgn_inf);
        // c3: y=+∞ → (x=∞ ? NaN : signed zero).
        let c3 = self.m.mk_and(&[y_inf, y_pos]);
        let v3 = self.m.mk_ite(x_inf, nan, xy_zero);
        // c4: x=-∞ → (y=∞ ? NaN : ∞ with −y's sign).
        let c4 = self.m.mk_and(&[x_inf, x_neg]);
        let neg_y_sgn_inf = self.m.mk_ite(y_pos, ninf, pinf);
        let v4 = self.m.mk_ite(y_inf, nan, neg_y_sgn_inf);
        // c5: y=-∞ → (x=∞ ? NaN : signed zero).
        let c5 = self.m.mk_and(&[y_inf, y_neg]);
        let v5 = self.m.mk_ite(x_inf, nan, xy_zero);
        // c6: y=0 → (x=0 ? NaN : ∞ with xor sign).
        let c6 = y_zero;
        let sgn_inf = self.m.mk_ite(signs_xor, ninf, pinf);
        let v6 = self.m.mk_ite(x_zero, nan, sgn_inf);
        // c7: x=0 → signed zero.
        let c7 = x_zero;
        let v7 = xy_zero;

        // Core division.
        let (a_sgn, a_sig, a_exp, a_lz) = self.fp_unpack_norm(bvx, eb, sb);
        let (b_sgn, b_sig, b_exp, b_lz) = self.fp_unpack_norm(bvy, eb, sb);
        let res_sgn = self.m.mk_bvxor(a_sgn, b_sgn);
        let a_exp_ext = self.m.mk_bv_sign_extend(2, a_exp);
        let b_exp_ext = self.m.mk_bv_sign_extend(2, b_exp);
        let a_lz_ext = self.m.mk_bv_zero_extend(2, a_lz);
        let b_lz_ext = self.m.mk_bv_zero_extend(2, b_lz);
        let ta = self.m.mk_bvsub(a_exp_ext, a_lz_ext);
        let tb = self.m.mk_bvsub(b_exp_ext, b_lz_ext);
        let res_exp = self.m.mk_bvsub(ta, tb); // eb+2
        let extra = sb + 2;
        let zeros_low = self.m.mk_bv(0, sb + extra);
        let a_sig_ext = self.m.mk_bv_concat(a_sig, zeros_low); // 3·sb+2
        let b_sig_ext = self.m.mk_bv_zero_extend(sb + extra, b_sig); // 3·sb+2
        let quotient = self.m.mk_bvudiv(a_sig_ext, b_sig_ext); // 3·sb+2
        // sticky = OR of quotient[extra-2 : 0].
        let low = self.m.mk_bv_extract(extra - 2, 0, quotient);
        let low_z = self.m.mk_bv(0, extra - 1);
        let low_zero = self.m.mk_eq(low, low_z);
        let zero1 = self.m.mk_bv(0, 1);
        let one1 = self.m.mk_bv(1, 1);
        let sticky = self.m.mk_ite(low_zero, zero1, one1);
        let midbits = self.m.mk_bv_extract(extra + sb + 1, extra - 1, quotient); // sb+3
        let res_sig = self.m.mk_bv_concat(midbits, sticky); // sb+4
        // too_large: any bit set in the top slice.
        let upper = self.m.mk_bv_extract(3 * sb + 1, extra + sb + 2, quotient); // sb-2
        let upper_z = self.m.mk_bv(0, sb - 2);
        let upper_eq = self.m.mk_eq(upper, upper_z);
        let too_large = self.m.mk_not(upper_eq);
        let c8 = too_large;
        let v8 = self.m.mk_ite(signs_xor, ninf, pinf);

        // Normalise the quotient significand.
        let res_sig_lz = self.fp_leading_zeros(res_sig, sb + 4); // sb+4
        let one_s4 = self.m.mk_bv(1, sb + 4);
        let shift_amount = self.m.mk_bvsub(res_sig_lz, one_s4);
        let shift_cond = self.m.mk_bvule(res_sig_lz, one_s4);
        let res_sig_shifted = self.m.mk_bvshl(res_sig, shift_amount);
        let shift_low = self.m.mk_bv_extract(eb + 1, 0, shift_amount); // eb+2
        let res_exp_shifted = self.m.mk_bvsub(res_exp, shift_low);
        let res_sig_f = self.m.mk_ite(shift_cond, res_sig, res_sig_shifted);
        let res_exp_f = self.m.mk_ite(shift_cond, res_exp, res_exp_shifted);
        let v9 = self.fp_round(rm3, res_sgn, res_sig_f, res_exp_f, eb, sb);

        // Tie together (lower index wins).
        let r = self.m.mk_ite(c8, v8, v9);
        let r = self.m.mk_ite(c7, v7, r);
        let r = self.m.mk_ite(c6, v6, r);
        let r = self.m.mk_ite(c5, v5, r);
        let r = self.m.mk_ite(c4, v4, r);
        let r = self.m.mk_ite(c3, v3, r);
        let r = self.m.mk_ite(c2, v2, r);
        let result_bv = self.m.mk_ite(c1, v1, r);

        let fps = self.fp_sort(eb, sb);
        let result = self.fresh_const(fps);
        self.fp_bv.insert(result, result_bv);
        Some(result)
    }

    /// Bit-blast `fp.sqrt` on a symbolic operand (port of `mk_sqrt`: the
    /// restoring bit-by-bit square root, Handbook of FP Arithmetic alg. 10.2).
    /// `None` for an unsupported format/rm or unavailable bits.
    fn fp_sqrt_bv(&mut self, rm: AstId, x: AstId) -> Option<AstId> {
        let (eb, sb) = self.fp_format_of(self.m.get_sort(x))?;
        if eb < 2 || sb < 4 || eb > sb || sb + 3 >= 63 {
            return None;
        }
        let rm_c = self.rm_code(rm)?;
        let rm3 = self.m.mk_bv(rm_c as i64, 3);
        let w = eb + sb;
        let bvx = self.fp_to_bv(x)?;
        let mant = sb - 1;
        let exp_ones_v = ((1u64 << eb) - 1) << mant;
        let nan = self.fp_lit(exp_ones_v | (1u64 << (mant - 1)), w);

        // Classification.
        let exp = self.m.mk_bv_extract(w - 2, sb - 1, bvx);
        let sigf = self.m.mk_bv_extract(sb - 2, 0, bvx);
        let sbit = self.m.mk_bv_extract(w - 1, w - 1, bvx);
        let ez = self.m.mk_bv(0, eb);
        let eo = self.m.mk_bvnot(ez);
        let sz = self.m.mk_bv(0, sb - 1);
        let exp_ones = self.m.mk_eq(exp, eo);
        let exp_zero = self.m.mk_eq(exp, ez);
        let sig_zero = self.m.mk_eq(sigf, sz);
        let sig_nz = self.m.mk_not(sig_zero);
        let one1 = self.m.mk_bv(1, 1);
        let x_nan = self.m.mk_and(&[exp_ones, sig_nz]);
        let x_inf = self.m.mk_and(&[exp_ones, sig_zero]);
        let x_zero = self.m.mk_and(&[exp_zero, sig_zero]);
        let x_neg = self.m.mk_eq(sbit, one1);
        let x_pos = self.m.mk_not(x_neg);

        // c1 NaN→x, c2 +∞→x, c3 ±0→x, c4 x<0→NaN.
        let c1 = x_nan;
        let v1 = bvx;
        let c2 = self.m.mk_and(&[x_inf, x_pos]);
        let v2 = bvx;
        let c3 = x_zero;
        let v3 = bvx;
        let c4 = x_neg;
        let v4 = nan;

        // Core square root.
        let (_a_sgn, a_sig, a_exp, a_lz) = self.fp_unpack_norm(bvx, eb, sb);
        let zero1 = self.m.mk_bv(0, 1);
        let res_sgn = zero1;
        let ae = self.m.mk_bv_sign_extend(1, a_exp);
        let al = self.m.mk_bv_zero_extend(1, a_lz);
        let real_exp = self.m.mk_bvsub(ae, al); // eb+1
        let re_hi = self.m.mk_bv_extract(eb, 1, real_exp); // eb bits (exp/2)
        let res_exp = self.m.mk_bv_sign_extend(2, re_hi); // eb+2
        let re_lo = self.m.mk_bv_extract(0, 0, real_exp);
        let e_is_odd = self.m.mk_eq(re_lo, one1);
        let a_z = self.m.mk_bv_concat(a_sig, zero1); // sb+1
        let z_a = self.m.mk_bv_concat(zero1, a_sig); // sb+1
        let sig_prime = self.m.mk_ite(e_is_odd, a_z, z_a); // sb+1
        let mut q = self.m.mk_bv(1i64 << (sb + 3), sb + 5); // 2^(sb+3)
        let z4 = self.m.mk_bv(0, 4);
        let sp4 = self.m.mk_bv_concat(sig_prime, z4); // sb+5
        let mut r = self.m.mk_bvsub(sp4, q);
        let mut s = q;
        for _ in 0..(sb + 3) {
            let s_hi = self.m.mk_bv_extract(sb + 4, 1, s); // sb+4
            s = self.m.mk_bv_concat(zero1, s_hi); // sb+5
            let qz = self.m.mk_bv_concat(q, zero1); // sb+6
            let zs = self.m.mk_bv_concat(zero1, s); // sb+6
            let two_q_plus_s = self.m.mk_bvadd(qz, zs);
            let rz = self.m.mk_bv_concat(r, zero1); // sb+6
            let t = self.m.mk_bvsub(rz, two_q_plus_s);
            let t_top = self.m.mk_bv_extract(sb + 5, sb + 5, t);
            let t_lt_0 = self.m.mk_eq(t_top, one1);
            let q_or_s = self.m.mk_bvor(q, s);
            q = self.m.mk_ite(t_lt_0, q, q_or_s);
            let r_lo = self.m.mk_bv_extract(sb + 3, 0, r); // sb+4
            let r_shftd = self.m.mk_bv_concat(r_lo, zero1); // sb+5
            let t_lo = self.m.mk_bv_extract(sb + 4, 0, t); // sb+5
            r = self.m.mk_ite(t_lt_0, r_shftd, t_lo);
        }
        let r_zero = self.m.mk_bv(0, sb + 5);
        let is_exact = self.m.mk_eq(r, r_zero);
        let last = self.m.mk_bv_extract(0, 0, q);
        let rest = self.m.mk_bv_extract(sb + 3, 1, q); // sb+3
        let rest_ext = self.m.mk_bv_zero_extend(1, rest); // sb+4
        let last_ext = self.m.mk_bv_zero_extend(sb + 3, last); // sb+4
        let one_sbits4 = self.m.mk_bv(1, sb + 4);
        let sticky = self.m.mk_ite(is_exact, last_ext, one_sbits4);
        let res_sig = self.m.mk_bvor(rest_ext, sticky); // sb+4
        let v5 = self.fp_round(rm3, res_sgn, res_sig, res_exp, eb, sb);

        let r = self.m.mk_ite(c4, v4, v5);
        let r = self.m.mk_ite(c3, v3, r);
        let r = self.m.mk_ite(c2, v2, r);
        let result_bv = self.m.mk_ite(c1, v1, r);

        let fps = self.fp_sort(eb, sb);
        let result = self.fresh_const(fps);
        self.fp_bv.insert(result, result_bv);
        Some(result)
    }

    /// Bit-blast `fp.fma` (fused `x·y + z` with a single rounding) — port of
    /// z3's `mk_fma`. `None` for unsupported format/rm or unavailable bits.
    fn fp_fma_bv(&mut self, rm: AstId, x: AstId, y: AstId, z: AstId) -> Option<AstId> {
        let (eb, sb) = self.fp_format_of(self.m.get_sort(x))?;
        if eb < 2 || sb < 5 || eb > sb {
            return None; // sb ≥ 5 ⇒ z3's `too_short` padding is 0
        }
        let rm_c = self.rm_code(rm)?;
        let rm_is_to_neg = rm_c == 3;
        let w = eb + sb;
        let bvx = self.fp_to_bv(x)?;
        let bvy = self.fp_to_bv(y)?;
        let bvz = self.fp_to_bv(z)?;
        let mant = sb - 1;
        let exp_ones_v = ((1u64 << eb) - 1) << mant;
        let sgnbit = 1u64 << (w - 1);
        let nan = self.fp_lit(exp_ones_v | (1u64 << (mant - 1)), w);
        let pzero = self.fp_lit(0, w);
        let nzero = self.fp_lit(sgnbit, w);
        let pinf = self.fp_lit(exp_ones_v, w);
        let ninf = self.fp_lit(exp_ones_v | sgnbit, w);

        let clas = |ctx: &mut Self, bv: AstId| -> (AstId, AstId, AstId, AstId) {
            let exp = ctx.m.mk_bv_extract(w - 2, sb - 1, bv);
            let sigf = ctx.m.mk_bv_extract(sb - 2, 0, bv);
            let sbit = ctx.m.mk_bv_extract(w - 1, w - 1, bv);
            let ez = ctx.m.mk_bv(0, eb);
            let eo = ctx.m.mk_bvnot(ez);
            let sz = ctx.m.mk_bv(0, sb - 1);
            let exp_ones = ctx.m.mk_eq(exp, eo);
            let exp_zero = ctx.m.mk_eq(exp, ez);
            let sig_zero = ctx.m.mk_eq(sigf, sz);
            let sig_nz = ctx.m.mk_not(sig_zero);
            let is_nan = ctx.m.mk_and(&[exp_ones, sig_nz]);
            let is_inf = ctx.m.mk_and(&[exp_ones, sig_zero]);
            let is_zero = ctx.m.mk_and(&[exp_zero, sig_zero]);
            let one1 = ctx.m.mk_bv(1, 1);
            let is_neg = ctx.m.mk_eq(sbit, one1);
            (is_nan, is_inf, is_zero, is_neg)
        };
        let (x_nan, x_inf, x_zero, x_neg) = clas(self, bvx);
        let (y_nan, y_inf, y_zero, y_neg) = clas(self, bvy);
        let (z_nan, z_inf, z_zero, z_neg) = clas(self, bvz);
        let x_pos = self.m.mk_not(x_neg);
        let y_pos = self.m.mk_not(y_neg);
        let z_pos = self.m.mk_not(z_neg);

        // inf_cond = z=∞ ∧ (x.sgn ⊕ y.sgn ⊕ z.sgn).
        let xor1a = self.m.mk_and(&[x_neg, y_pos]);
        let xor1b = self.m.mk_and(&[x_pos, y_neg]);
        let inf_xor1 = self.m.mk_or(&[xor1a, xor1b]);
        let n_ix = self.m.mk_not(inf_xor1);
        let ix2a = self.m.mk_and(&[inf_xor1, z_pos]);
        let ix2b = self.m.mk_and(&[n_ix, z_neg]);
        let inf_xor = self.m.mk_or(&[ix2a, ix2b]);
        let inf_cond = self.m.mk_and(&[z_inf, inf_xor]);

        // c1: any NaN.
        let c1 = self.m.mk_or(&[x_nan, y_nan, z_nan]);
        let v1 = nan;
        // c2: x=+∞.
        let c2 = self.m.mk_and(&[x_inf, x_pos]);
        let y_sgn_inf = self.m.mk_ite(y_pos, pinf, ninf);
        let inf_or2 = self.m.mk_or(&[y_zero, inf_cond]);
        let v2 = self.m.mk_ite(inf_or2, nan, y_sgn_inf);
        // c3: y=+∞.
        let c3 = self.m.mk_and(&[y_inf, y_pos]);
        let x_sgn_inf = self.m.mk_ite(x_pos, pinf, ninf);
        let inf_or3 = self.m.mk_or(&[x_zero, inf_cond]);
        let v3 = self.m.mk_ite(inf_or3, nan, x_sgn_inf);
        // c4: x=-∞.
        let c4 = self.m.mk_and(&[x_inf, x_neg]);
        let neg_y_sgn_inf = self.m.mk_ite(y_pos, ninf, pinf);
        let inf_or4 = self.m.mk_or(&[y_zero, inf_cond]);
        let v4 = self.m.mk_ite(inf_or4, nan, neg_y_sgn_inf);
        // c5: y=-∞.
        let c5 = self.m.mk_and(&[y_inf, y_neg]);
        let neg_x_sgn_inf = self.m.mk_ite(x_pos, ninf, pinf);
        let inf_or5 = self.m.mk_or(&[x_zero, inf_cond]);
        let v5 = self.m.mk_ite(inf_or5, nan, neg_x_sgn_inf);
        // c6: z=±∞ → z.
        let c6 = z_inf;
        let v6 = bvz;
        // c7: x=0 ∨ y=0 → z (with the c71 sign-cancel special case).
        let c7 = self.m.mk_or(&[x_zero, y_zero]);
        let xy_sgn_a = self.m.mk_and(&[x_neg, y_pos]);
        let xy_sgn_b = self.m.mk_and(&[x_pos, y_neg]);
        let xy_sgn = self.m.mk_or(&[xy_sgn_a, xy_sgn_b]);
        let n_xy = self.m.mk_not(xy_sgn);
        let xyz_a = self.m.mk_and(&[xy_sgn, z_pos]);
        let xyz_b = self.m.mk_and(&[n_xy, z_neg]);
        let xyz_sgn = self.m.mk_or(&[xyz_a, xyz_b]);
        let c71 = self.m.mk_and(&[z_zero, xyz_sgn]);
        let zero_cond = if rm_is_to_neg { nzero } else { pzero };
        let v7 = self.m.mk_ite(c71, zero_cond, bvz);

        // === fused core ===
        let (a_sgn, a_sig, a_exp, a_lz) = self.fp_unpack_norm(bvx, eb, sb);
        let (b_sgn, b_sig, b_exp, b_lz) = self.fp_unpack_norm(bvy, eb, sb);
        let (c_sgn, c_sig, c_exp, c_lz) = self.fp_unpack_norm(bvz, eb, sb);
        let a_lz_e = self.m.mk_bv_zero_extend(2, a_lz);
        let b_lz_e = self.m.mk_bv_zero_extend(2, b_lz);
        let c_lz_e = self.m.mk_bv_zero_extend(2, c_lz);
        let a_sig_e = self.m.mk_bv_zero_extend(sb, a_sig); // 2sb
        let b_sig_e = self.m.mk_bv_zero_extend(sb, b_sig);
        let a_exp_e = self.m.mk_bv_sign_extend(2, a_exp); // eb+2
        let b_exp_e = self.m.mk_bv_sign_extend(2, b_exp);
        let c_exp_e0 = self.m.mk_bv_sign_extend(2, c_exp);
        let mul_sgn = self.m.mk_bvxor(a_sgn, b_sgn);
        let ta = self.m.mk_bvsub(a_exp_e, a_lz_e);
        let tb = self.m.mk_bvsub(b_exp_e, b_lz_e);
        let mul_exp = self.m.mk_bvadd(ta, tb); // eb+2
        let mul_sig0 = self.m.mk_bvmul(a_sig_e, b_sig_e); // 2sb
        let z_sb2 = self.m.mk_bv(0, sb + 2);
        let c_cat = self.m.mk_bv_concat(c_sig, z_sb2); // 2sb+1
        let c_sig_ext = self.m.mk_bv_zero_extend(1, c_cat); // 2sb+2
        let c_exp_ext = self.m.mk_bvsub(c_exp_e0, c_lz_e); // eb+2
        let z3b = self.m.mk_bv(0, 3);
        let mul_sig = self.m.mk_bv_concat(mul_sig0, z3b); // 2sb+3
        let swap_cond = self.m.mk_bvsle(mul_exp, c_exp_ext);
        let e_sgn = self.m.mk_ite(swap_cond, c_sgn, mul_sgn);
        let e_sig = self.m.mk_ite(swap_cond, c_sig_ext, mul_sig); // 2sb+3
        let e_exp = self.m.mk_ite(swap_cond, c_exp_ext, mul_exp); // eb+2
        let f_sgn = self.m.mk_ite(swap_cond, mul_sgn, c_sgn);
        let f_sig = self.m.mk_ite(swap_cond, mul_sig, c_sig_ext); // 2sb+3
        let f_exp = self.m.mk_ite(swap_cond, mul_exp, c_exp_ext); // eb+2
        let exp_delta0 = self.m.mk_bvsub(e_exp, f_exp);
        let cap = self.m.mk_bv((2 * sb + 3) as i64, eb + 2);
        let cap_le = self.m.mk_bvule(cap, exp_delta0);
        let exp_delta = self.m.mk_ite(cap_le, cap, exp_delta0); // eb+2
        let z_sb = self.m.mk_bv(0, sb);
        let f_cat = self.m.mk_bv_concat(f_sig, z_sb); // 3sb+3
        let delta_ext = self.m.mk_bv_zero_extend((3 * sb + 3) - (eb + 2), exp_delta); // 3sb+3
        let shifted_big = self.m.mk_bvlshr(f_cat, delta_ext); // 3sb+3
        let shifted_f_sig = self.m.mk_bv_extract(3 * sb + 2, sb, shifted_big); // 2sb+3
        let align_raw = self.m.mk_bv_extract(sb - 1, 0, shifted_big); // sb
        let araw_z = self.m.mk_bv(0, sb);
        let araw_zero = self.m.mk_eq(align_raw, araw_z);
        let zero1 = self.m.mk_bv(0, 1);
        let one1 = self.m.mk_bv(1, 1);
        let align_sticky = self.m.mk_ite(araw_zero, zero1, one1); // 1
        let e_sig5 = self.m.mk_bv_zero_extend(2, e_sig); // 2sb+5
        let sf_sig5 = self.m.mk_bv_zero_extend(2, shifted_f_sig); // 2sb+5
        let eq_sgn = self.m.mk_eq(e_sgn, f_sgn);
        let sticky_wide = self.m.mk_bv_zero_extend(2 * sb + 4, align_sticky); // 2sb+5
        let epf0 = self.m.mk_bvadd(e_sig5, sf_sig5);
        let epf_lsb = self.m.mk_bv_extract(0, 0, epf0);
        let epf_lsb0 = self.m.mk_eq(epf_lsb, zero1);
        let epf_add = self.m.mk_bvadd(epf0, sticky_wide);
        let e_plus_f = self.m.mk_ite(epf_lsb0, epf_add, epf0);
        let emf0 = self.m.mk_bvsub(e_sig5, sf_sig5);
        let emf_lsb = self.m.mk_bv_extract(0, 0, emf0);
        let emf_lsb0 = self.m.mk_eq(emf_lsb, zero1);
        let emf_sub = self.m.mk_bvsub(emf0, sticky_wide);
        let e_minus_f = self.m.mk_ite(emf_lsb0, emf_sub, emf0);
        let sum = self.m.mk_ite(eq_sgn, e_plus_f, e_minus_f); // 2sb+5
        let sign_bv = self.m.mk_bv_extract(2 * sb + 4, 2 * sb + 4, sum);
        let n_sum = self.m.mk_bvneg(sum);
        let sign_eq1 = self.m.mk_eq(sign_bv, one1);
        let sig_abs = self.m.mk_ite(sign_eq1, n_sum, sum); // 2sb+5, ≥ 0
        let not_e = self.m.mk_bvnot(e_sgn);
        let not_f = self.m.mk_bvnot(f_sgn);
        let not_sb = self.m.mk_bvnot(sign_bv);
        let rc1 = self.m.mk_bvand(not_e, f_sgn);
        let rc1 = self.m.mk_bvand(rc1, sign_bv);
        let rc2 = self.m.mk_bvand(e_sgn, not_f);
        let rc2 = self.m.mk_bvand(rc2, not_sb);
        let rc3 = self.m.mk_bvand(e_sgn, f_sgn);
        let res_sgn = self.m.mk_bvor(rc1, rc2);
        let res_sgn = self.m.mk_bvor(res_sgn, rc3);
        let extra = self.m.mk_bv_extract(2 * sb + 4, 2 * sb + 3, sig_abs); // 2
        let extra_z = self.m.mk_bv(0, 2);
        let extra_is_zero = self.m.mk_eq(extra, extra_z);
        let one_e2 = self.m.mk_bv(1, eb + 2);
        let e_exp_p1 = self.m.mk_bvadd(e_exp, one_e2);
        let res_exp = self.m.mk_ite(extra_is_zero, e_exp, e_exp_p1); // eb+2
        let min_exp = self.fp_ilit(2 - (1i64 << (eb - 1)), eb);
        let min_exp = self.m.mk_bv_sign_extend(2, min_exp); // eb+2
        let sig_lz0 = self.fp_leading_zeros(sig_abs, eb + 2);
        let two_e2 = self.m.mk_bv(2, eb + 2);
        let sig_lz = self.m.mk_bvsub(sig_lz0, two_e2);
        let max_delta = self.m.mk_bvsub(res_exp, min_exp);
        let lz_le = self.m.mk_bvsle(sig_lz, max_delta);
        let sig_lz_capped = self.m.mk_ite(lz_le, sig_lz, max_delta);
        let zero_e2 = self.m.mk_bv(0, eb + 2);
        let ge0 = self.m.mk_bvsle(zero_e2, sig_lz_capped);
        let renorm = self.m.mk_ite(ge0, sig_lz_capped, zero_e2);
        let res_exp = self.m.mk_bvsub(res_exp, renorm);
        let renorm_ext = self.m.mk_bv_zero_extend(2 * sb + 3 - eb, renorm); // 2sb+5
        let sig_abs = self.m.mk_bvshl(sig_abs, renorm_ext); // 2sb+5
        // Round-significand assembly (too_short = 0).
        let sticky_h1 = self.m.mk_bv_extract(sb - 2, 0, sig_abs); // sb-1
        let sig_abs_h1 = self.m.mk_bv_extract(2 * sb + 4, sb - 1, sig_abs); // sb+6
        let sh1z = self.m.mk_bv(0, sb - 1);
        let sh1_eq = self.m.mk_eq(sticky_h1, sh1z);
        let sh1_nz = self.m.mk_not(sh1_eq);
        let sh1_bit = self.m.mk_ite(sh1_nz, one1, zero1);
        let sh1_red = self.m.mk_bv_zero_extend(sb + 5, sh1_bit); // sb+6
        let h1_f = self.m.mk_bvor(sig_abs_h1, sh1_red); // sb+6
        let res_sig_1 = self.m.mk_bv_extract(sb + 3, 0, h1_f); // sb+4
        let sig_abs_h2 = self.m.mk_bv_extract(2 * sb + 4, sb, sig_abs); // sb+5
        let sh2_red = self.m.mk_bv_zero_extend(sb + 4, sh1_bit); // sb+5 (z3 uses sticky_h1)
        let h2_or = self.m.mk_bvor(sig_abs_h2, sh2_red); // sb+5
        let h2_f = self.m.mk_bv_zero_extend(1, h2_or); // sb+6
        let res_sig_2 = self.m.mk_bv_extract(sb + 3, 0, h2_f); // sb+4
        let res_sig = self.m.mk_ite(extra_is_zero, res_sig_1, res_sig_2); // sb+4
        let nil_s4 = self.m.mk_bv(0, sb + 4);
        let is_zero_sig = self.m.mk_eq(res_sig, nil_s4);
        let zero_case = if rm_is_to_neg { nzero } else { pzero };
        let rm3 = self.m.mk_bv(rm_c as i64, 3);
        let rounded = self.fp_round(rm3, res_sgn, res_sig, res_exp, eb, sb);
        let v8 = self.m.mk_ite(is_zero_sig, zero_case, rounded);

        // Tie together (lower index wins).
        let r = self.m.mk_ite(c7, v7, v8);
        let r = self.m.mk_ite(c6, v6, r);
        let r = self.m.mk_ite(c5, v5, r);
        let r = self.m.mk_ite(c4, v4, r);
        let r = self.m.mk_ite(c3, v3, r);
        let r = self.m.mk_ite(c2, v2, r);
        let result_bv = self.m.mk_ite(c1, v1, r);

        let fps = self.fp_sort(eb, sb);
        let result = self.fresh_const(fps);
        self.fp_bv.insert(result, result_bv);
        Some(result)
    }

    /// Bit-blast `(_ to_fp to_eb to_sb) rm x` where `x` is a **float** (format
    /// conversion; port of z3's `mk_to_fp_float`). Handles same-format (identity)
    /// and the widening-exponent case (`from_eb < to_eb+2`, e.g. Float16→32,
    /// Float32→64); the narrowing-exponent case is gated (`None`).
    fn fp_to_fp_bv(&mut self, rm: AstId, x: AstId, to_eb: u32, to_sb: u32) -> Option<AstId> {
        let (fe, fs) = self.fp_format_of(self.m.get_sort(x))?;
        if (fe, fs) == (to_eb, to_sb) {
            return Some(x); // identity
        }
        if fe < 2 || fs < 2 || to_eb < 2 || to_sb < 2 || to_eb > to_sb || fe >= to_eb + 2 {
            return None; // narrowing exponent (or bad format) — gate
        }
        let rm_c = self.rm_code(rm)?;
        let rm3 = self.m.mk_bv(rm_c as i64, 3);
        let fw = fe + fs;
        let tw = to_eb + to_sb;
        let bvx = self.fp_to_bv(x)?;
        let tmant = to_sb - 1;
        let t_exp_ones = ((1u64 << to_eb) - 1) << tmant;
        let t_sign = 1u64 << (tw - 1);
        let nan = self.fp_lit(t_exp_ones | (1u64 << (tmant - 1)), tw);
        let pzero = self.fp_lit(0, tw);
        let nzero = self.fp_lit(t_sign, tw);
        let pinf = self.fp_lit(t_exp_ones, tw);
        let ninf = self.fp_lit(t_exp_ones | t_sign, tw);

        // Classification in the FROM format.
        let expf = self.m.mk_bv_extract(fw - 2, fs - 1, bvx);
        let sigf = self.m.mk_bv_extract(fs - 2, 0, bvx);
        let sbit = self.m.mk_bv_extract(fw - 1, fw - 1, bvx);
        let ez = self.m.mk_bv(0, fe);
        let eo = self.m.mk_bvnot(ez);
        let sz = self.m.mk_bv(0, fs - 1);
        let one1 = self.m.mk_bv(1, 1);
        let exp_ones = self.m.mk_eq(expf, eo);
        let exp_zero = self.m.mk_eq(expf, ez);
        let sig_zero = self.m.mk_eq(sigf, sz);
        let sig_nz = self.m.mk_not(sig_zero);
        let x_nan = self.m.mk_and(&[exp_ones, sig_nz]);
        let x_inf = self.m.mk_and(&[exp_ones, sig_zero]);
        let x_zero = self.m.mk_and(&[exp_zero, sig_zero]);
        let x_neg = self.m.mk_eq(sbit, one1);
        let x_pos = self.m.mk_not(x_neg);

        let c1 = x_nan;
        let v1 = nan;
        let c2 = self.m.mk_and(&[x_zero, x_pos]);
        let v2 = pzero;
        let c3 = self.m.mk_and(&[x_zero, x_neg]);
        let v3 = nzero;
        let c4 = self.m.mk_and(&[x_inf, x_pos]);
        let v4 = pinf;
        let c5 = self.m.mk_and(&[x_inf, x_neg]);
        let v5 = ninf;

        // Core: unpack, resize significand to to_sb+4, exponent to to_eb+2, round.
        let (sgn, sig, exp, lz) = self.fp_unpack_norm(bvx, fe, fs);
        let res_sgn = sgn;
        let res_sig3 = if fs < to_sb + 3 {
            let pad = self.m.mk_bv(0, to_sb + 3 - fs);
            self.m.mk_bv_concat(sig, pad) // to_sb+3
        } else if fs > to_sb + 3 {
            let high = self.m.mk_bv_extract(fs - 1, fs - to_sb - 2, sig); // to_sb+2
            let low = self.m.mk_bv_extract(fs - to_sb - 3, 0, sig);
            let low_z = self.m.mk_bv(0, fs - to_sb - 2);
            let low_zero = self.m.mk_eq(low, low_z);
            let z1 = self.m.mk_bv(0, 1);
            let sticky = self.m.mk_ite(low_zero, z1, one1);
            self.m.mk_bv_concat(high, sticky) // to_sb+3
        } else {
            sig // to_sb+3
        };
        let res_sig = self.m.mk_bv_zero_extend(1, res_sig3); // to_sb+4
        let res_exp0 = self.m.mk_bv_sign_extend(to_eb - fe + 2, exp); // to_eb+2
        let lz_ext = self.m.mk_bv_zero_extend(to_eb - fe + 2, lz);
        let res_exp = self.m.mk_bvsub(res_exp0, lz_ext);
        let v6 = self.fp_round(rm3, res_sgn, res_sig, res_exp, to_eb, to_sb);

        let r = self.m.mk_ite(c5, v5, v6);
        let r = self.m.mk_ite(c4, v4, r);
        let r = self.m.mk_ite(c3, v3, r);
        let r = self.m.mk_ite(c2, v2, r);
        let result_bv = self.m.mk_ite(c1, v1, r);

        let fps = self.fp_sort(to_eb, to_sb);
        let result = self.fresh_const(fps);
        self.fp_bv.insert(result, result_bv);
        Some(result)
    }

    /// Bit-blast `fp.roundToIntegral` on a symbolic operand (port of z3's
    /// `mk_round_to_integral`). The rounding mode is a constant, so its many
    /// per-mode branches collapse at build time. `None` for unsupported bits.
    fn fp_r2i_bv(&mut self, rm: AstId, x: AstId) -> Option<AstId> {
        let (eb, sb) = self.fp_format_of(self.m.get_sort(x))?;
        if eb < 2 || sb < 3 || eb > sb {
            return None;
        }
        let rm_c = self.rm_code(rm)?;
        let (rte, rta, rtp, rtn, rtz) = (rm_c == 0, rm_c == 1, rm_c == 2, rm_c == 3, rm_c == 4);
        let w = eb + sb;
        let bvx = self.fp_to_bv(x)?;
        let mant = sb - 1;
        let exp_ones_v = ((1u64 << eb) - 1) << mant;
        let bias = (1u64 << (eb - 1)) - 1;
        let nan = self.fp_lit(exp_ones_v | (1u64 << (mant - 1)), w);
        let pzero = self.fp_lit(0, w);
        let nzero = self.fp_lit(1u64 << (w - 1), w);
        let pone = self.fp_lit(bias << mant, w); // +1.0
        let none = self.fp_lit((1u64 << (w - 1)) | (bias << mant), w); // -1.0

        // Classification.
        let expf = self.m.mk_bv_extract(w - 2, sb - 1, bvx);
        let sigf = self.m.mk_bv_extract(sb - 2, 0, bvx);
        let sbit = self.m.mk_bv_extract(w - 1, w - 1, bvx);
        let ez = self.m.mk_bv(0, eb);
        let eo = self.m.mk_bvnot(ez);
        let sz = self.m.mk_bv(0, sb - 1);
        let one1 = self.m.mk_bv(1, 1);
        let exp_ones = self.m.mk_eq(expf, eo);
        let exp_zero = self.m.mk_eq(expf, ez);
        let sig_zero = self.m.mk_eq(sigf, sz);
        let sig_nz = self.m.mk_not(sig_zero);
        let x_nan = self.m.mk_and(&[exp_ones, sig_nz]);
        let x_inf = self.m.mk_and(&[exp_ones, sig_zero]);
        let x_zero = self.m.mk_and(&[exp_zero, sig_zero]);
        let x_denormal = self.m.mk_and(&[exp_zero, sig_nz]);
        let x_neg = self.m.mk_eq(sbit, one1);

        // c1 NaN→NaN, c2 ±∞→x, c3 ±0→x.
        let c1 = x_nan;
        let v1 = nan;
        let c2 = x_inf;
        let v2 = bvx;
        let c3 = x_zero;
        let v3 = bvx;

        let (a_sgn, a_sig, a_exp, _a_lz) = self.fp_unpack_norm(bvx, eb, sb);
        let sgn_eq_1 = self.m.mk_eq(a_sgn, one1);
        let xzero = self.m.mk_ite(sgn_eq_1, nzero, pzero);
        let xone = self.m.mk_ite(sgn_eq_1, none, pone);

        // c4: |x| < 1 (exp < 0 or denormal).
        let exp_h = self.m.mk_bv_extract(eb - 1, eb - 1, a_exp);
        let exp_lt_zero = self.m.mk_eq(exp_h, one1);
        let c4 = self.m.mk_or(&[exp_lt_zero, x_denormal]);
        // tie: |x| == 0.5  (a_sig == 2^(sb-1) ∧ a_exp == -1).
        let pow_sm1 = self.m.mk_bv(1i64 << (sb - 1), sb);
        let t1 = self.m.mk_eq(a_sig, pow_sm1);
        let neg1_e = self.fp_ilit(-1, eb);
        let t2 = self.m.mk_eq(a_exp, neg1_e);
        let tie = self.m.mk_and(&[t1, t2]);
        let neg2_e = self.fp_ilit(-2, eb);
        let c423 = self.m.mk_bvsle(a_exp, neg2_e); // |x| < 0.5
        // v42 (round-to-nearest family): tie handling.
        let v42 = if rte {
            // tie → xzero (round half to even = 0); |x|<0.5 → xzero; else xone.
            let below = self.m.mk_or(&[tie, c423]);
            self.m.mk_ite(below, xzero, xone)
        } else if rta {
            // tie → xone (away); |x|<0.5 → xzero; else xone.
            self.m.mk_ite(c423, xzero, xone)
        } else {
            // rtz path uses xzero below; this branch only reached for rte/rta.
            xone
        };
        let v4 = if rtp {
            self.m.mk_ite(x_neg, nzero, pone)
        } else if rtn {
            self.m.mk_ite(x_neg, none, pzero)
        } else if rtz {
            xzero
        } else {
            v42
        };

        // c5: exp ≥ sbits-1 ⇒ already integral ⇒ x.
        let c5 = if (32 - (sb - 1).leading_zeros()) < eb {
            let big = self.fp_ilit((sb - 1) as i64, eb);
            self.m.mk_bvsle(big, a_exp)
        } else {
            self.m.mk_false()
        };
        let v5 = bvx;

        // v6: general case 0 ≤ exp < sbits-1 — shift out the fractional bits,
        // round the integer part per the (constant) mode, renormalise, pack.
        let res_sgn = a_sgn;
        let zero_s = self.m.mk_bv(0, sb);
        let sm1 = self.m.mk_bv((sb - 1) as i64, sb);
        let aexp_ext = self.m.mk_bv_sign_extend(sb - eb, a_exp); // sb bits
        let shift = self.m.mk_bvsub(sm1, aexp_ext); // sb
        let sig_cat = self.m.mk_bv_concat(a_sig, zero_s); // 2*sb
        let shift_ext = self.m.mk_bv_concat(zero_s, shift); // 2*sb
        let shifted_sig = self.m.mk_bvlshr(sig_cat, shift_ext); // 2*sb
        let divp = self.m.mk_bv_extract(2 * sb - 1, sb, shifted_sig); // sb
        let remp = self.m.mk_bv_extract(sb - 1, 0, shifted_sig); // sb
        let one_s = self.m.mk_bv(1, sb);
        let div_p1 = self.m.mk_bvadd(divp, one_s);
        let zero1 = self.m.mk_bv(0, 1);
        let res_sig = if rte || rta {
            // half-way pattern 100..0.
            let tie_z = self.m.mk_bv(0, sb - 1);
            let tie_pat = self.m.mk_bv_concat(one1, tie_z); // sb
            let tie2 = self.m.mk_eq(remp, tie_pat);
            let div_last = self.m.mk_bv_extract(0, 0, divp);
            let dl1 = self.m.mk_eq(div_last, one1);
            let tie_up = if rta {
                self.m.mk_true()
            } else {
                dl1 // rte: round half to even
            };
            let gt_half = self.m.mk_bvule(tie_pat, remp);
            let cond = self.m.mk_ite(tie2, tie_up, gt_half);
            self.m.mk_ite(cond, div_p1, divp)
        } else if rtp {
            let rem_z = self.m.mk_bv(0, sb);
            let rem_eq0 = self.m.mk_eq(remp, rem_z);
            let rem_nz = self.m.mk_not(rem_eq0);
            let pos = self.m.mk_eq(res_sgn, zero1);
            let up = self.m.mk_and(&[rem_nz, pos]);
            self.m.mk_ite(up, div_p1, divp)
        } else if rtn {
            let rem_z = self.m.mk_bv(0, sb);
            let rem_eq0 = self.m.mk_eq(remp, rem_z);
            let rem_nz = self.m.mk_not(rem_eq0);
            let negc = self.m.mk_eq(res_sgn, one1);
            let up = self.m.mk_and(&[rem_nz, negc]);
            self.m.mk_ite(up, div_p1, divp)
        } else {
            divp // rtz: truncate
        };

        // res_exp = zext(2, a_exp) + e_shift, then renormalise + bias.
        let e_shift = if eb + 2 <= sb + 1 {
            self.m.mk_bv_extract(eb + 1, 0, shift)
        } else {
            self.m.mk_bv_sign_extend((eb + 2) - sb, shift)
        }; // eb+2
        let res_exp0 = self.m.mk_bv_zero_extend(2, a_exp); // eb+2
        let res_exp1 = self.m.mk_bvadd(res_exp0, e_shift); // eb+2
        // Renormalise.
        let min_exp = self.fp_ilit(2 - (1i64 << (eb - 1)), eb);
        let min_exp = self.m.mk_bv_sign_extend(2, min_exp); // eb+2
        let sig_lz = self.fp_leading_zeros(res_sig, eb + 2); // eb+2
        let max_delta = self.m.mk_bvsub(res_exp1, min_exp);
        let lz_le = self.m.mk_bvule(sig_lz, max_delta);
        let sig_lz_capped = self.m.mk_ite(lz_le, sig_lz, max_delta);
        let zero_e2 = self.m.mk_bv(0, eb + 2);
        let ge0 = self.m.mk_bvule(zero_e2, sig_lz_capped);
        let renorm = self.m.mk_ite(ge0, sig_lz_capped, zero_e2);
        let res_exp2 = self.m.mk_bvsub(res_exp1, renorm);
        let res_sig_shifted = if sb >= eb + 2 {
            let rd = self.m.mk_bv_zero_extend(sb - eb - 2, renorm);
            self.m.mk_bvshl(res_sig, rd)
        } else {
            let rs = self.m.mk_bv_zero_extend(eb + 2 - sb, res_sig);
            let sh = self.m.mk_bvshl(rs, renorm);
            self.m.mk_bv_extract(sb - 1, 0, sh)
        };
        let res_exp_eb = self.m.mk_bv_extract(eb - 1, 0, res_exp2); // eb
        let res_exp_biased = self.fp_bias(res_exp_eb, eb);
        let res_mant = self.m.mk_bv_extract(sb - 2, 0, res_sig_shifted); // sb-1
        let hi = self.m.mk_bv_concat(res_sgn, res_exp_biased); // 1+eb
        let v6 = self.m.mk_bv_concat(hi, res_mant); // w

        // Tie together (lower index wins).
        let r = self.m.mk_ite(c5, v5, v6);
        let r = self.m.mk_ite(c4, v4, r);
        let r = self.m.mk_ite(c3, v3, r);
        let r = self.m.mk_ite(c2, v2, r);
        let result_bv = self.m.mk_ite(c1, v1, r);

        let fps = self.fp_sort(eb, sb);
        let result = self.fresh_const(fps);
        self.fp_bv.insert(result, result_bv);
        Some(result)
    }

    /// Build/fold a floating-point operation. Only `Float64` operands with the
    /// `RNE` rounding mode fold (via `f64`); anything else is a sound `unknown`.
    fn fp_op(&mut self, op: &str, args: &[AstId]) -> Result<AstId, String> {
        // fp.* ops take a rounding-mode first argument for the rounding ops.
        let rne = |ctx: &Self, a: AstId| {
            ctx.rm_name(a)
                .as_deref()
                .is_some_and(|n| n == "RNE" || n == "roundNearestTiesToEven")
        };
        let f64_bits = |v: f64| v.to_bits();
        match op {
            "fp.add" | "fp.sub" | "fp.mul" | "fp.div" if args.len() == 3 => {
                if let (true, Some(a), Some(b)) =
                    (rne(self, args[0]), self.fp64(args[1]), self.fp64(args[2]))
                {
                    let r = match op {
                        "fp.add" => a + b,
                        "fp.sub" => a - b,
                        "fp.mul" => a * b,
                        _ => a / b,
                    };
                    return Ok(self.mk_fp(f64_bits(r), 11, 53));
                }
                // Bit-exact symbolic add/sub/mul, bit-blasted to QF_BV (all
                // formats, all constant rounding modes). div / symbolic rm gate.
                if (op == "fp.add" || op == "fp.sub")
                    && let Some(t) = self.fp_add_bv(op, args[0], args[1], args[2])
                {
                    return Ok(t);
                }
                if op == "fp.mul"
                    && let Some(t) = self.fp_mul_bv(args[0], args[1], args[2])
                {
                    return Ok(t);
                }
                if op == "fp.div"
                    && let Some(t) = self.fp_div_bv(args[0], args[1], args[2])
                {
                    return Ok(t);
                }
                self.symbolic_fp(op, args)
            }
            "fp.sqrt" if args.len() == 2 => {
                // No `f64::sqrt` under no_std; the bit-blast circuit decides
                // concrete operands too (via the QF_BV engine).
                if let Some(t) = self.fp_sqrt_bv(args[0], args[1]) {
                    return Ok(t);
                }
                self.symbolic_fp(op, args)
            }
            "fp.roundToIntegral" if args.len() == 2 => {
                if let Some(t) = self.fp_r2i_bv(args[0], args[1]) {
                    return Ok(t);
                }
                self.symbolic_fp(op, args)
            }
            "fp.fma" if args.len() == 4 => {
                if let Some(t) = self.fp_fma_bv(args[0], args[1], args[2], args[3]) {
                    return Ok(t);
                }
                self.symbolic_fp(op, args)
            }
            "fp.abs" | "fp.neg" if args.len() == 1 => {
                if let Some(a) = self.fp64(args[0]) {
                    let bits = a.to_bits();
                    let r = if op == "fp.abs" {
                        bits & !(1u64 << 63)
                    } else {
                        bits ^ (1u64 << 63)
                    };
                    return Ok(self.mk_fp(r, 11, 53));
                }
                // Symbolic: `abs` clears the sign bit, `neg` flips it — pure BV ops
                // (no arithmetic circuit). The result is a fresh FP term whose
                // bit-vector is the modified input, so classification/comparison of
                // it is decided by the QF_BV engine.
                if let Some((eb, sb)) = self.fp_format_of(self.m.get_sort(args[0]))
                    && let Some(bv) = self.fp_to_bv(args[0])
                {
                    let w = eb + sb;
                    let one_bit = self.m.mk_bv(1, 1);
                    let zeros = self.m.mk_bv(0, w - 1);
                    let msb = self.m.mk_bv_concat(one_bit, zeros); // 1 :: 0^{w-1}
                    let result_bv = if op == "fp.abs" {
                        let notmsb = self.m.mk_bvnot(msb);
                        self.m.mk_bvand(bv, notmsb)
                    } else {
                        self.m.mk_bvxor(bv, msb)
                    };
                    let fps = self.fp_sort(eb, sb);
                    let result = self.fresh_const(fps);
                    self.fp_bv.insert(result, result_bv);
                    return Ok(result);
                }
                self.symbolic_fp(op, args)
            }
            "fp.to_real" if args.len() == 1 => {
                // Exact real value of a finite Float64 constant as a dyadic
                // rational `mant · 2^p`, decomposed from the IEEE-754 bits.
                if let Some(a) = self.fp64(args[0])
                    && a.is_finite()
                {
                    let bits = a.to_bits();
                    let s = (bits >> 63) & 1;
                    let e = ((bits >> 52) & 0x7ff) as i32;
                    let m = (bits & 0x000f_ffff_ffff_ffff) as i64;
                    let (mant, p) = if e == 0 {
                        (m, -1074i32) // subnormal / zero
                    } else {
                        (m | (1i64 << 52), e - 1075) // normal (hidden bit)
                    };
                    let val = Rational::from_integer(puremp::Int::from(mant))
                        .mul(&Rational::power_of_two(p));
                    let val = if s == 1 { val.neg() } else { val };
                    return Ok(self.m.mk_numeral(val, false));
                }
                self.symbolic_fp(op, args)
            }
            "fp.min" | "fp.max" if args.len() == 2 => {
                if let (Some(a), Some(b)) = (self.fp64(args[0]), self.fp64(args[1])) {
                    let r = if op == "fp.min" { a.min(b) } else { a.max(b) };
                    return Ok(self.mk_fp(f64_bits(r), 11, 53));
                }
                if let Some(t) = self.fp_min_max_bv(op, args[0], args[1]) {
                    return Ok(t);
                }
                self.symbolic_fp(op, args)
            }
            "fp.eq" | "fp.lt" | "fp.leq" | "fp.gt" | "fp.geq" if args.len() == 2 => {
                if let (Some(a), Some(b)) = (self.fp64(args[0]), self.fp64(args[1])) {
                    let r = match op {
                        "fp.eq" => a == b,
                        "fp.lt" => a < b,
                        "fp.leq" => a <= b,
                        "fp.gt" => a > b,
                        _ => a >= b,
                    };
                    return Ok(self.mk_bool(r));
                }
                // Bit-blast the comparison: `fp.eq` via equality + zero handling,
                // the ordered comparisons via the direct sign+magnitude circuit
                // (`fp_compare_bv`) — all decided by the QF_BV engine.
                if let Some(t) = self.fp_compare_bv(op, args[0], args[1]) {
                    return Ok(t);
                }
                self.symbolic_fp(op, args)
            }
            "fp.isNaN" | "fp.isInfinite" | "fp.isZero" | "fp.isNormal" | "fp.isSubnormal"
            | "fp.isNegative" | "fp.isPositive"
                if args.len() == 1 =>
            {
                if let Some(a) = self.fp64(args[0]) {
                    let r = match op {
                        "fp.isNaN" => a.is_nan(),
                        "fp.isInfinite" => a.is_infinite(),
                        "fp.isZero" => a == 0.0,
                        "fp.isNormal" => a.is_normal(),
                        "fp.isSubnormal" => {
                            a != 0.0 && !a.is_normal() && !a.is_nan() && a.is_finite()
                        }
                        "fp.isNegative" => a.is_sign_negative() && !a.is_nan(),
                        _ => a.is_sign_positive() && !a.is_nan(),
                    };
                    return Ok(self.mk_bool(r));
                }
                // Symbolic: bit-blast the classification through QF_BV.
                if let Some(t) = self.fp_classify_bv(op, args[0]) {
                    return Ok(t);
                }
                self.symbolic_fp(op, args)
            }
            _ => self.symbolic_fp(op, args),
        }
    }

    /// The `RoundingMode` constant name of `t`, if it is one.
    fn rm_name(&self, t: AstId) -> Option<String> {
        let d = self.m.app_decl(t);
        let name = self.m.func_decl(d)?.name.as_str()?;
        matches!(
            name,
            "RNE" | "RNA" | "RTP" | "RTN" | "RTZ" | "roundNearestTiesToEven"
        )
        .then(|| name.to_string())
    }

    fn mk_bool(&mut self, b: bool) -> AstId {
        if b {
            self.m.mk_true()
        } else {
            self.m.mk_false()
        }
    }

    /// A fresh uninterpreted term for a symbolic FP operation, gated to `unknown`.
    fn symbolic_fp(&mut self, op: &str, args: &[AstId]) -> Result<AstId, String> {
        let sort = match op {
            "fp.eq" | "fp.lt" | "fp.leq" | "fp.gt" | "fp.geq" | "fp.isNaN" | "fp.isInfinite"
            | "fp.isZero" | "fp.isNormal" | "fp.isSubnormal" | "fp.isNegative"
            | "fp.isPositive" => self.m.mk_bool_sort(),
            // Rounding ops carry an RM first arg; the result is like the last FP arg.
            _ => self.m.get_sort(*args.last().unwrap()),
        };
        let domain: Vec<AstId> = args.iter().map(|&a| self.m.get_sort(a)).collect();
        let name = alloc::format!("!fpop!{}!{}", op, self.fresh_counter);
        self.fresh_counter += 1;
        let d = self.m.mk_func_decl(Symbol::new(&name), &domain, sort);
        let app = self.m.mk_app(d, args);
        self.str_symbolic.insert(app);
        Ok(app)
    }

    /// The `(Seq E)` sort for element sort `e` (interned per element sort).
    fn seq_sort(&mut self, e: AstId) -> AstId {
        if let Some(&s) = self.seq_sorts.get(&e) {
            return s;
        }
        let name = alloc::format!("Seq!{}", self.seq_sorts.len());
        let s = self.m.mk_uninterpreted_sort(Symbol::new(&name));
        self.seq_sorts.insert(e, s);
        s
    }

    /// Build a sequence-theory term. Structural operations on sequences with a
    /// known element list (`seq.unit`/`++`/`empty`) fold exactly; a symbolic
    /// sequence operation is marked so the goal is answered `unknown`.
    fn seq_op(&mut self, op: &str, args: &[AstId]) -> Result<AstId, String> {
        // Known element list of each argument (if all are structural sequences).
        let lists: Option<Vec<Vec<AstId>>> =
            args.iter().map(|a| self.seq_of.get(a).cloned()).collect();
        match op {
            "seq.unit" => {
                let elem = self.m.get_sort(args[0]);
                let sort = self.seq_sort(elem);
                let t = self.fresh_const(sort);
                self.seq_of.insert(t, alloc::vec![args[0]]);
                Ok(t)
            }
            "seq.++" => {
                if let Some(parts) = lists {
                    let joined: Vec<AstId> = parts.into_iter().flatten().collect();
                    return Ok(self.mk_seq(joined));
                }
                self.symbolic_seq(op, args)
            }
            "seq.len" => {
                if let Some(l) = self.seq_of.get(&args[0]) {
                    return Ok(self.m.mk_int(l.len() as i64));
                }
                // Symbolic sequence length: a genuine Int-valued function (like
                // str.len), carrying a non-negativity axiom (see string_axioms).
                let d = self.seq_len_decl_for(self.m.get_sort(args[0]));
                Ok(self.m.mk_app(d, &[args[0]]))
            }
            "seq.nth" => {
                if let (Some(l), Some(i)) =
                    (self.seq_of.get(&args[0]).cloned(), self.int_arg(args[1]))
                    && i >= 0
                    && (i as usize) < l.len()
                {
                    return Ok(l[i as usize]);
                }
                self.symbolic_seq(op, args)
            }
            "seq.at" => {
                if let (Some(l), Some(i)) =
                    (self.seq_of.get(&args[0]).cloned(), self.int_arg(args[1]))
                {
                    let out = if i >= 0 && (i as usize) < l.len() {
                        alloc::vec![l[i as usize]]
                    } else {
                        Vec::new()
                    };
                    return Ok(self.mk_seq(out));
                }
                self.symbolic_seq(op, args)
            }
            "seq.extract" => {
                if let (Some(l), Some(i), Some(n)) = (
                    self.seq_of.get(&args[0]).cloned(),
                    self.int_arg(args[1]),
                    self.int_arg(args[2]),
                ) && i >= 0
                    && n >= 0
                    && (i as usize) <= l.len()
                {
                    let start = i as usize;
                    let end = (start + n as usize).min(l.len());
                    return Ok(self.mk_seq(l[start..end].to_vec()));
                }
                self.symbolic_seq(op, args)
            }
            "seq.contains" | "seq.prefixof" | "seq.suffixof" => {
                if let Some(ps) = &lists {
                    // seq.prefixof/suffixof: (sub, whole); seq.contains: (whole, sub).
                    let (whole, sub) = if op == "seq.contains" {
                        (ps[0].clone(), ps[1].clone())
                    } else {
                        (ps[1].clone(), ps[0].clone())
                    };
                    // Candidate start positions where `sub` could sit in `whole`.
                    let positions: Vec<usize> = if sub.len() > whole.len() {
                        Vec::new()
                    } else {
                        match op {
                            "seq.prefixof" => alloc::vec![0],
                            "seq.suffixof" => alloc::vec![whole.len() - sub.len()],
                            _ => (0..=whole.len() - sub.len()).collect(),
                        }
                    };
                    // A match at `p` is the conjunction of element equalities
                    // `whole[p+k] = sub[k]` — which folds for concrete elements and
                    // stays symbolic (e.g. `a=b`) for variables, rather than being
                    // wrongly decided by syntactic AstId comparison.
                    let mut disj = Vec::new();
                    for p in positions {
                        let mut conj = Vec::new();
                        for k in 0..sub.len() {
                            let e = self.m.mk_eq(whole[p + k], sub[k]);
                            conj.push(e);
                        }
                        let c = match conj.len() {
                            0 => self.m.mk_true(),
                            1 => conj[0],
                            _ => self.m.mk_and(&conj),
                        };
                        disj.push(c);
                    }
                    return Ok(match disj.len() {
                        0 => self.m.mk_false(),
                        1 => disj[0],
                        _ => self.m.mk_or(&disj),
                    });
                }
                self.symbolic_seq(op, args)
            }
            "seq.indexof" => {
                // The optional third argument is an Int offset, not a sequence,
                // so fetch the two sequence operands directly.
                let off = if args.len() > 2 {
                    self.int_arg(args[2])
                } else {
                    Some(0)
                };
                if let (Some(whole), Some(sub), Some(o)) = (
                    self.seq_of.get(&args[0]).cloned(),
                    self.seq_of.get(&args[1]).cloned(),
                    off,
                ) && o >= 0
                {
                    let idx = find_sub(&whole, &sub, o as usize)
                        .map(|p| p as i64)
                        .unwrap_or(-1);
                    return Ok(self.m.mk_int(idx));
                }
                self.symbolic_seq(op, args)
            }
            // seq.replace (first occurrence) folds; seq.replace_all is not part
            // of z3's SMT2 surface (uninterpreted there), so it stays `unknown`
            // to avoid contradicting the oracle.
            "seq.replace" => {
                if let Some(ps) = &lists {
                    return Ok(self.mk_seq(replace_first_seq(&ps[0], &ps[1], &ps[2])));
                }
                self.symbolic_seq(op, args)
            }
            _ => self.symbolic_string(op, args),
        }
    }

    /// The element sort of a `(Seq E)` sort, if known.
    fn seq_elem_sort(&self, seq_sort: AstId) -> Option<AstId> {
        self.seq_sorts
            .iter()
            .find(|(_, s)| **s == seq_sort)
            .map(|(&e, _)| e)
    }

    /// A fresh uninterpreted term for a symbolic sequence operation, with the
    /// correct result sort, recorded so the goal is answered `unknown`.
    fn symbolic_seq(&mut self, op: &str, args: &[AstId]) -> Result<AstId, String> {
        let sort = match op {
            "seq.len" | "seq.indexof" => self.m.mk_int_sort(),
            "seq.contains" | "seq.prefixof" | "seq.suffixof" => self.m.mk_bool_sort(),
            "seq.nth" => self
                .seq_elem_sort(self.m.get_sort(args[0]))
                .unwrap_or_else(|| self.m.mk_int_sort()),
            // seq.++/at/extract and the rest return a sequence like args[0].
            _ => self.m.get_sort(args[0]),
        };
        let domain: Vec<AstId> = args.iter().map(|&a| self.m.get_sort(a)).collect();
        let name = alloc::format!("!seqop!{}!{}", op, self.fresh_counter);
        self.fresh_counter += 1;
        let d = self.m.mk_func_decl(Symbol::new(&name), &domain, sort);
        let app = self.m.mk_app(d, args);
        self.str_symbolic.insert(app);
        if op == "seq.++" {
            self.seq_concat.push((app, args.to_vec()));
        }
        self.seqop_ops.insert(d, op.to_string());
        Ok(app)
    }

    /// A fresh sequence constant with the given element list recorded.
    fn mk_seq(&mut self, elems: Vec<AstId>) -> AstId {
        let elem_sort = elems
            .first()
            .map(|&e| self.m.get_sort(e))
            .unwrap_or_else(|| self.m.mk_int_sort());
        let sort = self.seq_sort(elem_sort);
        let t = self.fresh_const(sort);
        self.seq_of.insert(t, elems);
        t
    }

    /// The interned `RegLan` sort (registered on first use).
    fn reglan_sort(&mut self) -> AstId {
        if let Some(s) = self.reglan_sort {
            return s;
        }
        let s = self.m.mk_uninterpreted_sort(Symbol::new("RegLan"));
        self.reglan_sort = Some(s);
        self.sorts.insert("RegLan".to_string(), s);
        s
    }

    /// Build a regex term. Every result is a fresh `RegLan` constant; when all
    /// of its parts are constant regexes, its [`Regex`] structure is recorded in
    /// `regex_of` (enabling `str.in_re` folding).
    fn regex_op(&mut self, op: &str, args: &[AstId]) -> Result<AstId, String> {
        // Sub-regex structures, if every argument is a tracked constant regex.
        let subs: Option<Vec<Regex>> = args.iter().map(|a| self.regex_of.get(a).cloned()).collect();
        let structure: Option<Regex> = match op {
            "str.to_re" | "str.to.re" => self.str_value(args[0]).map(Regex::Lit),
            "re.range" => match (self.str_value(args[0]), self.str_value(args[1])) {
                (Some(a), Some(b)) if a.len() == 1 && b.len() == 1 => {
                    Some(Regex::Range(a[0], b[0]))
                }
                _ => None,
            },
            "re.none" | "re.empty" => Some(Regex::None),
            "re.all" => Some(Regex::All),
            "re.allchar" => Some(Regex::AllChar),
            "re.++" => subs.map(|s| fold_regex(s, |a, b| Regex::Concat(Box::new(a), Box::new(b)))),
            "re.union" => {
                subs.map(|s| fold_regex(s, |a, b| Regex::Union(Box::new(a), Box::new(b))))
            }
            "re.inter" => {
                subs.map(|s| fold_regex(s, |a, b| Regex::Inter(Box::new(a), Box::new(b))))
            }
            "re.*" => subs.map(|s| Regex::Star(Box::new(s.into_iter().next().unwrap()))),
            "re.+" => subs.map(|s| {
                let r = s.into_iter().next().unwrap();
                Regex::Concat(Box::new(r.clone()), Box::new(Regex::Star(Box::new(r))))
            }),
            "re.opt" => subs.map(|s| {
                Regex::Union(
                    Box::new(s.into_iter().next().unwrap()),
                    Box::new(Regex::Lit(Vec::new())),
                )
            }),
            "re.comp" => subs.map(|s| Regex::Comp(Box::new(s.into_iter().next().unwrap()))),
            "re.diff" => subs.map(|s| {
                // a \ b = a ∩ comp(b).
                let mut it = s.into_iter();
                let a = it.next().unwrap();
                let b = it.next().unwrap();
                Regex::Inter(Box::new(a), Box::new(Regex::Comp(Box::new(b))))
            }),
            _ => None,
        };
        let sort = self.reglan_sort();
        let name = alloc::format!("!re!{}", self.fresh_counter);
        self.fresh_counter += 1;
        let d = self.m.mk_func_decl(Symbol::new(&name), &[], sort);
        let term = self.m.mk_const(d);
        if let Some(r) = structure {
            self.regex_of.insert(term, r);
        }
        Ok(term)
    }

    /// A fresh uninterpreted term standing for a symbolic string operation,
    /// recorded so the goal is answered `unknown`.
    fn symbolic_string(&mut self, op: &str, args: &[AstId]) -> Result<AstId, String> {
        // Result sort: Bool for predicates, Int for indexof/to_int, else String.
        let sort = match op {
            "str.contains" | "str.prefixof" | "str.suffixof" | "str.is_digit" | "str.<"
            | "str.<=" | "str.in_re" | "str.in.re" => self.m.mk_bool_sort(),
            "str.indexof" | "str.to_int" | "str.to-int" | "str.to_code" | "str.to-code" => {
                self.m.mk_int_sort()
            }
            _ => self.string_sort(),
        };
        let domain: Vec<AstId> = args.iter().map(|&a| self.m.get_sort(a)).collect();
        let name = alloc::format!("!strop!{}!{}", op, self.fresh_counter);
        self.fresh_counter += 1;
        let d = self.m.mk_func_decl(Symbol::new(&name), &domain, sort);
        let app = self.m.mk_app(d, args);
        self.str_symbolic.insert(app);
        self.str_op_decls.insert(d, op.to_string());
        // Record a length link so `pred ⇒ len(longer) ≥ len(shorter)` can be
        // emitted (sound for contains/prefixof/suffixof).
        match op {
            "str.contains" if args.len() == 2 => {
                self.str_pred_len.push((app, args[0], args[1]));
            }
            "str.prefixof" | "str.suffixof" if args.len() == 2 => {
                self.str_pred_len.push((app, args[1], args[0]));
            }
            // `str.at` returns a string of length ≤ 1 — a sound bound that refutes
            // e.g. `(str.at x 0) = "xyz"` directly.
            "str.at" => self.str_len_ub.push((app, 1)),
            _ => {}
        }
        Ok(app)
    }

    /// Fold a string-producing op over literal arguments (`str_vals` the code
    /// points of each argument if all literals), returning the result string.
    fn fold_string_producer(&self, op: &str, raw: &[AstId]) -> Option<String> {
        match op {
            "str.at" => {
                let s = self.str_value(raw[0])?;
                let i = self.int_arg(raw[1])?;
                Some(if i >= 0 && (i as usize) < s.len() {
                    code_points_to_string(&[s[i as usize]])
                } else {
                    String::new()
                })
            }
            "str.substr" => {
                let s = self.str_value(raw[0])?;
                let (i, n) = (self.int_arg(raw[1])?, self.int_arg(raw[2])?);
                if i < 0 || n < 0 || (i as usize) > s.len() {
                    return Some(String::new());
                }
                let start = i as usize;
                let end = (start + n as usize).min(s.len());
                Some(code_points_to_string(&s[start..end]))
            }
            "str.replace" => {
                let (s, from, to) = (
                    self.str_value(raw[0])?,
                    self.str_value(raw[1])?,
                    self.str_value(raw[2])?,
                );
                Some(replace_first(&s, &from, &to))
            }
            "str.from_int" | "str.from-int" => {
                let n = self.int_arg(raw[0])?;
                Some(if n < 0 {
                    String::new()
                } else {
                    alloc::format!("{n}")
                })
            }
            _ => None,
        }
    }

    /// The integer value of `t` if it is an integer numeral.
    fn int_arg(&self, t: AstId) -> Option<i64> {
        self.m.as_numeral(t)?.to_integer()?.to_i64()
    }

    /// Fold a string→int op (`str.to_int`, `str.indexof`, `str.to_code`).
    fn fold_string_to_int(&self, op: &str, raw: &[AstId]) -> Option<i64> {
        match op {
            "str.to_code" | "str.to-code" => {
                let s = self.str_value(raw[0])?;
                // The code point of a single-character string, else -1.
                Some(if s.len() == 1 { s[0] as i64 } else { -1 })
            }
            "str.to_int" | "str.to-int" => {
                let s = self.str_value(raw[0])?;
                // A non-empty run of ASCII digits is its value; otherwise -1.
                if !s.is_empty() && s.iter().all(|&c| (0x30..=0x39).contains(&c)) {
                    let mut n: i64 = 0;
                    for &c in &s {
                        n = n.checked_mul(10)?.checked_add((c - 0x30) as i64)?;
                    }
                    Some(n)
                } else {
                    Some(-1)
                }
            }
            "str.indexof" => {
                let s = self.str_value(raw[0])?;
                let sub = self.str_value(raw[1])?;
                let off = if raw.len() > 2 {
                    self.int_arg(raw[2])?
                } else {
                    0
                };
                if off < 0 || off as usize > s.len() {
                    return Some(-1);
                }
                let start = off as usize;
                if sub.is_empty() {
                    return Some(start as i64);
                }
                // No room for `sub` at or after `start` ⇒ not found (guards the
                // slice below against `s` shorter than `sub`).
                if start + sub.len() > s.len() {
                    return Some(-1);
                }
                for i in start..=s.len() - sub.len() {
                    if s[i..i + sub.len()] == sub[..] {
                        return Some(i as i64);
                    }
                }
                Some(-1)
            }
            _ => None,
        }
    }

    /// A fresh 0-ary constant of the given sort (for term lifting).
    fn fresh_const(&mut self, sort: AstId) -> AstId {
        let name = alloc::format!("!k!{}", self.fresh_counter);
        self.fresh_counter += 1;
        let d = self.m.mk_func_decl(Symbol::new(&name), &[], sort);
        self.m.mk_const(d)
    }

    /// Lift term-level `ite`s and constant-divisor `div`/`mod` out of `base`,
    /// conjoining their defining constraints, so the theory solvers can reason
    /// about them.
    fn lift(&mut self, base: AstId) -> AstId {
        let mut ctx = LiftCtx {
            defs: Vec::new(),
            cache: BTreeMap::new(),
            dm: BTreeMap::new(),
            toint: BTreeMap::new(),
        };
        let lifted = self.lift_terms(base, &mut ctx);
        if ctx.defs.is_empty() {
            lifted
        } else {
            ctx.defs.push(lifted);
            self.m.mk_and(&ctx.defs)
        }
    }

    /// The conjunction of all assertions (`true` if none), lifted, with the
    /// array read-over-write axioms instantiated.
    /// Decide the current assertion set, instantiating any recorded universals
    /// over the ground terms. A `forall` instance is a consequence of the
    /// universal, so an `unsat` result is sound; but the instantiation is
    /// incomplete, so a `sat` result in the presence of universals is reported
    /// as a sound `unknown`.
    fn check_sat(&mut self) -> (SmtResult, Option<Model>) {
        // A single-predicate Constrained Horn Clause system (a transition system
        // `Init/τ/Bad`) is decided by bounded model checking (for `unsat`, a
        // counterexample trace) and k-induction (for `sat`, an inductive
        // invariant). Both are sound; on the resource bound it declines (`None`)
        // and falls through to the general instantiation engine.
        if !self.universals.is_empty()
            && let Some(r) = self
                .solve_chc()
                .or_else(|| self.solve_chc_acyclic())
                .or_else(|| self.solve_chc_invariant())
                .or_else(|| self.solve_chc_bmc_paths())
                .or_else(|| self.solve_chc_multi())
        {
            return (r, None);
        }
        let (instances, saturated) = self.universal_instances();
        let base = self.conjunction();
        let combined = if instances.is_empty() {
            base
        } else {
            let mut conj = alloc::vec![base];
            conj.extend(instances);
            self.m.mk_and(&conj)
        };
        let lifted = self.lift(combined);
        let goal = self.with_axioms(lifted);
        // The string/seq witness re-derives its own axioms on the concretised
        // goal, so it must start from the pre-axiom formula (substituting into the
        // axiom-laden `goal` leaves partially-folded axiom terms that block a `sat`
        // — the refutation path still uses the full `goal`).
        self.witness_base = Some(lifted);
        let (res, model) = self.decide(goal);
        self.witness_base = None;
        // A `sat` result is complete only if instantiation reached a fixpoint
        // (every ground instance is present — e.g. a finite Datalog domain);
        // otherwise the un-instantiated cases keep it a sound `unknown`.
        if res == SmtResult::Sat && !self.universals.is_empty() && !saturated {
            (SmtResult::Unknown, None)
        } else {
            (res, model)
        }
    }

    /// If `t` is an application of an uninterpreted, `Bool`-ranged function of
    /// arity ≥ 1 (a CHC *predicate*), return its declaration.
    fn predicate_of(&self, t: AstId) -> Option<AstId> {
        let app = self.m.app(t)?;
        if app.args.is_empty() {
            return None;
        }
        let d = self.m.func_decl(app.decl)?;
        // Datatype testers `((_ is C) t)` are Bool-returning user decls too, but
        // they are *interpreted* (fixed by the datatype axioms), not CHC
        // predicates whose relation we solve for — exclude them.
        if self.tester_of.values().any(|&td| td == app.decl) {
            return None;
        }
        if d.info.family_id == crate::ast::NULL_FAMILY_ID && self.m.is_bool_sort(d.range) {
            Some(app.decl)
        } else {
            None
        }
    }

    /// Try to decide the asserted universals as a **single-predicate CHC**
    /// transition system: parse `Init(x)`, `τ(x,x')`, `Bad(x)`, then run bounded
    /// model checking (⇒ `unsat` on a counterexample) and k-induction (⇒ `sat` on
    /// an inductive invariant). Returns `None` (fall back) when the shape is not a
    /// single-predicate CHC or the bound is exhausted.
    fn solve_chc(&mut self) -> Option<SmtResult> {
        // 1. Identify exactly one predicate across all universals.
        let mut preds: BTreeSet<AstId> = BTreeSet::new();
        for (_, body) in &self.universals.clone() {
            for t in self.m.postorder(*body) {
                if let Some(p) = self.predicate_of(t) {
                    preds.insert(p);
                }
            }
        }
        if preds.len() != 1 {
            return None;
        }
        let pred = *preds.iter().next().unwrap();
        // Decline if the predicate is constrained by a *ground* assertion (e.g.
        // `¬p(5)`): the transition-system framing only accounts for the universal
        // rules, so such a constraint would be ignored — let the general
        // instantiation engine handle those goals instead.
        for a in &self.assertions {
            if self
                .m
                .postorder(*a)
                .iter()
                .any(|&t| self.predicate_of(t) == Some(pred))
            {
                return None;
            }
        }
        let sorts: Vec<AstId> = self.m.func_decl(pred)?.domain.clone();

        // Canonical state / next-state variables.
        let state: Vec<AstId> = sorts.iter().map(|&s| self.fresh_const(s)).collect();
        let next: Vec<AstId> = sorts.iter().map(|&s| self.fresh_const(s)).collect();

        // 2. Parse each universal into an Init / Trans / Bad disjunct.
        let mut inits: Vec<AstId> = Vec::new();
        let mut transs: Vec<AstId> = Vec::new();
        let mut bads: Vec<AstId> = Vec::new();
        for (binders, body) in self.universals.clone() {
            let Some((ant, cons)) = self.chc_split_rule(body) else {
                return None; // not an implication/clause we handle
            };
            // Antecedent → (body predicate application if any, arithmetic guard).
            let mut body_pred: Option<AstId> = None;
            let mut guards: Vec<AstId> = Vec::new();
            let mut ant_conj = Vec::new();
            self.icp_flatten_and(ant, &mut ant_conj);
            for a in ant_conj {
                if self.predicate_of(a).is_some() {
                    if body_pred.is_some() {
                        return None; // nonlinear (≥2 body predicates) — out of MVP scope
                    }
                    body_pred = Some(a);
                } else {
                    guards.push(a);
                }
            }
            let _ = binders;
            // Head: a predicate application (fact/rule), `false` (query), or an
            // arithmetic *property* `⇒ prop(x)`. A property head is exactly the
            // query `P(x) ∧ guard ∧ ¬prop(x) ⇒ false`, so fold `¬prop` into the
            // guard and treat it as a query — this handles the common
            // safety-property CHC form `(=> (inv x) (>= x 0))`.
            let head_pred = if self.m.is_false(cons) {
                None
            } else if self.predicate_of(cons).is_some() {
                Some(cons)
            } else {
                let neg = self.m.mk_not(cons);
                guards.push(neg);
                None
            };
            // Map each predicate argument to its state/next variable. A bare,
            // not-yet-seen binder maps directly (`subst`); any other argument
            // (a compound term `P(x+1)`, or a reused binder) instead contributes
            // an equality `var = arg` — z3's own CHC normalisation — so
            // transitions like `inv(x) ⇒ inv(x+1)` are handled.
            let collect = |ctx: &Self,
                           app: AstId,
                           vars: &[AstId],
                           subst: &mut Vec<(AstId, AstId)>,
                           eqs: &mut Vec<(AstId, AstId)>|
             -> bool {
                let args = ctx.m.app_args(app).to_vec();
                if args.len() != vars.len() {
                    return false;
                }
                for (j, &a) in args.iter().enumerate() {
                    if ctx.m.is_uninterp_const(a) && !subst.iter().any(|&(from, _)| from == a) {
                        subst.push((a, vars[j]));
                    } else {
                        eqs.push((vars[j], a));
                    }
                }
                true
            };
            // Build the (substituted) guard for a rule from the shared `guards`
            // plus the per-application equalities.
            let build = |ctx: &mut Self,
                         guards: &[AstId],
                         eqs: &[(AstId, AstId)],
                         subst: &[(AstId, AstId)]|
             -> AstId {
                let mut all: Vec<AstId> = guards.to_vec();
                for &(v, a) in eqs {
                    all.push(ctx.m.mk_eq(v, a));
                }
                let g = if all.is_empty() {
                    ctx.m.mk_true()
                } else if all.len() == 1 {
                    all[0]
                } else {
                    ctx.m.mk_and(&all)
                };
                substitute(&mut ctx.m, g, subst)
            };
            match (body_pred, head_pred) {
                (None, Some(h)) => {
                    // Fact: guard ⇒ P(s).
                    let (mut subst, mut eqs) = (Vec::new(), Vec::new());
                    if !collect(self, h, &state, &mut subst, &mut eqs) {
                        return None;
                    }
                    let d = build(self, &guards, &eqs, &subst);
                    inits.push(d);
                }
                (Some(b), Some(h)) => {
                    // Rule: P(t) ∧ guard ⇒ P(s).
                    let (mut subst, mut eqs) = (Vec::new(), Vec::new());
                    if !collect(self, b, &state, &mut subst, &mut eqs)
                        || !collect(self, h, &next, &mut subst, &mut eqs)
                    {
                        return None;
                    }
                    let d = build(self, &guards, &eqs, &subst);
                    transs.push(d);
                }
                (Some(b), None) => {
                    // Query: P(t) ∧ guard ⇒ false.
                    let (mut subst, mut eqs) = (Vec::new(), Vec::new());
                    if !collect(self, b, &state, &mut subst, &mut eqs) {
                        return None;
                    }
                    let d = build(self, &guards, &eqs, &subst);
                    bads.push(d);
                }
                (None, None) => {
                    // guard ⇒ false: satisfiable iff guard is unsat. If guard is
                    // satisfiable, the system is unsat (a ground contradiction).
                    let guard = build(self, &guards, &[], &[]);
                    let (r, _) = check_model(&self.m, guard);
                    match r {
                        SmtResult::Sat => return Some(SmtResult::Unsat),
                        SmtResult::Unsat => {}
                        SmtResult::Unknown => return None,
                    }
                }
            }
        }
        if bads.is_empty() {
            return Some(SmtResult::Sat); // no query ⇒ trivially safe
        }
        let init = self.mk_disjunction(&inits);
        let trans = self.mk_disjunction(&transs);
        let bad = self.mk_disjunction(&bads);
        // Collect the local (binder) variables to freshen per unrolling step.
        let mut locals: BTreeSet<AstId> = BTreeSet::new();
        for f in [init, trans, bad] {
            for t in self.m.postorder(f) {
                if self.m.is_uninterp_const(t) && !state.contains(&t) && !next.contains(&t) {
                    locals.insert(t);
                }
            }
        }
        let locals: Vec<AstId> = locals.into_iter().collect();
        self.chc_bmc_kinduction(&sorts, &state, &next, init, trans, bad, &locals)
    }

    /// The image formula of a **linear** CHC rule `body_app ∧ guard ⇒ head_app`
    /// over the *previous* reachable sets: fresh-rename the binders, substitute
    /// `reach[body_pred]` at the body arguments, conjoin the guards, and (when a
    /// head is given) pin `state[head_pred] = head arguments`. Binders left free
    /// are existential path variables (the SAT engine picks them).
    fn chc_rule_image(
        &mut self,
        binders: &[AstId],
        body_app: Option<AstId>,
        guard_parts: &[AstId],
        head_app: Option<AstId>,
        reach: &BTreeMap<AstId, AstId>,
        state: &BTreeMap<AstId, Vec<AstId>>,
    ) -> Option<AstId> {
        let fresh: Vec<(AstId, AstId)> = binders
            .iter()
            .map(|&b| (b, self.fresh_const(self.m.get_sort(b))))
            .collect();
        let mut parts: Vec<AstId> = Vec::new();
        if let Some(bapp) = body_app {
            let bp = self.predicate_of(bapp)?;
            let bargs: Vec<AstId> = self.m.app_args(bapp).to_vec();
            let canon = state.get(&bp)?.clone();
            if canon.len() != bargs.len() {
                return None;
            }
            // reach[body] is over the canonical vars; substitute them by the
            // (fresh-renamed) body arguments.
            let sub: Vec<(AstId, AstId)> = canon
                .iter()
                .zip(bargs.iter())
                .map(|(&c, &a)| (c, crate::rewriter::substitute(&mut self.m, a, &fresh)))
                .collect();
            let rb = crate::rewriter::substitute(&mut self.m, reach[&bp], &sub);
            parts.push(rb);
        }
        for &g in guard_parts {
            let gf = crate::rewriter::substitute(&mut self.m, g, &fresh);
            parts.push(gf);
        }
        if let Some(happ) = head_app {
            let hp = self.predicate_of(happ)?;
            let hargs: Vec<AstId> = self.m.app_args(happ).to_vec();
            let canon = state.get(&hp)?.clone();
            if canon.len() != hargs.len() {
                return None;
            }
            for (i, &ha) in hargs.iter().enumerate() {
                let haf = crate::rewriter::substitute(&mut self.m, ha, &fresh);
                let eq = self.m.mk_eq(canon[i], haf);
                parts.push(eq);
            }
        }
        Some(if parts.is_empty() {
            self.m.mk_true()
        } else if parts.len() == 1 {
            parts[0]
        } else {
            self.m.mk_and(&parts)
        })
    }

    /// Multi-predicate **linear** CHC via bounded symbolic forward reachability:
    /// grow each predicate's reachable set `reach[P]` by applying the rules, and
    /// after each round test every query `body ∧ guard ⇒ false`. A satisfiable
    /// query is a genuine counterexample derivation ⇒ **unsat** (the CHC system
    /// is unsafe). Sound in that direction; the safe direction (a fixpoint of the
    /// reach sets) needs model-based projection, so on bound exhaustion it
    /// declines (`None`) and the goal stays a sound `unknown`.
    /// Parse the asserted universals as a **linear multi-predicate** CHC system:
    /// the predicates, their canonical state variables, and each rule as
    /// `(binders, body_app, guards, head_app)` (`head_app = None` ⇒ a query,
    /// property heads already folded into the guards). `None` if not such a system.
    #[allow(clippy::type_complexity)]
    fn chc_parse_multi(
        &mut self,
    ) -> Option<(
        BTreeSet<AstId>,
        BTreeMap<AstId, Vec<AstId>>,
        Vec<(Vec<AstId>, Option<AstId>, Vec<AstId>, Option<AstId>)>,
    )> {
        let mut preds: BTreeSet<AstId> = BTreeSet::new();
        for (_, body) in &self.universals.clone() {
            for t in self.m.postorder(*body) {
                if let Some(p) = self.predicate_of(t) {
                    preds.insert(p);
                }
            }
        }
        if preds.len() < 2 || preds.len() > 8 {
            return None;
        }
        for a in &self.assertions.clone() {
            if self
                .m
                .postorder(*a)
                .iter()
                .any(|&t| self.predicate_of(t).is_some_and(|p| preds.contains(&p)))
            {
                return None;
            }
        }
        let mut state: BTreeMap<AstId, Vec<AstId>> = BTreeMap::new();
        for &p in &preds {
            let sorts = self.m.func_decl(p)?.domain.clone();
            let vars: Vec<AstId> = sorts.iter().map(|&s| self.fresh_const(s)).collect();
            state.insert(p, vars);
        }
        let mut rules = Vec::new();
        for (binders, body) in self.universals.clone() {
            let (ant, cons) = self.chc_split_rule(body)?;
            let mut conj = Vec::new();
            self.icp_flatten_and(ant, &mut conj);
            let mut body_app = None;
            let mut guards = Vec::new();
            for a in conj {
                if self.predicate_of(a).is_some() {
                    if body_app.is_some() {
                        return None; // nonlinear (≥2 body predicates)
                    }
                    body_app = Some(a);
                } else {
                    guards.push(a);
                }
            }
            let head_app = if self.m.is_false(cons) {
                None
            } else if self.predicate_of(cons).is_some() {
                Some(cons)
            } else {
                let neg = self.m.mk_not(cons);
                guards.push(neg);
                None
            };
            rules.push((binders, body_app, guards, head_app));
        }
        Some((preds, state, rules))
    }

    /// Multi-predicate CHC with an **acyclic** predicate-dependency graph: inline
    /// each predicate's reachable set in topological order. With no recursion the
    /// reach sets are *exact* and finite, so a satisfiable query is a genuine
    /// counterexample (**unsat**) and no satisfiable query proves the system safe
    /// (**sat**) — both sound. `None` on a dependency cycle (needs the PDR engine)
    /// or when a query can't be decided.
    fn solve_chc_acyclic(&mut self) -> Option<SmtResult> {
        let (preds, state, rules) = self.chc_parse_multi()?;
        // Dependency edges: a head predicate depends on its rule's body predicate.
        let mut deps: BTreeMap<AstId, BTreeSet<AstId>> =
            preds.iter().map(|&p| (p, BTreeSet::new())).collect();
        for (_, body_app, _, head_app) in &rules {
            if let (Some(happ), Some(bapp)) = (head_app, body_app) {
                let hp = self.predicate_of(*happ)?;
                let bp = self.predicate_of(*bapp)?;
                deps.get_mut(&hp)?.insert(bp);
            }
        }
        // Topological order (Kahn) — bail on any cycle (recursion).
        let mut order: Vec<AstId> = Vec::new();
        let mut remaining: BTreeSet<AstId> = preds.clone();
        while !remaining.is_empty() {
            let ready: Vec<AstId> = remaining
                .iter()
                .copied()
                .filter(|p| deps[p].iter().all(|q| !remaining.contains(q)))
                .collect();
            if ready.is_empty() {
                return None; // cycle
            }
            for p in ready {
                order.push(p);
                remaining.remove(&p);
            }
        }
        // Exact reach per predicate, in topological order.
        let mut reach: BTreeMap<AstId, AstId> =
            preds.iter().map(|&p| (p, self.m.mk_false())).collect();
        for &p in &order {
            let mut acc = self.m.mk_false();
            for (bs, body_app, guards, head_app) in &rules.clone() {
                let Some(happ) = *head_app else { continue };
                if self.predicate_of(happ)? != p {
                    continue;
                }
                let img = self.chc_rule_image(bs, *body_app, guards, Some(happ), &reach, &state)?;
                acc = self.m.mk_or(&[acc, img]);
            }
            acc = crate::rewriter::simplify(&mut self.m, acc);
            if self.m.postorder(acc).len() > 4000 {
                return None; // inlined reach blew up
            }
            reach.insert(p, acc);
        }
        // Check every query against the exact reach.
        for (bs, body_app, guards, head_app) in &rules.clone() {
            if head_app.is_some() {
                continue;
            }
            let q = self.chc_rule_image(bs, *body_app, guards, None, &reach, &state)?;
            match check_model(&self.m, q).0 {
                SmtResult::Sat => return Some(SmtResult::Unsat),
                SmtResult::Unknown => return None,
                SmtResult::Unsat => {}
            }
        }
        Some(SmtResult::Sat)
    }

    fn solve_chc_multi(&mut self) -> Option<SmtResult> {
        let (preds, state, rules) = self.chc_parse_multi()?;
        // Bounded forward reachability. Without model-based projection the reach
        // sets never converge to a quantifier-free fixpoint (each rule firing adds
        // fresh existential path variables), so the bound is kept small: deep
        // enough to expose shallow counterexamples, shallow enough that the safe
        // case declines quickly rather than churning on ever-growing formulas.
        let mut reach: BTreeMap<AstId, AstId> =
            preds.iter().map(|&p| (p, self.m.mk_false())).collect();
        const BOUND: usize = 3;
        for _ in 0..BOUND {
            let mut new_reach = reach.clone();
            for (bs, body_app, guards, head_app) in &rules.clone() {
                let Some(happ) = *head_app else { continue };
                let hp = self.predicate_of(happ)?;
                let img = self.chc_rule_image(bs, *body_app, guards, Some(happ), &reach, &state)?;
                let cur = new_reach[&hp];
                let or = self.m.mk_or(&[cur, img]);
                let or = crate::rewriter::simplify(&mut self.m, or);
                // Without projection the reach formula can bloat; bail to a sound
                // `unknown` rather than churn once it grows past a size budget.
                if self.m.postorder(or).len() > 160 {
                    return None;
                }
                new_reach.insert(hp, or);
            }
            reach = new_reach;
            for (bs, body_app, guards, head_app) in &rules.clone() {
                if head_app.is_some() {
                    continue;
                }
                let q = self.chc_rule_image(bs, *body_app, guards, None, &reach, &state)?;
                match check_model(&self.m, q).0 {
                    SmtResult::Sat => return Some(SmtResult::Unsat), // counterexample
                    // If the query can't be decided (the accumulating reach formula
                    // outgrew the budget), deeper rounds are only larger — bail.
                    SmtResult::Unknown => return None,
                    SmtResult::Unsat => {}
                }
            }
        }
        None
    }

    /// `reach[body]` restricted to a rule's body application: each stored
    /// polyhedron over the body predicate's canonical state, with those state
    /// variables substituted by the (linear) body arguments. A fact (no body
    /// predicate) contributes the single empty polyhedron (trivially reachable).
    fn chc_body_polys(
        &self,
        body_app: Option<AstId>,
        reach: &BTreeMap<AstId, Vec<Vec<Constraint>>>,
        state: &BTreeMap<AstId, Vec<AstId>>,
    ) -> Option<Vec<Vec<Constraint>>> {
        let Some(bapp) = body_app else {
            return Some(alloc::vec![Vec::new()]);
        };
        let bp = self.predicate_of(bapp)?;
        let bstate = state.get(&bp)?.clone();
        let bargs: Vec<AstId> = self.m.app_args(bapp).to_vec();
        if bargs.len() != bstate.len() {
            return None;
        }
        let bargs_lin: Vec<LinExpr> = bargs.iter().map(|&a| ast_to_lin(&self.m, a)).collect();
        let mut out = Vec::new();
        for poly in reach.get(&bp)? {
            let sub: Vec<Constraint> = poly
                .iter()
                .map(|c| {
                    let mut e = c.expr.clone();
                    for (i, &sv) in bstate.iter().enumerate() {
                        e = substitute_lin(&e, sv, &bargs_lin[i]);
                    }
                    Self::con(e, c.rel)
                })
                .collect();
            out.push(sub);
        }
        Some(out)
    }

    /// A [`Constraint`] from a linear expression and relation (`expr ⋈ 0`).
    fn con(expr: LinExpr, rel: Rel) -> Constraint {
        match rel {
            Rel::Le => Constraint::le(expr),
            Rel::Lt => Constraint::lt(expr),
            Rel::Eq => Constraint::eq(expr),
        }
    }

    /// Eliminate every variable not in `keep` from the polyhedron by
    /// Fourier–Motzkin (an over-approximation of the integer projection).
    fn poly_project(
        poly: &[Constraint],
        keep: &BTreeSet<AstId>,
        budget: &mut u64,
    ) -> Option<Vec<Constraint>> {
        let mut cs = poly.to_vec();
        let mut elim: Vec<AstId> = cs
            .iter()
            .flat_map(|c| c.expr.vars())
            .filter(|v| !keep.contains(v))
            .collect();
        elim.sort();
        elim.dedup();
        for v in elim {
            cs = project(&cs, v, budget)?;
        }
        Some(cs)
    }

    /// Does `poly` entail the constraint `c`? (`poly ⇒ c`, decided by
    /// infeasibility of `poly ∧ ¬c`.)
    fn poly_entails(poly: &[Constraint], c: &Constraint) -> bool {
        match c.rel {
            Rel::Le => {
                let mut t = poly.to_vec();
                t.push(Constraint::lt(c.expr.neg())); // ¬(e≤0) = e>0
                !feasible(&t)
            }
            Rel::Lt => {
                let mut t = poly.to_vec();
                t.push(Constraint::le(c.expr.neg())); // ¬(e<0) = e≥0
                !feasible(&t)
            }
            Rel::Eq => {
                let mut lo = poly.to_vec();
                lo.push(Constraint::lt(c.expr.clone()));
                let mut hi = poly.to_vec();
                hi.push(Constraint::lt(c.expr.neg()));
                !feasible(&lo) && !feasible(&hi)
            }
        }
    }

    /// Is `poly` already covered by one of the polyhedra in `union`?
    fn poly_subsumed(poly: &[Constraint], union: &[Vec<Constraint>]) -> bool {
        if !feasible(poly) {
            return true; // empty adds nothing
        }
        union
            .iter()
            .any(|e| e.iter().all(|c| Self::poly_entails(poly, c)))
    }

    /// Multi-predicate CHC **safety** via forward polyhedral reachability. Each
    /// `reach[P]` is a union of polyhedra over `P`'s canonical state, grown by
    /// applying the rules with Fourier–Motzkin projection to eliminate the path
    /// variables. FM over the reals *over-approximates* the integer reach, so a
    /// fixpoint whose reachable states never satisfy any query is a sound proof of
    /// **safety** (`sat`) — the exact counterexample (`unsat`) direction is left
    /// to the bounded engine. `None` when it doesn't converge or the
    /// over-approximation is too coarse (a query looks reachable).
    fn solve_chc_invariant(&mut self) -> Option<SmtResult> {
        let (preds, state, rules) = self.chc_parse_multi()?;
        let mut reach: BTreeMap<AstId, Vec<Vec<Constraint>>> =
            preds.iter().map(|&p| (p, Vec::new())).collect();
        let mut budget: u64 = 400_000;
        const MAX_ROUNDS: usize = 16;
        for _ in 0..MAX_ROUNDS {
            let mut changed = false;
            for (_bs, body_app, guards, head_app) in &rules.clone() {
                let Some(happ) = *head_app else { continue };
                let hp = self.predicate_of(happ)?;
                let hstate = state.get(&hp)?.clone();
                let hargs: Vec<AstId> = self.m.app_args(happ).to_vec();
                if hargs.len() != hstate.len() {
                    return None;
                }
                // Head equalities `state[hp]_i = arg_i`.
                let head_eqs: Vec<Constraint> = hstate
                    .iter()
                    .zip(hargs.iter())
                    .map(|(&sv, &ha)| {
                        Constraint::eq(LinExpr::var(sv).sub(&ast_to_lin(&self.m, ha)))
                    })
                    .collect();
                let guard_cubes = self.chc_guard_cubes(guards)?;
                let body_polys = self.chc_body_polys(*body_app, &reach, &state)?;
                let keep: BTreeSet<AstId> = hstate.iter().copied().collect();
                for bpoly in &body_polys {
                    for gcube in &guard_cubes {
                        let mut cs: Vec<Constraint> = bpoly.clone();
                        cs.extend(gcube.clone());
                        cs.extend(head_eqs.clone());
                        if !feasible(&cs) {
                            continue;
                        }
                        let proj = Self::poly_project(&cs, &keep, &mut budget)?;
                        if !feasible(&proj) {
                            continue;
                        }
                        if !Self::poly_subsumed(&proj, &reach[&hp]) {
                            reach.get_mut(&hp).unwrap().push(proj);
                            changed = true;
                        }
                    }
                }
                if reach[&hp].len() > 12 {
                    return None; // too many polyhedra — bail
                }
            }
            if !changed {
                // Fixpoint reached. A query is unreachable in the over-approx ⇒ safe.
                for (_bs, body_app, guards, head_app) in &rules.clone() {
                    if head_app.is_some() {
                        continue;
                    }
                    let guard_cubes = self.chc_guard_cubes(guards)?;
                    let body_polys = self.chc_body_polys(*body_app, &reach, &state)?;
                    for bpoly in &body_polys {
                        for gcube in &guard_cubes {
                            let mut cs = bpoly.clone();
                            cs.extend(gcube.clone());
                            if feasible(&cs) {
                                return None; // over-approx hits the query — inconclusive
                            }
                        }
                    }
                }
                return Some(SmtResult::Sat);
            }
        }
        None
    }

    /// Multi-predicate CHC **unsafety** via BFS path unrolling. Each predicate's
    /// frontier holds the concrete path formulas reached at the current depth
    /// (each a single feasible conjunction over that predicate's canonical state,
    /// with fresh path variables per step — never OR-accumulated, so the formulas
    /// stay small even at depth). A query satisfiable against any frontier path is
    /// a genuine counterexample (`unsat`). Bounded in depth and breadth; `None`
    /// when neither a counterexample nor a saturated (empty) frontier is found.
    fn solve_chc_bmc_paths(&mut self) -> Option<SmtResult> {
        let (_preds, state, rules) = self.chc_parse_multi()?;
        let empty: BTreeMap<AstId, AstId> = BTreeMap::new();
        // Depth 0: the fact rules (no body predicate).
        let mut frontier: BTreeMap<AstId, Vec<AstId>> = BTreeMap::new();
        for (bs, body_app, guards, head_app) in &rules {
            if body_app.is_some() {
                continue;
            }
            let Some(happ) = *head_app else { continue };
            let hp = self.predicate_of(happ)?;
            let img = self.chc_rule_image(bs, None, guards, Some(happ), &empty, &state)?;
            let img = crate::rewriter::simplify(&mut self.m, img);
            if matches!(check_model(&self.m, img).0, SmtResult::Sat) {
                frontier.entry(hp).or_default().push(img);
            }
        }
        const DEPTH: usize = 30;
        const MAX_PATHS: usize = 40;
        for _ in 0..DEPTH {
            // Query check against the current frontier.
            for (bs, body_app, guards, head_app) in &rules {
                if head_app.is_some() {
                    continue;
                }
                let paths: Vec<(BTreeMap<AstId, AstId>, &[AstId])> = match *body_app {
                    None => alloc::vec![(empty.clone(), &bs[..])],
                    Some(bapp) => {
                        let bp = self.predicate_of(bapp)?;
                        frontier
                            .get(&bp)
                            .into_iter()
                            .flatten()
                            .map(|&p| {
                                let mut rm = BTreeMap::new();
                                rm.insert(bp, p);
                                (rm, &bs[..])
                            })
                            .collect()
                    }
                };
                for (rm, bsl) in paths {
                    let q = self.chc_rule_image(bsl, *body_app, guards, None, &rm, &state)?;
                    if matches!(check_model(&self.m, q).0, SmtResult::Sat) {
                        return Some(SmtResult::Unsat);
                    }
                }
            }
            // Extend one transition step: next[P] = images of transition rules.
            let mut next: BTreeMap<AstId, Vec<AstId>> = BTreeMap::new();
            for (bs, body_app, guards, head_app) in &rules {
                let (Some(bapp), Some(happ)) = (*body_app, *head_app) else {
                    continue;
                };
                let bp = self.predicate_of(bapp)?;
                let hp = self.predicate_of(happ)?;
                for &path in frontier.get(&bp).into_iter().flatten() {
                    let mut rm = BTreeMap::new();
                    rm.insert(bp, path);
                    let img =
                        self.chc_rule_image(bs, Some(bapp), guards, Some(happ), &rm, &state)?;
                    let img = crate::rewriter::simplify(&mut self.m, img);
                    let bucket = next.entry(hp).or_default();
                    if !bucket.contains(&img)
                        && matches!(check_model(&self.m, img).0, SmtResult::Sat)
                    {
                        bucket.push(img);
                    }
                    if bucket.len() > MAX_PATHS {
                        return None;
                    }
                }
            }
            if next.values().all(|v| v.is_empty()) {
                break; // saturated — no counterexample reachable
            }
            frontier = next;
        }
        None
    }

    /// The guard of a rule as DNF constraint cubes (empty guard ⇒ one empty cube).
    fn chc_guard_cubes(&mut self, guards: &[AstId]) -> Option<Vec<Vec<Constraint>>> {
        if guards.is_empty() {
            return Some(alloc::vec![Vec::new()]);
        }
        let g = if guards.len() == 1 {
            guards[0]
        } else {
            self.m.mk_and(guards)
        };
        self.body_dnf(g, true)
    }

    /// Bounded model checking + k-induction over a parsed transition system.
    #[allow(clippy::too_many_arguments)]
    fn chc_bmc_kinduction(
        &mut self,
        sorts: &[AstId],
        state: &[AstId],
        next: &[AstId],
        init: AstId,
        trans: AstId,
        bad: AstId,
        locals: &[AstId],
    ) -> Option<SmtResult> {
        const MAX_K: usize = 40;
        // Step-state variables s_0, s_1, …; extended lazily.
        let mut steps: Vec<Vec<AstId>> = Vec::new();
        let fresh_state =
            |ctx: &mut Self| -> Vec<AstId> { sorts.iter().map(|&s| ctx.fresh_const(s)).collect() };
        steps.push(fresh_state(self));

        for k in 0..=MAX_K {
            while steps.len() <= k {
                let s = fresh_state(self);
                steps.push(s);
            }
            // BMC(k): Init(s_0) ∧ ⋀_{i<k} τ(s_i,s_{i+1}) ∧ Bad(s_k).
            let mut conj = alloc::vec![self.chc_inst(init, state, &steps[0], next, &[], locals)];
            for i in 0..k {
                let step_next = steps[i + 1].clone();
                conj.push(self.chc_inst(trans, state, &steps[i], next, &step_next, locals));
            }
            conj.push(self.chc_inst(bad, state, &steps[k], next, &[], locals));
            let formula = self.m.mk_and(&conj);
            match check_model(&self.m, formula).0 {
                SmtResult::Sat => return Some(SmtResult::Unsat), // counterexample ⇒ CHC unsat
                SmtResult::Unknown => return None,
                SmtResult::Unsat => {}
            }
            // k-induction step: ⋀_{i<k} ¬Bad(s_i) ∧ ⋀ τ(s_i,s_{i+1}) ∧ Bad(s_k)
            // UNSAT ⇒ ¬Bad is k-inductive; with the BMC base (all depths < k
            // unsat) this proves the invariant ⇒ CHC sat.
            if k >= 1 {
                let mut sconj = Vec::new();
                for i in 0..k {
                    let notbad = self.chc_inst(bad, state, &steps[i], next, &[], locals);
                    let nb = self.m.mk_not(notbad);
                    sconj.push(nb);
                    let step_next = steps[i + 1].clone();
                    sconj.push(self.chc_inst(trans, state, &steps[i], next, &step_next, locals));
                }
                sconj.push(self.chc_inst(bad, state, &steps[k], next, &[], locals));
                let sformula = self.m.mk_and(&sconj);
                // `unsat` ⇒ ¬Bad is k-inductive ⇒ safe. A `sat`/`unknown` step is
                // inconclusive; keep unrolling (BMC may find a counterexample).
                if check_model(&self.m, sformula).0 == SmtResult::Unsat {
                    return Some(SmtResult::Sat);
                }
            }
        }
        None // bound reached: sound `unknown`
    }

    /// Instantiate a transition-system formula for one unrolling step: substitute
    /// the canonical `state`/`next` vectors by the step vectors `cur`/`nxt`, and
    /// rename every local (binder) variable to a fresh copy (so different steps'
    /// auxiliary variables are independent).
    fn chc_inst(
        &mut self,
        formula: AstId,
        state: &[AstId],
        cur: &[AstId],
        next: &[AstId],
        nxt: &[AstId],
        locals: &[AstId],
    ) -> AstId {
        let mut subst: Vec<(AstId, AstId)> = Vec::new();
        for (j, &s) in state.iter().enumerate() {
            subst.push((s, cur[j]));
        }
        for (j, &s) in next.iter().enumerate() {
            if j < nxt.len() {
                subst.push((s, nxt[j]));
            }
        }
        for &l in locals {
            let s = self.m.get_sort(l);
            let f = self.fresh_const(s);
            subst.push((l, f));
        }
        substitute(&mut self.m, formula, &subst)
    }

    /// Split a Horn rule body into `(antecedent, consequent)`. Handles the
    /// `(=> A B)` form and the clausal `(or ¬A₁ … ¬Aₙ H)` form.
    fn chc_split_rule(&mut self, body: AstId) -> Option<(AstId, AstId)> {
        if self.m.is_implies(body) {
            let args = self.m.app_args(body).to_vec();
            if args.len() == 2 {
                return Some((args[0], args[1]));
            }
        }
        // A bare head predicate `P(..)` is a fact with a `true` antecedent.
        if self.predicate_of(body).is_some() {
            let t = self.m.mk_true();
            return Some((t, body));
        }
        None
    }

    /// Disjoin formulas (`false` if empty).
    fn mk_disjunction(&mut self, fs: &[AstId]) -> AstId {
        match fs {
            [] => self.m.mk_false(),
            [f] => *f,
            _ => self.m.mk_or(fs),
        }
    }

    /// Decide the assertions together with `extra` temporary constraints,
    /// without permanently adding them.
    fn check_with(&mut self, extra: &[AstId]) -> (SmtResult, Option<Model>) {
        let n = self.assertions.len();
        self.assertions.extend_from_slice(extra);
        let r = self.check_sat();
        self.assertions.truncate(n);
        r
    }

    /// Decide an arbitrary formula set in isolation (the current assertions are
    /// swapped out and restored), returning only the verdict.
    fn solve_set(&mut self, set: &[AstId]) -> SmtResult {
        let saved = core::mem::replace(&mut self.assertions, set.to_vec());
        let (res, _) = self.check_sat();
        self.assertions = saved;
        res
    }

    /// Solver-backed `ctx-solver-simplify`: return an equisatisfiable residual
    /// where each formula that the conjunction of the *others* already entails is
    /// dropped, or `None` if the set is unsatisfiable. Redundancy/contradiction
    /// are proved with the SMT engine; a non-`unsat` (incl. `unknown`) check
    /// conservatively keeps the formula, so the result is always sound.
    fn ctx_solver_simplify(&mut self, formulas: &[AstId]) -> Option<Vec<AstId>> {
        let mut kept: Vec<AstId> = Vec::new();
        for (i, &fi) in formulas.iter().enumerate() {
            if self.m.is_true(fi) {
                continue;
            }
            if self.m.is_false(fi) {
                return None;
            }
            // Context = already-kept formulas + not-yet-processed ones.
            let mut ctx = kept.clone();
            ctx.extend_from_slice(&formulas[i + 1..]);
            // If ctx ∧ ¬fi is unsat, ctx entails fi ⇒ fi is redundant.
            let nfi = self.m.mk_not(fi);
            let mut probe_redundant = ctx.clone();
            probe_redundant.push(nfi);
            if self.solve_set(&probe_redundant) == SmtResult::Unsat {
                continue;
            }
            // If ctx ∧ fi is unsat, the whole goal is unsat.
            let mut probe_conflict = ctx.clone();
            probe_conflict.push(fi);
            if self.solve_set(&probe_conflict) == SmtResult::Unsat {
                return None;
            }
            kept.push(fi);
        }
        Some(kept)
    }

    /// Optimize the recorded objectives (integer, lexicographic in declaration
    /// order) and return the model at the optimum. Each objective is bounded by
    /// binary search; a non-integer objective or one not bounded within budget
    /// is reported as `unknown` (or `oo`/`(- oo)` when provably unbounded).
    fn optimize(&mut self) -> (SmtResult, Option<Model>) {
        // The MaxSAT penalty (minimize the violated soft weight) is optimized
        // first, then the user objectives, lexicographically. The penalty is
        // bound to a fresh variable `pen = Σ(ite pᵢ wᵢ 0)`, threaded through the
        // optimization via `fixed`.
        let mut objs: Vec<(AstId, bool, String)> = Vec::new();
        let mut fixed: Vec<AstId> = Vec::new();
        if let Some(sum) = self.soft_penalty() {
            let int = self.m.mk_int_sort();
            let pen = self.fresh_const(int);
            let c = self.m.mk_eq(pen, sum);
            fixed.push(c);
            objs.push((pen, false, "!penalty".to_string()));
        }
        let user_start = objs.len();
        objs.extend(self.objectives.clone());
        let mut values = alloc::vec!["unknown".to_string(); objs.len()];
        let (res, mut model) = self.check_with(&fixed);
        if res != SmtResult::Sat {
            self.objective_values = values.split_off(user_start);
            return (res, model);
        }
        for (i, (obj, maximize, _)) in objs.iter().enumerate() {
            let (obj, maximize) = (*obj, *maximize);
            let osort = self.m.get_sort(obj);
            if self.m.is_arith_sort(osort) && !self.m.is_int_sort(osort) {
                // Real objective: Fourier–Motzkin optimum, then verify it.
                match self.real_optimize(obj, maximize, &fixed) {
                    RealOpt::Attained(r) => {
                        values[i] = render_rational(&r);
                        let rv = self.m.mk_numeral(r, false);
                        let eq = self.m.mk_eq(obj, rv);
                        fixed.push(eq);
                        model = self.check_with(&fixed).1;
                    }
                    RealOpt::Supremum(r) => {
                        // z3 form: max → r - ε, min → r + ε.
                        values[i] = if maximize {
                            alloc::format!("(+ {} (* (- 1.0) epsilon))", render_real(&r))
                        } else {
                            alloc::format!("(+ {} epsilon)", render_real(&r))
                        };
                    }
                    RealOpt::Unbounded => {
                        values[i] = if maximize {
                            "oo".to_string()
                        } else {
                            "(- oo)".to_string()
                        };
                    }
                    RealOpt::Unknown => {}
                }
                continue;
            }
            if !self.m.is_int_sort(self.m.get_sort(obj)) {
                continue; // only Int/Real objectives are optimized
            }
            let v0 = match model.as_mut().map(|m| m.eval(&self.m, obj)) {
                Some(Value::Num(r, _)) => r.numerator().clone(),
                _ => continue,
            };
            match self.opt_int_search(obj, maximize, v0, &fixed) {
                OptResult::Optimum(v) => {
                    values[i] = render_int(&v);
                    let iv = self.m.mk_numeral(Rational::from_integer(v), true);
                    let eq = self.m.mk_eq(obj, iv);
                    fixed.push(eq);
                    model = self.check_with(&fixed).1;
                }
                OptResult::Unbounded => {
                    values[i] = if maximize {
                        "oo".to_string()
                    } else {
                        "(- oo)".to_string()
                    };
                }
                OptResult::Unknown => {}
            }
        }
        // `get-objectives` reports only the user objectives, not the penalty.
        self.objective_values = values.split_off(user_start);
        (SmtResult::Sat, model)
    }

    /// Optimize a real-valued objective by Fourier–Motzkin bound extraction, and
    /// **verify** the candidate with the full solver so only a proven-exact
    /// attained optimum is reported (a supremum not attained, a non-linear goal,
    /// or a verification failure all fall back to `Unknown`).
    fn real_optimize(&mut self, obj: AstId, maximize: bool, fixed: &[AstId]) -> RealOpt {
        // The constraint system: base assertions plus the objective-fix set.
        let mut conj = self.assertions.clone();
        conj.extend_from_slice(fixed);
        let combined = match conj.len() {
            0 => self.m.mk_true(),
            1 => conj[0],
            _ => self.m.mk_and(&conj),
        };
        let lifted = self.lift(combined);
        let Some(cons) = linear_constraints(&self.m, lifted) else {
            return RealOpt::Unknown; // not a pure conjunction of linear constraints
        };
        let obj_lin = ast_to_lin(&self.m, obj);
        let real = self.m.mk_real_sort();
        let z = self.fresh_const(real);
        let mut budget: u64 = 200_000;
        match arith_optimize(&cons, &obj_lin, z, maximize, &mut budget) {
            OptOutcome::Unbounded => RealOpt::Unbounded,
            OptOutcome::Attained(r) => {
                // Verify: `obj` reaches r, and cannot pass it.
                let rv = self.m.mk_numeral(r.clone(), false);
                let (reach, pass) = if maximize {
                    (self.m.mk_ge(obj, rv), self.m.mk_gt(obj, rv))
                } else {
                    (self.m.mk_le(obj, rv), self.m.mk_lt(obj, rv))
                };
                let mut ex = fixed.to_vec();
                ex.push(reach);
                let achievable = self.check_with(&ex).0 == SmtResult::Sat;
                let mut ex = fixed.to_vec();
                ex.push(pass);
                let bounded = self.check_with(&ex).0 == SmtResult::Unsat;
                if achievable && bounded {
                    RealOpt::Attained(r)
                } else {
                    RealOpt::Unknown
                }
            }
            OptOutcome::Bound(r) => {
                // A strict bound: verify `obj` cannot reach r.
                let rv = self.m.mk_numeral(r.clone(), false);
                let reach = if maximize {
                    self.m.mk_ge(obj, rv)
                } else {
                    self.m.mk_le(obj, rv)
                };
                let mut ex = fixed.to_vec();
                ex.push(reach);
                if self.check_with(&ex).0 == SmtResult::Unsat {
                    RealOpt::Supremum(r)
                } else {
                    RealOpt::Unknown
                }
            }
            OptOutcome::Exhausted => RealOpt::Unknown,
        }
    }

    /// The MaxSAT penalty term `Σ (ite pᵢ wᵢ 0)` over the soft constraints, or
    /// `None` if there are none.
    fn soft_penalty(&mut self) -> Option<AstId> {
        if self.soft.is_empty() {
            return None;
        }
        let soft = self.soft.clone();
        let zero = self.m.mk_int(0);
        let terms: Vec<AstId> = soft
            .iter()
            .map(|&(p, w)| {
                let wv = self.m.mk_int(w);
                self.m.mk_ite(p, wv, zero)
            })
            .collect();
        Some(if terms.len() == 1 {
            terms[0]
        } else {
            self.m.mk_add(&terms)
        })
    }

    /// The bound constraint `obj ≥ k` (maximize) or `obj ≤ k` (minimize).
    fn opt_bound(&mut self, obj: AstId, maximize: bool, k: &Int) -> AstId {
        let kv = self.m.mk_numeral(Rational::from_integer(k.clone()), true);
        if maximize {
            self.m.mk_ge(obj, kv)
        } else {
            self.m.mk_le(obj, kv)
        }
    }

    /// Binary-search the optimum of the integer objective `obj` (feasible value
    /// `v0`) subject to the base assertions plus `fixed`. Probes an outer bound
    /// by doubling, then bisects; caps total solves.
    fn opt_int_search(
        &mut self,
        obj: AstId,
        maximize: bool,
        v0: Int,
        fixed: &[AstId],
    ) -> OptResult {
        let two = Int::from(2);
        let mut budget = 200i32;
        let sat_at = |ctx: &mut Self, k: &Int, budget: &mut i32| -> Option<bool> {
            if *budget <= 0 {
                return None;
            }
            *budget -= 1;
            let c = ctx.opt_bound(obj, maximize, k);
            let mut ex = fixed.to_vec();
            ex.push(c);
            Some(ctx.check_with(&ex).0 == SmtResult::Sat)
        };
        // Doubling to find a bound infeasible in the optimizing direction.
        let dir = |v: &Int, s: &Int, maximize: bool| if maximize { v.add(s) } else { v.sub(s) };
        let mut step = Int::from(1);
        let mut feasible = v0;
        let infeasible;
        loop {
            let cand = dir(&feasible, &step, maximize);
            match sat_at(self, &cand, &mut budget) {
                None => return OptResult::Unknown,
                Some(true) => {
                    feasible = cand;
                    step = step.mul(&two);
                    if step.bit_len() > 200 {
                        return OptResult::Unbounded;
                    }
                }
                Some(false) => {
                    infeasible = cand;
                    break;
                }
            }
        }
        // Bisect: `feasible` is sat, `infeasible` is unsat, one step apart at end.
        let (mut lo, mut hi) = (feasible, infeasible);
        loop {
            let gap = hi.sub(&lo).abs();
            if gap <= Int::from(1) {
                break;
            }
            let mid = lo.add(&hi).div_rem(&two).map(|(q, _)| q).unwrap();
            match sat_at(self, &mid, &mut budget) {
                None => return OptResult::Unknown,
                Some(true) => lo = mid,
                Some(false) => hi = mid,
            }
        }
        OptResult::Optimum(lo)
    }

    /// The `(objectives …)` response after an optimizing `check-sat`.
    fn get_objectives(&self) -> String {
        let mut out = String::from("(objectives");
        for ((_, _, text), val) in self.objectives.iter().zip(&self.objective_values) {
            out.push_str(&alloc::format!("\n ({text} {val})"));
        }
        out.push_str("\n)");
        out
    }

    /// Quantifier elimination for a top-level `∀ vars. body` over **real**
    /// linear arithmetic: `∀x.φ ≡ ¬∃x.¬φ`; the DNF of `¬φ` is projected
    /// variable-by-variable (Fourier–Motzkin, exact for the reals), and the
    /// result is rebuilt as a quantifier-free formula. `None` if the body is not
    /// purely linear or a projection exceeds budget (→ fall back to instantiation).
    fn qe_forall(&mut self, vars: &[AstId], body: AstId) -> Option<AstId> {
        let arith = |m: &AstManager, v: AstId| m.is_arith_sort(m.get_sort(v));
        if !vars.iter().all(|&v| arith(&self.m, v)) {
            return None;
        }
        let all_int = vars.iter().all(|&v| self.m.is_int_sort(self.m.get_sort(v)));
        let all_real = vars
            .iter()
            .all(|&v| !self.m.is_int_sort(self.m.get_sort(v)));
        if !all_int && !all_real {
            return None; // mixed Int/Real binders unsupported
        }
        // DNF of ¬body: a disjunction of cubes (conjunctions of constraints).
        let mut cubes = self.body_dnf(body, false)?;
        // A binder may appear ONLY as a linear variable. If one occurs inside a
        // compound term — e.g. an uninterpreted application `f(x)`, which
        // `ast_to_lin` opaquely treats as a single variable — Fourier–Motzkin
        // cannot eliminate it (projecting the binder would leave it free in that
        // term, unsound). Fall back to instantiation in that case.
        let bound: BTreeSet<AstId> = vars.iter().copied().collect();
        for cube in &cubes {
            for c in cube {
                for (u, _) in c.expr.terms() {
                    if !bound.contains(&u) && self.m.postorder(u).iter().any(|t| bound.contains(t))
                    {
                        return None;
                    }
                }
            }
        }
        // Fourier–Motzkin is exact for the reals; for integers it is exact only
        // when the body is pure LIA (integer coefficients) and every binder
        // appears with coefficient ±1 (real shadow = integer shadow). Otherwise
        // fall back to instantiation rather than risk an unsound elimination.
        if all_int {
            for cube in &cubes {
                for c in cube {
                    if !c.expr.const_term().is_integer()
                        || c.expr.terms().any(|(_, k)| !k.is_integer())
                    {
                        return None;
                    }
                    for &v in vars {
                        let cv = c
                            .expr
                            .terms()
                            .find(|(u, _)| *u == v)
                            .map(|(_, k)| k.clone());
                        if let Some(k) = cv
                            && k.abs() != rat(1)
                        {
                            return None;
                        }
                    }
                }
            }
            // Over the integers a strict `expr < 0` is `expr + 1 ≤ 0`; tighten it
            // so Fourier–Motzkin's real shadow matches the integer shadow (else
            // `x > 0 ∧ x < 1` looks feasible over the reals though it is empty
            // over the integers).
            for cube in &mut cubes {
                for c in cube.iter_mut() {
                    if c.rel == Rel::Lt {
                        *c = Constraint::le(c.expr.integer_strict_tighten());
                    }
                }
            }
        }
        let mut budget: u64 = 100_000;
        // Project every bound variable out of each cube, then rebuild ∃x.¬body.
        let mut disjuncts: Vec<AstId> = Vec::new();
        for mut cube in cubes {
            for &v in vars {
                cube = project(&cube, v, &mut budget)?;
            }
            let atoms: Vec<AstId> = cube
                .iter()
                .map(|c| self.constraint_atom(c, all_int))
                .collect();
            disjuncts.push(match atoms.len() {
                0 => self.m.mk_true(),
                1 => atoms[0],
                _ => self.m.mk_and(&atoms),
            });
        }
        let exists_neg = match disjuncts.len() {
            0 => self.m.mk_false(),
            1 => disjuncts[0],
            _ => self.m.mk_or(&disjuncts),
        };
        Some(self.m.mk_not(exists_neg)) // ¬∃x.¬body
    }

    /// Decide `∀x. ∃y. φ` over **linear real** arithmetic: parse `x` and `y` into
    /// one scope, eliminate `∃y` exactly (Fourier–Motzkin), then eliminate `∀x`.
    /// `None` if the shape/sorts/body are outside this fragment (fall through to
    /// Skolemization + instantiation).
    fn try_forall_exists_qe(&mut self, binders: &SExpr, inner: &SExpr) -> Option<AstId> {
        // Prenex the positive existentials of the body to the front (`guard ⇒ ∃y.φ`
        // ≡ `∃y. guard ⇒ φ`, since `guard` is `y`-free). No existential ⇒ not our
        // shape.
        let mut ybind: Vec<SExpr> = Vec::new();
        let body = Self::prenex_pos_exists(inner, &mut ybind, true);
        if ybind.is_empty() {
            return None;
        }
        let xbind = as_list(binders).ok()?;
        let ybind = &ybind[..];
        let inner = body;
        // Push a combined scope with all universal and existential binders; all
        // must be real-sorted.
        let mut scope = Vec::new();
        let mut xvars = Vec::new();
        let mut yvars = Vec::new();
        for (bs, out) in [(xbind, &mut xvars), (ybind, &mut yvars)] {
            for b in bs {
                let pair = as_list(b).ok()?;
                let nm = Self::sym(&pair[0]).ok()?.to_string();
                let s = self.resolve_sort(&pair[1]).ok()?;
                if !self.m.is_arith_sort(s) {
                    return None;
                }
                let c = self.fresh_const(s);
                scope.push((nm, c));
                out.push(c);
            }
        }
        self.scopes.push(scope);
        let phi = self.term(&inner);
        self.scopes.pop();
        let phi = phi.ok()?;
        // Integers: full Presburger QE (Cooper) — decides divisibility cases the
        // real-shadow Fourier–Motzkin path declines on.
        let all_int = xvars
            .iter()
            .chain(&yvars)
            .all(|&v| self.m.is_int_sort(self.m.get_sort(v)));
        if all_int && let Some(verdict) = self.cooper_forall_exists(&xvars, &yvars, phi) {
            return Some(if verdict {
                self.m.mk_true()
            } else {
                self.m.mk_false()
            });
        }
        // Nonlinear `∀xs. ∃y. c·y² + Q(xs) ⋈ 0`: the inner `∃y` reduces to a sign
        // condition on `Q` (a real `y` with `y² = −Q/c` exists iff `−Q/c ≥ 0`),
        // and the resulting `∀xs. sign(Q)` is a quantifier-free CAD query.
        if let Some(verdict) = self.try_nonlinear_forall_exists(&xvars, &yvars, phi) {
            return Some(if verdict {
                self.m.mk_true()
            } else {
                self.m.mk_false()
            });
        }
        let psi = self.qe_exists(&yvars, phi)?;
        self.qe_forall(&xvars, psi)
    }

    /// Decide `∀xs. ∃y. c·y² + Q(xs) ⋈ 0` (a single existential appearing only as
    /// `y²`, single atom body) by reducing the inner `∃y` to a sign condition on
    /// the `y`-free part `Q` and checking the universal over `xs` with `cad_sat`.
    /// `None` if the body is not of this shape.
    fn try_nonlinear_forall_exists(
        &self,
        _xvars: &[AstId],
        yvars: &[AstId],
        phi: AstId,
    ) -> Option<bool> {
        use crate::nlsat::{Rel as NRel, cad::cad_sat};
        if yvars.len() != 1 {
            return None;
        }
        let y = yvars[0];
        let mut var_map = BTreeMap::new();
        let con = self.icp_atom(phi, false, &mut var_map)?;
        let yi = *var_map.get(&y)?;
        let poly = &con.poly;
        let dy = poly.degree_of(yi);
        // An odd-degree polynomial in `y` with a nonzero *constant* leading
        // coefficient is surjective in `y`, so `∃y. p(y) = 0` holds for every xs.
        if con.rel == crate::nlsat::Rel::Eq
            && dy % 2 == 1
            && poly
                .coeff_of_var(yi, dy)
                .as_constant()
                .is_some_and(|c| !c.is_zero())
        {
            return Some(true);
        }
        // Otherwise handle the genuine quadratic in `y` (degree exactly 2 with a
        // nonzero constant leading coefficient).
        if dy != 2 {
            return None;
        }
        let a = poly.coeff_of_var(yi, 2).as_constant()?;
        if a.is_zero() {
            return None;
        }
        let bpoly = poly.coeff_of_var(yi, 1); // linear-in-`y` coefficient, over xs
        let q = poly.coeff_of_var(yi, 0); // the `y`-free part Q(xs)
        let nvars = var_map.len();
        // Equation `a·y² + b·y + Q = 0` has a real `y` iff the discriminant
        // `b² − 4aQ ≥ 0`; the residual universal `∀xs. disc ≥ 0` refutes iff
        // `∃xs. disc < 0`.
        if con.rel == crate::nlsat::Rel::Eq {
            let four_a = a.mul(&Rational::from_integer(Int::from(4)));
            let disc = bpoly.mul(&bpoly).sub(&q.scale(&four_a));
            let sat = cad_sat(&[(disc, NRel::Lt)], nvars)?;
            return Some(!sat);
        }
        // Inequalities: only the pure-`y²` case (no linear term), where `c·y²`
        // ranges over `[0,∞)` (`c>0`) or `(−∞,0]` (`c<0`).
        if !bpoly.is_zero() {
            return None;
        }
        let c = a;
        // `∃y. c·y² + Q ⋈ 0` as a condition on `Q`:
        //   `≤`  : solvable iff `c>0 ⇒ Q ≤ 0`, `c<0` always
        //   `≥`  : `c>0` always; `c<0 ⇒ Q ≥ 0`
        // The universal `∀xs. cond` holds iff its negation is UNSAT over `xs`.
        let cpos = c.signum() > 0;
        // `neg_cond`: the `(poly, rel)` whose satisfiability refutes the universal.
        let neg_cond = match (con.rel, cpos) {
            // Q ≤ 0 required → refute with Q > 0.
            (NRel::Le, true) => (q, NRel::Gt),
            // Q ≥ 0 required → refute with Q < 0.
            (NRel::Ge, false) => (q, NRel::Lt),
            // Q < 0 required (strict, `c·y²` reaches its min 0 at y=0) → refute Q ≥ 0.
            (NRel::Lt, true) => (q, NRel::Ge),
            // Q > 0 required (`c·y²` reaches its max 0 at y=0) → refute Q ≤ 0.
            (NRel::Gt, false) => (q, NRel::Le),
            // `c·y²` is unbounded in the required direction → always solvable.
            (NRel::Ge | NRel::Gt, true) | (NRel::Le | NRel::Lt, false) => return Some(true),
            _ => return None,
        };
        let nvars = var_map.len();
        let sat = cad_sat(&[neg_cond], nvars)?;
        Some(!sat)
    }

    /// Decide `∀xs. ∃ys. φ` over linear-integer arithmetic by Cooper's QE:
    /// eliminate every existential then every universal, leaving a ground formula.
    /// `None` if `φ` is not linear-integer or the elimination exceeds its budget.
    fn cooper_forall_exists(
        &mut self,
        xvars: &[AstId],
        yvars: &[AstId],
        phi: AstId,
    ) -> Option<bool> {
        use crate::smt::cooper::{self, Atom};
        let cubes = self.body_dnf(phi, true)?;
        let mut dnf: cooper::Dnf = Vec::new();
        for cube in &cubes {
            let mut c: Vec<Atom> = Vec::new();
            for con in cube {
                // Cooper needs integer coefficients.
                if !con.expr.const_term().is_integer()
                    || con.expr.terms().any(|(_, k)| !k.is_integer())
                {
                    return None;
                }
                c.push(match con.rel {
                    Rel::Lt => Atom::Lt(con.expr.clone()),
                    Rel::Le => Atom::Le(con.expr.clone()),
                    Rel::Eq => Atom::Eq(con.expr.clone()),
                });
            }
            dnf.push(c);
        }
        let mut budget: u64 = 2_000_000;
        for &y in yvars {
            dnf = cooper::exists(&dnf, y, &mut budget)?;
        }
        for &x in xvars {
            dnf = cooper::forall(&dnf, x, &mut budget)?;
        }
        cooper::ground_sat(&dnf)
    }

    /// Strip positive existentials from `body`, collecting their binder
    /// declarations into `out` (prenexing them to the front). Descends through
    /// `not` (flipping polarity), `=>`, `and`, `or`; existentials in negative
    /// position (or under `ite`) are left in place.
    fn prenex_pos_exists(body: &SExpr, out: &mut Vec<SExpr>, positive: bool) -> SExpr {
        let SExpr::List(l) = body else {
            return body.clone();
        };
        let Some(SExpr::Atom(head)) = l.first() else {
            return body.clone();
        };
        match (head.as_str(), l.len()) {
            ("exists", 3) if positive => {
                if let SExpr::List(bs) = &l[1] {
                    out.extend(bs.iter().cloned());
                }
                Self::prenex_pos_exists(&l[2], out, positive)
            }
            ("not", 2) => SExpr::List(alloc::vec![
                l[0].clone(),
                Self::prenex_pos_exists(&l[1], out, !positive),
            ]),
            ("=>", 3) => SExpr::List(alloc::vec![
                l[0].clone(),
                Self::prenex_pos_exists(&l[1], out, !positive),
                Self::prenex_pos_exists(&l[2], out, positive),
            ]),
            ("and" | "or", _) => {
                let mut v = alloc::vec![l[0].clone()];
                for a in &l[1..] {
                    v.push(Self::prenex_pos_exists(a, out, positive));
                }
                SExpr::List(v)
            }
            _ => body.clone(),
        }
    }

    /// Eliminate the existential binders `vars` from `∃vars. body`, returning the
    /// equivalent quantifier-free formula. **Real binders only** — Fourier–Motzkin
    /// is exact over the reals, so both directions are sound (over the integers it
    /// would over-approximate). `None` if the body is not purely linear or a binder
    /// occurs inside a compound term.
    fn qe_exists(&mut self, vars: &[AstId], body: AstId) -> Option<AstId> {
        if !vars
            .iter()
            .all(|&v| self.m.is_arith_sort(self.m.get_sort(v)))
        {
            return None;
        }
        let all_int = vars.iter().all(|&v| self.m.is_int_sort(self.m.get_sort(v)));
        let all_real = vars
            .iter()
            .all(|&v| !self.m.is_int_sort(self.m.get_sort(v)));
        if !all_int && !all_real {
            return None; // mixed Int/Real binders unsupported
        }
        let mut cubes = self.body_dnf(body, true)?;
        let bound: BTreeSet<AstId> = vars.iter().copied().collect();
        for cube in &cubes {
            for c in cube {
                for (u, _) in c.expr.terms() {
                    if !bound.contains(&u) && self.m.postorder(u).iter().any(|t| bound.contains(t))
                    {
                        return None;
                    }
                }
            }
        }
        // Fourier–Motzkin is exact for the reals; over the integers it is exact
        // only for pure LIA where every binder appears with coefficient ±1 (real
        // shadow = integer shadow). Otherwise decline (a divisibility-carrying
        // projection would need Cooper) rather than risk an unsound elimination.
        if all_int {
            for cube in &cubes {
                for c in cube {
                    if !c.expr.const_term().is_integer()
                        || c.expr.terms().any(|(_, k)| !k.is_integer())
                    {
                        return None;
                    }
                    for &v in vars {
                        if let Some(k) = c
                            .expr
                            .terms()
                            .find(|(u, _)| *u == v)
                            .map(|(_, k)| k.clone())
                            && k.abs() != rat(1)
                        {
                            return None;
                        }
                    }
                }
            }
            for cube in &mut cubes {
                for c in cube.iter_mut() {
                    if c.rel == Rel::Lt {
                        *c = Constraint::le(c.expr.integer_strict_tighten());
                    }
                }
            }
        }
        let mut budget: u64 = 100_000;
        let mut disjuncts: Vec<AstId> = Vec::new();
        for mut cube in cubes {
            for &v in vars {
                cube = project(&cube, v, &mut budget)?;
            }
            let atoms: Vec<AstId> = cube
                .iter()
                .map(|c| self.constraint_atom(c, all_int))
                .collect();
            disjuncts.push(match atoms.len() {
                0 => self.m.mk_true(),
                1 => atoms[0],
                _ => self.m.mk_and(&atoms),
            });
        }
        Some(match disjuncts.len() {
            0 => self.m.mk_false(),
            1 => disjuncts[0],
            _ => self.m.mk_or(&disjuncts),
        })
    }

    /// The DNF of `term` (or its negation when `positive` is false) as a list of
    /// cubes, each a conjunction of linear [`Constraint`]s. `None` if `term` is
    /// not built from `and`/`or`/`not`/`=>`/`ite`-free linear (in)equalities.
    fn body_dnf(&self, term: AstId, positive: bool) -> Option<Vec<Vec<Constraint>>> {
        let m = &self.m;
        if m.is_true(term) {
            return Some(if positive {
                alloc::vec![Vec::new()]
            } else {
                Vec::new()
            });
        }
        if m.is_false(term) {
            return Some(if positive {
                Vec::new()
            } else {
                alloc::vec![Vec::new()]
            });
        }
        if m.is_not(term) {
            return self.body_dnf(m.app_args(term)[0], !positive);
        }
        // (and …) positive = ⋀; negative = ⋁ of negations (De Morgan). `or` dual.
        let is_and = m.is_and(term);
        let is_or = m.is_or(term);
        if is_and || is_or {
            let args = m.app_args(term).to_vec();
            // Conjunctive if (and,positive) or (or,negative); else disjunctive.
            let conjunctive = is_and == positive;
            let mut acc: Vec<Vec<Constraint>> = alloc::vec![Vec::new()];
            let mut disj: Vec<Vec<Constraint>> = Vec::new();
            for a in args {
                let sub = self.body_dnf(a, positive)?;
                if conjunctive {
                    // Cross product acc × sub.
                    let mut next = Vec::new();
                    for c1 in &acc {
                        for c2 in &sub {
                            let mut c = c1.clone();
                            c.extend(c2.clone());
                            next.push(c);
                            if next.len() > 256 {
                                return None; // DNF blow-up guard
                            }
                        }
                    }
                    acc = next;
                } else {
                    disj.extend(sub);
                    if disj.len() > 256 {
                        return None;
                    }
                }
            }
            return Some(if conjunctive { acc } else { disj });
        }
        if m.is_implies(term) {
            // (=> a b) ≡ (or (not a) b).
            let args = m.app_args(term).to_vec();
            let (na, b) = (
                self.body_dnf(args[0], !positive)?,
                self.body_dnf(args[1], positive)?,
            );
            if positive {
                // positive (=> a b): disjunctive → union.
                let mut out = na;
                out.extend(b);
                return Some(out);
            }
            // negative (=> a b) = a ∧ ¬b: conjunctive cross product.
            let a = self.body_dnf(args[0], true)?;
            let nb = self.body_dnf(args[1], false)?;
            let mut out = Vec::new();
            for c1 in &a {
                for c2 in &nb {
                    let mut c = c1.clone();
                    c.extend(c2.clone());
                    out.push(c);
                }
            }
            return Some(out);
        }
        // A linear atom.
        self.atom_dnf(term, positive)
    }

    /// The DNF cubes of a single linear atom under the given polarity.
    fn atom_dnf(&self, atom: AstId, positive: bool) -> Option<Vec<Vec<Constraint>>> {
        let m = &self.m;
        let (a, b, op) = if m.is_eq(atom) {
            let args = m.app_args(atom);
            if !m.is_arith_sort(m.get_sort(args[0])) {
                return None;
            }
            (args[0], args[1], "=")
        } else if let Some(o) = m.arith_op(atom) {
            let args = m.app_args(atom);
            let s = match o {
                ArithOp::Le => "<=",
                ArithOp::Lt => "<",
                ArithOp::Ge => ">=",
                ArithOp::Gt => ">",
                _ => return None,
            };
            (args[0], args[1], s)
        } else {
            return None;
        };
        let diff = ast_to_lin(m, a).sub(&ast_to_lin(m, b)); // a - b
        // Build the constraint(s) for `op` (positive) or its negation.
        let le = |e: crate::smt::LinExpr| alloc::vec![alloc::vec![Constraint::le(e)]];
        let lt = |e: crate::smt::LinExpr| alloc::vec![alloc::vec![Constraint::lt(e)]];
        Some(match (op, positive) {
            // ¬(a > b) = a ≤ b (non-strict); ¬(a ≥ b) = a < b (strict).
            ("<=", true) | (">", false) => le(diff), // a ≤ b
            ("<=", false) | (">", true) => lt(diff.neg()), // a > b  ⟺ b < a
            ("<", true) | (">=", false) => lt(diff), // a < b
            ("<", false) | (">=", true) => le(diff.neg()), // a ≥ b
            ("=", true) => alloc::vec![alloc::vec![Constraint::eq(diff)]],
            ("=", false) => alloc::vec![
                alloc::vec![Constraint::lt(diff.clone())], // a < b
                alloc::vec![Constraint::lt(diff.neg())],   // a > b
            ],
            _ => return None,
        })
    }

    /// Rebuild the AST atom `expr ⋈ 0` from a linear [`Constraint`] (`is_int`
    /// selects Int vs Real numerals).
    fn constraint_atom(&mut self, c: &Constraint, is_int: bool) -> AstId {
        let t = self.lin_to_term(&c.expr, is_int);
        let zero = self.m.mk_numeral(rat(0), is_int);
        match c.rel {
            Rel::Le => self.m.mk_le(t, zero),
            Rel::Lt => self.m.mk_lt(t, zero),
            Rel::Eq => self.m.mk_eq(t, zero),
        }
    }

    /// Build the AST term of a linear expression (`is_int` → Int numerals).
    fn lin_to_term(&mut self, e: &crate::smt::LinExpr, is_int: bool) -> AstId {
        let mut parts: Vec<AstId> = Vec::new();
        for (v, coeff) in e.terms() {
            if coeff == &rat(1) {
                parts.push(v);
            } else {
                let k = self.m.mk_numeral(coeff.clone(), is_int);
                parts.push(self.m.mk_mul(&[k, v]));
            }
        }
        let c = e.const_term().clone();
        if !c.is_zero() || parts.is_empty() {
            parts.push(self.m.mk_numeral(c, is_int));
        }
        match parts.len() {
            1 => parts[0],
            _ => self.m.mk_add(&parts),
        }
    }

    /// Parse a quantifier's binder list `((x S) …)` and body into fresh
    /// placeholder constants (one per bound variable) and the body term built
    /// over them. The placeholders double as skolem constants for `exists`.
    /// Declare a (possibly recursive) function `name` with the given parameter
    /// list and return sort as an uninterpreted symbol.
    fn declare_rec_fun(&mut self, name: &SExpr, params: &SExpr, ret: &SExpr) -> Result<(), String> {
        let name = Self::sym(name)?.to_string();
        let domain: Vec<AstId> = as_list(params)?
            .iter()
            .map(|p| {
                let pair = as_list(p)?;
                self.resolve_sort(&pair[1])
            })
            .collect::<Result<_, _>>()?;
        let range = self.resolve_sort(ret)?;
        let d = self.m.mk_func_decl(Symbol::new(&name), &domain, range);
        self.funcs.insert(name.clone(), d);
        self.decl_order.push(name);
        Ok(())
    }

    /// Add the defining axiom `∀p. name(p) = body` for a recursive function as a
    /// universal (a ground equation when there are no parameters).
    fn add_rec_axiom(&mut self, name: &SExpr, params: &SExpr, body: &SExpr) -> Result<(), String> {
        let fname = Self::sym(name)?.to_string();
        let decl = *self
            .funcs
            .get(&fname)
            .ok_or_else(|| alloc::format!("recursive function {fname} not declared"))?;
        let mut scope = Vec::new();
        let mut vars = Vec::new();
        for p in as_list(params)? {
            let pair = as_list(p)?;
            let pname = Self::sym(&pair[0])?.to_string();
            let psort = self.resolve_sort(&pair[1])?;
            let ph = self.fresh_const(psort);
            scope.push((pname, ph));
            vars.push(ph);
        }
        let app = self.m.mk_app(decl, &vars);
        self.scopes.push(scope);
        let body = self.term(body);
        self.scopes.pop();
        let axiom = self.m.mk_eq(app, body?);
        if vars.is_empty() {
            self.assertions.push(axiom);
            self.assert_names.push(None);
        } else {
            self.universals.push((vars, axiom));
        }
        Ok(())
    }

    /// Skolemize the positive existentials of a universal body: `∀xs. … ∃y:S. P …`
    /// (`y` in positive position) becomes `∀xs. … P[y := f(xs)] …` with a fresh
    /// Skolem function `f : (sorts of xs) → S`. Descends through `not` (flipping
    /// polarity), `=>`/`and`/`or`/`ite`; positive nested `∀` extend the scope.
    /// Existentials in negative position are left for the sound `unknown` path.
    fn skolemize_body(
        &mut self,
        body: &SExpr,
        univ: &[(String, SExpr)],
        positive: bool,
    ) -> Result<SExpr, String> {
        let SExpr::List(l) = body else {
            return Ok(body.clone());
        };
        let Some(SExpr::Atom(head)) = l.first() else {
            return Ok(body.clone());
        };
        let recur = |ctx: &mut Self, e: &SExpr, pos: bool| ctx.skolemize_body(e, univ, pos);
        match (head.as_str(), l.len()) {
            ("exists", 3) if positive => {
                let mut subst: Vec<(String, SExpr)> = Vec::new();
                for b in as_list(&l[1])? {
                    let pair = as_list(b)?;
                    let yname = Self::sym(&pair[0])?.to_string();
                    let ysort = pair[1].clone();
                    let fname = alloc::format!("!sk!{}", self.fresh_counter);
                    self.fresh_counter += 1;
                    let dom: Vec<AstId> = univ
                        .iter()
                        .map(|(_, s)| self.resolve_sort(s))
                        .collect::<Result<_, _>>()?;
                    let ran = self.resolve_sort(&ysort)?;
                    let d = self.m.mk_func_decl(Symbol::new(&fname), &dom, ran);
                    self.funcs.insert(fname.clone(), d);
                    let skterm = if univ.is_empty() {
                        SExpr::Atom(fname)
                    } else {
                        let mut app = alloc::vec![SExpr::Atom(fname)];
                        app.extend(univ.iter().map(|(n, _)| SExpr::Atom(n.clone())));
                        SExpr::List(app)
                    };
                    subst.push((yname, skterm));
                }
                let inner = subst_sexpr(&l[2], &subst);
                self.skolemize_body(&inner, univ, positive)
            }
            ("forall", 3) if positive => {
                let mut u2 = univ.to_vec();
                for b in as_list(&l[1])? {
                    let p = as_list(b)?;
                    u2.push((Self::sym(&p[0])?.to_string(), p[1].clone()));
                }
                let inner = self.skolemize_body(&l[2], &u2, positive)?;
                Ok(SExpr::List(alloc::vec![l[0].clone(), l[1].clone(), inner]))
            }
            ("not", 2) => Ok(SExpr::List(alloc::vec![
                l[0].clone(),
                recur(self, &l[1], !positive)?,
            ])),
            ("=>", 3) => Ok(SExpr::List(alloc::vec![
                l[0].clone(),
                recur(self, &l[1], !positive)?,
                recur(self, &l[2], positive)?,
            ])),
            ("and" | "or", _) => {
                let mut out = alloc::vec![l[0].clone()];
                for a in &l[1..] {
                    out.push(recur(self, a, positive)?);
                }
                Ok(SExpr::List(out))
            }
            ("ite", 4) => Ok(SExpr::List(alloc::vec![
                l[0].clone(),
                l[1].clone(),
                recur(self, &l[2], positive)?,
                recur(self, &l[3], positive)?,
            ])),
            _ => Ok(body.clone()),
        }
    }

    fn parse_quantifier(
        &mut self,
        binders: &SExpr,
        body: &SExpr,
    ) -> Result<(Vec<AstId>, AstId), String> {
        let binders = as_list(binders)?;
        let mut scope = Vec::new();
        let mut vars = Vec::new();
        for b in binders {
            let pair = as_list(b)?;
            let name = Self::sym(&pair[0])?.to_string();
            let sort = self.resolve_sort(&pair[1])?;
            let ph = self.fresh_const(sort);
            scope.push((name, ph));
            vars.push(ph);
        }
        self.scopes.push(scope);
        let result = self.term(body);
        self.scopes.pop();
        Ok((vars, result?))
    }

    /// Ground instances of every recorded universal. Bound-var placeholders are
    /// substituted by ground terms of the matching sort, drawn from the
    /// assertions **and from previously generated instances** — iterating to a
    /// fixpoint so chained/inductive universals (`∀x. p(x) ⇒ p(x+1)` with
    /// `p(0)`, `¬p(3)`) fully unfold. Bounded by rounds and a total-instance cap.
    /// Fold datatype selector/tester applications on constructor terms
    /// (`selᵢ(C(a₁,…))=aᵢ`, `is-C(D(…))` = `C==D`), bottom-up. This lets a
    /// recursive function over a datatype bottom out under instantiation (e.g.
    /// `tail(cons h t)` collapses to `t`, exposing the next argument to
    /// E-matching) instead of unfolding an opaque selector chain forever.
    fn dt_fold(&mut self, root: AstId) -> AstId {
        // Reverse lookups: selector decl → (constructor decl, field index);
        // tester decl → constructor decl; and the set of constructor decls.
        let mut sel_of: BTreeMap<AstId, (AstId, usize)> = BTreeMap::new();
        let mut test_of: BTreeMap<AstId, AstId> = BTreeMap::new();
        let mut ctors: BTreeSet<AstId> = BTreeSet::new();
        for infos in self.datatypes.values() {
            for (cdecl, sels, tdecl) in infos {
                ctors.insert(*cdecl);
                test_of.insert(*tdecl, *cdecl);
                for (j, &s) in sels.iter().enumerate() {
                    sel_of.insert(s, (*cdecl, j));
                }
            }
        }
        for (cdecl, sels) in self.records.values() {
            ctors.insert(*cdecl);
            for (j, &s) in sels.iter().enumerate() {
                sel_of.insert(s, (*cdecl, j));
            }
        }
        if sel_of.is_empty() && test_of.is_empty() {
            return root;
        }
        let order = self.m.postorder(root);
        let mut cache: BTreeMap<AstId, AstId> = BTreeMap::new();
        for id in order {
            let folded = match self.m.app(id).cloned() {
                Some(a) => {
                    let args: Vec<AstId> = a.args.iter().map(|c| cache[c]).collect();
                    let arg0 = args.first().and_then(|&x| self.m.app(x).cloned());
                    if let (Some(&cdecl), Some(a0)) = (test_of.get(&a.decl), &arg0)
                        && ctors.contains(&a0.decl)
                    {
                        if a0.decl == cdecl {
                            self.m.mk_true()
                        } else {
                            self.m.mk_false()
                        }
                    } else if let (Some(&(cdecl, j)), Some(a0)) = (sel_of.get(&a.decl), &arg0)
                        && a0.decl == cdecl
                    {
                        a0.args[j]
                    } else {
                        self.m.mk_app(a.decl, &args)
                    }
                }
                None => id,
            };
            cache.insert(id, folded);
        }
        cache[&root]
    }

    /// Trigger *sets* for E-matching. Each returned set is a group of
    /// user-function applications from `body` that jointly contain every bound
    /// variable; matching a set binds all binders. A single application covering
    /// all binders is a one-element set (preferred); otherwise a greedy
    /// multi-trigger set is formed (e.g. `p(x,y)` + `p(y,z)` for a ternary
    /// transitivity binder). Empty if the binders can't be covered.
    fn trigger_sets(
        &self,
        vars: &BTreeSet<AstId>,
        body: AstId,
        user_decls: &BTreeSet<AstId>,
    ) -> Vec<Vec<AstId>> {
        // Candidate trigger applications and the binders each one covers.
        let mut apps: Vec<(AstId, BTreeSet<AstId>)> = Vec::new();
        let mut seen = BTreeSet::new();
        for t in self.m.postorder(body) {
            if self.m.is_app(t) && user_decls.contains(&self.m.app_decl(t)) && seen.insert(t) {
                let covers: BTreeSet<AstId> = self
                    .m
                    .postorder(t)
                    .into_iter()
                    .filter(|x| vars.contains(x))
                    .collect();
                if !covers.is_empty() {
                    apps.push((t, covers));
                }
            }
        }
        // Single triggers that already cover every binder.
        let singles: Vec<Vec<AstId>> = apps
            .iter()
            .filter(|(_, c)| vars.iter().all(|v| c.contains(v)))
            .map(|(t, _)| alloc::vec![*t])
            .collect();
        if !singles.is_empty() {
            return singles;
        }
        // Greedy multi-trigger: repeatedly add the app covering the most
        // still-uncovered binders.
        let mut covered: BTreeSet<AstId> = BTreeSet::new();
        let mut set: Vec<AstId> = Vec::new();
        while !vars.iter().all(|v| covered.contains(v)) {
            let best = apps
                .iter()
                .filter(|(t, _)| !set.contains(t))
                .max_by_key(|(_, c)| c.difference(&covered).count());
            match best {
                Some((t, c)) if c.difference(&covered).count() > 0 => {
                    set.push(*t);
                    covered.extend(c.iter().copied());
                }
                _ => return Vec::new(), // binders cannot be covered by triggers
            }
        }
        alloc::vec![set]
    }

    /// All complete binder substitutions obtained by matching a trigger *set*
    /// against the ground applications in `by_decl`, joining the per-application
    /// partial bindings on their shared variables.
    fn ematch_set(
        &self,
        set: &[AstId],
        vars: &BTreeSet<AstId>,
        by_decl: &BTreeMap<AstId, BTreeSet<AstId>>,
    ) -> Vec<BTreeMap<AstId, AstId>> {
        const CAP: usize = 256;
        let mut acc: Vec<BTreeMap<AstId, AstId>> = alloc::vec![BTreeMap::new()];
        for &trig in set {
            let decl = self.m.app_decl(trig);
            let grounds = match by_decl.get(&decl) {
                Some(g) => g,
                None => return Vec::new(),
            };
            // Partial bindings from matching this trigger alone.
            let mut partials: Vec<BTreeMap<AstId, AstId>> = Vec::new();
            for &g in grounds {
                let mut b = BTreeMap::new();
                if self.ematch(trig, g, vars, &mut b) {
                    partials.push(b);
                }
            }
            // Join with the accumulator, keeping only compatible merges.
            let mut next: Vec<BTreeMap<AstId, AstId>> = Vec::new();
            for a in &acc {
                for p in &partials {
                    if a.iter().all(|(k, v)| p.get(k).is_none_or(|w| w == v)) {
                        let mut m = a.clone();
                        m.extend(p.iter().map(|(&k, &v)| (k, v)));
                        next.push(m);
                        if next.len() >= CAP {
                            break;
                        }
                    }
                }
                if next.len() >= CAP {
                    break;
                }
            }
            acc = next;
            if acc.is_empty() {
                return Vec::new();
            }
        }
        acc.retain(|b| vars.iter().all(|v| b.contains_key(v)));
        acc
    }

    /// Try to match trigger pattern `pat` against ground term `g`, extending
    /// `binding` (bound var → ground term). A non-variable pattern with no bound
    /// variables must equal `g` exactly (terms are hash-consed); a compound
    /// pattern must match `g`'s decl and arguments structurally.
    fn ematch(
        &self,
        pat: AstId,
        g: AstId,
        vars: &BTreeSet<AstId>,
        binding: &mut BTreeMap<AstId, AstId>,
    ) -> bool {
        if vars.contains(&pat) {
            return match binding.get(&pat) {
                Some(&x) => x == g,
                None => {
                    binding.insert(pat, g);
                    true
                }
            };
        }
        if !self.m.postorder(pat).iter().any(|x| vars.contains(x)) {
            return pat == g;
        }
        if self.m.is_app(pat) && self.m.is_app(g) && self.m.app_decl(pat) == self.m.app_decl(g) {
            let pa = self.m.app_args(pat).to_vec();
            let ga = self.m.app_args(g).to_vec();
            return pa.len() == ga.len()
                && pa
                    .iter()
                    .zip(&ga)
                    .all(|(&p, &q)| self.ematch(p, q, vars, binding));
        }
        false
    }

    fn universal_instances(&mut self) -> (Vec<AstId>, bool) {
        if self.universals.is_empty() {
            return (Vec::new(), true);
        }
        const MAX_INSTANCES_PER_UNIVERSAL: usize = 64;
        const MAX_ROUNDS: usize = 8;
        const MAX_TOTAL: usize = 400;
        let universals = self.universals.clone();
        // Set when Phase 2 enumerates a datatype-sorted binder. Such a binder
        // ranges over an infinite constructor domain, so enumerating the *present*
        // ground terms can expose a counterexample (→ unsat) but can never prove
        // the universal for every value — the run is then never "saturated" and a
        // `sat` stays a sound `unknown`. (A recursive *function* over a datatype
        // is handled by E-matching instead and can still saturate.)
        let mut dt_enumerated = false;
        // Set when a universal enumerated in Phase 2 has an infinite arithmetic
        // (Int/Real) binder that occurs inside an arithmetic operation, e.g. the
        // CHC transition `inv(x) ∧ y = x+1 ⇒ inv(y)`. Enumerating only the present
        // ground terms cannot materialise `x+1`, so the fixpoint is *not* captured
        // and a `sat` over the finite instantiation would be unsound — the run is
        // then never "saturated" (a `sat` stays a sound `unknown`). Purely
        // relational finite Datalog (binders only inside predicate applications)
        // is unaffected and still saturates. A recursive *function* over Int
        // (e.g. `fact`) is arithmetic-productive too, but it is seeded by a ground
        // application (`fact(3)`) and E-matching unfolds it to a *terminating*
        // fixpoint — so it is NOT gated here; only universals E-matching never
        // fires on (`ematch_counts == 0`, no ground seed — the CHC case) are.
        let mut arith_enumerated = false;

        // User-function declarations (targets for E-matching triggers) and, per
        // universal, a trigger that covers all its binders (if one exists).
        let user_decls: BTreeSet<AstId> = self.funcs.values().copied().collect();
        let trigs: Vec<Vec<Vec<AstId>>> = universals
            .iter()
            .map(|(vars, body)| {
                let vs: BTreeSet<AstId> = vars.iter().copied().collect();
                self.trigger_sets(&vs, *body, &user_decls)
            })
            .collect();

        // Ground terms by sort, and user-function applications by decl (for
        // E-matching), seeded from the assertions.
        let mut by_sort: BTreeMap<AstId, BTreeSet<AstId>> = BTreeMap::new();
        let mut by_decl: BTreeMap<AstId, BTreeSet<AstId>> = BTreeMap::new();
        for a in self.assertions.clone() {
            for t in self.m.postorder(a) {
                by_sort.entry(self.m.get_sort(t)).or_default().insert(t);
                if self.m.is_app(t) && user_decls.contains(&self.m.app_decl(t)) {
                    by_decl.entry(self.m.app_decl(t)).or_default().insert(t);
                }
            }
        }
        // Ensure every binder sort has at least one ground term (a fresh rep).
        // `seeded_sorts` = those that had *no* real ground term (only the fresh
        // rep): enumerating a universal over such a sort can refute it (a fresh
        // instance is a sound counterexample witness) but cannot *saturate* it —
        // so a `sat` over a seed-only enumeration stays a sound `unknown`.
        let mut seeded_sorts: BTreeSet<AstId> = BTreeSet::new();
        for (vars, _) in &universals {
            for &v in vars {
                let s = self.m.get_sort(v);
                if by_sort.get(&s).is_none_or(BTreeSet::is_empty) {
                    let rep = self.fresh_const(s);
                    by_sort.entry(s).or_default().insert(rep);
                    seeded_sorts.insert(s);
                }
            }
        }
        let mut seed_enumerated = false;

        let mut instances: Vec<AstId> = Vec::new();
        let mut seen: BTreeSet<AstId> = BTreeSet::new();
        let mut ematch_saturated = false;
        // How many instances E-matching produced per universal (a datatype
        // universal whose trigger matched nothing needs enumeration instead).
        let mut ematch_counts = alloc::vec![0usize; universals.len()];
        // Phase 1 — E-matching to a fixpoint: instantiate each universal by
        // matching its trigger against ground applications of the same function,
        // so only *relevant* instances are generated (a recursive/UF universal
        // unfolds its actual argument chain, e.g. fact(3)→fact(2)→…→fact(0),
        // instead of flooding the budget with irrelevant ground combinations).
        for _ in 0..MAX_ROUNDS {
            let mut fresh = false;
            for (ui, (vars, body)) in universals.iter().enumerate() {
                let vs: BTreeSet<AstId> = vars.iter().copied().collect();
                for set in &trigs[ui] {
                    for binding in self.ematch_set(set, &vs, &by_decl) {
                        let subst: Vec<(AstId, AstId)> =
                            vars.iter().map(|&v| (v, binding[&v])).collect();
                        let raw = substitute(&mut self.m, *body, &subst);
                        // Alternate arithmetic/Boolean simplification with
                        // datatype folding so selector/tester chains collapse.
                        let mut inst = crate::rewriter::simplify(&mut self.m, raw);
                        for _ in 0..3 {
                            let folded = self.dt_fold(inst);
                            let next = crate::rewriter::simplify(&mut self.m, folded);
                            if next == inst {
                                break;
                            }
                            inst = next;
                        }
                        if !seen.insert(inst) {
                            continue;
                        }
                        instances.push(inst);
                        ematch_counts[ui] += 1;
                        for t in self.m.postorder(inst) {
                            let s = self.m.get_sort(t);
                            if by_sort.entry(s).or_default().insert(t) {
                                fresh = true;
                            }
                            if self.m.is_app(t) && user_decls.contains(&self.m.app_decl(t)) {
                                by_decl.entry(self.m.app_decl(t)).or_default().insert(t);
                            }
                        }
                        if instances.len() >= MAX_TOTAL {
                            return (instances, false);
                        }
                    }
                }
            }
            if !fresh {
                ematch_saturated = true;
                break; // E-matching fixpoint reached
            }
        }
        // An arithmetic-productive universal that E-matching never fired on (no
        // ground seed) is not genuinely instantiated; enumeration cannot saturate
        // its infinite arithmetic domain, so a `sat` over it would be unsound.
        // This is exactly the CHC-transition case (`inv(x) ∧ y=x+1 ⇒ inv(y)` with
        // no ground `inv` application to seed the chain).
        for (ui, (vars, body)) in universals.iter().enumerate() {
            if ematch_counts[ui] == 0 && self.universal_arith_productive(vars, *body) {
                arith_enumerated = true;
            }
        }
        // Phase 2 — enumerative instantiation over all ground terms: provides the
        // saturation guarantee that makes a `sat` result complete for finite
        // domains / Datalog. Universals that HAVE a covering trigger are left to
        // E-matching (phase 1) — enumerating them over their own function's
        // outputs would spawn irrelevant nested applications (e.g. fact(fact(x)),
        // which is non-linear) that only obscure the goal.
        for _round in 0..MAX_ROUNDS {
            let mut fresh_term = false;
            for (ui, (vars, body)) in universals.iter().enumerate() {
                // Universals with a covering trigger are left to E-matching —
                // EXCEPT a datatype universal whose trigger matched *nothing*
                // (e.g. a selector/tester `hd(x)`/`is_cons(x)` with no ground
                // selector application): enumeration over the ground constructor
                // terms is what reaches the relevant instance (x = cons(-1, nil)).
                // A datatype universal whose E-matching DID fire (a recursive
                // function unfolding on a concrete list) is left to E-matching so
                // it can still saturate.
                let dt_binder = vars
                    .iter()
                    .any(|&v| self.datatypes.contains_key(&self.m.get_sort(v)));
                // Enumerate when there is no covering trigger, when a datatype
                // trigger matched nothing, OR when E-matching produced *no*
                // instance for this universal (a triggered predicate/function with
                // no ground application to seed it — e.g. `∀x. p(x) ∧ ¬p(x)`).
                let enumerate = trigs[ui].is_empty() || ematch_counts[ui] == 0;
                if !enumerate {
                    continue; // handled completely by E-matching
                }
                if dt_binder {
                    dt_enumerated = true; // infinite domain → cannot claim saturation
                }
                // A binder ranging over a seed-only sort makes this a refutation-
                // only enumeration: it cannot prove the universal for every value.
                if vars
                    .iter()
                    .any(|&v| seeded_sorts.contains(&self.m.get_sort(v)))
                {
                    seed_enumerated = true;
                }
                if self.universal_arith_productive(vars, *body) {
                    arith_enumerated = true; // arithmetic recursion → cannot saturate
                }
                let cands: Vec<Vec<AstId>> = vars
                    .iter()
                    .map(|&v| by_sort[&self.m.get_sort(v)].iter().copied().collect())
                    .collect();
                // Bounded cartesian product of the candidate ground terms.
                let mut combos: Vec<Vec<AstId>> = alloc::vec![Vec::new()];
                for c in &cands {
                    let mut next = Vec::new();
                    for combo in &combos {
                        for &g in c {
                            let mut nc = combo.clone();
                            nc.push(g);
                            next.push(nc);
                            if next.len() >= MAX_INSTANCES_PER_UNIVERSAL {
                                break;
                            }
                        }
                        if next.len() >= MAX_INSTANCES_PER_UNIVERSAL {
                            break;
                        }
                    }
                    combos = next;
                }
                for combo in combos {
                    let subst: Vec<(AstId, AstId)> = vars.iter().copied().zip(combo).collect();
                    let raw = substitute(&mut self.m, *body, &subst);
                    // Simplify the instance: constant `ite` conditions and ground
                    // arithmetic fold away, so recursive definitions bottom out
                    // (e.g. `f(0) = ite(0≤0, 0, f(-1))` collapses to `0`) instead
                    // of unfolding without bound.
                    let mut inst = crate::rewriter::simplify(&mut self.m, raw);
                    // Fold datatype selector/tester chains so a constructor
                    // instance collapses (is_cons(cons …)=true, hd(cons a …)=a).
                    for _ in 0..3 {
                        let folded = self.dt_fold(inst);
                        let next = crate::rewriter::simplify(&mut self.m, folded);
                        if next == inst {
                            break;
                        }
                        inst = next;
                    }
                    if !seen.insert(inst) {
                        continue;
                    }
                    instances.push(inst);
                    // Feed the instance's ground terms into the next round.
                    for t in self.m.postorder(inst) {
                        if by_sort.entry(self.m.get_sort(t)).or_default().insert(t) {
                            fresh_term = true;
                        }
                    }
                    if instances.len() >= MAX_TOTAL {
                        return (instances, false); // capped: not saturated
                    }
                }
            }
            if !fresh_term {
                // Enumeration fixpoint; overall completeness also needs the
                // E-matching phase to have reached its own fixpoint AND no
                // infinite-domain (datatype) binder to have been enumerated.
                return (
                    instances,
                    ematch_saturated && !dt_enumerated && !arith_enumerated && !seed_enumerated,
                );
            }
        }
        (instances, false) // ran out of rounds: not saturated
    }

    /// Does `body` have an infinite arithmetic (Int/Real) binder occurring inside
    /// an arithmetic operator (`+`, `-`, `*`, `div`, `mod`, `^`)? Such a binder
    /// can be constrained to values (`x+1`) that enumeration over present ground
    /// terms never materialises, so the enumeration cannot prove saturation.
    fn universal_arith_productive(&self, vars: &[AstId], body: AstId) -> bool {
        let binders: BTreeSet<AstId> = vars
            .iter()
            .copied()
            .filter(|&v| self.m.is_arith_sort(self.m.get_sort(v)))
            .collect();
        if binders.is_empty() {
            return false;
        }
        for t in self.m.postorder(body) {
            let is_arith_op = matches!(
                self.m.arith_op(t),
                Some(
                    ArithOp::Add
                        | ArithOp::Sub
                        | ArithOp::Mul
                        | ArithOp::Uminus
                        | ArithOp::Div
                        | ArithOp::Idiv
                        | ArithOp::Mod
                        | ArithOp::Rem
                        | ArithOp::Power
                )
            );
            if is_arith_op && self.m.postorder(t).iter().any(|s| binders.contains(s)) {
                return true;
            }
        }
        false
    }

    /// Instantiate the array + enum axioms for `lifted` and conjoin them.
    /// Sign axioms for binary product subterms `(* a b)`: a square `(* t t)`
    /// gets `≥ 0` directly, and a general product gets the four sign rules
    /// `(a⋛0 ∧ b⋛0) ⇒ ab⋛0`. Sound over ordered fields, these let the linear
    /// relaxation refute e.g. `x*x < 0` or `x>0 ∧ y>0 ∧ x*y<0` (otherwise a free
    /// variable, answered `unknown`).
    fn square_axioms(&mut self, goal: AstId) -> Vec<AstId> {
        let mut prods: Vec<(AstId, AstId, AstId)> = Vec::new();
        for t in self.m.postorder(goal) {
            if matches!(self.m.arith_op(t), Some(ArithOp::Mul)) {
                let args = self.m.app_args(t);
                if args.len() == 2
                    && self.m.as_numeral(args[0]).is_none()
                    && self.m.as_numeral(args[1]).is_none()
                {
                    prods.push((t, args[0], args[1]));
                }
            }
        }
        prods.sort();
        prods.dedup();
        let mut axioms = Vec::new();
        // Guard against goal blow-up when many products are present.
        if prods.len() > 12 {
            prods.truncate(12);
        }
        for (p, a, b) in prods {
            let is_int = self.m.is_int_sort(self.m.get_sort(p));
            let zero = self.m.mk_numeral(rat(0), is_int);
            let p_nn = self.m.mk_ge(p, zero);
            if a == b {
                axioms.push(p_nn); // a square is nonnegative
                continue;
            }
            // The four sign rules `(a⋛0 ∧ b⋛0) ⇒ ab⋛0`. Non-strict (≤/≥) keeps
            // the case split small; it still refutes any product with the wrong
            // sign (the common goal), while the strict boundary stays `unknown`.
            let p_np = self.m.mk_le(p, zero);
            let (a_nn, a_np) = (self.m.mk_ge(a, zero), self.m.mk_le(a, zero));
            let (b_nn, b_np) = (self.m.mk_ge(b, zero), self.m.mk_le(b, zero));
            for (ca, cb, concl) in [
                (a_nn, b_nn, p_nn),
                (a_np, b_np, p_nn),
                (a_nn, b_np, p_np),
                (a_np, b_nn, p_np),
            ] {
                let hyp = self.m.mk_and(&[ca, cb]);
                axioms.push(self.m.mk_implies(hyp, concl));
            }
        }
        axioms
    }

    /// Euclidean linking axioms for `div`/`mod` by a constant: for each such
    /// term over dividend `a` and constant divisor `n≠0`, assert
    /// `a = n·(a div n) + (a mod n)` and `0 ≤ (a mod n) < |n|`. This ties the
    /// otherwise-opaque `div`/`mod` variables to `a`, so e.g. `x mod 2 = 0 ∧
    /// (x+1) mod 2 = 0` is refuted.
    fn divmod_axioms(&mut self, goal: AstId) -> Vec<AstId> {
        // Distinct (dividend, divisor) pairs of `div`/`mod` applications.
        let mut pairs: Vec<(AstId, AstId)> = Vec::new();
        for t in self.m.postorder(goal) {
            if matches!(self.m.arith_op(t), Some(ArithOp::Mod | ArithOp::Idiv)) {
                let args = self.m.app_args(t);
                pairs.push((args[0], args[1]));
            }
        }
        pairs.sort();
        pairs.dedup();
        if pairs.len() > 12 {
            pairs.truncate(12);
        }
        let mut axioms = Vec::new();
        let zero = self.m.mk_int(0);
        for (a, b) in pairs {
            let divt = self.m.mk_idiv(a, b);
            let modt = self.m.mk_mod(a, b);
            let prod = self.m.mk_mul(&[b, divt]);
            let sum = self.m.mk_add(&[prod, modt]);
            let euclid = self.m.mk_eq(a, sum); // a = b·div + mod
            let mod_ge0 = self.m.mk_ge(modt, zero);
            if let Some(n) = self.m.as_numeral(b).and_then(|r| r.to_integer()) {
                if n.is_zero() {
                    continue; // div/mod by literal 0 is unconstrained in SMT-LIB
                }
                // Constant nonzero divisor: unconditional Euclidean axioms.
                axioms.push(euclid);
                axioms.push(mod_ge0);
                let abs_n = self.m.mk_numeral(Rational::from_integer(n.abs()), true);
                axioms.push(self.m.mk_lt(modt, abs_n)); // mod < |n|
            } else {
                // Symbolic divisor: the Euclidean identity holds only when b ≠ 0
                // (div/mod by 0 are unconstrained). `|b| = ite(b≥0, b, −b)`.
                let bge0 = self.m.mk_ge(b, zero);
                let neg1 = self.m.mk_int(-1);
                let negb = self.m.mk_mul(&[neg1, b]);
                let absb = self.m.mk_ite(bge0, b, negb);
                let mod_lt = self.m.mk_lt(modt, absb); // mod < |b|
                let body = self.m.mk_and(&[euclid, mod_ge0, mod_lt]);
                let beq0 = self.m.mk_eq(b, zero);
                let bne0 = self.m.mk_not(beq0);
                axioms.push(self.m.mk_implies(bne0, body));
            }
        }
        axioms
    }

    fn with_axioms(&mut self, lifted: AstId) -> AstId {
        let mut axioms = self.array_axioms(lifted);
        axioms.extend(self.enum_axioms(lifted));
        axioms.extend(self.record_axioms(lifted));
        axioms.extend(self.datatype_axioms(lifted));
        axioms.extend(self.string_axioms(lifted));
        axioms.extend(self.square_axioms(lifted));
        axioms.extend(self.divmod_axioms(lifted));
        if axioms.is_empty() {
            lifted
        } else {
            axioms.push(lifted);
            self.m.mk_and(&axioms)
        }
    }

    fn goal(&mut self) -> AstId {
        let base = self.conjunction();
        let lifted = self.lift(base);
        self.with_axioms(lifted)
    }

    /// Instantiate the array axioms over the `store`, `select`, and
    /// array-equality terms occurring in `goal`. Read-over-write, for each
    /// `store(a, i, v)`: `select(store(a,i,v), i) = v`, and for other indices `j`
    /// `i = j ∨ select(store(a,i,v), j) = select(a, j)`. Extensionality, for each
    /// array equality `(= a b)`: a fresh Skolem index `k` with
    /// `a = b ∨ select(a, k) ≠ select(b, k)`, with `k` joining the index set so
    /// read-over-write covers it too. This eager instantiation decides ground
    /// (extensional) QF_AX; the congruence closure supplies the rest. It is finite
    /// and terminating.
    fn array_axioms(&mut self, goal: AstId) -> Vec<AstId> {
        let subterms = self.m.postorder(goal);
        let mut stores: Vec<AstId> = Vec::new();
        let mut const_arrays: Vec<AstId> = Vec::new();
        let mut indices: Vec<AstId> = Vec::new();
        let mut seen: BTreeSet<AstId> = BTreeSet::new();
        let mut array_eqs: Vec<(AstId, AstId)> = Vec::new();
        for &t in &subterms {
            if self.m.is_store(t) {
                stores.push(t);
                let idx = self.m.app_args(t)[1];
                if seen.insert(idx) {
                    indices.push(idx);
                }
            } else if self.m.is_select(t) {
                let idx = self.m.app_args(t)[1];
                if seen.insert(idx) {
                    indices.push(idx);
                }
            } else if self.m.is_const_array(t) {
                const_arrays.push(t);
            } else if self.m.is_eq(t) {
                let args = self.m.app_args(t);
                if self.m.is_array_sort(self.m.get_sort(args[0])) {
                    array_eqs.push((args[0], args[1]));
                }
            }
        }
        let mut axioms = Vec::new();
        // Extensionality: introduce a distinguishing index for each array equality.
        for &(a, b) in &array_eqs {
            let (idx_sort, _) = self
                .m
                .array_sort_params(self.m.get_sort(a))
                .expect("array equality over a non-array sort");
            let k = self.fresh_const(idx_sort);
            let eq_ab = self.m.mk_eq(a, b);
            let sel_a = self.m.mk_select(a, k);
            let sel_b = self.m.mk_select(b, k);
            let eq_reads = self.m.mk_eq(sel_a, sel_b);
            let neq_reads = self.m.mk_not(eq_reads);
            axioms.push(self.m.mk_or(&[eq_ab, neq_reads])); // a=b ∨ a[k]≠b[k]
            indices.push(k);
        }
        // Constant array: select(const(v), j) = v for every index j (including
        // the extensionality Skolems).
        for &ca in &const_arrays {
            let v = self.m.app_args(ca)[0];
            for &j in &indices {
                let sel = self.m.mk_select(ca, j);
                let ax = self.m.mk_eq(sel, v);
                axioms.push(ax);
            }
        }
        for &st in &stores {
            let args = self.m.app_args(st).to_vec(); // [a, i, v]
            let (a, i, v) = (args[0], args[1], args[2]);
            let sel_i = self.m.mk_select(st, i);
            let row1 = self.m.mk_eq(sel_i, v);
            axioms.push(row1);
            for &j in &indices {
                if j == i {
                    continue;
                }
                let eq_ij = self.m.mk_eq(i, j);
                let sel_st_j = self.m.mk_select(st, j);
                let sel_a_j = self.m.mk_select(a, j);
                let eq_reads = self.m.mk_eq(sel_st_j, sel_a_j);
                let row2 = self.m.mk_or(&[eq_ij, eq_reads]);
                axioms.push(row2);
            }
        }
        axioms
    }

    /// The conjunction of all assertions (`true` if none).
    fn conjunction(&mut self) -> AstId {
        match self.assertions.len() {
            0 => self.m.mk_true(),
            1 => self.assertions[0],
            _ => {
                let a = self.assertions.clone();
                self.m.mk_and(&a)
            }
        }
    }

    /// Decide `goal`, capping a `sat` verdict to `unknown` when the formula
    /// contains genuine nonlinear arithmetic the linear core over-approximates
    /// (so a definite `sat`/`unsat` is always sound).
    /// Eliminate `bv2int(a)` when the bit-vector `a` is consumed *only* by
    /// `bv2int` (never in a bit-vector operation): replace it with a fresh
    /// integer bounded to `[0, 2ⁿ−1]`. This is a sound bijection (the value
    /// exists iff an integer in range does), and it removes the bit-vector so a
    /// goal that was only mixed via `bv2int` becomes pure integer and decidable.
    fn eliminate_pure_bv2int(&mut self, goal: AstId) -> AstId {
        let sub = self.m.postorder(goal);
        let mut apps: Vec<(AstId, AstId)> = Vec::new(); // (bv2int(a), a)
        let mut impure: BTreeSet<AstId> = BTreeSet::new();
        for &t in &sub {
            if !self.m.is_app(t) {
                continue;
            }
            let args = self.m.app_args(t).to_vec();
            let is_b2i = args.len() == 1
                && matches!(
                    self.decl_name(self.m.app_decl(t)).as_deref(),
                    Some("bv2int" | "bv2nat" | "ubv_to_int")
                );
            for &arg in &args {
                if self.m.bv_sort_width(self.m.get_sort(arg)).is_some() {
                    // Only a free bit-vector *leaf* (a variable) may be replaced by
                    // an unconstrained bounded integer. A compound argument such as
                    // `int2bv(x)` carries a value (x mod 2ⁿ) a free integer would
                    // not, so eliminating it would be unsound.
                    let is_leaf = !self.m.is_app(arg) || self.m.app_args(arg).is_empty();
                    if is_b2i && is_leaf {
                        apps.push((t, arg));
                    } else if !is_b2i {
                        impure.insert(arg);
                    }
                }
            }
        }
        let int = self.m.mk_int_sort();
        let mut subst: Vec<(AstId, AstId)> = Vec::new();
        let mut ranges: Vec<AstId> = Vec::new();
        let mut assigned: BTreeMap<AstId, AstId> = BTreeMap::new();
        for (app, a) in apps {
            if impure.contains(&a) {
                continue;
            }
            let w = match self.m.bv_sort_width(self.m.get_sort(a)) {
                Some(w) if w <= 32 => w,
                _ => continue,
            };
            let n = if let Some(&n) = assigned.get(&a) {
                n
            } else {
                let n = self.fresh_const(int);
                assigned.insert(a, n);
                let zero = self.m.mk_int(0);
                let ub = self.m.mk_int((1i64 << w) - 1);
                let lo = self.m.mk_le(zero, n);
                let hi = self.m.mk_le(n, ub);
                ranges.push(lo);
                ranges.push(hi);
                n
            };
            subst.push((app, n));
        }
        if subst.is_empty() {
            return goal;
        }
        let g2 = crate::rewriter::substitute(&mut self.m, goal, &subst);
        ranges.push(g2);
        self.m.mk_and(&ranges)
    }

    fn decide(&mut self, goal: AstId) -> (SmtResult, Option<Model>) {
        let goal = self.eliminate_pure_bv2int(goal);
        // Inline `v = <ground constructor>` so selectors/testers over `v` fold.
        let goal = self.inline_ground_dt_bindings(goal);
        // Cyclic datatype equalities among variables (`p = cons(0,q) ∧
        // q = cons(0,p)`) are UNSAT by acyclicity — caught structurally here since
        // the depth axioms miss multi-variable cycles.
        if self.datatype_occurs_unsat(goal) {
            return (SmtResult::Unsat, None);
        }
        // Array extensionality: `a ≠ b ∧ ∀i. a[i] = b[i]` is UNSAT.
        if self.extensionality_unsat(goal) {
            return (SmtResult::Unsat, None);
        }
        // Quantified formulas are not decided here (the instantiation engine ran
        // upstream); a residual quantifier sentinel ⇒ sound `unknown`.
        if !self.quant_atoms.is_empty()
            && self
                .m
                .postorder(goal)
                .iter()
                .any(|t| self.quant_atoms.contains(t))
        {
            return (SmtResult::Unknown, None);
        }
        // Symbolic string operations are opaque uninterpreted markers: a `sat`
        // over them may be spurious (the marker can take a value inconsistent with
        // string semantics), so a `sat` stays `unknown` — but an `unsat` derived
        // together with the sound string axioms (length links, literal lengths) is
        // a real `unsat`. So don't gate up front; check, then gate only `sat`.
        // A "functional" array constant — `(_ map f)`, `(_ as-array f)`, or a
        // `(lambda …)` — is only given semantics for *explicit* `select`s of it
        // (rewritten to `f(select …)` / `f(i)` / the beta-reduced body). If such a
        // constant survives into the goal — e.g. used in an array equality
        // `(_ as-array f) = b`, inside a `store`, or as an array-of-arrays element —
        // its pointwise definition is not enforced, so a `sat` could be wrong;
        // gate to a sound `unknown`.
        if !self.maps.is_empty() || !self.as_arrays.is_empty() || !self.lambdas.is_empty() {
            let functional: BTreeSet<AstId> = self
                .maps
                .keys()
                .chain(self.as_arrays.keys())
                .chain(self.lambdas.keys())
                .copied()
                .collect();
            if self
                .m
                .postorder(goal)
                .iter()
                .any(|t| functional.contains(t))
            {
                return (SmtResult::Unknown, None);
            }
        }
        let has_symbolic_str = !self.str_symbolic.is_empty()
            && self
                .m
                .postorder(goal)
                .iter()
                .any(|t| self.str_symbolic.contains(t));
        if has_symbolic_str {
            let (res0, model0) = check_model(&self.m, goal);
            if res0 == SmtResult::Unsat {
                return (SmtResult::Unsat, None);
            }
            let wg = self.witness_base.unwrap_or(goal);
            // The abstract model may already pin every string variable to a
            // literal (e.g. a concat-vs-literal split forces `x="ab", y="cd"`);
            // verify that concrete assignment directly — it confirms `sat` without
            // an exponential candidate search.
            if let Some(mut model) = model0
                && let Some(m) = self.verify_string_model(wg, &mut model)
            {
                return (SmtResult::Sat, Some(m));
            }
            // Otherwise search for a concrete satisfying string/seq model, from the
            // pre-axiom formula (its axioms fold cleanly under substitution).
            if let Some(m) = self.try_string_witness(wg) {
                return (SmtResult::Sat, Some(m));
            }
            if let Some(m) = self.try_seq_witness(wg) {
                return (SmtResult::Sat, Some(m));
            }
            return (SmtResult::Unknown, None);
        }
        // Bit-vector formulas are decided by bit-blasting (no model produced yet).
        // The bit-blaster handles only pure QF_BV; a goal mixing bit-vectors with
        // uninterpreted, array, or arithmetic terms is not combined yet, so return
        // a sound `unknown` rather than a possibly-wrong verdict.
        if self.is_bv_goal(goal) {
            // A free array read `(select m i)` of bit-vector sort (m a free array
            // constant read once, otherwise unconstrained) is an unconstrained
            // bit-vector — replace it by a fresh bit-vector constant so an
            // otherwise-pure goal like `select m i = i+1 ∧ select m i = 0`
            // bit-blasts. Sound: a free array can realise any read value.
            let mut g = goal;
            if !self.bv_goal_is_pure(goal) {
                let groups = self.free_array_read_groups(goal);
                let mut subst: Vec<(AstId, AstId)> = Vec::new();
                let mut axioms: Vec<AstId> = Vec::new();
                for terms in groups {
                    // Multi-read groups need read-over-read congruence, which is
                    // only expressible in pure bit-vectors when the indices are
                    // themselves bit-vectors; otherwise skip the group.
                    let bv_idx = terms.iter().all(|&t| {
                        self.m
                            .bv_sort_width(self.m.get_sort(self.m.app_args(t)[1]))
                            .is_some()
                    });
                    if terms.len() > 1 && !bv_idx {
                        continue;
                    }
                    let fresh: Vec<AstId> = terms
                        .iter()
                        .map(|&r| self.fresh_const(self.m.get_sort(r)))
                        .collect();
                    for (a, b) in
                        (0..terms.len()).flat_map(|i| (i + 1..terms.len()).map(move |j| (i, j)))
                    {
                        let idx_eq = self
                            .m
                            .mk_eq(self.m.app_args(terms[a])[1], self.m.app_args(terms[b])[1]);
                        let val_eq = self.m.mk_eq(fresh[a], fresh[b]);
                        axioms.push(self.m.mk_implies(idx_eq, val_eq));
                    }
                    for (r, f) in terms.iter().zip(fresh.iter()) {
                        subst.push((*r, *f));
                    }
                }
                if !subst.is_empty() {
                    g = crate::rewriter::substitute(&mut self.m, goal, &subst);
                    if !axioms.is_empty() {
                        axioms.push(g);
                        g = self.m.mk_and(&axioms);
                    }
                }
            }
            if self.bv_goal_is_pure(g) {
                let (res, bv) = check_bv_model(&self.m, g);
                return (res, bv.map(Model::from_bv));
            }
            return (SmtResult::Unknown, None);
        }
        // Arrays indexed by a *symbolic* Bool need the index's 2-valuedness: decide
        // by case-splitting the Bool index variables (`true`/`false`), which makes
        // every index constant and reduces to plain congruence reads.
        if self.has_bool_indexed_array(goal) {
            return self.decide_bool_array(goal);
        }
        let (res, model) = check_model(&self.m, goal);
        // SAT witness for symbolic-divisor div/mod goals: a small concrete divisor
        // often makes the goal linear and satisfiable (e.g. `mod(35,y)≥1 ∧ y<6`
        // at y=2). A confirmed linear model is a real `sat` — and `check_model`'s
        // own `sat` on the still-nonlinear `y·q` is not trustworthy, so try the
        // witness whenever the verdict is not a sound `unsat`.
        if res != SmtResult::Unsat
            && !self.symbolic_divisors.is_empty()
            && self
                .m
                .postorder(goal)
                .iter()
                .any(|t| self.symbolic_divisors.contains(t))
        {
            if let Some(m) = self.try_divmod_witness(goal) {
                return (SmtResult::Sat, Some(m));
            }
            // No witness: for the constant-dividend single-divisor class the
            // witness search is *complete*, so a proven-exhaustive failure is a
            // sound `unsat` (e.g. `div(31,y) < −4 ∧ y > 2`).
            if self.divmod_complete_unsat(goal) {
                return (SmtResult::Unsat, None);
            }
        }
        if res == SmtResult::Sat && self.arith_nonlinear(goal) {
            // First, try to *linearize*: a variable pinned by an equality
            // `x = c` (constant) can be substituted throughout, which often
            // turns a nonlinear product like `x*y` into the linear `c*y`. If the
            // residual is fully linear the ordinary engine decides it soundly,
            // producing a real verdict (and model) instead of `unknown`.
            let lin = self.linearize_fixed_vars(goal);
            if lin != goal && !self.arith_nonlinear(lin) {
                return check_model(&self.m, lin);
            }
            // A genuinely nonlinear residual in a *single* variable is decided
            // exactly by the univariate procedure (real-root isolation over the
            // reals; integer-root enumeration over the integers) — this is a
            // complete decision for that fragment, matching z3.
            // Polynomial-level decision: eliminate linearly-determined variables,
            // then decide the residual exactly (univariate CAD, or exhaustive
            // search over a bounded integer box). Complete for those fragments.
            if let Some(r) = self.decide_nonlinear_definite(lin) {
                return (r, None);
            }
            // Otherwise, interval constraint propagation over the *actual*
            // polynomials may still prove the (multivariate) system
            // unsatisfiable; that refutation is sound.
            if self.nonlinear_icp_refutes(lin) {
                (SmtResult::Unsat, None)
            } else {
                (SmtResult::Unknown, None)
            }
        } else {
            (res, model)
        }
    }

    /// Repeatedly substitute every variable that a top-level equality pins to a
    /// numeral constant (`x = c` / `c = x`) and re-simplify, to a fixpoint. This
    /// linearizes nonlinear terms whose non-constant factors become constant
    /// (e.g. `x*y` with `x = 2` → `2*y`). Sound: each substitution is entailed
    /// by the goal, so the result is equisatisfiable.
    fn linearize_fixed_vars(&mut self, goal: AstId) -> AstId {
        let mut g = goal;
        for _ in 0..16 {
            let mut conjuncts = Vec::new();
            self.icp_flatten_and(g, &mut conjuncts);
            let mut subst: Option<(AstId, AstId)> = None;
            'find: for &c in &conjuncts {
                if !self.m.is_eq(c) {
                    continue;
                }
                let args = self.m.app_args(c);
                if args.len() != 2 {
                    continue;
                }
                for (a, b) in [(args[0], args[1]), (args[1], args[0])] {
                    // Substitute a variable `a` determined by `a = b`, provided
                    // `a` is a free uninterpreted constant that does not itself
                    // occur in `b` (occurs-check, so the substitution terminates
                    // and stays equisatisfiable). This linearizes `x*y` under
                    // `y = x+1` just as it does under `x = 2`.
                    //
                    // Soundness for **integers**: substituting an `Int` variable
                    // by a general expression can drop its integrality (e.g.
                    // `y = x − 6` with `x` Real forces `x − 6 ∈ ℤ`, lost if `y`
                    // is eliminated). So an `Int` variable is only substituted by
                    // a numeral here; the general integer/real case is handled
                    // soundly by the polynomial-level elimination downstream.
                    let a_is_int = self.m.is_int_sort(self.m.get_sort(a));
                    let safe = self.m.as_numeral(b).is_some() || !a_is_int;
                    if a != b
                        && self.m.is_uninterp_const(a)
                        && self.m.is_arith_sort(self.m.get_sort(a))
                        && safe
                        && !self.term_contains(b, a)
                    {
                        subst = Some((a, b));
                        break 'find;
                    }
                }
            }
            let Some((from, to)) = subst else { break };
            let ng = substitute(&mut self.m, g, &[(from, to)]);
            let ng = crate::rewriter::simplify(&mut self.m, ng);
            if ng == g {
                break;
            }
            g = ng;
        }
        g
    }

    /// Does `sub` occur anywhere within `term`?
    fn term_contains(&self, term: AstId, sub: AstId) -> bool {
        self.m.postorder(term).contains(&sub)
    }

    /// Try to decide a nonlinear goal definitely (sat **or** unsat). Extracts the
    /// polynomial constraints, eliminates linearly-determined variables
    /// (soundly, per the integer/real rule), then decides the residual: a single
    /// variable by the univariate real/integer procedure, or an all-integer
    /// finitely-bounded system by exhaustive search. Returns `None` (fall back to
    /// the refutation-only ICP path) when the goal is not of a decidable shape.
    ///
    /// Every variable must be a genuine *free* uninterpreted constant: an opaque
    /// compound term (`(^ 2.0 0.5)` = √2, `(f x)`) has a determined value, so
    /// treating it as free would make a `sat` claim unsound.
    /// The `(select a i)` terms in `goal` that may be treated as free nonlinear
    /// variables: `a` is a free array constant, is read exactly once, and never
    /// appears except as a select's array argument (so it is not a store target,
    /// not equated to another array — the read is genuinely unconstrained). Sound
    /// for both directions: a free array can realise any value at the read.
    fn free_array_reads(&self, goal: AstId) -> BTreeSet<AstId> {
        let mut reads: BTreeMap<AstId, BTreeSet<AstId>> = BTreeMap::new();
        let mut tainted: BTreeSet<AstId> = BTreeSet::new();
        for t in self.m.postorder(goal) {
            if self.m.is_select(t) {
                reads.entry(self.m.app_args(t)[0]).or_default().insert(t);
            }
            // Taint any array-sorted term used other than as a select's array arg.
            for &a in self.m.app_args(t) {
                if self.m.is_array_sort(self.m.get_sort(a))
                    && !(self.m.is_select(t) && self.m.app_args(t)[0] == a)
                {
                    tainted.insert(a);
                }
            }
        }
        let mut out = BTreeSet::new();
        for (arr, terms) in reads {
            if self.m.is_uninterp_const(arr) && !tainted.contains(&arr) && terms.len() == 1 {
                out.extend(terms);
            }
        }
        out
    }

    /// Groups of `(select a i)` reads by their free, untainted array `a` (a free
    /// constant used only as a select argument). Unlike [`Self::free_array_reads`]
    /// this keeps *all* reads of an array together, so a caller can add the
    /// read-over-read congruence `(i = j) → (read_i = read_j)` when replacing them
    /// by fresh variables.
    fn free_array_read_groups(&self, goal: AstId) -> Vec<Vec<AstId>> {
        let mut reads: BTreeMap<AstId, Vec<AstId>> = BTreeMap::new();
        let mut tainted: BTreeSet<AstId> = BTreeSet::new();
        for t in self.m.postorder(goal) {
            if self.m.is_select(t) {
                let bucket = reads.entry(self.m.app_args(t)[0]).or_default();
                if !bucket.contains(&t) {
                    bucket.push(t);
                }
            }
            for &a in self.m.app_args(t) {
                if self.m.is_array_sort(self.m.get_sort(a))
                    && !(self.m.is_select(t) && self.m.app_args(t)[0] == a)
                {
                    tainted.insert(a);
                }
            }
        }
        reads
            .into_iter()
            .filter(|(arr, _)| self.m.is_uninterp_const(*arr) && !tainted.contains(arr))
            .map(|(_, terms)| terms)
            .collect()
    }

    fn decide_nonlinear_definite(&self, goal: AstId) -> Option<SmtResult> {
        use crate::nlsat::{Constraint, Rel};
        let mut conjuncts = Vec::new();
        self.icp_flatten_and(goal, &mut conjuncts);
        let mut var_map: BTreeMap<AstId, u32> = BTreeMap::new();
        let mut constraints: Vec<(crate::math::polynomial::Polynomial, Rel)> = Vec::new();
        for atom in conjuncts {
            let (negated, a) = if self.m.is_not(atom) {
                (true, self.m.app_args(atom)[0])
            } else {
                (false, atom)
            };
            if let Some(c) = self.icp_atom(a, negated, &mut var_map) {
                constraints.push((c.poly, c.rel));
            }
        }
        if var_map.is_empty() || constraints.is_empty() {
            return None;
        }
        // `int_of[idx]` = is this variable integer-sorted? Each must be a free
        // uninterpreted constant, or a *free read* `(select a i)` whose array is a
        // free constant read exactly once (so the read is unconstrained — sound to
        // treat as an independent variable in both directions).
        let free_reads = self.free_array_reads(goal);
        let mut int_of: BTreeMap<u32, bool> = BTreeMap::new();
        for (&ast, &idx) in &var_map {
            if !self.m.is_uninterp_const(ast) && !free_reads.contains(&ast) {
                return None;
            }
            int_of.insert(idx, self.m.is_int_sort(self.m.get_sort(ast)));
        }
        let all_int = int_of.values().all(|&b| b);

        // Eliminate linearly-determined variables. Integer variables are only
        // eliminated in a pure-integer system with a unit coefficient, so the
        // substituted value stays integral (soundness).
        let reduced0 = crate::nlsat::elim::eliminate_linear(constraints, |v, c| {
            if *int_of.get(&v).unwrap_or(&false) {
                all_int && (c.is_one() || c.is_minus_one())
            } else {
                true
            }
        });
        let (reduced, orig_vars) = crate::nlsat::elim::remap_vars(&reduced0);
        let k = orig_vars.len();
        let remaining_int: Vec<bool> = orig_vars
            .iter()
            .map(|v| *int_of.get(v).unwrap_or(&false))
            .collect();

        let verdict = if k <= 1 {
            let is_int = remaining_int.first().copied().unwrap_or(true);
            if is_int {
                crate::nlsat::univariate::decide_int(&reduced, 0)
            } else {
                crate::nlsat::univariate::decide(&reduced, 0)
            }
        } else if remaining_int.iter().all(|&b| b) {
            let cons: Vec<Constraint> = reduced
                .iter()
                .map(|(p, r)| Constraint::new(p.clone(), *r))
                .collect();
            crate::nlsat::icp::decide_bounded_int(&cons, k)
        } else {
            None
        };
        if let Some(b) = verdict {
            return Some(if b { SmtResult::Sat } else { SmtResult::Unsat });
        }
        // Multivariate residual not otherwise decided. If it is over the reals
        // (no integer variables — CAD decides ℝ, not ℤ), invoke the complete CAD
        // decision procedure; it returns a definite verdict or declines soundly.
        if k >= 2 && remaining_int.iter().all(|&b| !b) {
            match crate::nlsat::cad::cad_sat(&reduced, k) {
                Some(true) => return Some(SmtResult::Sat),
                Some(false) => return Some(SmtResult::Unsat),
                None => {}
            }
        }
        // Otherwise, try to *prove sat* by fixing all-but-one variable to
        // candidate values and deciding the last univariately (a verified
        // witness — sound).
        if k >= 2 && crate::nlsat::elim::sat_by_fixing(&reduced, &remaining_int) {
            return Some(SmtResult::Sat);
        }
        None
    }

    /// Try to refute a (nonlinear) goal by interval constraint propagation over
    /// its top-level conjunctive arithmetic atoms. Sound: returns `true` only on
    /// a genuine interval proof of unsatisfiability, so it may only strengthen an
    /// `unknown` into `unsat`.
    fn nonlinear_icp_refutes(&self, goal: AstId) -> bool {
        let mut conjuncts = Vec::new();
        self.icp_flatten_and(goal, &mut conjuncts);
        let mut var_map: BTreeMap<AstId, u32> = BTreeMap::new();
        let mut constraints: Vec<crate::nlsat::Constraint> = Vec::new();
        for atom in conjuncts {
            let (negated, a) = if self.m.is_not(atom) {
                (true, self.m.app_args(atom)[0])
            } else {
                (false, atom)
            };
            if let Some(c) = self.icp_atom(a, negated, &mut var_map) {
                constraints.push(c);
            }
        }
        if constraints.is_empty() {
            return false;
        }
        crate::nlsat::refute(&constraints, var_map.len())
    }

    /// Flatten a nest of top-level `(and …)` into its conjuncts.
    fn icp_flatten_and(&self, f: AstId, out: &mut Vec<AstId>) {
        if self.m.is_and(f) {
            for &c in self.m.app_args(f) {
                self.icp_flatten_and(c, out);
            }
        } else {
            out.push(f);
        }
    }

    /// Convert one (possibly negated) arithmetic atom into an ICP constraint
    /// `poly REL 0`, or `None` if it is not an arithmetic comparison/equality.
    fn icp_atom(
        &self,
        atom: AstId,
        negated: bool,
        var_map: &mut BTreeMap<AstId, u32>,
    ) -> Option<crate::nlsat::Constraint> {
        use crate::nlsat::Rel as NRel;
        let args = self.m.app(atom)?.args.clone();
        if args.len() != 2 {
            return None;
        }
        let rel = if let Some(op) = self.m.arith_op(atom) {
            match op {
                ArithOp::Lt => NRel::Lt,
                ArithOp::Le => NRel::Le,
                ArithOp::Gt => NRel::Gt,
                ArithOp::Ge => NRel::Ge,
                _ => return None,
            }
        } else if self.m.is_eq(atom) && self.m.is_arith_sort(self.m.get_sort(args[0])) {
            NRel::Eq
        } else {
            return None;
        };
        let lhs = self.icp_to_poly(args[0], var_map);
        let rhs = self.icp_to_poly(args[1], var_map);
        let poly = lhs.sub(&rhs);
        let rel = if negated {
            match rel {
                NRel::Lt => NRel::Ge,
                NRel::Le => NRel::Gt,
                NRel::Gt => NRel::Le,
                NRel::Ge => NRel::Lt,
                NRel::Eq => NRel::Ne,
                NRel::Ne => NRel::Eq,
            }
        } else {
            rel
        };
        Some(crate::nlsat::Constraint::new(poly, rel))
    }

    /// Convert an arithmetic term to a [`Polynomial`], mapping each opaque
    /// arith-sorted subterm to a fresh variable keyed by its `AstId`. Any term we
    /// cannot decompose becomes a free variable — sound for refutation, since it
    /// only *enlarges* the value set ICP reasons over.
    fn icp_to_poly(
        &self,
        t: AstId,
        var_map: &mut BTreeMap<AstId, u32>,
    ) -> crate::math::polynomial::Polynomial {
        use crate::math::polynomial::Polynomial;
        if let Some(n) = self.m.as_numeral(t) {
            return Polynomial::constant(n);
        }
        if let Some(op) = self.m.arith_op(t) {
            let args = self.m.app_args(t);
            match op {
                ArithOp::Add => {
                    let mut acc = Polynomial::zero();
                    for &a in args {
                        acc = acc.add(&self.icp_to_poly(a, var_map));
                    }
                    return acc;
                }
                ArithOp::Sub if !args.is_empty() => {
                    let mut acc = self.icp_to_poly(args[0], var_map);
                    if args.len() == 1 {
                        return acc.neg();
                    }
                    for &a in &args[1..] {
                        acc = acc.sub(&self.icp_to_poly(a, var_map));
                    }
                    return acc;
                }
                ArithOp::Uminus if args.len() == 1 => {
                    return self.icp_to_poly(args[0], var_map).neg();
                }
                ArithOp::Mul => {
                    let mut acc = Polynomial::constant(Rational::from_integer(1.into()));
                    for &a in args {
                        acc = acc.mul(&self.icp_to_poly(a, var_map));
                    }
                    return acc;
                }
                ArithOp::Power if args.len() == 2 => {
                    if let Some(e) = self.m.as_numeral(args[1])
                        && e.is_integer()
                        && !e.is_negative()
                        && let Some(ei) = e.to_i64()
                        && ei <= 8
                    {
                        return self.icp_to_poly(args[0], var_map).pow(ei as u32);
                    }
                    // Non-constant / large exponent: fall through to a fresh var.
                }
                ArithOp::ToReal if args.len() == 1 => {
                    return self.icp_to_poly(args[0], var_map);
                }
                _ => {} // Div / Mod / Idiv / Abs / … → opaque variable below.
            }
        }
        // Opaque arith-sorted term → a fresh variable (consistent per AstId).
        let idx = var_map.len() as u32;
        let v = *var_map.entry(t).or_insert(idx);
        Polynomial::var(v)
    }

    /// Does `goal` contain a `select`/`store` over an array whose index sort is
    /// `Bool`? (An unsupported corner needing boolean-value index reasoning.)
    /// Decide a goal with symbolic-Bool-indexed arrays by exhaustively splitting
    /// the Bool index variables into `true`/`false`: each branch has only constant
    /// indices (plain congruence). `sat` on any branch is `sat`; all `unsat` is
    /// `unsat`; any undecided branch keeps a sound `unknown`.
    fn decide_bool_array(&mut self, goal: AstId) -> (SmtResult, Option<Model>) {
        let mut bvars: Vec<AstId> = Vec::new();
        for t in self.m.postorder(goal) {
            if (self.m.is_select(t) || self.m.is_store(t))
                && self
                    .m
                    .array_sort_params(self.m.get_sort(self.m.app_args(t)[0]))
                    .is_some_and(|(i, _)| self.m.is_bool_sort(i))
            {
                let idx = self.m.app_args(t)[1];
                for u in self.m.postorder(idx) {
                    if self.m.is_app(u)
                        && self.m.app_args(u).is_empty()
                        && self.m.is_bool_sort(self.m.get_sort(u))
                        && !self.m.is_true(u)
                        && !self.m.is_false(u)
                        && !bvars.contains(&u)
                    {
                        bvars.push(u);
                    }
                }
            }
        }
        if bvars.is_empty() || bvars.len() > 4 {
            return (SmtResult::Unknown, None);
        }
        let n = bvars.len();
        let mut any_unknown = false;
        for mask in 0..(1u32 << n) {
            let subst: Vec<(AstId, AstId)> = bvars
                .iter()
                .enumerate()
                .map(|(i, &v)| {
                    let b = if (mask >> i) & 1 == 1 {
                        self.m.mk_true()
                    } else {
                        self.m.mk_false()
                    };
                    (v, b)
                })
                .collect();
            let g = crate::rewriter::substitute(&mut self.m, goal, &subst);
            let g = crate::rewriter::simplify(&mut self.m, g);
            match self.decide(g) {
                (SmtResult::Sat, m) => return (SmtResult::Sat, m),
                (SmtResult::Unknown, _) => any_unknown = true,
                (SmtResult::Unsat, _) => {}
            }
        }
        if any_unknown {
            (SmtResult::Unknown, None)
        } else {
            (SmtResult::Unsat, None)
        }
    }

    fn has_bool_indexed_array(&self, goal: AstId) -> bool {
        self.m.postorder(goal).iter().any(|&t| {
            (self.m.is_select(t) || self.m.is_store(t))
                && self
                    .m
                    .array_sort_params(self.m.get_sort(self.m.app_args(t)[0]))
                    .is_some_and(|(idx, _)| self.m.is_bool_sort(idx))
                && {
                    // A *symbolic* Bool index needs 2-valuedness reasoning (which
                    // the core solver does not do soundly for the resulting ites);
                    // a constant `true`/`false` index is a plain congruence read.
                    let index = self.m.app_args(t)[1];
                    !(self.m.is_true(index) || self.m.is_false(index))
                }
        })
    }

    /// Does `goal` mention any bit-vector-sorted term?
    fn is_bv_goal(&self, goal: AstId) -> bool {
        self.m
            .postorder(goal)
            .iter()
            .any(|&t| self.m.bv_sort_width(self.m.get_sort(t)).is_some())
    }

    /// Is `goal` decidable by the bit-blaster alone — every term bit-vector- or
    /// Boolean-sorted, and no *uninterpreted function application* (which the
    /// bit-blaster cannot give congruence)? Uninterpreted 0-ary constants are
    /// fine (they act as free bit-vector variables).
    fn bv_goal_is_pure(&self, goal: AstId) -> bool {
        self.m.postorder(goal).iter().all(|&t| {
            let s = self.m.get_sort(t);
            if self.m.bv_sort_width(s).is_none() && !self.m.is_bool_sort(s) {
                return false; // an uninterpreted/array/arithmetic-sorted term
            }
            // Reject applications of uninterpreted functions (null family, arity ≥ 1).
            if let Some(app) = self.m.app(t)
                && !app.args.is_empty()
                && let Some(fd) = self.m.func_decl(app.decl)
                && fd.info.family_id == crate::ast::NULL_FAMILY_ID
            {
                return false;
            }
            true
        })
    }

    /// Does `goal` contain nonlinear arithmetic the linear solver treats as an
    /// unconstrained variable (a product of two non-constants, a non-constant
    /// divisor, or a power)? Such terms make a `sat` verdict unsound.
    fn arith_nonlinear(&self, goal: AstId) -> bool {
        for t in self.m.postorder(goal) {
            // The exponentiation fallback for a non-constant base or non-integer
            // exponent is an opaque UF named "^" — unconstrained, so treat it as
            // nonlinear (a `sat` over it would be unsound).
            if self.m.is_app(t) && self.decl_name(self.m.app_decl(t)).as_deref() == Some("^") {
                return true;
            }
            let Some(op) = self.m.arith_op(t) else {
                continue;
            };
            let args = self.m.app_args(t);
            let nonconst = |a: &AstId| self.m.as_numeral(*a).is_none();
            match op {
                ArithOp::Mul if args.iter().filter(|a| nonconst(a)).count() >= 2 => return true,
                ArithOp::Div | ArithOp::Idiv | ArithOp::Mod | ArithOp::Rem
                    if nonconst(&args[1]) =>
                {
                    return true;
                }
                ArithOp::Power => return true,
                _ => {}
            }
        }
        false
    }

    /// Decide a subset of the current assertions (by index).
    fn check_subset(&mut self, keep: &[bool]) -> SmtResult {
        let subset: Vec<AstId> = self
            .assertions
            .iter()
            .zip(keep)
            .filter_map(|(&a, &k)| k.then_some(a))
            .collect();
        let base = match subset.len() {
            0 => self.m.mk_true(),
            1 => subset[0],
            _ => self.m.mk_and(&subset),
        };
        let goal = self.lift(base);
        self.decide(goal).0
    }

    /// `(get-unsat-core)` — the `:named` assertions in a minimal unsatisfiable
    /// core of the last (unsatisfiable) check. Computed by deletion-based
    /// minimization: drop each named assertion; keep it only if the remainder is
    /// still unsatisfiable. Unnamed assertions are always retained.
    /// `(get-proof)` — z3rs emits a lightweight *unsatisfiability certificate*
    /// (the minimal named unsat core) rather than a full z3-format resolution
    /// proof-term (a follow-on). The core is checkable: asserting exactly it is
    /// still `unsat`.
    fn get_proof(&mut self) -> Result<String, String> {
        if self.last_verdict != Some(SmtResult::Unsat) {
            return Err("get-proof requires a preceding unsatisfiable check-sat".to_string());
        }
        if self.assert_names.iter().any(|n| n.is_some()) {
            let core = self.get_unsat_core()?;
            Ok(alloc::format!("(proof (unsat-core {core}))"))
        } else {
            // No named assertions to reference; certify unsatisfiability directly.
            Ok("(proof (unsat))".to_string())
        }
    }

    fn get_unsat_core(&mut self) -> Result<String, String> {
        if self.last_verdict != Some(SmtResult::Unsat) {
            return Err("get-unsat-core requires a preceding unsatisfiable check-sat".to_string());
        }
        let n = self.assertions.len();
        let mut keep = alloc::vec![true; n];
        for i in 0..n {
            if self.assert_names[i].is_none() {
                continue; // unnamed assertions are not core candidates
            }
            keep[i] = false;
            // Keep the assertion unless the remainder is *still* unsatisfiable.
            if self.check_subset(&keep) != SmtResult::Unsat {
                keep[i] = true;
            }
        }
        let mut names = Vec::new();
        for (k, label) in keep.iter().zip(&self.assert_names) {
            if *k && let Some(name) = label {
                names.push(name.clone());
            }
        }
        Ok(alloc::format!("({})", names.join(" ")))
    }

    /// `(get-value (t1 t2 …))` — evaluate each term under the current model and
    /// return `((t1 v1) (t2 v2) …)`.
    fn get_value(&mut self, list: &[SExpr]) -> Result<String, String> {
        let queries = match list.get(1) {
            Some(SExpr::List(q)) => q,
            _ => return Err("get-value: expected a term list".to_string()),
        };
        if self.last_model.is_none() {
            return Err("get-value requires a preceding satisfiable check-sat".to_string());
        }
        // Build every queried term first (this borrows `self.m` mutably).
        let mut terms: Vec<(String, AstId)> = Vec::new();
        for q in queries {
            let mut id = self.term(q)?;
            // Substitute the string-witness assignment and re-fold, so a string
            // term evaluates to its concrete literal instead of a placeholder.
            if !self.str_witness.is_empty() {
                let sub = self.str_witness.clone();
                id = crate::rewriter::substitute(&mut self.m, id, &sub);
                let mut memo = BTreeMap::new();
                id = self.refold_str_markers(id, &mut memo);
                id = crate::rewriter::simplify(&mut self.m, id);
            }
            terms.push((render_sexpr(q), id));
        }
        // Then evaluate against the model (disjoint immutable borrow of `m`).
        let mut model = self.last_model.take().unwrap();
        let mut out = String::from("(");
        for (i, (text, id)) in terms.iter().enumerate() {
            if i > 0 {
                out.push(' ');
            }
            let v = self
                .str_value(*id)
                .map(|cps| alloc::format!("\"{}\"", code_points_to_string(&cps)))
                .or_else(|| self.str_model_value(&mut model, *id))
                .or_else(|| self.enum_value_name(&mut model, *id))
                .unwrap_or_else(|| model.value_string(&self.m, *id));
            out.push_str(&alloc::format!("({text} {v})"));
        }
        out.push(')');
        self.last_model = Some(model);
        Ok(out)
    }

    /// `(get-model)` — a `define-fun` per 0-ary declared constant, in
    /// declaration order.
    fn get_model(&mut self) -> Result<String, String> {
        if self.last_model.is_none() {
            return Err("get-model requires a preceding satisfiable check-sat".to_string());
        }
        // Collect the 0-ary constants and their range-sort names.
        let mut consts: Vec<(String, AstId, String)> = Vec::new();
        for name in &self.decl_order {
            let d = self.funcs[name];
            let fd = self.m.func_decl(d).unwrap();
            if !fd.domain.is_empty() {
                continue; // n-ary function interpretations not yet emitted
            }
            let range = fd.range;
            if self.m.is_array_sort(range) {
                continue; // array interpretations not yet emitted (would be invalid)
            }
            let sort_name = self
                .m
                .sort(range)
                .and_then(|s| s.name.as_str())
                .unwrap_or("?")
                .to_string();
            let c = self.m.mk_const(d);
            consts.push((name.clone(), c, sort_name));
        }
        let mut model = self.last_model.take().unwrap();
        let mut out = String::from("(");
        for (name, c, sort_name) in &consts {
            let v = model.value_string(&self.m, *c);
            out.push_str(&alloc::format!(
                "\n  (define-fun {name} () {sort_name} {v})"
            ));
        }
        out.push_str("\n)");
        self.last_model = Some(model);
        Ok(out)
    }

    /// `((_ repeat k) x)` — concatenate `x` with itself `k` times.
    fn bv_repeat(&mut self, k: u32, x: AstId) -> AstId {
        let mut acc = x;
        for _ in 1..k {
            acc = self.m.mk_bv_concat(acc, x);
        }
        acc
    }

    /// `((_ rotate_left k) x)` / rotate_right: a cyclic bit rotation, built from
    /// `extract` + `concat`. Rotating by a multiple of the width is the identity.
    fn bv_rotate(&mut self, k: u32, x: AstId, left: bool) -> AstId {
        let n = self
            .m
            .bv_sort_width(self.m.get_sort(x))
            .expect("rotate: not bv");
        let k = if left { k % n } else { (n - k % n) % n }; // reduce to a left rotate
        if k == 0 {
            return x;
        }
        // left rotate by k: high (n-k) bits from x[0..n-k-1], low k bits from x[n-k..n-1].
        let hi = self.m.mk_bv_extract(n - 1 - k, 0, x);
        let lo = self.m.mk_bv_extract(n - 1, n - k, x);
        self.m.mk_bv_concat(hi, lo)
    }

    /// Look up a name in the active `let` scopes (innermost first).
    fn lookup_bound(&self, name: &str) -> Option<AstId> {
        self.scopes.iter().rev().find_map(|scope| {
            scope
                .iter()
                .rev()
                .find(|(n, _)| n == name)
                .map(|(_, id)| *id)
        })
    }

    /// Build a term from an s-expression.
    fn term(&mut self, s: &SExpr) -> Result<AstId, String> {
        match s {
            SExpr::Atom(a) => match a.as_str() {
                "true" => Ok(self.m.mk_true()),
                "false" => Ok(self.m.mk_false()),
                name if name.starts_with('"') => {
                    // A string literal "…" → its interned distinct constant.
                    let text = unquote_string(name);
                    Ok(self.mk_str_lit(&text))
                }
                // 0-ary regex constants: re.none / re.all / re.allchar.
                name if name.starts_with("re.") && self.lookup_bound(name).is_none() => {
                    self.regex_op(name, &[])
                }
                // RoundingMode constants (RNE, RTP, …) as named constants.
                name if is_rm_name(name) && self.lookup_bound(name).is_none() => {
                    let s = self.rm_sort();
                    let d = self.m.mk_func_decl(Symbol::new(name), &[], s);
                    Ok(self.m.mk_const(d))
                }
                name => {
                    if let Some(id) = self.lookup_bound(name) {
                        return Ok(id);
                    }
                    if let Some((r, is_int)) = parse_numeral(name) {
                        return Ok(self.m.mk_numeral(r, is_int));
                    }
                    if let Some((v, w)) = parse_bv_literal(name) {
                        return Ok(self.m.mk_bv_numeral(v, w));
                    }
                    if self.macros.contains_key(name) {
                        return self.expand_macro(name, Vec::new());
                    }
                    let d = *self
                        .funcs
                        .get(name)
                        .ok_or_else(|| alloc::format!("unknown symbol {name:?}"))?;
                    Ok(self.m.mk_const(d))
                }
            },
            SExpr::List(l) if !l.is_empty() => {
                // Qualified-identifier head, e.g. ((as const (Array I E)) v).
                if let SExpr::List(qid) = &l[0] {
                    if qid.len() == 3
                        && matches!(&qid[0], SExpr::Atom(a) if a == "_")
                        && matches!(&qid[1], SExpr::Atom(a) if a == "is")
                    {
                        // ((_ is C) x) — the datatype tester.
                        let cname = Self::sym(&qid[2])?.to_string();
                        let x = self.term(&l[1])?;
                        // General multi-constructor datatype: apply the predicate.
                        if let Some(&tdecl) = self.tester_of.get(&cname) {
                            return Ok(self.m.mk_app(tdecl, &[x]));
                        }
                        // A record has a single constructor, so its tester is true.
                        if self.records.contains_key(&self.m.get_sort(x)) {
                            return Ok(self.m.mk_true());
                        }
                        let c = self.term(&SExpr::Atom(cname))?;
                        return Ok(self.m.mk_eq(x, c));
                    }
                    if qid.len() == 3
                        && matches!(&qid[0], SExpr::Atom(a) if a == "_")
                        && matches!(&qid[1], SExpr::Atom(a) if a == "map")
                    {
                        // ((_ map f) a…): an array value; `select` applies f
                        // element-wise below. The function is qid[2], either a
                        // plain name or a qualified `(f (Dom…) Rng)` identifier.
                        let fname = match &qid[2] {
                            SExpr::Atom(a) => a.clone(),
                            SExpr::List(fl) if !fl.is_empty() => Self::sym(&fl[0])?.to_string(),
                            _ => return Err("map: bad function".to_string()),
                        };
                        let arrays: Vec<AstId> = l[1..]
                            .iter()
                            .map(|a| self.term(a))
                            .collect::<Result<_, _>>()?;
                        let sort = self.m.get_sort(arrays[0]);
                        let t = self.fresh_const(sort);
                        self.maps.insert(t, (fname, arrays));
                        return Ok(t);
                    }
                    if qid.len() == 3
                        && matches!(&qid[0], SExpr::Atom(a) if a == "as")
                        && matches!(&qid[1], SExpr::Atom(a) if a == "const")
                    {
                        let array_sort = self.resolve_sort(&qid[2])?;
                        let value = self.term(&l[1])?;
                        return Ok(self.m.mk_const_array(array_sort, value));
                    }
                    if qid.len() == 4
                        && matches!(&qid[0], SExpr::Atom(a) if a == "_")
                        && matches!(&qid[1], SExpr::Atom(a) if a == "extract")
                    {
                        let high: u32 = Self::sym(&qid[2])?
                            .parse()
                            .map_err(|_| "extract: bad index".to_string())?;
                        let low: u32 = Self::sym(&qid[3])?
                            .parse()
                            .map_err(|_| "extract: bad index".to_string())?;
                        let x = self.term(&l[1])?;
                        return Ok(self.m.mk_bv_extract(high, low, x));
                    }
                    if qid.len() == 3
                        && matches!(&qid[0], SExpr::Atom(a) if a == "_")
                        && matches!(&qid[1], SExpr::Atom(a) if a == "zero_extend" || a == "sign_extend")
                    {
                        let k: u32 = Self::sym(&qid[2])?
                            .parse()
                            .map_err(|_| "extend: bad amount".to_string())?;
                        let x = self.term(&l[1])?;
                        return Ok(if Self::sym(&qid[1])? == "zero_extend" {
                            self.m.mk_bv_zero_extend(k, x)
                        } else {
                            self.m.mk_bv_sign_extend(k, x)
                        });
                    }
                    if qid.len() == 3
                        && matches!(&qid[0], SExpr::Atom(a) if a == "_")
                        && matches!(&qid[1], SExpr::Atom(a) if a == "rotate_left" || a == "rotate_right" || a == "repeat")
                    {
                        let k: u32 = Self::sym(&qid[2])?
                            .parse()
                            .map_err(|_| "bad index".to_string())?;
                        let x = self.term(&l[1])?;
                        let op = Self::sym(&qid[1])?;
                        return match op {
                            "repeat" => Ok(self.bv_repeat(k, x)),
                            "rotate_left" => Ok(self.bv_rotate(k, x, true)),
                            _ => Ok(self.bv_rotate(k, x, false)),
                        };
                    }
                    if (qid.len() == 4
                        && matches!(&qid[0], SExpr::Atom(a) if a == "_")
                        && matches!(&qid[1], SExpr::Atom(a) if a == "re.loop"))
                        || (qid.len() == 3
                            && matches!(&qid[0], SExpr::Atom(a) if a == "_")
                            && matches!(&qid[1], SExpr::Atom(a) if a == "re.^"))
                    {
                        // ((_ re.loop n m) r): r repeated between n and m times.
                        // ((_ re.^ n) r): exactly n times (n = m).
                        let lo: usize = Self::sym(&qid[2])?
                            .parse()
                            .map_err(|_| "re.loop: bad lower bound".to_string())?;
                        let hi: usize = if qid.len() == 4 {
                            Self::sym(&qid[3])?
                                .parse()
                                .map_err(|_| "re.loop: bad upper bound".to_string())?
                        } else {
                            lo
                        };
                        let rt = self.term(&l[1])?;
                        if let Some(r) = self.regex_of.get(&rt).cloned() {
                            let mut alts: Vec<Regex> = Vec::new();
                            for k in lo..=hi.max(lo) {
                                let mut acc = Regex::Lit(Vec::new());
                                for _ in 0..k {
                                    acc = Regex::Concat(Box::new(r.clone()), Box::new(acc));
                                }
                                alts.push(acc);
                            }
                            let looped =
                                fold_regex(alts, |a, b| Regex::Union(Box::new(a), Box::new(b)));
                            let sort = self.reglan_sort();
                            let t = self.fresh_const(sort);
                            self.regex_of.insert(t, looped);
                            return Ok(t);
                        }
                        let sort = self.reglan_sort();
                        return Ok(self.fresh_const(sort));
                    }
                    if qid.len() == 3
                        && matches!(&qid[0], SExpr::Atom(a) if a == "_")
                        && matches!(&qid[1], SExpr::Atom(a) if a == "divisible")
                    {
                        // ((_ divisible n) t) ≡ (= (mod t n) 0).
                        let n = Self::sym(&qid[2])?;
                        let t = self.term(&l[1])?;
                        let d = self.m.mk_int(
                            n.parse::<i64>()
                                .map_err(|_| "divisible: bad n".to_string())?,
                        );
                        let m = self.m.mk_mod(t, d);
                        let zero = self.m.mk_int(0);
                        return Ok(self.m.mk_eq(m, zero));
                    }
                    if qid.len() == 3
                        && matches!(&qid[0], SExpr::Atom(a) if a == "_")
                        && matches!(&qid[1], SExpr::Atom(a) if a == "int2bv")
                    {
                        // ((_ int2bv n) t): fold a constant Int to its n-bit value;
                        // a symbolic Int argument leaves a mixed term the `decide`
                        // gate answers `unknown`.
                        let n: u32 = Self::sym(&qid[2])?
                            .parse()
                            .map_err(|_| "int2bv: bad width".to_string())?;
                        let t = self.term(&l[1])?;
                        if let Some(v) = self.m.as_numeral(t).and_then(|r| r.to_integer()) {
                            return Ok(self.m.mk_bv_numeral(v, n));
                        }
                        let bvs = self.m.mk_bv_sort(n);
                        let its = self.m.get_sort(t);
                        let d = self.m.mk_func_decl(Symbol::new("int2bv"), &[its], bvs);
                        return Ok(self.m.mk_app(d, &[t]));
                    }
                    if qid.len() == 4
                        && matches!(&qid[0], SExpr::Atom(a) if a == "_")
                        && matches!(&qid[1], SExpr::Atom(a) if a == "to_fp" || a == "to_fp_unsigned")
                    {
                        // ((_ to_fp eb sb) RM x): fold a constant real to Float64
                        // under RNE; otherwise a gated symbolic FP term.
                        let eb: u32 = Self::sym(&qid[2])?
                            .parse()
                            .map_err(|_| "bad eb".to_string())?;
                        let sb: u32 = Self::sym(&qid[3])?
                            .parse()
                            .map_err(|_| "bad sb".to_string())?;
                        // Two forms: `((_ to_fp eb sb) RM x)` (round a real/int/fp)
                        // and `((_ to_fp eb sb) bv)` (reinterpret a width-(eb+sb)
                        // bit-vector as FP — no rounding mode).
                        let has_rm = l.len() > 2;
                        let x = self.term(&l[if has_rm { 2 } else { 1 }])?;
                        if has_rm {
                            let rm = self.term(&l[1])?;
                            // Round a constant real/int to the target format under a
                            // constant rounding mode — bit-exact for any (eb,sb).
                            if let (Some(rmc), Some(r)) = (self.rm_code(rm), self.m.as_numeral(x))
                                && let Some(bits) = Self::real_to_fp_bits(&r, eb, sb, rmc)
                            {
                                return Ok(self.mk_fp(bits, eb, sb));
                            }
                            // Float → float format conversion.
                            if self.fp_format_of(self.m.get_sort(x)).is_some()
                                && let Some(t) = self.fp_to_fp_bv(rm, x, eb, sb)
                            {
                                return Ok(t);
                            }
                        } else if self.m.bv_sort_width(self.m.get_sort(x)) == Some(eb + sb)
                            && let Some(v) = self.m.bv_numeral_value(x)
                        {
                            // Constant bit-vector reinterpreted as an FP bit pattern.
                            if let Some(bits) = v.to_i64() {
                                return Ok(self.mk_fp(bits as u64, eb, sb));
                            }
                        }
                        let s = self.fp_sort(eb, sb);
                        let t = self.fresh_const(s);
                        self.str_symbolic.insert(t);
                        return Ok(t);
                    }
                    // Pseudo-boolean cardinality ((_ at-least k) / (_ at-most k)):
                    // "at least/most k of the arguments are true", encoded as an
                    // integer sum of 0/1 ites compared to k, decided by arithmetic.
                    if qid.len() == 3
                        && matches!(&qid[0], SExpr::Atom(a) if a == "_")
                        && matches!(&qid[1], SExpr::Atom(a) if a == "at-least" || a == "at-most")
                    {
                        let name = Self::sym(&qid[1])?.to_string();
                        let k: i64 = Self::sym(&qid[2])?
                            .parse()
                            .map_err(|_| "at-least/at-most: bad count".to_string())?;
                        let mut terms = Vec::new();
                        for arg in &l[1..] {
                            let b = self.term(arg)?;
                            let one = self.m.mk_int(1);
                            let zero = self.m.mk_int(0);
                            terms.push(self.m.mk_ite(b, one, zero));
                        }
                        let sum = match terms.len() {
                            0 => self.m.mk_int(0),
                            1 => terms[0],
                            _ => self.m.mk_add(&terms),
                        };
                        let kk = self.m.mk_int(k);
                        return Ok(if name == "at-least" {
                            self.m.mk_ge(sum, kk)
                        } else {
                            self.m.mk_le(sum, kk)
                        });
                    }
                    return Err("unsupported qualified application".to_string());
                }
                let head = Self::sym(&l[0])?.to_string();
                if head == "let" {
                    return self.term_let(&l[1], &l[2]);
                }
                if head == "match" {
                    return self.term_match(&l[1], &l[2]);
                }
                if head == "as" && l.len() == 3 {
                    // (as t Sort) — a sort-annotated term. `seq.empty` needs the
                    // annotation to know its element type.
                    if matches!(&l[1], SExpr::Atom(a) if a == "seq.empty") {
                        let s = self.resolve_sort(&l[2])?;
                        return Ok(self.seq_empty_of(s));
                    }
                    return self.term(&l[1]);
                }
                if head == "!" {
                    // (! t :annotation value …) — annotations are transparent to
                    // the term's meaning; evaluate the annotated term.
                    return self.term(&l[1]);
                }
                if head == "forall" || head == "exists" {
                    // Quantifiers are not decided yet. Sound over-approximation:
                    // replace the quantified formula by a fresh, unconstrained
                    // Boolean sentinel; any goal that mentions one forces a sound
                    // `unknown` (see `decide`). The body is intentionally not
                    // parsed (its bound variables are undeclared).
                    let name = alloc::format!("!q!{}", self.fresh_counter);
                    self.fresh_counter += 1;
                    let b = self.m.mk_bool_sort();
                    let d = self.m.mk_func_decl(Symbol::new(&name), &[], b);
                    let atom = self.m.mk_const(d);
                    self.quant_atoms.insert(atom);
                    return Ok(atom);
                }
                if head == "lambda" {
                    // (lambda ((x S)…) body): an array value. Record the closure;
                    // `select` beta-reduces it below.
                    let (params, body) = self.parse_quantifier(&l[1], &l[2])?;
                    let dom = self.m.get_sort(params[0]);
                    let cod = self.m.get_sort(body);
                    let arr = self.m.mk_array_sort(dom, cod);
                    let t = self.fresh_const(arr);
                    self.lambdas.insert(t, (params, body));
                    return Ok(t);
                }
                if head == "_" {
                    // Indexed identifier, e.g. (_ bv5 8) — a bit-vector numeral.
                    let name = Self::sym(&l[1])?;
                    // (_ as-array f): the array λi. f(i). `select` applies f below.
                    if name == "as-array" && l.len() == 3 {
                        let fname = Self::sym(&l[2])?.to_string();
                        let decl = *self
                            .funcs
                            .get(&fname)
                            .ok_or_else(|| alloc::format!("as-array: unknown function {fname}"))?;
                        let fd = self.m.func_decl(decl).ok_or("as-array: bad decl")?;
                        let (dom, rng) = (fd.domain[0], fd.range);
                        let arr = self.m.mk_array_sort(dom, rng);
                        let t = self.fresh_const(arr);
                        self.as_arrays.insert(t, decl);
                        return Ok(t);
                    }
                    // FP special values: (_ +oo eb sb), (_ NaN eb sb), …
                    if l.len() == 4 && matches!(name, "+oo" | "-oo" | "NaN" | "+zero" | "-zero") {
                        let kind = name.to_string();
                        let eb: u32 = Self::sym(&l[2])?
                            .parse()
                            .map_err(|_| "bad eb".to_string())?;
                        let sb: u32 = Self::sym(&l[3])?
                            .parse()
                            .map_err(|_| "bad sb".to_string())?;
                        return Ok(self.fp_special(&kind, eb, sb));
                    }
                    if let Some(digits) = name.strip_prefix("bv") {
                        let v = Int::from_str_radix(digits, 10)
                            .map_err(|_| "bad bv numeral".to_string())?;
                        let w: u32 = Self::sym(&l[2])?
                            .parse()
                            .map_err(|_| "bad bv width".to_string())?;
                        return Ok(self.m.mk_bv_numeral(v, w));
                    }
                    return Err(alloc::format!("unsupported indexed identifier {name:?}"));
                }
                // Word equation `(= (str.++ …) "literal")`: expand to the sound,
                // complete disjunction over split points before building the
                // (otherwise gated) symbolic concatenation.
                if head == "="
                    && l.len() == 3
                    && let Some(t) = self.try_split_concat_eq(&l[1], &l[2])?
                {
                    return Ok(t);
                }
                let args: Vec<AstId> = l[1..]
                    .iter()
                    .map(|a| self.term(a))
                    .collect::<Result<_, _>>()?;
                // (select (lambda ((x S)…) body) i…) beta-reduces to body[x:=i…].
                if head == "select"
                    && let Some((params, body)) = self.lambdas.get(&args[0]).cloned()
                    && params.len() == args.len() - 1
                {
                    let subst: Vec<(AstId, AstId)> =
                        params.into_iter().zip(args[1..].iter().copied()).collect();
                    let reduced = substitute(&mut self.m, body, &subst);
                    return Ok(crate::rewriter::simplify(&mut self.m, reduced));
                }
                // (select ((_ map f) a…) i) → f((select a i)…).
                if head == "select"
                    && let Some((fname, arrays)) = self.maps.get(&args[0]).cloned()
                {
                    let idx = args[1];
                    let selects: Vec<AstId> =
                        arrays.iter().map(|&a| self.m.mk_select(a, idx)).collect();
                    return self.apply(&fname, selects);
                }
                // (select (_ as-array f) i) → f(i).
                if head == "select"
                    && let Some(&decl) = self.as_arrays.get(&args[0])
                {
                    return Ok(self.m.mk_app(decl, &[args[1]]));
                }
                if self.macros.contains_key(&head) {
                    return self.expand_macro(&head, args);
                }
                if head.starts_with("str.") {
                    return self.string_op(&head, &args);
                }
                if head.starts_with("re.") {
                    return self.regex_op(&head, &args);
                }
                if head.starts_with("seq.") {
                    return self.seq_op(&head, &args);
                }
                if head.starts_with("fp.") {
                    return self.fp_op(&head, &args);
                }
                if head == "fp" && args.len() == 3 {
                    return self.mk_fp_literal(&args);
                }
                // Structural equality of two FP constants compares their bits.
                if head == "="
                    && args.len() == 2
                    && let (Some(&(ba, _, _)), Some(&(bb, _, _))) =
                        (self.fp_of.get(&args[0]), self.fp_of.get(&args[1]))
                {
                    return Ok(self.mk_bool(ba == bb));
                }
                // Structural equality of FP terms (at least one symbolic) →
                // bit-vector equality of their representations (QF_BV).
                if head == "="
                    && args.len() == 2
                    && self.fp_format_of(self.m.get_sort(args[0])).is_some()
                    && let (Some(a), Some(b)) = (self.fp_to_bv(args[0]), self.fp_to_bv(args[1]))
                {
                    return Ok(self.m.mk_eq(a, b));
                }
                // Int↔BV bridge: (= (bv2int a) c) / (= (int2bv x) c).
                if head == "="
                    && args.len() == 2
                    && let Some(t) = self.bv_int_bridge_eq(args[0], args[1])
                {
                    return Ok(t);
                }
                // Fold equality of two structural sequences (element-wise, or
                // false on a length mismatch).
                if head == "="
                    && args.len() == 2
                    && let (Some(a), Some(b)) = (
                        self.seq_of.get(&args[0]).cloned(),
                        self.seq_of.get(&args[1]).cloned(),
                    )
                {
                    if a.len() != b.len() {
                        return Ok(self.m.mk_false());
                    }
                    let eqs: Vec<AstId> = a
                        .iter()
                        .zip(&b)
                        .map(|(&x, &y)| self.m.mk_eq(x, y))
                        .collect();
                    return Ok(match eqs.len() {
                        0 => self.m.mk_true(),
                        1 => eqs[0],
                        _ => self.m.mk_and(&eqs),
                    });
                }
                self.apply(&head, args)
            }
            SExpr::List(_) => Err("empty application".to_string()),
        }
    }

    /// Expand a `define-fun` macro applied to `args`.
    fn expand_macro(&mut self, name: &str, args: Vec<AstId>) -> Result<AstId, String> {
        let (params, body) = self.macros.get(name).cloned().unwrap();
        if params.len() != args.len() {
            return Err(alloc::format!(
                "macro {name:?} expects {} argument(s), got {}",
                params.len(),
                args.len()
            ));
        }
        let scope: Vec<(String, AstId)> = params.into_iter().zip(args).collect();
        // Hygiene: the body sees only its parameters and globals, not the
        // caller's `let` bindings.
        let saved = core::mem::take(&mut self.scopes);
        self.scopes.push(scope);
        let result = self.term(&body);
        self.scopes = saved;
        result
    }

    /// `(let ((v t) ...) body)` — parallel binding, then evaluate `body`.
    /// The declaration name of a function/constant.
    fn decl_name(&self, decl: AstId) -> Option<String> {
        Some(self.m.func_decl(decl)?.name.as_str()?.to_string())
    }

    /// For a datatype `sort` and constructor name `cname`, the tester guard
    /// `is-C(e)` and the selector declarations of that constructor.
    fn constructor_info(
        &mut self,
        e: AstId,
        sort: AstId,
        cname: &str,
    ) -> Option<(AstId, Vec<AstId>)> {
        if let Some(ctors) = self.datatypes.get(&sort).cloned() {
            for (cdecl, sels, tdecl) in ctors {
                if self.decl_name(cdecl).as_deref() == Some(cname) {
                    let guard = self.m.mk_app(tdecl, &[e]);
                    return Some((guard, sels));
                }
            }
        }
        if let Some((cdecl, sels)) = self.records.get(&sort).cloned()
            && self.decl_name(cdecl).as_deref() == Some(cname)
        {
            let guard = self.m.mk_true();
            return Some((guard, sels));
        }
        if let Some(ctors) = self.enums.get(&sort).cloned() {
            for c in ctors {
                let cd = self.m.app_decl(c);
                if self.decl_name(cd).as_deref() == Some(cname) {
                    let guard = self.m.mk_eq(e, c);
                    return Some((guard, Vec::new()));
                }
            }
        }
        None
    }

    /// `(match e ((pat body)…))` — datatype pattern matching, desugared to a
    /// guarded `ite` chain over the constructor testers, binding each pattern's
    /// variables to the corresponding selectors. Matches are exhaustive, so the
    /// final case is the `else` branch.
    fn term_match(&mut self, scrutinee: &SExpr, cases: &SExpr) -> Result<AstId, String> {
        let e = self.term(scrutinee)?;
        let sort = self.m.get_sort(e);
        let cases = as_list(cases)?;
        let mut result: Option<AstId> = None;
        // Build from the last case (the else) up to the first.
        for case in cases.iter().rev() {
            let cl = as_list(case)?;
            if cl.len() != 2 {
                return Err("match: each case is (pattern body)".to_string());
            }
            let (guard, scope) = self.match_pattern(e, sort, &cl[0])?;
            self.scopes.push(scope);
            let body = self.term(&cl[1]);
            self.scopes.pop();
            let body = body?;
            result = Some(match result {
                None => body,
                Some(rest) => self.m.mk_ite(guard, body, rest),
            });
        }
        result.ok_or_else(|| "match: no cases".to_string())
    }

    /// A match pattern's `(guard, variable bindings)`: a constructor pattern
    /// `C` / `(C x…)` guards on its tester and binds fields to selectors; a plain
    /// variable (or `_`) matches anything and binds the whole scrutinee.
    fn match_pattern(
        &mut self,
        e: AstId,
        sort: AstId,
        pattern: &SExpr,
    ) -> Result<(AstId, Vec<(String, AstId)>), String> {
        match pattern {
            SExpr::Atom(name) => {
                if let Some((guard, _)) = self.constructor_info(e, sort, name) {
                    Ok((guard, Vec::new()))
                } else {
                    let scope = if name == "_" {
                        Vec::new()
                    } else {
                        alloc::vec![(name.clone(), e)]
                    };
                    let t = self.m.mk_true();
                    Ok((t, scope))
                }
            }
            SExpr::List(pl) if !pl.is_empty() => {
                let cname = Self::sym(&pl[0])?.to_string();
                let (guard, sels) = self
                    .constructor_info(e, sort, &cname)
                    .ok_or_else(|| alloc::format!("match: unknown constructor {cname:?}"))?;
                let mut scope = Vec::new();
                for (v, &sel) in pl[1..].iter().zip(&sels) {
                    let name = Self::sym(v)?.to_string();
                    let app = self.m.mk_app(sel, &[e]);
                    scope.push((name, app));
                }
                Ok((guard, scope))
            }
            _ => Err("match: bad pattern".to_string()),
        }
    }

    fn term_let(&mut self, bindings: &SExpr, body: &SExpr) -> Result<AstId, String> {
        let bs = match bindings {
            SExpr::List(bs) => bs,
            _ => return Err("let: expected a binding list".to_string()),
        };
        // Evaluate every RHS in the *outer* scope (parallel `let` semantics).
        let mut scope: Vec<(String, AstId)> = Vec::new();
        for b in bs {
            match b {
                SExpr::List(pair) if pair.len() == 2 => {
                    let name = Self::sym(&pair[0])?.to_string();
                    let val = self.term(&pair[1])?;
                    scope.push((name, val));
                }
                _ => return Err("let: expected (name term) bindings".to_string()),
            }
        }
        self.scopes.push(scope);
        let result = self.term(body);
        self.scopes.pop();
        result
    }

    fn apply(&mut self, head: &str, args: Vec<AstId>) -> Result<AstId, String> {
        let m = &mut self.m;
        // Bit-vector binary ops and comparisons require equal operand widths;
        // reject a mismatch (as z3 does) instead of building a garbage term.
        const BV_SAME_WIDTH: &[&str] = &[
            "bvadd", "bvsub", "bvmul", "bvand", "bvor", "bvxor", "bvnand", "bvnor", "bvxnor",
            "bvudiv", "bvurem", "bvsdiv", "bvsrem", "bvsmod", "bvshl", "bvlshr", "bvashr", "bvult",
            "bvule", "bvugt", "bvuge", "bvslt", "bvsle", "bvsgt", "bvsge", "bvcomp", "bvuaddo",
            "bvsaddo", "bvusubo", "bvssubo", "bvumulo", "bvsmulo", "bvsdivo",
        ];
        if BV_SAME_WIDTH.contains(&head) && args.len() == 2 {
            let w0 = m.bv_sort_width(m.get_sort(args[0]));
            let w1 = m.bv_sort_width(m.get_sort(args[1]));
            if let (Some(a), Some(b)) = (w0, w1)
                && a != b
            {
                return Err(alloc::format!(
                    "{head}: operand width mismatch ({a} vs {b})"
                ));
            }
        }
        match head {
            "not" => Ok(m.mk_not(args[0])),
            "and" => Ok(match args.len() {
                0 => m.mk_true(),
                1 => args[0],
                _ => m.mk_and(&args),
            }),
            "or" => Ok(match args.len() {
                0 => m.mk_false(),
                1 => args[0],
                _ => m.mk_or(&args),
            }),
            "xor" => Ok(match args.len() {
                0 => m.mk_false(),
                1 => args[0],
                // left-associative: (xor a b c) = ((a xor b) xor c)
                _ => args[1..].iter().fold(args[0], |acc, &a| m.mk_xor(acc, a)),
            }),
            "=>" => {
                // right associative
                let mut acc = *args.last().unwrap();
                for &a in args[..args.len() - 1].iter().rev() {
                    acc = m.mk_implies(a, acc);
                }
                Ok(acc)
            }
            "ite" => Ok(m.mk_ite(args[0], args[1], args[2])),
            "select" => Ok(m.mk_select(args[0], args[1])),
            "store" => Ok(m.mk_store(args[0], args[1], args[2])),
            "distinct" => {
                // Expand to pairwise disequality so the theory solvers see it
                // (a bare `distinct` node would be an opaque Boolean atom).
                if args.len() < 2 {
                    return Ok(m.mk_true());
                }
                let mut neqs = Vec::new();
                for i in 0..args.len() {
                    for j in (i + 1)..args.len() {
                        let eq = m.mk_eq(args[i], args[j]);
                        neqs.push(m.mk_not(eq));
                    }
                }
                Ok(if neqs.len() == 1 {
                    neqs[0]
                } else {
                    m.mk_and(&neqs)
                })
            }
            "=" => {
                // Operands must share a sort; a bit-vector width mismatch (e.g.
                // a 4-bit variable against an 8-bit literal) is ill-typed.
                for w in args.windows(2) {
                    if let (Some(x), Some(y)) = (
                        m.bv_sort_width(m.get_sort(w[0])),
                        m.bv_sort_width(m.get_sort(w[1])),
                    ) && x != y
                    {
                        return Err(alloc::format!("=: bit-vector width mismatch ({x} vs {y})"));
                    }
                }
                // chainable: (= a b c) => (and (= a b) (= b c))
                if args.len() == 2 {
                    Ok(m.mk_eq(args[0], args[1]))
                } else {
                    let mut eqs = Vec::new();
                    for w in args.windows(2) {
                        eqs.push(m.mk_eq(w[0], w[1]));
                    }
                    Ok(m.mk_and(&eqs))
                }
            }
            // --- linear arithmetic (with constant folding, so downstream `mod`,
            // `abs`, … see literal operands) ---
            "+" => {
                if let Some(ns) = all_numerals(m, &args) {
                    let sum = ns.iter().fold(rat(0), |a, b| &a + b);
                    return Ok(m.mk_numeral(sum, all_int(m, &args)));
                }
                Ok(match args.len() {
                    0 => m.mk_int(0),
                    1 => args[0],
                    _ => m.mk_add(&args),
                })
            }
            "-" => {
                if let Some(ns) = all_numerals(m, &args) {
                    let is_int = all_int(m, &args);
                    let val = match ns.split_first() {
                        Some((head, rest)) if !rest.is_empty() => {
                            rest.iter().fold(head.clone(), |a, b| &a - b)
                        }
                        Some((head, _)) => head.neg(), // unary minus
                        None => rat(0),
                    };
                    return Ok(m.mk_numeral(val, is_int));
                }
                Ok(if args.len() == 1 {
                    m.mk_uminus(args[0])
                } else {
                    m.mk_sub(&args)
                })
            }
            "*" => {
                if let Some(ns) = all_numerals(m, &args) {
                    let prod = ns.iter().fold(rat(1), |a, b| &a * b);
                    return Ok(m.mk_numeral(prod, all_int(m, &args)));
                }
                Ok(match args.len() {
                    0 => m.mk_int(1),
                    1 => args[0],
                    _ => m.mk_mul(&args),
                })
            }
            "/" => {
                // `/` is real division. A constant divisor makes it linear:
                // both constant → an exact rational; `(/ a k)` with a constant
                // `k ≠ 0` → `a · (1/k)`. Only a non-constant divisor stays opaque.
                match (m.as_numeral(args[0]), m.as_numeral(args[1])) {
                    (Some(p), Some(q)) if !q.is_zero() => Ok(m.mk_numeral(p.div(&q), false)),
                    (_, Some(q)) if !q.is_zero() => {
                        let inv = m.mk_numeral(rat(1).div(&q), false);
                        Ok(m.mk_mul(&[args[0], inv]))
                    }
                    _ => Ok(m.mk_div(args[0], args[1])),
                }
            }
            "div" => match int_pair(m, args[0], args[1]) {
                Some((a, b)) if !b.is_zero() => {
                    let (q, _) = euclid_div_mod(&a, &b);
                    Ok(m.mk_numeral(Rational::from_integer(q), true))
                }
                _ => Ok(m.mk_idiv(args[0], args[1])),
            },
            "mod" => match int_pair(m, args[0], args[1]) {
                Some((a, b)) if !b.is_zero() => {
                    let (_, r) = euclid_div_mod(&a, &b);
                    Ok(m.mk_numeral(Rational::from_integer(r), true))
                }
                _ => Ok(m.mk_mod(args[0], args[1])),
            },
            "^" => {
                // Exponentiation: fold a constant base to a non-negative integer
                // constant power; otherwise leave an opaque (non-linear) term.
                if let (Some(base), Some(exp)) = (
                    m.as_numeral(args[0]),
                    m.as_numeral(args[1]).and_then(|v| v.to_integer()),
                ) && let Some(e) = exp.to_i64()
                    && (0..=1024).contains(&e)
                {
                    let is_int = m.is_int_sort(m.get_sort(args[0]));
                    let mut acc = Rational::from_integer(puremp::Int::from(1));
                    for _ in 0..e {
                        acc = acc.mul(&base);
                    }
                    return Ok(m.mk_numeral(acc, is_int));
                }
                let d = m.mk_func_decl(
                    Symbol::new("^"),
                    &[m.get_sort(args[0]); 2],
                    m.get_sort(args[0]),
                );
                Ok(m.mk_app(d, &args))
            }
            "abs" => match m.as_numeral(args[0]).and_then(|v| v.to_integer()) {
                Some(a) => Ok(m.mk_numeral(Rational::from_integer(a.abs()), true)),
                None => {
                    // (abs a) = (ite (>= a 0) a (- a)); opaque to the linear core
                    // for non-constant a, but structurally faithful.
                    let zero = m.mk_int(0);
                    let ge = m.mk_ge(args[0], zero);
                    let neg = m.mk_uminus(args[0]);
                    Ok(m.mk_ite(ge, args[0], neg))
                }
            },
            "to_real" => match m.as_numeral(args[0]) {
                Some(v) => Ok(m.mk_numeral(v, false)),
                None => Ok(m.mk_to_real(args[0])),
            },
            "to_int" => match m.as_numeral(args[0]) {
                Some(v) => Ok(m.mk_numeral(Rational::from_integer(v.floor()), true)),
                None => Ok(m.mk_to_int(args[0])),
            },
            "is_int" => match m.as_numeral(args[0]) {
                // (is_int r): true iff r is integral.
                Some(v) => Ok(if v.is_integer() {
                    m.mk_true()
                } else {
                    m.mk_false()
                }),
                // Symbolic: is_int(x) ⟺ to_real(to_int(x)) = x (i.e. ⌊x⌋ = x).
                None => {
                    let ti = m.mk_to_int(args[0]);
                    let tr = m.mk_to_real(ti);
                    Ok(m.mk_eq(tr, args[0]))
                }
            },
            "<=" | "<" | ">=" | ">" => {
                let mk = |m: &mut AstManager, a, b| match head {
                    "<=" => m.mk_le(a, b),
                    "<" => m.mk_lt(a, b),
                    ">=" => m.mk_ge(a, b),
                    _ => m.mk_gt(a, b),
                };
                if args.len() == 2 {
                    Ok(mk(m, args[0], args[1]))
                } else {
                    let mut cs = Vec::new();
                    for w in args.windows(2) {
                        cs.push(mk(m, w[0], w[1]));
                    }
                    Ok(m.mk_and(&cs))
                }
            }
            // --- bit-vectors ---
            "bvnot" => Ok(m.mk_bvnot(args[0])),
            "bvneg" => Ok(m.mk_bvneg(args[0])),
            // bvand/bvor/bvxor/bvadd/bvmul are left-associative and variadic.
            "bvand" => Ok(args[1..].iter().fold(args[0], |a, &b| m.mk_bvand(a, b))),
            "bvor" => Ok(args[1..].iter().fold(args[0], |a, &b| m.mk_bvor(a, b))),
            "bvxor" => Ok(args[1..].iter().fold(args[0], |a, &b| m.mk_bvxor(a, b))),
            "bvadd" => Ok(args[1..].iter().fold(args[0], |a, &b| m.mk_bvadd(a, b))),
            "bvmul" => Ok(args[1..].iter().fold(args[0], |a, &b| m.mk_bvmul(a, b))),
            "bvsub" => Ok(m.mk_bvsub(args[0], args[1])),
            "bvudiv" => Ok(m.mk_bvudiv(args[0], args[1])),
            "bvurem" => Ok(m.mk_bvurem(args[0], args[1])),
            "bvuaddo" | "bvsaddo" | "bvusubo" | "bvssubo" | "bvumulo" | "bvsmulo" | "bvsdivo" => {
                let w = m.bv_sort_width(m.get_sort(args[0])).unwrap_or(1);
                Ok(bv_overflow(m, head, args[0], args[1], w))
            }
            "bvnego" => {
                let w = m.bv_sort_width(m.get_sort(args[0])).unwrap_or(1);
                Ok(bv_overflow(m, head, args[0], args[0], w))
            }
            "bvsdiv" => Ok(bv_sdiv(m, args[0], args[1])),
            "bvsrem" => Ok(bv_srem(m, args[0], args[1])),
            "bvsmod" => Ok(bv_smod(m, args[0], args[1])),
            "bvshl" => Ok(m.mk_bvshl(args[0], args[1])),
            "bvlshr" => Ok(m.mk_bvlshr(args[0], args[1])),
            "bvashr" => Ok(m.mk_bvashr(args[0], args[1])),
            "bvult" => Ok(m.mk_bvult(args[0], args[1])),
            "bvule" => Ok(m.mk_bvule(args[0], args[1])),
            "bvugt" => Ok(m.mk_bvult(args[1], args[0])), // a >u b  ⟺  b <u a
            "bvuge" => Ok(m.mk_bvule(args[1], args[0])), // a ≥u b  ⟺  b ≤u a
            "bvslt" => Ok(m.mk_bvslt(args[0], args[1])),
            "bvsle" => Ok(m.mk_bvsle(args[0], args[1])),
            "bvsgt" => Ok(m.mk_bvslt(args[1], args[0])), // a >s b  ⟺  b <s a
            "bvsge" => Ok(m.mk_bvsle(args[1], args[0])), // a ≥s b  ⟺  b ≤s a
            "concat" => Ok(m.mk_bv_concat(args[0], args[1])),
            // Derived bitwise ops: nand/nor/xnor = not of and/or/xor.
            "bvnand" => {
                let t = m.mk_bvand(args[0], args[1]);
                Ok(m.mk_bvnot(t))
            }
            "bvnor" => {
                let t = m.mk_bvor(args[0], args[1]);
                Ok(m.mk_bvnot(t))
            }
            "bvxnor" => {
                let t = m.mk_bvxor(args[0], args[1]);
                Ok(m.mk_bvnot(t))
            }
            // bvcomp a b → #b1 if a = b else #b0.
            "bvcomp" => {
                let eq = m.mk_eq(args[0], args[1]);
                let (one, zero) = (m.mk_bv(1, 1), m.mk_bv(0, 1));
                Ok(m.mk_ite(eq, one, zero))
            }
            // bvredand a → #b1 iff every bit is set; bvredor → #b1 iff any is.
            "bvredand" => {
                let w = m.bv_sort_width(m.get_sort(args[0])).unwrap_or(1);
                let zero = m.mk_bv(0, w);
                let ones = m.mk_bvnot(zero);
                let eq = m.mk_eq(args[0], ones);
                let (b1, b0) = (m.mk_bv(1, 1), m.mk_bv(0, 1));
                Ok(m.mk_ite(eq, b1, b0))
            }
            "bvredor" => {
                let w = m.bv_sort_width(m.get_sort(args[0])).unwrap_or(1);
                let zero = m.mk_bv(0, w);
                let eq = m.mk_eq(args[0], zero);
                let (b1, b0) = (m.mk_bv(1, 1), m.mk_bv(0, 1));
                Ok(m.mk_ite(eq, b0, b1))
            }
            // bv2int / (u)bv_to_int / bv2nat: fold a constant. A symbolic use is
            // an Int term over a bit-vector, so the mixed-theory gate in `decide`
            // routes the goal to a sound `unknown`.
            "bv2int" | "ubv_to_int" | "bv2nat" | "sbv_to_int" => {
                if let Some(v) = m.bv_numeral_value(args[0]) {
                    let val = if head == "sbv_to_int" {
                        to_signed(&v, m.bv_sort_width(m.get_sort(args[0])).unwrap_or(0))
                    } else {
                        v
                    };
                    return Ok(m.mk_numeral(Rational::from_integer(val), true));
                }
                let int = m.mk_int_sort();
                let bvs = m.get_sort(args[0]);
                let d = m.mk_func_decl(Symbol::new(head), &[bvs], int);
                Ok(m.mk_app(d, &args))
            }
            name => {
                let d = *self
                    .funcs
                    .get(name)
                    .ok_or_else(|| alloc::format!("unknown function {name:?}"))?;
                Ok(self.m.mk_app(d, &args))
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn qf_uf_transitivity_unsat() {
        let script = "
            (declare-sort S 0)
            (declare-const a S) (declare-const b S) (declare-const c S)
            (assert (= a b))
            (assert (= b c))
            (assert (not (= a c)))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["unsat"]);
    }

    #[test]
    fn qf_uf_congruence_unsat() {
        let script = "
            (declare-sort S 0)
            (declare-fun f (S) S)
            (declare-const a S) (declare-const b S)
            (assert (= a b))
            (assert (not (= (f a) (f b))))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["unsat"]);
    }

    #[test]
    fn satisfiable_script() {
        let script = "
            (declare-sort S 0)
            (declare-const a S) (declare-const b S) (declare-const c S)
            (assert (= a b))
            (assert (not (= a c)))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["sat"]);
    }

    #[test]
    fn boolean_and_ite() {
        let script = "
            (declare-const p Bool) (declare-const q Bool)
            (assert (and p (not p)))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["unsat"]);
    }

    #[test]
    fn comments_and_multiple_checks() {
        let script = "
            ; a comment
            (declare-const p Bool)
            (assert (or p (not p))) ; tautology
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["sat"]);
    }

    #[test]
    fn let_bindings() {
        // (let ((x (= a b))) (and x (not x))) is unsat regardless of a,b.
        let script = "
            (declare-sort S 0)
            (declare-const a S) (declare-const b S)
            (assert (let ((x (= a b))) (and x (not x))))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["unsat"]);
    }

    #[test]
    fn nested_and_shadowing_lets() {
        // Inner let shadows the outer binding; result stays consistent → sat.
        let script = "
            (declare-const p Bool) (declare-const q Bool)
            (assert (let ((x p)) (let ((x q)) (or x (not x)))))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["sat"]);
    }

    #[test]
    fn push_pop_scopes_assertions() {
        // The contradictory assertion is scoped inside push/pop; after pop the
        // remaining assertions are satisfiable.
        let script = "
            (declare-const p Bool)
            (assert (or p (not p)))
            (push 1)
              (assert (and p (not p)))
              (check-sat)
            (pop 1)
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["unsat", "sat"]);
    }

    #[test]
    fn qf_lra_bounds_unsat() {
        let script = "
            (set-logic QF_LRA)
            (declare-const x Real) (declare-const y Real)
            (assert (>= x 1)) (assert (>= y 1))
            (assert (<= (+ x y) 1))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["unsat"]);
    }

    #[test]
    fn qf_lia_satisfiable_and_decimals() {
        let script = "
            (declare-const x Int)
            (assert (<= 3 x)) (assert (<= x 5))
            (check-sat)
            (declare-const r Real)
            (assert (= r 1.5))
            (assert (< r 1.0))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["sat", "unsat"]);
    }

    #[test]
    fn qf_lia_integrality_unsat() {
        // No integer strictly between 3 and 4, but a real fits — the Int
        // declaration makes this unsat where QF_LRA would be sat.
        let script = "
            (set-logic QF_LIA)
            (declare-const x Int)
            (assert (< 3 x)) (assert (< x 4))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["unsat"]);
    }

    #[test]
    fn qf_lia_divisibility_sat() {
        // 3 ≤ 2x ≤ 5 has the integer solution x = 2 (relaxation corner is 1.5).
        let script = "
            (set-logic QF_LIA)
            (declare-const x Int)
            (assert (<= 3 (* 2 x))) (assert (<= (* 2 x) 5))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["sat"]);
    }

    #[test]
    fn define_fun_macros() {
        // A 0-ary abbreviation and an n-ary macro, both inlined.
        let script = "
            (declare-const x Int) (declare-const y Int)
            (define-fun bound () Int 10)
            (define-fun below ((a Int) (b Int)) Bool (< a b))
            (assert (below x bound))
            (assert (>= x 10))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["unsat"]);
    }

    #[test]
    fn get_value_returns_assignments() {
        let script = "
            (declare-const x Int) (declare-const p Bool)
            (assert (= x 7)) (assert p)
            (check-sat)
            (get-value (x p (+ x 1)))
        ";
        assert_eq!(
            run(script).unwrap(),
            alloc::vec!["sat", "((x 7) (p true) ((+ x 1) 8))"]
        );
    }

    #[test]
    fn get_value_real_fraction() {
        let script = "
            (declare-const r Real)
            (assert (= (* 2 r) 1))
            (check-sat)
            (get-value (r))
        ";
        assert_eq!(
            run(script).unwrap(),
            alloc::vec!["sat", "((r (/ 1.0 2.0)))"]
        );
    }

    #[test]
    fn get_model_lists_constants() {
        let script = "
            (declare-const x Int) (declare-const b Bool)
            (assert (= x 3)) (assert (not b))
            (check-sat)
            (get-model)
        ";
        let out = run(script).unwrap();
        assert_eq!(out[0], "sat");
        assert!(out[1].contains("(define-fun x () Int 3)"), "{}", out[1]);
        assert!(
            out[1].contains("(define-fun b () Bool false)"),
            "{}",
            out[1]
        );
    }

    #[test]
    fn get_value_without_sat_is_error() {
        // No check-sat before get-value.
        let script = "
            (declare-const x Int)
            (get-value (x))
        ";
        assert!(run(script).is_err());
    }

    #[test]
    fn distinct_expands_to_pairwise_disequality() {
        // distinct a b c with a = b is unsat.
        let script = "
            (declare-sort S 0)
            (declare-const a S) (declare-const b S) (declare-const c S)
            (assert (distinct a b c))
            (assert (= a b))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["unsat"]);
    }

    #[test]
    fn distinct_bool_pigeonhole_unsat() {
        // Three pairwise-distinct Booleans cannot exist.
        let script = "
            (declare-const a Bool) (declare-const b Bool) (declare-const c Bool)
            (assert (distinct a b c))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["unsat"]);
    }

    #[test]
    fn real_division_is_exact() {
        // (/ 1 3) is real division; x = 1/3 ∧ 3x = 1 is satisfiable.
        let script = "
            (declare-const x Real)
            (assert (= x (/ 1 3)))
            (assert (= (* 3 x) 1))
            (check-sat)
            (get-value (x))
        ";
        assert_eq!(
            run(script).unwrap(),
            alloc::vec!["sat", "((x (/ 1.0 3.0)))"]
        );
    }

    #[test]
    fn integer_div_mod_fold() {
        // Euclidean semantics: (div 7 3)=2, (mod 7 3)=1, (mod (- 7) 3)=2.
        let script = "
            (assert (not (= (div 7 3) 2)))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["unsat"]);
        let script2 = "(assert (not (= (mod (- 7) 3) 2)))(check-sat)";
        assert_eq!(run(script2).unwrap(), alloc::vec!["unsat"]);
    }

    #[test]
    fn abs_and_to_real() {
        let script = "
            (declare-const x Int)
            (assert (= x (abs (- 5))))
            (assert (not (= x 5)))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["unsat"]);
        // to_real preserves value: y = to_real x, x = 3, y ≠ 3.0 is unsat.
        let script2 = "
            (declare-const x Int) (declare-const y Real)
            (assert (= y (to_real x))) (assert (= x 3)) (assert (not (= y 3.0)))
            (check-sat)
        ";
        assert_eq!(run(script2).unwrap(), alloc::vec!["unsat"]);
    }

    #[test]
    fn to_int_symbolic() {
        // (to_int x) = ⌊x⌋: x = 3.7 ⇒ (to_int x) = 3, so ≥ 4 is unsat.
        assert_eq!(
            run("(declare-const x Real)(assert (= x 3.7))(assert (>= (to_int x) 4))(check-sat)")
                .unwrap(),
            alloc::vec!["unsat"]
        );
        // 2 ≤ x < 3 ⇒ (to_int x) = 2.
        assert_eq!(
            run("(declare-const x Real)(assert (<= 2.0 x))(assert (< x 3.0))(assert (not (= (to_int x) 2)))(check-sat)")
                .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn to_real_linear_nonconstant() {
        // to_real of a variable is the identity on value: to_real(x) < x is unsat.
        let script = "
            (declare-const x Int)
            (assert (< (to_real x) (to_real x)))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["unsat"]);
    }

    #[test]
    fn term_ite_arithmetic() {
        // x = (ite b 1 2), b, x ≠ 1 is unsat (b ⇒ x = 1).
        let unsat = "
            (declare-const b Bool) (declare-const x Int)
            (assert (= x (ite b 1 2))) (assert b) (assert (not (= x 1)))
            (check-sat)
        ";
        assert_eq!(run(unsat).unwrap(), alloc::vec!["unsat"]);
        // Self-referential guard: x = (ite (< x 0) 1 2) forces x = 2 → sat.
        let sat = "
            (declare-const x Int)
            (assert (= x (ite (< x 0) 1 2)))
            (check-sat)
        ";
        assert_eq!(run(sat).unwrap(), alloc::vec!["sat"]);
    }

    #[test]
    fn nested_term_ite_in_arith() {
        // (ite (> x 0) x 0) + 1 > 100 with x < 50 is unsat in both branches.
        let script = "
            (declare-const x Int)
            (assert (> (+ (ite (> x 0) x 0) 1) 100))
            (assert (< x 50))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["unsat"]);
    }

    #[test]
    fn pop_undeclares_scoped_constants() {
        // x is declared inside a push; after pop it is out of scope, so the
        // reference errors (matching SMT-LIB declaration scoping).
        let script = "
            (push 1)
              (declare-const x Int)
              (assert (> x 0))
            (pop 1)
            (assert (> x 0))
            (check-sat)
        ";
        assert!(run(script).is_err());
    }

    #[test]
    fn scoped_declaration_can_be_reused_after_pop() {
        let script = "
            (push 1) (declare-const x Int) (assert (> x 0)) (check-sat) (pop 1)
            (declare-const y Int) (assert (> y 0)) (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["sat", "sat"]);
    }

    #[test]
    fn mod_div_variable_axioms() {
        // (mod x 3) is always in [0,3): these are unsat.
        assert_eq!(
            run("(declare-const x Int)(assert (< (mod x 3) 0))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run("(declare-const x Int)(assert (>= (mod x 3) 3))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
        // The defining relation x = n·(div x n) + (mod x n) always holds.
        assert_eq!(
            run(
                "(declare-const x Int)(assert (not (= x (+ (* 3 (div x 3)) (mod x 3)))))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn mod_div_satisfiable() {
        // x = 12 ⇒ (mod x 5) = 2, (div x 5) = 2.
        let script = "
            (declare-const x Int)
            (assert (= x 12))
            (assert (= (mod x 5) 2))
            (assert (= (div x 5) 2))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["sat"]);
    }

    #[test]
    fn is_int_constant_fold() {
        // (is_int 4.0) is true, (is_int 2.5) is false.
        assert_eq!(
            run("(assert (not (is_int 4.0)))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run("(assert (is_int 2.5))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn reset_assertions_keeps_declarations() {
        // reset-assertions drops assertions but keeps the declaration of x.
        let script = "
            (declare-const x Int)
            (assert (= x 1)) (assert (= x 2))
            (check-sat)
            (reset-assertions)
            (assert (= x 5))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["unsat", "sat"]);
    }

    #[test]
    fn unsat_core_minimal() {
        // x > 0 ∧ x < 0 ∧ x = 5: c2 is in every core; deletion keeps {c2, c3}.
        let script = "
            (set-option :produce-unsat-cores true)
            (declare-const x Int)
            (assert (! (> x 0) :named c1))
            (assert (! (< x 0) :named c2))
            (assert (! (= x 5) :named c3))
            (check-sat)
            (get-unsat-core)
        ";
        let out = run(script).unwrap();
        assert_eq!(out[0], "unsat");
        // A valid minimal core; c2 must appear, and dropping either member is sat.
        assert!(out[1].contains("c2"), "core must contain c2: {}", out[1]);
        assert_eq!(out[1], "(c2 c3)");
    }

    #[test]
    fn check_sat_assuming_does_not_persist() {
        // The assumption makes this check unsat, but a later plain check is sat.
        let script = "
            (declare-const p Bool) (declare-const q Bool)
            (assert (=> p q))
            (check-sat-assuming (p (not q)))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["unsat", "sat"]);
    }

    #[test]
    fn named_assertion_transparent() {
        // (! t :named n) behaves exactly like t.
        let script = "
            (declare-const p Bool)
            (assert (! (and p (not p)) :named bad))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["unsat"]);
    }

    #[test]
    fn array_read_over_write_same() {
        // select(store(a,i,v), i) = v always.
        let script = "
            (declare-const a (Array Int Int)) (declare-const i Int) (declare-const v Int)
            (assert (not (= (select (store a i v) i) v)))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["unsat"]);
    }

    #[test]
    fn array_read_over_write_other() {
        // i ≠ j ⇒ select(store(a,i,v), j) = select(a, j).
        let script = "
            (declare-const a (Array Int Int)) (declare-const i Int) (declare-const j Int) (declare-const v Int)
            (assert (not (= i j)))
            (assert (not (= (select (store a i v) j) (select a j))))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["unsat"]);
    }

    #[test]
    fn array_congruence_via_equality() {
        // a = b ⇒ select(a,i) = select(b,i), so 1 = 2 is contradictory.
        let script = "
            (declare-const a (Array Int Int)) (declare-const b (Array Int Int)) (declare-const i Int)
            (assert (= (select a i) 1)) (assert (= (select b i) 2)) (assert (= a b))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["unsat"]);
    }

    #[test]
    fn array_extensionality_store_commute() {
        // Writing i then j (i ≠ j) equals writing j then i: the two arrays are
        // equal, so their disequality is unsat (requires extensionality).
        let script = "
            (declare-const a (Array Int Int)) (declare-const i Int) (declare-const j Int)
            (assert (not (= i j)))
            (assert (not (= (store (store a i 1) j 2) (store (store a j 2) i 1))))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["unsat"]);
    }

    #[test]
    fn array_extensionality_sat() {
        // Agreeing at one index does not force equality.
        let script = "
            (declare-const a (Array Int Int)) (declare-const b (Array Int Int))
            (assert (not (= a b))) (assert (= (select a 0) (select b 0)))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["sat"]);
    }

    #[test]
    fn constant_array() {
        // select((as const (Array Int Int)) 7, i) = 7 for any i.
        let script = "
            (declare-const i Int)
            (assert (not (= (select ((as const (Array Int Int)) 7) i) 7)))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["unsat"]);
        // A store over a constant array leaves other indices at the constant.
        let script2 = "
            (declare-const i Int)
            (assert (not (= (select (store ((as const (Array Int Int)) 0) i 5) (+ i 1)) 0)))
            (check-sat)
        ";
        assert_eq!(run(script2).unwrap(), alloc::vec!["unsat"]);
    }

    #[test]
    fn store_equality_terminates() {
        // Equality of two stores over distinct base arrays must terminate (the
        // Fourier–Motzkin blow-up is budget-bounded); a sound verdict is fine.
        let script = "
            (declare-const a (Array Int Int)) (declare-const b (Array Int Int))
            (assert (= (store a 0 1) (store b 0 1)))
            (check-sat)
        ";
        let out = run(script).unwrap();
        assert!(
            matches!(out[0].as_str(), "sat" | "unknown"),
            "expected a sound verdict, got {}",
            out[0]
        );
    }

    #[test]
    fn array_satisfiable() {
        let script = "
            (declare-const a (Array Int Int)) (declare-const i Int) (declare-const v Int)
            (assert (= (select (store a i v) i) v))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["sat"]);
    }

    #[test]
    fn is_int_symbolic() {
        // is_int(x) ⟺ ⌊x⌋ = x.
        assert_eq!(
            run("(declare-const x Real)(assert (is_int x))(assert (= x 2.5))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run("(declare-const x Real)(assert (not (is_int x)))(assert (= (* 2 x) 3))(check-sat)")
                .unwrap(),
            alloc::vec!["sat"]
        );
    }

    #[test]
    fn integer_gcd_inequality_tightening() {
        // 3x−3y ∈ [1,2]: the real relaxation is feasible (x−y ∈ [1/3, 2/3]) but
        // no integer x−y lies in it. GCD tightening (÷3, round bounds) turns this
        // into x−y ≥ 1 ∧ x−y ≤ 0, which Fourier–Motzkin refutes.
        assert_eq!(
            run("(declare-const x Int)(declare-const y Int)\
                 (assert (>= (- (* 3 x) (* 3 y)) 1))(assert (<= (- (* 3 x) (* 3 y)) 2))\
                 (check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // 2x+2y = 1 is integer-infeasible (odd = even).
        assert_eq!(
            run("(declare-const x Int)(declare-const y Int)\
                 (assert (>= (+ (* 2 x) (* 2 y)) 1))(assert (<= (+ (* 2 x) (* 2 y)) 1))\
                 (check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // …but 3x−3y = 3 (⇒ x−y = 1) stays satisfiable.
        assert_eq!(
            run("(declare-const x Int)(declare-const y Int)\
                 (assert (= (- (* 3 x) (* 3 y)) 3))(check-sat)")
            .unwrap(),
            alloc::vec!["sat"]
        );
    }

    #[test]
    fn negative_literals() {
        // z3 accepts `-1` / `-2.5` as numerals (strict SMT-LIB writes `(- 1)`).
        assert_eq!(
            run("(declare-const x Int)(assert (= x -5))(assert (> x 0))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run("(declare-const b Int)(assert (= (* -1 b) 2))(assert (>= (* -1 b) 8))(check-sat)")
                .unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run("(declare-const x Real)(assert (= x -2.5))(assert (< x 0.0))(check-sat)").unwrap(),
            alloc::vec!["sat"]
        );
        // The `-` operator is unaffected.
        assert_eq!(
            run("(declare-const x Int)(assert (= (- 3 1) 2))(check-sat)").unwrap(),
            alloc::vec!["sat"]
        );
    }

    #[test]
    fn integer_implied_equality() {
        // 6x−4y ∈ [1,3] gcd-tightens to the pinned 3x−2y ∈ [1,1], i.e. the
        // equation 3x−2y = 1 (x=1,y=1) — recovered as an implied equality and
        // solved by the Diophantine witness.
        assert_eq!(
            run("(declare-const x Int)(declare-const y Int)\
                 (assert (<= (- (* 6 x) (* 4 y)) 3))(assert (>= (- (* 6 x) (* 4 y)) 1))\
                 (check-sat)")
            .unwrap(),
            alloc::vec!["sat"]
        );
        // 2x−2y = 1 (odd = even) is unsat.
        assert_eq!(
            run("(declare-const x Int)(declare-const y Int)\
                 (assert (<= (- (* 2 x) (* 2 y)) 1))(assert (>= (- (* 2 x) (* 2 y)) 1))\
                 (check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn integer_dark_shadow_with_equality() {
        // Equality + unbounded inequalities: 2b=6 ⇒ b=3, leaving a≤2 ∧ c≤a−1
        // (both unbounded below). The dark shadow eliminates equalities first,
        // then builds and verifies a witness (a=2,b=3,c=1).
        assert_eq!(
            run(
                "(declare-const a Int)(declare-const b Int)(declare-const c Int)\
                 (assert (<= (+ a b) 5))(assert (>= (- a c) 1))(assert (= (* 2 b) 6))\
                 (check-sat)"
            )
            .unwrap(),
            alloc::vec!["sat"]
        );
    }

    #[test]
    fn integer_dark_shadow_sat() {
        // Unbounded feasible integer systems that branch-and-bound cannot
        // converge on: the dark shadow constructs and verifies a witness.
        assert_eq!(
            run("(declare-const a Int)(declare-const b Int)\
                 (assert (>= (- a b) 1))(assert (<= (- a b) 5))(check-sat)")
            .unwrap(),
            alloc::vec!["sat"]
        );
        assert_eq!(
            run("(declare-const x Int)(declare-const y Int)\
                 (assert (<= (+ (* 3 x) (* 2 y)) 10))(assert (>= (+ (* 3 x) (* 2 y)) 5))\
                 (assert (>= x 0))(assert (>= y 0))(check-sat)")
            .unwrap(),
            alloc::vec!["sat"]
        );
    }

    #[test]
    fn integer_fourier_motzkin_unsat() {
        // 2a+4b ∈ [3,5] ∧ a = b: real-feasible (a ∈ [1/2, 5/6]) but no integer
        // solution — eliminating b and tightening (6a ∈ [3,5] → a≥1 ∧ a≤0)
        // refutes it, which branch-and-bound alone cannot on the unbounded system.
        assert_eq!(
            run("(declare-const a Int)(declare-const b Int)\
                 (assert (<= (+ (* 2 a) (* 4 b)) 5))(assert (>= (+ (* 2 a) (* 4 b)) 3))\
                 (assert (= a b))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn unbounded_diophantine() {
        // 6a+4b=2 (gcd 2 | 2) is satisfiable but unbounded, so branch-and-bound
        // cannot converge; a verified integer witness decides it.
        assert_eq!(
            run("(declare-const a Int)(declare-const b Int)\
                 (assert (= (+ (* 6 a) (* 4 b)) 2))(check-sat)")
            .unwrap(),
            alloc::vec!["sat"]
        );
        // Still sat under a one-sided bound (the witness search covers the
        // general solution).
        assert_eq!(
            run("(declare-const a Int)(declare-const b Int)\
                 (assert (= (+ (* 6 a) (* 4 b)) 2))(assert (>= a 100))(check-sat)")
            .unwrap(),
            alloc::vec!["sat"]
        );
        // gcd 2 does not divide 3 → unsat.
        assert_eq!(
            run("(declare-const a Int)(declare-const b Int)\
                 (assert (= (+ (* 6 a) (* 4 b)) 3))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // Three variables: gcd(6,10,15)=1 divides 1 → sat; a wrong-parity RHS is
        // unsat.
        assert_eq!(
            run(
                "(declare-const a Int)(declare-const b Int)(declare-const c Int)\
                 (assert (= (+ (* 6 a) (* 10 b) (* 15 c)) 1))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["sat"]
        );
        assert_eq!(
            run(
                "(declare-const a Int)(declare-const b Int)(declare-const c Int)\
                 (assert (= (+ (* 6 a) (* 10 b) (* 4 c)) 1))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // A system: eliminate c=3-b (unit coefficient), reducing to 6a+4b=2.
        assert_eq!(
            run(
                "(declare-const a Int)(declare-const b Int)(declare-const c Int)\
                 (assert (= (+ (* 6 a) (* 4 b)) 2))(assert (= (+ b c) 3))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["sat"]
        );
    }

    #[test]
    fn divmod_linking() {
        // mod is in range and consistent with div.
        assert_eq!(
            run("(declare-const x Int)(assert (>= (mod x 5) 5))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run(
                "(declare-const x Int)(assert (= (mod x 4) 1))(assert (= (div x 4) 2))\
                 (assert (not (= x 9)))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // Common multiple: nothing in (0,6) is divisible by both 2 and 3.
        assert_eq!(
            run(
                "(declare-const x Int)(assert (= (mod x 2) 0))(assert (= (mod x 3) 0))\
                 (assert (> x 0))(assert (< x 6))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // Symbolic divisor: the Euclidean identity `a = b·div(a,b) + mod(a,b)`
        // holds (guarded by b≠0), so `b·div(a,b)+mod(a,b)=5` forces `a=5`.
        assert_eq!(
            run("(declare-const a Int)(declare-const b Int)(assert (> b 0))\
                 (assert (= (+ (* b (div a b))(mod a b)) 5))(assert (not (= a 5)))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // div/mod by literal 0 is unconstrained ⇒ satisfiable.
        assert_eq!(
            run("(declare-const y Int)(assert (= (mod 5 y) 3))(assert (= y 0))(check-sat)")
                .unwrap(),
            alloc::vec!["sat"]
        );
        // Symbolic divisor abstracted with the Euclidean constraints: a pinned
        // quotient linearizes the goal (`div(100,y)=7 ∧ y>0` ⇒ sat), and the
        // range `0 ≤ mod < |divisor|` refutes out-of-range mods.
        assert_eq!(
            run("(declare-const y Int)(assert (= (div 100 y) 7))(assert (> y 0))(check-sat)")
                .unwrap(),
            alloc::vec!["sat"]
        );
        assert_eq!(
            run("(declare-const x Int)(declare-const y Int)\
                 (assert (>= (mod x y) y))(assert (> y 0))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run("(declare-const x Int)(declare-const y Int)\
                 (assert (< (mod x y) 0))(assert (not (= y 0)))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // SAT witness by enumerating a small divisor: `mod(35,y)≥1 ∧ y<6` at y=2.
        assert_eq!(
            run("(declare-const y Int)(assert (>= (mod 35 y) 1))(assert (< y 6))(check-sat)")
                .unwrap(),
            alloc::vec!["sat"]
        );
        assert_eq!(
            run("(declare-const y Int)(assert (= (mod 26 y) 1))(assert (> y 0))(check-sat)")
                .unwrap(),
            alloc::vec!["sat"]
        );
    }

    #[test]
    fn square_nonnegativity() {
        // A square cannot be negative — the axiom (* x x) ≥ 0 refutes these.
        assert_eq!(
            run("(declare-const x Real)(assert (< (* x x) 0.0))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
        // Product-sign rule: two positives cannot multiply to a negative.
        assert_eq!(
            run("(declare-const x Int)(declare-const y Int)\
                 (assert (> x 0))(assert (> y 0))(assert (< (* x y) 0))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run("(declare-const x Real)(assert (= (* x x) (- 4.0)))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
        // Sum of squares plus a positive constant is positive.
        assert_eq!(
            run("(declare-const x Real)(declare-const y Real)\
                 (assert (< (+ (* x x) (* y y) 1.0) 0.0))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn chc_transition_system_decided() {
        // An **unsafe** CHC transition system: `inv(0)`, `inv(x) ⇒ inv(x+1)`,
        // query `inv(x) ∧ x=2 ⇒ false`. Bounded model checking reaches `inv(2)`,
        // deriving the counterexample ⇒ the CHC system is unsat (matches z3).
        assert_eq!(
            run("(declare-fun inv (Int) Bool)\
                 (assert (forall ((x Int)) (=> (= x 0) (inv x))))\
                 (assert (forall ((x Int)(y Int)) (=> (and (inv x) (= y (+ x 1))) (inv y))))\
                 (assert (forall ((x Int)) (=> (and (inv x) (= x 2)) false)))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // A **safe** system: `inv(x) ∧ x<0 ⇒ false` — `x ≥ 0` is 1-inductive, so
        // k-induction proves it satisfiable (safe).
        assert_eq!(
            run("(declare-fun inv (Int) Bool)\
                 (assert (forall ((x Int)) (=> (= x 0) (inv x))))\
                 (assert (forall ((x Int)(y Int)) (=> (and (inv x) (= y (+ x 1))) (inv y))))\
                 (assert (forall ((x Int)) (=> (and (inv x) (< x 0)) false)))(check-sat)")
            .unwrap(),
            alloc::vec!["sat"]
        );
        // A recursive *function* seeded by a ground application still decides sat.
        assert_eq!(
            run(
                "(define-fun-rec f ((n Int)) Int (ite (<= n 0) 1 (* n (f (- n 1)))))\
                 (assert (= (f 3) 6))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["sat"]
        );
    }

    #[test]
    fn nonlinear_integer_equality_bounds_decide() {
        // Square bounds derived from a nonlinear EQUALITY box the integer
        // variables, so exhaustive search refutes/decides (was `unknown`).
        // `x²+y²=3` has no integer solution.
        assert_eq!(
            run("(declare-const x Int)(declare-const y Int)\
                 (assert (= (+ (* x x)(* y y)) 3))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // `x²=2y² ∧ 0<x<5` — bound y via the negated orientation `2y²=x²`.
        assert_eq!(
            run("(declare-const x Int)(declare-const y Int)\
                 (assert (= (* x x)(* 2 (* y y))))(assert (> x 0))(assert (< x 5))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // …but a solvable one is sat: `x²+y²=25` with x,y>0 ⇒ (3,4).
        assert_eq!(
            run("(declare-const x Int)(declare-const y Int)\
                 (assert (= (+ (* x x)(* y y)) 25))(assert (> x 0))(assert (> y 0))(check-sat)")
            .unwrap(),
            alloc::vec!["sat"]
        );
    }

    #[test]
    fn nonlinear_now_decided_matches_z3() {
        // Substituting a variable pinned by an equality linearizes the product:
        // `x*y = 6 ∧ x = 2` ⇒ `2*y = 6`, decided sat (matches z3).
        assert_eq!(
            run("(declare-const x Int)(declare-const y Int)(assert (= (* x y) 6))(assert (= x 2))(check-sat)")
                .unwrap(),
            alloc::vec!["sat"]
        );
        // The univariate integer procedure: `x*x = 2` has no integer root ⇒ unsat.
        assert_eq!(
            run("(declare-const x Int)(assert (= (* x x) 2))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
        // Over the reals `x*x = 2` is satisfiable (x = ±√2) via real-root isolation.
        assert_eq!(
            run("(declare-const x Real)(assert (= (* x x) 2))(check-sat)").unwrap(),
            alloc::vec!["sat"]
        );
        // Constant coefficient is linear — still decided.
        assert_eq!(
            run("(declare-const x Int)(assert (= (* 3 x) 9))(check-sat)").unwrap(),
            alloc::vec!["sat"]
        );
    }

    #[test]
    fn echo_and_get_info() {
        // echo prints the string content; string literals with spaces tokenize
        // as one token.
        let script = "
            (echo \"hello world\")
            (get-info :name)
            (declare-const x Int) (assert (> x 0)) (check-sat)
        ";
        assert_eq!(
            run(script).unwrap(),
            alloc::vec!["hello world", "(:name \"z3rs\")", "sat"]
        );
    }

    #[test]
    fn bitvector_arithmetic_and_literals() {
        // 8-bit wrap: 0xff + 1 = 0.
        let wrap = "
            (declare-const x (_ BitVec 8))
            (assert (= x #xff)) (assert (not (= (bvadd x #x01) #x00)))
            (check-sat)
        ";
        assert_eq!(run(wrap).unwrap(), alloc::vec!["unsat"]);
        // Satisfiable: x + y = 10 with x < 5.
        let sat = "
            (declare-const x (_ BitVec 8)) (declare-const y (_ BitVec 8))
            (assert (= (bvadd x y) #x0a)) (assert (bvult x #x05))
            (check-sat)
        ";
        assert_eq!(run(sat).unwrap(), alloc::vec!["sat"]);
        // (_ bvN w) literal form.
        assert_eq!(
            run("(assert (= (_ bv5 8) #x05))(check-sat)").unwrap(),
            alloc::vec!["sat"]
        );
    }

    #[test]
    fn bitvector_concat_extract() {
        // Splitting a byte and recombining gives it back.
        let id = "
            (declare-const x (_ BitVec 8))
            (assert (not (= (concat ((_ extract 7 4) x) ((_ extract 3 0) x)) x)))
            (check-sat)
        ";
        assert_eq!(run(id).unwrap(), alloc::vec!["unsat"]);
        // concat literal.
        assert_eq!(
            run("(assert (not (= (concat #x0f #xf0) #x0ff0)))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn bitvector_bitwise_and_compare() {
        // x & 0 = 0 always; x <u x never.
        assert_eq!(
            run("(declare-const x (_ BitVec 4))(assert (not (= (bvand x #b0000) #b0000)))(check-sat)")
                .unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run("(declare-const x (_ BitVec 8))(assert (bvult x x))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn bv_comp_reductions_conversions() {
        // bvcomp equality, reductions, and constant int/bv conversions.
        assert_eq!(
            run(
                "(declare-const x (_ BitVec 4))(declare-const y (_ BitVec 4))\
                 (assert (= (bvcomp x y) #b1))(assert (not (= x y)))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run("(assert (not (= (bvredand #xff) #b1)))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run("(assert (not (= (bv2int #x0f) 15)))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run("(assert (not (= ((_ int2bv 4) 17) #x1)))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run("(assert (not (= (sbv_to_int #xff) (- 1))))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn define_sort_macros() {
        // Non-parametric alias.
        assert_eq!(
            run("(define-sort MyInt () Int)(declare-const x MyInt)\
                 (assert (> x 5))(assert (< x 5))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // Parametric macro expanded with arguments.
        assert_eq!(
            run(
                "(define-sort Pair (X Y) (Array X Y))(declare-const a (Pair Int Bool))\
                 (assert (select a 3))(assert (not (select a 3)))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn datatype_match_expression() {
        let o = "(declare-datatypes ((Opt 0)) (((none) (some (val Int)))))";
        // (match o ((none 0) ((some v) v))) selects the field for `some`.
        assert_eq!(
            run(&alloc::format!(
                "{o}(declare-const o Opt)(assert (= o (some 7)))\
                 (assert (not (= (match o ((none 0) ((some v) v))) 7)))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // …and the constant for `none`, via a wildcard-free exhaustive match.
        assert_eq!(
            run(&alloc::format!(
                "{o}(declare-const o Opt)(assert (= o none))\
                 (assert (not (= (match o ((none 0) ((some v) v))) 0)))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn regex_membership_folds() {
        // "a5z" matches letter·digit·letter.
        let re =
            "(re.++ (re.range \"a\" \"z\") (re.++ (re.range \"0\" \"9\") (re.range \"a\" \"z\")))";
        assert_eq!(
            run(&alloc::format!(
                "(assert (not (str.in_re \"a5z\" {re})))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // (ab)* matches "abab" but not "aba".
        assert_eq!(
            run("(assert (not (str.in_re \"abab\" (re.* (str.to_re \"ab\")))))(check-sat)")
                .unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run("(assert (str.in_re \"aba\" (re.* (str.to_re \"ab\"))))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn session_is_incremental() {
        let mut s = Session::new();
        // State carries across eval calls, including the push/pop stack.
        assert!(
            s.eval("(declare-const n Int)(assert (> n 0))")
                .unwrap()
                .is_empty()
        );
        assert_eq!(
            s.eval("(push)(assert (< n 0))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(s.eval("(pop)(check-sat)").unwrap(), alloc::vec!["sat"]);
    }

    #[test]
    fn divmod_symbolic_divisor_complete() {
        // Constant-dividend div/mod by a symbolic divisor is now fully decided.
        // SAT via a zero divisor (unspecified) or a witness:
        assert_eq!(
            run("(declare-const y Int)(assert (<= (mod (- 29) y) (- 8)))(check-sat)").unwrap(),
            alloc::vec!["sat"]
        );
        // UNSAT via the complete finite-enumeration + stable-tail decision:
        assert_eq!(
            run("(declare-const y Int)(assert (< (div 31 y) (- 4)))(assert (> y 2))(check-sat)")
                .unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run("(declare-const y Int)(assert (> (div 27 y) 11))(assert (< y 0))(check-sat)")
                .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn symbolic_fp_min_max() {
        // fp.min/max via the BV ite circuit (uses the ordered comparison).
        assert_eq!(
            run("(declare-const x Float32)(declare-const y Float32)\
                 (assert (fp.gt (fp.min x y) x))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run("(declare-const x Float32)(declare-const y Float32)\
                 (assert (fp.lt (fp.max x y) y))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run("(declare-const x Float32)(declare-const y Float32)\
                 (assert (fp.lt (fp.min x y) (fp.max x y)))(check-sat)")
            .unwrap(),
            alloc::vec!["sat"]
        );
    }

    #[test]
    fn symbolic_fp_mul_bitblast() {
        // fp.mul bit-blasted (Float16, concrete bit-literals): 2·3=6, 1.5·2=3.
        assert_eq!(
            run(
                "(assert (not (fp.eq (fp.mul RNE (fp #b0 #b10000 #b0000000000) \
                 (fp #b0 #b10000 #b1000000000)) (fp #b0 #b10001 #b1000000000))))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run(
                "(assert (not (fp.eq (fp.mul RNE (fp #b0 #b01111 #b1000000000) \
                 (fp #b0 #b10000 #b0000000000)) (fp #b0 #b10000 #b1000000000))))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn symbolic_fp_add_sub_bitblast() {
        // Bit-exact add/sub bit-blasted to QF_BV (verified against z3).
        // 1.0 + 1.0 = 2.0 (Float16).
        assert_eq!(
            run("(declare-fun x () (_ FloatingPoint 5 11))\
                 (assert (= x (fp #b0 #b01111 #b0000000000)))\
                 (assert (not (= (fp.add RNE x x) (fp #b0 #b10000 #b0000000000))))\
                 (check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // Round-to-odd style tie under RTP vs RTZ differs: 1.0 + tiny with RTP
        // rounds up, with RTZ stays 1.0 (Float16, tiny = smallest subnormal).
        assert_eq!(
            run("(declare-fun x () (_ FloatingPoint 5 11))\
                 (assert (= x (fp #b0 #b01111 #b0000000000)))\
                 (assert (= (fp.add RTP x (fp #b0 #b00000 #b0000000001))\
                             (fp #b0 #b01111 #b0000000001)))\
                 (check-sat)")
            .unwrap(),
            alloc::vec!["sat"]
        );
        assert_eq!(
            run("(declare-fun x () (_ FloatingPoint 5 11))\
                 (assert (= x (fp #b0 #b01111 #b0000000000)))\
                 (assert (not (= (fp.add RTZ x (fp #b0 #b00000 #b0000000001))\
                                  (fp #b0 #b01111 #b0000000000))))\
                 (check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // fp.sub: 2.0 - 1.0 = 1.0 (Float32).
        assert_eq!(
            run("(declare-fun x () (_ FloatingPoint 8 24))\
                 (assert (= x (fp #b0 #x80 #b00000000000000000000000)))\
                 (assert (not (= (fp.sub RNE x (fp #b0 #x7f #b00000000000000000000000))\
                                  (fp #b0 #x7f #b00000000000000000000000))))\
                 (check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // Overflow to +inf: max-finite + max-finite under RNE (Float16).
        assert_eq!(
            run("(declare-fun x () (_ FloatingPoint 5 11))\
                 (assert (= x (fp #b0 #b11110 #b1111111111)))\
                 (assert (not (= (fp.add RNE x x) (_ +oo 5 11))))\
                 (check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // +inf + -inf = NaN.
        assert_eq!(
            run(
                "(assert (not (= (fp.add RNE (_ +oo 5 11) (_ -oo 5 11)) (_ NaN 5 11))))\
                 (check-sat)"
            )
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn symbolic_fp_ordered_compare() {
        // Ordered fp comparisons via the direct sign+magnitude circuit — the
        // transitivity contradiction is decided fast (was a hang with the
        // monotone-key encoding).
        assert_eq!(
            run("(declare-const x Float32)(declare-const y Float32)\
                 (assert (fp.lt x y))(assert (fp.lt y x))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run("(declare-const x Float32)(assert (fp.lt x x))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run("(declare-const x Float32)(declare-const y Float32)\
                 (assert (fp.geq x y))(assert (fp.gt y x))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run(
                "(declare-const x Float32)(declare-const y Float32)(assert (fp.lt x y))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["sat"]
        );
    }

    #[test]
    fn symbolic_fp_abs_neg_decide() {
        // Symbolic fp.abs/neg are sign-bit ops decided by the BV engine.
        assert_eq!(
            run("(declare-const x Float32)(assert (fp.isNegative (fp.abs x)))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run(
                "(declare-const x Float32)(assert (not (fp.eq (fp.neg (fp.neg x)) x)))\
                 (assert (not (fp.isNaN x)))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run(
                "(declare-const x Float32)(assert (fp.isPositive (fp.abs x)))\
                 (assert (not (fp.isZero x)))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["sat"]
        );
    }

    #[test]
    fn fp_ops_decide_and_never_contradict() {
        // fp.fma / fp.sqrt are now bit-blasted and decide, matching z3 (they must
        // never give a wrong verdict — a bug once bit-blasted them to a free
        // bit-vector, giving `sat` where z3 is unsat).
        let t = "((_ to_fp 11 53) RNE";
        // fma(2,3,1) = 7, not NaN ⇒ `¬isNaN(fma)` is sat.
        assert_eq!(
            run(&alloc::format!(
                "(assert (not (fp.isNaN (fp.fma RNE {t} 2.0) {t} 3.0) {t} 1.0)))))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["sat"]
        );
        // √9 = 3 ⇒ `¬(√9 = 3)` is unsat.
        assert_eq!(
            run(&alloc::format!(
                "(assert (not (fp.eq (fp.sqrt RNE {t} 9.0)) {t} 3.0))))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn symbolic_floating_point_via_bv() {
        let d = "(declare-const x (_ FloatingPoint 11 53))";
        // A value can't be both NaN and zero (classification bit-blasted to BV).
        assert_eq!(
            run(&alloc::format!(
                "{d}(assert (fp.isNaN x))(assert (fp.isZero x))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // Equality of the bit representations interacts with classification:
        // x = NaN forces isNaN(x).
        assert_eq!(
            run(&alloc::format!(
                "{d}(assert (= x (_ NaN 11 53)))(assert (not (fp.isNaN x)))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // Some value is NaN — satisfiable.
        assert_eq!(
            run(&alloc::format!("{d}(assert (fp.isNaN x))(check-sat)")).unwrap(),
            alloc::vec!["sat"]
        );
        // IEEE fp.eq: NaN is not equal to itself; a NaN operand rules it out.
        assert_eq!(
            run("(assert (fp.eq (_ NaN 11 53) (_ NaN 11 53)))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run(&alloc::format!(
                "{d}(declare-const y (_ FloatingPoint 11 53))\
                 (assert (fp.eq x y))(assert (fp.isNaN x))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn floating_point_folding() {
        let fp = "((_ to_fp 11 53) RNE";
        // IEEE arithmetic: 1.5 + 2.5 = 4.0.
        assert_eq!(
            run(&alloc::format!(
                "(assert (not (= (fp.add RNE {fp} 1.5) {fp} 2.5)) {fp} 4.0))))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // Division by zero yields infinity.
        assert_eq!(
            run(&alloc::format!(
                "(assert (not (fp.eq (fp.div RNE {fp} 1.0) {fp} 0.0)) (_ +oo 11 53))))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // NaN is not fp.eq to itself; +0 and -0 are fp.eq but structurally unequal.
        assert_eq!(
            run("(assert (fp.eq (_ NaN 11 53) (_ NaN 11 53)))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run("(assert (= (_ +zero 11 53) (_ -zero 11 53)))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn sequence_structural_fragment() {
        // Length and indexing of a structurally-built sequence.
        assert_eq!(
            run("(declare-const x Int)(declare-const y Int)\
                 (assert (not (= (seq.nth (seq.++ (seq.unit x) (seq.unit y)) 1) y)))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // Length mismatch makes sequences unequal.
        assert_eq!(
            run("(declare-const x Int)\
                 (assert (= (seq.++ (seq.unit x) (seq.unit x)) (seq.unit x)))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // Element-wise equality: (seq.unit x) = (seq.unit y) forces x = y.
        assert_eq!(
            run("(declare-const x Int)(declare-const y Int)\
                 (assert (= (seq.unit x) (seq.unit y)))(assert (not (= x y)))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn bitvector_width_mismatch_rejected() {
        // A bit-vector op with mismatched operand widths is ill-typed (z3 errors
        // too) — reject it rather than build a garbage term that could answer
        // unsoundly.
        assert!(
            run("(declare-const a (_ BitVec 4))(assert (bvsgt (concat a a) a))(check-sat)")
                .is_err()
        );
        assert!(
            run(
                "(declare-const a (_ BitVec 8))(declare-const b (_ BitVec 4))\
                 (assert (= (bvadd a b) a))(check-sat)"
            )
            .is_err()
        );
    }

    #[test]
    fn bitvector_overflow_predicates() {
        // #xf + #xf overflows unsigned 4-bit addition.
        assert_eq!(
            run("(assert (not (bvuaddo #xf #xf)))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
        // #x8 (=-8) negated overflows signed 4-bit (it is INT_MIN).
        assert_eq!(
            run("(assert (not (bvnego #x8)))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
        // Symbolic: an 8-bit a ≤ 15 cannot overflow a*a.
        assert_eq!(
            run("(declare-const a (_ BitVec 8))(assert (bvumulo a a))\
                 (assert (bvule a #x0f))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn more_string_operations() {
        // Lexicographic order, replace-all, and code conversions fold.
        for (script, expect) in [
            ("(assert (not (str.< \"abc\" \"abd\")))(check-sat)", "unsat"),
            (
                "(assert (not (= (str.replace_all \"aXaXa\" \"X\" \"-\") \"a-a-a\")))(check-sat)",
                "unsat",
            ),
            (
                "(assert (not (= (str.to_code \"A\") 65)))(check-sat)",
                "unsat",
            ),
            (
                "(assert (not (= (str.from_code 66) \"B\")))(check-sat)",
                "unsat",
            ),
        ] {
            assert_eq!(
                run(script).unwrap(),
                alloc::vec![expect],
                "script: {script}"
            );
        }
    }

    #[test]
    fn concat_boundary_char_mismatch() {
        // Differing determinable last characters make the equation unsat.
        assert_eq!(
            run("(declare-const x String)(declare-const y String)\
                 (assert (= (str.++ x \"a\") (str.++ y \"b\")))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // Differing first characters, likewise.
        assert_eq!(
            run("(declare-const x String)(declare-const y String)\
                 (assert (= (str.++ \"a\" x) (str.++ \"b\" y)))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn concat_equation_cancellation() {
        // Left cancellation: (str.++ x y) = (str.++ x z) ⟹ y = z.
        assert_eq!(
            run(
                "(declare-const x String)(declare-const y String)(declare-const z String)\
                 (assert (= (str.++ x y) (str.++ x z)))(assert (= y \"a\"))\
                 (assert (not (= z \"a\")))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // Prefix + suffix cancellation around a middle variable.
        assert_eq!(
            run("(declare-const x String)(declare-const y String)\
                 (assert (= (str.++ \"a\" x \"b\") (str.++ \"a\" y \"b\")))\
                 (assert (= x \"1\"))(assert (not (= y \"1\")))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // (str.++ x y) = x ⟹ y = "".
        assert_eq!(
            run("(declare-const x String)(declare-const y String)\
                 (assert (= (str.++ x y) x))(assert (not (= y \"\")))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn string_concat_word_equations() {
        // (str.++ x y) = "abcd" ∧ x = "ab" forces y = "cd".
        assert_eq!(
            run("(declare-const x String)(declare-const y String)\
                 (assert (= (str.++ x y) \"abcd\"))(assert (= x \"ab\"))\
                 (assert (not (= y \"cd\")))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // A suffix that can't fit makes it unsat.
        assert_eq!(
            run("(declare-const x String)(assert (= (str.++ x \"z\") \"abcd\"))(check-sat)")
                .unwrap(),
            alloc::vec!["unsat"]
        );
        // Nested/flat concatenation with a fixed middle part.
        assert_eq!(
            run("(declare-const x String)\
                 (assert (= (str.++ \"a\" x \"c\") \"abc\"))(assert (not (= x \"b\")))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn nonlinear_power_is_gated() {
        // Regression: `(^ base exp)` with a non-integer exponent or symbolic base
        // is an opaque nonlinear term; a `sat` over it would be unsound
        // (√2 = 2 and x² = −1 are false but the unconstrained UF made them sat).
        assert_ne!(
            run("(assert (= (^ 2.0 0.5) 2.0))(check-sat)").unwrap(),
            alloc::vec!["sat"]
        );
        assert_ne!(
            run("(declare-const x Real)(assert (= (^ x 2.0) (- 1.0)))(check-sat)").unwrap(),
            alloc::vec!["sat"]
        );
        // Integer powers still fold exactly.
        assert_eq!(
            run("(assert (= (^ 2 3) 8))(check-sat)").unwrap(),
            alloc::vec!["sat"]
        );
        assert_eq!(
            run("(assert (= (^ 2 3) 9))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn set_sort_is_array_to_bool() {
        // (Set T) is (Array T Bool): a set backed by a const-false array has no
        // members. (z3 supports the sort; its set.* operation names are cvc5-only,
        // so we do not interpret those — matching z3, which errors on them.)
        assert_eq!(
            run("(declare-const s (Set Int))\
                 (assert (= s ((as const (Set Int)) false)))\
                 (assert (select s 5))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn pseudo_boolean_cardinality() {
        // (_ at-least k) / (_ at-most k): at least/most k of the args are true.
        assert_eq!(
            run("(declare-const a Bool)(declare-const b Bool)\
                 (assert ((_ at-least 1) a b))(assert (not a))(assert (not b))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run("(declare-const a Bool)(declare-const b Bool)\
                 (assert ((_ at-most 1) a b))(assert a)(assert b)(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run(
                "(declare-const a Bool)(declare-const b Bool)(declare-const c Bool)\
                 (assert ((_ at-least 2) a b c))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["sat"]
        );
    }

    #[test]
    fn bv2int_range() {
        // bv2int of an n-bit vector lies in [0, 2ⁿ−1]. When the vector is used
        // only via bv2int, it is replaced by a bounded integer, so these decide.
        assert_eq!(
            run("(declare-const a (_ BitVec 4))(assert (< (bv2int a) 0))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run("(declare-const a (_ BitVec 4))(assert (> (bv2int a) 15))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
        // Sum of two 8-bit values cannot exceed 510.
        assert_eq!(
            run(
                "(declare-const a (_ BitVec 8))(declare-const b (_ BitVec 8))\
                 (assert (> (+ (bv2int a) (bv2int b)) 600))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run("(declare-const a (_ BitVec 4))(assert (= (bv2int a) 7))(check-sat)").unwrap(),
            alloc::vec!["sat"]
        );
        // Regression: a compound bv2int argument (int2bv(x)) must NOT be replaced
        // by a free integer — it carries the value x mod 2ⁿ. This is unsat
        // (round-trip identity for x in range), and must never answer sat.
        assert_ne!(
            run("(declare-const x Int)(assert (>= x 0))(assert (< x 16))\
                 (assert (not (= (bv2int ((_ int2bv 4) x)) x)))(check-sat)")
            .unwrap(),
            alloc::vec!["sat"]
        );
    }

    #[test]
    fn seq_len_symbolic() {
        // Symbolic sequence length is a non-negative Int, so arithmetic bounds
        // decide (previously gated to unknown).
        assert_eq!(
            run("(declare-const s (Seq Int))(assert (< (seq.len s) 0))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run("(declare-const s (Seq Int))(assert (>= (seq.len s) 5))\
                 (assert (<= (seq.len s) 3))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run("(declare-const s (Seq Int))(assert (= (seq.len s) 3))(check-sat)").unwrap(),
            alloc::vec!["sat"]
        );
        // Emptiness biconditional `seq.len(s)=0 ⇔ s=empty` (fuzz-found spurious
        // sat in both directions).
        assert_eq!(
            run("(declare-const s (Seq Int))(assert (= (seq.len s) 0))\
                 (assert (not (= s (as seq.empty (Seq Int)))))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // A variable bound to a concrete sequence inherits its length by
        // congruence — `s=(seq.unit 1)` forces `seq.len(s)=1` (fuzz-found: a
        // conflicting length was spuriously sat), transitively through `t=s`.
        assert_eq!(
            run("(declare-const s (Seq Int))(assert (= s (seq.unit 1)))\
                 (assert (= (seq.len s) 5))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run("(declare-const s (Seq Int))(declare-const t (Seq Int))\
                 (assert (= s (seq.++ (seq.unit 1)(seq.unit 2))))(assert (= t s))\
                 (assert (= (seq.len t) 0))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run(
                "(declare-const s (Seq Int))(assert (= s (as seq.empty (Seq Int))))\
                 (assert (> (seq.len s) 0))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn str_len_nonnegative() {
        // A string's length is never negative — the symbolic str.len must carry
        // this axiom (regression: it was an unconstrained UF, so -1 looked sat).
        assert_eq!(
            run("(declare-const s String)(assert (= (str.len s) (- 1)))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run("(declare-const s String)(assert (< (str.len s) 0))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
        // …but a non-negative constraint is still satisfiable.
        assert_eq!(
            run("(declare-const s String)(assert (= (str.len s) 0))(check-sat)").unwrap(),
            alloc::vec!["sat"]
        );
        // Emptiness: `len(s)=0 ⇒ s=""`, so `len(s)=0 ∧ s≠""` is unsat (was a
        // fuzz-found spurious sat).
        assert_eq!(
            run("(declare-const s String)(assert (= (str.len s) 0))\
                 (assert (not (= s \"\")))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn string_predicate_length_links() {
        // `str.contains(s, sub) ⇒ len(s) ≥ len(sub)` etc. refute length
        // contradictions even with a symbolic string (was `unknown`).
        assert_eq!(
            run("(declare-const x String)(assert (str.contains x \"a\"))\
                 (assert (= (str.len x) 0))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run("(declare-const x String)(assert (str.prefixof \"abc\" x))\
                 (assert (< (str.len x) 2))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run("(declare-const x String)(assert (str.suffixof \"ab\" x))\
                 (assert (= (str.len x) 1))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn to_fp_from_bitvec_no_crash() {
        // Regression: `((_ to_fp eb sb) bv)` (bit-vector reinterpret form, no
        // rounding mode) indexed a missing argument and panicked. It must not
        // crash; a constant bit pattern folds to the FP literal.
        assert_eq!(
            run("(assert (fp.isNaN ((_ to_fp 8 24) #x7fc00000)))(check-sat)").unwrap(),
            alloc::vec!["sat"]
        );
        // Symbolic bit-vector: no crash (sound unknown or decided).
        assert_ne!(
            run("(declare-const x (_ BitVec 32))\
                 (assert (fp.isNaN ((_ to_fp 8 24) x)))(check-sat)")
            .unwrap(),
            alloc::vec!["error"]
        );
    }

    #[test]
    fn str_indexof_no_crash() {
        // Regression: `str.indexof` folding sliced past the end when the string
        // was shorter than the needle (hit via the witness search's empty
        // candidate) — it must never panic.
        assert_eq!(
            run("(assert (= (str.indexof \"ab\" \"abc\" 0) (- 1)))(check-sat)").unwrap(),
            alloc::vec!["sat"]
        );
        assert_eq!(
            run("(assert (= (str.indexof \"\" \"a\" 0) (- 1)))(check-sat)").unwrap(),
            alloc::vec!["sat"]
        );
        // A symbolic indexof no longer panics (decides via the witness search).
        assert_eq!(
            run("(declare-const x String)(assert (= (str.indexof x \"a\" 0) 3))(check-sat)")
                .unwrap(),
            alloc::vec!["sat"]
        );
    }

    #[test]
    fn string_witness_search_decides_sat() {
        // A concrete satisfying string is exhibited for symbolic-string goals
        // that were previously `unknown` (bounded witness search + re-fold).
        for s in [
            "(declare-const x String)(assert (= (str.at x 0) \"a\"))(check-sat)",
            "(declare-const x String)(assert (str.contains x \"ab\"))(assert (str.contains x \"cd\"))(check-sat)",
            "(declare-const x String)(assert (str.prefixof \"a\" x))(assert (str.suffixof \"b\" x))(assert (= (str.len x) 3))(check-sat)",
            "(declare-const x String)(assert (not (str.contains x \"a\")))(assert (= (str.len x) 2))(check-sat)",
            "(declare-const x String)(assert (str.contains x \"a\"))(assert (= (str.len x) 5))(check-sat)",
        ] {
            assert_eq!(run(s).unwrap(), alloc::vec!["sat"], "script: {s}");
        }
        // The witness search must NOT report a spurious `sat`: `str.at` yields a
        // ≤1-char string (can't equal "xyz"), and a variable pinned to "cd" does
        // not contain "z". These must not be `sat` (they stay sound: unknown or
        // unsat, never a wrong sat). Regression for a fuzz-found soundness bug
        // where new literals created during the search were not asserted distinct.
        for s in [
            "(declare-const x String)(assert (= (str.at x 0) \"xyz\"))(check-sat)",
            "(declare-const x String)(assert (= x \"cd\"))(assert (str.contains x \"z\"))(check-sat)",
            "(declare-const x String)(assert (= x \"cd\"))(assert (str.suffixof \"b\" x))(check-sat)",
        ] {
            assert_ne!(run(s).unwrap(), alloc::vec!["sat"], "spurious sat: {s}");
        }
    }

    #[test]
    fn string_fragment_decides() {
        // Constant folding of string operations.
        assert_eq!(
            run("(assert (not (= (str.++ \"ab\" (str.substr \"xcdy\" 1 2)) \"abcd\")))(check-sat)")
                .unwrap(),
            alloc::vec!["unsat"]
        );
        // Length reasoning through equality/congruence.
        assert_eq!(
            run("(declare-const x String)(assert (= x \"abc\"))\
                 (assert (= (str.len x) 4))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // Distinct string literals.
        assert_eq!(
            run("(declare-const x String)(assert (= x \"a\"))(assert (= x \"b\"))(check-sat)")
                .unwrap(),
            alloc::vec!["unsat"]
        );
        // A satisfiable length constraint on a free string.
        assert_eq!(
            run("(declare-const x String)(assert (= (str.len x) 5))(check-sat)").unwrap(),
            alloc::vec!["sat"]
        );
    }

    #[test]
    fn maxsat_soft_constraints() {
        // Two conflicting softs with weights 1 and 5: the optimum keeps the
        // weight-5 one, so a is sacrificed (a=false, b=true) — a unique optimum.
        let out = run(
            "(declare-const a Bool)(declare-const b Bool)(assert (not (and a b)))\
             (assert-soft a :weight 1)(assert-soft b :weight 5)(check-sat)(get-value (a b))",
        )
        .unwrap();
        assert_eq!(out[0], "sat");
        assert_eq!(out[1], "((a false) (b true))");
    }

    #[test]
    fn real_optimization() {
        // Attained maximum.
        let out = run(
            "(declare-const x Real)(assert (<= x 10.0))(assert (>= x 0.0))\
             (maximize x)(check-sat)(get-objectives)",
        )
        .unwrap();
        assert_eq!(out[0], "sat");
        assert!(out[1].contains("(x 10)"), "got {:?}", out[1]);
        // A fractional optimum.
        let out = run(
            "(declare-const x Real)(assert (>= (* 2.0 x) 3.0))(minimize x)(check-sat)(get-objectives)",
        )
        .unwrap();
        assert!(out[1].contains("(/ 3.0 2.0)"), "got {:?}", out[1]);
        // Unbounded.
        let out =
            run("(declare-const x Real)(assert (>= x 0.0))(maximize x)(check-sat)(get-objectives)")
                .unwrap();
        assert!(out[1].contains("(x oo)"), "got {:?}", out[1]);
        // A strict supremum in z3's epsilon form.
        let out =
            run("(declare-const x Real)(assert (< x 5.0))(maximize x)(check-sat)(get-objectives)")
                .unwrap();
        assert!(
            out[1].contains("(+ 5.0 (* (- 1.0) epsilon))"),
            "got {:?}",
            out[1]
        );
    }

    #[test]
    fn integer_optimization() {
        // Maximize a bounded objective.
        let out = run("(declare-const x Int)(assert (<= x 10))(assert (>= x 0))\
             (maximize x)(check-sat)(get-objectives)")
        .unwrap();
        assert_eq!(out[0], "sat");
        assert!(out[1].contains("(x 10)"), "got {:?}", out[1]);
        // Minimize.
        let out = run(
            "(declare-const x Int)(declare-const y Int)(assert (>= x 3))\
             (assert (>= y x))(minimize y)(check-sat)(get-objectives)",
        )
        .unwrap();
        assert!(out[1].contains("(y 3)"), "got {:?}", out[1]);
        // Unbounded.
        let out =
            run("(declare-const x Int)(assert (>= x 0))(maximize x)(check-sat)(get-objectives)")
                .unwrap();
        assert!(out[1].contains("(x oo)"), "got {:?}", out[1]);
    }

    #[test]
    fn recursive_datatype_acyclicity() {
        let l = "(declare-datatypes ((Lst 0)) (((nil) (cons (hd Int) (tl Lst)))))";
        // A list cannot contain itself.
        assert_eq!(
            run(&alloc::format!(
                "{l}(declare-const x Lst)(assert (= x (cons 1 x)))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // Selectors and testers still decide normally.
        assert_eq!(
            run(&alloc::format!(
                "{l}(assert (not (= (hd (cons 3 nil)) 3)))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run(&alloc::format!(
                "{l}(declare-const x Lst)(assert ((_ is cons) x))(assert (= (hd x) 5))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["sat"]
        );
    }

    #[test]
    fn mutually_recursive_datatype_acyclicity() {
        // Acyclicity must hold ACROSS mutually-recursive datatypes (fuzz-found
        // spurious sat): `x = nodeA(nodeB(x))` is unsat, but a finite term is sat.
        let d = "(declare-datatypes ((A 0)(B 0)) \
                 (((leafA)(nodeA (getb B)))((leafB)(nodeB (geta A)))))";
        assert_eq!(
            run(&alloc::format!(
                "{d}(declare-const x A)(assert (= x (nodeA (nodeB x))))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run(&alloc::format!(
                "{d}(declare-const x A)(declare-const y B)\
                 (assert (= x (nodeA y)))(assert (= y (nodeB x)))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run(&alloc::format!(
                "{d}(declare-const x A)(assert (= x (nodeA leafB)))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["sat"]
        );
    }

    #[test]
    fn variant_datatypes_decide() {
        let o = "(declare-datatypes ((Opt 0)) (((none) (some (val Int)))))";
        // Selector-over-constructor and distinctness.
        assert_eq!(
            run(&alloc::format!(
                "{o}(assert (not (= (val (some 7)) 7)))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run(&alloc::format!("{o}(assert (= none (some 3)))(check-sat)")).unwrap(),
            alloc::vec!["unsat"]
        );
        // A value can't satisfy two testers (exclusivity).
        assert_eq!(
            run(&alloc::format!(
                "{o}(declare-const a Opt)(assert ((_ is none) a))(assert ((_ is some) a))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // A tagged value with a constraint on its field is satisfiable.
        assert_eq!(
            run(&alloc::format!(
                "{o}(declare-const a Opt)(assert ((_ is some) a))(assert (> (val a) 5))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["sat"]
        );
    }

    #[test]
    fn record_datatypes_decide() {
        let p = "(declare-datatypes ((Pair 0)) (((mk-pair (fst Int) (snd Int)))))";
        // Selector-over-constructor (projection).
        assert_eq!(
            run(&alloc::format!(
                "{p}(assert (not (= (fst (mk-pair 3 4)) 3)))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // Constructor injectivity.
        assert_eq!(
            run(&alloc::format!(
                "{p}(declare-const a Int)(declare-const b Int)\
                 (assert (= (mk-pair a 1) (mk-pair 2 b)))\
                 (assert (not (and (= a 2) (= b 1))))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // Surjectivity (eta): every Pair is its own (fst, snd).
        assert_eq!(
            run(&alloc::format!(
                "{p}(declare-const q Pair)(assert (not (= q (mk-pair (fst q) (snd q)))))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn enum_datatypes_decide() {
        let dt = "(declare-datatypes () ((Color red green blue)))";
        // A constructor equality is unsat (constructors are distinct).
        assert_eq!(
            run(&alloc::format!("{dt}(assert (= red green))(check-sat)")).unwrap(),
            alloc::vec!["unsat"]
        );
        // Excluding every constructor is unsat (the domain axiom).
        assert_eq!(
            run(&alloc::format!(
                "{dt}(declare-const c Color)(assert (not (= c red)))\
                 (assert (not (= c green)))(assert (not (= c blue)))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // The tester and transitivity: c is red, so it can't also be green.
        assert_eq!(
            run(&alloc::format!(
                "{dt}(declare-const c Color)(assert ((_ is red) c))\
                 (assert ((_ is green) c))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn bv_get_value_produces_model() {
        let out = run(
            "(declare-const x (_ BitVec 8))(assert (= (bvadd x #x01) #x10))(check-sat)(get-value (x))",
        )
        .unwrap();
        assert_eq!(out[0], "sat");
        assert_eq!(out[1], "((x #x0f))");
    }

    #[test]
    fn qe_valid_universals_are_sat() {
        // Regression: valid universals must be sat, not refuted. A strictness bug
        // in the ≥/> negation once made these unsat.
        for body in [
            "(>= x x)",               // tautology
            "(=> (<= 0 x) (>= x 0))", // valid
            "(=> (and (<= 0 x) (<= x 2)) (>= x 0))",
            "(=> (> x 0) (>= x 1))", // valid over the integers
        ] {
            assert_eq!(
                run(&alloc::format!(
                    "(assert (forall ((x Int)) {body}))(check-sat)"
                ))
                .unwrap(),
                alloc::vec!["sat"],
                "body: {body}"
            );
        }
        // …while a genuinely false universal is still refuted.
        assert_eq!(
            run("(assert (forall ((x Int)) (=> (> x 0) (>= x 2))))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn quantifier_elimination_real_lra() {
        // ∀x∈[0,1]. x ≤ a  ⟺  a ≥ 1; contradicts a < 1.
        assert_eq!(
            run("(declare-const a Real)\
                 (assert (forall ((x Real)) (=> (and (<= 0.0 x) (<= x 1.0)) (<= x a))))\
                 (assert (< a 1.0))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // …satisfiable when a is large enough.
        assert_eq!(
            run("(declare-const a Real)\
                 (assert (forall ((x Real)) (=> (and (<= 0.0 x) (<= x 1.0)) (<= x a))))\
                 (assert (>= a 5.0))(check-sat)")
            .unwrap(),
            alloc::vec!["sat"]
        );
        // ∀x. x < 0 is false.
        assert_eq!(
            run("(assert (forall ((x Real)) (< x 0.0)))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
        // Integer QE (unit coefficients): ∀x∈[0,10]. x ≤ a ⟺ a ≥ 10.
        assert_eq!(
            run("(declare-const a Int)\
                 (assert (forall ((x Int)) (=> (and (<= 0 x) (<= x 10)) (<= x a))))\
                 (assert (< a 10))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // Non-unit coefficient falls back (sound unknown, not a wrong verdict).
        assert_eq!(
            run("(declare-const a Int)\
                 (assert (forall ((x Int)) (=> (<= (* 2 x) a) (<= x 3))))(check-sat)")
            .unwrap(),
            alloc::vec!["unknown"]
        );
    }

    #[test]
    fn quantifier_saturation_decides_sat() {
        // Datalog-style reachability (CHC): path(1,3) is derivable -> unsat.
        let rules = "(declare-fun edge (Int Int) Bool)(declare-fun path (Int Int) Bool)\
             (assert (forall ((a Int)(b Int)) (=> (edge a b) (path a b))))\
             (assert (forall ((a Int)(b Int)(c Int)) (=> (and (path a b)(edge b c)) (path a c))))\
             (assert (edge 1 2))(assert (edge 2 3))";
        assert_eq!(
            run(&alloc::format!(
                "{rules}(assert (not (path 1 3)))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // path(3,1) is NOT derivable; the finite instantiation saturates, so the
        // sat is complete (not unknown).
        assert_eq!(
            run(&alloc::format!(
                "{rules}(assert (not (path 3 1)))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["sat"]
        );
        // A universal over a finite (enum) domain: sat once saturated.
        assert_eq!(
            run("(declare-datatypes () ((C a b)))(declare-fun q (C) Bool)\
                 (assert (forall ((x C)) (q x)))(check-sat)")
            .unwrap(),
            alloc::vec!["sat"]
        );
    }

    #[test]
    fn quantifier_iterative_instantiation() {
        // Inductive unfolding: p(0), ∀x. p(x) ⇒ p(x+1), ¬p(3) is unsat only if
        // instantiation chains 0→1→2→3 (fixpoint instantiation).
        assert_eq!(
            run(
                "(declare-fun p (Int) Bool)(assert (forall ((x Int)) (=> (p x) (p (+ x 1)))))\
                 (assert (p 0))(assert (not (p 3)))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // Chained UF: f(f(x)) = x forces f^4(a) = a.
        assert_eq!(
            run("(declare-sort S)(declare-fun f (S) S)(declare-const a S)\
                 (assert (forall ((x S)) (= (f (f x)) x)))\
                 (assert (not (= (f (f (f (f a)))) a)))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn quantifier_instantiation_and_skolemization() {
        // forall instantiated over the ground term 5 → unsat.
        assert_eq!(
            run(
                "(declare-fun p (Int) Bool)(assert (forall ((x Int)) (p x)))\
                 (assert (not (p 5)))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // exists skolemized → sat.
        assert_eq!(
            run("(declare-fun p (Int) Bool)(assert (exists ((x Int)) (p x)))(check-sat)").unwrap(),
            alloc::vec!["sat"]
        );
        // exists a witness, but forall forbids every value → unsat.
        assert_eq!(
            run(
                "(declare-fun p (Int) Bool)(assert (exists ((y Int)) (p y)))\
                 (assert (forall ((x Int)) (not (p x))))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn quantifiers_accepted_soundly() {
        // A non-linear quantified body is accepted (not a parse error) and
        // answered with a sound `unknown` (no QE, no saturation).
        assert_eq!(
            run("(declare-const x Int)(assert (forall ((y Int)) (> (* y y) x)))(check-sat)")
                .unwrap(),
            alloc::vec!["unknown"]
        );
        // A ground goal alongside a quantifier still decides.
        assert_eq!(
            run("(declare-const x Int)(assert (= x 3))(assert (> x 5))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn int_bv_bridge() {
        // (bv2int a) = 5 forces a = #x05.
        assert_eq!(
            run("(declare-const a (_ BitVec 8))(assert (= (bv2int a) 5))\
                 (assert (not (= a #x05)))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // Out of range for the width → no bit-vector maps to it.
        assert_eq!(
            run("(declare-const a (_ BitVec 4))(assert (= (bv2int a) 20))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
        // int2bv is modular: int2bv(x)=#x05 ⟺ x ≡ 5 (mod 256), so x=261 works.
        assert_eq!(
            run("(declare-const x Int)(assert (= ((_ int2bv 8) x) #x05))\
                 (assert (= x 261))(check-sat)")
            .unwrap(),
            alloc::vec!["sat"]
        );
    }

    #[test]
    fn str_is_digit_and_fp_to_real() {
        // str.is_digit: single decimal digit.
        assert_eq!(
            run("(assert (not (str.is_digit \"5\")))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run("(assert (str.is_digit \"a\"))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
        // fp.to_real on an integral Float64 constant.
        assert_eq!(
            run("(assert (not (= (fp.to_real ((_ to_fp 11 53) RNE 3.0)) 3.0)))(check-sat)")
                .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn sequence_search_and_replace() {
        let s = "(seq.++ (seq.unit 1) (seq.unit 2) (seq.unit 1))";
        // indexof with an offset skips the first occurrence.
        assert_eq!(
            run(&alloc::format!(
                "(assert (not (= (seq.indexof {s} (seq.unit 1) 1) 2)))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // contains and first-occurrence replace.
        assert_eq!(
            run(&alloc::format!(
                "(assert (not (seq.contains {s} (seq.unit 2))))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run(
                "(assert (not (= (seq.replace (seq.++ (seq.unit 1) (seq.unit 2)) \
                 (seq.unit 2) (seq.unit 9)) (seq.++ (seq.unit 1) (seq.unit 9)))))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // Symbolic elements: `seq.contains (seq.unit a) (seq.unit b)` means `a=b`,
        // not a syntactic comparison — so it is sat (was a wrong unsat), and
        // conjoined with `a≠b` it is unsat.
        assert_eq!(
            run("(declare-const a Int)(declare-const b Int)\
                 (assert (seq.contains (seq.unit a) (seq.unit b)))(check-sat)")
            .unwrap(),
            alloc::vec!["sat"]
        );
        assert_eq!(
            run("(declare-const a Int)(declare-const b Int)\
                 (assert (seq.contains (seq.unit a) (seq.unit b)))\
                 (assert (not (= a b)))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn regex_complement_and_difference() {
        // re.comp: "b" is in the complement of "a", "a" is not.
        assert_eq!(
            run("(assert (str.in_re \"b\" (re.comp (str.to_re \"a\"))))(check-sat)").unwrap(),
            alloc::vec!["sat"]
        );
        // re.diff: [a-z] minus "b" excludes "b" but keeps "a".
        assert_eq!(
            run("(assert (not (str.in_re \"a\" (re.diff (re.range \"a\" \"z\") (str.to_re \"b\")))))\
                 (check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // Complement composes inside a concatenation.
        assert_eq!(
            run("(assert (not (str.in_re \"ab\" \
                 (re.++ (re.comp (str.to_re \"x\")) (str.to_re \"b\")))))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn regex_power() {
        // ((_ re.^ 3) a) matches exactly aaa.
        assert_eq!(
            run("(assert (str.in_re \"aaa\" ((_ re.^ 3) (str.to_re \"a\"))))(check-sat)").unwrap(),
            alloc::vec!["sat"]
        );
        assert_eq!(
            run("(assert (str.in_re \"aa\" ((_ re.^ 3) (str.to_re \"a\"))))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn regex_loop() {
        // ((_ re.loop 3 5) a) matches a³…a⁵. "aa" is out (unsat), "aaaa" is in.
        assert_eq!(
            run("(assert (str.in_re \"aa\" ((_ re.loop 3 5) (str.to_re \"a\"))))(check-sat)")
                .unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run(
                "(assert (str.in_re \"aaa\" ((_ re.loop 3 5) (str.to_re \"a\"))))\
                 (assert (not (str.in_re \"aa\" ((_ re.loop 3 5) (str.to_re \"a\")))))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["sat"]
        );
    }

    #[test]
    fn datatype_universal_selector_property_is_sound() {
        // ∀x. is_cons(x) ⇒ hd(x) ≥ 0, with a witness l = cons(-1, nil): the
        // selector trigger matches no ground application, so enumeration over the
        // ground constructor term derives the contradiction. Previously an unsound
        // `sat` (the run wrongly claimed saturation).
        assert_eq!(
            run(
                "(declare-datatypes ((L 0)) (((nl) (cons (hd Int) (tl L)))))\
                 (assert (forall ((x L)) (=> ((_ is cons) x) (>= (hd x) 0))))\
                 (declare-const l L)(assert (= l (cons (- 1) nl)))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn arity_n_uninterpreted_sorts() {
        // (declare-sort P 1): each argument tuple is a distinct sort; reflexivity
        // still holds, and elements at different sorts are unrelated.
        assert_eq!(
            run("(declare-sort P 1)(declare-const x (P Int))\
                 (assert (not (= x x)))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run("(declare-sort Pair 2)(declare-const p (Pair Int Bool))\
                 (declare-const q (Pair Int Bool))(assert (distinct p q))(check-sat)")
            .unwrap(),
            alloc::vec!["sat"]
        );
    }

    #[test]
    fn apply_simplify_tactic() {
        // (apply simplify) prints the residual goal; trivially-true assertions
        // are dropped by the rewriter.
        let out = run(
            "(declare-const x Int)(assert (and true (> x 5)))(assert (= 1 1))\
                       (apply simplify)",
        )
        .unwrap();
        assert_eq!(out.len(), 1);
        assert!(out[0].contains("(goal"), "output: {}", out[0]);
        assert!(out[0].contains("x 5"), "output: {}", out[0]);
        // The `nnf` tactic (and combinators over it) pushes negation inward.
        let nnf = run("(declare-const p Bool)(declare-const q Bool)\
                       (assert (not (and p q)))(apply (then simplify nnf))")
        .unwrap();
        assert!(
            nnf[0].contains("(or (not p) (not q))"),
            "output: {}",
            nnf[0]
        );
    }

    #[test]
    fn apply_ctx_solver_simplify() {
        // A context-implied conjunct (`x > 0`, entailed by `x > 5`) is dropped.
        let out = run("(declare-const x Int)(assert (> x 5))(assert (> x 0))\
             (apply ctx-solver-simplify)")
        .unwrap();
        assert!(out[0].contains("x 5"), "output: {}", out[0]);
        assert!(
            !out[0].contains("x 0"),
            "redundant conjunct kept: {}",
            out[0]
        );
        // A contradictory context collapses the goal to `false`.
        let unsat = run("(declare-const p Bool)(assert p)(assert (not p))\
             (apply ctx-solver-simplify)")
        .unwrap();
        assert!(unsat[0].contains("false"), "output: {}", unsat[0]);
    }

    #[test]
    fn singular_datatype_eval_simplify() {
        // (declare-datatype …) — the single-datatype form, incl. recursive.
        assert_eq!(
            run("(declare-datatype Lst ((nil) (cons (hd Int) (tl Lst))))\
                 (declare-const l Lst)(assert (= l (cons 5 nil)))\
                 (assert (not (= (hd l) 5)))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // (eval term) reports the model value.
        assert_eq!(
            run("(declare-const x Int)(assert (= x 7))(check-sat)(eval (* x 2))").unwrap(),
            alloc::vec!["sat", "14"]
        );
        // (simplify …) folds Booleans.
        assert_eq!(
            run("(simplify (and true (or false true)))").unwrap(),
            alloc::vec!["true"]
        );
    }

    #[test]
    fn as_array_and_check_sat_using() {
        // (_ as-array f): select is f applied to the index.
        assert_eq!(
            run("(declare-fun f (Int) Int)\
                 (assert (not (= (select (_ as-array f) 3) (f 3))))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // check-sat-using ignores the tactic and returns the same verdict.
        assert_eq!(
            run("(declare-const x Int)(assert (> x 5))(assert (< x 3))\
                 (check-sat-using (then simplify smt))")
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn array_map_combinator() {
        // ((_ map f) a b) applies f element-wise; select rewrites to f of selects.
        assert_eq!(
            run(
                "(declare-const a (Array Int Int))(declare-const b (Array Int Int))\
                 (assert (= (select a 2) 10))(assert (= (select b 2) 20))\
                 (assert (not (= (select ((_ map (+ (Int Int) Int)) a b) 2) 30)))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // Boolean map (not) over a set-like array.
        assert_eq!(
            run("(declare-const a (Array Int Bool))(assert (select a 3))\
                 (assert (not (select ((_ map not) a) 3)))(check-sat)")
            .unwrap(),
            alloc::vec!["sat"]
        );
        // Soundness: a map array used in an *equality* (not selected) is not given
        // its element-wise semantics, so `sat` would be wrong — must stay sound.
        // `map(-,a,b)=a` forces `b=0`, contradicting `b[0]≠0` (z3: unsat).
        assert_ne!(
            run(
                "(declare-const a (Array Int Int))(declare-const b (Array Int Int))\
                 (assert (= ((_ map (- (Int Int) Int)) a b) a))\
                 (assert (not (= (select b 0) 0)))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["sat"]
        );
    }

    #[test]
    fn functional_array_equality_is_sound() {
        // `(_ as-array f)` and `(lambda …)` arrays used in an EQUALITY (not
        // selected) must not be treated as free variables — a `sat` would be
        // wrong (both are unsat in z3). Regression for a fuzz-found soundness bug.
        assert_ne!(
            run("(declare-fun f (Int) Int)(declare-const b (Array Int Int))\
                 (assert (= (_ as-array f) b))\
                 (assert (not (= (select b 0) (f 0))))(check-sat)")
            .unwrap(),
            alloc::vec!["sat"]
        );
        assert_ne!(
            run("(declare-const b (Array Int Int))\
                 (assert (= (lambda ((x Int)) (+ x 1)) b))\
                 (assert (not (= (select b 0) 1)))(check-sat)")
            .unwrap(),
            alloc::vec!["sat"]
        );
        // …but a direct `select` of each still decides.
        assert_eq!(
            run("(declare-fun f (Int) Int)(assert (= (f 0) 7))\
                 (assert (not (= (select (_ as-array f) 0) 7)))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn lambda_arrays() {
        // select beta-reduces a lambda-defined array.
        assert_eq!(
            run(
                "(define-fun a () (Array Int Int) (lambda ((x Int)) (+ x 1)))\
                 (assert (not (= (select a 3) 4)))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // Multi-argument lambda.
        assert_eq!(
            run("(assert (not (= (select (lambda ((x Int) (y Int)) (+ x y)) 3 4) 7)))(check-sat)")
                .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn divisible_define_const_power() {
        // (_ divisible n) ≡ mod-zero.
        assert_eq!(
            run("(declare-const x Int)(assert ((_ divisible 3) x))(assert (= x 9))(check-sat)")
                .unwrap(),
            alloc::vec!["sat"]
        );
        assert_eq!(
            run("(declare-const x Int)(assert ((_ divisible 3) x))(assert (= x 7))(check-sat)")
                .unwrap(),
            alloc::vec!["unsat"]
        );
        // define-const and constant exponentiation fold.
        assert_eq!(
            run("(define-const k Int 5)(assert (not (= (^ k 2) 25)))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn parametric_datatypes() {
        // (Pair A B) monomorphized at two distinct instantiations.
        let pair = "(declare-datatypes ((Pair 2)) ((par (A B) ((mk-pair (fst A) (snd B))))))";
        assert_eq!(
            run(&alloc::format!(
                "{pair}(declare-const p (Pair Int Bool))\
                 (assert (= p (mk-pair 3 true)))(assert (not (= (fst p) 3)))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // A parametric recursive list: (Lst X) refers to itself.
        assert_eq!(
            run(
                "(declare-datatypes ((Lst 1)) ((par (X) ((nil) (cons (hd X) (tl (Lst X)))))))\
                 (declare-const l (Lst Int))(assert (= l (cons 1 nil)))\
                 (assert (not (= (hd l) 1)))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn recursive_function_over_datatype() {
        // len over a list decides: selector/tester folding (tail(cons h t)=t,
        // is-nil(cons …)=false) lets E-matching unfold the spine.
        let lst = "(declare-datatypes ((Lst 0)) (((nil) (cons (head Int) (tail Lst)))))\
                   (define-fun-rec len ((l Lst)) Int \
                    (ite ((_ is nil) l) 0 (+ 1 (len (tail l)))))";
        assert_eq!(
            run(&alloc::format!(
                "{lst}(assert (= (len (cons 1 (cons 2 nil))) 2))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["sat"]
        );
        assert_eq!(
            run(&alloc::format!(
                "{lst}(assert (= (len (cons 1 (cons 2 nil))) 3))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn mutually_recursive_datatypes() {
        // T and F reference each other; both must be registered before either's
        // constructors are parsed. Cross-type selection resolves.
        let dt = "(declare-datatypes ((T 0) (F 0))\
                  (((tnil) (tcons (th Int) (tf F))) ((fnil) (fcons (fh Int) (ft T)))))";
        assert_eq!(
            run(&alloc::format!(
                "{dt}(declare-const x T)(assert (= x (tcons 5 (fcons 6 tnil))))\
                 (assert (not (= (fh (tf x)) 6)))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["unsat"]
        );
        assert_eq!(
            run(&alloc::format!(
                "{dt}(declare-const x T)(assert ((_ is tcons) x))(assert (= (th x) 9))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["sat"]
        );
    }

    #[test]
    fn exists_forall_alternation() {
        // ∃x.∀y. y ≥ x is false over the (unbounded) integers — no minimum.
        assert_eq!(
            run("(assert (exists ((x Int)) (forall ((y Int)) (>= y x))))(check-sat)").unwrap(),
            alloc::vec!["unsat"]
        );
        // But with y bounded to [0,5] there is such an x (e.g. 5).
        assert_eq!(
            run("(assert (exists ((x Int)) (forall ((y Int)) \
                 (=> (and (<= 0 y) (<= y 5)) (<= y x)))))(check-sat)")
            .unwrap(),
            alloc::vec!["sat"]
        );
    }

    #[test]
    fn nested_forall_flattened() {
        // ∀x.∀y. f(x,y)=f(y,x) is flattened to ∀x,y. …, so E-matching derives
        // f(1,2)=f(2,1) and refutes 5≠6.
        assert_eq!(
            run("(declare-fun f (Int Int) Int)\
                 (assert (forall ((x Int)) (forall ((y Int)) (= (f x y) (f y x)))))\
                 (assert (= (f 1 2) 5))(assert (= (f 2 1) 6))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // Three nested levels flatten too.
        assert_eq!(
            run("(declare-fun g (Int Int Int) Bool)\
                 (assert (forall ((x Int)) (forall ((y Int)) (forall ((z Int)) \
                   (=> (g x y z) (g z y x))))))\
                 (declare-const a Int)(declare-const b Int)(declare-const c Int)\
                 (assert (g a b c))(assert (not (g c b a)))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn multi_trigger_ematching() {
        // Transitivity over an *infinite* (symbolic) domain: no single trigger
        // covers x,y,z, so the multi-trigger {r(x,y), r(y,z)} is joined on y.
        assert_eq!(
            run("(declare-fun r (Int Int) Bool)\
                 (declare-const a Int)(declare-const b Int)(declare-const c Int)\
                 (assert (forall ((x Int)(y Int)(z Int)) (=> (and (r x y) (r y z)) (r x z))))\
                 (assert (r a b))(assert (r b c))(assert (not (r a c)))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // The same axiom is satisfiable without the negated goal.
        assert_eq!(
            run("(declare-fun r (Int Int) Bool)\
                 (declare-const a Int)(declare-const b Int)(declare-const c Int)\
                 (assert (forall ((x Int)(y Int)(z Int)) (=> (and (r x y) (r y z)) (r x z))))\
                 (assert (r a b))(assert (r b c))(check-sat)")
            .unwrap(),
            alloc::vec!["sat"]
        );
    }

    #[test]
    fn ematching_decides_recursive_and_uf() {
        // E-matching unfolds fact's argument chain, so fact(3)=6 refutes =7...
        assert_eq!(
            run(
                "(define-fun-rec fact ((n Int)) Int (ite (<= n 0) 1 (* n (fact (- n 1)))))\
                 (assert (= (fact 3) 6))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["sat"]
        );
        // ...and a summation recursion decides both ways.
        assert_eq!(
            run(
                "(define-fun-rec sm ((n Int)) Int (ite (<= n 0) 0 (+ n (sm (- n 1)))))\
                 (assert (not (= (sm 4) 10)))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // A non-terminating instantiation (f(x)=f(x+1)) still yields a sound
        // `unknown` (E-matching never reaches a fixpoint).
        assert_eq!(
            run(
                "(declare-fun f (Int) Int)(assert (forall ((x Int)) (= (f x) (f (+ x 1)))))\
                 (assert (= (f 0) 5))(assert (not (= (f 100) 5)))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["unknown"]
        );
    }

    #[test]
    fn recursive_function_definitions() {
        // define-funs-rec (mutual recursion): even/odd over a small argument
        // fully unfold and decide.
        assert_eq!(
            run("(define-funs-rec ((ev ((n Int)) Bool) (od ((n Int)) Bool))\
                 ((ite (= n 0) true (od (- n 1))) (ite (= n 0) false (ev (- n 1)))))\
                 (assert (ev 4))(assert (not (od 4)))(check-sat)")
            .unwrap(),
            alloc::vec!["sat"]
        );
        // define-fun-rec: E-matching unfolds the argument chain, so a base-case
        // recursion decides (f(2)=f(1)=f(0)=0).
        assert_eq!(
            run(
                "(define-fun-rec f ((n Int)) Int (ite (<= n 0) 0 (f (- n 1))))\
                 (assert (= (f 2) 0))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["sat"]
        );
        // A contradictory arithmetic recursion is refuted: fact(3) = 6 ≠ 7.
        assert_eq!(
            run(
                "(define-fun-rec fact ((n Int)) Int (ite (<= n 0) 1 (* n (fact (- n 1)))))\
                 (assert (= (fact 3) 7))(check-sat)"
            )
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn quantified_uf_instantiates_not_qe() {
        // Regression: `∀x. f(x)=0` binds x inside an uninterpreted application,
        // so Fourier–Motzkin QE must NOT fire (it would leave x free, an
        // unsound over-approximation that once returned `sat`). Instantiation
        // decides it: x = a yields f(a)=0, contradicting `f(a)≠0`.
        assert_eq!(
            run("(declare-fun f (Int) Int)(declare-const a Int)\
                 (assert (forall ((x Int)) (= (f x) 0)))(assert (not (= (f a) 0)))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
        // With a :pattern annotation on the body, likewise.
        assert_eq!(
            run("(declare-fun f (Int) Int)(declare-fun g (Int) Int)\
                 (assert (forall ((x Int)) (! (= (f x) (g x)) :pattern ((f x)))))\
                 (declare-const a Int)(assert (not (= (f a) (g a))))(check-sat)")
            .unwrap(),
            alloc::vec!["unsat"]
        );
    }

    #[test]
    fn smtlib_v1_benchmark_euf() {
        // SMT-LIB 1.2 (benchmark …) format: sorts/funs/preds, assumptions,
        // implies, if_then_else, single-binding let, {…} source blocks.
        let script = "
            (benchmark euf_test
              :logic QF_UF
              :extrasorts (U)
              :extrafuns ((a U) (b U) (c U) (f U U))
              :assumption (= a b)
              :assumption (= b c)
              :formula (not (= (f a) (f c)))
              :status unsat
              :source { a hand-written test })
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["unsat"]);
    }

    #[test]
    fn smtlib_v1_arith_let_and_implies() {
        let script = "
            (benchmark lia_test
              :logic QF_LIA
              :extrafuns ((x Int) (y Int))
              :formula (and (< x y) (let (?d (- y x)) (<= ?d 0)))
              :status unsat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["unsat"]);
    }

    #[test]
    fn parse_error_is_reported() {
        assert!(run("(declare-const a").is_err());
    }
}
