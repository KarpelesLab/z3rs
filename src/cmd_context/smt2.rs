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
    Constraint, Model, OptOutcome, Rel, SmtResult, Value, arith_optimize, ast_to_lin,
    check_bv_model, check_model, linear_constraints, project,
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
            reglan_sort: None,
            regex_of: BTreeMap::new(),
            sort_defs: BTreeMap::new(),
            fp_sorts: BTreeMap::new(),
            rm_sort: None,
            fp_of: BTreeMap::new(),
            fp_bv: BTreeMap::new(),
            seq_sorts: BTreeMap::new(),
            seq_of: BTreeMap::new(),
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
                let asserts = self.assertions.clone();
                let mut lines: Vec<String> = Vec::new();
                for a in asserts {
                    let mut s = self.dt_fold(a);
                    if use_nnf {
                        s = crate::rewriter::to_nnf(&mut self.m, s);
                    }
                    s = crate::rewriter::simplify(&mut self.m, s);
                    if self.m.is_false(s) {
                        lines = alloc::vec!["false".to_string()];
                        break;
                    }
                    if !self.m.is_true(s) {
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
        let n = self.m.as_numeral(b)?.to_integer()?; // constant divisor only
        if n.is_zero() {
            return None;
        }
        if let Some(&pair) = ctx.dm.get(&(a, b)) {
            return Some(pair);
        }
        let int = self.m.mk_int_sort();
        let q = self.fresh_const(int);
        let r = self.fresh_const(int);
        // a = n·q + r
        let nq = self.m.mk_mul(&[b, q]);
        let sum = self.m.mk_add(&[nq, r]);
        let eq = self.m.mk_eq(a, sum);
        // 0 ≤ r < |n|
        let zero = self.m.mk_int(0);
        let ge = self.m.mk_ge(r, zero);
        let abs_n = self.m.mk_numeral(Rational::from_integer(n.abs()), true);
        let lt = self.m.mk_lt(r, abs_n);
        ctx.defs.push(eq);
        ctx.defs.push(ge);
        ctx.defs.push(lt);
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
                // Recursive if any selector's field sort is the datatype itself.
                let recursive = ctor_infos
                    .iter()
                    .flat_map(|(_, sels, _)| sels)
                    .any(|&sd| self.m.func_decl(sd).map(|d| d.range) == Some(sort));
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
                            if self.m.func_decl(sd).map(|d| d.range) != Some(s) {
                                continue; // only recursive (same-sort) selectors
                            }
                            let child = self.m.mk_app(sd, &[t]);
                            let dc = self.m.mk_app(depth, &[child]);
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
        if self.str_lits.is_empty() {
            return Vec::new();
        }
        let present: BTreeSet<AstId> = self.m.postorder(goal).into_iter().collect();
        // Literals occurring in the goal, with their lengths.
        let lits: Vec<(AstId, i64)> = self
            .str_lits
            .iter()
            .filter(|(_, c)| present.contains(*c))
            .map(|(text, &c)| (c, text.chars().count() as i64))
            .collect();
        let mut ax = Vec::new();
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
        // General concat = concat with variables on both sides: gate to unknown.
        Ok(None)
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
        if op != "fp.eq" {
            return None;
        }
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
        let val_eq = self.m.mk_or(&[bv_eq, both_zero]);
        Some(self.m.mk_and(&[val_eq, no_nan]))
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
                self.symbolic_fp(op, args)
            }
            "fp.to_real" if args.len() == 1 => {
                // Exact real value of a finite Float64 constant. Folded when the
                // value is an integer; other finite values would need an exact
                // dyadic rational, so they stay a gated `unknown`.
                if let Some(a) = self.fp64(args[0])
                    && a.is_finite()
                    && a.abs() < 9.007e15
                    && (a as i64) as f64 == a
                {
                    return Ok(self
                        .m
                        .mk_numeral(Rational::from_integer(puremp::Int::from(a as i64)), false));
                }
                self.symbolic_fp(op, args)
            }
            "fp.min" | "fp.max" if args.len() == 2 => {
                if let (Some(a), Some(b)) = (self.fp64(args[0]), self.fp64(args[1])) {
                    let r = if op == "fp.min" { a.min(b) } else { a.max(b) };
                    return Ok(self.mk_fp(f64_bits(r), 11, 53));
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
                // fp.eq is cheap to bit-blast (equality + zero handling); the
                // ordered comparisons need a key-transform + bvult circuit the
                // basic CDCL core handles too slowly, so they stay a sound
                // `unknown` (constant operands still fold above).
                if op == "fp.eq"
                    && let Some(t) = self.fp_compare_bv(op, args[0], args[1])
                {
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
                self.symbolic_seq(op, args)
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
                        (&ps[0], &ps[1])
                    } else {
                        (&ps[1], &ps[0])
                    };
                    let b = match op {
                        "seq.prefixof" => whole.len() >= sub.len() && whole[..sub.len()] == sub[..],
                        "seq.suffixof" => {
                            whole.len() >= sub.len() && whole[whole.len() - sub.len()..] == sub[..]
                        }
                        _ => find_sub(whole, sub, 0).is_some(),
                    };
                    return Ok(self.mk_bool(b));
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
            | "str.<=" => self.m.mk_bool_sort(),
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
                for i in start..=s.len().saturating_sub(sub.len()) {
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
        let (res, model) = self.decide(goal);
        // A `sat` result is complete only if instantiation reached a fixpoint
        // (every ground instance is present — e.g. a finite Datalog domain);
        // otherwise the un-instantiated cases keep it a sound `unknown`.
        if res == SmtResult::Sat && !self.universals.is_empty() && !saturated {
            (SmtResult::Unknown, None)
        } else {
            (res, model)
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
        for (vars, _) in &universals {
            for &v in vars {
                let s = self.m.get_sort(v);
                if by_sort.get(&s).is_none_or(BTreeSet::is_empty) {
                    let rep = self.fresh_const(s);
                    by_sort.entry(s).or_default().insert(rep);
                }
            }
        }

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
                let enumerate = trigs[ui].is_empty() || (dt_binder && ematch_counts[ui] == 0);
                if !enumerate {
                    continue; // handled completely by E-matching
                }
                if dt_binder {
                    dt_enumerated = true; // infinite domain → cannot claim saturation
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
                return (instances, ematch_saturated && !dt_enumerated);
            }
        }
        (instances, false) // ran out of rounds: not saturated
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
        let mut targets: Vec<(AstId, Int)> = Vec::new();
        for t in self.m.postorder(goal) {
            if matches!(self.m.arith_op(t), Some(ArithOp::Mod | ArithOp::Idiv)) {
                let args = self.m.app_args(t);
                if let Some(n) = self.m.as_numeral(args[1]).and_then(|r| r.to_integer())
                    && !n.is_zero()
                {
                    targets.push((args[0], n));
                }
            }
        }
        targets.sort();
        targets.dedup();
        if targets.len() > 12 {
            targets.truncate(12);
        }
        let mut axioms = Vec::new();
        for (a, n) in targets {
            let n_num = self.m.mk_numeral(Rational::from_integer(n.clone()), true);
            let divt = self.m.mk_idiv(a, n_num);
            let modt = self.m.mk_mod(a, n_num);
            let prod = self.m.mk_mul(&[n_num, divt]);
            let sum = self.m.mk_add(&[prod, modt]);
            axioms.push(self.m.mk_eq(a, sum)); // a = n·div + mod
            let zero = self.m.mk_int(0);
            axioms.push(self.m.mk_ge(modt, zero)); // 0 ≤ mod
            let abs_n = self.m.mk_numeral(Rational::from_integer(n.abs()), true);
            axioms.push(self.m.mk_lt(modt, abs_n)); // mod < |n|
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
    fn decide(&mut self, goal: AstId) -> (SmtResult, Option<Model>) {
        // Quantified formulas and symbolic string operations are not fully
        // decided: if the goal mentions either kind of sentinel, answer a sound
        // `unknown`.
        if (!self.quant_atoms.is_empty() || !self.str_symbolic.is_empty())
            && self
                .m
                .postorder(goal)
                .iter()
                .any(|t| self.quant_atoms.contains(t) || self.str_symbolic.contains(t))
        {
            return (SmtResult::Unknown, None);
        }
        // Bit-vector formulas are decided by bit-blasting (no model produced yet).
        // The bit-blaster handles only pure QF_BV; a goal mixing bit-vectors with
        // uninterpreted, array, or arithmetic terms is not combined yet, so return
        // a sound `unknown` rather than a possibly-wrong verdict.
        if self.is_bv_goal(goal) {
            if self.bv_goal_is_pure(goal) {
                let (res, bv) = check_bv_model(&self.m, goal);
                return (res, bv.map(Model::from_bv));
            }
            return (SmtResult::Unknown, None);
        }
        // Arrays indexed by Bool need boolean-value reasoning on the indices
        // (Bool is 2-valued, true ≠ false) that the array axioms do not yet do;
        // return a sound `unknown` rather than a possibly-wrong verdict.
        if self.has_bool_indexed_array(goal) {
            return (SmtResult::Unknown, None);
        }
        let (res, model) = check_model(&self.m, goal);
        if res == SmtResult::Sat && self.arith_nonlinear(goal) {
            (SmtResult::Unknown, None)
        } else {
            (res, model)
        }
    }

    /// Does `goal` contain a `select`/`store` over an array whose index sort is
    /// `Bool`? (An unsupported corner needing boolean-value index reasoning.)
    fn has_bool_indexed_array(&self, goal: AstId) -> bool {
        self.m.postorder(goal).iter().any(|&t| {
            (self.m.is_select(t) || self.m.is_store(t))
                && self
                    .m
                    .array_sort_params(self.m.get_sort(self.m.app_args(t)[0]))
                    .is_some_and(|(idx, _)| self.m.is_bool_sort(idx))
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
            let id = self.term(q)?;
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
                .enum_value_name(&mut model, *id)
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
                        let rm = self.term(&l[1])?;
                        let x = self.term(&l[2])?;
                        if (eb, sb) == (11, 53)
                            && self
                                .rm_name(rm)
                                .as_deref()
                                .is_some_and(|n| n == "RNE" || n == "roundNearestTiesToEven")
                            && let Some(r) = self.m.as_numeral(x)
                        {
                            let num = r.numerator().to_i64();
                            let den = r.denominator().to_i64();
                            if let (Some(n), Some(d)) = (num, den) {
                                return Ok(self.mk_fp((n as f64 / d as f64).to_bits(), 11, 53));
                            }
                        }
                        let s = self.fp_sort(eb, sb);
                        let t = self.fresh_const(s);
                        self.str_symbolic.insert(t);
                        return Ok(t);
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
                        let t = self.fresh_const(s);
                        self.seq_of.insert(t, Vec::new());
                        return Ok(t);
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
    fn nonlinear_is_unknown_not_wrong() {
        // The linear core over-approximates x*y, so a sat verdict would be
        // unsound; report unknown instead. Linear multiplication still decides.
        assert_eq!(
            run("(declare-const x Int)(declare-const y Int)(assert (= (* x y) 6))(assert (= x 2))(check-sat)")
                .unwrap(),
            alloc::vec!["unknown"]
        );
        assert_eq!(
            run("(declare-const x Int)(assert (= (* x x) 2))(check-sat)").unwrap(),
            alloc::vec!["unknown"]
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
    fn opaque_fp_ops_gate_not_contradict() {
        // fp.fma / fp.sqrt on constants have a determined value we can't fold
        // in no_std; they must stay `unknown`, never a wrong verdict. (A bug once
        // bit-blasted them to a free bit-vector, giving `sat` where z3 is unsat.)
        let t = "((_ to_fp 11 53) RNE";
        assert_eq!(
            run(&alloc::format!(
                "(assert (not (= (fp.fma RNE {t} 2.0) {t} 3.0) {t} 1.0)) {t} 7.0))))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["unknown"]
        );
        assert_eq!(
            run(&alloc::format!(
                "(assert (not (= (fp.sqrt RNE {t} 9.0)) {t} 3.0))))(check-sat)"
            ))
            .unwrap(),
            alloc::vec!["unknown"]
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
