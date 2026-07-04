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

use alloc::collections::{BTreeMap, BTreeSet};
use alloc::string::{String, ToString};
use alloc::vec::Vec;

use puremp::{Int, Rational};

use crate::ast::AstId;
use crate::ast::arith::ArithOp;
use crate::ast::manager::AstManager;
use crate::rewriter::substitute;
use crate::smt::{Model, SmtResult, check_bv_model, check_model};
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
#[derive(Clone, Debug)]
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

/// If `s` is a top-level `(forall …)` or `(exists …)`, its keyword.
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
    /// Top-level universal (`forall`) assertions as `(bound-var placeholders,
    /// body)`; instantiated over ground terms at each `check-sat`.
    universals: Vec<(Vec<AstId>, AstId)>,
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
            universals: Vec::new(),
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

    fn resolve_sort(&mut self, s: &SExpr) -> Result<AstId, String> {
        match s {
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
            "set-logic" | "set-info" | "set-option" | "exit" => Ok(None),
            "echo" => Ok(Some(match list.get(1) {
                Some(SExpr::Atom(a)) => unquote_string(a),
                _ => String::new(),
            })),
            "get-info" => match list.get(1) {
                Some(SExpr::Atom(k)) if k == ":version" => {
                    Ok(Some("(:version \"0.0.1\")".to_string()))
                }
                Some(SExpr::Atom(k)) if k == ":name" => Ok(Some("(:name \"z3rs\")".to_string())),
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
                self.scope_stack.clear();
                self.last_model = None;
                self.last_verdict = None;
                Ok(None)
            }
            "declare-sort" => {
                let name = Self::sym(&list[1])?.to_string();
                let s = self.m.mk_uninterpreted_sort(Symbol::new(&name));
                self.sorts.insert(name.clone(), s);
                self.sort_order.push(name);
                Ok(None)
            }
            "declare-datatypes" => {
                self.declare_datatypes(&list[1], &list[2])?;
                self.last_model = None;
                Ok(None)
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
            "assert" => {
                // A top-level quantifier gets real (sound) handling: `exists` is
                // skolemized (its body asserted with fresh constants), `forall` is
                // recorded for ground instantiation at check-sat. Quantifiers
                // nested inside a formula fall back to the `unknown` sentinel.
                if let Some(kind) = top_level_quantifier(&list[1]) {
                    let ql = as_list(&list[1])?;
                    let (vars, body) = self.parse_quantifier(&ql[1], &ql[2])?;
                    if kind == "exists" {
                        // ∃x. P(x) is equisatisfiable with P(k) for fresh k.
                        self.assertions.push(body);
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
            "check-sat" => {
                let (res, model) = self.check_sat();
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
        for (i, body) in bodies.iter().enumerate() {
            let bodyl = as_list(body)?;
            // The datatype name and the constructor s-expressions.
            let (name, ctors): (String, &[SExpr]) = if sort_decls.is_empty() {
                (Self::sym(&bodyl[0])?.to_string(), &bodyl[1..]) // legacy (T c1 c2 …)
            } else {
                let sd = as_list(&sort_decls[i])?;
                (Self::sym(&sd[0])?.to_string(), bodyl) // 2.6: name from (T k)
            };
            let sort = self.m.mk_uninterpreted_sort(Symbol::new(&name));
            self.sorts.insert(name.clone(), sort);
            self.sort_order.push(name);
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
        let instances = self.universal_instances();
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
        if res == SmtResult::Sat && !self.universals.is_empty() {
            (SmtResult::Unknown, None)
        } else {
            (res, model)
        }
    }

    /// Parse a quantifier's binder list `((x S) …)` and body into fresh
    /// placeholder constants (one per bound variable) and the body term built
    /// over them. The placeholders double as skolem constants for `exists`.
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

    /// Ground instances of every recorded universal: substitute the bound-var
    /// placeholders by ground terms of the matching sort drawn from the current
    /// assertions (bounded to keep the instance set finite).
    fn universal_instances(&mut self) -> Vec<AstId> {
        if self.universals.is_empty() {
            return Vec::new();
        }
        // Ground terms by sort, collected from the assertions.
        let mut by_sort: BTreeMap<AstId, Vec<AstId>> = BTreeMap::new();
        for a in self.assertions.clone() {
            for t in self.m.postorder(a) {
                let s = self.m.get_sort(t);
                by_sort.entry(s).or_default().push(t);
            }
        }
        for v in by_sort.values_mut() {
            v.sort_unstable();
            v.dedup();
        }
        const MAX_INSTANCES_PER_UNIVERSAL: usize = 64;
        let mut instances = Vec::new();
        for (vars, body) in self.universals.clone() {
            // Candidate ground terms for each bound variable.
            let mut cands: Vec<Vec<AstId>> = Vec::new();
            for &v in &vars {
                let s = self.m.get_sort(v);
                let mut c = by_sort.get(&s).cloned().unwrap_or_default();
                if c.is_empty() {
                    // No ground term of this sort: use a fresh representative
                    // (uninterpreted sorts are non-empty; sound for the others).
                    c.push(self.fresh_const(s));
                }
                cands.push(c);
            }
            // Bounded cartesian product of the candidates.
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
                let inst = substitute(&mut self.m, body, &subst);
                instances.push(inst);
            }
        }
        instances
    }

    /// Instantiate the array + enum axioms for `lifted` and conjoin them.
    fn with_axioms(&mut self, lifted: AstId) -> AstId {
        let mut axioms = self.array_axioms(lifted);
        axioms.extend(self.enum_axioms(lifted));
        axioms.extend(self.record_axioms(lifted));
        axioms.extend(self.datatype_axioms(lifted));
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
        // Quantified formulas are not decided yet: if the goal mentions a
        // quantifier sentinel, answer a sound `unknown`.
        if !self.quant_atoms.is_empty()
            && self
                .m
                .postorder(goal)
                .iter()
                .any(|t| self.quant_atoms.contains(t))
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
                    return Err("unsupported qualified application".to_string());
                }
                let head = Self::sym(&l[0])?.to_string();
                if head == "let" {
                    return self.term_let(&l[1], &l[2]);
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
                if head == "_" {
                    // Indexed identifier, e.g. (_ bv5 8) — a bit-vector numeral.
                    let name = Self::sym(&l[1])?;
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
                let args: Vec<AstId> = l[1..]
                    .iter()
                    .map(|a| self.term(a))
                    .collect::<Result<_, _>>()?;
                if self.macros.contains_key(&head) {
                    return self.expand_macro(&head, args);
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
    fn quantifiers_accepted_as_unknown() {
        // Quantified formulas are accepted (not a parse error) and answered
        // with a sound `unknown`; ground goals alongside still decide.
        assert_eq!(
            run("(declare-const x Int)(assert (forall ((y Int)) (>= (+ x y) y)))(check-sat)")
                .unwrap(),
            alloc::vec!["unknown"]
        );
        assert_eq!(
            run("(declare-const x Int)(assert (= x 3))(assert (> x 5))(check-sat)").unwrap(),
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
