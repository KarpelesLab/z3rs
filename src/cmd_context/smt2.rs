//! A minimal SMT-LIB 2 front end — the QF_UF subset of `z3/src/cmd_context` +
//! `z3/src/parsers/smt2` (Z3 4.17.0, MIT).
//!
//! Supports: `set-logic`/`set-info`/`set-option` (ignored), `declare-sort`
//! (arity 0), `declare-fun`, `declare-const`, `assert`, `check-sat`,
//! `get-value`, `get-model`, `push`/`pop`/`reset`, and `exit`; the
//! `Bool`/`Int`/`Real` sorts, integer and decimal numerals, the core Boolean
//! operators, equality/`distinct`, `ite`, `let`, linear arithmetic
//! (`+ - * / <= < >= >`, `div`/`mod`/`abs`/`to_real`/`to_int`, with constant
//! folding), uninterpreted functions, and arrays (`(Array I E)`, `select`,
//! `store`). Runs QF_UF / QF_LRA / QF_LIA / QF_A scripts through
//! [`crate::smt::check_model`], and reports models via `get-value`/`get-model`.
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
use crate::smt::{Model, SmtResult, check_model};
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

/// Run an SMT-LIB2 `script`, returning one response line per `check-sat`
/// (`"sat"`, `"unsat"`, or `"unknown"`).
pub fn run(script: &str) -> Result<Vec<String>, String> {
    let forms = parse(script)?;
    let mut ctx = Context::new();
    let mut out = Vec::new();
    for form in forms {
        if let Some(resp) = ctx.command(&form)? {
            out.push(resp);
        }
    }
    Ok(out)
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
                // Parametric sort application, e.g. (Array I E).
                match Self::sym(&l[0])? {
                    "Array" if l.len() == 3 => {
                        let index = self.resolve_sort(&l[1])?;
                        let elem = self.resolve_sort(&l[2])?;
                        Ok(self.m.mk_array_sort(index, elem))
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
            "set-logic" | "set-info" | "set-option" | "get-info" | "echo" | "exit" => Ok(None),
            "push" => {
                let n = Self::level_arg(list)?;
                for _ in 0..n {
                    self.scope_stack.push(Scope {
                        assertions: self.assertions.len(),
                        decls: self.decl_order.len(),
                        sorts: self.sort_order.len(),
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
                let t = self.term(&list[1])?;
                let name = named_label(&list[1]);
                self.assertions.push(t);
                self.assert_names.push(name);
                self.last_model = None;
                self.last_verdict = None;
                Ok(None)
            }
            "check-sat" => {
                let goal = self.goal();
                let (res, model) = check_model(&self.m, goal);
                self.last_model = model;
                self.last_verdict = Some(res);
                let resp = match res {
                    SmtResult::Sat => "sat",
                    SmtResult::Unsat => "unsat",
                    SmtResult::Unknown => "unknown",
                };
                Ok(Some(resp.to_string()))
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
                let (res, model) = check_model(&self.m, goal);
                self.last_model = model;
                self.last_verdict = Some(res);
                Ok(Some(
                    match res {
                        SmtResult::Sat => "sat",
                        SmtResult::Unsat => "unsat",
                        SmtResult::Unknown => "unknown",
                    }
                    .to_string(),
                ))
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
    fn goal(&mut self) -> AstId {
        let base = self.conjunction();
        let lifted = self.lift(base);
        let mut axioms = self.array_axioms(lifted);
        if axioms.is_empty() {
            lifted
        } else {
            axioms.push(lifted);
            self.m.mk_and(&axioms)
        }
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
        check_model(&self.m, goal).0
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
            if *k
                && let Some(name) = label
            {
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
            let v = model.value_string(&self.m, *id);
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
            out.push_str(&alloc::format!("\n  (define-fun {name} () {sort_name} {v})"));
        }
        out.push_str("\n)");
        self.last_model = Some(model);
        Ok(out)
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
                let head = Self::sym(&l[0])?.to_string();
                if head == "let" {
                    return self.term_let(&l[1], &l[2]);
                }
                if head == "!" {
                    // (! t :annotation value …) — annotations are transparent to
                    // the term's meaning; evaluate the annotated term.
                    return self.term(&l[1]);
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
                // Fold constant real division to an exact rational; otherwise
                // build an opaque `/` term.
                match (m.as_numeral(args[0]), m.as_numeral(args[1])) {
                    (Some(p), Some(q)) if !q.is_zero() => Ok(m.mk_numeral(p.div(&q), false)),
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
                // (is_int r): true iff r is integral. Only constants are decided;
                // a non-constant argument is unsupported.
                Some(v) => Ok(if v.is_integer() {
                    m.mk_true()
                } else {
                    m.mk_false()
                }),
                None => Err("is_int: only constant arguments are supported".to_string()),
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
        assert_eq!(run(script).unwrap(), alloc::vec!["sat", "((r (/ 1.0 2.0)))"]);
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
        assert!(out[1].contains("(define-fun b () Bool false)"), "{}", out[1]);
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
            run("(declare-const x Int)(assert (not (= x (+ (* 3 (div x 3)) (mod x 3)))))(check-sat)")
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
    fn array_satisfiable() {
        let script = "
            (declare-const a (Array Int Int)) (declare-const i Int) (declare-const v Int)
            (assert (= (select (store a i v) i) v))
            (check-sat)
        ";
        assert_eq!(run(script).unwrap(), alloc::vec!["sat"]);
    }

    #[test]
    fn parse_error_is_reported() {
        assert!(run("(declare-const a").is_err());
    }
}
