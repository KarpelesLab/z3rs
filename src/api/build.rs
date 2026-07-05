//! A programmatic, memory-safe expression-building API — the idiomatic native
//! Rust surface of Z3's C API (`Z3_mk_*` builders + `Z3_solver_*`), without any
//! `unsafe`.
//!
//! Where [`crate::api::Solver`] drives the engine with raw SMT-LIB 2 *text*,
//! this module lets a caller build terms as typed [`Ast`] values through a
//! [`Context`] and solve them, the way Z3's object API does — but implemented as
//! a thin, safe layer over the same [`Session`](crate::cmd_context::Session)
//! front end (each `Ast` carries its SMT-LIB 2 rendering and [`Sort`]). This
//! keeps the whole reasoning path the differentially-tested one while giving
//! consumers a builder API instead of string-mashing.
//!
//! ```
//! use z3rs::api::build::{Context, Sort};
//! use z3rs::api::SatResult;
//!
//! let mut ctx = Context::new();
//! let x = ctx.const_("x", Sort::Int);
//! let y = ctx.const_("y", Sort::Int);
//! // assert  x > y  ∧  x < y + 1   (unsatisfiable over the integers)
//! ctx.assert(&x.gt(&y));
//! ctx.assert(&x.lt(&y.add(&Context::int(1))));
//! assert_eq!(ctx.check(), SatResult::Unsat);
//! ```

use alloc::collections::BTreeSet;
use alloc::string::{String, ToString};
use alloc::vec::Vec;

use crate::api::SatResult;
use crate::cmd_context::Session;

/// A sort (type) in the builder API.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Sort {
    Bool,
    Int,
    Real,
    /// A bit-vector of the given width.
    BitVec(u32),
    /// An array sort `(Array domain range)`.
    Array(alloc::boxed::Box<Sort>, alloc::boxed::Box<Sort>),
    /// An uninterpreted sort, named.
    Uninterpreted(String),
    /// An algebraic datatype sort, named. Rendered as its bare name (the
    /// `(declare-datatype …)` that introduces it is emitted into the session
    /// separately, exactly like [`Sort::Uninterpreted`]).
    Datatype(String),
}

impl Sort {
    /// The SMT-LIB 2 rendering of the sort.
    pub fn smt(&self) -> String {
        match self {
            Sort::Bool => "Bool".to_string(),
            Sort::Int => "Int".to_string(),
            Sort::Real => "Real".to_string(),
            Sort::BitVec(n) => alloc::format!("(_ BitVec {n})"),
            Sort::Array(d, r) => alloc::format!("(Array {} {})", d.smt(), r.smt()),
            Sort::Uninterpreted(name) => name.clone(),
            Sort::Datatype(name) => name.clone(),
        }
    }

    /// The width of a bit-vector sort, if this is one.
    pub fn bv_width(&self) -> Option<u32> {
        match self {
            Sort::BitVec(n) => Some(*n),
            _ => None,
        }
    }
}

/// A term: its SMT-LIB 2 rendering plus its [`Sort`]. Cheap to clone; carries no
/// borrow of the [`Context`], so terms compose freely.
#[derive(Clone, Debug)]
pub struct Ast {
    src: String,
    sort: Sort,
}

impl Ast {
    /// The term's sort.
    pub fn sort(&self) -> &Sort {
        &self.sort
    }

    /// The term's SMT-LIB 2 rendering.
    pub fn to_smt(&self) -> &str {
        &self.src
    }

    /// Construct a term from its raw SMT-LIB 2 rendering and sort. The escape
    /// hatch used by the C ABI for constructors that don't map onto the typed
    /// combinators above.
    pub fn new(src: String, sort: Sort) -> Ast {
        Ast { src, sort }
    }

    /// Render a quantifier instantiation pattern `(t₁ … tₙ)` from its trigger
    /// terms — the group form consumed by [`Context::quantifier`]'s `:pattern`.
    pub fn pattern(terms: &[&Ast]) -> String {
        let mut src = String::from("(");
        for (i, t) in terms.iter().enumerate() {
            if i > 0 {
                src.push(' ');
            }
            src.push_str(&t.src);
        }
        src.push(')');
        src
    }

    /// `(distinct a₁ … aₙ)` — pairwise disequality (→ Bool).
    pub fn distinct(args: &[&Ast]) -> Ast {
        let mut src = String::from("(distinct");
        for a in args {
            src.push(' ');
            src.push_str(&a.src);
        }
        src.push(')');
        Ast { src, sort: Sort::Bool }
    }

    fn binop(&self, op: &str, rhs: &Ast, sort: Sort) -> Ast {
        Ast {
            src: alloc::format!("({op} {} {})", self.src, rhs.src),
            sort,
        }
    }
    fn unop(&self, op: &str, sort: Sort) -> Ast {
        Ast {
            src: alloc::format!("({op} {})", self.src),
            sort,
        }
    }

    // --- arithmetic (Int/Real) -------------------------------------------
    pub fn add(&self, rhs: &Ast) -> Ast {
        self.binop("+", rhs, self.sort.clone())
    }
    pub fn sub(&self, rhs: &Ast) -> Ast {
        self.binop("-", rhs, self.sort.clone())
    }
    pub fn mul(&self, rhs: &Ast) -> Ast {
        self.binop("*", rhs, self.sort.clone())
    }
    pub fn neg(&self) -> Ast {
        self.unop("-", self.sort.clone())
    }

    // --- comparisons (→ Bool) --------------------------------------------
    pub fn lt(&self, rhs: &Ast) -> Ast {
        self.binop("<", rhs, Sort::Bool)
    }
    pub fn le(&self, rhs: &Ast) -> Ast {
        self.binop("<=", rhs, Sort::Bool)
    }
    pub fn gt(&self, rhs: &Ast) -> Ast {
        self.binop(">", rhs, Sort::Bool)
    }
    pub fn ge(&self, rhs: &Ast) -> Ast {
        self.binop(">=", rhs, Sort::Bool)
    }
    /// Structural equality `(= self rhs)`.
    pub fn eq(&self, rhs: &Ast) -> Ast {
        self.binop("=", rhs, Sort::Bool)
    }
    /// Disequality `(not (= self rhs))`.
    pub fn ne(&self, rhs: &Ast) -> Ast {
        self.eq(rhs).not()
    }

    // --- Boolean connectives ---------------------------------------------
    pub fn and(&self, rhs: &Ast) -> Ast {
        self.binop("and", rhs, Sort::Bool)
    }
    pub fn or(&self, rhs: &Ast) -> Ast {
        self.binop("or", rhs, Sort::Bool)
    }
    pub fn implies(&self, rhs: &Ast) -> Ast {
        self.binop("=>", rhs, Sort::Bool)
    }
    pub fn xor(&self, rhs: &Ast) -> Ast {
        self.binop("xor", rhs, Sort::Bool)
    }
    pub fn not(&self) -> Ast {
        self.unop("not", Sort::Bool)
    }

    pub fn iff(&self, rhs: &Ast) -> Ast {
        self.binop("=", rhs, Sort::Bool)
    }

    /// `(ite self then els)` — `self` is the Boolean condition; result sort is
    /// that of the branches.
    pub fn ite(&self, then: &Ast, els: &Ast) -> Ast {
        Ast {
            src: alloc::format!("(ite {} {} {})", self.src, then.src, els.src),
            sort: then.sort.clone(),
        }
    }

    // --- more arithmetic --------------------------------------------------
    pub fn div(&self, rhs: &Ast) -> Ast {
        // Integer division renders as `div`; real division as `/`.
        let op = if self.sort == Sort::Int { "div" } else { "/" };
        self.binop(op, rhs, self.sort.clone())
    }
    pub fn rem_(&self, rhs: &Ast) -> Ast {
        self.binop("rem", rhs, self.sort.clone())
    }
    pub fn modulo(&self, rhs: &Ast) -> Ast {
        self.binop("mod", rhs, self.sort.clone())
    }
    pub fn power(&self, rhs: &Ast) -> Ast {
        self.binop("^", rhs, self.sort.clone())
    }
    pub fn int2real(&self) -> Ast {
        self.unop("to_real", Sort::Real)
    }
    pub fn real2int(&self) -> Ast {
        self.unop("to_int", Sort::Int)
    }
    pub fn is_int(&self) -> Ast {
        self.unop("is_int", Sort::Bool)
    }

    // --- bit-vectors: arithmetic / logical (result = operand sort) --------
    pub fn bvadd(&self, rhs: &Ast) -> Ast {
        self.binop("bvadd", rhs, self.sort.clone())
    }
    pub fn bvsub(&self, rhs: &Ast) -> Ast {
        self.binop("bvsub", rhs, self.sort.clone())
    }
    pub fn bvmul(&self, rhs: &Ast) -> Ast {
        self.binop("bvmul", rhs, self.sort.clone())
    }
    pub fn bvudiv(&self, rhs: &Ast) -> Ast {
        self.binop("bvudiv", rhs, self.sort.clone())
    }
    pub fn bvsdiv(&self, rhs: &Ast) -> Ast {
        self.binop("bvsdiv", rhs, self.sort.clone())
    }
    pub fn bvurem(&self, rhs: &Ast) -> Ast {
        self.binop("bvurem", rhs, self.sort.clone())
    }
    pub fn bvsrem(&self, rhs: &Ast) -> Ast {
        self.binop("bvsrem", rhs, self.sort.clone())
    }
    pub fn bvsmod(&self, rhs: &Ast) -> Ast {
        self.binop("bvsmod", rhs, self.sort.clone())
    }
    pub fn bvand(&self, rhs: &Ast) -> Ast {
        self.binop("bvand", rhs, self.sort.clone())
    }
    pub fn bvor(&self, rhs: &Ast) -> Ast {
        self.binop("bvor", rhs, self.sort.clone())
    }
    pub fn bvxor(&self, rhs: &Ast) -> Ast {
        self.binop("bvxor", rhs, self.sort.clone())
    }
    pub fn bvnand(&self, rhs: &Ast) -> Ast {
        self.binop("bvnand", rhs, self.sort.clone())
    }
    pub fn bvnor(&self, rhs: &Ast) -> Ast {
        self.binop("bvnor", rhs, self.sort.clone())
    }
    pub fn bvxnor(&self, rhs: &Ast) -> Ast {
        self.binop("bvxnor", rhs, self.sort.clone())
    }
    pub fn bvshl(&self, rhs: &Ast) -> Ast {
        self.binop("bvshl", rhs, self.sort.clone())
    }
    pub fn bvlshr(&self, rhs: &Ast) -> Ast {
        self.binop("bvlshr", rhs, self.sort.clone())
    }
    pub fn bvashr(&self, rhs: &Ast) -> Ast {
        self.binop("bvashr", rhs, self.sort.clone())
    }
    pub fn bvnot(&self) -> Ast {
        self.unop("bvnot", self.sort.clone())
    }
    pub fn bvneg(&self) -> Ast {
        self.unop("bvneg", self.sort.clone())
    }

    // --- bit-vectors: comparisons (→ Bool) --------------------------------
    pub fn bvult(&self, rhs: &Ast) -> Ast {
        self.binop("bvult", rhs, Sort::Bool)
    }
    pub fn bvslt(&self, rhs: &Ast) -> Ast {
        self.binop("bvslt", rhs, Sort::Bool)
    }
    pub fn bvule(&self, rhs: &Ast) -> Ast {
        self.binop("bvule", rhs, Sort::Bool)
    }
    pub fn bvsle(&self, rhs: &Ast) -> Ast {
        self.binop("bvsle", rhs, Sort::Bool)
    }
    pub fn bvugt(&self, rhs: &Ast) -> Ast {
        self.binop("bvugt", rhs, Sort::Bool)
    }
    pub fn bvsgt(&self, rhs: &Ast) -> Ast {
        self.binop("bvsgt", rhs, Sort::Bool)
    }
    pub fn bvuge(&self, rhs: &Ast) -> Ast {
        self.binop("bvuge", rhs, Sort::Bool)
    }
    pub fn bvsge(&self, rhs: &Ast) -> Ast {
        self.binop("bvsge", rhs, Sort::Bool)
    }

    // --- bit-vectors: shape-changing --------------------------------------
    /// `(concat self rhs)` — widths add.
    pub fn concat(&self, rhs: &Ast) -> Ast {
        let w = self.sort.bv_width().unwrap_or(0) + rhs.sort.bv_width().unwrap_or(0);
        self.binop("concat", rhs, Sort::BitVec(w))
    }
    /// `((_ extract high low) self)` — result width `high - low + 1`.
    pub fn extract(&self, high: u32, low: u32) -> Ast {
        Ast {
            src: alloc::format!("((_ extract {high} {low}) {})", self.src),
            sort: Sort::BitVec(high.saturating_sub(low) + 1),
        }
    }
    pub fn sign_ext(&self, i: u32) -> Ast {
        Ast {
            src: alloc::format!("((_ sign_extend {i}) {})", self.src),
            sort: Sort::BitVec(self.sort.bv_width().unwrap_or(0) + i),
        }
    }
    pub fn zero_ext(&self, i: u32) -> Ast {
        Ast {
            src: alloc::format!("((_ zero_extend {i}) {})", self.src),
            sort: Sort::BitVec(self.sort.bv_width().unwrap_or(0) + i),
        }
    }
    pub fn repeat(&self, i: u32) -> Ast {
        Ast {
            src: alloc::format!("((_ repeat {i}) {})", self.src),
            sort: Sort::BitVec(self.sort.bv_width().unwrap_or(0) * i),
        }
    }
    pub fn rotate_left(&self, i: u32) -> Ast {
        Ast {
            src: alloc::format!("((_ rotate_left {i}) {})", self.src),
            sort: self.sort.clone(),
        }
    }
    pub fn rotate_right(&self, i: u32) -> Ast {
        Ast {
            src: alloc::format!("((_ rotate_right {i}) {})", self.src),
            sort: self.sort.clone(),
        }
    }
    /// `((_ int2bv n) self)` — an integer to a width-`n` bit-vector.
    pub fn int2bv(&self, n: u32) -> Ast {
        Ast {
            src: alloc::format!("((_ int2bv {n}) {})", self.src),
            sort: Sort::BitVec(n),
        }
    }
    /// `(bv2int self)` — a bit-vector to a (non-negative, unsigned) integer.
    pub fn bv2int(&self, _signed: bool) -> Ast {
        self.unop("bv2int", Sort::Int)
    }

    // --- arrays -----------------------------------------------------------
    /// `(select self index)` — result is the array's range sort.
    pub fn select(&self, index: &Ast) -> Ast {
        let range = match &self.sort {
            Sort::Array(_, r) => (**r).clone(),
            other => other.clone(),
        };
        self.binop("select", index, range)
    }
    /// `(store self index value)` — result is the (unchanged) array sort.
    pub fn store(&self, index: &Ast, value: &Ast) -> Ast {
        Ast {
            src: alloc::format!("(store {} {} {})", self.src, index.src, value.src),
            sort: self.sort.clone(),
        }
    }

    // --- numeral readback (the C ABI's `Z3_get_numeral_*`) ----------------

    /// Whether this term is a numeral *literal* — an integer, rational, or
    /// bit-vector constant — by its syntactic form (matching `Z3_NUMERAL_AST`).
    pub fn is_numeral(&self) -> bool {
        parse_numeral(&self.src).is_some()
    }

    /// The numeral as a reduced rational `(numerator, denominator)` (denominator
    /// positive), if this term is a numeral literal.
    pub fn as_rational(&self) -> Option<(i128, i128)> {
        parse_numeral(&self.src)
    }

    /// The numeral as an integer, if it is one (rejects genuine rationals).
    pub fn as_int(&self) -> Option<i128> {
        match parse_numeral(&self.src)? {
            (n, 1) => Some(n),
            _ => None,
        }
    }

    /// The numeral's decimal (integer) or `p/q` (rational) string, matching
    /// `Z3_get_numeral_string`. `None` if this term is not a numeral literal.
    pub fn numeral_string(&self) -> Option<String> {
        let (n, d) = parse_numeral(&self.src)?;
        Some(if d == 1 {
            n.to_string()
        } else {
            alloc::format!("{n}/{d}")
        })
    }
}

/// Split `s` into its top-level whitespace/parenthesis-delimited parts (atoms
/// and `(...)` groups). ASCII-indexed, which is sound for SMT-LIB text.
pub(crate) fn top_level_parts(s: &str) -> Vec<&str> {
    let bytes = s.as_bytes();
    let mut parts = Vec::new();
    let mut depth: i32 = 0;
    let mut start: Option<usize> = None;
    for (i, &c) in bytes.iter().enumerate() {
        match c {
            b'(' => {
                if depth == 0 && start.is_none() {
                    start = Some(i);
                }
                depth += 1;
            }
            b')' => {
                depth -= 1;
                if depth == 0 && let Some(st) = start.take() {
                    parts.push(&s[st..=i]);
                }
            }
            c if c.is_ascii_whitespace() => {
                if depth == 0 && let Some(st) = start.take() {
                    parts.push(&s[st..i]);
                }
            }
            _ => {
                if depth == 0 && start.is_none() {
                    start = Some(i);
                }
            }
        }
    }
    if let Some(st) = start {
        parts.push(&s[st..]);
    }
    parts
}

fn gcd(mut a: u128, mut b: u128) -> u128 {
    while b != 0 {
        let t = a % b;
        a = b;
        b = t;
    }
    a
}

/// Reduce `n/d` to lowest terms with a positive denominator.
fn reduce(mut n: i128, mut d: i128) -> Option<(i128, i128)> {
    if d == 0 {
        return None;
    }
    if d < 0 {
        n = -n;
        d = -d;
    }
    let g = gcd(n.unsigned_abs(), d.unsigned_abs());
    if g > 1 {
        n /= g as i128;
        d /= g as i128;
    }
    Some((n, d))
}

/// Parse an SMT-LIB numeral *literal* into a reduced rational `(num, den)`.
/// Handles decimals (`6`, `-3`), `(- n)`, `(/ p q)`, hex/binary bit-vector
/// constants (`#x0f`, `#b1010`), `(_ bvN W)`, and simple decimals (`1.5`).
/// Returns `None` for anything that is not a self-contained numeral literal.
fn parse_numeral(s: &str) -> Option<(i128, i128)> {
    let s = s.trim();
    if s.is_empty() {
        return None;
    }
    // Hex / binary bit-vector constants.
    if let Some(hex) = s.strip_prefix("#x") {
        if !hex.is_empty() && hex.bytes().all(|b| b.is_ascii_hexdigit()) {
            return i128::from_str_radix(hex, 16).ok().map(|n| (n, 1));
        }
        return None;
    }
    if let Some(bin) = s.strip_prefix("#b") {
        if !bin.is_empty() && bin.bytes().all(|b| b == b'0' || b == b'1') {
            return i128::from_str_radix(bin, 2).ok().map(|n| (n, 1));
        }
        return None;
    }
    // `(_ bvN W)` bit-vector value.
    if let Some(rest) = s.strip_prefix("(_ bv") {
        let digits: String = rest.chars().take_while(|c| c.is_ascii_digit()).collect();
        if !digits.is_empty() {
            return digits.parse::<i128>().ok().map(|n| (n, 1));
        }
        return None;
    }
    // Parenthesised `(- x)` or `(/ p q)`.
    if let Some(inner) = s.strip_prefix('(').and_then(|r| r.strip_suffix(')')) {
        let parts = top_level_parts(inner);
        match parts.as_slice() {
            ["-", x] => {
                let (n, d) = parse_numeral(x)?;
                return Some((-n, d));
            }
            ["/", p, q] => {
                let (pn, pd) = parse_numeral(p)?;
                let (qn, qd) = parse_numeral(q)?;
                return reduce(pn.checked_mul(qd)?, pd.checked_mul(qn)?);
            }
            _ => return None,
        }
    }
    // Simple decimal `123.456`.
    if let Some(dot) = s.find('.') {
        let (int_part, frac_part) = (&s[..dot], &s[dot + 1..]);
        let neg = int_part.starts_with('-');
        let int_digits = int_part.strip_prefix('-').unwrap_or(int_part);
        if (int_digits.is_empty() || int_digits.bytes().all(|b| b.is_ascii_digit()))
            && frac_part.bytes().all(|b| b.is_ascii_digit())
            && frac_part.len() <= 30
        {
            let combined = alloc::format!("{int_digits}{frac_part}");
            let num = combined.parse::<i128>().ok()?;
            let mut den: i128 = 1;
            for _ in 0..frac_part.len() {
                den = den.checked_mul(10)?;
            }
            return reduce(if neg { -num } else { num }, den);
        }
        return None;
    }
    // Plain integer.
    s.parse::<i128>().ok().map(|n| (n, 1))
}

/// An uninterpreted function declaration (Z3's `Z3_func_decl`). Apply it to
/// arguments with [`FuncDecl::apply`].
#[derive(Clone, Debug)]
pub struct FuncDecl {
    name: String,
    range: Sort,
}

impl FuncDecl {
    /// Construct a declaration handle from a name and range sort. Used by the C
    /// ABI to synthesise `Z3_func_decl`s for model constants and `Z3_get_app_decl`.
    pub fn new(name: String, range: Sort) -> FuncDecl {
        FuncDecl { name, range }
    }

    /// The declaration's name.
    pub fn name(&self) -> &str {
        &self.name
    }

    /// The declaration's range (result) sort.
    pub fn range(&self) -> &Sort {
        &self.range
    }

    /// Apply the function to `args` — `(name a₁ … aₙ)`, or just `name` when
    /// nullary. Result sort is the declared range.
    pub fn apply(&self, args: &[&Ast]) -> Ast {
        if args.is_empty() {
            return Ast {
                src: self.name.clone(),
                sort: self.range.clone(),
            };
        }
        let mut src = alloc::format!("({}", self.name);
        for a in args {
            src.push(' ');
            src.push_str(&a.src);
        }
        src.push(')');
        Ast {
            src,
            sort: self.range.clone(),
        }
    }
}

/// A logical context: it owns the underlying [`Session`] and remembers which
/// constants have been declared, so building the same constant twice is safe.
pub struct Context {
    session: Session,
    declared: BTreeSet<String>,
    /// Every declaration command (`declare-const`/`declare-fun`/`declare-sort`)
    /// issued, in order — used to seed independent per-solver sessions.
    decls: Vec<String>,
    /// Counter feeding [`Context::fresh_const`] unique names.
    fresh: u64,
}

impl Default for Context {
    fn default() -> Context {
        Context::new()
    }
}

impl Context {
    /// A fresh context.
    pub fn new() -> Context {
        Context {
            session: Session::new(),
            declared: BTreeSet::new(),
            decls: Vec::new(),
            fresh: 0,
        }
    }

    /// The declaration commands issued so far (for seeding solver sessions).
    pub fn declarations(&self) -> &[String] {
        &self.decls
    }

    /// Record a declaration command: eval it against the context session and
    /// remember it so freshly-created solvers can replay it.
    fn declare(&mut self, cmd: String) {
        let _ = self.session.eval(&cmd);
        self.decls.push(cmd);
    }

    /// Declare (once) and return a constant of the given sort.
    pub fn const_(&mut self, name: &str, sort: Sort) -> Ast {
        if self.declared.insert(name.to_string()) {
            self.declare(alloc::format!("(declare-const {name} {})", sort.smt()));
        }
        Ast {
            src: name.to_string(),
            sort,
        }
    }

    /// Declare an uninterpreted function and return its [`FuncDecl`]. A 0-arity
    /// declaration behaves like a constant.
    pub fn declare_func(&mut self, name: &str, domain: Vec<Sort>, range: Sort) -> FuncDecl {
        if self.declared.insert(name.to_string()) {
            let doms: Vec<String> = domain.iter().map(Sort::smt).collect();
            self.declare(alloc::format!(
                "(declare-fun {name} ({}) {})",
                doms.join(" "),
                range.smt()
            ));
        }
        FuncDecl {
            name: name.to_string(),
            range,
        }
    }

    /// Declare an uninterpreted sort of arity 0 and return it.
    pub fn declare_sort(&mut self, name: &str) -> Sort {
        if self.declared.insert(alloc::format!("sort:{name}")) {
            self.declare(alloc::format!("(declare-sort {name} 0)"));
        }
        Sort::Uninterpreted(name.to_string())
    }

    /// Declare (once) an algebraic datatype and return its [`Sort`]. `ctors_body`
    /// is the space-separated list of constructor S-expressions — e.g.
    /// `"(nil) (cons (hd Int) (tl List))"` — which is wrapped into a
    /// `(declare-datatype Name (…))` command and evaluated against the session.
    pub fn declare_datatype(&mut self, name: &str, ctors_body: &str) -> Sort {
        if self.declared.insert(alloc::format!("sort:{name}")) {
            self.declare(alloc::format!("(declare-datatype {name} ({ctors_body}))"));
        }
        Sort::Datatype(name.to_string())
    }

    /// A freshly-named constant of the given sort (`prefix!N`).
    pub fn fresh_const(&mut self, prefix: &str, sort: Sort) -> Ast {
        self.fresh += 1;
        let name = alloc::format!("{prefix}!{}", self.fresh);
        self.const_(&name, sort)
    }

    /// A constant array `((as const (Array dom range)) value)`.
    pub fn const_array(domain: Sort, value: &Ast) -> Ast {
        let arr = Sort::Array(
            alloc::boxed::Box::new(domain),
            alloc::boxed::Box::new(value.sort.clone()),
        );
        Ast {
            src: alloc::format!("((as const {}) {})", arr.smt(), value.src),
            sort: arr,
        }
    }

    /// Build a quantified formula (→ Bool). `bound` lists the bound variables as
    /// `(name, sort)` pairs (rendered `((name Sort) …)`); `patterns` are the
    /// already-rendered instantiation patterns (each the `(t₁ … tₙ)` form from
    /// [`Ast::pattern`]); `weight` annotates the quantifier when non-zero. When
    /// there are patterns (or a weight), the body is wrapped as
    /// `(! body :pattern … :weight w)`.
    ///
    /// ```
    /// use z3rs::api::build::{Ast, Context, Sort};
    /// let body = Ast::new("(>= (f x) 0)".to_string(), Sort::Bool);
    /// let q = Context::quantifier(true, 0, &[("x", &Sort::Int)], &[], &body);
    /// assert_eq!(q.to_smt(), "(forall ((x Int)) (>= (f x) 0))");
    /// ```
    pub fn quantifier(
        is_forall: bool,
        weight: u32,
        bound: &[(&str, &Sort)],
        patterns: &[&str],
        body: &Ast,
    ) -> Ast {
        let kw = if is_forall { "forall" } else { "exists" };
        let mut vars = String::new();
        for (name, sort) in bound {
            vars.push_str(&alloc::format!("({name} {})", sort.smt()));
        }
        // Body, optionally annotated with patterns / weight.
        let inner = if patterns.is_empty() && weight == 0 {
            body.src.clone()
        } else {
            let mut ann = alloc::format!("(! {}", body.src);
            for p in patterns {
                ann.push_str(" :pattern ");
                ann.push_str(p);
            }
            if weight != 0 {
                ann.push_str(&alloc::format!(" :weight {weight}"));
            }
            ann.push(')');
            ann
        };
        Ast {
            src: alloc::format!("({kw} ({vars}) {inner})"),
            sort: Sort::Bool,
        }
    }

    /// An integer numeral.
    pub fn int(v: i64) -> Ast {
        // Negative literals render as `(- n)` for SMT-LIB well-formedness.
        let src = if v < 0 {
            alloc::format!("(- {})", -(v as i128))
        } else {
            v.to_string()
        };
        Ast { src, sort: Sort::Int }
    }

    /// A real numeral from an integer value.
    pub fn real(v: i64) -> Ast {
        let inner = Context::int(v);
        Ast {
            src: inner.src,
            sort: Sort::Real,
        }
    }

    /// The Boolean constants.
    pub fn bool_val(b: bool) -> Ast {
        Ast {
            src: if b { "true" } else { "false" }.to_string(),
            sort: Sort::Bool,
        }
    }

    /// A bit-vector numeral of the given width (rendered as `(_ bvV W)`).
    pub fn bv_val(v: u64, width: u32) -> Ast {
        Ast {
            src: alloc::format!("(_ bv{v} {width})"),
            sort: Sort::BitVec(width),
        }
    }

    /// A numeral parsed from its SMT-LIB 2 text (`"3"`, `"1/2"`, `"#x0f"`), with
    /// the caller-supplied sort — the general builder the C `Z3_mk_numeral` uses.
    pub fn numeral(s: &str, sort: Sort) -> Ast {
        Ast {
            src: s.to_string(),
            sort,
        }
    }

    /// Assert a Boolean term.
    pub fn assert(&mut self, a: &Ast) {
        let _ = self.session.eval(&alloc::format!("(assert {})", a.src));
    }

    /// Evaluate a raw SMT-LIB 2 script against the context's session — the bridge
    /// used by the C ABI's `Z3_eval_smtlib2_string` so the object API and the
    /// string API share one persistent state.
    pub fn session_eval(&mut self, script: &str) -> Result<Vec<String>, String> {
        self.session.eval(script)
    }

    /// Decide the current assertions.
    pub fn check(&mut self) -> SatResult {
        match self
            .session
            .eval("(check-sat)")
            .ok()
            .and_then(|v| v.into_iter().next())
            .as_deref()
        {
            Some("sat") => SatResult::Sat,
            Some("unsat") => SatResult::Unsat,
            _ => SatResult::Unknown,
        }
    }

    /// Push / pop an assertion scope.
    pub fn push(&mut self) {
        let _ = self.session.eval("(push)");
    }
    pub fn pop(&mut self) {
        let _ = self.session.eval("(pop)");
    }

    /// The value of `a` in the model of the most recent satisfiable [`check`], as
    /// its printed SMT-LIB 2 form (e.g. `"6"`, `"#x0f"`).
    pub fn eval_value(&mut self, a: &Ast) -> Option<String> {
        let out = self
            .session
            .eval(&alloc::format!("(get-value ({}))", a.src))
            .ok()?;
        let line = out.first()?;
        // `((expr value))` → value.
        let inner = line.trim().strip_prefix('(')?.strip_suffix(')')?.trim();
        let inner = inner.strip_prefix('(')?.strip_suffix(')')?.trim();
        Some(inner.strip_prefix(&a.src).map(str::trim).unwrap_or(inner).to_string())
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn arithmetic_unsat() {
        let mut ctx = Context::new();
        let x = ctx.const_("x", Sort::Int);
        let three = Context::int(3);
        let four = Context::int(4);
        ctx.assert(&three.lt(&x));
        ctx.assert(&x.lt(&four));
        assert_eq!(ctx.check(), SatResult::Unsat); // no integer strictly between 3 and 4
    }

    #[test]
    fn boolean_and_model() {
        let mut ctx = Context::new();
        let x = ctx.const_("x", Sort::Int);
        ctx.assert(&x.ge(&Context::int(5)));
        ctx.assert(&x.le(&Context::int(5)));
        assert_eq!(ctx.check(), SatResult::Sat);
        assert_eq!(ctx.eval_value(&x).as_deref(), Some("5"));
    }

    #[test]
    fn push_pop_scopes() {
        let mut ctx = Context::new();
        let p = ctx.const_("p", Sort::Bool);
        ctx.assert(&p.or(&p.not()));
        assert_eq!(ctx.check(), SatResult::Sat);
        ctx.push();
        ctx.assert(&p.and(&p.not()));
        assert_eq!(ctx.check(), SatResult::Unsat);
        ctx.pop();
        assert_eq!(ctx.check(), SatResult::Sat);
    }

    #[test]
    fn bitvector_ops() {
        let mut ctx = Context::new();
        let b = ctx.const_("b", Sort::BitVec(8));
        // b + 1 = 16  ⇒  b = 15
        ctx.assert(&b.bvadd(&Context::bv_val(1, 8)).eq(&Context::bv_val(16, 8)));
        assert_eq!(ctx.check(), SatResult::Sat);
        assert_eq!(ctx.eval_value(&b).as_deref(), Some("#x0f"));
    }

    #[test]
    fn array_select_store() {
        let mut ctx = Context::new();
        let idx = Sort::Int;
        let arr = Sort::Array(
            alloc::boxed::Box::new(idx.clone()),
            alloc::boxed::Box::new(Sort::Int),
        );
        let m = ctx.const_("m", arr);
        // (select (store m 3 7) 3) = 7 is valid, so its negation is unsat.
        let stored = m.store(&Context::int(3), &Context::int(7));
        let sel = stored.select(&Context::int(3));
        ctx.assert(&sel.ne(&Context::int(7)));
        assert_eq!(ctx.check(), SatResult::Unsat);
    }

    #[test]
    fn ite_and_distinct() {
        let mut ctx = Context::new();
        let x = ctx.const_("x", Sort::Int);
        let y = ctx.const_("y", Sort::Int);
        // distinct x y, and z = ite (x < y) x y = min; assert z = x and z = y -> unsat.
        ctx.assert(&Ast::distinct(&[&x, &y]));
        let z = x.lt(&y).ite(&x, &y);
        ctx.assert(&z.eq(&x));
        ctx.assert(&z.eq(&y));
        assert_eq!(ctx.check(), SatResult::Unsat);
    }

    #[test]
    fn uf_apply_congruence() {
        let mut ctx = Context::new();
        let f = ctx.declare_func("f", alloc::vec![Sort::Int], Sort::Int);
        let x = ctx.const_("x", Sort::Int);
        let y = ctx.const_("y", Sort::Int);
        ctx.assert(&x.eq(&y));
        ctx.assert(&f.apply(&[&x]).ne(&f.apply(&[&y])));
        assert_eq!(ctx.check(), SatResult::Unsat);
    }

    #[test]
    fn bitvector_extended_ops() {
        let mut ctx = Context::new();
        let b = ctx.const_("b", Sort::BitVec(8));
        // (bvsub b 1) = 14  ⇒  b = 15
        ctx.assert(&b.bvsub(&Context::bv_val(1, 8)).eq(&Context::bv_val(14, 8)));
        assert_eq!(ctx.check(), SatResult::Sat);
        assert_eq!(ctx.eval_value(&b).as_deref(), Some("#x0f"));
    }

    #[test]
    fn numeral_readback() {
        let bv = |s: &str| Ast::new(s.to_string(), Sort::BitVec(8));
        let int = |s: &str| Ast::new(s.to_string(), Sort::Int);
        let real = |s: &str| Ast::new(s.to_string(), Sort::Real);

        assert_eq!(int("6").numeral_string().as_deref(), Some("6"));
        assert_eq!(int("6").as_int(), Some(6));
        assert_eq!(int("(- 6)").numeral_string().as_deref(), Some("-6"));
        assert_eq!(int("(- 6)").as_int(), Some(-6));
        assert_eq!(bv("#x0f").numeral_string().as_deref(), Some("15"));
        assert_eq!(bv("#x0f").as_int(), Some(15));
        assert_eq!(bv("#b1010").as_int(), Some(10));
        assert_eq!(bv("(_ bv15 8)").as_int(), Some(15));
        assert_eq!(real("(/ 1 2)").numeral_string().as_deref(), Some("1/2"));
        assert_eq!(real("(/ 1 2)").as_int(), None);
        assert_eq!(real("(/ (- 3) 6)").numeral_string().as_deref(), Some("-1/2"));
        assert_eq!(real("1.5").numeral_string().as_deref(), Some("3/2"));
        assert_eq!(real("2.0").as_int(), Some(2));

        // Non-numerals.
        assert!(!Ast::new("x".to_string(), Sort::Int).is_numeral());
        assert!(!Ast::new("(+ x 1)".to_string(), Sort::Int).is_numeral());
        assert!(!Ast::new("(- x 1)".to_string(), Sort::Int).is_numeral());
        assert!(!Ast::new("true".to_string(), Sort::Bool).is_numeral());
        assert!(int("6").is_numeral());
    }

    #[test]
    fn forall_uf_unsat() {
        // forall x. f(x) >= 0, and f(3) < 0  ⇒  unsat.
        let mut ctx = Context::new();
        let f = ctx.declare_func("f", alloc::vec![Sort::Int], Sort::Int);
        let x = Ast::new("x".to_string(), Sort::Int);
        let body = f.apply(&[&x]).ge(&Context::int(0));
        let q = Context::quantifier(true, 0, &[("x", &Sort::Int)], &[], &body);
        ctx.assert(&q);
        ctx.assert(&f.apply(&[&Context::int(3)]).lt(&Context::int(0)));
        assert_eq!(ctx.check(), SatResult::Unsat);
    }

    #[test]
    fn forall_with_pattern() {
        let mut ctx = Context::new();
        let f = ctx.declare_func("f", alloc::vec![Sort::Int], Sort::Int);
        let x = Ast::new("x".to_string(), Sort::Int);
        let fx = f.apply(&[&x]);
        let pat = Ast::pattern(&[&fx]);
        let body = fx.ge(&Context::int(0));
        let q = Context::quantifier(true, 1, &[("x", &Sort::Int)], &[&pat], &body);
        assert!(q.to_smt().contains(":pattern"));
        assert!(q.to_smt().contains(":weight 1"));
        ctx.assert(&q);
        ctx.assert(&f.apply(&[&Context::int(3)]).lt(&Context::int(0)));
        assert_eq!(ctx.check(), SatResult::Unsat);
    }

    #[test]
    fn datatype_list_sat() {
        // List = nil | cons(hd: Int, tl: List); assert l = cons(1, nil).
        let mut ctx = Context::new();
        let lst = ctx.declare_datatype("Lst", "(nil) (cons (hd Int) (tl Lst))");
        assert_eq!(lst, Sort::Datatype("Lst".to_string()));
        let l = ctx.const_("l", lst);
        let cons1 = Ast::new("(cons 1 nil)".to_string(), Sort::Datatype("Lst".to_string()));
        ctx.assert(&l.eq(&cons1));
        let hd_l = Ast::new("(hd l)".to_string(), Sort::Int);
        ctx.assert(&hd_l.eq(&Context::int(1)));
        assert_eq!(ctx.check(), SatResult::Sat);
    }

    #[test]
    fn uf_congruence_unsat() {
        // Reusing declare via raw session isn't needed: build with consts only.
        let mut ctx = Context::new();
        let x = ctx.const_("x", Sort::Int);
        let y = ctx.const_("y", Sort::Int);
        ctx.assert(&x.eq(&y));
        ctx.assert(&x.add(&Context::int(1)).ne(&y.add(&Context::int(1))));
        assert_eq!(ctx.check(), SatResult::Unsat);
    }
}
