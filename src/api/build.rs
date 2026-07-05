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
}

impl Sort {
    /// The SMT-LIB 2 rendering of the sort.
    fn smt(&self) -> String {
        match self {
            Sort::Bool => "Bool".to_string(),
            Sort::Int => "Int".to_string(),
            Sort::Real => "Real".to_string(),
            Sort::BitVec(n) => alloc::format!("(_ BitVec {n})"),
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

    // --- bit-vectors ------------------------------------------------------
    pub fn bvadd(&self, rhs: &Ast) -> Ast {
        self.binop("bvadd", rhs, self.sort.clone())
    }
    pub fn bvand(&self, rhs: &Ast) -> Ast {
        self.binop("bvand", rhs, self.sort.clone())
    }
    pub fn bvor(&self, rhs: &Ast) -> Ast {
        self.binop("bvor", rhs, self.sort.clone())
    }
    pub fn bvult(&self, rhs: &Ast) -> Ast {
        self.binop("bvult", rhs, Sort::Bool)
    }
}

/// A logical context: it owns the underlying [`Session`] and remembers which
/// constants have been declared, so building the same constant twice is safe.
pub struct Context {
    session: Session,
    declared: BTreeSet<String>,
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
        }
    }

    /// Declare (once) and return a constant of the given sort.
    pub fn const_(&mut self, name: &str, sort: Sort) -> Ast {
        if self.declared.insert(name.to_string()) {
            let _ = self
                .session
                .eval(&alloc::format!("(declare-const {name} {})", sort.smt()));
        }
        Ast {
            src: name.to_string(),
            sort,
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
