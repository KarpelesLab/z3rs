//! Term pretty-printing in SMT-LIB-ish s-expression form.
//!
//! A lightweight counterpart of Z3's `ast_smt2_pp` (`z3/src/ast`, MIT): enough
//! to render sorts, declarations, applications, and variables as readable
//! s-expressions for tests and debugging. Full SMT-LIB2 pretty-printing (let
//! sharing, line wrapping, quantifier binder names) comes later.

use alloc::string::String;

use crate::ast::AstId;
use crate::ast::manager::AstManager;
use crate::ast::node::AstNode;
use core::fmt::Write;

impl AstManager {
    /// Render `id` as an s-expression string.
    pub fn pp(&self, id: AstId) -> String {
        let mut out = String::new();
        self.pp_into(id, &mut out);
        out
    }

    fn pp_into(&self, id: AstId, out: &mut String) {
        match self.node(id) {
            AstNode::Sort(s) => {
                let _ = write!(out, "{}", s.name);
            }
            AstNode::FuncDecl(f) => {
                // (declare-fun name (dom...) range)
                let _ = write!(out, "(declare-fun {} (", f.name);
                for (i, &d) in f.domain.iter().enumerate() {
                    if i > 0 {
                        out.push(' ');
                    }
                    self.pp_into(d, out);
                }
                out.push_str(") ");
                self.pp_into(f.range, out);
                out.push(')');
            }
            AstNode::App(a) => {
                let name = self.func_decl(a.decl).expect("app decl").name;
                if a.args.is_empty() {
                    let _ = write!(out, "{name}");
                } else {
                    let _ = write!(out, "({name}");
                    for &arg in &a.args {
                        out.push(' ');
                        self.pp_into(arg, out);
                    }
                    out.push(')');
                }
            }
            AstNode::Var(v) => {
                let _ = write!(out, "(:var {})", v.index);
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::symbol::Symbol;

    #[test]
    fn prints_constants_and_applications() {
        let mut m = AstManager::new();
        let p = m.mk_bool_const("p");
        let q = m.mk_bool_const("q");
        assert_eq!(m.pp(p), "p");

        let notq = m.mk_not(q);
        assert_eq!(m.pp(notq), "(not q)");

        let or = m.mk_or(&[p, notq]);
        let eq = m.mk_eq(p, q);
        let f = m.mk_and(&[or, eq]);
        assert_eq!(m.pp(f), "(and (or p (not q)) (= p q))");
    }

    #[test]
    fn prints_uninterpreted_terms_and_vars() {
        let mut m = AstManager::new();
        let a = m.mk_uninterpreted_sort(Symbol::new("A"));
        let f = m.mk_func_decl(Symbol::new("f"), &[a], a);
        let xd = m.mk_func_decl(Symbol::new("x"), &[], a);
        let x = m.mk_const(xd);
        let fx = m.mk_app(f, &[x]);
        assert_eq!(m.pp(fx), "(f x)");

        let v = m.mk_var(2, a);
        assert_eq!(m.pp(v), "(:var 2)");
        assert_eq!(m.pp(a), "A");
    }
}
