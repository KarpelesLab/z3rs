//! The built-in "basic" theory: the Boolean sort, the propositional
//! connectives, equality, `distinct`, and `ite`. Ported from
//! `basic_decl_plugin` in `z3/src/ast/ast.{h,cpp}` (Z3 4.17.0, MIT).
//!
//! Rather than a general `decl_plugin` registry (that abstraction comes with the
//! other theories), these are constructor methods on [`AstManager`]. Because
//! declarations are hash-consed, building the same connective decl repeatedly is
//! free — the manager returns the shared node — so no per-decl caching is needed.

use alloc::vec;

use crate::ast::manager::AstManager;
use crate::ast::node::{DeclInfo, FuncDeclFlags};
use crate::ast::{AstId, BASIC_FAMILY_ID, DeclKind, SortSize};
use crate::util::symbol::Symbol;

/// Basic sorts (`basic_sort_kind` in Z3).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[repr(i32)]
pub enum BasicSortKind {
    /// The Boolean sort.
    Bool = 0,
    /// The proof sort.
    Proof = 1,
}

/// Basic operators (`basic_op_kind` in Z3; discriminants match up to `OP_OEQ`).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[repr(i32)]
pub enum BasicOp {
    /// `true`
    True = 0,
    /// `false`
    False = 1,
    /// `=`
    Eq = 2,
    /// `distinct`
    Distinct = 3,
    /// `ite`
    Ite = 4,
    /// `and`
    And = 5,
    /// `or`
    Or = 6,
    /// `xor`
    Xor = 7,
    /// `not`
    Not = 8,
    /// `=>`
    Implies = 9,
    /// observational equality (`~`)
    Oeq = 10,
}

impl BasicOp {
    #[inline]
    const fn kind(self) -> DeclKind {
        self as DeclKind
    }
}

/// Boolean-family constructors.
impl AstManager {
    /// The Boolean sort (`Bool`), hash-consed.
    pub fn mk_bool_sort(&mut self) -> AstId {
        self.mk_sort(
            Symbol::new("Bool"),
            DeclInfo::new(
                BASIC_FAMILY_ID,
                BasicSortKind::Bool as DeclKind,
                alloc::vec::Vec::new(),
            ),
            SortSize::finite(2),
        )
    }

    /// Build a basic-family boolean connective decl and apply it.
    fn mk_basic_app(
        &mut self,
        name: &str,
        op: BasicOp,
        domain: &[AstId],
        range: AstId,
        flags: FuncDeclFlags,
        args: &[AstId],
    ) -> AstId {
        let info = DeclInfo::new(BASIC_FAMILY_ID, op.kind(), alloc::vec::Vec::new());
        let decl = self.mk_func_decl_full(Symbol::new(name), domain, range, info, flags);
        self.mk_app(decl, args)
    }

    /// The constant `true`.
    pub fn mk_true(&mut self) -> AstId {
        let b = self.mk_bool_sort();
        self.mk_basic_app("true", BasicOp::True, &[], b, FuncDeclFlags::default(), &[])
    }

    /// The constant `false`.
    pub fn mk_false(&mut self) -> AstId {
        let b = self.mk_bool_sort();
        self.mk_basic_app(
            "false",
            BasicOp::False,
            &[],
            b,
            FuncDeclFlags::default(),
            &[],
        )
    }

    /// `(not a)`.
    pub fn mk_not(&mut self, a: AstId) -> AstId {
        let b = self.mk_bool_sort();
        self.mk_basic_app("not", BasicOp::Not, &[b], b, FuncDeclFlags::default(), &[a])
    }

    /// `(and args...)` (n-ary). Panics if fewer than 2 args, as in Z3.
    pub fn mk_and(&mut self, args: &[AstId]) -> AstId {
        assert!(args.len() >= 2, "mk_and needs at least two arguments");
        let b = self.mk_bool_sort();
        let domain = vec![b; args.len()];
        self.mk_basic_app("and", BasicOp::And, &domain, b, and_or_flags(), args)
    }

    /// `(or args...)` (n-ary). Panics if fewer than 2 args, as in Z3.
    pub fn mk_or(&mut self, args: &[AstId]) -> AstId {
        assert!(args.len() >= 2, "mk_or needs at least two arguments");
        let b = self.mk_bool_sort();
        let domain = vec![b; args.len()];
        self.mk_basic_app("or", BasicOp::Or, &domain, b, and_or_flags(), args)
    }

    /// `(xor a b)`.
    pub fn mk_xor(&mut self, a: AstId, b_arg: AstId) -> AstId {
        let b = self.mk_bool_sort();
        let flags = FuncDeclFlags {
            left_assoc: true,
            right_assoc: true,
            commutative: true,
            ..FuncDeclFlags::default()
        };
        self.mk_basic_app("xor", BasicOp::Xor, &[b, b], b, flags, &[a, b_arg])
    }

    /// `(=> a b)`.
    pub fn mk_implies(&mut self, a: AstId, b_arg: AstId) -> AstId {
        let b = self.mk_bool_sort();
        let flags = FuncDeclFlags {
            right_assoc: true,
            ..FuncDeclFlags::default()
        };
        self.mk_basic_app("=>", BasicOp::Implies, &[b, b], b, flags, &[a, b_arg])
    }

    /// `(= l r)` — polymorphic equality over the sort of `l`.
    pub fn mk_eq(&mut self, l: AstId, r: AstId) -> AstId {
        let sort = self.get_sort(l);
        let b = self.mk_bool_sort();
        let flags = FuncDeclFlags {
            commutative: true,
            chainable: true,
            ..FuncDeclFlags::default()
        };
        self.mk_basic_app("=", BasicOp::Eq, &[sort, sort], b, flags, &[l, r])
    }

    /// `(distinct args...)` — pairwise disequality.
    pub fn mk_distinct(&mut self, args: &[AstId]) -> AstId {
        assert!(args.len() >= 2, "mk_distinct needs at least two arguments");
        let sort = self.get_sort(args[0]);
        let b = self.mk_bool_sort();
        let domain = vec![sort; args.len()];
        let flags = FuncDeclFlags {
            pairwise: true,
            ..FuncDeclFlags::default()
        };
        self.mk_basic_app("distinct", BasicOp::Distinct, &domain, b, flags, args)
    }

    /// `(ite c t e)` — the sort is the sort of `t`.
    pub fn mk_ite(&mut self, c: AstId, t: AstId, e: AstId) -> AstId {
        let sort = self.get_sort(t);
        let b = self.mk_bool_sort();
        self.mk_basic_app(
            "if",
            BasicOp::Ite,
            &[b, sort, sort],
            sort,
            FuncDeclFlags::default(),
            &[c, t, e],
        )
    }

    /// A fresh uninterpreted Boolean constant named `name` (a propositional
    /// variable).
    pub fn mk_bool_const(&mut self, name: &str) -> AstId {
        let b = self.mk_bool_sort();
        let decl = self.mk_func_decl(Symbol::new(name), &[], b);
        self.mk_const(decl)
    }

    /// Is `sort_id` the Boolean sort? (Read-only; does not register anything.)
    pub fn is_bool_sort(&self, sort_id: AstId) -> bool {
        self.sort(sort_id).is_some_and(|s| {
            s.info.family_id == BASIC_FAMILY_ID
                && s.info.decl_kind == BasicSortKind::Bool as DeclKind
        })
    }

    /// Is `expr` Boolean-sorted?
    pub fn is_bool(&self, expr: AstId) -> bool {
        self.is_bool_sort(self.get_sort(expr))
    }
}

/// Flags shared by `and`/`or`: associative, flat, commutative, idempotent.
fn and_or_flags() -> FuncDeclFlags {
    FuncDeclFlags {
        left_assoc: true,
        right_assoc: true,
        flat_associative: true,
        commutative: true,
        idempotent: true,
        ..FuncDeclFlags::default()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ast::AstKind;

    #[test]
    fn bool_sort_is_unique_and_finite() {
        let mut m = AstManager::new();
        let b1 = m.mk_bool_sort();
        let b2 = m.mk_bool_sort();
        assert_eq!(b1, b2);
        assert_eq!(m.sort(b1).unwrap().num_elements, SortSize::finite(2));
        assert_eq!(m.sort(b1).unwrap().info.family_id, BASIC_FAMILY_ID);
    }

    #[test]
    fn build_a_propositional_formula() {
        let mut m = AstManager::new();
        let p = m.mk_bool_const("p");
        let q = m.mk_bool_const("q");
        // (and (or p (not q)) (= p q))
        let notq = m.mk_not(q);
        let or = m.mk_or(&[p, notq]);
        let eq = m.mk_eq(p, q);
        let f = m.mk_and(&[or, eq]);

        assert_eq!(m.kind(f), AstKind::App);
        assert_eq!(m.get_sort(f), m.mk_bool_sort());
        // The and-decl is in the basic family with kind OP_AND.
        let and_decl = m.app_decl(f);
        let fd = m.func_decl(and_decl).unwrap();
        assert_eq!(fd.info.family_id, BASIC_FAMILY_ID);
        assert_eq!(fd.info.decl_kind, BasicOp::And as DeclKind);
        assert!(fd.flags.commutative && fd.flags.flat_associative);
    }

    #[test]
    fn structural_sharing_holds_for_formulas() {
        let mut m = AstManager::new();
        let p = m.mk_bool_const("p");
        let q = m.mk_bool_const("q");
        let a1 = m.mk_and(&[p, q]);
        let a2 = m.mk_and(&[p, q]);
        assert_eq!(a1, a2);
        // and is not commutative-normalized at construction: (and p q) != (and q p).
        let a3 = m.mk_and(&[q, p]);
        assert_ne!(a1, a3);
    }

    #[test]
    fn ite_and_eq_take_argument_sorts() {
        let mut m = AstManager::new();
        let a = m.mk_uninterpreted_sort(Symbol::new("A"));
        let xd = m.mk_func_decl(Symbol::new("x"), &[], a);
        let yd = m.mk_func_decl(Symbol::new("y"), &[], a);
        let x = m.mk_const(xd);
        let y = m.mk_const(yd);
        let c = m.mk_bool_const("c");
        let ite = m.mk_ite(c, x, y);
        assert_eq!(m.get_sort(ite), a);
        let eq = m.mk_eq(x, y);
        assert_eq!(m.get_sort(eq), m.mk_bool_sort());
        // eq's domain is over sort A, not Bool.
        let eq_decl = m.app_decl(eq);
        assert_eq!(m.func_decl(eq_decl).unwrap().domain[0], a);
    }
}
