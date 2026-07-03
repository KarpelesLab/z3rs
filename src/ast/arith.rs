//! The arithmetic theory: the `Int` and `Real` sorts, numeral literals, and the
//! core arithmetic operators and comparisons. Ported from `arith_decl_plugin`
//! (`z3/src/ast/arith_decl_plugin.{h,cpp}`, Z3 4.17.0, MIT).
//!
//! Constructor methods on [`AstManager`], as with the [basic](crate::ast::basic)
//! family. Numerals are carried in a [`Parameter::Rational`] on a nullary decl,
//! exactly as Z3 stores `OP_NUM`. Transcendentals, `divmod`-by-zero variants and
//! the bit-vector arithmetic ops are deferred.

use alloc::string::ToString;
use alloc::vec;

use puremp::{Int, Rational};

use crate::ast::manager::AstManager;
use crate::ast::node::{DeclInfo, FuncDeclFlags};
use crate::ast::parameter::Parameter;
use crate::ast::{AstId, DeclKind, FamilyId, SortSize};
use crate::util::symbol::Symbol;

/// Arithmetic sorts (`arith_sort_kind` in Z3).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[repr(i32)]
pub enum ArithSortKind {
    /// The `Real` sort.
    Real = 0,
    /// The `Int` sort.
    Int = 1,
}

/// Arithmetic operators (`arith_op_kind` in Z3; discriminants match the subset
/// that is ported).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[repr(i32)]
pub enum ArithOp {
    /// A rational/integer numeral (`OP_NUM`).
    Num = 0,
    /// `<=`
    Le = 2,
    /// `>=`
    Ge = 3,
    /// `<`
    Lt = 4,
    /// `>`
    Gt = 5,
    /// `+`
    Add = 6,
    /// `-` (binary/n-ary)
    Sub = 7,
    /// unary `-`
    Uminus = 8,
    /// `*`
    Mul = 9,
    /// `/` (real division)
    Div = 10,
    /// `div` (integer division)
    Idiv = 11,
    /// `rem`
    Rem = 15,
    /// `mod`
    Mod = 16,
    /// `to_real`
    ToReal = 18,
    /// `to_int`
    ToInt = 19,
    /// `is_int`
    IsInt = 20,
    /// `abs`
    Abs = 21,
    /// `^` (power)
    Power = 22,
}

impl ArithOp {
    #[inline]
    const fn kind(self) -> DeclKind {
        self as DeclKind
    }
}

/// Arithmetic-family constructors.
impl AstManager {
    /// The arithmetic family id (registers "arith" on first use).
    fn arith_fid(&mut self) -> FamilyId {
        self.mk_family_id(Symbol::new("arith"))
    }

    fn mk_arith_sort(&mut self, name: &str, kind: ArithSortKind) -> AstId {
        let fid = self.arith_fid();
        self.mk_sort(
            Symbol::new(name),
            DeclInfo::new(fid, kind as DeclKind, alloc::vec::Vec::new()),
            SortSize::Infinite,
        )
    }

    /// The `Int` sort.
    pub fn mk_int_sort(&mut self) -> AstId {
        self.mk_arith_sort("Int", ArithSortKind::Int)
    }

    /// The `Real` sort.
    pub fn mk_real_sort(&mut self) -> AstId {
        self.mk_arith_sort("Real", ArithSortKind::Real)
    }

    /// A numeral of value `value`, of the `Int` sort if `is_int` else `Real`.
    pub fn mk_numeral(&mut self, value: Rational, is_int: bool) -> AstId {
        debug_assert!(
            !is_int || value.is_integer(),
            "integer numeral must be integral"
        );
        let sort = if is_int {
            self.mk_int_sort()
        } else {
            self.mk_real_sort()
        };
        let fid = self.arith_fid();
        let name = Symbol::new(&value.to_string());
        let info = DeclInfo::new(fid, ArithOp::Num.kind(), vec![Parameter::Rational(value)]);
        let decl = self.mk_func_decl_full(name, &[], sort, info, FuncDeclFlags::default());
        self.mk_const(decl)
    }

    /// An `Int` numeral from an `i64`.
    pub fn mk_int(&mut self, v: i64) -> AstId {
        self.mk_numeral(Rational::from_integer(Int::from(v)), true)
    }

    /// A `Real` numeral from an `i64`.
    pub fn mk_real(&mut self, v: i64) -> AstId {
        self.mk_numeral(Rational::from_integer(Int::from(v)), false)
    }

    /// An uninterpreted integer constant.
    pub fn mk_int_const(&mut self, name: &str) -> AstId {
        let s = self.mk_int_sort();
        let d = self.mk_func_decl(Symbol::new(name), &[], s);
        self.mk_const(d)
    }

    /// An uninterpreted real constant.
    pub fn mk_real_const(&mut self, name: &str) -> AstId {
        let s = self.mk_real_sort();
        let d = self.mk_func_decl(Symbol::new(name), &[], s);
        self.mk_const(d)
    }

    /// Build an arithmetic op `name`/`op` over the given operand `sort`.
    fn mk_arith_app(
        &mut self,
        name: &str,
        op: ArithOp,
        domain: &[AstId],
        range: AstId,
        flags: FuncDeclFlags,
        args: &[AstId],
    ) -> AstId {
        let fid = self.arith_fid();
        let info = DeclInfo::new(fid, op.kind(), alloc::vec::Vec::new());
        let decl = self.mk_func_decl_full(Symbol::new(name), domain, range, info, flags);
        self.mk_app(decl, args)
    }

    /// Binary/n-ary op whose result sort equals the operand sort.
    fn mk_arith_nary(
        &mut self,
        name: &str,
        op: ArithOp,
        flags: FuncDeclFlags,
        args: &[AstId],
    ) -> AstId {
        assert!(args.len() >= 2, "{name} needs at least two arguments");
        let sort = self.get_sort(args[0]);
        let domain = vec![sort; args.len()];
        self.mk_arith_app(name, op, &domain, sort, flags, args)
    }

    /// `(+ args...)`.
    pub fn mk_add(&mut self, args: &[AstId]) -> AstId {
        self.mk_arith_nary("+", ArithOp::Add, assoc_comm_flags(), args)
    }

    /// `(* args...)`.
    pub fn mk_mul(&mut self, args: &[AstId]) -> AstId {
        self.mk_arith_nary("*", ArithOp::Mul, assoc_comm_flags(), args)
    }

    /// `(- args...)` (n-ary subtraction).
    pub fn mk_sub(&mut self, args: &[AstId]) -> AstId {
        let flags = FuncDeclFlags {
            left_assoc: true,
            ..FuncDeclFlags::default()
        };
        self.mk_arith_nary("-", ArithOp::Sub, flags, args)
    }

    /// `(- a)` (unary minus).
    pub fn mk_uminus(&mut self, a: AstId) -> AstId {
        let sort = self.get_sort(a);
        self.mk_arith_app(
            "-",
            ArithOp::Uminus,
            &[sort],
            sort,
            FuncDeclFlags::default(),
            &[a],
        )
    }

    fn mk_cmp(&mut self, name: &str, op: ArithOp, a: AstId, b: AstId) -> AstId {
        let sort = self.get_sort(a);
        let bool_sort = self.mk_bool_sort();
        let flags = FuncDeclFlags {
            chainable: true,
            ..FuncDeclFlags::default()
        };
        self.mk_arith_app(name, op, &[sort, sort], bool_sort, flags, &[a, b])
    }

    /// `(<= a b)`.
    pub fn mk_le(&mut self, a: AstId, b: AstId) -> AstId {
        self.mk_cmp("<=", ArithOp::Le, a, b)
    }
    /// `(>= a b)`.
    pub fn mk_ge(&mut self, a: AstId, b: AstId) -> AstId {
        self.mk_cmp(">=", ArithOp::Ge, a, b)
    }
    /// `(< a b)`.
    pub fn mk_lt(&mut self, a: AstId, b: AstId) -> AstId {
        self.mk_cmp("<", ArithOp::Lt, a, b)
    }
    /// `(> a b)`.
    pub fn mk_gt(&mut self, a: AstId, b: AstId) -> AstId {
        self.mk_cmp(">", ArithOp::Gt, a, b)
    }

    /// `(/ a b)` — real division.
    pub fn mk_div(&mut self, a: AstId, b: AstId) -> AstId {
        let sort = self.get_sort(a);
        self.mk_arith_app(
            "/",
            ArithOp::Div,
            &[sort, sort],
            sort,
            FuncDeclFlags::default(),
            &[a, b],
        )
    }

    /// `(div a b)` — integer division.
    pub fn mk_idiv(&mut self, a: AstId, b: AstId) -> AstId {
        let sort = self.get_sort(a);
        self.mk_arith_app(
            "div",
            ArithOp::Idiv,
            &[sort, sort],
            sort,
            FuncDeclFlags::default(),
            &[a, b],
        )
    }

    /// `(mod a b)`.
    pub fn mk_mod(&mut self, a: AstId, b: AstId) -> AstId {
        let sort = self.get_sort(a);
        self.mk_arith_app(
            "mod",
            ArithOp::Mod,
            &[sort, sort],
            sort,
            FuncDeclFlags::default(),
            &[a, b],
        )
    }

    /// `(to_real a)`.
    pub fn mk_to_real(&mut self, a: AstId) -> AstId {
        let r = self.mk_real_sort();
        let i = self.mk_int_sort();
        self.mk_arith_app(
            "to_real",
            ArithOp::ToReal,
            &[i],
            r,
            FuncDeclFlags::default(),
            &[a],
        )
    }

    /// `(to_int a)`.
    pub fn mk_to_int(&mut self, a: AstId) -> AstId {
        let r = self.mk_real_sort();
        let i = self.mk_int_sort();
        self.mk_arith_app(
            "to_int",
            ArithOp::ToInt,
            &[r],
            i,
            FuncDeclFlags::default(),
            &[a],
        )
    }
}

/// `+`/`*` flags: associative, flat, commutative.
fn assoc_comm_flags() -> FuncDeclFlags {
    FuncDeclFlags {
        left_assoc: true,
        right_assoc: true,
        flat_associative: true,
        commutative: true,
        ..FuncDeclFlags::default()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn int_and_real_sorts_are_distinct() {
        let mut m = AstManager::new();
        let i = m.mk_int_sort();
        let r = m.mk_real_sort();
        assert_ne!(i, r);
        assert_eq!(m.sort(i).unwrap().name, Symbol::new("Int"));
        // arith family is registered after basic (id 0), so it is >= 1.
        assert!(m.sort(i).unwrap().info.family_id >= 1);
    }

    #[test]
    fn numerals_carry_their_value_and_sort() {
        let mut m = AstManager::new();
        let five = m.mk_int(5);
        let five2 = m.mk_int(5);
        assert_eq!(five, five2, "equal numerals are shared");
        assert_eq!(m.get_sort(five), m.mk_int_sort());
        let decl = m.app_decl(five);
        let param = &m.func_decl(decl).unwrap().info.parameters[0];
        assert_eq!(param.get_rational().unwrap().to_string(), "5");
        // Int 5 and Real 5 differ (different sort).
        let five_r = m.mk_real(5);
        assert_ne!(five, five_r);
    }

    #[test]
    fn build_and_print_arithmetic_atom() {
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let y = m.mk_int_const("y");
        let one = m.mk_int(1);
        // (<= (+ x y) 1)
        let sum = m.mk_add(&[x, y]);
        let le = m.mk_le(sum, one);
        assert_eq!(m.pp(le), "(<= (+ x y) 1)");
        assert_eq!(m.get_sort(le), m.mk_bool_sort());
        assert_eq!(m.get_sort(sum), m.mk_int_sort());
    }
}
