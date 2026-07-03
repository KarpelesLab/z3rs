//! The fixed-width bit-vector theory: the parameterized `BitVec` sort, bit-vector
//! numerals, and a core of the arithmetic/comparison operators. Ported from
//! `bv_decl_plugin` (`z3/src/ast/bv_decl_plugin.{h,cpp}`, Z3 4.17.0, MIT).
//!
//! A first slice: the sort (with its width parameter), numerals, `bvneg`/`bvadd`
//! /`bvsub`/`bvmul`, and the unsigned comparisons `bvule`/`bvult`. The bitwise,
//! shift, signed, `concat`/`extract` families come next.

use alloc::vec;

use puremp::{Int, Rational};

use crate::ast::manager::AstManager;
use crate::ast::node::{DeclInfo, FuncDeclFlags};
use crate::ast::parameter::Parameter;
use crate::ast::{AstId, DeclKind, FamilyId, SortSize};
use crate::util::symbol::Symbol;

/// Bit-vector sorts (`bv_sort_kind` in Z3).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[repr(i32)]
pub enum BvSortKind {
    /// The bit-vector sort (parameterized by width).
    BitVec = 0,
}

/// Bit-vector operators (`bv_op_kind` in Z3; discriminants match the ported
/// subset).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[repr(i32)]
pub enum BvOp {
    /// A bit-vector numeral (`OP_BV_NUM`).
    Num = 0,
    /// `bvneg`
    Neg = 3,
    /// `bvadd`
    Add = 4,
    /// `bvsub`
    Sub = 5,
    /// `bvmul`
    Mul = 6,
    /// `bvule`
    Uleq = 22,
    /// `bvult`
    Ult = 26,
}

impl BvOp {
    #[inline]
    const fn kind(self) -> DeclKind {
        self as DeclKind
    }
}

/// Bit-vector-family constructors.
impl AstManager {
    fn bv_fid(&mut self) -> FamilyId {
        self.mk_family_id(Symbol::new("bv"))
    }

    /// The bit-vector sort of the given `width` (`(_ BitVec width)`).
    pub fn mk_bv_sort(&mut self, width: u32) -> AstId {
        let fid = self.bv_fid();
        // 2^width elements; very-big once it exceeds u64.
        let size = if width < 64 {
            SortSize::finite(1u64 << width)
        } else {
            SortSize::very_big()
        };
        self.mk_sort(
            Symbol::new(&alloc::format!("bv{width}")),
            DeclInfo::new(
                fid,
                BvSortKind::BitVec as DeclKind,
                vec![Parameter::Int(width as i32)],
            ),
            size,
        )
    }

    /// A bit-vector numeral of `value` (taken mod 2^width) at the given `width`.
    pub fn mk_bv_numeral(&mut self, value: Int, width: u32) -> AstId {
        let sort = self.mk_bv_sort(width);
        let fid = self.bv_fid();
        let value = value.mod_2k(width); // reduce to [0, 2^width)
        let name = Symbol::new(&alloc::format!("bv{value}"));
        let info = DeclInfo::new(
            fid,
            BvOp::Num.kind(),
            vec![Parameter::Rational(Rational::from_integer(value))],
        );
        let decl = self.mk_func_decl_full(name, &[], sort, info, FuncDeclFlags::default());
        self.mk_const(decl)
    }

    /// A bit-vector numeral from an unsigned `i64` at the given `width`.
    pub fn mk_bv(&mut self, value: i64, width: u32) -> AstId {
        self.mk_bv_numeral(Int::from(value), width)
    }

    /// An uninterpreted bit-vector constant of the given `width`.
    pub fn mk_bv_const(&mut self, name: &str, width: u32) -> AstId {
        let s = self.mk_bv_sort(width);
        let d = self.mk_func_decl(Symbol::new(name), &[], s);
        self.mk_const(d)
    }

    fn mk_bv_app(
        &mut self,
        name: &str,
        op: BvOp,
        domain: &[AstId],
        range: AstId,
        flags: FuncDeclFlags,
        args: &[AstId],
    ) -> AstId {
        let fid = self.bv_fid();
        let info = DeclInfo::new(fid, op.kind(), alloc::vec::Vec::new());
        let decl = self.mk_func_decl_full(Symbol::new(name), domain, range, info, flags);
        self.mk_app(decl, args)
    }

    /// A binary bit-vector op over the width of `a` (result same width).
    fn mk_bv_binop(
        &mut self,
        name: &str,
        op: BvOp,
        flags: FuncDeclFlags,
        a: AstId,
        b: AstId,
    ) -> AstId {
        let sort = self.get_sort(a);
        self.mk_bv_app(name, op, &[sort, sort], sort, flags, &[a, b])
    }

    /// `(bvneg a)`.
    pub fn mk_bvneg(&mut self, a: AstId) -> AstId {
        let sort = self.get_sort(a);
        self.mk_bv_app(
            "bvneg",
            BvOp::Neg,
            &[sort],
            sort,
            FuncDeclFlags::default(),
            &[a],
        )
    }

    /// `(bvadd a b)`.
    pub fn mk_bvadd(&mut self, a: AstId, b: AstId) -> AstId {
        let flags = FuncDeclFlags {
            left_assoc: true,
            right_assoc: true,
            commutative: true,
            ..FuncDeclFlags::default()
        };
        self.mk_bv_binop("bvadd", BvOp::Add, flags, a, b)
    }

    /// `(bvsub a b)`.
    pub fn mk_bvsub(&mut self, a: AstId, b: AstId) -> AstId {
        self.mk_bv_binop("bvsub", BvOp::Sub, FuncDeclFlags::default(), a, b)
    }

    /// `(bvmul a b)`.
    pub fn mk_bvmul(&mut self, a: AstId, b: AstId) -> AstId {
        let flags = FuncDeclFlags {
            left_assoc: true,
            right_assoc: true,
            commutative: true,
            ..FuncDeclFlags::default()
        };
        self.mk_bv_binop("bvmul", BvOp::Mul, flags, a, b)
    }

    fn mk_bv_cmp(&mut self, name: &str, op: BvOp, a: AstId, b: AstId) -> AstId {
        let sort = self.get_sort(a);
        let bool_sort = self.mk_bool_sort();
        self.mk_bv_app(
            name,
            op,
            &[sort, sort],
            bool_sort,
            FuncDeclFlags::default(),
            &[a, b],
        )
    }

    /// `(bvule a b)` — unsigned `<=`.
    pub fn mk_bvule(&mut self, a: AstId, b: AstId) -> AstId {
        self.mk_bv_cmp("bvule", BvOp::Uleq, a, b)
    }

    /// `(bvult a b)` — unsigned `<`.
    pub fn mk_bvult(&mut self, a: AstId, b: AstId) -> AstId {
        self.mk_bv_cmp("bvult", BvOp::Ult, a, b)
    }

    // --- recognizers ------------------------------------------------------

    /// The width of a bit-vector sort (or `None` if `sort_id` is not one).
    pub fn bv_sort_width(&self, sort_id: AstId) -> Option<u32> {
        let bvfid = self.get_family_id(Symbol::new("bv"))?;
        let s = self.sort(sort_id)?;
        if s.info.family_id == bvfid && s.info.decl_kind == BvSortKind::BitVec as DeclKind {
            s.info.parameters.first()?.get_int().map(|w| w as u32)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn bv_sort_carries_width() {
        let mut m = AstManager::new();
        let s8 = m.mk_bv_sort(8);
        let s8b = m.mk_bv_sort(8);
        let s16 = m.mk_bv_sort(16);
        assert_eq!(s8, s8b);
        assert_ne!(s8, s16);
        assert_eq!(m.bv_sort_width(s8), Some(8));
        assert_eq!(m.sort(s8).unwrap().num_elements, SortSize::finite(256));
    }

    #[test]
    fn numerals_wrap_modulo_width() {
        let mut m = AstManager::new();
        // 256 mod 2^8 = 0, so bv(256, 8) == bv(0, 8).
        let a = m.mk_bv(256, 8);
        let z = m.mk_bv(0, 8);
        assert_eq!(a, z);
        // 257 mod 256 = 1.
        let b = m.mk_bv(257, 8);
        let one = m.mk_bv(1, 8);
        assert_eq!(b, one);
    }

    #[test]
    fn build_bitvector_term() {
        let mut m = AstManager::new();
        let x = m.mk_bv_const("x", 8);
        let one = m.mk_bv(1, 8);
        let sum = m.mk_bvadd(x, one);
        assert_eq!(m.bv_sort_width(m.get_sort(sum)), Some(8));
        assert_eq!(m.pp(sum), "(bvadd x bv1)");
        let cmp = m.mk_bvult(x, sum);
        assert_eq!(m.get_sort(cmp), m.mk_bool_sort());
    }
}
