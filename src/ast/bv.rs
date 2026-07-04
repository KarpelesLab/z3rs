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
    /// `bvsle` (signed `<=`)
    Sleq = 23,
    /// `bvult`
    Ult = 26,
    /// `bvslt` (signed `<`)
    Slt = 27,
    /// `bvand` (bitwise AND)
    BAnd = 30,
    /// `bvor` (bitwise OR)
    BOr = 31,
    /// `bvnot` (bitwise NOT)
    BNot = 32,
    /// `bvxor` (bitwise XOR)
    BXor = 33,
    /// `concat`
    Concat = 37,
    /// `(_ sign_extend k)`
    SignExt = 38,
    /// `(_ zero_extend k)`
    ZeroExt = 39,
    /// `(_ extract i j)`
    Extract = 40,
    /// `bvshl` (shift left)
    Shl = 45,
    /// `bvlshr` (logical shift right)
    Lshr = 46,
    /// `bvashr` (arithmetic shift right)
    Ashr = 47,
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

    /// `(bvand a b)` — bitwise AND.
    pub fn mk_bvand(&mut self, a: AstId, b: AstId) -> AstId {
        let flags = FuncDeclFlags {
            commutative: true,
            ..FuncDeclFlags::default()
        };
        self.mk_bv_binop("bvand", BvOp::BAnd, flags, a, b)
    }

    /// `(bvor a b)` — bitwise OR.
    pub fn mk_bvor(&mut self, a: AstId, b: AstId) -> AstId {
        let flags = FuncDeclFlags {
            commutative: true,
            ..FuncDeclFlags::default()
        };
        self.mk_bv_binop("bvor", BvOp::BOr, flags, a, b)
    }

    /// `(bvxor a b)` — bitwise XOR.
    pub fn mk_bvxor(&mut self, a: AstId, b: AstId) -> AstId {
        let flags = FuncDeclFlags {
            commutative: true,
            ..FuncDeclFlags::default()
        };
        self.mk_bv_binop("bvxor", BvOp::BXor, flags, a, b)
    }

    /// `(concat a b)` — `a` in the high bits, `b` in the low bits; the result
    /// width is the sum of the operand widths.
    pub fn mk_bv_concat(&mut self, a: AstId, b: AstId) -> AstId {
        let wa = self
            .bv_sort_width(self.get_sort(a))
            .expect("concat: a not bv");
        let wb = self
            .bv_sort_width(self.get_sort(b))
            .expect("concat: b not bv");
        let sa = self.get_sort(a);
        let sb = self.get_sort(b);
        let range = self.mk_bv_sort(wa + wb);
        self.mk_bv_app(
            "concat",
            BvOp::Concat,
            &[sa, sb],
            range,
            FuncDeclFlags::default(),
            &[a, b],
        )
    }

    /// `((_ extract high low) x)` — bits `[low, high]` of `x` (inclusive), a
    /// bit-vector of width `high - low + 1`.
    pub fn mk_bv_extract(&mut self, high: u32, low: u32, x: AstId) -> AstId {
        assert!(high >= low, "extract: high < low");
        let sx = self.get_sort(x);
        let range = self.mk_bv_sort(high - low + 1);
        let fid = self.bv_fid();
        let info = DeclInfo::new(
            fid,
            BvOp::Extract as DeclKind,
            vec![Parameter::Int(high as i32), Parameter::Int(low as i32)],
        );
        let decl = self.mk_func_decl_full(
            Symbol::new("extract"),
            &[sx],
            range,
            info,
            FuncDeclFlags::default(),
        );
        self.mk_app(decl, &[x])
    }

    /// `((_ zero_extend k) x)` — widen `x` by `k` zero bits (unsigned).
    pub fn mk_bv_zero_extend(&mut self, k: u32, x: AstId) -> AstId {
        self.mk_bv_extend("zero_extend", BvOp::ZeroExt, k, x)
    }

    /// `((_ sign_extend k) x)` — widen `x` by `k` copies of its sign bit.
    pub fn mk_bv_sign_extend(&mut self, k: u32, x: AstId) -> AstId {
        self.mk_bv_extend("sign_extend", BvOp::SignExt, k, x)
    }

    fn mk_bv_extend(&mut self, name: &str, op: BvOp, k: u32, x: AstId) -> AstId {
        let w = self
            .bv_sort_width(self.get_sort(x))
            .expect("extend: not bv");
        let sx = self.get_sort(x);
        let range = self.mk_bv_sort(w + k);
        let fid = self.bv_fid();
        let info = DeclInfo::new(fid, op as DeclKind, vec![Parameter::Int(k as i32)]);
        let decl = self.mk_func_decl_full(
            Symbol::new(name),
            &[sx],
            range,
            info,
            FuncDeclFlags::default(),
        );
        self.mk_app(decl, &[x])
    }

    /// `(bvnot a)` — bitwise NOT.
    pub fn mk_bvnot(&mut self, a: AstId) -> AstId {
        let sort = self.get_sort(a);
        self.mk_bv_app(
            "bvnot",
            BvOp::BNot,
            &[sort],
            sort,
            FuncDeclFlags::default(),
            &[a],
        )
    }

    /// `(bvshl a b)` — shift `a` left by `b` bits.
    pub fn mk_bvshl(&mut self, a: AstId, b: AstId) -> AstId {
        self.mk_bv_binop("bvshl", BvOp::Shl, FuncDeclFlags::default(), a, b)
    }

    /// `(bvlshr a b)` — logical (zero-filling) shift `a` right by `b` bits.
    pub fn mk_bvlshr(&mut self, a: AstId, b: AstId) -> AstId {
        self.mk_bv_binop("bvlshr", BvOp::Lshr, FuncDeclFlags::default(), a, b)
    }

    /// `(bvashr a b)` — arithmetic (sign-filling) shift `a` right by `b` bits.
    pub fn mk_bvashr(&mut self, a: AstId, b: AstId) -> AstId {
        self.mk_bv_binop("bvashr", BvOp::Ashr, FuncDeclFlags::default(), a, b)
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

    /// `(bvslt a b)` — signed `<`.
    pub fn mk_bvslt(&mut self, a: AstId, b: AstId) -> AstId {
        self.mk_bv_cmp("bvslt", BvOp::Slt, a, b)
    }

    /// `(bvsle a b)` — signed `<=`.
    pub fn mk_bvsle(&mut self, a: AstId, b: AstId) -> AstId {
        self.mk_bv_cmp("bvsle", BvOp::Sleq, a, b)
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

    /// The value of a bit-vector numeral `id` (in `[0, 2^width)`), if it is one.
    pub fn bv_numeral_value(&self, id: AstId) -> Option<Int> {
        let bvfid = self.get_family_id(Symbol::new("bv"))?;
        let a = self.app(id)?;
        if !a.args.is_empty() {
            return None;
        }
        let d = self.func_decl(a.decl)?;
        if d.info.family_id == bvfid && d.info.decl_kind == BvOp::Num as DeclKind {
            d.info
                .parameters
                .first()?
                .get_rational()
                .map(|r| r.numerator().clone())
        } else {
            None
        }
    }

    /// If `id` applies a bit-vector-family declaration, its op kind.
    pub fn bv_op(&self, id: AstId) -> Option<BvOp> {
        let bvfid = self.get_family_id(Symbol::new("bv"))?;
        let a = self.app(id)?;
        let d = self.func_decl(a.decl)?;
        if d.info.family_id != bvfid {
            return None;
        }
        let k = d.info.decl_kind;
        [
            BvOp::Num,
            BvOp::Neg,
            BvOp::Add,
            BvOp::Sub,
            BvOp::Mul,
            BvOp::Uleq,
            BvOp::Ult,
            BvOp::BAnd,
            BvOp::BOr,
            BvOp::BNot,
            BvOp::BXor,
            BvOp::Sleq,
            BvOp::Slt,
            BvOp::Concat,
            BvOp::SignExt,
            BvOp::ZeroExt,
            BvOp::Extract,
            BvOp::Shl,
            BvOp::Lshr,
            BvOp::Ashr,
        ]
        .into_iter()
        .find(|op| *op as DeclKind == k)
    }

    /// The `(high, low)` indices of an `(_ extract high low)` application.
    pub fn bv_extract_params(&self, id: AstId) -> Option<(u32, u32)> {
        if self.bv_op(id)? != BvOp::Extract {
            return None;
        }
        let d = self.func_decl(self.app(id)?.decl)?;
        let high = d.info.parameters.first()?.get_int()? as u32;
        let low = d.info.parameters.get(1)?.get_int()? as u32;
        Some((high, low))
    }

    /// The extension amount `k` of a `zero_extend` / `sign_extend` application.
    pub fn bv_extend_amount(&self, id: AstId) -> Option<u32> {
        match self.bv_op(id)? {
            BvOp::ZeroExt | BvOp::SignExt => {
                let d = self.func_decl(self.app(id)?.decl)?;
                Some(d.info.parameters.first()?.get_int()? as u32)
            }
            _ => None,
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
    fn bitwise_ops_shapes() {
        let mut m = AstManager::new();
        let x = m.mk_bv_const("x", 8);
        let y = m.mk_bv_const("y", 8);
        let s8 = m.mk_bv_sort(8);
        let and = m.mk_bvand(x, y);
        let or = m.mk_bvor(x, y);
        let xor = m.mk_bvxor(x, y);
        let not = m.mk_bvnot(x);
        for t in [and, or, xor, not] {
            assert_eq!(m.get_sort(t), s8);
        }
        assert_eq!(m.bv_op(and), Some(BvOp::BAnd));
        assert_eq!(m.bv_op(or), Some(BvOp::BOr));
        assert_eq!(m.bv_op(xor), Some(BvOp::BXor));
        assert_eq!(m.bv_op(not), Some(BvOp::BNot));
        assert_eq!(m.bv_op(x), None);
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
