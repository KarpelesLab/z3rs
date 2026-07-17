//! Bit-vector constant folding — a subset of `bv_rewriter`
//! (`z3/src/ast/rewriter/bv_rewriter.{h,cpp}`, Z3 4.17.0, MIT).
//!
//! `try_fold` evaluates a bit-vector application whose operands are (partly)
//! numeral, using `puremp`'s exact integers with modular (`mod 2^width`)
//! semantics. It covers full constant folding of the arithmetic, bitwise,
//! shift, `concat`/`extract`/extend families and the unsigned/signed
//! comparisons, plus the cheap unconditional algebraic identities Z3 applies
//! (`x+0`, `x*0`, `x*1`, `x&0`, `x&x`, `x|allones`, `x^x`, `~~x`, `x-x`, …).
//!
//! Everything here mirrors a rule from `bv_rewriter.cpp`; the mapping is noted
//! at each site. `=` is intentionally *not* handled — bit-vector numeral
//! equality is already folded by [`crate::rewriter::bool_rewriter`]'s
//! `simplify_eq` (Z3's `mk_eq_core`).

use alloc::vec::Vec;

use puremp::Int;

use crate::ast::bv::BvOp;
use crate::ast::manager::AstManager;
use crate::ast::{AstId, DeclKind};
use crate::util::symbol::Symbol;

/// `2^w`.
fn pow2(w: u32) -> Int {
    Int::from(1).mul_2k(w)
}

/// `2^w - 1` (the all-ones value of a `w`-bit vector).
fn allones_int(w: u32) -> Int {
    pow2(w).sub(&Int::from(1))
}

/// Interpret the unsigned value `u` (in `[0, 2^w)`) as a `w`-bit signed integer.
/// Mirrors `bv_util::norm(v, w, /*signed=*/true)`.
fn to_signed(u: &Int, w: u32) -> Int {
    if u.bit(w - 1) {
        u.sub(&pow2(w))
    } else {
        u.clone()
    }
}

/// Map a bit-vector func-decl kind back to its [`BvOp`] (mirrors
/// [`AstManager::bv_op`], which needs an application id we do not have here).
fn bvop_of_kind(kind: DeclKind) -> Option<BvOp> {
    use BvOp::*;
    [
        Num, Neg, Add, Sub, Mul, Udiv, Urem, Uleq, Ult, BAnd, BOr, BNot, BXor, Sleq, Slt, Concat,
        SignExt, ZeroExt, Extract, Shl, Lshr, Ashr,
    ]
    .into_iter()
    .find(|op| *op as DeclKind == kind)
}

/// Try to fold a bit-vector application `decl(args)` with already-simplified
/// `args`. Returns `None` if `decl` is not a bit-vector op this rewriter
/// handles, or the operands are not concrete enough to fold.
pub(crate) fn try_fold(m: &mut AstManager, decl: AstId, args: &[AstId]) -> Option<AstId> {
    let bvfid = m.get_family_id(Symbol::new("bv"))?;
    let d = m.func_decl(decl).expect("app decl");
    if d.info.family_id != bvfid {
        return None;
    }
    let kind = d.info.decl_kind;
    // Extract/extend carry their bounds as decl parameters; clone before we take
    // a mutable borrow of `m` to build results.
    let params = d.info.parameters.clone();
    let op = bvop_of_kind(kind)?;
    if args.is_empty() {
        return None; // numerals and other nullary decls: nothing to fold.
    }
    // Width of the first operand's bit-vector sort (all handled ops take a bv
    // first operand).
    let w = m.bv_sort_width(m.get_sort(args[0]))?;

    // Concrete value of each operand, if it is a numeral.
    let nums: Vec<Option<Int>> = args.iter().map(|&a| m.bv_numeral_value(a)).collect();

    match op {
        // --- comparisons (mk_leq_core / mk_ule / mk_ult / mk_sle / mk_slt) ---
        BvOp::Uleq => cmp(m, &nums, |x, y| x <= y),
        BvOp::Ult => cmp(m, &nums, |x, y| x < y),
        BvOp::Sleq => scmp(m, &nums, w, |x, y| x <= y),
        BvOp::Slt => scmp(m, &nums, w, |x, y| x < y),

        // --- n-ary arithmetic / bitwise (mk_bv_add / mk_bv_mul / and / or / xor) ---
        BvOp::Add => Some(fold_add(m, args, w)),
        BvOp::Mul => Some(fold_mul(m, args, w)),
        BvOp::BAnd => Some(fold_and(m, args, w)),
        BvOp::BOr => Some(fold_or(m, args, w)),
        BvOp::BXor => Some(fold_xor(m, args, w)),

        // --- subtraction / negation / bitwise-not (mk_sub / mk_uminus / mk_bv_not) ---
        BvOp::Sub => fold_sub(m, args, &nums, w),
        BvOp::Neg => nums[0].as_ref().map(|v| m.mk_bv_numeral(v.neg(), w)),
        BvOp::BNot => fold_not(m, args, &nums, w),

        // --- shifts (mk_bv_shl / mk_bv_lshr / mk_bv_ashr) ---
        BvOp::Shl => fold_shl(m, args, &nums, w),
        BvOp::Lshr => fold_lshr(m, args, &nums, w),
        BvOp::Ashr => fold_ashr(m, args, &nums, w),

        // --- division / remainder (mk_bv_udiv_core / mk_bv_urem_core, hi_div0) ---
        BvOp::Udiv => fold_udiv(m, args, &nums, w),
        BvOp::Urem => fold_urem(m, args, &nums, w),

        // --- concat / extract / extend (mk_concat / mk_extract / *_extend) ---
        BvOp::Concat => fold_concat(m, args, &nums),
        BvOp::Extract => fold_extract(m, args, &nums, &params, w),
        BvOp::ZeroExt => fold_zero_extend(m, args, &nums, &params, w),
        BvOp::SignExt => fold_sign_extend(m, args, &nums, &params, w),

        BvOp::Num => None,
    }
}

fn bool_of(m: &mut AstManager, b: bool) -> AstId {
    if b { m.mk_true() } else { m.mk_false() }
}

/// Unsigned comparison of two numerals; `None` if either operand is symbolic.
fn cmp(m: &mut AstManager, nums: &[Option<Int>], f: impl Fn(&Int, &Int) -> bool) -> Option<AstId> {
    let (a, b) = (nums[0].as_ref()?, nums[1].as_ref()?);
    Some(bool_of(m, f(a, b)))
}

/// Signed comparison of two numerals (operands normalized to `w`-bit signed).
fn scmp(
    m: &mut AstManager,
    nums: &[Option<Int>],
    w: u32,
    f: impl Fn(&Int, &Int) -> bool,
) -> Option<AstId> {
    let (a, b) = (nums[0].as_ref()?, nums[1].as_ref()?);
    Some(bool_of(m, f(&to_signed(a, w), &to_signed(b, w))))
}

/// Left-fold `ops` (each same-width) with the binary constructor for `op`.
fn rebuild(m: &mut AstManager, op: BvOp, ops: &[AstId]) -> AstId {
    let mut acc = ops[0];
    for &o in &ops[1..] {
        acc = match op {
            BvOp::Add => m.mk_bvadd(acc, o),
            BvOp::Mul => m.mk_bvmul(acc, o),
            BvOp::BAnd => m.mk_bvand(acc, o),
            BvOp::BOr => m.mk_bvor(acc, o),
            BvOp::BXor => m.mk_bvxor(acc, o),
            _ => unreachable!("rebuild only used for add/mul/and/or/xor"),
        };
    }
    acc
}

/// `bvadd`: combine numeral summands, drop `0` (identity `x + 0 = x`).
fn fold_add(m: &mut AstManager, args: &[AstId], w: u32) -> AstId {
    let mut acc = Int::from(0);
    let mut syms: Vec<AstId> = Vec::new();
    for &a in args {
        match m.bv_numeral_value(a) {
            Some(v) => acc = acc.add(&v),
            None => syms.push(a),
        }
    }
    let c = acc.mod_2k(w);
    let mut ops = syms;
    if !c.is_zero() || ops.is_empty() {
        let n = m.mk_bv_numeral(c, w);
        ops.push(n);
    }
    rebuild(m, BvOp::Add, &ops)
}

/// `bvmul`: combine numeral factors; `x * 0 = 0`, drop `1` (`x * 1 = x`).
fn fold_mul(m: &mut AstManager, args: &[AstId], w: u32) -> AstId {
    let mut acc = Int::from(1);
    let mut syms: Vec<AstId> = Vec::new();
    for &a in args {
        match m.bv_numeral_value(a) {
            Some(v) => acc = acc.mul(&v),
            None => syms.push(a),
        }
    }
    let c = acc.mod_2k(w);
    if c.is_zero() {
        return m.mk_bv_numeral(Int::from(0), w); // annihilator
    }
    let mut ops = syms;
    if !c.is_one() || ops.is_empty() {
        let n = m.mk_bv_numeral(c, w);
        ops.push(n);
    }
    rebuild(m, BvOp::Mul, &ops)
}

/// `bvand`: `x & 0 = 0`, `x & allones = x`, `x & x = x`, constant fold.
fn fold_and(m: &mut AstManager, args: &[AstId], w: u32) -> AstId {
    let mut accn: Option<Int> = None;
    let mut syms: Vec<AstId> = Vec::new();
    for &a in args {
        match m.bv_numeral_value(a) {
            Some(v) => accn = Some(accn.map_or(v.clone(), |c| c.bitand(&v))),
            None => {
                if !syms.contains(&a) {
                    syms.push(a); // idempotent: x & x = x
                }
            }
        }
    }
    if let Some(c) = &accn
        && c.is_zero()
    {
        return m.mk_bv_numeral(Int::from(0), w); // annihilator
    }
    let allones = allones_int(w);
    let mut ops = syms;
    if let Some(c) = accn
        && c != allones
    {
        // allones is the identity for &; drop it. Any other constant stays.
        let n = m.mk_bv_numeral(c, w);
        ops.push(n);
    }
    if ops.is_empty() {
        return m.mk_bv_numeral(allones, w); // all operands were allones
    }
    rebuild(m, BvOp::BAnd, &ops)
}

/// `bvor`: `x | allones = allones`, `x | 0 = x`, `x | x = x`, constant fold.
fn fold_or(m: &mut AstManager, args: &[AstId], w: u32) -> AstId {
    let mut accn: Option<Int> = None;
    let mut syms: Vec<AstId> = Vec::new();
    for &a in args {
        match m.bv_numeral_value(a) {
            Some(v) => accn = Some(accn.map_or(v.clone(), |c| c.bitor(&v))),
            None => {
                if !syms.contains(&a) {
                    syms.push(a); // idempotent: x | x = x
                }
            }
        }
    }
    let allones = allones_int(w);
    if let Some(c) = &accn
        && *c == allones
    {
        return m.mk_bv_numeral(allones, w); // annihilator
    }
    let mut ops = syms;
    if let Some(c) = accn
        && !c.is_zero()
    {
        // 0 is the identity for |; drop it. Any other constant stays.
        let n = m.mk_bv_numeral(c, w);
        ops.push(n);
    }
    if ops.is_empty() {
        return m.mk_bv_numeral(Int::from(0), w); // all operands were 0
    }
    rebuild(m, BvOp::BOr, &ops)
}

/// `bvxor`: `x ^ 0 = x`, `x ^ x = 0` (pairwise cancellation), constant fold.
fn fold_xor(m: &mut AstManager, args: &[AstId], w: u32) -> AstId {
    let mut acc = Int::from(0);
    let mut syms: Vec<AstId> = Vec::new();
    for &a in args {
        match m.bv_numeral_value(a) {
            Some(v) => acc = acc.bitxor(&v),
            None => {
                // xor is its own inverse: an operand appearing twice cancels.
                if let Some(pos) = syms.iter().position(|&s| s == a) {
                    syms.remove(pos);
                } else {
                    syms.push(a);
                }
            }
        }
    }
    let c = acc.mod_2k(w);
    let mut ops = syms;
    if !c.is_zero() || ops.is_empty() {
        let n = m.mk_bv_numeral(c, w);
        ops.push(n);
    }
    rebuild(m, BvOp::BXor, &ops)
}

/// `bvsub`: full numeral fold, `x - x = 0`, `x - 0 = x` (`mk_sub`).
fn fold_sub(m: &mut AstManager, args: &[AstId], nums: &[Option<Int>], w: u32) -> Option<AstId> {
    if nums.iter().all(|n| n.is_some()) {
        let mut acc = nums[0].clone().unwrap();
        for n in &nums[1..] {
            acc = acc.sub(n.as_ref().unwrap());
        }
        return Some(m.mk_bv_numeral(acc.mod_2k(w), w));
    }
    if args.len() == 2 {
        if args[0] == args[1] {
            return Some(m.mk_bv_numeral(Int::from(0), w)); // x - x = 0
        }
        if nums[1].as_ref().is_some_and(|v| v.is_zero()) {
            return Some(args[0]); // x - 0 = x
        }
    }
    None
}

/// `bvnot`: `~~x = x`, constant fold (`mk_bv_not`).
fn fold_not(m: &mut AstManager, args: &[AstId], nums: &[Option<Int>], w: u32) -> Option<AstId> {
    if m.bv_op(args[0]) == Some(BvOp::BNot) {
        return Some(m.app_args(args[0])[0]); // ~(~x) = x
    }
    let v = nums[0].as_ref()?;
    Some(m.mk_bv_numeral(allones_int(w).sub(v), w)) // ~v = allones - v
}

/// `bvshl` (`mk_bv_shl`): `x << 0 = x`; `x << k = 0` when `k >= w`; constant fold.
fn fold_shl(m: &mut AstManager, args: &[AstId], nums: &[Option<Int>], w: u32) -> Option<AstId> {
    let r2 = nums[1].as_ref()?;
    if r2.is_zero() {
        return Some(args[0]);
    }
    if *r2 >= Int::from(w as i64) {
        return Some(m.mk_bv_numeral(Int::from(0), w));
    }
    let r1 = nums[0].as_ref()?;
    let s = r2.to_u64()? as u32;
    Some(m.mk_bv_numeral(r1.mul_2k(s).mod_2k(w), w))
}

/// `bvlshr` (`mk_bv_lshr`): `x >> 0 = x`; `x >> k = 0` when `k >= w`; constant fold.
fn fold_lshr(m: &mut AstManager, args: &[AstId], nums: &[Option<Int>], w: u32) -> Option<AstId> {
    let r2 = nums[1].as_ref()?;
    if r2.is_zero() {
        return Some(args[0]);
    }
    if *r2 >= Int::from(w as i64) {
        return Some(m.mk_bv_numeral(Int::from(0), w));
    }
    let r1 = nums[0].as_ref()?;
    let s = r2.to_u64()? as u32;
    Some(m.mk_bv_numeral(r1.div_2k_trunc(s), w)) // r1 < 2^w, so already in range
}

/// `bvashr` (`mk_bv_ashr`): `x >> 0 = x`; sign-filling constant fold.
fn fold_ashr(m: &mut AstManager, args: &[AstId], nums: &[Option<Int>], w: u32) -> Option<AstId> {
    let r2 = nums[1].as_ref()?;
    if r2.is_zero() {
        return Some(args[0]);
    }
    let r1 = nums[0].as_ref()?;
    let sign = r1.bit(w - 1);
    if *r2 >= Int::from(w as i64) {
        // shift out everything: replicate the sign bit across the width.
        let v = if sign { allones_int(w) } else { Int::from(0) };
        return Some(m.mk_bv_numeral(v, w));
    }
    let s = r2.to_u64()? as u32;
    let shifted = r1.div_2k_trunc(s);
    let v = if sign {
        // fill the top s bits with ones: mask = 2^w - 2^(w-s).
        let mask = pow2(w).sub(&pow2(w - s));
        shifted.bitor(&mask)
    } else {
        shifted
    };
    Some(m.mk_bv_numeral(v, w))
}

/// `bvudiv` (`mk_bv_udiv_core`, `hi_div0=true`): `x / 0 = allones` (hardware
/// interpretation), `x / 1 = x`, and full numeral fold (truncating division).
fn fold_udiv(m: &mut AstManager, args: &[AstId], nums: &[Option<Int>], w: u32) -> Option<AstId> {
    let r2 = nums[1].as_ref()?;
    if r2.is_zero() {
        return Some(m.mk_bv_numeral(allones_int(w), w));
    }
    if r2.is_one() {
        return Some(args[0]);
    }
    let r1 = nums[0].as_ref()?;
    Some(m.mk_bv_numeral(r1.div_trunc(r2), w)) // both non-negative: == machine_div
}

/// `bvurem` (`mk_bv_urem_core`, `hi_div0=true`): `x % 0 = x` (hardware
/// interpretation), `x % 1 = 0`, and full numeral fold.
fn fold_urem(m: &mut AstManager, args: &[AstId], nums: &[Option<Int>], w: u32) -> Option<AstId> {
    let r2 = nums[1].as_ref()?;
    if r2.is_zero() {
        return Some(args[0]);
    }
    if r2.is_one() {
        return Some(m.mk_bv_numeral(Int::from(0), w));
    }
    let r1 = nums[0].as_ref()?;
    Some(m.mk_bv_numeral(r1.rem_trunc(r2), w)) // both non-negative
}

/// `concat` of two numerals (`mk_concat`): high operand shifted above the low.
fn fold_concat(m: &mut AstManager, args: &[AstId], nums: &[Option<Int>]) -> Option<AstId> {
    let (hi, lo) = (nums[0].as_ref()?, nums[1].as_ref()?);
    let wb = m.bv_sort_width(m.get_sort(args[1]))?;
    let wa = m.bv_sort_width(m.get_sort(args[0]))?;
    let v = hi.mul_2k(wb).add(lo); // lo < 2^wb, so this is (hi << wb) | lo
    Some(m.mk_bv_numeral(v, wa + wb))
}

/// `(_ extract high low)` (`mk_extract`): whole-vector identity and numeral fold.
fn fold_extract(
    m: &mut AstManager,
    args: &[AstId],
    nums: &[Option<Int>],
    params: &[crate::ast::parameter::Parameter],
    w: u32,
) -> Option<AstId> {
    let high = params.first()?.get_int()? as u32;
    let low = params.get(1)?.get_int()? as u32;
    if low == 0 && high == w - 1 {
        return Some(args[0]); // extract of the whole vector
    }
    let v = nums[0].as_ref()?;
    let newsz = high - low + 1;
    Some(m.mk_bv_numeral(v.div_2k_trunc(low).mod_2k(newsz), newsz))
}

/// `(_ zero_extend k)` (`mk_zero_extend`): `k = 0` identity and numeral fold
/// (value is unchanged, only the width grows).
fn fold_zero_extend(
    m: &mut AstManager,
    args: &[AstId],
    nums: &[Option<Int>],
    params: &[crate::ast::parameter::Parameter],
    w: u32,
) -> Option<AstId> {
    let k = params.first()?.get_int()? as u32;
    if k == 0 {
        return Some(args[0]);
    }
    let v = nums[0].as_ref()?;
    Some(m.mk_bv_numeral(v.clone(), w + k))
}

/// `(_ sign_extend k)` (`mk_sign_extend`): `k = 0` identity and numeral fold
/// (sign-normalize, then reduce to the wider width).
fn fold_sign_extend(
    m: &mut AstManager,
    args: &[AstId],
    nums: &[Option<Int>],
    params: &[crate::ast::parameter::Parameter],
    w: u32,
) -> Option<AstId> {
    let k = params.first()?.get_int()? as u32;
    if k == 0 {
        return Some(args[0]);
    }
    let v = nums[0].as_ref()?;
    // norm to signed, then mk_bv_numeral reduces mod 2^(w+k) (Euclidean).
    Some(m.mk_bv_numeral(to_signed(v, w), w + k))
}

#[cfg(test)]
mod tests {
    use crate::ast::manager::AstManager;
    use crate::rewriter::simplify;

    fn bv(m: &mut AstManager, v: i64, w: u32) -> crate::ast::AstId {
        m.mk_bv(v, w)
    }

    #[test]
    fn folds_arithmetic_constants() {
        let mut m = AstManager::new();
        // (bvadd #x07 #x0a) = #x11 (8-bit): 7 + 10 = 17
        let a = bv(&mut m, 7, 8);
        let b = bv(&mut m, 10, 8);
        let add = m.mk_bvadd(a, b);
        let exp = bv(&mut m, 17, 8);
        assert_eq!(simplify(&mut m, add), exp);

        // (bvmul 200 3) mod 256 = 600 mod 256 = 88
        let a = bv(&mut m, 200, 8);
        let b = bv(&mut m, 3, 8);
        let mul = m.mk_bvmul(a, b);
        let exp = bv(&mut m, 88, 8);
        assert_eq!(simplify(&mut m, mul), exp);

        // (bvsub 3 10) mod 256 = 249
        let a = bv(&mut m, 3, 8);
        let b = bv(&mut m, 10, 8);
        let sub = m.mk_bvsub(a, b);
        let exp = bv(&mut m, 249, 8);
        assert_eq!(simplify(&mut m, sub), exp);

        // (bvneg 1) = 255
        let a = bv(&mut m, 1, 8);
        let neg = m.mk_bvneg(a);
        let exp = bv(&mut m, 255, 8);
        assert_eq!(simplify(&mut m, neg), exp);
    }

    #[test]
    fn folds_bitwise_constants() {
        let mut m = AstManager::new();
        let a = bv(&mut m, 0b1100, 8);
        let b = bv(&mut m, 0b1010, 8);
        let and = m.mk_bvand(a, b);
        assert_eq!(simplify(&mut m, and), bv(&mut m, 0b1000, 8));
        let or = m.mk_bvor(a, b);
        assert_eq!(simplify(&mut m, or), bv(&mut m, 0b1110, 8));
        let xor = m.mk_bvxor(a, b);
        assert_eq!(simplify(&mut m, xor), bv(&mut m, 0b0110, 8));
        let not = m.mk_bvnot(a);
        assert_eq!(simplify(&mut m, not), bv(&mut m, 0xF3, 8));
    }

    #[test]
    fn folds_shifts_constants() {
        let mut m = AstManager::new();
        // 1 << 3 = 8
        let a = bv(&mut m, 1, 8);
        let s = bv(&mut m, 3, 8);
        let shl = m.mk_bvshl(a, s);
        assert_eq!(simplify(&mut m, shl), bv(&mut m, 8, 8));
        // 0x80 >> 3 (logical) = 0x10
        let a = bv(&mut m, 0x80, 8);
        let s = bv(&mut m, 3, 8);
        let lshr = m.mk_bvlshr(a, s);
        assert_eq!(simplify(&mut m, lshr), bv(&mut m, 0x10, 8));
        // 0x80 >> 3 (arithmetic) = 0xF0
        let a = bv(&mut m, 0x80, 8);
        let s = bv(&mut m, 3, 8);
        let ashr = m.mk_bvashr(a, s);
        assert_eq!(simplify(&mut m, ashr), bv(&mut m, 0xF0, 8));
        // shift by >= width: logical -> 0, arithmetic of negative -> allones
        let a = bv(&mut m, 0x81, 8);
        let s = bv(&mut m, 8, 8);
        let lshr = m.mk_bvlshr(a, s);
        assert_eq!(simplify(&mut m, lshr), bv(&mut m, 0, 8));
        let a = bv(&mut m, 0x81, 8);
        let s = bv(&mut m, 8, 8);
        let ashr = m.mk_bvashr(a, s);
        assert_eq!(simplify(&mut m, ashr), bv(&mut m, 0xFF, 8));
    }

    #[test]
    fn folds_concat_extract_extend() {
        let mut m = AstManager::new();
        // concat(#xAB[8], #xCD[8]) = #xABCD[16]
        let a = bv(&mut m, 0xAB, 8);
        let b = bv(&mut m, 0xCD, 8);
        let c = m.mk_bv_concat(a, b);
        assert_eq!(simplify(&mut m, c), bv(&mut m, 0xABCD, 16));
        // extract[7:4] of #x_ABCD -> 0xC ... use extract[11:8] of 0xABCD = 0xB
        let x = bv(&mut m, 0xABCD, 16);
        let e = m.mk_bv_extract(11, 8, x);
        assert_eq!(simplify(&mut m, e), bv(&mut m, 0xB, 4));
        // zero_extend 8 of 0xFF[8] = 0x00FF[16]
        let x = bv(&mut m, 0xFF, 8);
        let z = m.mk_bv_zero_extend(8, x);
        assert_eq!(simplify(&mut m, z), bv(&mut m, 0x00FF, 16));
        // sign_extend 8 of 0x80[8] = 0xFF80[16]
        let x = bv(&mut m, 0x80, 8);
        let s = m.mk_bv_sign_extend(8, x);
        assert_eq!(simplify(&mut m, s), bv(&mut m, 0xFF80, 16));
    }

    #[test]
    fn folds_comparisons() {
        let mut m = AstManager::new();
        let t = m.mk_true();
        let f = m.mk_false();
        // unsigned: 0x80 > 0x7F ; signed: 0x80 (-128) < 0x7F (127)
        let a = bv(&mut m, 0x80, 8);
        let b = bv(&mut m, 0x7F, 8);
        let ule = m.mk_bvule(a, b);
        assert_eq!(simplify(&mut m, ule), f); // 128 <= 127 false
        let sle = m.mk_bvsle(a, b);
        assert_eq!(simplify(&mut m, sle), t); // -128 <= 127 true
        let ult = m.mk_bvult(b, a);
        assert_eq!(simplify(&mut m, ult), t); // 127 < 128 true
        let slt = m.mk_bvslt(a, b);
        assert_eq!(simplify(&mut m, slt), t); // -128 < 127 true
    }

    #[test]
    fn folds_div_rem_including_zero_divisor() {
        let mut m = AstManager::new();
        // 17 / 5 = 3, 17 % 5 = 2
        let a = bv(&mut m, 17, 8);
        let b = bv(&mut m, 5, 8);
        let d = m.mk_bvudiv(a, b);
        assert_eq!(simplify(&mut m, d), bv(&mut m, 3, 8));
        let r = m.mk_bvurem(a, b);
        assert_eq!(simplify(&mut m, r), bv(&mut m, 2, 8));
        // division/remainder by zero: hardware interpretation.
        let a = bv(&mut m, 42, 8);
        let z = bv(&mut m, 0, 8);
        let d0 = m.mk_bvudiv(a, z);
        assert_eq!(simplify(&mut m, d0), bv(&mut m, 0xFF, 8)); // x / 0 = allones
        let r0 = m.mk_bvurem(a, z);
        assert_eq!(simplify(&mut m, r0), bv(&mut m, 42, 8)); // x % 0 = x
    }

    #[test]
    fn applies_algebraic_identities() {
        let mut m = AstManager::new();
        let x = m.mk_bv_const("x", 8);
        let zero = bv(&mut m, 0, 8);
        let one = bv(&mut m, 1, 8);
        let allones = bv(&mut m, 0xFF, 8);

        // x + 0 = x
        let t = m.mk_bvadd(x, zero);
        assert_eq!(simplify(&mut m, t), x);
        // x * 0 = 0 ; x * 1 = x
        let t = m.mk_bvmul(x, zero);
        assert_eq!(simplify(&mut m, t), zero);
        let t = m.mk_bvmul(x, one);
        assert_eq!(simplify(&mut m, t), x);
        // x & 0 = 0 ; x & allones = x ; x & x = x
        let t = m.mk_bvand(x, zero);
        assert_eq!(simplify(&mut m, t), zero);
        let t = m.mk_bvand(x, allones);
        assert_eq!(simplify(&mut m, t), x);
        let t = m.mk_bvand(x, x);
        assert_eq!(simplify(&mut m, t), x);
        // x | 0 = x ; x | allones = allones ; x | x = x
        let t = m.mk_bvor(x, zero);
        assert_eq!(simplify(&mut m, t), x);
        let t = m.mk_bvor(x, allones);
        assert_eq!(simplify(&mut m, t), allones);
        let t = m.mk_bvor(x, x);
        assert_eq!(simplify(&mut m, t), x);
        // x ^ 0 = x ; x ^ x = 0
        let t = m.mk_bvxor(x, zero);
        assert_eq!(simplify(&mut m, t), x);
        let t = m.mk_bvxor(x, x);
        assert_eq!(simplify(&mut m, t), zero);
        // ~~x = x ; x - x = 0 ; x - 0 = x
        let t = {
            let nx = m.mk_bvnot(x);
            m.mk_bvnot(nx)
        };
        assert_eq!(simplify(&mut m, t), x);
        let t = m.mk_bvsub(x, x);
        assert_eq!(simplify(&mut m, t), zero);
        let t = m.mk_bvsub(x, zero);
        assert_eq!(simplify(&mut m, t), x);
        // x << 0 = x ; x udiv 1 = x ; x urem 1 = 0
        let t = m.mk_bvshl(x, zero);
        assert_eq!(simplify(&mut m, t), x);
        let t = m.mk_bvudiv(x, one);
        assert_eq!(simplify(&mut m, t), x);
        let t = m.mk_bvurem(x, one);
        assert_eq!(simplify(&mut m, t), zero);
    }

    #[test]
    fn leaves_symbolic_bv_alone() {
        let mut m = AstManager::new();
        let x = m.mk_bv_const("x", 8);
        let y = m.mk_bv_const("y", 8);
        let t = m.mk_bvadd(x, y);
        assert_eq!(simplify(&mut m, t), t);
        let t = m.mk_bvudiv(x, y);
        assert_eq!(simplify(&mut m, t), t);
    }
}
