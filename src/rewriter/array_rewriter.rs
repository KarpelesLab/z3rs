//! Array constant folding — a sound subset of `array_rewriter`
//! (`z3/src/ast/rewriter/array_rewriter.{h,cpp}`, Z3 4.17.0, MIT).
//!
//! `try_fold` rewrites `select`/`store` applications using the syntactic
//! identities Z3 applies in `mk_select_core` / `mk_store_core`, restricted to
//! the cases whose precondition can be established locally (indices equal iff
//! they are the same node, distinct iff they are two concrete numerals with
//! different values). Anything needing the model, `are_distinct`, maps,
//! `as-array`, lambdas or extensionality is intentionally left to `None`.
//!
//! Every rule mirrors a branch of `array_rewriter.cpp`; the mapping is noted at
//! each site.

use crate::ast::array::ArrayOp;
use crate::ast::manager::AstManager;
use crate::ast::{AstId, DeclKind};
use crate::util::symbol::Symbol;

/// Map an array func-decl kind back to its [`ArrayOp`].
fn arrayop_of_kind(kind: DeclKind) -> Option<ArrayOp> {
    [ArrayOp::Store, ArrayOp::Select, ArrayOp::Const]
        .into_iter()
        .find(|op| *op as DeclKind == kind)
}

/// Are indices `i` and `j` *provably distinct*? Only two concrete numerals with
/// different values count (Int/Real numerals, or bit-vector numerals). Mirrors
/// the `l_false` result of `array_rewriter::compare_args` (which uses
/// `are_distinct`), narrowed to the facts we can establish syntactically.
fn provably_distinct(m: &AstManager, i: AstId, j: AstId) -> bool {
    if i == j {
        return false;
    }
    if let (Some(a), Some(b)) = (m.as_numeral(i), m.as_numeral(j)) {
        return a != b;
    }
    if let (Some(a), Some(b)) = (m.bv_numeral_value(i), m.bv_numeral_value(j)) {
        return a != b;
    }
    false
}

/// Try to fold an array application `decl(args)` with already-simplified `args`.
/// Returns `None` if `decl` is not an array op this rewriter handles, or the
/// operands are not concrete enough to fold.
pub(crate) fn try_fold(m: &mut AstManager, decl: AstId, args: &[AstId]) -> Option<AstId> {
    let afid = m.get_family_id(Symbol::new("array"))?;
    let d = m.func_decl(decl).expect("app decl");
    if d.info.family_id != afid {
        return None;
    }
    let op = arrayop_of_kind(d.info.decl_kind)?;
    match op {
        ArrayOp::Select => mk_select_core(m, args),
        ArrayOp::Store => mk_store_core(m, args),
        ArrayOp::Const => None,
    }
}

/// `(select a j)` — subset of `array_rewriter::mk_select_core` /
/// `mk_select_same_store`. `args = [a, j]`.
fn mk_select_core(m: &mut AstManager, args: &[AstId]) -> Option<AstId> {
    let array = args[0];
    let j = args[1];

    // select(const(v), j) --> v   (mk_select_core, is_const branch handled via
    // the const-array read: every index maps to v).
    if m.is_const_array(array) {
        return Some(m.app_args(array)[0]);
    }

    if m.is_store(array) {
        let sa = m.app_args(array);
        let (a, i, v) = (sa[0], sa[1], sa[2]);
        // select(store(a, I, v), I) --> v      (mk_select_same_store, l_true)
        if i == j {
            return Some(v);
        }
        // select(store(a, I, v), J) --> select(a, J) if I != J  (mk_select_core,
        // l_false). Build via mk_select so the next fold pass re-enters (a may
        // itself be a store).
        if provably_distinct(m, i, j) {
            return Some(m.mk_select(a, j));
        }
    }
    None
}

/// `(store a i v)` — subset of `array_rewriter::mk_store_core`.
/// `args = [a, i, v]`.
fn mk_store_core(m: &mut AstManager, args: &[AstId]) -> Option<AstId> {
    let (array, i, v) = (args[0], args[1], args[2]);

    // store(store(a, i, w), i, v) --> store(a, i, v)   (mk_store_core, l_true)
    if m.is_store(array) {
        let inner = m.app_args(array);
        let (a, j) = (inner[0], inner[1]);
        if i == j {
            return Some(m.mk_store(a, i, v));
        }
    }

    // store(const(v), i, v) --> const(v)   (mk_store_core, is_const branch)
    if m.is_const_array(array) && m.app_args(array)[0] == v {
        return Some(array);
    }

    // store(a, i, select(a, i)) --> a   (mk_store_core, is_select(v) branch,
    // compare_args l_true: same array node and same index node).
    if m.is_select(v) {
        let sel = m.app_args(v);
        if sel[0] == array && sel[1] == i {
            return Some(array);
        }
    }

    None
}

#[cfg(test)]
mod tests {
    use crate::ast::AstId;
    use crate::ast::manager::AstManager;
    use crate::rewriter::simplify;
    use crate::util::symbol::Symbol;

    /// A fresh array constant of sort `(Array Int Int)`.
    fn int_array(m: &mut AstManager, name: &str) -> AstId {
        let int = m.mk_int_sort();
        let arr_sort = m.mk_array_sort(int, int);
        let d = m.mk_func_decl(Symbol::new(name), &[], arr_sort);
        m.mk_const(d)
    }

    #[test]
    fn select_store_same_index() {
        let mut m = AstManager::new();
        let a = int_array(&mut m, "a");
        let i = m.mk_int(1);
        let v = m.mk_int(7);
        let st = m.mk_store(a, i, v);
        // (select (store a 1 7) 1) = 7
        let sel = m.mk_select(st, i);
        assert_eq!(simplify(&mut m, sel), v);
    }

    #[test]
    fn select_store_distinct_index() {
        let mut m = AstManager::new();
        let a = int_array(&mut m, "a");
        let i = m.mk_int(1);
        let j = m.mk_int(2);
        let v = m.mk_int(7);
        let st = m.mk_store(a, i, v);
        // (select (store a 1 7) 2) = (select a 2)
        let sel = m.mk_select(st, j);
        let expected = m.mk_select(a, j);
        assert_eq!(simplify(&mut m, sel), expected);
    }

    #[test]
    fn select_const_array() {
        let mut m = AstManager::new();
        let int = m.mk_int_sort();
        let arr_sort = m.mk_array_sort(int, int);
        let v = m.mk_int(5);
        let c = m.mk_const_array(arr_sort, v);
        let j = m.mk_int_const("j");
        // (select (const 5) j) = 5 for any j
        let sel = m.mk_select(c, j);
        assert_eq!(simplify(&mut m, sel), v);
    }

    #[test]
    fn store_store_shadow() {
        let mut m = AstManager::new();
        let a = int_array(&mut m, "a");
        let i = m.mk_int(1);
        let v1 = m.mk_int(7);
        let v2 = m.mk_int(9);
        let inner = m.mk_store(a, i, v1);
        // (store (store a 1 7) 1 9) = (store a 1 9)
        let outer = m.mk_store(inner, i, v2);
        let expected = m.mk_store(a, i, v2);
        assert_eq!(simplify(&mut m, outer), expected);
    }

    #[test]
    fn store_select_identity() {
        let mut m = AstManager::new();
        let a = int_array(&mut m, "a");
        let i = m.mk_int_const("i");
        let sel = m.mk_select(a, i);
        // (store a i (select a i)) = a
        let st = m.mk_store(a, i, sel);
        assert_eq!(simplify(&mut m, st), a);
    }

    #[test]
    fn store_const_of_same_value() {
        let mut m = AstManager::new();
        let int = m.mk_int_sort();
        let arr_sort = m.mk_array_sort(int, int);
        let v = m.mk_int(5);
        let c = m.mk_const_array(arr_sort, v);
        let i = m.mk_int_const("i");
        // (store (const 5) i 5) = (const 5)
        let st = m.mk_store(c, i, v);
        assert_eq!(simplify(&mut m, st), c);
    }

    #[test]
    fn negative_symbolic_indices_not_folded() {
        let mut m = AstManager::new();
        let a = int_array(&mut m, "a");
        let i = m.mk_int_const("i");
        let j = m.mk_int_const("j");
        let v = m.mk_int(7);
        let st = m.mk_store(a, i, v);
        // (select (store a i v) j): i, j symbolic and not the same node — cannot
        // prove equal or distinct, so nothing folds.
        let sel = m.mk_select(st, j);
        let simplified = simplify(&mut m, sel);
        // Result is still a select over the store (not v, not (select a j)).
        assert!(m.is_select(simplified));
        assert!(m.is_store(m.app_args(simplified)[0]));
    }
}
