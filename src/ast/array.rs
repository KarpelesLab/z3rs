//! The array theory: the parametric sort `(Array I E)` and its operations
//! `select` (read) and `store` (write). Ported from `array_decl_plugin` in
//! `z3/src/ast/array_decl_plugin.{h,cpp}` (Z3 4.17.0, MIT).
//!
//! As with the other theories these are constructor methods on [`AstManager`].
//! An array sort carries its index and element sorts as `PARAM_AST` parameters,
//! so `select`/`store` recover the right domains from their array argument.

use alloc::vec;

use crate::ast::manager::AstManager;
use crate::ast::node::{DeclInfo, FuncDeclFlags};
use crate::ast::{AstId, DeclKind, FamilyId, Parameter, SortSize};
use crate::util::symbol::Symbol;

/// Array sorts (`array_sort_kind` in Z3).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[repr(i32)]
pub enum ArraySortKind {
    /// The parametric array sort `(Array I E)`.
    Array = 0,
}

/// Array operators (`array_op_kind` in Z3; the core three so far).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[repr(i32)]
pub enum ArrayOp {
    /// `store` (write): `(Array I E) × I × E → (Array I E)`.
    Store = 0,
    /// `select` (read): `(Array I E) × I → E`.
    Select = 1,
    /// `const` (constant array): `E → (Array I E)` — every index maps to the value.
    Const = 2,
}

/// Array-family constructors and recognizers.
impl AstManager {
    /// The array family id (registers "array" on first use).
    fn array_fid(&mut self) -> FamilyId {
        self.mk_family_id(Symbol::new("array"))
    }

    /// The registered array family id, if arrays have been used yet.
    fn array_fid_opt(&self) -> Option<FamilyId> {
        self.get_family_id(Symbol::new("array"))
    }

    /// The array sort `(Array index elem)`.
    pub fn mk_array_sort(&mut self, index: AstId, elem: AstId) -> AstId {
        let fid = self.array_fid();
        let info = DeclInfo::new(
            fid,
            ArraySortKind::Array as DeclKind,
            vec![Parameter::Ast(index), Parameter::Ast(elem)],
        );
        self.mk_sort(Symbol::new("Array"), info, SortSize::Infinite)
    }

    /// If `sort` is an array sort, its `(index, element)` sorts.
    pub fn array_sort_params(&self, sort: AstId) -> Option<(AstId, AstId)> {
        let afid = self.array_fid_opt()?;
        let s = self.sort(sort)?;
        if s.info.family_id != afid || s.info.decl_kind != ArraySortKind::Array as DeclKind {
            return None;
        }
        let index = s.info.parameters.first()?.get_ast()?;
        let elem = s.info.parameters.get(1)?.get_ast()?;
        Some((index, elem))
    }

    /// Is `sort` an array sort?
    pub fn is_array_sort(&self, sort: AstId) -> bool {
        self.array_sort_params(sort).is_some()
    }

    fn mk_array_app(
        &mut self,
        name: &str,
        op: ArrayOp,
        domain: &[AstId],
        range: AstId,
        args: &[AstId],
    ) -> AstId {
        let fid = self.array_fid();
        let info = DeclInfo::new(fid, op as DeclKind, alloc::vec::Vec::new());
        let decl = self.mk_func_decl_full(
            Symbol::new(name),
            domain,
            range,
            info,
            FuncDeclFlags::default(),
        );
        self.mk_app(decl, args)
    }

    /// `(select array index)` — the element `array[index]`.
    pub fn mk_select(&mut self, array: AstId, index: AstId) -> AstId {
        let array_sort = self.get_sort(array);
        let (idx_sort, elem_sort) = self
            .array_sort_params(array_sort)
            .expect("mk_select: first argument is not an array");
        self.mk_array_app(
            "select",
            ArrayOp::Select,
            &[array_sort, idx_sort],
            elem_sort,
            &[array, index],
        )
    }

    /// `(store array index value)` — `array` updated so that `index ↦ value`.
    pub fn mk_store(&mut self, array: AstId, index: AstId, value: AstId) -> AstId {
        let array_sort = self.get_sort(array);
        let (idx_sort, elem_sort) = self
            .array_sort_params(array_sort)
            .expect("mk_store: first argument is not an array");
        self.mk_array_app(
            "store",
            ArrayOp::Store,
            &[array_sort, idx_sort, elem_sort],
            array_sort,
            &[array, index, value],
        )
    }

    /// `((as const (Array I E)) value)` — the array mapping every index to
    /// `value`. `array_sort` is the target `(Array I E)`.
    pub fn mk_const_array(&mut self, array_sort: AstId, value: AstId) -> AstId {
        let (_, elem_sort) = self
            .array_sort_params(array_sort)
            .expect("mk_const_array: not an array sort");
        self.mk_array_app("const", ArrayOp::Const, &[elem_sort], array_sort, &[value])
    }

    /// If `id` is an application of an array-family declaration, its op.
    pub fn array_op(&self, id: AstId) -> Option<ArrayOp> {
        let afid = self.array_fid_opt()?;
        let a = self.app(id)?;
        let d = self.func_decl(a.decl)?;
        if d.info.family_id != afid {
            return None;
        }
        match d.info.decl_kind {
            k if k == ArrayOp::Store as DeclKind => Some(ArrayOp::Store),
            k if k == ArrayOp::Select as DeclKind => Some(ArrayOp::Select),
            k if k == ArrayOp::Const as DeclKind => Some(ArrayOp::Const),
            _ => None,
        }
    }

    /// Is `id` a constant-array application?
    pub fn is_const_array(&self, id: AstId) -> bool {
        self.array_op(id) == Some(ArrayOp::Const)
    }

    /// Is `id` a `select` application?
    pub fn is_select(&self, id: AstId) -> bool {
        self.array_op(id) == Some(ArrayOp::Select)
    }

    /// Is `id` a `store` application?
    pub fn is_store(&self, id: AstId) -> bool {
        self.array_op(id) == Some(ArrayOp::Store)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn array_sort_roundtrip() {
        let mut m = AstManager::new();
        let int = m.mk_int_sort();
        let arr = m.mk_array_sort(int, int);
        assert!(m.is_array_sort(arr));
        assert_eq!(m.array_sort_params(arr), Some((int, int)));
        assert!(!m.is_array_sort(int));
    }

    #[test]
    fn select_store_shapes() {
        let mut m = AstManager::new();
        let int = m.mk_int_sort();
        let arr_sort = m.mk_array_sort(int, int);
        let a = {
            let d = m.mk_func_decl(Symbol::new("a"), &[], arr_sort);
            m.mk_const(d)
        };
        let i = m.mk_int(1);
        let v = m.mk_int(7);
        let stored = m.mk_store(a, i, v);
        assert_eq!(m.get_sort(stored), arr_sort);
        assert!(m.is_store(stored));
        let read = m.mk_select(stored, i);
        assert_eq!(m.get_sort(read), int);
        assert!(m.is_select(read));
    }
}
