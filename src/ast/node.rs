//! AST node content types, ported from the `decl`/`sort`/`func_decl`/`app`/`var`
//! classes in `z3/src/ast/ast.h` (Z3 4.17.0, MIT).
//!
//! These structs hold only the *structural content* of a node — the data that
//! defines its identity for hash-consing. Per-node bookkeeping that Z3 keeps in
//! the `ast` base (id, reference count, marks) lives in the manager, not here,
//! so `AstNode` can derive `Eq`/`Hash` and be used directly as a hash-cons key.

use alloc::vec::Vec;

use crate::ast::{
    AstId, AstKind, DeclKind, FamilyId, NULL_DECL_KIND, NULL_FAMILY_ID, Parameter, SortSize,
};
use crate::util::symbol::Symbol;

/// Family id, decl kind, and parameters shared by sorts and function decls
/// (`decl_info` in Z3).
///
/// No `Default` impl on purpose: the zero `family_id` is the *basic* family, not
/// the null one — use [`DeclInfo::null`] for an uninterpreted declaration.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct DeclInfo {
    /// The theory this declaration belongs to (`null` = uninterpreted).
    pub family_id: FamilyId,
    /// The specific declaration within the family.
    pub decl_kind: DeclKind,
    /// Extra parameters (widths, nested sorts, numerals, …).
    pub parameters: Vec<Parameter>,
}

impl DeclInfo {
    /// The uninterpreted (`null` family) info with no parameters.
    pub fn null() -> DeclInfo {
        DeclInfo {
            family_id: NULL_FAMILY_ID,
            decl_kind: NULL_DECL_KIND,
            parameters: Vec::new(),
        }
    }

    /// Interpreted info for `(family_id, decl_kind)` with `parameters`.
    pub fn new(family_id: FamilyId, decl_kind: DeclKind, parameters: Vec<Parameter>) -> DeclInfo {
        DeclInfo {
            family_id,
            decl_kind,
            parameters,
        }
    }

    /// Is this declaration uninterpreted with no parameters?
    pub fn is_null(&self) -> bool {
        self.family_id == NULL_FAMILY_ID && self.parameters.is_empty()
    }

    /// Does this declaration belong to `(fid, k)`?
    pub fn is_decl_of(&self, fid: FamilyId, k: DeclKind) -> bool {
        self.family_id == fid && self.decl_kind == k
    }
}

/// A sort (type). `sort` in Z3.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct SortData {
    /// The sort's name.
    pub name: Symbol,
    /// Family/kind/parameters.
    pub info: DeclInfo,
    /// Cardinality.
    pub num_elements: SortSize,
}

/// Boolean attributes of a function declaration (`func_decl_info` flags in Z3).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug, Default)]
pub struct FuncDeclFlags {
    /// Left associative (e.g. `-`).
    pub left_assoc: bool,
    /// Right associative (e.g. `=>`).
    pub right_assoc: bool,
    /// Flattened n-ary associative.
    pub flat_associative: bool,
    /// Commutative.
    pub commutative: bool,
    /// Chainable (e.g. `<`, expands to a conjunction of pairs).
    pub chainable: bool,
    /// Pairwise (e.g. `distinct`).
    pub pairwise: bool,
    /// Injective.
    pub injective: bool,
    /// Idempotent.
    pub idempotent: bool,
    /// A Skolem function introduced by the solver.
    pub skolem: bool,
    /// Polymorphic.
    pub polymorphic: bool,
}

/// A function declaration. `func_decl` in Z3.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct FuncDeclData {
    /// The function's name.
    pub name: Symbol,
    /// Family/kind/parameters.
    pub info: DeclInfo,
    /// Boolean attributes.
    pub flags: FuncDeclFlags,
    /// Argument sorts (each an [`AstKind::Sort`] node).
    pub domain: Vec<AstId>,
    /// Result sort (an [`AstKind::Sort`] node).
    pub range: AstId,
}

impl FuncDeclData {
    /// The arity (number of arguments).
    #[inline]
    pub fn arity(&self) -> usize {
        self.domain.len()
    }
}

/// A function application. `app` in Z3. The application's sort is the range of
/// its declaration, so it is not stored here.
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub struct AppData {
    /// The applied declaration (an [`AstKind::FuncDecl`] node).
    pub decl: AstId,
    /// The arguments (each an expression).
    pub args: Vec<AstId>,
}

/// A De Bruijn variable bound by an enclosing quantifier. `var` in Z3.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct VarData {
    /// The De Bruijn index.
    pub index: u32,
    /// The variable's sort (an [`AstKind::Sort`] node).
    pub sort: AstId,
}

/// The content of an AST node (one variant per [`AstKind`], quantifiers TBD).
#[derive(Clone, PartialEq, Eq, Hash, Debug)]
pub enum AstNode {
    /// A sort.
    Sort(SortData),
    /// A function declaration.
    FuncDecl(FuncDeclData),
    /// A function application.
    App(AppData),
    /// A bound variable.
    Var(VarData),
}

impl AstNode {
    /// This node's kind.
    pub const fn kind(&self) -> AstKind {
        match self {
            AstNode::App(_) => AstKind::App,
            AstNode::Var(_) => AstKind::Var,
            AstNode::Sort(_) => AstKind::Sort,
            AstNode::FuncDecl(_) => AstKind::FuncDecl,
        }
    }
}
