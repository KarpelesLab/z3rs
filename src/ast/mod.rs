//! # `ast` — expression / sort / decl representation and the theory decl plugins
//!
//! **Port phase 1.** Ported from `z3/src/ast` (Z3 4.17.0, MIT). See NOTICE.
//! See [`ROADMAP.md`](../../ROADMAP.md) for the porting plan and status.
//!
//! ## Upstream components ported so far
//! - [x] `ast.h` metadata: [`AstKind`], [`FamilyId`], [`DeclKind`], [`SortSize`]
//! - [x] `ast.h` `parameter` → [`parameter`]
//! - [x] AST node content (`sort`/`func_decl`/`app`/`var`) → [`node`]
//! - [x] hash-consing `ast_manager` (sorts/decls/apps/vars) → [`manager`]
//! - [ ] quantifiers, theory `*_decl_plugin`s, translation, pretty-printing
//!
//! ## Status: IN PROGRESS

pub mod manager;
pub mod node;
pub mod parameter;

pub use manager::AstManager;
pub use node::{AppData, AstNode, DeclInfo, FuncDeclData, FuncDeclFlags, SortData, VarData};
pub use parameter::Parameter;

/// Identifies the theory ("family") a declaration belongs to. `-1`
/// ([`NULL_FAMILY_ID`]) means uninterpreted.
pub type FamilyId = i32;

/// The null family id (uninterpreted).
pub const NULL_FAMILY_ID: FamilyId = -1;

/// Identifies a specific declaration within a family (e.g. `+` within arith).
pub type DeclKind = i32;

/// The null decl kind.
pub const NULL_DECL_KIND: DeclKind = -1;

/// The five kinds of AST node (`ast_kind` in Z3; discriminants match).
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[repr(u8)]
pub enum AstKind {
    /// Function application.
    App = 0,
    /// De Bruijn variable (bound by an enclosing quantifier).
    Var = 1,
    /// Quantifier (`forall` / `exists` / `lambda`).
    Quantifier = 2,
    /// A sort (type).
    Sort = 3,
    /// A function declaration.
    FuncDecl = 4,
}

impl AstKind {
    /// Z3's `get_ast_kind_name`.
    pub const fn name(self) -> &'static str {
        match self {
            AstKind::App => "application",
            AstKind::Var => "variable",
            AstKind::Quantifier => "quantifier",
            AstKind::Sort => "sort",
            AstKind::FuncDecl => "declaration",
        }
    }
}

/// A lightweight, copyable handle to an AST node owned by the `ast_manager`
/// (introduced with the node layer). It is an index/identity: two handles are
/// equal iff they denote the same hash-consed node.
#[derive(Clone, Copy, PartialEq, Eq, Hash, PartialOrd, Ord, Debug)]
pub struct AstId(pub u32);

/// The cardinality of a sort: finite (with a size), finite-but-very-big
/// (> 2^64), or infinite. Ported from Z3's `sort_size`.
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub enum SortSize {
    /// Finite with exactly this many elements.
    Finite(u64),
    /// Finite but larger than 2^64.
    VeryBig,
    /// Infinite.
    Infinite,
}

impl SortSize {
    /// A finite sort of `n` elements.
    #[inline]
    pub const fn finite(n: u64) -> SortSize {
        SortSize::Finite(n)
    }

    /// An infinite sort.
    #[inline]
    pub const fn infinite() -> SortSize {
        SortSize::Infinite
    }

    /// A finite-but-very-big sort.
    #[inline]
    pub const fn very_big() -> SortSize {
        SortSize::VeryBig
    }

    /// Is this sort finite?
    #[inline]
    pub const fn is_finite(self) -> bool {
        matches!(self, SortSize::Finite(_))
    }

    /// Is this sort infinite?
    #[inline]
    pub const fn is_infinite(self) -> bool {
        matches!(self, SortSize::Infinite)
    }

    /// Is this sort finite but too big to count (> 2^64)?
    #[inline]
    pub const fn is_very_big(self) -> bool {
        matches!(self, SortSize::VeryBig)
    }

    /// The number of elements (only meaningful when [`is_finite`](Self::is_finite)).
    #[inline]
    pub const fn size(self) -> u64 {
        match self {
            SortSize::Finite(n) => n,
            _ => 0,
        }
    }

    /// `2^power` elements is "very big" once `power >= 64`.
    #[inline]
    pub const fn is_very_big_base2(power: u32) -> bool {
        power >= 64
    }
}

impl Default for SortSize {
    #[inline]
    fn default() -> SortSize {
        SortSize::Infinite
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ast_kind_discriminants_match_z3() {
        assert_eq!(AstKind::App as u8, 0);
        assert_eq!(AstKind::Var as u8, 1);
        assert_eq!(AstKind::Quantifier as u8, 2);
        assert_eq!(AstKind::Sort as u8, 3);
        assert_eq!(AstKind::FuncDecl as u8, 4);
        assert_eq!(AstKind::Sort.name(), "sort");
    }

    #[test]
    fn sort_size_variants() {
        assert!(SortSize::finite(8).is_finite());
        assert_eq!(SortSize::finite(8).size(), 8);
        assert!(SortSize::infinite().is_infinite());
        assert!(SortSize::very_big().is_very_big());
        assert!(SortSize::is_very_big_base2(64));
        assert!(!SortSize::is_very_big_base2(63));
        assert_eq!(SortSize::default(), SortSize::Infinite);
    }
}
