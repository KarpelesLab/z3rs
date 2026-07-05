//! The AST manager — ported from the hash-consing core of `ast_manager` in
//! `z3/src/ast/ast.{h,cpp}` (Z3 4.17.0, MIT).
//!
//! Every AST node is *hash-consed*: structurally identical nodes are created
//! once and share an [`AstId`]. The manager owns node storage (a `Vec` indexed
//! by id) and a hash-cons table mapping node content to its id. This gives Z3's
//! maximal structural sharing and pointer-equality-as-identity, without raw
//! pointers or reference cycles.
//!
//! No garbage collection yet: like Z3's never-freed symbol table, nodes live for
//! the manager's lifetime. Reference counting / GC will be layered on later.

use alloc::vec;
use alloc::vec::Vec;

use crate::ast::node::{
    AppData, AstNode, DeclInfo, FuncDeclData, FuncDeclFlags, QuantifierData, QuantifierKind,
    SortData, VarData,
};
use crate::ast::{AstId, AstKind, FamilyId, SortSize};
use crate::util::hash::fnv_hash;
use crate::util::symbol::Symbol;

struct Stored {
    node: AstNode,
    hash: u32,
}

/// Owns and hash-conses every AST node.
pub struct AstManager {
    nodes: Vec<Stored>,
    /// Hash-cons buckets: `buckets[hash & mask]` lists candidate node ids.
    buckets: Vec<Vec<u32>>,
    mask: usize,
    /// Registered theory families; the index is the [`FamilyId`].
    families: Vec<Symbol>,
}

impl Default for AstManager {
    fn default() -> AstManager {
        AstManager::new()
    }
}

impl AstManager {
    /// A new, empty manager. The "basic" family is pre-registered as id `0`.
    pub fn new() -> AstManager {
        const INIT_BUCKETS: usize = 16; // power of two
        AstManager {
            nodes: Vec::new(),
            buckets: vec![Vec::new(); INIT_BUCKETS],
            mask: INIT_BUCKETS - 1,
            families: vec![Symbol::new("basic")],
        }
    }

    // --- theory families --------------------------------------------------

    /// Register (or look up) a theory family by name, returning its id.
    pub fn mk_family_id(&mut self, name: Symbol) -> FamilyId {
        if let Some(fid) = self.get_family_id(name) {
            return fid;
        }
        let fid = self.families.len() as FamilyId;
        self.families.push(name);
        fid
    }

    /// The id of an already-registered family, if any.
    pub fn get_family_id(&self, name: Symbol) -> Option<FamilyId> {
        self.families
            .iter()
            .position(|&s| s == name)
            .map(|i| i as FamilyId)
    }

    /// The name of a registered family.
    pub fn family_name(&self, fid: FamilyId) -> Option<Symbol> {
        self.families.get(fid as usize).copied()
    }

    /// Number of distinct nodes created.
    #[inline]
    pub fn len(&self) -> usize {
        self.nodes.len()
    }

    /// Are there no nodes?
    #[inline]
    pub fn is_empty(&self) -> bool {
        self.nodes.is_empty()
    }

    /// Intern `node`, returning the (possibly pre-existing) id of an equal node.
    fn intern(&mut self, node: AstNode) -> AstId {
        let hash = fnv_hash(&node);
        let b = (hash as usize) & self.mask;
        for &id in &self.buckets[b] {
            let stored = &self.nodes[id as usize];
            if stored.hash == hash && stored.node == node {
                return AstId(id);
            }
        }
        let id = self.nodes.len() as u32;
        self.nodes.push(Stored { node, hash });
        self.buckets[b].push(id);
        if self.nodes.len() > self.buckets.len() * 2 {
            self.grow();
        }
        AstId(id)
    }

    /// Double the bucket count and rehash (keeps average chain length small).
    fn grow(&mut self) {
        let new_len = self.buckets.len() * 2;
        let new_mask = new_len - 1;
        let mut buckets: Vec<Vec<u32>> = vec![Vec::new(); new_len];
        for (id, stored) in self.nodes.iter().enumerate() {
            buckets[(stored.hash as usize) & new_mask].push(id as u32);
        }
        self.buckets = buckets;
        self.mask = new_mask;
    }

    // --- construction -----------------------------------------------------

    /// Create a sort with explicit info and cardinality.
    pub fn mk_sort(&mut self, name: Symbol, info: DeclInfo, num_elements: SortSize) -> AstId {
        self.intern(AstNode::Sort(SortData {
            name,
            info,
            num_elements,
        }))
    }

    /// Create an uninterpreted sort (null family, infinite cardinality).
    pub fn mk_uninterpreted_sort(&mut self, name: Symbol) -> AstId {
        self.mk_sort(name, DeclInfo::null(), SortSize::Infinite)
    }

    /// Create a function declaration `name : domain -> range`.
    pub fn mk_func_decl(&mut self, name: Symbol, domain: &[AstId], range: AstId) -> AstId {
        self.mk_func_decl_full(
            name,
            domain,
            range,
            DeclInfo::null(),
            FuncDeclFlags::default(),
        )
    }

    /// Create a function declaration with explicit info and flags.
    pub fn mk_func_decl_full(
        &mut self,
        name: Symbol,
        domain: &[AstId],
        range: AstId,
        info: DeclInfo,
        flags: FuncDeclFlags,
    ) -> AstId {
        debug_assert!(domain.iter().all(|&s| self.is_sort(s)));
        debug_assert!(self.is_sort(range));
        self.intern(AstNode::FuncDecl(FuncDeclData {
            name,
            info,
            flags,
            domain: domain.to_vec(),
            range,
        }))
    }

    /// Apply `decl` to `args`.
    pub fn mk_app(&mut self, decl: AstId, args: &[AstId]) -> AstId {
        debug_assert!(
            self.is_func_decl(decl),
            "mk_app: decl is not a function declaration"
        );
        debug_assert_eq!(
            self.func_decl(decl).unwrap().arity(),
            args.len(),
            "mk_app: arity mismatch"
        );
        self.intern(AstNode::App(AppData {
            decl,
            args: args.to_vec(),
        }))
    }

    /// A constant: a nullary application of `decl`.
    #[inline]
    pub fn mk_const(&mut self, decl: AstId) -> AstId {
        self.mk_app(decl, &[])
    }

    /// A De Bruijn variable of the given `sort`.
    pub fn mk_var(&mut self, index: u32, sort: AstId) -> AstId {
        debug_assert!(self.is_sort(sort));
        self.intern(AstNode::Var(VarData { index, sort }))
    }

    /// A quantifier / lambda. `var_sorts` and `var_names` list the bound
    /// variables outermost-first; inside `body` the innermost binder is De Bruijn
    /// index `0`. `patterns` are E-matching triggers. The node's sort is derived
    /// (`Bool` for `forall`/`exists`; a (possibly nested) array sort for
    /// `lambda`).
    pub fn mk_quantifier(
        &mut self,
        kind: QuantifierKind,
        var_sorts: &[AstId],
        var_names: &[Symbol],
        body: AstId,
        patterns: &[AstId],
        weight: i32,
    ) -> AstId {
        debug_assert_eq!(var_sorts.len(), var_names.len());
        debug_assert!(
            !var_sorts.is_empty(),
            "quantifier needs at least one binder"
        );
        let sort = match kind {
            QuantifierKind::Forall | QuantifierKind::Exists => self.mk_bool_sort(),
            QuantifierKind::Lambda => {
                // Nest array sorts innermost-first: (Array s_k ... (Array s_1 body)).
                let mut s = self.get_sort(body);
                for &vs in var_sorts.iter().rev() {
                    s = self.mk_array_sort(vs, s);
                }
                s
            }
        };
        self.intern(AstNode::Quantifier(QuantifierData {
            kind,
            var_sorts: var_sorts.to_vec(),
            var_names: var_names.to_vec(),
            body,
            patterns: patterns.to_vec(),
            weight,
            sort,
        }))
    }

    /// Convenience: a universal quantifier with fresh binder names `x0, x1, …`.
    pub fn mk_forall(&mut self, var_sorts: &[AstId], body: AstId) -> AstId {
        let names = default_binder_names(var_sorts.len());
        self.mk_quantifier(QuantifierKind::Forall, var_sorts, &names, body, &[], 0)
    }

    /// Convenience: an existential quantifier with fresh binder names `x0, x1, …`.
    pub fn mk_exists(&mut self, var_sorts: &[AstId], body: AstId) -> AstId {
        let names = default_binder_names(var_sorts.len());
        self.mk_quantifier(QuantifierKind::Exists, var_sorts, &names, body, &[], 0)
    }

    // --- accessors --------------------------------------------------------

    /// The node content for `id`.
    #[inline]
    pub fn node(&self, id: AstId) -> &AstNode {
        &self.nodes[id.0 as usize].node
    }

    /// The kind of `id`.
    #[inline]
    pub fn kind(&self, id: AstId) -> AstKind {
        self.node(id).kind()
    }

    /// Is `id` a sort?
    #[inline]
    pub fn is_sort(&self, id: AstId) -> bool {
        matches!(self.node(id), AstNode::Sort(_))
    }
    /// Is `id` a function declaration?
    #[inline]
    pub fn is_func_decl(&self, id: AstId) -> bool {
        matches!(self.node(id), AstNode::FuncDecl(_))
    }
    /// Is `id` an application?
    #[inline]
    pub fn is_app(&self, id: AstId) -> bool {
        matches!(self.node(id), AstNode::App(_))
    }
    /// Is `id` a variable?
    #[inline]
    pub fn is_var(&self, id: AstId) -> bool {
        matches!(self.node(id), AstNode::Var(_))
    }

    /// The sort content of `id`, if it is a sort.
    pub fn sort(&self, id: AstId) -> Option<&SortData> {
        match self.node(id) {
            AstNode::Sort(s) => Some(s),
            _ => None,
        }
    }
    /// The declaration content of `id`, if it is a function declaration.
    pub fn func_decl(&self, id: AstId) -> Option<&FuncDeclData> {
        match self.node(id) {
            AstNode::FuncDecl(f) => Some(f),
            _ => None,
        }
    }
    /// The application content of `id`, if it is an application.
    pub fn app(&self, id: AstId) -> Option<&AppData> {
        match self.node(id) {
            AstNode::App(a) => Some(a),
            _ => None,
        }
    }
    /// The variable content of `id`, if it is a variable.
    pub fn var(&self, id: AstId) -> Option<VarData> {
        match self.node(id) {
            AstNode::Var(v) => Some(*v),
            _ => None,
        }
    }

    /// The declaration of an application.
    pub fn app_decl(&self, id: AstId) -> AstId {
        self.app(id).expect("app_decl: not an application").decl
    }

    /// The arguments of an application.
    pub fn app_args(&self, id: AstId) -> &[AstId] {
        &self.app(id).expect("app_args: not an application").args
    }

    /// The sort of an expression (application or variable).
    pub fn get_sort(&self, expr: AstId) -> AstId {
        match self.node(expr) {
            AstNode::App(a) => {
                self.func_decl(a.decl)
                    .expect("app decl must be a func_decl")
                    .range
            }
            AstNode::Var(v) => v.sort,
            AstNode::Quantifier(q) => q.sort,
            _ => panic!("get_sort: node is not an expression"),
        }
    }

    /// The quantifier content of `id`, if it is a quantifier/lambda.
    pub fn quantifier(&self, id: AstId) -> Option<&QuantifierData> {
        match self.node(id) {
            AstNode::Quantifier(q) => Some(q),
            _ => None,
        }
    }

    /// Is `id` a quantifier or lambda?
    #[inline]
    pub fn is_quantifier(&self, id: AstId) -> bool {
        matches!(self.node(id), AstNode::Quantifier(_))
    }
}

/// Default binder display names `x0, x1, …` for `n` bound variables.
fn default_binder_names(n: usize) -> alloc::vec::Vec<Symbol> {
    (0..n)
        .map(|i| Symbol::new(&alloc::format!("x{i}")))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn sorts_are_hash_consed() {
        let mut m = AstManager::new();
        let a1 = m.mk_uninterpreted_sort(Symbol::new("A"));
        let a2 = m.mk_uninterpreted_sort(Symbol::new("A"));
        let b = m.mk_uninterpreted_sort(Symbol::new("B"));
        assert_eq!(a1, a2, "identical sorts share one id");
        assert_ne!(a1, b);
        assert_eq!(m.len(), 2);
        assert!(m.is_sort(a1));
        assert_eq!(m.sort(a1).unwrap().name, Symbol::new("A"));
    }

    #[test]
    fn applications_dedupe_and_carry_sorts() {
        let mut m = AstManager::new();
        let a = m.mk_uninterpreted_sort(Symbol::new("A"));
        // f : A -> A, constants x, y : A
        let f = m.mk_func_decl(Symbol::new("f"), &[a], a);
        let x_decl = m.mk_func_decl(Symbol::new("x"), &[], a);
        let x = m.mk_const(x_decl);
        // f(x) built twice must be the same node.
        let fx1 = m.mk_app(f, &[x]);
        let fx2 = m.mk_app(f, &[x]);
        assert_eq!(fx1, fx2);
        // f(f(x)) is distinct.
        let ffx = m.mk_app(f, &[fx1]);
        assert_ne!(fx1, ffx);
        // Sorts propagate through applications.
        assert_eq!(m.get_sort(x), a);
        assert_eq!(m.get_sort(fx1), a);
        assert_eq!(m.app_args(fx1), &[x]);
        assert_eq!(m.app_decl(fx1), f);
    }

    #[test]
    fn variables_hash_cons_by_index_and_sort() {
        let mut m = AstManager::new();
        let a = m.mk_uninterpreted_sort(Symbol::new("A"));
        let b = m.mk_uninterpreted_sort(Symbol::new("B"));
        let v0a = m.mk_var(0, a);
        let v0a2 = m.mk_var(0, a);
        let v0b = m.mk_var(0, b);
        let v1a = m.mk_var(1, a);
        assert_eq!(v0a, v0a2);
        assert_ne!(v0a, v0b);
        assert_ne!(v0a, v1a);
        assert_eq!(m.get_sort(v0a), a);
        assert_eq!(m.var(v0a).unwrap().index, 0);
    }

    #[test]
    fn hash_cons_survives_table_growth() {
        // Create enough nodes to force several bucket grows, then re-create the
        // first ones and confirm they still dedupe to the original ids.
        let mut m = AstManager::new();
        let a = m.mk_uninterpreted_sort(Symbol::new("A"));
        let mut decls = alloc::vec::Vec::new();
        for i in 0..200 {
            let name = alloc::format!("c{i}");
            decls.push(m.mk_func_decl(Symbol::new(&name), &[], a));
        }
        let n_after = m.len();
        // Re-creating an early decl must not add a node.
        let again = m.mk_func_decl(Symbol::new("c0"), &[], a);
        assert_eq!(again, decls[0]);
        assert_eq!(m.len(), n_after);
    }
}
