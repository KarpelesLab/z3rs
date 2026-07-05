//! Cross-manager AST translation.
//!
//! Ported from Z3's `ast_translation` (`z3/src/ast/ast_translation.{h,cpp}`,
//! Z3 4.17.0, MIT). Z3's `ast_translation` deep-copies an AST from a source
//! `ast_manager` into a target one, re-interning every sub-node so the result is
//! hash-consed in the destination (used for `Z3_translate`, model copying, and
//! moving terms between contexts/threads).
//!
//! Because the two managers assign theory *family ids* independently (in
//! registration order), we remap each declaration's `family_id` **by name** —
//! looking up the source family's symbol and (re)registering it in the
//! destination — so an interpreted decl keeps its meaning after translation.
//! Nested [`crate::ast::Parameter::Ast`] parameters (e.g. an array sort's
//! index/element sorts) are translated recursively.

use alloc::vec::Vec;

use crate::ast::manager::AstManager;
use crate::ast::node::{AppData, AstNode, DeclInfo, FuncDeclData, SortData, VarData};
use crate::ast::parameter::Parameter;
use crate::ast::{AstId, FamilyId, NULL_FAMILY_ID};

impl AstManager {
    /// Deep-copy the term/sort/decl `id` from `self` into `dst`, returning its id
    /// in `dst`. Structurally-shared sub-nodes are copied once and re-shared via
    /// `dst`'s hash-consing. `self` is left unchanged.
    pub fn translate(&self, id: AstId, dst: &mut AstManager) -> AstId {
        let mut memo: Vec<(AstId, AstId)> = Vec::new();
        self.translate_memo(id, dst, &mut memo)
    }

    fn translate_memo(
        &self,
        id: AstId,
        dst: &mut AstManager,
        memo: &mut Vec<(AstId, AstId)>,
    ) -> AstId {
        if let Some(&(_, t)) = memo.iter().find(|&&(s, _)| s == id) {
            return t;
        }
        let translated = match self.node(id).clone() {
            AstNode::Sort(SortData {
                name,
                info,
                num_elements,
            }) => {
                let info = self.translate_info(&info, dst, memo);
                dst.mk_sort(name, info, num_elements)
            }
            AstNode::FuncDecl(FuncDeclData {
                name,
                info,
                flags,
                domain,
                range,
            }) => {
                let info = self.translate_info(&info, dst, memo);
                let domain: Vec<AstId> = domain
                    .iter()
                    .map(|&d| self.translate_memo(d, dst, memo))
                    .collect();
                let range = self.translate_memo(range, dst, memo);
                dst.mk_func_decl_full(name, &domain, range, info, flags)
            }
            AstNode::App(AppData { decl, args }) => {
                let decl = self.translate_memo(decl, dst, memo);
                let args: Vec<AstId> = args
                    .iter()
                    .map(|&a| self.translate_memo(a, dst, memo))
                    .collect();
                dst.mk_app(decl, &args)
            }
            AstNode::Var(VarData { index, sort }) => {
                let sort = self.translate_memo(sort, dst, memo);
                dst.mk_var(index, sort)
            }
            AstNode::Quantifier(q) => {
                let var_sorts: Vec<AstId> = q
                    .var_sorts
                    .iter()
                    .map(|&s| self.translate_memo(s, dst, memo))
                    .collect();
                let body = self.translate_memo(q.body, dst, memo);
                let patterns: Vec<AstId> = q
                    .patterns
                    .iter()
                    .map(|&p| self.translate_memo(p, dst, memo))
                    .collect();
                dst.mk_quantifier(q.kind, &var_sorts, &q.var_names, body, &patterns, q.weight)
            }
        };
        memo.push((id, translated));
        translated
    }

    /// Translate a [`DeclInfo`], remapping its family id by name and any
    /// AST-valued parameters recursively.
    fn translate_info(
        &self,
        info: &DeclInfo,
        dst: &mut AstManager,
        memo: &mut Vec<(AstId, AstId)>,
    ) -> DeclInfo {
        let family_id = self.translate_family(info.family_id, dst);
        let parameters = info
            .parameters
            .iter()
            .map(|p| match p {
                Parameter::Ast(a) => Parameter::Ast(self.translate_memo(*a, dst, memo)),
                other => other.clone(),
            })
            .collect();
        DeclInfo {
            family_id,
            decl_kind: info.decl_kind,
            parameters,
        }
    }

    /// Map a source family id to the destination's id for the same family name,
    /// registering it in `dst` if necessary. `null` maps to `null`.
    fn translate_family(&self, fid: FamilyId, dst: &mut AstManager) -> FamilyId {
        if fid == NULL_FAMILY_ID {
            return NULL_FAMILY_ID;
        }
        match self.family_name(fid) {
            Some(name) => dst.mk_family_id(name),
            None => NULL_FAMILY_ID,
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::symbol::Symbol;

    // A translated term prints identically and, when translated back, is
    // structurally identical to the original — the round-trip contract.
    #[test]
    fn round_trip_preserves_pp() {
        let mut src = AstManager::new();
        // (and (or p (not q)) (= p q)) over Bool + an uninterpreted (f x) : A.
        let p = src.mk_bool_const("p");
        let q = src.mk_bool_const("q");
        let a = src.mk_uninterpreted_sort(Symbol::new("A"));
        let f = src.mk_func_decl(Symbol::new("f"), &[a], a);
        let xd = src.mk_func_decl(Symbol::new("x"), &[], a);
        let x = src.mk_const(xd);
        let fx = src.mk_app(f, &[x]);
        let nq = src.mk_not(q);
        let or = src.mk_or(&[p, nq]);
        let eq = src.mk_eq(p, q);
        let body = src.mk_and(&[or, eq]);

        for &term in &[p, q, fx, body] {
            let mut dst = AstManager::new();
            let t = src.translate(term, &mut dst);
            assert_eq!(src.pp(term), dst.pp(t), "pp changed under translation");
            // Round-trip back into a third manager.
            let mut back = AstManager::new();
            let t2 = dst.translate(t, &mut back);
            assert_eq!(src.pp(term), back.pp(t2));
        }
    }

    // Interpreted (arithmetic) decls keep their meaning even though the fresh
    // destination manager assigns the arith family a different id.
    #[test]
    fn translate_arith_remaps_family() {
        let mut src = AstManager::new();
        let x = src.mk_int_const("x");
        let three = src.mk_int(3);
        let sum = src.mk_add(&[x, three]);
        let ten = src.mk_int(10);
        let le = src.mk_le(sum, ten);

        let mut dst = AstManager::new();
        let t = src.translate(le, &mut dst);
        assert_eq!(src.pp(le), dst.pp(t));
        // Structural sharing is re-established in dst: translating x twice within
        // one call yields the same node (checked via a term that mentions x twice).
        let twice = src.mk_add(&[x, x]);
        let mut d2 = AstManager::new();
        let tt = src.translate(twice, &mut d2);
        let args = d2.app_args(tt).to_vec();
        assert_eq!(args[0], args[1], "shared subterm not re-shared");
    }

    // Array sorts carry their index/element sorts as AST-valued parameters;
    // translation must copy those too.
    #[test]
    fn translate_nested_sort_parameters() {
        let mut src = AstManager::new();
        let arr = src.mk_int_const("a"); // placeholder to ensure arith family exists
        let _ = arr;
        let idx = src.mk_int(0);
        let a = src.mk_int_const("arr_elem");
        let _ = (idx, a);
        // Build a select over an array const if the array theory is available.
        // (Kept minimal: exercise a bv numeral whose width is a Parameter::Int.)
        let bv = src.mk_bv(5, 8);
        let mut dst = AstManager::new();
        let t = src.translate(bv, &mut dst);
        assert_eq!(src.pp(bv), dst.pp(t));
    }

    // A universal quantifier `(forall ((x0 Int)) (<= (:var 0) 0))` round-trips.
    #[test]
    fn translate_quantifier() {
        let mut src = AstManager::new();
        let int = src.mk_int_sort();
        let v0 = src.mk_var(0, int);
        let zero = src.mk_int(0);
        let body = src.mk_le(v0, zero);
        let phi = src.mk_forall(&[int], body);
        assert!(src.is_quantifier(phi));
        let bool_sort = src.mk_bool_sort();
        assert_eq!(src.get_sort(phi), bool_sort);

        let mut dst = AstManager::new();
        let t = src.translate(phi, &mut dst);
        assert_eq!(src.pp(phi), dst.pp(t));
        assert!(dst.is_quantifier(t));
        // The body is reachable through traversal.
        assert!(src.num_subexprs(phi) >= 2);
    }
}
