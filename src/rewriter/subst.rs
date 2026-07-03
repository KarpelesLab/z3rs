//! Expression substitution — the quantifier-free core of `expr_substitution` /
//! `var_subst` (`z3/src/ast/rewriter`, Z3 4.17.0, MIT).
//!
//! [`substitute`] performs a simultaneous replacement of whole subterms;
//! [`substitute_vars`] replaces De Bruijn variables by position (beta-reduction).
//! Both walk bottom-up and rebuild through the [`AstManager`], preserving hash
//! consing. De Bruijn index shifting under binders is added with quantifiers.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use crate::ast::AstId;
use crate::ast::manager::AstManager;
use crate::ast::node::AstNode;

/// Simultaneously replace each `from` subterm by its paired `to`, everywhere in
/// `root`. Replacements are not themselves rewritten (standard simultaneous
/// substitution).
pub fn substitute(m: &mut AstManager, root: AstId, subst: &[(AstId, AstId)]) -> AstId {
    let map: BTreeMap<AstId, AstId> = subst.iter().copied().collect();
    rebuild(m, root, |_, id| map.get(&id).copied())
}

/// Replace De Bruijn variable `i` with `values[i]` (for `i < values.len()`),
/// leaving higher-indexed variables unchanged. This is beta-reduction for the
/// quantifier-free fragment.
pub fn substitute_vars(m: &mut AstManager, root: AstId, values: &[AstId]) -> AstId {
    rebuild(m, root, |m, id| match m.node(id) {
        AstNode::Var(v) => values.get(v.index as usize).copied(),
        _ => None,
    })
}

/// Bottom-up rebuild of `root` where `replace(m, id)` may map a node to a
/// replacement (used verbatim, not descended into); otherwise applications are
/// rebuilt with rewritten children and leaves map to themselves.
fn rebuild<F>(m: &mut AstManager, root: AstId, mut replace: F) -> AstId
where
    F: FnMut(&AstManager, AstId) -> Option<AstId>,
{
    let order = m.postorder(root);
    let mut cache: Vec<Option<AstId>> = alloc::vec![None; m.len()];
    for &id in &order {
        let out = if let Some(r) = replace(m, id) {
            r
        } else {
            match m.node(id).clone() {
                AstNode::App(a) => {
                    let new_args: Vec<AstId> = a
                        .args
                        .iter()
                        .map(|&c| cache[c.0 as usize].unwrap())
                        .collect();
                    m.mk_app(a.decl, &new_args)
                }
                _ => id,
            }
        };
        cache[id.0 as usize] = Some(out);
    }
    cache[root.0 as usize].unwrap()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::util::symbol::Symbol;

    #[test]
    fn replaces_a_subterm_everywhere() {
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let y = m.mk_int_const("y");
        let one = m.mk_int(1);
        // (<= x y), replace x by (+ x 1)  =>  (<= (+ x 1) y)
        let le = m.mk_le(x, y);
        let xp1 = m.mk_add(&[x, one]);
        let out = substitute(&mut m, le, &[(x, xp1)]);
        let expected = m.mk_le(xp1, y);
        assert_eq!(out, expected);
    }

    #[test]
    fn substitution_is_simultaneous() {
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let y = m.mk_int_const("y");
        // swap x and y in (< x y) => (< y x)
        let lt = m.mk_lt(x, y);
        let out = substitute(&mut m, lt, &[(x, y), (y, x)]);
        let expected = m.mk_lt(y, x);
        assert_eq!(out, expected);
    }

    #[test]
    fn replacements_are_not_rewritten_further() {
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let y = m.mk_int_const("y");
        // replace x -> y and y -> x simultaneously; the x introduced for y is not
        // then turned back into y.
        let expr = m.mk_add(&[x, y]);
        let out = substitute(&mut m, expr, &[(x, y), (y, x)]);
        let expected = m.mk_add(&[y, x]);
        assert_eq!(out, expected);
    }

    #[test]
    fn substitutes_de_bruijn_variables() {
        let mut m = AstManager::new();
        let int = m.mk_int_sort();
        let v0 = m.mk_var(0, int);
        let v1 = m.mk_var(1, int);
        let a = m.mk_int_const("a");
        let b = m.mk_int_const("b");
        // (+ v0 v1) with [v0:=a, v1:=b] => (+ a b)
        let body = m.mk_add(&[v0, v1]);
        let out = substitute_vars(&mut m, body, &[a, b]);
        let expected = m.mk_add(&[a, b]);
        assert_eq!(out, expected);
        // A variable beyond the supplied values is left as-is.
        let f = m.mk_func_decl(Symbol::new("f"), &[int], int);
        let fv2 = {
            let v2 = m.mk_var(2, int);
            m.mk_app(f, &[v2])
        };
        assert_eq!(substitute_vars(&mut m, fv2, &[a, b]), fv2);
    }
}
