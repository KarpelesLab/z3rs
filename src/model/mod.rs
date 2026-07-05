//! # `model` — Models and model evaluation
//!
//! **Port phase 3.** Ported from `z3/src/model` (Z3 4.17.0, MIT): `model_core`
//! (the map from declarations to interpretations) and `model_evaluator` (the
//! model-based term evaluator built on the rewriter).
//!
//! A [`Model`] assigns a value to each *uninterpreted* symbol: a constant maps
//! to a value term, an n-ary function to a finite graph plus an `else` value.
//! [`Model::eval`] evaluates an arbitrary term under the model — the
//! `model_evaluator` — by recursively evaluating children, substituting bound
//! symbols, applying function graphs, and folding interpreted operators through
//! the [`th_rewriter`](crate::rewriter) so the result collapses to a value
//! whenever the model is total for the term.

use alloc::collections::BTreeMap;
use alloc::vec::Vec;

use crate::ast::AstId;
use crate::ast::manager::AstManager;
use crate::ast::node::AstNode;
use crate::rewriter::simplify;

/// The interpretation of an uninterpreted function: an explicit graph of
/// `args → value` entries plus a default (`else`) value for unlisted arguments.
#[derive(Clone, Debug, Default)]
pub struct FuncInterp {
    /// Point entries: each `(argument-values, result-value)`.
    pub entries: Vec<(Vec<AstId>, AstId)>,
    /// The value for arguments not matched by any entry, if known.
    pub els: Option<AstId>,
}

impl FuncInterp {
    /// Look up the value for a fully-evaluated argument tuple.
    fn get(&self, args: &[AstId]) -> Option<AstId> {
        for (k, v) in &self.entries {
            if k.as_slice() == args {
                return Some(*v);
            }
        }
        self.els
    }
}

/// A model: interpretations for uninterpreted constants and functions.
/// Declarations are keyed by their `func_decl` [`AstId`] in the owning manager.
#[derive(Clone, Debug, Default)]
pub struct Model {
    consts: BTreeMap<AstId, AstId>,
    funcs: BTreeMap<AstId, FuncInterp>,
}

impl Model {
    /// An empty model.
    pub fn new() -> Model {
        Model::default()
    }

    /// Assign a constant declaration `decl` (a nullary `func_decl`) the value
    /// `value`.
    pub fn assign_const(&mut self, decl: AstId, value: AstId) {
        self.consts.insert(decl, value);
    }

    /// Assign a function declaration `decl` an interpretation.
    pub fn assign_func(&mut self, decl: AstId, interp: FuncInterp) {
        self.funcs.insert(decl, interp);
    }

    /// The value assigned to constant `decl`, if any.
    pub fn get_const(&self, decl: AstId) -> Option<AstId> {
        self.consts.get(&decl).copied()
    }

    /// The interpretation of function `decl`, if any.
    pub fn get_func(&self, decl: AstId) -> Option<&FuncInterp> {
        self.funcs.get(&decl)
    }

    /// The number of interpreted constants.
    pub fn num_consts(&self) -> usize {
        self.consts.len()
    }

    /// Evaluate `expr` under this model, returning the value term. Interpreted
    /// operators (arithmetic, Boolean, …) are folded by the rewriter; an
    /// uninterpreted constant/function with no assignment is left symbolic
    /// (a *partial* model), so `eval` is total and never fails.
    pub fn eval(&self, m: &mut AstManager, expr: AstId) -> AstId {
        // Post-order so children are evaluated before parents; memoise by id.
        let order = m.postorder(expr);
        let mut memo: BTreeMap<AstId, AstId> = BTreeMap::new();
        for id in order {
            let value = match m.node(id).clone() {
                AstNode::App(a) => {
                    let decl = a.decl;
                    if a.args.is_empty() {
                        // A constant: use its model value if assigned, else keep it
                        // (interpreted constants like numerals fold to themselves).
                        self.consts.get(&decl).copied().unwrap_or(id)
                    } else {
                        let vals: Vec<AstId> = a.args.iter().map(|c| memo[c]).collect();
                        // Uninterpreted function with a graph → look it up.
                        if let Some(interp) = self.funcs.get(&decl)
                            && let Some(v) = interp.get(&vals)
                        {
                            v
                        } else {
                            // Rebuild with evaluated args and fold interpreted ops.
                            let rebuilt = m.mk_app(decl, &vals);
                            simplify(m, rebuilt)
                        }
                    }
                }
                // Bound variables and quantifiers evaluate to themselves here
                // (closed ground terms are the evaluator's domain).
                _ => id,
            };
            memo.insert(id, value);
        }
        memo[&expr]
    }

    /// Evaluate `expr` and, if it reduces to a Boolean constant, return it.
    pub fn eval_bool(&self, m: &mut AstManager, expr: AstId) -> Option<bool> {
        let v = self.eval(m, expr);
        if m.is_true(v) {
            Some(true)
        } else if m.is_false(v) {
            Some(false)
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use puremp::Rational;

    // A model {x↦3, y↦5} evaluates `x + 2*y` to 13 and `x < y` to true.
    #[test]
    fn evaluates_arithmetic_and_predicates() {
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let y = m.mk_int_const("y");
        let two = m.mk_int(2);
        let two_y = m.mk_mul(&[two, y]);
        let sum = m.mk_add(&[x, two_y]);
        let lt = m.mk_lt(x, y);

        let mut model = Model::new();
        let three = m.mk_int(3);
        let five = m.mk_int(5);
        model.assign_const(m.app_decl(x), three);
        model.assign_const(m.app_decl(y), five);

        let v = model.eval(&mut m, sum);
        assert_eq!(m.as_numeral(v), Some(Rational::from_integer(13.into())));
        assert_eq!(model.eval_bool(&mut m, lt), Some(true));
    }

    // An uninterpreted function graph {f(1)=10, else 0} evaluates f(1) and f(2).
    #[test]
    fn evaluates_function_graph() {
        let mut m = AstManager::new();
        let int = m.mk_int_sort();
        let f = m.mk_func_decl(crate::util::symbol::Symbol::new("f"), &[int], int);
        let one = m.mk_int(1);
        let two = m.mk_int(2);
        let f1 = m.mk_app(f, &[one]);
        let f2 = m.mk_app(f, &[two]);

        let ten = m.mk_int(10);
        let zero = m.mk_int(0);
        let mut model = Model::new();
        model.assign_func(
            f,
            FuncInterp {
                entries: alloc::vec![(alloc::vec![one], ten)],
                els: Some(zero),
            },
        );
        assert_eq!(model.eval(&mut m, f1), ten);
        assert_eq!(model.eval(&mut m, f2), zero);
    }

    // A partial model leaves an unassigned constant symbolic but still folds
    // around it: eval(x + 0) = x even when x is unassigned.
    #[test]
    fn partial_model_is_total_and_symbolic() {
        let mut m = AstManager::new();
        let x = m.mk_int_const("x");
        let zero = m.mk_int(0);
        let sum = m.mk_add(&[x, zero]);
        let model = Model::new();
        assert_eq!(model.eval(&mut m, sum), x);
    }
}
