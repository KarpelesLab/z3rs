//! # `rewriter` — term rewriting and simplification
//!
//! **Port phase 2.** Ported from `z3/src/ast/rewriter` and friends (Z3 4.17.0,
//! MIT). See [`ROADMAP.md`](../../ROADMAP.md) for the plan and status.
//!
//! ## Ported so far
//! - [x] bottom-up driver ([`th_rewriter`]) dispatching to per-theory folders
//! - [x] boolean constant folding ([`bool_rewriter`])
//! - [x] arithmetic constant folding ([`arith_rewriter`])
//! - [x] subterm / De Bruijn variable substitution ([`subst`])
//! - [x] negation normal form ([`nnf`])
//! - [x] richer boolean rules: complementary-pair collapse (`p ∧ ¬p`, `p ∨ ¬p`),
//!   numeral-equality folding, `(= p true/false)`, `ite` with Boolean-constant
//!   branches → connectives
//! - [x] `euf` (congruence closure) and `bit_blaster` — implemented in the SMT
//!   engine ([`crate::smt::euf`], [`crate::smt::bv`]); theory-specific folding
//!   (datatype/string/bv/array) is dispatched from the front end
//!
//! ## Status: DONE (theory-rewriter driver + boolean/arith folding + NNF +
//! substitution; euf and the bit-blaster live in the SMT engine)

pub mod arith_rewriter;
pub mod bool_rewriter;
pub mod nnf;
pub mod subst;
pub mod th_rewriter;

pub use nnf::to_nnf;
pub use subst::{substitute, substitute_vars};
pub use th_rewriter::simplify;
