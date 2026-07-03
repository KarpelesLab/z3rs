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
//! - [ ] richer boolean/arith rules, more theories, `euf`, `bit_blaster`, …
//!
//! ## Status: IN PROGRESS

pub mod arith_rewriter;
pub mod bool_rewriter;
pub mod nnf;
pub mod subst;
pub mod th_rewriter;

pub use nnf::to_nnf;
pub use subst::{substitute, substitute_vars};
pub use th_rewriter::simplify;
