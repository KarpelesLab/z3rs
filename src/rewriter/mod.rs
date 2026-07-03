//! # `rewriter` — term rewriting and simplification
//!
//! **Port phase 2.** Ported from `z3/src/ast/rewriter` and friends (Z3 4.17.0,
//! MIT). See [`ROADMAP.md`](../../ROADMAP.md) for the plan and status.
//!
//! ## Ported so far
//! - [x] boolean constant folding (`bool_rewriter` subset) → [`bool_rewriter`]
//! - [ ] full `th_rewriter`, per-theory rewriters, `euf`, `nnf`, `bit_blaster`, …
//!
//! ## Status: IN PROGRESS

pub mod bool_rewriter;

pub use bool_rewriter::simplify;
