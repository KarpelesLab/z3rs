//! # `rewriter` — Term rewriting, simplification, E-graph, NNF, bit-blasting, FPA
//!
//! **Port phase 2.** Ported from the Z3 C++ component(s) below.
//! See [`ROADMAP.md`](../../ROADMAP.md) for the porting plan and status.
//!
//! ## Upstream C++ components to port
//! - [ ] `z3/src/rewriter`
//! - [ ] `z3/src/euf`
//! - [ ] `z3/src/substitution`
//! - [ ] `z3/src/macros`
//! - [ ] `z3/src/normal_forms`
//! - [ ] `z3/src/proofs`
//! - [ ] `z3/src/bit_blaster`
//! - [ ] `z3/src/pattern`
//! - [ ] `z3/src/parser_util`
//! - [ ] `z3/src/fpa`
//!
//! ## Status: SCAFFOLD (no functionality ported yet)

// Submodules will be declared here as components are ported, mirroring the
// upstream file layout (e.g. `pub mod mpz;` for `z3/src/util/mpz.{h,cpp}`).
