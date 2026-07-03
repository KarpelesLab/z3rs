//! # `util` — Foundation: numerals, containers, hashtables, symbols, vectors, params infra, rlimit, memory, sexpr
//!
//! **Port phase 0.** Ported from the Z3 C++ `util` component.
//! See [`ROADMAP.md`](../../ROADMAP.md) for the porting plan and status.
//!
//! ## Numerals
//!
//! Z3's `util` bignum stack (`mpn`/`mpz`/`mpq`/`rational`) is **not** re-ported
//! here — it is provided by our first-party, dependency-free
//! [`puremp`](https://github.com/KarpelesLab/puremp) crate, used directly
//! throughout z3rs (`puremp::Int`, `puremp::Rational`, `puremp::Float`; also
//! re-exported as [`crate::puremp`]). No wrapper layer. Z3's specialized
//! numerals not provided by `puremp` are ported in-tree on top of `puremp::Int`:
//! `mpbq` (dyadic `n·2^-k`) and `mpff`/`mpfx` (fixed precision); `mpf` (software
//! IEEE-754) maps onto [`puremp::Float`](puremp::Float).
//!
//! ## Upstream C++ components to port
//! - [x] `z3/src/util/{mpn,mpz,mpq,rational}` → provided by `puremp`
//! - [ ] `z3/src/util/{mpbq,mpff,mpfx}` (specialized numerals, on `puremp::Int`)
//! - [ ] `z3/src/util` containers/hashtables/symbol/vector/params/rlimit/…
//!
//! ## Status: SCAFFOLD (numeral backend wired; rest to port)

// Submodules are declared here as components are ported, mirroring the upstream
// file layout (e.g. `pub mod symbol;` for `z3/src/util/symbol.{h,cpp}`).
