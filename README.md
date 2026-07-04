# z3rs

A **pure-Rust, `no_std`** port of the [Z3 theorem prover](https://github.com/Z3Prover/z3),
free of any third-party or native dependency.

`z3rs` reimplements Z3 (pinned at **v4.17.0**) as a single Rust crate with **no
GMP, no C, no `-sys` crate**. Its only dependency is our own pure-Rust,
dependency-free numeric core [`puremp`](https://github.com/KarpelesLab/puremp),
so the resolved dependency tree is just `z3rs → puremp`. The library is
`no_std` (needs only `alloc`); the optional `std` feature adds std-backed
conveniences. It aims to be behaviourally faithful to upstream Z3.

> ⚠️ **Status: early, in progress.** In place: a hash-consing AST, a simplifying
> rewriter, a **CDCL SAT core** (DIMACS), and a **lazy DPLL(T) SMT engine** that
> decides **QF_UF / QF_LRA / QF_LIA / QF_AX** and their combinations — congruence
> closure (incl. predicate congruence), Fourier–Motzkin linear arithmetic,
> integer branch-and-bound, read-over-write + extensionality arrays, and
> **bidirectional Nelson–Oppen** theory combination — plus a **bit-blasting engine
> for QF_BV** (bitwise, add/sub/mul, shifts, signed/unsigned compares,
> concat/extract, extend). It is **sound and terminating** (a work budget yields a
> sound `unknown` rather than a wrong answer or a hang) and
> **differential-tested against upstream z3** across three rounds of fuzzing. A
> full **SMT-LIB 2 front end** drives it (`check-sat(-assuming)`, `get-value`,
> `get-model`, `get-unsat-core`, `push`/`pop`, `define-fun`, …). Still ahead:
> quantifiers, more theories, the fixedpoint/optimization engines, and the C API.
> See [`ROADMAP.md`](ROADMAP.md).
>
> ```sh
> $ z3rs problem.cnf          # DIMACS CNF
> s SATISFIABLE
> v 1 2 3 0
>
> $ z3rs problem.smt2         # SMT-LIB2 (QF_UF/LRA/LIA/AX/BV)
> unsat
> ```

## Why

- **No native dependencies.** `cargo add z3rs` and go — no linking GMP or a C++
  toolchain, no `-sys` crate, works anywhere Rust does (incl. cross-compilation).
- **`no_std` + `alloc`.** The reasoning core runs without the standard library
  (embedded, wasm, kernel); `std` is an opt-in feature for timers/threads/I-O.
- **Memory safety.** A safe Rust surface over an SMT solver.
- **Legibility.** Ported file-by-file from Z3 so the two stay diffable.

## Layout

```
z3rs/
├── Cargo.toml        # package `z3rs`; only dependency is our own `puremp`
├── src/
│   ├── lib.rs        # module tree (mirrors z3/src), dependency-ordered
│   ├── main.rs       # the `z3rs` binary (CLI-compatible with `z3`)
│   ├── util/         # Phase 0: foundation (numerals via `puremp`)
│   ├── math/  ast/  params/          # Phase 1
│   ├── rewriter/                     # Phase 2
│   ├── model/  tactic/               # Phase 3
│   ├── sat/                          # Phase 4
│   ├── nlsat/  smt/                  # Phase 5
│   ├── solver/  cmd_context/         # Phase 6
│   ├── qe/  muz/  opt/               # Phase 7
│   ├── parsers/                      # Phase 8
│   └── api/                          # Phase 9
├── ROADMAP.md        # the master plan
├── PORTING.md        # how we translate C++ → Rust + testing strategy
└── z3/               # upstream Z3 4.17.0 (reference oracle; git-ignored)
```

## Build

```sh
cargo build                    # no_std library + `z3rs` binary
cargo run -- --version
cargo test
cargo build --lib --target thumbv7em-none-eabi   # proves the lib is no_std
```

The library is `no_std` by default. Enable std-backed features with
`--features std`. (The bundled `z3rs` binary links std itself for CLI I/O.)

## License & attribution

MIT. `z3rs` is a derivative work of Z3 (© Microsoft Corporation, MIT-licensed).
Not affiliated with or endorsed by Microsoft. See [`LICENSE`](LICENSE) and
[`NOTICE`](NOTICE).
