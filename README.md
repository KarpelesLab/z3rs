# z3rs

A **pure-Rust, zero-dependency** port of the [Z3 theorem prover](https://github.com/Z3Prover/z3).

`z3rs` reimplements Z3 (pinned at **v4.17.0**) as a single Rust crate that links
against **nothing but the Rust standard library** — no GMP, no C, no third-party
crates — while aiming to be behaviourally faithful to upstream Z3.

> ⚠️ **Status: early scaffold.** The crate compiles and the module tree mirrors
> Z3's architecture, but no solving functionality is implemented yet. See
> [`ROADMAP.md`](ROADMAP.md) for the phased plan and live progress.

## Why

- **No native dependencies.** `cargo add z3rs` and go — no linking GMP or a C++
  toolchain, no `-sys` crate, works anywhere Rust does (incl. cross-compilation).
- **Memory safety.** A safe Rust surface over an SMT solver.
- **Legibility.** Ported file-by-file from Z3 so the two stay diffable.

## Layout

```
z3rs/
├── Cargo.toml        # package `z3rs`; [dependencies] is empty by design
├── src/
│   ├── lib.rs        # module tree (mirrors z3/src), dependency-ordered
│   ├── main.rs       # the `z3rs` binary (CLI-compatible with `z3`)
│   ├── util/         # Phase 0: bignum + foundation
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
cargo build            # library + `z3rs` binary
cargo run -- --version
cargo test
```

## License & attribution

MIT. `z3rs` is a derivative work of Z3 (© Microsoft Corporation, MIT-licensed).
Not affiliated with or endorsed by Microsoft. See [`LICENSE`](LICENSE) and
[`NOTICE`](NOTICE).
