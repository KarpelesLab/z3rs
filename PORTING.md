# Porting methodology

How we translate Z3 (C++) into `z3rs` (Rust). Companion to [`ROADMAP.md`](ROADMAP.md).

## Golden rules

1. **Port, don't reinvent.** Translate the upstream file, preserving its
   structure, function names, and comments where idiomatic Rust allows. The goal
   is that a reviewer can diff `z3rs` against the corresponding `z3/src` file and
   follow along. Improve only where C++ idioms (manual refcounting, raw pointers,
   `goto`) map cleanly onto safer Rust ones.
2. **Every ported file cites its origin.** First line of each Rust source file:
   ```rust
   //! Ported from `z3/src/util/mpz.{h,cpp}` (Z3 4.17.0, MIT). See NOTICE.
   ```
3. **Numerals only through the `util` facades.** Never reach for a platform
   integer where Z3 used `rational`/`mpz`. This keeps the zero-dependency bignum
   boundary intact.
4. **`unsafe` is a localized, documented exception**, never in public API.

## Mapping C++ patterns to Rust

| Z3 C++ idiom                          | z3rs Rust approach |
|---------------------------------------|--------------------|
| `obj_ref` / `ref<T>` refcounting      | `Rc`/`Arc` or arena + index handles (`ast` uses interning + ids) |
| `ptr_vector<T>`, `vector<T>`          | `Vec<T>`, or index-based handles |
| `hashtable`, `obj_map`, `obj_hashtable` | `HashMap`/custom open-addressing where iteration order matters |
| `region` / `small_object_allocator`   | typed arenas in `util` |
| manual `~dtor` cleanup                 | `Drop` |
| `SASSERT`, `VERIFY`                    | `debug_assert!`, `assert!` |
| `TRACE("tag", …)`                      | a lightweight `trace!` macro gated behind a feature-free env check |
| C++ templates                          | Rust generics / traits |
| `virtual` dispatch (plugins, theories) | traits + `dyn`, or enums for closed sets |
| `goto`-based control flow              | loops with `break`/`continue` labels |

## AST representation

Z3's `ast_manager` interns every AST node and hands out `ast*` with manual
refcounting. In `z3rs`, `ast` interns into an arena and hands out lightweight
copyable handles (ids); the manager owns node storage. This preserves Z3's
hash-consing (structural sharing) and pointer-equality semantics without raw
pointers.

## Testing strategy (the spec is upstream Z3)

The oracle is the C++ Z3 **5.3.2** (latest stable) checked out in [`z3/`](z3/) (git-ignored).
The port itself started from the 4.17.0 development line (upstream commit
`f15584cda`, there is no `z3-4.17.0` tag); per-file "Ported from … (Z3 4.17.0)"
headers record that origin. Build the oracle once, GMP-backed, and treat its
output as ground truth.

```sh
git clone --filter=blob:none --branch z3-5.3.2 https://github.com/Z3Prover/z3.git z3
```

The byte-for-byte regression corpus is z3's own `z3test` repository, pinned to
the last commit before the 5.3.2 release so its `.expected.out` files are 5.3.2
behaviour (later commits add tests for unreleased features):

```sh
git clone https://github.com/Z3Prover/z3test.git z3test && git -C z3test checkout 55563df
python3 scripts/z3test_diff.py          # needs `cargo build --release`
```

1. **Unit tests** — port `z3/src/test/*` into Rust `#[test]`s next to each module.
2. **Numeral fuzzing (Phase 0)** — generate random operations over
   `mpz`/`mpq`/`mpf`, run against both z3rs and a tiny C shim calling Z3's numeral
   API, assert equality. Millions of iterations.
3. **Differential SMT testing (Phases 5+)** — run SMT-LIB benchmarks through both
   `z3rs file.smt2` and `z3 file.smt2`; compare `sat`/`unsat`/`unknown`, and for
   `sat` re-check the model, for `unsat` re-check the core/proof.
4. **Grammar fuzzing (Phase 10)** — fuzz the SMT-LIB parser and AST builders.

Differential harness scripts live under `tests/differential/` (added as phases
land). Keep resource limits generous initially so heuristic drift doesn't masquerade
as a correctness bug.

## Zero-dependency enforcement

- `Cargo.toml` `[dependencies]` stays empty. CI runs `cargo tree -e normal` and
  fails if any non-workspace crate appears.
- A guard test (`tests/no_external_deps.rs`) parses `Cargo.toml` and asserts the
  dependency table is empty.
- Standard-library only; no `build.rs` linking to C, no `-sys` crates, no vendored
  C. The bignum layer is hand-ported Rust (see ROADMAP §4).

## Per-module workflow

1. Read the upstream header + `.cpp` and its `CMakeLists.txt` dependencies.
2. Add the `mod.rs` submodule declarations mirroring upstream file names.
3. Port data structures first, then methods, then the free functions.
4. Port the corresponding `test/` cases; add differential coverage.
5. Update the file's `- [ ]` checklist and the ROADMAP §8 status when the phase
   exit criterion is met.
