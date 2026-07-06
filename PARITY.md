# z3rs ↔ Z3 Parity Report

A published account of how `z3rs` (a pure-Rust, `no_std + alloc` port of Z3 whose
only dependency is `puremp`) compares to upstream **Z3** as a decision oracle.
This is the Phase 10 deliverable: *where the two agree, where `z3rs` soundly
declines, and how that is validated.*

The governing invariant is **soundness before completeness**: `z3rs` must never
return a verdict that contradicts Z3. Where it cannot decide an instance it
returns `unknown` — never a guess. Every claim below is checked by differential
testing against `/usr/bin/z3` (the methodology of ROADMAP §7).

## At a glance

*Parity report v2 — reflects the completion of the theory roadmap (div/mod, the
full floating-point theory, complete-projection CAD, and single + acyclic
multi-predicate CHC).*

| | |
|---|---|
| Roadmap decision phases at exit | **all** — B (div/mod), C (floating-point), E (QF_NRA CAD), G (Horn/CHC), H (C ABI) met this cycle, joining the earlier fragments |
| Tests | 390 unit/integration `#[test]`s + doctests, all green; CI green on Linux/macOS/Windows, MSRV 1.88, no_std, C-ABI |
| Differential fuzzing | continuous vs `/usr/bin/z3`; a broad cross-theory sweep over **15 fragments** (LIA/LRA/BV/arrays/Bool-arrays/arrays-of-BV/datatypes/strings/sequences/regex/FP/NRA/NIA/quantifiers+∀∃/CHC/pseudo-boolean) is **0 gap, 0 unsound** on both-definite cases |
| Cumulative fuzzing | ~90k+ random scripts vs z3 across all fragments, **0 unsound** at final state |
| Dependencies | `z3rs → puremp` only (enforced by a guard test) |

## Per-theory coverage

"Decides" = returns a definite `sat`/`unsat` matching z3 across the fuzzed
fragment. "Declines" = returns a sound `unknown` on the noted hard tail rather
than guessing.

| Theory | Decides | Declines (sound `unknown`) |
|---|---|---|
| **QF_UF** | congruence closure at every sort, `distinct`, uninterpreted functions | — |
| **QF_LIA** | Fourier–Motzkin + branch-and-bound + Omega-test (GCD tightening, dark-shadow witness), **recursive disequality case-split into the dark shadow** (`distinct x y z`, n-way), free-variable-disequality elimination | instances exceeding the work budget |
| **QF_LRA** | Fourier–Motzkin with witness reconstruction, strict/non-strict | budget exhaustion |
| **QF_BV** | full core bit-blasting (arith/bitwise/shift/div/rem/compare/concat/extract/ext) over CDCL with **gate constant-folding + structural hashing** | conflict-budget exhaustion on hard instances |
| **QF_A / AX** | read-over-write + extensionality array axioms, **extensionality refutation from a universal** (`a≠b ∧ ∀i. a[i]=b[i]`), **Bool-indexed arrays** (symbolic indices decided by exhaustive index case-split; constant indices by congruence) | array combinators (`map`, `as-array`) beyond folded forms |
| **QF_DT** | datatypes: enums, records, recursive & mutually-recursive, parametric; `match`, selectors/testers; **occurs-check refutation of cyclic variable equalities** (`p = cons(0,q) ∧ q = cons(0,p)`, n-cycles) | — |
| **QF_S** | string constant folding, symbolic `str.len`, regex membership, length-link refutation, substring/prefix/suffix **monotonicity**, `str.at`/`str.substr`/`str.to_code`/`str.indexof` **length-range axioms**, **`str.contains ⟺ str.indexof …0 ≥ 0`**, **`str.to_int∘str.from_int` round-trip fold**, **`str.<` / `str.<=` order theories** (antisymmetry/transitivity/strictness/cycles), length-guided bounded witness (on the pre-axiom goal, with abstract-model confirmation), and a **Nielsen word-equation procedure** refuting periodicity equations (`x·b=a·x`) | deep-content SAT word equations (length-coupled) |
| **QF sequences** | integer-sequence length links, additive `seq.++` length, and a **bounded SAT witness** (seeded with goal & `seq_of` element values) deciding concat/`nth`/empty-subsequence cases | symbolic element sorts beyond Int; long sequences past the search bound |
| **QF_FP** | **the whole common surface bit-exact**: classification, ordered compares, `min`/`max`, `abs`/`neg`, exact `to_real`, **all arithmetic — `add`/`sub`/`mul`/`div`/`sqrt`/`fma`/`roundToIntegral`** (all 5 rounding modes), `to_fp(real/int/bv/fp-widening)`; concrete all-formats + symbolic Float16 decide | symbolic **Float32/64** circuits (performance-bound, like QF_BV); `rem`/`to_ubv`/`to_sbv`/`to_fp`-narrowing |
| **QF_NRA** | full CAD over real algebraic numbers with **complete (subresultant) projection** + cofactor-determinant fallback: coupled/degenerate multivariate systems decide; crash-safe fallible resultant chain | over-cap degree/dimension; ∀/∃-over-NRA (real QE) |
| **QF_NIA** | linearization, univariate CAD, bounded-integer search + **integer-witness sampling**, **≤2-variable box witness** (difference-of-squares `x²=y²+17`, small solutions) and **bounded-region unsat**, **interval-coefficient product bounds** (factoring `x·y=7`; coupled `x·y=z ∧ y·z=x`), variable elimination, **symbolic div/mod** (compound divisors, stable-tail UNSAT, `div(t,t)`/`mod(t,t)`) | undecidable/unbounded nonlinear integer cases beyond the box |
| **Quantified UF/LIA/NRA** | ground instantiation to a fixpoint, E-matching (recursive functions), finite Datalog/CHC, **Skolemization of `∃` under `∀`** (refutes `∀x∃y. y>x∧y<x`), **fresh-seed refutation** of un-grounded universals (`∀x. p(x)∧¬p(x)`), **linear-real `∀x∃y` by nested QE**, **integer `∀x∃y` by Presburger QE (Cooper)** with divisibility, and **nonlinear `∀x∃y`** for the quadratic-in-`y` family (discriminant → CAD), odd-degree (surjectivity), and **conjunction bodies via a witness-at-infinity** (`∀x∃y. y>x ∧ y²>x²`) | nonlinear `∀∃` needing a finite interior witness, MBQI sat over uninterpreted functions |
| **CHC (HORN)** | single-predicate transition systems (BMC + k-induction), acyclic multi-predicate systems, **and recursive/cyclic multi-predicate both directions**: safety by forward **polyhedral reachability** (FM-projected reach fixpoint), unsafety by **BFS path-unrolling BMC** | reach that needs non-polyhedral invariants (disjunctive/nonlinear) |
| **Theory combination** | **array reads of a free array as free variables** into the nonlinear engine (`select a x = x² ∧ x>2 ∧ select a x<5`) and the bit-blaster (**arrays of bit-vectors**, with read-over-read congruence for aliasing indices) | reads coupling ≥2 theories through a stored/aliased array |

## Soundness validation

Soundness is established by **differential fuzzing**: generate random small
scripts, run both `z3rs` and `z3`, and flag any case where *both* return a
definite verdict but they *disagree*. `unknown` (either side), errors, and
timeouts are ignored — only a both-definite contradiction is a bug.

Across the project this method drove out **12+ real soundness bugs**, each fixed
and captured as a regression test:

- opaque term treated as a free variable in the univariate `sat` path
- mixed Int/Real elimination dropping an integrality constraint
- integer-root enumeration missing roots when the constant term is 0
- unsound `bv2int` elimination on compound arguments
- opaque exponentiation not gated as nonlinear
- CAD between-sector sample collapsing onto a section (open cells under strict inequalities)
- CHC arithmetic-recursion reporting a wrong `sat` (vacuous instantiation "saturation")
- string-witness search reporting spurious `sat` (new literals not asserted distinct)
- "functional" array constants (`(_ map f)`, `(_ as-array f)`, `(lambda …)`) used
  in equalities treated as free variables → spurious `sat`
- single-constructor/record and mutually-recursive datatypes given no acyclicity
  measure → a cycle through them (`x = mka(mkb x)`) reported `sat` not `unsat`
- (plus earlier datatype selector-trigger and FP free-BV bugs)

Every one was a **wrong definite verdict** caught by differential fuzzing before
it could mislead — which is exactly why the fuzzing harness is run after every
completeness change.

Cumulative fuzzing to date: tens of thousands of nonlinear scripts, ~7.5k
multivariate CAD scripts, 3.3k CHC scripts, and a broad cross-theory sweep — all
**0 unsound** at their final state.

### Cross-theory agreement (latest sweep)

A 7,200-script differential sweep vs z3, `sat`/`unsat` verdicts only. "Both
definite" counts cases where z3 *and* z3rs each returned a definite verdict;
"agree" is how many of those matched. **Disagreements: 0 everywhere.**

| Fragment | scripts | both definite | agree | disagree |
|---|--:|--:|--:|--:|
| QF_UF | 420 | 420 | 420 | 0 |
| QF_LIA | 420 | 379 | 379 | 0 |
| QF_LRA | 420 | 417 | 417 | 0 |
| QF_BV | 420 | 420 | 420 | 0 |
| QF_A (arrays) | 420 | 139 | 139 | 0 |
| QF_DT (datatypes) | 420 | 412 | 412 | 0 |
| QF_S (strings) | 420 | 32 | 32 | 0 |
| QF_FP | 420 | 17 | 17 | 0 |
| Quantified UF/LIA | 420 | 420 | 420 | 0 |
| Mixed (UF+LIA, arrays+LIA, BV+UF) | 420 | 238 | 238 | 0 |
| div/mod with negatives | 300 | 300 | 300 | 0 |
| nonlinear (var·var, squares) | 300 | 261 | 261 | 0 |
| opaque `^` | 300 | 148 | 148 | 0 |
| bv2nat / int2bv | 300 | 54 | 54 | 0 |
| pseudo-boolean (at-least/at-most) | 300 | 230 | 230 | 0 |
| `(Set T)` sort | 300 | 235 | 235 | 0 |
| BV sdiv/srem/smod/shifts | 300 | 300 | 300 | 0 |
| BV sign/zero-extend, rotate | 300 | 300 | 300 | 0 |
| UF congruence/`distinct` | 300 | 300 | 300 | 0 |
| datatype acyclicity (deep) | 300 | 133 | 133 | 0 |
| **Total** | **7200** | — | — | **0** |

Where "both definite" is well below the script count (strings, FP, arrays,
bv2nat, deep datatypes), z3rs returned a sound `unknown` on the harder end of the
fragment — completeness, not correctness. No script produced opposing definite
verdicts.


## Known limitations (all sound `unknown`, never wrong)

- **Performance, not correctness**, bounds the hard tail: deep BMC, large
  bit-blasted circuits, and high-degree CAD hit resource budgets and decline.
- **CHC**: only single-predicate, k-inductive/bounded systems; the full
  CHC-COMP set needs Spacer PDR with model-based projection (a documented
  follow-on).
- **Quantifiers**: no MBQI; nested-quantifier goals decline.
- **C API**: a representative slice of the `Z3_` ABI (enough to link and run a
  canonical find-model program); the full `z3_api.h` surface is a follow-on.

These are completeness gaps. In every case `z3rs` returns `unknown` rather than a
verdict that could contradict Z3.
