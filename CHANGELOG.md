# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.0.7](https://github.com/KarpelesLab/z3rs/compare/v0.0.6...v0.0.7) - 2026-07-06

### Other

- inline `a = (lambda …)` bindings and beta-reduce reads of a
- fold str.replace with concrete s,t into a concat so the equation decides
- PARITY for const-array/map/BV-array, UFBV Ackermann, to_fp re-fold
- decide array map equalities by pointwise expansion
- QF sequences: inline `s = <concrete sequence>` so nth/len over s fold
- inline `a = (as const …) v` bindings so const-array reads fold
- re-fold to_fp(to_real n) once n is pinned, re-blasting the FP equality
- witness for distinct integers with lower bounds
- pigeonhole refutation for distinct integers with a sum bound
- Ackermannize uninterpreted bit-vector function applications
- read-over-write for bit-vector arrays
- record 598/598 cross-theory soundness stress result
- QF sequences: make symbolic seq.nth congruent (same (s,i) → same marker)
- Fix CI regression: apply datatype binding inline only as an unknown-fallback
- QF sequences: out-of-bounds seq.nth is an underspecified free value
- record the record/mutual-recursion datatype acyclicity soundness fix
- fold literal-literal str.< / str.<= order markers to their lexicographic truth
- QF sequences: length links for seq.contains / seq.prefixof / seq.suffixof
- Fix unsound datatypes: acyclicity for record/mutual-recursion cycles
- QF sequences: seq.prefixof / seq.suffixof partial-order axioms
- PARITY updates for NIA box witness, nonlinear ∀∃ conjunction, prefixof order
- bounded small-solution witness for ≤2-variable integer goals
- nonlinear ∀x∃y conjunction bodies via witness-at-infinity
- str.prefixof / str.suffixof partial-order axioms
- seed string witness with str.to_code target characters
- prefix/suffix character-overlap refutation over a length-pinned string
- inline ground constructor bindings so selectors/testers fold
- link str.prefixof to str.at (prefix pins leading characters)
- regex intersection length analysis
- cross-link str.< and str.<= (a<b ⇒ a≤b, a<b ⇒ ¬(b≤a))
- PARITY updates for extensionality, occurs-check, string ordering/ops, sequences
- link str.contains and str.indexof (contains ⟺ indexof x t 0 ≥ 0)
- str.<= total-order axioms (antisymmetry, transitivity, reflexivity)
- array extensionality refutation from a universal equality
- QF sequences: seed seq witness with elements of concrete sequences
- occurs-check refutation for cyclic datatype equalities among variables
- QF sequences: seq witness returns a model on sat even when check_model gives none
- fold str.to_int∘str.from_int at parse time (decides sat too)
- str.to_int ∘ str.from_int round-trip axiom
- str.< strict-order axioms (antisymmetry, transitivity, strictness)
- update PARITY for Cooper, nonlinear ∀∃, Bool-arrays, string ops
- odd-degree ∀x∃y equations are always solvable
- generalize nonlinear ∀x∃y to the full quadratic via discriminant
- decide nonlinear ∀x∃y for the y²-quadratic family
- str.to_code and str.indexof result-range axioms
- str.substr length axiom
- decide symbolic Bool-indexed arrays by index case-split
- decide Bool-indexed arrays with constant indices
- confirm a string sat directly from the abstract model
- QF sequences: seed the seq witness with goal integer literals
- str.at bounds axiom (out-of-bounds is empty)
- run the string/seq witness on the pre-axiom goal
- string witness returns a model on sat even when check_model gives none
- regex membership length restriction + fix in_re sort
- QF sequences: bounded SAT witness for symbolic integer sequences
- QF sequences: additive length axiom for symbolic seq.++
- resolve string predicates against x fixed by an equality
- generalize monotonicity to prefixof/suffixof
- substring monotonicity for str.contains
- Fix clippy: redundant i64 cast in Cooper
- full Presburger QE (Cooper) for integer ∀x∃y
- decide integer ∀x∃y with unit coefficients (exact FM)
- PARITY v2.1: reflect NIA product bounds, Nielsen, quantifier QE, recursive CHC, theory combination
- decide linear-real ∀x∃y by nested QE
- Simplify enumerate condition (clippy: redundant boolean)
- fix unsound sat on unseeded universals; Skolemize ∀∃; refute both
- G decides recursive CHC (both directions); D refutes word equations
- exact signed multiplication (bounded side stays bounded)
- Update ipow doc comment (now preserves open/closed flags)
- preserve interval open/closed flags through ipow (strict powers)
- decide array-of-bitvector via free reads + read-over-read congruence
- prove integer-unsat on bounded regions; free array reads as variables
- recursively case-split all disequalities into the dark-shadow witness
- sample an integer witness when no equality bounds the search
- interval-coefficient bound propagation for bilinear products
- Phase D: Nielsen transformation refutes word equations (unsat)
- Phase G: decide recursive multi-predicate CHC (invariant engine + path BMC)
- A (SAT/BV core speed) → done: bit-blaster speedups; practical fragment sub-second
- D (strings) and F (quantifiers) → done: practical fragments differential-clean
- I (models & proofs) → done: concrete models across theories + proof certificate
- Phase I: concrete string values in get-value / get-model
- publish PARITY.md v2; broad differential sweep is 0 gap / 0 unsound
- Phase D: length-guided string witness for fixed-length word equations
- disequality case-split into the dark-shadow witness

## [0.0.6](https://github.com/KarpelesLab/z3rs/compare/v0.0.5...v0.0.6) - 2026-07-05

### Other

- Phase G (Horn/CHC) → done: single-pred + acyclic multi-pred decide both directions
- Phase G: bound the multi-predicate BMC to decline cyclic systems fast
- Phase G: decide acyclic multi-predicate CHC exactly (both directions)
- roadmap Phase G — multi-predicate unsafe decides; safe needs MBP
- Phase G: multi-predicate CHC (unsafe direction) via bounded reachability
- roadmap Phase G — single-predicate CHC robust (property heads, non-bare args)
- Phase G: single-predicate CHC — property heads + non-bare predicate args
- Phase C (floating-point) → done: whole common QF_FP fragment decides
- Phase C: bit-blast to_fp(fp→fp) format conversion (widening)
- fp.fma/fp.sqrt now decide (were opaque); update the gate test
- Phase C: bit-blast symbolic fp.fma (port of z3's mk_fma)
- roadmap Phase C — symbolic Float16 arithmetic decides (bit-blaster wins)
- roadmap Phase C — 6 FP ops bit-exact + concrete arithmetic decides all formats
- Phase C: bit-blast symbolic fp.roundToIntegral (port of z3's mk_round_to_integral)
- roadmap Phase C — add/sub/mul/div/sqrt + to_fp folding landed
- Phase C: bit-blast symbolic fp.sqrt (port of z3's mk_sqrt)
- Phase C: bit-blast symbolic fp.div (port of z3's mk_div)
- Phase C: fold to_fp(real/int) to any format under any rounding mode
- Phase C: bit-blast symbolic fp.mul (port of z3's mk_mul)
- Phase B (div/mod) and Phase E (QF_NRA CAD) → done
- cofactor-expansion fallback when Bareiss division is inexact
- Fix CAD panic: make the Bareiss determinant / resultant chain fallible
- roadmap Phase B — comprehensive div/mod (gap ~1.3%)
- Phase B: pin div(t,t)=1, mod(t,t)=0 when dividend equals divisor
- Phase B: handle compound divisor expressions via a fresh alias variable
- roadmap Phase B — single-var divisor complete; compound divisors remain
- Phase B: complete decision for constant-dividend symbolic-divisor div/mod
- Phase B: div/mod witness — try zero divisor + goal-derived candidates
- apply rustfmt and fix rustdoc intra-doc warnings
- satisfy free-variable disequalities without draining branch-and-bound
- roadmap Phase E — complete-projection CAD fallback landed (salvaged)
- Phase A: structural hashing of bit-blaster gates
- roadmap Phase C — fp.add/sub landed (Float16 fast, Float32 needs Phase A)
- Bit-exact symbolic fp.add / fp.sub, bit-blasted to QF_BV
- Phase H (full C ABI) → done: representative real-world C programs run unchanged
- quantifier _const builders, datatypes, enum/tuple/set sorts + C program
- add Datatype sort, quantifier + pattern + declare_datatype builders
- read back model values and exercise unsat core
- model/AST-inspection surface (numeral readback, model_eval, ast vectors)
- roadmap tracker — Phase B/C/H progress this cycle
- expand drop-in Z3_ C ABI (80% path)
- Phase B: widen divisor-witness candidate range (gap ~8%→~6%)
- Phase B: SAT witnesses for symbolic div/mod via divisor enumeration
- Phase B: abstract symbolic div/mod as solver variables (Euclidean lift)
- Reset roadmap: from "port complete" to "close the parity gaps"
- record the divergence-closing campaign in Phase 10 (hardening & parity)
- Euclidean axiom for div/mod by a symbolic divisor
- changelog for sequence-theory soundness fixes
- Fix unsound UNSAT: seq.contains/prefixof/suffixof over symbolic elements
- Fix unsound SAT: propagate length of concrete sequences through equality
- changelog for fuzz-mined divergence fixes
- derive variable bounds from square equalities
- Fix unsound SAT: acyclicity across mutually-recursive datatypes
- Fix panic on ((_ to_fp eb sb) bv) bit-vector reinterpret form
- Fix panic in str.indexof folding on needle longer than string
- Fix unsound SAT: seq.len(s)=0 ⇔ s=empty (canonical empty sequence)
- Fix unsound SAT: str.len(s)=0 must force s=""
- roadmap all phases done, changelog, published parity report
- wire CAD, add CHC (BMC + k-induction), string & array completeness
- nlsat CAD/realclosure + ICP, DRAT checker, Datalog engine
- math kernels + ast quantifiers/translation foundations

### Other

- Divergence-closing vs z3 (fuzz-mined): fix wrong `sat` on string/sequence
  emptiness (`str.len(s)=0 ⇔ s=""`, `seq.len(s)=0 ⇔ s=empty` with a canonical
  empty sequence) and on acyclicity across **mutually-recursive datatypes**
  (`x=nodeA(nodeB(x))`); fix panics in `str.indexof` (needle longer than string)
  and `((_ to_fp eb sb) bv)` (bit-vector reinterpret form); and decide more
  nonlinear-integer systems by deriving variable bounds from square equalities
  (`x²+y²=3` unsat, `x²=2y² ∧ 0<x<5` unsat). Plus earlier this cycle: string
  length-link axioms + bounded witness search, and the functional-array-equality
  (`(_ map f)`/`(_ as-array f)`/`(lambda …)`) soundness gate. Sequence theory:
  propagate a concrete sequence's length through equality (`s=(seq.unit 1)` forces
  `seq.len(s)=1`, transitively) and decide `seq.contains`/`prefixof`/`suffixof`
  over symbolic elements by the exact element-equality constraint (`a=b`) rather
  than a syntactic AstId comparison (was a wrong `unsat`).
- Phase 1 ✅: `math` (multivariate `polynomial` + rational `interval` kernels),
  `params` (`param_descrs` schema tables), AST quantifiers/lambda +
  cross-manager `ast_translation` with a build→translate→pp round-trip
- Phase 3 ✅: `model` + recursive `model_evaluator`; the `tactic` framework
  (`Goal`, `Tactic`, `then`/`or_else`/`repeat`/`par`/`cond`, probes) + a
  solver-backed `ctx-solver-simplify`
- Phase 6 ✅: 100-case full-response differential regression corpus (verdict +
  get-value/get-model/get-unsat-core + push/pop/check-sat-assuming) vs z3
- Phase 8 ✅: `-dl` (finite-domain Datalog engine in `muz`) and `-drat` (RUP+RAT
  DRAT proof checker in `sat::drat`) frontends wired into the `z3rs` binary;
  `parsers` module gathers all four frontends
- Phase 5: substantial nonlinear-arithmetic decision procedure — sound
  refutation (`nlsat::icp`, interval constraint propagation), **linearization**
  (`x*y` with `x=2` → `2*y`), a complete **univariate procedure**
  (`nlsat::univariate`: Sturm-sequence real-root isolation + integer-root
  enumeration), **linear-variable elimination** (`nlsat::elim`: solve an equality
  for a linearly-occurring variable and substitute — `x*y=6 ∧ x+y=5` →
  `x*(5−x)=6`, with sound integer/real coefficient rules), and **bounded
  integer-box enumeration**. Together they turn a large fraction of QF_NRA/QF_NIA
  `unknown`s into definite sat/unsat matching z3, **fuzz-validated for soundness
  over 45k+ scripts (0 unsound after fixes)**. Also: multivariate SAT by
  variable-fixing (verified witnesses) and HC4-style **square narrowing** in ICP
  (`a·v²+rest<0` ⇒ `|v|≤√…`, refuting e.g. `x²+y²<1 ∧ xy>1`). Fuzzing caught and
  fixed a mixed Int/Real integrality bug and a zero-constant-term root bug.
- Phase 10: **soundness fix** — a "functional" array constant (`(_ map f)`,
  `(_ as-array f)`, or a `(lambda …)`) used in an *equality* (rather than being
  `select`ed) was left opaque, so its pointwise definition went unenforced and
  e.g. `map(-,a,b)=a ∧ b[0]≠0` or `(_ as-array f)=b ∧ b[0]≠f(0)` wrongly returned
  `sat`. Any such constant surviving into the goal now gates to a sound `unknown`
  (an explicit `select` still rewrites to `f(select …)`/`f(i)`/the β-reduced body
  and decides). Found by a 4.6k-script array-combinator differential fuzz.
- Phase 10: **string completeness** — closing z3rs↔z3 divergences in QF_S. New
  length-link axioms (`str.contains(s,sub) ⇒ len(s) ≥ len(sub)`,
  prefixof/suffixof, `len(str.at) ≤ 1`) refute length contradictions (`unsat`
  where it was `unknown`), and a bounded **string-witness search** (enumerate
  short candidates → re-fold the opaque markers to concrete values → confirm via
  the core solver) exhibits concrete models (`sat` where it was `unknown`). A
  fuzz-found soundness bug in the first cut of the witness search — new literals
  created mid-search were not asserted pairwise-distinct, so `check_model` could
  equate different literals and report a spurious `sat` — was fixed by conjoining
  the string axioms before confirming a witness.
- Phase 10 ✅: **hardening & parity** — a published **`PARITY.md`** report
  (per-theory coverage, soundness methodology, the fuzz-caught-and-fixed bugs,
  honest limitations) and a **77k-script cross-theory differential fuzz** vs z3
  spanning QF_UF/LIA/LRA/BV/A/DT/S/FP + quantifiers + nonlinear + CHC, with **0
  unsound** (every case where both solvers returned a definite verdict agreed).
  Completes the roadmap: **all 11 phases at their exit criterion**. Continuous
  follow-ons: performance tuning to a target factor of upstream, `unknown`-rate
  parity and proof/core validation at scale.
- Phase 7 ✅: **Constrained Horn Clause decision procedure** — a single-predicate
  CHC transition system (`(set-logic HORN)` rules parsed into `Init`/`τ`/`Bad`) is
  decided by **bounded model checking** (an `unsat`/unsafe verdict from a concrete
  counterexample trace) and **k-induction** (a `sat`/safe verdict from an inductive
  invariant such as `x≥0` or `x=y`), both sound with a resource bound → `unknown`.
  Conservative guards decline anything outside the fragment (multi-predicate,
  ground-constrained predicate, argument-permutation rules, non-bare arguments) so
  it never guesses. Fuzz-validated vs z3 over 3.3k CHC scripts (0 unsound;
  z3rs-only non-matches are `unknown`/timeout). Full multi-predicate CHC-COMP
  parity (Spacer PDR with model-based projection) remains a follow-on. Together
  with the existing `opt` (MaxSMT/optimization) and `qe` (quantifier elimination),
  this completes Phase 7's functional criterion.
- Phase 7: **soundness fix** for Constrained Horn Clauses — the quantifier
  instantiation engine wrongly reported `sat` for unsafe arithmetic-recursive CHC
  (e.g. `inv(x) ∧ y=x+1 ⇒ inv(y)` with no ground seed), because vacuous
  E-matching "saturation" over an infinite arithmetic domain was treated as
  complete. Now an arithmetic-productive universal that E-matching never fires on
  keeps a `sat` a sound `unknown`; recursive functions (ground-seeded, terminating)
  still decide.
- Phase 5: **full multivariate CAD for QF_NRA** (`nlsat::cad` + `nlsat::realclosure`
  + `math::{upoly,resultant}`) — a complete real-arithmetic decision procedure via
  McCallum projection (resultants/discriminants by fraction-free Bareiss), a
  base+lift decomposition, and exact **real-algebraic-number** arithmetic
  (`(defining poly, isolating interval)`, Sturm root isolation, `sign_at_point` by
  interval refinement + resultant certification). Decides genuinely multivariate
  systems previously left `unknown` — `x²+y²<4 ∧ xy>1` (sat), `x²+y²<1 ∧ xy>1`
  (unsat), `x·y=1 ∧ x²+y²=1` (unsat), `x²=2 ∧ y²=3 ∧ x+y<0` (sat) — all matching
  z3; degenerate (nullified / non-squarefree with parametric coefficients) or
  over-cap cases decline to a sound `unknown`. Soundness fuzzed vs z3 over
  ~7.5k multivariate scripts (0 unsound); fuzzing caught and fixed a
  between-sector-sample bug (open cells under strict inequalities collapsing onto
  a section).
- Phase 9 ✅: doctested safe-Rust APIs — text-driven `Solver` (`check_assuming`/
  `get_model`/`get_unsat_core`/`simplify`) and a handle-based `api::build`
  (`Context`/`Ast`/`Sort` term builders) — plus a **`Z3_`-prefixed drop-in C ABI**
  (real z3_api.h names/ABI, valgrind-clean): config/context lifecycle,
  `Z3_eval_smtlib2_string`, and the handle object API (sorts, consts, numerals,
  n-ary arith/bool, comparisons, `Z3_mk_solver`/`Z3_solver_assert`/`_check`,
  `Z3_solver_get_model`/`Z3_model_to_string`/`Z3_ast_to_string`). A find-model z3
  C program links & runs unchanged against libz3rs

## [0.0.5](https://github.com/KarpelesLab/z3rs/compare/v0.0.4...v0.0.5) - 2026-07-04

### Other

- Fix unsound SAT: opaque exponentiation was not gated as nonlinear
- Phase 6: accept the (Set T) sort as (Array T Bool)
- Phase 6: pseudo-boolean cardinality (_ at-least / _ at-most
- Fix unsound bv2int elimination on compound arguments
- Reject bit-vector width mismatch in equality (robustness)
- Phase 6: decide bv2int when the bit-vector is used only via bv2int
- Phase 5: string-predicate reflexivity on identical arguments
- Phase 5: symbolic seq.len as a non-negative Int function
- Fix unsound SAT: symbolic str.len could be negative

## [0.0.4](https://github.com/KarpelesLab/z3rs/compare/v0.0.3...v0.0.4) - 2026-07-04

### Other

- Bump puremp to 0.2.0
- Accept negative numeric literals (z3 compatibility)
- Phase 5: recover implied equalities from opposing inequalities
- Phase 5: dark shadow eliminates equalities first (+ budget isolation)

## [0.0.3](https://github.com/KarpelesLab/z3rs/compare/v0.0.2...v0.0.3) - 2026-07-04

### Other

- Update ROADMAP: Omega-test progress in Phase 5
- Phase 5: Omega-test dark shadow (verified SAT witness)
- Phase 5: Fourier–Motzkin integer-unsat fallback (Omega real shadow)
- Phase 5: Omega-test GCD tightening of integer inequalities
- Phase 3: honor tactics in (apply …) — nnf + combinators
- Fix unsound SAT: datatype universal with a non-matching selector trigger
- Phase 6: get-assertions, arity-N uninterpreted sorts, version fix
- Phase 2 ✅: enrich the theory rewriter; mark rewriter phase done
- Phase 4 ✅: SAT phase functional criterion met (cores + sat_smt)
- Phase 0 ✅: complete the util foundation (params + rlimit)
- Phase 5: word-equation boundary-character mismatch
- Phase 3: minimal (apply simplify) tactic + get-value model surface
- Reject bit-vector operand-width mismatches (robustness)

## [0.0.2](https://github.com/KarpelesLab/z3rs/compare/v0.0.1...v0.0.2) - 2026-07-04

### Other

- Phase 5: regex power ((_ re.^ n))
- Phase 6: (_ as-array f) and check-sat-using
- Fix two soundness bugs in quantifier elimination (valid universals refuted)
- Phase 5: Diophantine systems via unit-variable elimination
- Phase 5: word equations for concat=concat via prefix/suffix cancellation
- Phase 5: generalize Diophantine witness to n variables
- Phase 5: verified integer witness for unbounded 2-var Diophantine (LIA)
- Phase 6: more get-info keys (:authors, :error-behavior, :reason-unknown)
- Phase 6: array map combinator ((_ map f))
- Phase 5: Euclidean div/mod linking axioms
- Phase 5: product-sign axioms (extend square-nonnegativity)
- Phase 5: square-nonnegativity axiom for nonlinear arithmetic
- Phase 4: bit-vector overflow predicates (bvuaddo/bvsaddo/bvumulo/…)
- Fix soundness bug: opaque FP ops must not bit-blast to a free BV
- Phase 7: exists-forall quantifier alternation (∃x.∀y.φ)
- Phase 6: flatten nested universal quantifiers
- Phase 5: sequence search/replace folds (indexof/contains/prefixof/replace)
- Phase 5: regex complement and difference (re.comp / re.diff)
- Phase 5: Int<->BV bridge for constant equalities (bv2int / int2bv)
- Phase 5: str.is_digit and fp.to_real (integral) folds
- Phase 5: regex bounded repetition ((_ re.loop n m))
- collect like terms in sums (arith_rewriter)
- Phase 6: declare-datatype (singular), (eval t), (simplify t)
- Update ROADMAP (lambda arrays)
- Phase 6: lambda-defined arrays (beta-reduction on select)
- Phase 6: define-const, (_ divisible n), and ^ (exponentiation)
- Update ROADMAP (parametric datatypes)
- Phase 6: parametric (polymorphic) datatypes
- Update ROADMAP (mutual datatypes + recursion over datatypes)
- Phase 6: fold datatype selectors/testers under instantiation
- Phase 6: mutually-recursive datatypes
- Update ROADMAP (multi-trigger E-matching)
- Phase 6: multi-trigger E-matching
- Update ROADMAP (E-matching / trigger-based instantiation)
- Phase 6: E-matching (trigger-based quantifier instantiation)
- Apply rustfmt to recursive-function test
- Update ROADMAP (recursive function definitions)
- Phase 6: recursive functions (define-fun-rec / define-funs-rec)
- Fix soundness bug: QE must not fire when a binder is under a UF
- Update ROADMAP (SAT: clause-DB reduction, assumptions, conflict budget)
- learnt-clause deletion (bounded clause DB) + activity
- Update ROADMAP (symbolic fp.eq + conflict-budgeted bit-blaster)
- Fix symbolic-FP test: declare y before use
- symbolic fp.eq via BV + bounded bit-blaster (sound termination)
- Update ROADMAP (symbolic FP bit-blasting)
- Phase 5: symbolic floating-point via bit-blasting (equality + classification)
- Phase 5: more string operations (str.< / replace_all / to_code / from_code)
- Update ROADMAP (word equations for concat vs literal)
- Bump puremp 0.1.4 -> 0.1.7
- Phase 5: word equations for string concatenation vs a literal
- Update ROADMAP (Phase 9: safe Rust API)
- Phase 9: safe idiomatic Rust API (api::Solver)
- Update ROADMAP (Phase 7: integer QE for unit-coefficient LIA)
- Phase 7 (qe): integer quantifier elimination (unit-coefficient LIA)
- Update ROADMAP (Phase 7: quantifier elimination for real LRA)
- Phase 7 (qe): quantifier elimination for real linear arithmetic
- Update ROADMAP (quantifier saturation: finite-domain sat + Datalog)
- complete (not just sound) sat when instantiation saturates
- Update ROADMAP (QF_FP Float64 fragment)
- Phase 5: floating-point (QF_FP) constant folding for Float64
- Update ROADMAP (Phase 7: strict-supremum epsilon reporting)
- Phase 7 (opt): strict-supremum optimization reporting (epsilon)
- Update ROADMAP (Phase 7: real-valued optimization)
- Phase 7 (opt): real-valued optimization via Fourier-Motzkin
- Update ROADMAP (sequence theory fragment)
- Phase 5: sequence theory (Seq) structural fragment
- Update ROADMAP (quantifier fixpoint instantiation)
- iterate instantiation to a fixpoint
- Phase 5: round out QF_BV — bvcomp, reductions, int/bv conversions
- Update ROADMAP (match expressions, define-sort)
- Phase 8: define-sort (sort macros / aliases)
- Phase 6: datatype match expressions (SMT-LIB 2.6 match)
- Format regex test
- Update ROADMAP (Phase 5: regex membership in string theory)
- Phase 5: regular expressions for the string theory (str.in_re)
- Update ROADMAP (Phase 9: incremental C session API)
- Phase 9: incremental solver session in the C API
- Update ROADMAP (Phase 5: string/sequence fragment)
- Phase 5: string theory — sound constant-folding + length fragment
- Update ROADMAP (Phase 9: C ABI eval entry point)
- Phase 9: C ABI — z3rs_eval_smtlib2_string
- Update ROADMAP (Phase 7: assert-soft/MaxSAT)
- Phase 7 (opt): assert-soft / weighted MaxSAT
- Update ROADMAP (Phase 7 opt: integer optimization)
- Phase 7 (opt): integer optimization — maximize/minimize/get-objectives
- Phase 5/6: recursive datatypes with acyclicity (occurs-check)
- Format test additions
- Update ROADMAP (non-recursive datatypes: records + variants)
- Phase 5/6: multi-constructor (non-recursive) datatypes
- Phase 5/6: record/tuple datatypes (single constructor with fields)
- Update ROADMAP (quantifier instantiation + skolemization)
- Quantifiers stage 2: instantiation and skolemization
- Enum models: get-value prints the constructor name
- Update ROADMAP (enum datatypes, BV models, quantifier acceptance)
- Phase 5/6: enumeration datatypes (declare-datatypes)
- Phase 6: QF_BV models — get-value/get-model for bit-vectors
- Update ROADMAP (full QF_BV operator set + quantifier acceptance)
- accept forall/exists with a sound unknown (stage 1)
- Phase 5/6: QF_BV div/rem family + bit-blaster ite/implies/xor
- Phase 5/6: QF_BV bvnand/bvnor/bvxnor, rotate_left/right, repeat, bvashr
- Fix QF_LIRA division-by-constant; gate Bool-indexed arrays (soundness)
