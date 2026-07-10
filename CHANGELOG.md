# Changelog

All notable changes to this project will be documented in this file.

The format is based on [Keep a Changelog](https://keepachangelog.com/en/1.0.0/),
and this project adheres to [Semantic Versioning](https://semver.org/spec/v2.0.0.html).

## [Unreleased]

## [0.0.8](https://github.com/KarpelesLab/z3rs/compare/v0.0.7...v0.0.8) - 2026-07-10

### Other

- add fp.add / fp.mul commutativity axiom
- fold str.replace with an empty pattern / empty source
- prefix search from 0 always succeeds (indexof of substr-prefix)
- add the str.indexof / str.contains link axiom
- fold (str.contains s (str.substr s i n)) to true
- String witness: enumerate integer args of any string op, not just indices
- String witness: enumerate index vars even with no string variable
- support the legacy parametric (declare-datatypes (T) …) syntax
- Nonlinear witness: enumerate only nonlinear-critical vars, linearising the rest
- Nonlinear integer sat: attach a witness model so eval/get-model work
- String witness: add literal-plus-one-char candidates (contains-but-distinct)
- Model eval: fold nonlinear terms over pinned arith leaves
- Fix invalid model from nonlinear box-witness: re-attach pinned variable values
- legacy (RegEx T) sort, re.nostr, and string-independent membership folds
- expand nested select-over-map recursively
- support the (default array) function
- accept n-ary (left-associative) concat
- Fix spurious sat: expand constant-exponent (^ y k) into a product
- Merge fix/features-4: 0^0 soundness, datatype-over-ite, array map equality
- decide (_ map f) equalities pointwise via extensionality
- distribute testers/selectors and equality over ite
- Fix unsound 0^0 folding; decide symbolic x^0 via b=0 ∨ x^0=1
- Fix unsound unsat: fp.min/fp.max ±0 clash has unspecified sign
- Merge fix/fp-soundness: single-NaN core equality, eager FP classification folding
- Fix two FP spurious-sat soundness bugs: NaN equality and pinned to_fp classification
- Speed up combined arith+EUF theory check: model-guided diseq split + interface pruning
- Merge fix/format-2: unsat-core fix, optimization objectives, array eval, fp model
- parse multi-line (define-fun) blocks in the model text
- narrowing float→float to_fp conversion (Float64→Float32 etc.)
- model-guided filler witness closes pure-length sat declines
- Merge fix/decline-completeness: decide fp.rem and to_fp-from-int
- Fold to_fp from a signed/unsigned machine integer (QF_FP DECLINE)
- Close fp.rem completeness gap (QF_FP DECLINE cluster)
- Add built-in List datatype, weighted pseudo-boolean, update-field; fix panics
- Fix unsound incremental SAT: unit clause added after solve killed the solver
- undecided infinite-domain universals return unknown, not sat
- refute division inequalities with a sign-known divisor
- Merge fix/regex-string: re.loop empty language, Unicode escapes, RegLan equality
- Fix regex/string soundness: re.loop min>max, \u escapes, RegLan equality
- discharge the Euclidean identity for a provably-nonzero divisor
- lift real division `/` with a symbolic divisor (soundness)
- arrays with different const-array defaults are unequal (soundness)
- differential harness against the z3 regression corpus
- complete residue-enumeration decision for modular goals
- exclude constant-pinned vars from the origin-box dimension
- modular congruence + residue witness for nonlinear mod
- origin-box fallback for real-feasible systems the LRA vertex hides
- widen the LRA rounding to a floor+{-1,0,1,2} neighborhood
- box-search free vars after Diophantine elimination; bound both searches
- search the null space of a residual Diophantine equation
- seq witness handles a variable pinned to length 0
- seq witness respects pinned lengths and skips content-free vars
- concat-pair on one variable refutes on leading/trailing char clash
- two concats on one variable with a length mismatch refute structurally
- align concats bound to the same variable directly
- fast integer witness by rounding the LRA relaxation
- str.< enumerates the words in a bounded gap
- a length-pinned seq with every nth pinned equals that concrete sequence
- Clean up clippy: use contains_key in seq concat split
- split a symbolic seq concat equal to a concrete sequence
- multi-element contains distributes over concat with rigorous span check
- flatten nested concats in the concat=literal split
- str.at char-chain refutation (perf-safe, refutation-only)
- seq.extract equality alignment, gated to existing nth markers
- contains-over-concat distributes over N parts with rigorous span check
- seq.at at an out-of-bounds index equals the empty sequence
- str.< bounds a gap of two to the single word between
- str.at at an out-of-bounds index equals the empty string
- length of seq.extract with concrete window and pinned len
- prefixof/suffixof pin the covered elements of a concat haystack
- suffixof pins the covered characters of a concat from the end
- prefixof pins the covered leading chars of a partially-covered part
- a concat of concrete + provably-empty parts is determined
- str.contains where len(haystack) = |Q| pins the concat parts
- multi-element contains where len H = len N ⇒ elementwise equality
- flatten nested concats in the nth-over-concat resolver
- element alignment of seq concat equalities
- cache seq.at & seq.unit for congruence; fix seq concat-var equality
- Fix unsound concat/literal bindings seeded from negated equalities
- Fix unsound seq.prefixof/suffixof pin emitted unconditionally
- Fix two unsound string/seq bugs found by differential fuzzing
- prefixof against a concat pins/refutes the covered parts
- resolve str.substr over a concatenation within concrete parts
- concat-determined witness flattens nested concatenations
- prefixof/suffixof true when a concat haystack starts/ends with the pattern
- a concat with a concrete part containing Q contains Q
- a concat whose length equals its concrete parts forces the tail empty
- str.at congruence under a plain equality
- resolve str.at over a concatenation (direct or concat-bound)
- distribute seq.contains over a concat-bound haystack variable
- resolve nth-over-concat when only the parts before the index are pinned
- Fix unsound seq.nth: not congruent under a plain equality
- distribute str.contains over a concat-bound haystack variable
- prefixof/suffixof with a concat pattern pins the target's characters
- seq.suffixof with a concrete-suffix concat pins the trailing elements
- seq.prefixof with a concrete-prefix concat pins the leading elements
- flatten nested concats in single-element contains distribution
- resolve seq.nth over a concatenation with pinned part lengths
- seq witness computes a concat-determined variable from its parts
- string witness computes a concat-determined variable from its parts
- string witness — don't pin a variable from a negated equality
- pin x to the single word of a literal-intersection regex
- invert str.replace to determine the removed pattern
- additive length axiom for symbolic str.++
- regex intersection with a literal pins the word
- length-pinned word equations by character alignment
- congruent string/seq op markers + int-term bound conflict
- re-derive an asserted mod-of-compound and refute a mismatch
- no length-n word between consecutive lexicographic bounds
- fold string predicates over a prefix/suffix-determined variable
- modulus scaling (mod(c·x, c·m) = c·mod(x,m))
- sequence predicate congruence under equality
- modulus chain (finer modulus determines a coarser one)
- close the variable-bound datatype nested-selector tail
- position-agnostic string predicate congruence
- Fix unsound array (_ map f) bound to a variable
- Fix unsound FP distinct/equality (bit-blasted results treated as free)
- seq.at element and length congruence
- enumerate words of a pinned length through a Kleene star
- generalize modular residue to +/−/· dividends
- string predicate congruence under equality
- modular residue of a product from pinned factor residues
- Fix unsound finite-language refutation from a phantom pinned length
- str.to_code and str.to_int inverses pin the string
- fold fp.to_real for any format, not only Float64
- QF_S (seq): single-element contains distributes over a concat
- prefixof over a concat with a concrete prefix
- generalize contains-over-concat span analysis to both orderings
- multi-char contains distributes over a non-spanning concat boundary
- chain mod-zero facts into mod-of-multiple
- mod of a multiple is zero
- trailing str.at characters imply suffixof
- leading str.at characters imply prefixof
- prefixof/suffixof of exact length fixes the whole string
- equal-length containment implies equality
- div/mod function congruence (pre-lift)
- empty re.inter from disjoint length sets
- adjacent prefix+suffix determine the whole string
- n-part string concat split at pinned part lengths
- regex mandatory suffix vs ¬suffixof
- Fix unsound concrete-sequence pinning under negation
- mutual containment implies equality
- finite-word regex membership filtered by a pinned length
- integer unit product (x·y = ±1 ⇒ each factor = ±1)
- ground datatype selector-tower perf fixed; note the variable-bound tail
- fold ground datatype selectors before axioms in check_sat
- refute membership in a regex and its complement
- non-empty all-digit membership forces str.to_int ≥ 0
- seq.suffixof element equality (nth(s,i) = nth(u, len u - len s + i))
- seq.prefixof element equality (nth(s,i) = nth(u,i) for i < len s)
- refute finite-language membership with all words excluded
- regex mandatory prefix vs ¬prefixof
- all str.at positions pinned fix the whole string
- seq.nth = c implies seq.contains (converse)
- gate datatype/record extensionality on Bool-containing sorts
- Fix unsound nested datatype/record extensionality
- Fix unsound datatype extensionality with Bool fields (multi-constructor)
- Fix unsound record with equal Bool fields but distinct (extensionality)
- invert to_fp(bv) = concrete to a bit-pattern equality
- refute non-empty membership in a nullable empty-core re.inter
- record bounded-product enumeration + NIA axioms; 20+ soundness bugs
- Fix unsound bounded nonlinear under disjunction (enumerate product vars)
- contains with concrete haystack pins x to a substring
- Fix unsound sum-of-squares = 0 under a disjunction
- enum-distinct witness (greedy constructor colouring)
- square monotonicity (0 ≤ a < b ⇒ a² < b²)
- seq.contains a single element pins it to some position
- seq.at element + length axioms
- refute membership in an empty re.inter (disjoint first-chars)
- str.at x i = c implies contains(x, c)
- single-character contains distributes over concat
- zero-product axiom (c·v0·v1·… = 0 ⇒ v0=0 ∨ v1=0 ∨ …)
- finite array cardinality in the distinct pigeonhole
- Fix unsound distinct over a finite datatype (Bool/BitVec/enum/record fields)
- PARITY.md — record this session's new refutation capabilities
- contains length axioms (len x ≥ len P; len x = len P ⇒ x = P)
- seq.extract element axioms + concrete-sequence equality pinning
- Fix unsound product-cancellation on a repeated factor (x·x = k·x)
- difference-of-squares axiom (a² = b² ⇒ a=b ∨ a=−b)
- bounded disjunctive case-split for concat-split goals
- integer range pigeonhole (n distinct ints in a range < n)
- product-cancellation axiom (x·y = k·x ⇒ x=0 ∨ y=k)
- suffixof pins the last character at str.len x - 1
- ROADMAP §7 note recursive-datatype axiom-unfold perf tail
- witness store a i c = store b i c by a = b
- fold fully-ground selector chains anywhere (conservative unsat-only)
- ROADMAP §7 — nested selectors closed; concat length-sum unsat side closed
- fold nested ground selector chains in the datatype inline
- ROADMAP §7 regex row — character-conflict cases closed
- extend regex refutation to str.contains (interior character)
- extend regex refutation to suffixof (last character)
- refute regex membership vs a conflicting first character
- refresh README status + ROADMAP road-to-100% (completeness tail)
- string witness uses only the pinned value for a literal-bound variable
- PARITY for the FP-ite soundness bug (15th) and enum pigeonhole
- enum pigeonhole refutation
- Fix unsound FP ite blasting (spurious sat)
- strip matching literal parts in a concat = literal (perf + completeness)
- QF sequences: generalize concat-split to n parts
- substitute congruence axioms so nested Ackermannization fires
- record the bv2nat/int2bv inline soundness bug (14th)
- Fix unsound int-const inline across bv2nat/int2bv (spurious verdict)
- pin characters from str.substr and prefixof/suffixof against a literal
- determine/refute n from str.from_int n = L
- resolve literal-bound containers + pin str.at from prefixof/suffixof
- QF sequences: pin elements from seq.prefixof/suffixof against a concrete part
- PARITY for seq concat-split/non-negativity, LIA int-const inline, prefix/suffix pinning
- QF sequences: split s ++ u = <concrete> at a pinned len s
- pin x from prefixof/suffixof against a literal at a fixed length
- inline integer `v = const` bindings so lifted-mod goals refute
- route all-variable ≥3-part concat=literal to the witness
- QF sequences: non-negativity for concat part lengths
- PARITY for new QF_S/seq capabilities and the seq-refold soundness fix
- simplify str/seq op arguments during refold so index expressions fold
- congruent str.at markers (shared decl per (x,i))
- string witness also tries small values for int index variables
- inline store-bound arrays and iterate const-array inline to a fixpoint
- Fix unsound seq equality after marker refold (spurious sat)
- str.to_int witness digits + length lower bound
- leave nested concat-vs-literal symbolic for the witness (perf + completeness)
- disjoint-contains length bound + overlap-merge witness candidates
- seed string witness with pairwise literal concatenations
- iterate ground-binding inline to a fixpoint
- seed the string witness with substrings of goal literals

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
