# Arbitrary-precision integer & rational library — specification

> **Realized by [`puremp`](https://github.com/KarpelesLab/puremp).** z3rs depends
> on `puremp` (pure-Rust, dependency-free, `no_std`) for this layer and uses its
> `Int` / `Rational` / `Float` types directly. This document is kept as the
> requirements reference the numeric core must satisfy; `puremp` also provides an
> MPFR-class `Float` beyond the integer/rational scope below.

A self-contained, dependency-free arbitrary-precision arithmetic library
providing two types:

- **`Integer`** — a signed integer of unbounded magnitude.
- **`Rational`** — an exact rational number, always kept in canonical form.

The library targets use as a numeric foundation for symbolic-computation,
computer-algebra, and constraint-solving software, where it is on the hot path
and where subtle rounding/sign conventions must be exact and predictable.

Floating-point types (arbitrary-precision or fixed) and specialized numeral
forms (e.g. dyadic `n·2^-k`) are **out of scope** — they are separate concerns
that can be layered on top of `Integer` by downstream crates.

---

## 1. Ground rules

- **No dependencies.** Standard library only. No native code, no build scripts
  linking C, no third-party crates. The whole point is a portable, pure-Rust
  numeric core that compiles anywhere Rust does.
- **Exactness.** Every operation is exact; there is no rounding except where a
  method explicitly converts to a bounded type (`to_f64`, `to_i64`, decimal
  display with a precision).
- **Canonical `Rational`.** Every `Rational` value satisfies: denominator `> 0`,
  `gcd(numerator, denominator) == 1`, and integers have denominator `1`. This is
  an invariant maintained by every constructor and operation.
- **Deterministic.** No global mutable state; results depend only on inputs.
  Hashing is stable within a build and consistent with `Eq`.

---

## 2. Design requirements that are easy to get wrong

These are the non-obvious constraints that separate a usable numeric core from a
naive `Vec<u64>` wrapper. They are correctness- or performance-critical.

### 2.1 Small-value inlining (performance — mandatory)
In practice the vast majority of values fit in a single machine word. Storing
those inline (a tagged `i64`) and only heap-allocating limbs on overflow avoids
allocation churn that otherwise dominates runtime. Represent `Integer` as a
tagged union, e.g.:

```
enum Repr { Small(i64), Large { sign: Sign, mag: Box<[u64]> } }
```

All arithmetic must take the fast path when both operands are small, and must
demote back to `Small` whenever a result once again fits in the inline word.

### 2.2 Three division/remainder conventions, precisely defined (correctness)
Different callers need different rounding of the quotient. Do not conflate them.
For `a / b`:

| Convention  | Quotient rounds toward | Remainder sign / range | Std analogue        |
|-------------|------------------------|------------------------|---------------------|
| **Truncated** | zero                 | sign of dividend `a`   | `i64::/`, `i64::%`  |
| **Euclidean** | (so remainder ≥ 0)   | always `0 ≤ r < |b|`   | `div_euclid`, `rem_euclid` |
| **Floored**   | −∞                   | sign of divisor `b`    | `i32::div_floor` (nightly) |

**Truncated** and **Euclidean** are required. **Floored** is recommended (cheap
once the other two exist). Every pair must satisfy `a == q*b + r` exactly.
Provide a combined `div_rem_*` that returns both without recomputing.

Also provide **exact division** (`div_exact`) for the case where the divisor is
known to divide the dividend — it can skip remainder handling and is much faster.

### 2.3 Power-of-two fast paths (performance)
Shifting and low-bit masking are extremely common and must not go through the
general multiply/divide routines:
- `mul_2k(k)` = `self << k`
- `div_2k_trunc(k)` = truncated `self / 2^k`
- `mod_2k(k)` = the low `k` bits (i.e. `self mod 2^k`, non-negative)
- `is_power_of_two()`, `next_power_of_two()`, `prev_power_of_two()`,
  `trailing_zeros()`.

### 2.4 Width-aware two's-complement bitwise ops (correctness)
Bit-level consumers need `and`/`or`/`xor`/`not` defined on the **two's-complement**
representation. Because negative values have infinitely many leading sign bits,
**`bitnot` takes an explicit bit-width**. Define the semantics precisely and
document them; this is distinct from bitwise ops on sign-magnitude.

### 2.5 Public limb & bit access (correctness/interop)
Consumers that serialize, hash, or inspect values bit-by-bit need direct access:
`bit(i)`, a little-endian limb slice, the least-significant limb, and a
`from_limbs` constructor. These must be public and cheap.

### 2.6 Fused multiply-accumulate (performance)
Inner loops of linear algebra / linear arithmetic repeatedly compute
`acc += a*b` and `acc -= a*b`. Provide fused `addmul`/`submul` that avoid the
temporary and, for the `Small` path, use widening 128-bit intermediates.

---

## 3. `Integer` — required API

Provide the standard operator traits **and** the named methods (the operators are
ergonomics; named methods make intent explicit and cover the non-operator ops).
Binary operators should have by-value, by-reference, and by-`i64` overloads.

```rust
pub struct Integer { /* Small(i64) | Large { sign, mag } */ }

// construction / conversion
impl From<i8/i16/i32/i64/i128/u8/u16/u32/u64/usize> for Integer {}
impl FromStr for Integer {}                          // decimal, optional '-'
impl Integer {
    pub fn from_str_radix(s:&str, radix:u32) -> Result<Integer, ParseIntError>;
    pub fn from_limbs(sign: Sign, limbs: &[u64]) -> Integer;      // little-endian
    pub const ZERO: Integer; pub const ONE: Integer; pub const MINUS_ONE: Integer;
}

// predicates / sign
pub fn is_zero(&self)->bool;   pub fn is_one(&self)->bool;  pub fn is_minus_one(&self)->bool;
pub fn is_positive(&self)->bool; pub fn is_negative(&self)->bool;
pub fn is_even(&self)->bool;   pub fn is_odd(&self)->bool;
pub fn signum(&self)->i32;                           // -1 / 0 / +1

// arithmetic (also Add/Sub/Mul/Neg + *Assign)
pub fn abs(&self)->Integer;
pub fn pow(&self, exp:u32)->Integer;
pub fn addmul(&mut self, a:&Integer, b:&Integer);    // self += a*b   (fused)
pub fn submul(&mut self, a:&Integer, b:&Integer);    // self -= a*b   (fused)

// division — see §2.2 for exact semantics
pub fn div_trunc  (&self, d:&Integer)->Integer;
pub fn rem_trunc  (&self, d:&Integer)->Integer;
pub fn div_rem_trunc(&self, d:&Integer)->(Integer,Integer);
pub fn div_euclid (&self, d:&Integer)->Integer;
pub fn rem_euclid (&self, d:&Integer)->Integer;      // always in [0,|d|)
pub fn div_rem_euclid(&self, d:&Integer)->(Integer,Integer);
pub fn div_floor  (&self, d:&Integer)->Integer;      // recommended
pub fn div_exact  (&self, d:&Integer)->Integer;      // precondition: d | self
pub fn divides(&self, other:&Integer)->bool;

// number theory
pub fn gcd(&self, b:&Integer)->Integer;
pub fn lcm(&self, b:&Integer)->Integer;
pub fn extended_gcd(&self, b:&Integer)->(Integer/*g*/, Integer/*x*/, Integer/*y*/);

// power-of-two & bit tricks (§2.3)
pub fn mul_2k(&self, k:u32)->Integer;
pub fn div_2k_trunc(&self, k:u32)->Integer;
pub fn mod_2k(&self, k:u32)->Integer;
pub fn is_power_of_two(&self)->Option<u32>;          // Some(shift) if ±2^shift
pub fn next_power_of_two(&self)->u32;
pub fn prev_power_of_two(&self)->u32;
pub fn trailing_zeros(&self)->u32;

// roots / size
pub fn sqrt_exact(&self)->Option<Integer>;
pub fn nth_root_exact(&self, n:u32)->Option<Integer>;
pub fn bit_len(&self)->u32;                          // bits in |self|
pub fn log2_floor(&self)->u32;

// two's-complement bitwise (§2.4)
pub fn bitand(&self, b:&Integer)->Integer;
pub fn bitor (&self, b:&Integer)->Integer;
pub fn bitxor(&self, b:&Integer)->Integer;
pub fn bitnot(&self, width:u32)->Integer;

// limb / bit access (§2.5)
pub fn bit(&self, i:u32)->bool;
pub fn limbs(&self)->&[u64];                         // little-endian magnitude
pub fn least_significant_limb(&self)->u64;

// bounded conversions
pub fn fits_i64(&self)->bool; pub fn fits_u64(&self)->bool;
pub fn to_i64(&self)->Option<i64>; pub fn to_u64(&self)->Option<u64>;
pub fn to_f64(&self)->f64;                           // nearest double

// display / hash
impl Display for Integer {}                          // decimal
impl Hash    for Integer {}
pub fn write_radix(&self, out:&mut impl Write, radix:u32)->fmt::Result;

// derive/impl: Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Default(=0)
```

---

## 4. `Rational` — required API

Always canonical (§1).

```rust
pub struct Rational { num: Integer, den: Integer }   // invariant: normalized

impl Rational {
    pub fn new(num: Integer, den: Integer) -> Rational;   // normalizes; den==0 → panic
    pub fn checked_new(num: Integer, den: Integer) -> Option<Rational>; // None if den==0
    pub fn from_integer(n: Integer) -> Rational;
    pub fn numerator(&self)->&Integer;
    pub fn denominator(&self)->&Integer;
    pub const ZERO: Rational; pub const ONE: Rational; pub const MINUS_ONE: Rational;
    pub fn power_of_two(k: i32) -> Rational;              // 2^k, k may be negative
}
impl From<i64> for Rational {}
impl From<Integer> for Rational {}
impl FromStr for Rational {}                             // "3", "-3/4", "1.5"

// predicates
pub fn is_zero(&self)->bool; pub fn is_one(&self)->bool; pub fn is_minus_one(&self)->bool;
pub fn is_positive(&self)->bool; pub fn is_negative(&self)->bool;
pub fn is_integer(&self)->bool;                          // denominator == 1
pub fn signum(&self)->i32;

// arithmetic: Add/Sub/Mul/Div/Neg + *Assign, plus:
pub fn recip(&self)->Rational;                          // 1/self; panic on zero
pub fn abs(&self)->Rational;
pub fn pow(&self, n:i32)->Rational;                     // negative n via recip
pub fn addmul(&mut self, a:&Rational, b:&Rational);
pub fn submul(&mut self, a:&Rational, b:&Rational);

// rounding to Integer
pub fn floor(&self)->Integer;
pub fn ceil(&self)->Integer;
pub fn trunc(&self)->Integer;
pub fn to_integer(&self)->Option<Integer>;             // Some iff is_integer

// integer division of rationals (quotient is an Integer)
pub fn div_floor(&self, b:&Rational)->Integer;
pub fn div_trunc(&self, b:&Rational)->Integer;
pub fn rem_euclid(&self, b:&Rational)->Rational;

// bounded conversion
pub fn fits_i64(&self)->bool; pub fn to_i64(&self)->Option<i64>;
pub fn to_f64(&self)->f64;

// display / hash
impl Display for Rational {}                           // "n" or "n/d"
impl Hash for Rational {}
pub fn write_decimal(&self, out:&mut impl Write, precision:u32, truncate:bool)->fmt::Result;

// derive/impl: Clone, PartialEq, Eq, PartialOrd, Ord, Debug, Default(=0)
```

`write_decimal` renders the value as a decimal expansion to `precision` fractional
digits; `truncate` chops (vs. rounds) the last digit. This is for human-readable
output of exact rationals that may have non-terminating expansions.

---

## 5. Free helpers

```rust
pub fn u_gcd(u: u32, v: u32) -> u32;      // binary GCD on machine words
pub fn u64_gcd(u: u64, v: u64) -> u64;
```

---

## 6. Correctness bar (tests the implementation must pass)

Property tests (randomized, many iterations):
- **Division identity** for all three conventions: `a == q*b + r`, with `r` in the
  documented range/sign for that convention, for all `a` and all `b != 0`.
- **Euclidean remainder** always satisfies `0 <= r < |b|`.
- `gcd(a,b) * lcm(a,b) == |a*b|`; `extended_gcd` returns `g == a*x + b*y`.
- **Round-trips:** `from_str(x.to_string()) == x`; `from_limbs(x.sign, x.limbs()) == x`
  for the magnitude; `from_str_radix(write_radix(x, r), r) == x`.
- **Canonical form:** after every `Rational` operation, `gcd(num,den)==1 && den>0`.
- **Small/Large agreement:** operations that cross the inline-word boundary produce
  the same result as if computed entirely in the large representation.
- **Bit tricks vs. general path:** `mul_2k(k) == self * 2^k`,
  `mod_2k(k) == rem_euclid(2^k)`, `bitnot(w)` matches the width-`w` truth table.

Edge cases to include explicitly: `0`, `±1`, `i64::MIN` and `i64::MAX` (inline
boundary), values one limb wide vs. exactly at a limb boundary, deep cancellation
in rationals, and remainder sign behavior around negative operands.

Fuzzing: feed random operation sequences and cross-check against an independent
arbitrary-precision reference (any trusted bignum, used only in the test harness,
never as a runtime dependency).

---

## 7. Implementation notes (non-normative)

The classical algorithms suffice and are well documented (Knuth, *TAOCP* Vol. 2,
§4.3): schoolbook add/sub/multiply on little-endian limb vectors, and Algorithm D
for multiprecision division. Karatsuba/Toom multiplication and sub-quadratic
division are optional later optimizations behind the same API. Base conversion for
decimal I/O is the standard repeated divide-by-`10^k` chunking. None of the
required API forces any particular internal algorithm — only the observable
results and the small-value fast path are contractual.
