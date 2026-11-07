# Locked native NTT root, arithmetic and limb regression

Run from the FormalProof4FHE repository:

```sh
CARGO_TARGET_DIR=build/native-ntt-roots cargo run --locked --manifest-path scripts/native-fixtures/ntt-roots/Cargo.toml
scripts/check-native-ntt-limb-fixtures
scripts/in-container lake env lean -DwarningAsError=true FormalProof4FHETest/HasteBootsConcreteNTTRootSmoke.lean
scripts/in-container lake env lean -DwarningAsError=true FormalProof4FHETest/HasteBootsConcreteNTTArithmeticSmoke.lean
scripts/in-container lake env lean -DwarningAsError=true FormalProof4FHETest/HasteBootsConcreteNTTWordRootSmoke.lean
scripts/in-container lake env lean -DwarningAsError=true FormalProof4FHETest/HasteBootsConcreteNTTLimbSmoke.lean
scripts/in-container lake env lean -DwarningAsError=true FormalProof4FHETest/HasteBootsConcreteNTTInitializationSmoke.lean
scripts/in-container lake env lean -DwarningAsError=true FormalProof4FHETest/HasteBootsConcreteNTTInitializedRootSmoke.lean
```

The Cargo dependency is pinned to the same `concrete-ntt` commit used by
HasteBoots: `cdeba793e46208320b30d78be19f7be78d49016a`. The fixture directly
calls `prime64::Plan::try_new` and checks five root literals, a too-small
plan domain, and an unsupported root order. The Lean smoke checks the same
five root literals through the field semantics of `roots.rs`, plus the
inner search, early exits, square inputs and failed construction.

`ConcreteNTTSquareRoot` and `ConcreteNTTRootConstruction` prove soundness of
successful field-semantic returns. They do not prove that all admissible
inputs succeed. These semantics cover `roots.rs`, not the complete plan
constructor: for example, its minimum plan size of 16 is a separate gate.
The field semantics map unsuccessful square-root exits and failed native
assertions to rejection; they do not identify panic with a native error.

This regression is not a Rust/Lean refinement proof. `Div64`, modular integer
operations, checked casts/shifts, the plan's stored root and twiddle arrays,
cache/concurrency behavior, SIMD kernels and physical work still need explicit
refinement. No alternative checked-root backend replaces the native path.

The fixture also directly probes native `Div64::rem_u128`, `mul_mod64` and
`exp_mod64`: 35 remainder cases, 175 multiplication cases and 210 power cases.
The references use Rust u128 `%` and an independent reduced-power accumulator.
The Lean arithmetic smoke uses the same divisor/base/exponent lists, checks
against natural remainder and ZMod power, and exhausts 128 small inputs for
31 divisors. Inputs include maximum u128/u64 words, noncanonical bases,
power-of-two and composite divisors, and zero/maximal exponents.

`ReciprocalRemainder` proves the mathematical reciprocal formula.
`ConcreteNTTDiv64` retains the wrapped reciprocal and high-product extraction
formula and proves it computes the canonical remainder on these word domains.
`ConcreteNTTModularPower` retains the literal exponentiation control flow using
that reducer and proves its canonical modular-power value. These results do not
yet refine the actual u256 limb operations, division, wide multiplication,
comparisons/shifts or Rust compilation. `ConcreteNTTWordSearch`, `ConcreteNTTWordSquareRoot` and
`ConcreteNTTWordRootConstruction` now connect those natural-word loops to the
field semantics, preserve assertion failure distinctly from no-root rejection,
and derive canonical successful roots and primitive order. Their eight smoke
groups include the same five native-plan root literals. Actual limb/instruction,
plan/cache and Rust refinement remains open.

The native limb checker compares every emitted result with independent Python
arbitrary-precision integers: 35 u256-by-u64 products (all 320 result bits),
42 wrapping u256-by-u128 products, and 49 overflowing additions. It requires the
complete expected input set, rejects duplicates or malformed/non-word records,
and refuses to run with Python assertion optimization enabled.

`ConcreteNTTLimbArithmetic` and `ConcreteNTTLimbAdd` model the literal bounded
multiply/carry and two-overflow-flag add routines. `ConcreteNTTU256Mul64`,
`ConcreteNTTU256Add` and `ConcreteNTTU256Mul128` prove their original ordered
limb compositions, wrapping values, overflow flag and complete remainder
formula. Its initialization relation is now derived by the literal limb
reciprocal-division/initialization semantics described below; actual Rust machine
refinement remains open. The nonwrapping u256-by-u128 high-result routine,
actual machine/compiler, native plan/cache and physical refinements remain open.

The checker additionally verifies 49 native `div_rem_u256_u64` outputs and seven
`Div64::new` retained reciprocal states, for 182 native limb/initialization cases.
All are compared with Python full-integer division and reciprocal formulas.
`ConcreteNTTU256Division` proves the literal high-to-low steps and their cast
bounds. `ConcreteNTTDiv64Initialization` derives both stored reciprocals from the
actual word-formula constructor and preserves zero/one assertion failure.
`ConcreteNTTInitializedPower` retains that one state across every modular product.
Its public new/remainder/product/power results need no supplied initialization
or arithmetic certificate. Actual machine division/casts, bit assembly,
compiler/Rust, native plan/cache and physical refinement remain open.

`ConcreteNTTInitializedSearch`, `ConcreteNTTInitializedSquareRoot` and
`ConcreteNTTInitializedRootConstruction` now retain the constructed Div64 state
through the complete root algorithm. Their public `newRoot` performs one
word-formula initialization, preserves assertion/no-root outcomes, and derives
canonical successful roots and primitive order. Eight smoke groups compare the
same five native root literals and exercise complete small-field search/square
root behavior, invalid divisors, unsupported orders and noncanonical inputs.
Native plan preflight/storage, cache provenance, machine/compiler and physical
refinement remain open; these results do not substitute a different native
backend or add root validation gates to HasteBoots.

The fixture also emits the locked `prime::is_prime64` result for every input
below 200, Goldilocks, BabyBear, u64::MAX, 341550071728321 and
3825123056546413051 (205 cases). The checker uses independent small trial
division, the kernel prime facts in NativeFields, and explicit proper divisors
for the large composites. It does not use Miller–Rabin as its reference.
The new Lean gate proves prime-input completeness and both native prime gates;
it does not prove the converse for arbitrary u64 inputs. Native machine counter
bounds, full Plan storage/cache and compiler/physical refinement remain open.

The five actual plans now emit all 2,240 `root_powers()` entries. The checker
requires every (modulus, size, index) exactly once, enforces canonical range and
compares each value with independent Python `pow(root, index, modulus)` using
the established native root literals. Lean's checked array-write model proves
these exact powers and write safety; the Goldilocks constructor prefix derives
its stored root/state and array contents internally. This still leaves the
original twiddle arrays, constants, complete Plan allocation/storage, cache and
machine/physical refinements open; no full Plan result is claimed.

The fixture now exercises the private native twiddle arrays through actual
Goldilocks `Plan::fwd`, `inv`, and `normalize` at N=32 and N=1024, for monomial
degrees 0, 1, N/2 and N-1. All 4,224 forward values are checked against independent
Python bit-string reversal and polynomial evaluation. All 4,224 normalized
inverse values must recover the original monomials; every case is required once
and canonical range is enforced. These are regression cases, not a general
native transform/compiler/SIMD proof. Lean now proves the non-Shoup paired-array
writes, source-word index permutation and separately initialized root/state,
composed with the earlier Goldilocks constructor prefix. Full Plan constants,
reverse-index assembly, allocation, cache and machine/physical refinement remain
open.
