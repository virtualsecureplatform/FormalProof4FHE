# Locked native NTT root and arithmetic regression

Run from the FormalProof4FHE repository:

```sh
CARGO_TARGET_DIR=build/native-ntt-roots cargo run --locked --manifest-path scripts/native-fixtures/ntt-roots/Cargo.toml
scripts/in-container lake env lean -DwarningAsError=true FormalProof4FHETest/HasteBootsConcreteNTTRootSmoke.lean
scripts/in-container lake env lean -DwarningAsError=true FormalProof4FHETest/HasteBootsConcreteNTTArithmeticSmoke.lean
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
comparisons/shifts or Rust compilation. Connecting the word-level Tonelli-Shanks
and root-construction loops to the earlier field semantics is also still open.
