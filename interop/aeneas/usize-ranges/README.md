# Constrained usize storage

The original RawVec capacity uses `core::num::niche_types::UsizeNoHighBit`.
Its field is a Rust pattern type with range `0..=9223372036854775807` on
our pinned 64-bit target. `baseline.json` records the frontend rejection before
this extension. The fixture preserves that range and a separate `7..=19` range.

The experimental paired frontend now carries the unsigned scalar kind along
with both inclusive bounds. U32 behavior remains unchanged. Usize support
requires the existing monomorphic builtin shapes option; signed, u64 and
disjoint patterns remain unsupported. Extraction uses a subtype of `Std.Usize`,
not an unconstrained scalar. No backend or production Rust is modified.

```sh
scripts/check-hasteboots-usize-ranges-guards
scripts/check-hasteboots-usize-ranges \
  --build-receipt build/hasteboots-extraction/inline-tools-build-RECEIPT/manifest.json \
  --backend /tmp/hasteboots-aeneas-m0
```

The gate validates exact source ranges and the 64-bit target, checks the entire
fresh output against `Generated.lean`, and kernel-checks six preservation/bounds
proofs and all three extracted functions (nine exact dependency audits). Three
negative extractions reject u64, disjoint patterns and disabled mode. Four guard
tests reject changed bounds, admissions, missing proofs and invalid target/IR.
No proof limits are raised and only the three allowed Lean axioms are permitted.

`regression.json` records tool and source hashes and the upstream comparison:
97 completed targets, the existing `dyn.rs` rejection, and 128 byte-identical
regenerated files. All 130 extraction guard tests pass.

`probe-hasteboots-inline-constructor --cleanup-scope layout` follows the original
layout, alignment, capacity and unchecked-multiply bodies. It retains 84
functions without residual drops or missing function declarations. After range
type analysis it rejects on the original alignment enum discriminant `2^63`,
which overflows the frontend's OCaml `int` representation. Pattern casts,
layout interpretation, pointer provenance, heap operations, physical work and
the native constructor/security refinement remain unproved.
