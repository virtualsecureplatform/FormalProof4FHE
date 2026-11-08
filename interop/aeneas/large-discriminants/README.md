# Arbitrary-precision enum discriminants

The original 64-bit Alignment enum contains `_Align1Shl63 = 2^63`.
Aeneas previously converted source discriminants through OCaml `int`, raising
`Z.Overflow` before extraction. `baseline.json` records this failure on
`fixture.rs` before the fix. The paired experimental frontend now retains the
existing arbitrary-precision source integer through its pure IR, compares
ordinal values with `Z.equal`, and prints with `Z.to_string`. Variant indices
remain ordinary indices; discriminant values are preserved separately.

`wide.rs` exercises fixed-width u64/u128 values beyond the host integer range,
including `2^63`, `2^64 - 1` and `2^128 - 1`, and original enum casts.
`WideGenerated.lean` is the complete generated module. Eight kernel theorems,
three source functions and two generated discriminant readers passed thirteen
exact dependency audits using only the allowed Lean axioms.

```sh
scripts/check-hasteboots-large-discriminants-guards
scripts/check-hasteboots-large-discriminants \
  --build-receipt build/hasteboots-extraction/inline-tools-build-RECEIPT/manifest.json \
  --backend /tmp/hasteboots-aeneas-m0
```

The gate checks exact IR variants, scalar kinds and discriminant values,
compares complete fresh modules to snapshots and audits every proof/source
function and generated reader. Four guard tests reject truncated values,
changed output, admissions, missing enums/proofs and disabled mono mode.
No proof limits are raised and no backend or production Rust is modified.

`fixture.rs` also retains the original large usize case. It now translates to
`Generated.lean`, but the complete module must still reject in Lean: the
backend's `#usize` notation uses a portable 32-bit conservative bound. The gate
requires this rejection and checks the specific literal failure. This is not an
accepted usize model, target-width substitution or a native constructor proof.

The previous 54 dependency audits passed again, for 67 across this profile.
All 134 extraction guard tests passed. Full upstream extraction completed 97
targets with only the existing `dyn.rs` rejection, and all 128 generated files
are byte-identical to the preceding profile. `regression.json` records the
paired tools, patch, audit and output hashes.

The original native `--cleanup-scope layout` trace now passes the large enum
conversion and rejects at the actual `UsizeNoHighBit::as_inner` transmute to
usize. It still has 84 functions, no residual drops and no missing regular
function declarations. Faithful pattern/transparent-wrapper representation,
large usize literal handling, layout/pointer/heap/work semantics and complete
security refinement remain open.
