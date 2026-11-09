# Retained empty byte Vec constructor

`fixture.rs` calls the original `Vec::<u8>::new`. `Generated.lean` reifies that
caller and constructor; `Retained.json` preserves both complete source function
declarations, ten nominal types, the evaluated alignment global and target.
`Proof.lean` and `Smoke.lean` are concatenated after the generated file by the
gate rather than compiled as independent Lean modules.

The six theorems establish exact nominal return values for every incoming world,
canonical invocation, zero capacity and length, a dangling address of one without
allocation provenance, and rejection of positive reads through that pointer.
The incoming world is unchanged, including its heap, registered pointers and
loans. Four regressions cover populated input worlds, arbitrary returned fields,
a live allocation at the same numerical address, and direct constructor invocation.

The pure `NativeRecordLLBC.Operand.addressLiteral` supports the retained alignment
to NonNull transmute. It does not create an allocation origin. The reifier checks
64 physical alignment discriminants, byte alignment, exact nominal layouts,
constrained capacity, operand types, field move/copy modes and the closed call
graph. Changed source bodies must reproduce the tracked generated program and
retained declarations exactly. Seventeen negative controls exercise those guards.
All 291 audited declarations use only the permitted standard Lean dependencies.

Run with the coupled tool receipt:

```bash
scripts/check-hasteboots-vec-empty \
  --build-receipt build/hasteboots-extraction/inline-tools-build-b6esls36/manifest.json
```

The gate freshly extracts the source, compares generated and retained files,
runs rejecting controls, checks the proofs and regressions with warnings as
errors, audits dependencies, and records source, input and log hashes in its
ignored build manifest. `regression.json` records the checked milestone.

Native aggregate storage/ABI and the bridge from this nominal value to the
resident Vec descriptor remain open. This profile does not prove positive
allocation constructors, compiler/lifetime refinement, external allocation,
physical attacker work or the final HasteBoots security theorem.
