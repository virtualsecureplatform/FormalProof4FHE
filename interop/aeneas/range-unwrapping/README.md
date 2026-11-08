# Outward constrained scalar unwrapping

The original `core::num::niche_types::UsizeNoHighBit::as_inner` transmutes a
transparent wrapper around `usize is 0..=9223372036854775807` to usize.
`baseline.json` records rejection of the same operation before this extension.
The fixture uses optimized MIR, matching the external standard-library body;
earlier MIR retains an intrinsic call instead of the transmute operation.

The opt-in monomorphic frontend now supports outward conversion from a valid
U32/Usize range value to its exact scalar base. It extracts `Subtype.val`, so
all original scalar values are preserved. A prepass decomposes a wrapper only
when it is closed, transparent, inhabited, has one range field at offset zero,
no alignment modifier, and matching size/alignment for the single 64-bit
little-endian target. The original Copy/Move projection is retained. Other
transmutes remain unsupported; in particular no scalar-to-range validity proof
is inferred and no cross-width conversion is introduced.

```sh
scripts/check-hasteboots-range-unwrapping-guards
scripts/check-hasteboots-range-unwrapping \
  --build-receipt build/hasteboots-extraction/inline-tools-build-RECEIPT/manifest.json \
  --backend /tmp/hasteboots-aeneas-m0
```

The gate freshly extracts the complete fixture, checks MIR/target/layouts and
the full output snapshot, then kernel-checks all three source functions and six
exact value/bounds theorems (nine dependency audits). Eleven negative runs reject
nontransparent, reverse, wrong-width and plain wrappers, disabled mode and six
explicitly corrupted layout/target artifacts. Accepted IR is never rewritten.
Four guard tests reject changed output, missing proofs and invalid MIR/layouts.
No backend or production Rust is modified, and no proof limits are raised.

The native layout trace now passes the original `as_inner` transmute and rejects
at `ub_checks<bool>`, the compiler configuration query in original unsafe
precondition checks. Its 84 functions have no residual drops and no missing
regular declarations. The query must be tied to actual compiler configuration;
it has not been replaced by a free Boolean. Large usize literal handling,
remaining layout operations, pointer/heap/work refinement and the complete
native constructor/security theorem remain open.

The prior 67 dependency audits passed again, for 76 across the paired profile.
All 138 extraction guard tests passed. Full upstream extraction completed the
same 97 targets with the existing `dyn.rs` rejection; all 128 regenerated files
are byte-identical. `regression.json` records paired tools, source patches,
complete audit coverage, negative cases and per-file comparison hashes.
