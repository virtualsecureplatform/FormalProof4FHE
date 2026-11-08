# Source Layout and explicit 64-bit words

The historical three-function baseline in `baseline.json` exposed two independent
failures: the assumed Layout used the backend's old pointer-alignment carrier,
while actual source getters used `core::mem::alignment::Alignment`; portable usize
literals also failed the conservative 32-bit bound. The fixture now additionally
covers source word limits, signed identity and signed/unsigned overflowing addition.

The experimental monomorphic Lean profile emits the original source Layout fields
instead of the legacy assumed Layout. An explicit `-target-word64` option requires
monomorphic Lean and exactly one 64-bit little-endian target. It translates usize,
isize, scalar literals, enum discriminants, patterns and constrained carriers to
U64/I64. It disables assumed function/global/effect bindings, so source methods and
word constants must have extracted bodies. Existing portable profiles keep their
original scalar representation. This is an experimental extraction profile, not a
compiler-correctness theorem or general support for all target-dependent bindings.

The interpreter now types AddChecked as an integer/Boolean pair; Lean extraction
uses the existing closed `UScalar.overflowing_add` or `IScalar.overflowing_add`
definition. The original stdlib overflowing-add methods, including their casts,
are retained. No generated computational term is rewritten. The gate adjusts only
the compatibility imports needed by the pinned Lean backend.

Twelve kernel theorems establish exact preservation and size, alignment reads for
all 64 source variants, the high alignment bit, actual unsigned maximum and signed
minimum, signed identity, and signed/unsigned overflowing addition for every input.
Boundary theorems cover unsigned wraparound, addition above 2^63 and signed wraparound.
Every generated definition/global, the enum reader, each theorem and its aliases
are dependency-audited: 36 checks, using only propext/Classical.choice/Quot.sound.
Proof limits remain 200000 heartbeats and recursion depth 1000.

```sh
scripts/check-hasteboots-layout-word64-guards
scripts/check-hasteboots-layout-word64 \
  --build-receipt build/hasteboots-extraction/inline-tools-build-RECEIPT/manifest.json \
  --backend /tmp/hasteboots-aeneas-m0
```

Seven negative runs check missing monomorphic mode, 32-bit, big-endian, missing or
multiple target metadata (explicit negative fault injections), portable kernel
word-bound rejection, and original checked_add. The latter extracts the original
unlikely body but leaves the compiler intrinsic cold_path opaque. Its single
unresolved axiom is inventoried and rejected, not admitted as a no-op. Four guard
tests check incomplete bodies, target/layout changes, altered widths/source fields,
admissions and missing universal/boundary proofs.

`probe-hasteboots-inline-constructor --cleanup-scope nonzero --target-word64`
generates a complete original constructor module with 84 retained functions and
no residual drops/runtime queries or missing regular declarations. It still
rejects 22 opaque declarations, now exposing arithmetic helpers/constants that
previously used assumed bindings, alongside runtime checks, pointers, layout
initialization and deallocation. Its exact inventory is in `regression.json`.
The increase from fourteen is an expanded source-binding obligation, not progress
on closure. The legacy portable ctlz runtime is not injected in word64 mode.

The mathematical Layout structure alone does not prove Rust's rounded-size
invariant or allocator/caller validity. Pointer provenance, source heap behavior,
NTT/SIMD/scheduler refinement, oracle/lifetime ownership, BabyBear and the final
128-bit expected-work security theorem remain open. These getter/word theorems do
not certify a native constructor or physical attacker-work bound.
