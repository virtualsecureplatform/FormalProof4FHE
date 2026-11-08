# RawVec current-memory enum payload frontier

This profile reifies the logical enum schema returned by the original ordinary
sysroot `alloc::raw_vec::current_memory`. It supplies the payload operations
needed before that function and its caller can enter the interpreter. It does
**not** translate either body or prove native Vec destruction.

The fixture uses an ordinary scoped `Vec<u8>` drop. Fresh Charon extraction with
the frozen tool receipt retains Vec/RawVec destruction, `current_memory`, Global
deallocation and the external allocator leaf. The result declaration is the
original **Foreign** `Option<(NonNull<u8>, Layout)>`; this classification is
preserved, and no foreign helper is promoted to an interpreted Rust body.

`NativeVariantValues` separates nominal type identity, variant index and signed
source discriminant. It checks complete, typed payload construction and active
variant projections. Moving a selected field inserts an explicit hole. Ten
lemmas prove construction/projection witnesses, selected completeness and pointer
leaf preservation, consumed reads, and unchanged discriminants after moves.
Nineteen model regressions include incorrect tags, variants, fields, null pointers,
repeated moves, surviving sibling reads and a negative source discriminant.

`Generated.lean` derives the source schema directly from the function's output
type and its reachable payload declarations. It retains their distinct nominal
IDs, including the specific Layout/Alignment instance returned by this function.
The original alignment enum's 64 values are checked. `Proof.lean` adds five
source-schema theorems, and `Smoke.lean` adds ten regressions using a pointer with
allocation identity and generation and the actual nested Layout payload.

The retained physical enum has size 24, alignment 8 and a niche discriminator at
offset 8. That discriminator is **not** the signed source discriminant. Physical
discriminator/tagger and field metadata stay in `Retained.json`; no byte decoder
or native enum ABI theorem is asserted. The gate detects changes to this metadata
through the retained snapshot.

Run:

```sh
scripts/check-hasteboots-rawvec-option \
  --build-receipt build/hasteboots-extraction/inline-tools-build-b6esls36/manifest.json
scripts/check
```

The profile gate passed 56 dependency audits and 18 rejecting controls. A supported
source-discriminant mutation from 1 to -7 changes the generated schema and passes
Lean evaluation while retaining variant index 1. A separate physical-metadata
control changes the niche offset and confirms the retained snapshot changes.
See `regression.json` for receipt and full-project validation evidence.

Next, connect these payload operations to actual enum construction, discriminant
switches and variant projections in the LLBC interpreter. Reify the original
`current_memory` body with checked resident-reference field reads: pointer fields
must recover shadow provenance, and capacity fields must use actual byte loads.
Handle the retained constrained-capacity carrier and unchecked multiplication
with their actual validity conditions, and preserve inactive helper branches and
original helper classifications. Then compose original RawVec deallocation and
Vec destruction with the checked Global branches. Rust lifetime/compiler correspondence, the external allocator
contract, physical-work refinement and the full expected-work security theorem
remain open. This logical schema introduces no successful allocator stub, caller
work certificate or constructor-acceptance claim.
