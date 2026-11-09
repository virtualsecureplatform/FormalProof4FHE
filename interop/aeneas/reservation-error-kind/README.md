# Transparent reservation-error kind getter

This profile freshly extracts `TryReserveError::kind` through a small safe Rust
wrapper, using the frozen coupled Charon/Aeneas tool receipt. It includes
`alloc::collections`, so the getter and its five relevant types are transparent.
Declarations are resolved by their source identity rather than constructor-profile
type numbers. `Retained.json` keeps both function declarations and all five types.

The reifier validates the getter signature, implementation owner, generic and
local types, complete statement tree, discriminant match, field dereferences,
copy/move modes, retags, aggregate variants, storage scopes and returns. It also
checks the wrapper, Layout, alignment and niche layouts. The emitted body retains
the original match/fallthrough and early return, assignments and cleanup.

`materializedFrame` explicitly replaces the shared-reference input with its
checked loaded pointee. `invoke` first resolves the resident reference and reads
the error fields, then executes that complete source body on the materialized
value. The proof covers all valid layouts and establishes equality with
`NativeReservationErrorRead.getKind`, including failure effects and heap framing.
It composes with the existing successful-snapshot theorem. The materialization
boundary does not establish a native reference ABI, stack placement, lifetime,
compiler or physical-work refinement.

The fixture wrapper's complete reborrow/call statement tree is now validated
and executed. `WrapperProof`, `ReadyProof`, `CleanupProof`, `ProjectionProof` and
`HeapProof` compose typed entry, checked child-loan issuance, the moved argument,
source getter, copied result and explicit normal-return scope cleanup. The
successful-snapshot theorem derives the reborrow and read success and restores
the incoming lease list. Read effects, the advanced tag counter and historical
reference/birth entries remain. Rejected/partial runs preserve executed prefixes.

Scope cleanup is explicit ghost/model composition for this non-unit return; it
does not establish native Rust lifetime correspondence or alter generic unit
settlement. Connecting the original constructor error handler remains open, as
do native reference/stack/compiler/lifetime refinement, physical reclamation,
resident destruction, physical work and final security.

Run:

```sh
scripts/check-hasteboots-reservation-error-kind \
  --build-receipt build/hasteboots-extraction/inline-tools-build-b6esls36/manifest.json
```

Validation: 632 dependency audits, 55 rejecting controls and 30 examples pass.
The library, root tests, toolchain, dependencies and full-check scripts are
unchanged; the prior successful 11101-job full project check is reused.
