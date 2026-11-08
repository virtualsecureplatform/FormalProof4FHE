# Original slice-reference bodies

This experimental Charon-to-Lean profile retains the original optimized bodies
of `core::slice::{from_raw_parts,from_raw_parts_mut}` instantiated for `u8` and
`u64`, and four monomorphic probe wrappers. It extends the scalar body profile
with fat-pointer construction, pointer-bound metadata and reference creation.
It does not extend Aeneas or establish compiler correctness.

The native constructor extraction currently stops at a byte-slice reference
creation inside retained `Vec<u8>::drop`, before its call to slice drop glue.
This profile covers that operator form, not the full destructor or constructor.
The wrappers use `'static` solely to force monomorphic extraction. Their return
types are not evidence that the returned references have valid Rust lifetimes.

The supported compiler configuration explicitly uses `-Cdebug-assertions=no`.
Original constant-false UB-check branches remain in the generated body.
Unsupported inactive statements become explicit halting nodes keyed to their
complete original JSON in `Retained.json`; they are never interpreted as no-ops.
The gate separately extracts the debug-enabled configuration and requires its
active unsupported checks to be rejected.

`NativeSliceLLBC` interprets source local storage, moves, calls, constant
branches, raw slice parts and shared/mutable reference creation. Its external
inputs select existing raw registers and provide lengths. Reference creation
executes the existing closed reference machine on its single shared heap;
callers cannot supply fresh provenance or lease tags. Byte layouts have size
and alignment 1; word layouts have size and alignment 8. Source equations prove
the exact constructor and wrapper behavior. Successful constructor results
identify the executed borrow and its resident fresh lease. Every outcome
projects to an actual reference-machine run, including failure prefixes.

All source reference sites create distinct tags: the shared wrapper creates two
leases and the mutable wrapper four. Local storage death does not end those
leases. The tests exercise parent/child cleanup ordering, access permissions,
byte alignment, range overflow and empty/uninitialized allocation behavior.
Source lifetime-ending instrumentation, Rust aliasing, heap-stored references,
typed caller refinement and whole native destructor behavior remain open.

Reproduce with the frozen compiler receipt:

```sh
scripts/check-hasteboots-slice-reference-body \
  --build-receipt build/hasteboots-extraction/inline-tools-build-b6esls36/manifest.json
```

The gate re-extracts both compiler configurations, compares source snapshots,
checks rejecting controls and a supported syntax mutation, and runs the Lean
source proofs, regressions and dependency audit. Proof dependencies are limited
to `propext`, `Classical.choice` and `Quot.sound`. This milestone supplies no
cryptographic soundness or attacker-work conclusion.
