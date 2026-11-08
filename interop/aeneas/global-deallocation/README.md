# Original Global allocator zero/nonzero dispatch

This profile interprets the complete ordinary-sysroot `Global` implementation of
`Allocator::deallocate`, including its original usize switch, zero-size skip,
nonzero external call, early return, unwind and storage markers. The fixture
uses the nightly `allocator_api` feature to reach the original method; production
Rust and compiler/backend sources are unchanged. All retained declarations keep
their original classifications. The external deallocator remains the checked
logical specification used by the earlier caller profile.

`NativeZstReference.decode` selects an existing shared zero-byte/alignment-one
lease through a reference-register index. It accepts no supplied tag, origin or
extent and mints no loan. Three theorems establish the exact resident lookup,
completeness and registration. `NativeRecordLLBC.Input.zstSharedReference` uses
that decoder. Seven regressions reject missing/revoked, exclusive, nonzero and
wrong-alignment loans and check successful argument decoding.

The reifier checks the original empty `Global` structure's zero-byte extent and
alignment one. It validates the declared lifetime parameter, signature and body
region indices before comparing types with regions erased in the logical model.
That validation is not a Rust lifetime-erasure theorem. It preserves the source
single-label usize switch as executable data, including its original default
branch. Existing public-deallocator reification remains unchanged.

Twelve source theorems establish entry/decoding, the exact zero return, nonzero
success/rejection, decoded invocations, and the two possible normal outcomes:
zero returns the original world; nonzero removes exactly one live allocation.
The zero branch is derived from the original source switch. It supplies no
successful substitute for a failed nonzero free. Ten regressions exercise both
branches, missing arguments, invalid alignments, stale references, address-only
pointers, double frees and active data borrows.

Reproduce:

```sh
scripts/check-hasteboots-global-deallocation \
  --build-receipt build/hasteboots-extraction/inline-tools-build-b6esls36/manifest.json
```

The gate reruns the earlier allocator caller profile, re-extracts this fixture
with the same frozen compiler tools, compares all retained functions/types and
emitted code, rejects malformed regions, types, layouts and dispatch tables, and
audits model/source dependencies. A changed switch label from zero to one is
checked to retain a one-byte allocation; disabling an inert alignment retag
changes code and preserves the original proofs/regressions.

The shared reference and aggregate arguments are logical representations. Native
calling conventions, Rust lifetime/compiler correspondence, the external
allocator implementation, RawVec/Vec destruction and physical attacker work
remain unproved. The wrapper's construction of the Global reference is not
interpreted by this profile. The whole native constructor and final protocol
security theorem remain open. Unit cleanup remains explicit ghost composition.
