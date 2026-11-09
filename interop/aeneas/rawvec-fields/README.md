# Checked resident RawVec field reads

This profile binds the retained `RawVecInner` storage geometry to actual
reference-machine byte and pointer-shadow reads. It does not translate the
original RawVec function body or prove a native reference/ABI correspondence.

`NativeRawVecFields.select` chooses an existing reference register and resident
shared lease for exactly sixteen bytes at alignment eight. No extent, tag or
pointer origin is supplied by the caller, and the selector mints no loan.
`capacity` executes an aligned eight-byte read at offset zero, decodes the actual
little-endian bytes and checks the high bit. `pointer` executes a shadow-aware
pointer load at offset eight and checks the recovered address is nonzero.
Integer bytes alone do not recover an allocation origin. Mixed shadow fragments
reject, and address reuse preserves the old stored generation.

Fourteen model theorems prove reference selection, projection into actual reference
execution, reachability, successful read witnesses, exact byte/shadow effects and
failure prefixes. Successful reads preserve the heap, allocation history, loan
counter, lease ledger, reference registers and birth history. Capacity reads
prepend actual output bytes and a scratch pointer; pointer loads prepend the
scratch and recovered pointers without changing byte outputs. Rejecting a
high-bit capacity or null pointer retains the already executed read.

Twenty-four model regressions exercise ordinary and zero capacities, the upper
valid boundary, high-bit rejection, complete provenance, origin-free integer
bytes, mixed shadow fragments, missing/revoked/wrong-layout/wrong-mode leases,
null pointer prefixes, deliberately cleared bytes under a retained resident
lease, and address reuse with a new allocation generation. The cleared-byte
case is a defensive altered-state test, not a claim that Rust can legally
uninitialize a live shared referent. Five source-wrapper regressions check the metadata-bound
readers. Seven source theorems bind source offsets and alignment to the executed
operations and expose the checked bound, shadow origin and failure prefixes.

The reifier starts from the original `current_memory` self-reference type and
checks the full retained layouts of RawVecInner, Unique, NonNull, the capacity
carrier, Global and PhantomData. In particular the source field order is
pointer/capacity/allocator, while physical offsets are 8/0/16. Unique and NonNull
transparently place the pointer at offset zero; the other Unique field is zero
bytes. Original Foreign and Opaque classifications stay in `Retained.json`.

The capacity reader's high-bit guard is a checked policy. The LLBC carrier is
Foreign/Opaque and its native validity range is not derived by this profile.
No native validity, ownership or transmute theorem for that carrier is asserted.

Run:

```sh
scripts/check-hasteboots-rawvec-fields \
  --build-receipt build/hasteboots-extraction/inline-tools-build-b6esls36/manifest.json
scripts/check
```

The profile gate was revalidated with 36 dependency audits and twenty rejecting controls,
including shifted fields, wrong extents/alignment, changed classifications,
invented carrier fields, nullability changes and hidden layout effects. It uses
a fresh extraction with the frozen tool receipt and compares the retained source
snapshot. The final `scripts/check` run passed its 11,006-job build and all
subsequent smoke checks with the strengthened cleared-byte regression included.
See `regression.json` for receipts and log hashes.

The [reference profile](../rawvec-reference/README.md) now connects these readers
to stable reference operands and interprets the original Vec capacity projection.
It resolves stable tags against the current reference registry and preserves
complete-object reborrows and their layout. Its regression file records the
latest storage-gate revalidation. Translate the original `current_memory` body with its
zero branches and unchecked product, then compose the original deallocation and
Vec destruction calls with Global dispatch. Preserve the source's lazy branches:
a path that does not use the pointer must not load it merely to build a snapshot.
Native stack/layout/ABI and lifetime/compiler correspondence, constrained-carrier
validity, allocator correctness, physical work and the final expected-work
security theorem remain open. No constructor acceptance or work certificate is
supplied by these readers.
