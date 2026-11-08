# Original allocator caller over nominal aggregate locals

This profile interprets the complete original `alloc::alloc::dealloc` body
(function 2 of the [deallocation fixture](../byte-deallocation/fixture.rs)).
It retains the original `Layout` field reads, raw-pointer-to-`NonNull` conversion,
retag flags, constant branch, regular calls, unwind blocks, storage markers and
return. Field paths check their original nominal owner and declared field type.
The ordinary sysroot/compiler extraction remains unchanged.

`NativeRecordValues` represents nominal records, pairs, enum discriminants and
partial moves. A moved field becomes uninitialized; its siblings remain readable
and a whole aggregate with a hole cannot be copied. Six theorems prove complete
reads, selection from existing scalar leaves, exact replacement and consumption
of moved fields. `NativeRecordLLBC` supplies typed locals, checked aggregate
inputs, field copy/move, field-order retagging with retained failed prefixes,
finite calls, constant and usize branches, explicit unit-return cleanup and the
checked external deallocation leaf. Thirteen theorems prove local-state framing,
machine-run projection and invocation reachability. Mutable references cannot
be copied through an aggregate.

The source proofs establish exact argument decoding and entry, caller success
and rejection, decoded invocation success, and removal of exactly one allocation
for every normal caller return. Success uses actual reachable machine states and
the computed checked free; no caller result or work certificate is supplied.
Twenty model regressions check fields, moves, nominal tags, enum/non-null
constraints, copy restrictions, partial retag failure and both usize branches.
Eight source regressions exercise successful invocation, wrong layouts, missing
pointers, zero size, active loans, double frees and address-only pointers.

The original precondition declaration (function 3) remains `Foreign`, with its
unavailable body retained. If reached, it produces an explicit unsupported
result. The original compiled constant-false branch never calls it. Function 4
retains its original external declaration and uses the
[checked logical deallocation specification](../byte-deallocation/README.md).
It is not reclassified as a transparent Rust implementation.

Reproduce:

```sh
scripts/check-hasteboots-allocator-caller \
  --build-receipt build/hasteboots-extraction/inline-tools-build-b6esls36/manifest.json
```

The gate reruns the deallocation parent and uses that fresh, hashed extraction
from the same frozen tools. It compares original functions/types and generated
code, checks rejecting controls, and audits every explicit model/source
declaration. Disabling an original inert retag changes emitted code and preserves
the proofs/regressions. Enabling the retained guard changes execution: the gate
checks that it reaches the foreign unsupported result before deallocation.

These aggregates are logical typed locals. Their Rust byte layouts, native ABI
and wrapper representation correspondence remain unproved. This does not yet
interpret `deallocate_bytes`'s unavailable `Layout::from_size_align_unchecked`
callee, the allocator trait implementation, `RawVec`/`Vec` destruction or the
whole native constructor. Rust lifetime/compiler correspondence, native external
allocator correctness, physical work and the final protocol security theorem
remain open. Unit cleanup continues to be explicit ghost composition.

The [Layout storage profile](../layout-storage/README.md) now bridges retained
physical field descriptions and permission-checked resident bytes to these
logical arguments, including the extracted source getters. Native calling
convention/compiler/lifetime correspondence remains open.
