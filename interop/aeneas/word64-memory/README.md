# Initialized range stores and word64 heap values

`NativeByteRangeWrite` writes actual byte lists into one live allocation.
It checks full geometry, alignment, origin and bounds before replacement.
Each byte becomes initialized; bytes outside the span remain unchanged.
Allocation shape, count and generation are preserved. A successful checked
store reads back exactly its input, and well-formed allocation checks derive
store execution even for previously uninitialized bytes. Positive stale-origin
writes reject after deallocation. Empty stores retain geometry checks.
Under the checked geometry, single-byte range stores agree with the existing
byte-store primitive.

Raw and tagged wrappers check conflicts over the entire accessed span. Tagged
writes require exclusive mode and checked offsets. The transition extension
includes every previous byte-ledger transition, preserves well-formedness from
the empty state and keeps ended tags revoked through arbitrary extended runs.
These policy transitions carry no physical instruction, cost or native atomicity
interpretation. No operation here supplies an attacker-work floor.

`NativeWord64Memory` encodes all u64 bit patterns as exactly eight little-endian
bytes, checks eight-byte alignment, and performs concrete range stores/loads.
Both codec round trips and exact byte-read correspondence are proved. Slice
metadata stays an element count: checked byte extents and element offsets use
natural-number multiplication by eight before any address conversion. Extent
and alignment failures reject; constructors grant no access by themselves.

Thirty-seven range-store and sixteen word-memory theorems establish these facts.
Persistent root audits cover all 69 new model declarations. Twenty-four executable
regressions include uninitialized buffers, all-one/zero words, byte order,
misalignment, extent failures, deallocation/reuse, parent/child conflict and
framing, stale tags, huge metadata, and correct element addressing.

The fixture retains the original standard-library shared/mutable u64 slice
pointer constructor bodies. Original `size_of::<u64>()` and `align_of::<u64>()`
constants are evaluated by rustc, retained in the source IR, and extracted
through the checked literal-constant profile. Seven source theorems prove the
constructors and the actual layout witnesses (8,8). Eight composition theorems
connect source pointer data, scalar bits, checked word extents, elements and
model store/load behavior. Decoding changes only a phantom pointee index; the
backend's platform-dependent slice value is never read or reinterpreted.

```sh
scripts/check-hasteboots-word64-memory-guards
scripts/check-hasteboots-word64-memory \
  --build-receipt build/hasteboots-extraction/inline-tools-build-RECEIPT/manifest.json \
  --backend /tmp/hasteboots-aeneas-m0
```

The combined gate audits all 116 model/source/runtime/bridge declarations and
reruns the literal constants, pointer-parts and local reborrow gates with their
source/heap dependencies. Only the three standard Lean axioms are allowed.

These are scalar u64 values and source pointer/layout witnesses. This does not
identify Rust's Goldilocks wrapper or arbitrary structs/enums/pointers with u64
memory, implement pointer-provenance storage, or prove actual Rust reference
creation, ownership, lifetime or alias semantics. Native allocator/destructor/
deallocator, compiler/caller and NTT/SIMD/scheduler refinement remain open.
The original native raw-pointer dereference remains rejected. Causal lifetime
oracle/owner coverage, BabyBear and the final 128-bit expected physical
attacker-work theorem remain open. The production Rust and Lean backend are
unchanged; the compiler change is confined to opt-in evaluated integer constants.
