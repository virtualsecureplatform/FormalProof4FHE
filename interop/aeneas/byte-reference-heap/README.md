# Extracted byte accessors and current heap views

`NativeByteRangeUpdate.lean` proves eleven laws about the existing executable
allocation store and borrow ledger. A successful store within an initialized
range changes that range's current bytes by exactly `List.set`. This includes
ranges starting inside an allocation, arbitrary selected offsets and allocation
list positions. Byte loads and successful one-byte ledger reads agree with the
same current range view. Store success is derived from a valid initialized
range; checked exclusive ownership, bounds and per-access conflict tests then
derive ledger write execution. The module introduces no replacement memory
operations or heap certificates.

`Bridge.lean` connects these facts to both unedited safe-reference accessors
in `../byte-reference/Generated.lean`. Byte encoding/decoding are inverse.
`observe` computes a logical slice from the current initialized range and
checks the 64-bit length bound; successful range execution derives that bound.
`Represents` relates the slice's decoded bytes to the current memory range.
A successful ledger read returns the same byte as the source accessor.
An authorized ledger write executes, the source accessor succeeds with the
same list update, and that updated slice represents the actual resulting heap.
Nine source/encoding theorems establish these properties.

The whole-range observation is ghost state, not a full-range borrow access.
Permissions are tested on the selected physical byte. A parent may therefore
write outside a child's span while the logical parent slice still represents
the whole range. Nine executable root cases cover this distinction, overlapping
access rejection, child updates, interior views, non-head allocations and
other-allocation preservation. The source slice contains current heap bytes;
it is not a stale copy captured at borrow acquisition.

```sh
scripts/check-hasteboots-byte-reference-heap-guards
scripts/check-hasteboots-byte-reference-heap \
  --build-receipt build/hasteboots-extraction/inline-tools-build-RECEIPT/manifest.json \
  --backend /tmp/hasteboots-aeneas-m0
```

The combined gate audits all 50 model/bridge/source/runtime declarations and
reruns the original-source byte-reference and byte-borrow gates, including
range, memory and source pointer dependencies. The root axiom audit guards
all eleven memory theorems. Only the three standard Lean axioms are allowed.

This relates logical source values to the checked memory model. It does not
prove that a native Rust reference holds this representation or that ghost tags
belong to the executing actor. Reference creation, actual source lifetime events,
Rust aliasing/UnsafeCell, native allocation and allocator/destructor/deallocator
composition remain open. The native constructor's original raw-pointer
dereference remains rejected; the compiler and Lean backend are unchanged in
this milestone. NTT/SIMD/scheduler, causal oracle/owner coverage, BabyBear and
the final 128-bit expected physical attacker-work theorem remain open. Ghost
observations and list updates do not supply attacker-work floors.
