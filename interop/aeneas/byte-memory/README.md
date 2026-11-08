# Byte allocation lifecycle and extracted Layout data

`NativeByteMemory.lean` supplies the byte-memory state that the immutable
parameter-cell registry lacked. It shares the existing address/provenance data.
It is an operational model, not an accepted Rust allocator, dereference or
borrow refinement, and it does not change the rejected native constructor.

An allocation checks power-of-two alignment on the 64-bit target, the rounded
isize size bound, positive allocation size, nonzero/aligned base, address-space
extent and disjointness from every live allocation. Its address is an allocator
outcome to be checked, not a freshness certificate. A successful allocation
increments a ghost generation counter and creates exactly the requested number
of **uninitialized** byte slots. Zero-size allocation is excluded from this
primitive; empty-vector/ZST paths must be accounted for separately in source.

Single-byte loads/stores check a matching live origin and an address inside
that allocation. Loads require an initialized byte; stores set the requested
slot and preserve its length and allocation geometry. These byte operations do
not yet justify typed references or mutable borrows. Deallocation checks the
original base/origin and exact size/alignment, then removes the allocation and
its stored bytes. Every successful release reduces the live-block count; it
cannot act as a no-op drop. Generation-aware address reuse keeps stale pointers
unreadable, and stores to a different origin preserve reads of other origins.

Thirty-nine theorems establish allocation/storage/deallocation invariants,
read-after-write, initialized/in-bounds access witnesses, origin isolation,
complete initial uninitialization, disappearance of deallocated aliases and
stale address-reuse behavior. All three transitions preserve a well-formed live
heap, so reachability from the empty heap derives that invariant. The `shape`
function is only an erasure used in the invariant proof; memory operations do
not call it or use it to replace a destructor.

Six bridge theorems connect the already extracted stdlib Layout getters to
model size/alignment, prove the complete 64-constructor alignment property, and
identify the allocation/deallocation bounds checked on those source values.
This decoder is not a Layout constructor or a proof that original native
allocator calls follow the model. The source Layout extraction gate is rerun
with the frozen paired tools. Its existing sysroot/profile is retained; no
configuration identity with the ordinary native constructor is inferred.

```sh
scripts/check-hasteboots-byte-memory-guards
scripts/check-hasteboots-byte-memory \
  --build-receipt build/hasteboots-extraction/inline-tools-build-RECEIPT/manifest.json \
  --backend /tmp/hasteboots-aeneas-m0
```

The combined gate checks 96 dependency audits: 61 memory declarations, eleven
bridge declarations and 24 reused source declarations/readers. The separate
source Layout gate checks its existing 36 audits. The persistent root axiom
file also checks all 61 memory declarations. Smoke cases cover invalid layouts,
null/misaligned/overlapping/wrapping allocations, uninitialized bytes, one-past
access, interior/wrong-layout deallocation, initialization/free/reallocation and
independent adjacent allocations. No new axiom, native_decide or raised proof
limit is introduced.

The native Aeneas run still rejects the raw-pointer dereference in original
`drop_in_place`. Remaining work includes the source memory-state relation,
allocator outcome/initialization correspondence, ranges/slices and ZST access,
typed value validity, aliasing/borrow lifetimes and correct destructor/deallocator
composition. Those must be implemented before enabling that dereference.
NTT/SIMD/scheduler, causal oracle/owner history, BabyBear and expected physical
attacker-work security remain open. No memory action is assigned a physical-work
floor or counted as a completed source refinement here.

Full `scripts/check` passes, including the 10,932-job build and subsequent audits
and smoke commands. All 192 extraction/model guard tests pass. The compiler and
backend are unchanged; their previous paired/upstream receipts are retained as
previous evidence, rather than described as fresh full compiler regressions.
