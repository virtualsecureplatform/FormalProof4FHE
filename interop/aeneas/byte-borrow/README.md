# Byte-borrow ledger with checked reborrows

`NativeByteBorrow` adds shared/exclusive access policy and lifetime transitions
to the byte-memory/range models. All access operations compute their checks from
the current ledger and call the existing memory operations. No caller supplies
a permission proof or replacement read/write/free callback.

Acquisition checks the initialized range and conflicts with existing leases.
Root shared leases may coexist; a root exclusive lease cannot overlap another
positive lease. Reborrowing requires a resident parent, bounded child span,
unchanged origin and no upgrade from shared to exclusive. Through a checked tag,
ancestor leases are exempted, while unrelated conflicting ranges still block
access. This permits disjoint children and parent accesses outside a child span.

The ancestry checker is proved sound and complete for resident tags in a valid
ledger. Parent paths strictly decrease tag numbers and cannot cycle. Ending a
parent waits for its children, removes the ended tag and preserves the memory.
Tags are fresh and monotone; a theorem proves that an ended tag never reappears
under any future model transition. Ended/unknown tags cannot read or write.

Raw reads reject overlapping exclusive leases. Raw writes and deallocation
reject any overlapping positive lease. Tagged writes require exclusive access,
check offsets and conflicts, and actually update the modeled byte store.
Deallocation calls the exact-layout deallocator and really removes an allocation.
Empty byte leases protect no bytes; their ancestry/lifetime bookkeeping still
applies. Allocation/storage/deallocation and all ledger transitions preserve
memory well-formedness, unique tags, geometry, parent residency, bounds and modes.
Reachability derives those invariants from the empty state.

Fifty-four model theorems cover these properties. Seven composition theorems
route original constant/mutable/cast byte-slice pointer constructors into the
same checked ledger operation, retaining pointer/origin/length and initialization
requirements. No Rust reference constructor is replaced or accepted by this step.

```sh
scripts/check-hasteboots-byte-borrow-guards
scripts/check-hasteboots-byte-borrow \
  --build-receipt build/hasteboots-extraction/inline-tools-build-RECEIPT/manifest.json \
  --backend /tmp/hasteboots-aeneas-m0
```

The combined gate audits 133 declarations: 81 ledger declarations, seven new
composition theorems, ten reused range bridge declarations and 35 source/runtime
declarations. The parent range gate is rerun, including pointer-parts and
byte-memory/Layout gates. The root axiom file guards all 81 ledger declarations.
Thirty-six executable smoke cases include shared aliases, exclusive conflicts,
actual writes, parent/child/grandchild reborrows, disjoint siblings, blocked
parent writes/endings, restoration after child end, revoked IDs and empty spans.
No new axiom, native_decide or raised proof limit is used.

This is a byte-access policy, not a proof of Rust's reference/aliasing semantics.
Tags are ghost identifiers, not runtime secrets: no tag-unforgeability, source
ownership or actor authentication is inferred from numeric lookup. A source
relation must associate tags with actual reference values and justify creation,
use and lifetime-end events. Typed values/strides, interior mutability, UnsafeCell,
compiler handling of references and allocator/memory-state correspondence remain
open. The policy is not claimed to implement Stacked Borrows or Tree Borrows.

The original native `drop_in_place` raw-pointer dereference remains rejected.
The compiler, production Rust and Lean backend are unchanged. Destructor/free
composition, NTT/SIMD/scheduler, causal oracle/owner history, BabyBear and the final
expected physical-work security theorem remain open. Ghost ledger operations
are not counted as actual adversary work. See `regression.json` for the evidence.

Full `scripts/check` passes after its 10,938-job build, including subsequent
root audits and smoke commands. All 202 extraction/model guard tests pass.
