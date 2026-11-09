# Original resident Vec destruction

This profile composes original `alloc::vec::Vec::drop_glue`, `alloc::vec::drop`,
foreign-classified retained `core::ptr::drop_glue`, the original mutable byte
loop, and the earlier RawVec destructor/deallocation chain. Entry selects an
existing exclusive 24-byte, alignment-eight Vec receiver. It supplies neither
pointer provenance nor a fresh reference tag. The by-value `release(Vec<u8>)`
fixture entry and native Vec construction are not interpreted here.

`NativeVecReference` validates the resident complete reference and pointer
identities, reads the data pointer from byte offset eight through pointer shadow,
and reads the length as an aligned word at offset sixteen. Field reads use the
exclusive parent directly; they do not copy its reference value. Whole-Vec and
RawVec-field mutable borrows execute address derivation and checked exclusive
loan issuance, with extents 24/16 and alignment eight. The RawVec field starts
at byte offset zero. Failed issuance retains its actual address prefix.

The aggregate interpreter now supports these operations, pointer/length parts
construction, and mutable byte-slice borrowing. Parts construction preserves the
complete pointer and adds only the evaluated length. The slice borrow executes
actual checked issuance over that byte extent. Uninitialized data, invalid
origins, conflicting loans and out-of-allocation extents reject.

`NativeRecordDropCalls` composes actual aggregate frames with the unbounded
`NativeByteLoopLLBC` execution relation. Callee arguments, moves, return slots,
unwind and rejected/unsupported prefixes are preserved. A translated call is
wrapped with explicit ghost cleanup covering argument preparation and that call;
normal continuation closes only loans born within that scope. It preserves
incoming loans and local slots. Terminal failure/unwind prefixes are retained.
The normal-return callee cleanup remains separate. These cleanup points are not
proved to coincide with Rust lifetime endings.

The source gate retains classifications, validates nominal projection owners,
receiver/layout geometry, metadata, regions, pointer cast, the parts intrinsic
and call signatures. The closed parts intrinsic's original UB edge is checked
and retained as data; it cannot unwind in this logical model. Both retained
abort causes reject in the model, while their original labels remain in the
source snapshot. Reference/fat-pointer extents are logical, not a native ABI
representation theorem.

The initial bridge supplied nine Vec-reference and seven composition theorems for checked execution,
reachable states, minted-reference identity, borrow heap preservation and scope
projection. Three aggregate helper theorems extend the existing interpreter
projections. Fifty-one declaration guards and 28 model regressions cover these
operations and scope behavior. The source profile has fourteen loop theorems
(including universal execution simulation and agreement) and five composition
and classification theorems. The traversal is not truncated by fuel or a sample
length. The execution examples still cover only specific caller outcomes; a
universal complete destructor characterization remains open.

Eight source examples check a three-byte traversal followed by deallocation,
zero capacity preserving the heap, zero length with nonzero capacity still
freeing the buffer, an oversized slice rejecting before its data loan, wrong
entry selectors and retained foreign classification. Successful examples also
assert an actual unit return; the rejection example asserts an invalid outcome.
The three-byte execution retains only the incoming loan and removes one data
allocation. The rejected oversized slice preserves its earlier whole-Vec loan
and heap. Invalid-entry examples are defensive model checks, not evidence that
those inputs are valid Rust values.

`Execution.lean` now supplies a total executor for the concrete retained
root. A closed syntax check verifies that every embedded loop is the original
byte loop. Structural evaluation follows actual frames, argument moves, scope
cleanup, calls, unwind and terminal prefixes. Loop execution uses the full
well-founded traversal, with an exact proof of both unit completion and rejected
iteration outcomes and their final worlds. There is no fuel, fallback result,
supplied execution witness or successful-traversal premise.

The new general call-relation and invocation determinism theorems make this
characterization an equivalence: every invocation of the original root equals
`execute world inputs`, for arbitrary states and inputs. The executor is proved
to admit an actual source execution and project to the checked reference machine;
it preserves reachability from a reachable entry. Its loop outcome preserves the
heap on success and failure. These are complete source-model outcomes, not a
native compiler/lifetime theorem or a universal postcondition asserting exactly
when a valid nonempty Vec is freed.

Fourteen new source theorems and eight additional regressions cover totality,
execution equivalence, arbitrary-state rejected entries, altered-loop rejection,
zero-length traversal, positive-extent failure without a parent, and exclusion
of simultaneous unit success and rejection with the same final heap. Two new
model theorem guards cover determinism. The profile now has sixteen source
regressions in total.

`HeapProof.lean` now proves a universal heap-effect postcondition for every
invocation outcome: either the complete byte-and-shadow heap is unchanged, or
there is exactly one fewer live allocation. The original Vec byte-drop method
preserves the full heap for every outcome. The facts apply to arbitrary modeled
entry states and inputs, including rejected, unsupported and unwinding prefixes;
they do not require a successful traversal or a normal unit return.

The new framing layer proves that reads, pointer loads, address derivation,
borrows, retags and explicit scope cleanup preserve the full heap. Its framing
marker is an equality proposition; original execution-projection theorems still
supply actual machine runs. Typed deallocation's existing successful-free theorem
is the only nonzero allocation effect used here. Heap-loss certificates also
require full heap identity whenever counts are equal. This prevents equal counts
from concealing writes or free/reallocate cancellation.

The finite-body bound conservatively sums alternatives. The composed-call bound
tracks normal continuation and terminal paths separately: completed unwind
cleanup cannot also execute the normal successor's free. The source root's
resulting budget is proved to be one; the byte-drop method's budget is zero.
These are allocation-effect bounds, not physical-work charges.

Thirty heap-framing and thirteen bound/composition theorems, 53 declaration
guards, eighteen model regressions and ten source heap theorems support this
result. Regressions check excluded writes/frees/allocations, retained null-read
prefixes, terminal versus continuing cleanup, two possible frees, byte changes,
address reuse with equal counts, and allocation growth. The final gate passed
425 dependency audits and 69 rejecting controls, including the extent mutation.
Full `scripts/check` passed its 11,029-job build and subsequent smoke checks.
Validation receipts are in `regression.json`.

## Exact release effects for every retained Vec outcome

The retained Vec root now either preserves the full heap or performs exactly
one positive, valid deallocation of a block from the original heap. Surviving
block records, including their bytes, are unchanged. Pointer shadow metadata is
filtered by the freed storage owner; pointers stored elsewhere retain their
provenance even when they point into the freed allocation. Generation state is
preserved. Under reachable-state invariants, loads through aliases of the freed
origin reject. The total source executor has the same exact-effect guarantee.

Release traces strengthen the general heap-loss certificates. Fifteen release
theorems and two derived bound theorems support eight additional source
theorems. Twelve model regressions cover surviving metadata, stale pointers,
address reuse and exclusion of hidden writes. Four source regressions cover
an empty Vec with an unallocated dangling data pointer and a zero-length Vec
with reserved, uninitialized capacity.

The fresh extraction gate passed 455 dependency audits and 69 rejection
controls. Full `scripts/check` passed its 11,032-job build and subsequent smoke
checks. Hashes and receipts are recorded in `interop/aeneas/vec-drop/regression.json`.

The removed block is not yet universally identified with the initial Vec buffer.
Next establish that binding and successful valid-Vec zero/nonzero postconditions.
Native construction, compiler/lifetime/ABI refinement, physical attacker work
and the final application security theorem remain open.


## Resident Vec field and ownership invariants

`NativeResidentVec` now binds a checked resident Vec descriptor to its original
heap slots. Successful pointer, capacity and length accesses return exactly the
stored values. Pointer observations preserve the complete stored provenance.
The converse pointer-access theorem requires the actual live borrow permission;
a resident descriptor alone does not authorize access through a blocked parent.

The ownership predicate distinguishes zero capacity from an exact positive byte
allocation. Initialization of the element prefix is a separate predicate; unused
capacity need not be initialized. Zero capacity implies zero length and an
initialized empty prefix without requiring a data allocation. At the modeled
allocator boundary, positive ownership supplies a successful exact-layout free.
It removes one block, preserves surviving blocks and generation state, and makes
positive ranges through the removed origin unreadable. Separately stored header
fields and their now-dangling pointer value survive that free.

Twenty-two model theorems, 26 declaration guards and seventeen regressions cover
this step. The fresh Vec extraction gate passed 481 dependency audits and 69
rejection controls. The generated source bodies and retained source schema are
unchanged; the profile additionally imports and audits the new invariant module.
Full `scripts/check` passed its 11,035-job build and subsequent smoke checks.
The profile regression file records the receipt and source/log hashes.

These are resident-model premises and allocator-boundary postconditions. The
universal theorem identifying the original source destructor's removed block
with this descriptor's buffer remains open. Next carry the invariant through
source borrow/call preparation and capacity dispatch, proving exact zero/nonzero
source postconditions. Native construction, compiler/lifetime/ABI refinement,
physical attacker work and the final application security theorem remain open.


## Borrow transport and original capacity dispatch

`NativeResidentVecBorrow` carries the original header contents through actual
whole-Vec, RawVec-field, shared RawVec, and reservation/activation operations.
The minted reference is bound to the original storage base, with its checked
mode and extent. Capacity and pointer reads through the shared child return the
original values and retain enough residency for subsequent reads, even as
scratch registers shift. Fresh child grants preserve older resident loans.
Scope cleanup preserves incoming residency, including a blocked cleanup prefix.

The Vec profile's `CapacityProof.lean` applies these facts to the original
retained `current_memory` function for byte elements. Under a resident shared
RawVec view, every outcome is either a rejected prefix or a returned value with
the exact source dispatch: zero capacity returns `None`; positive capacity returns
`Some` containing the original complete buffer pointer and capacity-byte layout.
The canonical caller reference is derived from the resident view. No successful
field-read or normal-return premise is supplied. A separate return corollary
exposes the result equality for subsequent caller proofs.

Thirty-one model theorems and five source theorems support this step. Eighteen
model regressions cover the nested borrow/read chain, reservation identity,
register shifts, ended child references and blocked cleanup. Six source
regressions cover zero capacity with a dangling buffer, reserved uninitialized
capacity, exact returned provenance and rejection after cleanup.

The fresh extraction gate passed 524 dependency audits and 69 rejection controls,
including the slice-extent mutation. Full `scripts/check` passed its 11,038-job
build and subsequent smoke checks. The profile regression file records the
receipts, input hashes and full-check log hash. Retained function bodies and
type declarations are unchanged.

Next carry this exact `current_memory` result through the original deallocation
caller and identify the root Vec destructor's freed allocation with the owned
buffer. Successful valid-Vec source postconditions, native construction,
compiler/lifetime/ABI refinement, physical attacker work and the final application
security theorem remain open. These results use the checked model and do not
establish native constructor acceptance.


Run:

```sh
scripts/check-hasteboots-vec-drop \
  --build-receipt build/hasteboots-extraction/inline-tools-build-b6esls36/manifest.json
scripts/check
```

The earlier executor gate passed 362 dependency audits and 69 rejecting controls. Changing
the constructed byte-slice extent to zero changes generated code, retains the
free, and removes six iteration loans from the three-byte example. The original
RawVec drop and deallocation gates passed again with 290/294 audits and 44/24
rejection controls. The full `scripts/check` passed its 11,023-job build and subsequent smoke checks;
final receipts and hashes are recorded in `regression.json`.

Next prove successful valid-Vec postconditions, including which owned allocation
is freed and the exact zero/nonzero cases, and connect native construction,
carrier/reference/stack/layout/ABI, compiler and lifetime refinement. Retained
precondition helper bodies and the external allocator still require refinement.
Physical attacker work, the complete application reduction and the final
expected-work security theorem remain open. This profile supplies no native
constructor acceptance or physical-work certificate.
