# Original resident Vec destruction

## The retained deallocation callee returns and releases its buffer

`NativeRawVecDeallocationCompleteness` proves the actual empty allocator-subobject
borrow, including with an overlapping shared header child. Logical full-capacity
buffer separation is preserved through header reborrows and the empty allocator
loan. Exact ownership, a resident complete pointer and separation suffice for
the existing permission-checked byte/shadow free at the specified external
boundary; unused buffer capacity need not be initialized.

`deallocation_complete` composes the retained shared borrow, current-memory call,
allocator borrow, Global wrapper call and final cleanup. Zero capacity returns
unit with the complete heap unchanged. Positive capacity returns unit after
freeing the original stored buffer and capacity. Both branches preserve
reachability and restore the original ordered incoming loans. The invocation
corollary also checks the canonical input decoder. No successful internal borrow,
free, return or cleanup result is supplied as a hypothesis.

The current-memory result now also derives positive-capacity buffer-register
membership from the actual pointer read and subsequent marker read. Scope cleanup
uses reachability and a fresh-loan-prefix proof relative to the original call
entry. The checked sufficient conditions package resident fields, initialized
header bytes and the exclusive alias frontier; ownership and physical buffer
separation remain explicit independent conditions.

This step adds 12 model theorems, one model structure and three source theorems,
with 17 declaration audits, seven model regressions and two source regressions.
The cases cover overlapping header/allocator loans, exact release, protected
buffer rejection, post-free unreadability, ordered scope restoration, positive
uninitialized spare capacity and an empty dangling buffer.

Next carry normal return through the RawVec method and glue, then compose outer
Vec destruction. Native construction, compiler/lifetime/ABI refinement, the
external allocator implementation, physical attacker work and final application
security remain open.

## The retained current-memory callee now returns normally

`NativeRawVecSharedCompleteness` proves completion of the actual RawVec shared
whole-object borrow and derives its read permissions. Its shared frontier retains
overlapping ancestors and excludes other overlapping loans. The resulting
`Header` binds capacity, length and the complete stored pointer to the original
heap observations. Capacity reads preserve these conditions for repeated reads;
pointer reads recover shadow provenance, and the allocator marker performs its
actual checked zero-byte read at the header boundary.

`current_memory_complete` follows the retained callee's original body. At zero
capacity it returns `None`; at positive capacity it returns the original buffer
and byte layout. Both cases return normally with the complete heap and incoming
ordered loan list unchanged. Successful reads, permission booleans and a normal
return are derived rather than supplied.

The addition includes 14 model theorems, six model definitions, one model
structure and one source theorem, with 23 declaration audits. Seven model
regressions cover construction, repeated reads, provenance, marker behavior and
an overlapping exclusive-loan rejection. Two source regressions instantiate the
normal-return theorem for positive uninitialized spare capacity and an empty
dangling buffer. Native construction, compiler/lifetime/ABI refinement, the
external allocator implementation, physical attacker work and final application
security remain open.

Next compose this result into the deallocation callee: prove its allocator
subobject borrow, owned-buffer release and cleanup complete, then carry normal
return through RawVec and outer Vec destruction.

## The RawVec borrow prefix completes from stored fields

`NativeRawVecBorrowCompleteness` proves actual Vec whole/subobject borrows,
RawVec shared reservation, and exclusive activation from resident identities,
initialized fields and the logical alias frontier. `loadRange_prefix` retains
the original alignment, and `Descriptor.rawvec_initialized` derives the 16-byte
RawVec read from the existing stored fields. No successful borrow result or
permission boolean is a hypothesis.

The composed Vec-to-RawVec activation result carries the original resident
header and buffer, a fresh exclusive frontier, reachability and the unchanged
complete heap. Its concrete regression checks two minted loans and the ordered
lease tags; reservation itself adds no loan. The regression fixture keeps spare
buffer capacity uninitialized.

`rawvec_method_ready_prefix` connects these completion results to the retained
RawVec method's reservation, activation, layout argument and deallocation call.
The method reaches its real callee and caller continuation under the explicit
conditions. The callee's normal return, owned-buffer release and successful
method cleanup remain to be established; this prefix theorem does not assert
them. Native construction, compiler/lifetime/ABI refinement, external allocator
implementation, physical work and final security also remain open.

This step adds seven model theorems, one checked model definition and one source
theorem, with six model regressions and nine declaration audits.

## Stored fields establish initialized Vec header borrows

`NativeByteRangeCompleteness` now composes adjacent initialized reads while
preserving their complete pointer origin. Heap well-formedness identifies the
same allocation for both reads; numerical adjacency alone is insufficient.
`Descriptor.header_initialized` derives the complete 24-byte aligned header read
from its existing capacity, pointer and length observations. It requires no new
whole-header initialization assumption and no initialization of unused capacity.

`NativeBorrowFrontier.grant_initialized` extends the checked child-grant
completion argument to aligned record layouts. `vec_header_grant_complete`
combines it with the derived header read and the explicit logical alias frontier.
The actual grant mints the child reference and preserves its frontier. This
establishes an input to the remaining source borrow/call proof; it does not yet
prove normal RawVec return or whole-Vec destruction.

The addition has six theorems, six model regressions and dependency audits for
all six declarations. The regressions include uninitialized spare capacity,
a missing byte, and a numerically adjacent pointer with a different generation.

## The retained slice helper and Vec byte method return unit

`ByteMethodReturnProof.lean` composes traversal completion through the retained
slice-drop helper and the original Vec byte method. It checks their actual
argument moves, loop call, unit-result writes, scope cleanup and return bodies.
The helper restores its incoming loans; the byte method then ends its own data
loan and restores the original ordered lease list. Both preserve the complete
heap and return a reachable modeled state.

The public invocation theorem checks the original Vec decoder and typed initial
frame. Determinism makes every invocation under the same sufficient conditions a
unit return with the original loans and heap. A separate corollary carries the
original resident header to the following RawVec path. The hypotheses remain
explicit: reachability, resident fields, initialized elements, full-capacity
separation from active loans, and the header's logical alias frontier. Successful
callee results or cleanup booleans are derived rather than supplied.

This step adds 17 source theorems and eight checked definitions, with five source
regressions. They cover the helper's incoming leases, byte-method invocation,
resident-header handoff, an empty dangling buffer and the original three-byte
execution's exact counter and remaining header loan.

Next prove sufficient conditions for normal RawVec return and owned-buffer
release, then compose successful outer Vec glue destruction. Native construction,
compiler/lifetime/ABI refinement, the external allocator implementation, physical
attacker work and the final application security theorem remain open. This byte
method result preserves the buffer; it does not claim the whole Vec was freed.

## The Vec byte-method prefix establishes the traversal conditions

`NativeVecBytePrefix` derives checked pointer and length field reads from a
resident Vec descriptor and its logical header-frontier condition. The pointer
read recovers the complete stored provenance; the length read returns the
original stored length. Initialization is required only for the element prefix.
Physical separation of the buffer's full capacity from active loans remains an
explicit condition, distinct from ownership and initialization.

`ByteMethodPrefixProof.lean` follows the retained field-read scope, raw cast,
fat-pointer construction and mutable slice borrow. The resulting slice satisfies
the conditions for successful unbounded traversal. The proof factors the actual
byte-method execution at its first call and checks the move from caller local 6
into the retained callee's typed argument frame. It keeps the original scope
entry cutoff, so later cleanup still ends the fresh data loan.

This step adds 14 model theorems, three definitions, 17 model declaration guards,
nine source theorems, 13 checked source definitions, nine model regressions and
four source regressions. Cases include empty dangling buffers, partially
initialized capacity, complete pointer origins and an overlapping data loan
that blocks exclusive borrowing.

The zero-slice mutation now has two checks: its altered execution still removes
six iteration loans in the three-byte fixture, while the original-length prefix
proof must fail specifically at `byte_parts_complete`. This binds the new proof
to the source's real length rather than accepting a silently shortened slice.

Fresh extraction passed 788 dependency audits and 70 rejection controls.
Full `scripts/check` passed its 11,062-job build and all subsequent smoke checks.
Retained Rust function bodies and type declarations are unchanged; input hashes
and validation receipts are recorded in `regression.json`.

Unit return through the retained slice-drop helper and byte-method cleanup is
now proved above. Next complete successful Vec/RawVec destruction under sufficient
ownership and alias conditions. Deriving those conditions from native
construction, compiler/lifetime/ABI refinement, physical attacker work and the
final application security theorem remain open.

## Successful unbounded byte traversal restores the incoming loans

`NativeScopeRestoration` tracks the exact fresh-loan prefix created by checked
non-ending operations, slice issuance and byte indexing. Completed cleanup
filters precisely the scope's fresh tags and restores the original ordered
lease list. Reachability proves cleanup completion for the actual prefix; the
traversal theorem does not take a cleanup-success premise.

`NativeByteTraversalCompleteness.Ready` combines reachability, resident slice
reference/pointer registers, exact byte extent, initialized elements and the
logical exclusive-frontier condition. Under these explicit conditions, issuance
succeeds, indexing recovers its actual raw pointer, and each bounded iteration
succeeds. Cleanup restores the incoming leases and the same slice conditions.
Well-founded induction then proves completion at the original extent for the
unbounded traversal, while retaining the original lease list. No execution cap
or supplied successful iteration trace is used.

`TraversalCompletenessProof.lean` connects this result to the actual retained
source loop and its operational relation. Source regressions also carry the
original resident Vec header through the successful loop and execute the loop
again with the resulting slice conditions. The proof remains about the checked
model; native construction/compiler/lifetime correspondence is still open.

This step adds 17 model theorems, one relation structure, one slice-condition
definition, 20 model declaration guards, two source theorems, 16 model
regressions and three source regressions. Tests cover nested cleanup order,
retained historical registers without tag reuse, revoked inputs, fresh borrowing
after cleanup, repeated traversal and an empty slice with uninitialized capacity.

Fresh extraction passed 749 dependency audits and 69 rejection controls.
Full `scripts/check` passed its 11,059-job build and all subsequent smoke checks.
Retained Rust function bodies and type declarations are unchanged. Input hashes
and validation receipts are recorded in the profile's `regression.json`.

The original Vec byte-method prefix now establishes the slice conditions above.
Next prove successful return and exact release through the remaining Vec and
RawVec source calls. Native refinement, physical attacker work and the final
application security theorem remain open.

## Initialized prefixes and logical alias conditions give checked index success

`NativeByteRangeCompleteness` proves that every bounded subrange of an
initialized byte prefix is readable with exactly the corresponding bytes.
It derives geometry and address bounds, preserves complete pointer provenance,
and includes empty ranges at the end. Resident Vec initialized-element proofs
now supply every bounded byte read. Unused capacity remains independent of the
initialized prefix.

`NativeBorrowFrontier` states a logical alias condition: the selected exclusive
lease may overlap its ancestors, while every other active lease must be
physically disjoint. Under a valid ledger, this condition gives the checked
permission for shared or exclusive subrange access. An actual exclusive borrow
preserves the condition for its fresh child. Combining this with initialized
subranges proves actual ledger borrowing, closed-machine reference grants and
byte indexing, including address preparation. These theorems derive successful
operations rather than accepting success booleans as premises.

This step adds 17 theorems, two definitions, 19 declaration guards and 20
regressions. Tests cover exact byte selection, dangling empty ranges,
uninitialized spare capacity, lost provenance, nested overlapping ancestors,
blocking descendants and unrelated overlaps, and actual reference/birth
register issuance. The prerequisites remain explicit: initialized elements,
well-formed modeled memory/ledger, resident registers and the logical alias
condition. They do not establish native Rust lifetimes or construction validity.

Fresh extraction passed 727 dependency audits and 69 rejecting controls.
Full `scripts/check` passed its 11,053-job build and all subsequent smoke checks.
Retained Rust function bodies and type declarations are unchanged; input and
validation hashes are recorded in the profile's `regression.json`.

Slice issuance, iteration cleanup and unbounded traversal completion are now
proved above. Lifting these conditions through the original Vec source calls
and the sufficient conditions for successful
whole-Vec return and exact release, native refinement, physical attacker work
and the final application security theorem remain open.

## Outer Vec glue identifies the original buffer on every outcome

`OuterVecProof.lean` now connects the original Vec entry to the existing RawVec
buffer result. It checks the entry decoder and typed arguments, the whole-Vec
borrow, the byte-method caller frame, cleanup, and both normal and unwind
RawVec continuations. The proof follows the retained source tree; its bodies
are not replaced by a destructor specification.

The resulting `VecDeallocationPost` says that every outcome either preserves
the complete heap or frees the original stored buffer with a positive capacity
and its exact capacity-byte layout. Zero capacity preserves the complete heap.
If the heap changes, a corollary identifies the matching block in the original
allocation list. These results include rejected borrow, call and cleanup
prefixes. They assume a resident header and an explicitly older incoming
reference; they do not assume that any internal borrow or call succeeds.

This step adds 31 source theorems and 16 checked definitions. Eight regressions
cover reserved but uninitialized capacity at length zero, exact original-buffer
identification, empty dangling buffers, both source continuation shapes and a
retained failure fixture. Concrete executor facts are obtained from the checked
operational relation and determinism at standard Lean limits.

Fresh extraction passed 708 dependency audits and 69 rejecting controls,
including the slice-extent mutation. Full `scripts/check` passed its 11,047-job
build and subsequent smoke checks. Retained Rust function bodies and type
declarations are unchanged; hashes and receipts are in `regression.json`.

Next prove sufficient valid-Vec conditions for successful return and exact
release, then connect native construction/compiler/lifetime/ABI refinement and
the external allocator implementation. Physical attacker work and the final
application security theorem also remain open. This result does not establish
native constructor acceptance or the complete security theorem.

## Incoming references survive record calls and the complete byte destructor

`NativeRecordIncomingReference` proves authority preservation through every
record rvalue and body, including ordinary calls, two-phase mutable calls,
retained failure prefixes and unit-return cleanup. Cleanup is proved relative
to callee entry: it can end temporary child leases while retaining every older
incoming lease. Raw deallocation preserves this authority relation without
claiming that the heap remains unchanged.

The source proof extends this result through the complete retained call tree,
scopes, loop and invocation. Combining the byte method's existing full-heap
frame with incoming-reference preservation now carries an older resident Vec
header through the complete original byte destructor on every outcome. The
reference-age premise remains explicit; no successful call or cleanup premise
is supplied.

This step adds 28 model theorems with guarded dependency audits, five source
theorems, eight model regressions and four source regressions. The model tests
check that a temporary child remains after rejection and ends after a normal
unit return while the incoming lease survives both.

The fresh extraction gate passed 661 dependency audits and 69 rejection
controls. Full `scripts/check` passed its 11,047-job build and all subsequent
smoke checks. Retained Rust function bodies and type declarations are unchanged.
The profile's `regression.json` records the input hashes and validation receipts.

Original-buffer identification at the outer Vec root is now proved above.
Successful valid-Vec postconditions, native construction/compiler/lifetime/ABI refinement,
the external allocator implementation, physical attacker work and the final
application security theorem remain open.

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


## Exact buffer identification in the retained deallocation caller

`DeallocationProof.lean` now proves the original RawVec deallocation caller's
heap effect under the resident buffer invariant. Every outcome either preserves
the full heap or performs exactly the specified deallocation of the original
stored buffer with its capacity-byte layout. Zero capacity preserves the heap on
every outcome. Any changed heap identifies a positive-capacity original live
block with that exact pointer and layout. The theorem also covers the canonical
checked-reference invocation; its input decode follows from residency.

The proof carries the existing `current_memory` result through the caller's
actual option dispatch, allocator-subobject borrow, Global wrapper and specified
external free boundary. Typed call execution is proved equal to the existing
finite-body call semantics, including argument consumption, normal/unwind
resumption, result-write failure and unit cleanup. Rejected prefixes are retained;
no successful borrow/read, free, normal return or cleanup is assumed by the
universal caller theorem. Structural views of the original caller are checked by
reflexive equalities against the complete retained body.

Six model theorems and 25 source theorems support this step. Nine model regressions
cover argument rejection, consumed caller slots, unwind/unsupported results and
failure to write a result after a callee has freed memory. Ten source regressions
cover empty dangling buffers, reserved uninitialized capacity, exact capacity and
provenance, preserved stale pointer metadata and a live data loan blocking free.

The fresh extraction gate passed 569 dependency audits and 69 rejection controls,
including the slice-extent mutation. Full `scripts/check` passed its 11,041-job
build and subsequent smoke checks. Receipts and hashes are recorded in the
profile regression file. Retained function bodies and type declarations are
unchanged.

This identifies the buffer at the RawVec deallocation caller. Next lift it through
the RawVec destructor and outer Vec drop composition to the original Vec entry,
and prove successful valid-Vec zero/nonzero postconditions. Native construction,
compiler/lifetime/ABI refinement, the external allocator implementation, physical
attacker work and the final application security theorem remain open.


## Exact buffer identification through the RawVec destructor entry

`RawVecDestructorProof.lean` lifts the deallocation caller result through the
original RawVec destructor method and drop glue. It follows actual reservation,
remaining-argument evaluation, exclusive activation, child-reference transfer,
callee execution, caller resumption and cleanup. Every outcome either preserves
the full heap or frees exactly the original stored buffer with its capacity-byte
layout. Zero capacity preserves the heap on every outcome.

The generated RawVec drop definition is proved equal to the native-body view of
the retained glue function. A general equality connects that view's operational
invocation relation to the existing finite-body invocation, including malformed
arguments and failed initialization. Consequently the exact-buffer postcondition
holds for the RawVec entry actually used by the outer Vec call tree. A changed
entry heap identifies a positive-capacity original live block with that exact
pointer and layout. No successful reservation, activation, call, normal return
or cleanup premise is supplied by these universal wrapper theorems.

Four added model theorems and 26 source theorems support this step. Four new model
regressions check remaining-argument rejection before activation, callee rejection
after activation, retained reservation effects, and heap-preserving continuations
that issue real loans. Ten source regressions cover the actual drop entry,
reserved/empty buffers, original block identity, preserved incoming loans,
blocked activation/free and stale checked references.

The fresh extraction gate passed 608 dependency audits and 69 rejection controls,
including the slice-extent mutation. Full `scripts/check` passed its 11,041-job
build and subsequent smoke checks. The profile regression file records the
receipts, input hashes and full-check log hash. Retained function bodies and type
declarations are unchanged.

Incoming-reference transport and composition at the outer Vec entry are now
proved above. Successful
valid-Vec postconditions, native construction, compiler/lifetime/ABI refinement,
the external allocator implementation, physical attacker work and the final
application security theorem remain open. Heap effects remain separate from
physical work charges.


## Incoming references survive the original unbounded byte loop

`NativeIncomingReference` now records counter monotonicity, preservation of
reference/pointer registers and birth records, and exact lookup equality for
every lease tag older than entry. Checked non-ending machine steps preserve
this relation. Fresh grants retain older leases. Scope cleanup preserves the
incoming relation even when cleanup stops with a pending suffix.

The relation is proved through slice issuance, byte indexing, every traversal
iteration and the complete unbounded traversal, including retained failure
prefixes. Combining it with the existing full-heap frame carries the original
resident Vec/RawVec view through traversal. No traversal-success or cleanup
completion premise is supplied. The age condition is explicit: historical
registers and births do not revive an ended lease. Loan preservation alone is
separate from heap preservation and does not assert that bytes were unchanged.

`IncomingReferenceProof.lean` connects the result to the original retained byte
loop's operational relation. Every loop outcome preserves incoming authority and
the complete heap, including malformed arguments and failed iterations. A source
corollary carries an older resident header view through that actual loop.

Fourteen model theorems, seventeen declaration guards and three source theorems
support this step. Twelve model regressions cover the three-byte traversal,
original leases/births, retained failed-index reborrows, ended leases, and the
separation between loan preservation and memory writes. Five source regressions
cover the original loop, resident-header transport, malformed arguments and an
ended slice input.

The final fresh extraction gate passed 628 dependency audits and 69 rejection
controls, including the slice-extent mutation. Full `scripts/check` passed its
11,044-job build and subsequent smoke checks. Concrete source-loop regressions
use the checked operational traversal relation at standard Lean limits. Receipts
and hashes are recorded in the profile regression file. Retained function bodies
and type declarations are unchanged.

The surrounding record and byte-drop call/cleanup composition is now proved
above, along with original-buffer identification at the outer Vec root. Successful valid-Vec
postconditions, native construction/compiler/lifetime/ABI refinement, the external
allocator implementation, physical attacker work and the final application
security theorem remain open.


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
