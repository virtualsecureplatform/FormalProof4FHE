# Retained Vec capacity arithmetic

`fixture.rs` calls the original `Vec::<u8>::with_capacity`. The gate retains 21
complete source function declarations, 31 types and globals in `Retained.json`.
`Generated.lean` emits nine isolated arithmetic assignments with their original
operators, destination/local indices, operand move/copy modes, primitive types
and statement hashes. The retained whole functions include their branches and
error helpers. The initial profile interpreted isolated scalar assignments;
the extension below also interprets continuous prefix control flow.

The scalar contexts for checked multiplication include its three actual locals;
all unused locals are dead. Four theorems prove the original assignment for every
word pair and incoming modeled world, its byte-size-one specialization, consumed
move operands and world preservation. Four source regressions cover zero and
maximum unsigned capacity, an overflowing product and unavailable moved operands.
The byte multiplication result does not establish the later allocation bound.

The shared interpreter uses distinct Boolean types and values, explicit overflow
flags, wrapping operations, precondition-checked subtraction and dynamic Boolean
branching. Existing heap, incoming-reference and deallocation-budget proofs are
extended to these cases. Seventeen model regressions and 28 core declaration
audits guard these additions. The original 333 audited dependencies used only the permitted
standard Lean dependencies; its 21 negative controls rejected changes to extraction
policy, widths, modes, locals, literals, owners and assignment metadata.

Run with the coupled tool receipt:

```bash
scripts/check-hasteboots-vec-capacity-arithmetic \
  --build-receipt build/hasteboots-extraction/inline-tools-build-b6esls36/manifest.json
```

The gate freshly extracts, compares generated code and retained declarations,
checks rejecting controls, compiles proofs and smoke examples with warnings as
errors, audits dependencies and records input/source/log hashes in an ignored
build manifest. `regression.json` records the checked milestone.

Whole-constructor control flow and calls, overflow/error and abort handling,
allocator implementation, native compiler/ABI/lifetime refinement, physical work
and the final HasteBoots security theorem remain open.

The continuous-prefix extension additionally emits the original 28 statements
before the multiplication-overflow branch and nine statements before the layout
branch. `LayoutProof.lean` proves their composition with arbitrary overflow,
accepted, rejected and following continuations. For byte elements the valid
branch is selected exactly when `capacity < 2^63`. Unrelated ambient locals and
the complete world are preserved; source Boolean moves remain observable.
`LayoutSmoke.lean` checks the four unsigned/signed boundary values, overflow-arm
irrelevance, ambient argument/world preservation and normal continuation.

Fresh extraction checks nominal Layout/Alignment fields, their physical layouts,
all alignment tags and the evaluated byte-layout global. This version audits
352 dependencies and rejects 32 source/profile mutations. Allocator and error
suffixes are retained as arbitrary continuation holes; their execution is open.


`AcceptedProof.lean` now additionally checks the 16 source statements constructing
Layout and its two success Result wrappers, consuming their fields and recovering
the allocation size. It composes their exact final frame and zero-size switch
with the preceding layout bound. The reservation-error field representation is
arbitrary and unused; its source variant declaration is validated. Eight further
source examples check zero/positive dispatch, failure propagation and storage
lifetimes. The current gate has 361 dependency audits and 42 rejecting controls.
At that stage zero-size return construction and the positive allocator-mode
dispatch were unprocessed; the subsequent extensions below handle the zero path.


`ZeroProof.lean` executes all 41 statements of the source zero-size arm and
composes its direct return with the preceding prefix. With an initialized Global
argument it returns the exact nominal success value, capacity zero and a dangling
address-one pointer without allocation origin. The modeled world is unchanged,
and arbitrary positive and following bodies cannot execute after the return.
Five source regressions check that composition, pointer/capacity/allocator fields
and rejection of an uninitialized allocator argument. The source conversion reads
the alignment enum through the new checked enum-address operation; its eight
model regressions cover provenance, move consumption, zero/tag/kind rejection and
world preservation. The positive allocation path and whole Rust constructor
refinement remain open.


`CallerProof.lean` closes the decoded capacity-zero fixture path through the
original Vec and RawVec callers and the allocation helper. Twenty-three theorems
prove source Global/Uninitialized construction, ordered argument moves, checked
callee entry, caller resumption, the raw caller's capacity assumption, both
aggregate returns and the final decoded root. No allocator premise is needed;
the modeled world is unchanged. Unused logical-local/error types remain arbitrary,
and unprocessed positive/error/unwind branches explicitly report unsupported.
This is a zero-capacity source-path result, with native ABI/compiler/lifetime and
positive constructor refinement still open.

The gate now passes 433 dependency audits, 66 rejecting controls and 37 source
regressions. `CallerSmoke.lean` checks malformed arguments, moved operands, exact
vector fields, zero-root execution over arbitrary worlds and an explicitly
unsupported positive-size callee. Production interpreter/root imports are unchanged.


`PositiveProof.lean` now handles the accepted positive-size prefix through
allocation-mode selection, shared Global reference issuance and exact moved
reference/copied Layout arguments. The Global placement address is explicit and
must be nonzero; native stack correspondence remains open. The operation executes
real model-machine address and borrow steps, keeps the heap and incoming authority,
and preserves reachability. Null placement retains the executed address prefix.
The source allocation calls and subsequent cleanup/result handling remain open.

Six source theorems and seven regressions extend the gate to 464 dependency
audits, 77 rejecting controls and 44 source examples. Eleven new model regressions
and ten persistent dependency guards cover the checked ZST-local borrow.


`AllocatorProof.lean` now interprets both allocation-method wrappers and the
common runtime's checked entry, initial size extraction and positive-size switch.
The forwarding equations quantify over allocation-capable continuation bodies
and preserve all outcomes and heap changes. Source shim ordering, opaque unsafe
Rust declarations, alignment argument shape and ordinary/zeroed targets are
validated. Opaque shim execution, post-allocation null/Result construction and
native allocator ABI correspondence remain open.

The separate allocation-capable evaluator embeds legacy bodies exactly and has
an all-outcome machine projection. Its allocator model checks actual allocation
and zeroing steps with explicit placement/failure outcomes; no external success
callback is used. Fourteen model regressions include allocation/deallocation
with advanced generation. Eight source examples and sixteen dependency guards
bring the capacity gate to 535 audits, 95 rejecting controls and 52 source examples.

## Runtime shim and pointer dispatch

`RuntimeProof.lean` adds eleven theorems for the source positive runtime: explicit
shim forwarding, returned-unit continuation, alignment extraction/move, concrete
modeled allocation result, pointer inspection, Boolean mode selection and null
selection. `runtime_positive_result` composes these stages with explicit premises
about the shim invocation and allocator-machine result. Unsupported shim results
stop execution; source shim unwind executes cleanup and abort. Seven regressions
exercise arguments, null/non-null selection, preserved provenance and shim exits.

The reifier validates the thin pointer cast, pointer-check local scopes, zero
comparison, and shim unwind abort. Five additional mutations must be rejected.
The gate now checks 566 declarations and 100 rejecting controls. This does not
interpret the post-dispatch Result construction or prove native shim behavior.

## Non-null slice Result construction

`SuccessProof.lean` proves the source non-null arm in three stages, then composes
it through cleanup and `implementationFunction` invocation. The result retains
the allocated pointer and origin and uses the requested byte capacity as slice
metadata. The final invocation theorem keeps positive capacity, non-nullness,
shim behavior and the concrete allocator-machine result explicit. The source
checker validates transparent NonNull fields, Option/Result/ControlFlow variants,
projections, disabled checks and the exact pointer-from-parts builtin.

The null Result discriminant and native layout/ABI refinement remain open.

## Null allocation failure

`NullProof.lean` interprets the original null arm through early `AllocError`
return and common runtime invocation. The retained zero-byte residual Result has
only its Err variant inhabited and known discriminant 1. An explicit checked
zero-size enum descriptor implements that read without reading an uninitialized
payload. The operation requires matching nominal type and live storage; its
world, heap and incoming-reference preservation are proved.

The reifier validates the residual/never/error layouts and variants, actual
discriminant place, equality assertion, move, error aggregates and cleanup.
Native layout/compiler correspondence remains open. Failure invocation derives
the allocator's null result for a valid positive layout and keeps the shim's
modeled returned-unit behavior as a premise.

## Positive constructor success

`MethodResultProof.lean` composes the original allocation wrappers' successful and
failed Result returns. `ConstructionProof.lean` proves the positive successful
`try_allocate_in` invocation from its four typed source arguments, through layout
checks, mode selection, Global borrowing, allocating call, Result dispatch and
RawVec construction/return. The returned pointer origin and requested capacity
are exact. Placement, shim behavior and the concrete allocator result remain
explicit; capacity is positive and below `2^63`, and the pointer is non-null.

The source checker retains and validates Result selection, casts, moves and
cleanup. The fat-to-thin data-pointer cast has its own world-preserving model
operation; the earlier thin-only cast retains its existing behavior. Error/drop,
unwind, rejected layout/overflow branches and outer decoded callers remain open,
as do native ABI/compiler/lifetime correspondence and physical work.

## Allocating outer callers and decoded root

`PositiveCallerProof.lean` composes the allocating constructor through the
original RawVec/Vec callers and decoded capacity root. Returned Vec fields retain
the allocator pointer's origin and requested capacity; length is zero. Callers
resume in the actual returned world. The caller capacity-check proof is split
at original source statement boundaries without changing proof limits.

The decoded theorem requires positive capacity below `2^63`, nonzero explicit
Global placement, a non-null pointer, the modeled shim return and allocator-machine
result. Reachability of a returned state follows from the shared interpreter.
Eight regressions cover exact fields, moved capacity, decoded invocation and
uninitialized reserved bytes. The gate checks 680 declarations and 131 rejecting
controls. Error/drop/unwind and invalid layout branches, resident storage and
native ABI/compiler/lifetime/work correspondence remain open.

## Allocation failure and Global drop

`ConstructorErrorProof.lean` proves the normal allocation-error path through its
reservation-error aggregate, actual exclusive zero-byte Global loan, retained
Global drop-glue body, cleanup and constructor return. The drop result follows
from its concrete unit-returning body. Effect-free unit settlement preserves old
leases under the world invariant, which is derived through actual modeled shim
invocation. Both initialization modes preserve the shim-returned heap.

The source checker validates the Global drop signature/body, mutable borrow,
metadata, moved reference, call/unwind, error fields and exact operand modes. The
profile has 724 audits, 141 rejecting controls and 100 source examples. Error
propagation through outer callers, allocator unwind and invalid layout paths,
native opaque-wrapper/ABI/compiler/lifetime correspondence, resident storage and
physical work remain open.
