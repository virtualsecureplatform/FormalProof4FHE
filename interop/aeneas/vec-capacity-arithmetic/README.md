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

## Rejected layouts and reusable drop cleanup

`DropFrameProof.lean` proves Global drop and cleanup for a checked caller frame,
independently of unrelated local contents. The cleanup list comes from
the retained source and excludes the return slot. `RejectedLayoutProof.lean`
uses that result for capacities at or above `2^63`: the typed constructor returns
`CapacityOverflow`, preserves the heap and performs the actual exclusive Global
borrow/drop. No shim or allocator result is assumed on this rejected path.

The profile has 747 audits, 149 rejecting controls and 108 source examples.
Regressions include the exact threshold in both modes and maximum unsigned
capacity. Outer error/unwind propagation, resident storage, native correspondence
and physical work remain open. Byte multiplication overflow is proved unreachable
by the existing prefix theorem; its unchosen arm remains explicit unsupported code.

## Shared constructor and unwind continuations

`UnwindProof.lean` checks the source ownership guard, exclusive Global borrow,
drop-glue invocation, cleanup/resume and double-unwind termination. Conditional
entry theorems preserve the actual unwind world and do not assert that native
allocation can unwind. `UnifiedConstructorProof.lean` combines zero capacity,
positive success, allocation failure and rejected layouts in one interpreter,
with their path-specific premises. Ten regressions exercise these branches.

The gate has 783 audits, 157 rejecting controls and 118 source examples. The
outer error handler's nonzero-sized opaque borrow and foreign accessor require
a resident-stack/native-wrapper bridge. Outer error propagation, native
allocator ABI/unwind behavior, resident storage/destruction and physical work
remain open.

## Shared decoded caller graph

`UnifiedCallerProof.lean` connects the original three outer caller layers to
`unifiedConstructorFunction`. The same decoded entry point proves zero-capacity
return without placement/shim/allocator premises and positive success under the
explicit modeled placement, shim and allocator-result premises. Fifteen theorems
check typed entry, move/call/resume behavior and reachability. Seven examples in
`UnifiedCallerSmoke.lean` cover zero, concrete positive allocation, uninitialized
reserved bytes and reachability. Source validation is reused when rendering the
six shared caller declarations. The source gate passes 804 dependency audits,
157 rejecting controls, 125 source examples and 74 model examples. It does not replace the reservation-error arm or
outer unwind handlers, whose semantics remain explicit unsupported boundaries.

A scratch extraction with `--include alloc::collections` successfully exposes
`TryReserveError::kind` as transparent and the reservation-error wrapper fields.
It keeps 21 functions/31 types but changes some IDs. This gives a source-based
next step for the accessor; it still needs validated declaration identities and
nonzero-sized resident local borrowing before proving outer error propagation.

## Reservation-error storage fields

The reifier validates the complete physical wrapper and niche layouts: 16 bytes,
alignment 8, wrapper field offset 0, zero u64 at offset 0 selecting capacity
overflow, and the allocation-error Layout at offset 0. Existing Layout checks
place alignment at offset 0 and size at offset 8. Eight new rejecting controls
cover changes to this representation. `NativeReservationErrorFields` performs
checked reads and proves the zero branch never reads the potentially
uninitialized tail. Its shared resident-loan premise is separate from local
loan issuance: the existing borrow primitive still requires the whole byte span
to be initialized. The source accessor and outer error handler remain unproved.

Validation: 827 dependency audits, 165 rejecting controls, 125 source examples
and 90 model examples pass. The fresh full `scripts/check` passes with 11091
build jobs.

## Checked storage loans

`NativeByteBorrowStorage` separates storage permission/extent from initialized
byte reads. `NativeStorageBorrowMachine` embeds the old reference operations
unchanged and issues fresh storage loans from checked resident registers. Its
extended reachability and well-formedness proofs support an actual loan over
the partially initialized overflow object, followed by the checked decoder.
Twenty-two model examples and forty-one dependency guards cover this extension.
A storage loan establishes no Rust pointee validity by itself; the LLBC local
bridge, transparent getter composition and native stack/lifetime refinement
remain open. The original initialized-byte borrowing and its theorems are
unchanged.

Storage-loan validation: 868 dependency audits, 165 rejecting controls,
125 source examples and 112 model examples. The fresh full project check
passes with 11095 build jobs, and all four new modules pass direct
warning-as-error checks.

## Typed error-local snapshots

`reservationErrorTags` is emitted from the validated wrapper/kind/Layout/
alignment identities. `LocalProof.lean` connects original constructor error
payloads to `NativeReservationErrorLocal`'s codec; allocation errors require the
existing capacity bound. The core operation selects a complete typed local,
executes modeled allocation/write/loan steps and returns a resident two-word
operand. Its residency theorem ties the original logical value to the bytes of
the selected lease, with failures preserving executed prefixes. Overflow padding
is not written. The handler composition below uses this marshaling. Native stack placement,
typed borrowing and lifetime refinement remain open.

Typed-local validation: 915 dependency audits, 165 rejecting controls,
128 source examples and 134 model examples. The full project check passes
with 11098 build jobs, alongside all three new-module warning-as-error checks.

## Complete snapshot reads and checked getter

`NativeReservationErrorRead` derives byte residency and alias permission from
actual snapshot execution, proves complete field reads, and supplies a checked
kind getter using stable reference-tag resolution. Successful snapshots require
no additional read-success premise. `ReadProof.lean` connects both constructor
error payloads to this modeled operation; `ReadSmoke.lean` runs the complete
payload/snapshot/getter pipeline. The handler composition below links the extracted Rust getter body to this
operation and its source caller. Native stack/type/lifetime refinement,
reclamation and physical work remain open.

Read/getter validation: 945 dependency audits, 165 rejecting controls,
130 source examples and 151 model examples. The full project check passes
with 11101 build jobs, alongside all three new-module warning-as-error checks.

## Owned-error handler dispatch through the extracted getter

The gate now freshly extracts both the constructor and the getter fixture using
the same frozen tool receipt. It checks the getter method owner, signature and
generics, the five nominal type roles, physical layouts and transparent type
fields/variants under the correspondence `(0,1,2,3,4) → (9,18,4,11,12)`.
The constructor extraction's error wrapper remains abstract; the independent
getter extraction supplies its validated field definition. This is an explicit
modular source link and logical representation boundary, not a native ABI proof.

The reifier checks the complete original `alloc::raw_vec::handle_error` body:
local shared borrow, moved getter argument, returned-kind match, copied layout,
terminal argument move, storage cleanup, unwind and unreachable continuations.
`handlerEval` marshals the owned logical local into checked modeled storage,
then executes the linked `invokeFor` getter and source tail. `HandlerProof`
derives getter success from a successful snapshot and proves exact dispatch for
both original constructor error payloads. The overflow branch calls
`capacity_overflow()`; the allocation branch calls `handle_alloc_error(layout)`.
`HandlerProjectionProof` preserves the complete modeled execution trace,
reachability and well-formedness, including failures and partial executions.

The two terminal bodies remain explicit parameters. Their input contexts follow
the validated signatures; an empty enumeration represents the uninhabited
logical `!` result, and no logical value can inhabit it. These proofs do not
assert native panic/abort behavior or native stack allocation. The root composition below connects the outer constructor error arm.
Terminal-helper refinement, destruction/reclamation, native ABI/compiler/
lifetime correspondence, physical-work accounting and the final security bound
remain open.

Twelve handler regressions cover both dispatches, the forwarded allocation size,
untouched overflow padding, retained loans, invalid inputs and placement,
unwind cleanup and rejected normal terminal returns. Source mutation controls
also reject handler changes and broken links between the two extractions.

Handler validation: 1,027 dependency audits and 194 rejecting controls pass,
covering 419 constructor declarations and 54 linked getter declarations. The
constructor profile now has 142 source examples; the 151 shared-model examples
retain their prior scope. All four related source gates pass. The unchanged
library, root tests, toolchain, dependencies and full-check scripts permit reuse
of the successful 11101-job full project check.

## Root construction with owned-error handling

`handledRootInvoke` connects the original root, Vec and RawVec caller bodies to
the shared constructor and checked error handler. The reifier now validates the
complete outer error arm: moving the error out of `Result::Err`, retagging it,
moving it into `handle_error`, storing its uninhabited result, and the exact
normal/unwind storage cleanup. It also checks the previously unprocessed unwind
successors of the three outer constructor calls.

Typed continuation composition supplies the checked local-materialization effect
while reusing the existing evaluators. `handled_call_legacy` proves that ordinary
calls retain exactly their previous interpreter semantics. `handledAmbient`
instantiates the nominal error and uninhabited-return types for the error locals.
The earlier `unifiedCapacityRoot` retains its prior baseline scope;
`handledRootInvoke` is the entry point with the connected error path.

`OuterProof` proves complete root execution for zero capacity and successful
allocation, and connects rejected capacities and normal allocation failure to
`outerErrorEval`. The latter's payload move and typed handler invocation are
proved independently, and compose with the prior handler snapshot/dispatch
results. Successful snapshot execution is still the explicit storage-
materialization boundary. Terminal routines remain model parameters. Unwind
cleanup is executed through each caller, and failure retains every completed
modeled operation.

`OuterProjectionProof` establishes execution projection, reachability and
well-formedness for the entire new entry point and every outcome. This extends
the storage-loan reachability relation. Native stack/compiler/ABI/lifetime
correspondence, terminal-helper behavior, destruction/reclamation, physical
attacker-work accounting and the final security inequality remain open.

Root-composition validation: 1,088 dependency audits and 212 rejecting controls
pass, covering 480 constructor declarations and 54 linked getter declarations.
The 155 source examples include 13 new full-root regressions for both error
variants, dynamic allocation-size forwarding, successful allocation, zero
capacity, moved payload locals, retained execution effects and unwind
propagation. All four related extraction gates pass. The unchanged shared
library, root tests, toolchain, dependencies and full-check scripts permit reuse
of the successful 11101-job full project check.

## Terminal helpers through formatting and panic boundaries

The reifier now validates the complete bodies of `capacity_overflow`,
`handle_alloc_error` and its nested `ct_error`: signatures, local types,
copy/retag modes, the one-element layout tuple, its moved field, exact string
literals, formatter calls, cleanup and distinct `Panic` versus undefined-behavior
exits. It also validates the foreign `Arguments::from_str` declaration, method
owner/instantiation and the retained 16-byte formatting-argument layout.

`terminalAllocationEval` interprets the allocation wrapper's source tuple and
typed call to `terminalCtEval`. The forwarding theorem covers every valid layout
and arbitrary modeled formatter/panic callbacks. The two formatting helpers pass
exactly `capacity overflow` and `allocation failed`, check returned formatting
values, run their source storage cleanup, and reach the named
`core::panicking::panic_fmt` boundary. Normal returns from that uninhabited panic
boundary are rejected in the model. A retained `Panic` is not silently interpreted
as an abort.

The formatter receives the literal as a logical String and returns an abstract
nominal `Arguments` value; native `&str`/`Arguments` representation and calling
conventions remain explicit obligations. Formatting and panic are external
callbacks. `TerminalProjectionProof` requires their execution-projection
contracts and preserves their actual effects through every helper outcome.
Reachability and well-formedness are consequently conditional on those stated
contracts. Source control flow alone supplies no proof of native panic/abort
behavior or formatting work cost.

These helpers currently have independent typed entry points
`terminalOverflowInvoke` and `terminalAllocationInvoke`. The root composition below threads them into the handler and root continuation
interfaces through `terminalRootInvoke`. `handledRootInvoke` retains its prior
terminal-body parameters as a checked specialization baseline. Native
stack/compiler/ABI/lifetime correspondence, destruction/reclamation, physical
attacker-work accounting and the final security inequality remain open.

Terminal-helper validation: 1,143 dependency audits and 241 rejecting controls
pass, covering 535 constructor/helper declarations and 54 linked getter
declarations. The profile has 170 source examples, including 15 new helper
regressions for literals, the named panic exit, tuple forwarding, malformed
results, unwinding and retained callback effects. The 151 shared-model examples
retain their prior scope. The unchanged library, root tests, toolchain,
dependencies and full-check scripts permit reuse of the successful 11101-job
full project check.

## Root execution through the retained terminal helpers

`terminalRootInvoke` now runs the retained terminal helpers from both constructor
error paths. The handler enters the complete helper-local contexts, including
the allocation wrapper's tuple temporaries, and forwards through `ct_error` to
the formatter and named panic boundary. The terminal routines are no longer
arbitrary terminal-body parameters of this new entry point; the remaining
external callbacks are the formatter and panic boundary themselves.

The generalized `effectHandlerEval` and root continuations are emitted from the
same already-validated source templates. `EffectRootProof` proves specialization
to the previous handler/root implementations and carries over zero, success,
rejected-capacity and allocation-failure behavior. `TerminalHandlerProof` derives
checked getter success from a successful snapshot, dispatches each kind into its
complete helper context, and executes the source caller cleanup.
`TerminalRootProof` composes both error paths through those helpers without an
assumed getter result. Modeled allocator/shim results and successful error-local
snapshot execution remain explicit boundaries in the corresponding theorems.

`TerminalRootProjectionProof` preserves every executed operation, including
failures and external-callback effects. Its root reachability and well-formedness
results require the explicit formatter/panic execution contracts. The logical
String/abstract Arguments carrier, native stack/reference/compiler/ABI/lifetime
correspondence, actual formatter/panic behavior, destruction/reclamation,
physical attacker-work accounting and the final security inequality remain
open. The generalized previous entry points retain their documented scope.

Terminal-root validation: 1,206 dependency audits and 247 rejecting controls
pass, covering 598 constructor/helper/composition declarations and 54 linked
getter declarations. The 186 source examples include 16 new full-root tests for
both literals, named panic dispatch, malformed results, unwinding, callback
effects, failed placement, successful allocation, zero capacity and conditional
well-formedness. The 151 shared-model examples retain their prior scope. The
unchanged library, root tests, toolchain, dependencies and full-check scripts
permit reuse of the successful 11101-job full project check.

## Allocation coverage and returned-vector provenance

`AllocationCoverageProof` classifies every supplied allocator address:
the checked primitive either rejects it, retaining its incoming state, or
produces the fresh non-null pointer and allocated heap. Its exact-success lemma
identifies the fresh block and generation, resulting state and validated block
geometry. Invalid allocator results now propagate through the runtime,
implementation, method, constructor and all root callers, preserving the actual
failed prefix. Generic terminal constructor outcomes also propagate through the
root callers.

`terminal_root_normal_allocation` covers every allocator outcome after the
actual modeled shim returns unit. It computes `NativeAllocatorExecution.run`
instead of assuming a successful allocation result: normalized null reaches the
error handler, a rejected address remains invalid, and a successful checked
allocation returns its vector. The original shim result and starting-state
conditions remain explicit. Native allocator ABI correspondence remains open.

`ReturnExclusionProof` shows that rejected capacities and normalized null
allocation cannot return a vector, without a snapshot-success premise or
formatter/panic execution contracts. Any returned vector therefore has capacity
below the signed layout limit. For positive capacity and a normal shim return,
`terminal_root_return_fresh_allocation` identifies its actual checked allocation,
returned vector pointer/capacity, fresh block and generation, validated geometry
and final allocator state. Zero capacity retains its separate allocation-free
result. These are source-model return/ownership facts; connecting returned setup
to native PBS acceptance and the physical attacker-work inequality remains open.

The ten new regressions include a symbolic allocator-outcome theorem, zero and
overflowing addresses, overlap rejection, a successful second allocation with a
new generation, malformed snapshot placement, error-return exclusion for
arbitrary formatter/panic callbacks, and the zero-capacity case. The four related
extraction profiles are reused only after verifying that every recorded input
hash remains current. Their source/proof inputs are unchanged by this extension.

Allocation-coverage validation: 1,226 dependency audits and 247 rejecting
controls pass, covering 618 constructor/helper/composition declarations and 54
linked getter declarations. All 196 source examples pass, including ten new
coverage regressions. The four related profiles retain valid input/log/manifest
hashes and their existing proof scope; their gates are reused. The unchanged
library, root tests, toolchain, dependencies and full-check scripts permit reuse
of the successful 11101-job full project check.
