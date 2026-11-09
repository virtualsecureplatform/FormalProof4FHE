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
