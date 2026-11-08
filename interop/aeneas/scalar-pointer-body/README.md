# Retained scalar/pointer LLBC body interpretation

Run `scripts/check-hasteboots-scalar-pointer-body --build-receipt <receipt> --backend <backend>`.
This is a separate experimental Charon-to-Lean body profile. It does **not** add
raw dereferences to Aeneas or accept the native constructor. The gate verifies
the unchanged Aeneas rejection alongside the new interpretation.

The frozen coupled tools extract five local wrappers and the four original
monomorphic `core::ptr::{read,write}` bodies for `u64` and `*mut u64`. Original
calls, dereference assignments, local moves, storage-live/dead markers, unit
assignments and unwind blocks are reified into `NativeScalarLLBC.Body`. Calls
embed their resolved original callee bodies; there are no externally supplied
callee functions or function-name semantic replacements. Recursive call graphs,
non-Copy types, references, non-unit aggregates, loops, traits, indirect calls,
residual runtime-check queries and drop effects are rejected. Compilation uses
the ordinary pinned sysroot with precise/desugared drops, preserved allocator
policy and compiler-evaluated runtime checks. Both scalar and pointer `(size,
alignment) = (8,8)` facts come from original rustc-evaluated `usize` constants.

`Generated.lean` is reproduced exactly from LLBC. Function/source spans and body
hashes are recorded in the gate receipt. `Proof.lean` proves each original memory
body's exact byte-heap behavior, wrapper agreement, and the replacement sequence.
`Bridge.lean` connects the pointer bodies to successful closed reference-machine
operations and derives the corresponding permissions from the executed checks.
Pointer loads/stores use allocation-origin metadata; numerical writes clear it.
`Smoke.lean` checks concrete initialization, pointer-origin preservation/erasure,
alignment rejection and replacement. Root interpreter regressions additionally
check local liveness/moves and preservation of earlier writes on invalid and
unwind outcomes. Every retained callee is interpreted rather than summarized by
a postcondition. There is no recursion fuel or arbitrary call-depth cap.

The receipt covers rejecting source/target/schema controls, a supported body
mutation that must change the reification, kernel dependency audits, the parent
word-memory gate and unchanged Aeneas rejection. The reifier and Charon remain
unverified translation components. The kernel results concern the reified LLBC
semantics and its heap interpretation, not a proof of Rust/compiler correctness.
Complete native constructor/lifecycle/typed source correspondence, Rust alias
semantics, actor authority, references stored in heap fields and actual work
accounting remain open. No security theorem is claimed here.
