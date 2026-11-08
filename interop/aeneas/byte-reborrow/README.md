# Original local mutable reborrow and checked child scope

`fixture.rs` takes a mutable slice, checks its index, creates a local mutable
cell reference and calls a helper that reads/replaces the cell. Charon retains
both source bodies and their signature lifetimes. The gate requires the
original helper load/store, mutable indexing, helper call, two mutable reference
rvalues and two-phase reference rvalue. The unedited Aeneas output contains the
actual mutable indexing continuation and passes the helper's returned cell
value back through it. Four theorems prove the full input/output behavior,
including the old byte and out-of-bounds result.

`NativeByteReborrow.replaceAt` is a closed model call: resolve the parent,
check bounds, compute the byte pointer, acquire a fresh exclusive child, read
and replace its byte, and end that child. It has no callee callback. Outer
`none` rejects invalid access; an inner `none` returns out of bounds with the
unchanged state. Thirteen model theorems prove exact execution decomposition,
well-formedness, current heap changes, original caller lease restoration,
fresh-tag consumption and permanent child revocation across arbitrary future
ledger transitions. They also derive child read/write permission from the
checked initial grant, guarantee completion and release after that grant, and
show the call consists of existing borrow/write/end state transitions. These
logical transitions are not a physical instruction count or attacker-work floor.

Three bridge theorems relate this call to the extracted source function. A
successful call returns the source-selected old byte, produces the same updated
source slice/current heap view and restores the caller's leases. A checked
initial child grant suffices to derive complete call execution; the helper's
read, write and release success are proved. Out-of-bounds execution changes
neither slice nor model state. Twelve executable regressions cover the old byte,
updated heap, parent reuse, revoked/non-reused tags, shared/stale rejection,
existing disjoint/overlapping children and nesting through a child.

```sh
scripts/check-hasteboots-byte-reborrow-guards
scripts/check-hasteboots-byte-reborrow \
  --build-receipt build/hasteboots-extraction/inline-tools-build-RECEIPT/manifest.json \
  --backend /tmp/hasteboots-aeneas-m0
```

The gate checks the complete original-source graph/snapshot, all 62 combined
model/source/runtime/bridge declarations and the parent source/heap gate.
Persistent root audits guard all fourteen new model declarations. Four guard
tests reject lost reference/call structure, altered backward values, removed
proofs and admissions. Only the three standard Lean axioms are allowed.

This is a local call-boundary simulation against the checked ledger, not a
verified compiler pass or per-MIR-event lifetime instrumentation. The intermediate
Rust reference identities and two-phase reservation/activation are retained in
source evidence but are not identified with separate model tags. The model's
fresh child describes the cell call's exclusive scope. Binding that scope to
actual native reference ownership, all intermediate source lifetimes and Rust's
alias rules remains open. Numeric ghost tags are not unforgeable actor tokens.
The fixture is a verification fixture, not an accepted HasteBoots constructor.

The compiler, Lean backend and production Rust are unchanged in this milestone.
Original raw-pointer dereference still blocks the native constructor. Typed
values/strides, allocator/destructor/deallocator, compiler/caller and
NTT/SIMD/scheduler refinement, causal lifetime oracle/owner coverage, BabyBear
and the final 128-bit expected physical attacker-work theorem remain open.
