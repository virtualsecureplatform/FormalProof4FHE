# Original RawVec drop glue and method

This profile composes original `alloc::raw_vec::RawVec::drop_glue` and
`alloc::raw_vec::drop` with the existing RawVec deallocation, `current_memory`,
Global dispatch and specified external deallocation leaf. It retains source
classifications, nominal types, layouts, regions, storage operations, call/unwind
edges, and the adjacent `TwoPhaseMut` constructor/call pair. It does not yet
translate outer Vec destruction or identify this model with native Rust execution.

`NativeRawVecMutBorrow` separates reservation from activation. Reservation resolves
an existing exclusive, sixteen-byte, alignment-eight receiver, executes its
address derivation and checks shared permission. A theorem proves it changes no
loan, reference registry, birth history, fresh-tag counter or heap. Activation
resolves the complete identities again and executes an actual exclusive reborrow;
its returned reference uses the machine's fresh tag. Ordinary `Mut` uses immediate
activation. The interpreter reads a borrow's parent place without copying its
exclusive reference; copying that reference still rejects.

The source translation accepts the two-phase case only as an adjacent borrow/call
pair whose first argument moves the reserved local and whose remaining argument
is the closed byte Layout global. The layout is evaluated before activation. No
reference value is issued or stored at reservation. The exclusive child is issued,
stored and moved at activation, before the actual callee is entered. Failed
argument evaluation retains the address prefix without issuing a loan. The
interpreter's body/invocation projection proofs cover this new node, including
its callee, unwind, suffix and settlement. This restricted ordering is not a
general Rust two-phase-borrow or lifetime correspondence theorem.

The byte Layout global is checked against its retained named declaration,
instantiation, type and nested value. Its enum variant index zero denotes the
validated alignment discriminant one; the translator does not use index zero as
an alignment word. RawVec's inner field is checked at byte offset zero, its marker
at sixteen, and the complete object has size sixteen and alignment eight.

Six new borrow theorems, two interpreter helper theorems, eighteen declaration
checks and sixteen model regressions cover reservation, activation, rejection
prefixes, conflicting children, exclusive-copy rejection, slot occupancy and the
closed Layout operand. Four source theorems give body and invocation projections
for both original roots. Eleven source regressions check nonempty deallocation,
zero-capacity heap preservation, cleanup retaining the incoming loan, wrong entry,
high-bit capacity, double free, old generations after address reuse and a blocking
loan. Universal nonzero destructor-outcome characterization remains open.

Run:

```sh
scripts/check-hasteboots-rawvec-drop \
  --build-receipt build/hasteboots-extraction/inline-tools-build-b6esls36/manifest.json
scripts/check
```

The source gate passed 252 dependency audits and 44 rejecting controls, using fresh
extraction and retained-source comparison. A supported `TwoPhaseMut` to `Mut`
mutation changes generated code and passes the destructor outcome regressions;
the separate interpreter regression distinguishes their failed-argument prefixes.
The parent deallocation/current-memory/Global profiles passed again with
256/251/279 audits and 24/23/34 rejecting controls. Validation is recorded in
`regression.json` with receipts and hashes. Full `scripts/check` passed its
11,017-job build and subsequent smoke checks.

Next compose original outer Vec destruction with the existing byte-drop traversal
and these RawVec bodies. Native construction, carrier/reference/stack/layout/ABI,
compiler and lifetime refinement, helper and allocator correctness, physical work
and the final expected-work security theorem remain open. Scope settlement is
explicit ghost composition. The external allocator body is still specified,
not interpreted. This profile supplies no native constructor acceptance or
attacker-work certificate.
