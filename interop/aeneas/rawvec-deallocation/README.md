# Original RawVec deallocation caller

This profile composes the original `alloc::raw_vec::deallocate` caller with the
original `current_memory` and Global deallocation bodies over the checked heap.
It retains mutable receiver entry, both shared reference constructors, the
original Option match and payload projections, region instantiations, call/unwind
edges, storage changes and early returns. The `__rust_dealloc` leaf remains the
existing explicit logical specification; its Rust body/ABI and native allocator
correspondence are not proved.

`NativeRawVecBorrow` decodes an existing exclusive sixteen-byte, alignment-eight
receiver. It resolves reference and complete pointer identities, derives the
whole-object or zero-byte allocator-field address, then executes an actual shared
reborrow. It supplies no caller-selected tag, extent or origin. Issuance failure
retains an address step already executed. Six model theorems prove decoding,
execution/reachability, successful-step witnesses, heap preservation and that the
returned reference was actually issued into the registry. Borrowing a place uses
checked reads without copying exclusive ownership; ordinary copy still rejects
an exclusive reference. One interpreter-helper projection theorem extends the
existing rvalue/body/invocation projection and reachability results.

Nineteen new declaration audits and fifteen model regressions cover full-object
and allocator-field loans, shifted reference registers, wrong/revoked parents,
exclusive-copy rejection and blocked issuance with its prefix retained.

The source reifier validates source receiver mutability, nominal projection
owners, reference metadata, regions/call instantiations, exhaustiveness, external
symbol/signature and storage geometry. Original classifications are preserved.
Its assignment hook and continuation composition leave the earlier generated
`current_memory` body unchanged. The source declares no nominal type-ID equality
to bridge the call: the retained caller, Global method and external leaf use the
same pointer/alignment declaration instances here.

Eight source theorems prove the four execution projections, the zero-element
caller outcome and heap preservation, and exact byte-aligned external-entry
semantics plus allocation removal on every normal return from that entry shape.
The zero-element theorem includes explicit scope settlement. It does not identify
that ghost cleanup with Rust lifetime endings. The external-entry theorem is for
the logical specified leaf; it is not a native allocator proof or a universal
nonzero caller-outcome theorem.

Fifteen source regressions exercise the full nonzero caller path removing one
allocation, both zero paths preserving allocations, loan cleanup preserving the
incoming mutable loan, wrong layout/alignment/receiver, high-bit failures,
double-free rejection, old-generation rejection after address reuse, and rejection
while the data allocation has an active borrow. The altered reuse/double-free
cases test defensive model behavior, not validity of those executions in Rust.

Run:

```sh
scripts/check-hasteboots-rawvec-deallocation \
  --build-receipt build/hasteboots-extraction/inline-tools-build-b6esls36/manifest.json
scripts/check
```

The gate passed 235 dependency audits and twenty-four rejection controls with
fresh extraction and retained-source comparison. Swapping the original Option
branch bodies changes the generated code and is checked in Lean: Some then skips
the free, and None rejects its invalid payload projection. The earlier Global gate
passed again with 258 audits and 34 controls, and `current_memory` with 230 audits
and twenty-three controls. The full `scripts/check` run passed its 11,014-job
build and subsequent smoke checks. The final source gate additionally checks the
external-entry theorems. See `regression.json` for receipts and log hashes.

The original RawVec drop methods/glue now compose in the sibling `rawvec-drop`
profile. Next compose outer Vec destruction with byte-drop traversal. A universal nonzero caller
characterization, native constructor/carrier/reference/stack/layout/ABI and
lifetime/compiler correspondence, helper refinement, allocator correctness,
physical work and the final expected-work security theorem remain open. Scope
cleanup is still explicit ghost composition. No native constructor acceptance or
caller-work certificate is supplied by this profile.
