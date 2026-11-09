# Enum construction and match bodies

This profile translates three complete, extracted Rust probe bodies: constructing
`Some((pointer, layout))`, constructing `None`, and selecting a Layout from the
Some payload or a fallback argument. The probe also includes ordinary Vec drop,
so the reifier anchors its enum schema to the actual retained
`alloc::raw_vec::current_memory` result. The probe functions and that result use
the same nominal Option declaration. Foreign declarations keep their original
classification; no Rust helper body is replaced with success.

The aggregate interpreter now represents a binary choice inside a nominal record.
`Step.active` checks the active side during field projection and replacement.
`sideAt` and `selectChoice` read the variant without reading payload fields that
may have been moved. Entirely moved enum storage still rejects the match. Copy
checking covers both branch types, and retagging visits only the active payload,
retaining actual loan operations and any failed prefix.

`Rvalue.aggregate` evaluates constructor operands in source order and builds the
checked field tree. `Body.matchChoice` preserves both source branches, early
return, unwind, rejection and the shared suffix. The reifier validates variant
owners, field indices and types, tuple arity, constructor fields, exhaustive
match labels and every statement. Existing heap-execution projection and
reachability proofs cover these new constructors. Four bridge lemmas in
`NativeVariantValues` relate binary enum typing, reads, replacement and tag
selection to the aggregate representation.

There are seventeen new model regressions and fifteen new declaration audits.
The source profile has three theorems (exact None invocation and whole-body heap
projections for the other functions) and eight regressions. They exercise both
match branches, complete Some construction with pointer provenance, fallback
selection, malformed payloads, wrong nominal tags, invalid alignment and missing
pointer registers. These concrete regressions do not assert a universal returned
payload theorem for the two parameterized functions.

Run:

```sh
scripts/check-hasteboots-variant-body \
  --build-receipt build/hasteboots-extraction/inline-tools-build-b6esls36/manifest.json
scripts/check
```

The source gate passed 169 dependency audits and seventeen rejecting controls.
Swapping the original match bodies changes the generated code and makes None
reject the Some-only projection, checked in Lean. Disabling a source retag flag
also changes the generated code and passes the original body proofs/regressions.
The pre-existing Global gate was revalidated with 174 audits and 34 rejection
controls, and the earlier RawVec schema gate passed again with 63 audits and
eighteen rejection controls. The full `scripts/check` run passed, including its 11,003-job build and subsequent
smoke checks. See `regression.json` for receipts and log hashes.

These are complete by-value probe translations, not translations of RawVec or
Vec cleanup. Logical locals still need native stack/layout/ABI correspondence.
The next native frontier is checked resident-reference loads of RawVec capacity
and pointer fields, recovery of pointer shadow provenance, the constrained
capacity carrier and unchecked product, and composition of original cleanup
bodies with the checked Global dispatch. Rust lifetime/compiler correspondence,
the external allocator contract, physical-work refinement and the final
expected-work security theorem remain open. No constructor-acceptance or work
certificate is supplied by this profile.
