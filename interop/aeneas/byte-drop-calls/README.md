# Retained byte-drop calls into the original slice loop

This profile interprets all five retained bodies of the original
[`byte-drop-loop` probe](../byte-drop-loop/fixture.rs). Functions 0–3 construct a
slice pointer, borrow it and call the original slice destructor. Function 4 is
the complete typed loop from the [loop profile](../byte-loop-body/README.md).
Its original code is embedded directly; there are no callee callbacks or
function-name replacements.

`NativeByteDropCalls` composes finite typed bodies and the unbounded typed loop
relation. Calls evaluate actual operands, preserve caller moves, initialize
callee locals, execute the retained callee code, write its returned value and
continue with the retained caller suffix. Unwinding executes the retained
unwind block. Invalid and unsupported outcomes preserve the machine state of
the executed prefix. A continued callee cannot silently produce a unit return.
Normal unit returns explicitly close leases created since call entry; failed
result writes preserve the already executed cleanup. Storage markers themselves
do not end loans. Projection and reachability theorems cover every execution
and decoded root invocation.

The source proofs connect the original pointer-parts body and original slice
loop to this call relation. Source regressions construct whole-call-chain
execution derivations for empty and three-byte slices, checking the final tag
counter, closed leases and unchanged heap. They also check missing raw inputs,
argument type rejection and an oversized slice rejected by the original borrow
statement. Model regressions check unit/reference returns, unwind behavior,
continued callees, cleanup failures, result-write failure and argument moves.

Function 3 retains its original `Foreign` classification and structured body.
Interpreting that retained body does **not** establish native foreign-call
correctness. Both call-return cleanup and backedge cleanup are explicit ghost
composition. Rust lifetime/alias correspondence, region erasure, the Rust ABI,
compiler correctness, the outer `Vec` destructor and allocator/deallocator path,
physical-work refinement and the final security theorem remain open. No native
constructor acceptance or allocator semantics are supplied by this profile.

Reproduce using the frozen compiler tools:

```sh
scripts/check-hasteboots-byte-drop-calls \
  --build-receipt build/hasteboots-extraction/inline-tools-build-b6esls36/manifest.json
```

The gate reruns the typed-loop parent profile, re-extracts the unchanged Rust
fixture, compares all five retained declarations and generated code, checks
malformed source/call variants, and audits explicit model/source declarations.
A supported mutation swaps two original caller storage-dead statements; the
emitted code changes and its source proofs/regressions are kernel checked again.
