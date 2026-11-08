# Typed interpretation of the original byte-slice loop

This profile reifies the complete original slice-body declaration (function 4)
from the five-body `byte-drop-loop` probe. Every original prefix, loop-body and
suffix statement is interpreted as typed LLBC code. The source function's
single outer loop is represented separately from its finite blocks; nested
loops, nonzero break/continue depths and unsupported operators are rejected.
There are no callee callbacks or function-name semantic replacements.

`NativeByteLoopLLBC` tracks typed local slots for unit, usize, booleans, raw byte
pointers, mutable slice references and mutable byte references. It implements
copy/move operands, slice metadata, numeric literals, explicit `WithRetag` flags,
equality, wrapping addition, checked reborrowing, mutable byte indexing and raw
pointer recovery. Index bounds failure executes the retained unwind block;
permission failures retain every executed machine prefix. The source loop's
bounded cursor never reaches its bounds-failure branch.

Storage markers change local slots only. `StorageLive` resets an existing slot,
and `StorageDead` also succeeds on an already dead slot. This is necessary for
the actual backedge's repeated live markers and the empty-loop suffix's dead
markers. Neither marker silently ends a ledger lease.

The unbounded `LoopRuns` and `Executes` relations compose finite-block execution
with explicit checked cleanup at a backedge. Determinism and machine-run
projection are proved. `Invokes` accepts a reference-register index; its slice
extent is recovered from a resident exclusive byte-aligned lease, and no
external pointer origin, tag or separate extent is accepted by that decoder.
This is a logical checked interface, not a proved implementation of the Rust ABI.

The original-source proofs establish exact entry, guard, exit and iteration
behavior, including all failed-iteration machine states. Induction on the
terminating traversal constructs an original-loop execution for every input
slice. Every original execution and decoded invocation then agrees with the
traversal on the complete machine state and normal-unit success. Heap framing
and successful unit return follow. The theorem is for arbitrary finite slice
extents, with no supplied execution budget or attacker-trial cap.

Reproduce with the frozen tool receipt:

```sh
scripts/check-hasteboots-byte-loop-body \
  --build-receipt build/hasteboots-extraction/inline-tools-build-b6esls36/manifest.json
```

The gate also reruns the byte-operation parent profile, re-extracts the original
probe, checks the complete retained function and generated code, checks malformed
source/target variants, and audits all explicit model/source declarations.
A positive source mutation changes the metadata use's retag flag from `No` to
`Yes`; the generated code changes, and its primitive metadata value has the same
proved behavior. The source still records the original flag in the main profile.

The backedge cleanup remains an explicit ghost composition. Agreement between
this scoped LLBC model and the traversal does not establish Rust aliasing,
lifetime endings, region erasure, compiler correctness or physical work.
The pointer/drop wrappers (functions 0–3), outer `Vec` destructor and allocator
path remain outside this interpreter. In particular, the generated `Foreign`
wrapper is neither reclassified nor replaced. Native constructor acceptance
and the final security/expected-work theorem remain open.
