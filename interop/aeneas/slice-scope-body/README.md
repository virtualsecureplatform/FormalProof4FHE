# Unit slice scopes and checked lease cleanup

This profile retains two original Rust unit-returning scope probes and the
original shared/mutable byte-slice constructor bodies they call. The shared
probe creates one temporary lease; the mutable probe creates two, including the
source reborrow. Unlike the reference-returning probes, these functions return
no reference. Their ordinary LLBC interpretation still retains the leases;
`invokeUnit` explicitly composes that source execution with checked cleanup.

`NativeReferenceCleanup` takes its scope boundary from the actual entry state's
fresh-tag counter and its cleanup candidates from the current resident lease
snapshot. Each candidate is resolved to an existing reference register and
passed to the closed reference machine's real `endBorrow` operation. Missing
registers, already-revoked tags and parents with resident children cause a
blocked result. The result records the executed prefix, current world and
unprocessed suffix. It never rolls back earlier successful cleanup.

The model proves that reachable machine states store leases in reverse creation
order and contain a reference register for each resident lease. These invariants
ensure scope cleanup completes for reachable states. Successful cleanup removes
exactly the snapshot's leases created since entry and preserves every older
lease. All outcomes project to actual closed-machine runs; cleanup preserves
bytes, pointer provenance, allocator history, reference registers, birth history,
fresh-tag counters and outputs. Ended references remain revoked. Physical
`free` is a subsequent operation with the allocator's actual permission checks.

The source equations retain local storage, original constructor calls, moves,
reference creation, inactive UB-check branches and exact empty-tuple aggregates.
The scope adapter adds only this empty-tuple rvalue to the earlier source
reifier; its other changes select a Lean namespace and import. It supplies no
callee summaries or function-name semantic replacements. Source bridge theorems
specialize the generic normal-unit cleanup result to the two original probes.

Reproduce with:

```sh
scripts/check-hasteboots-slice-scope-body \
  --build-receipt build/hasteboots-extraction/inline-tools-build-b6esls36/manifest.json
```

The gate also reruns the parent slice-reference profile with the same frozen
tools. It re-extracts release and debug-enabled probes, checks retained source,
rejecting controls and a supported syntax mutation, and checks the source
proofs, cleanup regressions and declaration dependencies in Lean.

This explicitly composed cleanup is not yet a proof of Rust lifetime endings
or actor ownership. The probes are ordinary finite scopes, not the native slice
drop loop. The retained native loop still needs metadata/arithmetic, indexing,
loop/control semantics and justified iteration lifetime boundaries. The full
`Vec<u8>` destructor, its allocator calls, compiler correctness, native work
semantics and final security theorem remain unproved. No destructor or physical
deallocation is replaced by an empty operation in this profile.
