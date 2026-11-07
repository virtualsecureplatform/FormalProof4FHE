# Native row metadata extraction diagnostics

These fixtures call the original BlockReedSolomonCode RowCode implementation;
they do not copy accessor bodies, replace the NTT backend or supply a context
certificate. They request precisely the block width, codeword-block count and
static domain separator consumed by Parameters::context_digest.

Run either diagnostic:

```
scripts/probe-hasteboots-row-metadata --tools /tmp/hasteboots-aeneas-tools --backend /tmp/hasteboots-aeneas-m0 --mode generic
scripts/probe-hasteboots-row-metadata --tools /tmp/hasteboots-aeneas-tools --backend /tmp/hasteboots-aeneas-m0 --mode concrete
```

Both modes first reproduce the accepted pinned registry extraction. They use
its locked dependencies, add the already-pinned algebra package as a direct
fixture dependency, check Charon's complete x86_64 little-endian target, and run
the unchanged official Aeneas with `-checks -sequential`, 200000 heartbeats and
recursion depth 1000. Native revision and tracked cleanliness are rechecked.
Each artifact records commands, source hashes, LLBC and compiler logs.

The generic fixture exposes a missing-borrow invariant failure at the call
returning the static domain slice. The concrete Goldilocks fixture additionally
reaches an unsupported associated-type constraint in ConcreteTable's root
method (SymbolicToPureTypes.ml line 1012). A prior overly broad selection also
reached the row encoder's unsupported outer-loop continue; the committed probe
selects only the three metadata methods.

A recognized diagnostic is still a rejected, unproved result, with a nonzero
exit status. Unknown failures remain unclassified and rejected. If translation
progresses, the probe still requires a reviewed snapshot and kernel refinement
proofs before acceptance. No generated terms, lifetimes, constraints or loop
bodies are rewritten. The accepted registry pipeline remains unchanged.

The next compiler work must isolate the missing-borrow failure while preserving
static borrow behavior, and resolve the
associated-type equality in the actual function signature. Dropping constraints,
adding opaque Formatter/NTT axioms or disabling invariants cannot close this
gate. Context formatting, Serde/bincode, hash updates, native owner selection,
heap and physical-work refinement remain open.
