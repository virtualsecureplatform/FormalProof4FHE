# Initialized enum tags after payload moves

The `discriminants` frontend profile extends `constructor-typing` with a
dedicated discriminant reader. Optimized Rust MIR can inspect an enum tag in a
cleanup block after moving out its payload. The previous match implementation
used a full-value reader, which rejected the moved payload even though the
operation consumes only the initialized discriminant.

The new reader performs the existing path and loan preparation, then accepts a
concrete enum with an initialized variant ID. It does not read, copy or restore
payload fields. A symbolic enum retains the earlier full-read precondition
before expansion. An uninitialized tag is rejected. Ordinary payload reads,
moves, borrow checks, global invariants and declared signatures keep their
existing checks. Only enum `Match` uses this operation.

The Rust fixture constructs an owned aggregate containing a byte vector and an
arbitrary second value, propagates a Result error, and returns the vector on
success. Extraction explicitly selects `--mir optimized`, reproducing the MIR
stage available for dependencies. The official frontend rejects the cleanup
match with the bottom-value error. The reviewed profile translates the same IR
without rewriting it. `Generated.lean` is an exact reviewed snapshot.

Three kernel theorems establish exact successful output, exact error payload
and their combined case distinction. A second fixture retains the original
`core::marker::PhantomData` clone body. Three further theorems establish exact
native clone/wrapper results and the singleton carrier, for arbitrary element
types. This removes the opaque clone callback from the native integer probe.

The gate first rechecks the five earlier trait/effect dependency audits on this
frontend, then checks fifteen combined audits: nine from cleanup handling plus
the native PhantomData carrier, clone, wrapper and three theorems. Both complete
generated snapshots are checked. Only propext, Classical.choice and Quot.sound
are permitted. Source,
package, executable, tool, prepared backend, input, output and proof hashes are
checked or recorded. Proof limits remain 200000/1000.

```
scripts/build-hasteboots-static-frontend --profile discriminants \
  --source /tmp/hasteboots-aeneas-discriminant-prototype \
  --opam /tmp/hasteboots-ocaml-bootstrap/opam \
  --opam-root /tmp/hasteboots-ocaml-bootstrap/root --switch hasteboots-static
scripts/probe-hasteboots-discriminants \
  --tools /tmp/hasteboots-aeneas-tools --backend /tmp/hasteboots-aeneas-m0 \
  --build-receipt /path/printed/by/builder/manifest.json
scripts/check-hasteboots-discriminant-guards
```

Use a clean isolated Aeneas checkout at
`15b968482b0dcd7aae45020b6d1bca39b5024af5` and a clean Charon library at
`ef3748c1a92c6acc402f978770193d34adc0fe6e` through its `charon` symlink.
Formatting and upstream traits/arrays regeneration are required checks. No
Lean backend file or native HasteBoots source changes.

This is a compiler regression gate. It does not prove compiler correctness,
destructor effects or physical work. The separately reproducible `word` mode in
`probe-hasteboots-code-serialization` now translates all 32 transparent native
Bincode integer-encoding functions, including the retained clone. Its generated
output still contains three external axioms for standard-library error types. That output
is not an accepted byte refinement. Actual Serde's recursive
interface, specialization lifetimes, constructor/NTT support, heap refinement
and complete application security remain open.
