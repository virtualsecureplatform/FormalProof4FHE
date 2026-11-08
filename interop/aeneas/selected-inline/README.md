# Coupled selected-function extraction experiment

This frontend patch applies to Aeneas commit
`15b968482b0dcd7aae45020b6d1bca39b5024af5` and must use the Charon library at
`ef3748c1a92c6acc402f978770193d34adc0fe6e` with
`interop/charon/inline-functions/charon.patch`. It includes the reviewed
`u32-ranges` frontend and the metadata annotation switch. It adds two opt-in
compatibility features for full monomorphic extraction:

- `-disambiguate-instantiated-names` derives identifier suffixes from the full
  original instantiated names. Hashes select names only; collisions remain
  fatal errors and supply no cryptographic assumption.
- `-monomorphic-builtin-shapes` requires Lean and monomorphic Charon IR. It
  emits the actual monomorphic trait declarations/instances instead of
  substituting richer generic backend traits. It retains `Destruct` and its
  executable methods. A concrete scalar option uses the standard option
  representation only after checking its original builtin name, empty generic
  parameters and exact two-variant/field shape. Other types retain their
  extracted declarations. Export uses the same checked builtin information.

Variable basenames also handle trailing instantiation metadata. There are no
new lifetime substitutions, borrow-check bypasses, trait-constraint removals,
post-hoc IR edits or rewritten generated terms in this profile. The eight
existing frontend profiles and their builders are unchanged.

The patches are compiler experiments, not verified compiler passes. Kernel
checking and the fixture equivalence below do not establish native constructor,
heap, cost or security refinement.

## Build and check

Prepare isolated checkouts at the revisions above. Apply the two patches with
`git apply --check` followed by `git apply`. Point the frontend's ignored root
`charon` symlink at the patched Charon checkout; its tracked `src/charon`
symlink remains unchanged. Use the reviewed 132-package OCaml switch from
`interop/aeneas/static-strings/opam-packages.json` and the pinned opam binary.
The build script checks exact complete source diffs, including untracked source
files, toolchain pins, library linkage and package versions before building. It
copies all three executables into a separate receipt directory.

```sh
scripts/build-hasteboots-inline-tools \
  --charon /tmp/hasteboots-charon-inline \
  --frontend /tmp/hasteboots-aeneas-inline \
  --opam /tmp/hasteboots-ocaml-bootstrap/opam \
  --opam-root /tmp/hasteboots-ocaml-bootstrap/root --switch hasteboots-static

scripts/check-hasteboots-inline-equivalence-guards
scripts/check-hasteboots-inline-equivalence \
  --build-receipt build/hasteboots-extraction/inline-tools-build-RECEIPT/manifest.json \
  --backend /tmp/hasteboots-aeneas-m0
```

The equivalence gate freshly extracts the original regression fixture, validates
IR and target before running Aeneas, rejects error logs even with a zero exit
status, compares the complete generated module against `Candidate.lean`, then
kernel-checks it alongside the reviewed `Baseline.lean` and `Equivalence.lean`.
Only imports change for backend compatibility. Proof limits remain 200000
heartbeats and recursion depth 1000.

Six theorems establish two-sided inverses for the returned result/state codecs,
complete `twice` equivalence (including errors, overflow and divergence), and
`capture` equivalence for all inputs. Seven source definitions, four codecs and
six theorems passed 17 exact dependency audits. Allowed axioms are only
`propext`, `Classical.choice` and `Quot.sound`. Five rejection tests cover
altered/truncated/admitted output, invalid IR, missing inverses/proofs,
error logs and dependency reports. All 114 extraction guard tests passed.
The patched Charon's full upstream suite and Clippy passed, including six
selected-inlining UI cases. Aeneas array/trait outputs were regenerated and
borrow-checking passed with the coupled tools and default feature flags.

## Native constructor frontier

```sh
scripts/probe-hasteboots-inline-constructor \
  --build-receipt build/hasteboots-extraction/inline-tools-build-RECEIPT/manifest.json \
  --backend /tmp/hasteboots-aeneas-m0
```

This probe copies the existing wrapper and locked dependency fixture, checks the
unchanged native revision, extracts the original Gold constructor with both
option helpers inlined, validates both original wrapper/constructor bodies,
and attempts strict translation. It does not make the encoder opaque or force
Rust MIR inlining. Its receipt records IR, source/tool bindings and failed
frontend logs. Any admitted constructor output or unapproved kernel dependency
would also fail.

The current native attempt has valid IR, 23 retained functions and no residual
type constraints. Aeneas then rejects a borrow invariant at the closure call in
`Option::is_none_or` (core `option.rs` line 1335). There is no accepted native
constructor Lean module or refinement theorem. String drop glue also remains
opaque in this IR and must be resolved before an admission-free module could
pass. Next work should reproduce and repair borrow tracking without disabling
invariants, then close the native constructor/heap correspondence and continue
the full security plan.
