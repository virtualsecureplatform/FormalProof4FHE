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

Variable basenames also handle trailing instantiation metadata. Symbolic and signature lifetimes are preserved. Runtime value types consistently
erase all lifetimes, including static lifetimes. There are no borrow-check
bypasses, trait-constraint removals, post-hoc IR edits or rewritten generated
terms in this profile. The eight
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
error logs and dependency reports. All 125 extraction guard tests passed.
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

The native static-reference borrowing failures are repaired. The probe now
explicitly requests precise drops and desugars them into calls before running
Aeneas with `-eval-drops`. Missing drop flags or any residual Drop statement,
including one in an unwind path, rejects before interpretation. This avoids
the default destructor-as-no-op abstraction for the native heap boundary.

With `--inline-ok-or` the current drop-preserving probe retains 34 functions,
passes interpretation and emits a complete Lean module. Goldilocks retains its
actual U64 representation and the usize intrinsic uses its closed model. The
module still fails admission checks on owned String drop glue; its original
rejection-path cleanup remains an explicit call. The receipt records the
extracted axioms and module hash. No native constructor refinement is accepted.

`--expand-string-cleanup` additionally exposes the original String type and
drop body. Its valid IR has 35 functions and no residual drops. String cleanup
then explicitly calls Vec<u8> cleanup; the Vec type and drop body remain opaque
and the module is rejected. This is a diagnostic of the next heap boundary,
not a trusted destructor implementation.

## Dead shared-loan cleanup regression

`static-error-option.rs` separates the inlined `ok_or` call from two ordinary
`match` controls. Before the cleanup repair, both controls translated and the
inlined call failed the marker invariant at `InterpReduceCollapse.ml:1137`.
`StaticErrorControls.lean` and `StaticErrorProof.lean` retain that checked
control baseline (three dependency audits).

The existing dead-loan cleanup checked that no corresponding shared borrower
exists and that the shared value has no nested borrow/loan. Its abstraction
guard nevertheless selected frozen (`can_end = false`) abstractions and skipped
endable ones, contrary to its comment. The guard now selects `can_end = true`;
frozen abstractions and all invariant checks remain protected. No predicate is
weakened to accept a live borrower.

The repaired extraction is `StaticErrorCandidate.lean`.
`StaticErrorEquivalence.lean` proves the inlined call equal to the direct match
for every input, including the exact static error string, and proves the eager
match equal to the direct match. All three source functions and both theorems
passed five exact allowed-axiom audits with unchanged proof limits:

```sh
scripts/check-hasteboots-static-error-option \
  --build-receipt build/hasteboots-extraction/inline-tools-build-RECEIPT/manifest.json \
  --backend /tmp/hasteboots-aeneas-m0
```

The gate freshly extracts the whole source with
`--inline-function core::option::_::ok_or`, validates IR before interpretation,
checks the complete retained snapshot and kernel-checks both equivalences.
Three additional rejection tests cover changed outputs, error labels, missing
source/proof coverage, opaque bodies and extraction options.

Full before/after upstream extraction with `IN_CI=1` completed the same 97 test
targets and rejected only `dyn.rs` for its existing erased signature lifetimes.
All 128 actually regenerated output files are byte-identical before/after;
`loan-regression.json` records the tool/patch/log hashes and per-file comparison.
This supports regression compatibility, not a proof of the compiler algorithm.
The original fixture also passed its fresh 17-audit gate with the repaired
frontend.

## Symbolic static-reference input regression

`static-result-input.rs` isolates input borrowing independently of the native
constructor. Before repair, reading `Error(&'static str).0` failed with a borrow
that had no backing loan. Shared static-reference expansion now registers the
backing loan using the same dummy-storage representation as static literals
and trait constants. Its value is the existing expansion linked to the source
symbol, rather than an unconstrained replacement. Runtime type erasure also
handles static lifetimes consistently; symbolic types retain their lifetime
information. All borrow and typing invariants remain enabled.

`StaticResultCandidate.lean` is the complete extraction. Four theorems in
`StaticResultProof.lean` prove field identity, preservation of arbitrary input
result/error values, and exact successful/error propagation. Six source
functions and four theorems passed ten dependency audits:

```sh
scripts/check-hasteboots-static-error-option --mode result \
  --build-receipt build/hasteboots-extraction/inline-tools-build-RECEIPT/manifest.json \
  --backend /tmp/hasteboots-aeneas-m0
```

The original 17-audit inlining fixture and five-audit static-error option gate
also passed with the repaired frontend. Three more rejection tests cover the
new mode's complete source/proof coverage, error-label changes and invalid IR;
the full guard suite has 125 passing tests. No proof limits are raised.

Full upstream extraction again completed the same 97 targets and rejected only
the existing `dyn.rs` erased-lifetime case. All 128 regenerated outputs remain
byte-identical to the preceding profile. `static-input-regression.json` records
the paired tools, source patches, logs and per-file comparison.

## Monomorphic usize intrinsic

`MonoCtlzCandidate.lean` freshly extracts the existing usize fixture in full
monomorphic mode. The frontend matches the explicit `ctlz_nonzero<usize>`
instantiation and validates its empty source/call binders and generics, exact
usize-to-u32 signature, Rust ABI, unsafe marker and non-variadic shape. Other
widths and generic references reject. The target remains the closed runtime
and proof suite in `interop/aeneas/usize-ctlz/`:

```sh
scripts/check-hasteboots-monomorphic-ctlz \
  --build-receipt build/hasteboots-extraction/inline-tools-build-RECEIPT/manifest.json \
  --backend /tmp/hasteboots-aeneas-m0
```

Thirteen kernel audits cover zero rejection, defined inputs, the leading-zero
value and the guarded total wrapper. Six negative runs reject a u32 call, u32
function alias, generic reference and deliberately corrupted ABI/unsafe/variadic
metadata. Only negative fault-injection artifacts are edited; accepted IR and
generated terms are unchanged. Three guard tests reject altered output and
incomplete runtime/proof coverage. The earlier 32 audits passed again, for 45
fresh audits across the paired profile. All 125 extraction guard tests passed.

Full upstream extraction again completed 97 targets with only the preexisting
`dyn.rs` erased-lifetime rejection. All 128 regenerated outputs remain
byte-identical; `mono-ctlz-regression.json` records the comparison.

Next work is explicit Vec/String heap cleanup and the constructor/model bridge,
then native heap/work refinement and the complete security plan. No production
Rust is modified by these fixtures or compiler patches.

## Allocator cleanup diagnostics

The coupled schema 0.1.225 profile preserves concrete allocator parameters and
methods through Charon and the monomorphic frontend. The native diagnostic
requires that option, precise/desugared/evaluated drops, and declarations for
all regular function references. Three cleanup guard tests cover these checks.

All 45 kernel dependency audits and six unsupported intrinsic runs passed again;
all 126 extraction guard tests passed. Full upstream extraction completed the
same 97 targets with the existing `dyn.rs` rejection, and all 128 regenerated
files are byte-identical to the preceding profile. Charon's full tests and
Clippy also passed.

`allocator-cleanup-regression.json` records the paired tool hashes, upstream
comparison and five original cleanup scopes. Retained function counts are
35/36/38/62/67 for opaque/String/Vec/RawVec/Global expansion. Every scope has
zero residual drops and no missing regular function declarations. Every complete
module still rejects for extracted axioms. Global expansion reaches original
`__rust_dealloc`, exposing layout and pointer primitives that require faithful
heap semantics. These diagnostics accept no native constructor or security
proof and introduce no replacement cleanup implementation.

## Explicit word64 byte-slice values

The opt-in `-word64-slices` profile requires `-target-word64` and uses
`HasteBootsSlice64Runtime.Slice` with U64 length/index/update primitives.
The concrete original byte `slice_len_fn` binding validates its safe shared
reference signature, Rust ABI and argument arities. Arrays remain rejected.
This does not install a native reference/heap model. See
[`../byte-reference/README.md`](../byte-reference/README.md) for the original
safe-reference fixture, all-input accessor proofs and remaining source obligations.
Existing profiles are unchanged with the flag absent.

## Evaluated plain integer constants

`-literal-const-initializers` requires the checked word64 target and lowers
rustc-evaluated plain integer constants from `--consts values` into exact typed
literal initializer bodies. It validates monomorphic top-level named storage,
matching integer types and bounds; other value/storage forms remain unsupported.
Existing initializer calls and flag-off profiles are unchanged. See
[`../literal-consts/README.md`](../literal-consts/README.md) and the word layout
composition in [`../word64-memory/README.md`](../word64-memory/README.md).
