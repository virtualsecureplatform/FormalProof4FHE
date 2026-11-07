# Constructor trait names and builtin effects

This isolated profile extends `usize-ctlz` with two compiler fixes and an early
signature-region validation pass. It preserves
all original trait clauses, including Copy assumptions, and uses invariant
checks. It does not enable `--remove-unused-clauses`.

* Parent trait fields are registered with distinct names within each record.
  Previously `Copy Self` and `Copy T` both became `coremarkerCopyInst`. The first
  name stays unchanged; subsequent collisions use the existing numbered-name
  allocator. Definitions and projections use the same registered clause IDs.
  This addresses parent-parent collisions, not every possible field collision.
* Effect analysis uses a builtin's declared backend effects even when Charon
  retained its Rust body. Previously the infallible Rust `Result::branch` body
  overrode its fallible-model signature, producing an extra `lift` around a
  model that already returns `Std.Result`. Nonbuiltin body analysis is unchanged.

* Before symbolic execution, every function input/output signature is checked
  for erased or body regions. Erased lifetimes require a lifetime-preserving
  extraction, rather than an invented input/output or alias relationship. Named,
  bound and static regions remain unchanged. This check applies to function
  declarations, including opaque ones; it is not a universal LLBC verifier.

The combined six-file `frontend.patch` applies to pinned Aeneas
`15b968482b0dcd7aae45020b6d1bca39b5024af5`. It includes the previous string and
concrete usize fixes. No backend Lean file, original tool, Charon source, or
HasteBoots source is changed. Compiler formatting was run. This remains a
compiler experiment, not a correctness certificate for the translation.

`fixture.rs` reproduces both failures with actual Rust traits and `?`
propagation. `Proof.lean` checks that the two typed parent fields survive record
construction, both method calls retain their sequence, and propagation returns
exactly the original Rust Result for every input. The fresh two functions and
three theorems pass strict Lean checking and five dependency audits. The
unchanged official frontend emits duplicate parent names and the extra lift on
this same input; the probe checks that rejected baseline.

## Reproduce

Use the pinned toolchain/package setup in `../static-strings/README.md` and a
separate frontend checkout; do not patch the prepared official Lean backend.

```sh
scripts/build-hasteboots-static-frontend \
  --source /tmp/hasteboots-aeneas-traits --profile constructor-typing \
  --opam /tmp/hasteboots-ocaml-bootstrap/opam \
  --opam-root /tmp/hasteboots-ocaml-bootstrap/root --switch hasteboots-static
scripts/check-hasteboots-constructor-typing-guards
scripts/probe-hasteboots-constructor-typing \
  --tools /tmp/hasteboots-aeneas-tools --backend /tmp/hasteboots-aeneas-m0 \
  --build-receipt /path/printed/by/builder/manifest.json
```

The probe checks exact tool/source/patch/package/build hashes, complete generated
output, the 64-bit little-endian extraction target, fixed proof limits and all
dependency audit entries. It preserves generated terms; fixture compatibility
changes only imports. Six guard groups cover completeness, mode separation,
admissions, proof limits, profile separation and dependency rejection. Fresh
manifests retain commands, hashes, logs and terminal pass/failure status.

## Actual constructor remains rejected

Run the same probe with `--mode constructor` to extract the actual generic
`Parameters::new_encoded` through `wrapper.rs`, pinned native dependencies and
the existing locked Cargo fixture. It includes the original option/result/
next-power-of-two bodies. Its only term support is the previously checked,
transparent usize primitive prelude. The discriminant attribute requires an
additional import. All emitted constructor terms are preserved.

This fresh constructor extraction now **typechecks**, but both the wrapper and
constructor dependency reports contain the backend's existing
`core.fmt.Formatter` axiom through inherited formatting dictionaries. The probe
therefore **exits nonzero and records failed status**. A constructor admission is
not accepted as a milestone certificate. Removing trait clauses or substituting
a dummy formatter has not been used to bypass this failure. The official default
`scripts/extract-hasteboots-parameters` gate is unchanged and still fails closed.

Remaining obligations include eliminating that dependency with justified
extraction, the concrete Goldilocks constructor/cache path and its source-to-model
invariant, primitive call-site preconditions and ABI correspondence, compiler/
heap/instruction/physical-work refinement, and the full unbounded causal security
proof. BabyBear and the other protocol obligations remain required independently.

## Captured closure lifetime reproducer

`captured-option.rs` isolates the same lifetime failure as the concrete
constructor: `Option<usize>::is_none_or` captures a shared `&usize` in its
predicate. The generic extraction and `CapturedOptionProof.lean` establish exact
none/some behavior for every input. The function and both lemmas pass three
dependency audits without axioms. Only imports change in the emitted Lean.

```sh
scripts/check-hasteboots-captured-option-guards
scripts/probe-hasteboots-captured-option \
  --tools /tmp/hasteboots-aeneas-tools --backend /tmp/hasteboots-aeneas-m0 \
  --build-receipt /path/printed/by/builder/manifest.json
```

The paired probe first runs a fresh constructor-typing fixture preflight to
validate the exact tool/source/build/package/backend policy. It then extracts
the same minimal Rust file both ways. Generic mode passes strict checking; mono
mode must fail at the early signature-region check. The LLBC inspection resolves
Charon's hash-consed types without editing them and checks precisely one
`is_none_or` declaration, no region/type parameters, and a closure input with
`regions = [Erased]`. The diagnostic requires lifetime-preserving extraction; the interpreter
invariant still requires non-erased symbolic input types.
The mono failure is retained as a rejected route, never a constructor pass.
Five guard groups cover signature identity, ambiguous/changed signatures,
hash-consing, nonmutation, and proof audit coverage.

The lifetime is already missing at the Charon/Aeneas boundary. Simply replacing
all erased regions with one region, inventing independent lifetimes without
checking output/alias relationships, or disabling Aeneas's invariant does not
establish a correct specialization. A source-preserving solution still needs
explicit binder and call-site correspondence. A diagnostic concrete generic
route including pcs/algebra also emitted Charon errors and was rejected before
it could qualify as an alternative extraction.

The paired probe also extracts `unsupported-returned-borrow.rs` and
`unsupported-mutable-capture.rs` through the pinned full mono route. Both are
valid Rust and complete Charon extractions, but the signature-region guard must
reject each before interpretation. Their fresh source/LLBC hashes and terminal
statuses are recorded separately. Neither case is accepted by inventing a
lifetime or dropping an ownership relationship.

A private prototype that freshened shared input regions and resolved standalone
impl methods still failed context-collapse/dependency invariants. It is excluded
from this patch. A successful repair must address lifetime relationships,
concrete dispatch metadata, declaration dependencies and branch-join semantics
together; the early rejection does not discharge that source-refinement task.
