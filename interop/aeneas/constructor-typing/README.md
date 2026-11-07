# Constructor trait names and builtin effects

This isolated profile extends `usize-ctlz` with two compiler fixes. It preserves
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
