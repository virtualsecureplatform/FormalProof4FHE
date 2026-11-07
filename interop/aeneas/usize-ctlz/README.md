# Concrete usize ctlz_nonzero subgate

The actual parameter constructor reaches `ctlz_nonzero` through Rust's
`checked_next_power_of_two`. The official frontend emits an axiom for it. This
profile replaces that missing primitive with a transparent, closed usize
operation and rejects other instantiations before extraction.

The combined `frontend.patch` contains the earlier static-string fixes plus:

- A Lean-only preprocessing check visits every direct function reference. A
  `core::intrinsics::ctlz_nonzero` reference must have exactly the concrete usize
  type argument; generic and other integer references report an error.
- The builtin mapping removes the now-checked type/Copy parameters and calls
  `HasteBootsUsizeCtlz.nonzero`. There is no caller-provided operation or callback.

`Runtime.lean` rejects zero as `Error.undef`, reflecting Rust's undefined-input
boundary. Nonzero words use the existing bit-vector leading-zero definition.
Four lemmas prove zero rejection, the nonzero result, nonzero bits and the exact
natural result `word-width - floor(log2(value)) - 1`. The last proof establishes
that the U32 result does not truncate. It uses the library's explicit 32/64-bit
platform bound, without assuming a new platform axiom or fixing its opaque
platform constant to 64.

`fixture.rs` contains actual raw and zero-guarded Rust calls. Seven proofs verify
their extracted definitions: defined-input results, rejected undefined input in
the model, the zero branch, a total guarded-call specification for every input,
and the returned natural value. Together with the two source functions, all 13
audited declarations use only propext, Classical.choice and Quot.sound.

The probe also extracts and rejects three valid Rust negative fixtures: direct
u32 use, generic use, and a u32 function-item alias. A function-pointer coercion
was rejected by rustc itself and is not used as a frontend negative test.

## Reproduce

Use the same pinned Aeneas/Charon sources, opam executable, OCaml 5.3.0 switch and
132-package profile documented in `../static-strings/README.md`. Use a separate
isolated source checkout for this profile. The shared builder's default remains
`static-strings`; select this combined patch explicitly:

```sh
scripts/build-hasteboots-static-frontend \
  --source /tmp/hasteboots-aeneas-ctlz --profile usize-ctlz \
  --opam /tmp/hasteboots-ocaml-bootstrap/opam \
  --opam-root /tmp/hasteboots-ocaml-bootstrap/root --switch hasteboots-static
scripts/check-hasteboots-usize-ctlz-guards
scripts/probe-hasteboots-usize-ctlz \
  --tools /tmp/hasteboots-aeneas-tools --backend /tmp/hasteboots-aeneas-m0 \
  --build-receipt /path/printed/by/builder/manifest.json
```

The probe verifies the official tools, exact frontend source/patch/package/build
receipt, and the unchanged prepared backend. It freshly extracts all fixtures
for the checked 64-bit little-endian target, requires the official intrinsic
admission as a rejected baseline, checks complete patched output, and runs strict
Lean checking with invariant checks enabled in the frontend. The transparent
runtime is inserted as a separate prelude; generated terms are preserved.
All proof declarations have exact dependency-audit coverage. Six guard tests
cover output truncation, missing functions, admissions/native proofs, all proof
limits, distinct build profiles and proof audit coverage. Fresh manifests record
commands, fixture/LLBC/runtime/proof/output/tool hashes and pass/failure status.

## Constructor and machine obligations still open

This removes the ctlz admission from the generic actual constructor's emitted
Lean, but the complete constructor is still rejected by strict typechecking.
Further failures include the discriminant attribute import, duplicate parent
trait field names, unresolved algebra traits and result-control-flow typing.
Removing unused trait clauses in a diagnostic extraction did not close the gate;
that flag is not enabled by these probes. Monomorphized extraction remains a
separate open path.

The primitive's source precondition must still be discharged at constructor call
sites. The complete source-to-model/ABI relation, actual Rust/compiler/heap and
instruction/physical-cost refinements, and full protocol security remain open.
The Charon target is checked as 64-bit; the runtime proof keeps the library's
platform width explicit and does not itself establish that ABI correspondence.
No original HasteBoots source or official tool is changed.

A later, separate `constructor-typing` profile resolves the parent-field and
Result effect errors. Its actual generic constructor typechecks, but remains
rejected for the inherited `core.fmt.Formatter` backend axiom. See
`../constructor-typing/README.md`; the `usize-ctlz` profile is unchanged.
