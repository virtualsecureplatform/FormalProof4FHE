# Static-string frontend experiment

This fixes a concrete extraction failure without changing native HasteBoots or
rewriting generated Lean terms. It is an isolated compiler experiment, not a
compiler-correctness or security certificate. The official extraction gate keeps
using the unchanged official tools.

The official Aeneas source is pinned to
`15b968482b0dcd7aae45020b6d1bca39b5024af5`; its Charon library is pinned to
`ef3748c1a92c6acc402f978770193d34adc0fe6e`. `frontend.patch` makes three changes:

- Shared string literals retain constant form. The interpreter's existing string
  constant handling uses a persistent dummy loan, so returning the literal does
  not invalidate it when dropping frame-local loans.
- Runtime ADT field types erase static regions as well as region variables,
  matching Aeneas's existing erased-runtime-type invariant. The invariant checks
  remain enabled.
- Lean string output preserves UTF-8 and uses Lean escapes for ASCII control and
  syntax bytes. Explicit size proofs unfold `U32.max` and use `decide +kernel`,
  avoiding the backend helper's native-proof default.

`fixture.rs` exercises returned literals, nested errors, both conditional result
branches, UTF-8, escaped/control bytes and an unchanged borrowed input. The nine
proofs in `Proof.lean` check exact extracted results, universal borrowed-input
identity, and explicit UTF-8/control byte lists. The probe runs the same LLBC
through the official and patched frontends with invariant checks enabled. It
requires the official failure baseline, complete patched output, strict Lean
checking, and all 15 dependency audits to use only propext, Classical.choice and
Quot.sound. Only generated imports change before kernel checking.

## Build and reproduce

Prepare an **isolated** Aeneas clone at the revision above, and a clean Charon
clone at its required revision. Symlink the latter as `charon` inside the Aeneas
clone. Do not use the prepared Lean-backend checkout as the frontend source: the
builder explicitly refuses it.

Use the official opam 2.3.0 Linux x86_64 executable:

```text
https://github.com/ocaml/opam/releases/download/2.3.0/opam-2.3.0-x86_64-linux
SHA-512 d4271d2387751313d5f904e8fdb3133ea893c72d09737139266d2bbe7624f81665a4276d2e55aa71856630ece8ce226b989560076599baae9afc053c5815f8c8
```

Create a local opam root and OCaml 5.3.0 switch. Pin `charon` and
`name_matcher_parser` to the clean Charon source using `--kind=path`. Install the
exact package versions in `opam-packages.json`; the builder compares the full
installed package map. The build needs GMP headers and a shared GMP library. The
validated setup unpacked Ubuntu's `libgmp-dev` under `/tmp`, supplied its include
and pkg-config paths, and linked to the existing shared runtime; no system files
were changed. The `.deb` SHA-256 was
`a9847b5ecfff791a46cb198f29a06d9d23a20afdfdd434812f2b44ccfb61d46a`.

With dependencies prepared, the validated invocation was:

```sh
scripts/build-hasteboots-static-frontend \
  --source /tmp/hasteboots-aeneas-static \
  --opam /tmp/hasteboots-ocaml-bootstrap/opam \
  --opam-root /tmp/hasteboots-ocaml-bootstrap/root --switch hasteboots-static
scripts/check-hasteboots-static-string-guards
scripts/probe-hasteboots-static-strings \
  --tools /tmp/hasteboots-aeneas-tools --backend /tmp/hasteboots-aeneas-m0 \
  --build-receipt /path/printed/by/builder/manifest.json
```

The builder applies the exact reviewed patch to a clean isolated checkout, or
checks an already patched one. It verifies source revisions, tracked cleanliness,
package versions and executable hashes. The probe rechecks the source and build
receipt. Both commands write fresh manifests/logs under
`build/hasteboots-extraction`, including commands, LLBC, source/patch/package/
executable/output/proof hashes and pass/failure status. Seven guard tests cover
truncation, missing functions, admissions/native proofs, all proof-limit settings,
and refusal of unreviewed source or the official backend checkout. Formatting was
run with the pinned compiler's `gmake format`; only the three patched source files
changed. The regression pipeline regenerates its outputs directly through the
pinned Charon and rebuilt frontend.

## Remaining constructor gate

The patch removes the traced static-string return failure. The generic actual
`Parameters::new_encoded` wrapper now reaches Lean emission with invariant checks,
but that output still contains an admitted `core.intrinsics.ctlz_nonzero` used by
`checked_next_power_of_two`. It is rejected, not accepted as a constructor proof.
Monomorphized closure/naming and possible further typechecking/refinement issues
also remain open. The default official constructor gate still fails. Full Rust
source-to-model, compiler, heap, NTT/SIMD/Div64, scheduler/physical-work and complete
security obligations are unchanged.
