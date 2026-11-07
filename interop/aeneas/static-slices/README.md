# Static shared slice call-result experiment

This isolated frontend profile addresses the reduced trait-call missing-borrow
failure from native row metadata. It is not a compiler-correctness certificate
or a proof of native PCS/context refinement. The official extraction tools and
prepared Lean backend remain unchanged.

The profile uses the pinned Aeneas/Charon revisions and exact OCaml packages from
`static-strings`. Its reviewed patch contains those earlier string fixes plus:

- Explicit runtime erasure also erases static regions. Declared signatures keep
  static regions until runtime erasure is requested; no lifetime is invented.
- An abstract call returning an explicitly declared shared static scalar slice
  represents the returned data with a persistent dummy shared loan, as existing
  static globals do. The regular input-region abstractions still process input
  borrows. Other result shapes retain the existing translation.

`fixture.rs` isolates this behavior without fields, NTT tables or byte literals.
It exercises a static method result, ordinary dimension calls, combined metadata,
copying the shared result, retaining it across another call and an ordinary
borrowed-input identity. Eight kernel theorems cover exact results, successful
metadata fields and width-error propagation. All six extracted functions are
audited too. The same run regenerates/checks the earlier six static-string
functions and nine theorems, for 29 dependency audits in total.

Three valid Rust cases remain rejected: mutable static results, nested static
references and direct static byte-slice literals. The literal-storage problem
is separate from the abstract-call loan problem. No loop, associated-type
constraint, borrow invariant or opaque definition is bypassed.

## Reproduce

Use an isolated clean checkout at Aeneas revision
`15b968482b0dcd7aae45020b6d1bca39b5024af5`, with its `charon` symlink pointing to
clean revision `ef3748c1a92c6acc402f978770193d34adc0fe6e`:

```
scripts/build-hasteboots-static-frontend --profile static-slices \
  --source /tmp/hasteboots-aeneas-static-results \
  --opam /tmp/hasteboots-ocaml-bootstrap/opam \
  --opam-root /tmp/hasteboots-ocaml-bootstrap/root --switch hasteboots-static
scripts/probe-hasteboots-static-slices \
  --tools /tmp/hasteboots-aeneas-tools --backend /tmp/hasteboots-aeneas-m0 \
  --build-receipt /path/printed/by/builder/manifest.json
scripts/check-hasteboots-static-slice-guards
```

The builder checks the complete patch, package profile and executable hashes.
The probe rechecks them and rejects stale receipts, unreviewed source, the
prepared backend checkout, admissions, native proofs and increased proof limits.
It requires the official missing-borrow baseline, strict kernel checks and all
three negative rejections. Only generated imports are adapted. Output, proof,
fixture, negative-case, LLBC and regression hashes are recorded in fresh artifacts.

`gmake format` and the upstream `gmake test-traits.rs` regeneration were run in
the isolated source checkout. Native row metadata, complete source serialization,
parameter formatting, the concrete associated-type constraint, source ownership,
heap and physical work remain open gates.
