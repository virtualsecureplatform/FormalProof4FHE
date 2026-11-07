# Shared literal byte-reference experiment

This profile preserves compile-time byte-reference storage instead of lowering
it to a borrowed frame-local array. It extends the isolated `static-slices`
experiment; neither profile is a compiler-correctness or native security proof.
The official tools, native HasteBoots source and prepared Lean backend remain
unchanged.

Charon's pinned `--raw-consts` option retains the explicit constant-reference
node. The frontend handles only a shared reference, without unsizing metadata,
to a fixed U8 array whose elements and length are explicit checked literals.
It introduces the exact array data and a persistent shared loan, as existing
static constants do. Mutable references, nested references, other element types
and nonliteral lengths/elements remain unsupported. No frame-local allocation
is promoted by a guessed lifetime, and no LLBC or generated Lean term is edited.

The fixture covers the domain-tag bytes, all U8 boundaries, an empty slice,
copying a returned shared slice, escaped/control bytes and ordinary borrowed
input. Eight kernel checks prove exact byte lists, length and agreement with
the model's tag value. Tag agreement here concerns the regression fixture;
it is not a refinement theorem for the native RowCode method.

The fresh probe checks all six functions and eight theorems, repeats the 29
static-slice/static-string dependency audits, and requires rejection of three
valid Rust cases: mutable, nested-reference and U16 constants. Every Charon
output must be complete and match the pinned x86_64 little-endian target. All
kernel audits permit only propext, Classical.choice and Quot.sound; proof limits
remain 200000 heartbeats and recursion depth 1000. The artifact copies of the
Rust inputs are compiled, and source/output/proof/LLBC hashes are recorded.

## Reproduce

Prepare a clean isolated checkout at Aeneas revision
`15b968482b0dcd7aae45020b6d1bca39b5024af5`, with a `charon` symlink to clean revision
`ef3748c1a92c6acc402f978770193d34adc0fe6e`, and use the pinned OCaml package profile:

```
scripts/build-hasteboots-static-frontend --profile static-bytes \
  --source /tmp/hasteboots-aeneas-static-bytes \
  --opam /tmp/hasteboots-ocaml-bootstrap/opam \
  --opam-root /tmp/hasteboots-ocaml-bootstrap/root --switch hasteboots-static
scripts/probe-hasteboots-static-bytes \
  --tools /tmp/hasteboots-aeneas-tools --backend /tmp/hasteboots-aeneas-m0 \
  --build-receipt /path/printed/by/builder/manifest.json
scripts/check-hasteboots-static-byte-guards
```

The profile uses the previous static-slice patch plus the reviewed constant
handling in InterpExpressions.ml. `gmake format` and the upstream arrays test
regeneration are part of its validation. The builder/probe reject unreviewed
patches, stale receipts, changed executables, admissions, native proofs and
increased limits. The official frontend must reproduce the unsupported-constant
baseline on the same raw-constant LLBC.

For the actual native metadata attempt, use:

```
scripts/probe-hasteboots-row-metadata --mode generic --raw-consts \
  --tools /tmp/hasteboots-aeneas-tools --backend /tmp/hasteboots-aeneas-m0 \
  --build-receipt /path/to/static-bytes/build/manifest.json
```

That diagnostic remains rejected/unproved: the metadata function bodies now
translate, but extraction stops at NTTField's associated-type interface. The
concrete associated-type constraint, field formatting, Serde/bincode, hash
updates, private owner selection, heap and physical work remain open gates.
