# Checked fieldless enum decoding

The native `Alignment::new_unchecked` transmutes usize into a transparent
wrapper around the 64-variant AlignmentEnum. Its valid stored representations
are exactly the powers of two. The preceding profile rejects this operation;
`baseline.json` records the corresponding source-shaped regression.

The opt-in monomorphic prepass now decodes explicitly represented, fieldless
U32/U64/Usize enums, optionally behind one closed transparent wrapper. It
requires a unique matching 64-bit little-endian target layout, scalar size and
alignment, canonical variant IDs, distinct matching unsigned discriminants,
zero-offset stored tags, singleton discriminator branches and invalid fallback.
Stored tags, source discriminants and discriminator decisions must all agree.
Wrappers additionally require a single zero-offset field and matching layout.
Unsupported layouts and transmute forms still reject.

The operand is consumed once. Tables larger than eight entries use a saved
scalar and nested small switches; this keeps Lean's generated match eliminators
within the unchanged proof budget while retaining all 64 cases. Same-type
unsigned scalar transmutes emitted by rustc's enum-validity checks preserve the
operand through an ordinary use. No pointer or borrow representation is cast.
These logical switches are not an attacker-work accounting model.

The source-shaped fixture also exposed a general interpreter bug: a concretely
failed assertion during symbolic execution was propagated as a Panic state into
a join that expects successful states. Such failures now terminate their branch
and synthesize the existing failure node, as explicit aborts already do.
The generated model reports invalid enum representations as `fail panic`;
it does not assert that this is a defined Rust result for an invalid transmute.
Native caller safety preconditions must still be proved before connecting this
partial model to actual Rust execution; the model's failure branch is not a
new runtime guard in HasteBoots.

```sh
scripts/check-hasteboots-enum-decoding-guards
scripts/check-hasteboots-enum-decoding \
  --build-receipt build/hasteboots-extraction/inline-tools-build-RECEIPT/manifest.json \
  --backend /tmp/hasteboots-aeneas-m0
```

Fifteen kernel theorems establish complete variant round trips, success
soundness for every input/output of all three source functions, the exact
accepted alignment representation set, power-of-two validity, high-bit
acceptance and representative failures. All 64 alignment variants are retained.
The three source functions and two generated readers bring dependency coverage
to twenty exact audits. Sixteen negative runs reject signed/nontransparent
sources, disabled mode and thirteen corrupted layout/discriminant/field tables.
Accepted IR and generated terms are never edited. Four guard tests reject
changed tables, invalid-value acceptance, admissions and missing soundness proofs.

Original native layout extraction now passes the inward Alignment conversion
and next rejects `Alignment -> NonZero<usize>`. It still has 84 functions,
no residual drops or runtime-check queries and no missing regular function
declarations. Large usize literal handling, remaining representation casts,
layout/pointer/heap/work refinement and full native constructor/security
proofs remain open. No backend or production Rust is modified, no proof limits
are raised and only the three allowed Lean axioms are accepted.

All preceding 88 dependency audits passed again, for 108 across the paired
profile. All 147 extraction guard tests passed. Full upstream extraction
completed the same 97 targets with the existing `dyn.rs` rejection; all 128
regenerated files are byte-identical. `regression.json` records the paired
tools, patch hashes, exact audit/negative coverage, native diagnostics and
per-file upstream comparison.
