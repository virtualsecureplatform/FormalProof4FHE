# Actual concrete row metadata

This gate extracts the unchanged native Goldilocks RowCode metadata methods and
checks their value correspondence. It does not prove constructors, heap/ABI
identity, serialization, context hashing, first-owner iteration or security.

The concrete wrapper calls block_width, codeword_blocks and domain_separator.
Charon uses its pinned `--monomorphize --raw-consts` modes to resolve the concrete
trait obligations and retain byte-constant storage. No general clause-pruning
option is used. The gate checks complete x86_64 little-endian LLBC, exactly the
four intended functions, resolved specialization obligations and absence of
erased/body regions in their signatures. The actual code and Goldilocks carriers
are included explicitly; an opaque Goldilocks type is rejected.

The reviewed `metadata-mono` frontend profile extends `static-bytes` by exposing
the existing optional external-name-pattern setting as
`-no-external-name-patterns` and consistently applying it to Rust-name attributes.
The default remains enabled. This avoids a NameMatcher roundtrip assertion for
monomorphized names during annotation printing. Source names (including concrete
instantiations), source spans, full LLBC and exact generated terms are retained.
No type constraint, runtime check or symbolic invariant is disabled. The gate
requires the annotation-enabled failure baseline and an exact reviewed snapshot.

`Proof.lean` has eleven theorems. They establish exact native width/block reads,
the actual native domain tag, metadata correspondence with decoded retained
parameters, and lossless conversion between the two extracted code carriers.
All six stored fields, including modulus and raw root, survive both conversion
round trips. The original receipt-selected native registry read supplies the
same metadata. These are value-level statements, not pointer-identity or
physical-work claims.

The gate first reproduces the 107-audit registry extraction and the 43-audit
byte/slice/string frontend regression. It then kernel-checks 130 combined
dependency audits: the previous 107, four native metadata functions, eleven
metadata theorems, three associated-type controls and five control theorems.
Two recursive interfaces remain rejected, even if Aeneas reports errors and
truncated output with exit code zero. The only permitted theorem axioms are
propext, Classical.choice and Quot.sound; proof limits stay at 200000/1000.

## Reproduce

Use a clean isolated checkout at Aeneas revision
`15b968482b0dcd7aae45020b6d1bca39b5024af5`, its `charon` symlink at clean revision
`ef3748c1a92c6acc402f978770193d34adc0fe6e`, and the existing pinned package profile:

```
scripts/build-hasteboots-static-frontend --profile metadata-mono \
  --source /tmp/hasteboots-aeneas-metadata-mono \
  --opam /tmp/hasteboots-ocaml-bootstrap/opam \
  --opam-root /tmp/hasteboots-ocaml-bootstrap/root --switch hasteboots-static
scripts/extract-hasteboots-metadata-mono \
  --tools /tmp/hasteboots-aeneas-tools --backend /tmp/hasteboots-aeneas-m0 \
  --build-receipt /path/printed/by/builder/manifest.json
scripts/check-hasteboots-metadata-mono-guards
```

The native source pin is `dff353006322693cab3dc6b654f82151f658f294`.
Tool/backend/build/package/source/snapshot hashes and native cleanliness are
checked; only imports are adapted for kernel checking. The official tools and
prepared backend checkout are unchanged. Formatting and upstream traits/arrays
regeneration are required checks for this isolated frontend profile.

The generic NTT interface remains unsupported. Concrete metadata success must
not be used as a constructor, NTT algorithm, serialization or full-protocol
refinement certificate.
