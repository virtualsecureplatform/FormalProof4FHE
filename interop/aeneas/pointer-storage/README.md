# Address/provenance storage and the current backend boundary

`NativePointerStorage` separates a native 64-bit address from an allocation
identity and generation. Its checked read matches both against an immutable
cell. Null pointers and references without provenance cannot read a cell.
Retiring an origin invalidates its references while preserving other reads;
reusing an address for a new generation does not revive an old reference.
Generations are unbounded logical identities, without a lifetime counter cap.

This is an operational storage specification. It does not implement a Rust
allocator, pointer arithmetic, borrow permissions, object layout, overlapping
allocation checks, memory accesses or their physical costs. It is not wired
into the source translator, and does not replace its rejected NonNull pattern.

The boundary proof checks the existing pinned Aeneas backend directly. Its
`ConstRawPtr Unit` contains only a Unit pointee value. All such model pointers
are equal. Consequently no encoding through that type can both classify null
addresses correctly and admit a lossless round trip for address/provenance
records. The round-trip counterexample uses the same nonzero address with
different allocation generations. These results concern null classification
and lossless bridges; coarser observational abstractions require their own
simulation proofs.

The existing U64 bit-vector representation does preserve all address bits:
conversion to/from the native address type is proved to be a bijection.
These are representation statements, not a Rust pointer/heap refinement.
The remaining native I/O extraction failure stays in force.

```
scripts/check-hasteboots-pointer-storage \
  --tools /tmp/hasteboots-aeneas-tools --backend /tmp/hasteboots-aeneas-m0
scripts/check-hasteboots-pointer-storage-guards
```

The gate verifies the unchanged tool/backend pins, builds the storage model,
eight regression examples and thirteen root axiom guards, then checks 21
combined dependency audits: thirteen storage lemmas, two word conversions and
six boundary theorems. Only propext, Classical.choice and Quot.sound are
permitted. No proof-limit increase, admission or generated-term rewrite is
used. Manifests hash model/test/proof inputs, backend pointer/scalar sources,
checked assembly and logs.
