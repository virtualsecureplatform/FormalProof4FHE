# Explicit 64-bit slice value carrier

`Runtime.lean` supplies the logical value carrier and checked primitives for
`-word64-slices`. It records `length < 2^64` and uses U64 indices independently
of the backend's opaque platform word size. It does not model addresses, heap
permissions, allocator behavior, Rust references or physical work. The mutable
indexing continuation performs an actual list update, with preserved length.

The original-source fixture, proofs, evidence and gate are in
[`../byte-reference`](../byte-reference/README.md). The Lean backend is unchanged.
