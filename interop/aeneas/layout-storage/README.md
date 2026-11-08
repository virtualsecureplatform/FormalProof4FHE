# Retained Layout bytes and resident descriptor-to-free composition

This profile connects the extracted source `Layout` getters, the retained
compiler byte descriptions, the shared byte/reference heap, and the original
allocator caller. On the pinned x86_64 target, `Layout` occupies 16 bytes with
alignment 8: its logical `size` field is stored at byte 8, and its logical
`align` field is stored at byte 0. `Alignment` is a transparent eight-byte
wrapper. The retained `AlignmentEnum` stores one of 64 power-of-two u64 tags at
byte zero and rejects every other bit pattern.

`NativeLayoutBytes` encodes alignment before size and decodes exactly 16
initialized bytes, checking the alignment domain. Thirteen theorems establish
both codec round trips, field projections, permission-checked read projection,
reachability, exact bytes/heap/history/register effects and failure prefixes.
The read executes an actual reference-machine read of 16 bytes at alignment 8.
Malformed enum bytes retain the completed read, its output and scratch pointer;
permission failure preserves the original state.

The composition captures the actual complete data pointer before reading the
resident descriptor, then initializes and executes the original allocator
caller using decoded fields. Capturing first matters: the read shifts raw
registers by inserting its scratch pointer. Projection and success are proved
for the composed operation. Source getter proofs convert actual Aeneas u64
values without truncation, derive alignment validity for every source enum
variant, and connect those values to the byte codec and caller entry. No caller
alignment certificate or chosen callee result is supplied by the operation.

Twelve root regressions check physical field order, exact round trips, invalid
lengths/tags, the high bit, successful reads, retained malformed-read prefixes,
revoked/short references and blocked parent access. Eight composition regressions
check the captured data pointer, real frees, missing pointers/references, wrong
size, malformed tags, reversed fields, revoked loans and address-only pointers.
Three getter regressions cover exact bytes and full-width source values.

Reproduce:

```sh
scripts/check-hasteboots-layout-storage \
  --build-receipt build/hasteboots-extraction/inline-tools-build-b6esls36/manifest.json \
  --backend /tmp/hasteboots-aeneas-m0
```

The gate reruns the allocator caller and source Layout parents with the same
frozen tools. It compares fresh retained metadata and generated descriptions,
rejects altered extents/offsets/alignments, stored tags, discriminators and invalid
fallbacks, and checks all combined declaration audits. Only compatibility
imports are adjusted when combining existing generated modules; computational
terms and proof limits are preserved.

These are byte representation and checked-machine composition proofs relative
to the retained compiler descriptions. Native calling conventions, compiler
correctness, Rust reference/lifetime correspondence, the external allocator
implementation, allocator trait/RawVec/Vec destruction and physical work remain
unproved. The composed adapter is not claimed to be an extracted whole Rust
function. The whole native constructor and final protocol security theorem
remain open. Explicit unit cleanup remains ghost composition.
