# Checked initialized byte ranges and source pointer data

`NativeByteRange` extends the byte-allocation lifecycle with initialized range
reads. This remains a model operation, not a Rust reference constructor or borrow
permission. It does not enable the rejected native destructor dereference.

A range checks target layout/size, a nonnull aligned address, and strict
nonwrapping arithmetic: `address + size < 2^64`. A positive range must fit inside
one live allocation and retain that allocation's origin. Adjacent allocations
cannot be combined into one slice. Reading requires every requested byte to be
initialized and returns exactly the requested length; it cannot truncate at an
uninitialized byte or at the end of a buffer.

A zero-byte range still requires a nonnull aligned address and a valid target
layout, but it does not require a live allocation. This admits aligned dangling
empty ranges, including after deallocation. Null/misaligned empty ranges reject.
Positive ranges through a deallocated origin reject, including aliases. Byte
pointer arithmetic preserves provenance and checks overflow before conversion
back to the address type. These checks are geometry/initialization conditions;
they do not establish typed-value validity or Rust alias/borrow lifetimes.

Twenty-four model theorems prove exact lengths, initialization/access witnesses,
single-allocation coverage, no wrap, empty-range behavior and rejection rules.
They also prove that each returned range byte agrees with a checked single-byte
load from the same allocation state. Conversely, an initialized covering block
in a well-formed state produces the exact range read. Thin/vtable metadata does
not masquerade as byte-slice length metadata.

Nine bridge theorems connect constant, mutable and cast byte-slice pointer
constructors, including the original stdlib bodies, to those model checks. The
decoder changes only the phantom byte-pointee index. It preserves original data
address, provenance and length. It neither introduces a Rust dereference nor
claims that an arbitrary model state represents the native allocator. The API
is for byte slices; other element strides, typed ZST multiplicity and string
validity are not inferred from byte counts.

```sh
scripts/check-hasteboots-byte-range-guards
scripts/check-hasteboots-byte-range \
  --build-receipt build/hasteboots-extraction/inline-tools-build-RECEIPT/manifest.json \
  --backend /tmp/hasteboots-aeneas-m0
```

The combined gate checks 77 dependency audits: 32 model declarations, ten bridge
declarations and 35 reused source/runtime declarations. It also reruns the
57-audit ordinary pointer-parts gate and 96-audit byte-memory/Layout bridge gate;
the latter retains its existing Layout extraction configuration. No sysroot
identity is assumed. The root axiom file checks all 32 range declarations, and
27 smoke examples cover initialized/partial/empty reads, null/misaligned inputs,
one-past access, adjacent allocations, deallocation and metadata discrimination.
No new axiom, native_decide or raised proof limit is used.

A fresh native run still rejects raw-pointer dereference in original
`drop_in_place`. The translator, production Rust and Lean backend are unchanged.
A checked memory-state/allocator relation, typed value validity, element layouts,
aliasing and mutable-borrow lifetimes are still needed before enabling that
operation. Destructor/deallocator composition, compiler/caller, NTT/SIMD/scheduler,
causal oracle/owner history, BabyBear and expected physical-work security remain
open. Model reads are not assigned a physical-work floor or substituted for
actual adversary work. See `regression.json` for current evidence.
