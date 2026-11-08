# Non-null pointer patterns and original outward conversion

The checked `-provenance-pointers` profile now translates `*const T is !null`
and `*mut T is !null` as subtypes of the shared raw-pointer descriptor whose
data address is nonzero. This is an address predicate. It does not establish
allocation, provenance, alignment, dereferenceability, borrow permission or
physical work. A slice's metadata does not decide whether its data address is null.

Direct pattern construction uses `check_nonnull`: zero addresses yield
`Result.fail .undef`, and every nonzero descriptor yields its unchanged pointer
with a checked proof. Outward conversion erases only the subtype proof. Four
runtime theorems establish both cases, the exact successful-result criterion and
roundtrip. No success callback or caller-supplied constructor certificate is added.
The Rust fixture's construction operations are unsafe transmutes; the rejected
zero case represents undefined source behavior, not a promise that Rust returns
an error there.

The original ordinary-sysroot `core::ptr::NonNull<u8>` declaration and `as_ptr`
body are retained. A frontend prepass decomposes an outward transparent-carrier
transmute only after checking a closed single-field declaration, one matching
64-bit little-endian target, size/alignment 8, transparent representation,
zero field offset, inhabited carrier/variant, no alignment modifier or tagger,
and the known sole discriminator. It projects the non-null field, erases its
proof and performs the existing raw-pointer cast for mutability/pointee changes.
This scoped rule is for thin literal pointees; it is not a general transmute,
Rust ABI, heap or compiler-correctness theorem. Inward carrier transmutes and
wide-carrier layout conversion remain unsupported.

The complete generated module includes eight fixture functions and the original
stdlib `as_ptr` function. Eighteen source theorems cover every extracted function,
all-input preservation, zero/nonzero cases, the original wrapper's nonzero data
address and roundtrip. Together with runtime/type/proof aliases and the shared
cast runtime, the gate checks 44 dependency audits and rejects 18 unsupported
profiles/targets/layouts/operations. Mutated IR is used only for negative controls;
accepted source, IR and generated terms are not edited.

```sh
scripts/check-hasteboots-nonnull-pointers-guards
scripts/check-hasteboots-nonnull-pointers \
  --build-receipt build/hasteboots-extraction/inline-tools-build-RECEIPT/manifest.json \
  --backend /tmp/hasteboots-aeneas-m0
```

The original native constructor now passes this former NonNull obstacle and
stops at the unsupported `PtrFromParts Mut` builtin. Its 52 retained functions,
ordinary standard library, precise drop handling and original pointer carriers
are preserved; it is still not an accepted native constructor. Pointer parts and
metadata operations, allocator/layout/deallocation, source encoding/caller/heap,
NTT/SIMD/scheduler, oracle/owner accounting, BabyBear and the final expected
physical-work security theorem remain open. See `regression.json` for the exact
paired tools, validation evidence and failed native diagnostic.
