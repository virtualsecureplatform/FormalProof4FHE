# Original safe byte-slice accessor values

`fixture.rs` uses ordinary `&[u8]` / `&mut [u8]` references, bounds checks,
indexing and assignment. Charon retains both source bodies and their signature
lifetimes. The only opaque dependency is the original standard-library
`slice_len_fn` lang item. The opt-in `-word64-slices` frontend profile binds
its concrete byte-slice instance to `HasteBootsSlice64Runtime.len` after checking
its name, lang-item identity, safe nonvariadic Rust ABI, reference signature,
region/argument arities and usize result. This is a primitive binding interface;
it is not a verified translation of the opaque standard-library body.

The profile requires the checked monomorphic, little-endian 64-bit target.
It uses the explicit carrier in `../slice-word64/Runtime.lean`: a list with
length strictly below `2^64`, a U64 length, and checked U64 indexing/update.
The backend's legacy `Slice` uses platform-dependent `Usize`; mixing it with
this profile's U64 indices fails type checking. No platform axiom or shorter
slice restriction repairs that mismatch. Array conversion/index builtins reject
until their carrier conversion is implemented. Only concrete byte-slice length
is registered; other unknown operations are not supplied by this milestone.
The existing profiles retain their old carriers when the new flag is absent.

Nine theorems prove all-input behavior of the unedited generated definitions:
reads return the list's optional selected byte; an in-bounds write succeeds
and changes precisely the selected byte while preserving length and all other
indices; an out-of-bounds write returns false and the original slice.
Eight runtime theorems establish length, success/failure and mutable continuation
behavior. The gate audits all 25 declarations, allows only the three standard
Lean axioms, checks the complete generated snapshot and rejects 13 malformed or
unsupported profiles/signatures/array cases. Four guard tests test evidence
validation failures. No proof placeholders or new axioms are accepted.

```sh
scripts/check-hasteboots-byte-reference-guards
scripts/check-hasteboots-byte-reference \
  --build-receipt build/hasteboots-extraction/inline-tools-build-RECEIPT/manifest.json \
  --backend /tmp/hasteboots-aeneas-m0
```

These are logical slice values, not a source heap/reference representation.
The model does not construct a Rust reference, authenticate a ghost borrow tag,
install memory callbacks, implement Rust alias rules, or assign a work cost.
Next, relate the slice's bytes to the byte-borrow ledger's current heap view,
prove selected accesses agree with checked ledger reads/writes, and establish
the source lifetime/allocator correspondence. Whole-slice observation in that
relation must remain a ghost view: it must not spuriously prohibit a parent
access outside a live child's disjoint range. Physical loads/stores still need
the permission checks for their actual accessed bytes.

The native constructor's original `drop_in_place` raw-pointer dereference is
still rejected. Constructor/destructor/deallocator, compiler/caller and
NTT/SIMD/scheduler refinement, lifetime oracle/owner coverage, BabyBear and the
128-bit expected physical attacker-work security theorem remain open.
See `regression.json` for checks and retained boundaries.
