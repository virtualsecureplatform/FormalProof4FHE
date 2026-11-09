# Retained empty byte Vec constructor

## Empty constructor to resident storage and reference destruction

`NativeEmptyVecStorage` proves a checked storage bridge for the original empty
byte Vec value. A registered pointer to a live 24-byte header, a reachable
modeled world, checked alignment/extent and separation from existing loans suffice
for the actual byte write and fresh exclusive borrow. Neither operation's success
is assumed. The resulting resident descriptor has capacity and length zero and
a dangling pointer with no allocation origin. Its initialization, buffer ownership,
empty buffer separation and exclusive header frontier are proved.

`HasteBootsVecEmpty.constructStored_complete` first invokes the retained original
constructor, validates its actual nominal fields, then performs that storage
sequence. The combined `empty_construct_destroy_complete` theorem feeds the
result directly into the retained complete reference-based Vec destructor.
`constructed_empty_every_invocation` gives the same normal unit return,
reachability, complete ordered incoming loans and unchanged stored heap to every
operational destructor invocation. This leaves the header's caller-owned loan
in place; native by-value drop and header lifetime discharge are not proved.

Seven model theorems, two definitions and a readiness structure have 11
declaration audits. Seven model regressions cover uninitialized header bytes,
actual descriptor construction, derived destructor conditions, unrelated live
loans, overlapping loans, misalignment and address bits without provenance.
The constructor profile now has seven source theorems, eight definitions and
six regressions. Two additional composition theorems and two regressions connect
the freshly extracted constructor and destructor profiles. The constructor gate
checks 304 dependencies and 17 rejection controls; the combined gate checks 925
dependencies and 87 controls. Both use the existing frozen toolchain.

This proves modeled serialization into the validated physical field layout.
Compiler/native ABI correspondence, positive-capacity constructors and ownership,
native lifetime/by-value release, the external allocator implementation, physical
attacker work and the final application security inequality remain open. Next
extend construction to the allocation-backed path, preserving capacity-overflow,
allocation-error and abort branches as well as success, while retaining these
explicit implementation-refinement boundaries.


`fixture.rs` calls the original `Vec::<u8>::new`. `Generated.lean` reifies that
caller and constructor; `Retained.json` preserves both complete source function
declarations, ten nominal types, the evaluated alignment global and target.
`Proof.lean` and `Smoke.lean` are concatenated after the generated file by the
gate rather than compiled as independent Lean modules.

The initial six theorems establish exact nominal return values for every incoming world,
canonical invocation, zero capacity and length, a dangling address of one without
allocation provenance, and rejection of positive reads through that pointer.
The incoming world is unchanged, including its heap, registered pointers and
loans. The initial four regressions cover populated input worlds, arbitrary returned fields,
a live allocation at the same numerical address, and direct constructor invocation.

The pure `NativeRecordLLBC.Operand.addressLiteral` supports the retained alignment
to NonNull transmute. It does not create an allocation origin. The reifier checks
64 physical alignment discriminants, byte alignment, exact nominal layouts,
constrained capacity, operand types, field move/copy modes and the closed call
graph. Changed source bodies must reproduce the tracked generated program and
retained declarations exactly. Seventeen negative controls exercise those guards.
All 304 audited declarations use only the permitted standard Lean dependencies.

Run with the coupled tool receipt:

```bash
scripts/check-hasteboots-vec-empty \
  --build-receipt build/hasteboots-extraction/inline-tools-build-b6esls36/manifest.json
```

The gate freshly extracts the source, compares generated and retained files,
runs rejecting controls, checks the proofs and regressions with warnings as
errors, audits dependencies, and records source, input and log hashes in its
ignored build manifest. `regression.json` records the checked milestone.

The bridge to the resident descriptor is now proved in the checked storage
model. Native aggregate ABI, by-value lifetime release, positive allocation
constructors, compiler refinement, external allocation, physical attacker work
and the final HasteBoots security theorem remain open.
