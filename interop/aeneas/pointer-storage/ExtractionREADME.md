# Raw-pointer extraction with shared storage data

The opt-in `-provenance-pointers` frontend mode requires checked monomorphic
64-bit little-endian Lean extraction. It replaces the legacy pointee-value raw
pointer binding with the shared pointer representation used by the existing
storage model. No backend or production Rust file changes.

NativePointerRepresentation imports only Init. It retains the existing public
Address/Origin/Pointer names and adds raw-pointer descriptors with data address,
allocation identity/generation and thin/slice/vtable metadata. Pointee type and
mutability are phantom indices; no pointee value stands in for an address.
Cast operations preserve storage and metadata. Pointer comparison uses data
address and metadata bits, ignoring data/vtable ghost provenance. Structural
equality of the descriptor is deliberately separate from source comparison.
The tag's relation to a Rust pointee type, actual object layout and a valid
source encoding remain refinement obligations; a descriptor is not a permission.

The existing NativePointerStorage now imports these shared definitions. Its
public API and storage laws remain available. NativeRawPointerStorage proves
that casts preserve logical registry reads, and that missing provenance, zero
addresses and retired origins cannot read. These reads are not Rust dereferences.
The earlier Proof.lean boundary counterexamples and their 21-audit gate remain
unchanged and pass again; see README.md. Six old root audit messages are updated
because the lighter representation removes their former propext dependency.

The complete generated source module covers mutable/constant identities, raw
mutability and pointee casts, equality/inequality, and wide slice comparison.
ExtractionProof.lean gives seventeen exact/case theorems, including all-input
field preservation, origin-independent comparison, slice-length distinctions,
null casts and unaligned raw casts. Four runtime theorems, six shared-model
theorems and four storage-bridge theorems complete the new obligations. The gate
checks 51 source/runtime/model dependency audits and five storage audits, allowing
only propext/Classical.choice/Quot.sound with unchanged proof limits.

```sh
scripts/check-hasteboots-pointer-extraction-guards
scripts/check-hasteboots-pointer-extraction \
  --build-receipt build/hasteboots-extraction/inline-tools-build-RECEIPT/manifest.json \
  --backend /tmp/hasteboots-aeneas-m0
```

Eight negative cases reject missing word/profile constraints, incompatible target
metadata, the NonNull pattern without the provenance profile and a slice-to-thin cast that needs
metadata-dropping semantics. Existing profiles retain their original bindings.
The compiler still rejects unsupported operations rather than applying the scalar
cast model to them. The historical baseline kernel-checks that the old binding
models a safe raw-pointer cast as undefined; it does not assert a Rust failure.

`probe-hasteboots-inline-constructor --cleanup-scope pointers --target-word64
--expand-language-ub-checks --provenance-pointers` retains the original pointer
wrappers. The next milestone in `../nonnull-pointers/README.md` adds checked
`*const T is !null` patterns and the original outward `as_ptr` conversion.
No native constructor is accepted. Further source pointer/heap
operations, allocator/deallocation, layout queries/initializers, naming collisions,
Rust caller/compiler refinement, NTT/SIMD/scheduler refinement, causal oracle/owner
accounting, BabyBear and the 128-bit expected physical-work security theorem
remain open. This interface supplies no allocator, dereference, exposed-provenance
recovery, successful constructor callback or physical-work charge.

The full repository `scripts/check` passes, including its 10,929-job build and
subsequent audits/smoke commands. Existing upstream extraction retains all 128
artifacts byte-for-byte; only the known dyn.rs lifetime case fails.
