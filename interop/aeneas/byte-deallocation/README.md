# Checked deallocation at the retained external boundary

`NativeByteDeallocation` connects typed byte-pointer, size and alignment operands
to the existing permission-checked heap deallocator. It resolves an existing
complete pointer value, requires a thin non-null pointer and a nonzero valid
64-bit layout, and executes `NativeReferenceMachine.raw (free ...)`. A unit
return follows a successful free. Rejected operands/frees retain the machine
prefix; the caller model also retains a successful free if writing the caller's
result subsequently fails.

Ten model theorems establish execution projection, exact heap change, removal
of one live allocation, unreadability of the freed pointer, retained allocation
history/registries/generations, and absence of overlap with every active lease.
The generic body-call model now has a closed deallocation leaf and an explicit
external classification. It executes this checked operation directly, with no
supplied callee result or work certificate.

The fixture reaches the ordinary sysroot allocator. The gate retains its original
`alloc::alloc::__rust_dealloc` declaration, `Extern` linkage and original `Opaque`
classification. It also retains the original `NonNull<u8>`, `Alignment` and
64-variant `AlignmentEnum` declarations, including the enum's `Foreign`
classification. The source validator checks the exact byte-pointer wrapper and
alignment discriminants. `Boundary.lean` specifies a **logical marshalled
interface** using a raw pointer and machine words; it does not translate a Rust
body or establish equivalence with the native wrapper representations or ABI.

Nine boundary theorems check the alignment list, classification, entry frame,
actual checked execution, projection, uniqueness of the specified leaf result
and removal of one allocation for every normal leaf return. Sixteen model
regressions check real heap/shadow changes, preserved dangling pointer values,
wrong layouts, null-origin pointers, active leases, double frees, stale origins
after address reuse, and caller result-write failure after a free. Five boundary
regressions check invocation and malformed inputs.

Reproduce:

```sh
scripts/check-hasteboots-byte-deallocation \
  --build-receipt build/hasteboots-extraction/inline-tools-build-b6esls36/manifest.json
```

The gate reruns the retained byte-drop call-chain profile, re-extracts this
fixture with unchanged compiler tools, compares all retained declarations and
the specification, rejects malformed external/type/target variants and checks
all model/boundary dependency audits. The caller profile now audits the new
operation as well as its own definitions.

This is a specified external boundary with a real modeled heap effect. Native
external-call/allocator correctness, wrapper representation/ABI correspondence,
allocator caller bodies and their dynamic branches, the outer `Vec` destructor,
Rust lifetimes, compiler correctness and physical work remain open. The native
constructor and final protocol security/expected-work theorem are not accepted
by this profile.
