# Pointer construction from original parts

The checked word64 `-provenance-pointers` profile now handles the original
`PtrFromParts` builtins used by stdlib `from_raw_parts` and `from_raw_parts_mut`.
A thin pointer supplies its existing data address and provenance. Unit metadata
constructs a thin result; a usize length constructs slice/string metadata with
exact 64-bit conversion. All four constant/mutable constructions preserve the
storage record. They grant no allocation, alignment, borrow, dereference or work
permission. Null and unaligned addresses, empty slices and maximum lengths are
permitted for pointer construction itself; using the result has further obligations.

The frontend validates the original one-pointee/two-operand builtin call and its
single erased region before elaborating concrete data/metadata types into the
interpreter signature. It checks destination pointee/mutability, requires a thin
raw data pointer and verifies the metadata type against the target pointee.
Lengths cover slices/str and closed declarations explicitly carrying length
metadata. Thin declarations must carry no metadata. Tuple metadata follows the
last element. Unknown/inherited metadata and vtables remain unsupported.
No source body, replacement callback or typeclass operation is supplied.

Extraction selects one of four concrete runtime definitions after checking the
elaborated types. Accepted source, original IR and generated terms remain intact;
IR mutations are used only for rejection tests. The internal generic signature
is a checked type elaboration, not a Rust ABI or compiler-correctness theorem.
Relating descriptor metadata tags to actual Rust source values, pointers and
layouts remains an explicit source-encoding obligation.

The fixture retains six original ordinary-sysroot construction bodies and seven
callers, covering mutable/constant slice pointers, a mutability cast, thin u64
pointers, string metadata and a closed struct pointee. Twenty-two source theorems
cover all thirteen bodies, full field preservation and boundary cases. Eight
runtime theorems include exact 64-bit length value/roundtrip laws. The complete
gate checks 57 dependency audits and rejects 16 unsupported target/profile/type/
operand cases. It admits no new axiom or raised proof limit.

```sh
scripts/check-hasteboots-pointer-parts-guards
scripts/check-hasteboots-pointer-parts \
  --build-receipt build/hasteboots-extraction/inline-tools-build-RECEIPT/manifest.json \
  --backend /tmp/hasteboots-aeneas-m0
```

The native constructor now gets past pointer-parts construction and reaches an
actual raw-pointer dereference in stdlib `drop_in_place`, reached from the original
vector destructor. That operation still rejects. The ordinary standard library,
52 retained functions, precise drops and original pointer carriers remain intact;
no native constructor is accepted. This is a memory/refinement obligation:
source allocator initialization, validity/aliasing, actual reads/writes and
proper deallocation must be related to the model. Replacing that path with a
successful callback or a no-op drop would not satisfy the objective.

Pointer metadata projection, wide-carrier conversions, allocator/layout queries,
caller/compiler/heap and NTT/SIMD/scheduler refinement, causal oracle/owner history,
BabyBear and the final expected physical-work security theorem remain open.
`regression.json` records the frozen tools, current checks and failed native run.
