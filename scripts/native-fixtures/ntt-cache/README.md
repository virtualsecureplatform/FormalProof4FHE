# Native Goldilocks cache regression

Run `scripts/check-native-ntt-cache-fixtures`. It invokes the actual unchanged
sibling HasteBoots checkout at commit
`dff353006322693cab3dc6b654f82151f658f294`, using the committed fixture lockfile.
The script rejects a different commit or tracked source changes. The backend
must be locked to concrete-ntt `cdeba793e46208320b30d78be19f7be78d49016a`.
The checker also requires ArcSwap and concrete-ntt to match the native workspace
lockfile in version, source and checksum.
Set `CARGO_TARGET_DIR` to reuse an external Cargo target directory if desired.

A fresh process reads roots for log sizes 4, 5 and 10 before initializing any
table. The roots match the actual backend Plan constructor. Eight threads then
initialize those keys in rotated order and retain 24 table handles. Every handle
for a key must share the same Arc as later reads, and all roots must retain their
original values. Root lookup at unsupported log size 3 returns the original
error; table initialization unwraps that error into a panic. The fixture catches
that expected panic and verifies the retained valid table/root survive unchanged.
Python requires every output marker and independently checks canonical values
and primitive-root power equations.

This exercises actual public cache/concurrency behavior, but does not force a
particular CAS retry schedule or prove every interleaving. Lean models literal
first-match reads, constructor-backed cache bodies, captured snapshots, rejected
proposals and stale-view root reads. The from-empty provenance theorems do not
replace ArcSwap/Mutex/pointer/ABA, Rust/Charon/Aeneas, memory, allocation, scheduler
or actor-separated physical-work refinement. Ghost receipts supply no work fee.
The existing `ntt-roots` fixture continues to check limb arithmetic, initialization,
primality, stored root powers and transform/normalization values.

The fixture also runs the actual `BlockReedSolomonCode::new` for four requests,
including partial blocks, the minimum domain and N=1024/N=4096. It checks all six
stored serde fields using a structural decoder and the actual cached/backend
root. Python independently recomputes padded counts, domains, primitive powers
and every bincode varint/String/raw-root byte. Eight rejected requests verify
dimension/blowup checks, message/domain/stride overflow, and unsupported field
domain generation in their original order. Lean's explicit constructor phases
perform real word-model generation, RCU init/retry and table load; completed
receipts supply encoding/root/codeword meaning without table-result callbacks.
These remain value/source models, not Rust/heap/SIMD or physical-work refinement.

The parameter fixtures call actual `Parameters::new_encoded` for three code
objects. They compare retained fields and serialization, capture the complete
context preimage, and compare the actual SHA-512 context digest. Python checks
all varints, domain tags, modulus strings, code bytes and SHA-512 independently.
Nine errors cover dimensions, code shape and all four allocation overflow classes.
The Merkle overflow uses a fixture-only generic RowCode with a huge tree; it is
not claimed reachable through BlockReedSolomonCode::new (that type derives
Serialize, not Deserialize). This remains regression evidence, not source refinement.

Balanced-layout fixtures call actual `Parameters::balanced_block_rs` for six
requests, including degree 1024 at widths 3/4. A two-variable width-4 request
with one query and blowup 2 has tied minima at row splits 0 and 1; the source
must retain split 0. Python independently enumerates the guarded candidates,
checks the minimum and earliest tie, and validates complete code/context bytes
and SHA-512 digests. Seven failures cover the layout input guards, table-size
overflow and absence of a field-compatible domain. Lean compares all six full
native code/context byte pairs after selection and explicit code construction.
