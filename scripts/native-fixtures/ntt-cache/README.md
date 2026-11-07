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
