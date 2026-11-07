# Native verifier-carrier reads and decoded registry ownership

`wrapper.rs` reads the actual `snarks::packed_oracle::CanonicalVerifierOracle`
from the unchanged native dependency. This carrier stores references to trusted
parameters and a `pcs::matrix_weighted::Commitment`. The wrapper returns those
stored references with their original lifetimes; it does not rebuild parameters
or commitments. Its four functions read both fields, the registry length, an
optional original slot, and the actual `Digest512` byte array.

`Generated.lean` is the complete reviewed output of the pinned official
Charon/Aeneas tools, with invariant checking enabled. No experimental compiler
profile or source edit is needed. The native source revision is
`dff353006322693cab3dc6b654f82151f658f294`, shared with the parameter extractor. Native source must be clean before and after
extraction. The 86-package fixture lock uses only versions, sources and checksums
present in the pinned native workspace lock, plus this fixture package.

## Checked results

`Proof.lean` has eight kernel theorems for the four extracted functions. Reads
return the exact retained parameters/root. Length is the actual source slice
length. Indexed reads return the original list position, including duplicates;
out-of-range reads return None. The actual Digest512 newtype has exactly 64 bytes.
Shared references use Aeneas's value translation; these statements do not equate
heap addresses or prove pointer/allocator behavior.

`Decode.lean` specializes the generic carrier to the already extracted Goldilocks
Brakedown parameters and actual Digest512 representation. All 64 raw U8 bytes map
to the model root, with a proved injective conversion. The parameter decoder
preserves every stored parameter/code field. Seven theorems prove exact native
reads, decoder field correspondence and injectivity, and the precise existence
condition: the stored modulus UTF-8 byte length fits below `2^64`. Decoding does
not establish code validity, primitive roots or constructor success.

`Registry.lean` decodes the complete original slice in order. An invalid entry
rejects the whole collection. There is no used-slot filter or alias deduplication.
Seven theorems prove per-entry correspondence, length and append-order
preservation, and exact source reads at every returned model index. The bounded
model vector derives its length bound from the source slice's own usize bound;
there is no caller-provided fitting or registry-correspondence certificate.

`original_owner_read` composes that result with the existing modeled registry
initializer. Its computed owner is read through the actual extracted native
slice accessor at the same original index. It returns the corresponding decoded
parameters and raw root, proves the index is no later than the target slot, and
proves every earlier computed context-digest/root key differs from the target.
Thus earlier unused aliases remain eligible: the initializer and decoder consume
the complete original registry before grouping. Context-hash collisions are not
silently excluded, and equal digests alone do not prove parameter equality.

This is conditional on execution of the existing **modeled** initializer on the
decoded registry. Refinement of the native Rust registry initializer/owner body,
actual heap/reference provenance, parameter/code construction, Serde/bincode/hash
updates, physical work and full protocol security remain open.

## Reproduce

Use the pinned official tools and prepared backend described in
`../parameters/README.md`. The harness first freshly checks the 50 parameter
source/accessor/decoder/binding audits, then extracts this native carrier and
checks the combined artifact with all 88 dependency audits. Only propext,
Classical.choice and Quot.sound are allowed; no admissions, native proofs or
proof-limit increases are accepted.

```sh
scripts/check-hasteboots-registry-guards
CARGO_TARGET_DIR=/tmp/hasteboots-charon-parameters-target \
  scripts/extract-hasteboots-registry \
  --tools /tmp/hasteboots-aeneas-tools --backend /tmp/hasteboots-aeneas-m0
```

Each run records Rust/Cargo inputs, exact source/tool/backend preflight receipts,
source/LLBC/proof/snapshot hashes, commands, logs and terminal status in a fresh
build directory. The target must be x86_64 little-endian. Fresh generated terms
must match the snapshot; only native checkout paths in source comments may
differ for comparison. Compiled terms are not normalized. Compatibility changes
only imports, and then append the checked proofs. Proof limits remain 200,000
heartbeats and recursion depth 1,000. Six guard groups check output completeness,
imports, admissions/limits, dependency lock/checksum integrity and exact proof
audit coverage.

## Accepted associations and the full causal history

`Association.lean` adds a data-only setup containing saved local state, the native
source slice and parent transcript. A causal prior program produces this setup;
the new modeled prelude decodes the original registry and runs the existing
modeled initializer. Initialization outcomes retain the setup and their full
observation trace, including failure paths. The continuation receives saved
state and primitive oracle responses, and every analysis prefix retains the
same prequery/initializer/continuation history.

Twelve theorems prove initialization/prelude origin and trace inclusion, then
transfer successful modeled field associations to native original-slot reads.
The complete field source key must match an entry in the canonical stored vector
decoded from the initializer. Outside the existing persistent bad event, the
first owner's actual extracted slice read returns parameters that decode exactly
to the extraction context, and its raw root equals the field's root.

The causal-prefix theorem derives history truthfulness and initializer inclusion
from execution. Its conclusion explicitly separates the persistent bad event
from original-source association; it takes no independent truthful-log,
root-safety or collision-exclusion certificate. A more general trace formulation
covers every initializer whose computed trace is included in one full program
history, allowing multiple registry/field witnesses without separate losses.

The event that any such association fails at any finite machine prefix is
bounded by the supremum of the existing joint persistent-root hazard charges
for that same machine. All registries, source positions, inputs and matched
fields in the event are covered together. Fuel is an analysis prefix, with no
retry/lifetime cutoff or per-field multiplier. This is an ideal-oracle charge
bound; actor attribution, physical attacker work and the final 128-bit theorem
are not established here.

The field-key membership condition and canonical stored-vector decoding remain
explicit computed conditions. Connecting them and the modeled prelude to the
native verifier/initializer body, and proving parameter construction, heap,
Serde/bincode/hash-update and physical-work refinement, remain required.
