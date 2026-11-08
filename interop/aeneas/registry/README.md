# Native verifier-carrier reads and decoded registry ownership

`wrapper.rs` reads the actual `snarks::packed_oracle::CanonicalVerifierOracle`
from the unchanged native dependency. This carrier stores references to trusted
parameters and a `pcs::matrix_weighted::Commitment`. The wrapper returns those
stored references with their original lifetimes; it does not rebuild parameters
or commitments. Its five functions read both fields, the registry length, an
optional original slot, the actual `Digest512` byte array, and invoke native
`Digest512` equality.

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
checks the combined artifact with all 125 dependency audits. Only propext,
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
heartbeats and recursion depth 1,000. Seven guard groups check output completeness,
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

`Lookup.lean` connects the modeled dispatcher's checked receipt to the extracted
original Rust source read. Four theorems derive stored-vector decoding and field
membership from `receipt_extracted`; callers supply neither a stored source
vector nor a matching field key. The read index equals the receipt's first-owner
slot, the decoded carrier equals its oracle, parameters equal the extraction
context, and all root bytes agree. The enclosing-program theorem derives log
truthfulness and returns either the existing joint bad event or that exact read.

The strongest wrapper, `receipt_from_original_parent`, derives receipt framing,
preflight frame validity and registry-packet message bounds from the original
parent and existing body/helper/source/batch message domains. It takes no
intermediate frame list, successful stored-packet decoder, field-key equality,
or receipt-framing premise. `NativeGoldLookupFraming` proves the stage composition
independently, including source aliases and earlier receipts before a later stop.
Original-parent framing, stage message domains, registry decoding and lookup
trace inclusion remain explicit premises. Connecting the modeled dispatcher and
initializer to their native bodies, and proving parameter construction, heap,
Serde/bincode/hash-update and physical-work refinement, remain required.

## Causal decoded lookup

`CausalLookup.lean` executes the retained source decoder before the modeled
lookup dispatcher. A causal prior program supplies source values, context data
and local memory. Successful decoding replaces the context registry with the
complete decoded original source vector; failure returns None. The dispatcher
outcome and original setup are retained for an arbitrary causal continuation.
No proof certificate is stored in the operational setup.

Eight kernel theorems establish exact dispatch/prelude behavior, computed
registry correspondence, original dispatcher outcome and inclusion of its
actual trace in each complete continuation prefix. The receipt association
result therefore needs no caller source-decoder correspondence or lookup trace
inclusion premise. Original-parent framing and stage message domains remain
explicit. Accepted extraction is checked against the same full history,
including prequeries, lookup execution and continuation.

The event that any retained receipt is misassociated at any finite continuation
prefix reduces to the existing persistent bad event. Its probability is bounded
by the supremum of the joint prefix charges for this same causal machine, with
no per-receipt multiplier or lifetime cutoff. This is still an ideal-oracle
association result: the complete native dispatcher, source decoder/heap,
physical work and false-PBS/application coverage remain unproved.

## Native digest comparison

`roots_equal` invokes the unchanged native derived `Digest512::eq`; its body is
included in the reviewed extraction snapshot and audited separately. It calls
the backend's transparent byte-array comparison, not a supplied equality oracle.
`Equality.lean` has five kernel lemmas for list comparison, exact digest equality,
and equivalence with the model's full 64-byte root equality (both true and false
results). The proof covers arbitrary digest bytes and derives matching list
lengths from the actual fixed-array carriers. No hash-injectivity or collision
resistance assumption is introduced.

This discharges the digest comparison operation used by registry ownership;
it does not extract or refine the private first-owner iterator loop. Parameter
context computation, original representative selection, native initialization,
serialization, heap and physical attacker work remain separate obligations.
The manifest now hashes every Lean input, including lookup, causal lookup and
equality proofs; a guard rejects unrecorded proof files.

## Pointer-backed constructor provenance

`Pointer.lean` composes actual extracted slice/field reads with the operational
pointer registry and constructed parameter arena. Both registry decoders must
return the same complete model registry. This compatibility premise remains
explicit and is not a proof that the native Rust heap realizes the arena.

Three kernel theorems retain one original index throughout: the native usize
read, the borrowed pointer, its matching address/allocation origin, the retained
arena entry, and that entry's constructor provenance. The ownership theorem
uses the computed first-original context/root owner, including earlier unused
aliases, and retains context-trace inclusion. The extraction theorem decodes
the actual native parameter object to the extraction context and identifies
its raw root with the accepted field root. Replay, inclusion and no-bad-event
premises remain explicit. No native verifier check or allocator model is
changed. The receipt hashes all four imported pointer/arena model sources and
rejects changes to them during extraction.

## Whole-heap representation and computed compatibility

`Heap.lean` relates an immutable heap of actual extracted parameter values to a
heap of retained arena handles. Corresponding cells have identical addresses
and allocation origins; the native cell value decodes to the parameter entry
at its retained handle. This relation covers the complete heap independently
of the borrow list or registry. It is preserved by arena append, paired object
retention and paired retirement, starting from empty heaps.

Eleven kernel theorems establish these preservation properties and simulation
of every successful pointer read. The operational `materialize` function reads
native parameter cells and constructs the original carrier list in order,
retaining commitment values and duplicate borrows. Successful materialization
from represented heaps supplies both a successful native-value registry decode
and the matching pointer-backed registry result. Registry compatibility is a
conclusion here, rather than two independently supplied registry runs.

The ownership and extraction wrappers derive the pointer-backed run and keep
native first-original slice reads, parameter decoding and constructor provenance
at one index. Their initializer/replay/history/no-bad-event premises remain
explicit. Establishing the heap invariant and materialization behavior from
Rust allocation, borrowing and source execution is still required. The proofs
do not establish allocation freshness, object layout or physical work. This
operational materializer adds no native verifier code or runtime checks.

## Failure preservation

Four further heap theorems cover failure as well as success. Represented native
parameter-value heaps and arena-handle heaps agree on read failure for every
pointer. Ordered materialization fails exactly when an original borrow is
unreadable, and exactly when the corresponding model resolution fails. Under
the whole-heap invariant, this also characterizes failure of the complete
pointer registry: successful reads cannot leave an invalid arena handle.
The failure witness ranges over the complete original borrow list, including
later unused entries and duplicate aliases.

These are failure properties of the operational materializer and heap model.
They do not claim that Rust detects invalid references or add native runtime
checks. Rust reference validity and source/allocator refinement remain open.
