# Actual Rust parameter extraction

`wrapper.rs` calls methods on the unchanged sibling HasteBoots dependency. It
copies no constructor or accessor implementation. The harness requires source
revision `dff353006322693cab3dc6b654f82151f658f294` and no tracked changes.

Use the prepared backend and verified official tools documented by
`scripts/extract-hasteboots-sampler`:

```sh
scripts/check-hasteboots-parameter-extraction-guards
CARGO_TARGET_DIR=/tmp/hasteboots-charon-parameters-target \
  scripts/extract-hasteboots-parameters \
  --tools /tmp/hasteboots-aeneas-tools \
  --backend /tmp/hasteboots-aeneas-m0 --mode retained
```

Retained mode extracts the actual generic parameter structure, actual
BlockReedSolomonCode structure, five native getters, and two diagnostic wrappers.
Only the generated import changes to `Aeneas.Std` and
`Aeneas.Tactic.RustAttributes`, plus the root model import needed for the
bridge; every generated declaration and term is preserved.
`Generated.lean` records the complete reviewed output. Fresh extraction must
match it; only the native checkout path in source-location comments may differ
for comparison. The generated and checked files are never normalized.
`Proof.lean` and `ModelBridge.lean` are appended and checked with warnings
treated as errors, using the prepared backend and root model libraries. The six
proofs in `Proof.lean` establish exact header reads, exact generic and concrete retained code,
all six returned code fields, header independence from the stored code, and
combined header/code reads. All seven extracted functions and six proofs have
empty axiom dependency closures on the tested pinned setup.

`ModelBridge.lean` adds nine lemmas with explicit representation premises. The
relation compares four header integers and all six code fields, including every
UTF-8 modulus byte and the raw root integer. It assigns a unique model code and
parameter record to each represented source object. Extracted reads preserve the
relation. Existing word-model constructor receipts then supply primitive-root
meaning, canonical root bounds and the Goldilocks modulus bytes for source reads.
The actual source constructor must still establish this relation; it is an open
simulation invariant, not an accepted verifier certificate.

Retained mode now builds the imported root initialization module and checks all
22 generated/accessor/bridge dependency closures against the permitted axiom
whitelist. Only the original 13 closures are empty; bridge proofs use propext,
Quot.sound and, for existing root/encoding results, Classical.choice.

The default mode is **constructor**, which currently fails:

```sh
CARGO_TARGET_DIR=/tmp/hasteboots-charon-parameters-target \
  scripts/extract-hasteboots-parameters \
  --tools /tmp/hasteboots-aeneas-tools --backend /tmp/hasteboots-aeneas-m0
```

Charon reaches actual `Parameters::new_encoded` and its actual block-code
accessors. Aeneas rejects captured-reference option combinators with internal
errors in `option.rs` and a bottom-value return error at
`matrix_weighted.rs:128–136`. No successful retained-mode result substitutes
for a constructor result. Earlier diagnostic configurations also encountered
unsupported `mul_with_overflow`, unsupported outer-loop continues when bringing
in the full RowCode trait, and a NameMatcher assertion when exporting fully
monomorphized types. That assertion returned exit code zero with truncated Lean;
the harness explicitly rejects error logs, missing declarations and incomplete
namespaces before invoking Lean. Further direct extraction of the actual `pcs`
crate with promoted MIR, evaluation of drops, forced MIR inlining and a generic
constructor wrapper still failed at constructor return; no generated terms or
original Rust bodies were rewritten to bypass those failures.

Every run writes a fresh directory under `build/hasteboots-extraction`, including
Rust/Cargo inputs, LLBC, generated and checked Lean when available, logs, commands,
source/tool/patch/lock/proof hashes and a passed/failed manifest. The LLBC target must be 64-bit little-endian x86 Linux. Backend source is
checked against the exact pinned compatibility patches using an isolated Git
index. Generated proof limits stay at 200,000 heartbeats and recursion depth
1,000. Admissions, opaque declarations, unsafe code and native_decide are refused;
dependency audits require exact coverage and only the three permitted axioms.
Eight guard tests exercise truncation, missing declarations, admissions, proof
limits, mode separation, snapshot integrity, proof-source theorem coverage and
dependency audit coverage.

These are extraction and accessor correctness results. Constructor correctness,
source-to-word-model correspondence, Rust compiler correctness, heap/pointer/Arc
aliasing, native NTT/SIMD/Div64, scheduler/physical work, and the complete security
theorem remain open. Borrowed references use Aeneas's value translation here;
there is no claimed physical ownership or allocation theorem.
