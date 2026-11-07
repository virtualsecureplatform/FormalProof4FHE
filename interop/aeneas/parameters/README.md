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
`Aeneas.Tactic.RustAttributes`; every generated declaration and term is preserved.
`Generated.lean` records the complete reviewed output. Fresh extraction must
match it; only the native checkout path in source-location comments may differ
for comparison. The generated and checked files are never normalized.
`Proof.lean` is appended and checked with warnings treated as errors. Its six
proofs establish exact header reads, exact generic and concrete retained code,
all six returned code fields, header independence from the stored code, and
combined header/code reads. All seven extracted functions and six proofs have
empty axiom dependency closures on the tested pinned setup.

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
namespaces before invoking Lean.

Every run writes a fresh directory under `build/hasteboots-extraction`, including
Rust/Cargo inputs, LLBC, generated and checked Lean when available, logs, commands,
source/tool/patch/lock/proof hashes and a passed/failed manifest. The LLBC target must be 64-bit little-endian x86 Linux. Backend source is
checked against the exact pinned compatibility patches using an isolated Git
index. Generated proof limits stay at 200,000 heartbeats and recursion depth
1,000. Admissions, opaque declarations, unsafe code and native_decide are refused;
dependency audits require exact coverage and only the three permitted axioms.
Seven guard tests exercise truncation, missing declarations, admissions, proof
limits, mode separation, snapshot integrity and dependency audit coverage.

These are extraction and accessor correctness results. Constructor correctness,
source-to-word-model correspondence, Rust compiler correctness, heap/pointer/Arc
aliasing, native NTT/SIMD/Div64, scheduler/physical work, and the complete security
theorem remain open. Borrowed references use Aeneas's value translation here;
there is no claimed physical ownership or allocation theorem.
