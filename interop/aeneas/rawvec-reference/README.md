# Stable resident reference operands and original Vec capacity

This profile reifies the complete original ordinary-sysroot `alloc::vec::capacity`
structured body over checked resident-reference operations. Its optimized MIR
already contains the nested Vec/RawVec/RawVecInner capacity projection. The probe
wrapper and Vec constructor are not interpreted, and native carrier, reference,
ABI/compiler and lifetime correspondence remain unproved.

`NativeRawVecReference` selects resident shared leases for two closed object
profiles: sixteen-byte RawVecInner and twenty-four-byte Vec, both aligned to
eight. Entry selectors take register indices, never caller-provided tags or
extents. Logical reference values retain stable tags. Field reads resolve those
tags against the current reference register list and live ledger, so inserting
new borrow registers does not invalidate older values. The logical two/three-word
counts describe object extents; they assert no native slice/fat-pointer ABI.

`NativeRecordLLBC` now has the corresponding input selectors and a closed
`rawVecField` rvalue. It reads capacity bytes or recovers a complete pointer from
shadow storage, preserves failed read prefixes, and executes the retained retag
flag. Word-aligned reference retags perform actual whole-object reborrows. The
existing body/invocation execution-projection and reachability proofs cover the
new rvalue. The original storage readers still require the sixteen-byte profile;
their actual byte/shadow operations were factored into shared checked accessors.

Eight reference-layer theorems prove selection, decoding, resolution and actual
execution/reachability. Two accessor projection theorems and one interpreter
helper projection theorem accompany the integration. Thirty new declaration
audits and seventeen model regressions cover both object profiles, shifted
reference indices, whole-object reborrows, wrong/revoked/missing operands,
origin-free pointer bytes, high-bit rejection and failed destination writes
retaining an already executed read.

The source reifier validates the original method classification, signature,
regions, locals, element-size global, nested field owners/types/indices and every
statement. It checks Vec/RawVec/RawVecInner storage geometry and preserves the
usize switch, maximum-word fallback, read retag flag, early return, storage
changes and shared suffix. The original Foreign/Opaque capacity carrier remains
in the retained source. Its read has an explicit high-bit guard, and its logical
carrier-to-usize transmute is word identity. Native carrier validity and bitcast
correspondence are not established by this representation.

Four source theorems establish scalar-retag behavior, body projection and both
complete invocation outcomes from the checked read result, including rejection
with its executed prefix. Six source regressions check returned capacity, zero,
high-bit rejection and receiver selection. These are kernel proofs and concrete
regressions of the reified semantics, not a Rust compiler-correctness theorem.

Run:

```sh
scripts/check-hasteboots-rawvec-reference \
  --build-receipt build/hasteboots-extraction/inline-tools-build-b6esls36/manifest.json
scripts/check
```

The source gate passed 188 dependency audits and twenty-five rejection controls.
Mutating the retained element-size literal from one to zero changes generated
code and proves a universal maximum-word return with unchanged world, exercising
the no-read branch. This is an AST mutation control, not a claim to support a
second native element type. Disabling the read retag flag also changes generated
code and passes all source proofs/regressions. The Global gate was revalidated
with 223 audits and 34 rejection controls; the storage gate passed again with
36 audits and twenty controls. The full `scripts/check` run passed its
11,009-job build and all subsequent smoke checks. Receipts and log hashes are
in `regression.json`.

Next reuse the reference operands for the original RawVec `current_memory`
body, including pointer wrapper reconstruction, its zero branches and unchecked
product. Compose the original deallocation and Vec destruction calls with Global
dispatch. Native reference construction, carrier validity, stack/layout/ABI and
lifetime/compiler correspondence, allocator correctness, physical work and the
final expected-work security theorem remain open. No constructor-acceptance
claim, successful helper stub or caller work certificate is supplied here.
