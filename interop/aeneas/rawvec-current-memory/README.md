# Original RawVec current_memory root

This profile reifies the complete original ordinary-sysroot
`alloc::raw_vec::current_memory` root body over the checked byte/shadow interpreter.
It retains the unsafe signature, original regions/locals, both zero branches,
the two nonzero-path capacity reads, unchecked unsigned product, alignment-word
cast, Layout construction, pointer and marker projections, Some/None construction,
early returns, calls, unwind and common suffixes.

The interpreter adds unsigned multiplication that rejects overflow rather than
wrapping, nominal enum-to-word extraction and recursive record-result wrappers.
The zero-byte marker projection performs a checked zero-byte reference read at
offset sixteen, preserving its scratch pointer and empty output event. It is not
replaced by a successful helper stub. The source NonNull and PhantomData wrappers
retain their distinct nominal identities. Six new model theorems establish the
arithmetic results/framing, enum conversion and marker execution projection;
existing rvalue/body/invocation projection and reachability proofs cover the new
cases. Sixteen new declaration audits and sixteen model regressions accompany
these operations.

Four source theorems prove body and invocation projection plus the exact zero
outcomes: zero element size returns None without a read, and zero capacity returns
None with the computed capacity-read state. Fourteen source regressions check the
early branches, reconstructed pointer/layout, products, overflow, null/high-bit
failure prefixes, receiver/alignment rejection, issued provenance and old pointer
generations surviving address reuse. The positive nonzero path preserves the
heap while retaining both capacity reads, the pointer load and the marker event.

The two precondition declarations remain in the snapshot with their original
Foreign/Opaque and Transparent/Structured classifications. Their bodies are
untranslated and enter `unsupported` if reached. The original call guards are
literal false, retained in the AST. A source mutation activates the multiply
precondition guard and checks that the entry is unsupported after retaining the
two capacity reads. No untranslated helper is converted to normal return.

The Foreign/Opaque constrained-capacity carrier is still represented by guarded
words. Its native validity and transmute correspondence are not proved. The
alignment cast uses the retained nominal enum and checked value representation;
it is not a native layout/compiler proof. Native reference construction,
stack/layout/ABI, lifetime/compiler correspondence, helper refinement, allocator
correctness, physical work and the final expected-work security theorem remain
open. This profile does not interpret RawVec deallocation or outer Vec destruction
and supplies no constructor-acceptance or caller-work certificate.

Run:

```sh
scripts/check-hasteboots-rawvec-current-memory \
  --build-receipt build/hasteboots-extraction/inline-tools-build-b6esls36/manifest.json
scripts/check
```

The gate passed 211 dependency audits and twenty-three rejection controls with
fresh extraction and retained-source comparison. Activating a helper guard and
disabling the pointer retag flag both change generated code and are checked in
Lean. The earlier Global gate passed again with 239 audits and 34 rejection
controls; the capacity gate passed with 204 audits and twenty-five controls.
The full `scripts/check` run passed its 11,011-job build and all subsequent
smoke checks. Receipts and log hashes are recorded in `regression.json`.

Next connect this original root to its caller `alloc::raw_vec::deallocate`.
Implement the source's mutable receiver/shared reborrow and zero-byte Global-field
borrow, consume the original Option match and preserve the returned pointer's
complete identity through the actual allocator call. Then compose the original
RawVec/Vec destruction path. Loan cleanup remains explicit ghost composition
until native lifetime correspondence is proved.
