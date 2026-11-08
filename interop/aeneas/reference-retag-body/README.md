# Original reference retag bodies

Charon's second `Rvalue::Use` field is `WithRetag`, not a Copy classification.
Copy and move behavior is carried separately by the operand. `NativeSliceLLBC`
now retains an explicit retag flag and element layout on `Rvalue.use`. A true
flag on a reference executes a checked reborrow and returns its newly minted
reference. A false flag transfers the stable reference identity. Primitive and
raw values contain no modeled references to retag. This is a closed-machine
interpretation; Rust alias/lifetime correspondence remains unproved.

The probe has two raw-pointer/length roots returning unit. The shared root
constructs a slice and passes a reborrow to a lifetime-parameterized shared
callee. That callee copies its reference with `WithRetag.Yes`. The mutable root
constructs and reborrows a slice, moves it with `WithRetag.Yes`, and calls a
monomorphic identity body that moves/retags the reference again. The original
shared root creates three leases; the mutable root creates four. Original
callee bodies are embedded from the retained declarations, without callee
callbacks or function-name semantic replacements.

The reifier validates canonical region declarations, free/body region indices,
region-argument count and caller scope, and canonical input/output data types.
It retains original generic/signature declarations in `Retained.json`. Region
labels are erased after these checks; this is not a proof of lifetime validity
or region substitution in Rust. Reference parameters are supported for internal
calls. Public extraction roots still accept only raw-register/length operands;
there is no external reference-tag or pointer-provenance operand.

The seven source layout/body/wrapper equations and two cleanup bridge theorems
are kernel checked. The shared-copy and mutable-move callee equations both
identify their actual checked byte-layout retag. Ten original-source regressions
exercise minted tags, parent chains, cleanup, later physical free, older leases,
conflicting permissions and the external-input restriction.

A separate positive control changes the original identity body's flag from
`WithRetag.Yes` to `WithRetag.No`, reifies that changed syntax and checks it in
Lean. The mutable root then creates three leases instead of four. This verifies
that the flag affects execution, rather than merely being archived.

Reproduce with:

```sh
scripts/check-hasteboots-reference-retag-body \
  --build-receipt build/hasteboots-extraction/inline-tools-build-b6esls36/manifest.json
```

The gate reruns the parent scope and slice-reference profiles with the same
frozen tools, extracts both release and debug-enabled probes, compares original
source snapshots, checks malformed flag/region/copy cases, and audits model and
source dependencies. The release configuration explicitly uses
`-Cdebug-assertions=no`; unsupported constant-inactive UB checks remain retained
halting nodes, and the active debug-enabled profile is rejected.

The scalar-only reifier's former Copy diagnostic is also corrected: its
restricted `WithRetag.Yes` uses have no reference values to retag. Existing
scalar/slice/scope generated positive bodies remain unchanged. Their refreshed
receipts are recorded with the regression evidence.

Typed local/control semantics for the original byte-drop loop, repeated local
storage behavior, iteration lifetime endings, native destructor/allocator
composition, compiler correctness, physical attacker work and the final
security theorem remain open.
