# Compiler-evaluated runtime-check queries

Rust leaves UB/overflow/contract configuration queries in MIR. The experimental
Charon option `--evaluate-runtime-checks` resolves each query through the pinned
rustc `mir::RuntimeChecks::value(self.tcx.sess)` API. Rustc itself applies debug
assertion defaults and explicit UB/overflow/contract flag overrides. No Boolean
is supplied by Aeneas or an external proof assumption. Without the option, the
original deferred query representation is retained.

This serialized option requires Charon schema 0.1.226 and regenerated OCaml
readers. Six UI controls compare enabled extraction and default policy for
checks enabled, checks disabled and explicit mixed overrides. The complete
Charon tests and Clippy pass. The original eight compiler profiles are unchanged.

```sh
scripts/check-hasteboots-runtime-checks-guards
scripts/check-hasteboots-runtime-checks \
  --build-receipt build/hasteboots-extraction/inline-tools-build-RECEIPT/manifest.json \
  --backend /tmp/hasteboots-aeneas-m0
```

The fresh source extraction covers two queries and a UB-query-dependent branch.
Three complete snapshots record debug defaults `(true,true)`, disabled defaults
`(false,false)` and explicit UB-off/overflow-on overrides `(false,true)`. Six
source functions and six closed behavior theorems require twelve exact kernel
dependency audits. The gate checks the policy, target and absence of residual
queries, and requires the default policy to retain queries and reject in Aeneas.
Four guard tests reject altered Booleans/branches, residual queries, changed
policy and missing proofs. No backend or production Rust is changed; proof
limits are unchanged and only the three allowed Lean axioms are accepted.

Native constructor diagnostics now require compiler evaluation and reject
remaining runtime-query operations anywhere in the IR, alongside their existing
precise-drop, allocator and function-declaration checks. Original layout
translation passes `ub_checks` and next rejects `usize -> Alignment`, an inward
transmute that requires valid enum representation semantics. Large usize
literal handling, remaining layout/pointer/heap/work refinement and complete
native constructor/security proofs remain open.

The preceding 76 kernel dependency audits passed again, for 88 across the paired
profile. All 143 extraction guard tests passed. Full upstream extraction
completed 97 targets and rejected only the preexisting `dyn.rs` erased-lifetime
case. All 128 regenerated files remain byte-identical. `regression.json` records
tool and patch hashes, rustc API source hashes, all audits, native diagnostics
and the upstream per-file comparison.
