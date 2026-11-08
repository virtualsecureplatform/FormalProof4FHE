# Baseline controls for selected-function inlining

`fixture.rs` exercises two calls to a non-inlined helper with mutable state,
early errors and overflow aborts, plus an `Option::and_then` closure capturing
a shared reference. It is a compiler regression fixture, not native verifier
code. `Baseline.lean` is the complete output of the official pinned Charon and
the reviewed constructor-typing-compatible frontend, before any new Charon
inlining behavior. Generated terms are not rewritten; checking changes imports
and appends proofs only.

Eight kernel theorems check the original behavior: zero-increment rejection,
first-error state, retained first mutation on second error, both returned
values/state on success, first/second arithmetic aborts, and none/some capture
results. The three source functions and eight proofs require eleven dependency
audits using only propext, Classical.choice and Quot.sound. These controls do
not prove an inliner or native HasteBoots constructor correct.

Run with pinned tools/backend and a reviewed frontend receipt:

```sh
scripts/check-hasteboots-inline-baseline-guards
scripts/check-hasteboots-inline-baseline \
  --tools /tmp/hasteboots-aeneas-tools --backend /tmp/hasteboots-aeneas-m0 \
  --build-receipt build/hasteboots-extraction/static-frontend-build-kc2ncvv7/manifest.json
```

The gate freshly extracts the source, validates IR and target, checks complete
output against the reviewed snapshot, rejects frontend errors even on zero
exit, kernel-checks all behavior proofs, and audits exact allowed dependencies.
Its receipt hashes source, snapshot, proofs, IR, checked artifact and logs.
No proof limits are increased. Five guard tests cover changed/incomplete source,
admissions, error logs and missing/duplicate/unapproved dependency reports.
