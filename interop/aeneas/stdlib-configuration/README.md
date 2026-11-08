# Explicit stdlib configuration and external roots

Charon automatically uses a Miri-built standard library when no sysroot is
specified. Its `cfg!(miri)` changes the original check_language_ub helper.
The ordinary sysroot, with checks enabled, returns true; Miri returns false.
With checks disabled the ordinary helper returns false. These are different
compiled source configurations. Earlier Miri fixture proofs cannot establish
production behavior without a configuration/refinement argument.

The baseline additionally exposed silent pruning of a requested external
entry point. The monomorphic frontend now preserves functions matching explicit Charon
start_from and start_from_if_exists patterns when pruning, retaining their original
foreign-source metadata. No generated computational term is rewritten. Existing
profiles remain unchanged unless monomorphic builtin shapes are enabled.

The fixture is a marker; extraction starts at the actual private core helper.
Three complete generated modules and five kernel theorems establish the two
sysroot behaviors, debug-on/off behavior and their inequalities. Four original
source definitions and those five theorems pass nine dependency audits without
new axioms. Four guards reject missing external roots, relabeled source metadata,
changed sysroot/query policies, changed Booleans and missing difference proofs.
Proof limits are unchanged.

```sh
scripts/check-hasteboots-stdlib-configuration-guards
scripts/check-hasteboots-stdlib-configuration \
  --build-receipt build/hasteboots-extraction/inline-tools-build-RECEIPT/manifest.json \
  --backend /tmp/hasteboots-aeneas-m0
```

The native probe now explicitly selects `--sysroot default` by default and
uses separate Cargo targets for ordinary/Miri libraries. `--sysroot miri` or
`--sysroot auto` are explicit diagnostic comparisons. Serialized sysroot and
constant-evaluation policies are checked; a guard prevents silent substitution.
`--expand-language-ub-checks` retains the original helper body. The ordinary
arithmetic/word64 extraction retains 52 functions and currently fails enum
expansion in original Result::from_residual; the Miri comparison retains 89
functions and generates a complete module but still rejects fourteen opaque
declarations. Neither is an accepted native constructor refinement. Miri's
smaller unresolved inventory does not describe production readiness.

The additional `layout-init` scope exposes original SizedTypeProperties::LAYOUT,
SIZE and ALIGN initializers, revealing size_of/align_of compiler intrinsics.
`--const-values` requests Charon's existing rustc constant evaluation; it is an
experimental diagnostic, not accepted extraction. The recorded automatic-sysroot comparison
crashes because Aeneas assumes every global has an initializer function. These
failures and their exact artifacts are recorded in regression.json; no fallback
value, hardcoded layout or admitted initializer is introduced.

Next work must follow the ordinary-sysroot enum failure and remaining source
library obligations, then layout-query/initializer support and the remaining runtime,
pointer and deallocation semantics. Full compiler/caller/heap refinement,
NTT/SIMD/scheduler refinement, causal oracle/owner accounting, BabyBear and the
128-bit expected physical-work security theorem remain open. No production Rust
or Lean backend was changed; the stdlib distinction is not a physical work bound.
