# Checked word64 bit-count intrinsics

The previous word64 profile disabled assumed function/global/effect bindings.
`baseline.json` records its two unresolved intrinsic declarations. This profile
now permits exactly ctlz_nonzero<usize> and ctpop<usize>, preserving all other
original source bindings. It still requires monomorphic Lean and exactly one
64-bit little-endian target. Fixed u64/u32 instantiations are deliberately outside
this usize-specific interface.

A prepass checks every selected declaration and every direct function reference,
including constants: closed monomorphic usize parameters, usize input, u32 output,
Rust ABI, no varargs, the compiler intrinsic body with its exact identity, unsafe
ctlz_nonzero versus safe ctpop, and no remaining reference generic arguments.
The selected effect table uses the same whitelist as extraction. Existing portable
profiles and the earlier usize runtime retain their original behavior.

`Runtime.lean` defines closed 64-bit semantics using the existing bit-vector
leading-zero operation and Lean's population count. Nonzero ctlz rejects zero
as undefined; it does not fabricate a successful zero count. Population count is
total. Eleven runtime theorems prove nonzero leading-zero behavior and logarithmic
value/bound, exact u32 population conversion, equality to the sum of the 64 set-bit
indicators, bounds and boundary values. Twelve extracted-source theorems establish
raw/guarded calls, total guarded behavior, population value, the original source
power-of-two predicate and high-bit examples. Every runtime/source definition and
theorem is audited: 31 dependency checks permit only propext/Classical.choice/
Quot.sound. Proof limits remain 200000 heartbeats and recursion depth 1000.

```sh
scripts/check-hasteboots-word64-intrinsics-guards
scripts/check-hasteboots-word64-intrinsics \
  --build-receipt build/hasteboots-extraction/inline-tools-build-RECEIPT/manifest.json \
  --backend /tmp/hasteboots-aeneas-m0
```

The gate freshly extracts the original count_ones/is_power_of_two bodies and
kernel-checks the complete generated module plus the runtime and proofs. It
rejects 23 unsupported cases: five incompatible targets/profiles; u32/u64 ctpop
and a u32 nonzero-ctlz function alias; fourteen corrupted ABI/safety/variadic/input/
output/intrinsic-identity/instantiation controls; and leftover reference generics.
Corruptions are explicit negative fault injections; accepted source/IR/terms are
untouched. Four guards check incomplete bodies, changed runtime calls/widths,
admissions, missing runtime bounds and source theorems.

The native arithmetic/word64 diagnostic still has 88 retained functions and no
residual drops/runtime queries or missing regular declarations. Its unresolved
inventory falls from seventeen to fifteen: ctpop and ctlz_nonzero now use the
checked definitions. The strict gate still rejects runtime/panic functions,
cold_path, pointers, default layout and deallocation. Exact inventories, paired
compiler hashes and regression evidence are recorded in `regression.json`.
The native probe includes the checked runtime when its kernel stage becomes
reachable; no complete native constructor is accepted at present.

These are model semantics and checked extraction interfaces, not a Rust/LLVM
compiler-correctness theorem. Caller validity for unsafe operations, native
pointer/heap behavior, NTT/SIMD/scheduler refinement, causal oracle/owner accounting,
BabyBear and the full 128-bit expected physical attacker-work security theorem
remain open. Logical bit counting does not impose a physical attacker-work charge.
No no-op cold_path/drop/deallocation admission or free work certificate is added.
