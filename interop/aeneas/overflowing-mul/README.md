# Original overflowing multiplication

Expanding native checked_mul/overflowing_mul exposed an unsupported MulChecked
operation in the original stdlib body. `baseline.json` records the isolated and
native failures using the previous frozen compiler pair. The arithmetic cleanup
scope also retains the source word constants, is_power_of_two/count_ones,
checked_add/checked_mul, unlikely and their actual dependencies.

The symbolic interpreter now types MulChecked as `(integer, bool)`, requiring
identical operand types. Lean extraction uses the existing closed
`UScalar.overflowing_mul` or `IScalar.overflowing_mul`. The original source methods
and casts are retained; no compiler assumption, backend edit or generated-term
rewrite was added. SubChecked remains unsupported.

Eight kernel theorems prove equivalence for every pair of signed/unsigned 64-bit
inputs, the unsigned mathematical wraparound/overflow specification, and boundary
cases at unsigned maximum, 2^63, signed minimum negation, negative signed overflow
and the safe signed minimum. Four original generated definitions and those eight
theorems give twelve dependency audits. The complete portable comparison uses the
existing assumed usize/isize methods and passes two separate dependency audits;
this comparison is not an original-body refinement. Only propext/Classical.choice/
Quot.sound are permitted. Existing proof limits remain unchanged.

```sh
scripts/check-hasteboots-overflowing-mul-guards
scripts/check-hasteboots-overflowing-mul \
  --build-receipt build/hasteboots-extraction/inline-tools-build-RECEIPT/manifest.json \
  --backend /tmp/hasteboots-aeneas-m0
scripts/probe-hasteboots-inline-constructor \
  --build-receipt build/hasteboots-extraction/inline-tools-build-RECEIPT/manifest.json \
  --backend /tmp/hasteboots-aeneas-m0 --cleanup-scope arithmetic --target-word64
```

The gate requires complete original source bodies and both actual MulChecked
operations, checks full generated snapshots, and rejects missing monomorphic mode,
32-bit, big-endian, absent and multiple target metadata. The target changes are
explicit negative fault injections, not accepted source transformations. Four
guards reject lost bodies/overflow flags, altered arithmetic/widths, admissions
and incomplete universal or boundary proofs.

The expanded native probe now generates a complete module with 88 retained
functions and no residual drops/runtime queries or missing regular references.
It still rejects seventeen unresolved declarations, inventoried exactly in
`regression.json`: ctpop, ctlz_nonzero, cold_path, runtime/panic functions,
pointer operations, default layout and deallocation. The earlier word64 scope
had twenty-two opaque declarations. This reduction closes source arithmetic
bodies, not the native constructor. Original checked methods still depend on
cold_path; no no-op or success callback is substituted.

Compiler correctness, unsafe-call validity, pointer/heap semantics, native
NTT/SIMD/scheduler refinement, oracle/owner accounting, BabyBear and the complete
128-bit expected physical attacker-work security theorem remain open. Logical
proof computation is not a physical work charge.
