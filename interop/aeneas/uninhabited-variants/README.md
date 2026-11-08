# Structurally empty alternatives in ordinary-sysroot extraction

The ordinary native constructor failed while projecting Err from the original
Result<Infallible, E> residual. Rust can omit a general variant split here because
Ok contains an empty type. The historical baseline records that rejection.

In monomorphic Lean mode, non-branching expansion now permits a unique remaining
variant only when every alternative is structurally empty. Empty enums establish
the base case; by-value tuple/struct/enum fields propagate emptiness. Opaque types,
references, arrays and recursion cycles remain unknown. Neither a zero size nor
rustc's uninhabited layout flag is treated as a logical proof. Other profiles and
ordinary branching remain unchanged.

All original constructors and empty types remain in the generated module. The
single remaining case is emitted as an actual match, so Lean independently checks
coverage. It does not become a pattern let that a later simplifier would extend
with an invented fallback value. No constructor/tag table is deleted and no axiom
or default inhabitant is added.

The fixture covers custom direct/nested empty alternatives and the original
stdlib residual conversion for an error wrapper holding &'static str, the same
payload shape as the native pcs::matrix_weighted::Error. That shape is checked in
IR, including the Static region. Six theorems prove constructor cases and exact
behavior for every valid input. All source definitions, exported types/readers,
the existing closed Infallible type, aliases and theorems pass 25 dependency
audits. Only propext/Classical.choice/Quot.sound are allowed; proof limits are
unchanged. This is a model/source-interface result, not Rust caller/heap safety
or an identity theorem between the fixture and native wrapper types.

```sh
scripts/check-hasteboots-uninhabited-variants-guards
scripts/check-hasteboots-uninhabited-variants \
  --build-receipt build/hasteboots-extraction/inline-tools-build-RECEIPT/manifest.json \
  --backend /tmp/hasteboots-aeneas-m0
```

Nine cases reject: five unsupported targets/profiles; opaque, inhabited and
cyclic replacements for the empty witness while retaining its layout hints;
and a separate source case with two residual instantiations that exposes a
pre-existing generated-name collision. The latter remains unsupported. Modified
IR is used only for explicit negative fault injections. Four guards reject lost
constructors, changed static error payloads, admitted code and missing all-input
proofs. Accepted source/IR/generated computational terms are not rewritten.

The ordinary native probe still retains 52 functions with no residual drops,
runtime queries or missing regular references. It passes the earlier enum
expansion and now fails when projecting the still-opaque Unique<u8> pointer
carrier. It does not produce an accepted complete module. Next work is original
pointer representation/operations, the naming collision and layout/heap/runtime
obligations. Compiler/caller/heap and NTT/SIMD/scheduler refinement, causal oracle/
owner accounting, BabyBear and the full 128-bit expected physical attacker-work
security theorem remain open. Logical case elimination provides no work floor.
