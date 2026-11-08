# Full-width enum to nonzero carriers

The original Alignment conversion targets `NonZero<usize>`, whose expanded
representation is two transparent wrappers around `usize is 1..=usize::MAX`.
The fixture uses the complete 64-variant alignment representation and the
actual stdlib `NonZeroU64`/`get` bodies. `baseline.json` records the preceding
profile's rejection. Fixed-width u64 exercises every bit, including `2^63`;
it does not substitute a target-width binding for the native usize type.

The new `-u64-range-patterns` flag requires monomorphic builtin shapes and Lean.
It preserves inclusive U64 bounds as a subtype; earlier profiles continue to
reject U64 patterns without the flag. Enum-to-range conversion reuses the
checked enum tag/discriminator validation and requires every stored tag within
the target bounds. Every transparent carrier in the target chain is checked
for closed references, matching target/size/alignment, a zero field offset and
no tag or alignment modifier. Cycles reject instead of using a depth limit.

Each enum case constructs its checked scalar literal and the original carrier
chain. The interpreter and pure translation both require an in-bounds literal;
Lean independently checks the subtype proof. Symbolic scalar-to-range casts
remain rejected. Outward carrier reads peel the same checked chain and return
the original scalar. Source operands are consumed once; the added logical
locals and matches are not native attacker-work charges. No runtime guard is
added to HasteBoots, and native caller safety still requires refinement proof.

```sh
scripts/check-hasteboots-enum-nonzero-guards
scripts/check-hasteboots-enum-nonzero \
  --build-receipt build/hasteboots-extraction/inline-tools-build-RECEIPT/manifest.json \
  --backend /tmp/hasteboots-aeneas-m0
```

Seven kernel theorems prove conversion totality for all 64 alignment variants,
exact bits, success soundness, range bounds, arbitrary nonzero getter behavior,
the composed source round trip and high-bit preservation. Four source functions,
the constrained carrier alias and generated reader complete thirteen dependency
audits. Eleven negative runs reject zero-bearing enums, nontransparent carriers,
symbolic construction, missing mode flags and six corrupted representation/range
tables. Accepted IR and generated terms remain untouched. Four guards reject
changed bounds/tags, admitted code and missing soundness proofs. The earlier
symbolic reverse-cast control still rejects, now with the precise literal-only
diagnostic rather than the earlier generic transmute error.

`probe-hasteboots-inline-constructor --cleanup-scope nonzero` expands the original
NonZero representation as well as layout and cleanup. It now generates a
complete native Lean module: 84 functions, no residual drops/runtime queries
and no missing regular declarations. The gate still rejects fourteen unresolved
axioms, including multiline declarations now included in its inventory: runtime
UB checks, panic formatting, pointer operations, default layout and deallocation.

A complete native proof also requires the large usize literal/target-width
binding and source/builtin layout compatibility. In particular the backend
Layout field uses the legacy `core.ptr.alignment.Alignment`, while the newly
exposed source accessors return `core.mem.alignment.Alignment`; that binding
has not been accepted. Pointer/heap/work refinement and full security remain
open. No backend or production Rust is modified, no proof limits are raised,
and only the three allowed Lean axioms are permitted in accepted artifacts.

The previous 108 dependency audits passed again, for 121 across the paired
profile. All 152 extraction guard tests passed. Full upstream extraction
completed 97 targets with the existing `dyn.rs` failure, and all 128 regenerated
files remain byte-identical. `regression.json` records the paired tools/patches,
exact audits, negative controls, native unresolved declarations and per-file
upstream comparison.
