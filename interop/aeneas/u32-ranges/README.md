# Read-only bounded U32 values and original time carriers

The isolated `u32-ranges` frontend profile extends `discriminants` with a
refined representation for closed, nonempty, inclusive U32 scalar ranges.
The underlying type, both literal bound types, bound order and U32 maximum
are checked. The pure AST retains both bounds; Lean output uses
`{ value : Std.U32 // lower ≤ value.val ∧ value.val ≤ upper }`.
No range predicate is erased, and no constructor proof is assumed.

Borrow/region analysis treats this checked scalar leaf as containing no
references. Forward/backward type translation retains its range. Ordinary
scalar casts and arithmetic do not gain a conversion into this subtype.
Unsupported scalar widths, disjunctions and non-null pointer patterns still
reject. Extraction of this representation is restricted to Lean. Original
LLBC, source names and spans remain unchanged; no backend or native HasteBoots
file is modified.

`fixture.rs` exercises the actual pattern types `u32 is 0..=999999999` and
`u32 is 7..=19` in stored fields, selection and direct input/output. Six kernel
theorems prove exact value results and both range predicates. The distinct
nonzero lower bound tests preservation of the lower predicate as well.

`time.rs` retains the original standard-library Nanoseconds, Duration,
Timespec, Unix SystemTime, public SystemTime and SystemTimeError carriers.
Five theorems establish exact storage preservation and native nanosecond
bounds. These are value/storage statements, not clock, syscall or heap-layout
proofs. Every field, including duration seconds and signed time seconds,
remains in the reviewed generated output.

The gate first reproduces fifteen trait/effect/cleanup/PhantomData audits on
this frontend. It checks thirty-nine combined dependency audits: fifteen
previous checks, ten scalar-range checks and fourteen native time-carrier
checks. Both new complete outputs are compared with exact reviewed snapshots.
Only propext, Classical.choice and Quot.sound are permitted, with unchanged
200000/1000 proof limits.

Four valid-Rust negative fixtures cover signed ranges, disjunctions, a checked
transmute constructor and non-null pointers. The transmute case currently
exits zero but emits an external axiom; the gate rejects that output. Nonzero
exits, error logs, admissions and truncated output all remain rejections.

```
scripts/build-hasteboots-static-frontend --profile u32-ranges \
  --source /tmp/hasteboots-aeneas-u32-ranges \
  --opam /tmp/hasteboots-ocaml-bootstrap/opam \
  --opam-root /tmp/hasteboots-ocaml-bootstrap/root --switch hasteboots-static
scripts/probe-hasteboots-u32-ranges \
  --tools /tmp/hasteboots-aeneas-tools --backend /tmp/hasteboots-aeneas-m0 \
  --build-receipt /path/printed/by/builder/manifest.json
scripts/check-hasteboots-u32-range-guards
```

The isolated Aeneas pin is `15b968482b0dcd7aae45020b6d1bca39b5024af5`;
the clean Charon library pin is `ef3748c1a92c6acc402f978770193d34adc0fe6e`.
Formatting, clean patch application and upstream traits/arrays regeneration
are required checks. Tool, source, package, executable and backend pins are
verified through the linked preflight; manifests hash inputs, complete IR,
generated output, proofs, checked assembly and logs.

With this receipt, the separate native integer diagnostic can retain all six
time carriers using `--mode word --retain-time-types`. Its sole remaining
external type axiom is std::io::Error, so the diagnostic still returns nonzero
and `rejected-unproved`. Retaining all error carriers instead reaches the
unsupported non-null pointer pattern. Native byte/Serde correspondence,
pointer provenance and heap refinement, physical attacker work and full
application security remain open.
