# Retained Vec capacity arithmetic

`fixture.rs` calls the original `Vec::<u8>::with_capacity`. The gate retains 21
complete source function declarations, 31 types and globals in `Retained.json`.
`Generated.lean` emits nine isolated arithmetic assignments with their original
operators, destination/local indices, operand move/copy modes, primitive types
and statement hashes. The retained whole functions include their branches and
error helpers; this profile interprets only the listed scalar assignments.

The scalar contexts for checked multiplication include its three actual locals;
all unused locals are dead. Four theorems prove the original assignment for every
word pair and incoming modeled world, its byte-size-one specialization, consumed
move operands and world preservation. Four source regressions cover zero and
maximum unsigned capacity, an overflowing product and unavailable moved operands.
The byte multiplication result does not establish the later allocation bound.

The shared interpreter uses distinct Boolean types and values, explicit overflow
flags, wrapping operations, precondition-checked subtraction and dynamic Boolean
branching. Existing heap, incoming-reference and deallocation-budget proofs are
extended to these cases. Seventeen model regressions and 28 core declaration
audits guard these additions. All 333 audited dependencies use only the permitted
standard Lean dependencies; 21 negative controls reject changes to extraction
policy, widths, modes, locals, literals, owners and assignment metadata.

Run with the coupled tool receipt:

```bash
scripts/check-hasteboots-vec-capacity-arithmetic \
  --build-receipt build/hasteboots-extraction/inline-tools-build-b6esls36/manifest.json
```

The gate freshly extracts, compares generated code and retained declarations,
checks rejecting controls, compiles proofs and smoke examples with warnings as
errors, audits dependencies and records input/source/log hashes in an ignored
build manifest. `regression.json` records the checked milestone.

Whole-constructor control flow and calls, overflow/error and abort handling,
allocator implementation, native compiler/ABI/lifetime refinement, physical work
and the final HasteBoots security theorem remain open.
