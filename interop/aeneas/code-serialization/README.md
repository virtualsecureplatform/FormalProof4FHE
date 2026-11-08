# Retained native code serialization diagnostic

The wrapper calls the pinned `bincode::serde::encode_to_vec` with the native
`BlockReedSolomonCode<Goldilocks>` and `config::standard()`. These are the code
object and configuration used inside `Parameters::context_digest`. The wrapper
does not include the surrounding metadata tuple, modulus formatting, digest
updates or hash implementation. It does not replace the native derived Serde
implementations or supply a serialization callback.

`scripts/probe-hasteboots-code-serialization` runs a fresh accepted 107-audit
registry extraction first. It checks the native revision and cleanliness,
locked package identities, reviewed metadata frontend receipt, complete
x86_64 little-endian IR, and transparent bodies for the wrapper, Bincode call,
derived code serializer and derived Goldilocks serializer. Including only the
native carrier can leave the macro-generated serializer opaque; that is
rejected. The reachable native modules are explicitly included instead.

The generic mode uses ordinary constant lowering and retains 230 functions.
Its signatures contain no erased/body regions. The reviewed frontend rejects a
mixed mutually recursive Bincode/Serde declaration group before translation.
The monomorphic mode preserves raw constants and retains 65 functions; six
signatures contain erased regions. It inspects all function signatures through
the hash-consed type pool. Missing lifetimes stop extraction before symbolic
execution. Neither route drops clauses, reconstructs missing
lifetimes, edits IR or rewrites generated Lean terms.

Every diagnostic outcome, including unexpected translation success, is
`rejected-unproved` with a nonzero exit status. Recognizing a blocker does not
certify serialized bytes. Reviewed complete output, source-to-model byte
correspondence and kernel dependency audits are still required. The existing
metadata and model codec theorems do not prove actual Serde/Bincode encoding.

```
scripts/probe-hasteboots-code-serialization \
  --tools /tmp/hasteboots-aeneas-tools --backend /tmp/hasteboots-aeneas-m0 \
  --build-receipt /path/to/metadata-mono/build/manifest.json --mode generic
scripts/probe-hasteboots-code-serialization \
  --tools /tmp/hasteboots-aeneas-tools --backend /tmp/hasteboots-aeneas-m0 \
  --build-receipt /path/to/metadata-mono/build/manifest.json --mode mono
scripts/check-hasteboots-code-serialization-guards
```

The `partial` mode tests the pinned lifetime-preserving
`--monomorphize-mut` route, without the general clause-pruning options. The
native Serde attempt currently returns compiler exit code zero but sets
`has_errors=true` and reports mismatched trait clauses after transformation.
The diagnostic records the IR/log hashes and rejects it before Aeneas runs as
`partial-serde-trait-type-errors`. Neither compiler errors nor invalid type
substitutions are suppressed to work around the erased-lifetime failure.

The primitive `word` mode calls the actual Bincode integer encoder with standard
config. It requires a reviewed `discriminants` build receipt and uses ordinary
constant lowering. The gate checks transparent entry-point, integer-Encode,
varint and original PhantomData-clone bodies and all signature regions, after a
fresh 107-audit preflight:

```
scripts/probe-hasteboots-code-serialization \
  --tools /tmp/hasteboots-aeneas-tools --backend /tmp/hasteboots-aeneas-m0 \
  --build-receipt /path/to/discriminants/build/manifest.json --mode word
```

All 32 transparent functions translate. The native PhantomData clone is now
concrete and separately kernel-checked in the fifteen-audit discriminant gate.
The complete generated output still has three external axioms: std::io::Error,
std::time::SystemTime and std::time::SystemTimeError. The manifest records the generated file hash and
axiom names, and the diagnostic returns `rejected-unproved`/`external-axioms`.
This mode proves no byte theorem and supplies no serialization callback.

Add `--retain-error-types` to retain nine original error/time/pointer carriers.
The gate checks complete struct definitions and the exact original Nanoseconds
field pattern `u32 is 0..=999999999`, including its underlying type and both
bounds. It records remaining opaque carriers. The current frontend rejects
that pattern type during type analysis; the diagnostic returns
`rejected-unproved`/`nanoseconds-pattern-type`. Range predicates are not erased,
and retaining these carriers does not certify pointer identity or heap layout.

The newer `u32-ranges` receipt is also accepted in word mode. With
`--retain-time-types`, all six original time carriers are retained and their
exact bounded scalar fields translate. The full generated integer encoder
then has one external axiom, std::io::Error, and remains `rejected-unproved`.
The separate range gate kernel-checks these time carriers in thirty-nine
combined dependency audits; this does not certify full integer bytes.

```
scripts/probe-hasteboots-code-serialization \
  --tools /tmp/hasteboots-aeneas-tools --backend /tmp/hasteboots-aeneas-m0 \
  --build-receipt /path/to/u32-ranges/build/manifest.json \
  --mode word --retain-time-types
```

With that same receipt and `--retain-error-types`, extraction progresses to
the non-null pointer pattern and remains rejected as `nonnull-pointer-pattern`.
The diagnostic checks that the original `NotNull` predicate, shared pointer
kind and generic referent are intact. Remaining opaque carriers are recorded;
no pointer predicate or provenance obligation is erased.

The native pin remains `dff353006322693cab3dc6b654f82151f658f294`.
Manifests record the preflight receipt, frontend, wrapper, native files,
Cargo inputs and full IR hashes, commands, retained body IDs and signature
failures. Eleven guard tests cover body completeness, target/translation errors,
hash-consed signature references, missing lifetimes, primitive versus code
surfaces, exact nanosecond bounds and blocker classification.

The next compiler work must address generic recursive serializer interfaces or
preserve the lifetimes required by specialization. The separate discriminant
profile resolves the primitive encoder's cleanup-match bottom-value failure;
external axioms still prevent an accepted native byte theorem. Constructors, context
hashing, native owner iteration, heap refinement, physical attacker work and
the complete application security theorem remain open.
