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

The native pin remains `dff353006322693cab3dc6b654f82151f658f294`.
Manifests record the preflight receipt, frontend, wrapper, native files,
Cargo inputs and full IR hashes, commands, retained body IDs and signature
failures. Seven guard tests cover body completeness, target/translation errors,
hash-consed signature references, missing lifetimes and blocker classification.

The next compiler work must address generic recursive serializer interfaces or
preserve the lifetimes required by specialization. Primitive integer encoder
experiments also encounter a separate bottom-value failure at Result handling;
they have not produced an accepted native byte theorem. Constructors, context
hashing, native owner iteration, heap refinement, physical attacker work and
the complete application security theorem remain open.
