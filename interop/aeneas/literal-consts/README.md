# Evaluated plain integer constants

The opt-in `-literal-const-initializers` profile requires the checked monomorphic,
little-endian word64 target. Charon's `--consts values` retains rustc's evaluated
integer values in global declarations. The older Aeneas pipeline expects an
initializer-function ID and otherwise raises `option is None`.

The new prepass preserves each supported literal by building a typed, zero-argument
initializer containing that exact literal. It allocates fresh function IDs,
retains the original global identity/metadata/type and registers the initializer
before its global declaration. Existing initializer calls remain unchanged.
No source function body or missing/opaque value is replaced with a guessed result.

Supported values are in-range signed/unsigned integers in plain, monomorphic,
top-level named constants. The declared type, value type and literal integer
kind must agree. Static/thread-local/anonymous storage, generic or associated
constants and noninteger values are outside this profile. Global address identity,
native storage and a compiler-correctness proof are not supplied.

The fixture uses 31, a nontrivial u64 mask, u8 zero, -17 and the maximum u128,
so the implementation is checked independently of the word-layout witness 8.
Six source theorems and all six source definitions are audited. Fifteen negative
controls cover missing profile/target checks, unsupported global kinds/generics,
type/kind mismatches, signedness/range failures and the old unsupported path.
Four guard tests reject lost source evidence, changed values and admissions.

```sh
scripts/check-hasteboots-literal-consts-guards
scripts/check-hasteboots-literal-consts \
  --build-receipt build/hasteboots-extraction/inline-tools-build-RECEIPT/manifest.json \
  --backend /tmp/hasteboots-aeneas-m0
```

The Lean backend and Charon sources are unchanged. The default frontend profiles
retain their existing behavior with the flag absent. The generated artifact is
unedited; checking assembles its declarations with the pinned standard prelude.
This proves extracted literal-value properties, not verified compilation, native
memory behavior or the final HasteBoots security theorem.
