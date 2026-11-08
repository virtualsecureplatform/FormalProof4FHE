module
public import FormalProof4FHE.HasteBoots.NativeVariantValues
@[expose] public section

-- Logical source schema; physical niche decoding and body translation remain open.
namespace HasteBootsRawVecOption
open FormalProof4FHE.HasteBoots
open NativeVariantValues
def alignmentDiscriminants : List NativeWord64Memory.Word := [⟨1, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩, ⟨8, by decide⟩, ⟨16, by decide⟩, ⟨32, by decide⟩, ⟨64, by decide⟩, ⟨128, by decide⟩, ⟨256, by decide⟩, ⟨512, by decide⟩, ⟨1024, by decide⟩, ⟨2048, by decide⟩, ⟨4096, by decide⟩, ⟨8192, by decide⟩, ⟨16384, by decide⟩, ⟨32768, by decide⟩, ⟨65536, by decide⟩, ⟨131072, by decide⟩, ⟨262144, by decide⟩, ⟨524288, by decide⟩, ⟨1048576, by decide⟩, ⟨2097152, by decide⟩, ⟨4194304, by decide⟩, ⟨8388608, by decide⟩, ⟨16777216, by decide⟩, ⟨33554432, by decide⟩, ⟨67108864, by decide⟩, ⟨134217728, by decide⟩, ⟨268435456, by decide⟩, ⟨536870912, by decide⟩, ⟨1073741824, by decide⟩, ⟨2147483648, by decide⟩, ⟨4294967296, by decide⟩, ⟨8589934592, by decide⟩, ⟨17179869184, by decide⟩, ⟨34359738368, by decide⟩, ⟨68719476736, by decide⟩, ⟨137438953472, by decide⟩, ⟨274877906944, by decide⟩, ⟨549755813888, by decide⟩, ⟨1099511627776, by decide⟩, ⟨2199023255552, by decide⟩, ⟨4398046511104, by decide⟩, ⟨8796093022208, by decide⟩, ⟨17592186044416, by decide⟩, ⟨35184372088832, by decide⟩, ⟨70368744177664, by decide⟩, ⟨140737488355328, by decide⟩, ⟨281474976710656, by decide⟩, ⟨562949953421312, by decide⟩, ⟨1125899906842624, by decide⟩, ⟨2251799813685248, by decide⟩, ⟨4503599627370496, by decide⟩, ⟨9007199254740992, by decide⟩, ⟨18014398509481984, by decide⟩, ⟨36028797018963968, by decide⟩, ⟨72057594037927936, by decide⟩, ⟨144115188075855872, by decide⟩, ⟨288230376151711744, by decide⟩, ⟨576460752303423488, by decide⟩, ⟨1152921504606846976, by decide⟩, ⟨2305843009213693952, by decide⟩, ⟨4611686018427387904, by decide⟩, ⟨9223372036854775808, by decide⟩]
def schema : Schema := ⟨10, [
  ⟨0, .scalar .unit⟩,
  ⟨1, (.pair (.pair (.record 7 (.pair .nonnull (.scalar .unit))) (.pair (.record 9 (.pair (.scalar .usize) (.pair (.record 11 (.pair (.enumeration 12 alignmentDiscriminants) (.scalar .unit))) (.scalar .unit)))) (.scalar .unit))) (.scalar .unit))⟩]⟩
end HasteBootsRawVecOption
