module
public import FormalProof4FHE.HasteBoots.NativeRecordLLBC
@[expose] public section

-- Original finite allocator caller; the external leaf remains a logical specification.
namespace HasteBootsGlobalDeallocation
open FormalProof4FHE.HasteBoots.NativeRecordLLBC

def alignmentDiscriminants : List FormalProof4FHE.HasteBoots.NativeWord64Memory.Word := [⟨1, by decide⟩, ⟨2, by decide⟩, ⟨4, by decide⟩, ⟨8, by decide⟩, ⟨16, by decide⟩, ⟨32, by decide⟩, ⟨64, by decide⟩, ⟨128, by decide⟩, ⟨256, by decide⟩, ⟨512, by decide⟩, ⟨1024, by decide⟩, ⟨2048, by decide⟩, ⟨4096, by decide⟩, ⟨8192, by decide⟩, ⟨16384, by decide⟩, ⟨32768, by decide⟩, ⟨65536, by decide⟩, ⟨131072, by decide⟩, ⟨262144, by decide⟩, ⟨524288, by decide⟩, ⟨1048576, by decide⟩, ⟨2097152, by decide⟩, ⟨4194304, by decide⟩, ⟨8388608, by decide⟩, ⟨16777216, by decide⟩, ⟨33554432, by decide⟩, ⟨67108864, by decide⟩, ⟨134217728, by decide⟩, ⟨268435456, by decide⟩, ⟨536870912, by decide⟩, ⟨1073741824, by decide⟩, ⟨2147483648, by decide⟩, ⟨4294967296, by decide⟩, ⟨8589934592, by decide⟩, ⟨17179869184, by decide⟩, ⟨34359738368, by decide⟩, ⟨68719476736, by decide⟩, ⟨137438953472, by decide⟩, ⟨274877906944, by decide⟩, ⟨549755813888, by decide⟩, ⟨1099511627776, by decide⟩, ⟨2199023255552, by decide⟩, ⟨4398046511104, by decide⟩, ⟨8796093022208, by decide⟩, ⟨17592186044416, by decide⟩, ⟨35184372088832, by decide⟩, ⟨70368744177664, by decide⟩, ⟨140737488355328, by decide⟩, ⟨281474976710656, by decide⟩, ⟨562949953421312, by decide⟩, ⟨1125899906842624, by decide⟩, ⟨2251799813685248, by decide⟩, ⟨4503599627370496, by decide⟩, ⟨9007199254740992, by decide⟩, ⟨18014398509481984, by decide⟩, ⟨36028797018963968, by decide⟩, ⟨72057594037927936, by decide⟩, ⟨144115188075855872, by decide⟩, ⟨288230376151711744, by decide⟩, ⟨576460752303423488, by decide⟩, ⟨1152921504606846976, by decide⟩, ⟨2305843009213693952, by decide⟩, ⟨4611686018427387904, by decide⟩, ⟨9223372036854775808, by decide⟩]

-- Original declaration SHA256 bb821f3c734f0cb0041df9c65575940f0a2ad707cf3d82dc5354eb26a2b41ad5
def f1 : Function :=
  ⟨"alloc::alloc::deallocate", .transparent, [(.scalar .unit), (.scalar (.reference false)), (.record 0 (.pair .nonnull (.scalar .unit))), (.record 1 (.pair (.scalar .usize) (.pair (.record 3 (.pair (.enumeration 4 alignmentDiscriminants) (.scalar .unit))) (.scalar .unit)))), (.scalar .usize), (.record 3 (.pair (.enumeration 4 alignmentDiscriminants) (.scalar .unit)))], 3, (.live 0 (.assign 0 .unit (.live 4 (.assign 4 (.use (.copy 3 [(.unwrap 1), .left]) true .byte) (.switchUsize (.copy 4 []) ⟨0, by decide⟩ .done (.live 5 (.assign 5 (.use (.copy 3 [(.unwrap 1), .right, .left]) true .byte) (.call "alloc::alloc::__rust_dealloc" .externalBody [(.scalar .unit), (.record 0 (.pair .nonnull (.scalar .unit))), (.scalar .usize), (.record 3 (.pair (.enumeration 4 alignmentDiscriminants) (.scalar .unit)))] 3 0 [(.move 2 []), (.move 4 []), (.move 5 [])] (.deallocate (.move 1 [(.unwrap 0), .left]) (.move 2 []) (.move 3 [(.unwrap 3), .left]) 4) (.dead 3 (.dead 2 (.dead 1 .abort))) (.dead 5 (.dead 4 (.dead 3 (.dead 2 (.dead 1 .ret)))))))) (.dead 4 (.dead 3 (.dead 2 (.dead 1 .ret)))))))))⟩

-- Original declaration SHA256 9f7a895aa460e190f6d5829e69aff2b0d9562a178118c322bfcb02a954f6a368
def f3 : Function :=
  ⟨"alloc::alloc::__rust_dealloc", .externalBody, [(.scalar .unit), (.record 0 (.pair .nonnull (.scalar .unit))), (.scalar .usize), (.record 3 (.pair (.enumeration 4 alignmentDiscriminants) (.scalar .unit)))], 3, (.deallocate (.move 1 [(.unwrap 0), .left]) (.move 2 []) (.move 3 [(.unwrap 3), .left]) 4)⟩

end HasteBootsGlobalDeallocation
