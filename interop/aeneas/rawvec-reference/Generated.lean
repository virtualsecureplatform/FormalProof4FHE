module
public import FormalProof4FHE.HasteBoots.NativeRecordLLBC
@[expose] public section

-- Original Vec capacity body; constrained carrier correspondence remains open.
namespace HasteBootsRawVecReference
open FormalProof4FHE.HasteBoots.NativeRecordLLBC
-- Original declaration SHA256 5cd9a4659340a0b1f3277004b02c59b5e9dabde75bf33f8673aec89522f7e2cb
def capacity : Function := ⟨"alloc::vec::capacity", .transparent, [(.scalar .usize), (.scalar (.reference false)), (.scalar .usize)], 1, (.live 0 (.switchUsize (.usize ⟨1, by decide⟩) ⟨0, by decide⟩ .done (.live 2 (.assign 2 (.rawVecField .capacity (.copy 1 []) true) (.assign 0 (.use (.copy 2 []) false .word) (.dead 2 (.dead 1 .ret))))) (.assign 0 (.use (.usize ⟨18446744073709551615, by decide⟩) true .byte) (.dead 1 .ret))))⟩
end HasteBootsRawVecReference
