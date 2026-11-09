module
import FormalProof4FHE.HasteBoots.NativeReservedVecConstruction
namespace FormalProof4FHETest.HasteBootsReservedVecConstructionSmoke
open FormalProof4FHE.HasteBoots
open NativeReservedVecConstruction
private def world : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty [.raw (.allocate 128 ⟨24,8⟩)]).getD NativeReferenceMachine.empty
private theorem reached : NativeReferenceMachine.Reachable world :=
  NativeReferenceMachine.run_reachable _ _ .empty [.raw (.allocate 128 ⟨24,8⟩)] (by decide)
private theorem headerAvailable : NativeVecBytePrefix.Available world ⟨128,some ⟨128,0⟩⟩ 24 := by
  intro lease member
  cases member
private theorem bufferAvailable : NativeVecBytePrefix.Available world (buffer world 64) 8 := by
  intro lease member
  cases member
private theorem space : ∀ block ∈ world.pointers.heap.memory.blocks,
    NativeByteMemory.Disjoint (NativeByteMemory.freshBlock world.pointers.heap.memory 64 ⟨8,1⟩) block := by
  intro block member
  have same : block = NativeByteMemory.freshBlock NativeByteMemory.empty 128 ⟨24,8⟩ := List.mem_singleton.mp member
  subst block
  decide
example : ∃ next, ∃ ready : NativeReservedVecStorage.Ready next 8 (buffer world 64) ⟨128,some ⟨128,0⟩⟩,
    reserve world 0 64 8 = some next ∧ NativeReferenceMachine.Reachable next ∧
    NativeResidentVec.OwnsBuffer ready.descriptor ∧
    NativeVecBytePrefix.Available next ready.descriptor.buffer ready.descriptor.capacity.val ∧
    next.leases = ready.descriptor.lease :: world.leases ∧
    next.references = ⟨world.nextTag⟩ :: world.references ∧ ready.descriptor.reference = ⟨world.nextTag⟩ :=
  reserve_complete world 0 ⟨128,some ⟨128,0⟩⟩ 64 8 reached (by decide) (by decide) headerAvailable
    (by decide) (by decide) (by decide) (by decide) space bufferAvailable (by decide)
private def reserved : NativeReferenceMachine.State := (reserve world 0 64 8).getD NativeReferenceMachine.empty
example : NativePointerByteMemory.load reserved.pointers.heap ⟨136,some ⟨128,0⟩⟩ = some ⟨64,some ⟨64,1⟩⟩ ∧
    NativeWord64Memory.load reserved.pointers.heap.memory ⟨128,some ⟨128,0⟩⟩ = some 8 ∧
    NativeWord64Memory.load reserved.pointers.heap.memory ⟨144,some ⟨128,0⟩⟩ = some 0 := by decide
example : NativeByteRange.loadRange reserved.pointers.heap.memory ⟨64,some ⟨64,1⟩⟩ ⟨8,1⟩ = none := by decide
example : (NativePointerByteMemory.deallocate reserved.pointers.heap ⟨64,some ⟨64,1⟩⟩ ⟨8,1⟩).isSome = true := by decide
example : NativePointerByteMemory.deallocate reserved.pointers.heap ⟨64,none⟩ ⟨8,1⟩ = none := by decide
example : NativePointerByteMemory.deallocate reserved.pointers.heap ⟨64,some ⟨64,1⟩⟩ ⟨4,1⟩ = none := by decide
example : reserve world 0 128 8 = none := by decide
example : reserve world 0 64 0 = none := by decide
example : reserve reserved 1 256 8 = none := by decide
example : reserve reserved 2 256 8 = none := by decide
example : NativePointerByteMemory.deallocate reserved.pointers.heap ⟨64,some ⟨64,0⟩⟩ ⟨8,1⟩ = none := by decide
private def erased : NativePointerByteMemory.State :=
  (NativePointerByteMemory.writeBytes reserved.pointers.heap ⟨128,some ⟨128,0⟩⟩ 8
    (NativeReservedVecStorage.bytes 8 ⟨64,some ⟨64,1⟩⟩)).getD NativePointerByteMemory.empty
example : NativePointerByteMemory.load erased ⟨136,some ⟨128,0⟩⟩ = some ⟨64,none⟩ := by decide
example : ∃ next, NativePointerByteMemory.store erased ⟨136,some ⟨128,0⟩⟩ ⟨64,some ⟨64,1⟩⟩ = some next ∧
    next.memory = erased.memory ∧ NativePointerByteMemory.load next ⟨136,some ⟨128,0⟩⟩ = some ⟨64,some ⟨64,1⟩⟩ ∧
    next.shadow = NativePointerShadow.replace erased.shadow ⟨128,0⟩ 136 (List.replicate 8 (some ⟨64,1⟩)) :=
  NativePointerRestore.restore erased ⟨136,some ⟨128,0⟩⟩ ⟨64,some ⟨64,1⟩⟩ ⟨128,0⟩ rfl (by decide)
end FormalProof4FHETest.HasteBootsReservedVecConstructionSmoke
