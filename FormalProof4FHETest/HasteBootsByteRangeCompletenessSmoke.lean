module
import FormalProof4FHE.HasteBoots.NativeByteRangeCompleteness
namespace FormalProof4FHETest.HasteBootsByteRangeCompletenessSmoke
open FormalProof4FHE.HasteBoots
open NativeByteRangeCompleteness
private def pointer : NativePointerStorage.Pointer := ⟨64,some ⟨64,0⟩⟩
private def memory : NativeByteMemory.State :=
  ⟨1,[⟨⟨64,0⟩,64,⟨8,1⟩,[some 10,some 20,some 30,some 40,none,none,none,none]⟩]⟩
private theorem valid : NativeByteMemory.WellFormed memory := by
  simp only [NativeByteMemory.WellFormed,memory,List.mem_singleton,forall_eq,
    List.pairwise_singleton,and_true,NativeByteMemory.Block.Valid]
  decide
example : ∃ shifted, NativeByteRange.pointerAt pointer 1 = some shifted ∧
    NativeByteRange.loadRange memory shifted ⟨2,1⟩ = some [20,30] :=
  loadRange_subrange memory valid pointer 4 1 2 [10,20,30,40] (by decide) (by decide)
example : ∃ shifted, NativeByteRange.pointerAt pointer 4 = some shifted ∧
    NativeByteRange.loadRange memory shifted ⟨0,1⟩ = some [] :=
  loadRange_subrange memory valid pointer 4 4 0 [10,20,30,40] (by decide) (by decide)
example : NativeByteRange.loadRange memory ⟨68,some ⟨64,0⟩⟩ ⟨1,1⟩ = none := by decide
example : NativeByteRange.loadRange memory ⟨pointer.address,none⟩ ⟨4,1⟩ = none := by decide
example : ∃ shifted, NativeByteRange.pointerAt ⟨1,none⟩ 0 = some shifted ∧
    NativeByteRange.loadRange NativeByteMemory.empty shifted ⟨0,1⟩ = some [] :=
  loadRange_subrange _ NativeByteMemory.empty_wellFormed ⟨1,none⟩ 0 0 0 [] (by decide) (by decide)
private def operations : List NativeReferenceMachine.Op :=
    [.raw (.allocate 64 ⟨8,1⟩),.raw (.writeBytes 0 1 [10,20]),.raw (.allocate 128 ⟨24,8⟩),
     .raw (.writeBytes 0 8 (NativeWord64Memory.encode 8)),.raw (.withAddress 0 136),.raw (.store 0 2),
     .raw (.withAddress 1 144),.raw (.writeBytes 0 8 (NativeWord64Memory.encode 2)),.borrow 2 .exclusive ⟨24,8⟩]
private def ready : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty operations).getD NativeReferenceMachine.empty
private theorem readyMemory : NativeByteMemory.WellFormed ready.pointers.heap.memory :=
  (NativeReferenceMachine.run_wellFormed operations ready (by decide)).1.1
private def descriptor : NativeResidentVec.Descriptor ready 0 where
  reference := ⟨0⟩
  lease := ⟨0,none,⟨128,some ⟨128,1⟩⟩,⟨24,8⟩,.exclusive⟩
  resident := by decide
  registered := by decide
  baseResident := by decide
  exclusive := rfl
  extent := rfl
  capacitySlot := ⟨128,some ⟨128,1⟩⟩
  pointerSlot := ⟨136,some ⟨128,1⟩⟩
  lengthSlot := ⟨144,some ⟨128,1⟩⟩
  capacityAt := by decide
  pointerAt := by decide
  lengthAt := by decide
  capacity := 8
  length := 2
  buffer := pointer
  capacityStored := by decide
  pointerStored := by decide
  lengthStored := by decide
  capacityBound := by decide
  lengthBound := by decide
  nonnull := by decide
private theorem initialized : NativeResidentVec.InitializedElements descriptor := ⟨[10,20],by decide⟩
example : ∃ shifted byte, NativeByteRange.pointerAt descriptor.buffer 1 = some shifted ∧
    NativeByteRange.loadRange ready.pointers.heap.memory shifted ⟨1,1⟩ = some [byte] :=
  initialized.byte readyMemory 1 (by decide)
example : ∃ shifted bytes, NativeByteRange.pointerAt descriptor.buffer 2 = some shifted ∧
    NativeByteRange.loadRange ready.pointers.heap.memory shifted ⟨0,1⟩ = some bytes :=
  initialized.subrange readyMemory 2 0 (by decide)
example : NativeByteRange.loadRange ready.pointers.heap.memory ⟨66,some ⟨64,0⟩⟩ ⟨1,1⟩ = none := by decide
end FormalProof4FHETest.HasteBootsByteRangeCompletenessSmoke
