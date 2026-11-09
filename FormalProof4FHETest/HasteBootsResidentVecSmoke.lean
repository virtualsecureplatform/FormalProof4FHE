module
import FormalProof4FHE.HasteBoots.NativeResidentVec
namespace FormalProof4FHETest.HasteBootsResidentVecSmoke
open FormalProof4FHE.HasteBoots
open NativeResidentVec
private def header : NativePointerStorage.Pointer := ⟨128,some ⟨128,1⟩⟩
private def buffer : NativePointerStorage.Pointer := ⟨64,some ⟨64,0⟩⟩
private def ready : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate 64 ⟨8,1⟩),.raw (.allocate 128 ⟨24,8⟩),
     .raw (.writeBytes 0 8 (NativeWord64Memory.encode 8)),.raw (.withAddress 0 136),
     .raw (.store 0 2),.raw (.withAddress 1 144),
     .raw (.writeBytes 0 8 (NativeWord64Memory.encode 0)),.borrow 2 .exclusive ⟨24,8⟩]).getD NativeReferenceMachine.empty
private def descriptor : Descriptor ready 0 where
  reference := ⟨0⟩
  lease := ⟨0,none,header,⟨24,8⟩,.exclusive⟩
  resident := by decide
  registered := by decide
  baseResident := by decide
  exclusive := rfl
  extent := rfl
  capacitySlot := header
  pointerSlot := ⟨136,some ⟨128,1⟩⟩
  lengthSlot := ⟨144,some ⟨128,1⟩⟩
  capacityAt := by decide
  pointerAt := by decide
  lengthAt := by decide
  capacity := 8
  length := 0
  buffer := buffer
  capacityStored := by decide
  pointerStored := by decide
  lengthStored := by decide
  capacityBound := by decide
  lengthBound := by decide
  nonnull := by decide
private theorem owns : OwnsBuffer descriptor := by
  right
  refine ⟨by decide,⟨⟨64,0⟩,64,⟨8,1⟩,List.replicate 8 none⟩,by decide,rfl,rfl⟩
example : NativeByteRange.loadRange ready.pointers.heap.memory buffer ⟨8,1⟩ = none := by decide
example : InitializedElements descriptor := ⟨[],by decide⟩
example : ∃ next, NativeRawVecFields.pointerAccess ready 0 = .value descriptor.buffer next :=
  descriptor.pointer_access_complete (by decide)
example (next : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (read : NativeRawVecFields.pointerAccess ready 0 = .value pointer next) : pointer = buffer :=
  descriptor.pointer_access next pointer read
example (next : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word)
    (read : NativeRawVecFields.capacityAccess ready 0 = .value capacity next) : capacity = 8 :=
  descriptor.capacity_access next capacity read
example (next : NativeReferenceMachine.State) (length : NativeWord64Memory.Word)
    (read : NativeVecReference.lengthAccess ready 0 = .value length next) : length = 0 :=
  descriptor.length_access next length read
example : ∃ after, NativePointerByteMemory.deallocate ready.pointers.heap buffer ⟨8,1⟩ = some after ∧
    NativeHeapRelease.count after + 1 = NativeHeapRelease.count ready.pointers.heap ∧
    after.memory.blocks.Sublist ready.pointers.heap.memory.blocks ∧
    after.memory.nextGeneration = ready.pointers.heap.memory.nextGeneration :=
  owns.deallocation_effect (by decide)

-- Equal address bits without the stored origin cannot supply the buffer value.
example : NativePointerByteMemory.load ready.pointers.heap descriptor.pointerSlot ≠ some ⟨64,none⟩ := by decide
-- The physical allocator requires the exact reserved capacity.
example : NativePointerByteMemory.deallocate ready.pointers.heap buffer ⟨4,1⟩ = none := by decide
example : NativePointerByteMemory.deallocate ready.pointers.heap ⟨64,none⟩ ⟨8,1⟩ = none := by decide

private def emptyReady : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate 128 ⟨24,8⟩),.raw (.writeBytes 0 8 (NativeWord64Memory.encode 0)),
     .raw (.fromAddress 1),.raw (.withAddress 1 136),.raw (.store 0 1),
     .raw (.withAddress 2 144),.raw (.writeBytes 0 8 (NativeWord64Memory.encode 0)),
     .borrow 3 .exclusive ⟨24,8⟩]).getD NativeReferenceMachine.empty
private def emptyDescriptor : Descriptor emptyReady 0 where
  reference := ⟨0⟩
  lease := ⟨0,none,⟨128,some ⟨128,0⟩⟩,⟨24,8⟩,.exclusive⟩
  resident := by decide
  registered := by decide
  baseResident := by decide
  exclusive := rfl
  extent := rfl
  capacitySlot := ⟨128,some ⟨128,0⟩⟩
  pointerSlot := ⟨136,some ⟨128,0⟩⟩
  lengthSlot := ⟨144,some ⟨128,0⟩⟩
  capacityAt := by decide
  pointerAt := by decide
  lengthAt := by decide
  capacity := 0
  length := 0
  buffer := ⟨1,none⟩
  capacityStored := by decide
  pointerStored := by decide
  lengthStored := by decide
  capacityBound := by decide
  lengthBound := by decide
  nonnull := by decide
example : OwnsBuffer emptyDescriptor := .inl rfl
example : emptyDescriptor.buffer.provenance = none := rfl
example : emptyDescriptor.length.val = 0 := emptyDescriptor.zero_capacity_length rfl
example : ∃ next, NativeRawVecFields.pointerAccess emptyReady 0 = .value emptyDescriptor.buffer next :=
  emptyDescriptor.pointer_access_complete (by decide)
example : InitializedElements emptyDescriptor := ⟨[],by decide⟩

-- An exclusive child loan blocks reading through the parent until cleanup.
private def blocked : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run ready
    [.raw (.withAddress 2 136),.reborrow 0 0 .exclusive ⟨8,8⟩]).getD NativeReferenceMachine.empty
example : blocked.nextTag = 2 := by decide
example : NativeRawVecFields.pointerAccess blocked 1 = .invalid blocked := by decide
end FormalProof4FHETest.HasteBootsResidentVecSmoke
