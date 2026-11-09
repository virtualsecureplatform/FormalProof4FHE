namespace HasteBootsVecDrop.Smoke
open FormalProof4FHE.HasteBoots
open NativeResidentVecBorrow
open NativeRecordCallValues
open NativeRecordLLBC
private theorem reserved_exclusive_view : Resident reservedRawVec.2 reservedRawVec.1 ⟨128,some ⟨128,1⟩⟩ 8 0 ⟨64,some ⟨64,0⟩⟩ := by
  refine ⟨true,⟨1⟩,2,⟨1,some 0,⟨128,some ⟨128,1⟩⟩,⟨16,8⟩,.exclusive⟩,
    by decide,by decide,by decide,rfl,rfl,Or.inr ⟨rfl,rfl⟩,by decide,?_⟩
  constructor <;> decide
private theorem empty_exclusive_view : Resident emptyRawVec.2 emptyRawVec.1 ⟨128,some ⟨128,0⟩⟩ 0 0 ⟨1,none⟩ := by
  refine ⟨true,⟨1⟩,2,⟨1,some 0,⟨128,some ⟨128,0⟩⟩,⟨16,8⟩,.exclusive⟩,
    by decide,by decide,by decide,rfl,rfl,Or.inr ⟨rfl,rfl⟩,by decide,?_⟩
  constructor <;> decide
private def reservedDeallocated := invoke HasteBootsRawVecDrop.f7 reservedRawVec.2 [.rawVecExclusiveReference 0,currentMemoryLayout]
private def emptyDeallocated := invoke HasteBootsRawVecDrop.f7 emptyRawVec.2 [.rawVecExclusiveReference 0,currentMemoryLayout]
example : DeallocationPost reservedRawVec.2 ⟨64,some ⟨64,0⟩⟩ 8 reservedDeallocated :=
  deallocation_invocation reservedRawVec.2 ⟨1⟩ ⟨128,some ⟨128,1⟩⟩ ⟨64,some ⟨64,0⟩⟩ 8 0 reserved_exclusive_view
-- Length zero still frees the complete uninitialized reservation.
example : reservedDeallocated = .returned (.scalar .unit) reservedDeallocated.world ∧
    NativePointerByteMemory.deallocate reservedRawVec.2.pointers.heap ⟨64,some ⟨64,0⟩⟩ ⟨8,1⟩ = some reservedDeallocated.world.pointers.heap := by decide
example : reservedDeallocated.world.leases.map NativeByteBorrow.Lease.tag = [1,0] ∧ reservedDeallocated.world.nextTag = 4 := by decide
example : NativeByteRange.loadRange reservedDeallocated.world.pointers.heap.memory ⟨64,some ⟨64,0⟩⟩ ⟨1,1⟩ = none := by decide
example : NativePointerByteMemory.load reservedDeallocated.world.pointers.heap ⟨136,some ⟨128,1⟩⟩ = some ⟨64,some ⟨64,0⟩⟩ := by decide
example : emptyDeallocated = .returned (.scalar .unit) emptyDeallocated.world ∧
    emptyDeallocated.world.pointers.heap = emptyRawVec.2.pointers.heap ∧ emptyDeallocated.world.nextTag = 3 := by decide
-- Address bits alone cannot select the original reservation for the Global call.
example : invokeValues HasteBootsRawVecDrop.f9 reservedRawVec.2 (globalValues ⟨0⟩ ⟨64,none⟩ 8) = .invalid reservedRawVec.2 := by decide
example : invokeValues HasteBootsRawVecDrop.f9 reservedRawVec.2 (globalValues ⟨0⟩ ⟨64,some ⟨64,0⟩⟩ 4) = .invalid reservedRawVec.2 := by decide

private def protectedBuffer : NativeReferenceMachine.State :=
  let register := reservedRawVec.2.pointers.registers.idxOf ⟨64,some ⟨64,0⟩⟩
  (NativeReferenceMachine.run reservedRawVec.2
    [.raw (.writeBytes register 1 (List.replicate 8 0)),.borrow register .shared ⟨8,1⟩]).getD NativeReferenceMachine.empty
private def rejectedFree := invoke HasteBootsRawVecDrop.f7 protectedBuffer [.rawVecExclusiveReference 1,currentMemoryLayout]
example : protectedBuffer.nextTag = 3 := by decide
-- The failed free retains the source prefix and leaves the protected allocation.
example : rejectedFree = .invalid rejectedFree.world ∧ rejectedFree.world.pointers.heap = protectedBuffer.pointers.heap ∧
    rejectedFree.world.nextTag = 5 := by decide
private theorem fixture_shared_frontier (world : NativeReferenceMachine.State) (lease : NativeByteBorrow.Lease)
    (shared : lease.mode = .shared) (found : NativeByteBorrow.lookup world.leases lease.tag = some lease)
    (checked : world.leases.all (fun other => decide (other.tag = lease.tag) ||
      NativeByteBorrow.ancestor world.leases world.nextTag other.tag lease.tag) = true) :
    NativeRawVecSharedCompleteness.SharedFrontier (NativeReferenceMachine.ledger world) lease := by
  refine ⟨shared,found,?_⟩
  simp only [List.all_eq_true,Bool.or_eq_true,decide_eq_true_eq] at checked
  intro other member
  rcases checked other member with same | ancestor
  · exact Or.inl same
  · exact Or.inr (Or.inl (NativeByteBorrow.ancestor_sound _ _ _ _ ancestor))
private def reservedSharedHeader : NativeRawVecSharedCompleteness.Header reservedShared.2 ⟨2⟩ 8 0 ⟨64,some ⟨64,0⟩⟩ where
  lease := ⟨2,some 1,⟨128,some ⟨128,1⟩⟩,⟨16,8⟩,.shared⟩
  valid := (NativeReferenceMachine.run_wellFormed
    [.raw (.allocate 64 ⟨8,1⟩),.raw (.allocate 128 ⟨24,8⟩),
     .raw (.writeBytes 0 8 (NativeWord64Memory.encode 8)),.raw (.withAddress 0 136),
     .raw (.store 0 2),.raw (.withAddress 1 144),.raw (.writeBytes 0 8 (NativeWord64Memory.encode 0)),
     .borrow 2 .exclusive ⟨24,8⟩,.raw (.withAddress 2 128),.reborrow 0 0 .exclusive ⟨16,8⟩,
     .raw (.withAddress 0 128),.reborrow 0 0 .shared ⟨16,8⟩] reservedShared.2 (by decide)).2.1
  frontier := fixture_shared_frontier _ _ rfl (by decide) (by decide)
  tag := rfl
  shape := rfl
  referenceResident := by decide
  pointerResident := by decide
  fields := by constructor <;> decide
private def emptySharedHeader : NativeRawVecSharedCompleteness.Header emptyShared.2 ⟨2⟩ 0 0 ⟨1,none⟩ where
  lease := ⟨2,some 1,⟨128,some ⟨128,0⟩⟩,⟨16,8⟩,.shared⟩
  valid := (NativeReferenceMachine.run_wellFormed
    [.raw (.allocate 128 ⟨24,8⟩),.raw (.writeBytes 0 8 (NativeWord64Memory.encode 0)),
     .raw (.fromAddress 1),.raw (.withAddress 1 136),.raw (.store 0 1),
     .raw (.withAddress 2 144),.raw (.writeBytes 0 8 (NativeWord64Memory.encode 0)),
     .borrow 3 .exclusive ⟨24,8⟩,.raw (.withAddress 3 128),.reborrow 0 0 .exclusive ⟨16,8⟩,
     .raw (.withAddress 0 128),.reborrow 0 0 .shared ⟨16,8⟩] emptyShared.2 (by decide)).2.1
  frontier := fixture_shared_frontier _ _ rfl (by decide) (by decide)
  tag := rfl
  shape := rfl
  referenceResident := by decide
  pointerResident := by decide
  fields := by constructor <;> decide
example : ∃ final, invokeValues HasteBootsRawVecDrop.f8 reservedShared.2
    [.scalar (.reference false ⟨2⟩ 2),currentMemoryLayoutValue] =
      .returned (currentMemorySome ⟨64,some ⟨64,0⟩⟩ 8) final ∧
    final.leases = reservedShared.2.leases ∧ final.pointers.heap = reservedShared.2.pointers.heap := by
  simpa only [show (8 : NativeWord64Memory.Word) ≠ 0 by decide,ite_false] using
    current_memory_complete reservedShared.2 ⟨2⟩ 8 0 ⟨64,some ⟨64,0⟩⟩ reservedSharedHeader
example : ∃ final, invokeValues HasteBootsRawVecDrop.f8 emptyShared.2
    [.scalar (.reference false ⟨2⟩ 2),currentMemoryLayoutValue] = .returned currentMemoryNone final ∧
    final.leases = emptyShared.2.leases ∧ final.pointers.heap = emptyShared.2.pointers.heap := by
  simpa only [ite_true] using current_memory_complete emptyShared.2 ⟨2⟩ 0 0 ⟨1,none⟩ emptySharedHeader
end HasteBootsVecDrop.Smoke
