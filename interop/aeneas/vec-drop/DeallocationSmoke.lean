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
end HasteBootsVecDrop.Smoke
