namespace HasteBootsVecDrop.Smoke
open FormalProof4FHE.HasteBoots
open NativeResidentVecBorrow
open NativeRecordLLBC
private def capacityObserved (result : NativeRawVecFields.Result NativeSliceLLBC.Value) : NativeSliceLLBC.Value × NativeReferenceMachine.State :=
  match result with | .value value world => (value,world) | .invalid world => (.unit,world)
private def reservedRawVec := capacityObserved (NativeVecReference.reborrow reservedReady (.reference true ⟨0⟩ 3) .rawVec)
private def reservedShared := capacityObserved (NativeRawVecBorrow.reborrow reservedRawVec.2 reservedRawVec.1 .whole)
private def emptyRawVec := capacityObserved (NativeVecReference.reborrow emptyReady (.reference true ⟨0⟩ 3) .rawVec)
private def emptyShared := capacityObserved (NativeRawVecBorrow.reborrow emptyRawVec.2 emptyRawVec.1 .whole)
private theorem reserved_view : Resident reservedShared.2 reservedShared.1 ⟨128,some ⟨128,1⟩⟩ 8 0 ⟨64,some ⟨64,0⟩⟩ := by
  refine ⟨false,⟨2⟩,2,⟨2,some 1,⟨128,some ⟨128,1⟩⟩,⟨16,8⟩,.shared⟩,
    by decide,by decide,by decide,rfl,rfl,Or.inr ⟨rfl,rfl⟩,by decide,?_⟩
  constructor <;> decide
private theorem empty_view : Resident emptyShared.2 emptyShared.1 ⟨128,some ⟨128,0⟩⟩ 0 0 ⟨1,none⟩ := by
  refine ⟨false,⟨2⟩,2,⟨2,some 1,⟨128,some ⟨128,0⟩⟩,⟨16,8⟩,.shared⟩,
    by decide,by decide,by decide,rfl,rfl,Or.inr ⟨rfl,rfl⟩,by decide,?_⟩
  constructor <;> decide

example : currentMemoryPost 8 ⟨64,some ⟨64,0⟩⟩ (invoke HasteBootsRawVecDrop.f8 reservedShared.2
    [.rawVecSharedReference 0,currentMemoryLayout]) :=
  current_memory_resident reservedShared.2 ⟨2⟩ ⟨128,some ⟨128,1⟩⟩ ⟨64,some ⟨64,0⟩⟩ 8 0 reserved_view
example : currentMemoryPost 0 ⟨1,none⟩ (invoke HasteBootsRawVecDrop.f8 emptyShared.2
    [.rawVecSharedReference 0,currentMemoryLayout]) :=
  current_memory_resident emptyShared.2 ⟨2⟩ ⟨128,some ⟨128,0⟩⟩ ⟨1,none⟩ 0 0 empty_view
-- Source dispatch uses reserved capacity even when no element is initialized.
example : ∃ final, invoke HasteBootsRawVecDrop.f8 reservedShared.2 [.rawVecSharedReference 0,currentMemoryLayout] =
    .returned (currentMemorySome ⟨64,some ⟨64,0⟩⟩ 8) final ∧ final.pointers.heap = reservedShared.2.pointers.heap := by
  refine ⟨(invoke HasteBootsRawVecDrop.f8 reservedShared.2 [.rawVecSharedReference 0,currentMemoryLayout]).world,by decide,by decide⟩
example : ∃ final, invoke HasteBootsRawVecDrop.f8 emptyShared.2 [.rawVecSharedReference 0,currentMemoryLayout] =
    .returned currentMemoryNone final ∧ final.pointers.heap = emptyShared.2.pointers.heap := by
  refine ⟨(invoke HasteBootsRawVecDrop.f8 emptyShared.2 [.rawVecSharedReference 0,currentMemoryLayout]).world,by decide,by decide⟩
example (result : NativeRecordValues.Value) (final : NativeReferenceMachine.State)
    (returned : invoke HasteBootsRawVecDrop.f8 reservedShared.2 [.rawVecSharedReference 0,currentMemoryLayout] = .returned result final) :
    result ≠ currentMemorySome ⟨64,none⟩ 8 := by
  have exactResult := current_memory_return reservedShared.2 final ⟨2⟩ ⟨128,some ⟨128,1⟩⟩ ⟨64,some ⟨64,0⟩⟩ 8 0 reserved_view result returned
  rw [exactResult]
  decide
private def endedShared := (NativeReferenceCleanup.closeScope reservedReady reservedShared.2).world
example : invoke HasteBootsRawVecDrop.f8 endedShared [.rawVecSharedReference 0,currentMemoryLayout] = .invalid endedShared := by decide
end HasteBootsVecDrop.Smoke
