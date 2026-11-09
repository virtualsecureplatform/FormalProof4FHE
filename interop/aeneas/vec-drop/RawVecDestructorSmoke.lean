namespace HasteBootsVecDrop.Smoke
open FormalProof4FHE.HasteBoots
open NativeResidentVecBorrow
open NativeRecordCallValues
open NativeRecordLLBC
private def rawvecMethodResult := invoke HasteBootsRawVecDrop.f5 reservedRawVec.2 [.rawVecExclusiveReference 0]
private def rawvecEntryResult := invoke HasteBootsRawVecDrop.f4 reservedRawVec.2 [.rawVecExclusiveReference 0]
private def emptyRawvecEntry := invoke HasteBootsRawVecDrop.f4 emptyRawVec.2 [.rawVecExclusiveReference 0]
private theorem rawvec_entry_invoked : NativeRecordDropCalls.Invokes f4 reservedRawVec.2 [.rawVecExclusiveReference 0] rawvecEntryResult := by
  apply invokeCode_sound
  rw [rawvec_glue_definition]
  exact native_definition_invoke HasteBootsRawVecDrop.f4 reservedRawVec.2 _
private theorem empty_rawvec_invoked : NativeRecordDropCalls.Invokes f4 emptyRawVec.2 [.rawVecExclusiveReference 0] emptyRawvecEntry := by
  apply invokeCode_sound
  rw [rawvec_glue_definition]
  exact native_definition_invoke HasteBootsRawVecDrop.f4 emptyRawVec.2 _
example : DeallocationPost reservedRawVec.2 ⟨64,some ⟨64,0⟩⟩ 8 rawvecMethodResult :=
  rawvec_method_invocation reservedRawVec.2 ⟨1⟩ ⟨128,some ⟨128,1⟩⟩ ⟨64,some ⟨64,0⟩⟩ 8 0 reserved_exclusive_view
example : DeallocationPost reservedRawVec.2 ⟨64,some ⟨64,0⟩⟩ 8 rawvecEntryResult :=
  rawvec_glue_invokes reservedRawVec.2 ⟨1⟩ ⟨128,some ⟨128,1⟩⟩ ⟨64,some ⟨64,0⟩⟩ 8 0 reserved_exclusive_view rawvecEntryResult rawvec_entry_invoked
example : 0 < (8 : NativeWord64Memory.Word).val ∧ ∃ block ∈ reservedRawVec.2.pointers.heap.memory.blocks,
    block.pointer = ⟨64,some ⟨64,0⟩⟩ ∧ block.layout = ⟨8,1⟩ ∧
    NativePointerByteMemory.deallocate reservedRawVec.2.pointers.heap block.pointer block.layout = some rawvecEntryResult.world.pointers.heap :=
  rawvec_glue_changed_block reservedRawVec.2 ⟨1⟩ ⟨128,some ⟨128,1⟩⟩ ⟨64,some ⟨64,0⟩⟩ 8 0 reserved_exclusive_view rawvecEntryResult rawvec_entry_invoked (by decide)
-- Original glue and method wrappers both finish and retain the caller loans.
example : rawvecEntryResult = .returned (.scalar .unit) rawvecEntryResult.world ∧
    NativePointerByteMemory.deallocate reservedRawVec.2.pointers.heap ⟨64,some ⟨64,0⟩⟩ ⟨8,1⟩ = some rawvecEntryResult.world.pointers.heap ∧
    rawvecEntryResult.world.nextTag = 6 ∧ rawvecEntryResult.world.leases.map NativeByteBorrow.Lease.tag = [1,0] := by decide
example : emptyRawvecEntry = .returned (.scalar .unit) emptyRawvecEntry.world ∧ emptyRawvecEntry.world.nextTag = 5 := by decide
example : emptyRawvecEntry.world.pointers.heap = emptyRawVec.2.pointers.heap :=
  rawvec_glue_invokes_zero emptyRawVec.2 ⟨1⟩ ⟨128,some ⟨128,0⟩⟩ ⟨1,none⟩ 0 empty_exclusive_view emptyRawvecEntry empty_rawvec_invoked
private def protectedRawvecEntry := invoke HasteBootsRawVecDrop.f4 protectedBuffer [.rawVecExclusiveReference 1]
example : protectedRawvecEntry = .invalid protectedRawvecEntry.world ∧ protectedRawvecEntry.world.pointers.heap = protectedBuffer.pointers.heap ∧
    protectedRawvecEntry.world.nextTag = 7 := by decide
-- An overlapping shared child permits reservation but blocks exclusive activation.
private def methodBlocked := invoke HasteBootsRawVecDrop.f5 reservedShared.2 [.rawVecExclusiveReference 1]
private def glueBlocked := invoke HasteBootsRawVecDrop.f4 reservedShared.2 [.rawVecExclusiveReference 1]
example : methodBlocked = .invalid methodBlocked.world ∧ methodBlocked.world.nextTag = 3 ∧
    methodBlocked.world.pointers.registers.length = reservedShared.2.pointers.registers.length + 1 ∧
    methodBlocked.world.pointers.heap = reservedShared.2.pointers.heap := by decide
example : glueBlocked = .invalid glueBlocked.world ∧ glueBlocked.world.nextTag = 3 ∧
    glueBlocked.world.pointers.registers.length = reservedShared.2.pointers.registers.length + 1 ∧
    glueBlocked.world.pointers.heap = reservedShared.2.pointers.heap := by decide
private def endedRawvec := (NativeReferenceCleanup.closeScope reservedReady reservedRawVec.2).world
example : invoke HasteBootsRawVecDrop.f4 endedRawvec [.rawVecExclusiveReference 0] = .invalid endedRawvec := by decide
example : ∃ final, invoke HasteBootsRawVecDrop.f5 reservedRawVec.2 [.rawVecExclusiveReference 0] =
    .returned (.scalar .unit) final ∧ final.leases = reservedRawVec.2.leases ∧ NativeReferenceMachine.Reachable final ∧
    NativePointerByteMemory.deallocate reservedRawVec.2.pointers.heap ⟨64,some ⟨64,0⟩⟩ ⟨8,1⟩ = some final.pointers.heap := by
  simpa only [show reservedRawVec.2.references.idxOf ⟨1⟩ = 0 by decide,
    show (8 : NativeWord64Memory.Word) ≠ 0 by decide,show (8 : NativeWord64Memory.Word).val = 8 from rfl,ite_false] using
    rawvec_method_invocation_complete reservedRawVec.2 ⟨1⟩ 8 0 ⟨64,some ⟨64,0⟩⟩ reservedRawVecReady
      (fixture_buffer_available _ _ _ (by decide))
      (Or.inr ⟨⟨⟨64,0⟩,64,⟨8,1⟩,List.replicate 8 none⟩,by decide,rfl,rfl⟩)
example : ∃ final, invoke HasteBootsRawVecDrop.f5 emptyRawVec.2 [.rawVecExclusiveReference 0] =
    .returned (.scalar .unit) final ∧ final.leases = emptyRawVec.2.leases ∧ NativeReferenceMachine.Reachable final ∧
    final.pointers.heap = emptyRawVec.2.pointers.heap := by
  simpa only [show emptyRawVec.2.references.idxOf ⟨1⟩ = 0 by decide,ite_true] using
    rawvec_method_invocation_complete emptyRawVec.2 ⟨1⟩ 0 0 ⟨1,none⟩ emptyRawVecReady
      (fixture_buffer_available _ _ _ (by decide)) (Or.inl rfl)
example : ∃ final, NativeRecordDropCalls.Invokes f4 reservedRawVec.2 [.rawVecExclusiveReference 0]
    (.returned (.scalar .unit) final) ∧ final.leases = reservedRawVec.2.leases ∧ NativeReferenceMachine.Reachable final ∧
    NativePointerByteMemory.deallocate reservedRawVec.2.pointers.heap ⟨64,some ⟨64,0⟩⟩ ⟨8,1⟩ = some final.pointers.heap := by
  simpa only [show reservedRawVec.2.references.idxOf ⟨1⟩ = 0 by decide,
    show (8 : NativeWord64Memory.Word) ≠ 0 by decide,show (8 : NativeWord64Memory.Word).val = 8 from rfl,ite_false] using
    rawvec_glue_invokes_complete reservedRawVec.2 ⟨1⟩ 8 0 ⟨64,some ⟨64,0⟩⟩ reservedRawVecReady
      (fixture_buffer_available _ _ _ (by decide))
      (Or.inr ⟨⟨⟨64,0⟩,64,⟨8,1⟩,List.replicate 8 none⟩,by decide,rfl,rfl⟩)
example : ∃ final, NativeRecordDropCalls.Invokes f4 emptyRawVec.2 [.rawVecExclusiveReference 0]
    (.returned (.scalar .unit) final) ∧ final.leases = emptyRawVec.2.leases ∧ NativeReferenceMachine.Reachable final ∧
    final.pointers.heap = emptyRawVec.2.pointers.heap := by
  simpa only [show emptyRawVec.2.references.idxOf ⟨1⟩ = 0 by decide,ite_true] using
    rawvec_glue_invokes_complete emptyRawVec.2 ⟨1⟩ 0 0 ⟨1,none⟩ emptyRawVecReady
      (fixture_buffer_available _ _ _ (by decide)) (Or.inl rfl)
end HasteBootsVecDrop.Smoke
