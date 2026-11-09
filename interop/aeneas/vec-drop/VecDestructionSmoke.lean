namespace HasteBootsVecDrop.Smoke
open FormalProof4FHE.HasteBoots
open NativeResidentVec
open NativeRecordLLBC (Flow)

private theorem bytePrefixOwned : OwnsBuffer bytePrefixDescriptor := by
  right
  exact ⟨by decide,⟨⟨64,0⟩,64,⟨8,1⟩,List.replicate 8 (some 0)⟩,by decide,rfl,rfl⟩

example : ∃ final, NativeRecordDropCalls.Invokes f1 (world 8 3) [.vectorExclusiveReference 0]
    (.returned (.scalar .unit) final) ∧ NativeReferenceMachine.Reachable final ∧ final.leases = (world 8 3).leases ∧
    NativePointerByteMemory.deallocate (world 8 3).pointers.heap ⟨64,some ⟨64,0⟩⟩ ⟨8,1⟩ = some final.pointers.heap := by
  simpa only [show (world 8 3).references.idxOf bytePrefixDescriptor.reference = 0 by decide,
    show bytePrefixDescriptor.capacity ≠ 0 by decide,show bytePrefixDescriptor.capacity.val = 8 from rfl,
    show bytePrefixDescriptor.buffer = ⟨64,some ⟨64,0⟩⟩ from rfl,ite_false] using
    vec_glue_invokes_complete bytePrefixDescriptor bytePrefixReachable bytePrefixInitialized bytePrefixAvailable bytePrefixFrontier bytePrefixOwned

example : ∃ final, execute emptyReady [.vectorExclusiveReference 0] = .returned (.scalar .unit) final ∧
    NativeReferenceMachine.Reachable final ∧ final.leases = emptyReady.leases ∧ final.pointers.heap = emptyReady.pointers.heap := by
  simpa only [show emptyReady.references.idxOf byteEmptyDescriptor.reference = 0 by decide,
    show byteEmptyDescriptor.capacity = 0 from rfl,ite_true] using
    vec_execute_complete byteEmptyDescriptor byteEmptyReachable (byteEmptyDescriptor.zero_capacity_initialized rfl)
      (fixture_buffer_available _ _ _ (by decide))
      (NativeBorrowFrontier.singleton_frontier _ _ (by decide) rfl) (Or.inl rfl)

private theorem reservedVecReachable : NativeReferenceMachine.Reachable reservedReady := by
  apply NativeReferenceMachine.run_reachable NativeReferenceMachine.empty reservedReady .empty
    [.raw (.allocate 64 ⟨8,1⟩),.raw (.allocate 128 ⟨24,8⟩),
     .raw (.writeBytes 0 8 (NativeWord64Memory.encode 8)),.raw (.withAddress 0 136),
     .raw (.store 0 2),.raw (.withAddress 1 144),
     .raw (.writeBytes 0 8 (NativeWord64Memory.encode 0)),.borrow 2 .exclusive ⟨24,8⟩]
  decide
private def reservedVecDescriptor : Descriptor reservedReady 0 where
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
  length := 0
  buffer := ⟨64,some ⟨64,0⟩⟩
  capacityStored := by decide
  pointerStored := by decide
  lengthStored := by decide
  capacityBound := by decide
  lengthBound := by decide
  nonnull := by decide
private theorem reservedVecOwned : OwnsBuffer reservedVecDescriptor := by
  right
  exact ⟨by decide,⟨⟨64,0⟩,64,⟨8,1⟩,List.replicate 8 none⟩,by decide,rfl,rfl⟩

-- No element bytes are initialized, yet normal destruction frees the reservation.
example : ∃ final, execute reservedReady [.vectorExclusiveReference 0] = .returned (.scalar .unit) final ∧
    NativeReferenceMachine.Reachable final ∧ final.leases = reservedReady.leases ∧
    NativePointerByteMemory.deallocate reservedReady.pointers.heap ⟨64,some ⟨64,0⟩⟩ ⟨8,1⟩ = some final.pointers.heap := by
  simpa only [show reservedReady.references.idxOf reservedVecDescriptor.reference = 0 by decide,
    show reservedVecDescriptor.capacity ≠ 0 by decide,show reservedVecDescriptor.capacity.val = 8 from rfl,
    show reservedVecDescriptor.buffer = ⟨64,some ⟨64,0⟩⟩ from rfl,ite_false] using
    vec_execute_complete reservedVecDescriptor reservedVecReachable (reservedVecDescriptor.empty_elements_initialized rfl)
      (fixture_buffer_available _ _ _ (by decide))
      (NativeBorrowFrontier.singleton_frontier _ _ (by decide) rfl) reservedVecOwned

example (flow : Flow) (invoked : NativeRecordDropCalls.Invokes f1 (world 8 3) [.vectorExclusiveReference 0] flow) :
    ∃ final, flow = .returned (.scalar .unit) final ∧ NativeReferenceMachine.Reachable final ∧
    final.leases = (world 8 3).leases ∧
    NativePointerByteMemory.deallocate (world 8 3).pointers.heap ⟨64,some ⟨64,0⟩⟩ ⟨8,1⟩ = some final.pointers.heap := by
  have selected : (world 8 3).references.idxOf bytePrefixDescriptor.reference = 0 := by decide
  rw [← selected] at invoked
  simpa only [show bytePrefixDescriptor.capacity ≠ 0 by decide,
    show bytePrefixDescriptor.capacity.val = 8 from rfl,
    show bytePrefixDescriptor.buffer = ⟨64,some ⟨64,0⟩⟩ from rfl,ite_false] using
    vec_glue_invokes_unit bytePrefixDescriptor bytePrefixReachable bytePrefixInitialized bytePrefixAvailable bytePrefixFrontier bytePrefixOwned flow invoked
end HasteBootsVecDrop.Smoke
