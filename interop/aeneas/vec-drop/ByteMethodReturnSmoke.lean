namespace HasteBootsVecDrop.Smoke
open FormalProof4FHE.HasteBoots
open NativeVecBytePrefix
example : ∃ final, evalCode f3.code (sliceHelperEntry incomingWorld incomingSlice) = some (.returned (.scalar .unit) final) ∧
    NativeReferenceMachine.Reachable final ∧ final.leases = incomingWorld.leases ∧ final.pointers.heap = incomingWorld.pointers.heap :=
  slice_helper_complete incomingWorld incomingSlice traversalIncomingReady
example : ∃ final, NativeRecordDropCalls.Invokes f2 (world 8 3) [.vectorExclusiveReference 0] (.returned (.scalar .unit) final) ∧
    NativeReferenceMachine.Reachable final ∧ final.leases = (world 8 3).leases ∧ final.pointers.heap = (world 8 3).pointers.heap :=
  byte_method_invocation_complete bytePrefixDescriptor bytePrefixReachable bytePrefixInitialized bytePrefixAvailable bytePrefixFrontier
example : ∃ final, evalCode f2.code (byteMethodEntry (world 8 3) ⟨0⟩) = some (.returned (.scalar .unit) final) ∧
    NativeResidentVecBorrow.Resident final (.reference true ⟨0⟩ 3) ⟨128,some ⟨128,1⟩⟩ 8 3 ⟨64,some ⟨64,0⟩⟩ :=
  byte_method_return_resident bytePrefixDescriptor bytePrefixReachable bytePrefixInitialized bytePrefixAvailable bytePrefixFrontier
example : ∃ final, NativeRecordDropCalls.Invokes f2 emptyReady [.vectorExclusiveReference 0] (.returned (.scalar .unit) final) ∧
    NativeReferenceMachine.Reachable final ∧ final.leases = emptyReady.leases ∧ final.pointers.heap = emptyReady.pointers.heap := by
  apply byte_method_invocation_complete byteEmptyDescriptor byteEmptyReachable (byteEmptyDescriptor.zero_capacity_initialized rfl) ?_
    (NativeBorrowFrontier.singleton_frontier _ _ (by decide) rfl)
  intro lease _
  change ¬ NativeByteBorrow.Overlap ⟨1,none⟩ ⟨0,1⟩ lease.pointer lease.layout
  simp only [NativeByteBorrow.Overlap]
  omega
-- A concrete original execution agrees with unit return and exact loan restoration.
example : ∃ flow, NativeRecordDropCalls.Invokes f2 (world 8 3) [.vectorExclusiveReference 0] flow ∧
    flow = .returned (.scalar .unit) flow.world ∧ flow.world.nextTag = 9 ∧
    flow.world.leases.map NativeByteBorrow.Lease.tag = [0] := by
  econstructor
  constructor
  · apply NativeRecordDropCalls.Invokes.run [.scalar (.reference true ⟨0⟩ 3)]
    · decide
    · rfl
    · run_vec_drop
  · decide
end HasteBootsVecDrop.Smoke
