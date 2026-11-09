namespace HasteBootsVecDrop.Smoke
open FormalProof4FHE.HasteBoots
open NativeResidentVec
open NativeVecBytePrefix
private theorem bytePrefixReachable : NativeReferenceMachine.Reachable (world 8 3) := by
  apply NativeReferenceMachine.run_reachable NativeReferenceMachine.empty (world 8 3) .empty
    [.raw (.allocate 64 ⟨8,1⟩),.raw (.writeBytes 0 1 (List.replicate 8 0)),
     .raw (.allocate 128 ⟨24,8⟩),.raw (.writeBytes 0 8 (NativeWord64Memory.encode 8)),
     .raw (.withAddress 0 136),.raw (.store 0 2),.raw (.withAddress 1 144),
     .raw (.writeBytes 0 8 (NativeWord64Memory.encode 3)),.borrow 2 .exclusive ⟨24,8⟩]
  decide
private def bytePrefixDescriptor : Descriptor (world 8 3) 0 where
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
  length := 3
  buffer := ⟨64,some ⟨64,0⟩⟩
  capacityStored := by decide
  pointerStored := by decide
  lengthStored := by decide
  capacityBound := by decide
  lengthBound := by decide
  nonnull := by decide
private theorem bytePrefixInitialized : InitializedElements bytePrefixDescriptor := ⟨[0,0,0],by decide⟩
private theorem bytePrefixFrontier : NativeBorrowFrontier.ExclusiveFrontier (NativeReferenceMachine.ledger (world 8 3)) bytePrefixDescriptor.lease :=
  NativeBorrowFrontier.singleton_frontier _ _ (by decide) rfl
private theorem bytePrefixAvailable : Available (world 8 3) bytePrefixDescriptor.buffer 8 := by
  intro lease member
  have leases : (world 8 3).leases = [bytePrefixDescriptor.lease] := by decide
  rw [leases] at member
  have same := List.mem_singleton.mp member
  subst lease
  decide
example : NativeRecordLLBC.eval byteFieldBody (byteMethodEntry (world 8 3) ⟨0⟩) =
    .normal (byteFieldsFrame bytePrefixDescriptor) :=
  byte_fields_complete bytePrefixDescriptor (NativeReferenceMachine.reachable_wellFormed _ bytePrefixReachable).2.1 bytePrefixFrontier
example : ∃ next, NativeByteTraversalCompleteness.Ready next ⟨⟨(world 8 3).nextTag⟩,3⟩ ∧
    evalCode f2.code (byteMethodEntry (world 8 3) ⟨0⟩) =
      match evalCode byteCallCode (byteBorrowCaller bytePrefixDescriptor next) with
      | none => none
      | some returned => match NativeRecordDropCalls.resumeScope (lengthWorld bytePrefixDescriptor) returned with
        | .normal changed => evalCode byteAfterCode changed
        | flow => some flow :=
  byte_method_ready_prefix bytePrefixDescriptor bytePrefixReachable bytePrefixInitialized bytePrefixAvailable bytePrefixFrontier
example : ∃ next, NativeRecordLLBC.eval byteBorrowBody (bytePartsFrame bytePrefixDescriptor) = .normal (byteBorrowCaller bytePrefixDescriptor next) ∧
    NativeRecordDropCalls.prepareCall (byteBorrowCaller bytePrefixDescriptor next) f3.types f3.argCount [.move 6 []] =
      some (byteCallConsumed bytePrefixDescriptor next,byteForeignEntry bytePrefixDescriptor next) ∧
    NativeByteTraversalCompleteness.Ready next ⟨⟨(world 8 3).nextTag⟩,3⟩ := by
  obtain ⟨next,computed,ready⟩ := byte_borrow_complete bytePrefixDescriptor bytePrefixReachable bytePrefixInitialized bytePrefixAvailable bytePrefixFrontier
  exact ⟨next,computed,byte_call_prepared bytePrefixDescriptor next,ready⟩
private theorem byteEmptyReachable : NativeReferenceMachine.Reachable emptyReady := by
  apply NativeReferenceMachine.run_reachable NativeReferenceMachine.empty emptyReady .empty
    [.raw (.allocate 128 ⟨24,8⟩),.raw (.writeBytes 0 8 (NativeWord64Memory.encode 0)),
     .raw (.fromAddress 1),.raw (.withAddress 1 136),.raw (.store 0 1),
     .raw (.withAddress 2 144),.raw (.writeBytes 0 8 (NativeWord64Memory.encode 0)),.borrow 3 .exclusive ⟨24,8⟩]
  decide
private def byteEmptyDescriptor : Descriptor emptyReady 0 where
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
example : ∃ next, NativeRecordLLBC.eval byteBorrowBody (bytePartsFrame byteEmptyDescriptor) = .normal (byteBorrowCaller byteEmptyDescriptor next) ∧
    NativeByteTraversalCompleteness.Ready next ⟨⟨emptyReady.nextTag⟩,0⟩ := by
  apply byte_borrow_complete byteEmptyDescriptor byteEmptyReachable (byteEmptyDescriptor.zero_capacity_initialized rfl) ?_
    (NativeBorrowFrontier.singleton_frontier _ _ (by decide) rfl)
  intro lease _
  change ¬ NativeByteBorrow.Overlap ⟨1,none⟩ ⟨0,1⟩ lease.pointer lease.layout
  simp only [NativeByteBorrow.Overlap]
  omega
end HasteBootsVecDrop.Smoke
