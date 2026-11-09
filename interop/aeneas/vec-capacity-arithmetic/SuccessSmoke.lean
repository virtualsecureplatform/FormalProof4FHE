namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

example : NativeRecordValues.fits allocationResultType (runtimeSuccessValue ⟨8,some ⟨8,0⟩⟩ 3) = true := rfl

example : NativeRecordValues.get (runtimeSuccessValue ⟨8,some ⟨8,0⟩⟩ 3)
    [(.unwrap 15),(.active false),.left, (.unwrap 16),.left] =
      some (.scalar (.raw ⟨⟨8,some ⟨8,0⟩⟩,some 3⟩)) := rfl

example (ambient : Frame) (world : NativeReferenceMachine.State) :
    (runtimeSuccessFrame ambient 3 false world ⟨8,some ⟨8,0⟩⟩).slots[12]? = some .dead := by
  simp [runtimeSuccessFrame,runtimeSliceFrame,runtimeThinFrame,runtimeInspectedFrame,runtimeAllocatedFrame,
    runtimeArgumentsFrame,runtimeAlignmentFrame,runtimeAfterShim,implementationPrepared]

example (ambient : Frame) (world : NativeReferenceMachine.State) :
    (runtimeSuccessFrame ambient 3 true world ⟨8,some ⟨8,0⟩⟩).slots[0]? =
      some (.live (some (runtimeSuccessValue ⟨8,some ⟨8,0⟩⟩ 3))) := by
  simp [runtimeSuccessFrame,runtimeSliceFrame,runtimeThinFrame,runtimeInspectedFrame,runtimeAllocatedFrame,
    runtimeArgumentsFrame,runtimeAlignmentFrame,runtimeAfterShim,implementationPrepared]

example (ambient : Frame) (world : NativeReferenceMachine.State) :
    NativeAllocatorLLBC.eval runtimeSuccess (runtimeInspectedFrame ambient 3 false world ⟨8,some ⟨8,0⟩⟩) =
      .normal (runtimeSuccessFrame ambient 3 false world ⟨8,some ⟨8,0⟩⟩) := runtime_success_exact ambient 3 false world _

example (ambient : Frame) (shim zero null : NativeAllocatorLLBC.Body)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) NativeReferenceMachine.empty [] =
      .returned (.scalar .unit) NativeReferenceMachine.empty) :
    NativeAllocatorLLBC.invokeValues
      (implementationFunction {ambient with world := NativeReferenceMachine.empty} zero
        (runtimePositive (some 8) shim null runtimeSuccess)) NativeReferenceMachine.empty
      [capacityLayout 3,.boolean false] = .returned (runtimeSuccessValue ⟨8,some ⟨8,0⟩⟩ 3)
        (NativeAllocatorExecution.allocated NativeReferenceMachine.empty 8 ⟨3,1⟩) :=
  runtime_positive_invocation _ 3 false (some 8) shim zero null _ _ _ (by decide) returned (by decide) (by decide)

private def successZeroWorld : NativeReferenceMachine.State :=
  (NativeAllocatorExecution.run NativeReferenceMachine.empty .zeroed (some 8) 3 1).world

example : NativeByteRange.loadRange successZeroWorld.pointers.heap.memory ⟨8,some ⟨8,0⟩⟩ ⟨3,1⟩ = some [0,0,0] := by decide

example (ambient : Frame) (shim zero null : NativeAllocatorLLBC.Body)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) NativeReferenceMachine.empty [] =
      .returned (.scalar .unit) NativeReferenceMachine.empty) :
    NativeAllocatorLLBC.invokeValues
      (implementationFunction {ambient with world := NativeReferenceMachine.empty} zero
        (runtimePositive (some 8) shim null runtimeSuccess)) NativeReferenceMachine.empty
      [capacityLayout 3,.boolean true] = .returned (runtimeSuccessValue ⟨8,some ⟨8,0⟩⟩ 3) successZeroWorld :=
  runtime_positive_invocation _ 3 true (some 8) shim zero null _ _ _ (by decide) returned (by decide) (by decide)

end HasteBootsVecCapacityArithmetic
