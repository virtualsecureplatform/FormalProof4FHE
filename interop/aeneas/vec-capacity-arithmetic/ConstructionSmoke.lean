namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

example (ambient : Frame) : NativeRecordValues.fits
    ((layoutTypes (positiveAmbient ambient false))[0]?.getD (.scalar .unit))
    (positiveResultValue ⟨8,some ⟨8,0⟩⟩ 3) = true := by
  simp [layoutTypes,positiveAmbient,positiveResultValue,positiveRawValue,runtimeThinValue,allocatorValue,
    NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]

example : NativeRecordValues.get (positiveResultValue ⟨8,some ⟨8,0⟩⟩ 3)
    [(.unwrap 8),(.active false),.left, (.unwrap 3),.left, (.unwrap 6),.left, (.unwrap 13),.left] =
      some (.scalar (.raw ⟨⟨8,some ⟨8,0⟩⟩,none⟩)) := rfl

example : NativeRecordValues.get (positiveResultValue ⟨8,some ⟨8,0⟩⟩ 3)
    [(.unwrap 8),(.active false),.left, (.unwrap 3),.right,.left, (.unwrap 7),.left] =
      some (.scalar (.usize 3)) := rfl

example (ambient : Frame) (world : NativeReferenceMachine.State) :
    (positiveRawFrame ambient 3 false 64 world ⟨8,some ⟨8,0⟩⟩).slots[3]? = some (.live (some .uninit)) := by
  simp [positiveRawFrame,positivePointerFrame,positiveReturnedFrame,positiveMovedFrame,positiveBorrowFrame,
    positiveModeFrame,layoutAcceptedFrame,positiveAmbient]

example (ambient : Frame) (reference : NativeReferenceMachine.Reference) (shim zero nonnull : NativeAllocatorLLBC.Body)
    (world : NativeReferenceMachine.State)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) ambient.world [] = .returned (.scalar .unit) world) :
    NativeAllocatorLLBC.invokeValues
      (allocationMethod ambient false zero (runtimePositive none shim runtimeNull nonnull)) ambient.world
      [.scalar (.reference false reference 0),capacityLayout 3] = .returned runtimeFailureValue world :=
  method_failure_invocation ambient reference 3 false shim zero nonnull world returned (by decide) (by decide)

example (ambient : Frame) (reference : NativeReferenceMachine.Reference) (shim zero null : NativeAllocatorLLBC.Body)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) NativeReferenceMachine.empty [] =
      .returned (.scalar .unit) NativeReferenceMachine.empty) :
    NativeAllocatorLLBC.invokeValues
      (allocationMethod {ambient with world := NativeReferenceMachine.empty} false zero
        (runtimePositive (some 8) shim null runtimeSuccess)) NativeReferenceMachine.empty
      [.scalar (.reference false reference 0),capacityLayout 3] = .returned (runtimeSuccessValue ⟨8,some ⟨8,0⟩⟩ 3)
        (NativeAllocatorExecution.allocated NativeReferenceMachine.empty 8 ⟨3,1⟩) :=
  method_success_invocation _ reference 3 false (some 8) shim zero null _ _ _ (by decide) returned (by decide) (by decide)

private def constructorBorrowed : NativeReferenceMachine.State := NativeZstBorrow.granted NativeReferenceMachine.empty 64
private def constructorZeroed : NativeReferenceMachine.State :=
  (NativeAllocatorExecution.run constructorBorrowed .zeroed (some 8) 3 1).world

example (ambient : Frame) (shim : NativeAllocatorLLBC.Body)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) constructorBorrowed [] =
      .returned (.scalar .unit) constructorBorrowed) :
    NativeAllocatorLLBC.invokeValues
      (positiveConstructorFunction {ambient with world := NativeReferenceMachine.empty} false 64 (some 8) shim) NativeReferenceMachine.empty
      [.scalar (.usize 3),allocationModeValue false,allocatorValue,byteLayout] =
      .returned (positiveResultValue ⟨8,some ⟨8,0⟩⟩ 3) (NativeAllocatorExecution.allocated constructorBorrowed 8 ⟨3,1⟩) :=
  positive_constructor_invocation _ 3 false 64 (by decide) (some 8) shim _ _ _ (by decide) (by decide) (by decide)
    returned (by decide)

example (ambient : Frame) (shim : NativeAllocatorLLBC.Body)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) constructorBorrowed [] =
      .returned (.scalar .unit) constructorBorrowed) :
    NativeAllocatorLLBC.invokeValues
      (positiveConstructorFunction {ambient with world := NativeReferenceMachine.empty} true 64 (some 8) shim) NativeReferenceMachine.empty
      [.scalar (.usize 3),allocationModeValue true,allocatorValue,byteLayout] =
      .returned (positiveResultValue ⟨8,some ⟨8,0⟩⟩ 3) constructorZeroed :=
  positive_constructor_invocation _ 3 true 64 (by decide) (some 8) shim _ _ _ (by decide) (by decide) (by decide)
    returned (by decide)

example : NativeByteRange.loadRange constructorZeroed.pointers.heap.memory ⟨8,some ⟨8,0⟩⟩ ⟨3,1⟩ = some [0,0,0] := by decide

end HasteBootsVecCapacityArithmetic
