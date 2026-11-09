namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

theorem runtime_success_thin (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer) (next : Body) :
    eval (runtimeSuccessThin next) (runtimeInspectedFrame ambient capacity zeroed world pointer) =
      eval next (runtimeThinFrame ambient capacity zeroed world pointer) := by
  cases zeroed <;>
    simp [runtimeSuccessThin,runtimeThinFrame,runtimeThinValue,runtimeInspectedFrame,runtimeAllocatedFrame,
      runtimeArgumentsFrame,runtimeAlignmentFrame,runtimeAfterShim,implementationPrepared,implementationTypes,
      runtimeThinPointerType,runtimePointerOptionType,runtimePointerResultType,runtimeControlType,
      eval,evalRvalue,evalArgs,evalOperand,storageLive,storageDead,NativeRecordLLBC.read,write,retag,
      NativeSliceLLBC.retagValue,NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.replace,
      NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeRecordValues.copyable,NativeSliceLLBC.fits]

theorem runtime_success_slice (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer) (next : Body) :
    eval (runtimeSuccessSlice next) (runtimeThinFrame ambient capacity zeroed world pointer) =
      eval next (runtimeSliceFrame ambient capacity zeroed world pointer) := by
  cases zeroed <;>
    simp [runtimeSuccessSlice,runtimeSliceFrame,runtimeThinFrame,runtimeThinValue,runtimeInspectedFrame,runtimeAllocatedFrame,
      runtimeArgumentsFrame,runtimeAlignmentFrame,runtimeAfterShim,implementationPrepared,implementationTypes,runtimeThinPointerType,
      eval,evalRvalue,evalParts,partsValue,NativeSliceLLBC.partsValue,evalArgs,evalOperand,storageLive,storageDead,
      NativeRecordLLBC.read,write,retag,NativeRecordValues.typeAt,NativeRecordValues.get,
      NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeRecordValues.copyable,NativeSliceLLBC.fits]

theorem runtime_success_result (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer) (next : Body) :
    eval (runtimeSuccessResult next) (runtimeSliceFrame ambient capacity zeroed world pointer) =
      eval next (runtimeSuccessFrame ambient capacity zeroed world pointer) := by
  cases zeroed <;>
    simp [runtimeSuccessResult,runtimeSuccessFrame,runtimeSuccessValue,runtimeSliceFrame,runtimeThinFrame,runtimeThinValue,
      runtimeInspectedFrame,runtimeAllocatedFrame,runtimeArgumentsFrame,runtimeAlignmentFrame,runtimeAfterShim,
      implementationPrepared,implementationTypes,allocationResultType,eval,evalRvalue,evalArgs,evalOperand,storageDead,
      NativeRecordLLBC.read,write,NativeRecordValues.typeAt,NativeRecordValues.get,
      NativeRecordValues.replace,NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,
      NativeRecordValues.copyable,NativeSliceLLBC.fits]

theorem runtime_success_exact (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer) :
    NativeAllocatorLLBC.eval runtimeSuccess (runtimeInspectedFrame ambient capacity zeroed world pointer) =
      .normal (runtimeSuccessFrame ambient capacity zeroed world pointer) := by
  rw [runtimeSuccess,NativeAllocatorLLBC.legacy_done,runtime_success_thin,runtime_success_slice,runtime_success_result]
  rfl

theorem runtime_positive_success (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (outcome : Option NativePointerStorage.Address) (shim null : NativeAllocatorLLBC.Body)
    (shimWorld resultWorld : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) ambient.world [] = .returned (.scalar .unit) shimWorld)
    (allocated : NativeAllocatorExecution.run shimWorld (if zeroed then .zeroed else .allocate) outcome capacity 1 =
      .value (.raw ⟨pointer,none⟩) resultWorld) (nonnull : pointer.address ≠ 0) :
    NativeAllocatorLLBC.eval (runtimePositive outcome shim null runtimeSuccess) (implementationPrepared ambient capacity zeroed) =
      .normal (runtimeSuccessFrame ambient capacity zeroed resultWorld pointer) := by
  rw [runtime_positive_result _ _ _ _ _ _ _ _ _ _ returned allocated,ite_eq_right nonnull]
  exact runtime_success_exact ambient capacity zeroed resultWorld pointer

theorem runtime_success_tail (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer) :
    eval implementationTail (runtimeSuccessFrame ambient capacity zeroed world pointer) =
      .returned (runtimeSuccessValue pointer capacity) world := by
  cases zeroed <;>
    simp [implementationTail,runtimeSuccessFrame,runtimeSuccessValue,runtimeSliceFrame,runtimeThinFrame,
      runtimeInspectedFrame,runtimeAllocatedFrame,runtimeArgumentsFrame,runtimeAlignmentFrame,runtimeAfterShim,
      implementationPrepared,implementationTypes,allocationResultType,eval,storageDead,NativeRecordLLBC.read,
      NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.fits,NativeRecordValues.complete,
      NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem runtime_positive_invocation (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (outcome : Option NativePointerStorage.Address) (shim zero null : NativeAllocatorLLBC.Body)
    (shimWorld resultWorld : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (positive : capacity ≠ 0)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) ambient.world [] = .returned (.scalar .unit) shimWorld)
    (allocated : NativeAllocatorExecution.run shimWorld (if zeroed then .zeroed else .allocate) outcome capacity 1 =
      .value (.raw ⟨pointer,none⟩) resultWorld) (nonnull : pointer.address ≠ 0) :
    NativeAllocatorLLBC.invokeValues
      (implementationFunction ambient zero (runtimePositive outcome shim null runtimeSuccess)) ambient.world
      [capacityLayout capacity,.boolean zeroed] = .returned (runtimeSuccessValue pointer capacity) resultWorld := by
  rw [implementation_positive_invocation _ _ _ positive,
    runtime_positive_success _ _ _ _ _ _ _ _ _ returned allocated nonnull]
  simp only [NativeAllocatorLLBC.continueWith,NativeAllocatorLLBC.legacy_done,runtime_success_tail]
  rfl

end HasteBootsVecCapacityArithmetic
