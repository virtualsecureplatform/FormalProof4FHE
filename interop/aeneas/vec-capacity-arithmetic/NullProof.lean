namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

theorem runtime_residual_descriptor_valid : runtimeResidualDiscriminant.valid = true := by decide

theorem runtime_null_prefix (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (world : NativeReferenceMachine.State) (next : Body) :
    eval (runtimeNullPrefix next) (runtimeInspectedFrame ambient capacity zeroed world ⟨0,none⟩) =
      eval next (runtimeNullPrepared ambient capacity zeroed world) := by
  cases zeroed <;>
    simp [runtimeNullPrefix,runtimeNullPrepared,runtimeInspectedFrame,runtimeAllocatedFrame,runtimeArgumentsFrame,
      runtimeAlignmentFrame,runtimeAfterShim,implementationPrepared,implementationTypes,runtimePointerOptionType,
      runtimePointerResultType,runtimeErrorType,eval,evalRvalue,evalArgs,evalOperand,storageLive,storageDead,
      NativeRecordLLBC.read,write,retag,NativeSliceLLBC.retagValue,NativeRecordValues.typeAt,NativeRecordValues.get,
      NativeRecordValues.replace,NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,
      NativeSliceLLBC.fits]

theorem runtime_null_check (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (world : NativeReferenceMachine.State) (next : Body) :
    eval (runtimeNullCheck next) (runtimeNullPrepared ambient capacity zeroed world) =
      eval next (runtimeNullChecked ambient capacity zeroed world) := by
  cases zeroed <;>
    simp [runtimeNullCheck,runtimeNullPrepared,runtimeNullChecked,runtimeInspectedFrame,runtimeAllocatedFrame,
      runtimeArgumentsFrame,runtimeAlignmentFrame,runtimeAfterShim,implementationPrepared,implementationTypes,
      eval,evalRvalue,evalKnownDiscriminant,ZeroSizeEnum.read,runtimeResidualDiscriminant,ZeroSizeEnum.valid,
      runtimeResidualType,expr_equal,evalArithmetic,NativeRecordArithmetic.eval,evalArgs,evalOperand,evalBooleanOperand,
      write,NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.replace,
      NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeRecordValues.copyable,NativeSliceLLBC.fits]

theorem runtime_null_tail (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (world : NativeReferenceMachine.State) :
    eval runtimeNullTail (runtimeNullChecked ambient capacity zeroed world) = .returned runtimeFailureValue world := by
  cases zeroed <;>
    simp [runtimeNullTail,runtimeNullChecked,runtimeFailureValue,runtimeNullPrepared,runtimeInspectedFrame,
      runtimeAllocatedFrame,runtimeArgumentsFrame,runtimeAlignmentFrame,runtimeAfterShim,implementationPrepared,
      implementationTypes,runtimeErrorType,allocationResultType,eval,evalRvalue,evalArgs,evalOperand,storageLive,
      storageDead,NativeRecordLLBC.read,write,retag,NativeSliceLLBC.retagValue,NativeRecordValues.typeAt,
      NativeRecordValues.get,NativeRecordValues.replace,NativeRecordValues.fits,NativeRecordValues.complete,
      NativeRecordValues.compatible,NativeSliceLLBC.fits]

theorem runtime_null_exact (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (world : NativeReferenceMachine.State) :
    NativeAllocatorLLBC.eval runtimeNull (runtimeInspectedFrame ambient capacity zeroed world ⟨0,none⟩) =
      .returned runtimeFailureValue world := by
  rw [runtimeNull,NativeAllocatorLLBC.legacy_done,runtime_null_prefix,runtime_null_check,runtime_null_tail]

theorem runtime_positive_failure (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (shim nonnull : NativeAllocatorLLBC.Body) (world : NativeReferenceMachine.State)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) ambient.world [] = .returned (.scalar .unit) world)
    (valid : (NativeAllocatorExecution.request capacity 1).Valid) (positive : 0 < capacity.val) :
    NativeAllocatorLLBC.eval (runtimePositive none shim runtimeNull nonnull) (implementationPrepared ambient capacity zeroed) =
      .returned runtimeFailureValue world := by
  have failed := NativeAllocatorExecution.failure_result world (if zeroed then .zeroed else .allocate) capacity 1 valid positive
  rw [runtime_positive_result _ _ _ _ _ _ _ _ _ ⟨0,none⟩ returned failed]
  exact runtime_null_exact ambient capacity zeroed world

theorem runtime_failure_invocation (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (shim zero nonnull : NativeAllocatorLLBC.Body) (world : NativeReferenceMachine.State)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) ambient.world [] = .returned (.scalar .unit) world)
    (valid : (NativeAllocatorExecution.request capacity 1).Valid) (positive : 0 < capacity.val) :
    NativeAllocatorLLBC.invokeValues (implementationFunction ambient zero (runtimePositive none shim runtimeNull nonnull))
      ambient.world [capacityLayout capacity,.boolean zeroed] = .returned runtimeFailureValue world := by
  have nonzero : capacity ≠ 0 := by intro same; subst capacity; simp at positive
  rw [implementation_positive_invocation _ _ _ nonzero,runtime_positive_failure _ _ _ _ _ _ returned valid positive]
  rfl

end HasteBootsVecCapacityArithmetic
