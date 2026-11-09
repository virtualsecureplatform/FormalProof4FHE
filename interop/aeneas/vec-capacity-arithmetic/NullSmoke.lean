namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

example : runtimeResidualDiscriminant.valid = true := runtime_residual_descriptor_valid

example : runtimeResidualDiscriminant.read runtimeResidualType = some (.scalar (.usize 1)) := rfl

example (ambient : Frame) (world : NativeReferenceMachine.State) :
    NativeRecordLLBC.read (runtimeNullPrepared ambient 3 false world) 10 [] = none := by
  simp [runtimeNullPrepared,runtimeInspectedFrame,runtimeAllocatedFrame,runtimeArgumentsFrame,runtimeAlignmentFrame,
    runtimeAfterShim,implementationPrepared,NativeRecordLLBC.read]

example (ambient : Frame) (world : NativeReferenceMachine.State) :
    (runtimeNullChecked ambient 3 true world).slots[33]? = some (.live (some .uninit)) := by
  simp [runtimeNullChecked,runtimeNullPrepared,runtimeInspectedFrame,runtimeAllocatedFrame,runtimeArgumentsFrame,
    runtimeAlignmentFrame,runtimeAfterShim,implementationPrepared]

example (ambient : Frame) (world : NativeReferenceMachine.State) :
    NativeAllocatorLLBC.eval runtimeNull (runtimeInspectedFrame ambient 3 false world ⟨0,none⟩) =
      .returned runtimeFailureValue world := runtime_null_exact ambient 3 false world

example (ambient : Frame) (world : NativeReferenceMachine.State) :
    NativeAllocatorLLBC.eval runtimeNull (runtimeInspectedFrame ambient 3 true world ⟨0,none⟩) =
      .returned runtimeFailureValue world := runtime_null_exact ambient 3 true world

example (ambient : Frame) (shim zero nonnull : NativeAllocatorLLBC.Body) (world : NativeReferenceMachine.State)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) ambient.world [] = .returned (.scalar .unit) world) :
    NativeAllocatorLLBC.invokeValues (implementationFunction ambient zero (runtimePositive none shim runtimeNull nonnull))
      ambient.world [capacityLayout 3,.boolean false] = .returned runtimeFailureValue world :=
  runtime_failure_invocation ambient 3 false shim zero nonnull world returned (by decide) (by decide)

example (ambient : Frame) (shim zero nonnull : NativeAllocatorLLBC.Body) (world : NativeReferenceMachine.State)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) ambient.world [] = .returned (.scalar .unit) world) :
    NativeAllocatorLLBC.invokeValues (implementationFunction ambient zero (runtimePositive none shim runtimeNull nonnull))
      ambient.world [capacityLayout 3,.boolean true] = .returned runtimeFailureValue world :=
  runtime_failure_invocation ambient 3 true shim zero nonnull world returned (by decide) (by decide)

end HasteBootsVecCapacityArithmetic
