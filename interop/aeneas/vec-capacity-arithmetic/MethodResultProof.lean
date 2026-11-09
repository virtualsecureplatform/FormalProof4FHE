namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

theorem method_returned_record (ambient : Frame) (reference : NativeReferenceMachine.Reference)
    (capacity : NativeWord64Memory.Word) (zeroed : Bool) (zero positive : NativeAllocatorLLBC.Body)
    (fields : NativeRecordValues.Value) (world : NativeReferenceMachine.State)
    (fits : NativeRecordValues.fits allocationResultType (.record 15 fields) = true)
    (returned : NativeAllocatorLLBC.invokeValues (implementationFunction ambient zero positive) ambient.world
      [capacityLayout capacity,.boolean zeroed] = .returned (.record 15 fields) world) :
    NativeAllocatorLLBC.invokeValues (allocationMethod ambient zeroed zero positive) ambient.world
      [.scalar (.reference false reference 0),capacityLayout capacity] = .returned (.record 15 fields) world := by
  have complete : NativeRecordValues.complete (.record 15 fields) = true := (Bool.and_eq_true_iff.mp fits).1
  rw [method_invocation_forwarding,returned]
  simp [NativeAllocatorLLBC.resume,write,allocationMethodMoved,allocationMethodTypes,fits,complete,
    NativeAllocatorLLBC.legacy_done,eval,storageDead,NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,
    settle]

theorem method_success_invocation (ambient : Frame) (reference : NativeReferenceMachine.Reference)
    (capacity : NativeWord64Memory.Word) (zeroed : Bool) (outcome : Option NativePointerStorage.Address)
    (shim zero null : NativeAllocatorLLBC.Body) (shimWorld resultWorld : NativeReferenceMachine.State)
    (pointer : NativePointerStorage.Pointer) (positive : capacity ≠ 0)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) ambient.world [] = .returned (.scalar .unit) shimWorld)
    (allocated : NativeAllocatorExecution.run shimWorld (if zeroed then .zeroed else .allocate) outcome capacity 1 =
      .value (.raw ⟨pointer,none⟩) resultWorld) (nonnull : pointer.address ≠ 0) :
    NativeAllocatorLLBC.invokeValues
      (allocationMethod ambient zeroed zero (runtimePositive outcome shim null runtimeSuccess)) ambient.world
      [.scalar (.reference false reference 0),capacityLayout capacity] = .returned (runtimeSuccessValue pointer capacity) resultWorld := by
  apply method_returned_record
  · rfl
  · exact runtime_positive_invocation ambient capacity zeroed outcome shim zero null shimWorld resultWorld pointer
      positive returned allocated nonnull

theorem method_failure_invocation (ambient : Frame) (reference : NativeReferenceMachine.Reference)
    (capacity : NativeWord64Memory.Word) (zeroed : Bool) (shim zero nonnull : NativeAllocatorLLBC.Body)
    (world : NativeReferenceMachine.State)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) ambient.world [] = .returned (.scalar .unit) world)
    (valid : (NativeAllocatorExecution.request capacity 1).Valid) (positive : 0 < capacity.val) :
    NativeAllocatorLLBC.invokeValues
      (allocationMethod ambient zeroed zero (runtimePositive none shim runtimeNull nonnull)) ambient.world
      [.scalar (.reference false reference 0),capacityLayout capacity] = .returned runtimeFailureValue world := by
  apply method_returned_record
  · rfl
  · exact runtime_failure_invocation ambient capacity zeroed shim zero nonnull world returned valid positive

end HasteBootsVecCapacityArithmetic
