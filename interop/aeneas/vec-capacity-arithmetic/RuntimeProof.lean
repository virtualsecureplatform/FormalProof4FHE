namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

theorem runtime_shim_forwarding (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) :
    NativeAllocatorLLBC.eval (runtimeCallBranch zeroed outcome shim) (implementationPrepared ambient capacity zeroed) =
      NativeAllocatorLLBC.resume (implementationPrepared ambient capacity zeroed) (if zeroed then 18 else 20)
        (.legacy (runtimeShimUnwind zeroed) .done) (.legacy (runtimeAlignmentPrefix zeroed) (runtimeAfterAlignment zeroed outcome))
        (NativeAllocatorLLBC.invokeValues (runtimeShim shim) ambient.world []) := by
  have called := NativeAllocatorLLBC.eval_call (runtimeShim shim) (implementationPrepared ambient capacity zeroed)
    (if zeroed then 18 else 20) [] (.legacy (runtimeShimUnwind zeroed) .done)
    (.legacy (runtimeAlignmentPrefix zeroed) (runtimeAfterAlignment zeroed outcome))
  simp only [evalArgs] at called
  have same : (implementationPrepared ambient capacity zeroed).world = ambient.world := rfl
  rw [same] at called
  simpa only [runtimeCallBranch] using called

theorem runtime_alignment_exact (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (world : NativeReferenceMachine.State) :
    eval (runtimeAlignmentPrefix zeroed) (runtimeAfterShim ambient capacity zeroed world) =
      .normal (runtimeAlignmentFrame ambient capacity zeroed world) := by
  cases zeroed <;>
    simp [runtimeAlignmentPrefix,runtimeAfterShim,runtimeAlignmentFrame,implementationPrepared,implementationTypes,
      layoutTypes,calleeEntryAmbient,capacityLayout,byteAlignment,alignmentDiscriminants,eval,evalRvalue,evalOperand,
      storageLive,NativeRecordLLBC.read,write,retag,NativeSliceLLBC.retagValue,NativeRecordValues.typeAt,
      NativeRecordValues.get,NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,
      NativeRecordValues.copyable,NativeSliceLLBC.fits]

/-- A unit-returning shim is a premise about its actual modeled invocation,
not an assumed native implementation or an erased source boundary. -/
theorem runtime_after_returned_shim (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) (world : NativeReferenceMachine.State)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) ambient.world [] = .returned (.scalar .unit) world) :
    NativeAllocatorLLBC.eval (runtimeCallBranch zeroed outcome shim) (implementationPrepared ambient capacity zeroed) =
      NativeAllocatorLLBC.eval (runtimeAfterAlignment zeroed outcome) (runtimeAlignmentFrame ambient capacity zeroed world) := by
  have written : write {implementationPrepared ambient capacity zeroed with world} (if zeroed then 18 else 20) (.scalar .unit) =
      some (runtimeAfterShim ambient capacity zeroed world) := by
    cases zeroed <;>
      simp [write,runtimeAfterShim,implementationPrepared,implementationTypes,NativeRecordValues.fits,
        NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]
  rw [runtime_shim_forwarding,returned]
  simp only [NativeAllocatorLLBC.resume,written]
  exact NativeAllocatorLLBC.legacy_normal _ (runtime_alignment_exact ambient capacity zeroed world)

theorem runtime_allocator_arguments (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (world : NativeReferenceMachine.State) :
    evalArgs (runtimeAlignmentFrame ambient capacity zeroed world) (runtimeAllocatorArgs zeroed) =
      some ([.scalar (.usize capacity),byteAlignment],runtimeArgumentsFrame ambient capacity zeroed world) := by
  cases zeroed <;>
    simp [runtimeAllocatorArgs,runtimeAlignmentFrame,runtimeArgumentsFrame,runtimeAfterShim,implementationPrepared,
      implementationTypes,layoutTypes,calleeEntryAmbient,byteAlignment,alignmentDiscriminants,evalArgs,evalOperand,
      NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.replace,
      NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeRecordValues.copyable,NativeSliceLLBC.fits]

theorem runtime_allocation_result (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (outcome : Option NativePointerStorage.Address) (before after : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (result : NativeAllocatorExecution.run before (if zeroed then .zeroed else .allocate) outcome capacity 1 =
      .value (.raw ⟨pointer,none⟩) after) :
    NativeAllocatorLLBC.eval (runtimeAfterAlignment zeroed outcome) (runtimeAlignmentFrame ambient capacity zeroed before) =
      .normal (runtimeAllocatedFrame ambient capacity zeroed after pointer) := by
  have decoded : NativeAllocatorLLBC.decodeRequest 11 12 [.scalar (.usize capacity),byteAlignment] = some (capacity,1) :=
    NativeAllocatorLLBC.decode_request_exact 11 12 capacity 1
  rw [runtimeAfterAlignment,NativeAllocatorLLBC.eval,runtime_allocator_arguments]
  simp only [decoded]
  change (match NativeAllocatorExecution.run before (if zeroed then .zeroed else .allocate) outcome capacity 1 with
    | .invalid world => Flow.invalid world
    | .value value world => match write {runtimeArgumentsFrame ambient capacity zeroed before with world} 6 (.scalar value) with
      | none => Flow.invalid world
      | some changed => NativeAllocatorLLBC.eval (.legacy (.dead (if zeroed then 19 else 21) .done) .done) changed) = _
  rw [result]
  cases zeroed <;>
    simp [write,runtimeArgumentsFrame,runtimeAllocatedFrame,runtimeAlignmentFrame,runtimeAfterShim,
      implementationPrepared,implementationTypes,NativeRecordValues.fits,NativeRecordValues.complete,
      NativeRecordValues.compatible,NativeSliceLLBC.fits,NativeAllocatorLLBC.eval,eval,storageDead]

theorem runtime_inspection_exact (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer) (next : Body) :
    eval (runtimeInspectPrefix next) (runtimeAllocatedFrame ambient capacity zeroed world pointer) =
      eval next (runtimeInspectedFrame ambient capacity zeroed world pointer) := by
  cases zeroed <;>
    simp [runtimeInspectPrefix,runtimeAllocatedFrame,runtimeInspectedFrame,runtimeArgumentsFrame,runtimeAlignmentFrame,
      runtimeAfterShim,implementationPrepared,implementationTypes,eval,evalRvalue,evalRawAddress,rawAddressValue,
      evalOperand,storageLive,NativeRecordLLBC.read,write,NativeRecordValues.typeAt,NativeRecordValues.get,
      NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeRecordValues.copyable,NativeSliceLLBC.fits]

theorem runtime_mode_dispatch (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (outcome : Option NativePointerStorage.Address) (shim null nonnull : NativeAllocatorLLBC.Body) :
    NativeAllocatorLLBC.eval (runtimePositive outcome shim null nonnull) (implementationPrepared ambient capacity zeroed) =
      NativeAllocatorLLBC.continueWith (runtimePointerDispatch null nonnull)
        (NativeAllocatorLLBC.eval (runtimeCallBranch zeroed outcome shim) (implementationPrepared ambient capacity zeroed)) := by
  have selected : evalBooleanOperand (implementationPrepared ambient capacity zeroed) (.copy 2 []) =
      some (zeroed,implementationPrepared ambient capacity zeroed) := by
    simp [evalBooleanOperand,evalOperand,implementationPrepared,implementationTypes,NativeRecordLLBC.read,
      NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.fits,NativeRecordValues.complete,
      NativeRecordValues.compatible,NativeRecordValues.copyable]
  rw [runtimePositive,NativeAllocatorLLBC.eval,selected]
  cases zeroed <;> rfl

theorem runtime_pointer_dispatch (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer) (null nonnull : NativeAllocatorLLBC.Body) :
    NativeAllocatorLLBC.eval (runtimePointerDispatch null nonnull) (runtimeAllocatedFrame ambient capacity zeroed world pointer) =
      if pointer.address = 0 then NativeAllocatorLLBC.eval null (runtimeInspectedFrame ambient capacity zeroed world pointer)
      else NativeAllocatorLLBC.eval nonnull (runtimeInspectedFrame ambient capacity zeroed world pointer) := by
  have prepared : eval (runtimeInspectPrefix .done) (runtimeAllocatedFrame ambient capacity zeroed world pointer) =
      .normal (runtimeInspectedFrame ambient capacity zeroed world pointer) := by rw [runtime_inspection_exact]; rfl
  have selected : evalOperand (runtimeInspectedFrame ambient capacity zeroed world pointer) (.copy 23 []) =
      some (.scalar (.usize pointer.address),runtimeInspectedFrame ambient capacity zeroed world pointer) := by
    cases zeroed <;>
      simp [runtimeInspectedFrame,runtimeAllocatedFrame,runtimeArgumentsFrame,runtimeAlignmentFrame,runtimeAfterShim,
        implementationPrepared,implementationTypes,evalOperand,NativeRecordLLBC.read,NativeRecordValues.typeAt,
        NativeRecordValues.get,NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,
        NativeRecordValues.copyable,NativeSliceLLBC.fits]
  rw [runtimePointerDispatch,NativeAllocatorLLBC.legacy_normal _ prepared,NativeAllocatorLLBC.eval,selected]
  change NativeAllocatorLLBC.continueWith .done
    (if pointer.address = 0 then NativeAllocatorLLBC.eval null (runtimeInspectedFrame ambient capacity zeroed world pointer)
     else NativeAllocatorLLBC.eval nonnull (runtimeInspectedFrame ambient capacity zeroed world pointer)) = _
  exact NativeAllocatorLLBC.continue_done _

/-- Complete runtime control through the pointer check, conditional on the
actual shim invocation and the concrete allocator-machine result. -/
theorem runtime_positive_result (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (outcome : Option NativePointerStorage.Address) (shim null nonnull : NativeAllocatorLLBC.Body)
    (shimWorld resultWorld : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) ambient.world [] = .returned (.scalar .unit) shimWorld)
    (allocated : NativeAllocatorExecution.run shimWorld (if zeroed then .zeroed else .allocate) outcome capacity 1 =
      .value (.raw ⟨pointer,none⟩) resultWorld) :
    NativeAllocatorLLBC.eval (runtimePositive outcome shim null nonnull) (implementationPrepared ambient capacity zeroed) =
      if pointer.address = 0 then NativeAllocatorLLBC.eval null (runtimeInspectedFrame ambient capacity zeroed resultWorld pointer)
      else NativeAllocatorLLBC.eval nonnull (runtimeInspectedFrame ambient capacity zeroed resultWorld pointer) := by
  rw [runtime_mode_dispatch,runtime_after_returned_shim _ _ _ _ _ _ returned,
    runtime_allocation_result _ _ _ _ _ _ _ allocated]
  simp only [NativeAllocatorLLBC.continueWith]
  exact runtime_pointer_dispatch ambient capacity zeroed resultWorld pointer null nonnull

theorem runtime_shim_unsupported (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (outcome : Option NativePointerStorage.Address) (shim null nonnull : NativeAllocatorLLBC.Body)
    (label : String) (world : NativeReferenceMachine.State)
    (blocked : NativeAllocatorLLBC.invokeValues (runtimeShim shim) ambient.world [] = .unsupported label world) :
    NativeAllocatorLLBC.eval (runtimePositive outcome shim null nonnull) (implementationPrepared ambient capacity zeroed) =
      .unsupported label world := by
  rw [runtime_mode_dispatch,runtime_shim_forwarding,blocked]
  rfl

theorem runtime_shim_unwind_aborts (ambient : Frame) (capacity : NativeWord64Memory.Word) (zeroed : Bool)
    (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) (world : NativeReferenceMachine.State)
    (unwound : NativeAllocatorLLBC.invokeValues (runtimeShim shim) ambient.world [] = .unwind world) :
    NativeAllocatorLLBC.eval (runtimeCallBranch zeroed outcome shim) (implementationPrepared ambient capacity zeroed) = .invalid world := by
  rw [runtime_shim_forwarding,unwound]
  cases zeroed <;>
    simp [NativeAllocatorLLBC.resume,NativeAllocatorLLBC.eval,runtimeShimUnwind,eval,storageDead,implementationPrepared]

end HasteBootsVecCapacityArithmetic
