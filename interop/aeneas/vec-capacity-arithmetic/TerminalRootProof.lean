namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC
open NativeReservationErrorFields (Kind)

theorem effect_outer_invocation_terminal (start world : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word)
    (kind : Kind) (valid : NativeReservationErrorLocal.Valid kind) (base : NativePointerStorage.Address)
    (handler : NativePointerStorage.Address → Frame → Flow) (flow : Flow) (terminal : handledTerminal flow)
    (called : handledInvoke handlerTypes 1 (handler base) world
      [NativeReservationErrorLocal.encode reservationErrorTags kind] = flow) :
    effectOuterErrorEval base handler (handledRawErrorFrame start capacity world kind) = flow := by
  rw [effectOuterErrorEval,outer_error_prefix start world capacity kind valid]
  simp only [handledContinue]
  rw [handled_call_invokes,outer_error_arguments start world capacity kind valid]
  change handledResume (handledRawErrorMoved start capacity world kind) 8
    (eval (outerErrorCleanup .resume)) (eval (outerErrorCleanup (.dead 14 .abort)))
    (handledInvoke handlerTypes 1 (handler base) world [NativeReservationErrorLocal.encode reservationErrorTags kind]) = flow
  rw [called]
  cases flow with
  | normal changed => cases terminal
  | returned value final => cases terminal
  | invalid final => rfl
  | unsupported source final => rfl
  | unwind final => simp [handledResume,outerErrorCleanup,handledRawErrorMoved,handledRawErrorFrame,
      rawCallerMoved,rawEntryAmbient,handledAmbient,eval,storageDead]

theorem terminal_root_zero (fields : NativeRecordValues.Ty) (formatter panic : String → NativeReferenceMachine.State → Flow)
    (world : NativeReferenceMachine.State) (base : NativePointerStorage.Address) (address : NativeWord64Memory.Word)
    (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) :
    terminalRootInvoke fields formatter panic world base address outcome shim 0 = .returned zeroVecValue world :=
  effect_root_zero world base address outcome shim _

theorem terminal_root_success (fields : NativeRecordValues.Ty) (formatter panic : String → NativeReferenceMachine.State → Flow)
    (world : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word) (base : NativePointerStorage.Address)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (shimWorld resultWorld : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (positive : 0 < capacity.val) (bounded : capacity.val < 2^63) (nonnull : pointer.address.val ≠ 0)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) (NativeZstBorrow.granted world address) [] =
      .returned (.scalar .unit) shimWorld)
    (allocated : NativeAllocatorExecution.run shimWorld .allocate outcome capacity 1 = .value (.raw ⟨pointer,none⟩) resultWorld) :
    terminalRootInvoke fields formatter panic world base address outcome shim capacity =
      .returned (positiveVecValue pointer capacity) resultWorld :=
  effect_root_success world capacity base address nonzero outcome shim _ shimWorld resultWorld pointer
    positive bounded nonnull returned allocated

theorem terminal_root_rejected (fields : NativeRecordValues.Ty) (formatter panic : String → NativeReferenceMachine.State → Flow)
    (world : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word) (base : NativePointerStorage.Address)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (large : 2^63 ≤ capacity.val) (valid : NativeReferenceMachine.WellFormed world) :
    terminalRootInvoke fields formatter panic world base address outcome shim capacity =
      effectOuterErrorEval base (fun placement => effectHandlerEval placement (terminalHandlerTail fields formatter panic))
        (handledRawErrorFrame world capacity (NativeZstBorrow.grantedExclusive world address) .capacityOverflow) :=
  effect_root_rejected world capacity base address nonzero outcome shim _ large valid

theorem terminal_root_allocation_failure (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow)
    (world : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word) (base : NativePointerStorage.Address)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (shim : NativeAllocatorLLBC.Body)
    (shimWorld : NativeReferenceMachine.State) (valid : NativeReferenceMachine.WellFormed world)
    (positive : 0 < capacity.val) (bounded : capacity.val < 2^63)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) (NativeZstBorrow.granted world address) [] =
      .returned (.scalar .unit) shimWorld) :
    terminalRootInvoke fields formatter panic world base address none shim capacity =
      effectOuterErrorEval base (fun placement => effectHandlerEval placement (terminalHandlerTail fields formatter panic))
        (handledRawErrorFrame world capacity (NativeZstBorrow.grantedExclusive shimWorld address) (.allocationError capacity 1)) :=
  effect_root_allocation_failure world capacity base address nonzero shim _ shimWorld valid positive bounded returned

theorem terminal_root_rejected_dispatch (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow)
    (world : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word) (base : NativePointerStorage.Address)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (large : 2^63 ≤ capacity.val) (valid : NativeReferenceMachine.WellFormed world)
    (next : NativeReferenceMachine.State) (reference : NativeRecordValues.Value)
    (snapshot : NativeReservationErrorLocal.snapshotValue reservationErrorTags (NativeZstBorrow.grantedExclusive world address) base
      (NativeReservationErrorLocal.encode reservationErrorTags .capacityOverflow) = .value reference next) :
    ∃ final, terminalRootInvoke fields formatter panic world base address outcome shim capacity =
      terminalOverflowInvoke fields formatter panic final := by
  have returned := unified_constructor_rejected (rawEntryAmbient (handledAmbient world)) capacity false address nonzero outcome shim large valid
  change NativeAllocatorLLBC.invokeValues
    (unifiedConstructorFunction (rawEntryAmbient (handledAmbient world)) false address outcome shim) world
    [.scalar (.usize capacity),uninitializedValue,allocatorValue,byteLayout] =
      .returned capacityOverflowValue (NativeZstBorrow.grantedExclusive world address) at returned
  have resultValid := NativeSliceLLBC.reference_runs_wellFormed _ _ valid
    (NativeAllocatorLLBC.invokeValues_projects (unifiedConstructorFunction (rawEntryAmbient (handledAmbient world)) false address outcome shim)
      world [.scalar (.usize capacity),uninitializedValue,allocatorValue,byteLayout])
  rw [returned] at resultValid
  obtain ⟨final,called⟩ := terminal_handler_snapshot_dispatch fields formatter panic _ next base .capacityOverflow reference resultValid snapshot
  refine ⟨final,?_⟩
  rw [terminal_root_rejected fields formatter panic world capacity base address nonzero outcome shim large valid]
  exact effect_outer_invocation_terminal world _ capacity .capacityOverflow (by trivial) base _ _
    (terminal_overflow_invoke_terminal fields formatter panic final) called

theorem terminal_root_allocation_dispatch (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow)
    (world : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word) (base : NativePointerStorage.Address)
    (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0) (shim : NativeAllocatorLLBC.Body)
    (shimWorld : NativeReferenceMachine.State) (valid : NativeReferenceMachine.WellFormed world)
    (positive : 0 < capacity.val) (bounded : capacity.val < 2^63)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) (NativeZstBorrow.granted world address) [] =
      .returned (.scalar .unit) shimWorld)
    (next : NativeReferenceMachine.State) (reference : NativeRecordValues.Value)
    (snapshot : NativeReservationErrorLocal.snapshotValue reservationErrorTags (NativeZstBorrow.grantedExclusive shimWorld address) base
      (NativeReservationErrorLocal.encode reservationErrorTags (.allocationError capacity 1)) = .value reference next) :
    ∃ final, terminalRootInvoke fields formatter panic world base address none shim capacity =
      terminalAllocationInvoke fields formatter panic final (NativeReservationErrorLocal.layoutValue reservationErrorTags capacity 1) := by
  have kindValid : NativeReservationErrorLocal.Valid (.allocationError capacity 1) := by
    refine ⟨by decide,⟨?_,?_⟩⟩
    · change 1 ∈ (List.range 64).map (fun exponent => 2 ^ exponent)
      decide
    · change capacity.val + (1-1) ≤ 2^63-1
      omega
  have constructorReturned := unified_constructor_failure (rawEntryAmbient (handledAmbient world)) capacity false address nonzero shim shimWorld valid positive bounded returned
  change NativeAllocatorLLBC.invokeValues
    (unifiedConstructorFunction (rawEntryAmbient (handledAmbient world)) false address none shim) world
    [.scalar (.usize capacity),uninitializedValue,allocatorValue,byteLayout] =
      .returned (constructorErrorValue capacity) (NativeZstBorrow.grantedExclusive shimWorld address) at constructorReturned
  have resultValid := NativeSliceLLBC.reference_runs_wellFormed _ _ valid
    (NativeAllocatorLLBC.invokeValues_projects (unifiedConstructorFunction (rawEntryAmbient (handledAmbient world)) false address none shim)
      world [.scalar (.usize capacity),uninitializedValue,allocatorValue,byteLayout])
  rw [constructorReturned] at resultValid
  obtain ⟨final,called⟩ := terminal_handler_snapshot_dispatch fields formatter panic _ next base (.allocationError capacity 1) reference resultValid snapshot
  refine ⟨final,?_⟩
  rw [terminal_root_allocation_failure fields formatter panic world capacity base address nonzero shim shimWorld valid positive bounded returned]
  exact effect_outer_invocation_terminal world _ capacity (.allocationError capacity 1) kindValid base _ _
    (terminal_allocation_invoke_terminal fields formatter panic final capacity 1 kindValid.2) called

end HasteBootsVecCapacityArithmetic
