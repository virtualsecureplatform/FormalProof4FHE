namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC
open NativeReservationErrorFields (Kind)

theorem effect_handler_specializes (base : NativePointerStorage.Address) (overflow allocation : Body) (frame : Frame) :
    effectHandlerEval base (eval (handlerTail overflow allocation)) frame = handlerEval base overflow allocation frame := by
  have resumeEq (caller : Frame) (flow : Flow) :
      handledResume caller 2 (eval (handlerCleanup .resume)) (eval (handlerTail overflow allocation)) flow =
        handlerResume overflow allocation caller flow := by
    cases flow <;> rfl
  simp only [effectHandlerEval,handlerEval,resumeEq]

theorem effect_outer_specializes (base : NativePointerStorage.Address) (overflow allocation : Body) (frame : Frame) :
    effectOuterErrorEval base (fun placement => handlerEval placement overflow allocation) frame =
      outerErrorEval base overflow allocation frame := rfl

theorem effect_root_specializes (world : NativeReferenceMachine.State) (base : NativePointerStorage.Address)
    (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body)
    (overflow allocation : Body) (capacity : NativeWord64Memory.Word) :
    effectRootInvoke world base address outcome shim (fun placement => handlerEval placement overflow allocation) capacity =
      handledRootInvoke world base address outcome shim overflow allocation capacity := rfl

theorem effect_raw_tail_success (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer) (nonnull : pointer.address.val ≠ 0)
    (base : NativePointerStorage.Address) (handler : NativePointerStorage.Address → Frame → Flow) (cold : Body) :
    effectRawTail base handler cold (positiveRawCallerReturned ambient capacity world pointer) =
      .returned (positiveRawValue pointer capacity) world := by
  have selected : selectChoice (positiveRawCallerReturned ambient capacity world pointer) 4 [] 8 = some false := by
    simp [selectChoice,positiveRawCallerReturned,rawCallerMoved,rawCallerTypes,layoutTypes,calleeEntryAmbient,
      positiveResultValue,NativeRecordValues.typeAt,NativeRecordValues.sideAt]
  have legacy := positive_raw_caller_tail ambient capacity world pointer nonnull .done cold
  rw [handled_tail_legacy,selected] at legacy
  simpa only [effectRawTail,selected,Bool.false_eq_true,ite_false,handledContinue] using legacy

theorem effect_raw_eval_success (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body)
    (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer) (nonnull : pointer.address.val ≠ 0)
    (base : NativePointerStorage.Address) (handler : NativePointerStorage.Address → Frame → Flow)
    (returned : NativeAllocatorLLBC.invokeValues (unifiedConstructorFunction ambient false address outcome shim) ambient.world
      [.scalar (.usize capacity),uninitializedValue,allocatorValue,byteLayout] = .returned (positiveResultValue pointer capacity) world) :
    effectRawEval ambient base address outcome shim handler (rawCallerFrame ambient capacity) =
      .returned (positiveRawValue pointer capacity) world := by
  rw [effectRawEval,unified_raw_caller_resumes _ _ _ _ _ _ _ _ _ nonnull returned]
  exact effect_raw_tail_success ambient capacity world pointer nonnull base handler _

theorem effect_outer_error_no_normal (base : NativePointerStorage.Address) (handler : NativePointerStorage.Address → Frame → Flow) (frame changed : Frame) :
    effectOuterErrorEval base handler frame ≠ .normal changed := by
  intro h
  simp only [effectOuterErrorEval,outerErrorPrefix,handledContinue,handledCall,handledResume,outerErrorCleanup,eval] at h
  repeat' (first | split at h | cases h)
  all_goals simp_all

theorem effect_outer_error_no_return (base : NativePointerStorage.Address) (handler : NativePointerStorage.Address → Frame → Flow) (frame : Frame)
    (value : NativeRecordValues.Value) (world : NativeReferenceMachine.State) :
    effectOuterErrorEval base handler frame ≠ .returned value world := by
  intro h
  simp only [effectOuterErrorEval,outerErrorPrefix,handledContinue,handledCall,handledResume,outerErrorCleanup,eval] at h
  repeat' (first | split at h | cases h)

theorem effect_outer_error_terminal (base : NativePointerStorage.Address) (handler : NativePointerStorage.Address → Frame → Flow) (frame : Frame) :
    handledTerminal (effectOuterErrorEval base handler frame) := by
  cases actual : effectOuterErrorEval base handler frame with
  | normal changed => exact False.elim (effect_outer_error_no_normal base handler frame changed actual)
  | returned value world => exact False.elim (effect_outer_error_no_return base handler frame value world actual)
  | invalid world => trivial
  | unwind world => trivial
  | unsupported source world => trivial

theorem effect_raw_tail_error (start world : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word)
    (kind : Kind) (base : NativePointerStorage.Address) (handler : NativePointerStorage.Address → Frame → Flow) (cold : Body) :
    effectRawTail base handler cold (handledRawErrorFrame start capacity world kind) =
      effectOuterErrorEval base handler (handledRawErrorFrame start capacity world kind) := by
  have selected : selectChoice (handledRawErrorFrame start capacity world kind) 4 [] 8 = some true := by
    simp [handledRawErrorFrame,handledErrorValue,rawCallerMoved,rawCallerTypes,rawEntryAmbient,handledAmbient,
      layoutTypes,calleeEntryAmbient,selectChoice,NativeRecordValues.typeAt,NativeRecordValues.sideAt]
  simp only [effectRawTail,selected,ite_true]
  exact handled_continue_terminal _ _ (effect_outer_error_terminal base handler _)

theorem effect_raw_invocation_error (start world : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word)
    (kind : Kind) (valid : NativeReservationErrorLocal.Valid kind) (base : NativePointerStorage.Address)
    (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body)
    (handler : NativePointerStorage.Address → Frame → Flow)
    (returned : NativeAllocatorLLBC.invokeValues
      (unifiedConstructorFunction (rawEntryAmbient (handledAmbient start)) false address outcome shim) start
      [.scalar (.usize capacity),uninitializedValue,allocatorValue,byteLayout] = .returned (handledErrorValue kind) world) :
    effectRawInvoke start base address outcome shim handler capacity =
      effectOuterErrorEval base handler (handledRawErrorFrame start capacity world kind) := by
  have initialized := unified_raw_caller_initialized (handledAmbient start) capacity address outcome shim
  change initial (rawCallerTypes (rawEntryAmbient (handledAmbient start))) 3 _ start = _ at initialized
  rw [effectRawInvoke,handledInvoke,initialized]
  change settle start (effectRawEval (rawEntryAmbient (handledAmbient start)) base address outcome shim handler
    (rawCallerFrame (rawEntryAmbient (handledAmbient start)) capacity)) = _
  rw [effectRawEval,handled_raw_constructor_error start world capacity kind valid address outcome shim _ returned]
  simp only [handledContinue]
  rw [effect_raw_tail_error]
  exact handled_settle_terminal _ _ (effect_outer_error_terminal base handler _)

theorem effect_vec_terminal (start : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word)
    (base : NativePointerStorage.Address) (address : NativeWord64Memory.Word)
    (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) (handler : NativePointerStorage.Address → Frame → Flow)
    (flow : Flow) (terminal : handledTerminal flow)
    (called : effectRawInvoke start base address outcome shim handler capacity = flow) :
    effectVecEval (handledAmbient start) base address outcome shim handler
      (vecCallerFrame (handledAmbient start) capacity) = flow := by
  rw [effectVecEval,vec_caller_prefix_exact]
  simp only [eval,handledContinue]
  rw [handled_call_invokes,vec_caller_arguments]
  change handledResume (vecCallerMoved (handledAmbient start) capacity) 3
    (eval (.dead 1 .resume)) (eval vecCallerTail)
    (effectRawInvoke start base address outcome shim handler capacity) = flow
  rw [called]
  cases flow with
  | normal changed => cases terminal
  | returned value world => cases terminal
  | invalid world => rfl
  | unsupported source world => rfl
  | unwind world => simp [handledResume,eval,storageDead,vecCallerMoved]

theorem effect_vec_invocation_terminal (start : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word)
    (base : NativePointerStorage.Address) (address : NativeWord64Memory.Word)
    (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) (handler : NativePointerStorage.Address → Frame → Flow)
    (flow : Flow) (terminal : handledTerminal flow)
    (called : effectRawInvoke start base address outcome shim handler capacity = flow) :
    handledInvoke (vecCallerTypes (handledAmbient start)) 1
      (effectVecEval (handledAmbient start) base address outcome shim handler) start [.scalar (.usize capacity)] = flow := by
  have initialized := unified_vec_caller_initialized (handledAmbient start) capacity address outcome shim
  change initial (vecCallerTypes (handledAmbient start)) 1 _ start = _ at initialized
  rw [handledInvoke,initialized]
  change settle start (effectVecEval (handledAmbient start) base address outcome shim handler
    (vecCallerFrame (handledAmbient start) capacity)) = flow
  rw [effect_vec_terminal start capacity base address outcome shim handler flow terminal called]
  exact handled_settle_terminal _ flow terminal

theorem effect_root_terminal (start : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word)
    (base : NativePointerStorage.Address) (address : NativeWord64Memory.Word)
    (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) (handler : NativePointerStorage.Address → Frame → Flow)
    (flow : Flow) (terminal : handledTerminal flow)
    (called : effectRawInvoke start base address outcome shim handler capacity = flow) :
    effectRootInvoke start base address outcome shim handler capacity = flow := by
  have initialized := unified_capacity_root_initialized (handledAmbient start) capacity address outcome shim
  change initial (capacityRootTypes (handledAmbient start)) 1 _ start = _ at initialized
  rw [effectRootInvoke,handledInvoke,initialized]
  change settle start (effectRootEval (handledAmbient start) base address outcome shim handler
    (capacityRootFrame (handledAmbient start) capacity)) = flow
  rw [effectRootEval,capacity_root_prefix]
  simp only [eval,handledContinue]
  rw [handled_call_invokes,capacity_root_arguments]
  change settle start (handledResume (capacityRootMoved (handledAmbient start) capacity) 0
    (eval (.dead 1 .resume)) (eval capacityRootTail)
    (handledInvoke (vecCallerTypes (handledAmbient start)) 1
      (effectVecEval (handledAmbient start) base address outcome shim handler) start [.scalar (.usize capacity)])) = flow
  rw [effect_vec_invocation_terminal start capacity base address outcome shim handler flow terminal called]
  cases flow with
  | normal changed => cases terminal
  | returned value world => cases terminal
  | invalid world => rfl
  | unsupported source world => rfl
  | unwind world => simp [handledResume,eval,storageDead,capacityRootMoved,settle]

theorem effect_root_rejected (start : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word)
    (base : NativePointerStorage.Address) (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0)
    (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) (handler : NativePointerStorage.Address → Frame → Flow)
    (large : 2^63 ≤ capacity.val) (valid : NativeReferenceMachine.WellFormed start) :
    effectRootInvoke start base address outcome shim handler capacity =
      effectOuterErrorEval base handler
        (handledRawErrorFrame start capacity (NativeZstBorrow.grantedExclusive start address) .capacityOverflow) := by
  apply effect_root_terminal _ _ _ _ _ _ _ _ (effect_outer_error_terminal _ _ _)
  apply effect_raw_invocation_error start _ capacity .capacityOverflow (by trivial) base address outcome shim handler
  exact unified_constructor_rejected (rawEntryAmbient (handledAmbient start)) capacity false address nonzero outcome shim large valid

theorem effect_root_allocation_failure (start : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word)
    (base : NativePointerStorage.Address) (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0)
    (shim : NativeAllocatorLLBC.Body) (handler : NativePointerStorage.Address → Frame → Flow) (world : NativeReferenceMachine.State)
    (valid : NativeReferenceMachine.WellFormed start) (positive : 0 < capacity.val) (bounded : capacity.val < 2^63)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) (NativeZstBorrow.granted start address) [] =
      .returned (.scalar .unit) world) :
    effectRootInvoke start base address none shim handler capacity =
      effectOuterErrorEval base handler
        (handledRawErrorFrame start capacity (NativeZstBorrow.grantedExclusive world address) (.allocationError capacity 1)) := by
  have kindValid : NativeReservationErrorLocal.Valid (.allocationError capacity 1) := by
    refine ⟨by decide,⟨?_,?_⟩⟩
    · change 1 ∈ (List.range 64).map (fun exponent => 2 ^ exponent)
      decide
    · change capacity.val + (1-1) ≤ 2^63-1
      omega
  apply effect_root_terminal _ _ _ _ _ _ _ _ (effect_outer_error_terminal _ _ _)
  apply effect_raw_invocation_error start _ capacity (.allocationError capacity 1) kindValid base address none shim handler
  exact unified_constructor_failure (rawEntryAmbient (handledAmbient start)) capacity false address nonzero shim world valid positive bounded returned

theorem effect_raw_invocation_success (start world : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word)
    (base : NativePointerStorage.Address) (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (handler : NativePointerStorage.Address → Frame → Flow) (pointer : NativePointerStorage.Pointer)
    (nonnull : pointer.address.val ≠ 0)
    (returned : NativeAllocatorLLBC.invokeValues
      (unifiedConstructorFunction (rawEntryAmbient (handledAmbient start)) false address outcome shim) start
      [.scalar (.usize capacity),uninitializedValue,allocatorValue,byteLayout] = .returned (positiveResultValue pointer capacity) world) :
    effectRawInvoke start base address outcome shim handler capacity =
      .returned (positiveRawValue pointer capacity) world := by
  have initialized := unified_raw_caller_initialized (handledAmbient start) capacity address outcome shim
  change initial (rawCallerTypes (rawEntryAmbient (handledAmbient start))) 3 _ start = _ at initialized
  rw [effectRawInvoke,handledInvoke,initialized]
  change settle start (effectRawEval (rawEntryAmbient (handledAmbient start)) base address outcome shim handler
    (rawCallerFrame (rawEntryAmbient (handledAmbient start)) capacity)) = _
  rw [effect_raw_eval_success _ _ _ _ _ _ _ nonnull base handler returned]
  rfl

theorem effect_vec_invocation_success (start world : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word)
    (base : NativePointerStorage.Address) (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (handler : NativePointerStorage.Address → Frame → Flow) (pointer : NativePointerStorage.Pointer)
    (nonnull : pointer.address.val ≠ 0)
    (called : effectRawInvoke start base address outcome shim handler capacity =
      .returned (positiveRawValue pointer capacity) world) :
    handledInvoke (vecCallerTypes (handledAmbient start)) 1
      (effectVecEval (handledAmbient start) base address outcome shim handler) start [.scalar (.usize capacity)] =
        .returned (positiveVecValue pointer capacity) world := by
  let ambient := handledAmbient start
  have initialized := unified_vec_caller_initialized ambient capacity address outcome shim
  change initial (vecCallerTypes ambient) 1 _ start = _ at initialized
  rw [handledInvoke,initialized]
  change settle start (effectVecEval ambient base address outcome shim handler
    (vecCallerFrame ambient capacity)) = _
  rw [effectVecEval,vec_caller_prefix_exact]
  simp only [eval,handledContinue]
  rw [handled_call_invokes,vec_caller_arguments]
  change settle start (handledResume (vecCallerMoved ambient capacity) 3 (eval (.dead 1 .resume)) (eval vecCallerTail)
    (effectRawInvoke start base address outcome shim handler capacity)) = _
  rw [called]
  have resumed : handledResume (vecCallerMoved ambient capacity) 3 (eval (.dead 1 .resume)) (eval vecCallerTail)
      (.returned (positiveRawValue pointer capacity) world) = eval vecCallerTail (positiveVecCallerReturned ambient capacity world pointer) := by
    simp [handledResume,positiveVecCallerReturned,write,vecCallerMoved,vecCallerTypes,layoutTypes,calleeEntryAmbient,
      positiveRawValue,runtimeThinValue,allocatorValue,nonnull,NativeRecordValues.fits,NativeRecordValues.complete,
      NativeRecordValues.compatible,NativeSliceLLBC.fits]
  rw [resumed,positive_vec_caller_tail ambient capacity world pointer nonnull]
  rfl

theorem effect_root_success_from_raw (start world : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word)
    (base : NativePointerStorage.Address) (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (handler : NativePointerStorage.Address → Frame → Flow) (pointer : NativePointerStorage.Pointer)
    (nonnull : pointer.address.val ≠ 0)
    (called : effectRawInvoke start base address outcome shim handler capacity =
      .returned (positiveRawValue pointer capacity) world) :
    effectRootInvoke start base address outcome shim handler capacity =
      .returned (positiveVecValue pointer capacity) world := by
  let ambient := handledAmbient start
  have initialized := unified_capacity_root_initialized ambient capacity address outcome shim
  change initial (capacityRootTypes ambient) 1 _ start = _ at initialized
  rw [effectRootInvoke,handledInvoke,initialized]
  change settle start (effectRootEval ambient base address outcome shim handler
    (capacityRootFrame ambient capacity)) = _
  rw [effectRootEval,capacity_root_prefix]
  simp only [eval,handledContinue]
  rw [handled_call_invokes,capacity_root_arguments]
  change settle start (handledResume (capacityRootMoved ambient capacity) 0 (eval (.dead 1 .resume)) (eval capacityRootTail)
    (handledInvoke (vecCallerTypes ambient) 1 (effectVecEval ambient base address outcome shim handler)
      start [.scalar (.usize capacity)])) = _
  rw [effect_vec_invocation_success start world capacity base address outcome shim handler pointer nonnull called]
  have resumed : handledResume (capacityRootMoved ambient capacity) 0 (eval (.dead 1 .resume)) (eval capacityRootTail)
      (.returned (positiveVecValue pointer capacity) world) = eval capacityRootTail (positiveCapacityRootReturned ambient capacity world pointer) := by
    simp [handledResume,positiveCapacityRootReturned,write,capacityRootMoved,capacityRootTypes,vecCallerTypes,layoutTypes,
      calleeEntryAmbient,positiveVecValue,positiveRawValue,runtimeThinValue,allocatorValue,nonnull,NativeRecordValues.fits,
      NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]
  rw [resumed,positive_capacity_root_tail ambient capacity world pointer nonnull]
  rfl

theorem effect_root_success (start : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word)
    (base : NativePointerStorage.Address) (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0)
    (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) (handler : NativePointerStorage.Address → Frame → Flow)
    (shimWorld resultWorld : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (positive : 0 < capacity.val) (bounded : capacity.val < 2^63) (nonnull : pointer.address.val ≠ 0)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) (NativeZstBorrow.granted start address) [] =
      .returned (.scalar .unit) shimWorld)
    (allocated : NativeAllocatorExecution.run shimWorld .allocate outcome capacity 1 = .value (.raw ⟨pointer,none⟩) resultWorld) :
    effectRootInvoke start base address outcome shim handler capacity =
      .returned (positiveVecValue pointer capacity) resultWorld := by
  apply effect_root_success_from_raw start resultWorld capacity base address outcome shim handler pointer nonnull
  apply effect_raw_invocation_success start resultWorld capacity base address outcome shim handler pointer nonnull
  exact unified_constructor_success (rawEntryAmbient (handledAmbient start)) capacity false address nonzero outcome shim
    shimWorld resultWorld pointer positive bounded nonnull returned allocated

theorem effect_root_zero (start : NativeReferenceMachine.State) (base : NativePointerStorage.Address)
    (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body)
    (handler : NativePointerStorage.Address → Frame → Flow) :
    effectRootInvoke start base address outcome shim handler 0 = .returned zeroVecValue start := by
  apply effect_root_success_from_raw start start 0 base address outcome shim handler ⟨1,none⟩ (by decide)
  apply effect_raw_invocation_success start start 0 base address outcome shim handler ⟨1,none⟩ (by decide)
  exact unified_constructor_zero (rawEntryAmbient (handledAmbient start)) false address outcome shim


end HasteBootsVecCapacityArithmetic
