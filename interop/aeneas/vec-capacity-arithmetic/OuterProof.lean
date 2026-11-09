namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC
open NativeReservationErrorFields (Kind)

theorem handled_call_legacy (name : String) (classification : NativeByteDropCalls.Classification)
    (types : List NativeRecordValues.Ty) (argCount target : Nat) (args : List Operand)
    (callee unwind next : Body) (frame : Frame) :
    handledCall types argCount target args (eval callee) (eval unwind) (eval next) frame =
      eval (.call name classification types argCount target args callee unwind next) frame := rfl

theorem handled_call_invokes (types : List NativeRecordValues.Ty) (argCount target : Nat) (args : List Operand)
    (callee unwind next : Frame → Flow) (frame : Frame) :
    handledCall types argCount target args callee unwind next frame =
      match evalArgs frame args with
      | none => .invalid frame.world
      | some (values,caller) => handledResume caller target unwind next
          (handledInvoke types argCount callee caller.world values) := by
  cases arguments : evalArgs frame args with
  | none => simp only [handledCall,arguments]
  | some pair =>
    rcases pair with ⟨values,caller⟩
    cases initialized : initial types argCount values caller.world with
    | none => simp only [handledCall,arguments,initialized,handledInvoke,handledResume]
    | some entered =>
      have same := initial_world types argCount values caller.world entered initialized
      simp only [handledCall,arguments,initialized,handledInvoke,same]

theorem handled_tail_legacy (error cold : Body) (frame : Frame) :
    eval (rawCallerTail error cold) frame =
      match selectChoice frame 4 [] 8 with
      | none => .invalid frame.world
      | some side => handledContinue (eval (rawSuccessTail cold))
          (if side then eval error frame else .normal frame) := rfl

theorem handled_raw_tail_success (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer) (nonnull : pointer.address.val ≠ 0)
    (base : NativePointerStorage.Address) (overflow allocation cold : Body) :
    handledRawTail base overflow allocation cold (positiveRawCallerReturned ambient capacity world pointer) =
      .returned (positiveRawValue pointer capacity) world := by
  have selected : selectChoice (positiveRawCallerReturned ambient capacity world pointer) 4 [] 8 = some false := by
    simp [selectChoice,positiveRawCallerReturned,rawCallerMoved,rawCallerTypes,layoutTypes,calleeEntryAmbient,
      positiveResultValue,NativeRecordValues.typeAt,NativeRecordValues.sideAt]
  have legacy := positive_raw_caller_tail ambient capacity world pointer nonnull .done cold
  rw [handled_tail_legacy,selected] at legacy
  simpa only [handledRawTail,selected,Bool.false_eq_true,ite_false,handledContinue] using legacy

theorem handled_raw_eval_success (ambient : Frame) (capacity : NativeWord64Memory.Word)
    (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body)
    (world : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer) (nonnull : pointer.address.val ≠ 0)
    (base : NativePointerStorage.Address) (overflow allocation : Body)
    (returned : NativeAllocatorLLBC.invokeValues (unifiedConstructorFunction ambient false address outcome shim) ambient.world
      [.scalar (.usize capacity),uninitializedValue,allocatorValue,byteLayout] = .returned (positiveResultValue pointer capacity) world) :
    handledRawEval ambient base address outcome shim overflow allocation (rawCallerFrame ambient capacity) =
      .returned (positiveRawValue pointer capacity) world := by
  rw [handledRawEval,unified_raw_caller_resumes _ _ _ _ _ _ _ _ _ nonnull returned]
  exact handled_raw_tail_success ambient capacity world pointer nonnull base overflow allocation _

theorem handled_encode_properties (kind : Kind) (valid : NativeReservationErrorLocal.Valid kind) :
    NativeRecordValues.complete (NativeReservationErrorLocal.encode reservationErrorTags kind) = true ∧
    NativeRecordValues.compatible (HasteBootsReservationErrorKind.errorTypeFor reservationErrorTags)
      (NativeReservationErrorLocal.encode reservationErrorTags kind) = true := by
  have fits := handler_kind_fits kind valid
  simp only [NativeRecordValues.fits,Bool.and_eq_true] at fits
  simpa [NativeReservationErrorLocal.encode,HasteBootsReservationErrorKind.errorTypeFor,
    NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits] using fits

theorem handled_encode_retag (world : NativeReferenceMachine.State) (kind : Kind) :
    retag world (NativeReservationErrorLocal.encode reservationErrorTags kind) true .byte =
      .value (NativeReservationErrorLocal.encode reservationErrorTags kind) world := by
  cases kind <;> rfl

theorem outer_error_prefix (start world : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word)
    (kind : Kind) (valid : NativeReservationErrorLocal.Valid kind) :
    eval outerErrorPrefix (handledRawErrorFrame start capacity world kind) =
      .normal (handledRawErrorPrepared start capacity world kind) := by
  obtain ⟨complete,compatible⟩ := handled_encode_properties kind valid
  simp [outerErrorPrefix,handledRawErrorFrame,handledRawErrorPrepared,handledErrorValue,rawCallerMoved,rawCallerTypes,
    rawEntryAmbient,handledAmbient,layoutTypes,calleeEntryAmbient,eval,evalRvalue,evalOperand,storageLive,
    NativeRecordLLBC.read,write,NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.replace,
    NativeRecordValues.fits,complete,compatible,handled_encode_retag]

theorem outer_error_arguments (start world : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word)
    (kind : Kind) (valid : NativeReservationErrorLocal.Valid kind) :
    evalArgs (handledRawErrorPrepared start capacity world kind) [(.move 7 [])] =
      some ([NativeReservationErrorLocal.encode reservationErrorTags kind],handledRawErrorMoved start capacity world kind) := by
  obtain ⟨complete,compatible⟩ := handled_encode_properties kind valid
  simp [handledRawErrorFrame,handledRawErrorPrepared,handledRawErrorMoved,handledErrorValue,rawCallerMoved,rawCallerTypes,
    rawEntryAmbient,handledAmbient,evalArgs,evalOperand,NativeRecordLLBC.read,NativeRecordValues.typeAt,
    NativeRecordValues.get,NativeRecordValues.replace,NativeRecordValues.fits,complete,compatible]

theorem handled_invoke_handler (world : NativeReferenceMachine.State) (base : NativePointerStorage.Address)
    (overflow allocation : Body) (value : NativeRecordValues.Value) :
    handledInvoke handlerTypes 1 (handlerEval base overflow allocation) world [value] =
      settle world (handlerInvoke world base overflow allocation value) := by
  cases initialized : initial handlerTypes 1 [value] world with
  | none => simp only [handledInvoke,handlerInvoke,initialized,settle]
  | some entered =>
    have same := initial_world handlerTypes 1 [value] world entered initialized
    simp only [handledInvoke,handlerInvoke,initialized,same]

theorem outer_error_invokes (start world : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word)
    (kind : Kind) (valid : NativeReservationErrorLocal.Valid kind) (base : NativePointerStorage.Address)
    (overflow allocation : Body) :
    outerErrorEval base overflow allocation (handledRawErrorFrame start capacity world kind) =
      handledResume (handledRawErrorMoved start capacity world kind) 8
        (eval (outerErrorCleanup .resume)) (eval (outerErrorCleanup (.dead 14 .abort)))
        (settle world (handlerInvoke world base overflow allocation
          (NativeReservationErrorLocal.encode reservationErrorTags kind))) := by
  rw [outerErrorEval,outer_error_prefix start world capacity kind valid]
  simp only [handledContinue]
  rw [handled_call_invokes,outer_error_arguments start world capacity kind valid]
  exact congrArg (handledResume _ _ _ _) (handled_invoke_handler world base overflow allocation _)

def handledTerminal : Flow → Prop
  | .invalid _ | .unwind _ | .unsupported _ _ => True
  | _ => False

theorem handled_continue_terminal (next : Frame → Flow) (flow : Flow) (terminal : handledTerminal flow) :
    handledContinue next flow = flow := by
  cases flow <;> simp_all [handledTerminal,handledContinue]

theorem handled_settle_terminal (world : NativeReferenceMachine.State) (flow : Flow) (terminal : handledTerminal flow) :
    settle world flow = flow := by
  cases flow <;> simp_all [handledTerminal,settle]

theorem outer_error_no_normal (base : NativePointerStorage.Address) (overflow allocation : Body) (frame changed : Frame) :
    outerErrorEval base overflow allocation frame ≠ .normal changed := by
  intro h
  simp only [outerErrorEval,outerErrorPrefix,handledContinue,handledCall,handledResume,outerErrorCleanup,eval] at h
  repeat' (first | split at h | cases h)
  all_goals simp_all

theorem outer_error_no_return (base : NativePointerStorage.Address) (overflow allocation : Body) (frame : Frame)
    (value : NativeRecordValues.Value) (world : NativeReferenceMachine.State) :
    outerErrorEval base overflow allocation frame ≠ .returned value world := by
  intro h
  simp only [outerErrorEval,outerErrorPrefix,handledContinue,handledCall,handledResume,outerErrorCleanup,eval] at h
  repeat' (first | split at h | cases h)

theorem outer_error_terminal (base : NativePointerStorage.Address) (overflow allocation : Body) (frame : Frame) :
    handledTerminal (outerErrorEval base overflow allocation frame) := by
  cases actual : outerErrorEval base overflow allocation frame with
  | normal changed => exact False.elim (outer_error_no_normal base overflow allocation frame changed actual)
  | returned value world => exact False.elim (outer_error_no_return base overflow allocation frame value world actual)
  | invalid world => trivial
  | unwind world => trivial
  | unsupported source world => trivial

theorem handled_raw_tail_error (start world : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word)
    (kind : Kind) (base : NativePointerStorage.Address) (overflow allocation cold : Body) :
    handledRawTail base overflow allocation cold (handledRawErrorFrame start capacity world kind) =
      outerErrorEval base overflow allocation (handledRawErrorFrame start capacity world kind) := by
  have selected : selectChoice (handledRawErrorFrame start capacity world kind) 4 [] 8 = some true := by
    simp [handledRawErrorFrame,handledErrorValue,rawCallerMoved,rawCallerTypes,rawEntryAmbient,handledAmbient,
      layoutTypes,calleeEntryAmbient,selectChoice,NativeRecordValues.typeAt,NativeRecordValues.sideAt]
  simp only [handledRawTail,selected,ite_true]
  exact handled_continue_terminal _ _ (outer_error_terminal base overflow allocation _)

theorem handled_raw_constructor_error (start world : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word)
    (kind : Kind) (valid : NativeReservationErrorLocal.Valid kind) (address : NativeWord64Memory.Word)
    (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body)
    (unwind : NativeAllocatorLLBC.Body)
    (returned : NativeAllocatorLLBC.invokeValues
      (unifiedConstructorFunction (rawEntryAmbient (handledAmbient start)) false address outcome shim) start
      [.scalar (.usize capacity),uninitializedValue,allocatorValue,byteLayout] = .returned (handledErrorValue kind) world) :
    NativeAllocatorLLBC.eval (unifiedRawCallerCall (rawEntryAmbient (handledAmbient start)) address outcome shim unwind .done)
      (rawCallerFrame (rawEntryAmbient (handledAmbient start)) capacity) =
        .normal (handledRawErrorFrame start capacity world kind) := by
  let ambient := rawEntryAmbient (handledAmbient start)
  have prepared : eval (rawCallerPrefix .done) (rawCallerFrame ambient capacity) = .normal (rawCallerPrepared ambient capacity) := by
    rw [raw_caller_prefix_exact]; rfl
  change NativeAllocatorLLBC.eval (unifiedRawCallerCall ambient address outcome shim unwind .done) _ = _
  rw [unifiedRawCallerCall,NativeAllocatorLLBC.legacy_normal _ prepared]
  have called := NativeAllocatorLLBC.eval_call (unifiedConstructorFunction ambient false address outcome shim)
    (rawCallerPrepared ambient capacity) 4 rawCallerArgs unwind .done
  rw [raw_caller_arguments] at called
  simp only at called
  rw [show (rawCallerMoved ambient capacity).world = start from rfl,returned] at called
  rw [called]
  obtain ⟨complete,compatible⟩ := handled_encode_properties kind valid
  simp [NativeAllocatorLLBC.resume,NativeAllocatorLLBC.eval,handledRawErrorFrame,handledErrorValue,
    rawCallerMoved,rawCallerTypes,rawEntryAmbient,handledAmbient,ambient,layoutTypes,calleeEntryAmbient,write,
    NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits,complete,compatible]

theorem handled_raw_invocation_error (start world : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word)
    (kind : Kind) (valid : NativeReservationErrorLocal.Valid kind) (base : NativePointerStorage.Address)
    (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body)
    (overflow allocation : Body)
    (returned : NativeAllocatorLLBC.invokeValues
      (unifiedConstructorFunction (rawEntryAmbient (handledAmbient start)) false address outcome shim) start
      [.scalar (.usize capacity),uninitializedValue,allocatorValue,byteLayout] = .returned (handledErrorValue kind) world) :
    handledRawInvoke start base address outcome shim overflow allocation capacity =
      outerErrorEval base overflow allocation (handledRawErrorFrame start capacity world kind) := by
  have initialized := unified_raw_caller_initialized (handledAmbient start) capacity address outcome shim
  change initial (rawCallerTypes (rawEntryAmbient (handledAmbient start))) 3 _ start = _ at initialized
  rw [handledRawInvoke,handledInvoke,initialized]
  change settle start (handledRawEval (rawEntryAmbient (handledAmbient start)) base address outcome shim overflow allocation
    (rawCallerFrame (rawEntryAmbient (handledAmbient start)) capacity)) = _
  rw [handledRawEval,handled_raw_constructor_error start world capacity kind valid address outcome shim _ returned]
  simp only [handledContinue]
  rw [handled_raw_tail_error]
  exact handled_settle_terminal _ _ (outer_error_terminal base overflow allocation _)

theorem handled_vec_terminal (start : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word)
    (base : NativePointerStorage.Address) (address : NativeWord64Memory.Word)
    (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) (overflow allocation : Body)
    (flow : Flow) (terminal : handledTerminal flow)
    (called : handledRawInvoke start base address outcome shim overflow allocation capacity = flow) :
    handledVecEval (handledAmbient start) base address outcome shim overflow allocation
      (vecCallerFrame (handledAmbient start) capacity) = flow := by
  rw [handledVecEval,vec_caller_prefix_exact]
  simp only [eval,handledContinue]
  rw [handled_call_invokes,vec_caller_arguments]
  change handledResume (vecCallerMoved (handledAmbient start) capacity) 3
    (eval (.dead 1 .resume)) (eval vecCallerTail)
    (handledRawInvoke start base address outcome shim overflow allocation capacity) = flow
  rw [called]
  cases flow with
  | normal changed => cases terminal
  | returned value world => cases terminal
  | invalid world => rfl
  | unsupported source world => rfl
  | unwind world => simp [handledResume,eval,storageDead,vecCallerMoved]

theorem handled_vec_invocation_terminal (start : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word)
    (base : NativePointerStorage.Address) (address : NativeWord64Memory.Word)
    (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) (overflow allocation : Body)
    (flow : Flow) (terminal : handledTerminal flow)
    (called : handledRawInvoke start base address outcome shim overflow allocation capacity = flow) :
    handledInvoke (vecCallerTypes (handledAmbient start)) 1
      (handledVecEval (handledAmbient start) base address outcome shim overflow allocation) start [.scalar (.usize capacity)] = flow := by
  have initialized := unified_vec_caller_initialized (handledAmbient start) capacity address outcome shim
  change initial (vecCallerTypes (handledAmbient start)) 1 _ start = _ at initialized
  rw [handledInvoke,initialized]
  change settle start (handledVecEval (handledAmbient start) base address outcome shim overflow allocation
    (vecCallerFrame (handledAmbient start) capacity)) = flow
  rw [handled_vec_terminal start capacity base address outcome shim overflow allocation flow terminal called]
  exact handled_settle_terminal _ flow terminal

theorem handled_root_terminal (start : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word)
    (base : NativePointerStorage.Address) (address : NativeWord64Memory.Word)
    (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) (overflow allocation : Body)
    (flow : Flow) (terminal : handledTerminal flow)
    (called : handledRawInvoke start base address outcome shim overflow allocation capacity = flow) :
    handledRootInvoke start base address outcome shim overflow allocation capacity = flow := by
  have initialized := unified_capacity_root_initialized (handledAmbient start) capacity address outcome shim
  change initial (capacityRootTypes (handledAmbient start)) 1 _ start = _ at initialized
  rw [handledRootInvoke,handledInvoke,initialized]
  change settle start (handledRootEval (handledAmbient start) base address outcome shim overflow allocation
    (capacityRootFrame (handledAmbient start) capacity)) = flow
  rw [handledRootEval,capacity_root_prefix]
  simp only [eval,handledContinue]
  rw [handled_call_invokes,capacity_root_arguments]
  change settle start (handledResume (capacityRootMoved (handledAmbient start) capacity) 0
    (eval (.dead 1 .resume)) (eval capacityRootTail)
    (handledInvoke (vecCallerTypes (handledAmbient start)) 1
      (handledVecEval (handledAmbient start) base address outcome shim overflow allocation) start [.scalar (.usize capacity)])) = flow
  rw [handled_vec_invocation_terminal start capacity base address outcome shim overflow allocation flow terminal called]
  cases flow with
  | normal changed => cases terminal
  | returned value world => cases terminal
  | invalid world => rfl
  | unsupported source world => rfl
  | unwind world => simp [handledResume,eval,storageDead,capacityRootMoved,settle]

theorem handled_root_rejected (start : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word)
    (base : NativePointerStorage.Address) (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0)
    (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) (overflow allocation : Body)
    (large : 2^63 ≤ capacity.val) (valid : NativeReferenceMachine.WellFormed start) :
    handledRootInvoke start base address outcome shim overflow allocation capacity =
      outerErrorEval base overflow allocation
        (handledRawErrorFrame start capacity (NativeZstBorrow.grantedExclusive start address) .capacityOverflow) := by
  apply handled_root_terminal _ _ _ _ _ _ _ _ _ (outer_error_terminal _ _ _ _)
  apply handled_raw_invocation_error start _ capacity .capacityOverflow (by trivial) base address outcome shim overflow allocation
  exact unified_constructor_rejected (rawEntryAmbient (handledAmbient start)) capacity false address nonzero outcome shim large valid

theorem handled_root_allocation_failure (start : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word)
    (base : NativePointerStorage.Address) (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0)
    (shim : NativeAllocatorLLBC.Body) (overflow allocation : Body) (world : NativeReferenceMachine.State)
    (valid : NativeReferenceMachine.WellFormed start) (positive : 0 < capacity.val) (bounded : capacity.val < 2^63)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) (NativeZstBorrow.granted start address) [] =
      .returned (.scalar .unit) world) :
    handledRootInvoke start base address none shim overflow allocation capacity =
      outerErrorEval base overflow allocation
        (handledRawErrorFrame start capacity (NativeZstBorrow.grantedExclusive world address) (.allocationError capacity 1)) := by
  have kindValid : NativeReservationErrorLocal.Valid (.allocationError capacity 1) := by
    refine ⟨by decide,⟨?_,?_⟩⟩
    · change 1 ∈ (List.range 64).map (fun exponent => 2 ^ exponent)
      decide
    · change capacity.val + (1-1) ≤ 2^63-1
      omega
  apply handled_root_terminal _ _ _ _ _ _ _ _ _ (outer_error_terminal _ _ _ _)
  apply handled_raw_invocation_error start _ capacity (.allocationError capacity 1) kindValid base address none shim overflow allocation
  exact unified_constructor_failure (rawEntryAmbient (handledAmbient start)) capacity false address nonzero shim world valid positive bounded returned

theorem handled_raw_invocation_success (start world : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word)
    (base : NativePointerStorage.Address) (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (overflow allocation : Body) (pointer : NativePointerStorage.Pointer)
    (nonnull : pointer.address.val ≠ 0)
    (returned : NativeAllocatorLLBC.invokeValues
      (unifiedConstructorFunction (rawEntryAmbient (handledAmbient start)) false address outcome shim) start
      [.scalar (.usize capacity),uninitializedValue,allocatorValue,byteLayout] = .returned (positiveResultValue pointer capacity) world) :
    handledRawInvoke start base address outcome shim overflow allocation capacity =
      .returned (positiveRawValue pointer capacity) world := by
  have initialized := unified_raw_caller_initialized (handledAmbient start) capacity address outcome shim
  change initial (rawCallerTypes (rawEntryAmbient (handledAmbient start))) 3 _ start = _ at initialized
  rw [handledRawInvoke,handledInvoke,initialized]
  change settle start (handledRawEval (rawEntryAmbient (handledAmbient start)) base address outcome shim overflow allocation
    (rawCallerFrame (rawEntryAmbient (handledAmbient start)) capacity)) = _
  rw [handled_raw_eval_success _ _ _ _ _ _ _ nonnull base overflow allocation returned]
  rfl

theorem handled_vec_invocation_success (start world : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word)
    (base : NativePointerStorage.Address) (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (overflow allocation : Body) (pointer : NativePointerStorage.Pointer)
    (nonnull : pointer.address.val ≠ 0)
    (called : handledRawInvoke start base address outcome shim overflow allocation capacity =
      .returned (positiveRawValue pointer capacity) world) :
    handledInvoke (vecCallerTypes (handledAmbient start)) 1
      (handledVecEval (handledAmbient start) base address outcome shim overflow allocation) start [.scalar (.usize capacity)] =
        .returned (positiveVecValue pointer capacity) world := by
  let ambient := handledAmbient start
  have initialized := unified_vec_caller_initialized ambient capacity address outcome shim
  change initial (vecCallerTypes ambient) 1 _ start = _ at initialized
  rw [handledInvoke,initialized]
  change settle start (handledVecEval ambient base address outcome shim overflow allocation
    (vecCallerFrame ambient capacity)) = _
  rw [handledVecEval,vec_caller_prefix_exact]
  simp only [eval,handledContinue]
  rw [handled_call_invokes,vec_caller_arguments]
  change settle start (handledResume (vecCallerMoved ambient capacity) 3 (eval (.dead 1 .resume)) (eval vecCallerTail)
    (handledRawInvoke start base address outcome shim overflow allocation capacity)) = _
  rw [called]
  have resumed : handledResume (vecCallerMoved ambient capacity) 3 (eval (.dead 1 .resume)) (eval vecCallerTail)
      (.returned (positiveRawValue pointer capacity) world) = eval vecCallerTail (positiveVecCallerReturned ambient capacity world pointer) := by
    simp [handledResume,positiveVecCallerReturned,write,vecCallerMoved,vecCallerTypes,layoutTypes,calleeEntryAmbient,
      positiveRawValue,runtimeThinValue,allocatorValue,nonnull,NativeRecordValues.fits,NativeRecordValues.complete,
      NativeRecordValues.compatible,NativeSliceLLBC.fits]
  rw [resumed,positive_vec_caller_tail ambient capacity world pointer nonnull]
  rfl

theorem handled_root_success_from_raw (start world : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word)
    (base : NativePointerStorage.Address) (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address)
    (shim : NativeAllocatorLLBC.Body) (overflow allocation : Body) (pointer : NativePointerStorage.Pointer)
    (nonnull : pointer.address.val ≠ 0)
    (called : handledRawInvoke start base address outcome shim overflow allocation capacity =
      .returned (positiveRawValue pointer capacity) world) :
    handledRootInvoke start base address outcome shim overflow allocation capacity =
      .returned (positiveVecValue pointer capacity) world := by
  let ambient := handledAmbient start
  have initialized := unified_capacity_root_initialized ambient capacity address outcome shim
  change initial (capacityRootTypes ambient) 1 _ start = _ at initialized
  rw [handledRootInvoke,handledInvoke,initialized]
  change settle start (handledRootEval ambient base address outcome shim overflow allocation
    (capacityRootFrame ambient capacity)) = _
  rw [handledRootEval,capacity_root_prefix]
  simp only [eval,handledContinue]
  rw [handled_call_invokes,capacity_root_arguments]
  change settle start (handledResume (capacityRootMoved ambient capacity) 0 (eval (.dead 1 .resume)) (eval capacityRootTail)
    (handledInvoke (vecCallerTypes ambient) 1 (handledVecEval ambient base address outcome shim overflow allocation)
      start [.scalar (.usize capacity)])) = _
  rw [handled_vec_invocation_success start world capacity base address outcome shim overflow allocation pointer nonnull called]
  have resumed : handledResume (capacityRootMoved ambient capacity) 0 (eval (.dead 1 .resume)) (eval capacityRootTail)
      (.returned (positiveVecValue pointer capacity) world) = eval capacityRootTail (positiveCapacityRootReturned ambient capacity world pointer) := by
    simp [handledResume,positiveCapacityRootReturned,write,capacityRootMoved,capacityRootTypes,vecCallerTypes,layoutTypes,
      calleeEntryAmbient,positiveVecValue,positiveRawValue,runtimeThinValue,allocatorValue,nonnull,NativeRecordValues.fits,
      NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits]
  rw [resumed,positive_capacity_root_tail ambient capacity world pointer nonnull]
  rfl

theorem handled_root_success (start : NativeReferenceMachine.State) (capacity : NativeWord64Memory.Word)
    (base : NativePointerStorage.Address) (address : NativeWord64Memory.Word) (nonzero : address.val ≠ 0)
    (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body) (overflow allocation : Body)
    (shimWorld resultWorld : NativeReferenceMachine.State) (pointer : NativePointerStorage.Pointer)
    (positive : 0 < capacity.val) (bounded : capacity.val < 2^63) (nonnull : pointer.address.val ≠ 0)
    (returned : NativeAllocatorLLBC.invokeValues (runtimeShim shim) (NativeZstBorrow.granted start address) [] =
      .returned (.scalar .unit) shimWorld)
    (allocated : NativeAllocatorExecution.run shimWorld .allocate outcome capacity 1 = .value (.raw ⟨pointer,none⟩) resultWorld) :
    handledRootInvoke start base address outcome shim overflow allocation capacity =
      .returned (positiveVecValue pointer capacity) resultWorld := by
  apply handled_root_success_from_raw start resultWorld capacity base address outcome shim overflow allocation pointer nonnull
  apply handled_raw_invocation_success start resultWorld capacity base address outcome shim overflow allocation pointer nonnull
  exact unified_constructor_success (rawEntryAmbient (handledAmbient start)) capacity false address nonzero outcome shim
    shimWorld resultWorld pointer positive bounded nonnull returned allocated

theorem handled_root_zero (start : NativeReferenceMachine.State) (base : NativePointerStorage.Address)
    (address : NativeWord64Memory.Word) (outcome : Option NativePointerStorage.Address) (shim : NativeAllocatorLLBC.Body)
    (overflow allocation : Body) :
    handledRootInvoke start base address outcome shim overflow allocation 0 = .returned zeroVecValue start := by
  apply handled_root_success_from_raw start start 0 base address outcome shim overflow allocation ⟨1,none⟩ (by decide)
  apply handled_raw_invocation_success start start 0 base address outcome shim overflow allocation ⟨1,none⟩ (by decide)
  exact unified_constructor_zero (rawEntryAmbient (handledAmbient start)) false address outcome shim

end HasteBootsVecCapacityArithmetic
