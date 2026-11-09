namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC
open NativeReservationErrorFields (Kind)

theorem effect_handler_snapshot_ready (world next : NativeReferenceMachine.State) (base : NativePointerStorage.Address)
    (kind : Kind) (result : NativeRecordValues.Value) (tail : Frame → Flow)
    (valid : NativeReferenceMachine.WellFormed world)
    (executed : NativeReservationErrorLocal.snapshotValue reservationErrorTags world base
      (NativeReservationErrorLocal.encode reservationErrorTags kind) = .value result next) :
    ∃ final, effectHandlerEval base tail (handlerFrame world kind) = tail (handlerReadyFrame final kind) := by
  obtain ⟨decoded,reference,decoding,steps,selected,resultEq⟩ := NativeReservationErrorLocal.snapshotValue_success _ _ _ _ _ _ executed
  have inputValid : NativeReservationErrorLocal.Valid kind := by
    by_contra rejected
    simp [NativeReservationErrorLocal.decode_encode,rejected] at decoding
  have decodedCorrect : NativeReservationErrorLocal.decode reservationErrorTags
      (NativeReservationErrorLocal.encode reservationErrorTags kind) = some kind := by
    rw [NativeReservationErrorLocal.decode_encode,ite_eq_left inputValid]
  obtain ⟨final,checked⟩ := NativeReservationErrorRead.snapshot_getKind_decoded
    reservationErrorTags world next base _ result kind valid decodedCorrect executed
  have getter : HasteBootsReservationErrorKind.invokeFor reservationErrorTags next result =
      .returned (NativeReservationErrorLocal.kindValue reservationErrorTags kind) final := by
    rw [HasteBootsReservationErrorKind.invoke_for_equiv,checked]
    rfl
  subst result
  have fits := handler_kind_fits kind inputValid
  have properties : NativeRecordValues.complete (NativeReservationErrorLocal.kindValue reservationErrorTags kind) = true ∧
      NativeRecordValues.compatible (HasteBootsReservationErrorKind.kindTypeFor reservationErrorTags)
        (NativeReservationErrorLocal.kindValue reservationErrorTags kind) = true := by
    simpa only [NativeRecordValues.fits,Bool.and_eq_true] using fits
  dsimp only [NativeReservationErrorLocal.encode] at executed
  refine ⟨final,?_⟩
  simp [effectHandlerEval,handlerFrame,handlerTypes,handlerPrefix,handledResume,handlerReadyFrame,
    NativeReservationErrorLocal.snapshotLocal,eval,storageLive,NativeRecordLLBC.read,write,evalArgs,evalOperand,
    NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.replace,NativeRecordValues.fits,
    NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits,
    HasteBootsReservationErrorKind.errorTypeFor,NativeReservationErrorLocal.encode,
    properties.1,properties.2,executed,getter]


theorem terminal_overflow_invoke_terminal (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow) (world : NativeReferenceMachine.State) :
    handledTerminal (terminalOverflowInvoke fields formatter panic world) := by
  rw [terminalOverflowInvoke,handledInvoke,terminal_overflow_initial]
  change handledTerminal (settle world (terminalOverflowEval formatter panic (terminalOverflowFrame fields world)))
  rw [handled_settle_terminal world _ (terminal_overflow_terminal formatter panic _)]
  exact terminal_overflow_terminal formatter panic _

theorem terminal_allocation_invoke_terminal (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow) (world : NativeReferenceMachine.State)
    (size alignment : NativeWord64Memory.Word) (valid : (NativeAllocatorExecution.request size alignment).Valid) :
    handledTerminal (terminalAllocationInvoke fields formatter panic world
      (NativeReservationErrorLocal.layoutValue reservationErrorTags size alignment)) := by
  rw [terminal_allocation_forwards_ct fields formatter panic world size alignment valid]
  exact terminal_ct_terminal formatter panic _

theorem terminal_handler_overflow_call (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow) (world : NativeReferenceMachine.State) :
    terminalHandlerOverflowCall fields formatter panic (handlerDispatchFrame world .capacityOverflow) =
      terminalOverflowInvoke fields formatter panic world := by
  rw [terminalHandlerOverflowCall,handled_call_invokes]
  change handledResume (handlerDispatchFrame world .capacityOverflow) 0
    (eval (handlerCleanup .resume)) (eval (handlerCleanup .abort))
    (terminalOverflowInvoke fields formatter panic world) = _
  have terminal := terminal_overflow_invoke_terminal fields formatter panic world
  cases actual : terminalOverflowInvoke fields formatter panic world with
  | normal changed => simp only [actual,handledTerminal] at terminal
  | returned value next => simp only [actual,handledTerminal] at terminal
  | invalid next => rfl
  | unsupported source next => rfl
  | unwind next => simp [handledResume,handlerCleanup,handlerDispatchFrame,handlerReadyFrame,eval,storageDead]

theorem terminal_handler_allocation_call (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow) (world : NativeReferenceMachine.State)
    (size alignment : NativeWord64Memory.Word) (valid : (NativeAllocatorExecution.request size alignment).Valid) :
    terminalHandlerAllocationCall fields formatter panic (handlerDispatchFrame world (.allocationError size alignment)) =
      terminalAllocationInvoke fields formatter panic world
        (NativeReservationErrorLocal.layoutValue reservationErrorTags size alignment) := by
  obtain ⟨complete,compatible⟩ := terminal_layout_properties size alignment valid
  have arguments : evalArgs (handlerDispatchFrame world (.allocationError size alignment)) [(.move 5 [])] =
      some ([NativeReservationErrorLocal.layoutValue reservationErrorTags size alignment],
        {handlerDispatchFrame world (.allocationError size alignment) with slots :=
          (handlerDispatchFrame world (.allocationError size alignment)).slots.set 5 (.live (some .uninit))}) := by
    simp [handlerDispatchFrame,handlerReadyFrame,handlerTypes,evalArgs,evalOperand,NativeRecordLLBC.read,
      NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.replace,NativeRecordValues.fits,complete,compatible]
  rw [terminalHandlerAllocationCall,handled_call_invokes,arguments]
  change handledResume _ 0 (eval (handlerCleanup .resume)) (eval (handlerCleanup .abort))
    (terminalAllocationInvoke fields formatter panic world (NativeReservationErrorLocal.layoutValue reservationErrorTags size alignment)) = _
  have terminal := terminal_allocation_invoke_terminal fields formatter panic world size alignment valid
  cases actual : terminalAllocationInvoke fields formatter panic world
      (NativeReservationErrorLocal.layoutValue reservationErrorTags size alignment) with
  | normal changed => simp only [actual,handledTerminal] at terminal
  | returned value next => simp only [actual,handledTerminal] at terminal
  | invalid next => rfl
  | unsupported source next => rfl
  | unwind next => simp [handledResume,handlerCleanup,handlerDispatchFrame,handlerReadyFrame,eval,storageDead]

theorem terminal_handler_allocation_prefix (world : NativeReferenceMachine.State)
    (size alignment : NativeWord64Memory.Word) (valid : (NativeAllocatorExecution.request size alignment).Valid) :
    eval (handlerAllocationPrefix .done)
      {handlerReadyFrame world (.allocationError size alignment) with slots :=
        (handlerReadyFrame world (.allocationError size alignment)).slots.set 3 .dead} =
      .normal (handlerDispatchFrame world (.allocationError size alignment)) := by
  have permitted := HasteBootsReservationErrorKind.alignment_member size alignment valid
  simp [handlerAllocationPrefix,handlerReadyFrame,handlerDispatchFrame,handlerTypes,
    HasteBootsReservationErrorKind.kindTypeFor,HasteBootsReservationErrorKind.layoutTypeFor,
    HasteBootsReservationErrorKind.alignmentTypeFor,NativeReservationErrorLocal.kindValue,
    NativeReservationErrorLocal.layoutValue,reservationErrorTags,eval,evalRvalue,evalOperand,retag,
    NativeSliceLLBC.retagValue,storageLive,NativeRecordLLBC.read,write,
    NativeRecordValues.typeAt,NativeRecordValues.get,
    NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeRecordValues.copyable,
    NativeSliceLLBC.fits,permitted]

theorem terminal_handler_tail_overflow (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow) (world : NativeReferenceMachine.State) :
    terminalHandlerTail fields formatter panic (handlerReadyFrame world .capacityOverflow) =
      terminalOverflowInvoke fields formatter panic world := by
  have dispatch : terminalHandlerTail fields formatter panic (handlerReadyFrame world .capacityOverflow) =
      terminalHandlerOverflowCall fields formatter panic (handlerDispatchFrame world .capacityOverflow) := by
    simp [terminalHandlerTail,handledContinue,handlerReadyFrame,handlerDispatchFrame,handlerTypes,
      HasteBootsReservationErrorKind.kindTypeFor,NativeReservationErrorLocal.kindValue,
      reservationErrorTags,eval,storageDead,selectChoice,NativeRecordValues.sideAt,NativeRecordValues.typeAt]
  exact dispatch.trans (terminal_handler_overflow_call fields formatter panic world)

theorem terminal_handler_tail_allocation (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow) (world : NativeReferenceMachine.State)
    (size alignment : NativeWord64Memory.Word) (valid : (NativeAllocatorExecution.request size alignment).Valid) :
    terminalHandlerTail fields formatter panic (handlerReadyFrame world (.allocationError size alignment)) =
      terminalAllocationInvoke fields formatter panic world
        (NativeReservationErrorLocal.layoutValue reservationErrorTags size alignment) := by
  let ready := handlerReadyFrame world (.allocationError size alignment)
  let caller := {ready with slots := ready.slots.set 3 .dead}
  have referenceDead : eval (.dead 3 .done) ready = .normal caller := by simp [ready,caller,handlerReadyFrame,eval,storageDead]
  have selected : selectChoice caller 2 [] 18 = some true := by
    simp [caller,ready,handlerReadyFrame,handlerTypes,HasteBootsReservationErrorKind.kindTypeFor,
      NativeReservationErrorLocal.kindValue,reservationErrorTags,selectChoice,NativeRecordValues.sideAt,NativeRecordValues.typeAt]
  change handledContinue _ (eval (.dead 3 .done) ready) = _
  rw [referenceDead]
  simp only [handledContinue,selected,ite_true]
  rw [terminal_handler_allocation_prefix world size alignment valid]
  simp only
  rw [terminal_handler_allocation_call fields formatter panic world size alignment valid]
  exact handled_continue_terminal _ _ (terminal_allocation_invoke_terminal fields formatter panic world size alignment valid)

theorem terminal_handler_snapshot_dispatch (fields : NativeRecordValues.Ty)
    (formatter panic : String → NativeReferenceMachine.State → Flow)
    (world next : NativeReferenceMachine.State) (base : NativePointerStorage.Address) (kind : Kind)
    (result : NativeRecordValues.Value) (valid : NativeReferenceMachine.WellFormed world)
    (executed : NativeReservationErrorLocal.snapshotValue reservationErrorTags world base
      (NativeReservationErrorLocal.encode reservationErrorTags kind) = .value result next) :
    ∃ final, terminalHandlerInvoke fields formatter panic world base (NativeReservationErrorLocal.encode reservationErrorTags kind) =
      match kind with
      | .capacityOverflow => terminalOverflowInvoke fields formatter panic final
      | .allocationError size alignment => terminalAllocationInvoke fields formatter panic final
          (NativeReservationErrorLocal.layoutValue reservationErrorTags size alignment) := by
  obtain ⟨decoded,reference,decoding,steps,selected,resultEq⟩ := NativeReservationErrorLocal.snapshotValue_success _ _ _ _ _ _ executed
  have inputValid : NativeReservationErrorLocal.Valid kind := by
    by_contra rejected
    simp [NativeReservationErrorLocal.decode_encode,rejected] at decoding
  obtain ⟨final,ready⟩ := effect_handler_snapshot_ready world next base kind result (terminalHandlerTail fields formatter panic) valid executed
  refine ⟨final,?_⟩
  rw [terminalHandlerInvoke,handledInvoke,handler_initial world kind inputValid]
  change settle world (effectHandlerEval base (terminalHandlerTail fields formatter panic) (handlerFrame world kind)) = _
  rw [ready]
  cases kind with
  | capacityOverflow =>
    rw [terminal_handler_tail_overflow]
    exact handled_settle_terminal _ _ (terminal_overflow_invoke_terminal fields formatter panic final)
  | allocationError size alignment =>
    rw [terminal_handler_tail_allocation fields formatter panic final size alignment inputValid.2]
    exact handled_settle_terminal _ _ (terminal_allocation_invoke_terminal fields formatter panic final size alignment inputValid.2)

end HasteBootsVecCapacityArithmetic
