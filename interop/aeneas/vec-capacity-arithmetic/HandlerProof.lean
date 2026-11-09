namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC
open NativeReservationErrorFields (Kind)

theorem handler_never_fits (value : NativeRecordValues.Value) :
    NativeRecordValues.fits handlerNeverType value = false := by
  cases value <;> simp [handlerNeverType,NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible]

theorem handler_kind_fits (kind : Kind) (valid : NativeReservationErrorLocal.Valid kind) :
    NativeRecordValues.fits (HasteBootsReservationErrorKind.kindTypeFor reservationErrorTags)
      (NativeReservationErrorLocal.kindValue reservationErrorTags kind) = true := by
  cases kind with
  | capacityOverflow => rfl
  | allocationError size alignment =>
    have permitted := HasteBootsReservationErrorKind.alignment_member size alignment valid.2
    simp [HasteBootsReservationErrorKind.kindTypeFor,HasteBootsReservationErrorKind.layoutTypeFor,
      HasteBootsReservationErrorKind.alignmentTypeFor,NativeReservationErrorLocal.kindValue,
      NativeReservationErrorLocal.layoutValue,reservationErrorTags,NativeRecordValues.fits,
      NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits,permitted]

theorem handler_initial (world : NativeReferenceMachine.State) (kind : Kind)
    (valid : NativeReservationErrorLocal.Valid kind) :
    initial handlerTypes 1 [NativeReservationErrorLocal.encode reservationErrorTags kind] world =
      some (handlerFrame world kind) := by
  have fits := handler_kind_fits kind valid
  have properties : NativeRecordValues.complete (NativeReservationErrorLocal.kindValue reservationErrorTags kind) = true ∧
      NativeRecordValues.compatible (HasteBootsReservationErrorKind.kindTypeFor reservationErrorTags)
        (NativeReservationErrorLocal.kindValue reservationErrorTags kind) = true := by
    simpa only [NativeRecordValues.fits,Bool.and_eq_true] using fits
  simp [initial,handlerTypes,handlerFrame,HasteBootsReservationErrorKind.errorTypeFor,
    NativeReservationErrorLocal.encode,NativeRecordValues.fits,NativeRecordValues.complete,
    NativeRecordValues.compatible,NativeSliceLLBC.fits,properties.1,properties.2,List.replicate_succ]

theorem handler_overflow_dispatch (world : NativeReferenceMachine.State) (overflow allocation : Body) :
    eval (handlerTail overflow allocation) (handlerReadyFrame world .capacityOverflow) =
      eval (handlerOverflowCall overflow) (handlerDispatchFrame world .capacityOverflow) := by
  simp [handlerTail,handlerReadyFrame,handlerDispatchFrame,eval,storageDead,selectChoice,
    NativeRecordValues.sideAt,handlerTypes,HasteBootsReservationErrorKind.kindTypeFor,
    NativeRecordValues.typeAt,NativeReservationErrorLocal.kindValue,reservationErrorTags]

theorem handler_allocation_not_normal (frame changed : Frame) (allocation : Body) :
    eval (handlerAllocationCall allocation) frame ≠ .normal changed := by
  intro h
  simp only [handlerAllocationCall,handlerCleanup,eval] at h
  repeat' (first | split at h | cases h)

theorem handler_allocation_dispatch (world : NativeReferenceMachine.State) (overflow allocation : Body)
    (size alignment : NativeWord64Memory.Word) (valid : (NativeAllocatorExecution.request size alignment).Valid) :
    eval (handlerTail overflow allocation) (handlerReadyFrame world (.allocationError size alignment)) =
      eval (handlerAllocationCall allocation) (handlerDispatchFrame world (.allocationError size alignment)) := by
  have permitted := HasteBootsReservationErrorKind.alignment_member size alignment valid
  have finish (frame : Frame) :
      (match eval (handlerAllocationCall allocation) frame with
      | .normal changed => eval (handlerOverflowCall overflow) changed
      | flow => flow) = eval (handlerAllocationCall allocation) frame := by
    cases actual : eval (handlerAllocationCall allocation) frame with
    | normal changed => exact False.elim (handler_allocation_not_normal _ changed allocation actual)
    | returned value next => rfl
    | unwind next => rfl
    | invalid next => rfl
    | unsupported source next => rfl
  simp [handlerTail,handlerAllocationPrefix,handlerReadyFrame,handlerDispatchFrame,handlerTypes,
    HasteBootsReservationErrorKind.kindTypeFor,HasteBootsReservationErrorKind.layoutTypeFor,
    HasteBootsReservationErrorKind.alignmentTypeFor,NativeReservationErrorLocal.kindValue,
    NativeReservationErrorLocal.layoutValue,reservationErrorTags,eval,evalRvalue,evalOperand,retag,
    NativeSliceLLBC.retagValue,storageLive,storageDead,selectChoice,NativeRecordLLBC.read,write,
    NativeRecordValues.sideAt,NativeRecordValues.typeAt,NativeRecordValues.get,
    NativeRecordValues.fits,NativeRecordValues.complete,NativeRecordValues.compatible,NativeRecordValues.copyable,
    NativeSliceLLBC.fits,permitted]
  change (match eval (handlerAllocationCall allocation) (handlerDispatchFrame world (.allocationError size alignment)) with
    | .normal changed => eval (handlerOverflowCall overflow) changed
    | flow => flow) = eval (handlerAllocationCall allocation) (handlerDispatchFrame world (.allocationError size alignment))
  exact finish _

theorem handler_snapshot_dispatch (world next : NativeReferenceMachine.State) (base : NativePointerStorage.Address)
    (kind : Kind) (result : NativeRecordValues.Value) (overflow allocation : Body)
    (valid : NativeReferenceMachine.WellFormed world)
    (executed : NativeReservationErrorLocal.snapshotValue reservationErrorTags world base
      (NativeReservationErrorLocal.encode reservationErrorTags kind) = .value result next) :
    ∃ final, handlerInvoke world base overflow allocation (NativeReservationErrorLocal.encode reservationErrorTags kind) =
      eval (handlerTail overflow allocation) (handlerReadyFrame final kind) := by
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
  rw [handlerInvoke,handler_initial world kind inputValid]
  simp [handlerEval,handlerFrame,handlerTypes,handlerPrefix,handlerResume,handlerReadyFrame,
    NativeReservationErrorLocal.snapshotLocal,eval,storageLive,NativeRecordLLBC.read,write,evalArgs,evalOperand,
    NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.replace,NativeRecordValues.fits,
    NativeRecordValues.complete,NativeRecordValues.compatible,NativeSliceLLBC.fits,
    HasteBootsReservationErrorKind.errorTypeFor,NativeReservationErrorLocal.encode,
    properties.1,properties.2,executed,getter]

theorem source_overflow_handler_dispatch (world next : NativeReferenceMachine.State) (base : NativePointerStorage.Address)
    (result : NativeRecordValues.Value) (overflow allocation : Body) (valid : NativeReferenceMachine.WellFormed world)
    (executed : NativeReservationErrorLocal.snapshotValue reservationErrorTags world base
      ((NativeRecordValues.get capacityOverflowValue [(.unwrap 8),(.active true),.left]).getD .uninit) = .value result next) :
    ∃ final, handlerInvoke world base overflow allocation
      ((NativeRecordValues.get capacityOverflowValue [(.unwrap 8),(.active true),.left]).getD .uninit) =
        eval (handlerOverflowCall overflow) (handlerDispatchFrame final .capacityOverflow) := by
  change NativeReservationErrorLocal.snapshotValue reservationErrorTags world base
    (NativeReservationErrorLocal.encode reservationErrorTags .capacityOverflow) = .value result next at executed
  obtain ⟨final,actual⟩ := handler_snapshot_dispatch world next base .capacityOverflow result overflow allocation valid executed
  exact ⟨final,actual.trans (handler_overflow_dispatch final overflow allocation)⟩

theorem source_allocation_handler_dispatch (capacity : NativeWord64Memory.Word) (bounded : capacity.val < 2^63)
    (world next : NativeReferenceMachine.State) (base : NativePointerStorage.Address)
    (result : NativeRecordValues.Value) (overflow allocation : Body) (valid : NativeReferenceMachine.WellFormed world)
    (executed : NativeReservationErrorLocal.snapshotValue reservationErrorTags world base
      ((NativeRecordValues.get (constructorErrorValue capacity) [(.unwrap 8),(.active true),.left]).getD .uninit) = .value result next) :
    ∃ final, handlerInvoke world base overflow allocation
      ((NativeRecordValues.get (constructorErrorValue capacity) [(.unwrap 8),(.active true),.left]).getD .uninit) =
        eval (handlerAllocationCall allocation) (handlerDispatchFrame final (.allocationError capacity 1)) := by
  change NativeReservationErrorLocal.snapshotValue reservationErrorTags world base
    (NativeReservationErrorLocal.encode reservationErrorTags (.allocationError capacity 1)) = .value result next at executed
  obtain ⟨final,actual⟩ := handler_snapshot_dispatch world next base (.allocationError capacity 1) result overflow allocation valid executed
  have layoutValid : (NativeAllocatorExecution.request capacity 1).Valid := by
    refine ⟨?_,?_⟩
    · change 1 ∈ (List.range 64).map (fun exponent => 2 ^ exponent)
      decide
    · change capacity.val + (1-1) ≤ 2^63-1
      omega
  exact ⟨final,actual.trans (handler_allocation_dispatch final overflow allocation capacity 1 layoutValid)⟩

end HasteBootsVecCapacityArithmetic
