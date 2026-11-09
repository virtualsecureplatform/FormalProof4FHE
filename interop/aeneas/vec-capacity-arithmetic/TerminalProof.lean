namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

theorem terminal_layout_properties (size alignment : NativeWord64Memory.Word)
    (valid : (NativeAllocatorExecution.request size alignment).Valid) :
    NativeRecordValues.complete (NativeReservationErrorLocal.layoutValue reservationErrorTags size alignment) = true ∧
    NativeRecordValues.compatible (HasteBootsReservationErrorKind.layoutTypeFor reservationErrorTags)
      (NativeReservationErrorLocal.layoutValue reservationErrorTags size alignment) = true := by
  have permitted := HasteBootsReservationErrorKind.alignment_member size alignment valid
  simp [HasteBootsReservationErrorKind.layoutTypeFor,HasteBootsReservationErrorKind.alignmentTypeFor,
    NativeReservationErrorLocal.layoutValue,NativeRecordValues.complete,NativeRecordValues.compatible,
    NativeSliceLLBC.fits,reservationErrorTags,permitted]

theorem terminal_layout_retag (world : NativeReferenceMachine.State) (size alignment : NativeWord64Memory.Word) :
    retag world (NativeReservationErrorLocal.layoutValue reservationErrorTags size alignment) true .byte =
      .value (NativeReservationErrorLocal.layoutValue reservationErrorTags size alignment) world := rfl

theorem terminal_overflow_initial (fields : NativeRecordValues.Ty) (world : NativeReferenceMachine.State) :
    initial (terminalOverflowTypes fields) 0 [] world = some (terminalOverflowFrame fields world) := by
  simp [initial,terminalOverflowTypes,terminalOverflowFrame,List.replicate_succ]

theorem terminal_ct_initial (fields : NativeRecordValues.Ty) (world : NativeReferenceMachine.State)
    (size alignment : NativeWord64Memory.Word) (valid : (NativeAllocatorExecution.request size alignment).Valid) :
    initial (terminalCtTypes fields) 1 [NativeReservationErrorLocal.layoutValue reservationErrorTags size alignment] world =
      some (terminalCtFrame fields world (NativeReservationErrorLocal.layoutValue reservationErrorTags size alignment)) := by
  obtain ⟨complete,compatible⟩ := terminal_layout_properties size alignment valid
  simp [initial,terminalCtTypes,terminalCtFrame,NativeRecordValues.fits,complete,compatible,List.replicate_succ]

theorem terminal_allocation_initial (world : NativeReferenceMachine.State) (size alignment : NativeWord64Memory.Word)
    (valid : (NativeAllocatorExecution.request size alignment).Valid) :
    initial terminalAllocationTypes 1 [NativeReservationErrorLocal.layoutValue reservationErrorTags size alignment] world =
      some (terminalAllocationFrame world (NativeReservationErrorLocal.layoutValue reservationErrorTags size alignment)) := by
  obtain ⟨complete,compatible⟩ := terminal_layout_properties size alignment valid
  simp [initial,terminalAllocationTypes,terminalAllocationFrame,NativeRecordValues.fits,complete,compatible,List.replicate_succ]

theorem terminal_overflow_prefix (fields : NativeRecordValues.Ty) (world : NativeReferenceMachine.State) :
    eval terminalOverflowPrefix (terminalOverflowFrame fields world) = .normal (terminalOverflowPrepared fields world) := by
  simp [terminalOverflowPrefix,terminalOverflowFrame,terminalOverflowPrepared,eval,storageLive]

theorem terminal_ct_prefix (fields : NativeRecordValues.Ty) (world : NativeReferenceMachine.State) (layout : NativeRecordValues.Value) :
    eval terminalCtPrefix (terminalCtFrame fields world layout) = .normal (terminalCtPrepared fields world layout) := by
  simp [terminalCtPrefix,terminalCtFrame,terminalCtPrepared,eval,storageLive]

theorem terminal_allocation_prefix (world : NativeReferenceMachine.State) (size alignment : NativeWord64Memory.Word)
    (valid : (NativeAllocatorExecution.request size alignment).Valid) :
    eval terminalAllocationPrefix (terminalAllocationFrame world (NativeReservationErrorLocal.layoutValue reservationErrorTags size alignment)) =
      .normal (terminalAllocationPrepared world (NativeReservationErrorLocal.layoutValue reservationErrorTags size alignment)) := by
  obtain ⟨complete,compatible⟩ := terminal_layout_properties size alignment valid
  have copyable : NativeRecordValues.copyable (HasteBootsReservationErrorKind.layoutTypeFor reservationErrorTags) = true := rfl
  simp [terminalAllocationPrefix,terminalAllocationFrame,terminalAllocationPrepared,terminalAllocationTypes,eval,
    evalRvalue,evalOperand,evalArgs,storageLive,storageDead,NativeRecordLLBC.read,write,NativeRecordValues.typeAt,
    NativeRecordValues.get,NativeRecordValues.replace,NativeRecordValues.fits,NativeRecordValues.complete,
    NativeRecordValues.compatible,NativeSliceLLBC.fits,complete,compatible,copyable,terminal_layout_retag]

theorem terminal_allocation_arguments (world : NativeReferenceMachine.State) (size alignment : NativeWord64Memory.Word)
    (valid : (NativeAllocatorExecution.request size alignment).Valid) :
    evalArgs (terminalAllocationPrepared world (NativeReservationErrorLocal.layoutValue reservationErrorTags size alignment)) [(.move 2 [.left])] =
      some ([NativeReservationErrorLocal.layoutValue reservationErrorTags size alignment],
        terminalAllocationMoved world (NativeReservationErrorLocal.layoutValue reservationErrorTags size alignment)) := by
  obtain ⟨complete,compatible⟩ := terminal_layout_properties size alignment valid
  simp [terminalAllocationPrepared,terminalAllocationMoved,terminalAllocationTypes,evalArgs,evalOperand,
    NativeRecordLLBC.read,NativeRecordValues.typeAt,NativeRecordValues.get,NativeRecordValues.replace,
    NativeRecordValues.fits,complete,compatible]

theorem terminal_panic_terminal (panic : String → NativeReferenceMachine.State → Flow) (frame : Frame) :
    handledTerminal (terminalPanicEval panic frame) := by
  cases actual : panic "core::panicking::panic_fmt" frame.world <;>
    simp only [terminalPanicEval,actual,handledTerminal]

theorem terminal_overflow_to_formatter (fields : NativeRecordValues.Ty) (formatter panic : String → NativeReferenceMachine.State → Flow)
    (world : NativeReferenceMachine.State) :
    terminalOverflowEval formatter panic (terminalOverflowFrame fields world) =
      terminalFormatEval 1 (Body.dead 1) "capacity overflow" formatter panic (terminalOverflowPrepared fields world) := by
  rw [terminalOverflowEval,terminal_overflow_prefix]
  rfl

theorem terminal_ct_to_formatter (fields : NativeRecordValues.Ty) (formatter panic : String → NativeReferenceMachine.State → Flow)
    (world : NativeReferenceMachine.State) (layout : NativeRecordValues.Value) :
    terminalCtEval formatter panic (terminalCtFrame fields world layout) =
      terminalFormatEval 2 terminalCtCleanup "allocation failed" formatter panic (terminalCtPrepared fields world layout) := by
  rw [terminalCtEval,terminal_ct_prefix]
  rfl

theorem terminal_allocation_invokes_ct (fields : NativeRecordValues.Ty) (formatter panic : String → NativeReferenceMachine.State → Flow)
    (world : NativeReferenceMachine.State) (size alignment : NativeWord64Memory.Word)
    (valid : (NativeAllocatorExecution.request size alignment).Valid) :
    terminalAllocationEval fields formatter panic
      (terminalAllocationFrame world (NativeReservationErrorLocal.layoutValue reservationErrorTags size alignment)) =
      handledResume (terminalAllocationMoved world (NativeReservationErrorLocal.layoutValue reservationErrorTags size alignment)) 0
        (eval (terminalCtCleanup .resume)) (eval (terminalCtCleanup .abort))
        (handledInvoke (terminalCtTypes fields) 1 (terminalCtEval formatter panic) world
          [NativeReservationErrorLocal.layoutValue reservationErrorTags size alignment]) := by
  rw [terminalAllocationEval,terminal_allocation_prefix world size alignment valid]
  simp only [handledContinue]
  rw [handled_call_invokes,terminal_allocation_arguments world size alignment valid]
  rfl

theorem terminal_overflow_formats (fields : NativeRecordValues.Ty) (formatter panic : String → NativeReferenceMachine.State → Flow)
    (world next : NativeReferenceMachine.State) (value : NativeRecordValues.Value)
    (returned : formatter "capacity overflow" world = .returned value next)
    (fits : NativeRecordValues.fits (terminalFormatType fields) value = true) :
    terminalOverflowEval formatter panic (terminalOverflowFrame fields world) =
      terminalPanicEval panic (terminalOverflowPrepared fields next) := by
  have properties : NativeRecordValues.complete value = true ∧
      NativeRecordValues.compatible (terminalFormatType fields) value = true := by
    simpa only [NativeRecordValues.fits,Bool.and_eq_true] using fits
  rw [terminal_overflow_to_formatter]
  simp [terminalFormatEval,returned,handledResume,terminalOverflowPrepared,terminalOverflowTypes,write,
    NativeRecordValues.fits,properties.1,properties.2,handledContinue,eval,storageDead,terminalPanicEval]

theorem terminal_ct_formats (fields : NativeRecordValues.Ty) (formatter panic : String → NativeReferenceMachine.State → Flow)
    (world next : NativeReferenceMachine.State) (layout value : NativeRecordValues.Value)
    (returned : formatter "allocation failed" world = .returned value next)
    (fits : NativeRecordValues.fits (terminalFormatType fields) value = true) :
    terminalCtEval formatter panic (terminalCtFrame fields world layout) =
      terminalPanicEval panic (terminalCtPrepared fields next layout) := by
  have properties : NativeRecordValues.complete value = true ∧
      NativeRecordValues.compatible (terminalFormatType fields) value = true := by
    simpa only [NativeRecordValues.fits,Bool.and_eq_true] using fits
  rw [terminal_ct_to_formatter]
  simp [terminalFormatEval,returned,handledResume,terminalCtPrepared,terminalCtTypes,terminalCtCleanup,write,
    NativeRecordValues.fits,properties.1,properties.2,handledContinue,eval,storageDead,terminalPanicEval]

theorem terminal_ct_no_normal (formatter panic : String → NativeReferenceMachine.State → Flow) (frame changed : Frame) :
    terminalCtEval formatter panic frame ≠ .normal changed := by
  intro h
  simp only [terminalCtEval,terminalCtPrefix,terminalFormatEval,handledResume,handledContinue,
    terminalCtCleanup,terminalPanicEval,eval] at h
  repeat' (first | split at h | cases h)
  all_goals simp_all

theorem terminal_ct_no_return (formatter panic : String → NativeReferenceMachine.State → Flow) (frame : Frame)
    (value : NativeRecordValues.Value) (world : NativeReferenceMachine.State) :
    terminalCtEval formatter panic frame ≠ .returned value world := by
  intro h
  simp only [terminalCtEval,terminalCtPrefix,terminalFormatEval,handledResume,handledContinue,
    terminalCtCleanup,terminalPanicEval,eval] at h
  repeat' (first | split at h | cases h)
  all_goals simp_all

theorem terminal_ct_terminal (formatter panic : String → NativeReferenceMachine.State → Flow) (frame : Frame) :
    handledTerminal (terminalCtEval formatter panic frame) := by
  cases actual : terminalCtEval formatter panic frame with
  | normal changed => exact False.elim (terminal_ct_no_normal formatter panic frame changed actual)
  | returned value world => exact False.elim (terminal_ct_no_return formatter panic frame value world actual)
  | invalid world => trivial
  | unwind world => trivial
  | unsupported source world => trivial

theorem terminal_overflow_no_normal (formatter panic : String → NativeReferenceMachine.State → Flow) (frame changed : Frame) :
    terminalOverflowEval formatter panic frame ≠ .normal changed := by
  intro h
  simp only [terminalOverflowEval,terminalOverflowPrefix,terminalFormatEval,handledResume,handledContinue,
    terminalPanicEval,eval] at h
  repeat' (first | split at h | cases h)
  all_goals simp_all

theorem terminal_overflow_no_return (formatter panic : String → NativeReferenceMachine.State → Flow) (frame : Frame)
    (value : NativeRecordValues.Value) (world : NativeReferenceMachine.State) :
    terminalOverflowEval formatter panic frame ≠ .returned value world := by
  intro h
  simp only [terminalOverflowEval,terminalOverflowPrefix,terminalFormatEval,handledResume,handledContinue,
    terminalPanicEval,eval] at h
  repeat' (first | split at h | cases h)
  all_goals simp_all

theorem terminal_overflow_terminal (formatter panic : String → NativeReferenceMachine.State → Flow) (frame : Frame) :
    handledTerminal (terminalOverflowEval formatter panic frame) := by
  cases actual : terminalOverflowEval formatter panic frame with
  | normal changed => exact False.elim (terminal_overflow_no_normal formatter panic frame changed actual)
  | returned value world => exact False.elim (terminal_overflow_no_return formatter panic frame value world actual)
  | invalid world => trivial
  | unwind world => trivial
  | unsupported source world => trivial

theorem terminal_allocation_forwards_ct (fields : NativeRecordValues.Ty) (formatter panic : String → NativeReferenceMachine.State → Flow)
    (world : NativeReferenceMachine.State) (size alignment : NativeWord64Memory.Word)
    (valid : (NativeAllocatorExecution.request size alignment).Valid) :
    terminalAllocationInvoke fields formatter panic world (NativeReservationErrorLocal.layoutValue reservationErrorTags size alignment) =
      terminalCtEval formatter panic (terminalCtFrame fields world (NativeReservationErrorLocal.layoutValue reservationErrorTags size alignment)) := by
  rw [terminalAllocationInvoke,handledInvoke,terminal_allocation_initial world size alignment valid]
  change settle world (terminalAllocationEval fields formatter panic
    (terminalAllocationFrame world (NativeReservationErrorLocal.layoutValue reservationErrorTags size alignment))) = _
  rw [terminal_allocation_invokes_ct fields formatter panic world size alignment valid,
    handledInvoke,terminal_ct_initial fields world size alignment valid]
  have terminal := terminal_ct_terminal formatter panic
    (terminalCtFrame fields world (NativeReservationErrorLocal.layoutValue reservationErrorTags size alignment))
  change settle world (handledResume
    (terminalAllocationMoved world (NativeReservationErrorLocal.layoutValue reservationErrorTags size alignment)) 0
    (eval (terminalCtCleanup .resume)) (eval (terminalCtCleanup .abort))
    (settle world (terminalCtEval formatter panic
      (terminalCtFrame fields world (NativeReservationErrorLocal.layoutValue reservationErrorTags size alignment))))) = _
  rw [handled_settle_terminal world _ terminal]
  cases actual : terminalCtEval formatter panic
      (terminalCtFrame fields world (NativeReservationErrorLocal.layoutValue reservationErrorTags size alignment)) with
  | normal changed => simp only [actual,handledTerminal] at terminal
  | returned value next => simp only [actual,handledTerminal] at terminal
  | invalid next => rfl
  | unsupported source next => rfl
  | unwind next => simp [handledResume,terminalCtCleanup,terminalAllocationMoved,eval,storageDead,settle]

end HasteBootsVecCapacityArithmetic
