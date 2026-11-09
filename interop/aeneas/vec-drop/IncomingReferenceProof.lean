namespace HasteBootsVecDrop
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC (Frame Flow)
open NativeReferenceMachine (State)
open NativeByteSliceIndex (Slice)
open NativeIncomingReference (Preserves)

theorem loopOutcome_incoming (world : State) (slice : Slice) : Preserves world (loopOutcome world slice).world := by
  simp only [loopOutcome]
  split <;> exact NativeIncomingReference.run world slice

/-- The actual retained loop preserves incoming references and old leases on
every outcome, including a rejected argument or failed iteration prefix. -/
theorem loop_code_incoming (classification : NativeByteDropCalls.Classification) (frame : Frame) (flow : Flow)
    (executed : NativeRecordDropCalls.Runs (.loop classification HasteBootsVecByteLoop.f6) frame flow) :
    Preserves frame.world flow.world ∧ flow.world.pointers.heap = frame.world.pointers.heap := by
  have computed := (evalCode_iff (.loop classification HasteBootsVecByteLoop.f6) frame flow (by simp only [sourceLoops,beq_self_eq_true])).mp executed
  cases argument : NativeRecordDropCalls.loopArgument frame with
  | none =>
    simp only [evalCode,ite_true,argument,Option.some.injEq] at computed
    subst flow
    exact ⟨.refl _,rfl⟩
  | some slice =>
    simp only [evalCode,ite_true,argument,Option.some.injEq] at computed
    subst flow
    exact ⟨loopOutcome_incoming frame.world slice,loopOutcome_heap_frame frame.world slice⟩

theorem loop_code_resident (classification : NativeByteDropCalls.Classification) (frame : Frame) (flow : Flow)
    (mutable : Bool) (reference : NativeReferenceMachine.Reference) (count capacity length : NativeWord64Memory.Word)
    (base buffer : NativePointerStorage.Pointer)
    (view : NativeResidentVecBorrow.Resident frame.world (.reference mutable reference count) base capacity length buffer)
    (older : reference.tag < frame.world.nextTag)
    (executed : NativeRecordDropCalls.Runs (.loop classification HasteBootsVecByteLoop.f6) frame flow) :
    NativeResidentVecBorrow.Resident flow.world (.reference mutable reference count) base capacity length buffer := by
  obtain ⟨preserved,heap⟩ := loop_code_incoming classification frame flow executed
  exact NativeIncomingReference.resident preserved view older heap

open NativeRecordDropCalls (Code Definition prepareCall prepareCall_worlds resumeCall Resume resumeScope loopArgument)

theorem resumeCall_incoming (entered : State) (caller : Frame) (target : Nat) (flow : Flow)
    (prior : Preserves entered flow.world) :
    Preserves entered (resumeCall entered caller target flow).world := by
  cases flow with
  | normal frame => exact prior
  | unwind world => exact prior
  | invalid world => exact prior
  | unsupported source world => exact prior
  | returned value world =>
    have first := NativeRecordLLBC.settle_incoming_projects entered (.returned value world) prior
    cases settled : NativeRecordLLBC.settle entered (.returned value world) with
    | normal frame => simpa only [resumeCall, settled, Flow.world, Resume.world] using first
    | invalid world => simpa only [resumeCall, settled, Flow.world, Resume.world] using first
    | unsupported source world => simpa only [resumeCall, settled, Flow.world, Resume.world] using first
    | unwind world => simpa only [resumeCall, settled, Flow.world, Resume.world] using first
    | returned result final =>
      cases stored : NativeRecordLLBC.write {caller with world := final} target result with
      | none => simpa only [resumeCall, settled, stored, Flow.world, Resume.world] using first
      | some changed =>
        have same := NativeRecordLLBC.write_world {caller with world := final} changed target result stored
        simpa only [resumeCall, settled, stored, Flow.world, Resume.world, same] using first

theorem evalCode_incoming (code : Code) (frame : Frame) (flow : Flow)
    (computed : evalCode code frame = some flow) : Preserves frame.world flow.world := by
  induction code generalizing frame flow with
  | done => simp only [evalCode, Option.some.injEq] at computed; subst flow; exact .refl _
  | native body next nextIH =>
    have first := NativeRecordLLBC.eval_incoming_projects body frame
    cases actual : NativeRecordLLBC.eval body frame with
    | normal middle =>
      rw [actual] at first
      exact first.trans (nextIH middle flow (by simpa only [evalCode, actual] using computed))
    | returned value world | unwind world | invalid world | unsupported source world =>
      rw [actual] at first
      simp only [evalCode, actual, Option.some.injEq] at computed
      subst flow
      exact first
  | scope body next bodyIH nextIH =>
    cases actual : evalCode body frame with
    | none => simp only [evalCode, actual] at computed; cases computed
    | some returned =>
      have first := bodyIH frame returned actual
      cases returned with
      | normal middle =>
        have cleanup := NativeIncomingReference.closeScope frame.world middle.world first
        by_cases cleaned : (NativeReferenceCleanup.closeScope frame.world middle.world).pending.isEmpty = true
        · exact cleanup.trans (nextIH {middle with world := (NativeReferenceCleanup.closeScope frame.world middle.world).world} flow
            (by simpa only [evalCode, actual, resumeScope, cleaned, ite_true] using computed))
        · simp only [evalCode, actual, resumeScope, cleaned, Bool.false_eq_true, ite_false, Option.some.injEq] at computed
          subst flow
          exact cleanup
      | returned value world | unwind world | invalid world | unsupported source world =>
        simp only [evalCode, actual, resumeScope, Option.some.injEq] at computed
        subst flow
        exact first
  | call name classification types count target args callee unwind next calleeIH unwindIH nextIH =>
    cases prepared : prepareCall frame types count args with
    | none =>
      simp only [evalCode, prepared, Option.some.injEq] at computed
      subst flow; exact .refl _
    | some pair =>
      rcases pair with ⟨caller,entered⟩
      have before := (prepareCall_worlds frame caller entered types count args prepared).2
      cases actual : evalCode callee entered with
      | none => simp only [evalCode, prepared, actual] at computed; cases computed
      | some returned =>
        have priorEntry : Preserves frame.world entered.world := by rw [before]; exact .refl _
        have first := priorEntry.trans (resumeCall_incoming entered.world caller target returned (calleeIH entered returned actual))
        cases resumed : resumeCall entered.world caller target returned with
        | next middle =>
          rw [resumed] at first
          exact first.trans (nextIH middle flow (by simpa only [evalCode, prepared, actual, resumed] using computed))
        | unwind middle =>
          rw [resumed] at first
          exact first.trans (unwindIH middle flow (by simpa only [evalCode, prepared, actual, resumed] using computed))
        | invalid world | unsupported source world =>
          rw [resumed] at first
          simp only [evalCode, prepared, actual, resumed, Option.some.injEq] at computed
          subst flow
          exact first
  | loop classification function =>
    by_cases same : function = HasteBootsVecByteLoop.f6
    · cases argument : loopArgument frame with
      | none =>
        simp only [evalCode, same, ite_true, argument, Option.some.injEq] at computed
        subst flow; exact .refl _
      | some slice =>
        simp only [evalCode, same, ite_true, argument, Option.some.injEq] at computed
        subst flow
        exact loopOutcome_incoming frame.world slice
    · simp only [evalCode, same, ite_false] at computed; cases computed

theorem invokeCode_incoming (function : Definition) (world : State) (args : List NativeRecordLLBC.Input) (flow : Flow)
    (computed : invokeCode function world args = some flow) : Preserves world flow.world := by
  cases decoded : NativeRecordLLBC.decodeArgs world args with
  | none => simp only [invokeCode, decoded, Option.some.injEq] at computed; subst flow; exact .refl _
  | some values =>
    cases initialized : NativeRecordLLBC.initial function.types function.argCount values world with
    | none => simp only [invokeCode, decoded, initialized, Option.some.injEq] at computed; subst flow; exact .refl _
    | some entered =>
      simp only [invokeCode, decoded, initialized, Option.map_eq_some_iff] at computed
      obtain ⟨returned,actual,same⟩ := computed
      subst flow
      have first := evalCode_incoming function.code entered returned actual
      rw [NativeRecordLLBC.initial_world function.types function.argCount values world entered initialized] at first
      exact NativeRecordLLBC.settle_incoming_projects world returned first
theorem invocation_incoming (function : Definition) (world : State) (args : List NativeRecordLLBC.Input) (flow : Flow)
    (checked : sourceLoops function.code = true) (invoked : NativeRecordDropCalls.Invokes function world args flow) :
    Preserves world flow.world := by
  have total := invokeCode_total function world args checked
  cases actual : invokeCode function world args with
  | none => rw [actual] at total; cases total
  | some other =>
    have same := NativeRecordDropCalls.invokes_deterministic function world args flow other invoked
      (invokeCode_sound function world args other actual)
    subst other
    exact invokeCode_incoming function world args flow actual

end HasteBootsVecDrop
