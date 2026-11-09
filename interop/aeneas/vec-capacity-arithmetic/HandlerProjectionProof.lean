namespace HasteBootsVecCapacityArithmetic
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC

theorem handlerResume_projects (overflow allocation : Body) (caller : Frame) (flow : Flow) :
    NativeStorageBorrowMachine.Runs flow.world (handlerResume overflow allocation caller flow).world := by
  cases flow with
  | normal changed => exact .refl _
  | invalid world => exact .refl _
  | unsupported source world => exact .refl _
  | unwind world => exact NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects (handlerCleanup .resume) {caller with world})
  | returned value world =>
    cases written : write {caller with world} 2 value with
    | none => simp only [handlerResume,written,Flow.world]; exact .refl _
    | some changed =>
      have projected := NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects (handlerTail overflow allocation) changed)
      rw [write_world {caller with world} changed 2 value written] at projected
      simpa only [handlerResume,written,Flow.world] using projected

theorem handlerEval_projects (base : NativePointerStorage.Address) (overflow allocation : Body) (frame : Frame) :
    NativeStorageBorrowMachine.Runs frame.world (handlerEval base overflow allocation frame).world := by
  have first := NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects handlerPrefix frame)
  cases prefixed : eval handlerPrefix frame with
  | returned value world => simpa only [handlerEval,prefixed] using first
  | unwind world => simpa only [handlerEval,prefixed] using first
  | invalid world => simpa only [handlerEval,prefixed] using first
  | unsupported source world => simpa only [handlerEval,prefixed] using first
  | normal prepared =>
    simp only [prefixed,Flow.world] at first
    have later := NativeReservationErrorLocal.snapshotLocal_projects reservationErrorTags prepared 1 base
    cases issued : NativeReservationErrorLocal.snapshotLocal reservationErrorTags prepared 1 base with
    | invalid world =>
      simp only [issued,NativeRawVecFields.Result.world] at later
      simpa only [handlerEval,prefixed,issued,Flow.world] using NativeStorageBorrowMachine.runs_trans _ _ _ first later
    | value reference world =>
      simp only [issued,NativeRawVecFields.Result.world] at later
      have entered := NativeStorageBorrowMachine.runs_trans _ _ _ first later
      cases written : write {prepared with world} 3 reference with
      | none => simpa only [handlerEval,prefixed,issued,written,Flow.world] using entered
      | some borrowed =>
        have sameBorrowed := write_world {prepared with world} borrowed 3 reference written
        cases arguments : evalArgs borrowed [.move 3 []] with
        | none => simpa only [handlerEval,prefixed,issued,written,arguments,Flow.world,sameBorrowed] using entered
        | some entry =>
          rcases entry with ⟨values,caller⟩
          have sameCaller := (evalArgs_world borrowed caller [.move 3 []] values arguments).trans sameBorrowed
          cases values with
          | nil => simpa only [handlerEval,prefixed,issued,written,arguments,Flow.world,sameCaller] using entered
          | cons argument rest =>
            cases rest with
            | nil =>
              have called := NativeStorageBorrowMachine.runs_trans _ _ _
                (HasteBootsReservationErrorKind.invoke_projects_for reservationErrorTags caller.world argument)
                (handlerResume_projects overflow allocation caller
                  (HasteBootsReservationErrorKind.invokeFor reservationErrorTags caller.world argument))
              have enteredCaller : NativeStorageBorrowMachine.Runs frame.world caller.world := by rw [sameCaller]; exact entered
              simpa only [handlerEval,prefixed,issued,written,arguments] using NativeStorageBorrowMachine.runs_trans _ _ _ enteredCaller called
            | cons next tail => simpa only [handlerEval,prefixed,issued,written,arguments,Flow.world,sameCaller] using entered

theorem handlerInvoke_projects (world : NativeReferenceMachine.State) (base : NativePointerStorage.Address)
    (overflow allocation : Body) (value : NativeRecordValues.Value) :
    NativeStorageBorrowMachine.Runs world (handlerInvoke world base overflow allocation value).world := by
  cases initialized : initial handlerTypes 1 [value] world with
  | none => simp only [handlerInvoke,initialized,Flow.world]; exact .refl _
  | some frame =>
    have projected := handlerEval_projects base overflow allocation frame
    rw [initial_world handlerTypes 1 [value] world frame initialized] at projected
    simpa only [handlerInvoke,initialized] using projected

theorem handlerInvoke_reachable (world : NativeReferenceMachine.State) (base : NativePointerStorage.Address)
    (overflow allocation : Body) (value : NativeRecordValues.Value) (reachable : NativeStorageBorrowMachine.Reachable world) :
    NativeStorageBorrowMachine.Reachable (handlerInvoke world base overflow allocation value).world :=
  NativeStorageBorrowMachine.runs_trans _ _ _ reachable (handlerInvoke_projects world base overflow allocation value)

theorem handlerInvoke_wellFormed (world : NativeReferenceMachine.State) (base : NativePointerStorage.Address)
    (overflow allocation : Body) (value : NativeRecordValues.Value) (valid : NativeReferenceMachine.WellFormed world) :
    NativeReferenceMachine.WellFormed (handlerInvoke world base overflow allocation value).world :=
  NativeStorageBorrowMachine.runs_wellFormed _ _ valid (handlerInvoke_projects world base overflow allocation value)

end HasteBootsVecCapacityArithmetic
