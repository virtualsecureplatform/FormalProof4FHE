namespace HasteBootsReservationErrorKind
open FormalProof4FHE.HasteBoots
open NativeRecordLLBC
open NativeReferenceMachine (State)

theorem rootResume_projects (caller : Frame) (flow : Flow) :
    NativeStorageBorrowMachine.Runs flow.world (rootResume caller flow).world := by
  cases flow with
  | normal changed => exact .refl _
  | invalid world => exact .refl _
  | unsupported source world => exact .refl _
  | unwind world => exact NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects rootUnwind {caller with world})
  | returned value world =>
    cases written : write {caller with world} 0 value with
    | none => simp only [rootResume,written,Flow.world]; exact .refl _
    | some changed =>
      have projected := NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects rootTail changed)
      rw [write_world {caller with world} changed 0 value written] at projected
      simpa only [rootResume,written,Flow.world] using projected

theorem rootEval_projects (frame : Frame) : NativeStorageBorrowMachine.Runs frame.world (rootEval frame).world := by
  have first := NativeStorageBorrowMachine.legacy_runs _ _ (eval_projects rootPrefix frame)
  cases prefixed : eval rootPrefix frame with
  | returned value world => simpa only [rootEval,prefixed] using first
  | unwind world => simpa only [rootEval,prefixed] using first
  | invalid world => simpa only [rootEval,prefixed] using first
  | unsupported source world => simpa only [rootEval,prefixed] using first
  | normal prepared =>
    simp only [prefixed,Flow.world] at first
    cases selected : NativeRecordLLBC.read prepared 1 [] with
    | none => simpa only [rootEval,prefixed,selected,Flow.world] using first
    | some value =>
      have later := reborrow_projects prepared.world value
      cases issued : reborrow prepared.world value with
      | invalid world =>
        simp only [issued,NativeRawVecFields.Result.world] at later
        simpa only [rootEval,prefixed,selected,issued,Flow.world] using NativeStorageBorrowMachine.runs_trans _ _ _ first later
      | value reference world =>
        simp only [issued,NativeRawVecFields.Result.world] at later
        have entered := NativeStorageBorrowMachine.runs_trans _ _ _ first later
        cases written : write {prepared with world} 2 reference with
        | none => simpa only [rootEval,prefixed,selected,issued,written,Flow.world] using entered
        | some borrowed =>
          have sameBorrowed := write_world {prepared with world} borrowed 2 reference written
          cases arguments : evalArgs borrowed [.move 2 []] with
          | none => simpa only [rootEval,prefixed,selected,issued,written,arguments,Flow.world,sameBorrowed] using entered
          | some entry =>
            rcases entry with ⟨values,caller⟩
            have sameCaller := (evalArgs_world borrowed caller [.move 2 []] values arguments).trans sameBorrowed
            cases values with
            | nil => simpa only [rootEval,prefixed,selected,issued,written,arguments,Flow.world,sameCaller] using entered
            | cons argument rest =>
              cases rest with
              | nil =>
                have called := NativeStorageBorrowMachine.runs_trans _ _ _ (invoke_projects caller.world argument)
                  (rootResume_projects caller (invoke caller.world argument))
                have enteredCaller : NativeStorageBorrowMachine.Runs frame.world caller.world := by rw [sameCaller]; exact entered
                simpa only [rootEval,prefixed,selected,issued,written,arguments] using NativeStorageBorrowMachine.runs_trans _ _ _ enteredCaller called
              | cons next tail => simpa only [rootEval,prefixed,selected,issued,written,arguments,Flow.world,sameCaller] using entered

theorem rootInvoke_projects (world : State) (value : NativeRecordValues.Value) :
    NativeStorageBorrowMachine.Runs world (rootInvoke world value).world := by
  cases initialized : initial rootTypes 1 [value] world with
  | none => simp only [rootInvoke,initialized,Flow.world]; exact .refl _
  | some frame =>
    have projected := rootEval_projects frame
    rw [initial_world rootTypes 1 [value] world frame initialized] at projected
    simpa only [rootInvoke,initialized] using projected

theorem closeReturned_projects (entered : State) (flow : Flow) :
    NativeStorageBorrowMachine.Runs flow.world (closeReturned entered flow).world := by
  cases flow with
  | normal frame => exact .refl _
  | unwind world => exact .refl _
  | invalid world => exact .refl _
  | unsupported source world => exact .refl _
  | returned value world =>
    have projected := NativeStorageBorrowMachine.legacy_runs _ _ (NativeReferenceCleanup.closeScope_projects entered world)
    simp only [closeReturned]
    split <;> exact projected

theorem rootWithCleanup_projects (world : State) (value : NativeRecordValues.Value) :
    NativeStorageBorrowMachine.Runs world (rootWithCleanup world value).world :=
  NativeStorageBorrowMachine.runs_trans _ _ _ (rootInvoke_projects world value) (closeReturned_projects world (rootInvoke world value))

theorem rootWithCleanup_reachable (world : State) (value : NativeRecordValues.Value)
    (reachable : NativeStorageBorrowMachine.Reachable world) : NativeStorageBorrowMachine.Reachable (rootWithCleanup world value).world :=
  NativeStorageBorrowMachine.runs_trans _ _ _ reachable (rootWithCleanup_projects world value)

theorem rootWithCleanup_wellFormed (world : State) (value : NativeRecordValues.Value)
    (valid : NativeReferenceMachine.WellFormed world) : NativeReferenceMachine.WellFormed (rootWithCleanup world value).world :=
  NativeStorageBorrowMachine.runs_wellFormed _ _ valid (rootWithCleanup_projects world value)

end HasteBootsReservationErrorKind
