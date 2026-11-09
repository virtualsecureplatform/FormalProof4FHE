namespace HasteBootsVecDrop
open FormalProof4FHE.HasteBoots
open NativeRecordDropCalls
open NativeRecordLLBC (Frame Flow Input)
open NativeReferenceMachine (State)
open NativeByteSliceIndex (Slice)

theorem loop_zero (frame : Frame) (slice : Slice) (argument : loopArgument frame = some slice)
    (empty : slice.length.val = 0) :
    Runs (.loop .transparent HasteBootsVecByteLoop.f6) frame (.returned (.scalar .unit) frame.world) := by
  have zero : slice.length = ⟨0, by decide⟩ := Fin.ext empty
  apply Runs.loopRun .transparent HasteBootsVecByteLoop.f6 frame slice
    (HasteBootsVecByteLoop.entry frame.world slice)
    (.returned .unit (HasteBootsVecByteLoop.exit frame.world)) argument
    (HasteBootsVecByteLoop.initial_exact frame.world slice)
  apply NativeByteLoopLLBC.Executes.start _
    (HasteBootsVecByteLoop.head frame.world slice ⟨0, by decide⟩ none .dead .dead)
  · exact HasteBootsVecByteLoop.before_exact _ _
  · apply NativeByteLoopLLBC.LoopRuns.stop _ _ _
    · simpa only [zero] using HasteBootsVecByteLoop.body_stop frame.world slice none .dead .dead
    · exact HasteBootsVecByteLoop.after_exact _ _ _ _ _ _

theorem loop_complete (frame : Frame) (slice : Slice) (argument : loopArgument frame = some slice)
    (complete : (NativeByteDropTraversal.run frame.world slice).complete = true) :
    Runs (.loop .transparent HasteBootsVecByteLoop.f6) frame
      (.returned (.scalar .unit) (NativeByteDropTraversal.run frame.world slice).world) := by
  obtain ⟨flow, executed, observed⟩ := HasteBootsVecByteLoop.run_simulation frame.world slice
  have flag := congrArg Prod.snd observed
  change (HasteBootsVecByteLoop.observe flow).2 = (NativeByteDropTraversal.run frame.world slice).complete at flag
  rw [complete] at flag
  have output : fromLoop flow = .returned (.scalar .unit) (NativeByteDropTraversal.run frame.world slice).world := by
    cases flow with
    | returned value native =>
      cases value <;> cases flag
      have worldEq := congrArg Prod.fst observed
      change native.world = (NativeByteDropTraversal.run frame.world slice).world at worldEq
      exact congrArg (Flow.returned (.scalar .unit)) worldEq
    | normal native => cases flag
    | unwind native => cases flag
    | invalid native => cases flag
    | breaking native => cases flag
    | continuing native => cases flag
  rw [← output]
  exact .loopRun .transparent _ frame slice _ flow argument (HasteBootsVecByteLoop.initial_exact _ _) executed


theorem every_invocation_projects (world : State) (args : List Input) (flow : Flow)
    (invoked : Invokes f1 world args flow) : NativeReferenceMachine.Runs world flow.world :=
  invokes_projects f1 world args flow invoked

theorem every_invocation_reachable (world : State) (args : List Input) (flow : Flow)
    (reachable : NativeReferenceMachine.Reachable world) (invoked : Invokes f1 world args flow) :
    NativeReferenceMachine.Reachable flow.world := invokes_reachable f1 world args flow reachable invoked

theorem slice_classification_preserved : f3.classification = .foreignBody := rfl
end HasteBootsVecDrop
