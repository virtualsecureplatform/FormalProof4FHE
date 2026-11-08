namespace HasteBootsByteDropProbe
open FormalProof4FHE.HasteBoots
open NativeByteDropCalls
open NativeSliceLLBC (Frame Flow Value Ty)
open NativeReferenceMachine (State)
open NativePointerStorage (Pointer)
open NativeWord64Memory (Word)
open NativeByteSliceIndex (Slice)

def entry (function : Definition) (world : State) (args : List Value) : Option Frame :=
  NativeSliceLLBC.initial function.types function.argCount args world

theorem foreign_classification_preserved : f3.classification = .foreignBody := rfl

theorem parts_body (world : State) (pointer : Pointer) (length : Word) :
    ∃ frame, entry f1 world [.raw ⟨pointer,none⟩,.usize length] = some frame ∧
      Runs f1.code frame (.returned (.raw ⟨pointer,some length⟩) world) := by
  refine ⟨⟨[.raw true,.raw false,.usize], [.dead,.live (some (.raw ⟨pointer,none⟩)),.live (some (.usize length))],world⟩, rfl, ?_⟩
  apply Runs.nativeStop
  · rfl
  · rfl

theorem loop_zero (frame : Frame) (slice : Slice) (argument : loopArgument frame = some slice)
    (empty : slice.length.val = 0) :
    Runs (.loop .transparent HasteBootsByteLoopBody.f4) frame (.returned .unit frame.world) := by
  have zero : slice.length = ⟨0, by decide⟩ := Fin.ext empty
  apply Runs.loopRun .transparent HasteBootsByteLoopBody.f4 frame slice
    (HasteBootsByteLoopBody.entry frame.world slice)
    (.returned .unit (HasteBootsByteLoopBody.exit frame.world)) argument
    (HasteBootsByteLoopBody.initial_exact frame.world slice)
  apply NativeByteLoopLLBC.Executes.start _
    (HasteBootsByteLoopBody.head frame.world slice ⟨0, by decide⟩ none .dead .dead)
  · exact HasteBootsByteLoopBody.before_exact _ _
  · apply NativeByteLoopLLBC.LoopRuns.stop _ _ _
    · simpa only [zero] using HasteBootsByteLoopBody.body_stop frame.world slice none .dead .dead
    · exact HasteBootsByteLoopBody.after_exact _ _ _ _ _ _

theorem loop_complete (frame : Frame) (slice : Slice) (argument : loopArgument frame = some slice)
    (complete : (NativeByteDropTraversal.run frame.world slice).complete = true) :
    Runs (.loop .transparent HasteBootsByteLoopBody.f4) frame
      (.returned .unit (NativeByteDropTraversal.run frame.world slice).world) := by
  obtain ⟨flow, executed, observed⟩ := HasteBootsByteLoopBody.run_simulation frame.world slice
  have flag := congrArg Prod.snd observed
  change (HasteBootsByteLoopBody.observe flow).2 = (NativeByteDropTraversal.run frame.world slice).complete at flag
  rw [complete] at flag
  have output : fromLoop flow = .returned .unit (NativeByteDropTraversal.run frame.world slice).world := by
    cases flow with
    | returned value native =>
      cases value <;> cases flag
      have worldEq := congrArg Prod.fst observed
      change native.world = (NativeByteDropTraversal.run frame.world slice).world at worldEq
      exact congrArg (Flow.returned .unit) worldEq
    | normal native => cases flag
    | unwind native => cases flag
    | invalid native => cases flag
    | breaking native => cases flag
    | continuing native => cases flag
  rw [← output]
  exact .loopRun .transparent _ frame slice _ flow argument (HasteBootsByteLoopBody.initial_exact _ _) executed

theorem every_invocation_projects (world : State) (args : List NativeSliceLLBC.Input) (flow : Flow)
    (invoked : Invokes f0 world args flow) : NativeReferenceMachine.Runs world flow.world :=
  invokes_projects f0 world args flow invoked

end HasteBootsByteDropProbe
