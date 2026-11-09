namespace HasteBootsVecDrop
open FormalProof4FHE.HasteBoots
open NativeReferenceMachine (State)
open NativeByteSliceIndex (Slice)
open NativeRecordLLBC (Frame Flow)

/-- The actual source loop outcome is a unit return under explicit reachable,
initialized, alias-available slice conditions. Cleanup success is derived. -/
theorem loopOutcome_complete_ready (world : State) (slice : Slice)
    (ready : NativeByteTraversalCompleteness.Ready world slice) :
    loopOutcome world slice = .returned (.scalar .unit) (NativeByteDropTraversal.run world slice).world ∧
      NativeByteTraversalCompleteness.Ready (NativeByteDropTraversal.run world slice).world slice ∧
      (NativeByteDropTraversal.run world slice).world.leases = world.leases := by
  have result := NativeByteTraversalCompleteness.run_complete world slice ready
  exact ⟨by simp only [loopOutcome,result.1,ite_true],result.2.1,result.2.2.1⟩

theorem loop_code_complete_ready (classification : NativeByteDropCalls.Classification) (frame : Frame) (slice : Slice)
    (argument : NativeRecordDropCalls.loopArgument frame = some slice)
    (ready : NativeByteTraversalCompleteness.Ready frame.world slice) :
    NativeRecordDropCalls.Runs (.loop classification HasteBootsVecByteLoop.f6) frame
      (.returned (.scalar .unit) (NativeByteDropTraversal.run frame.world slice).world) := by
  have actual := loopOutcome_runs classification frame slice argument
  rw [(loopOutcome_complete_ready frame.world slice ready).1] at actual
  exact actual
end HasteBootsVecDrop
