namespace HasteBootsVecDrop.Smoke
open FormalProof4FHE.HasteBoots
private theorem traversalIncomingReachable : NativeReferenceMachine.Reachable incomingWorld := by
  have entered : NativeReferenceMachine.Reachable (world 8 3) := by
    apply NativeReferenceMachine.run_reachable NativeReferenceMachine.empty (world 8 3) .empty
      [.raw (.allocate 64 ⟨8,1⟩),.raw (.writeBytes 0 1 (List.replicate 8 0)),
       .raw (.allocate 128 ⟨24,8⟩),.raw (.writeBytes 0 8 (NativeWord64Memory.encode 8)),
       .raw (.withAddress 0 136),.raw (.store 0 2),.raw (.withAddress 1 144),
       .raw (.writeBytes 0 8 (NativeWord64Memory.encode 3)),.borrow 2 .exclusive ⟨24,8⟩]
    decide
  apply NativeSliceLLBC.reference_runs_reachable (world 8 3) incomingWorld entered
  exact NativeSliceLLBC.issue_projects (world 8 3) incomingWorld true (.raw ⟨⟨64,some ⟨64,0⟩⟩,some 3⟩)
    (.reference true ⟨1⟩ 3) (by decide : NativeSliceLLBC.issue (world 8 3) true
      (.raw ⟨⟨64,some ⟨64,0⟩⟩,some 3⟩) .byte = some (.reference true ⟨1⟩ 3,incomingWorld))
private def traversalDataLease : NativeByteBorrow.Lease := ⟨1,none,⟨64,some ⟨64,0⟩⟩,⟨3,1⟩,.exclusive⟩
private def traversalHeaderLease : NativeByteBorrow.Lease := ⟨0,none,⟨128,some ⟨128,1⟩⟩,⟨24,8⟩,.exclusive⟩
private theorem traversalIncomingReady : NativeByteTraversalCompleteness.Ready incomingWorld incomingSlice := by
  refine ⟨traversalIncomingReachable,traversalDataLease,by decide,by decide,by decide,rfl,?_,[0,0,0],by decide⟩
  refine ⟨rfl,by decide,?_⟩
  intro other member
  have leases : incomingWorld.leases = [traversalDataLease,traversalHeaderLease] := by decide
  change other ∈ incomingWorld.leases at member
  rw [leases] at member
  rcases List.mem_cons.mp member with same | later
  · exact Or.inl (congrArg NativeByteBorrow.Lease.tag same)
  · have same := List.mem_singleton.mp later
    subst other
    exact Or.inr (Or.inr (by decide))
private theorem traversalSourceRun : NativeRecordDropCalls.Runs (.loop .transparent HasteBootsVecByteLoop.f6) incomingFrame
    (.returned (.scalar .unit) (NativeByteDropTraversal.run incomingWorld incomingSlice).world) :=
  loop_code_complete_ready .transparent incomingFrame incomingSlice (by decide) traversalIncomingReady
example : NativeRecordDropCalls.Runs (.loop .transparent HasteBootsVecByteLoop.f6) incomingFrame
    (.returned (.scalar .unit) (NativeByteDropTraversal.run incomingWorld incomingSlice).world) := traversalSourceRun
example : NativeResidentVecBorrow.Resident (NativeByteDropTraversal.run incomingWorld incomingSlice).world
    (.reference true ⟨0⟩ 3) ⟨128,some ⟨128,1⟩⟩ 8 3 ⟨64,some ⟨64,0⟩⟩ :=
  loop_code_resident .transparent incomingFrame _ true ⟨0⟩ 3 8 3 ⟨128,some ⟨128,1⟩⟩ ⟨64,some ⟨64,0⟩⟩ incomingView (by decide) traversalSourceRun
example : NativeRecordDropCalls.Runs (.loop .transparent HasteBootsVecByteLoop.f6)
    {incomingFrame with world := (NativeByteDropTraversal.run incomingWorld incomingSlice).world}
    (.returned (.scalar .unit) (NativeByteDropTraversal.run (NativeByteDropTraversal.run incomingWorld incomingSlice).world incomingSlice).world) :=
  loop_code_complete_ready .transparent _ incomingSlice (by decide) (loopOutcome_complete_ready _ _ traversalIncomingReady).2.1
end HasteBootsVecDrop.Smoke
