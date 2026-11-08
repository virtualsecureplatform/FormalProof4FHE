namespace HasteBootsByteLoopSmoke
open FormalProof4FHE.HasteBoots
open NativeByteLoopLLBC HasteBootsByteLoopBody

private def ready (length : Nat) : NativeReferenceMachine.State :=
  (NativeReferenceMachine.run NativeReferenceMachine.empty
    [.raw (.allocate ⟨64, by decide⟩ ⟨8,8⟩), .raw (.writeBytes 0 8 (List.replicate 8 0)), .borrow 0 .exclusive ⟨length,1⟩]).getD NativeReferenceMachine.empty
private def slice3 : NativeByteSliceIndex.Slice := ⟨⟨0⟩,⟨3, by decide⟩⟩
private def slice0 : NativeByteSliceIndex.Slice := ⟨⟨0⟩,⟨0, by decide⟩⟩

example : decodeSlice (ready 3) 0 = some slice3 := by decide

example : (match eval f4.body (head (ready 3) slice3 ⟨0, by decide⟩ none .dead .dead) with
    | .continuing frame => (frame.world.nextTag, readLocal frame 3,
        readLocal frame 6, readLocal frame 7)
    | _ => (99,none,none,none)) =
    (3,some (.usize ⟨1, by decide⟩),none,some (.byteRef ⟨2⟩)) := by decide

example : (match settle (ready 3) (eval f4.body (head (ready 3) slice3 ⟨0, by decide⟩ none .dead .dead)) with
    | .continuing frame => (frame.world.nextTag, frame.world.leases.map NativeByteBorrow.Lease.tag,
        frame.world.pointers.heap == (ready 3).pointers.heap)
    | _ => (99,[],false)) = (3,[0],true) := by decide

example : eval f4.body (head (ready 0) slice0 ⟨0, by decide⟩ none .dead .dead) =
    .breaking (head (ready 0) slice0 ⟨0, by decide⟩ none .dead .dead) := by decide

example : Invokes f4 (ready 0) 0 (.returned .unit (exit (ready 0))) := by
  apply Invokes.valid slice0 (entry (ready 0) slice0)
  · decide
  · exact initial_exact _ _
  · apply Executes.start _ (head (ready 0) slice0 ⟨0, by decide⟩ none .dead .dead)
    · exact before_exact _ _
    · exact .stop _ _ _ (body_stop _ _ _ _ _) (after_exact _ _ _ _ _ _)

example : ∃ flow, Invokes f4 (ready 3) 0 flow ∧ flow.world.nextTag = 7 ∧
    flow.world.leases.map NativeByteBorrow.Lease.tag = [0] := by
  obtain ⟨flow, invoked, observed⟩ := invoke_simulation (ready 3) 0 slice3 (by decide)
  have worldEq := congrArg Prod.fst observed
  change flow.world = (NativeByteDropTraversal.run (ready 3) slice3).world at worldEq
  refine ⟨flow,invoked,?_,?_⟩
  · rw [worldEq]
    simp [NativeByteDropTraversal.run, NativeByteDropTraversal.runFrom, slice3]
    decide
  · rw [worldEq]
    conv_lhs => simp [NativeByteDropTraversal.run, NativeByteDropTraversal.runFrom, slice3]
    decide

private def blocked : NativeReferenceMachine.State :=
  (NativeByteSliceIndex.index (ready 3) slice3 ⟨1, by decide⟩).world

example : ∃ flow, Invokes f4 blocked 1 flow ∧ observe flow = (blocked,false) := by
  obtain ⟨flow,invoked,observed⟩ := invoke_simulation blocked 1 slice3 (by decide)
  refine ⟨flow,invoked,?_⟩
  rw [observed]
  simp [NativeByteDropTraversal.run, NativeByteDropTraversal.runFrom, slice3]
  decide

end HasteBootsByteLoopSmoke
