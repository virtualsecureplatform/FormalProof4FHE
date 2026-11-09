namespace HasteBootsVecDrop.Smoke
open FormalProof4FHE.HasteBoots
open NativeIncomingReference (Preserves)
open NativeRecordLLBC (Frame Flow)
private def incomingWorld : NativeReferenceMachine.State :=
  ((NativeSliceLLBC.issue (world 8 3) true (.raw ⟨⟨64,some ⟨64,0⟩⟩,some 3⟩) .byte).map Prod.snd).getD NativeReferenceMachine.empty
private def incomingSlice : NativeByteSliceIndex.Slice := ⟨⟨1⟩,3⟩
private def incomingFrame : Frame :=
  ⟨[.scalar .unit,.scalar (.reference true)],[.dead,.live (some (.scalar (.reference true ⟨1⟩ 3)))],incomingWorld⟩
private def incomingOutcome := loopOutcome incomingWorld incomingSlice
private theorem incomingRun : NativeRecordDropCalls.Runs (.loop .transparent HasteBootsVecByteLoop.f6) incomingFrame incomingOutcome :=
  loopOutcome_runs .transparent incomingFrame incomingSlice (by decide)
private theorem incomingView : NativeResidentVecBorrow.Resident incomingWorld (.reference true ⟨0⟩ 3) ⟨128,some ⟨128,1⟩⟩ 8 3 ⟨64,some ⟨64,0⟩⟩ := by
  refine ⟨true,⟨0⟩,3,⟨0,none,⟨128,some ⟨128,1⟩⟩,⟨24,8⟩,.exclusive⟩,rfl,
    by decide,by decide,rfl,rfl,Or.inl ⟨rfl,rfl⟩,by decide,?_⟩
  constructor <;> decide
example : Preserves incomingWorld incomingOutcome.world ∧ incomingOutcome.world.pointers.heap = incomingWorld.pointers.heap :=
  loop_code_incoming .transparent incomingFrame incomingOutcome incomingRun
example : NativeResidentVecBorrow.Resident incomingOutcome.world (.reference true ⟨0⟩ 3) ⟨128,some ⟨128,1⟩⟩ 8 3 ⟨64,some ⟨64,0⟩⟩ :=
  loop_code_resident .transparent incomingFrame incomingOutcome true ⟨0⟩ 3 8 3 ⟨128,some ⟨128,1⟩⟩ ⟨64,some ⟨64,0⟩⟩ incomingView (by decide) incomingRun
private def incomingAfter0 := (NativeByteDropTraversal.iteration incomingWorld incomingSlice 0).world
private def incomingAfter1 := (NativeByteDropTraversal.iteration incomingAfter0 incomingSlice 1).world
private def incomingAfter2 := (NativeByteDropTraversal.iteration incomingAfter1 incomingSlice 2).world
private theorem incomingComputed : NativeByteDropTraversal.run incomingWorld incomingSlice =
    ⟨incomingAfter2,3,some ⟨66,some ⟨64,0⟩⟩,true⟩ := by
  symm
  apply NativeByteDropTraversal.executes_result
  · apply NativeByteDropTraversal.Executes.next 0 incomingWorld incomingAfter0 none ⟨64,some ⟨64,0⟩⟩ _ (by decide) (by decide)
    apply NativeByteDropTraversal.Executes.next 1 incomingAfter0 incomingAfter1 (some ⟨64,some ⟨64,0⟩⟩) ⟨65,some ⟨64,0⟩⟩ _ (by decide) (by decide)
    apply NativeByteDropTraversal.Executes.next 2 incomingAfter1 incomingAfter2 (some ⟨65,some ⟨64,0⟩⟩) ⟨66,some ⟨64,0⟩⟩ _ (by decide) (by decide)
    exact .stop 3 incomingAfter2 (some ⟨66,some ⟨64,0⟩⟩) rfl
example : incomingOutcome = .returned (.scalar .unit) incomingOutcome.world ∧ incomingOutcome.world.nextTag = 8 ∧
    incomingOutcome.world.leases.map NativeByteBorrow.Lease.tag = [1,0] := by
  simp only [incomingOutcome,loopOutcome,incomingComputed]
  decide
-- Malformed loop arguments retain the original registry and complete heap.
private def badIncomingFrame : Frame := {incomingFrame with slots := [.dead,.live (some (.scalar (.usize 3)))]}
example : Preserves incomingWorld (.invalid incomingWorld : Flow).world ∧ incomingWorld.pointers.heap = incomingWorld.pointers.heap := by
  apply loop_code_incoming .transparent badIncomingFrame (.invalid incomingWorld)
  exact .loopArgumentInvalid .transparent _ _ (by decide)
-- An ended input lease remains ended through the rejected original source loop.
private def revokedWorld : NativeReferenceMachine.State :=
  (NativeReferenceMachine.execute incomingWorld (.endBorrow 0)).getD NativeReferenceMachine.empty
private def revokedFrame : Frame := {incomingFrame with world := revokedWorld}
private def revokedOutcome := loopOutcome revokedWorld incomingSlice
private theorem revokedRun : NativeRecordDropCalls.Runs (.loop .transparent HasteBootsVecByteLoop.f6) revokedFrame revokedOutcome :=
  loopOutcome_runs .transparent revokedFrame incomingSlice (by decide)
private theorem revokedComputed : NativeByteDropTraversal.run revokedWorld incomingSlice = ⟨revokedWorld,0,none,false⟩ := by
  symm
  apply NativeByteDropTraversal.executes_result
  · exact .fail 0 revokedWorld revokedWorld none (by decide) (by decide)
example : revokedOutcome = .invalid revokedWorld ∧ NativeByteBorrow.lookup revokedOutcome.world.leases 1 = none := by
  simp only [revokedOutcome,loopOutcome,revokedComputed]
  decide
private def byteMethodOutcome : Flow :=
  (invokeCode f2 incomingWorld [.vectorExclusiveReference 0]).get
    (invokeCode_total f2 incomingWorld [.vectorExclusiveReference 0] (by decide))
private theorem byteMethodInvoked : NativeRecordDropCalls.Invokes f2 incomingWorld [.vectorExclusiveReference 0] byteMethodOutcome :=
  invokeCode_sound f2 incomingWorld [.vectorExclusiveReference 0] byteMethodOutcome
    (Option.get_mem (invokeCode_total f2 incomingWorld [.vectorExclusiveReference 0] (by decide)))
-- An overlapping incoming data lease may reject the body; the header still survives.
example : Preserves incomingWorld byteMethodOutcome.world :=
  invocation_incoming f2 incomingWorld [.vectorExclusiveReference 0] byteMethodOutcome (by decide) byteMethodInvoked
example : NativeResidentVecBorrow.Resident byteMethodOutcome.world (.reference true ⟨0⟩ 3) ⟨128,some ⟨128,1⟩⟩ 8 3 ⟨64,some ⟨64,0⟩⟩ :=
  byte_method_resident incomingWorld [.vectorExclusiveReference 0] byteMethodOutcome true ⟨0⟩ 3 8 3
    ⟨128,some ⟨128,1⟩⟩ ⟨64,some ⟨64,0⟩⟩ incomingView (by decide) byteMethodInvoked
example : NativeByteBorrow.lookup byteMethodOutcome.world.leases 1 = NativeByteBorrow.lookup incomingWorld.leases 1 :=
  (invocation_incoming f2 incomingWorld [.vectorExclusiveReference 0] byteMethodOutcome (by decide) byteMethodInvoked).lookup 1 (by decide)
example : Preserves incomingWorld (execute incomingWorld [.vectorExclusiveReference 0]).world :=
  invokeCode_incoming f1 incomingWorld [.vectorExclusiveReference 0] _
    (Option.get_mem (invokeCode_total f1 incomingWorld [.vectorExclusiveReference 0] source_loops_checked))
end HasteBootsVecDrop.Smoke
