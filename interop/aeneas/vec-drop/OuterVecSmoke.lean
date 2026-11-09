namespace HasteBootsVecDrop.Smoke
open FormalProof4FHE.HasteBoots
open NativeResidentVecBorrow
open NativeRecordLLBC (Flow)
private def outerOutcome : Flow := execute reservedReady [.vectorExclusiveReference 0]
private theorem outerInvoked : NativeRecordDropCalls.Invokes f1 reservedReady [.vectorExclusiveReference 0] outerOutcome :=
  (invocation_iff_execute reservedReady [.vectorExclusiveReference 0] outerOutcome).mpr rfl
private theorem outerView : Resident reservedReady (.reference true ⟨0⟩ 3) ⟨128,some ⟨128,1⟩⟩ 8 0 ⟨64,some ⟨64,0⟩⟩ := by
  refine ⟨true,⟨0⟩,3,⟨0,none,⟨128,some ⟨128,1⟩⟩,⟨24,8⟩,.exclusive⟩,rfl,
    by decide,by decide,rfl,rfl,Or.inl ⟨rfl,rfl⟩,by decide,?_⟩
  constructor <;> decide
private def outerEmptyOutcome : Flow := execute emptyReady [.vectorExclusiveReference 0]
private theorem outerEmptyInvoked : NativeRecordDropCalls.Invokes f1 emptyReady [.vectorExclusiveReference 0] outerEmptyOutcome :=
  (invocation_iff_execute emptyReady [.vectorExclusiveReference 0] outerEmptyOutcome).mpr rfl
private theorem outerEmptyView : Resident emptyReady (.reference true ⟨0⟩ 3) ⟨128,some ⟨128,0⟩⟩ 0 0 ⟨1,none⟩ := by
  refine ⟨true,⟨0⟩,3,⟨0,none,⟨128,some ⟨128,0⟩⟩,⟨24,8⟩,.exclusive⟩,rfl,
    by decide,by decide,rfl,rfl,Or.inl ⟨rfl,rfl⟩,by decide,?_⟩
  constructor <;> decide
private theorem outerFacts : outerOutcome = .returned (.scalar .unit) outerOutcome.world ∧
    outerOutcome.world.nextTag = 9 ∧ outerOutcome.world.leases.map NativeByteBorrow.Lease.tag = [0] ∧
    outerOutcome.world.pointers.heap ≠ reservedReady.pointers.heap := by
  have certificate : ∃ flow, NativeRecordDropCalls.Invokes f1 reservedReady [.vectorExclusiveReference 0] flow ∧
      flow = .returned (.scalar .unit) flow.world ∧ flow.world.nextTag = 9 ∧
      flow.world.leases.map NativeByteBorrow.Lease.tag = [0] ∧ flow.world.pointers.heap ≠ reservedReady.pointers.heap := by
    econstructor
    constructor
    · apply NativeRecordDropCalls.Invokes.run [.scalar (.reference true ⟨0⟩ 3)]
      · decide
      · rfl
      · run_vec_drop
    · decide
  obtain ⟨flow,invoked,facts⟩ := certificate
  have same := (invocation_iff_execute reservedReady [.vectorExclusiveReference 0] flow).mp invoked
  simpa only [same,outerOutcome] using facts
private theorem outerEmptyFacts : outerEmptyOutcome = .returned (.scalar .unit) outerEmptyOutcome.world ∧
    outerEmptyOutcome.world.nextTag = 8 := by
  have certificate : ∃ flow, NativeRecordDropCalls.Invokes f1 emptyReady [.vectorExclusiveReference 0] flow ∧
      flow = .returned (.scalar .unit) flow.world ∧ flow.world.nextTag = 8 := by
    econstructor
    constructor
    · apply NativeRecordDropCalls.Invokes.run [.scalar (.reference true ⟨0⟩ 3)]
      · decide
      · rfl
      · run_vec_drop
    · decide
  obtain ⟨flow,invoked,facts⟩ := certificate
  have same := (invocation_iff_execute emptyReady [.vectorExclusiveReference 0] flow).mp invoked
  simpa only [same,outerEmptyOutcome] using facts
example : VecDeallocationPost reservedReady ⟨64,some ⟨64,0⟩⟩ 8 outerOutcome :=
  vec_glue_invokes reservedReady ⟨0⟩ ⟨128,some ⟨128,1⟩⟩ ⟨64,some ⟨64,0⟩⟩ 8 0 outerView (by decide) outerOutcome outerInvoked
example : 0 < (8 : NativeWord64Memory.Word).val ∧ ∃ block ∈ reservedReady.pointers.heap.memory.blocks,
    block.pointer = ⟨64,some ⟨64,0⟩⟩ ∧ block.layout = ⟨8,1⟩ ∧
    NativePointerByteMemory.deallocate reservedReady.pointers.heap block.pointer block.layout = some outerOutcome.world.pointers.heap :=
  vec_glue_changed_block reservedReady ⟨0⟩ ⟨128,some ⟨128,1⟩⟩ ⟨64,some ⟨64,0⟩⟩ 8 0 outerView (by decide) outerOutcome outerInvoked outerFacts.2.2.2
-- Length zero needs no initialized bytes in the reserved capacity.
example : outerOutcome = .returned (.scalar .unit) outerOutcome.world ∧ outerOutcome.world.nextTag = 9 ∧
    outerOutcome.world.leases.map NativeByteBorrow.Lease.tag = [0] :=
  ⟨outerFacts.1,outerFacts.2.1,outerFacts.2.2.1⟩
example : outerEmptyOutcome.world.pointers.heap = emptyReady.pointers.heap :=
  vec_glue_invokes_zero emptyReady ⟨0⟩ ⟨128,some ⟨128,0⟩⟩ ⟨1,none⟩ 0 outerEmptyView (by decide) outerEmptyOutcome outerEmptyInvoked
example : outerEmptyOutcome = .returned (.scalar .unit) outerEmptyOutcome.world ∧ outerEmptyOutcome.world.nextTag = 8 := outerEmptyFacts
-- Revoking the incoming header rejects both actual source RawVec continuations.
private def outerRevokedWorld : NativeReferenceMachine.State :=
  (NativeReferenceMachine.execute incomingWorld (.endBorrow 1)).getD NativeReferenceMachine.empty
example : evalCode (vecRawStage true) (vecRootFrame outerRevokedWorld ⟨0⟩ (.live none)) =
    some (.invalid outerRevokedWorld) := by decide
example : evalCode (vecRawStage false) (vecRootFrame outerRevokedWorld ⟨0⟩ (.live (some (.scalar .unit)))) =
    some (.invalid outerRevokedWorld) := by decide
-- The public all-outcome theorem also covers the previously retained failure fixture.
example : VecDeallocationPost incomingWorld ⟨64,some ⟨64,0⟩⟩ 8 (execute incomingWorld [.vectorExclusiveReference (incomingWorld.references.idxOf ⟨0⟩)]) :=
  vec_glue_invokes incomingWorld ⟨0⟩ ⟨128,some ⟨128,1⟩⟩ ⟨64,some ⟨64,0⟩⟩ 8 3 incomingView (by decide) _
    (execute_invokes incomingWorld [.vectorExclusiveReference (incomingWorld.references.idxOf ⟨0⟩)])
end HasteBootsVecDrop.Smoke
