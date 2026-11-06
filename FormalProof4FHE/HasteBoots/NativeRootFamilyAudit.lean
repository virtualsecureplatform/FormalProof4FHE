module

public import FormalProof4FHE.HasteBoots.NativeGoldBatchFamilyAvailability
public import FormalProof4FHE.HasteBoots.NativeRootFamilyHistory
@[expose] public section

/-! Truthful complete histories reconstruct an audited fixed-shape-family state. Hash collisions and the source-failure flag persist under further truthful observations. Their actual ideal-oracle probability is bounded by the shared accumulated hash charge. -/
namespace FormalProof4FHE.HasteBoots.NativeRootFamilyAudit
open NativeMerkleShapeFamily (Tag shape)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (Input World)
open NativeGoldColumnAuthentication (encoding)
open NativeRootFamilyState (State record)
open NativeGoldBatchFamilyAvailability (reconstructed)
open OracleSpec OracleComp MeasureTheory
noncomputable section

theorem roots_stable (roots : List (Tag × Digest))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) (dummy : Digest)
    (stable : state.failed = false → MerklePayloadCheckpoints.StableAt encoding dummy shape state.checkpoints state.hash.log) :
    (RecordRoots.state shape roots state).failed = false →
      MerklePayloadCheckpoints.StableAt encoding dummy shape (RecordRoots.state shape roots state).checkpoints (RecordRoots.state shape roots state).hash.log := by
  induction roots generalizing state with
  | nil => exact stable
  | cons root rest ih =>
    apply ih
    intro clear
    exact MerklePayloadCheckpoints.stable_record encoding dummy shape state.checkpoints state.hash.log (stable clear) root.1 root.2

theorem record_stable (state : State) (entry : Observation) (dummy : Digest)
    (stable : state.2.failed = false → MerklePayloadCheckpoints.StableAt encoding dummy shape state.2.checkpoints state.2.hash.log) :
    (record encoding dummy state entry).2.failed = false →
      MerklePayloadCheckpoints.StableAt encoding dummy shape (record encoding dummy state entry).2.checkpoints
        (record encoding dummy state entry).2.hash.log := by
  cases entry with
  | start input => exact stable
  | hash input digest => exact CheckpointExecution.afterHash_clear_stable encoding dummy shape state.2 _
  | output input offset values =>
    simp only [record]
    split
    · exact stable
    · exact roots_stable _ state.2 dummy stable

theorem fold_stable (state : State) (history : List Observation) (dummy : Digest)
    (stable : state.2.failed = false → MerklePayloadCheckpoints.StableAt encoding dummy shape state.2.checkpoints state.2.hash.log) :
    (history.foldl (record encoding dummy) state).2.failed = false →
      MerklePayloadCheckpoints.StableAt encoding dummy shape (history.foldl (record encoding dummy) state).2.checkpoints
        (history.foldl (record encoding dummy) state).2.hash.log := by
  induction history generalizing state with
  | nil => exact stable
  | cons entry rest ih => exact ih _ (record_stable state entry dummy stable)

theorem reconstructed_audited (dummy : Digest) (world : World) (history : List Observation)
    (truthful : ObservationReplay.Agrees world history) :
    CheckpointExecution.Audited encoding dummy shape (reconstructed dummy history) := by
  constructor
  · rw [NativeGoldBatchFamilyAvailability.reconstructed_hash]
    exact (JointHashCache.project_valid world history truthful).1
  · exact fold_stable _ history dummy (fun _ => MerklePayloadCheckpoints.stable_empty encoding dummy shape _)

theorem roots_failed (roots : List (Tag × Digest))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    (RecordRoots.state shape roots state).failed = state.failed := by
  induction roots generalizing state with
  | nil => rfl
  | cons root rest ih => exact ih _

theorem record_failed (state : State) (entry : Observation) (dummy : Digest) (failed : state.2.failed = true) :
    (record encoding dummy state entry).2.failed = true := by
  cases entry with
  | start input => exact failed
  | hash input digest => exact (CheckpointExecution.afterHash_failed_iff encoding dummy shape state.2 _).mpr (Or.inl failed)
  | output input offset values =>
    simp only [record]
    split
    · exact failed
    · rw [roots_failed]; exact failed

theorem fold_failed (state : State) (history : List Observation) (dummy : Digest) (failed : state.2.failed = true) :
    (history.foldl (record encoding dummy) state).2.failed = true := by
  induction history generalizing state with
  | nil => exact failed
  | cons entry rest ih => exact ih _ (record_failed state entry dummy failed)

theorem cache_mono (world : World) (earlier later : List Observation)
    (truthful : ObservationReplay.Agrees world later) (growing : earlier.IsPrefix later) :
    (JointHashCache.project earlier).cache ≤ (JointHashCache.project later).cache := by
  have prior : ObservationReplay.Agrees world earlier := fun entry member => truthful entry (growing.sublist.subset member)
  have valid := JointHashCache.project_valid world earlier prior
  intro input answer known
  have key := (valid.1.mem_keys_iff input).mpr ⟨answer,known⟩
  rw [JointHashCache.project_keys,List.mem_toFinset] at key
  obtain ⟨raw,observed⟩ := (JointHashCache.mem_hashInputs earlier input).mp key
  have same : List.ofFn answer = raw := by
    rw [valid.2 input answer known]
    exact prior _ observed
  rw [← same] at observed
  exact NativeHashOracleBridge.cache_known world later truthful input answer (growing.sublist.subset observed)

/-- A true source-failure flag or hash collision cannot be repaired by later truthful native observations. -/
theorem bad_persistent (dummy : Digest) (world : World) (earlier later : List Observation)
    (truthful : ObservationReplay.Agrees world later) (growing : earlier.IsPrefix later)
    (bad : CheckpointCollision.Bad shape (reconstructed dummy earlier)) :
    CheckpointCollision.Bad shape (reconstructed dummy later) := by
  rcases bad with failed | collision
  · obtain ⟨suffix,rfl⟩ := growing
    apply Or.inl
    simpa only [reconstructed,List.foldl_append,NativeRootFamilyHistory.reconstruct,NativeRootFamilyHistory.initial] using
      fold_failed (NativeRootFamilyHistory.reconstruct encoding dummy earlier) suffix dummy failed
  · apply Or.inr
    rw [NativeGoldBatchFamilyAvailability.reconstructed_hash] at collision ⊢
    exact CachedHashCollision.collision_mono _ _ (cache_mono world earlier later truthful growing) collision

theorem disagreement_implies_bad (dummy : Digest) (world : World) (history : List Observation)
    (truthful : ObservationReplay.Agrees world history)
    (different : CheckpointAvailability.Disagreement encoding dummy shape (reconstructed dummy history)) :
    CheckpointCollision.Bad shape (reconstructed dummy history) :=
  CheckpointAvailability.disagreement_implies_bad encoding dummy shape _ (reconstructed_audited dummy world history truthful) different
local instance digestDecisions : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

/-- The actual global persistent bad-state event has one accumulated hash charge. -/
theorem bad_le_charge {A : Type} (dummy : Digest) (program : OracleProgram.Program A) :
    InputIndexedOracle.law {world | CheckpointCollision.Bad shape (reconstructed dummy (OracleProgram.run program world).run.2)} ≤
    ExpectedHazard.charge
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) encoding dummy shape)
      (CheckpointCollision.loss unifSpec shape)
      ((NativeRootFamilyFreeze.compile NativeParentLedger.empty program).run NativeShakeCache.empty)
      (CheckpointExecution.empty shape) := by
  have law := NativeRootFamilyState.from_empty program encoding dummy
    (fun result => CheckpointCollision.Bad shape result.2)
  change InputIndexedOracle.law {world | CheckpointCollision.Bad shape
      (reconstructed dummy (OracleProgram.run program world).run.2)} = _ at law
  rw [law]
  unfold NativeRootFamilyFreeze.execute
  have decisions : (fun left right : Digest => Fintype.decidablePiFintype left right) = digestDecisions := Subsingleton.elim _ _
  rw [decisions]
  exact CheckpointCollision.failure_le_charge (QueryImpl.ofLift unifSpec ProbComp) encoding dummy shape
    ((NativeRootFamilyFreeze.compile NativeParentLedger.empty program).run NativeShakeCache.empty)
    (CheckpointExecution.empty shape) (CheckpointCollision.safe_empty encoding dummy shape)

end
end FormalProof4FHE.HasteBoots.NativeRootFamilyAudit
