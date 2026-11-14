module
public import FormalProof4FHE.HasteBoots.HonestSetupInitialHistory
@[expose] public section

/-! Hash-only setup preserves the actual initialized history when another
honest key setup has already populated its cache and chronological query log. -/
namespace FormalProof4FHE.HasteBoots.HonestSetupContinuation
open OracleSpec OracleComp BinaryTree
noncomputable section
variable {F Cfg Input Digest : Type} [Field F]
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  {H : Cfg → ℕ} {b : ℕ} {ι : Type} {base : OracleSpec ι}

/-- Initial verifier invariants, including compatibility with every later shape. -/
structure Ready (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (shape : Cfg → Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) : Prop where
  coherent : CachedHashHandler.Coherent state.hash
  sound : RecordedCheckpointQueries.Sound shape state
  audited : CheckpointExecution.Audited enc dummy shape state
  compatible : ∀ nextShape, CheckpointShapeTransport.Compatible shape nextShape state.checkpoints

/-- A subsequent real setup preserves all initialized invariants and checkpoints. -/
theorem from_state (impl : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (shape : Cfg → Skeleton)
    {n : ℕ} (parameters : Fin n → RecordedPaddedSource.Parameters F Cfg H b)
    (tables : (i : Fin n) → RecordedPaddedSource.PhysicalMatrix (parameters i))
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (incoming : Ready enc dummy shape initial)
    (result : ((i : Fin n) → FullData Digest (Skeleton.perfect (H (parameters i).tag))) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : result ∈ support ((simulateQ (CheckpointExecution.handler impl enc dummy shape)
      (HonestMatrixSetupTrace.program enc parameters tables)).run initial)) :
    Ready enc dummy shape result.2 := by
  have valid := RecordedCheckpointQueries.run impl enc dummy shape
    (HonestMatrixSetupTrace.program enc parameters tables) initial
    ⟨incoming.coherent,incoming.sound⟩ result supported
  have audited := CheckpointExecution.audited_run impl enc dummy shape
    (HonestMatrixSetupTrace.program enc parameters tables) initial incoming.audited result supported
  have same := HonestMatrixSetupTrace.checkpoints impl enc dummy shape parameters tables initial result supported
  refine ⟨valid.1,valid.2,audited,?_⟩
  intro nextShape
  rw [same]
  exact incoming.compatible nextShape

/-- The first actual setup from empty establishes the same invariant interface. -/
theorem from_empty (impl : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (shape : Cfg → Skeleton)
    {n : ℕ} (parameters : Fin n → RecordedPaddedSource.Parameters F Cfg H b)
    (tables : (i : Fin n) → RecordedPaddedSource.PhysicalMatrix (parameters i))
    (result : ((i : Fin n) → FullData Digest (Skeleton.perfect (H (parameters i).tag))) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : result ∈ support ((simulateQ (CheckpointExecution.handler impl enc dummy shape)
      (HonestMatrixSetupTrace.program enc parameters tables)).run (CheckpointExecution.empty shape))) :
    Ready enc dummy shape result.2 := by
  have valid := HonestSetupInitialHistory.initialized impl enc dummy shape parameters tables result supported
  exact ⟨valid.1,valid.2.1,valid.2.2.1,valid.2.2.2⟩

omit [Field F] [SampleableType Digest] in
/-- Change the verifier geometry after setup while retaining its exact cache,
query log, failure bit and all initialized history invariants. -/
theorem transport (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (oldShape newShape : Cfg → Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) oldShape)
    (incoming : Ready enc dummy oldShape state) :
    Ready enc dummy newShape (CheckpointShapeTransport.state oldShape newShape state) := by
  refine ⟨incoming.coherent,CheckpointQueryHistory.transport_sound oldShape newShape state incoming.sound,
    CheckpointShapeTransport.audited enc dummy oldShape newShape state (incoming.compatible newShape) incoming.audited,?_⟩
  intro nextShape tag saved member
  change ⟨tag,saved⟩ ∈ (CheckpointShapeTransport.history oldShape newShape state.checkpoints).checkpoints at member
  obtain ⟨⟨oldTag,oldSaved⟩,present,equal⟩ := List.mem_map.mp member
  cases equal
  exact (incoming.compatible newShape oldTag oldSaved present).symm.trans
    (incoming.compatible nextShape oldTag oldSaved present)

omit [Field F] [SampleableType Digest] [DecidableEq Input] [DecidableEq Digest] in
/-- Reconfiguring geometry and returning restores the complete original state. -/
theorem state_roundtrip (oldShape newShape : Cfg → Skeleton)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) oldShape) :
    CheckpointShapeTransport.state newShape oldShape (CheckpointShapeTransport.state oldShape newShape state) = state := by
  cases state
  simp only [CheckpointShapeTransport.state,CheckpointShapeTransport.history_roundtrip]

end
end FormalProof4FHE.HasteBoots.HonestSetupContinuation
