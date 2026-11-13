module
public import FormalProof4FHE.HasteBoots.HonestMatrixSetupTrace
public import FormalProof4FHE.HasteBoots.CheckpointQueryHistory
@[expose] public section

/-! Actual hash-only honest setup establishes the initial PBS history conditions
without dropping checkpoints or resetting its cache, query log or monitor. -/
namespace FormalProof4FHE.HasteBoots.HonestSetupInitialHistory
open OracleSpec OracleComp BinaryTree
noncomputable section
attribute [local irreducible] MonadAttach.support
variable {F Cfg Input Digest : Type} [Field F] [DecidableEq Input] [DecidableEq Digest]
  [SampleableType Digest] {H : Cfg → ℕ} {b : ℕ} {ι : Type} {base : OracleSpec ι}

/-- Honest setup from empty derives coherence, frozen-cache receipts, the
actual audit and compatibility with every later extraction geometry. -/
theorem initialized (impl : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (shape : Cfg → Skeleton)
    {n : ℕ} (parameters : Fin n → RecordedPaddedSource.Parameters F Cfg H b)
    (tables : (i : Fin n) → RecordedPaddedSource.PhysicalMatrix (parameters i))
    (result : ((i : Fin n) → FullData Digest (Skeleton.perfect (H (parameters i).tag))) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : result ∈ support ((simulateQ (CheckpointExecution.handler impl enc dummy shape)
      (HonestMatrixSetupTrace.program enc parameters tables)).run (CheckpointExecution.empty shape))) :
    CachedHashHandler.Coherent result.2.hash ∧ RecordedCheckpointQueries.Sound shape result.2 ∧
      CheckpointExecution.Audited enc dummy shape result.2 ∧
      ∀ nextShape : Cfg → Skeleton, CheckpointShapeTransport.Compatible shape nextShape result.2.checkpoints := by
  have valid := RecordedCheckpointQueries.run impl enc dummy shape
    (HonestMatrixSetupTrace.program enc parameters tables) (CheckpointExecution.empty shape)
    ⟨CachedHashHandler.coherent_empty, RecordedCheckpointQueries.empty _⟩ result supported
  have good := CheckpointExecution.good_empty enc dummy shape
  have audited := CheckpointExecution.audited_run impl enc dummy shape
    (HonestMatrixSetupTrace.program enc parameters tables) (CheckpointExecution.empty shape)
    ⟨good.1, fun _ => good.2.2⟩ result supported
  have checkpoints := HonestMatrixSetupTrace.checkpoints impl enc dummy shape parameters tables
    (CheckpointExecution.empty shape) result supported
  refine ⟨valid.1,valid.2,audited,?_⟩
  intro nextShape tag saved member
  change ⟨tag,saved⟩ ∈ result.2.checkpoints.checkpoints at member
  rw [checkpoints] at member
  cases member

end
end FormalProof4FHE.HasteBoots.HonestSetupInitialHistory
