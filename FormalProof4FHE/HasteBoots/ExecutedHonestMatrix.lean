module
public import FormalProof4FHE.HasteBoots.ExecutedHonestCommitment
public import FormalProof4FHE.HasteBoots.HonestRecordedMatrix
@[expose] public section

/-! A matrix committed by the actual shared handler, retained through arbitrary
verification, decodes to its honest table outside the same final Bad event. -/
namespace FormalProof4FHE.HasteBoots.ExecutedHonestMatrix
open OracleSpec OracleComp BinaryTree
noncomputable section
variable {F Cfg Input Digest : Type} [Field F]
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  {H : Cfg → ℕ} {b : ℕ} {ι : Type} {base : OracleSpec ι} {Result : Type}

/-- The computed honest owner is recorded by setup and retained by execution. -/
theorem owner_retained
    (impl : QueryImpl base ProbComp)
    (p : RecordedPaddedSource.Parameters F Cfg H b)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (table : RecordedPaddedSource.PhysicalMatrix p)
    (built : FullData Digest (Skeleton.perfect (H p.tag)) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (setupSupported : built ∈ support ((simulateQ (CheckpointExecution.handler impl enc dummy
      (AmbientMatrixSource.Shape H)) (ExecutedHonestCommitment.commit enc (AmbientMatrixSource.Shape H)
        p.tag (HonestRecordedMatrix.leaves p table))).run (CheckpointExecution.empty (AmbientMatrixSource.Shape H))))
    (continuation : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) Result)
    (result : Result × CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (supported : result ∈ support ((simulateQ (CheckpointExecution.handler impl enc dummy
      (AmbientMatrixSource.Shape H)) continuation).run built.2)) :
    ⟨p.tag, HonestRecordedMatrix.owner p enc (fun input => (result.2.hash.cache input).getD dummy)
      [] table⟩ ∈ result.2.checkpoints.checkpoints := by
  have first := RecordedCheckpointQueries.run impl enc dummy (AmbientMatrixSource.Shape H)
    (ExecutedHonestCommitment.commit enc (AmbientMatrixSource.Shape H) p.tag (HonestRecordedMatrix.leaves p table))
    (CheckpointExecution.empty (AmbientMatrixSource.Shape H))
    ⟨CachedHashHandler.coherent_empty, RecordedCheckpointQueries.empty _⟩ built setupSupported
  have final := RecordedCheckpointQueries.run impl enc dummy (AmbientMatrixSource.Shape H)
    continuation built.2 first result supported
  have saved := ExecutedHonestCommitment.retained impl enc dummy (AmbientMatrixSource.Shape H)
    p.tag (HonestRecordedMatrix.leaves p table) (CheckpointExecution.empty (AmbientMatrixSource.Shape H))
    built setupSupported continuation result supported
  exact ExecutedHonestCommitment.realized_recorded enc dummy (AmbientMatrixSource.Shape H)
    p.tag (HonestRecordedMatrix.leaves p table) built.1 [] result.2 final.2 saved

variable [DecidableEq F] [NeZero b]

/-- Table semantics now follow from supported setup and continuation, without
caller-supplied recorded-owner, audit, or transcript/cache certificates. -/
theorem logical_or_bad
    (impl : QueryImpl base ProbComp)
    (p : RecordedPaddedSource.Parameters F Cfg H b)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (table : RecordedPaddedSource.PhysicalMatrix p)
    (built : FullData Digest (Skeleton.perfect (H p.tag)) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (setupSupported : built ∈ support ((simulateQ (CheckpointExecution.handler impl enc dummy
      (AmbientMatrixSource.Shape H)) (ExecutedHonestCommitment.commit enc (AmbientMatrixSource.Shape H)
        p.tag (HonestRecordedMatrix.leaves p table))).run (CheckpointExecution.empty (AmbientMatrixSource.Shape H))))
    (continuation : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) Result)
    (result : Result × CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (supported : result ∈ support ((simulateQ (CheckpointExecution.handler impl enc dummy
      (AmbientMatrixSource.Shape H)) continuation).run built.2))
    (enough : p.degree ≤ 2^H p.tag)
    (margin : 2*p.radius < Code.minDist (BlockCode.code p.domain p.degree b :
      Set (Fin (2^H p.tag) → Fin b → F))) (arity : ℕ) :
    RecordedPaddedSourceFamily.logical (RecordedSourceWorld.family (F := F) (b := b) result.2) enc dummy arity
      (RecordedSourceWorld.slot
        (HonestRecordedMatrix.family p enc (fun input => (result.2.hash.cache input).getD dummy) [] table)
        result.2 (fun _ => owner_retained impl p enc dummy table built setupSupported continuation result supported) ()) =
      PaddedSourceAddress.logical arity table ∨
        CheckpointCollision.Bad (AmbientMatrixSource.Shape H) result.2 := by
  have good := CheckpointExecution.good_empty enc dummy (AmbientMatrixSource.Shape H)
  have firstAudit := CheckpointExecution.audited_run impl enc dummy (AmbientMatrixSource.Shape H)
    (ExecutedHonestCommitment.commit enc (AmbientMatrixSource.Shape H) p.tag (HonestRecordedMatrix.leaves p table))
    (CheckpointExecution.empty (AmbientMatrixSource.Shape H))
    ⟨good.1, fun _ => good.2.2⟩ built setupSupported
  have finalAudit := CheckpointExecution.audited_run impl enc dummy (AmbientMatrixSource.Shape H)
    continuation built.2 firstAudit result supported
  have first := RecordedCheckpointQueries.run impl enc dummy (AmbientMatrixSource.Shape H)
    (ExecutedHonestCommitment.commit enc (AmbientMatrixSource.Shape H) p.tag (HonestRecordedMatrix.leaves p table))
    (CheckpointExecution.empty (AmbientMatrixSource.Shape H))
    ⟨CachedHashHandler.coherent_empty, RecordedCheckpointQueries.empty _⟩ built setupSupported
  have final := RecordedCheckpointQueries.run impl enc dummy (AmbientMatrixSource.Shape H)
    continuation built.2 first result supported
  have saved := owner_retained impl p enc dummy table built setupSupported continuation result supported
  exact HonestRecordedMatrix.world_logical_or_bad p enc dummy
    (fun input => (result.2.hash.cache input).getD dummy) [] table result.2 finalAudit
    (final.2 _ saved) saved enough margin arity

end
end FormalProof4FHE.HasteBoots.ExecutedHonestMatrix
