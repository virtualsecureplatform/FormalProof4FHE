module
public import FormalProof4FHE.HasteBoots.HonestRecordedEvaluationKey
public import FormalProof4FHE.HasteBoots.RecordedCheckpointQueries
@[expose] public section

/-! Honest-key association for supported shared executions. Cache and audit
receipts follow from execution; setup checkpoint membership and public routing
remain explicit until the native setup program is connected. -/
namespace FormalProof4FHE.HasteBoots.HonestExecutedEvaluationKey
open OracleSpec OracleComp HonestRecordedEvaluationKey
noncomputable section
variable {q c levels : ℕ} [Fact q.Prime]
  {Cfg Input Digest : Type} [DecidableEq Input] [DecidableEq Digest] {H : Cfg → ℕ}

/-- The actual execution establishes cache coherence and all recorded transcript
receipts. No independent final-state audit or log/cache certificate is assumed. -/
theorem associated_key_of_run_or_bad {Source Result ι : Type}
    [SampleableType Digest] {base : OracleSpec ι}
    (impl : QueryImpl base ProbComp)
    (program : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) Result)
    (parameters : Fin levels → RecordedPaddedSource.Parameters (ZMod q) Cfg H 4)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest) (hash : Input → Digest)
    (before : Fin levels → MerkleTreeExtractor.QueryLog Input Digest)
    (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(c+2+1)))
    (original : NativeKeySwitch.Key q (2^(c+2)) levels)
    (result : Result × CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (supported : result ∈ support ((simulateQ (CheckpointExecution.handler impl enc dummy
      (AmbientMatrixSource.Shape H)) program).run (CheckpointExecution.empty (AmbientMatrixSource.Shape H))))
    (recorded : ∀ level, ⟨(parameters level).tag,owner parameters enc hash before psi original level⟩ ∈
      result.2.checkpoints.checkpoints)
    (enough : ∀ level, (parameters level).degree ≤ 2^H (parameters level).tag)
    (margin : ∀ level, 2*(parameters level).radius <
      Code.minDist (BlockCode.code (parameters level).domain (parameters level).degree 4 :
        Set (Fin (2^H (parameters level).tag) → Fin 4 → ZMod q)))
    (fits : ∀ level, c+1 ≤ (parameters level).front+(parameters level).suffix)
    (actual : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Source H 4)
    (actualRecorded : RecordedPaddedSourceFamily.Recorded actual result.2) (keySources : Fin levels → Source)
    (sameParameters : ∀ level, actual.parameters (keySources level) = parameters level)
    (sameRoots : ∀ level, actual.roots (keySources level) =
      (owner parameters enc hash before psi original level).root) :
    DecodedEvaluationKey.key (c+2) psi primitive
      (fun level => PackedCipherSource.familyCipher (c := c) (lanes := 2) (RecordedSourceWorld.family result.2)
        enc dummy (RecordedSourceWorld.slot actual result.2 actualRecorded (keySources level))) = original ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape H) result.2 := by
  have good := CheckpointExecution.good_empty enc dummy (AmbientMatrixSource.Shape H)
  have audited := CheckpointExecution.audited_run impl enc dummy (AmbientMatrixSource.Shape H)
    program (CheckpointExecution.empty (AmbientMatrixSource.Shape H))
    ⟨good.1, fun _ => good.2.2⟩ result supported
  have sound := RecordedCheckpointQueries.from_empty impl enc dummy (AmbientMatrixSource.Shape H)
    program result supported
  exact associated_key_eq_or_bad parameters enc dummy hash before psi primitive original result.2
    audited (fun level => sound _ (recorded level)) recorded enough margin fits actual actualRecorded
    keySources sameParameters sameRoots

end
end FormalProof4FHE.HasteBoots.HonestExecutedEvaluationKey
