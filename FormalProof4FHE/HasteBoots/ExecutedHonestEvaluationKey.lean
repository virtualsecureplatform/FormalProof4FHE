module
public import FormalProof4FHE.HasteBoots.ExecutedHonestMatrixBatch
public import FormalProof4FHE.HasteBoots.HonestRecordedEvaluationKey
@[expose] public section

/-! Actual shared-oracle setup of all evaluation-key matrices and association
of its returned roots with the final canonical inverse-NTT key. -/
namespace FormalProof4FHE.HasteBoots.ExecutedHonestEvaluationKey
open OracleSpec OracleComp HonestRecordedEvaluationKey
noncomputable section
variable {q c levels : ℕ} [Fact q.Prime]
  {Cfg Input Digest : Type} {H : Cfg → ℕ}

def setup {ι : Type} {base : OracleSpec ι}
    (parameters : Fin levels → RecordedPaddedSource.Parameters (ZMod q) Cfg H 4)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q)))
    (psi : ZMod q) (original : NativeKeySwitch.Key q (2^(c+2)) levels) :
    OracleComp (CheckpointExecution.Spec base Cfg Input Digest) (Fin levels → Digest) :=
  ExecutedHonestMatrixBatch.program enc parameters (table parameters psi original)

/-- Setup roots feed the continuation in the same oracle execution. -/
def joint {ι Result : Type} {base : OracleSpec ι}
    (parameters : Fin levels → RecordedPaddedSource.Parameters (ZMod q) Cfg H 4)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q)))
    (psi : ZMod q) (original : NativeKeySwitch.Key q (2^(c+2)) levels)
    (continuation : (Fin levels → Digest) → OracleComp (CheckpointExecution.Spec base Cfg Input Digest) Result) :
    OracleComp (CheckpointExecution.Spec base Cfg Input Digest) ((Fin levels → Digest) × Result) := do
  let roots ← setup parameters enc psi original
  let result ← continuation roots
  pure (roots,result)

variable [DecidableEq Input] [DecidableEq Digest]

/-- The selected canonical key equals the original coefficient key or the one
shared final Bad event. Setup roots and all owner receipts are execution-derived. -/
theorem associated_key_or_bad {Source Result ι : Type}
    [SampleableType Digest] {base : OracleSpec ι}
    (impl : QueryImpl base ProbComp)
    (parameters : Fin levels → RecordedPaddedSource.Parameters (ZMod q) Cfg H 4)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest)
    (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(c+2+1)))
    (original : NativeKeySwitch.Key q (2^(c+2)) levels)
    (built : (Fin levels → Digest) × CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (setupSupported : built ∈ support ((simulateQ (CheckpointExecution.handler impl enc dummy
      (AmbientMatrixSource.Shape H)) (setup parameters enc psi original)).run
        (CheckpointExecution.empty (AmbientMatrixSource.Shape H))))
    (continuation : OracleComp (CheckpointExecution.Spec base Cfg Input Digest) Result)
    (result : Result × CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (supported : result ∈ support ((simulateQ (CheckpointExecution.handler impl enc dummy
      (AmbientMatrixSource.Shape H)) continuation).run built.2))
    (enough : ∀ level, (parameters level).degree ≤ 2^H (parameters level).tag)
    (margin : ∀ level, 2*(parameters level).radius <
      Code.minDist (BlockCode.code (parameters level).domain (parameters level).degree 4 :
        Set (Fin (2^H (parameters level).tag) → Fin 4 → ZMod q)))
    (fits : ∀ level, c+1 ≤ (parameters level).front+(parameters level).suffix)
    (actual : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Source H 4)
    (actualRecorded : RecordedPaddedSourceFamily.Recorded actual result.2) (keySources : Fin levels → Source)
    (sameParameters : ∀ level, actual.parameters (keySources level) = parameters level)
    (sameRoots : ∀ level, actual.roots (keySources level) =
      built.1 level) :
    DecodedEvaluationKey.key (c+2) psi primitive
      (fun level => PackedCipherSource.familyCipher (c := c) (lanes := 2) (RecordedSourceWorld.family result.2)
        enc dummy (RecordedSourceWorld.slot actual result.2 actualRecorded (keySources level))) = original ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape H) result.2 := by
  obtain ⟨before, saved⟩ := ExecutedHonestMatrixBatch.owners_retained impl enc dummy parameters
    (table parameters psi original) built setupSupported continuation result supported
  have good := CheckpointExecution.good_empty enc dummy (AmbientMatrixSource.Shape H)
  have firstAudit := CheckpointExecution.audited_run impl enc dummy (AmbientMatrixSource.Shape H)
    (setup parameters enc psi original) (CheckpointExecution.empty (AmbientMatrixSource.Shape H))
    ⟨good.1, fun _ => good.2.2⟩ built setupSupported
  have finalAudit := CheckpointExecution.audited_run impl enc dummy (AmbientMatrixSource.Shape H)
    continuation built.2 firstAudit result supported
  have first := RecordedCheckpointQueries.run impl enc dummy (AmbientMatrixSource.Shape H)
    (setup parameters enc psi original) (CheckpointExecution.empty (AmbientMatrixSource.Shape H))
    ⟨CachedHashHandler.coherent_empty, RecordedCheckpointQueries.empty _⟩ built setupSupported
  have final := RecordedCheckpointQueries.run impl enc dummy (AmbientMatrixSource.Shape H)
    continuation built.2 first result supported
  exact associated_key_eq_or_bad parameters enc dummy
    (fun input => (result.2.hash.cache input).getD dummy) before psi primitive original result.2
    finalAudit (fun level => final.2 _ (saved level).2) (fun level => (saved level).2)
    enough margin fits actual actualRecorded keySources sameParameters
    (fun level => (sameRoots level).trans (saved level).1)

/-- Honest key association for one complete supported setup/verifier run,
with no independent setup receipts or detached verifier execution. -/
theorem joint_associated_key_or_bad {Source Result ι : Type}
    [SampleableType Digest] {base : OracleSpec ι}
    (impl : QueryImpl base ProbComp)
    (parameters : Fin levels → RecordedPaddedSource.Parameters (ZMod q) Cfg H 4)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest)
    (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(c+2+1)))
    (original : NativeKeySwitch.Key q (2^(c+2)) levels)
    (continuation : (Fin levels → Digest) → OracleComp (CheckpointExecution.Spec base Cfg Input Digest) Result)
    (outcome : ((Fin levels → Digest) × Result) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (supported : outcome ∈ support ((simulateQ (CheckpointExecution.handler impl enc dummy
      (AmbientMatrixSource.Shape H)) (joint parameters enc psi original continuation)).run
        (CheckpointExecution.empty (AmbientMatrixSource.Shape H))))
    (enough : ∀ level, (parameters level).degree ≤ 2^H (parameters level).tag)
    (margin : ∀ level, 2*(parameters level).radius <
      Code.minDist (BlockCode.code (parameters level).domain (parameters level).degree 4 :
        Set (Fin (2^H (parameters level).tag) → Fin 4 → ZMod q)))
    (fits : ∀ level, c+1 ≤ (parameters level).front+(parameters level).suffix)
    (actual : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Source H 4)
    (actualRecorded : RecordedPaddedSourceFamily.Recorded actual outcome.2) (keySources : Fin levels → Source)
    (sameParameters : ∀ level, actual.parameters (keySources level) = parameters level)
    (sameRoots : ∀ level, actual.roots (keySources level) =
      outcome.1.1 level) :
    DecodedEvaluationKey.key (c+2) psi primitive
      (fun level => PackedCipherSource.familyCipher (c := c) (lanes := 2) (RecordedSourceWorld.family outcome.2)
        enc dummy (RecordedSourceWorld.slot actual outcome.2 actualRecorded (keySources level))) = original ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape H) outcome.2 := by
  simp only [joint, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure,
    support_bind, support_pure, Set.mem_iUnion, Set.mem_singleton_iff] at supported
  obtain ⟨built, setupSupported, result, continuationSupported, equal⟩ := supported
  subst outcome
  exact associated_key_or_bad impl parameters enc dummy psi primitive original built setupSupported
    (continuation built.1) result continuationSupported enough margin fits actual actualRecorded
    keySources sameParameters sameRoots

end
end FormalProof4FHE.HasteBoots.ExecutedHonestEvaluationKey
