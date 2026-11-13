module
public import FormalProof4FHE.HasteBoots.HonestMatrixTranscript
public import FormalProof4FHE.HasteBoots.HonestRecordedEvaluationKey
public import FormalProof4FHE.HasteBoots.RecordedCheckpointQueries
@[expose] public section

/-! Recover honest evaluation-key contents from setup queries included in the
actual later native source snapshots, without recording setup roots early. -/
namespace FormalProof4FHE.HasteBoots.HonestEvaluationKeyTranscript
open BinaryTree
noncomputable section
variable {q c levels : ℕ} [Fact q.Prime]
  {Cfg Input Digest Source : Type} [DecidableEq Input] [DecidableEq Digest] {H : Cfg → ℕ}

/-- Source checkpoints may be recorded after honest setup at their own native
geometries. Actual setup query inclusion, rather than a decoded-value equality,
associates their canonical key with the original coefficient key. -/
theorem key_eq_or_bad
    (actual : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Source H 4)
    (keySources : Fin levels → Source)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest)
    (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(c+3)))
    (original : NativeKeySwitch.Key q (2^(c+2)) levels)
    (labels : (level : Fin levels) → FullData Digest (Skeleton.perfect (H (actual.parameters (keySources level)).tag)))
    (roots : ∀ level, (actual.owners (keySources level)).root = (labels level).getRootValue)
    (included : ∀ level, ∀ entry ∈ HonestMerkleTranscript.queries enc
      (HonestRecordedMatrix.leaves (actual.parameters (keySources level))
        (HonestRecordedEvaluationKey.table (fun i => actual.parameters (keySources i)) psi original level))
      (labels level), entry ∈ (actual.owners (keySources level)).cumulativeLog)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape H) state)
    (sound : RecordedCheckpointQueries.Sound (AmbientMatrixSource.Shape H) state)
    (recorded : RecordedPaddedSourceFamily.Recorded actual state)
    (enough : ∀ level, (actual.parameters (keySources level)).degree ≤ 2^H (actual.parameters (keySources level)).tag)
    (margin : ∀ level, 2*(actual.parameters (keySources level)).radius <
      Code.minDist (BlockCode.code (actual.parameters (keySources level)).domain
        (actual.parameters (keySources level)).degree 4 :
        Set (Fin (2^H (actual.parameters (keySources level)).tag) → Fin 4 → ZMod q)))
    (fits : ∀ level, c+1 ≤ (actual.parameters (keySources level)).front+
      (actual.parameters (keySources level)).suffix) :
    DecodedEvaluationKey.key (c+2) psi primitive
      (fun level => PackedCipherSource.familyCipher (c := c) (lanes := 2) (RecordedSourceWorld.family state)
        enc dummy (RecordedSourceWorld.slot actual state recorded (keySources level))) = original ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape H) state := by
  classical
  by_cases bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape H) state
  · exact Or.inr bad
  have shared := (RecordedSourceWorld.cipher_eq_or_bad (c := c) (lanes := 2) actual enc dummy state
    audited recorded).resolve_right bad
  have values : ∀ level, PackedCipherSource.familyCipher (c := c) (lanes := 2) actual enc dummy
      (keySources level) = HonestRecordedEvaluationKey.evaluations psi original level := by
    intro level
    have injective := MerkleTreeExtractability.responseInjectiveOn_of_cache_noCollision
      (actual.owners (keySources level)).cumulativeLog state.hash.cache
      (sound _ (recorded (keySources level))) (fun collision => bad (Or.inr collision))
    have logical := HonestMatrixTranscript.logical (actual.parameters (keySources level)) enc dummy
      (HonestRecordedEvaluationKey.table (fun i => actual.parameters (keySources i)) psi original level)
      (labels level) (actual.owners (keySources level)) (roots level) (included level) injective
      (enough level) (margin level) (c+1)
    unfold PackedCipherSource.familyCipher
    change PackedCipherSource.unpack (c := c) (lanes := 2) (RecordedPaddedSource.logical (actual.parameters (keySources level))
      enc dummy (c+1) (actual.owners (keySources level))) = _
    rw [logical]
    unfold HonestRecordedEvaluationKey.table
    rw [HonestPaddedSource.logical_cipher _ _ _ (fits level)]
    exact PackedCipherSource.unpack_pack _
  left
  apply DecodedEvaluationKey.key_eq_of_setup
  intro level half
  have actualValue := (congrFun shared (keySources level)).symm.trans (values level)
  exact (congrFun actualValue half).symm

end
end FormalProof4FHE.HasteBoots.HonestEvaluationKeyTranscript
