module
public import FormalProof4FHE.HasteBoots.HonestControlKeyTable
public import FormalProof4FHE.HasteBoots.HonestMatrixTranscript
public import FormalProof4FHE.HasteBoots.RecordedCheckpointQueries
@[expose] public section

/-! Recover honestly initialized control-key evaluations from setup queries
inside the actual native source snapshots, under the same final Bad event. -/
namespace FormalProof4FHE.HasteBoots.HonestControlKeyTranscript
open BinaryTree
noncomputable section
variable {q cells lanes rows levels : ℕ} [Fact q.Prime]
  {Cfg Input Digest Source : Type} [DecidableEq Input] [DecidableEq Digest] {H : Cfg → ℕ}

omit [DecidableEq Input] in
/-- Honest setup queries identify every actual key evaluation row, with no
assumed decoded-table, coefficient-key or transform-value equality. -/
theorem polynomials_or_bad
    (actual : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest Source H (2^lanes))
    (keySources : Fin (2*levels) → Source)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest) (psi : ZMod q)
    (controls : HonestControlKeyTable.Controls (q := q) (cells := cells) (lanes := lanes) (rows := rows) (levels := levels))
    (labels : (slot : Fin (2*levels)) → FullData Digest (Skeleton.perfect (H (actual.parameters (keySources slot)).tag)))
    (roots : ∀ slot, (actual.owners (keySources slot)).root = (labels slot).getRootValue)
    (included : ∀ slot, ∀ entry ∈ HonestMerkleTranscript.queries enc
      (HonestRecordedMatrix.leaves (actual.parameters (keySources slot))
        (HonestControlKeyTable.table (fun i => actual.parameters (keySources i)) psi controls slot)) (labels slot),
      entry ∈ (actual.owners (keySources slot)).cumulativeLog)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (sound : RecordedCheckpointQueries.Sound (AmbientMatrixSource.Shape H) state)
    (recorded : RecordedPaddedSourceFamily.Recorded actual state)
    (enough : ∀ slot, (actual.parameters (keySources slot)).degree ≤ 2^H (actual.parameters (keySources slot)).tag)
    (margin : ∀ slot, 2*(actual.parameters (keySources slot)).radius <
      Code.minDist (BlockCode.code (actual.parameters (keySources slot)).domain (actual.parameters (keySources slot)).degree (2^lanes) :
        Set (Fin (2^H (actual.parameters (keySources slot)).tag) → Fin (2^lanes) → ZMod q)))
    (fits : ∀ slot, (rows+1)+cells ≤ (actual.parameters (keySources slot)).front+(actual.parameters (keySources slot)).suffix) :
    (∀ position half source level, PackedMonomialRotation.polynomial
      (RecordedPaddedSourceFamily.logical actual enc dummy ((rows+1)+cells)
        (keySources (PBSHadamardBlindRotation.digitIndex (source,level)))) position half =
      BlindRotationNTT.transform (cells+lanes) psi (controls position source level half)) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape H) state := by
  classical
  by_cases bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape H) state
  · exact Or.inr bad
  left
  intro position half source level
  let slot := PBSHadamardBlindRotation.digitIndex (source,level)
  have injective := MerkleTreeExtractability.responseInjectiveOn_of_cache_noCollision
    (actual.owners (keySources slot)).cumulativeLog state.hash.cache (sound _ (recorded (keySources slot)))
    (fun collision => bad (Or.inr collision))
  have original := HonestMatrixTranscript.logical (actual.parameters (keySources slot)) enc dummy
    (HonestControlKeyTable.table (fun i => actual.parameters (keySources i)) psi controls slot)
    (labels slot) (actual.owners (keySources slot)) (roots slot) (included slot) injective
    (enough slot) (margin slot) ((rows+1)+cells)
  have sourceValue : RecordedPaddedSourceFamily.logical actual enc dummy ((rows+1)+cells) (keySources slot) =
      HonestControlKeyTable.logical psi controls slot := by
    exact original.trans (HonestControlKeyTable.logical_table _ psi controls slot (fits slot))
  change PackedMonomialRotation.polynomial
    (RecordedPaddedSourceFamily.logical actual enc dummy ((rows+1)+cells) (keySources slot)) position half = _
  rw [sourceValue]
  exact HonestControlKeyTable.polynomial psi controls position half source level

end
end FormalProof4FHE.HasteBoots.HonestControlKeyTranscript
