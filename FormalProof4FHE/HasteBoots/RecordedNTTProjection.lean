module
public import FormalProof4FHE.HasteBoots.RecordedPaddedSourceFamily
public import FormalProof4FHE.HasteBoots.PackedHadamardRows
public import FormalProof4FHE.HasteBoots.DecompositionBlindRotation
@[expose] public section

/-! Native polynomial projections commute with logical dimension transport. -/
namespace FormalProof4FHE.HasteBoots.RecordedNTTProjection
noncomputable section
variable {q log d b c r left right : ℕ} [Fact q.Prime]
  {Cfg Input Digest : Type} [DecidableEq Digest] {heights : Cfg → ℕ}

/-- Both logical presentations read each coefficient at the same original
flat address; neither field values nor a row permutation is a premise. -/
theorem same_address
    (world : RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest (Fin (2*d+2)) heights b)
    (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (dummy : Digest)
    (length : 2^c*b = 2^log) (leftDimensions : r+c = left) (rightDimensions : r+c = right)
    (row : MatrixFold.Cube r) (factor : Fin (2*d+2)) :
    DecompositionBlindRotation.project (RecordedPaddedSourceFamily.logical world enc dummy left)
      (PackedHadamardRows.address length leftDimensions row) factor =
    DecompositionBlindRotation.project (RecordedPaddedSourceFamily.logical world enc dummy right)
      (PackedHadamardRows.address length rightDimensions row) factor := by
  funext index
  apply congrFun (RecordedPaddedSourceFamily.same_address world enc dummy factor
    (PackedHadamardRows.address length leftDimensions row index).1
    (PackedHadamardRows.address length rightDimensions row index).1 ?_)
    (PackedNTTBinding.address length row index).2
  simp only [PackedHadamardRows.address,PaddedSourceAddress.index_transport]

end
end FormalProof4FHE.HasteBoots.RecordedNTTProjection
