module
public import FormalProof4FHE.HasteBoots.PBSHadamardBlindRotation
public import FormalProof4FHE.HasteBoots.PackedNTTBinding
public import FormalProof4FHE.HasteBoots.PackedPBSOriginalReferences
@[expose] public section

/-! Derive the application polynomial addresses from the original NTT row
layout. Dimension transport preserves coefficient bits, row bits and lanes. -/
namespace FormalProof4FHE.HasteBoots.PackedHadamardRows
open NativeBlindRotation (Poly Cipher digit)
noncomputable section
variable {q log levels cells b c r : ℕ}

/-- The Hadamard view uses the very same packed polynomial addresses. -/
def address (length : 2^c*b = 2^log) (dimensions : r+c = cells)
    (row : MatrixFold.Cube r) (coefficient : Fin (2^log)) : MatrixFold.Cube cells × Fin b :=
  let original := PackedNTTBinding.address length row coefficient
  (dimensions ▸ original.1,original.2)

theorem project_eq_row (length : 2^c*b = 2^log) (dimensions : r+c = cells)
    (tables : PackedSumcheckExecution.Tables (ZMod q) (PBSHadamard.Factor (2*levels)) cells b)
    (row : MatrixFold.Cube r) (factor : PBSHadamard.Factor (2*levels)) :
    PBSHadamardBlindRotation.project tables (address length dimensions row) factor =
      PackedNTTBinding.row length (QueryReindex.source dimensions (tables factor)) row := by
  funext coefficient
  rfl

/-- Digit slots use native half-major order, followed by the result slot. -/
def expectedCoefficient (bits : ℕ) (difference result : Cipher q (2^log))
    (slot : Fin (2*levels+1)) (half : Bool) : Poly q (2^log) :=
  Fin.lastCases (result half) (fun index =>
    let original := (PBSHadamardBlindRotation.digitEquiv levels).symm index
    digit bits original.2 (difference original.1)) slot

@[simp] theorem expected_digit (bits : ℕ) (difference result : Cipher q (2^log))
    (source half : Bool) (level : Fin levels) :
    expectedCoefficient bits difference result
      (Fin.castSucc (PBSHadamardBlindRotation.digitIndex (source,level))) half =
      digit bits level (difference source) := by
  simp only [expectedCoefficient,Fin.lastCases_castSucc]
  have same := (PBSHadamardBlindRotation.digitEquiv levels).symm_apply_apply (source,level)
  change (PBSHadamardBlindRotation.digitEquiv levels).symm
    (PBSHadamardBlindRotation.digitIndex (source,level)) = (source,level) at same
  rw [same]

@[simp] theorem expected_result (bits : ℕ) (difference result : Cipher q (2^log)) (half : Bool) :
    expectedCoefficient bits difference result (Fin.last (2*levels)) half = result half := by
  simp only [expectedCoefficient,Fin.lastCases_last]

theorem evaluation_digit (index : Fin (2*levels)) :
    PackedPBSOriginalReferences.evaluationFactor (Fin.castSucc index) = .inl (index,false) := by
  simp [PackedPBSOriginalReferences.evaluationFactor,index.isLt]

theorem evaluation_result :
    PackedPBSOriginalReferences.evaluationFactor (Fin.last (2*levels)) = .inr () := by
  simp [PackedPBSOriginalReferences.evaluationFactor]

end
end FormalProof4FHE.HasteBoots.PackedHadamardRows
