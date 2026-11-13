module
public import FormalProof4FHE.HasteBoots.PackedCipherSource
@[expose] public section

/-! Build physical setup buffers from logical sources in native low-address
order. Unused physical addresses are zero; decoder truth is proved separately
from the honest encoding and commitment execution. -/
namespace FormalProof4FHE.HasteBoots.HonestPaddedSource
noncomputable section
variable {F : Type} [Field F] {front suffix arity b : ℕ}

def physical (source : MatrixFold.Cube arity → Fin b → F) :
    Fin (2^front) → Fin (2^suffix) → Fin b → F :=
  fun left right =>
    let address := left.val + 2^front*right.val
    if bound : address < 2^arity then source ((FlatMatrixFold.index arity).symm ⟨address,bound⟩)
    else 0

/-- All low logical addresses fit the physical allocation, and the native
quotient/remainder split preserves their exact coefficient order. -/
theorem logical_physical (source : MatrixFold.Cube arity → Fin b → F)
    (fits : arity ≤ front+suffix) :
    PaddedSourceAddress.logical arity (physical (front := front) (suffix := suffix) source) = source := by
  funext cell lane
  have physicalBound : (FlatMatrixFold.index arity cell).val < 2^front*2^suffix := by
    have extent : 2^arity ≤ 2^(front+suffix) := Nat.pow_le_pow_right (by omega) fits
    simpa only [Nat.pow_add] using lt_of_lt_of_le (FlatMatrixFold.index arity cell).isLt extent
  have quotient : (FlatMatrixFold.index arity cell).val / 2^front < 2^suffix :=
    (Nat.div_lt_iff_lt_mul (by positivity)).mpr (by simpa only [Nat.mul_comm] using physicalBound)
  simp only [PaddedSourceAddress.logical,SubclaimSourceLayout.lookup,quotient,dite_true]
  simp only [physical,Nat.mod_add_div,Fin.isLt,dite_true]
  change source ((FlatMatrixFold.index arity).symm (FlatMatrixFold.index arity cell)) lane = source cell lane
  rw [Equiv.symm_apply_apply]

variable {q c lanes : ℕ} [Fact q.Prime]

/-- The setup buffer for an actual ciphertext is built from its complete pack,
including both halves and every coefficient lane. -/
def cipher (front suffix : ℕ) (value : NativeBlindRotation.Cipher q (2^(c+lanes))) :
    Fin (2^front) → Fin (2^suffix) → Fin (2^lanes) → ZMod q :=
  physical (front := front) (suffix := suffix) (KeySwitchExtraction.pack (c := c) (lanes := lanes) value)

theorem logical_cipher (front suffix : ℕ) (value : NativeBlindRotation.Cipher q (2^(c+lanes)))
    (fits : c+1 ≤ front+suffix) :
    PaddedSourceAddress.logical (c+1) (cipher front suffix value) =
      KeySwitchExtraction.pack (c := c) (lanes := lanes) value :=
  logical_physical _ fits

end
end FormalProof4FHE.HasteBoots.HonestPaddedSource
