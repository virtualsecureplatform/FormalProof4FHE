module

public import FormalProof4FHE.HasteBoots.NativeGoldMatrixProductPayload
public import FormalProof4FHE.HasteBoots.NativeGoldCoefficientsQuery

@[expose] public section

/-!
# Checked native raw matrix-matrix product

Both source views use bounded getters into the original validated payloads.
The result is the literal row-major payload program, in native a,c,b order,
followed by the native checked matrix constructor. Its field interpretation
preserves operand order; neither a commuted product nor a supplied semantic
matrix is used. Instruction/scheduler refinement remains open.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldMatrixProduct

open NativeFields NativeFieldRepresentation
open NativeGoldMatrixProductLoop (State)
open scoped Matrix BigOperators

def view (width : ℕ) (matrix : NativeGoldMatrix.Matrix) (valid : NativeGoldMatrix.validate matrix width = true) : State width :=
  fun row column => matrix.values[row.val * width + column.val]'(by
    rw [(NativeGoldMatrix.validate_iff matrix width).mp valid |>.2.2.2]
    exact NativeGoldMatrixMeaning.address_bound width row column)

def result (width : ℕ) (left right : NativeGoldMatrix.Matrix)
    (leftValid : NativeGoldMatrix.validate left width = true) (rightValid : NativeGoldMatrix.validate right width = true) :
    NativeGoldMatrix.Matrix :=
  ⟨width, (NativeGoldMatrixProductPayload.run (view width left leftValid) (view width right rightValid)).values⟩

def mul (left right : NativeGoldMatrix.Matrix) : Option NativeGoldMatrix.Matrix :=
  if leftValid : NativeGoldMatrix.validate left left.width = true then
    if rightValid : NativeGoldMatrix.validate right left.width = true then
      NativeGoldMatrix.checked left.width (result left.width left right leftValid rightValid).values
    else none
  else none

theorem result_valid (width : ℕ) (left right : NativeGoldMatrix.Matrix)
    (leftValid : NativeGoldMatrix.validate left width = true) (rightValid : NativeGoldMatrix.validate right width = true) :
    NativeGoldMatrix.validate (result width left right leftValid rightValid) width = true := by
  have shape := (NativeGoldMatrix.validate_iff left width).mp leftValid
  exact (NativeGoldMatrix.validate_iff _ _).mpr ⟨shape.1, rfl, shape.2.2.1,
    (NativeGoldMatrixProductPayload.run (view width left leftValid) (view width right rightValid)).length⟩

theorem mul_success (width : ℕ) (left right : NativeGoldMatrix.Matrix)
    (leftValid : NativeGoldMatrix.validate left width = true) (rightValid : NativeGoldMatrix.validate right width = true) :
    mul left right = some (result width left right leftValid rightValid) := by
  have widthEq := (NativeGoldMatrix.validate_iff left width).mp leftValid |>.2.1
  simp only [mul, widthEq, dite_eq_left leftValid, dite_eq_left rightValid]
  have shape := (NativeGoldMatrix.validate_iff _ _).mp (result_valid width left right leftValid rightValid)
  exact (NativeGoldMatrix.checked_iff _ _ _).mpr ⟨shape.1, shape.2.2.1, shape.2.2.2, rfl⟩

theorem mul_invalid_left (left right : NativeGoldMatrix.Matrix)
    (invalid : NativeGoldMatrix.validate left left.width ≠ true) : mul left right = none := by
  rw [mul, dite_eq_right invalid]

theorem mul_invalid_right (left right : NativeGoldMatrix.Matrix)
    (valid : NativeGoldMatrix.validate left left.width = true)
    (invalid : NativeGoldMatrix.validate right left.width ≠ true) : mul left right = none := by
  rw [mul, dite_eq_left valid, dite_eq_right invalid]

/-- The full literal payload program retains every per-cell ordered raw fold. -/
theorem result_get (width : ℕ) (left right : NativeGoldMatrix.Matrix)
    (leftValid : NativeGoldMatrix.validate left width = true) (rightValid : NativeGoldMatrix.validate right width = true)
    (row column : Fin width) :
    (result width left right leftValid rightValid).values[row.val * width + column.val]'(by
      exact (NativeGoldMatrixMeaning.address_bound width row column).trans_eq
        (NativeGoldMatrixProductPayload.run (view width left leftValid) (view width right rightValid)).length.symm) =
      NativeGoldMatrix.dotFrom (List.ofFn (fun i : Fin width =>
        (view width left leftValid row i, view width right rightValid i column))) 0 := by
  simp only [result, NativeGoldMatrixProductPayload.run_eq_serialize, NativeGoldMatrixProductPayload.serialize]
  rw [NativeGoldMatrixProductLoop.flatten_get, NativeGoldMatrixProductLoop.product_get]

noncomputable section

/-- Semantic multiplication is derived from the actual two raw source payloads. -/
theorem semantic_eq (width : ℕ) (left right : NativeGoldMatrix.Matrix)
    (leftValid : NativeGoldMatrix.validate left width = true) (rightValid : NativeGoldMatrix.validate right width = true) :
    NativeGoldMatrixMeaning.semantic width (result width left right leftValid rightValid)
      (result_valid width left right leftValid rightValid) =
        NativeGoldMatrixMeaning.semantic width left leftValid * NativeGoldMatrixMeaning.semantic width right rightValid := by
  funext row column
  change goldValue ((result width left right leftValid rightValid).values[row.val * width + column.val]'(by
    rw [(NativeGoldMatrix.validate_iff _ _).mp (result_valid width left right leftValid rightValid) |>.2.2.2]
    exact NativeGoldMatrixMeaning.address_bound width row column)) = _
  rw [result_get, NativeGoldMatrix.dotFrom_value]
  simp only [List.map_ofFn, Fin.sum_ofFn, goldValue, Fin.val_zero, Nat.cast_zero, zero_add]
  rfl

/-- The checked raw product reads as left times right, in that order. -/
theorem mul_value (width : ℕ) (left right : NativeGoldMatrix.Matrix)
    (leftValid : NativeGoldMatrix.validate left width = true) (rightValid : NativeGoldMatrix.validate right width = true) :
    (mul left right).bind (NativeGoldCoefficientsQuery.readMatrix width) = some
      (NativeGoldMatrixMeaning.semantic width left leftValid * NativeGoldMatrixMeaning.semantic width right rightValid) := by
  rw [mul_success width left right leftValid rightValid, Option.bind_some,
    NativeGoldCoefficientsQuery.readMatrix, dite_eq_left (result_valid width left right leftValid rightValid),
    semantic_eq]

/-- The right map acts first when the actual constructed product is applied. -/
theorem apply_value (width : ℕ) (left right : NativeGoldMatrix.Matrix)
    (leftValid : NativeGoldMatrix.validate left width = true) (rightValid : NativeGoldMatrix.validate right width = true)
    (input : Fin width → GoldWord) :
    (NativeGoldMatrix.apply width (result width left right leftValid rightValid) (List.ofFn input)).map
      (List.map goldValue) = some (List.ofFn (NativeGoldMatrixMeaning.semantic width left leftValid *ᵥ
        (NativeGoldMatrixMeaning.semantic width right rightValid *ᵥ (fun i => goldValue (input i))))) := by
  rw [NativeGoldMatrixMeaning.apply_value _ _ (result_valid _ _ _ leftValid rightValid), semantic_eq,
    ← Matrix.mulVec_mulVec]

end

end FormalProof4FHE.HasteBoots.NativeGoldMatrixProduct
