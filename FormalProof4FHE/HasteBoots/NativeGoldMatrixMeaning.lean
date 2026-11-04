module

public import FormalProof4FHE.HasteBoots.NativeGoldMatrix
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# Field interpretation of checked raw matrix-vector application

Every semantic coefficient is read from the actual validated row-major
payload. No separate mathematical matrix or matrix-correctness certificate
is an input to these results.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldMatrixMeaning

open NativeFields NativeFieldRepresentation NativeGoldMatrix
open scoped BigOperators Matrix

theorem address_bound (width : ℕ) (row column : Fin width) : row.val * width + column.val < width * width := by
  have last := Nat.mul_le_mul_right width (Nat.succ_le_of_lt row.isLt)
  simp only [Nat.succ_mul] at last
  have inside := Nat.add_lt_add_left column.isLt (row.val * width)
  omega

theorem row_length (width : ℕ) (matrix : NativeGoldMatrix.Matrix) (index : Fin width)
    (valid : validate matrix width = true) : (NativeGoldMatrix.row matrix index.val).length = width := by
  have shape := (validate_iff matrix width).mp valid
  have last := Nat.mul_le_mul_right width (Nat.succ_le_of_lt index.isLt)
  simp only [Nat.succ_mul] at last
  simp only [NativeGoldMatrix.row, shape.2.1, List.length_take, List.length_drop, shape.2.2.2]
  exact Nat.min_eq_left (by omega)

/-- Every validated row is exactly its original contiguous raw-word block. -/
theorem row_ofFn (width : ℕ) (matrix : NativeGoldMatrix.Matrix) (index : Fin width)
    (valid : validate matrix width = true) :
    NativeGoldMatrix.row matrix index.val = List.ofFn (fun column : Fin width =>
      matrix.values[index.val * width + column.val]'(by
        rw [(validate_iff matrix width).mp valid |>.2.2.2]
        exact address_bound width index column)) := by
  have shape := (validate_iff matrix width).mp valid
  apply List.ext_getElem (by rw [row_length width matrix index valid, List.length_ofFn])
  intro position leftPresent rightPresent
  simp only [NativeGoldMatrix.row, shape.2.1, List.getElem_take, List.getElem_drop, List.getElem_ofFn]

private theorem zip_ofFn {width : ℕ} (first second : Fin width → GoldWord) :
    (List.ofFn first).zip (List.ofFn second) = List.ofFn (fun i => (first i, second i)) := by
  induction width with
  | zero => rfl
  | succ width ih =>
    simp only [List.ofFn_succ, List.zip_cons_cons]
    rw [ih]

theorem dot_ofFn {width : ℕ} (first second : Fin width → GoldWord) :
    goldValue (dot (List.ofFn first) (List.ofFn second)) =
      ∑ i : Fin width, goldValue (first i) * goldValue (second i) := by
  rw [dot_value, zip_ofFn, List.map_ofFn, Fin.sum_ofFn]
  rfl

noncomputable section

def semantic (width : ℕ) (matrix : NativeGoldMatrix.Matrix) (valid : validate matrix width = true) :
    _root_.Matrix (Fin width) (Fin width) Goldilocks :=
  fun row column => goldValue (matrix.values[row.val * width + column.val]'(by
    rw [(validate_iff matrix width).mp valid |>.2.2.2]
    exact address_bound width row column))

/-- Literal raw multiply/add output is the product of the actual payload's
field interpretation with every original input lane. -/
theorem apply_value (width : ℕ) (matrix : NativeGoldMatrix.Matrix) (valid : validate matrix width = true)
    (vector : Fin width → GoldWord) :
    (NativeGoldMatrix.apply width matrix (List.ofFn vector)).map (List.map goldValue) =
      some (List.ofFn (semantic width matrix valid *ᵥ (fun i => goldValue (vector i)))) := by
  have shape := (validate_iff matrix width).mp valid
  have guard : ¬(width = 0 ∨ (List.ofFn vector).length ≠ width) := by
    simp only [List.length_ofFn, ne_eq, not_true_eq_false, or_false]
    exact shape.1
  rw [NativeGoldMatrix.apply, ite_eq_right guard, ite_eq_left valid, Option.map_some]
  apply congrArg some
  apply List.ext_getElem (by simp)
  intro index leftPresent rightPresent
  have inside : index < width := by simpa only [List.length_ofFn] using rightPresent
  simp only [List.getElem_map, List.getElem_range, List.getElem_ofFn]
  rw [row_ofFn width matrix ⟨index, inside⟩ valid, dot_ofFn]
  rfl

end

end FormalProof4FHE.HasteBoots.NativeGoldMatrixMeaning
