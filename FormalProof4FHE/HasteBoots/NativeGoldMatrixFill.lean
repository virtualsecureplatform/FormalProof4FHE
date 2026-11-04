module

public import FormalProof4FHE.HasteBoots.NativeGoldMatrixMeaning

@[expose] public section

/-!
# Ordered row-major coefficient writes

The native extension-query constructors zero a square payload, then copy
columns in order and coordinates within each column in order. These loops
retain raw stored words. Bounds and the resulting payload are derived here;
no mathematical matrix or payload certificate is supplied.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldMatrixFill

open NativeFieldRepresentation

/-- Copy the first `count` coordinates of one column, in ascending order. -/
def rows (width : ℕ) (entry : ℕ → ℕ → GoldWord) (column : ℕ) : ℕ → List GoldWord → List GoldWord
  | 0, payload => payload
  | count + 1, payload => (rows width entry column count payload).set
      (count * width + column) (entry count column)

/-- Copy columns in ascending order; each column copies its coordinates first. -/
def columns (width : ℕ) (entry : ℕ → ℕ → GoldWord) (height : ℕ) : ℕ → List GoldWord → List GoldWord
  | 0, payload => payload
  | count + 1, payload => rows width entry count height (columns width entry height count payload)

def fill (width height count : ℕ) (entry : ℕ → ℕ → GoldWord) : List GoldWord :=
  columns width entry height count (List.replicate (width * width) 0)

theorem rows_length (width : ℕ) (entry : ℕ → ℕ → GoldWord) (column count : ℕ) (payload : List GoldWord) :
    (rows width entry column count payload).length = payload.length := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [rows, List.length_set, ih]

theorem columns_length (width : ℕ) (entry : ℕ → ℕ → GoldWord) (height count : ℕ) (payload : List GoldWord) :
    (columns width entry height count payload).length = payload.length := by
  induction count with
  | zero => rfl
  | succ count ih => rw [columns, rows_length, ih]

theorem fill_length (width height count : ℕ) (entry : ℕ → ℕ → GoldWord) :
    (fill width height count entry).length = width * width := by
  rw [fill, columns_length, List.length_replicate]

/-- Distinct valid column/row pairs cannot alias in the row-major payload. -/
theorem address_eq_iff (width firstRow secondRow firstColumn secondColumn : ℕ)
    (firstInside : firstColumn < width) (secondInside : secondColumn < width) :
    firstRow * width + firstColumn = secondRow * width + secondColumn ↔
      firstRow = secondRow ∧ firstColumn = secondColumn := by
  constructor
  · intro same
    have divided := congrArg (fun address => address / width) same
    have reduced := congrArg (fun address => address % width) same
    simp only [Nat.mul_comm firstRow width, Nat.mul_comm secondRow width,
      Nat.mul_add_div (by omega : 0 < width), Nat.div_eq_of_lt firstInside,
      Nat.div_eq_of_lt secondInside, Nat.add_zero] at divided
    simp only [Nat.mul_comm firstRow width, Nat.mul_comm secondRow width,
      Nat.mul_add_mod, Nat.mod_eq_of_lt firstInside, Nat.mod_eq_of_lt secondInside] at reduced
    exact ⟨divided, reduced⟩
  · rintro ⟨rfl, rfl⟩; rfl

/-- Every write is in bounds, and all other original entries are retained. -/
theorem rows_get (width : ℕ) (entry : ℕ → ℕ → GoldWord) (column count : ℕ)
    (payload : List GoldWord) (length : payload.length = width * width)
    (columnInside : column < width) (countInside : count ≤ width) (row target : Fin width) :
    (rows width entry column count payload)[row.val * width + target.val]'(by
      rw [rows_length, length]; exact NativeGoldMatrixMeaning.address_bound width row target) =
      if row.val < count ∧ target.val = column then entry row.val target.val else
        payload[row.val * width + target.val]'(by
          rw [length]; exact NativeGoldMatrixMeaning.address_bound width row target) := by
  induction count with
  | zero => simp only [rows, Nat.not_lt_zero, false_and, ite_false]
  | succ count ih =>
    simp only [rows, List.getElem_set]
    simp only [ih (by omega), address_eq_iff width count row.val column target.val columnInside target.isLt]
    by_cases sameRow : count = row.val
    · by_cases sameColumn : column = target.val
      · simp only [sameRow, sameColumn, and_self, ite_true, Nat.lt_succ_self]
      · have different : target.val ≠ column := Ne.symm sameColumn
        simp only [sameColumn, different, and_false, ite_false]
    · by_cases sameColumn : column = target.val
      · have before : row.val < count + 1 ↔ row.val < count := by omega
        simp only [sameRow, sameColumn, ite_false, and_true, before]
      · have different : target.val ≠ column := Ne.symm sameColumn
        simp only [sameColumn, different, and_false, ite_false]

theorem columns_get (width : ℕ) (entry : ℕ → ℕ → GoldWord) (height count : ℕ)
    (payload : List GoldWord) (length : payload.length = width * width)
    (heightInside : height ≤ width) (countInside : count ≤ width) (row target : Fin width) :
    (columns width entry height count payload)[row.val * width + target.val]'(by
      rw [columns_length, length]; exact NativeGoldMatrixMeaning.address_bound width row target) =
      if row.val < height ∧ target.val < count then entry row.val target.val else
        payload[row.val * width + target.val]'(by
          rw [length]; exact NativeGoldMatrixMeaning.address_bound width row target) := by
  induction count with
  | zero => simp only [columns, Nat.not_lt_zero, and_false, ite_false]
  | succ count ih =>
    simp only [columns]
    rw [rows_get width entry count height _ (by rw [columns_length, length])
      (by omega) heightInside, ih (by omega)]
    by_cases present : row.val < height
    · by_cases same : target.val = count
      · simp only [present, same, Nat.lt_succ_self, and_self, ite_true]
      · have before : target.val < count + 1 ↔ target.val < count := by omega
        simp only [present, same, true_and, ite_false, before]
    · simp only [present, false_and, ite_false]

/-- The complete initialized payload, including all untouched raw zeros. -/
theorem fill_get (width height count : ℕ) (entry : ℕ → ℕ → GoldWord)
    (heightInside : height ≤ width) (countInside : count ≤ width) (row column : Fin width) :
    (fill width height count entry)[row.val * width + column.val]'(by
      rw [fill_length]; exact NativeGoldMatrixMeaning.address_bound width row column) =
      if row.val < height ∧ column.val < count then entry row.val column.val else 0 := by
  simp only [fill]
  rw [columns_get width entry height count _ List.length_replicate heightInside countInside,
    List.getElem_replicate]

end FormalProof4FHE.HasteBoots.NativeGoldMatrixFill
