module

public import FormalProof4FHE.HasteBoots.NativeGoldMatrixFill
public import Mathlib.Data.List.OfFn

@[expose] public section

/-!
# Ordered raw matrix-product accumulation

The loop order is the native a,c,b order. A step updates one raw output
entry using its previous accumulator and the product of the fixed left and
right entries. The intermediate state is a finite row/column view; its
row-major serialization is connected to the native list-set write.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldMatrixProductLoop

open NativeFieldRepresentation

abbrev State (width : ℕ) := Fin width → Fin width → GoldWord

def write {width : ℕ} (out : State width) (row column : Fin width) (value : GoldWord) : State width :=
  Function.update out row (Function.update (out row) column value)

def step {width : ℕ} (left right : State width) (a c b : Fin width) (out : State width) : State width :=
  write out a b (NativeGoldArithmetic.add (out a b) (NativeGoldArithmetic.mul (left a c) (right c b)))

def bLoop {width : ℕ} (left right : State width) (a c : Fin width) :
    (count : ℕ) → count ≤ width → State width → State width
  | 0, _, out => out
  | count + 1, bound, out => step left right a c ⟨count, by omega⟩
      (bLoop left right a c count (by omega) out)

def cLoop {width : ℕ} (left right : State width) (a : Fin width) :
    (count : ℕ) → count ≤ width → State width → State width
  | 0, _, out => out
  | count + 1, bound, out => bLoop left right a ⟨count, by omega⟩ width (by omega)
      (cLoop left right a count (by omega) out)

def aLoop {width : ℕ} (left right : State width) :
    (count : ℕ) → count ≤ width → State width → State width
  | 0, _, out => out
  | count + 1, bound, out => cLoop left right ⟨count, by omega⟩ width (by omega)
      (aLoop left right count (by omega) out)

def product {width : ℕ} (left right : State width) : State width :=
  aLoop left right width (by omega) (fun _ _ => 0)

def flatten {width : ℕ} (out : State width) : List GoldWord :=
  List.ofFn (fun address : Fin (width * width) =>
    let coordinates := finProdFinEquiv.symm address
    out coordinates.1 coordinates.2)

theorem flatten_length {width : ℕ} (out : State width) : (flatten out).length = width * width := List.length_ofFn

theorem flatten_get {width : ℕ} (out : State width) (row column : Fin width) :
    (flatten out)[row.val * width + column.val]'(by
      rw [flatten_length]; exact NativeGoldMatrixMeaning.address_bound width row column) = out row column := by
  have address : (finProdFinEquiv (row, column)).val = row.val * width + column.val := by
    change column.val + width * row.val = row.val * width + column.val
    rw [Nat.mul_comm width row.val, Nat.add_comm]
  have same : (⟨row.val * width + column.val, NativeGoldMatrixMeaning.address_bound width row column⟩ :
      Fin (width * width)) = finProdFinEquiv (row, column) := Fin.ext address.symm
  simp only [flatten, List.getElem_ofFn, same, Equiv.symm_apply_apply]

/-- Finite-state writes serialize to the same single raw row-major write. -/
theorem flatten_write {width : ℕ} (out : State width) (row column : Fin width) (value : GoldWord) :
    flatten (write out row column value) = (flatten out).set (row.val * width + column.val) value := by
  apply List.ext_getElem (by simp only [flatten_length, List.length_set])
  intro index leftPresent rightPresent
  have inside : index < width * width := by simpa only [flatten_length] using leftPresent
  let coordinates : Fin width × Fin width := finProdFinEquiv.symm ⟨index, inside⟩
  have address : coordinates.1.val * width + coordinates.2.val = index := by
    have got := congrArg Fin.val (finProdFinEquiv.apply_symm_apply (⟨index, inside⟩ : Fin (width * width)))
    change (finProdFinEquiv coordinates).val = index at got
    change coordinates.2.val + width * coordinates.1.val = index at got
    simpa only [Nat.mul_comm width coordinates.1.val, Nat.add_comm] using got
  have eqIndex : row.val * width + column.val = index ↔ row = coordinates.1 ∧ column = coordinates.2 := by
    rw [← address, NativeGoldMatrixFill.address_eq_iff width row.val coordinates.1.val column.val coordinates.2.val column.isLt coordinates.2.isLt]
    exact and_congr Fin.val_inj Fin.val_inj
  simp only [List.getElem_set, flatten, List.getElem_ofFn]
  change write out row column value coordinates.1 coordinates.2 =
    if row.val * width + column.val = index then value else out coordinates.1 coordinates.2
  simp only [eqIndex, write, Function.update_apply]
  by_cases sameRow : coordinates.1 = row
  · by_cases sameColumn : coordinates.2 = column
    · simp only [sameRow, sameColumn, and_self, ite_true, Function.update_apply]
    · simp only [sameRow, sameColumn, Ne.symm sameColumn, and_false, ite_false, ite_true, Function.update_apply]
  · simp only [sameRow, Ne.symm sameRow, false_and, ite_false]

/-- A completed inner b-loop updates each selected column exactly once. -/
theorem bLoop_get {width : ℕ} (left right : State width) (a c : Fin width) (count : ℕ)
    (bound : count ≤ width) (out : State width) (row column : Fin width) :
    bLoop left right a c count bound out row column =
      if row = a ∧ column.val < count then
        NativeGoldArithmetic.add (out row column) (NativeGoldArithmetic.mul (left row c) (right c column))
      else out row column := by
  induction count with
  | zero => simp only [bLoop, Nat.not_lt_zero, and_false, ite_false]
  | succ count ih =>
    simp only [bLoop, step, write, Function.update_apply]
    by_cases sameRow : row = a
    · subst row
      by_cases sameColumn : column.val = count
      · have selected : column = (⟨count, by omega⟩ : Fin width) := Fin.ext sameColumn
        simp only [selected] at ih
        simp only [Function.update_apply, selected, ite_true, ih (by omega), Nat.lt_succ_self, lt_self_iff_false,
          and_false, and_self, ite_false]
      · have different : column ≠ (⟨count, by omega⟩ : Fin width) := fun equal => sameColumn (congrArg Fin.val equal)
        have before : column.val < count + 1 ↔ column.val < count := by omega
        simp only [Function.update_apply, different, ite_true, ite_false, ih (by omega), true_and, before]
    · simp only [sameRow, ite_false, ih (by omega), false_and]

/-- The c-loop retains the native ascending-c raw accumulator order. -/
theorem cLoop_get {width : ℕ} (left right : State width) (a : Fin width) (count : ℕ)
    (bound : count ≤ width) (out : State width) (row column : Fin width) :
    cLoop left right a count bound out row column =
      if row = a then NativeGoldMatrix.dotFrom
        (List.ofFn (fun i : Fin count => (left row ⟨i.val, i.isLt.trans_le bound⟩,
          right ⟨i.val, i.isLt.trans_le bound⟩ column))) (out row column)
      else out row column := by
  induction count with
  | zero => simp only [cLoop, List.ofFn_zero, NativeGoldMatrix.dotFrom, List.foldl_nil, ite_self]
  | succ count ih =>
    rw [cLoop, bLoop_get]
    simp only [column.isLt, and_true]
    by_cases sameRow : row = a
    · subst row
      simp only [ite_true, ih (by omega)]
      rw [List.ofFn_succ', List.concat_eq_append]
      simp only [NativeGoldMatrix.dotFrom, List.foldl_append, List.foldl_cons, List.foldl_nil]
      rfl
    · simp only [sameRow, ite_false, ih (by omega)]

/-- Finished rows retain their ordered dot products while later rows are written. -/
theorem aLoop_get {width : ℕ} (left right : State width) (count : ℕ) (bound : count ≤ width)
    (out : State width) (row column : Fin width) :
    aLoop left right count bound out row column =
      if row.val < count then NativeGoldMatrix.dotFrom (List.ofFn (fun i : Fin width => (left row i, right i column))) (out row column)
      else out row column := by
  induction count with
  | zero => simp only [aLoop, Nat.not_lt_zero, ite_false]
  | succ count ih =>
    rw [aLoop, cLoop_get]
    by_cases sameRow : row.val = count
    · have selected : row = (⟨count, by omega⟩ : Fin width) := Fin.ext sameRow
      simp only [selected] at ih
      simp only [selected, ite_true, ih (by omega), Nat.lt_succ_self, lt_self_iff_false, ite_false]
    · have different : row ≠ (⟨count, by omega⟩ : Fin width) := fun equal => sameRow (congrArg Fin.val equal)
      have before : row.val < count + 1 ↔ row.val < count := by omega
      simp only [different, ite_false, ih (by omega), before]

theorem product_get {width : ℕ} (left right : State width) (row column : Fin width) :
    product left right row column = NativeGoldMatrix.dotFrom
      (List.ofFn (fun i : Fin width => (left row i, right i column))) 0 := by
  rw [product, aLoop_get, ite_eq_left row.isLt]

end FormalProof4FHE.HasteBoots.NativeGoldMatrixProductLoop
