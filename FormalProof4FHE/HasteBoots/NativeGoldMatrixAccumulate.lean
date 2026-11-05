module

public import FormalProof4FHE.HasteBoots.NativeGoldMatrixMeaning

@[expose] public section

/-! Native Matrix::add_mul retains each row's existing accumulator. In a
zero/one fold the second product starts from the first product's raw output;
separately reducing two dot products would not preserve lazy representatives. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldMatrixAccumulate

open NativeFieldRepresentation NativeFields
open NativeGoldMatrix (Matrix validate dotFrom row)
open scoped Matrix

def payload (width : ℕ) (matrix : Matrix) (vector initial : List GoldWord) : List GoldWord :=
  (List.range width).map (fun index => dotFrom ((row matrix index).zip vector) (initial[index]?.getD 0))

def apply (width : ℕ) (matrix : Matrix) (vector initial : List GoldWord) : Option (List GoldWord) :=
  if vector.length = width ∧ initial.length = width then
    if validate matrix width then some (payload width matrix vector initial) else none
  else none

theorem payload_length (width : ℕ) (matrix : Matrix) (vector initial : List GoldWord) :
    (payload width matrix vector initial).length = width := by simp only [payload,List.length_map,List.length_range]

theorem apply_success (width : ℕ) (matrix : Matrix) (vector initial : List GoldWord)
    (valid : validate matrix width = true) (vectorSize : vector.length = width) (initialSize : initial.length = width) :
    apply width matrix vector initial = some (payload width matrix vector initial) := by
  simp only [apply,vectorSize,initialSize,and_self,ite_true,valid]

theorem payload_get (width : ℕ) (matrix : Matrix) (vector initial : List GoldWord) (index : Fin width) :
    (payload width matrix vector initial)[index.val]'(by rw [payload_length]; exact index.isLt) =
      dotFrom ((row matrix index.val).zip vector) (initial[index.val]?.getD 0) := by
  simp only [payload,List.getElem_map,List.getElem_range]

theorem zip_ofFn {width : ℕ} (left right : Fin width → GoldWord) :
    (List.ofFn left).zip (List.ofFn right) = List.ofFn (fun index => (left index,right index)) := by
  induction width with
  | zero => rfl
  | succ width ih => simp only [List.ofFn_succ,List.zip_cons_cons,ih]

noncomputable section

/-- Field meaning of the actual ascending-column multiply/add sequence. -/
theorem payload_value (width : ℕ) (matrix : Matrix) (valid : validate matrix width = true)
    (vector initial : Fin width → GoldWord) :
    (payload width matrix (List.ofFn vector) (List.ofFn initial)).map goldValue =
      List.ofFn (fun row => goldValue (initial row) +
        (NativeGoldMatrixMeaning.semantic width matrix valid *ᵥ (fun column => goldValue (vector column))) row) := by
  apply List.ext_getElem (by simp only [List.length_map,payload_length,List.length_ofFn])
  intro index inside other
  have bound : index < width := by simpa only [List.length_ofFn] using other
  simp only [List.getElem_map,List.getElem_ofFn]
  rw [payload_get _ _ _ _ ⟨index,bound⟩,NativeGoldMatrixMeaning.row_ofFn width matrix ⟨index,bound⟩ valid,
    zip_ofFn,NativeGoldMatrix.dotFrom_value,List.map_ofFn,Fin.sum_ofFn]
  simp only [List.getElem?_ofFn,dite_eq_left bound,Option.getD_some]
  rfl

end
end FormalProof4FHE.HasteBoots.NativeGoldMatrixAccumulate
