module

public import FormalProof4FHE.HasteBoots.NativeGoldMatrixFill
public import FormalProof4FHE.HasteBoots.NativeGoldPostMap
public import FormalProof4FHE.HasteBoots.NativeGoldCubic

@[expose] public section

/-!
# Raw native extension multiplication-matrix construction

This is the checked `packed_extension::multiplication` constructor: allocate
raw zeros, multiply by each raw basis monomial, and copy its three stored
coordinates in column/row order. The complete payload interpretation is the
existing padded multiplication matrix, including its unused zero lanes.
Instruction, scheduler and PCS refinement remain separate obligations.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldMultiplicationMatrix

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeGoldExtensionArithmetic (Word)
open scoped Matrix

/-- Native monomial initialization: raw zero coordinates with one raw one. -/
def monomial (column : ℕ) : Word := fun row => if row.val = column then 1 else 0

def entry (value : Word) (row column : ℕ) : GoldWord :=
  if meaningful : row < 3 then NativeGoldCubic.mul value (monomial column) ⟨row, meaningful⟩ else 0

def payload (width : ℕ) (value : Word) : List GoldWord :=
  NativeGoldMatrixFill.fill width 3 3 (entry value)

def matrix (width : ℕ) (value : Word) : NativeGoldMatrix.Matrix := ⟨width, payload width value⟩

def multiplication (width : ℕ) (value : Word) : Option NativeGoldMatrix.Matrix :=
  if NativeGoldProjection.dimensions width then NativeGoldMatrix.checked width (payload width value) else none

theorem monomial_list (column : Fin 3) :
    List.ofFn (monomial column.val) = (List.replicate 3 (0 : GoldWord)).set column.val 1 := by
  apply List.ext_getElem (by simp)
  intro index leftPresent rightPresent
  simp only [List.getElem_ofFn, List.getElem_set, List.getElem_replicate, monomial]
  by_cases same : index = column.val
  · simp only [same, ite_true]
  · simp only [same, Ne.symm same, ite_false]

theorem payload_length (width : ℕ) (value : Word) : (payload width value).length = width * width :=
  NativeGoldMatrixFill.fill_length width 3 3 (entry value)

theorem matrix_valid (width : ℕ) (value : Word) (shape : NativeGoldProjection.dimensions width = true) :
    NativeGoldMatrix.validate (matrix width value) width = true := by
  have bounds := (NativeGoldProjection.dimensions_iff width).mp shape
  exact (NativeGoldMatrix.validate_iff _ _).mpr ⟨by omega, rfl, bounds.2, payload_length width value⟩

theorem multiplication_success (width : ℕ) (value : Word) (shape : NativeGoldProjection.dimensions width = true) :
    multiplication width value = some (matrix width value) := by
  rw [multiplication, ite_eq_left shape]
  exact (NativeGoldMatrix.checked_iff _ _ _).mpr ⟨
    (NativeGoldMatrix.validate_iff _ _).mp (matrix_valid width value shape) |>.1,
    (NativeGoldProjection.dimensions_iff width).mp shape |>.2, payload_length width value, rfl⟩

/-- Every copied coordinate is the actual raw monomial product; all other
entries retain their initialized zero word. -/
theorem payload_get (width : ℕ) (value : Word) (enough : 3 ≤ width) (row column : Fin width) :
    (payload width value)[row.val * width + column.val]'(by
      rw [payload_length]; exact NativeGoldMatrixMeaning.address_bound width row column) =
      if column.val < 3 then NativeGoldHelper.coefficient width
        (NativeGoldCubic.mul value (monomial column.val)) row else 0 := by
  simp only [payload]
  rw [NativeGoldMatrixFill.fill_get width 3 3 (entry value) enough enough]
  by_cases columnInside : column.val < 3
  · simp only [columnInside, and_true, ite_true]
    by_cases rowInside : row.val < 3
    · simp only [ite_eq_left rowInside, entry, NativeGoldHelper.coefficient, dite_eq_left rowInside]
    · simp only [ite_eq_right rowInside, NativeGoldHelper.coefficient, dite_eq_right rowInside]
  · simp only [columnInside, and_false, ite_false]

noncomputable section

theorem monomial_value (column : Fin 3) : goldExtensionValue (monomial column.val) = goldilocksBasis column := by
  apply goldilocksBasis.equivFun.injective
  ext row
  simp only [goldExtension_coordinate, Module.Basis.equivFun_self, monomial]
  by_cases same : row = column
  · subst row; simp [goldValue]
  · have different : row.val ≠ column.val := fun equal => same (Fin.ext equal)
    simp only [different, Ne.symm same, ite_false, goldValue, Fin.val_zero, Nat.cast_zero]

/-- The semantic matrix is derived from the complete raw constructed payload. -/
theorem semantic_eq {padding : ℕ} (value : Word)
    (shape : NativeGoldProjection.dimensions (3 + padding) = true) :
    NativeGoldMatrixMeaning.semantic (3 + padding) (matrix (3 + padding) value)
      (matrix_valid (3 + padding) value shape) =
        PaddedExtension.multiplication (padding := padding) goldilocksBasis (goldExtensionValue value) := by
  funext row column
  change goldValue ((payload (3 + padding) value)[row.val * (3 + padding) + column.val]'(by
    rw [payload_length]; exact NativeGoldMatrixMeaning.address_bound _ row column)) = _
  rw [payload_get (3 + padding) value (by omega)]
  refine Fin.addCases (fun column => ?_) (fun column => ?_) column
  · simp only [Fin.val_castAdd, column.isLt, ite_true, NativeGoldHelper.coefficient_value,
      NativeGoldCubic.mul_value, monomial_value column, NativeHelperPacking.coefficients_padded,
      PaddedExtension.multiplication_left]
  · have outside : ¬(Fin.natAdd 3 column).val < 3 := by simp only [Fin.val_natAdd]; omega
    simp only [outside, ite_false, PaddedExtension.multiplication_right, goldValue, Fin.val_zero, Nat.cast_zero]

/-- Applying the actual raw constructor multiplies by the supplied extension
value after decoding the meaningful input lanes. Original padding is arbitrary. -/
theorem apply_value {padding : ℕ} (value : Word) (input : Fin (3 + padding) → GoldWord)
    (shape : NativeGoldProjection.dimensions (3 + padding) = true) :
    (NativeGoldMatrix.apply (3 + padding) (matrix (3 + padding) value) (List.ofFn input)).map (List.map goldValue) =
      some (List.ofFn (PaddedExtension.encode (padding := padding) goldilocksBasis
        (goldExtensionValue value * PaddedExtension.decode goldilocksBasis (fun i => goldValue (input i))))) := by
  rw [NativeGoldMatrixMeaning.apply_value _ _ (matrix_valid _ _ shape), semantic_eq value shape,
    PaddedExtension.multiplication_mulVec]

/-- The constructed post-matrix always yields valid output padding, even
when the original opened vector has nonzero unused lanes. -/
theorem project_value {padding : ℕ} (value : Word) (input : Fin (3 + padding) → GoldWord)
    (shape : NativeGoldProjection.dimensions (3 + padding) = true) :
    (NativeGoldPostMap.project (3 + padding) (some (matrix (3 + padding) value)) (List.ofFn input)).map
      goldExtensionValue = some (goldExtensionValue value *
        PaddedExtension.decode goldilocksBasis (fun i => goldValue (input i))) := by
  rw [NativeGoldPostMap.project_value _ _ ((NativeGoldProjection.dimensions_iff _).mp shape).2,
    NativeGoldPostMap.fieldApply, ite_eq_right (by omega : 3 + padding ≠ 0),
    dite_eq_left (matrix_valid _ _ shape), Option.bind_some, semantic_eq value shape,
    PaddedExtension.element_multiplication]

end

end FormalProof4FHE.HasteBoots.NativeGoldMultiplicationMatrix
