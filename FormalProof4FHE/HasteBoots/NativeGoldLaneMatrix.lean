module

public import FormalProof4FHE.HasteBoots.NativeGoldLaneWeights

@[expose] public section

/-!
# Raw scalar-source lane coefficient matrix

The native constructor copies each raw lane weight into one whole original
source column, in ascending lane/coordinate order. Every original column
participates, including columns that helper projection would ignore.
The scalar-query outer power-of-two, ilog2 and point split remain separate
from this checked matrix-construction arithmetic.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldLaneMatrix

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeGoldExtensionArithmetic (Word)
open NativeGoldLaneWeights (weight laneWord)
open scoped Matrix

def entry (point : List Word) (row column : ℕ) : GoldWord :=
  if meaningful : row < 3 then weight (laneWord column) point ⟨row, meaningful⟩ else 0

def payload (width : ℕ) (point : List Word) : List GoldWord :=
  NativeGoldMatrixFill.fill width 3 width (entry point)

def matrix (width : ℕ) (point : List Word) : NativeGoldMatrix.Matrix := ⟨width, payload width point⟩

def lanes (width : ℕ) (point : List Word) : Option NativeGoldMatrix.Matrix :=
  if NativeGoldProjection.dimensions width then NativeGoldMatrix.checked width (payload width point) else none

theorem payload_length (width : ℕ) (point : List Word) : (payload width point).length = width * width :=
  NativeGoldMatrixFill.fill_length width 3 width (entry point)

theorem matrix_valid (width : ℕ) (point : List Word) (shape : NativeGoldProjection.dimensions width = true) :
    NativeGoldMatrix.validate (matrix width point) width = true := by
  have bounds := (NativeGoldProjection.dimensions_iff width).mp shape
  exact (NativeGoldMatrix.validate_iff _ _).mpr ⟨by omega, rfl, bounds.2, payload_length width point⟩

theorem lanes_success (width : ℕ) (point : List Word) (shape : NativeGoldProjection.dimensions width = true) :
    lanes width point = some (matrix width point) := by
  rw [lanes, ite_eq_left shape]
  exact (NativeGoldMatrix.checked_iff _ _ _).mpr ⟨
    (NativeGoldMatrix.validate_iff _ _).mp (matrix_valid width point shape) |>.1,
    (NativeGoldProjection.dimensions_iff width).mp shape |>.2, payload_length width point, rfl⟩

theorem lanes_invalid (width : ℕ) (point : List Word) (invalid : NativeGoldProjection.dimensions width ≠ true) :
    lanes width point = none := by rw [lanes, ite_eq_right invalid]

/-- Every original source lane stores its own actual raw weight coefficients. -/
theorem payload_get (width : ℕ) (point : List Word) (enough : 3 ≤ width) (row column : Fin width) :
    (payload width point)[row.val * width + column.val]'(by
      rw [payload_length]; exact NativeGoldMatrixMeaning.address_bound width row column) =
      NativeGoldHelper.coefficient width (weight (laneWord column.val) point) row := by
  simp only [payload]
  rw [NativeGoldMatrixFill.fill_get width 3 width (entry point) enough (by omega)]
  simp only [column.isLt, and_true]
  by_cases rowInside : row.val < 3
  · simp only [ite_eq_left rowInside, entry, NativeGoldHelper.coefficient, dite_eq_left rowInside]
  · simp only [ite_eq_right rowInside, NativeGoldHelper.coefficient, dite_eq_right rowInside]

noncomputable section

/-- Derived from the actual raw payload, with every original input column. -/
theorem semantic_eq {padding : ℕ} (point : List Word)
    (shape : NativeGoldProjection.dimensions (3 + padding) = true) :
    NativeGoldMatrixMeaning.semantic (3 + padding) (matrix (3 + padding) point)
      (matrix_valid (3 + padding) point shape) = ExtensionQuery.laneMatrix goldilocksBasis
        (fun lane => goldExtensionValue (weight (laneWord lane.val) point)) := by
  funext row column
  change goldValue ((payload (3 + padding) point)[row.val * (3 + padding) + column.val]'(by
    rw [payload_length]; exact NativeGoldMatrixMeaning.address_bound _ row column)) = _
  rw [payload_get (3 + padding) point (by omega), NativeGoldHelper.coefficient_value,
    NativeHelperPacking.coefficients_padded]
  rfl

/-- The low-bit tensor weights are derived from the same checked source lanes. -/
theorem semantic_nativeLanes {padding c : ℕ} (point : Fin c → Word)
    (shape : NativeGoldProjection.dimensions (3 + padding) = true) (power : 3 + padding = 2 ^ c) :
    NativeGoldMatrixMeaning.semantic (3 + padding) (matrix (3 + padding) (List.ofFn point))
      (matrix_valid (3 + padding) (List.ofFn point) shape) = ExtensionQuery.laneMatrix goldilocksBasis
        (ExtensionQuery.laneWeights (ExtensionQuery.nativeLanes power) (fun i => goldExtensionValue (point i))) := by
  rw [semantic_eq (List.ofFn point) shape]
  congr 1
  funext lane
  exact NativeGoldLaneWeights.weight_nativeLanes point shape power lane

theorem readMatrix_lanes {padding c : ℕ} (point : Fin c → Word)
    (shape : NativeGoldProjection.dimensions (3 + padding) = true) (power : 3 + padding = 2 ^ c) :
    NativeGoldCoefficientsQuery.readMatrix (3 + padding) (matrix (3 + padding) (List.ofFn point)) =
      some (ExtensionQuery.laneMatrix goldilocksBasis
        (ExtensionQuery.laneWeights (ExtensionQuery.nativeLanes power) (fun i => goldExtensionValue (point i)))) := by
  rw [NativeGoldCoefficientsQuery.readMatrix, dite_eq_left (matrix_valid _ _ shape), semantic_nativeLanes point shape power]

/-- All original scalar input lanes contribute, without a padded-input premise. -/
theorem apply_value {padding : ℕ} (point : List Word) (input : Fin (3 + padding) → GoldWord)
    (shape : NativeGoldProjection.dimensions (3 + padding) = true) :
    (NativeGoldMatrix.apply (3 + padding) (matrix (3 + padding) point) (List.ofFn input)).map (List.map goldValue) =
      some (List.ofFn (PaddedExtension.encode (padding := padding) goldilocksBasis
        (ExtensionQuery.laneValue (fun lane => goldExtensionValue (weight (laneWord lane.val) point))
          (fun lane => goldValue (input lane))))) := by
  rw [NativeGoldMatrixMeaning.apply_value _ _ (matrix_valid _ _ shape), semantic_eq point shape,
    ExtensionQuery.laneMatrix_mulVec]

/-- Checked projection after the actual lane matrix reads the weighted sum
of all original source lanes. Unused output rows are zero by construction. -/
theorem project_value {padding : ℕ} (point : List Word) (input : Fin (3 + padding) → GoldWord)
    (shape : NativeGoldProjection.dimensions (3 + padding) = true) :
    (NativeGoldPostMap.project (3 + padding) (some (matrix (3 + padding) point)) (List.ofFn input)).map
      goldExtensionValue = some (ExtensionQuery.laneValue
        (fun lane => goldExtensionValue (weight (laneWord lane.val) point)) (fun lane => goldValue (input lane))) := by
  rw [NativeGoldPostMap.project_value _ _ ((NativeGoldProjection.dimensions_iff _).mp shape).2,
    NativeGoldPostMap.fieldApply, ite_eq_right (by omega : 3 + padding ≠ 0),
    dite_eq_left (matrix_valid _ _ shape), Option.bind_some, semantic_eq point shape,
    ExtensionQuery.laneMatrix_mulVec, PaddedExtension.element_encode]

end

end FormalProof4FHE.HasteBoots.NativeGoldLaneMatrix
