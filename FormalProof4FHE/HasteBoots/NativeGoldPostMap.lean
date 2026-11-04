module

public import FormalProof4FHE.HasteBoots.NativeGoldProjection
public import FormalProof4FHE.HasteBoots.NativeGoldMatrixMeaning

@[expose] public section

/-!
# Checked native query post-map and extension projection

`BroadcastQuery::apply` is identity only when there is no post-matrix.
Otherwise the actual matrix is validated and applied before padding is
checked by `packed_extension::element`. Source/helper query constructors
and accepted PCS opening correspondence remain separate obligations.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldPostMap

open NativeFields NativeFieldRepresentation NativeExtensionFields NativeFieldWire
open NativeGoldExtensionArithmetic (Word)
open scoped Matrix

def apply (width : ℕ) (post : Option NativeGoldMatrix.Matrix) (values : List GoldWord) : Option (List GoldWord) :=
  match post with
  | none => if width = 0 ∨ values.length ≠ width then none else some values
  | some matrix => NativeGoldMatrix.apply width matrix values

def project (width : ℕ) (post : Option NativeGoldMatrix.Matrix) (values : List GoldWord) : Option Word :=
  (apply width post values).bind (NativeGoldProjection.element width)

noncomputable section

/-- Interpret only the matrix actually carried by the native query. Invalid
matrix shape remains failure instead of supplying an unrelated field map. -/
def fieldApply (width : ℕ) (post : Option NativeGoldMatrix.Matrix) (values : Fin width → Goldilocks) :
    Option (Fin width → Goldilocks) :=
  if width = 0 then none else
    match post with
    | none => some values
    | some matrix => if valid : NativeGoldMatrix.validate matrix width = true then
        some (NativeGoldMatrixMeaning.semantic width matrix valid *ᵥ values) else none

theorem apply_value (width : ℕ) (post : Option NativeGoldMatrix.Matrix) (values : Fin width → GoldWord)
    (positive : width ≠ 0) :
    (apply width post (List.ofFn values)).map (List.map goldValue) =
      (fieldApply width post (fun i => goldValue (values i))).map List.ofFn := by
  have guard : ¬(width = 0 ∨ (List.ofFn values).length ≠ width) := by
    simp only [List.length_ofFn, ne_eq, not_true_eq_false, or_false]
    exact positive
  cases post with
  | none =>
    rw [apply, ite_eq_right guard, fieldApply, ite_eq_right positive]
    simp only [Option.map_some, List.map_ofFn, Function.comp_def]
  | some matrix =>
    by_cases valid : NativeGoldMatrix.validate matrix width = true
    · rw [apply, NativeGoldMatrixMeaning.apply_value width matrix valid values,
        fieldApply, ite_eq_right positive, dite_eq_left valid, Option.map_some]
    · rw [apply, NativeGoldMatrix.apply, ite_eq_right guard, ite_eq_right valid, Option.map_none,
        fieldApply, ite_eq_right positive, dite_eq_right valid, Option.map_none]

/-- A successful raw post-map provides its own exact output length. -/
theorem apply_length (width : ℕ) (post : Option NativeGoldMatrix.Matrix) (values output : List GoldWord)
    (success : apply width post values = some output) : output.length = width := by
  cases post with
  | none =>
    simp only [apply] at success
    split at success
    · contradiction
    · rename_i valid
      have widthEq : values.length = width := by omega
      exact congrArg List.length (Option.some.inj success).symm |>.trans widthEq
  | some matrix => exact NativeGoldMatrix.apply_length width matrix values output success

/-- The checked query application followed by native projection has exactly
the existing padded-extension meaning, for all raw input lanes. -/
theorem project_value {padding : ℕ} (post : Option NativeGoldMatrix.Matrix)
    (values : Fin (3 + padding) → GoldWord) (fits : (3 + padding) * (3 + padding) < 2 ^ 64) :
    (project (3 + padding) post (List.ofFn values)).map goldExtensionValue =
      (fieldApply (3 + padding) post (fun i => goldValue (values i))).bind
        (PaddedExtension.element goldilocksBasis) := by
  have interpreted := apply_value (3 + padding) post values (by omega)
  cases executed : apply (3 + padding) post (List.ofFn values) with
  | none =>
    rw [executed, Option.map_none] at interpreted
    have absent : fieldApply (3 + padding) post (fun i => goldValue (values i)) = none := by
      cases result : fieldApply (3 + padding) post (fun i => goldValue (values i)) with
      | none => rfl
      | some vector => rw [result, Option.map_some] at interpreted; contradiction
    rw [project, executed, Option.bind_none, Option.map_none, absent, Option.bind_none]
  | some output =>
    have length := apply_length (3 + padding) post (List.ofFn values) output executed
    let raw : Fin (3 + padding) → GoldWord := fun i => output[i.val]'(by rw [length]; exact i.isLt)
    have rebuilt : List.ofFn raw = output := by
      apply List.ext_getElem (by rw [List.length_ofFn, length])
      intro index leftPresent rightPresent
      simp only [List.getElem_ofFn, raw]
    rw [executed, Option.map_some] at interpreted
    cases result : fieldApply (3 + padding) post (fun i => goldValue (values i)) with
    | none => rw [result, Option.map_none] at interpreted; contradiction
    | some vector =>
      rw [result, Option.map_some] at interpreted
      have coordinates : (fun i => goldValue (raw i)) = vector := by
        funext i
        have same := congrArg (fun list => list[i.val]?) (Option.some.inj interpreted)
        rw [List.getElem?_map, List.getElem?_eq_getElem (by rw [length]; exact i.isLt),
          List.getElem?_eq_getElem (by rw [List.length_ofFn]; exact i.isLt), List.getElem_ofFn, Option.map_some] at same
        exact Option.some.inj same
      have projected := NativeGoldProjection.element_value raw fits
      rw [rebuilt] at projected
      rw [coordinates] at projected
      simp only [project, executed, Option.bind_some]
      exact projected

end

end FormalProof4FHE.HasteBoots.NativeGoldPostMap
