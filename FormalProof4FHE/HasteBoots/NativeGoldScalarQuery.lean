module

public import FormalProof4FHE.HasteBoots.NativeScalarQueryShape
public import FormalProof4FHE.HasteBoots.NativeGoldLaneMatrix
public import FormalProof4FHE.HasteBoots.NativeGoldMatrixProduct

@[expose] public section

/-!
# Complete checked raw scalar-source query constructor

The original point is split at the checked ilog2 width. The lane matrix and
helper query are actually constructed before the first pair is multiplied
on the right by the lane map. For an empty remaining point the already
constructed helper post-map is replaced by the lane matrix. All checked
matrix calls and their failure order are retained. Instruction and work
refinement remain separate.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldScalarQuery

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeGoldExtensionArithmetic (Word)
open NativeGoldCoefficientsQuery (Query Pair)
open NativeScalarQueryShape (check laneBits)

/-- Native first-pair mutation, or replacement of the empty helper post-map. -/
def install (lanes : NativeGoldMatrix.Matrix) (query : Query) : Option Query :=
  match query.pairs with
  | [] => some { query with post := some lanes }
  | pair :: tail => (NativeGoldMatrixProduct.mul pair.zero lanes).bind (fun zero =>
      (NativeGoldMatrixProduct.mul pair.one lanes).map (fun one =>
        { query with pairs := ⟨zero, one⟩ :: tail }))

def scalarQuery (sourceVars width : ℕ) (point : List Word) : Option Query :=
  if check sourceVars width point.length then
    (NativeGoldLaneMatrix.lanes width (point.take (laneBits width))).bind (fun lanes =>
      (NativeGoldCoefficientsQuery.coefficientsQuery width (point.drop (laneBits width))).bind (install lanes))
  else none

/-- Derived raw result; every product below consumes the actual original
constructed matrices and their proved native validation checks. -/
def built (width : ℕ) (low high : List Word) (shape : NativeGoldProjection.dimensions width = true) : Query :=
  let lanes := NativeGoldLaneMatrix.matrix width low
  let lanesValid := NativeGoldLaneMatrix.matrix_valid width low shape
  match high with
  | [] => ⟨[], some lanes⟩
  | value :: tail =>
      let zero := NativeGoldMultiplicationMatrix.matrix width (NativeGoldExtensionArithmetic.sub NativeGoldLookup.one value)
      let one := NativeGoldMultiplicationMatrix.matrix width value
      ⟨⟨NativeGoldMatrixProduct.result width zero lanes
          (NativeGoldMultiplicationMatrix.matrix_valid _ _ shape) lanesValid,
        NativeGoldMatrixProduct.result width one lanes
          (NativeGoldMultiplicationMatrix.matrix_valid _ _ shape) lanesValid⟩ ::
        (NativeGoldCoefficientsQuery.built width tail).pairs, none⟩

theorem install_built (width : ℕ) (low high : List Word) (shape : NativeGoldProjection.dimensions width = true) :
    install (NativeGoldLaneMatrix.matrix width low) (NativeGoldCoefficientsQuery.built width high) =
      some (built width low high shape) := by
  cases high with
  | nil => rfl
  | cons value tail =>
    simp only [NativeGoldCoefficientsQuery.built, List.map_cons, install,
      NativeGoldMatrixProduct.mul_success width _ _ (NativeGoldMultiplicationMatrix.matrix_valid _ _ shape)
        (NativeGoldLaneMatrix.matrix_valid _ _ shape), Option.bind_some, Option.map_some, built,
      List.isEmpty_cons, Bool.false_eq_true, ite_false]

theorem scalarQuery_success (sourceVars width : ℕ) (point : List Word)
    (accepted : check sourceVars width point.length = true) :
    scalarQuery sourceVars width point = some (built width (point.take (laneBits width)) (point.drop (laneBits width))
      (NativeScalarQueryShape.checked_dimensions _ _ _ accepted)) := by
  have shape := NativeScalarQueryShape.checked_dimensions _ _ _ accepted
  rw [scalarQuery, ite_eq_left accepted, NativeGoldLaneMatrix.lanes_success _ _ shape,
    Option.bind_some, NativeGoldCoefficientsQuery.coefficientsQuery_success _ _ shape,
    Option.bind_some, install_built width _ _ shape]

theorem scalarQuery_invalid (sourceVars width : ℕ) (point : List Word)
    (invalid : check sourceVars width point.length ≠ true) : scalarQuery sourceVars width point = none := by
  rw [scalarQuery, ite_eq_right invalid]

/-- No hidden arithmetic failure remains after the actual outer checks pass. -/
theorem scalarQuery_none_iff (sourceVars width : ℕ) (point : List Word) :
    scalarQuery sourceVars width point = none ↔ check sourceVars width point.length ≠ true := by
  by_cases accepted : check sourceVars width point.length = true
  · rw [scalarQuery_success _ _ _ accepted]
    simp only [Option.some_ne_none, accepted, ne_self_iff_false]
  · rw [scalarQuery_invalid _ _ _ accepted]
    exact ⟨fun _ => accepted, fun _ => rfl⟩

/-- A returned raw query provides its own complete outer-check evidence. -/
theorem scalarQuery_checked (sourceVars width : ℕ) (point : List Word) (query : Query)
    (success : scalarQuery sourceVars width point = some query) : check sourceVars width point.length = true := by
  by_contra rejected
  rw [scalarQuery_invalid _ _ _ rejected] at success
  contradiction

theorem built_length (width : ℕ) (low high : List Word) (shape : NativeGoldProjection.dimensions width = true) :
    (built width low high shape).pairs.length = high.length := by
  cases high with
  | nil => rfl
  | cons value tail => simp only [built, List.length_cons, NativeGoldCoefficientsQuery.built_length]

theorem scalarQuery_length (sourceVars width : ℕ) (point : List Word) (query : Query)
    (success : scalarQuery sourceVars width point = some query) : query.pairs.length = sourceVars := by
  have accepted := scalarQuery_checked sourceVars width point query success
  have same := Option.some.inj ((scalarQuery_success _ _ _ accepted).symm.trans success)
  rw [← same, built_length, List.length_drop]
  have length := NativeScalarQueryShape.checked_length _ _ _ accepted
  omega

/-- The low getter retains the original point coordinate at every lane bit. -/
def lowPoint (sourceVars width : ℕ) (point : List Word) (accepted : check sourceVars width point.length = true) :
    Fin (laneBits width) → Word := fun i => point[i.val]'(by
      have length := NativeScalarQueryShape.checked_length _ _ _ accepted; omega)

/-- The high getter retains the original coordinate after the exact native split. -/
def highPoint (sourceVars width : ℕ) (point : List Word) (accepted : check sourceVars width point.length = true) :
    Fin sourceVars → Word := fun i => point[laneBits width + i.val]'(by
      have length := NativeScalarQueryShape.checked_length _ _ _ accepted; omega)

theorem take_eq_ofFn (sourceVars width : ℕ) (point : List Word) (accepted : check sourceVars width point.length = true) :
    point.take (laneBits width) = List.ofFn (lowPoint sourceVars width point accepted) := by
  have length := NativeScalarQueryShape.checked_length _ _ _ accepted
  apply List.ext_getElem (by rw [List.length_take, List.length_ofFn, Nat.min_eq_left (by omega)])
  intro index leftPresent rightPresent
  simp only [List.getElem_take, List.getElem_ofFn, lowPoint]

theorem drop_eq_ofFn (sourceVars width : ℕ) (point : List Word) (accepted : check sourceVars width point.length = true) :
    point.drop (laneBits width) = List.ofFn (highPoint sourceVars width point accepted) := by
  have length := NativeScalarQueryShape.checked_length _ _ _ accepted
  apply List.ext_getElem (by rw [List.length_drop, List.length_ofFn]; omega)
  intro index leftPresent rightPresent
  simp only [List.getElem_drop, List.getElem_ofFn, highPoint]

end FormalProof4FHE.HasteBoots.NativeGoldScalarQuery
