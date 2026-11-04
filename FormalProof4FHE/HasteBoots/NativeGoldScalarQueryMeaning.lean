module

public import FormalProof4FHE.HasteBoots.NativeGoldScalarQuery
public import FormalProof4FHE.HasteBoots.NativeGoldQueryProjection
public import FormalProof4FHE.HasteBoots.ExtensionLookupTerminal

@[expose] public section

/-!
# Meaning of the complete raw scalar-source query constructor

The accepted outer checks derive the lane shape, machine shift bounds and
all original point getters. The complete raw constructor and checked field
reader produce the existing native scalar query on those coordinates.
The source-query and source-truth adapters below consume the original
point, rather than a separately supplied query or geometry certificate.
Native folding, PCS authentication and instruction refinement remain open.
-/

namespace FormalProof4FHE.HasteBoots.NativeGoldScalarQueryMeaning

open NativeFields NativeFieldRepresentation NativeFieldWire NativeExtensionFields
open NativeGoldExtensionArithmetic (Word)
open NativeGoldScalarQuery (built scalarQuery lowPoint highPoint)
open NativeScalarQueryShape (check laneBits)

noncomputable section

theorem readFirstProduct {padding c : ℕ} (value : Word) (low : Fin c → Word)
    (shape : NativeGoldProjection.dimensions (3 + padding) = true) (power : 3 + padding = 2 ^ c) :
    NativeGoldCoefficientsQuery.readMatrix (3 + padding)
      (NativeGoldMatrixProduct.result (3 + padding)
        (NativeGoldMultiplicationMatrix.matrix (3 + padding) value)
        (NativeGoldLaneMatrix.matrix (3 + padding) (List.ofFn low))
        (NativeGoldMultiplicationMatrix.matrix_valid _ _ shape)
        (NativeGoldLaneMatrix.matrix_valid _ _ shape)) = some
          (PaddedExtension.multiplication (padding := padding) goldilocksBasis (goldExtensionValue value) *
            ExtensionQuery.laneMatrix goldilocksBasis
              (ExtensionQuery.laneWeights (ExtensionQuery.nativeLanes power) (fun i => goldExtensionValue (low i)))) := by
  rw [NativeGoldCoefficientsQuery.readMatrix, dite_eq_left (NativeGoldMatrixProduct.result_valid _ _ _ _ _),
    NativeGoldMatrixProduct.semantic_eq, NativeGoldMultiplicationMatrix.semantic_eq value shape,
    NativeGoldLaneMatrix.semantic_nativeLanes low shape power]

/-- The nonempty first pair has M(weight)*L; the empty branch has only L as
its post-map. All remaining pairs retain their actual helper construction. -/
theorem interpret_built {padding c n : ℕ} (low : Fin c → Word) (high : Fin n → Word)
    (shape : NativeGoldProjection.dimensions (3 + padding) = true) (power : 3 + padding = 2 ^ c) :
    NativeGoldCoefficientsQuery.interpret (3 + padding) n
      (built (3 + padding) (List.ofFn low) (List.ofFn high) shape) = some
        (ExtensionQuery.scalarQuery goldilocksBasis
          (ExtensionQuery.laneWeights (ExtensionQuery.nativeLanes power) (fun i => goldExtensionValue (low i))) n
          (fun i => goldExtensionValue (high i))) := by
  cases n with
  | zero =>
    simp only [List.ofFn_zero, built, NativeGoldCoefficientsQuery.interpret, NativeGoldCoefficientsQuery.readPairs,
      Option.bind_some, NativeGoldCoefficientsQuery.readPost, NativeGoldLaneMatrix.readMatrix_lanes low shape power,
      Option.map_some, ExtensionQuery.scalarQuery]
  | succ n =>
    rw [List.ofFn_succ]
    simp only [built, NativeGoldCoefficientsQuery.interpret, NativeGoldCoefficientsQuery.readPairs,
      readFirstProduct _ low shape power, Option.bind_some,
      NativeGoldExtensionArithmetic.sub_value, NativeGoldLookup.one_value]
    rw [NativeGoldCoefficientsQuery.readPairs_built (fun i => high i.succ) shape, Option.map_some, Option.bind_some]
    simp only [NativeGoldCoefficientsQuery.readPost, Option.map_some, ExtensionQuery.scalarQuery]
    congr 3
    funext bit
    cases bit <;> rfl

/-- The lane weights use the checked power shape and the original low getters. -/
def laneWeights {padding : ℕ} (sourceVars : ℕ) (point : List Word)
    (accepted : check sourceVars (3 + padding) point.length = true) : Fin (3 + padding) → Goldilocks3 :=
  ExtensionQuery.laneWeights
    (ExtensionQuery.nativeLanes (NativeScalarQueryShape.checked_power _ _ _ accepted))
    (fun i => goldExtensionValue (lowPoint sourceVars (3 + padding) point accepted i))

def rowPoint {padding : ℕ} (sourceVars : ℕ) (point : List Word)
    (accepted : check sourceVars (3 + padding) point.length = true) : Fin sourceVars → Goldilocks3 :=
  fun i => goldExtensionValue (highPoint sourceVars (3 + padding) point accepted i)

/-- The full point view retains every original coordinate, with a bound
derived from accepted checked addition and the original list length. -/
def fullPoint {padding : ℕ} (sourceVars : ℕ) (point : List Word)
    (accepted : check sourceVars (3 + padding) point.length = true) :
    Fin (laneBits (3 + padding) + sourceVars) → Goldilocks3 := fun i => goldExtensionValue
      (point[i.val]'(by have length := NativeScalarQueryShape.checked_length _ _ _ accepted; omega))

/-- End-to-end construction/reader correspondence for every accepted original
raw point list. The caller does not supply the split point or tensor weights. -/
theorem scalarQuery_value {padding : ℕ} (sourceVars : ℕ) (point : List Word)
    (accepted : check sourceVars (3 + padding) point.length = true) :
    (scalarQuery sourceVars (3 + padding) point).bind (NativeGoldCoefficientsQuery.interpret (3 + padding) sourceVars) =
      some (ExtensionQuery.scalarQuery goldilocksBasis (laneWeights sourceVars point accepted) sourceVars
        (rowPoint sourceVars point accepted)) := by
  rw [NativeGoldScalarQuery.scalarQuery_success _ _ _ accepted, Option.bind_some,
    NativeGoldScalarQuery.take_eq_ofFn _ _ _ accepted, NativeGoldScalarQuery.drop_eq_ofFn _ _ _ accepted]
  exact interpret_built (lowPoint sourceVars (3 + padding) point accepted) (highPoint sourceVars (3 + padding) point accepted)
    (NativeScalarQueryShape.checked_dimensions _ _ _ accepted) (NativeScalarQueryShape.checked_power _ _ _ accepted)

/-- The constructed query is the existing lookup-terminal source query at
the complete original point, with native low-lane/high-row coordinate order. -/
theorem scalarQuery_sourceQuery {padding : ℕ} (sourceVars : ℕ) (point : List Word)
    (accepted : check sourceVars (3 + padding) point.length = true) :
    (scalarQuery sourceVars (3 + padding) point).bind (NativeGoldCoefficientsQuery.interpret (3 + padding) sourceVars) =
      some (ExtensionLookupTerminal.sourceQuery goldilocksBasis (NativeScalarQueryShape.checked_power _ _ _ accepted)
        (fullPoint sourceVars point accepted)) := by
  rw [scalarQuery_value sourceVars point accepted]
  rfl

/-- Every original source lane is retained under the constructed query's
existing scalar-MLE evaluation, including nonzero unused helper lanes. -/
theorem scalarQuery_evaluate {padding : ℕ} (sourceVars : ℕ) (point : List Word)
    (accepted : check sourceVars (3 + padding) point.length = true)
    (table : MatrixFold.Cube sourceVars → Fin (3 + padding) → Goldilocks) :
    ((scalarQuery sourceVars (3 + padding) point).bind (NativeGoldCoefficientsQuery.interpret (3 + padding) sourceVars)).map
      (fun query => query.evaluate table) = some (PaddedExtension.encode (padding := padding) goldilocksBasis
        (ExtensionLookupTerminal.sourceTruth (NativeScalarQueryShape.checked_power _ _ _ accepted)
          (fullPoint sourceVars point accepted) table)) := by
  rw [scalarQuery_sourceQuery sourceVars point accepted, Option.map_some, ExtensionLookupTerminal.source_evaluate]

/-- The original claimed vector is processed by the actual constructed
query's post-map and padding check before entering the terminal decoder. -/
theorem scalarQuery_project_value {padding : ℕ} (sourceVars : ℕ) (point : List Word)
    (accepted : check sourceVars (3 + padding) point.length = true) (input : Fin (3 + padding) → GoldWord) :
    ((scalarQuery sourceVars (3 + padding) point).bind (fun raw =>
      NativeGoldPostMap.project (3 + padding) raw.post (List.ofFn input))).map goldExtensionValue =
        PaddedExtension.element goldilocksBasis
          ((ExtensionLookupTerminal.sourceQuery goldilocksBasis (NativeScalarQueryShape.checked_power _ _ _ accepted)
            (fullPoint sourceVars point accepted)).finish (fun i => goldValue (input i))) := by
  have interpreted := scalarQuery_sourceQuery sourceVars point accepted
  rw [NativeGoldScalarQuery.scalarQuery_success _ _ _ accepted, Option.bind_some] at interpreted
  rw [NativeGoldScalarQuery.scalarQuery_success _ _ _ accepted, Option.bind_some]
  exact NativeGoldQueryProjection.query_project_value _ _ interpreted input
    ((NativeGoldProjection.dimensions_iff _).mp (NativeScalarQueryShape.checked_dimensions _ _ _ accepted)).2

/-- Conditional decoding of a truthful original scalar-source opening.
Deriving this opening premise from accepted PCS verification remains open. -/
theorem scalarQuery_project_truth {padding : ℕ} (sourceVars : ℕ) (point : List Word)
    (accepted : check sourceVars (3 + padding) point.length = true) (input : Fin (3 + padding) → GoldWord)
    (table : MatrixFold.Cube sourceVars → Fin (3 + padding) → Goldilocks)
    (correct : (fun i => goldValue (input i)) =
      (ExtensionLookupTerminal.sourceQuery goldilocksBasis (NativeScalarQueryShape.checked_power _ _ _ accepted)
        (fullPoint sourceVars point accepted)).query.fold table) :
    ((scalarQuery sourceVars (3 + padding) point).bind (fun raw =>
      NativeGoldPostMap.project (3 + padding) raw.post (List.ofFn input))).map goldExtensionValue = some
        (ExtensionLookupTerminal.sourceTruth (NativeScalarQueryShape.checked_power _ _ _ accepted)
          (fullPoint sourceVars point accepted) table) := by
  rw [scalarQuery_project_value sourceVars point accepted input, correct, ← ExtensionQuery.Broadcast.evaluate,
    ExtensionLookupTerminal.source_evaluate, PaddedExtension.element_encode]

end

end FormalProof4FHE.HasteBoots.NativeGoldScalarQueryMeaning
