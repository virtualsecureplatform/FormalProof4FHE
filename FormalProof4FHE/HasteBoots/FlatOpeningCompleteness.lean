module

public import FormalProof4FHE.HasteBoots.FlatOpeningSecurity
public import FormalProof4FHE.HasteBoots.MatrixOpeningCompleteness

@[expose] public section

/-!
# Completeness of complete-query flat matrix openings

The same native address bijection is used for honest aggregation, response
finishing, source extraction and complete-query evaluation.
-/

open Matrix

namespace FormalProof4FHE.HasteBoots.FlatOpeningCompleteness

noncomputable section

variable {F Position : Type} [Field F] {m b : ℕ}

/-- A two-half table stored at its native flat addresses. -/
def flatten (front suffix : List (MatrixFold.Pair (F := F) (Lane := Fin b)))
    (table : Fin (2 ^ front.length) → Fin (2 ^ suffix.length) → Fin b → F)
    (cell : Fin (2 ^ (front ++ suffix).length)) : Fin b → F :=
  let pair := (MatrixQuerySplit.join front suffix).symm cell
  table pair.1 pair.2

/-- Honest structured messages, folded through the suffix, equal complete-query
evaluation by the native adjacent-cell fold loop. -/
theorem finish (front suffix : List (MatrixFold.Pair (F := F) (Lane := Fin b)))
    (table : Fin (2 ^ front.length) → Fin (2 ^ suffix.length) → Fin b → F) :
    FlatMatrixFold.foldAll suffix (fun right lane =>
      MatrixOpeningCompleteness.response (MatrixResponse.weights (FlatMatrixFold.weights front))
        table lane right) =
      FlatMatrixFold.foldAll (front ++ suffix) (flatten front suffix table) := by
  rw [← FlatMatrixFold.finishMessage_eq_fold, MatrixOpeningCompleteness.finish,
    MatrixQuerySplit.foldAll_eq_split]
  congr 1
  funext left right
  simp only [flatten, Equiv.symm_apply_apply]

/-- Honest flat extraction recovers every original table cell, including cases
where a final code symbol was only partially occupied. -/
theorem extract [Fintype Position] [DecidableEq F] [NeZero b]
    (domain : Position ↪ F) (front suffix : List (MatrixFold.Pair (F := F) (Lane := Fin b)))
    (enough : m ≤ Fintype.card Position) (capacity : 2 ^ suffix.length ≤ m * b)
    (radius : ℕ) (margin : 2 * radius <
      Code.minDist (BlockCode.code domain m b : Set (Position → Fin b → F)))
    (table : Fin (2 ^ front.length) → Fin (2 ^ suffix.length) → Fin b → F) :
    FlatOpeningSecurity.extract domain front suffix capacity radius
      (MatrixOpeningCompleteness.encodedTable (m := m) domain table) = flatten front suffix table := by
  funext cell lane
  unfold FlatOpeningSecurity.extract flatten
  rw [MatrixOpeningCompleteness.extract domain enough capacity radius margin table]

end

end FormalProof4FHE.HasteBoots.FlatOpeningCompleteness
