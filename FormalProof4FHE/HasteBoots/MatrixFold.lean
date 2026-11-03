module

public import FormalProof4FHE.HasteBoots.MatrixOpening

@[expose] public section

/-!
# Least-significant-variable-first folding

Semantic counterpart of `PackedTable::fold` and `evaluate` in
`HasteBoots/algebra/src/matrix_weighted.rs`. A cube is indexed by the first
Boolean bit and its suffix. No property of the challenge generator is assumed.
-/

open scoped BigOperators
open Matrix

namespace FormalProof4FHE.HasteBoots.MatrixFold

def Cube : ℕ → Type
  | 0 => Unit
  | n + 1 => Bool × Cube n

instance cubeFintype : (n : ℕ) → Fintype (Cube n)
  | 0 => inferInstanceAs (Fintype Unit)
  | n + 1 =>
    letI := cubeFintype n
    inferInstanceAs (Fintype (Bool × Cube n))

variable {F Lane : Type*} [Semiring F] [Fintype Lane] [DecidableEq Lane]

abbrev Pair := Bool → Matrix Lane Lane F

/-- Eliminate the first Boolean variable, retaining the suffix order. -/
def foldFirst {n : ℕ} (pair : Pair (F := F) (Lane := Lane))
    (table : Cube (n + 1) → Lane → F) : Cube n → Lane → F :=
  fun suffix => ∑ bit, pair bit *ᵥ table (bit, suffix)

/-- Later query matrices act on the left of earlier ones. -/
def weight : (query : List (Pair (F := F) (Lane := Lane))) →
    Cube query.length → Matrix Lane Lane F
  | [], _ => 1
  | pair :: tail, (bit, suffix) => weight tail suffix * pair bit

/-- Execute the ordered fold without materializing a full weight matrix per cell. -/
def foldAll : (query : List (Pair (F := F) (Lane := Lane))) →
    (Cube query.length → Lane → F) → Lane → F
  | [], table => table ()
  | pair :: tail, table => foldAll tail (foldFirst pair table)

def weightedEvaluation (query : List (Pair (F := F) (Lane := Lane)))
    (table : Cube query.length → Lane → F) : Lane → F :=
  ∑ cell, weight query cell *ᵥ table cell

/-- The actual ordered fold has exactly the advertised matrix-weighted semantics. -/
theorem foldAll_eq_weightedEvaluation
    (query : List (Pair (F := F) (Lane := Lane)))
    (table : Cube query.length → Lane → F) :
    foldAll query table = weightedEvaluation query table := by
  classical
  induction query with
  | nil =>
    change table () = ∑ cell : Unit, (1 : Matrix Lane Lane F) *ᵥ table cell
    rw [Fintype.sum_subsingleton _ ()]
    simp
  | cons pair tail ih =>
    rw [foldAll, ih]
    change (∑ suffix : Cube tail.length,
      weight tail suffix *ᵥ (∑ bit : Bool, pair bit *ᵥ table (bit, suffix))) =
      ∑ cell : Bool × Cube tail.length,
        (weight tail cell.2 * pair cell.1) *ᵥ table cell
    simp only [Fintype.sum_prod_type, Matrix.mulVec_sum, Matrix.mulVec_mulVec]
    exact Finset.sum_comm

end FormalProof4FHE.HasteBoots.MatrixFold
