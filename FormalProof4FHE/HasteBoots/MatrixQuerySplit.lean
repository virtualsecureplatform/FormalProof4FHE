module

public import FormalProof4FHE.HasteBoots.FlatMatrixFold

@[expose] public section

/-!
# Native front/suffix table split

The front is the low address portion. Its matrix acts first; the suffix
matrix multiplies on the left. The same indexing identifies complete-query
flat folding with the two-half evaluation used in the opening security proof.
-/

open scoped BigOperators
open Matrix

namespace FormalProof4FHE.HasteBoots.MatrixQuerySplit

variable {F Lane : Type} [Semiring F] [Fintype Lane] [DecidableEq Lane]

/-- Join front and suffix Boolean assignments in variable order. -/
def appendCube : (front suffix : List (MatrixFold.Pair (F := F) (Lane := Lane))) →
    MatrixFold.Cube front.length → MatrixFold.Cube suffix.length →
      MatrixFold.Cube (front ++ suffix).length
  | [], _, _, suffix => suffix
  | _ :: tail, rest, (bit, front), suffix => (bit, appendCube tail rest front suffix)

/-- Later query matrices multiply on the left, including at a split boundary. -/
theorem weight_append (front suffix : List (MatrixFold.Pair (F := F) (Lane := Lane)))
    (left : MatrixFold.Cube front.length) (right : MatrixFold.Cube suffix.length) :
    MatrixFold.weight (front ++ suffix) (appendCube front suffix left right) =
      MatrixFold.weight suffix right * MatrixFold.weight front left := by
  induction front with
  | nil => simp only [List.nil_append, appendCube, MatrixFold.weight, mul_one]
  | cons pair tail ih =>
    rcases left with ⟨bit, left⟩
    simp only [List.cons_append, appendCube, MatrixFold.weight, ih, mul_assoc]

/-- Flat left/right cell indices, with the front in the low bits. -/
def join (front suffix : List (MatrixFold.Pair (F := F) (Lane := Lane))) :
    (Fin (2 ^ front.length) × Fin (2 ^ suffix.length)) ≃ Fin (2 ^ (front ++ suffix).length) :=
  (Equiv.prodComm _ _).trans (finProdFinEquiv.trans
    (finCongr (by simp only [List.length_append, Nat.pow_add, Nat.mul_comm])))

omit [Semiring F] [Fintype Lane] [DecidableEq Lane] in
/-- Exact source-table address used by the native aggregation loop. -/
theorem join_val (front suffix : List (MatrixFold.Pair (F := F) (Lane := Lane)))
    (left : Fin (2 ^ front.length)) (right : Fin (2 ^ suffix.length)) :
    (join front suffix (left, right)).val = left.val + 2 ^ front.length * right.val := rfl

omit [Semiring F] [Fintype Lane] [DecidableEq Lane] in
/-- Cube concatenation and native flat source-table addresses agree. -/
theorem index_append_val (front suffix : List (MatrixFold.Pair (F := F) (Lane := Lane)))
    (left : MatrixFold.Cube front.length) (right : MatrixFold.Cube suffix.length) :
    (FlatMatrixFold.index (front ++ suffix).length (appendCube front suffix left right)).val =
      (FlatMatrixFold.index front.length left).val +
        2 ^ front.length * (FlatMatrixFold.index suffix.length right).val := by
  induction front with
  | nil =>
    have zeroIndex : (FlatMatrixFold.index 0 left).val = 0 := by
      have bound := (FlatMatrixFold.index 0 left).isLt
      change _ < 1 at bound
      omega
    simp only [List.nil_append, appendCube, List.length_nil, zeroIndex, pow_zero, one_mul, zero_add]
  | cons pair tail ih =>
    rcases left with ⟨bit, left⟩
    simp only [List.cons_append, appendCube, List.length_cons]
    rw [FlatMatrixFold.index_succ_val bit (appendCube tail suffix left right),
      FlatMatrixFold.index_succ_val bit left, ih, Nat.pow_succ]
    ring

omit [Semiring F] [Fintype Lane] [DecidableEq Lane] in
theorem index_append (front suffix : List (MatrixFold.Pair (F := F) (Lane := Lane)))
    (left : MatrixFold.Cube front.length) (right : MatrixFold.Cube suffix.length) :
    FlatMatrixFold.index (front ++ suffix).length (appendCube front suffix left right) =
      join front suffix (FlatMatrixFold.index front.length left, FlatMatrixFold.index suffix.length right) := by
  apply Fin.ext
  exact index_append_val front suffix left right

/-- Native tensor weights factor across the split in the correct matrix order. -/
theorem weights_join (front suffix : List (MatrixFold.Pair (F := F) (Lane := Lane)))
    (left : Fin (2 ^ front.length)) (right : Fin (2 ^ suffix.length)) :
    FlatMatrixFold.weights (front ++ suffix) (join front suffix (left, right)) =
      FlatMatrixFold.weights suffix right * FlatMatrixFold.weights front left := by
  have address := index_append front suffix
    ((FlatMatrixFold.index front.length).symm left) ((FlatMatrixFold.index suffix.length).symm right)
  simp only [Equiv.apply_symm_apply] at address
  rw [← address]
  simp only [FlatMatrixFold.weights, Equiv.symm_apply_apply, weight_append]

/-- Appending a variable creates the two native weight-vector halves by left multiplication. -/
theorem weights_snoc (front : List (MatrixFold.Pair (F := F) (Lane := Lane)))
    (pair : MatrixFold.Pair (F := F) (Lane := Lane))
    (left : Fin (2 ^ front.length)) (bit : Bool) :
    FlatMatrixFold.weights (front ++ [pair])
      (join front [pair] (left, FlatMatrixFold.index 1 (bit, ()))) =
      pair bit * FlatMatrixFold.weights front left := by
  rw [weights_join]
  have single : FlatMatrixFold.weights [pair] (FlatMatrixFold.index 1 (bit, ())) = pair bit := by
    change MatrixFold.weight [pair]
      ((FlatMatrixFold.index 1).symm (FlatMatrixFold.index 1 (bit, ()))) = pair bit
    have roundtrip := (FlatMatrixFold.index 1).symm_apply_apply
      (show MatrixFold.Cube 1 from (bit, ()))
    exact (congrArg (MatrixFold.weight [pair]) roundtrip).trans (one_mul _)
  rw [single]

/-- Complete-query flat folding is precisely the two-half matrix evaluation. -/
theorem foldAll_eq_split (front suffix : List (MatrixFold.Pair (F := F) (Lane := Lane)))
    (table : Fin (2 ^ (front ++ suffix).length) → Lane → F) :
    FlatMatrixFold.foldAll (front ++ suffix) table =
      matrixEvaluation (FlatMatrixFold.weights front) (FlatMatrixFold.weights suffix)
        (fun left right => table (join front suffix (left, right))) := by
  classical
  rw [FlatMatrixFold.foldAll_eq_weighted]
  rw [← (join front suffix).sum_comp
    (fun cell => FlatMatrixFold.weights (front ++ suffix) cell *ᵥ table cell)]
  simp only [Fintype.sum_prod_type, weights_join, matrixEvaluation]
  exact Finset.sum_comm

end FormalProof4FHE.HasteBoots.MatrixQuerySplit
