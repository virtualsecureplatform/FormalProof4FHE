module
public import FormalProof4FHE.HasteBoots.PublicMonomialEvaluation
public import FormalProof4FHE.HasteBoots.MatrixQuerySplit
@[expose] public section

/-! One query-independent packed source for the complete public monomial
check. Coefficients occupy low cell bits, then rounds, then ciphertext half.
This is exact finite table arithmetic, not Rust allocation/usize refinement. -/
namespace FormalProof4FHE.HasteBoots.PackedMonomialLayout
open scoped BigOperators
open Matrix
noncomputable section
variable {F Lane : Type} [Semiring F] [Fintype Lane] [DecidableEq Lane]

theorem fold_split (front back : List (MatrixFold.Pair (F := F) (Lane := Lane))) (word : ℕ → Lane → F) :
    FlatMatrixFold.foldAll (front++back) (fun position => word position.val) =
      FlatMatrixFold.foldAll back (fun right => FlatMatrixFold.foldAll front
        (fun left => word (left.val+2^front.length*right.val))) := by
  classical
  simp only [FlatMatrixFold.foldAll_eq_weighted]
  rw [← (MatrixQuerySplit.join front back).sum_comp]
  simp only [Fintype.sum_prod_type, MatrixQuerySplit.weights_join, MatrixQuerySplit.join_val,
    Matrix.mulVec_mulVec, Matrix.mulVec_sum]
  exact Finset.sum_comm

omit [DecidableEq Lane] in
theorem fold_single (pair : MatrixFold.Pair (F := F) (Lane := Lane)) (word : ℕ → Lane → F) :
    FlatMatrixFold.foldAll [pair] (fun position => word position.val) =
      pair false *ᵥ word 0 + pair true *ᵥ word 1 := rfl

theorem fold_three (front back : List (MatrixFold.Pair (F := F) (Lane := Lane)))
    (half : MatrixFold.Pair (F := F) (Lane := Lane)) (word : ℕ → Lane → F) :
    FlatMatrixFold.foldAll (front++(back++[half])) (fun position => word position.val) =
      half false *ᵥ FlatMatrixFold.foldAll back (fun right => FlatMatrixFold.foldAll front
        (fun left => word (left.val+2^front.length*right.val))) +
      half true *ᵥ FlatMatrixFold.foldAll back (fun right => FlatMatrixFold.foldAll front
        (fun left => word (left.val+2^front.length*(right.val+2^back.length)))) := by
  rw [fold_split]
  let suffix : ℕ → Lane → F := fun right => FlatMatrixFold.foldAll front
    (fun left => word (left.val+2^front.length*right))
  change FlatMatrixFold.foldAll (back++[half]) (fun position => suffix position.val) = _
  rw [fold_split]
  rw [fold_single half (fun bit => FlatMatrixFold.foldAll back
    (fun left => suffix (left.val+2^back.length*bit)))]
  simp only [suffix, Nat.mul_zero, Nat.add_zero, Nat.mul_one]

/-- Low front bits followed by high back bits. -/
def join (front back : ℕ) : (Fin (2^front) × Fin (2^back)) ≃ Fin (2^(front+back)) :=
  (Equiv.prodComm _ _).trans (finProdFinEquiv.trans (finCongr (by rw [pow_add, Nat.mul_comm])))

theorem join_val (front back : ℕ) (first : Fin (2^front)) (last : Fin (2^back)) :
    (join front back (first,last)).val = first.val+2^front*last.val := rfl

def layout (coefficient rows : ℕ) :
    (Fin (2^coefficient) × (Fin (2^rows) × Bool)) ≃ Fin (2^(coefficient+(rows+1))) :=
  (Equiv.prodCongr (Equiv.refl _) ((Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans (join rows 1))).trans
    (join coefficient (rows+1))

theorem layout_val (coefficient rows : ℕ) (cell : Fin (2^coefficient)) (row : Fin (2^rows)) (half : Bool) :
    (layout coefficient rows (cell,(row,half))).val =
      cell.val+2^coefficient*(row.val+2^rows*(if half then 1 else 0)) := by
  change cell.val+2^coefficient*(row.val+2^rows*(finTwoEquiv.symm half).val) = _
  cases half <;> rfl

/-- Address of a scalar in the concatenated halves of the native allocation. -/
theorem scalar_address (lanes coefficient rows : ℕ) (cell : Fin (2^coefficient)) (row : Fin (2^rows))
    (half : Bool) (lane : Fin (2^lanes)) :
    2^lanes*(layout coefficient rows (cell,(row,half))).val+lane.val =
      (PublicMonomialEvaluation.flatAddress lanes coefficient cell lane).val +
        2^(coefficient+lanes)*(row.val+2^rows*(if half then 1 else 0)) := by
  rw [layout_val]
  change 2^lanes*(cell.val+2^coefficient*(row.val+2^rows*(if half then 1 else 0)))+lane.val =
    lane.val+2^lanes*cell.val+2^(coefficient+lanes)*(row.val+2^rows*(if half then 1 else 0))
  rw [pow_add]
  ring

variable {q lanes coefficient rows rounds : ℕ} [Fact q.Prime]

/-- The fixed public table is defined without any matrix query. -/
def source (psi : ZMod q) (rotations : Fin rounds → Fin (2*(2^(coefficient+lanes))))
    (position : Fin (2^(coefficient+(rows+1)))) (lane : Fin (2^lanes)) : ZMod q :=
  let coordinate := (layout coefficient rows).symm position
  PublicMonomialTable.table psi rotations coordinate.2.2 coordinate.2.1
    (PublicMonomialEvaluation.flatAddress lanes coefficient coordinate.1 lane)

/-- Zero outside the finite source extent; valid folds never read it there. -/
def word (psi : ZMod q) (rotations : Fin rounds → Fin (2*(2^(coefficient+lanes))))
    (position : ℕ) : Fin (2^lanes) → ZMod q :=
  if bound : position < 2^(coefficient+(rows+1)) then source psi rotations ⟨position,bound⟩ else 0

theorem word_coordinate (psi : ZMod q) (rotations : Fin rounds → Fin (2*(2^(coefficient+lanes))))
    (cell : Fin (2^coefficient)) (row : Fin (2^rows)) (half : Bool) :
    word (rows := rows) psi rotations (cell.val+2^coefficient*(row.val+2^rows*(if half then 1 else 0))) =
      fun lane => PublicMonomialTable.table psi rotations half row
        (PublicMonomialEvaluation.flatAddress lanes coefficient cell lane) := by
  have value := layout_val coefficient rows cell row half
  have bound : cell.val+2^coefficient*(row.val+2^rows*(if half then 1 else 0)) < 2^(coefficient+(rows+1)) := by
    rw [← value]
    exact (layout coefficient rows (cell,(row,half))).isLt
  unfold word
  rw [dite_eq_left bound]
  have index : (⟨cell.val+2^coefficient*(row.val+2^rows*(if half then 1 else 0)),bound⟩ : Fin (2^(coefficient+(rows+1)))) =
      layout coefficient rows (cell,(row,half)) := Fin.ext value.symm
  rw [index]
  unfold source
  rw [Equiv.symm_apply_apply]

theorem word_inbounds (psi : ZMod q) (rotations : Fin rounds → Fin (2*(2^(coefficient+lanes))))
    (position : Fin (2^(coefficient+(rows+1)))) :
    word (rows := rows) psi rotations position.val = source psi rotations position := by
  unfold word
  rw [dite_eq_left position.isLt]

/-- Every coefficient slice belongs to that same public source, independent
of which matrix query is used to evaluate it. -/
theorem coefficient_slice (psi : ZMod q)
    (query : List (MatrixFold.Pair (F := ZMod q) (Lane := Fin (2^lanes))))
    (rotations : Fin rounds → Fin (2*(2^(query.length+lanes)))) (row : Fin (2^rows)) (half : Bool) :
    FlatMatrixFold.foldAll query (fun cell => word (rows := rows) psi rotations
      (cell.val+2^query.length*(row.val+2^rows*(if half then 1 else 0)))) =
      PublicMonomialEvaluation.materializedRows psi lanes query rotations half row := by
  rw [FlatMatrixFold.foldAll_eq_cube]
  unfold PublicMonomialEvaluation.materializedRows
  apply congrArg (MatrixFold.foldAll query)
  funext cell lane
  rw [word_coordinate psi rotations (FlatMatrixFold.index query.length cell) row half]
  rw [PublicMonomialEvaluation.address_eq_flat]

/-- The optimized evaluator equals a single full packed-table fold, with
coefficient, round and half variables in their native order. -/
theorem evaluate_source (psi : ZMod q) (lanes : ℕ)
    (coefficientQuery rowQuery : List (MatrixFold.Pair (F := ZMod q) (Lane := Fin (2^lanes))))
    (halfPair : MatrixFold.Pair (F := ZMod q) (Lane := Fin (2^lanes)))
    (primitive : IsPrimitiveRoot psi (2^(coefficientQuery.length+lanes+1)))
    (rotations : Fin rounds → Fin (2*(2^(coefficientQuery.length+lanes)))) :
    PublicMonomialEvaluation.evaluate psi lanes coefficientQuery rowQuery halfPair rotations =
      FlatMatrixFold.foldAll (coefficientQuery++(rowQuery++[halfPair]))
        (fun position => word (rows := rowQuery.length) psi rotations position.val) := by
  rw [fold_three]
  have slices (half : Bool) :
      FlatMatrixFold.foldAll rowQuery (fun row => FlatMatrixFold.foldAll coefficientQuery
        (fun cell => word (rows := rowQuery.length) psi rotations
          (cell.val+2^coefficientQuery.length*(row.val+2^rowQuery.length*(if half then 1 else 0))))) =
      FlatMatrixFold.foldAll rowQuery (PublicMonomialEvaluation.materializedRows psi lanes coefficientQuery rotations half) := by
    apply congrArg (FlatMatrixFold.foldAll rowQuery)
    funext row
    exact coefficient_slice psi coefficientQuery rotations row half
  have first := slices false
  have last := slices true
  simp only [Bool.false_eq_true, ite_false, Nat.mul_zero, Nat.add_zero] at first
  simp only [ite_true, Nat.mul_one] at last
  rw [first, last]
  exact PublicMonomialEvaluation.evaluate_materialized psi lanes coefficientQuery rowQuery halfPair primitive rotations

/-- Reindex only the query's length; the public source stays fixed. -/
def queryIndex {α : Type} (front back : List α) (half : α) :
    Fin (2^(front++(back++[half])).length) ≃ Fin (2^(front.length+(back.length+1))) :=
  finCongr (by simp only [List.length_append, List.length_singleton])

theorem queryIndex_val {α : Type} (front back : List α) (half : α)
    (position : Fin (2^(front++(back++[half])).length)) :
    (queryIndex front back half position).val = position.val := rfl

/-- The finite source itself, without a total-word interface, is evaluated by
one complete packed query in coefficient/round/half order. -/
theorem evaluate_packed (psi : ZMod q) (lanes : ℕ)
    (coefficientQuery rowQuery : List (MatrixFold.Pair (F := ZMod q) (Lane := Fin (2^lanes))))
    (halfPair : MatrixFold.Pair (F := ZMod q) (Lane := Fin (2^lanes)))
    (primitive : IsPrimitiveRoot psi (2^(coefficientQuery.length+lanes+1)))
    (rotations : Fin rounds → Fin (2*(2^(coefficientQuery.length+lanes)))) :
    PublicMonomialEvaluation.evaluate psi lanes coefficientQuery rowQuery halfPair rotations =
      FlatMatrixFold.foldAll (coefficientQuery++(rowQuery++[halfPair]))
        (fun position => source psi rotations (queryIndex coefficientQuery rowQuery halfPair position)) := by
  rw [evaluate_source psi lanes coefficientQuery rowQuery halfPair primitive rotations]
  apply congrArg (FlatMatrixFold.foldAll (coefficientQuery++(rowQuery++[halfPair])))
  funext position lane
  exact congrFun (word_inbounds psi rotations (queryIndex coefficientQuery rowQuery halfPair position)) lane

theorem coefficient_query_slice {α : Type} (front back : List α) (half : α) :
    (front++(back++[half])).take front.length = front := by simp

theorem row_query_slice {α : Type} (front back : List α) (half : α) :
    ((front++(back++[half])).drop front.length).take back.length = back := by simp

theorem half_query_slice {α : Type} (front back : List α) (half : α) :
    (front++(back++[half])).getLast? = some half := by simp

end
end FormalProof4FHE.HasteBoots.PackedMonomialLayout
