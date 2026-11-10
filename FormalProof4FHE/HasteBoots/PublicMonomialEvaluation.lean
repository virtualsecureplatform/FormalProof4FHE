module
public import FormalProof4FHE.HasteBoots.MonomialBitOrder
@[expose] public section

/-! Exact field semantics of the optimized public-monomial coefficient loop.
Scalar phases commute with matrix-vector multiplication; query matrices retain
their native order. Machine shifts, field kernels and Rust memory are separate. -/
namespace FormalProof4FHE.HasteBoots.PublicMonomialEvaluation
open scoped BigOperators
open Matrix
noncomputable section
variable {F Lane : Type} [CommSemiring F] [Fintype Lane]

def cells (phase : F) (n : ℕ) (base : Lane → F) (cell : MatrixFold.Cube n) : Lane → F :=
  phase^(2*(NTTButterfly.outputIndex n cell).val) • base

/-- The multiplier exponent decreases by one bit on each native iteration. -/
def loop (phase : F) : List (MatrixFold.Pair (F := F) (Lane := Lane)) → (Lane → F) → Lane → F
  | [], base => base
  | pair :: tail, base => loop phase tail
      (pair false *ᵥ base + phase^(2^(tail.length+1)) • (pair true *ᵥ base))

theorem foldFirst_cells (phase : F) (n : ℕ) (pair : MatrixFold.Pair (F := F) (Lane := Lane)) (base : Lane → F) :
    MatrixFold.foldFirst pair (cells phase (n+1) base) =
      cells phase n (pair false *ᵥ base + phase^(2^(n+1)) • (pair true *ᵥ base)) := by
  funext suffix
  simp only [MatrixFold.foldFirst, Fintype.sum_bool, cells, NTTButterfly.outputIndex_succ_val,
    ite_true, Bool.false_eq_true, ite_false, zero_add, Matrix.mulVec_smul, smul_add, smul_smul]
  have exponent : 2*(2^n+(NTTButterfly.outputIndex n suffix).val) =
      2*(NTTButterfly.outputIndex n suffix).val+2^(n+1) := by rw [pow_succ]; ring
  rw [exponent, pow_add, add_comm]

theorem loop_eq_fold (phase : F) (query : List (MatrixFold.Pair (F := F) (Lane := Lane))) (base : Lane → F) :
    loop phase query base = MatrixFold.foldAll query (cells phase query.length base) := by
  induction query generalizing base with
  | nil => simp [loop, MatrixFold.foldAll, cells, NTTButterfly.outputIndex]
  | cons pair tail ih =>
    simp only [loop, MatrixFold.foldAll, List.length_cons, foldFirst_cells, ih]

theorem fold_zero (query : List (MatrixFold.Pair (F := F) (Lane := Lane))) :
    MatrixFold.foldAll query (fun _ => (0 : Lane → F)) = 0 := by
  induction query with
  | nil => rfl
  | cons pair tail ih =>
    rw [MatrixFold.foldAll]
    apply Eq.trans ?_ ih
    apply congrArg (MatrixFold.foldAll tail)
    funext suffix
    simp only [MatrixFold.foldFirst, Matrix.mulVec_zero, Finset.sum_const_zero]

variable {q : ℕ} [Fact q.Prime]

/-- The lane address is reversed over the full transform width by shifting its
lane-only reversed value by the number of coefficient bits. -/
def base (phase : ZMod q) (lanes coefficient : ℕ) (lane : Fin (2^lanes)) : ZMod q :=
  phase^(2*(2^coefficient*(NTTButterfly.outputIndex lanes ((FlatMatrixFold.index lanes).symm lane)).val)+1)

def address (lanes coefficient : ℕ) (cell : MatrixFold.Cube coefficient) (lane : Fin (2^lanes)) : Fin (2^(coefficient+lanes)) :=
  FlatMatrixFold.index (coefficient+lanes) (MonomialBitOrder.append ((FlatMatrixFold.index lanes).symm lane) cell)

theorem address_val (lanes coefficient : ℕ) (cell : MatrixFold.Cube coefficient) (lane : Fin (2^lanes)) :
    (address lanes coefficient cell lane).val = lane.val+2^lanes*(FlatMatrixFold.index coefficient cell).val := by
  simp only [address, MonomialBitOrder.flat_append, Equiv.apply_symm_apply]

/-- The contiguous native row address: lanes are the low address bits. -/
def flatAddress (lanes coefficient : ℕ) (cell : Fin (2^coefficient)) (lane : Fin (2^lanes)) : Fin (2^(coefficient+lanes)) :=
  finCongr (Nat.pow_add 2 coefficient lanes).symm (finProdFinEquiv (cell,lane))

theorem address_eq_flat (lanes coefficient : ℕ) (cell : MatrixFold.Cube coefficient) (lane : Fin (2^lanes)) :
    address lanes coefficient cell lane = flatAddress lanes coefficient (FlatMatrixFold.index coefficient cell) lane := by
  apply Fin.ext
  exact address_val lanes coefficient cell lane

def packedPowers (phase : ZMod q) (lanes coefficient : ℕ) (cell : MatrixFold.Cube coefficient) (lane : Fin (2^lanes)) : ZMod q :=
  phase^(2*(NTTButterfly.reverseIndex (coefficient+lanes) (address lanes coefficient cell lane)).val+1)

theorem packedPowers_eq_cells (phase : ZMod q) (lanes coefficient : ℕ) :
    packedPowers phase lanes coefficient = cells phase coefficient (base phase lanes coefficient) := by
  funext cell lane
  simp only [packedPowers, address, MonomialBitOrder.reverse_flat, MonomialBitOrder.output_append,
    cells, base, Pi.smul_apply, smul_eq_mul]
  rw [← pow_add]
  congr 1
  ring

/-- The coefficient slice of an active materialized row in actual lane/cell
address order, rather than an assumed geometric table. -/
def materialized (psi : ZMod q) (lanes coefficient : ℕ) (rotation : Fin (2*(2^(coefficient+lanes))))
    (cell : MatrixFold.Cube coefficient) (lane : Fin (2^lanes)) : ZMod q :=
  NTTButterfly.flatTransform (coefficient+lanes) psi (psi^2) (PublicMonomialTable.coefficients rotation)
    (address lanes coefficient cell lane)

theorem materialized_eq_powers (psi : ZMod q) (lanes coefficient : ℕ)
    (primitive : IsPrimitiveRoot psi (2^(coefficient+lanes+1))) (rotation : Fin (2*(2^(coefficient+lanes)))) :
    materialized psi lanes coefficient rotation = packedPowers (psi^rotation.val) lanes coefficient := by
  funext cell lane
  simp only [materialized, PublicMonomialTable.butterfly_coefficients (coefficient+lanes) psi primitive,
    BlindRotationMonomial.powers, NTTButterfly.nodes, packedPowers]
  rw [← pow_mul, ← pow_mul]
  exact congrArg (psi^·) (Nat.mul_comm _ _)

/-- The optimized phase initialization and ordered coefficient loop evaluate
exactly the materialized signed-monomial NTT row. -/
theorem loop_materialized (psi : ZMod q) (lanes : ℕ)
    (query : List (MatrixFold.Pair (F := ZMod q) (Lane := Fin (2^lanes))))
    (primitive : IsPrimitiveRoot psi (2^(query.length+lanes+1))) (rotation : Fin (2*(2^(query.length+lanes)))) :
    loop (psi^rotation.val) query (base (psi^rotation.val) lanes query.length) =
      MatrixFold.foldAll query (materialized psi lanes query.length rotation) := by
  rw [materialized_eq_powers psi lanes query.length primitive rotation, packedPowers_eq_cells]
  exact loop_eq_fold _ _ _

/-- The same theorem for the flat adjacent-cell folds used by PackedTable. -/
theorem loop_flat_materialized (psi : ZMod q) (lanes : ℕ)
    (query : List (MatrixFold.Pair (F := ZMod q) (Lane := Fin (2^lanes))))
    (primitive : IsPrimitiveRoot psi (2^(query.length+lanes+1))) (rotation : Fin (2*(2^(query.length+lanes)))) :
    loop (psi^rotation.val) query (base (psi^rotation.val) lanes query.length) =
      FlatMatrixFold.foldAll query (fun cell lane =>
        NTTButterfly.flatTransform (query.length+lanes) psi (psi^2) (PublicMonomialTable.coefficients rotation)
          (flatAddress lanes query.length cell lane)) := by
  rw [FlatMatrixFold.foldAll_eq_cube]
  have same : (fun cell lane =>
      NTTButterfly.flatTransform (query.length+lanes) psi (psi^2) (PublicMonomialTable.coefficients rotation)
        (flatAddress lanes query.length (FlatMatrixFold.index query.length cell) lane)) =
      materialized psi lanes query.length rotation := by
    funext cell lane
    rw [← address_eq_flat]
    rfl
  rw [same]
  exact loop_materialized psi lanes query primitive rotation

/-- Active rows run the coefficient loop; inactive rows retain their zero
initialization. The original row index is used without deduplication. -/
def optimizedRows (psi : ZMod q) (lanes : ℕ)
    (query : List (MatrixFold.Pair (F := ZMod q) (Lane := Fin (2^lanes))))
    {rounds padded : ℕ} (rotations : Fin rounds → Fin (2*(2^(query.length+lanes))))
    (position : Fin padded) : Fin (2^lanes) → ZMod q :=
  if active : position.val < rounds then
    let phase := psi^(rotations ⟨position.val,active⟩).val
    loop phase query (base phase lanes query.length)
  else 0

def materializedRows (psi : ZMod q) (lanes : ℕ)
    (query : List (MatrixFold.Pair (F := ZMod q) (Lane := Fin (2^lanes))))
    {rounds padded : ℕ} (rotations : Fin rounds → Fin (2*(2^(query.length+lanes))))
    (half : Bool) (position : Fin padded) : Fin (2^lanes) → ZMod q :=
  MatrixFold.foldAll query (fun cell lane => PublicMonomialTable.table psi rotations half position
    (address lanes query.length cell lane))

theorem optimizedRows_eq_materialized (psi : ZMod q) (lanes : ℕ)
    (query : List (MatrixFold.Pair (F := ZMod q) (Lane := Fin (2^lanes))))
    (primitive : IsPrimitiveRoot psi (2^(query.length+lanes+1)))
    {rounds padded : ℕ} (rotations : Fin rounds → Fin (2*(2^(query.length+lanes)))) (half : Bool) :
    optimizedRows psi lanes query (padded := padded) rotations = materializedRows psi lanes query rotations half := by
  funext position
  unfold optimizedRows materializedRows
  by_cases active : position.val < rounds
  · rw [dite_eq_left active]
    simp only [PublicMonomialTable.table, PublicMonomialTable.row, dite_eq_left active]
    exact loop_materialized psi lanes query primitive _
  · rw [dite_eq_right active]
    simp only [PublicMonomialTable.table_inactive psi primitive rotations half position active, Pi.zero_apply]
    exact (fold_zero query).symm

/-- All arithmetic stages of Plan::evaluate, with typed valid dimensions and
queries: coefficient loop, padded row folds and the duplicated-half fold. -/
def evaluate (psi : ZMod q) (lanes : ℕ)
    (coefficient rowQuery : List (MatrixFold.Pair (F := ZMod q) (Lane := Fin (2^lanes))))
    (halfPair : MatrixFold.Pair (F := ZMod q) (Lane := Fin (2^lanes)))
    {rounds : ℕ} (rotations : Fin rounds → Fin (2*(2^(coefficient.length+lanes)))) : Fin (2^lanes) → ZMod q :=
  let value := FlatMatrixFold.foldAll rowQuery (optimizedRows psi lanes coefficient rotations)
  halfPair false *ᵥ value + halfPair true *ᵥ value

theorem evaluate_materialized (psi : ZMod q) (lanes : ℕ)
    (coefficient rowQuery : List (MatrixFold.Pair (F := ZMod q) (Lane := Fin (2^lanes))))
    (halfPair : MatrixFold.Pair (F := ZMod q) (Lane := Fin (2^lanes)))
    (primitive : IsPrimitiveRoot psi (2^(coefficient.length+lanes+1)))
    {rounds : ℕ} (rotations : Fin rounds → Fin (2*(2^(coefficient.length+lanes)))) :
    evaluate psi lanes coefficient rowQuery halfPair rotations =
      halfPair false *ᵥ FlatMatrixFold.foldAll rowQuery (materializedRows psi lanes coefficient rotations false) +
      halfPair true *ᵥ FlatMatrixFold.foldAll rowQuery (materializedRows psi lanes coefficient rotations true) := by
  unfold evaluate
  rw [optimizedRows_eq_materialized psi lanes coefficient primitive rotations false]
  rfl

end
end FormalProof4FHE.HasteBoots.PublicMonomialEvaluation
