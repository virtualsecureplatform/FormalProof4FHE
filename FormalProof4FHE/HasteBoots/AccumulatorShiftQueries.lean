module
public import FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim
@[expose] public section

/-! Exact ordered matrix weights of packed_accumulator::shift_queries.
Carry branches select the first set bit of the source row; a separate wrap
branch selects row zero. Matrix factors retain their native multiplication
order. Native query construction and acceptance are separate refinements. -/
namespace FormalProof4FHE.HasteBoots.AccumulatorShiftQueries
open scoped BigOperators
open Matrix
open PackedSumcheckSubclaim (Query)
noncomputable section
variable {F : Type} [Field F] {k n : ℕ}
local instance (n : ℕ) : DecidableEq (MatrixFold.Cube n) := Classical.decEq _

def zero : (n : ℕ) → MatrixFold.Cube n
  | 0 => ()
  | n+1 => (false,zero n)

theorem zero_dim (cell : MatrixFold.Cube 0) : cell = zero 0 :=
  Subsingleton.elim (α := Unit) _ _

theorem zero_cons_eq (bit : Bool) (tail : MatrixFold.Cube n) :
    (show MatrixFold.Cube (n+1) from (bit,tail)) = zero (n+1) ↔ bit = false ∧ tail = zero n := by
  exact Iff.of_eq (Prod.mk.injEq bit tail false (zero n))

def predecessor : {n : ℕ} → MatrixFold.Cube n → MatrixFold.Cube n
  | 0, _ => ()
  | _+1, (bit,tail) => if bit then (false,tail) else (true,predecessor tail)

def weight : {n : ℕ} → Query F k n → MatrixFold.Cube n → Matrix (Fin k) (Fin k) F
  | _, .nil, _ => 1
  | _, .cons pair tail, (bit,suffix) => weight tail suffix * pair bit

def selector (bit : Bool) (matrix : Matrix (Fin k) (Fin k) F) : MatrixFold.Pair (F := F) (Lane := Fin k) :=
  fun choice => if choice = bit then matrix else 0

def zeros : (n : ℕ) → Query F k n
  | 0 => .nil
  | n+1 => .cons (selector false 1) (zeros n)

/-- The native low-weight accumulator multiplies each one-matrix on the left. -/
def ones : {n : ℕ} → Query F k n → Matrix (Fin k) (Fin k) F → Matrix (Fin k) (Fin k) F
  | _, .nil, low => low
  | _, .cons pair tail, low => ones tail (pair true * low)

/-- Non-wrap branches in increasing first-set-bit order. -/
def carries : {n : ℕ} → Query F k n → Matrix (Fin k) (Fin k) F → List (Query F k n)
  | _, .nil, _ => []
  | _, .cons pair tail, low =>
      .cons (selector true (pair false * low)) tail ::
        (carries tail (pair true * low)).map (.cons (selector false 1))

/-- The wrap query places the complete low product at the first zero selector. -/
def wrap : {n : ℕ} → Query F k n → Matrix (Fin k) (Fin k) F → Query F k n
  | _, .nil, _ => .nil
  | _, query@(.cons _ _), low => .cons (selector false (ones query low)) (zeros _)

def shifted : {n : ℕ} → Query F k n → List (Query F k n)
  | _, .nil => [.nil]
  | _, query@(.cons _ _) => carries query 1 ++ [wrap query 1]

theorem weight_zeros (cell : MatrixFold.Cube n) :
    weight (zeros n : Query F k n) cell = if cell = zero n then 1 else 0 := by
  induction n with
  | zero => simp [zeros, weight, zero_dim]
  | succ n ih =>
    rcases cell with ⟨bit,tail⟩
    cases bit <;> simp [zeros, weight, selector, zero_cons_eq, ih]

theorem ones_predecessor (query : Query F k n) (low : Matrix (Fin k) (Fin k) F) :
    ones query low = weight query (predecessor (zero n)) * low := by
  induction query generalizing low with
  | nil => simp [ones, weight]
  | cons pair tail ih =>
    simp [ones, zero, predecessor, weight, ih, mul_assoc]

theorem carries_weight (query : Query F k n) (low : Matrix (Fin k) (Fin k) F) (cell : MatrixFold.Cube n) :
    ((carries query low).map (fun branch => weight branch cell)).sum =
      if cell = zero n then 0 else weight query (predecessor cell) * low := by
  induction query generalizing low with
  | nil => simp [carries, zero_dim]
  | cons pair tail ih =>
    rcases cell with ⟨bit,suffix⟩
    cases bit
    · by_cases empty : suffix = zero _
      · simp [carries, List.map_map, Function.comp_def, weight, selector, ih, empty, zero_cons_eq]
      · simp [carries, List.map_map, Function.comp_def, weight, selector, ih, empty, zero_cons_eq, predecessor, mul_assoc]
    · simp [carries, List.map_map, Function.comp_def, weight, selector, zero_cons_eq, predecessor, mul_assoc]

theorem wrap_weight (pair : MatrixFold.Pair (F := F) (Lane := Fin k)) (tail : Query F k n)
    (low : Matrix (Fin k) (Fin k) F) (cell : MatrixFold.Cube (n+1)) :
    weight (wrap (.cons pair tail) low) cell =
      if cell = zero (n+1) then ones (.cons pair tail) low else 0 := by
  rcases cell with ⟨bit,suffix⟩
  cases bit <;> simp [wrap, weight, selector, weight_zeros, zero_cons_eq]

theorem shifted_weight (query : Query F k n) (cell : MatrixFold.Cube n) :
    ((shifted query).map (fun branch => weight branch cell)).sum = weight query (predecessor cell) := by
  cases query with
  | nil => cases cell; simp [shifted, weight]
  | cons pair tail =>
    simp only [shifted, List.map_append, List.map_cons, List.map_nil, List.sum_append]
    simp only [List.sum_cons, List.sum_nil, add_zero]
    rw [carries_weight, wrap_weight, ones_predecessor]
    by_cases empty : cell = zero _
    · simp [empty]
    · simp [empty]


def successor : {n : ℕ} → MatrixFold.Cube n → MatrixFold.Cube n
  | 0, _ => ()
  | _+1, (bit,tail) => if bit then (false,successor tail) else (true,tail)

theorem predecessor_successor (cell : MatrixFold.Cube n) : predecessor (successor cell) = cell := by
  induction n with
  | zero => exact Subsingleton.elim (α := Unit) _ _
  | succ n ih =>
    rcases cell with ⟨bit,tail⟩
    cases bit <;> simp [successor, predecessor, ih] <;> rfl

theorem successor_predecessor (cell : MatrixFold.Cube n) : successor (predecessor cell) = cell := by
  induction n with
  | zero => exact Subsingleton.elim (α := Unit) _ _
  | succ n ih =>
    rcases cell with ⟨bit,tail⟩
    cases bit <;> simp [successor, predecessor, ih] <;> rfl

def rowEquiv (n : ℕ) : MatrixFold.Cube n ≃ MatrixFold.Cube n where
  toFun := successor
  invFun := predecessor
  left_inv := predecessor_successor
  right_inv := successor_predecessor

theorem carries_length (query : Query F k n) (low : Matrix (Fin k) (Fin k) F) :
    (carries query low).length = n := by
  induction query generalizing low with
  | nil => rfl
  | cons pair tail ih => simp [carries, ih]

theorem shifted_length (query : Query F k n) : (shifted query).length = n+1 := by
  cases query with
  | nil => rfl
  | cons pair tail => simp [shifted, carries_length]

theorem weight_eq_list (query : Query F k n) (cell : MatrixFold.Cube n) :
    weight query cell = MatrixFold.weight query.toList (query.cubeEquiv cell) := by
  induction query with
  | nil => rfl
  | cons pair tail ih =>
    rcases cell with ⟨bit,suffix⟩
    exact congrArg (· * pair bit) (ih suffix)

theorem fold_eq_weighted (query : Query F k n) (table : MatrixFold.Cube n → Fin k → F) :
    query.fold table = ∑ cell, weight query cell *ᵥ table cell := by
  rw [query.fold_eq_list, MatrixFold.foldAll_eq_weightedEvaluation]
  unfold MatrixFold.weightedEvaluation
  rw [← query.cubeEquiv.sum_comp]
  simp only [Equiv.symm_apply_apply, ← weight_eq_list]

theorem sum_fold_weighted (branches : List (Query F k n)) (table : MatrixFold.Cube n → Fin k → F) :
    (branches.map (fun branch => branch.fold table)).sum =
      ∑ cell, (branches.map (fun branch => weight branch cell)).sum *ᵥ table cell := by
  induction branches with
  | nil => simp
  | cons branch rest ih =>
    rw [List.map_cons, List.sum_cons, ih]
    simp only [List.map_cons, List.sum_cons, Matrix.add_mulVec, Finset.sum_add_distrib, fold_eq_weighted]

/-- Summing every native branch evaluates the original input table at r=t+1
modulo the row domain, with no commutation of matrix factors. -/
theorem shifted_fold (query : Query F k n) (table : MatrixFold.Cube n → Fin k → F) :
    ((shifted query).map (fun branch => branch.fold table)).sum =
      query.fold (fun row => table (successor row)) := by
  rw [sum_fold_weighted, fold_eq_weighted]
  simp only [shifted_weight]
  rw [← (rowEquiv n).sum_comp (fun cell => weight query (predecessor cell) *ᵥ table cell)]
  simp only [rowEquiv, Equiv.coe_fn_mk, predecessor_successor]

theorem successor_index (cell : MatrixFold.Cube n) :
    (FlatMatrixFold.index n (successor cell)).val = ((FlatMatrixFold.index n cell).val+1)%(2^n) := by
  induction n with
  | zero => cases cell; rfl
  | succ n ih =>
    rcases cell with ⟨bit,tail⟩
    cases bit
    · change (FlatMatrixFold.index (n+1) (true,tail)).val =
        ((FlatMatrixFold.index (n+1) (false,tail)).val+1)%(2^(n+1))
      rw [FlatMatrixFold.index_succ_val, FlatMatrixFold.index_succ_val]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      have bound : 2*(FlatMatrixFold.index n tail).val+1 < 2^(n+1) := by
        have := (FlatMatrixFold.index n tail).isLt
        rw [pow_succ]
        omega
      exact (Nat.mod_eq_of_lt bound).symm
    · change (FlatMatrixFold.index (n+1) (false,successor tail)).val =
        ((FlatMatrixFold.index (n+1) (true,tail)).val+1)%(2^(n+1))
      rw [FlatMatrixFold.index_succ_val, FlatMatrixFold.index_succ_val, ih]
      simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      rw [show 2*(FlatMatrixFold.index n tail).val+1+1 = 2*((FlatMatrixFold.index n tail).val+1) by omega,
        show 2^(n+1) = 2*2^n by rw [pow_succ]; omega, Nat.mul_mod_mul_left]

/-- Original flat row addresses, including the wrap to row zero. -/
theorem shifted_fold_flat (query : Query F k n) (table : Fin (2^n) → Fin k → F) :
    ((shifted query).map (fun branch => branch.fold (fun cell => table (FlatMatrixFold.index n cell)))).sum =
      query.fold (fun cell => table ⟨((FlatMatrixFold.index n cell).val+1)%(2^n),Nat.mod_lt _ (by positivity)⟩) := by
  rw [shifted_fold]
  apply congrArg query.fold
  funext cell
  apply congrArg table
  exact Fin.ext (successor_index cell)

/-- Native select_row replaces each row pair with an identity selector. -/
def selected : {n : ℕ} → MatrixFold.Cube n → Query F k n
  | 0, _ => .nil
  | _+1, (bit,tail) => .cons (selector bit 1) (selected tail)

theorem selected_fold (target : MatrixFold.Cube n) (table : MatrixFold.Cube n → Fin k → F) :
    (selected target : Query F k n).fold table = table target := by
  induction n with
  | zero => cases target; rfl
  | succ n ih =>
    rcases target with ⟨bit,tail⟩
    change (selected tail : Query F k n).fold (MatrixFold.foldFirst (selector bit 1) table) = table (bit,tail)
    rw [ih]
    cases bit <;> simp [MatrixFold.foldFirst, selector]

end
end FormalProof4FHE.HasteBoots.AccumulatorShiftQueries
