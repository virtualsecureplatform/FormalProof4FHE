module

public import FormalProof4FHE.HasteBoots.NativeEqualityTable

@[expose] public section

/-!
# Public equality evaluation equals folding the mixed equality source

The verifier starts from each mixing-matrix column, applies the zero and one
query matrices in native order with scalar equality weights, and adds the
resulting vectors. This equals the full matrix fold of `mixed_equality`.
Consequently the verifier's public EQ terminal is fixed by its point/mixing
coins and query; it is not a prover-chosen factor value.

Theorems cover typed field and matrix operations, including zero rounds and
noncommuting matrices. Rust memory and field implementation refinement remain
separate obligations.
-/

open scoped BigOperators
open Matrix

namespace FormalProof4FHE.HasteBoots.PackedPublicEquality

noncomputable section

variable {F Lane Point : Type} [Field F] [Fintype Lane] [DecidableEq Lane]

def step (pair : MatrixFold.Pair (F := F) (Lane := Lane)) (point : F) (vector : Lane → F) : Lane → F :=
  (1 - point) • (pair false *ᵥ vector) + point • (pair true *ᵥ vector)

/-- The native inner loop updates one mixing column in query order. -/
def evaluateSingle : (query : List (MatrixFold.Pair (F := F) (Lane := Lane))) →
    (Fin query.length → F) → (Lane → F) → Lane → F
  | [], _, vector => vector
  | pair :: tail, point, vector =>
    evaluateSingle tail (fun index => point index.succ) (step pair (point 0) vector)

omit [DecidableEq Lane] in
theorem foldFirst_weight (pair : MatrixFold.Pair (F := F) (Lane := Lane)) {n : ℕ}
    (point : Fin (n + 1) → F) (vector : Lane → F) :
    MatrixFold.foldFirst pair (fun cell => PackedEqualityCube.weight point cell • vector) =
      fun suffix => PackedEqualityCube.weight (fun index => point index.succ) suffix • step pair (point 0) vector := by
  funext suffix
  simp only [MatrixFold.foldFirst, Fintype.sum_bool, PackedEqualityCube.weight_succ,
    Bool.false_eq_true, reduceIte, Matrix.mulVec_smul, step, smul_add, smul_smul, mul_comm, add_comm]

omit [DecidableEq Lane] in
/-- One native column recurrence evaluates exactly its equality-weighted
source vector under the complete ordered matrix query. -/
theorem evaluateSingle_eq_fold (query : List (MatrixFold.Pair (F := F) (Lane := Lane)))
    (point : Fin query.length → F) (vector : Lane → F) :
    evaluateSingle query point vector =
      MatrixFold.foldAll query (fun cell => PackedEqualityCube.weight point cell • vector) := by
  induction query generalizing vector with
  | nil =>
    change vector = PackedEqualityCube.weight (n := 0) point () • vector
    simpa only [one_smul] using
      (congrArg (fun scalar : F => scalar • vector) (PackedEqualityCube.weight_zero point ())).symm
  | cons pair tail ih =>
    rw [evaluateSingle, MatrixFold.foldAll, ih]
    apply congrArg (MatrixFold.foldAll tail)
    exact (foldFirst_weight pair point vector).symm

/-- Folding preserves a sum of source tables without changing query order. -/
theorem foldAll_sum [Fintype Point] (query : List (MatrixFold.Pair (F := F) (Lane := Lane)))
    (tables : Point → MatrixFold.Cube query.length → Lane → F) :
    MatrixFold.foldAll query (fun cell => ∑ point, tables point cell) =
      ∑ point, MatrixFold.foldAll query (tables point) := by
  simp only [MatrixFold.foldAll_eq_weightedEvaluation, MatrixFold.weightedEvaluation, Matrix.mulVec_sum]
  exact Finset.sum_comm

def mixedTable [Fintype Point] {n : ℕ} (points : Point → Fin n → F) (mixing : Lane → Point → F) :
    MatrixFold.Cube n → Lane → F :=
  fun cell lane => ∑ point, mixing lane point * PackedEqualityCube.weight (points point) cell

/-- The native outer loop adds the evaluated mixing-matrix columns. -/
def evaluatePublic [Fintype Point] (query : List (MatrixFold.Pair (F := F) (Lane := Lane)))
    (points : Point → Fin query.length → F) (mixing : Lane → Point → F) : Lane → F :=
  ∑ point, evaluateSingle query (points point) (fun lane => mixing lane point)

/-- The public value is exactly the terminal of the original mixed EQ table. -/
theorem fold_eq_evaluatePublic [Fintype Point] (query : List (MatrixFold.Pair (F := F) (Lane := Lane)))
    (points : Point → Fin query.length → F) (mixing : Lane → Point → F) :
    MatrixFold.foldAll query (mixedTable points mixing) = evaluatePublic query points mixing := by
  have tableEq : mixedTable points mixing = fun cell =>
      ∑ point, PackedEqualityCube.weight (points point) cell • (fun lane => mixing lane point) := by
    funext cell lane
    simp only [mixedTable, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [tableEq, foldAll_sum]
  apply Finset.sum_congr rfl
  intro point _
  exact (evaluateSingle_eq_fold query (points point) (fun lane => mixing lane point)).symm

/-- Same equality source at the native low-bit flat addresses. -/
def flatMixedTable [Fintype Point] {n : ℕ} (points : Point → Fin n → F) (mixing : Lane → Point → F) :
    Fin (2 ^ n) → Lane → F :=
  fun position => mixedTable points mixing ((FlatMatrixFold.index n).symm position)

theorem flat_fold_eq_evaluatePublic [Fintype Point] (query : List (MatrixFold.Pair (F := F) (Lane := Lane)))
    (points : Point → Fin query.length → F) (mixing : Lane → Point → F) :
    FlatMatrixFold.foldAll query (flatMixedTable points mixing) = evaluatePublic query points mixing := by
  rw [FlatMatrixFold.foldAll_eq_cube]
  simpa only [flatMixedTable, Equiv.symm_apply_apply] using fold_eq_evaluatePublic query points mixing

/-- The original native mixed table uses the actual two-block EQ construction. -/
def nativeMixedTable [Fintype Point] {n : ℕ} (points : Point → Fin n → F) (mixing : Lane → Point → F) :
    Fin (2 ^ n) → Lane → F :=
  fun position lane => ∑ point, mixing lane point * NativeEqualityTable.table n (points point) position

omit [Fintype Lane] [DecidableEq Lane] in
theorem nativeMixedTable_eq_flat [Fintype Point] {n : ℕ}
    (points : Point → Fin n → F) (mixing : Lane → Point → F) :
    nativeMixedTable points mixing = flatMixedTable points mixing := by
  funext position lane
  apply Finset.sum_congr rfl
  intro point _
  congr 1
  simpa only [Equiv.apply_symm_apply] using NativeEqualityTable.table_index n (points point)
    ((FlatMatrixFold.index n).symm position)

/-- The complete verifier recurrence equals folding the native constructed
mixed table; there is no separate unverified public-EQ terminal assumption. -/
theorem native_fold_eq_evaluatePublic [Fintype Point]
    (query : List (MatrixFold.Pair (F := F) (Lane := Lane)))
    (points : Point → Fin query.length → F) (mixing : Lane → Point → F) :
    FlatMatrixFold.foldAll query (nativeMixedTable points mixing) = evaluatePublic query points mixing := by
  rw [nativeMixedTable_eq_flat]
  exact flat_fold_eq_evaluatePublic query points mixing

end

end FormalProof4FHE.HasteBoots.PackedPublicEquality
