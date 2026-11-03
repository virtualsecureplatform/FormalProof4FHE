module

public import FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim
public import FormalProof4FHE.HasteBoots.PackedPublicEquality

@[expose] public section

/-!
# Public EQ evaluation for indexed returned sumcheck queries

The typed query dimension fixes the equality-point dimension independently of
its matrix values. The verifier's ordered column recurrence folds the original
mixed EQ source. This public factor needs no commitment or supplied value.
-/

open scoped BigOperators
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim

namespace FormalProof4FHE.HasteBoots.IndexedPublicEquality

noncomputable section

variable {F Point : Type} [Field F] {k n : ℕ}

def evaluateSingle : {n : ℕ} → Query F k n → (Fin n → F) → (Fin k → F) → Fin k → F
  | _, .nil, _, vector => vector
  | _, .cons pair tail, point, vector =>
    evaluateSingle tail (fun index => point index.succ) (PackedPublicEquality.step pair (point 0) vector)

/-- The inner native recurrence retains first-variable-first matrix order. -/
theorem evaluateSingle_eq_fold (query : Query F k n) (point : Fin n → F) (vector : Fin k → F) :
    evaluateSingle query point vector = query.fold (fun cell => PackedEqualityCube.weight point cell • vector) := by
  induction query generalizing vector with
  | nil =>
    change vector = PackedEqualityCube.weight (n := 0) point () • vector
    simpa only [one_smul] using
      (congrArg (fun scalar : F => scalar • vector) (PackedEqualityCube.weight_zero point ())).symm
  | cons pair tail ih =>
    rw [evaluateSingle, Query.fold, ih]
    apply congrArg tail.fold
    exact (PackedPublicEquality.foldFirst_weight pair point vector).symm

/-- The indexed query preserves linear sums of source vectors. -/
theorem fold_sum [Fintype Point] (query : Query F k n) (tables : Point → MatrixFold.Cube n → Fin k → F) :
    query.fold (fun cell => ∑ point, tables point cell) = ∑ point, query.fold (tables point) := by
  simp only [Query.fold_eq_list]
  exact PackedPublicEquality.foldAll_sum query.toList
    (fun point cell => tables point (query.cubeEquiv.symm cell))

def evaluate [Fintype Point] (query : Query F k n) (points : Point → Fin n → F) (mixing : Fin k → Point → F) : Fin k → F :=
  ∑ point, evaluateSingle query (points point) (fun lane => mixing lane point)

/-- The public EQ terminal equals the actual mixed table's query fold. -/
theorem fold_eq_evaluate [Fintype Point] (query : Query F k n)
    (points : Point → Fin n → F) (mixing : Fin k → Point → F) :
    query.fold (PackedPublicEquality.mixedTable points mixing) = evaluate query points mixing := by
  have tableEq : PackedPublicEquality.mixedTable points mixing = fun cell =>
      ∑ point, PackedEqualityCube.weight (points point) cell • (fun lane => mixing lane point) := by
    funext cell lane
    simp only [PackedPublicEquality.mixedTable, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [tableEq, fold_sum]
  apply Finset.sum_congr rfl
  intro point _
  exact (evaluateSingle_eq_fold query (points point) (fun lane => mixing lane point)).symm

/-- Erasing query indices gives precisely the already-checked native recurrence. -/
theorem evaluateSingle_eq_list (query : Query F k n) (point : Fin n → F) (vector : Fin k → F) :
    evaluateSingle query point vector = PackedPublicEquality.evaluateSingle query.toList
      (fun index => point (Fin.cast query.length_toList index)) vector := by
  induction query generalizing vector with
  | nil => rfl
  | cons pair tail ih =>
    change evaluateSingle tail (fun index => point index.succ) (PackedPublicEquality.step pair (point 0) vector) = _
    rw [ih]
    rfl

end

end FormalProof4FHE.HasteBoots.IndexedPublicEquality
