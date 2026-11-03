module

public import FormalProof4FHE.HasteBoots.NTTRowCheck
public import FormalProof4FHE.HasteBoots.IndexedPublicEquality

@[expose] public section

/-!
# NTT source-query geometry without intermediate commitments

The native query places arbitrary coefficient-compression matrices first and
scalar identity row matrices afterwards. Evaluation equals compressing the
actual tensor-weighted source row. The first coefficient bit remains low in
the source address; row bits are high. No folded-row table is newly committed.
The sum r+c below permits structural recursion on the coefficient front; it
has c front variables followed by r row variables, not a reversed bit order.
-/

open scoped BigOperators
open Matrix
open FormalProof4FHE.HasteBoots.PackedSumcheckSubclaim

namespace FormalProof4FHE.HasteBoots.NTTSourceQuery

noncomputable section

variable {F : Type} [Field F] {b c r : ℕ}

def append : {c r : ℕ} → Query F b c → Query F b r → Query F b (r + c)
  | _, _, .nil, suffix => suffix
  | _, _, .cons pair tail, suffix => .cons pair (append tail suffix)

def join : (c r : ℕ) → MatrixFold.Cube c → MatrixFold.Cube r → MatrixFold.Cube (r + c)
  | 0, _, _, row => row
  | c + 1, r, (bit, coefficient), row => (bit, join c r coefficient row)

omit [Field F] in
theorem append_list (front : Query F b c) (suffix : Query F b r) :
    (append front suffix).toList = front.toList ++ suffix.toList := by
  induction front with
  | nil => rfl
  | cons pair tail ih => simp only [append, Query.toList, ih, List.cons_append]

/-- Native source addresses are coefficient + 2^c * row. -/
theorem join_index (coefficient : MatrixFold.Cube c) (row : MatrixFold.Cube r) :
    (FlatMatrixFold.index (r + c) (join c r coefficient row)).val =
      (FlatMatrixFold.index c coefficient).val + 2 ^ c * (FlatMatrixFold.index r row).val := by
  induction c with
  | zero =>
    cases coefficient
    change (FlatMatrixFold.index r row).val = 0 + 1 * (FlatMatrixFold.index r row).val
    omega
  | succ c ih =>
    rcases coefficient with ⟨bit, coefficient⟩
    change (FlatMatrixFold.index ((r + c) + 1) (bit, join c r coefficient row)).val = _
    rw [FlatMatrixFold.index_succ_val, FlatMatrixFold.index_succ_val, ih]
    simp only [pow_succ]
    ring

/-- Coefficient compression precedes row folding in the complete ordered query. -/
theorem append_fold (front : Query F b c) (suffix : Query F b r)
    (table : MatrixFold.Cube (r + c) → Fin b → F) :
    (append front suffix).fold table =
      suffix.fold (fun row => front.fold (fun coefficient => table (join c r coefficient row))) := by
  induction front with
  | nil => rfl
  | cons pair tail ih =>
    rw [append, Query.fold, ih]
    rfl

def rowQuery : {r : ℕ} → (Fin r → F) → Query F b r
  | 0, _ => .nil
  | _ + 1, point => .cons (fun bit => (if bit then point 0 else 1 - point 0) • (1 : Matrix (Fin b) (Fin b) F))
      (rowQuery (fun index => point index.succ))

/-- The scalar suffix is exactly native tensor-row evaluation. -/
theorem rowQuery_fold (point : Fin r → F) (table : MatrixFold.Cube r → Fin b → F) :
    (rowQuery point).fold table = NTTRowCheck.fold point table := by
  induction r with
  | zero =>
    change table () = ∑ row : Unit, PackedEqualityCube.weight point row • table row
    rw [Fintype.sum_unique]
    rw [PackedEqualityCube.weight_zero (F := F) point ()]
    exact (one_smul F (table ())).symm
  | succ r ih =>
    rw [rowQuery, Query.fold, ih]
    change (∑ suffix : MatrixFold.Cube r,
      PackedEqualityCube.weight (fun index => point index.succ) suffix •
        MatrixFold.foldFirst (fun bit => (if bit then point 0 else 1 - point 0) •
          (1 : Matrix (Fin b) (Fin b) F)) table suffix) =
      ∑ cell : Bool × MatrixFold.Cube r, PackedEqualityCube.weight point cell • table cell
    rw [Fintype.sum_prod_type, Fintype.sum_bool]
    simp only [PackedEqualityCube.weight_succ, Bool.false_eq_true, reduceIte,
      MatrixFold.foldFirst, Fintype.sum_bool, Matrix.smul_mulVec, Matrix.one_mulVec]
    simp only [smul_add, smul_smul, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro row _
    simp only [mul_comm]

/-- Compression is linear even for noncommuting matrix pairs. -/
theorem fold_smul (query : Query F b c) (scalar : F) (table : MatrixFold.Cube c → Fin b → F) :
    query.fold (fun coefficient => scalar • table coefficient) = scalar • query.fold table := by
  simp only [Query.fold_eq_list, MatrixFold.foldAll_eq_weightedEvaluation,
    MatrixFold.weightedEvaluation, Matrix.mulVec_smul, Finset.smul_sum]

/-- Every provided compressed polynomial has exactly the corresponding full
query on its original source. Row proposals require authentication against
these original roots, not against a newly committed folded view. -/
theorem source_evaluation (compression : Query F b c) (point : Fin r → F)
    (table : MatrixFold.Cube (r + c) → Fin b → F) :
    (append compression (rowQuery point)).fold table =
      compression.fold (fun coefficient => ∑ row,
        PackedEqualityCube.weight point row • table (join c r coefficient row)) := by
  rw [append_fold, rowQuery_fold]
  unfold NTTRowCheck.fold
  rw [IndexedPublicEquality.fold_sum]
  apply Finset.sum_congr rfl
  intro row _
  exact (fold_smul compression (PackedEqualityCube.weight point row) _).symm

end

end FormalProof4FHE.HasteBoots.NTTSourceQuery
