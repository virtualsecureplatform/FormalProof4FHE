module
public import FormalProof4FHE.HasteBoots.ColumnDistanceCost
@[expose] public section

/-! Scalar mismatch counting from materialized vectors. Each comparison charges
its field loads and equality test; the shared counting loop charges visits,
indicators, additions and index construction. Backend/physical costs are separate. -/
namespace FormalProof4FHE.HasteBoots.ScalarDistanceCost
open SolverOperationCost
open scoped BigOperators
variable {A : Type} [DecidableEq A] {n : ℕ}

def countIndices (test : Fin n → Run Bool) : Run ℕ :=
  let result := ColumnDistanceCost.count test (List.ofFn id)
  ⟨result.value,result.cost+n+1⟩

theorem countIndices_value (test : Fin n → Run Bool) :
    (countIndices test).value = ∑ i : Fin n, if (test i).value then 0 else 1 := by
  simp only [countIndices,ColumnDistanceCost.count_value,List.map_ofFn,Function.comp_def,List.sum_ofFn,id_eq]

theorem countIndices_cost (test : Fin n → Run Bool) (c : ℕ) (cost : ∀ i, (test i).cost = c) :
    (countIndices test).cost = n*(c+4)+2 := by
  have h := ColumnDistanceCost.count_cost test (List.ofFn id) c (fun i _ => cost i)
  simp only [List.length_ofFn] at h
  simp only [countIndices,h]
  ring

def distance (left right : Vector A n) : Run ℕ :=
  countIndices (fun i => ⟨decide (left.get i = right.get i),3⟩)

theorem distance_value (left right : Vector A n) :
    (distance left right).value = hammingDist (fun i => left.get i) (fun i => right.get i) := by
  simp only [distance,countIndices_value]
  have entries (i : Fin n) :
      (if decide (left.get i = right.get i) then 0 else 1) =
        if left.get i ≠ right.get i then 1 else 0 := by
    by_cases h : left.get i = right.get i <;> simp [h]
  simp only [entries,Finset.sum_boole,hammingDist,Nat.cast_id]

theorem distance_cost (left right : Vector A n) : (distance left right).cost = 7*n+2 := by
  rw [distance,countIndices_cost _ 3 (fun _ => rfl)]
  omega

variable [Zero A]

def norm (input : Vector A n) : Run ℕ :=
  countIndices (fun i => ⟨decide (input.get i = 0),2⟩)

theorem norm_value (input : Vector A n) : (norm input).value = hammingNorm (fun i => input.get i) := by
  simp only [norm,countIndices_value]
  have entries (i : Fin n) :
      (if decide (input.get i = 0) then 0 else 1) = if input.get i ≠ 0 then 1 else 0 := by
    by_cases h : input.get i = 0 <;> simp [h]
  simp only [entries,Finset.sum_boole,hammingNorm,Nat.cast_id]

theorem norm_cost (input : Vector A n) : (norm input).cost = 6*n+2 := by
  rw [norm,countIndices_cost _ 2 (fun _ => rfl)]
  omega
end FormalProof4FHE.HasteBoots.ScalarDistanceCost
