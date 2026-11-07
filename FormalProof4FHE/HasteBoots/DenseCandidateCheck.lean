module
public import FormalProof4FHE.HasteBoots.PolynomialShapeCost
public import FormalProof4FHE.HasteBoots.DensePolynomialStepCost
public import FormalProof4FHE.HasteBoots.ScalarDistanceCost
@[expose] public section

/-! Candidate validation on prepared coefficient and input vectors. The remainder
zero test, candidate degree, evaluations and distance scan use measured vector
operations. Polynomial conversion is used only in specifications. Costs are
abstract field/access charges; input preparation and physical refinement are separate. -/
namespace FormalProof4FHE.HasteBoots.DenseCandidateCheck
open SolverOperationCost Polynomial PolynomialShapeCost DensePolynomialStepCost
open scoped BigOperators
variable {F : Type} [Field F] [DecidableEq F] {w n : ℕ}

theorem evaluateMany_get (candidate : Vector F w) (points : Vector F n) (i : Fin n) :
    (PolynomialEvaluationCost.evaluateMany candidate points).value.get i =
      (polynomial candidate).eval (points.get i) := by
  by_cases empty : w = 0
  · subst w
    have zero : polynomial candidate = 0 := by
      ext j
      rw [polynomial_coeff_above _ j (by omega),coeff_zero]
    simp [PolynomialEvaluationCost.evaluateMany_get,zero]
  · have bound : (polynomial candidate).natDegree < w := by
      rw [polynomial_natDegree]
      have stored := effectiveLength_bound candidate
      omega
    rw [PolynomialEvaluationCost.evaluateMany_get]
    calc
      _ = ∑ j : Fin w, (polynomial candidate).coeff j.val * (points.get i)^j.val := by
        apply Finset.sum_congr rfl
        intro j _
        rw [polynomial_coeff_fin]
      _ = ∑ j ∈ Finset.range w, (polynomial candidate).coeff j * (points.get i)^j :=
        Fin.sum_univ_eq_sum_range (fun j => (polynomial candidate).coeff j * (points.get i)^j) w
      _ = (polynomial candidate).eval (points.get i) := (Polynomial.eval_eq_sum_range' bound _).symm

def check (e k : ℕ) (candidate remainder : Vector F w) (points received : Vector F n) : Run Bool :=
  let residual := inspect remainder
  if residual.value.2 = 0 then
    let metadata := inspect candidate
    if metadata.value.1 < k then
      let evaluations := PolynomialEvaluationCost.evaluateMany candidate points
      let distance := ScalarDistanceCost.distance received evaluations.value
      ⟨decide (distance.value ≤ e),residual.cost+metadata.cost+evaluations.cost+distance.cost+8⟩
    else ⟨false,residual.cost+metadata.cost+5⟩
  else ⟨false,residual.cost+3⟩

theorem check_value (e k : ℕ) (candidate remainder : Vector F w) (points received : Vector F n) :
    (check e k candidate remainder points received).value =
      decide (polynomial remainder = 0 ∧ (polynomial candidate).natDegree < k ∧
        hammingDist (fun i => received.get i) (fun i => (polynomial candidate).eval (points.get i)) ≤ e) := by
  have evaluated : (fun i => (PolynomialEvaluationCost.evaluateMany candidate points).value.get i) =
      (fun i => (polynomial candidate).eval (points.get i)) := by
    funext i
    exact evaluateMany_get candidate points i
  simp only [check,inspect_leading,leadingCoeff_eq_zero,inspect_degree,ScalarDistanceCost.distance_value,evaluated]
  split_ifs <;> simp_all

theorem check_cost (e k : ℕ) (candidate remainder : Vector F w) (points received : Vector F n) :
    (check e k candidate remainder points received).cost ≤ n*(7*w+12)+16*w+23 := by
  unfold check
  dsimp only
  split_ifs <;> simp only [inspect_cost,PolynomialEvaluationCost.evaluateMany_cost,ScalarDistanceCost.distance_cost] <;> nlinarith
end FormalProof4FHE.HasteBoots.DenseCandidateCheck
