module
public import FormalProof4FHE.HasteBoots.SolverOperationErasure
@[expose] public section

/-! Horner evaluation from a prepared coefficient vector in ascending order.
Charges use the abstract field/access model. Each recursive step charges a
coefficient load, multiplication, addition, list visit and tail access. Conversion
from vector to list charges a load/store per element and initialization. Input
coefficient preparation, degree discovery and backend/physical costs are separate. -/
namespace FormalProof4FHE.HasteBoots.PolynomialEvaluationCost
open SolverOperationCost
open scoped BigOperators
variable {F : Type} [Field F]

def horner (point : F) : List F → Run F
  | [] => ⟨0,1⟩
  | coefficient :: rest =>
    let tail := horner point rest
    ⟨coefficient+point*tail.value,tail.cost+5⟩

theorem horner_cost (point : F) (coefficients : List F) :
    (horner point coefficients).cost = 5*coefficients.length+1 := by
  induction coefficients with
  | nil => rfl
  | cons head rest ih => simp only [horner,List.length_cons,ih]; omega

theorem horner_ofFn (point : F) (length : ℕ) (coefficients : Fin length → F) :
    (horner point (List.ofFn coefficients)).value = ∑ i : Fin length, coefficients i * point^i.val := by
  induction length with
  | zero => simp [horner]
  | succ length ih =>
    simp only [List.ofFn_succ,horner,ih,Fin.sum_univ_succ,Fin.val_zero,pow_zero,mul_one,Fin.val_succ,pow_succ]
    rw [Finset.mul_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    ring

def evaluate {length : ℕ} (coefficients : Vector F length) (point : F) : Run F :=
  let result := horner point coefficients.toList
  ⟨result.value,result.cost+2*length+2⟩

theorem evaluate_value {length : ℕ} (coefficients : Vector F length) (point : F) :
    (evaluate coefficients point).value = ∑ i : Fin length, coefficients.get i * point^i.val := by
  have stored : coefficients.toList = List.ofFn (fun i => coefficients.get i) := by
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      simp [Vector.get]
  simp only [evaluate,stored,horner_ofFn]

theorem evaluate_cost {length : ℕ} (coefficients : Vector F length) (point : F) :
    (evaluate coefficients point).cost = 7*length+3 := by
  simp only [evaluate,horner_cost,Vector.length_toList]
  omega
/-- Reuse one prepared coefficient vector for every evaluation point. -/
def evaluateMany {length n : ℕ} (coefficients : Vector F length) (points : Vector F n) : Run (Vector F n) :=
  tabulate (fun i : Fin n =>
    let point := load (points.get i)
    let result := evaluate coefficients point.value
    ⟨result.value,point.cost+result.cost⟩)

theorem evaluateMany_get {length n : ℕ} (coefficients : Vector F length) (points : Vector F n) (i : Fin n) :
    (evaluateMany coefficients points).value.get i = ∑ j : Fin length, coefficients.get j * (points.get i)^j.val := by
  simp only [evaluateMany,tabulate_value,FiniteLinearSolver.get_ofFn,load,evaluate_value]

theorem evaluateMany_cost {length n : ℕ} (coefficients : Vector F length) (points : Vector F n) :
    (evaluateMany coefficients points).cost = n*(7*length+5)+1 := by
  simp only [evaluateMany,tabulate_cost,load,evaluate_cost,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring
end FormalProof4FHE.HasteBoots.PolynomialEvaluationCost
