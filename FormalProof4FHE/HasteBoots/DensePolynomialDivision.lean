module
public import FormalProof4FHE.HasteBoots.DenseMonicDivision
@[expose] public section

/-! General measured division from prepared fixed-width coefficient vectors.
A nonzero divisor is scaled to monic form, the verified loop runs once, and
its quotient is rescaled. A zero divisor returns zero quotient and unchanged
remainder. Costs use the abstract field/access model, excluding input preparation
and backend/physical execution. -/
namespace FormalProof4FHE.HasteBoots.DensePolynomialDivision
open SolverOperationCost Polynomial PolynomialShapeCost DensePolynomialStepCost
open scoped BigOperators
variable {F : Type} [Field F] [DecidableEq F] {n : ℕ}

def scale (values : Vector F n) (scalar : F) : Run (Vector F n) :=
  tabulate (fun i : Fin n => multiply (SolverOperationCost.pure scalar) (load (values.get i)))

omit [DecidableEq F] in
theorem scale_cost (values : Vector F n) (scalar : F) : (scale values scalar).cost = 3*n+1 := by
  simp only [scale,tabulate_cost,multiply,SolverOperationCost.pure,load,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  omega

theorem scale_polynomial (values : Vector F n) (scalar : F) :
    polynomial (scale values scalar).value = polynomial values * C scalar := by
  ext i
  rw [coeff_mul_C]
  by_cases inside : i < n
  · rw [polynomial_coeff_fin _ ⟨i,inside⟩,polynomial_coeff_fin values ⟨i,inside⟩]
    simp only [scale,tabulate_value,FiniteLinearSolver.get_ofFn,multiply,SolverOperationCost.pure,load]
    exact mul_comm _ _
  · rw [polynomial_coeff_above _ i (by omega),polynomial_coeff_above values i (by omega),zero_mul]

theorem normalized_monic (right : Vector F n) (nonzero : (inspect right).value.2 ≠ 0) :
    (polynomial (scale right ((inspect right).value.2)⁻¹).value).Monic := by
  rw [scale_polynomial,inspect_leading]
  apply monic_mul_leadingCoeff_inv
  intro vanished
  exact nonzero (by simp only [inspect_leading,vanished,leadingCoeff_zero])

def divMod (left right : Vector F n) : Run (Vector F n × Vector F n) :=
  let metadata := inspect right
  if zero : metadata.value.2 = 0 then
    let empty := DenseMonicDivision.zeroVector (F := F) (n := n)
    ⟨(empty.value,left),metadata.cost+empty.cost+5⟩
  else
    let inverse := invert (SolverOperationCost.pure metadata.value.2)
    let normalized := scale right inverse.value
    have monic : (polynomial normalized.value).Monic := normalized_monic right zero
    let result := DenseMonicDivision.divide normalized.value monic left
    let quotient := scale result.value.1 inverse.value
    ⟨(quotient.value,result.value.2),metadata.cost+inverse.cost+normalized.cost+result.cost+quotient.cost+10⟩

theorem divMod_fst_eq (left right : Vector F n) :
    polynomial (divMod left right).value.1 = polynomial left / polynomial right := by
  rw [divMod]
  by_cases zero : (inspect right).value.2 = 0
  · rw [dite_eq_left zero]
    have vanished : polynomial right = 0 := leadingCoeff_eq_zero.mp (by simpa only [inspect_leading] using zero)
    simp only [DenseMonicDivision.zeroVector_polynomial,vanished,EuclideanDomain.div_zero]
  · rw [dite_eq_right zero]
    simp only [scale_polynomial,DenseMonicDivision.divide_fst_eq,invert,SolverOperationCost.pure,inspect_leading,Polynomial.div_def]
    exact mul_comm _ _

theorem divMod_snd_eq (left right : Vector F n) :
    polynomial (divMod left right).value.2 = polynomial left % polynomial right := by
  rw [divMod]
  by_cases zero : (inspect right).value.2 = 0
  · rw [dite_eq_left zero]
    have vanished : polynomial right = 0 := leadingCoeff_eq_zero.mp (by simpa only [inspect_leading] using zero)
    simp only [vanished,EuclideanDomain.mod_zero]
  · rw [dite_eq_right zero]
    simp only [DenseMonicDivision.divide_snd_eq,scale_polynomial,invert,SolverOperationCost.pure,inspect_leading,Polynomial.mod_def]

theorem divMod_eq (left right : Vector F n) :
    (polynomial (divMod left right).value.1,polynomial (divMod left right).value.2) =
      (polynomial left / polynomial right,polynomial left % polynomial right) :=
  Prod.ext (divMod_fst_eq left right) (divMod_snd_eq left right)

theorem divMod_reconstruct (left right : Vector F n) :
    polynomial right * polynomial (divMod left right).value.1 +
      polynomial (divMod left right).value.2 = polynomial left := by
  rw [divMod_fst_eq,divMod_snd_eq]
  exact EuclideanDomain.div_add_mod _ _

theorem divMod_remainder_degree (left right : Vector F n) (nonzero : polynomial right ≠ 0) :
    (polynomial (divMod left right).value.2).degree < (polynomial right).degree := by
  rw [divMod_snd_eq]
  exact Polynomial.degree_mod_lt _ nonzero

theorem divMod_cost (left right : Vector F n) :
    (divMod left right).cost ≤ 50*(n+1)^2+14*n+19 := by
  rw [divMod]
  split_ifs with zero
  · simp only [inspect_cost,DenseMonicDivision.zeroVector_cost]
    omega
  · have bound := DenseMonicDivision.divide_cost
      (scale right ((inspect right).value.2)⁻¹).value (normalized_monic right zero) left
    simp only [inspect_cost,invert,SolverOperationCost.pure,scale_cost]
    omega
end FormalProof4FHE.HasteBoots.DensePolynomialDivision
