module
public import FormalProof4FHE.HasteBoots.PolynomialShapeCost
@[expose] public section

/-! Materialized leading-term cancellation for a future measured division loop.
Every output coefficient is stored. Costs count field/access and structural
operations; coefficient preparation and physical/backend costs are separate. -/
namespace FormalProof4FHE.HasteBoots.DensePolynomialStepCost
open SolverOperationCost Polynomial PolynomialShapeCost
open scoped BigOperators
variable {F : Type} [Field F] [DecidableEq F] {n : ℕ}

def entry (left right : Vector F n) (scale : F) (shift : ℕ) (i : Fin n) : Run F :=
  if before : i.val < shift then ⟨left.get i,2⟩
  else ⟨left.get i - scale * right.get ⟨i.val-shift,by omega⟩,5⟩

def subtractShift (left right : Vector F n) (scale : F) (shift : ℕ) : Run (Vector F n) :=
  tabulate (entry left right scale shift)

omit [DecidableEq F] in
theorem entry_cost (left right : Vector F n) (scale : F) (shift : ℕ) (i : Fin n) :
    (entry left right scale shift i).cost ≤ 5 := by
  unfold entry
  split <;> dsimp only <;> omega

omit [DecidableEq F] in
theorem subtractShift_cost (left right : Vector F n) (scale : F) (shift : ℕ) :
    (subtractShift left right scale shift).cost ≤ 6*n+1 := by
  have bound := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => entry_cost left right scale shift i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at bound
  simp only [subtractShift,tabulate_cost]
  omega

theorem polynomial_coeff_fin (values : Vector F n) (i : Fin n) :
    (polynomial values).coeff i.val = values.get i := by
  simp [polynomial,ExecutablePolynomial.coeff_ofCoefficients,coefficient,Vector.get]

theorem polynomial_coeff_above (values : Vector F n) (i : ℕ) (bound : n ≤ i) :
    (polynomial values).coeff i = 0 := by
  simp only [polynomial,ExecutablePolynomial.coeff_ofCoefficients,not_lt_of_ge bound,ite_false]

theorem subtractShift_get (left right : Vector F n) (scale : F) (shift : ℕ) (i : Fin n) :
    (subtractShift left right scale shift).value.get i =
      left.get i - scale * (if shift ≤ i.val then (polynomial right).coeff (i.val-shift) else 0) := by
  simp only [subtractShift,tabulate_value,FiniteLinearSolver.get_ofFn]
  by_cases before : i.val < shift
  · have after : ¬shift ≤ i.val := by omega
    simp [entry,before,after]
  · have after : shift ≤ i.val := by omega
    simp only [entry,dite_eq_right before,after,ite_true]
    rw [polynomial_coeff_fin right ⟨i.val-shift,by omega⟩]

theorem subtractShift_polynomial (left right : Vector F n) (scale : F) (shift : ℕ)
    (fits : (polynomial right).natDegree+shift < n) :
    polynomial (subtractShift left right scale shift).value =
      polynomial left - C scale * (X^shift * polynomial right) := by
  ext i
  rw [coeff_sub,coeff_C_mul,coeff_X_pow_mul']
  by_cases inside : i < n
  · rw [polynomial_coeff_fin _ ⟨i,inside⟩,subtractShift_get,polynomial_coeff_fin left ⟨i,inside⟩]
  · rw [polynomial_coeff_above _ i (by omega),polynomial_coeff_above left i (by omega)]
    by_cases shifted : shift ≤ i
    · rw [ite_eq_left shifted,coeff_eq_zero_of_natDegree_lt (by omega)]
      simp
    · simp [shifted]

theorem polynomial_natDegree_lt (values : Vector F n) (nonzero : polynomial values ≠ 0) :
    (polynomial values).natDegree < n := by
  have positive : (effectiveLength values).value ≠ 0 := by
    intro zero
    exact nonzero ((polynomial_eq_zero_iff values).mpr zero)
  have bound := effectiveLength_bound values
  rw [polynomial_natDegree]
  omega

def cancel (left right : Vector F n) : Run (Vector F n) :=
  let first := inspect left
  let second := inspect right
  let shift := first.value.1-second.value.1
  let result := subtractShift left right first.value.2 shift
  ⟨result.value,first.cost+second.cost+result.cost+2⟩

theorem cancel_polynomial (left right : Vector F n) (nonzero : polynomial left ≠ 0)
    (order : (polynomial right).degree ≤ (polynomial left).degree) :
    polynomial (cancel left right).value = polynomial left - polynomial right *
      (C (polynomial left).leadingCoeff * X^((polynomial left).natDegree-(polynomial right).natDegree)) := by
  have bounded := polynomial_natDegree_lt left nonzero
  have ordered := natDegree_le_natDegree order
  have fits : (polynomial right).natDegree+((polynomial left).natDegree-(polynomial right).natDegree) < n := by omega
  simp only [cancel,inspect_degree,inspect_leading]
  rw [subtractShift_polynomial left right _ _ fits]
  congr 1
  ring

theorem cancel_degree_lt (left right : Vector F n) (nonzero : polynomial left ≠ 0)
    (order : (polynomial right).degree ≤ (polynomial left).degree) (monic : (polynomial right).Monic) :
    (polynomial (cancel left right).value).degree < (polynomial left).degree := by
  rw [cancel_polynomial left right nonzero order]
  exact div_wf_lemma ⟨order,nonzero⟩ monic

theorem cancel_cost (left right : Vector F n) : (cancel left right).cost ≤ 22*n+15 := by
  have bound := subtractShift_cost left right (inspect left).value.2 ((inspect left).value.1-(inspect right).value.1)
  simp only [cancel,inspect_cost]
  omega
end FormalProof4FHE.HasteBoots.DensePolynomialStepCost
