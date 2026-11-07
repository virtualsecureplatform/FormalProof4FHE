module
public import FormalProof4FHE.HasteBoots.DensePolynomialStepCost
public import FormalProof4FHE.HasteBoots.ExecutablePolynomialDivisionAux
@[expose] public section
namespace FormalProof4FHE.HasteBoots.DenseMonicDivision
open SolverOperationCost Polynomial PolynomialShapeCost DensePolynomialStepCost
open scoped BigOperators
variable {F : Type} [Field F] [DecidableEq F] {n : ℕ}

def addTerm (values : Vector F n) (scale : F) (shift : ℕ) : Run (Vector F n) :=
  tabulate (fun i : Fin n => if i.val = shift then ⟨values.get i+scale,3⟩ else ⟨values.get i,2⟩)

omit [DecidableEq F] in
theorem addTerm_cost (values : Vector F n) (scale : F) (shift : ℕ) :
    (addTerm values scale shift).cost ≤ 4*n+1 := by
  have entry (i : Fin n) : (if i.val = shift then (⟨values.get i+scale,3⟩ : Run F) else ⟨values.get i,2⟩).cost ≤ 3 := by
    split <;> dsimp only <;> omega
  have bound := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => entry i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at bound
  simp only [addTerm,tabulate_cost]
  omega

theorem addTerm_polynomial (values : Vector F n) (scale : F) (shift : ℕ) (fits : shift < n) :
    polynomial (addTerm values scale shift).value = polynomial values + C scale * X^shift := by
  ext i
  rw [coeff_add,coeff_C_mul_X_pow]
  by_cases inside : i < n
  · rw [polynomial_coeff_fin _ ⟨i,inside⟩,polynomial_coeff_fin values ⟨i,inside⟩]
    simp only [addTerm,tabulate_value,FiniteLinearSolver.get_ofFn]
    split_ifs <;> simp_all
  · rw [polynomial_coeff_above _ i (by omega),polynomial_coeff_above values i (by omega)]
    simp [show i ≠ shift by omega]

theorem active_iff (left right : Vector F n) (monic : (polynomial right).Monic) :
    ((inspect left).value.2 ≠ 0 ∧ (inspect right).value.1 ≤ (inspect left).value.1) ↔
      polynomial left ≠ 0 ∧ (polynomial right).degree ≤ (polynomial left).degree := by
  simp only [inspect_leading,inspect_degree,ne_eq,leadingCoeff_eq_zero]
  constructor
  · rintro ⟨nonzero,order⟩
    refine ⟨nonzero,?_⟩
    rw [degree_eq_natDegree monic.ne_zero,degree_eq_natDegree nonzero]
    exact_mod_cast order
  · rintro ⟨nonzero,order⟩
    exact ⟨nonzero,natDegree_le_natDegree order⟩

theorem effectiveLength_lt_of_degree_lt (left right : Vector F n)
    (smaller : (polynomial left).degree < (polynomial right).degree) :
    (effectiveLength left).value < (effectiveLength right).value := by
  have rightNonzero : polynomial right ≠ 0 := by
    intro zero
    simp [zero] at smaller
  have rightPositive : (effectiveLength right).value ≠ 0 := by
    intro zero
    exact rightNonzero ((polynomial_eq_zero_iff right).mpr zero)
  by_cases leftZero : polynomial left = 0
  · have zero := (polynomial_eq_zero_iff left).mp leftZero
    omega
  · rw [degree_eq_natDegree leftZero,degree_eq_natDegree rightNonzero] at smaller
    have degrees : (polynomial left).natDegree < (polynomial right).natDegree := by exact_mod_cast smaller
    rw [polynomial_natDegree,polynomial_natDegree] at degrees
    omega

def zeroVector : Run (Vector F n) := tabulate (fun _ => (SolverOperationCost.pure 0))

omit [DecidableEq F] in
theorem zeroVector_cost : (zeroVector : Run (Vector F n)).cost = n+1 := by
  simp only [zeroVector,tabulate_cost,SolverOperationCost.pure,Finset.sum_const_zero,Nat.zero_add]

theorem zeroVector_polynomial : polynomial (zeroVector : Run (Vector F n)).value = 0 := by
  ext i
  by_cases inside : i < n
  · rw [polynomial_coeff_fin _ ⟨i,inside⟩]
    simp only [zeroVector,tabulate_value,FiniteLinearSolver.get_ofFn,SolverOperationCost.pure,coeff_zero]
  · rw [polynomial_coeff_above _ i (by omega),coeff_zero]

/-- Measured monic long division. Each branch reserves ten structural/control
units in addition to metadata, cancellation, recursion and quotient stores.
Inputs are prepared coefficient vectors; field backend and physical costs are separate. -/
def divide (right : Vector F n) (monic : (polynomial right).Monic) (left : Vector F n) :
    Run (Vector F n × Vector F n) :=
  let first := inspect left
  let second := inspect right
  if active : first.value.2 ≠ 0 ∧ second.value.1 ≤ first.value.1 then
    have valid := (active_iff left right monic).mp active
    let reduced := cancel left right
    have smaller := effectiveLength_lt_of_degree_lt reduced.value left
      (cancel_degree_lt left right valid.1 valid.2 monic)
    let result := divide right monic reduced.value
    let quotient := addTerm result.value.1 first.value.2 (first.value.1-second.value.1)
    ⟨(quotient.value,result.value.2),first.cost+second.cost+reduced.cost+result.cost+quotient.cost+10⟩
  else
    let empty := zeroVector (F := F) (n := n)
    ⟨(empty.value,left),first.cost+second.cost+empty.cost+10⟩
  termination_by (effectiveLength left).value
theorem divide_value (right : Vector F n) (monic : (polynomial right).Monic) (left : Vector F n) :
    (polynomial (divide right monic left).value.1,polynomial (divide right monic left).value.2) =
      ExecutablePolynomialDivision.monicAux (polynomial left) monic := by
  generalize sizeEq : (effectiveLength left).value = size
  induction size using Nat.strong_induction_on generalizing left with
  | h size ih =>
    rw [divide]
    by_cases active : (inspect left).value.2 ≠ 0 ∧ (inspect right).value.1 ≤ (inspect left).value.1
    · rw [dite_eq_left active]
      have valid := (active_iff left right monic).mp active
      have smaller := effectiveLength_lt_of_degree_lt (cancel left right).value left
        (cancel_degree_lt left right valid.1 valid.2 monic)
      have recursiveResult := ih (effectiveLength (cancel left right).value).value (by omega) (cancel left right).value rfl
      have shiftFits : (inspect left).value.1-(inspect right).value.1 < n := by
        rw [inspect_degree,inspect_degree]
        have bounded := polynomial_natDegree_lt left valid.1
        omega
      have oldActive : (polynomial right).degree ≤ (polynomial left).degree ∧ (polynomial left).support.Nonempty :=
        ⟨valid.2,support_nonempty.mpr valid.1⟩
      rw [ExecutablePolynomialDivision.monicAux,dite_eq_left oldActive]
      simp only [ExecutablePolynomial.add_eq,ExecutablePolynomial.sub_eq,ExecutablePolynomial.mul_eq,ExecutablePolynomial.term_eq]
      change (polynomial (addTerm _ _ _).value,polynomial _) = _
      rw [addTerm_polynomial _ _ _ shiftFits,inspect_leading,inspect_degree,inspect_degree]
      apply Prod.ext
      · have first := congrArg Prod.fst recursiveResult
        dsimp only at first ⊢
        rw [first,cancel_polynomial left right valid.1 valid.2]
        ring
      · have second := congrArg Prod.snd recursiveResult
        dsimp only at second ⊢
        rw [second,cancel_polynomial left right valid.1 valid.2]
    · rw [dite_eq_right active]
      have oldInactive : ¬((polynomial right).degree ≤ (polynomial left).degree ∧ (polynomial left).support.Nonempty) := by
        rintro ⟨order,nonzero⟩
        exact active ((active_iff left right monic).mpr ⟨support_nonempty.mp nonzero,order⟩)
      rw [ExecutablePolynomialDivision.monicAux,dite_eq_right oldInactive]
      simp only [zeroVector_polynomial,ExecutablePolynomial.zero_eq]

theorem divide_eq (right : Vector F n) (monic : (polynomial right).Monic) (left : Vector F n) :
    (polynomial (divide right monic left).value.1,polynomial (divide right monic left).value.2) =
      divModByMonicAux (polynomial left) monic := by
  rw [divide_value,ExecutablePolynomialDivision.monicAux_eq]

theorem divide_fst_eq (right : Vector F n) (monic : (polynomial right).Monic) (left : Vector F n) :
    polynomial (divide right monic left).value.1 = polynomial left /ₘ polynomial right := by
  rw [divByMonic,dite_eq_left monic]
  exact congrArg Prod.fst (divide_eq right monic left)

theorem divide_snd_eq (right : Vector F n) (monic : (polynomial right).Monic) (left : Vector F n) :
    polynomial (divide right monic left).value.2 = polynomial left %ₘ polynomial right := by
  rw [modByMonic,dite_eq_left monic]
  exact congrArg Prod.snd (divide_eq right monic left)

theorem divide_reconstruct (right : Vector F n) (monic : (polynomial right).Monic) (left : Vector F n) :
    polynomial right * polynomial (divide right monic left).value.1 +
      polynomial (divide right monic left).value.2 = polynomial left := by
  rw [divide_fst_eq,divide_snd_eq]
  simpa only [add_comm] using modByMonic_add_div (polynomial left) (polynomial right)

theorem divide_remainder_degree (right : Vector F n) (monic : (polynomial right).Monic) (left : Vector F n) :
    (polynomial (divide right monic left).value.2).degree < (polynomial right).degree := by
  rw [divide_snd_eq]
  exact degree_modByMonic_lt _ monic

theorem divide_cost_by_length (right : Vector F n) (monic : (polynomial right).Monic) (left : Vector F n) :
    (divide right monic left).cost ≤ ((effectiveLength left).value+1)*(50*n+50) := by
  generalize sizeEq : (effectiveLength left).value = size
  induction size using Nat.strong_induction_on generalizing left with
  | h size ih =>
    rw [divide]
    by_cases active : (inspect left).value.2 ≠ 0 ∧ (inspect right).value.1 ≤ (inspect left).value.1
    · rw [dite_eq_left active]
      have valid := (active_iff left right monic).mp active
      have smaller := effectiveLength_lt_of_degree_lt (cancel left right).value left
        (cancel_degree_lt left right valid.1 valid.2 monic)
      have recursiveBound := ih (effectiveLength (cancel left right).value).value (by omega) (cancel left right).value rfl
      have cancellationBound := cancel_cost left right
      have quotientBound := addTerm_cost (divide right monic (cancel left right).value).value.1
        (inspect left).value.2 ((inspect left).value.1-(inspect right).value.1)
      have scaled : ((effectiveLength (cancel left right).value).value+1)*(50*n+50) ≤ size*(50*n+50) :=
        Nat.mul_le_mul_right _ (by omega)
      simp only [inspect_cost]
      calc
        _ ≤ ((effectiveLength (cancel left right).value).value+1)*(50*n+50)+(50*n+50) := by omega
        _ ≤ size*(50*n+50)+(50*n+50) := Nat.add_le_add_right scaled _
        _ = (size+1)*(50*n+50) := by ring
    · rw [dite_eq_right active]
      simp only [inspect_cost,zeroVector_cost]
      have scaled : 50*n+50 ≤ (size+1)*(50*n+50) := by
        simpa only [Nat.one_mul] using Nat.mul_le_mul_right (50*n+50) (show 1 ≤ size+1 by omega)
      omega

theorem divide_cost (right : Vector F n) (monic : (polynomial right).Monic) (left : Vector F n) :
    (divide right monic left).cost ≤ 50*(n+1)^2 := by
  have bound := divide_cost_by_length right monic left
  have size := effectiveLength_bound left
  calc
    _ ≤ ((effectiveLength left).value+1)*(50*n+50) := bound
    _ ≤ (n+1)*(50*n+50) := Nat.mul_le_mul_right _ (Nat.add_le_add_right size 1)
    _ = 50*(n+1)^2 := by ring

end FormalProof4FHE.HasteBoots.DenseMonicDivision
