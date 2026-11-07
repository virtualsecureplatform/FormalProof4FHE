module
public import FormalProof4FHE.HasteBoots.DensePolynomialDivision
public import ArkLib.Data.CodingTheory.BerlekampWelch.Condition
@[expose] public section

/-! Reconstruction from the materialized Berlekamp-Welch solution. Locator and
numerator coefficients are loaded directly into vectors of known width e+k+1;
no polynomial degree discovery or coefficient callback is used in this phase.
The charge includes their construction and dense division. Output-polynomial
conversion and physical/backend costs are separate. -/
namespace FormalProof4FHE.HasteBoots.BerlekampWelchReconstruction
open SolverOperationCost Polynomial PolynomialShapeCost DensePolynomialStepCost
open scoped BigOperators
variable {F : Type} [Field F] [DecidableEq F]

def locatorEntry (e k : ℕ) (solution : Vector F (2*e+k)) (i : Fin (e+k+1)) : Run F :=
  if top : i.val = e then ⟨1,2⟩
  else if low : i.val < e then ⟨solution.get ⟨i.val,by omega⟩,3⟩ else ⟨0,2⟩

def locator (e k : ℕ) (solution : Vector F (2*e+k)) : Run (Vector F (e+k+1)) :=
  tabulate (locatorEntry e k solution)

def numeratorEntry (e k : ℕ) (solution : Vector F (2*e+k)) (i : Fin (e+k+1)) : Run F :=
  if inside : i.val < e+k then ⟨solution.get ⟨e+i.val,by omega⟩,2⟩ else ⟨0,2⟩

def numerator (e k : ℕ) (solution : Vector F (2*e+k)) : Run (Vector F (e+k+1)) :=
  tabulate (numeratorEntry e k solution)

theorem locator_polynomial (e k : ℕ) (solution : Vector F (2*e+k)) :
    polynomial (locator e k solution).value = BerlekampWelch.solutionToE e k (fun i => solution.get i) := by
  ext i
  change _ = if i = e then 1 else if i < e then Fin.liftF (fun j => solution.get j) i else 0
  by_cases inside : i < e+k+1
  · rw [polynomial_coeff_fin _ ⟨i,inside⟩]
    simp only [locator,tabulate_value,FiniteLinearSolver.get_ofFn,locatorEntry]
    by_cases top : i = e
    · simp [top]
    · by_cases low : i < e
      · simp [top,low,Fin.liftF,show i < 2*e+k by omega]
      · simp [top,low]
  · rw [polynomial_coeff_above _ i (by omega)]
    simp [show i ≠ e by omega,show ¬i < e by omega]

theorem numerator_polynomial (e k : ℕ) (solution : Vector F (2*e+k)) :
    polynomial (numerator e k solution).value = BerlekampWelch.solutionToQ e k (fun i => solution.get i) := by
  ext i
  rw [BerlekampWelch.solutionToQ_coeff]
  by_cases inside : i < e+k+1
  · rw [polynomial_coeff_fin _ ⟨i,inside⟩]
    simp only [numerator,tabulate_value,FiniteLinearSolver.get_ofFn,numeratorEntry]
    by_cases low : i < e+k
    · simp [low,Fin.liftF,show e+i < 2*e+k by omega]
    · simp [low]
  · rw [polynomial_coeff_above _ i (by omega)]
    simp [show ¬i < e+k by omega]

omit [DecidableEq F] in
theorem locator_cost (e k : ℕ) (solution : Vector F (2*e+k)) :
    (locator e k solution).cost ≤ 4*(e+k+1)+1 := by
  have entry (i : Fin (e+k+1)) : (locatorEntry e k solution i).cost ≤ 3 := by
    unfold locatorEntry
    split_ifs <;> dsimp only <;> omega
  have bound := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin (e+k+1)))) => entry i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] at bound
  simp only [locator,tabulate_cost]
  omega

omit [DecidableEq F] in
theorem numerator_cost (e k : ℕ) (solution : Vector F (2*e+k)) :
    (numerator e k solution).cost = 3*(e+k+1)+1 := by
  have entry (i : Fin (e+k+1)) : (numeratorEntry e k solution i).cost = 2 := by
    unfold numeratorEntry
    split <;> rfl
  simp only [numerator,tabulate_cost,entry,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring

def reconstruct (e k : ℕ) (solution : Vector F (2*e+k)) : Run (Vector F (e+k+1) × Vector F (e+k+1)) :=
  let first := numerator e k solution
  let second := locator e k solution
  let divided := DensePolynomialDivision.divMod first.value second.value
  ⟨divided.value,first.cost+second.cost+divided.cost+1⟩

theorem reconstruct_fst (e k : ℕ) (solution : Vector F (2*e+k)) :
    polynomial (reconstruct e k solution).value.1 =
      BerlekampWelch.solutionToQ e k (fun i => solution.get i) / BerlekampWelch.solutionToE e k (fun i => solution.get i) := by
  simp only [reconstruct,DensePolynomialDivision.divMod_fst_eq,numerator_polynomial,locator_polynomial]

theorem reconstruct_snd (e k : ℕ) (solution : Vector F (2*e+k)) :
    polynomial (reconstruct e k solution).value.2 =
      BerlekampWelch.solutionToQ e k (fun i => solution.get i) % BerlekampWelch.solutionToE e k (fun i => solution.get i) := by
  simp only [reconstruct,DensePolynomialDivision.divMod_snd_eq,numerator_polynomial,locator_polynomial]

theorem reconstruct_cost (e k : ℕ) (solution : Vector F (2*e+k)) :
    (reconstruct e k solution).cost ≤ 50*(e+k+2)^2+21*(e+k+1)+22 := by
  have first := numerator_cost e k solution
  have second := locator_cost e k solution
  have divided := DensePolynomialDivision.divMod_cost (numerator e k solution).value (locator e k solution).value
  simp only [reconstruct]
  nlinarith
end FormalProof4FHE.HasteBoots.BerlekampWelchReconstruction
