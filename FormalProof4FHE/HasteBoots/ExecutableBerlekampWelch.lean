module
public import FormalProof4FHE.HasteBoots.BerlekampWelchSystem
public import FormalProof4FHE.HasteBoots.ExecutablePolynomialDivision
public import ArkLib.Data.CodingTheory.BerlekampWelch.BerlekampWelch
@[expose] public section

/-! Executable Berlekamp–Welch decoding. Algebraic reconstruction uses ArkLib's
lemmas (Apache 2.0; František Silváši and Ilia Vlasov). Runtime solution selection,
polynomial arithmetic and evaluation use our explicit executable definitions.
Success checks include degree, divisibility, and distance; dimension zero fails. -/
namespace FormalProof4FHE.HasteBoots.ExecutableBerlekampWelch
open Polynomial BerlekampWelch
variable {F : Type} [Field F] [DecidableEq F] {n : ℕ} [NeZero n]

/-- Measured system construction and elimination from prepared input vectors.
Evaluation of the input functions and their initial materialization is excluded;
this is not the cost of all decoder branches or polynomial reconstruction. -/
def solveSystem (e k : ℕ) (points received : Fin n → F) : SolverOperationCost.Run (Option (Fin (2*e+k) → F)) :=
  BerlekampWelchSystem.solve e k (Vector.ofFn points) (Vector.ofFn received)

omit [NeZero n] in
theorem solveSystem_value (e k : ℕ) (points received : Fin n → F) :
    (solveSystem e k points received).value =
      FiniteMatrixSolver.solve (BerlekampWelchMatrix e k points received) (Rhs e points received) := by
  simp only [solveSystem,BerlekampWelchSystem.solve_value,FiniteLinearSolver.get_ofFn]

omit [NeZero n] in
theorem solveSystem_cost (e k : ℕ) (points received : Fin n → F) :
    (solveSystem e k points received).cost ≤ n*(13*e+9*k+17)+8*(n+1)*(2*e+k+1)^2+3 :=
  BerlekampWelchSystem.solve_cost e k _ _

def decoder (e k : ℕ) (points received : Fin n → F) : Option (Polynomial F) :=
  if k = 0 then none
  else if ‖received‖₀ ≤ e then some ExecutablePolynomial.zero
  else match (solveSystem e k points received).value with
    | none => none
    | some solution =>
      let locator := solutionToE e k solution
      let numerator := solutionToQ e k solution
      let reconstruction := ExecutablePolynomialDivision.divMod numerator locator
      if reconstruction.2.support = ∅ then
        let candidate := reconstruction.1
        let evaluations := ExecutablePolynomial.evaluateMany candidate points
        if candidate.natDegree < k ∧ Δ₀(received, fun i => evaluations.get i) ≤ e then
          some candidate
        else none
      else none

omit [NeZero n] in
theorem success {e k : ℕ} {points received : Fin n → F} {candidate : Polynomial F}
    (accepted : decoder e k points received = some candidate) :
    candidate.natDegree < k ∧ Δ₀(received, candidate.eval ∘ points) ≤ e := by
  unfold decoder at accepted
  by_cases hk : k = 0
  · simp only [hk,ite_eq_left] at accepted
    contradiction
  · rw [ite_eq_right hk] at accepted
    by_cases sparse : ‖received‖₀ ≤ e
    · rw [ite_eq_left sparse,ExecutablePolynomial.zero_eq] at accepted
      have equal := Option.some.inj accepted
      subst candidate
      constructor
      · simpa using Nat.pos_of_ne_zero hk
      · simpa [Function.comp_def,hammingDist,hammingNorm] using sparse
    · rw [ite_eq_right sparse] at accepted
      split at accepted
      · contradiction
      · dsimp only at accepted
        split_ifs at accepted with divisible close
        · cases accepted
          simpa only [ExecutablePolynomial.evaluateMany_get,Function.comp_def] using close

theorem complete {e k : ℕ} {points received : Fin n → F} {message : Polynomial F}
    (radius : 2 * e < n - k + 1) (dimension : k ≤ n)
    (distinct : Function.Injective points) (degree : message.natDegree < k)
    (nearby : Δ₀(received, message.eval ∘ points) ≤ e) :
    decoder e k points received = some message := by
  have positive : k ≠ 0 := by omega
  unfold decoder
  rw [ite_eq_right positive]
  by_cases sparse : ‖received‖₀ ≤ e
  · rw [ite_eq_left sparse,ExecutablePolynomial.zero_eq]
    have zero : message = 0 := by
      refine poly_eq_zero_of_dist_lt degree dimension distinct (lt_of_le_of_lt ?_ radius)
      calc
        Δ₀(message.eval ∘ points, 0) ≤ ‖received‖₀ + Δ₀(received, message.eval ∘ points) := by
          simpa [hammingDist_comm,hammingDist_zero_right] using hammingDist_triangle 0 received (message.eval ∘ points)
        _ ≤ 2 * e := by omega
    rw [zero]
  · rw [ite_eq_right sparse,solveSystem_value]
    have consistent : ∃ value, (BerlekampWelchMatrix e k points received).mulVec value = Rhs e points received := by
      cases chosen : linsolve (BerlekampWelchMatrix e k points received) (Rhs e points received) with
      | none => exact False.elim (linsolve_always_some_berlekamp_welch degree nearby chosen)
      | some value => exact ⟨value,linsolve_some chosen⟩
    obtain ⟨solution,solved⟩ := FiniteMatrixSolver.solve_complete _ _ consistent
    rw [solved]
    have condition := BerlekampWelchCondition_iff_Solution.mp (FiniteMatrixSolver.solve_some _ _ _ solved)
    have nonzero : message ≠ 0 := by
      intro zero
      subst message
      apply sparse
      simpa [Function.comp_def,hammingDist,hammingNorm] using nearby
    have quotient := Q'_div_E'_eq_p degree radius dimension nearby distinct
      (solutionToQ_ne_zero (not_le.mp sparse) (BerlekampWelchCondition_iff_Solution.mpr condition) distinct)
      nonzero condition
    simp only [ExecutablePolynomialDivision.divMod_snd_eq,ExecutablePolynomialDivision.divMod_fst_eq,
      support_eq_empty,EuclideanDomain.mod_eq_zero.mpr quotient.1,ite_eq_left,quotient.2,
      ExecutablePolynomial.evaluateMany_get]
    exact ite_eq_left ⟨degree,nearby⟩
theorem failure_iff {e k : ℕ} {points received : Fin n → F}
    (radius : 2 * e < n - k + 1) (dimension : k ≤ n)
    (distinct : Function.Injective points) :
    decoder e k points received = none ↔
      ¬∃ message : Polynomial F, message.natDegree < k ∧ Δ₀(received, message.eval ∘ points) ≤ e := by
  constructor
  · intro failed ⟨message,degree,nearby⟩
    have accepted := complete radius dimension distinct degree nearby
    rw [failed] at accepted
    contradiction
  · intro absent
    cases result : decoder e k points received with
    | none => rfl
    | some message => exact False.elim (absent ⟨message,success result⟩)

end FormalProof4FHE.HasteBoots.ExecutableBerlekampWelch
