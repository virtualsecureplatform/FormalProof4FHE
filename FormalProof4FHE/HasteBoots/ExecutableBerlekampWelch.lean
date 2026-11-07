module
public import FormalProof4FHE.HasteBoots.BerlekampWelchSystem
public import FormalProof4FHE.HasteBoots.BerlekampWelchReconstruction
public import FormalProof4FHE.HasteBoots.ExecutablePolynomialDivision
public import FormalProof4FHE.HasteBoots.ScalarDistanceCost
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

def solveSystemVector (e k : ℕ) (points received : Fin n → F) :
    SolverOperationCost.Run (Option (Vector F (2*e+k))) :=
  BerlekampWelchSystem.solveVector e k (Vector.ofFn points) (Vector.ofFn received)

omit [NeZero n] in
theorem solveSystemVector_map (e k : ℕ) (points received : Fin n → F) :
    (solveSystemVector e k points received).value.map (fun value i => value.get i) =
      (solveSystem e k points received).value := rfl

omit [NeZero n] in
theorem solveSystemVector_cost (e k : ℕ) (points received : Fin n → F) :
    (solveSystemVector e k points received).cost ≤ n*(13*e+9*k+17)+8*(n+1)*(2*e+k+1)^2+2 :=
  BerlekampWelchSystem.solveVector_cost e k _ _

/-- Input-function evaluation and vector preparation are separate costs. -/
def normWithCost (received : Fin n → F) : SolverOperationCost.Run ℕ :=
  ScalarDistanceCost.norm (Vector.ofFn received)

omit [NeZero n] in
theorem normWithCost_value (received : Fin n → F) : (normWithCost received).value = ‖received‖₀ := by
  simp only [normWithCost,ScalarDistanceCost.norm_value,FiniteLinearSolver.get_ofFn]

omit [NeZero n] in
theorem normWithCost_cost (received : Fin n → F) : (normWithCost received).cost = 6*n+2 :=
  ScalarDistanceCost.norm_cost _

/-- Prepared-input phase charge for evaluations, scalar distance and radius
comparison. Degree checking and reconstruction are separate costs. -/
def candidateCheckWithCost (e : ℕ) (candidate : Polynomial F) (points received : Fin n → F) :
    SolverOperationCost.Run Bool :=
  let evaluations := ExecutablePolynomial.evaluateManyWithCost candidate (Vector.ofFn points)
  let distance := ScalarDistanceCost.distance (Vector.ofFn received) evaluations.value
  ⟨decide (distance.value ≤ e),evaluations.cost+distance.cost+1⟩

omit [NeZero n] in
theorem candidateCheckWithCost_value (e : ℕ) (candidate : Polynomial F) (points received : Fin n → F) :
    (candidateCheckWithCost e candidate points received).value =
      decide (Δ₀(received,candidate.eval ∘ points) ≤ e) := by
  have evaluated : (fun i => ((ExecutablePolynomial.evaluateManyWithCost candidate (Vector.ofFn points)).value).get i) =
      candidate.eval ∘ points := by
    funext i
    exact ExecutablePolynomial.evaluateMany_get candidate points i
  simp only [candidateCheckWithCost,ScalarDistanceCost.distance_value,FiniteLinearSolver.get_ofFn,evaluated]

omit [NeZero n] in
theorem candidateCheckWithCost_cost (e : ℕ) (candidate : Polynomial F) (points received : Fin n → F) :
    (candidateCheckWithCost e candidate points received).cost = n*(7*(candidate.natDegree+1)+12)+4 := by
  simp only [candidateCheckWithCost,ExecutablePolynomial.evaluateManyWithCost_cost,ScalarDistanceCost.distance_cost]
  ring

omit [NeZero n] in
theorem candidateCheckWithCost_cost_le_dimension (e k : ℕ) (candidate : Polynomial F)
    (points received : Fin n → F) (degree : candidate.natDegree < k) :
    (candidateCheckWithCost e candidate points received).cost ≤ n*(7*k+12)+4 := by
  rw [candidateCheckWithCost_cost]
  have bound : candidate.natDegree+1 ≤ k := by omega
  exact Nat.add_le_add_right
    (Nat.mul_le_mul_left n (Nat.add_le_add_right (Nat.mul_le_mul_left 7 bound) 12)) 4

def decoder (e k : ℕ) (points received : Fin n → F) : Option (Polynomial F) :=
  if k = 0 then none
  else if (normWithCost received).value ≤ e then some ExecutablePolynomial.zero
  else match (solveSystemVector e k points received).value with
    | none => none
    | some solution =>
      let reconstruction := BerlekampWelchReconstruction.reconstruct e k solution
      if (PolynomialShapeCost.polynomial reconstruction.value.2).support = ∅ then
        let candidate := PolynomialShapeCost.polynomial reconstruction.value.1
        if candidate.natDegree < k ∧ (candidateCheckWithCost e candidate points received).value then
          some candidate
        else none
      else none

omit [NeZero n] in
theorem success {e k : ℕ} {points received : Fin n → F} {candidate : Polynomial F}
    (accepted : decoder e k points received = some candidate) :
    candidate.natDegree < k ∧ Δ₀(received, candidate.eval ∘ points) ≤ e := by
  unfold decoder at accepted
  simp only [normWithCost_value] at accepted
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
      · split_ifs at accepted with divisible close
        · cases accepted
          simpa only [candidateCheckWithCost_value,decide_eq_true_eq] using close

theorem complete {e k : ℕ} {points received : Fin n → F} {message : Polynomial F}
    (radius : 2 * e < n - k + 1) (dimension : k ≤ n)
    (distinct : Function.Injective points) (degree : message.natDegree < k)
    (nearby : Δ₀(received, message.eval ∘ points) ≤ e) :
    decoder e k points received = some message := by
  have positive : k ≠ 0 := by omega
  unfold decoder
  simp only [normWithCost_value]
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
  · rw [ite_eq_right sparse]
    have consistent : ∃ value, (BerlekampWelchMatrix e k points received).mulVec value = Rhs e points received := by
      cases chosen : linsolve (BerlekampWelchMatrix e k points received) (Rhs e points received) with
      | none => exact False.elim (linsolve_always_some_berlekamp_welch degree nearby chosen)
      | some value => exact ⟨value,linsolve_some chosen⟩
    obtain ⟨referenceSolution,referenceSolved⟩ := FiniteMatrixSolver.solve_complete _ _ consistent
    have mapped : (solveSystemVector e k points received).value.map (fun value i => value.get i) = some referenceSolution := by
      rw [solveSystemVector_map,solveSystem_value,referenceSolved]
    obtain ⟨solution,selected,_⟩ := Option.map_eq_some_iff.mp mapped
    rw [selected]
    have solved : FiniteMatrixSolver.solve (BerlekampWelchMatrix e k points received) (Rhs e points received) =
        some (fun i => solution.get i) := by
      rw [← solveSystem_value e k points received,← solveSystemVector_map e k points received,selected]
      rfl
    have condition := BerlekampWelchCondition_iff_Solution.mp (FiniteMatrixSolver.solve_some _ _ _ solved)
    have nonzero : message ≠ 0 := by
      intro zero
      subst message
      apply sparse
      simpa [Function.comp_def,hammingDist,hammingNorm] using nearby
    have quotient := Q'_div_E'_eq_p degree radius dimension nearby distinct
      (solutionToQ_ne_zero (not_le.mp sparse) (BerlekampWelchCondition_iff_Solution.mpr condition) distinct)
      nonzero condition
    simp only [BerlekampWelchReconstruction.reconstruct_snd,BerlekampWelchReconstruction.reconstruct_fst,
      support_eq_empty,EuclideanDomain.mod_eq_zero.mpr quotient.1,ite_eq_left,quotient.2,
      candidateCheckWithCost_value,decide_eq_true_eq]
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
