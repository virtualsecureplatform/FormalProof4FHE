module
public import FormalProof4FHE.HasteBoots.BerlekampWelchSystem
public import FormalProof4FHE.HasteBoots.BerlekampWelchReconstruction
public import FormalProof4FHE.HasteBoots.DenseCandidateCheck
@[expose] public section

/-! Complete scalar decoding on prepared vectors, with a composed field/access
bound. The result remains a coefficient vector; polynomial output conversion,
input-function materialization and physical/backend refinement are separate. -/
namespace FormalProof4FHE.HasteBoots.DenseBerlekampWelch
open SolverOperationCost PolynomialShapeCost
variable {F : Type} [Field F] [DecidableEq F] {n : ℕ}

-- The phase bounds are deliberately retained as a sum to expose every charge.
def operationBound (n e k : ℕ) : ℕ :=
  (6*n+2) +
  (n*(13*e+9*k+17)+8*(n+1)*(2*e+k+1)^2+2) +
  (50*(e+k+2)^2+21*(e+k+1)+22) +
  (n*(7*(e+k+1)+12)+16*(e+k+1)+23) + (e+k+1+20)

theorem operationBound_eq (n e k : ℕ) :
    operationBound n e k = n*(20*e+16*k+42)+8*(n+1)*(2*e+k+1)^2+
      50*(e+k+2)^2+38*(e+k+1)+69 := by
  unfold operationBound
  ring

def decode (e k : ℕ) (points received : Vector F n) : Run (Option (Vector F (e+k+1))) :=
  if k = 0 then ⟨none,2⟩
  else
    let norm := ScalarDistanceCost.norm received
    if norm.value ≤ e then
      let zero := DenseMonicDivision.zeroVector (F := F) (n := e+k+1)
      ⟨some zero.value,norm.cost+zero.cost+6⟩
    else
      let solved := BerlekampWelchSystem.solveVector e k points received
      match solved.value with
      | none => ⟨none,norm.cost+solved.cost+6⟩
      | some solution =>
        let reconstructed := BerlekampWelchReconstruction.reconstruct e k solution
        let checked := DenseCandidateCheck.check e k reconstructed.value.1 reconstructed.value.2 points received
        ⟨if checked.value then some reconstructed.value.1 else none,
          norm.cost+solved.cost+reconstructed.cost+checked.cost+10⟩

theorem decode_map (e k : ℕ) (points received : Vector F n) :
    (decode e k points received).value.map polynomial =
      if k = 0 then none
      else if (ScalarDistanceCost.norm received).value ≤ e then some 0
      else match (BerlekampWelchSystem.solveVector e k points received).value with
        | none => none
        | some solution =>
          let reconstructed := BerlekampWelchReconstruction.reconstruct e k solution
          if (DenseCandidateCheck.check e k reconstructed.value.1 reconstructed.value.2 points received).value then
            some (polynomial reconstructed.value.1) else none := by
  unfold decode
  dsimp only
  split_ifs
  · rfl
  · simp only [Option.map_some,DenseMonicDivision.zeroVector_polynomial]
  · cases solved : (BerlekampWelchSystem.solveVector e k points received).value with
    | none => rfl
    | some solution =>
      dsimp only
      split_ifs <;> rfl

theorem decode_cost (e k : ℕ) (points received : Vector F n) :
    (decode e k points received).cost ≤ operationBound n e k := by
  by_cases dimension : k = 0
  · rw [decode,ite_eq_left dimension]
    dsimp only
    unfold operationBound
    omega
  · rw [decode,ite_eq_right dimension]
    by_cases sparse : (ScalarDistanceCost.norm received).value ≤ e
    · rw [ite_eq_left sparse]
      simp only [ScalarDistanceCost.norm_cost,DenseMonicDivision.zeroVector_cost]
      unfold operationBound
      omega
    · rw [ite_eq_right sparse]
      have solvedBound := BerlekampWelchSystem.solveVector_cost e k points received
      cases solved : (BerlekampWelchSystem.solveVector e k points received).value with
      | none =>
        simp only [solved,ScalarDistanceCost.norm_cost]
        unfold operationBound
        omega
      | some solution =>
        have reconstructedBound := BerlekampWelchReconstruction.reconstruct_cost e k solution
        have checkedBound := DenseCandidateCheck.check_cost e k
          (BerlekampWelchReconstruction.reconstruct e k solution).value.1
          (BerlekampWelchReconstruction.reconstruct e k solution).value.2 points received
        simp only [solved,ScalarDistanceCost.norm_cost]
        unfold operationBound
        omega
end FormalProof4FHE.HasteBoots.DenseBerlekampWelch
