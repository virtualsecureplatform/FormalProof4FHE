module
import all FormalProof4FHE.HasteBoots.DenseBerlekampWelch
import all FormalProof4FHE.HasteBoots.BerlekampWelchSystem
import all FormalProof4FHE.HasteBoots.BerlekampWelchReconstruction
import all FormalProof4FHE.HasteBoots.BerlekampWelchPowers
import all FormalProof4FHE.HasteBoots.DenseCandidateCheck
import all FormalProof4FHE.HasteBoots.DensePolynomialDivision
import all FormalProof4FHE.HasteBoots.DenseMonicDivision
import all FormalProof4FHE.HasteBoots.DensePolynomialStepCost
import all FormalProof4FHE.HasteBoots.PolynomialShapeCost
import all FormalProof4FHE.HasteBoots.PolynomialEvaluationCost
import all FormalProof4FHE.HasteBoots.ScalarDistanceCost
import all FormalProof4FHE.HasteBoots.ColumnDistanceCost
import all FormalProof4FHE.HasteBoots.SolverOperationCost
import all FormalProof4FHE.HasteBoots.FiniteLinearSolver
import all Mathlib.Algebra.Field.ZMod
import all Mathlib.Data.ZMod.Basic
open FormalProof4FHE.HasteBoots
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private def points : Vector (ZMod 7) 5 := Vector.ofFn (fun i => i.val)
private def corrupted : Vector (ZMod 7) 5 := ⟨#[2,5,0,4,0],rfl⟩

/-- info: true -/
#guard_msgs in
#eval let run := DenseBerlekampWelch.decode 1 2 points corrupted
      match run.value with
      | some candidate => decide (candidate.toList = [2,3,0,0] ∧ run.cost ≤ 3141)
      | none => false

/-- info: true -/
#guard_msgs in
#eval let honest : Vector (ZMod 7) 5 := ⟨#[2,5,1,4,0],rfl⟩
      let run := DenseBerlekampWelch.decode 0 2 points honest
      match run.value with
      | some candidate => decide (candidate.toList = [2,3,0] ∧ run.cost ≤ 1785)
      | none => false

/-- info: true -/
#guard_msgs in
#eval let run := DenseBerlekampWelch.decode 1 0 points corrupted
      run.value.isNone && decide (run.cost = 2)

-- The norm shortcut constructs the full-width zero coefficient vector.
/-- info: true -/
#guard_msgs in
#eval let sparse : Vector (ZMod 7) 5 := ⟨#[0,0,0,4,0],rfl⟩
      let run := DenseBerlekampWelch.decode 1 2 points sparse
      match run.value with
      | some candidate => decide (candidate.toList = [0,0,0,0] ∧ run.cost = 43)
      | none => false

-- Inconsistent constant interpolation stops at the solver's none branch.
/-- info: true -/
#guard_msgs in
#eval let received : Vector (ZMod 7) 5 := ⟨#[1,2,3,4,5],rfl⟩
      let run := DenseBerlekampWelch.decode 0 1 points received
      run.value.isNone && decide (run.cost ≤ 1077)

/-- info: true -/
#guard_msgs in
#eval let quadratic : Vector (ZMod 7) 5 := Vector.ofFn (fun i => (points.get i)^2)
      let run := DenseBerlekampWelch.decode 1 2 points quadratic
      run.value.isNone && decide (run.cost ≤ 3141)

/-- info: true -/
#guard_msgs in
#eval let empty : Vector (ZMod 7) 0 := ⟨#[],rfl⟩
      let run := DenseBerlekampWelch.decode 0 1 empty empty
      match run.value with
      | some candidate => decide (candidate.toList = [0,0] ∧ run.cost = 11)
      | none => false

/-- info: true -/
#guard_msgs in
#eval let points : Vector (ZMod 7) 1 := ⟨#[0],rfl⟩
      let received : Vector (ZMod 7) 1 := ⟨#[3],rfl⟩
      let run := DenseBerlekampWelch.decode 0 1 points received
      match run.value with
      | some candidate => decide (candidate.toList = [3,0] ∧ run.cost ≤ 717)
      | none => false
