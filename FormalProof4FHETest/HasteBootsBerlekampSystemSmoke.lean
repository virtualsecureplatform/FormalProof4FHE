module
import all FormalProof4FHE.HasteBoots.BerlekampWelchPowers
import all FormalProof4FHE.HasteBoots.BerlekampWelchSystem
import all FormalProof4FHE.HasteBoots.BerlekampWelchReconstruction
import all FormalProof4FHE.HasteBoots.ExecutableBerlekampWelch
import all FormalProof4FHE.HasteBoots.SolverOperationCost
import all FormalProof4FHE.HasteBoots.ScalarDistanceCost
import all FormalProof4FHE.HasteBoots.ColumnDistanceCost
import all FormalProof4FHE.HasteBoots.FiniteLinearSolver
import all FormalProof4FHE.HasteBoots.FiniteMatrixSolver
import all FormalProof4FHE.HasteBoots.ExecutablePolynomialDivision
import all FormalProof4FHE.HasteBoots.DensePolynomialDivision
import all FormalProof4FHE.HasteBoots.DenseMonicDivision
import all FormalProof4FHE.HasteBoots.DensePolynomialStepCost
import all FormalProof4FHE.HasteBoots.PolynomialShapeCost
import all FormalProof4FHE.HasteBoots.ExecutablePolynomial
import all FormalProof4FHE.HasteBoots.PolynomialEvaluationCost
import all ArkLib.Data.CodingTheory.BerlekampWelch.Condition
import all Mathlib.Algebra.Field.ZMod
import all Mathlib.Data.ZMod.Basic
import all Mathlib.Data.Fintype.Basic
import all Mathlib.Data.Fintype.Defs
open FormalProof4FHE.HasteBoots
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private def points : Vector (ZMod 7) 5 := Vector.ofFn (fun i => i.val)
private def honest : Vector (ZMod 7) 5 := Vector.ofFn (fun i => 2+3*points.get i)
private def received : Vector (ZMod 7) 5 := Vector.ofFn (fun i => if i = 2 then 0 else honest.get i)

/-- info: true -/
#guard_msgs in
#eval let run := BerlekampWelchPowers.powers (3 : ZMod 7) 4
      decide (run.value.toList = [1,3,2,6,4] ∧ run.cost = 27)

-- The zero point still has zeroth power one.
/-- info: true -/
#guard_msgs in
#eval let run := BerlekampWelchPowers.powers (0 : ZMod 7) 2
      decide (run.value.toList = [1,0,0] ∧ run.cost = 17)

-- Shared powers give the exact construction charge and the original matrix signs.
/-- info: true -/
#guard_msgs in
#eval let built := BerlekampWelchSystem.build 1 2 points received
      match built.value[0]?,built.value[2]? with
      | some first,some corrupt => decide (built.cost = 242 ∧ first.coefficients.toList = [2,6,0,0] ∧ first.rhs = 0 ∧
          corrupt.coefficients.toList = [0,6,5,3] ∧ corrupt.rhs = 0)
      | _,_ => false

/-- info: true -/
#guard_msgs in
#eval let run := BerlekampWelchSystem.solve 1 2 points received
      match run.value with
      | some value => decide ((BerlekampWelch.BerlekampWelchMatrix 1 2 (fun i => points.get i) (fun i => received.get i)).mulVec value =
          BerlekampWelch.Rhs 1 (fun i => points.get i) (fun i => received.get i) ∧ run.cost ≤ 1443)
      | none => false

-- No error-locator coefficients when e=0; the quotient coefficients are recovered directly.
/-- info: true -/
#guard_msgs in
#eval let run := BerlekampWelchSystem.solve 0 2 points honest
      match run.value with
      | some value => decide (value 0 = 2 ∧ value 1 = 3 ∧ (BerlekampWelchSystem.build 0 2 points honest).cost = 177)
      | none => false

/-- info: true -/
#guard_msgs in
#eval let run := BerlekampWelchSystem.solve 0 0 (Vector.ofFn (fun _ : Fin 1 => (0 : ZMod 7)))
        (Vector.ofFn (fun _ : Fin 1 => (1 : ZMod 7)))
      run.value.isNone && decide (run.cost = 25)

-- Reconstruction can consume the stored solver vector without a function round trip.
/-- info: true -/
#guard_msgs in
#eval let run := BerlekampWelchSystem.solveVector 1 2 points received
      match run.value with
      | some value => decide (value.toList = [5,3,3,3] ∧ run.cost ≤ 1442)
      | none => false
