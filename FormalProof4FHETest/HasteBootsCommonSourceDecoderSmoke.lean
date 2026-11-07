module
import all FormalProof4FHE.HasteBoots.SolverOperationCost
import all FormalProof4FHE.HasteBoots.ScalarDistanceCost
import all FormalProof4FHE.HasteBoots.BerlekampWelchPowers
import all FormalProof4FHE.HasteBoots.BerlekampWelchSystem
import all FormalProof4FHE.HasteBoots.BerlekampWelchReconstruction
import all FormalProof4FHE.HasteBoots.BlockEvaluationCost
import all FormalProof4FHE.HasteBoots.ColumnDistanceCost
import all FormalProof4FHE.HasteBoots.ExecutableSourceCoefficients
import all FormalProof4FHE.HasteBoots.ExecutableCommonSource
import all FormalProof4FHE.HasteBoots.ExecutableBerlekampWelch
import all FormalProof4FHE.HasteBoots.ExecutablePolynomialDivision
import all FormalProof4FHE.HasteBoots.DensePolynomialDivision
import all FormalProof4FHE.HasteBoots.DenseMonicDivision
import all FormalProof4FHE.HasteBoots.DensePolynomialStepCost
import all FormalProof4FHE.HasteBoots.PolynomialShapeCost
import all FormalProof4FHE.HasteBoots.ExecutablePolynomial
import all FormalProof4FHE.HasteBoots.PolynomialEvaluationCost
import all FormalProof4FHE.HasteBoots.FiniteMatrixSolver
import all FormalProof4FHE.HasteBoots.FiniteLinearSolver
import all FormalProof4FHE.HasteBoots.RowLayout
import all ArkLib.Data.CodingTheory.BerlekampWelch.Condition
import all Mathlib.Algebra.Field.ZMod
import all Mathlib.Data.ZMod.Basic
open FormalProof4FHE.HasteBoots
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private def points (i : Fin 5) : ZMod 7 := i.val
private def source : ExecutableCommonSource.Table (ZMod 7) 2 2 2 :=
  Vector.ofFn (fun row => Vector.ofFn (fun j => Vector.ofFn (fun lane =>
    if j = 0 then 1 + (row.val : ZMod 7) + lane.val else 3)))
private def honest : Fin 5 → Fin 2 → Fin 2 → ZMod 7 := ExecutableCommonSource.word points source
private def sameColumn (pos : Fin 5) (row lane : Fin 2) : ZMod 7 :=
  honest pos row lane + if pos = 2 then 1 else 0
private def differentColumns (pos : Fin 5) (row lane : Fin 2) : ZMod 7 :=
  honest pos row lane + if (lane = 0 ∧ pos = 2) ∨ (lane = 1 ∧ pos = 3) then 1 else 0

-- All row/lane errors in one column fit the joint promise.
/-- info: true -/
#guard_msgs in
#eval decide ((ExecutableCommonSource.decode 1 points sameColumn : ExecutableCommonSource.Table (ZMod 7) 2 2 2) = source)

-- Scalar decoding succeeds, but its two error positions exceed the whole-column radius.
/-- info: true -/
#guard_msgs in
#eval let candidate : ExecutableCommonSource.Table (ZMod 7) 2 2 2 := ExecutableCommonSource.candidates 1 points differentColumns
      let decoded : ExecutableCommonSource.Table (ZMod 7) 2 2 2 := ExecutableCommonSource.decode 1 points differentColumns
      decide (candidate = source ∧ decoded = ExecutableCommonSource.zeroTable)

-- Recover the first three original coordinates, dropping the fourth padding slot.
/-- info: true -/
#guard_msgs in
#eval let table := ExecutableSourceCoefficients.extract 1 points (size := 3) (m := 2) (b := 2) (by decide) sameColumn
      decide (((table.get 0).get 0 = 1) ∧ ((table.get 0).get 1 = 2) ∧ ((table.get 0).get 2 = 3) ∧
        ((table.get 1).get 0 = 2))

-- The measured final check preserves the joint column radius and has one
-- data-independent charge for evaluation, scanning and the radius comparison.
/-- info: true -/
#guard_msgs in
#eval let run := ExecutableCommonSource.checkWithCost 1 points sameColumn source
      run.value && decide (run.cost = 634)

/-- info: true -/
#guard_msgs in
#eval let run := ExecutableCommonSource.checkWithCost 1 points differentColumns source
      !run.value && decide (run.cost = 634)
