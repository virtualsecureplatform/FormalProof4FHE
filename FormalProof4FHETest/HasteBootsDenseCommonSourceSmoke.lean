module
import all FormalProof4FHE.HasteBoots.DenseCommonSource
import all FormalProof4FHE.HasteBoots.BlockEvaluationCost
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
private def source : DenseCommonSource.Table (ZMod 7) 2 2 2 :=
  Vector.ofFn (fun row => Vector.ofFn (fun j => Vector.ofFn (fun lane =>
    if j = 0 then 1+(row.val : ZMod 7)+lane.val else 3)))
private def raw (split : Bool) : DenseCommonSource.Columns (ZMod 7) 5 2 2 :=
  Vector.ofFn (fun pos => Vector.ofFn (fun row => Vector.ofFn (fun lane =>
    1+(row.val : ZMod 7)+lane.val+3*(pos.val : ZMod 7) +
      if (if split then (lane = 0 ∧ pos = 2) ∨ (lane = 1 ∧ pos = 3) else pos = 2) then 1 else 0)))

/-- info: true -/
#guard_msgs in
#eval let run := DenseCommonSource.decode 1 2 points (raw false)
      decide (run.value = source ∧ run.cost ≤ 13399)

-- Scalar candidates recover, but the joint two-column error is rejected.
/-- info: true -/
#guard_msgs in
#eval let candidates := DenseCommonSource.candidates 1 2 points (raw true)
      let run := DenseCommonSource.decode 1 2 points (raw true)
      let zero := (DenseCommonSource.zeroTable : SolverOperationCost.Run (DenseCommonSource.Table (ZMod 7) 2 2 2)).value
      decide (candidates.value = source ∧ run.value = zero ∧ run.cost ≤ 13399)

/-- info: true -/
#guard_msgs in
#eval let word := DenseCommonSource.laneWord (raw false) 0 0
      decide (word.value.toList = [1,4,1,3,6] ∧ word.cost = 21)

/-- info: true -/
#guard_msgs in
#eval let points : Vector (ZMod 7) 3 := Vector.ofFn (fun i => i.val)
      let empty : DenseCommonSource.Columns (ZMod 7) 3 0 2 := Vector.ofFn (fun _ => Vector.ofFn (fun i => i.elim0))
      let run := DenseCommonSource.decode 1 2 points empty
      decide (run.value.toList = [] ∧ run.cost = 96)

/-- info: true -/
#guard_msgs in
#eval let points : Vector (ZMod 7) 3 := Vector.ofFn (fun i => i.val)
      let empty : DenseCommonSource.Columns (ZMod 7) 3 2 0 :=
        Vector.ofFn (fun _ => Vector.ofFn (fun _ => Vector.ofFn (fun i => i.elim0)))
      let run := DenseCommonSource.decode 1 2 points empty
      decide (((run.value.get 0).get 0).toList = [] ∧ run.cost = 166)

/-- info: true -/
#guard_msgs in
#eval let points : Vector (ZMod 7) 0 := ⟨#[],rfl⟩
      let empty : DenseCommonSource.Columns (ZMod 7) 0 2 2 := Vector.ofFn (fun i => i.elim0)
      let run := DenseCommonSource.decode 0 2 points empty
      let zero := (DenseCommonSource.zeroTable : SolverOperationCost.Run (DenseCommonSource.Table (ZMod 7) 2 2 2)).value
      decide (run.value = zero ∧ run.cost = 152)

/-- info: true -/
#guard_msgs in
#eval let points : Vector (ZMod 7) 1 := ⟨#[0],rfl⟩
      let raw : DenseCommonSource.Columns (ZMod 7) 1 1 1 := Vector.ofFn (fun _ => Vector.ofFn (fun _ => Vector.ofFn (fun _ => 0)))
      let run := DenseCommonSource.decode 0 0 points raw
      decide ((run.value.get 0).toList = [] ∧ run.cost = 62)
