module
import all FormalProof4FHE.HasteBoots.BlockEvaluationCost
import all FormalProof4FHE.HasteBoots.BerlekampWelchPowers
import all FormalProof4FHE.HasteBoots.SolverOperationCost
import all Mathlib.Algebra.Field.ZMod
import all Mathlib.Data.ZMod.Basic
open FormalProof4FHE.HasteBoots
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private def points : Vector (ZMod 7) 3 := Vector.ofFn (fun i => i.val)
private def table : BlockEvaluationCost.Table (ZMod 7) 2 2 2 :=
  Vector.ofFn (fun row => Vector.ofFn (fun j => Vector.ofFn (fun lane =>
    if j = 0 then 1 + (row.val : ZMod 7) + lane.val else 3)))

-- Nonconstant coefficients, two rows and two lanes share each position's powers.
/-- info: true -/
#guard_msgs in
#eval let run := BlockEvaluationCost.evaluate points table
      decide (run.cost = 241 ∧ ((run.value.get 0).get 0).toList = [1,2] ∧
        ((run.value.get 1).get 0).toList = [4,5] ∧ ((run.value.get 2).get 1).toList = [1,2])

/-- info: true -/
#guard_msgs in
#eval let run := BlockEvaluationCost.evaluate (Vector.ofFn (fun i : Fin 0 => i.elim0)) table
      decide (run.cost = 1 ∧ run.value.toList = [])

-- Empty row and lane dimensions retain the structural traversal charges.
/-- info: true -/
#guard_msgs in
#eval let empty : BlockEvaluationCost.Table (ZMod 7) 0 2 2 := Vector.ofFn (fun i => i.elim0)
      let run := BlockEvaluationCost.evaluate points empty
      decide (run.cost = 61 ∧ (run.value.get 0).toList = [])

/-- info: true -/
#guard_msgs in
#eval let empty : BlockEvaluationCost.Table (ZMod 7) 2 2 0 :=
        Vector.ofFn (fun _ => Vector.ofFn (fun _ => Vector.ofFn (fun i => i.elim0)))
      let run := BlockEvaluationCost.evaluate points empty
      decide (run.cost = 73 ∧ ((run.value.get 0).get 0).toList = [])

-- Zero message width evaluates to zero, including at the zero point.
/-- info: true -/
#guard_msgs in
#eval let empty : BlockEvaluationCost.Table (ZMod 7) 2 0 2 :=
        Vector.ofFn (fun _ => Vector.ofFn (fun i => i.elim0))
      let run := BlockEvaluationCost.evaluate points empty
      decide (run.cost = 67 ∧ ((run.value.get 0).get 1).toList = [0,0] ∧
        ((run.value.get 2).get 0).toList = [0,0])
