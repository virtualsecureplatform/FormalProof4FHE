module
import all FormalProof4FHE.HasteBoots.PolynomialEvaluationCost
import all FormalProof4FHE.HasteBoots.SolverOperationCost
import all Mathlib.Algebra.Field.ZMod
import all Mathlib.Data.ZMod.Basic
open FormalProof4FHE.HasteBoots
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private def affine : Vector (ZMod 7) 2 := ⟨#[2,3],rfl⟩
private def points : Vector (ZMod 7) 5 := Vector.ofFn (fun i => i.val)

/-- info: true -/
#guard_msgs in
#eval let run := PolynomialEvaluationCost.evaluate affine 2
      decide (run.value = 1 ∧ run.cost = 17)

-- Ascending coefficient order, internal zeros, and field cancellation.
/-- info: true -/
#guard_msgs in
#eval let coefficients : Vector (ZMod 7) 5 := ⟨#[1,0,2,0,4],rfl⟩
      let run := PolynomialEvaluationCost.evaluate coefficients 3
      decide (run.value = 0 ∧ run.cost = 38)

-- A prepared vector's trailing zeros still contribute to its traversal cost.
/-- info: true -/
#guard_msgs in
#eval let coefficients : Vector (ZMod 7) 5 := ⟨#[2,3,0,0,0],rfl⟩
      let run := PolynomialEvaluationCost.evaluate coefficients 2
      decide (run.value = 1 ∧ run.cost = 38)

/-- info: true -/
#guard_msgs in
#eval let run := PolynomialEvaluationCost.evaluateMany affine points
      decide (run.value.toList = [2,5,1,4,0] ∧ run.cost = 96)

/-- info: true -/
#guard_msgs in
#eval let empty : Vector (ZMod 7) 0 := ⟨#[],rfl⟩
      let one := PolynomialEvaluationCost.evaluate empty 0
      let many := PolynomialEvaluationCost.evaluateMany empty points
      decide (one.value = 0 ∧ one.cost = 3 ∧ many.value.toList = [0,0,0,0,0] ∧ many.cost = 26)

/-- info: true -/
#guard_msgs in
#eval let empty : Vector (ZMod 7) 0 := ⟨#[],rfl⟩
      let run := PolynomialEvaluationCost.evaluateMany affine empty
      decide (run.value.toList = [] ∧ run.cost = 1)
