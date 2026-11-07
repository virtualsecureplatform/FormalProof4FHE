module
import all FormalProof4FHE.HasteBoots.DensePolynomialStepCost
import all FormalProof4FHE.HasteBoots.PolynomialShapeCost
import all FormalProof4FHE.HasteBoots.SolverOperationCost
import all Mathlib.Algebra.Field.ZMod
import all Mathlib.Data.ZMod.Basic
open FormalProof4FHE.HasteBoots
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private def numerator : Vector (ZMod 7) 4 := ⟨#[1,0,1,0],rfl⟩
private def divisor : Vector (ZMod 7) 4 := ⟨#[1,1,0,0],rfl⟩

-- X²+1 -> 1-X -> 2 when dividing by X+1.
/-- info: true -/
#guard_msgs in
#eval let first := DensePolynomialStepCost.cancel numerator divisor
      let second := DensePolynomialStepCost.cancel first.value divisor
      decide (first.value.toList = [1,6,0,0] ∧ first.cost = 100 ∧
        second.value.toList = [2,0,0,0] ∧ second.cost = 103)

/-- info: true -/
#guard_msgs in
#eval let run := DensePolynomialStepCost.cancel divisor divisor
      decide (run.value.toList = [0,0,0,0] ∧ run.cost = 103)

/-- info: true -/
#guard_msgs in
#eval let constant : Vector (ZMod 7) 4 := ⟨#[1,0,0,0],rfl⟩
      let run := DensePolynomialStepCost.cancel numerator constant
      decide (run.value.toList = [1,0,0,0] ∧ run.cost = 97)

-- Explicit scale also supports a nonmonic divisor in the generic subtraction.
/-- info: true -/
#guard_msgs in
#eval let nonmonic : Vector (ZMod 7) 4 := ⟨#[2,2,0,0],rfl⟩
      let run := DensePolynomialStepCost.subtractShift numerator nonmonic 4 1
      decide (run.value.toList = [1,6,0,0] ∧ run.cost = 22)

-- Shifts outside the represented window copy all original coefficients.
/-- info: true -/
#guard_msgs in
#eval let run := DensePolynomialStepCost.subtractShift numerator divisor 3 9
      decide (run.value = numerator ∧ run.cost = 13)

/-- info: true -/
#guard_msgs in
#eval let run := DensePolynomialStepCost.subtractShift numerator divisor 0 0
      decide (run.value = numerator ∧ run.cost = 25)

/-- info: true -/
#guard_msgs in
#eval let empty : Vector (ZMod 7) 0 := ⟨#[],rfl⟩
      let run := DensePolynomialStepCost.cancel empty empty
      decide (run.value.toList = [] ∧ run.cost = 15)
