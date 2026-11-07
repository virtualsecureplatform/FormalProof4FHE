module
import all FormalProof4FHE.HasteBoots.DensePolynomialDivision
import all FormalProof4FHE.HasteBoots.DenseMonicDivision
import all FormalProof4FHE.HasteBoots.DensePolynomialStepCost
import all FormalProof4FHE.HasteBoots.PolynomialShapeCost
import all FormalProof4FHE.HasteBoots.SolverOperationCost
import all Mathlib.Algebra.Field.ZMod
import all Mathlib.Data.ZMod.Basic
open FormalProof4FHE.HasteBoots
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private def numerator : Vector (ZMod 7) 4 := ⟨#[1,0,1,0],rfl⟩
private def divisor : Vector (ZMod 7) 4 := ⟨#[2,2,0,0],rfl⟩

-- Nonmonic normalization and quotient rescaling: (X²+1)/(2X+2).
/-- info: true -/
#guard_msgs in
#eval let run := DensePolynomialDivision.divMod numerator divisor
      decide (run.value.1.toList = [3,4,0,0] ∧ run.value.2.toList = [2,0,0,0] ∧ run.cost = 569 ∧ run.cost ≤ 1325)

/-- info: true -/
#guard_msgs in
#eval let constant : Vector (ZMod 7) 4 := ⟨#[2,0,0,0],rfl⟩
      let run := DensePolynomialDivision.divMod numerator constant
      decide (run.value.1.toList = [4,0,4,0] ∧ run.value.2.toList = [0,0,0,0] ∧ run.cost = 566)

/-- info: true -/
#guard_msgs in
#eval let zero : Vector (ZMod 7) 4 := ⟨#[0,0,0,0],rfl⟩
      let run := DensePolynomialDivision.divMod numerator zero
      decide (run.value.1 = zero ∧ run.value.2 = numerator ∧ run.cost = 48)

/-- info: true -/
#guard_msgs in
#eval let zero : Vector (ZMod 7) 4 := ⟨#[0,0,0,0],rfl⟩
      let run := DensePolynomialDivision.divMod zero divisor
      decide (run.value.1 = zero ∧ run.value.2 = zero ∧ run.cost = 166)

/-- info: true -/
#guard_msgs in
#eval let empty : Vector (ZMod 7) 0 := ⟨#[],rfl⟩
      let run := DensePolynomialDivision.divMod empty empty
      decide (run.value.1 = empty ∧ run.value.2 = empty ∧ run.cost = 12)

/-- info: true -/
#guard_msgs in
#eval let left : Vector (ZMod 7) 1 := ⟨#[6],rfl⟩
      let right : Vector (ZMod 7) 1 := ⟨#[3],rfl⟩
      let run := DensePolynomialDivision.divMod left right
      decide (run.value.1.toList = [2] ∧ run.value.2.toList = [0] ∧ run.cost = 153)
