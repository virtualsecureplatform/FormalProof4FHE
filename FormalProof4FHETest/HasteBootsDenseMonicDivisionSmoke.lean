module
import all FormalProof4FHE.HasteBoots.DenseMonicDivision
import all FormalProof4FHE.HasteBoots.DensePolynomialStepCost
import all FormalProof4FHE.HasteBoots.PolynomialShapeCost
import all FormalProof4FHE.HasteBoots.SolverOperationCost
import all Mathlib.Algebra.Field.ZMod
import all Mathlib.Data.ZMod.Basic
open FormalProof4FHE.HasteBoots
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private def numerator : Vector (ZMod 7) 4 := ⟨#[1,0,1,0],rfl⟩
private def divisor : Vector (ZMod 7) 4 := ⟨#[1,1,0,0],rfl⟩
private def unit : Vector (ZMod 7) 4 := ⟨#[1,0,0,0],rfl⟩
private theorem divisorMonic : (PolynomialShapeCost.polynomial divisor).Monic := by
  change (PolynomialShapeCost.polynomial divisor).leadingCoeff = 1
  rw [← PolynomialShapeCost.inspect_leading]
  decide
private theorem unitMonic : (PolynomialShapeCost.polynomial unit).Monic := by
  change (PolynomialShapeCost.polynomial unit).leadingCoeff = 1
  rw [← PolynomialShapeCost.inspect_leading]
  decide
private theorem numeratorMonic : (PolynomialShapeCost.polynomial numerator).Monic := by
  change (PolynomialShapeCost.polynomial numerator).leadingCoeff = 1
  rw [← PolynomialShapeCost.inspect_leading]
  decide

-- Two cancellation rounds with accumulated quotient X-1 and remainder 2.
/-- info: true -/
#guard_msgs in
#eval let run := DenseMonicDivision.divide divisor divisorMonic numerator
      decide (run.value.1.toList = [6,1,0,0] ∧ run.value.2.toList = [2,0,0,0] ∧ run.cost = 494 ∧ run.cost ≤ 1250)

/-- info: true -/
#guard_msgs in
#eval let run := DenseMonicDivision.divide divisor divisorMonic divisor
      decide (run.value.1.toList = [1,0,0,0] ∧ run.value.2.toList = [0,0,0,0] ∧ run.cost = 294)

/-- info: true -/
#guard_msgs in
#eval let run := DenseMonicDivision.divide unit unitMonic numerator
      decide (run.value.1 = numerator ∧ run.value.2.toList = [0,0,0,0] ∧ run.cost = 491)

-- The degree condition stops before any cancellation or quotient accumulation.
/-- info: true -/
#guard_msgs in
#eval let run := DenseMonicDivision.divide numerator numeratorMonic divisor
      decide (run.value.1.toList = [0,0,0,0] ∧ run.value.2 = divisor ∧ run.cost = 91)

/-- info: true -/
#guard_msgs in
#eval let zero : Vector (ZMod 7) 4 := ⟨#[0,0,0,0],rfl⟩
      let run := DenseMonicDivision.divide divisor divisorMonic zero
      decide (run.value.1 = zero ∧ run.value.2 = zero ∧ run.cost = 91)

/-- info: true -/
#guard_msgs in
#eval let one : Vector (ZMod 7) 1 := ⟨#[1],rfl⟩
      let numerator : Vector (ZMod 7) 1 := ⟨#[3],rfl⟩
      let monic : (PolynomialShapeCost.polynomial one).Monic := by
        change (PolynomialShapeCost.polynomial one).leadingCoeff = 1
        rw [← PolynomialShapeCost.inspect_leading]
        decide
      let run := DenseMonicDivision.divide one monic numerator
      decide (run.value.1.toList = [3] ∧ run.value.2.toList = [0] ∧ run.cost = 120 ∧ run.cost ≤ 200)
