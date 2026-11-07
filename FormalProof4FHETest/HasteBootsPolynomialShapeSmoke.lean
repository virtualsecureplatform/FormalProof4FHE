module
import all FormalProof4FHE.HasteBoots.PolynomialShapeCost
import all FormalProof4FHE.HasteBoots.SolverOperationCost
import all Mathlib.Algebra.Field.ZMod
import all Mathlib.Data.ZMod.Basic
open FormalProof4FHE.HasteBoots
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

-- Internal and trailing zeros: the last nonzero coefficient is at index 3.
/-- info: true -/
#guard_msgs in
#eval let coefficients : Vector (ZMod 7) 5 := ⟨#[0,3,0,4,0],rfl⟩
      let run := PolynomialShapeCost.inspect coefficients
      decide (run.value = (3,4) ∧ run.cost = 46 ∧ (PolynomialShapeCost.effectiveLength coefficients).value = 4)

/-- info: true -/
#guard_msgs in
#eval let coefficients : Vector (ZMod 7) 0 := ⟨#[],rfl⟩
      let run := PolynomialShapeCost.inspect coefficients
      decide (run.value = (0,0) ∧ run.cost = 6)

/-- info: true -/
#guard_msgs in
#eval let coefficients : Vector (ZMod 7) 4 := ⟨#[0,0,0,0],rfl⟩
      let run := PolynomialShapeCost.inspect coefficients
      decide (run.value = (0,0) ∧ run.cost = 38 ∧ (PolynomialShapeCost.effectiveLength coefficients).value = 0)

/-- info: true -/
#guard_msgs in
#eval let coefficients : Vector (ZMod 7) 5 := ⟨#[5,0,0,0,0],rfl⟩
      let run := PolynomialShapeCost.inspect coefficients
      decide (run.value = (0,5) ∧ run.cost = 46)

-- Field-zero representatives must not create a nonzero leading term.
/-- info: true -/
#guard_msgs in
#eval let coefficients : Vector (ZMod 7) 1 := ⟨#[7],rfl⟩
      let run := PolynomialShapeCost.inspect coefficients
      decide (run.value = (0,0) ∧ run.cost = 14)

/-- info: true -/
#guard_msgs in
#eval let coefficients : Vector (ZMod 7) 3 := ⟨#[0,0,6],rfl⟩
      let run := PolynomialShapeCost.inspect coefficients
      decide (run.value = (2,6) ∧ run.cost = 30)
