module
import all FormalProof4FHE.HasteBoots.BerlekampWelchReconstruction
import all FormalProof4FHE.HasteBoots.DensePolynomialDivision
import all FormalProof4FHE.HasteBoots.DenseMonicDivision
import all FormalProof4FHE.HasteBoots.DensePolynomialStepCost
import all FormalProof4FHE.HasteBoots.PolynomialShapeCost
import all FormalProof4FHE.HasteBoots.SolverOperationCost
import all Mathlib.Algebra.Field.ZMod
import all Mathlib.Data.ZMod.Basic
open FormalProof4FHE.HasteBoots
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

-- E=X-2, Q=E*(2+3X) for a one-error affine word.
/-- info: true -/
#guard_msgs in
#eval let solution : Vector (ZMod 7) 4 := ⟨#[5,3,3,3],rfl⟩
      let locator := BerlekampWelchReconstruction.locator 1 2 solution
      let numerator := BerlekampWelchReconstruction.numerator 1 2 solution
      let run := BerlekampWelchReconstruction.reconstruct 1 2 solution
      decide (locator.value.toList = [5,1,0,0] ∧ numerator.value.toList = [3,3,3,0] ∧
        locator.cost = 14 ∧ numerator.cost = 13 ∧ run.value.1.toList = [2,3,0,0] ∧
        run.value.2.toList = [0,0,0,0] ∧ run.cost = 597 ∧ run.cost ≤ 1356)

-- e=0 retains a constant-one locator.
/-- info: true -/
#guard_msgs in
#eval let solution : Vector (ZMod 7) 2 := ⟨#[2,3],rfl⟩
      let run := BerlekampWelchReconstruction.reconstruct 0 2 solution
      decide ((BerlekampWelchReconstruction.locator 0 2 solution).value.toList = [1,0,0] ∧
        run.value.1.toList = [2,3,0] ∧ run.value.2.toList = [0,0,0] ∧ run.cost = 477)

-- A nonzero remainder remains visible for the decoder's divisibility check.
/-- info: true -/
#guard_msgs in
#eval let solution : Vector (ZMod 7) 3 := ⟨#[5,3,3],rfl⟩
      let run := BerlekampWelchReconstruction.reconstruct 1 1 solution
      decide (run.value.1.toList = [3,0,0] ∧ run.value.2.toList = [2,0,0] ∧ run.cost = 319)

/-- info: true -/
#guard_msgs in
#eval let solution : Vector (ZMod 7) 0 := ⟨#[],rfl⟩
      let run := BerlekampWelchReconstruction.reconstruct 0 0 solution
      decide (run.value.1.toList = [0] ∧ run.value.2.toList = [0] ∧ run.cost = 82)

-- The primitive is total at k=0 even though the scalar decoder rejects that dimension.
/-- info: true -/
#guard_msgs in
#eval let solution : Vector (ZMod 7) 4 := ⟨#[1,2,3,4],rfl⟩
      let run := BerlekampWelchReconstruction.reconstruct 2 0 solution
      decide ((BerlekampWelchReconstruction.locator 2 0 solution).value.toList = [1,2,1] ∧
        run.value.1.toList = [0,0,0] ∧ run.value.2.toList = [3,4,0] ∧ run.cost = 158)
