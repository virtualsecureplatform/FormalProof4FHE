module
import all FormalProof4FHE.HasteBoots.DenseSourceExtraction
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
private def padded : DenseCommonSource.Table (ZMod 7) 2 2 3 :=
  Vector.ofFn (fun row => Vector.ofFn (fun j => Vector.ofFn (fun lane =>
    10*(row.val : ZMod 7)+lane.val+if j = 0 then 1 else 4)))

-- Five original coordinates drop the sixth coefficient, even when nonzero.
/-- info: true -/
#guard_msgs in
#eval let run := DenseSourceExtraction.project (size := 5) (by decide) padded
      decide ((run.value.get 0).toList = [1,2,3,4,5] ∧ (run.value.get 1).toList = [4,5,6,0,1] ∧ run.cost = 75)

/-- info: true -/
#guard_msgs in
#eval let rows : Vector (Vector (ZMod 7) 3) 4 := Vector.ofFn (fun row => Vector.ofFn (fun j => 10*(row.val : ZMod 7)+j.val))
      let run := DenseSourceExtraction.rectangular (left := 2) (packing := 2) rows
      decide (((run.value.get 0).get 0).toList = [0,3] ∧ ((run.value.get 1).get 2).toList = [1,4] ∧ run.cost = 77)

-- Packing width 2 and code width 3 stay independent through decoding/projection.
/-- info: true -/
#guard_msgs in
#eval let points : Vector (ZMod 7) 5 := Vector.ofFn (fun i => i.val)
      let raw : DenseCommonSource.Columns (ZMod 7) 5 4 3 :=
        Vector.ofFn (fun pos => Vector.ofFn (fun row => Vector.ofFn (fun lane =>
          (row.val : ZMod 7)+lane.val+1+
            (if lane.val < 2 then (row.val : ZMod 7)+lane.val+4 else 0)*(pos.val : ZMod 7)+
            if pos = 2 then 1 else 0)))
      let flat := DenseSourceExtraction.extract (m := 2) (size := 5) 1 points (by decide) raw
      let rectangular := DenseSourceExtraction.extractRectangular (m := 2) (left := 2) (packing := 2) (size := 5) 1 points (by decide) raw
      decide ((flat.value.get 0).toList = [1,2,3,4,5] ∧ (flat.value.get 3).toList = [4,5,6,0,1] ∧
        ((rectangular.value.get 1).get 4).toList = [0,1] ∧ flat.cost ≤ 39923 ∧ rectangular.cost ≤ 40049)

/-- info: true -/
#guard_msgs in
#eval let run := DenseSourceExtraction.project (size := 0) (by decide) padded
      decide ((run.value.get 0).toList = [] ∧ run.cost = 5)

/-- info: true -/
#guard_msgs in
#eval let empty : Vector (Vector (ZMod 7) 3) 0 := ⟨#[],rfl⟩
      let run := DenseSourceExtraction.rectangular (left := 2) (packing := 0) empty
      decide (((run.value.get 1).get 2).toList = [] ∧ run.cost = 17)

/-- info: true -/
#guard_msgs in
#eval let empty : Vector (Vector (ZMod 7) 3) 0 := ⟨#[],rfl⟩
      let run := DenseSourceExtraction.rectangular (left := 0) (packing := 2) empty
      decide (run.value.toList = [] ∧ run.cost = 1)
