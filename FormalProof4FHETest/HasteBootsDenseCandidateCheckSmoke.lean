module
import all FormalProof4FHE.HasteBoots.DenseCandidateCheck
import all FormalProof4FHE.HasteBoots.PolynomialShapeCost
import all FormalProof4FHE.HasteBoots.PolynomialEvaluationCost
import all FormalProof4FHE.HasteBoots.ScalarDistanceCost
import all FormalProof4FHE.HasteBoots.ColumnDistanceCost
import all FormalProof4FHE.HasteBoots.SolverOperationCost
import all Mathlib.Algebra.Field.ZMod
import all Mathlib.Data.ZMod.Basic
open FormalProof4FHE.HasteBoots
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private def candidate : Vector (ZMod 7) 4 := ⟨#[2,3,0,0],rfl⟩
private def zero : Vector (ZMod 7) 4 := ⟨#[0,0,0,0],rfl⟩
private def points : Vector (ZMod 7) 5 := Vector.ofFn (fun i => i.val)
private def received : Vector (ZMod 7) 5 := ⟨#[2,5,0,4,0],rfl⟩

/-- info: true -/
#guard_msgs in
#eval let run := DenseCandidateCheck.check 1 2 candidate zero points received
      run.value && decide (run.cost = 287)

-- The same prepared vectors fail at radius zero after the full scan.
/-- info: true -/
#guard_msgs in
#eval let run := DenseCandidateCheck.check 0 2 candidate zero points received
      !run.value && decide (run.cost = 287)

-- A nonzero remainder stops before candidate metadata and evaluations.
/-- info: true -/
#guard_msgs in
#eval let remainder : Vector (ZMod 7) 4 := ⟨#[0,0,1,0],rfl⟩
      let run := DenseCandidateCheck.check 1 2 candidate remainder points received
      !run.value && decide (run.cost = 41)

/-- info: true -/
#guard_msgs in
#eval let quadratic : Vector (ZMod 7) 4 := ⟨#[1,0,1,0],rfl⟩
      let run := DenseCandidateCheck.check 1 2 quadratic zero points received
      !run.value && decide (run.cost = 81)

/-- info: true -/
#guard_msgs in
#eval let run := DenseCandidateCheck.check 1 0 zero zero points received
      !run.value && decide (run.cost = 81)

-- Padded zero candidates keep the traversal charge of their stored width.
/-- info: true -/
#guard_msgs in
#eval let honest : Vector (ZMod 7) 5 := ⟨#[0,0,0,0,0],rfl⟩
      let run := DenseCandidateCheck.check 0 1 zero zero points honest
      run.value && decide (run.cost = 287)

/-- info: true -/
#guard_msgs in
#eval let empty : Vector (ZMod 7) 0 := ⟨#[],rfl⟩
      let accepted := DenseCandidateCheck.check 0 1 empty empty empty empty
      let rejected := DenseCandidateCheck.check 0 0 empty empty empty empty
      accepted.value && !rejected.value && decide (accepted.cost = 23 ∧ rejected.cost = 17)
