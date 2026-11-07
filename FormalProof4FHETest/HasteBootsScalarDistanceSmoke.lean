module
import all FormalProof4FHE.HasteBoots.ScalarDistanceCost
import all FormalProof4FHE.HasteBoots.ColumnDistanceCost
import all FormalProof4FHE.HasteBoots.SolverOperationCost
import all Mathlib.Algebra.Field.ZMod
import all Mathlib.Data.ZMod.Basic
open FormalProof4FHE.HasteBoots
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩
private def left : Vector ℕ 5 := ⟨#[0,2,0,3,0],rfl⟩
private def right : Vector ℕ 5 := ⟨#[1,2,0,4,0],rfl⟩

/-- info: true -/
#guard_msgs in
#eval let run := ScalarDistanceCost.distance left right
      decide (run.value = 2 ∧ run.cost = 37)

/-- info: true -/
#guard_msgs in
#eval let run := ScalarDistanceCost.distance left left
      decide (run.value = 0 ∧ run.cost = 37)

/-- info: true -/
#guard_msgs in
#eval let different : Vector ℕ 5 := ⟨#[1,3,1,4,1],rfl⟩
      let run := ScalarDistanceCost.distance left different
      decide (run.value = 5 ∧ run.cost = 37)

/-- info: true -/
#guard_msgs in
#eval let first := ScalarDistanceCost.norm left
      let second := ScalarDistanceCost.norm right
      decide (first.value = 2 ∧ second.value = 3 ∧ first.cost = 32 ∧ second.cost = 32)

-- Field equality, including different representatives of the same element.
/-- info: true -/
#guard_msgs in
#eval let first : Vector (ZMod 7) 2 := ⟨#[8,0],rfl⟩
      let second : Vector (ZMod 7) 2 := ⟨#[1,7],rfl⟩
      let run := ScalarDistanceCost.distance first second
      decide (run.value = 0 ∧ run.cost = 16)

/-- info: true -/
#guard_msgs in
#eval let empty : Vector ℕ 0 := ⟨#[],rfl⟩
      let distance := ScalarDistanceCost.distance empty empty
      let norm := ScalarDistanceCost.norm empty
      decide (distance.value = 0 ∧ norm.value = 0 ∧ distance.cost = 2 ∧ norm.cost = 2)
