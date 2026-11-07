module
import all FormalProof4FHE.HasteBoots.ColumnDistanceCost
import all FormalProof4FHE.HasteBoots.SolverOperationCost
open FormalProof4FHE.HasteBoots
private def original : ColumnDistanceCost.Columns ℕ 3 2 2 :=
  Vector.ofFn (fun pos => Vector.ofFn (fun row => Vector.ofFn (fun lane => pos.val+row.val+lane.val)))
private def oneColumn : ColumnDistanceCost.Columns ℕ 3 2 2 :=
  Vector.ofFn (fun pos => Vector.ofFn (fun row => Vector.ofFn (fun lane =>
    pos.val+row.val+lane.val + if pos = 1 then 1 else 0)))
private def twoColumns : ColumnDistanceCost.Columns ℕ 3 2 2 :=
  Vector.ofFn (fun pos => Vector.ofFn (fun row => Vector.ofFn (fun lane =>
    pos.val+row.val+lane.val + if (pos = 1 ∧ lane = 0) ∨ (pos = 2 ∧ lane = 1) then 1 else 0)))

/-- info: true -/
#guard_msgs in
#eval let run := ColumnDistanceCost.distance original original
      decide (run.value = 0 ∧ run.cost = 140)

-- Four unequal cells at one position count as one disagreeing column.
/-- info: true -/
#guard_msgs in
#eval let run := ColumnDistanceCost.distance original oneColumn
      decide (run.value = 1 ∧ run.cost = 140)

-- Errors split across lanes in distinct columns count as two columns.
/-- info: true -/
#guard_msgs in
#eval let run := ColumnDistanceCost.distance original twoColumns
      decide (run.value = 2 ∧ run.cost = 140)

/-- info: true -/
#guard_msgs in
#eval let empty : ColumnDistanceCost.Columns ℕ 0 2 2 := Vector.ofFn (fun i => i.elim0)
      let run := ColumnDistanceCost.distance empty empty
      decide (run.value = 0 ∧ run.cost = 2)

/-- info: true -/
#guard_msgs in
#eval let empty : ColumnDistanceCost.Columns ℕ 3 0 2 :=
        Vector.ofFn (fun _ => Vector.ofFn (fun i => i.elim0))
      let run := ColumnDistanceCost.distance empty empty
      decide (run.value = 0 ∧ run.cost = 26)

/-- info: true -/
#guard_msgs in
#eval let empty : ColumnDistanceCost.Columns ℕ 3 2 0 :=
        Vector.ofFn (fun _ => Vector.ofFn (fun _ => Vector.ofFn (fun i => i.elim0)))
      let run := ColumnDistanceCost.distance empty empty
      decide (run.value = 0 ∧ run.cost = 68)
