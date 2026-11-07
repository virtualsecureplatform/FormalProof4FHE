module
import all FormalProof4FHE.HasteBoots.SolverOperationCost
import all FormalProof4FHE.HasteBoots.FiniteMatrixSolver
import all FormalProof4FHE.HasteBoots.FiniteLinearSolver
import all Mathlib.Algebra.Field.ZMod
import all Mathlib.Data.ZMod.Basic
open FormalProof4FHE.HasteBoots
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

-- The first zero pivot is skipped; counters follow the successful reconstruction.
/-- info: true -/
#guard_msgs in
#eval let run := FiniteMatrixSolver.solveWithCost (![![0,1],![1,1]] : Matrix (Fin 2) (Fin 2) (ZMod 7)) ![3,5]
      match run.value with
      | some value => decide (value 0 = 2 ∧ value 1 = 3 ∧ run.cost = 108)
      | none => false

-- A free column uses extension instead of pivot reconstruction.
/-- info: true -/
#guard_msgs in
#eval let run := FiniteMatrixSolver.solveWithCost (![![0,1]] : Matrix (Fin 1) (Fin 2) (ZMod 7)) ![4]
      match run.value with
      | some value => decide (value 0 = 0 ∧ value 1 = 4 ∧ run.cost = 54)
      | none => false

-- Inconsistency stops before reconstructing any solution vector.
/-- info: true -/
#guard_msgs in
#eval let run := FiniteMatrixSolver.solveWithCost (![![1,1],![2,2]] : Matrix (Fin 2) (Fin 2) (ZMod 7)) ![1,3]
      run.value.isNone && decide (run.cost = 71)

/-- info: true -/
#guard_msgs in
#eval let run := FiniteMatrixSolver.solveWithCost (fun _ _ => 0 : Matrix (Fin 0) (Fin 0) (ZMod 7)) Fin.elim0
      run.value.isSome && decide (run.cost = 5)

/-- info: true -/
#guard_msgs in
#eval let run := FiniteMatrixSolver.solveWithCost (fun _ _ => 0 : Matrix (Fin 1) (Fin 0) (ZMod 7)) ![1]
      run.value.isNone && decide (run.cost = 6)
