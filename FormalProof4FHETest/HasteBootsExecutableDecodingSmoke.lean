module
import all FormalProof4FHE.HasteBoots.FiniteMatrixSolver
import all FormalProof4FHE.HasteBoots.FiniteLinearSolver
import all Mathlib.Data.ZMod.Basic
import all Mathlib.Algebra.Field.ZMod
open FormalProof4FHE.HasteBoots
private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private def matrix : Matrix (Fin 2) (Fin 2) (ZMod 7) := ![![0,1],![1,1]]
private def rhs : Fin 2 → ZMod 7 := ![3,5]

/-- info: true -/
#guard_msgs in
#eval match FiniteMatrixSolver.solve matrix rhs with
  | some value => decide (value 0 = 2 ∧ value 1 = 3)
  | none => false

-- Dependent equations with conflicting right hand sides.
/-- info: true -/
#guard_msgs in
#eval (FiniteMatrixSolver.solve (![![1,1],![2,2]] : Matrix (Fin 2) (Fin 2) (ZMod 7)) ![1,3]).isNone

-- A free column is set to zero.
/-- info: true -/
#guard_msgs in
#eval match FiniteMatrixSolver.solve (![![0,1]] : Matrix (Fin 1) (Fin 2) (ZMod 7)) ![4] with
  | some value => decide (value 0 = 0 ∧ value 1 = 4)
  | none => false

/-- info: true -/
#guard_msgs in
#eval (FiniteMatrixSolver.solve (fun _ _ => 0 : Matrix (Fin 0) (Fin 0) (ZMod 7)) Fin.elim0).isSome

/-- info: true -/
#guard_msgs in
#eval (FiniteMatrixSolver.solve (fun _ _ => 0 : Matrix (Fin 1) (Fin 0) (ZMod 7)) ![1]).isNone

