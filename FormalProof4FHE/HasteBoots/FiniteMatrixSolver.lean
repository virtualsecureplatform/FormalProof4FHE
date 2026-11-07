module
public import FormalProof4FHE.HasteBoots.SolverOperationBounds
@[expose] public section

/-! Executable rectangular matrix solving through materialized elimination.
Input entries are read into vectors once. The returned function reads the
materialized solution; no solution is chosen by a noncomputable inverse. -/
namespace FormalProof4FHE.HasteBoots.FiniteMatrixSolver
open scoped BigOperators
open FiniteLinearSolver
variable {F : Type} [Field F] [DecidableEq F] {n m : ℕ}

def equations (matrix : Matrix (Fin n) (Fin m) F) (rhs : Fin n → F) : List (Equation F m) :=
  List.ofFn (fun row => ⟨Vector.ofFn (fun column => matrix row column),rhs row⟩)

/-- Measured elimination of the materialized equations plus one return step.
Evaluating the supplied matrix/rhs functions, constructing their equations,
backend field costs and later reads of the returned function are excluded. -/
def solveWithCost (matrix : Matrix (Fin n) (Fin m) F) (rhs : Fin n → F) : SolverOperationCost.Run (Option (Fin m → F)) :=
  let solved := SolverOperationCost.solve m (equations matrix rhs)
  ⟨solved.value.map (fun value index => value.get index),solved.cost+1⟩

def solve (matrix : Matrix (Fin n) (Fin m) F) (rhs : Fin n → F) : Option (Fin m → F) :=
  (solveWithCost matrix rhs).value

theorem solve_eq_reference (matrix : Matrix (Fin n) (Fin m) F) (rhs : Fin n → F) :
    solve matrix rhs = (FiniteLinearSolver.solve m (equations matrix rhs)).map (fun value index => value.get index) := by
  simp only [solve,solveWithCost,SolverOperationCost.solve_value]

theorem solveWithCost_bound (matrix : Matrix (Fin n) (Fin m) F) (rhs : Fin n → F) :
    (solveWithCost matrix rhs).cost ≤ 8*(n+1)*(m+1)^2+1 := by
  have bounded := SolverOperationCost.solve_cost m (equations matrix rhs)
  have length : (equations matrix rhs).length = n := by simp only [equations,List.length_ofFn]
  rw [length] at bounded
  exact Nat.add_le_add_right bounded 1

omit [DecidableEq F] in
theorem satisfies_equations (matrix : Matrix (Fin n) (Fin m) F) (rhs : Fin n → F) (value : Vector F m) :
    Satisfies (equations matrix rhs) value ↔ matrix.mulVec (fun index => value.get index) = rhs := by
  constructor
  · intro valid
    funext row
    have equation := valid ⟨Vector.ofFn (fun column => matrix row column),rhs row⟩ (List.mem_ofFn.mpr ⟨row,rfl⟩)
    simpa only [Solves,coefficient,get_ofFn,Matrix.mulVec,dotProduct] using equation
  · intro valid row present
    obtain ⟨index,rfl⟩ := List.mem_ofFn.mp present
    simpa only [Solves,coefficient,get_ofFn,Matrix.mulVec,dotProduct] using congrFun valid index

theorem solve_some (matrix : Matrix (Fin n) (Fin m) F) (rhs : Fin n → F) (value : Fin m → F)
    (solved : solve matrix rhs = some value) : matrix.mulVec value = rhs := by
  rw [solve_eq_reference] at solved
  obtain ⟨vector,vectorSolved,equal⟩ := Option.map_eq_some_iff.mp solved
  subst value
  exact (satisfies_equations matrix rhs vector).mp (FiniteLinearSolver.solve_some _ _ vectorSolved)

theorem solve_complete (matrix : Matrix (Fin n) (Fin m) F) (rhs : Fin n → F)
    (consistent : ∃ value, matrix.mulVec value = rhs) : ∃ value, solve matrix rhs = some value := by
  obtain ⟨value,valid⟩ := consistent
  have materialized : matrix.mulVec (fun index => (Vector.ofFn value).get index) = rhs := by
    simpa only [get_ofFn] using valid
  obtain ⟨vector,solved⟩ := FiniteLinearSolver.solve_complete (equations matrix rhs)
    ⟨Vector.ofFn value,(satisfies_equations _ _ _).mpr materialized⟩
  exact ⟨fun index => vector.get index,by simp only [solve_eq_reference,solved,Option.map_some]⟩

theorem solve_none (matrix : Matrix (Fin n) (Fin m) F) (rhs : Fin n → F)
    (failed : solve matrix rhs = none) : ¬∃ value, matrix.mulVec value = rhs := by
  intro consistent
  obtain ⟨value,solved⟩ := solve_complete matrix rhs consistent
  rw [failed] at solved
  contradiction
end FormalProof4FHE.HasteBoots.FiniteMatrixSolver
