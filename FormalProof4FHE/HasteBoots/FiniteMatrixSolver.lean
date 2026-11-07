module
public import FormalProof4FHE.HasteBoots.FiniteLinearSolver
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

def solve (matrix : Matrix (Fin n) (Fin m) F) (rhs : Fin n → F) : Option (Fin m → F) :=
  (FiniteLinearSolver.solve m (equations matrix rhs)).map (fun value index => value.get index)

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
  unfold solve at solved
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
  exact ⟨fun index => vector.get index,by simp only [solve,solved,Option.map_some]⟩

theorem solve_none (matrix : Matrix (Fin n) (Fin m) F) (rhs : Fin n → F)
    (failed : solve matrix rhs = none) : ¬∃ value, matrix.mulVec value = rhs := by
  intro consistent
  obtain ⟨value,solved⟩ := solve_complete matrix rhs consistent
  rw [failed] at solved
  contradiction
end FormalProof4FHE.HasteBoots.FiniteMatrixSolver
