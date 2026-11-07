module
public import FormalProof4FHE.HasteBoots.SolverOperationCost
@[expose] public section
namespace FormalProof4FHE.HasteBoots.SolverOperationCost
variable {A B : Type}

@[simp] theorem tabulate_value {n : ℕ} (entry : Fin n → Run A) :
    (tabulate entry).value = Vector.ofFn (fun i => (entry i).value) := by
  simp only [tabulate,FiniteLinearSolver.get_ofFn]

@[simp] theorem tabulate_cost {n : ℕ} (entry : Fin n → Run A) :
    (tabulate entry).cost = (∑ i : Fin n, (entry i).cost)+n+1 := by
  simp only [tabulate,FiniteLinearSolver.get_ofFn]

@[simp] theorem mapRows_value (operation : A → Run B) (rows : List A) :
    (mapRows operation rows).value = rows.map (fun row => (operation row).value) := by
  induction rows with
  | nil => rfl
  | cons head rest ih => simp only [mapRows,List.map_cons,ih]

variable {F : Type} [Field F] [DecidableEq F]

@[simp] theorem findPivot_value {n : ℕ} (rows : List (FiniteLinearSolver.Equation F (n+1))) :
    (findPivot rows).value = FiniteLinearSolver.findPivot rows := by
  induction rows with
  | nil => rfl
  | cons head rest ih =>
    by_cases zero : FiniteLinearSolver.coefficient head 0 = 0 <;>
      simp [findPivot,FiniteLinearSolver.findPivot,zeroTest,load,zero,ih]

@[simp] theorem allZero_value {n : ℕ} (rows : List (FiniteLinearSolver.Equation F n)) :
    (allZero rows).value = rows.all (fun row => decide (row.rhs = 0)) := by
  induction rows with
  | nil => rfl
  | cons head rest ih =>
    by_cases zero : head.rhs = 0 <;> simp [allZero,zeroTest,load,zero,ih]

omit [Field F] [DecidableEq F] in
@[simp] theorem tail_value {n : ℕ} (row : FiniteLinearSolver.Equation F (n+1)) :
    (tail row).value = FiniteLinearSolver.tail row := by
  simp only [tail,FiniteLinearSolver.tail,tabulate_value,load]

omit [DecidableEq F] in
@[simp] theorem reduceRow_value {n : ℕ} (pivot row : FiniteLinearSolver.Equation F (n+1)) :
    (reduceRow pivot row).value = FiniteLinearSolver.reduceRow pivot row := by
  simp only [reduceRow,FiniteLinearSolver.reduceRow,tabulate_value,multiply,subtract,invert,load,pure,div_eq_mul_inv]

omit [Field F] [DecidableEq F] in
@[simp] theorem extend_value {n : ℕ} (head : F) (value : Vector F n) :
    (extend head value).value = FiniteLinearSolver.extend head value := by
  simp only [extend,FiniteLinearSolver.extend,tabulate_value]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

omit [DecidableEq F] in
@[simp] theorem lift_value {n : ℕ} (pivot : FiniteLinearSolver.Equation F (n+1)) (value : Vector F n) :
    (lift pivot value).value = FiniteLinearSolver.lift pivot value := by
  simp only [lift,FiniteLinearSolver.lift,extend_value,sum,FiniteLinearSolver.get_ofFn,multiply,subtract,invert,load,pure,div_eq_mul_inv]

/-- Forgetting counters recovers the production solver on every input. -/
@[simp] theorem solve_value (n : ℕ) (rows : List (FiniteLinearSolver.Equation F n)) :
    (solve n rows).value = FiniteLinearSolver.solve n rows := by
  induction n with
  | zero =>
    simp only [solve,FiniteLinearSolver.solve,allZero_value]
    split <;> rfl
  | succ n ih =>
    cases selected : FiniteLinearSolver.findPivot rows with
    | none =>
      simp only [solve,FiniteLinearSolver.solve,findPivot_value,selected,mapRows_value,tail_value,ih]
      cases FiniteLinearSolver.solve n (rows.map FiniteLinearSolver.tail) <;> simp
    | some pivot =>
      simp only [solve,FiniteLinearSolver.solve,findPivot_value,selected,mapRows_value,reduceRow_value,ih]
      cases FiniteLinearSolver.solve n (rows.map (FiniteLinearSolver.reduceRow pivot)) <;> simp
end FormalProof4FHE.HasteBoots.SolverOperationCost
