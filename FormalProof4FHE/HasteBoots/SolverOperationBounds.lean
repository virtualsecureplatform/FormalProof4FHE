module
public import FormalProof4FHE.HasteBoots.SolverOperationErasure
@[expose] public section
namespace FormalProof4FHE.HasteBoots.SolverOperationCost
open scoped BigOperators
variable {A B : Type}

theorem mapRows_cost (operation : A → Run B) (rows : List A) (charge : ℕ)
    (exactCost : ∀ row ∈ rows, (operation row).cost = charge) :
    (mapRows operation rows).cost = rows.length * (charge+2)+1 := by
  induction rows with
  | nil => simp [mapRows]
  | cons head rest ih =>
    have headCost := exactCost head List.mem_cons_self
    have tailCost := ih (fun row present => exactCost row (List.mem_cons_of_mem head present))
    simp only [mapRows,headCost,tailCost,List.length_cons]
    ring

variable {F : Type} [Field F] [DecidableEq F]

theorem findPivot_cost {n : ℕ} (rows : List (FiniteLinearSolver.Equation F (n+1))) :
    (findPivot rows).cost ≤ 3*rows.length+1 := by
  induction rows with
  | nil => simp [findPivot]
  | cons head rest ih =>
    by_cases zero : FiniteLinearSolver.coefficient head 0 = 0 <;>
      simp [findPivot,zeroTest,load,zero] <;> omega

theorem allZero_cost {n : ℕ} (rows : List (FiniteLinearSolver.Equation F n)) :
    (allZero rows).cost ≤ 3*rows.length+1 := by
  induction rows with
  | nil => simp [allZero]
  | cons head rest ih =>
    by_cases zero : head.rhs = 0 <;>
      simp [allZero,zeroTest,load,zero] <;> omega

omit [Field F] [DecidableEq F] in
@[simp] theorem tail_cost {n : ℕ} (row : FiniteLinearSolver.Equation F (n+1)) :
    (tail row).cost = 2*n+3 := by
  simp only [tail,tabulate_cost,load,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  omega

omit [DecidableEq F] in
@[simp] theorem reduceRow_cost {n : ℕ} (pivot row : FiniteLinearSolver.Equation F (n+1)) :
    (reduceRow pivot row).cost = 5*n+10 := by
  simp only [reduceRow,tabulate_cost,multiply,subtract,invert,load,pure,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  omega

omit [Field F] [DecidableEq F] in
@[simp] theorem extend_cost {n : ℕ} (head : F) (value : Vector F n) :
    (extend head value).cost = 2*n+2 := by
  simp only [extend,tabulate_cost,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ,pure,load,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  omega

omit [DecidableEq F] in
@[simp] theorem lift_cost {n : ℕ} (pivot : FiniteLinearSolver.Equation F (n+1)) (value : Vector F n) :
    (lift pivot value).cost = 6*n+8 := by
  simp only [lift,extend_cost,sum,FiniteLinearSolver.get_ofFn,multiply,subtract,invert,load,pure,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  omega

private theorem free_step (rows columns recursive : ℕ)
    (bounded : recursive ≤ 8*(rows+1)*(columns+1)^2) :
    (3*rows+1)+(rows*(2*columns+5)+1)+recursive+(2*columns+2)+3 ≤
      8*(rows+1)*(columns+2)^2 := by
  nlinarith [Nat.zero_le (rows*columns)]

private theorem pivot_step (rows columns recursive : ℕ)
    (bounded : recursive ≤ 8*(rows+1)*(columns+1)^2) :
    (3*rows+1)+(rows*(5*columns+12)+1)+recursive+(6*columns+8)+3 ≤
      8*(rows+1)*(columns+2)^2 := by
  nlinarith [Nat.zero_le (rows*columns)]

/-- Quadratic in the column count and linear in the row count, including
rank deficiency, inconsistency and zero-dimensional systems. -/
theorem solve_cost (n : ℕ) (rows : List (FiniteLinearSolver.Equation F n)) :
    (solve n rows).cost ≤ 8*(rows.length+1)*(n+1)^2 := by
  induction n with
  | zero =>
    have checkedCost := allZero_cost rows
    simp only [solve]
    split
    · change (allZero rows).cost+1+2 ≤ 8*(rows.length+1)*(0+1)^2
      omega
    · change (allZero rows).cost+2 ≤ 8*(rows.length+1)*(0+1)^2
      omega
  | succ n ih =>
    change (solve (n+1) rows).cost ≤ 8*(rows.length+1)*(n+2)^2
    have scanned := findPivot_cost rows
    cases selected : (findPivot rows).value with
    | none =>
      have mapped : (mapRows (tail (F := F)) rows).cost = rows.length*(2*n+5)+1 :=
        mapRows_cost _ rows (2*n+3) (fun row _ => tail_cost row)
      have recursive : (solve n (mapRows tail rows).value).cost ≤ 8*(rows.length+1)*(n+1)^2 := by
        have raw := ih (mapRows tail rows).value
        have length : (mapRows tail rows).value.length = rows.length := by simp only [mapRows_value,List.length_map]
        rw [length] at raw
        exact raw
      have total := free_step rows.length n _ recursive
      cases result : (solve n (mapRows tail rows).value).value with
      | none =>
        simp only [solve,selected,result]
        omega
      | some value =>
        simp only [solve,selected,result,extend_cost]
        omega
    | some pivot =>
      have mapped : (mapRows (reduceRow pivot) rows).cost = rows.length*(5*n+12)+1 :=
        mapRows_cost _ rows (5*n+10) (fun row _ => reduceRow_cost pivot row)
      have recursive : (solve n (mapRows (reduceRow pivot) rows).value).cost ≤ 8*(rows.length+1)*(n+1)^2 := by
        have raw := ih (mapRows (reduceRow pivot) rows).value
        have length : (mapRows (reduceRow pivot) rows).value.length = rows.length := by simp only [mapRows_value,List.length_map]
        rw [length] at raw
        exact raw
      have total := pivot_step rows.length n _ recursive
      cases result : (solve n (mapRows (reduceRow pivot) rows).value).value with
      | none =>
        simp only [solve,selected,result]
        omega
      | some value =>
        simp only [solve,selected,result,lift_cost]
        omega
end FormalProof4FHE.HasteBoots.SolverOperationCost
