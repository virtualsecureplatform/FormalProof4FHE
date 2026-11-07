module
public import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv
public import Mathlib.Tactic
@[expose] public section

/-! Deterministic elimination over a field. Coefficients and solutions are
materialized vectors, so successive elimination stages do not build nested
coefficient-evaluation closures. Free variables are set to zero. There is no
finite-field enumeration, classical solution selection or supplied solver. -/
namespace FormalProof4FHE.HasteBoots.FiniteLinearSolver
open scoped BigOperators
variable {F : Type} [Field F] [DecidableEq F]

structure Equation (F : Type) (columns : ℕ) where
  coefficients : Vector F columns
  rhs : F

def coefficient {n : ℕ} (row : Equation F n) (index : Fin n) : F := row.coefficients.get index

def Solves {n : ℕ} (row : Equation F n) (value : Vector F n) : Prop :=
  ∑ index : Fin n, coefficient row index * value.get index = row.rhs

def Satisfies {n : ℕ} (rows : List (Equation F n)) (value : Vector F n) : Prop :=
  ∀ row ∈ rows, Solves row value

def tail {n : ℕ} (row : Equation F (n+1)) : Equation F n :=
  ⟨Vector.ofFn (fun index => coefficient row index.succ),row.rhs⟩

def suffix {n : ℕ} (value : Vector F (n+1)) : Vector F n :=
  Vector.ofFn (fun index => value.get index.succ)

def extend {n : ℕ} (head : F) (value : Vector F n) : Vector F (n+1) :=
  Vector.ofFn (Fin.cons head (fun index => value.get index))

def reduceRow {n : ℕ} (pivot row : Equation F (n+1)) : Equation F n :=
  let factor := coefficient row 0 / coefficient pivot 0
  ⟨Vector.ofFn (fun index => coefficient row index.succ-factor*coefficient pivot index.succ),
    row.rhs-factor*pivot.rhs⟩

def lift {n : ℕ} (pivot : Equation F (n+1)) (value : Vector F n) : Vector F (n+1) :=
  let head := (pivot.rhs-∑ index : Fin n, coefficient pivot index.succ*value.get index)/coefficient pivot 0
  extend head value

def findPivot {n : ℕ} : List (Equation F (n+1)) → Option (Equation F (n+1))
  | [] => none
  | row :: rest => if coefficient row 0 = 0 then findPivot rest else some row

/-- Explicit elimination, terminating by the number of variables. -/
def solve : (n : ℕ) → List (Equation F n) → Option (Vector F n)
  | 0,rows => if rows.all (fun row => decide (row.rhs = 0)) then some (Vector.ofFn Fin.elim0) else none
  | n+1,rows => match findPivot rows with
    | none => (solve n (rows.map tail)).map (extend 0)
    | some pivot => (solve n (rows.map (reduceRow pivot))).map (lift pivot)

omit [Field F] [DecidableEq F] in
@[simp] theorem get_ofFn {n : ℕ} (value : Fin n → F) (index : Fin n) :
    (Vector.ofFn value).get index = value index := by
  simp [Vector.get]
  congr 1

omit [Field F] [DecidableEq F] in
@[simp] theorem coefficient_tail {n : ℕ} (row : Equation F (n+1)) (index : Fin n) :
    coefficient (tail row) index = coefficient row index.succ := by simp [coefficient,tail]

omit [Field F] [DecidableEq F] in
@[simp] theorem get_extend_zero {n : ℕ} (head : F) (value : Vector F n) : (extend head value).get 0 = head := by
  simp [extend]
omit [Field F] [DecidableEq F] in
@[simp] theorem get_extend_succ {n : ℕ} (head : F) (value : Vector F n) (index : Fin n) :
    (extend head value).get index.succ = value.get index := by simp [extend]

@[simp] theorem findPivot_none {n : ℕ} (rows : List (Equation F (n+1))) :
    findPivot rows = none ↔ ∀ row ∈ rows, coefficient row 0 = 0 := by
  induction rows with
  | nil => simp [findPivot]
  | cons row rest ih => by_cases zero : coefficient row 0 = 0 <;> simp [findPivot,zero,ih]

theorem findPivot_some {n : ℕ} (rows : List (Equation F (n+1))) (pivot : Equation F (n+1))
    (selected : findPivot rows = some pivot) : pivot ∈ rows ∧ coefficient pivot 0 ≠ 0 := by
  induction rows with
  | nil => cases selected
  | cons row rest ih =>
    by_cases zero : coefficient row 0 = 0
    · simp only [findPivot,zero,ite_true] at selected
      obtain ⟨present,nonzero⟩ := ih selected
      exact ⟨List.mem_cons_of_mem row present,nonzero⟩
    · simp only [findPivot,zero,ite_false,Option.some.injEq] at selected
      subst pivot
      exact ⟨List.mem_cons_self,zero⟩

omit [DecidableEq F] in
theorem solves_extend {n : ℕ} (row : Equation F (n+1)) (head : F) (value : Vector F n) :
    Solves row (extend head value) ↔
      coefficient row 0*head + ∑ index : Fin n, coefficient row index.succ*value.get index = row.rhs := by
  simp only [Solves,Fin.sum_univ_succ,get_extend_zero,get_extend_succ]

omit [DecidableEq F] in
theorem zero_head {n : ℕ} (row : Equation F (n+1)) (value : Vector F (n+1))
    (zero : coefficient row 0 = 0) : Solves row value ↔ Solves (tail row) (suffix value) := by
  simp only [Solves,Fin.sum_univ_succ,zero,zero_mul,zero_add,coefficient_tail,suffix,get_ofFn]
  rfl

omit [DecidableEq F] in
theorem zero_extend {n : ℕ} (row : Equation F (n+1)) (value : Vector F n) :
    Solves row (extend 0 value) ↔ Solves (tail row) value := by
  rw [solves_extend]
  simp only [mul_zero,zero_add,Solves,coefficient_tail]
  rfl

omit [DecidableEq F] in
theorem reduce_lift {n : ℕ} (pivot row : Equation F (n+1)) (value : Vector F n) :
    Solves row (lift pivot value) ↔ Solves (reduceRow pivot row) value := by
  unfold lift
  rw [solves_extend]
  simp only [Solves,coefficient,reduceRow,get_ofFn]
  simp only [sub_mul,Finset.sum_sub_distrib,mul_assoc,← Finset.mul_sum,div_eq_mul_inv]
  constructor <;> intro h <;> linear_combination h

omit [DecidableEq F] in
theorem reconstruct {n : ℕ} (pivot : Equation F (n+1)) (value : Vector F (n+1))
    (nonzero : coefficient pivot 0 ≠ 0) (solved : Solves pivot value) : value = lift pivot (suffix value) := by
  apply Vector.ext
  intro index bounded
  have asFin : value.get ⟨index,bounded⟩ = (lift pivot (suffix value)).get ⟨index,bounded⟩ := by
    induction (⟨index,bounded⟩ : Fin (n+1)) using Fin.cases with
    | zero =>
      simp only [lift,get_extend_zero]
      apply (eq_div_iff nonzero).mpr
      simp only [Solves,Fin.sum_univ_succ] at solved
      simp only [suffix,get_ofFn]
      linear_combination solved
    | succ next => simp only [lift,get_extend_succ,suffix,get_ofFn]
  exact asFin

omit [DecidableEq F] in
theorem satisfies_map {n m : ℕ} (rows : List (Equation F n)) (change : Equation F n → Equation F m) (value : Vector F m) :
    Satisfies (rows.map change) value ↔ ∀ row ∈ rows, Solves (change row) value := by
  simp only [Satisfies,List.mem_map,forall_exists_index,and_imp,forall_apply_eq_imp_iff₂]

omit [DecidableEq F] in
theorem solves_zero (row : Equation F 0) (value : Vector F 0) : Solves row value ↔ row.rhs = 0 := by
  simp only [Solves,Fin.sum_univ_zero,eq_comm]

def Correct {n : ℕ} (rows : List (Equation F n)) : Option (Vector F n) → Prop
  | some value => Satisfies rows value
  | none => ¬∃ value, Satisfies rows value

/-- Total soundness and completeness; inconsistency is reported by `none`. -/
theorem correct (n : ℕ) (rows : List (Equation F n)) : Correct rows (solve n rows) := by
  induction n with
  | zero =>
    have base : rows.all (fun row => decide (row.rhs = 0)) = true ↔ Satisfies rows (Vector.ofFn Fin.elim0) := by
      simp only [List.all_eq_true,decide_eq_true_eq,Satisfies,solves_zero]
    by_cases good : rows.all (fun row => decide (row.rhs = 0)) = true
    · simp only [solve,good,Correct]
      exact base.mp good
    · simp only [solve,good,Correct]
      rintro ⟨value,valid⟩
      have same : value = Vector.ofFn Fin.elim0 := by apply Vector.ext; intro i bounded; omega
      rw [same] at valid
      exact good (base.mpr valid)
  | succ n ih =>
    cases selected : findPivot rows with
    | none =>
      have zeros := findPivot_none rows |>.mp selected
      have recursive := ih (rows.map tail)
      cases result : solve n (rows.map tail) with
      | none =>
        simp only [result,Correct] at recursive
        simp only [solve,selected,result,Option.map_none,Correct]
        rintro ⟨value,valid⟩
        apply recursive
        refine ⟨suffix value,(satisfies_map _ _ _).mpr ?_⟩
        intro row present
        exact (zero_head row value (zeros row present)).mp (valid row present)
      | some value =>
        simp only [result,Correct] at recursive
        simp only [solve,selected,result,Option.map_some,Correct]
        intro row present
        exact (zero_extend row value).mpr ((satisfies_map _ _ _).mp recursive row present)
    | some pivot =>
      obtain ⟨present,nonzero⟩ := findPivot_some rows pivot selected
      have recursive := ih (rows.map (reduceRow pivot))
      cases result : solve n (rows.map (reduceRow pivot)) with
      | none =>
        simp only [result,Correct] at recursive
        simp only [solve,selected,result,Option.map_none,Correct]
        rintro ⟨value,valid⟩
        apply recursive
        refine ⟨suffix value,(satisfies_map _ _ _).mpr ?_⟩
        intro row member
        have original := valid row member
        rw [reconstruct pivot value nonzero (valid pivot present)] at original
        exact (reduce_lift pivot row _).mp original
      | some value =>
        simp only [result,Correct] at recursive
        simp only [solve,selected,result,Option.map_some,Correct]
        intro row member
        exact (reduce_lift pivot row value).mpr ((satisfies_map _ _ _).mp recursive row member)

theorem solve_some {n : ℕ} (rows : List (Equation F n)) (value : Vector F n) (solved : solve n rows = some value) :
    Satisfies rows value := by
  have valid := correct n rows
  simpa only [solved,Correct] using valid

theorem solve_none {n : ℕ} (rows : List (Equation F n)) (failed : solve n rows = none) :
    ¬∃ value, Satisfies rows value := by
  have valid := correct n rows
  simpa only [failed,Correct] using valid

theorem solve_complete {n : ℕ} (rows : List (Equation F n)) (consistent : ∃ value, Satisfies rows value) :
    ∃ value, solve n rows = some value := by
  cases result : solve n rows with
  | none => exact False.elim (solve_none rows result consistent)
  | some value => exact ⟨value,rfl⟩
end FormalProof4FHE.HasteBoots.FiniteLinearSolver
