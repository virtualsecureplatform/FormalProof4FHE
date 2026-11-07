module
public import FormalProof4FHE.HasteBoots.SolverOperationErasure
public import Mathlib.InformationTheory.Hamming
public import Mathlib.Algebra.BigOperators.Ring.Finset
@[expose] public section

/-! Full scans of materialized columns. Every row and lane is compared; the
result counts disagreeing columns, not disagreeing cells. Charges include index
list construction, visits, Boolean operations, additions and nested loads in the
abstract access model. Input materialization and backend/physical costs are separate. -/
namespace FormalProof4FHE.HasteBoots.ColumnDistanceCost
open SolverOperationCost
open scoped BigOperators
variable {A I : Type}

def all (test : I → Run Bool) : List I → Run Bool
  | [] => ⟨true,1⟩
  | head :: rest =>
    let first := test head
    let tail := all test rest
    ⟨first.value && tail.value,first.cost+tail.cost+2⟩

theorem all_value (test : I → Run Bool) (indices : List I) :
    (all test indices).value = true ↔ ∀ i ∈ indices, (test i).value = true := by
  induction indices with
  | nil => simp [all]
  | cons head rest ih => simp [all,ih]

theorem all_cost (test : I → Run Bool) (indices : List I) (c : ℕ)
    (cost : ∀ i ∈ indices, (test i).cost = c) :
    (all test indices).cost = indices.length*(c+2)+1 := by
  induction indices with
  | nil => simp [all]
  | cons head rest ih =>
    simp only [all,List.length_cons,cost head (by simp),ih (fun i hi => cost i (by simp [hi]))]
    ring

def allIndices (n : ℕ) (test : Fin n → Run Bool) : Run Bool :=
  let scanned := all test (List.ofFn id)
  ⟨scanned.value,scanned.cost+n+1⟩

theorem allIndices_value (n : ℕ) (test : Fin n → Run Bool) :
    (allIndices n test).value = true ↔ ∀ i, (test i).value = true := by
  simp [allIndices,all_value,List.mem_ofFn]

theorem allIndices_cost (n c : ℕ) (test : Fin n → Run Bool)
    (cost : ∀ i, (test i).cost = c) :
    (allIndices n test).cost = n*(c+3)+2 := by
  have h := all_cost test (List.ofFn id) c (fun i _ => cost i)
  simp only [List.length_ofFn] at h
  simp only [allIndices,h]
  ring

def count (test : I → Run Bool) : List I → Run ℕ
  | [] => ⟨0,1⟩
  | head :: rest =>
    let first := test head
    let tail := count test rest
    ⟨(if first.value then 0 else 1)+tail.value,first.cost+tail.cost+3⟩

theorem count_value (test : I → Run Bool) (indices : List I) :
    (count test indices).value = (indices.map (fun i => if (test i).value then 0 else 1)).sum := by
  induction indices with
  | nil => rfl
  | cons head rest ih => simp only [count,List.map_cons,List.sum_cons,ih]

theorem count_cost (test : I → Run Bool) (indices : List I) (c : ℕ)
    (cost : ∀ i ∈ indices, (test i).cost = c) :
    (count test indices).cost = indices.length*(c+3)+1 := by
  induction indices with
  | nil => simp [count]
  | cons head rest ih =>
    simp only [count,List.length_cons,cost head (by simp),ih (fun i hi => cost i (by simp [hi]))]
    ring

variable [DecidableEq A] {n rows b : ℕ}
abbrev Columns (A : Type) (n rows b : ℕ) := Vector (Vector (Vector A b) rows) n

def equalRow (left right : Vector A b) : Run Bool :=
  allIndices b (fun lane => ⟨decide (left.get lane = right.get lane),3⟩)

theorem equalRow_value (left right : Vector A b) :
    (equalRow left right).value = true ↔ ∀ lane, left.get lane = right.get lane := by
  simp [equalRow,allIndices_value]

theorem equalRow_cost (left right : Vector A b) :
    (equalRow left right).cost = 6*b+2 := by
  rw [equalRow,allIndices_cost b 3 _ (fun _ => rfl)]
  omega

def equalColumn (left right : Vector (Vector A b) rows) : Run Bool :=
  allIndices rows (fun row =>
    let result := equalRow (left.get row) (right.get row)
    ⟨result.value,result.cost+2⟩)

theorem equalColumn_value (left right : Vector (Vector A b) rows) :
    (equalColumn left right).value = true ↔ ∀ row lane, (left.get row).get lane = (right.get row).get lane := by
  simp only [equalColumn,allIndices_value,equalRow_value]

theorem equalColumn_cost (left right : Vector (Vector A b) rows) :
    (equalColumn left right).cost = rows*(6*b+7)+2 := by
  rw [equalColumn,allIndices_cost rows (6*b+4) _ (by intro i; simp only [equalRow_cost])]

def equalPosition (left right : Columns A n rows b) (pos : Fin n) : Run Bool :=
  let result := equalColumn (left.get pos) (right.get pos)
  ⟨result.value,result.cost+2⟩

def word (table : Columns A n rows b) : Fin n → Fin rows → Fin b → A :=
  fun pos row lane => ((table.get pos).get row).get lane

theorem equalPosition_value (left right : Columns A n rows b) (pos : Fin n) :
    (equalPosition left right pos).value = true ↔ word left pos = word right pos := by
  simp only [equalPosition,equalColumn_value,word,funext_iff]

theorem equalPosition_cost (left right : Columns A n rows b) (pos : Fin n) :
    (equalPosition left right pos).cost = rows*(6*b+7)+4 := by
  simp only [equalPosition,equalColumn_cost]

def distance (left right : Columns A n rows b) : Run ℕ :=
  let result := count (equalPosition left right) (List.ofFn id)
  ⟨result.value,result.cost+n+1⟩

theorem distance_value (left right : Columns A n rows b) :
    (distance left right).value = hammingDist (word left) (word right) := by
  simp only [distance,count_value,List.map_ofFn,Function.comp_def,List.sum_ofFn]
  have entries (i : Fin n) :
      (if (equalPosition left right i).value then 0 else 1) =
        if word left i ≠ word right i then 1 else 0 := by
    by_cases h : word left i = word right i
    · have yes := (equalPosition_value left right i).mpr h
      simp [yes,h]
    · have no : (equalPosition left right i).value = false := by
        apply Bool.eq_false_iff.mpr
        intro yes
        exact h ((equalPosition_value left right i).mp yes)
      simp [no,h]
  simp only [entries,Finset.sum_boole,hammingDist,id_eq,Nat.cast_id]

theorem distance_cost (left right : Columns A n rows b) :
    (distance left right).cost = n*(rows*(6*b+7)+8)+2 := by
  have h := count_cost (equalPosition left right) (List.ofFn id) (rows*(6*b+7)+4)
    (fun i _ => equalPosition_cost left right i)
  simp only [List.length_ofFn] at h
  simp only [distance,h]
  ring
end FormalProof4FHE.HasteBoots.ColumnDistanceCost
