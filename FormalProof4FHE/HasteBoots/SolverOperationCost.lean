module
public import FormalProof4FHE.HasteBoots.FiniteLinearSolver
@[expose] public section

/-! An abstract operation-counting execution of the materialized field solver.
A field arithmetic operation, zero test, coefficient/rhs load, coefficient
store, or explicit structural step costs one. Vector traversals charge every
entry; list mapping charges a visit and a cons per row. This is a reference
field/access model, not a complete RAM instruction count, Lean timing or Rust
refinement.
Costs of the field implementation and construction of the input equations are
separate obligations. -/
namespace FormalProof4FHE.HasteBoots.SolverOperationCost
open scoped BigOperators
open FiniteLinearSolver (Equation coefficient)

structure Run (A : Type) where
  value : A
  cost : ℕ
  deriving Repr

variable {A B C : Type}

def pure (value : A) : Run A := ⟨value,0⟩
def load (value : A) : Run A := ⟨value,1⟩

def tabulate {n : ℕ} (entry : Fin n → Run A) : Run (Vector A n) :=
  let entries := Vector.ofFn entry
  ⟨Vector.ofFn (fun i => (entries.get i).value),(∑ i : Fin n, (entries.get i).cost)+n+1⟩

def sum {F : Type} [Field F] {n : ℕ} (entry : Fin n → Run F) : Run F :=
  let entries := Vector.ofFn entry
  ⟨∑ i : Fin n, (entries.get i).value,(∑ i : Fin n, (entries.get i).cost)+n+1⟩

def mapRows (operation : A → Run B) : List A → Run (List B)
  | [] => ⟨[],1⟩
  | head :: rest =>
    let first := operation head
    let tail := mapRows operation rest
    ⟨first.value :: tail.value,first.cost+tail.cost+2⟩

variable {F : Type} [Field F] [DecidableEq F]

def invert (input : Run F) : Run F := ⟨input.value⁻¹,input.cost+1⟩
def multiply (left right : Run F) : Run F := ⟨left.value*right.value,left.cost+right.cost+1⟩
def subtract (left right : Run F) : Run F := ⟨left.value-right.value,left.cost+right.cost+1⟩
def zeroTest (input : Run F) : Run Bool := ⟨decide (input.value = 0),input.cost+1⟩

def findPivot {n : ℕ} : List (Equation F (n+1)) → Run (Option (Equation F (n+1)))
  | [] => ⟨none,1⟩
  | head :: rest =>
    let test := zeroTest (load (coefficient head 0))
    if test.value then
      let tail := findPivot rest
      ⟨tail.value,test.cost+tail.cost+1⟩
    else ⟨some head,test.cost+1⟩

def allZero {n : ℕ} : List (Equation F n) → Run Bool
  | [] => ⟨true,1⟩
  | head :: rest =>
    let test := zeroTest (load head.rhs)
    if test.value then
      let tail := allZero rest
      ⟨tail.value,test.cost+tail.cost+1⟩
    else ⟨false,test.cost+1⟩

def tail {n : ℕ} (row : Equation F (n+1)) : Run (Equation F n) :=
  let coefficients := tabulate (fun i : Fin n => load (coefficient row i.succ))
  let rhs := load row.rhs
  ⟨⟨coefficients.value,rhs.value⟩,coefficients.cost+rhs.cost+1⟩

def reduceRow {n : ℕ} (pivot row : Equation F (n+1)) : Run (Equation F n) :=
  let factor := multiply (load (coefficient row 0)) (invert (load (coefficient pivot 0)))
  let coefficients := tabulate (fun i : Fin n => subtract (load (coefficient row i.succ))
    (multiply (pure factor.value) (load (coefficient pivot i.succ))))
  let rhs := subtract (load row.rhs) (multiply (pure factor.value) (load pivot.rhs))
  ⟨⟨coefficients.value,rhs.value⟩,factor.cost+coefficients.cost+rhs.cost+1⟩

def extend {n : ℕ} (head : F) (value : Vector F n) : Run (Vector F (n+1)) :=
  tabulate (Fin.cons (pure head) (fun i => load (value.get i)))

def lift {n : ℕ} (pivot : Equation F (n+1)) (value : Vector F n) : Run (Vector F (n+1)) :=
  let dot := sum (fun i : Fin n => multiply (load (coefficient pivot i.succ)) (load (value.get i)))
  let head := multiply (subtract (load pivot.rhs) (pure dot.value))
    (invert (load (coefficient pivot 0)))
  let result := extend head.value value
  ⟨result.value,dot.cost+head.cost+result.cost⟩

def solve : (n : ℕ) → List (Equation F n) → Run (Option (Vector F n))
  | 0,rows =>
    let checked := allZero rows
    if checked.value then
      let empty : Run (Vector F 0) := tabulate (fun i => Fin.elim0 i)
      ⟨some empty.value,checked.cost+empty.cost+2⟩
    else ⟨none,checked.cost+2⟩
  | n+1,rows =>
    let pivot := findPivot rows
    match pivot.value with
    | none =>
      let reduced := mapRows tail rows
      let recursive := solve n reduced.value
      match recursive.value with
      | none => ⟨none,pivot.cost+reduced.cost+recursive.cost+3⟩
      | some value =>
        let result := extend 0 value
        ⟨some result.value,pivot.cost+reduced.cost+recursive.cost+result.cost+3⟩
    | some pivotRow =>
      let reduced := mapRows (reduceRow pivotRow) rows
      let recursive := solve n reduced.value
      match recursive.value with
      | none => ⟨none,pivot.cost+reduced.cost+recursive.cost+3⟩
      | some value =>
        let result := lift pivotRow value
        ⟨some result.value,pivot.cost+reduced.cost+recursive.cost+result.cost+3⟩
end FormalProof4FHE.HasteBoots.SolverOperationCost
