module
public import FormalProof4FHE.HasteBoots.BerlekampWelchPowers
public import FormalProof4FHE.HasteBoots.FiniteMatrixSolver
public import ArkLib.Data.CodingTheory.BerlekampWelch.Condition
@[expose] public section

/-! Materialized and measured Berlekamp–Welch system construction. Inputs are
vectors of already available field values; no matrix-entry callback is priced
as a load. Powers are shared per row. Input-vector preparation and backend field
implementation costs remain outside this abstract field/access model. -/
namespace FormalProof4FHE.HasteBoots.BerlekampWelchSystem
open SolverOperationCost
open BerlekampWelchPowers
open scoped BigOperators
variable {F : Type} [Field F] {n : ℕ}

def negate (value : Run F) : Run F := ⟨-value.value,value.cost+1⟩

def coefficient (e k : ℕ) (table : Vector F (e+k+1)) (message : F) (j : Fin (2*e+k)) : Run F :=
  if bound : j.val < e then
    let value := multiply (SolverOperationCost.pure message) (load (table.get ⟨j.val,by omega⟩))
    ⟨value.value,value.cost+1⟩
  else
    let value := negate (load (table.get ⟨j.val-e,by omega⟩))
    ⟨value.value,value.cost+1⟩

theorem coefficient_value (e k : ℕ) (point message : F) (j : Fin (2*e+k)) :
    (coefficient e k (powers point (e+k)).value message j).value =
      if j.val < e then message*point^j.val else -point^(j.val-e) := by
  unfold coefficient
  split_ifs <;> simp only [multiply,SolverOperationCost.pure,load,negate,powers_get]

theorem coefficient_cost (e k : ℕ) (table : Vector F (e+k+1)) (message : F) (j : Fin (2*e+k)) :
    (coefficient e k table message j).cost = 3 := by
  unfold coefficient
  split <;> rfl

def row (e k : ℕ) (point message : F) : Run (FiniteLinearSolver.Equation F (2*e+k)) :=
  let x := load point
  let y := load message
  let table := powers x.value (e+k)
  let coefficients := tabulate (coefficient e k table.value y.value)
  let rhs := multiply (negate (SolverOperationCost.pure y.value)) (load (table.value.get ⟨e,by omega⟩))
  ⟨⟨coefficients.value,rhs.value⟩,x.cost+y.cost+table.cost+coefficients.cost+rhs.cost+1⟩

theorem row_value (e k : ℕ) (point message : F) :
    (row e k point message).value =
      ⟨Vector.ofFn (fun j => if j.val < e then message*point^j.val else -point^(j.val-e)), -message*point^e⟩ := by
  simp only [row,load,tabulate_value,coefficient_value,multiply,negate,SolverOperationCost.pure,powers_get]

theorem row_cost (e k : ℕ) (point message : F) : (row e k point message).cost = 13*e+9*k+14 := by
  simp only [row,load,tabulate_cost,coefficient_cost,powers_cost,multiply,negate,SolverOperationCost.pure,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  omega

def build (e k : ℕ) (points received : Vector F n) : Run (List (FiniteLinearSolver.Equation F (2*e+k))) :=
  let rows := tabulate (fun i : Fin n => row e k (points.get i) (received.get i))
  ⟨rows.value.toList,rows.cost+2*n+1⟩

theorem build_value (e k : ℕ) (points received : Vector F n) :
    (build e k points received).value = FiniteMatrixSolver.equations
      (BerlekampWelch.BerlekampWelchMatrix e k (fun i => points.get i) (fun i => received.get i))
      (BerlekampWelch.Rhs e (fun i => points.get i) (fun i => received.get i)) := by
  simp only [build,tabulate_value,row_value,Vector.toList_ofFn,FiniteMatrixSolver.equations]
  congr 1
  funext i
  congr 1
  · congr 1
    funext j
    unfold BerlekampWelch.BerlekampWelchMatrix BerlekampWelch.Rhs
    split_ifs <;> simp_all

theorem build_length (e k : ℕ) (points received : Vector F n) : (build e k points received).value.length = n := by
  rw [build_value]
  simp only [FiniteMatrixSolver.equations,List.length_ofFn]

theorem build_cost (e k : ℕ) (points received : Vector F n) :
    (build e k points received).cost = n*(13*e+9*k+17)+2 := by
  simp only [build,tabulate_cost,row_cost,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring

variable [DecidableEq F]

/-- Keep the materialized solution available for subsequent reconstruction. -/
def solveVector (e k : ℕ) (points received : Vector F n) : Run (Option (Vector F (2*e+k))) :=
  let system := build e k points received
  let solved := SolverOperationCost.solve (2*e+k) system.value
  ⟨solved.value,system.cost+solved.cost⟩

def solve (e k : ℕ) (points received : Vector F n) : Run (Option (Fin (2*e+k) → F)) :=
  let solved := solveVector e k points received
  ⟨solved.value.map (fun value i => value.get i),solved.cost+1⟩

theorem solveVector_map (e k : ℕ) (points received : Vector F n) :
    (solveVector e k points received).value.map (fun value i => value.get i) = (solve e k points received).value := rfl

theorem solveVector_cost (e k : ℕ) (points received : Vector F n) :
    (solveVector e k points received).cost ≤ n*(13*e+9*k+17)+8*(n+1)*(2*e+k+1)^2+2 := by
  have eliminated := SolverOperationCost.solve_cost (2*e+k) (build e k points received).value
  rw [build_length] at eliminated
  simp only [solveVector,build_cost]
  omega

theorem solve_value (e k : ℕ) (points received : Vector F n) :
    (solve e k points received).value = FiniteMatrixSolver.solve
      (BerlekampWelch.BerlekampWelchMatrix e k (fun i => points.get i) (fun i => received.get i))
      (BerlekampWelch.Rhs e (fun i => points.get i) (fun i => received.get i)) := by
  simp only [solve,solveVector,SolverOperationCost.solve_value,build_value,FiniteMatrixSolver.solve_eq_reference]

theorem solve_cost (e k : ℕ) (points received : Vector F n) :
    (solve e k points received).cost ≤ n*(13*e+9*k+17)+8*(n+1)*(2*e+k+1)^2+3 := by
  have bound := solveVector_cost e k points received
  simp only [solve]
  omega
end FormalProof4FHE.HasteBoots.BerlekampWelchSystem
