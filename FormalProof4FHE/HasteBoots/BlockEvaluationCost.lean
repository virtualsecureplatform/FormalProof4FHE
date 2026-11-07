module
public import FormalProof4FHE.HasteBoots.BerlekampWelchPowers
public import FormalProof4FHE.HasteBoots.CodeCorrespondence
@[expose] public section

/-! Measured evaluation of all rows and lanes from materialized coefficients.
Consecutive powers are shared across an entire position. Charges use the abstract
field/access model, including nested table loads and output vector stores.
Preparing input vectors and physical field/backend costs are separate. -/
namespace FormalProof4FHE.HasteBoots.BlockEvaluationCost
open SolverOperationCost
open scoped BigOperators
variable {F : Type} [Field F] {n rows m b : ℕ}

abbrev Table (F : Type) (rows m b : ℕ) := Vector (Vector (Vector F b) m) rows

def term (table : Table F rows m b) (powers : Vector F (m+1))
    (row : Fin rows) (lane : Fin b) (j : Fin m) : Run F :=
  let outer := load (table.get row)
  let inner := load (outer.value.get j)
  let coefficient := load (inner.value.get lane)
  let power := load (powers.get ⟨j.val,by omega⟩)
  let product := multiply coefficient power
  ⟨product.value,outer.cost+inner.cost+product.cost⟩

theorem term_value (table : Table F rows m b) (point : F)
    (row : Fin rows) (lane : Fin b) (j : Fin m) :
    (term table (BerlekampWelchPowers.powers point m).value row lane j).value =
      ((table.get row).get j).get lane * point ^ j.val := by
  simp only [term,load,multiply,BerlekampWelchPowers.powers_get]

theorem term_cost (table : Table F rows m b) (powers : Vector F (m+1))
    (row : Fin rows) (lane : Fin b) (j : Fin m) :
    (term table powers row lane j).cost = 5 := rfl

def position (point : F) (table : Table F rows m b) : Run (Vector (Vector F b) rows) :=
  let x := load point
  let powers := BerlekampWelchPowers.powers x.value m
  let values := tabulate (fun row : Fin rows => tabulate (fun lane : Fin b =>
    sum (term table powers.value row lane)))
  ⟨values.value,x.cost+powers.cost+values.cost⟩

theorem position_get (point : F) (table : Table F rows m b) (row : Fin rows) (lane : Fin b) :
    (((position point table).value.get row).get lane) =
      ∑ j : Fin m, ((table.get row).get j).get lane * point ^ j.val := by
  simp only [position,load,tabulate_value,FiniteLinearSolver.get_ofFn,sum,term_value]

theorem position_cost (point : F) (table : Table F rows m b) :
    (position point table).cost = 5*m+rows*(b*(6*m+2)+2)+9 := by
  simp only [position,load,BerlekampWelchPowers.powers_cost,tabulate_cost,sum,FiniteLinearSolver.get_ofFn,term_cost,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring

def evaluate (points : Vector F n) (table : Table F rows m b) :
    Run (Vector (Vector (Vector F b) rows) n) :=
  tabulate (fun pos : Fin n => position (points.get pos) table)

theorem evaluate_get (points : Vector F n) (table : Table F rows m b)
    (pos : Fin n) (row : Fin rows) (lane : Fin b) :
    ((((evaluate points table).value.get pos).get row).get lane) =
      BlockEncoder.encode (fun i => points.get i) (fun j lane => ((table.get row).get j).get lane) pos lane := by
  simp only [evaluate,tabulate_value,FiniteLinearSolver.get_ofFn,position_get,BlockEncoder.encode]

theorem evaluate_cost (points : Vector F n) (table : Table F rows m b) :
    (evaluate points table).cost = n*(5*m+rows*(b*(6*m+2)+2)+10)+1 := by
  simp only [evaluate,tabulate_cost,position_cost,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring
end FormalProof4FHE.HasteBoots.BlockEvaluationCost
