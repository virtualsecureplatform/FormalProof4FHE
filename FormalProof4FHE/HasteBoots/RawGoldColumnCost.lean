module
public import FormalProof4FHE.HasteBoots.CostedMerkleWord
public import FormalProof4FHE.HasteBoots.NativeFieldRepresentation
@[expose] public section

/-! Materialize native field columns from stored raw rows. List-coordinate
reads charge every traversed cons, including padding and lazy u64 values.
Sizes are supplied interface parameters. Field interpretation, vector access,
index arithmetic and stores use the abstract operation model; physical integer,
field and compiler refinement remain separate. -/
namespace FormalProof4FHE.HasteBoots.RawGoldColumnCost
open NativeFieldRepresentation (GoldWord goldValue)
open NativeFields (Goldilocks)
open NativeLookupRequestWire (Row)
open SolverOperationCost (Run tabulate)
open scoped BigOperators

def read : List GoldWord → ℕ → Run GoldWord
  | [],_ => ⟨0,1⟩
  | head :: _,0 => ⟨head,2⟩
  | _ :: tail,index+1 => let rest := read tail index; ⟨rest.value,rest.cost+2⟩

theorem read_value (values : List GoldWord) (index : ℕ) :
    (read values index).value = values[index]?.getD 0 := by
  induction values generalizing index with
  | nil => rfl
  | cons head tail ih => cases index <;> simp only [read,List.getElem?_cons_zero,
      List.getElem?_cons_succ,Option.getD_some,ih]

theorem read_cost (values : List GoldWord) (index : ℕ) :
    (read values index).cost ≤ 2*index+2 := by
  induction values generalizing index with
  | nil => simp only [read]; omega
  | cons head tail ih =>
    cases index with
    | zero => simp only [read]; omega
    | succ index => have bound := ih index; simp only [read]; omega

def cell (values : Row) (stride row lane : ℕ) : Run Goldilocks :=
  let found := read values.val (row*stride+lane)
  ⟨goldValue found.value,found.cost+5⟩

theorem cell_value (values : Row) (stride row lane : ℕ) :
    (cell values stride row lane).value = goldValue (values.val[row*stride+lane]?.getD 0) := by
  simp only [cell,read_value]

def column (rows lanes : ℕ) (values : Row) : Run (Vector (Vector Goldilocks lanes) rows) :=
  tabulate (fun row => tabulate (fun lane => cell values lanes row.val lane.val))

theorem column_get (rows lanes : ℕ) (values : Row) (row : Fin rows) (lane : Fin lanes) :
    (((column rows lanes values).value.get row).get lane) =
      goldValue (values.val[row.val*lanes+lane.val]?.getD 0) := by
  simp only [column,SolverOperationCost.tabulate_value,FiniteLinearSolver.get_ofFn,cell_value]

theorem tabulate_bound {A : Type} {n : ℕ} (entry : Fin n → Run A) (bound : ℕ)
    (bounded : ∀ i, (entry i).cost ≤ bound) :
    (tabulate entry).cost ≤ n*(bound+1)+1 := by
  have summed := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => bounded i)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,
    SolverOperationCost.tabulate_cost,Nat.mul_add,Nat.mul_one] using Nat.add_le_add_right (Nat.add_le_add_right summed n) 1

def columnBound (rows lanes : ℕ) := rows*(lanes*(2*rows*lanes+8)+2)+1

theorem column_cost (rows lanes : ℕ) (values : Row) :
    (column rows lanes values).cost ≤ columnBound rows lanes := by
  apply tabulate_bound
  intro row
  apply tabulate_bound
  intro lane
  have found := read_cost values.val (row.val*lanes+lane.val)
  have index : row.val*lanes+lane.val < rows*lanes := by
    nlinarith [lane.isLt,Nat.mul_le_mul_right lanes (Nat.succ_le_of_lt row.isLt)]
  dsimp only [cell]
  nlinarith

def columns {rawCount : ℕ} [NeZero rawCount] (count rows lanes : ℕ)
    (raw : Vector Row rawCount) : Run (Vector (Vector (Vector Goldilocks lanes) rows) count) :=
  tabulate (fun position =>
    let result := column rows lanes (raw.get (Fin.ofNat rawCount position.val))
    ⟨result.value,result.cost+3⟩)

theorem columns_get {rawCount : ℕ} [NeZero rawCount] (count rows lanes : ℕ)
    (raw : Vector Row rawCount) (position : Fin count) (row : Fin rows) (lane : Fin lanes) :
    ((((columns count rows lanes raw).value.get position).get row).get lane) =
      goldValue ((raw.get (Fin.ofNat rawCount position.val)).val[row.val*lanes+lane.val]?.getD 0) := by
  simp only [columns,SolverOperationCost.tabulate_value,FiniteLinearSolver.get_ofFn,column_get]

theorem columns_cost {rawCount : ℕ} [NeZero rawCount] (count rows lanes : ℕ)
    (raw : Vector Row rawCount) :
    (columns count rows lanes raw).cost ≤ count*(columnBound rows lanes+4)+1 := by
  apply tabulate_bound
  intro position
  have bound := column_cost rows lanes (raw.get (Fin.ofNat rawCount position.val))
  dsimp only
  omega
end FormalProof4FHE.HasteBoots.RawGoldColumnCost
