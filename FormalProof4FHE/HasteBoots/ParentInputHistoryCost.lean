module
public import FormalProof4FHE.HasteBoots.ParentSeedRequestCost
public import FormalProof4FHE.HasteBoots.CompactSourceHistory
@[expose] public section

/-! Complete-history discovery of every parent input, including duplicates and
unused/off-path observations. Recognition is measured. The result is exactly the
input projection of the original compact ledger; source/helper metadata replay,
physical costs and full extraction composition remain separate. -/
namespace FormalProof4FHE.HasteBoots.ParentInputHistoryCost
open InputIndexedOracle (Input)
open NativeTranscript (Observation)
open NativeParentLedgerPools (inputOf)
open SolverOperationCost (Run)

abbrev Pool := List Input

def record (saved : Pool) (entry : Observation) : Run Pool :=
  let input := inputOf entry
  let parsed := ParentSeedRequestCost.parse input
  ⟨match parsed.value with | none => saved | some _ => input::saved,parsed.cost+3⟩

def projection (state : ExecutableSourceHistory.State) : Pool :=
  state.ledger.parents.map (fun parent => parent.input)

theorem discover_inputs (state : NativeParentLedger.State) (cache : NativeShakeCache.Cache) (input : Input) :
    (CompactParentLedger.discover state cache input).parents.map (fun parent => parent.input) =
      match ExecutableParentInputView.parseParent input with
      | none => state.parents.map (fun parent => parent.input)
      | some _ => input::state.parents.map (fun parent => parent.input) := by
  cases parsed : ExecutableParentInputView.parseParent input <;>
    simp only [CompactParentLedger.discover,parsed,List.map_cons]

theorem record_value (state : ExecutableSourceHistory.State) (entry : Observation) :
    (record (projection state) entry).value = projection (CompactSourceHistory.record state entry) := by
  cases entry with
  | start input => simp only [record,inputOf,projection,CompactSourceHistory.record,discover_inputs,ParentSeedRequestCost.parse_value]
  | hash input output => simp only [record,inputOf,projection,CompactSourceHistory.record,discover_inputs,ParentSeedRequestCost.parse_value]
  | output input offset values =>
    by_cases empty : values = [] <;>
      simp only [record,inputOf,projection,CompactSourceHistory.record,CompactParentLedger.prepare,
        empty,ite_true,ite_false,discover_inputs,ParentSeedRequestCost.parse_value]

theorem record_cost (saved : Pool) (entry : Observation) :
    (record saved entry).cost ≤ 27*(inputOf entry).length+
      6*ParentSeedRequestCost.label.length+6*ParentSeedRequestCost.message.length+35 := by
  have parsed := ParentSeedRequestCost.parse_cost (inputOf entry)
  simp only [record]
  omega

def loop (saved : Pool) : List Observation → Run Pool
  | [] => ⟨saved,1⟩
  | head::tail =>
    let first := record saved head
    let rest := loop first.value tail
    ⟨rest.value,first.cost+rest.cost+2⟩

theorem loop_value (state : ExecutableSourceHistory.State) (history : List Observation) :
    (loop (projection state) history).value = projection (history.foldl CompactSourceHistory.record state) := by
  induction history generalizing state with
  | nil => rfl
  | cons head tail ih => simp only [loop,record_value,List.foldl_cons,ih]

def inputBytes (history : List Observation) : ℕ :=
  (history.map (fun entry => (inputOf entry).length)).sum

def perObservation := 6*ParentSeedRequestCost.label.length+6*ParentSeedRequestCost.message.length+37

theorem loop_cost (saved : Pool) (history : List Observation) :
    (loop saved history).cost ≤ 27*inputBytes history+perObservation*history.length+1 := by
  induction history generalizing saved with
  | nil => simp [loop,inputBytes]
  | cons head tail ih =>
    have first := record_cost saved head
    have rest := ih (record saved head).value
    simp only [loop,inputBytes,List.map_cons,List.sum_cons,List.length_cons,perObservation] at *
    nlinarith

def storedBytes (saved : Pool) : ℕ := (saved.map List.length).sum

theorem record_count (saved : Pool) (entry : Observation) :
    (record saved entry).value.length ≤ saved.length+1 := by
  simp only [record]
  split <;> simp

theorem record_storedBytes (saved : Pool) (entry : Observation) :
    storedBytes (record saved entry).value ≤ storedBytes saved+(inputOf entry).length := by
  simp only [record]
  split <;> simp only [storedBytes,List.map_cons,List.sum_cons] <;> omega

theorem loop_count (saved : Pool) (history : List Observation) :
    (loop saved history).value.length ≤ saved.length+history.length := by
  induction history generalizing saved with
  | nil => simp [loop]
  | cons head tail ih =>
    have first := record_count saved head
    have rest := ih (record saved head).value
    simp only [loop,List.length_cons]
    omega

theorem loop_storedBytes (saved : Pool) (history : List Observation) :
    storedBytes (loop saved history).value ≤ storedBytes saved+inputBytes history := by
  induction history generalizing saved with
  | nil => simp [loop,inputBytes]
  | cons head tail ih =>
    have first := record_storedBytes saved head
    have rest := ih (record saved head).value
    simp only [loop,inputBytes,List.map_cons,List.sum_cons] at *
    omega

def replay (history : List Observation) : Run Pool := loop [] history

theorem replay_value (history : List Observation) :
    (replay history).value = projection (CompactSourceHistory.reconstruct history) :=
  loop_value ExecutableSourceHistory.initial history

theorem replay_cost (history : List Observation) :
    (replay history).cost ≤ 27*inputBytes history+perObservation*history.length+1 := loop_cost [] history

theorem replay_count (history : List Observation) : (replay history).value.length ≤ history.length := by
  simpa only [replay,List.length_nil,Nat.zero_add] using loop_count [] history

theorem replay_storedBytes (history : List Observation) : storedBytes (replay history).value ≤ inputBytes history := by
  simpa only [replay,storedBytes,List.map_nil,List.sum_nil,Nat.zero_add] using loop_storedBytes [] history
end FormalProof4FHE.HasteBoots.ParentInputHistoryCost
