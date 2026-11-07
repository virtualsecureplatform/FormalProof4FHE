module
public import FormalProof4FHE.HasteBoots.StoredSourceSnapshotSelection
@[expose] public section

/-! Charged recovery of the full mixed history before a stream's first positive
read. Any offset counts. Starts, hashes and empty reads are retained as data,
without querying an oracle or invoking a functional stream/cache callback. -/
namespace FormalProof4FHE.HasteBoots.CausalPrefixReadCost
open InputIndexedOracle (Input)
open NativeTranscript (Observation)
open SolverOperationCost (Run)

def touches (input : Input) : Observation → Run Bool
  | .output other _ (_::_) =>
    let same := BytePrefixMatchCost.equal other input
    ⟨same.value,same.cost+3⟩
  | .output _ _ [] => ⟨false,2⟩
  | _ => ⟨false,1⟩

theorem touches_value (input : Input) (entry : Observation) :
    (touches input entry).value = CausalStreamExposure.touches input entry := by
  cases entry with
  | start other => rfl
  | hash other digest => rfl
  | output other offset values =>
    cases values with
    | nil => simp only [touches,CausalStreamExposure.touches,List.length_nil,Nat.lt_irrefl,and_false,decide_false]
    | cons head tail => simp only [touches,BytePrefixMatchCost.equal_value,CausalStreamExposure.touches,
        List.length_cons,Nat.zero_lt_succ,and_true]

theorem touches_cost (input : Input) (entry : Observation) : (touches input entry).cost ≤ 6*input.length+12 := by
  cases entry with
  | start other => simp only [touches]; omega
  | hash other digest => simp only [touches]; omega
  | output other offset values =>
    cases values with
    | nil => simp only [touches]; omega
    | cons head tail =>
      have same := BytePrefixMatchCost.equal_cost other input
      have width := Nat.min_le_right other.length input.length
      simp only [touches]
      omega

def recover (input : Input) : List Observation → Run (Option (List Observation))
  | [] => ⟨none,1⟩
  | entry::tail =>
    let touched := touches input entry
    if touched.value then ⟨some [],touched.cost+3⟩
    else
      let rest := recover input tail
      ⟨rest.value.map (entry::·),touched.cost+rest.cost+4⟩

theorem reference_cons (input : Input) (entry : Observation) (tail : List Observation) :
    CausalFirstStreamPrefix.recover input (entry::tail) =
      if CausalStreamExposure.touches input entry then some []
      else (CausalFirstStreamPrefix.recover input tail).map (entry::·) := by
  cases touched : CausalStreamExposure.touches input entry <;>
    cases located : CausalStreamCoverage.locate input tail <;>
    simp only [CausalFirstStreamPrefix.recover,CausalStreamCoverage.locate,touched,located,
      Bool.false_eq_true,ite_false,ite_true,Option.map_none,Option.map_some,List.take_zero,List.take_succ_cons]

theorem recover_value (input : Input) (history : List Observation) :
    (recover input history).value = CausalFirstStreamPrefix.recover input history := by
  induction history with
  | nil => rfl
  | cons entry tail ih => simp only [recover,touches_value,reference_cons,ih]; split <;> rfl

theorem recover_cost (input : Input) (history : List Observation) :
    (recover input history).cost ≤ (6*input.length+16)*history.length+1 := by
  induction history with
  | nil => simp [recover]
  | cons entry tail ih =>
    have touched := touches_cost input entry
    simp only [recover,List.length_cons]
    split <;> dsimp only <;> nlinarith

theorem recover_sound (input : Input) (history before : List Observation)
    (found : (recover input history).value = some before) :
    CausalStreamExposure.seen before input = false ∧ ∃ offset values after,
      values ≠ [] ∧ history = before++ .output input offset values :: after := by
  rw [recover_value] at found
  exact CausalFirstStreamPrefix.recover_sound _ _ _ found

theorem recover_at (input : Input) (before after : List Observation) (entry : Observation)
    (unseen : CausalStreamExposure.seen before input = false) (hit : CausalStreamExposure.touches input entry = true) :
    (recover input (before++entry::after)).value = some before := by
  rw [recover_value]
  exact CausalFirstStreamPrefix.recover_at _ _ _ _ unseen hit

theorem recover_append (input : Input) (history later before : List Observation)
    (found : (recover input history).value = some before) :
    (recover input (history++later)).value = some before := by
  rw [recover_value] at found ⊢
  exact CausalFirstStreamPrefix.recover_append _ _ _ _ found
end FormalProof4FHE.HasteBoots.CausalPrefixReadCost
