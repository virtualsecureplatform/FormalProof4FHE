module
public import FormalProof4FHE.HasteBoots.ParentInputHistoryCost
public import FormalProof4FHE.HasteBoots.StoredChildSeedQuote
@[expose] public section

/-! Measured complete-history parent-input candidates for a raw child input.
Discover every original parent, replay all observed SHAKE coordinates, parse the
original child seed and retain every compatible parent input. Value equality is
to the full compact ledger's active-parent input projection. Source/helper
metadata, source snapshot selection and physical refinement remain separate. -/
namespace FormalProof4FHE.HasteBoots.HistoryParentCandidatesCost
open InputIndexedOracle (Input Byte)
open NativeTranscript (Observation)
open ParentInputHistoryCost (Pool inputBytes storedBytes)
open StoredShakeByteCache (Cache)
open SolverOperationCost (Run)

def select (cache : Cache) (seed : Vector Byte 64) : Pool → Run Pool
  | [] => ⟨[],1⟩
  | input::tail =>
    let found := StoredParentSeedCheck.compatible cache input seed
    let rest := select cache seed tail
    ⟨if found.value then input::rest.value else rest.value,found.cost+rest.cost+3⟩

theorem select_value (cache : Cache) (seed : Vector Byte 64) (candidates : Pool) :
    (select cache seed candidates).value = candidates.filter (fun input =>
      ExecutableParentInputView.compatible (StoredShakeByteCache.view cache) input seed.get) := by
  induction candidates with
  | nil => rfl
  | cons head tail ih => simp only [select,StoredParentSeedCheck.compatible_value,List.filter_cons,ih]

theorem select_projection (cache : Cache) (seed : Vector Byte 64) (parents : List NativeParentLedger.Parent) :
    (select cache seed (parents.map (fun parent => parent.input))).value =
      (StoredParentSeedCheck.parents cache seed parents).value.map (fun parent => parent.input) := by
  induction parents with
  | nil => rfl
  | cons head tail ih =>
    simp only [select,StoredParentSeedCheck.parents,List.map_cons,ih]
    split <;> rfl

theorem select_cost (cache : Cache) (seed : Vector Byte 64) (candidates : Pool) :
    (select cache seed candidates).cost ≤
      64*(6*storedBytes candidates+14*candidates.length)*cache.length+454*candidates.length+1 := by
  induction candidates with
  | nil => simp [select,storedBytes]
  | cons head tail ih =>
    have checked := StoredParentSeedCheck.compatible_cost cache head seed
    simp only [select,storedBytes,List.map_cons,List.sum_cons,List.length_cons] at *
    nlinarith

def run (history : List Observation) (child : Input) : Run Pool :=
  let candidates := ParentInputHistoryCost.replay history
  let cache := StoredShakeHistory.replay history
  let quote := StoredChildSeedQuote.quote child
  match quote.value with
  | none => ⟨[],candidates.cost+cache.cost+quote.cost+5⟩
  | some seed =>
    let result := select cache.value seed candidates.value
    ⟨result.value,candidates.cost+cache.cost+quote.cost+result.cost+7⟩

theorem run_value (history : List Observation) (child : Input) :
    (run history child).value =
      (ExecutableParentLedger.active (CompactSourceHistory.reconstruct history).ledger
        (CompactSourceHistory.reconstruct history).bytes child).map (fun parent => parent.input) := by
  have quote := StoredChildSeedQuote.quote_value child
  cases parsed : (StoredChildSeedQuote.quote child).value with
  | none =>
    rw [parsed,Option.map_none] at quote
    simp only [run,parsed,ExecutableParentLedger.active,← quote,List.map_nil]
  | some seed =>
    rw [parsed,Option.map_some] at quote
    simp only [run,parsed,ParentInputHistoryCost.replay_value,ParentInputHistoryCost.projection,
      select_projection,StoredParentSeedCheck.parents_value,StoredShakeHistory.replay_eq_compact,
      ExecutableParentLedger.active,← quote]

theorem run_cost (history : List Observation) (child : Input) :
    (run history child).cost ≤
      27*inputBytes history+8*StoredShakeHistory.bytes history+
      (ParentInputHistoryCost.perObservation+459)*history.length+
      24*child.length+6*StoredChildSeedQuote.seedLabel.length+497+
      64*(6*inputBytes history+14*history.length)*StoredShakeHistory.bytes history := by
  have candidates := ParentInputHistoryCost.replay_cost history
  have cache := StoredShakeHistory.replay_cost history
  have quote := StoredChildSeedQuote.quote_cost child
  simp only [run]
  split
  · dsimp only
    nlinarith
  · rename_i seed parsed
    have checked := select_cost (StoredShakeHistory.replay history).value seed
      (ParentInputHistoryCost.replay history).value
    rw [StoredShakeHistory.replay_size] at checked
    have count := ParentInputHistoryCost.replay_count history
    have sizes := ParentInputHistoryCost.replay_storedBytes history
    have metadata :
        6*storedBytes (ParentInputHistoryCost.replay history).value+
          14*(ParentInputHistoryCost.replay history).value.length ≤ 6*inputBytes history+14*history.length := by omega
    have product := Nat.mul_le_mul_right (StoredShakeHistory.bytes history) (Nat.mul_le_mul_left 64 metadata)
    dsimp only
    nlinarith
end FormalProof4FHE.HasteBoots.HistoryParentCandidatesCost
