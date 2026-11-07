module
public import FormalProof4FHE.HasteBoots.StoredFrozenRequestsCost
@[expose] public section

/-! Complete causal stored parent ledger, frozen keys and SHAKE cache. Fresh
requests are returned at precisely the nonempty-output transition that freezes
them. Their hash-log snapshots are a separate component, so no final-cache or
final-log reconstruction can silently replace the original causal boundary. -/
namespace FormalProof4FHE.HasteBoots.StoredFrozenLedgerHistory
open InputIndexedOracle (Input)
open NativeTranscript (Observation)
open SolverOperationCost (Run)
open StoredSourceVectorReadCost (Source sourceView)
open StoredParentMetadataHistory (State)
open StoredFrozenRequestsCost (frozenView)
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq

structure Ledger where
  metadata : State
  frozen : List Source

structure Step where
  next : Ledger
  requests : List Source

def initial : Ledger := ⟨StoredParentMetadataHistory.initial,[]⟩

def view (state : Ledger) : CompactParentHistory.State :=
  (⟨state.metadata.parents.map StoredParentContributionsCost.view,frozenView state.frozen⟩,
    StoredShakeByteCache.view state.metadata.cache)

def record (state : Ledger) (entry : Observation) : Run Step :=
  match entry with
  | .output input _ (_::_) =>
    let plan := StoredFrozenRequestsCost.prepare state.metadata.cache state.metadata.parents state.frozen input
    let metadata := StoredParentMetadataHistory.record state.metadata entry
    ⟨⟨⟨metadata.value,plan.value.frozen⟩,plan.value.requests⟩,plan.cost+metadata.cost+4⟩
  | _ =>
    let metadata := StoredParentMetadataHistory.record state.metadata entry
    ⟨⟨⟨metadata.value,state.frozen⟩,[]⟩,metadata.cost+2⟩

theorem ledger_eq (parents : List StoredParentContributionsCost.Parent) (frozen : List Source)
    (reference : NativeParentLedger.State)
    (parentEq : parents.map StoredParentContributionsCost.view = reference.parents)
    (frozenEq : frozenView frozen = reference.frozen) :
    (⟨parents.map StoredParentContributionsCost.view,frozenView frozen⟩ : NativeParentLedger.State) = reference := by
  cases reference
  simp only [parentEq,frozenEq]

theorem record_metadata (state : Ledger) (entry : Observation) :
    (record state entry).value.next.metadata = (StoredParentMetadataHistory.record state.metadata entry).value := by
  cases entry with
  | start input => rfl
  | hash input digest => rfl
  | output input offset values => cases values <;> rfl

theorem discover_frozen (state : NativeParentLedger.State) (cache : NativeShakeCache.Cache) (input : Input) :
    (CompactParentLedger.discover state cache input).frozen = state.frozen := by
  simp only [CompactParentLedger.discover]
  split <;> rfl

theorem record_value (state : Ledger) (entry : Observation) :
    view (record state entry).value.next = CompactParentHistory.record (view state) entry := by
  have metadata := StoredParentMetadataHistory.record_related state.metadata (view state) ⟨rfl,rfl⟩ entry
  apply Prod.ext
  · apply ledger_eq
    · simpa only [record_metadata] using metadata.1
    · cases entry with
      | start input => exact (discover_frozen (view state).1 (view state).2 input).symm
      | hash input digest => exact (discover_frozen (view state).1 (view state).2 input).symm
      | output input offset values =>
        cases values with
        | nil => exact (discover_frozen (view state).1 (view state).2 input).symm
        | cons byte tail =>
          exact StoredFrozenRequestsCost.prepare_frozen state.metadata.cache state.metadata.parents state.frozen input
  · simpa only [view,record_metadata] using metadata.2

def referenceRequests (state : CompactParentHistory.State) : Observation → List NativeCanonicalLookupWire.Source
  | .output input _ (_::_) => (CompactParentLedger.prepare state.1 state.2 input).requests
  | _ => []

theorem record_requests (state : Ledger) (entry : Observation) :
    (record state entry).value.requests.map sourceView = referenceRequests (view state) entry := by
  cases entry with
  | start input => rfl
  | hash input digest => rfl
  | output input offset values =>
    cases values with
    | nil => rfl
    | cons byte tail => exact StoredFrozenRequestsCost.prepare_requests _ _ _ _

theorem record_cost (state : Ledger) (entry : Observation) :
    (record state entry).cost ≤ (StoredParentMetadataHistory.record state.metadata entry).cost+
      (match entry with
       | .output input _ (_::_) => (StoredFrozenRequestsCost.prepare state.metadata.cache state.metadata.parents state.frozen input).cost+4
       | _ => 2) := by
  cases entry with
  | start input => exact le_rfl
  | hash input digest => exact le_rfl
  | output input offset values => cases values <;> dsimp only [record] <;> omega

def loop (state : Ledger) : List Observation → Run Ledger
  | [] => ⟨state,1⟩
  | entry::tail =>
    let first := record state entry
    let rest := loop first.value.next tail
    ⟨rest.value,first.cost+rest.cost+2⟩

theorem loop_value (state : Ledger) (history : List Observation) :
    view (loop state history).value = history.foldl CompactParentHistory.record (view state) := by
  induction history generalizing state with
  | nil => rfl
  | cons entry tail ih => simp only [loop,List.foldl_cons,ih,record_value]

theorem loop_metadata (state : Ledger) (history : List Observation) :
    (loop state history).value.metadata = (StoredParentMetadataHistory.loop state.metadata history).value := by
  induction history generalizing state with
  | nil => rfl
  | cons entry tail ih => simp only [loop,StoredParentMetadataHistory.loop,ih,record_metadata]

def reconstruct (history : List Observation) : Run Ledger := loop initial history

theorem reconstruct_value (history : List Observation) :
    view (reconstruct history).value = CompactParentHistory.reconstruct history := loop_value initial history

theorem reconstruct_metadata (history : List Observation) :
    (reconstruct history).value.metadata = (StoredParentMetadataHistory.reconstruct history).value := loop_metadata initial history
theorem record_distinct (state : Ledger) (entry : Observation)
    (distinct : (state.frozen.map sourceView).Nodup) :
    ((record state entry).value.next.frozen.map sourceView).Nodup := by
  cases entry with
  | start input => exact distinct
  | hash input digest => exact distinct
  | output input offset values =>
    cases values with
    | nil => exact distinct
    | cons byte tail => exact StoredFrozenRequestsCost.prepare_distinct _ _ _ _ distinct

theorem loop_distinct (state : Ledger) (history : List Observation)
    (distinct : (state.frozen.map sourceView).Nodup) :
    ((loop state history).value.frozen.map sourceView).Nodup := by
  induction history generalizing state with
  | nil => exact distinct
  | cons entry tail ih => exact ih _ (record_distinct state entry distinct)

theorem reconstruct_distinct (history : List Observation) :
    ((reconstruct history).value.frozen.map sourceView).Nodup := loop_distinct initial history (by simp [initial])

theorem reconstruct_frozen_size (history : List Observation) :
    (reconstruct history).value.frozen.length ≤ 4*ClosedByteMachineRootBudget.inputWork history^2 := by
  have coherent := (CompactParentHistory.reconstruct_coherent history).2
  have bounded := Finset.card_le_card coherent
  have same := congrArg (fun state : CompactParentHistory.State => state.1.frozen) (reconstruct_value history)
  change frozenView (reconstruct history).value.frozen = _ at same
  rw [← same] at bounded
  simp only [frozenView,List.toFinset_card_of_nodup (reconstruct_distinct history),List.length_map] at bounded
  obtain ⟨contexts,roots⟩ := ClosedByteMachineRootBudget.observed_pools_card history
  have product := Nat.mul_le_mul contexts roots
  simp only [NativeParentLedgerPools.sources,Finset.card_product] at bounded
  nlinarith

theorem reconstruct_record_value (prior : List Observation) (entry : Observation) :
    (reconstruct (prior++[entry])).value = (record (reconstruct prior).value entry).value.next := by
  have append (state : Ledger) : (loop state (prior++[entry])).value =
      (record (loop state prior).value entry).value.next := by
    induction prior generalizing state with
    | nil => rfl
    | cons head tail ih => exact ih (record state head).value.next
  exact append initial
end FormalProof4FHE.HasteBoots.StoredFrozenLedgerHistory
