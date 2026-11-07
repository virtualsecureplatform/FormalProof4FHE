module
public import FormalProof4FHE.HasteBoots.StoredHashLogCost
@[expose] public section

/-! Immutable stored source snapshots over the full causal hash log. Each mark
stores one complete context/root pair and shares the already immutable log.
The 64-height reference checkpoint expansion is a proof-only view. No digest
callback or reference checkpoint materialization executes in this replay. -/
namespace FormalProof4FHE.HasteBoots.StoredSourceSnapshotHistory
open InputIndexedOracle (Input)
open NativeTranscript (Observation)
open SolverOperationCost (Run)
open StoredSourceVectorReadCost (Source sourceView)
open StoredGoldPublicSource (Log viewLog)

structure Snapshot where
  source : Source
  log : Log

def expand (snapshot : Snapshot) : ExecutableSourceHistory.Snapshots :=
  (List.finRange 64).map (fun index => ⟨(snapshot.source.1.get,index),⟨snapshot.source.2.get,viewLog snapshot.log⟩⟩)

def snapshotView (snapshots : List Snapshot) : ExecutableSourceHistory.Snapshots := snapshots.flatMap expand

theorem snapshotView_append (first last : List Snapshot) :
    snapshotView (first++last) = snapshotView first++snapshotView last := List.flatMap_append

def freeze (log : Log) : List Source → Run (List Snapshot)
  | [] => ⟨[],1⟩
  | head::tail =>
    let rest := freeze log tail
    ⟨⟨head,log⟩::rest.value,rest.cost+4⟩

theorem freeze_value (log : Log) (sources : List Source) :
    (freeze log sources).value = sources.map (fun source => ⟨source,log⟩) := by
  induction sources with
  | nil => rfl
  | cons head tail ih => simp only [freeze,List.map_cons,ih]

theorem freeze_cost (log : Log) (sources : List Source) : (freeze log sources).cost = 4*sources.length+1 := by
  induction sources with
  | nil => rfl
  | cons head tail ih => simp only [freeze,List.length_cons,ih]; omega

theorem freeze_view (log : Log) (sources : List Source) :
    snapshotView (freeze log sources).value =
      (ExecutableSourceHistory.requests (sources.map sourceView)).map
        (fun request => ⟨request.1,⟨request.2,viewLog log⟩⟩) := by
  simp only [snapshotView,freeze_value,List.flatMap_map,ExecutableSourceHistory.requests,
    List.map_flatMap,List.map_map,Function.comp_def,expand,sourceView]

def append : List Snapshot → List Snapshot → Run (List Snapshot)
  | [],last => ⟨last,1⟩
  | head::tail,last =>
    let rest := append tail last
    ⟨head::rest.value,rest.cost+3⟩

theorem append_value (first last : List Snapshot) : (append first last).value = first++last := by
  induction first with
  | nil => rfl
  | cons head tail ih => simp only [append,List.cons_append,ih]

theorem append_cost (first last : List Snapshot) : (append first last).cost = 3*first.length+1 := by
  induction first with
  | nil => rfl
  | cons head tail ih => simp only [append,List.length_cons,ih]; omega

structure State where
  ledger : StoredFrozenLedgerHistory.Ledger
  hashes : Log
  snapshots : List Snapshot

def initial : State := ⟨StoredFrozenLedgerHistory.initial,[],[]⟩

def view (state : State) : ExecutableSourceHistory.State :=
  ⟨(StoredFrozenLedgerHistory.view state.ledger).1,(StoredFrozenLedgerHistory.view state.ledger).2,
    viewLog state.hashes,snapshotView state.snapshots⟩

def record (state : State) (entry : Observation) : Run State :=
  let ledger := StoredFrozenLedgerHistory.record state.ledger entry
  let marked := freeze state.hashes ledger.value.requests
  let saved := append state.snapshots marked.value
  match entry with
  | .hash input digest =>
    let hashes := StoredHashLogCost.push state.hashes input digest
    ⟨⟨ledger.value.next,hashes.value,saved.value⟩,ledger.cost+marked.cost+saved.cost+hashes.cost+5⟩
  | _ => ⟨⟨ledger.value.next,state.hashes,saved.value⟩,ledger.cost+marked.cost+saved.cost+4⟩

theorem record_ledger (state : State) (entry : Observation) :
    (record state entry).value.ledger = (StoredFrozenLedgerHistory.record state.ledger entry).value.next := by
  cases entry <;> rfl

theorem record_snapshots (state : State) (entry : Observation) :
    snapshotView (record state entry).value.snapshots = snapshotView state.snapshots ++
      (ExecutableSourceHistory.requests ((StoredFrozenLedgerHistory.record state.ledger entry).value.requests.map sourceView)).map
        (fun request => ⟨request.1,⟨request.2,viewLog state.hashes⟩⟩) := by
  cases entry <;> simp only [record,append_value,snapshotView_append,freeze_view]

theorem state_eq (first last : ExecutableSourceHistory.State)
    (ledger : first.ledger = last.ledger) (bytes : first.bytes = last.bytes)
    (hashes : first.hashes = last.hashes) (snapshots : first.snapshots = last.snapshots) : first = last := by
  cases first
  cases last
  cases ledger
  cases bytes
  cases hashes
  cases snapshots
  rfl

theorem record_value (state : State) (entry : Observation) :
    view (record state entry).value = CompactSourceHistory.record (view state) entry := by
  have ledger := StoredFrozenLedgerHistory.record_value state.ledger entry
  have reference := CompactSourceHistory.parentProjection_record (view state) entry
  have parents : (StoredFrozenLedgerHistory.view (record state entry).value.ledger).1 =
      (CompactSourceHistory.record (view state) entry).ledger := by
    rw [record_ledger,ledger]
    exact congrArg Prod.fst reference.symm
  have bytes : (StoredFrozenLedgerHistory.view (record state entry).value.ledger).2 =
      (CompactSourceHistory.record (view state) entry).bytes := by
    rw [record_ledger,ledger]
    exact congrArg Prod.snd reference.symm
  apply state_eq _ _ parents bytes
  · cases entry with
    | start input => rfl
    | hash input digest => exact StoredHashLogCost.push_value _ _ _
    | output input offset values => cases values <;> rfl
  · change snapshotView (record state entry).value.snapshots = _
    rw [record_snapshots,StoredFrozenLedgerHistory.record_requests]
    cases entry with
    | start input => simp only [StoredFrozenLedgerHistory.referenceRequests,ExecutableSourceHistory.requests,
        List.flatMap_nil,List.map_nil,List.append_nil]; rfl
    | hash input digest => simp only [StoredFrozenLedgerHistory.referenceRequests,ExecutableSourceHistory.requests,
        List.flatMap_nil,List.map_nil,List.append_nil]; rfl
    | output input offset values =>
      cases values with
      | nil => simp only [StoredFrozenLedgerHistory.referenceRequests,ExecutableSourceHistory.requests,
          List.flatMap_nil,List.map_nil,List.append_nil]; rfl
      | cons byte tail =>
        simp only [StoredFrozenLedgerHistory.referenceRequests,CompactSourceHistory.record,List.cons_ne_nil,
          ite_false,CompactSourceHistory.freezeMany_append]
        rfl

theorem record_cost (state : State) (entry : Observation) :
    (record state entry).cost ≤ (StoredFrozenLedgerHistory.record state.ledger entry).cost+
      4*(StoredFrozenLedgerHistory.record state.ledger entry).value.requests.length+
      3*state.snapshots.length+3*state.hashes.length+271 := by
  have marked := freeze_cost state.hashes (StoredFrozenLedgerHistory.record state.ledger entry).value.requests
  have saved := append_cost state.snapshots (freeze state.hashes (StoredFrozenLedgerHistory.record state.ledger entry).value.requests).value
  cases entry with
  | start input => simp only [record]; omega
  | output input offset values => simp only [record]; omega
  | hash input digest =>
    have hashes := StoredHashLogCost.push_cost state.hashes input digest
    simp only [record]
    omega

theorem record_hashes_size (state : State) (entry : Observation) :
    (record state entry).value.hashes.length ≤ state.hashes.length+1 := by
  cases entry with
  | start input => exact Nat.le_succ _
  | output input offset values => exact Nat.le_succ _
  | hash input digest =>
    simp only [record,StoredHashLogCost.push,StoredHashLogCost.append_value,List.length_append,
      List.length_cons,List.length_nil,Nat.zero_add]
    omega

theorem record_keys (state : State) (entry : Observation)
    (keys : state.snapshots.map Snapshot.source = state.ledger.frozen) :
    (record state entry).value.snapshots.map Snapshot.source = (record state entry).value.ledger.frozen := by
  have frozen : (StoredFrozenLedgerHistory.record state.ledger entry).value.next.frozen =
      state.ledger.frozen++(StoredFrozenLedgerHistory.record state.ledger entry).value.requests := by
    cases entry with
    | start input => simp only [StoredFrozenLedgerHistory.record,List.append_nil]
    | hash input digest => simp only [StoredFrozenLedgerHistory.record,List.append_nil]
    | output input offset values =>
      cases values with
      | nil => simp only [StoredFrozenLedgerHistory.record,List.append_nil]
      | cons byte tail => simp only [StoredFrozenLedgerHistory.record,StoredFrozenRequestsCost.prepare,
          StoredRegistrySourcesCost.appendSources_value]
  cases entry <;>
    simp only [record,append_value,List.map_append,freeze_value,List.map_map,Function.comp_def,keys,frozen] <;>
    exact congrArg (fun values => state.ledger.frozen++values) (List.map_id _)

def loop (state : State) : List Observation → Run State
  | [] => ⟨state,1⟩
  | entry::tail =>
    let first := record state entry
    let rest := loop first.value tail
    ⟨rest.value,first.cost+rest.cost+2⟩

theorem loop_value (state : State) (history : List Observation) :
    view (loop state history).value = history.foldl CompactSourceHistory.record (view state) := by
  induction history generalizing state with
  | nil => rfl
  | cons entry tail ih => simp only [loop,List.foldl_cons,ih,record_value]

theorem loop_ledger (state : State) (history : List Observation) :
    (loop state history).value.ledger = (StoredFrozenLedgerHistory.loop state.ledger history).value := by
  induction history generalizing state with
  | nil => rfl
  | cons entry tail ih => simp only [loop,StoredFrozenLedgerHistory.loop,ih,record_ledger]

theorem loop_keys (state : State) (history : List Observation)
    (keys : state.snapshots.map Snapshot.source = state.ledger.frozen) :
    (loop state history).value.snapshots.map Snapshot.source = (loop state history).value.ledger.frozen := by
  induction history generalizing state with
  | nil => exact keys
  | cons entry tail ih => exact ih _ (record_keys state entry keys)

theorem loop_hashes_size (state : State) (history : List Observation) :
    (loop state history).value.hashes.length ≤ state.hashes.length+history.length := by
  induction history generalizing state with
  | nil => exact le_rfl
  | cons entry tail ih =>
    have first := record_hashes_size state entry
    have rest := ih (record state entry).value
    simp only [loop,List.length_cons]
    omega

def reconstruct (history : List Observation) : Run State := loop initial history

theorem reconstruct_value (history : List Observation) :
    view (reconstruct history).value = CompactSourceHistory.reconstruct history := loop_value initial history
theorem reconstruct_ledger (history : List Observation) :
    (reconstruct history).value.ledger = (StoredFrozenLedgerHistory.reconstruct history).value := loop_ledger initial history

theorem reconstruct_keys (history : List Observation) :
    (reconstruct history).value.snapshots.map Snapshot.source = (reconstruct history).value.ledger.frozen := loop_keys initial history rfl

theorem reconstruct_snapshots_size (history : List Observation) :
    (reconstruct history).value.snapshots.length ≤ 4*ClosedByteMachineRootBudget.inputWork history^2 := by
  have keys := congrArg List.length (reconstruct_keys history)
  rw [List.length_map,reconstruct_ledger] at keys
  rw [keys]
  exact StoredFrozenLedgerHistory.reconstruct_frozen_size history

theorem reconstruct_hashes_size (history : List Observation) :
    (reconstruct history).value.hashes.length ≤ history.length := by
  simpa only [reconstruct,initial,List.length_nil,Nat.zero_add] using loop_hashes_size initial history

theorem reconstruct_record_value (prior : List Observation) (entry : Observation) :
    (reconstruct (prior++[entry])).value = (record (reconstruct prior).value entry).value := by
  have append (state : State) : (loop state (prior++[entry])).value =
      (record (loop state prior).value entry).value := by
    induction prior generalizing state with
    | nil => rfl
    | cons head tail ih => exact ih (record state head).value
  exact append initial
end FormalProof4FHE.HasteBoots.StoredSourceSnapshotHistory
