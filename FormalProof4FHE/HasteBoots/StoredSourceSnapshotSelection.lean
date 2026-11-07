module
public import FormalProof4FHE.HasteBoots.StoredSourceSnapshotBudget
@[expose] public section

/-! Source selection by charged full context/root byte lookup in immutable marks.
The proof transports the reference's all-height checkpoint/log search; uniqueness
and coverage are derived from causal replay, not required of attacker input. -/
namespace FormalProof4FHE.HasteBoots.StoredSourceSnapshotSelection
open InputIndexedOracle (Input)
open NativeTranscript (Observation)
open SolverOperationCost (Run)
open StoredSourceVectorReadCost (Source sourceView)
open StoredSourceSnapshotHistory (Snapshot State view snapshotView expand)
open StoredGoldPublicSource (Log viewLog)
local instance : DecidableEq NativeRootMessage.Digest := NativeGoldColumnAuthentication.digestDecidableEq

def find (key : Source) : List Snapshot → Run (Option Snapshot)
  | [] => ⟨none,1⟩
  | head::tail =>
    let same := StoredMetadataCost.sourceEqual head.source key
    if same.value then ⟨some head,same.cost+3⟩
    else
      let rest := find key tail
      ⟨rest.value,same.cost+rest.cost+4⟩

theorem find_cost (key : Source) (snapshots : List Snapshot) :
    (find key snapshots).cost ≤ 1327*snapshots.length+1 := by
  induction snapshots with
  | nil => simp [find]
  | cons head tail ih =>
    have compared := StoredMetadataCost.sourceEqual_cost head.source key
    simp only [find,List.length_cons]
    split <;> dsimp only <;> omega

theorem find_some (key : Source) (snapshots : List Snapshot) (snapshot : Snapshot)
    (found : (find key snapshots).value = some snapshot) :
    snapshot ∈ snapshots ∧ sourceView snapshot.source = sourceView key := by
  induction snapshots with
  | nil => cases found
  | cons head tail ih =>
    simp only [find] at found
    split at found
    · rename_i same
      have eqSource : head.source = key := of_decide_eq_true ((StoredMetadataCost.sourceEqual_value _ _).symm.trans same)
      have eqMark := Option.some.inj found
      subst snapshot
      exact ⟨List.mem_cons_self,congrArg sourceView eqSource⟩
    · obtain ⟨member,same⟩ := ih found
      exact ⟨List.mem_cons_of_mem _ member,same⟩

theorem find_none (key : Source) (snapshots : List Snapshot)
    (found : (find key snapshots).value = none) :
    ∀ snapshot ∈ snapshots, sourceView snapshot.source ≠ sourceView key := by
  induction snapshots with
  | nil => intro snapshot member; cases member
  | cons head tail ih =>
    simp only [find] at found
    split at found
    · cases found
    · rename_i different
      intro snapshot member same
      rcases List.mem_cons.mp member with rfl | old
      · have eqSource := StoredMetadataCost.sourceView_injective same
        have eqBool : (StoredMetadataCost.sourceEqual snapshot.source key).value = true := by
          rw [StoredMetadataCost.sourceEqual_value,eqSource]
          exact decide_eq_true rfl
        exact different eqBool
      · exact ih found snapshot old same

theorem checkpoint_iff (snapshots : List Snapshot) (key : NativeCanonicalLookupWire.Source)
    (height : Fin 64) (log : ExecutableSourceHistory.Log) :
    (∃ entry ∈ snapshotView snapshots, entry.1 = (key.1,height) ∧ entry.2.root = key.2 ∧ entry.2.cumulativeLog = log) ↔
      ∃ snapshot ∈ snapshots, sourceView snapshot.source = key ∧ viewLog snapshot.log = log := by
  constructor
  · rintro ⟨entry,member,tag,root,logEq⟩
    obtain ⟨snapshot,present,entryIn⟩ := List.mem_flatMap.mp member
    obtain ⟨index,_,same⟩ := List.mem_map.mp entryIn
    subst entry
    exact ⟨snapshot,present,Prod.ext (congrArg (fun tag : NativeRootMessage.Digest × Fin 64 => tag.1) tag) root,logEq⟩
  · rintro ⟨snapshot,present,same,logEq⟩
    refine ⟨⟨(snapshot.source.1.get,height),⟨snapshot.source.2.get,viewLog snapshot.log⟩⟩,?_,?_,?_,logEq⟩
    · exact List.mem_flatMap.mpr ⟨snapshot,present,List.mem_map.mpr ⟨height,List.mem_finRange _,rfl⟩⟩
    · exact Prod.ext (congrArg (fun source : NativeCanonicalLookupWire.Source => source.1) same) rfl
    · exact congrArg Prod.snd same

theorem contains_iff (state : State) (key : NativeCanonicalLookupWire.Source) (log : ExecutableSourceHistory.Log) :
    ExecutableSourceSelection.contains (view state) key log = true ↔
      ∃ snapshot ∈ state.snapshots, sourceView snapshot.source = key ∧ viewLog snapshot.log = log := by
  simp only [ExecutableSourceSelection.contains,List.all_eq_true,List.any_eq_true,decide_eq_true_eq]
  change (∀ height ∈ List.finRange 64, ∃ entry ∈ snapshotView state.snapshots,
    entry.1 = (key.1,height) ∧ entry.2.root = key.2 ∧ entry.2.cumulativeLog = log) ↔ _
  simp only [checkpoint_iff]
  constructor
  · intro all; exact all 0 (List.mem_finRange _)
  · intro present height _; exact present

theorem unique_source (snapshots : List Snapshot)
    (distinct : (snapshots.map (fun snapshot => sourceView snapshot.source)).Nodup)
    (first last : Snapshot) (firstIn : first ∈ snapshots) (lastIn : last ∈ snapshots)
    (same : sourceView first.source = sourceView last.source) : first = last := by
  induction snapshots generalizing first last with
  | nil => cases firstIn
  | cons head tail ih =>
    have nodup := List.nodup_cons.mp distinct
    rcases List.mem_cons.mp firstIn with firstEq | firstTail
    · subst first
      rcases List.mem_cons.mp lastIn with lastEq | lastTail
      · exact lastEq.symm
      · exact False.elim (nodup.1 (List.mem_map.mpr ⟨last,lastTail,same.symm⟩))
    · rcases List.mem_cons.mp lastIn with lastEq | lastTail
      · subst last
        exact False.elim (nodup.1 (List.mem_map.mpr ⟨first,firstTail,same⟩))
      · exact ih nodup.2 first last firstTail lastTail same

theorem candidate_mem (snapshots : List Snapshot) (snapshot : Snapshot) (present : snapshot ∈ snapshots) :
    viewLog snapshot.log ∈ (snapshotView snapshots).map (fun entry => entry.2.cumulativeLog) := by
  refine List.mem_map.mpr ⟨⟨(snapshot.source.1.get,0),⟨snapshot.source.2.get,viewLog snapshot.log⟩⟩,?_,rfl⟩
  exact List.mem_flatMap.mpr ⟨snapshot,present,List.mem_map.mpr ⟨0,List.mem_finRange _,rfl⟩⟩

theorem find_unique {A : Type} (predicate : A → Bool) (values : List A) (wanted : A)
    (present : wanted ∈ values) (accepted : predicate wanted = true)
    (unique : ∀ value ∈ values, predicate value = true → value = wanted) : values.find? predicate = some wanted := by
  induction values with
  | nil => cases present
  | cons head tail ih =>
    by_cases first : predicate head = true
    · have eqHead := unique head List.mem_cons_self first
      subst head
      simp only [List.find?,accepted]
    · have inTail : wanted ∈ tail := by
        rcases List.mem_cons.mp present with rfl | old
        · exact False.elim (first accepted)
        · exact old
      simpa only [List.find?,first,ite_false] using
        ih inTail (fun value member => unique value (List.mem_cons_of_mem _ member))

def select (state : State) (key : Source) : Run Log :=
  let found := find key state.snapshots
  ⟨match found.value with | none => state.hashes | some snapshot => snapshot.log,found.cost+2⟩

theorem select_value (state : State) (key : Source)
    (keys : state.snapshots.map Snapshot.source = state.ledger.frozen)
    (distinct : (state.snapshots.map (fun snapshot => sourceView snapshot.source)).Nodup) :
    viewLog (select state key).value = ExecutableSourceSelection.select (view state) (sourceView key) := by
  cases parsed : (find key state.snapshots).value with
  | none =>
    have absent := find_none key state.snapshots parsed
    have notFrozen : sourceView key ∉ (view state).ledger.frozen := by
      change sourceView key ∉ StoredFrozenRequestsCost.frozenView state.ledger.frozen
      simp only [StoredFrozenRequestsCost.frozenView,List.mem_toFinset,← keys,List.map_map,Function.comp_def,List.mem_map]
      rintro ⟨snapshot,member,same⟩
      exact absent snapshot member same
    simp only [select,parsed,ExecutableSourceSelection.select,ite_eq_right notFrozen]
    rfl
  | some snapshot =>
    obtain ⟨present,same⟩ := find_some key state.snapshots snapshot parsed
    have frozen : sourceView key ∈ (view state).ledger.frozen := by
      change sourceView key ∈ StoredFrozenRequestsCost.frozenView state.ledger.frozen
      apply List.mem_toFinset.mpr
      rw [← keys,List.map_map]
      exact List.mem_map.mpr ⟨snapshot,present,same⟩
    have accepted := (contains_iff state (sourceView key) (viewLog snapshot.log)).mpr ⟨snapshot,present,same,rfl⟩
    have selected := find_unique (ExecutableSourceSelection.contains (view state) (sourceView key))
      ((view state).snapshots.map (fun entry => entry.2.cumulativeLog)) (viewLog snapshot.log)
      (candidate_mem state.snapshots snapshot present) accepted (by
        intro log _ matched
        obtain ⟨other,otherIn,otherKey,logEq⟩ := (contains_iff state (sourceView key) log).mp matched
        have eqMark := unique_source state.snapshots distinct other snapshot otherIn present (otherKey.trans same.symm)
        subst other
        exact logEq.symm)
    simp only [select,parsed,ExecutableSourceSelection.select,ite_eq_left frozen,selected,Option.getD_some]

theorem select_cost (state : State) (key : Source) : (select state key).cost ≤ 1327*state.snapshots.length+3 := by
  have found := find_cost key state.snapshots
  simp only [select]
  omega

theorem reconstruct_distinct (history : List Observation) :
    ((StoredSourceSnapshotHistory.reconstruct history).value.snapshots.map (fun snapshot => sourceView snapshot.source)).Nodup := by
  have frozen := StoredFrozenLedgerHistory.reconstruct_distinct history
  rw [← StoredSourceSnapshotHistory.reconstruct_ledger,← StoredSourceSnapshotHistory.reconstruct_keys] at frozen
  simpa only [List.map_map,Function.comp_def] using frozen

theorem select_reconstructed (history : List Observation) (key : Source) :
    viewLog (select (StoredSourceSnapshotHistory.reconstruct history).value key).value =
      ExecutableSourceSelection.select (CompactSourceHistory.reconstruct history) (sourceView key) := by
  rw [select_value _ _ (StoredSourceSnapshotHistory.reconstruct_keys history) (reconstruct_distinct history),
    StoredSourceSnapshotHistory.reconstruct_value]

theorem select_reconstructed_cost (history : List Observation) (key : Source) :
    (select (StoredSourceSnapshotHistory.reconstruct history).value key).cost ≤
      5308*ClosedByteMachineRootBudget.inputWork history^2+3 := by
  have bounded := select_cost (StoredSourceSnapshotHistory.reconstruct history).value key
  have size := StoredSourceSnapshotHistory.reconstruct_snapshots_size history
  omega
def run (history : List Observation) (key : Source) : Run Log :=
  let state := StoredSourceSnapshotHistory.reconstruct history
  let selected := select state.value key
  ⟨selected.value,state.cost+selected.cost+1⟩

theorem run_value (history : List Observation) (key : Source) :
    viewLog (run history key).value =
      ExecutableSourceSelection.select (ExecutableSourceHistory.reconstruct history) (sourceView key) := by
  change viewLog (select (StoredSourceSnapshotHistory.reconstruct history).value key).value = _
  rw [select_reconstructed]
  exact CompactSourceHistory.select_eq (CompactSourceHistory.reconstruct_related history) _

theorem run_cost (history : List Observation) (key : Source) :
    (run history key).cost ≤
      StoredSourceSnapshotBudget.stepBound (ClosedByteMachineRootBudget.inputWork history)
        history.length (StoredShakeHistory.bytes history)*history.length+
      5308*ClosedByteMachineRootBudget.inputWork history^2+5 := by
  have replayed := StoredSourceSnapshotBudget.reconstruct_cost history
  have selected := select_reconstructed_cost history key
  simp only [run]
  omega
end FormalProof4FHE.HasteBoots.StoredSourceSnapshotSelection
