module
public import FormalProof4FHE.HasteBoots.CompactParentHistory
public import FormalProof4FHE.HasteBoots.CompactParentWorkStorage
public import FormalProof4FHE.HasteBoots.ExecutableSourceSelection
@[expose] public section
namespace FormalProof4FHE.HasteBoots.CompactSourceHistory
open InputIndexedOracle (Input)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open ExecutableSourceHistory (State Log Snapshots freezeMany requests)
open NativeMerkleShapeFamily (Tag)
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

/-! Complete source replay with compact inherited parent metadata. Requests
can be permuted, but each step freezes one common log. Consequently snapshot
membership and the ordered candidate-log sequence are both preserved. -/
def record (state : State) : Observation → State
  | .start input => {state with ledger := CompactParentLedger.discover state.ledger state.bytes input}
  | .hash input digest => {state with
      ledger := CompactParentLedger.discover state.ledger state.bytes input
      hashes := state.hashes ++ [⟨input,JointHashCache.decode digest⟩]}
  | .output input offset values =>
    if values = [] then {state with ledger := CompactParentLedger.discover state.ledger state.bytes input}
    else
      let plan := CompactParentLedger.prepare state.ledger state.bytes input
      { ledger := plan.next
        bytes := ExecutableSourceHistory.writeBytes state.bytes input offset values
        hashes := state.hashes
        snapshots := freezeMany state.hashes (requests plan.requests) state.snapshots }

def reconstruct (history : List Observation) : State := history.foldl record ExecutableSourceHistory.initial

def parentProjection (state : State) : CompactParentHistory.State := (state.ledger,state.bytes)

structure Related (compact reference : State) : Prop where
  parents : CompactParentHistory.Related (parentProjection compact) reference
  hashes : compact.hashes = reference.hashes
  snapshots : compact.snapshots.Perm reference.snapshots
  logs : compact.snapshots.map (fun entry => entry.2.cumulativeLog) = reference.snapshots.map (fun entry => entry.2.cumulativeLog)

theorem parentProjection_record (state : State) (entry : Observation) :
    parentProjection (record state entry) = CompactParentHistory.record (parentProjection state) entry := by
  cases entry with
  | start input => rfl
  | hash input digest => rfl
  | output input offset values =>
    by_cases empty : values = []
    · subst values; rfl
    · simp only [parentProjection,record,CompactParentHistory.record,empty,ite_false]

theorem freezeMany_append (log : Log) (roots : List (Tag × Digest)) (snapshots : Snapshots) :
    freezeMany log roots snapshots = snapshots ++ roots.map (fun root => ⟨root.1,⟨root.2,log⟩⟩) := by
  induction roots generalizing snapshots with
  | nil => simp [freezeMany]
  | cons root rest ih => simp only [freezeMany,ih,List.map_cons,List.append_assoc,List.singleton_append]

theorem freezeMany_perm (log : Log) {left right : List (Tag × Digest)} (roots : left.Perm right)
    {first last : Snapshots} (snapshots : first.Perm last) :
    (freezeMany log left first).Perm (freezeMany log right last) := by
  rw [freezeMany_append,freezeMany_append]
  exact snapshots.append (roots.map _)

theorem freezeMany_logs (log : Log) (roots : List (Tag × Digest)) (snapshots : Snapshots) :
    (freezeMany log roots snapshots).map (fun entry => entry.2.cumulativeLog) =
      snapshots.map (fun entry => entry.2.cumulativeLog) ++ List.replicate roots.length log := by
  rw [freezeMany_append,List.map_append,List.map_map]
  simp only [Function.comp_def]
  congr 1
  induction roots <;> simp_all [List.replicate_succ]

theorem record_related (compact reference : State) (related : Related compact reference) (entry : Observation) :
    Related (record compact entry) (ExecutableSourceHistory.record reference entry) := by
  have cache : compact.bytes = reference.bytes := related.parents.2
  have parents : CompactParentHistory.Related (parentProjection (record compact entry))
      (ExecutableSourceHistory.record reference entry) := by
    rw [parentProjection_record]
    exact CompactParentHistory.record_related _ _ related.parents entry
  refine ⟨parents,?_,?_,?_⟩
  · cases entry with
    | start input => exact related.hashes
    | hash input digest => simp only [record,ExecutableSourceHistory.record,related.hashes]
    | output input offset values =>
      by_cases empty : values = [] <;> simp only [record,ExecutableSourceHistory.record,empty,ite_true,ite_false,related.hashes]
  · cases entry with
    | start input => exact related.snapshots
    | hash input digest => exact related.snapshots
    | output input offset values =>
      by_cases empty : values = []
      · simpa only [record,ExecutableSourceHistory.record,empty,ite_true] using related.snapshots
      · have keys := CompactParentLedger.requests_perm related.parents.1 reference.bytes input
        have roots := keys.flatMap_right (fun key => (List.finRange 64).map (fun index => ((key.1,index),key.2)))
        simp only [record,ExecutableSourceHistory.record,empty,ite_false,related.hashes,cache]
        exact freezeMany_perm _ roots related.snapshots
  · cases entry with
    | start input => exact related.logs
    | hash input digest => exact related.logs
    | output input offset values =>
      by_cases empty : values = []
      · simpa only [record,ExecutableSourceHistory.record,empty,ite_true] using related.logs
      · have keys := CompactParentLedger.requests_perm related.parents.1 reference.bytes input
        have roots := keys.flatMap_right (fun key => (List.finRange 64).map (fun index => ((key.1,index),key.2)))
        simp only [record,ExecutableSourceHistory.record,empty,ite_false,related.hashes,cache,
          freezeMany_logs,related.logs]
        have count : (requests (CompactParentLedger.prepare compact.ledger reference.bytes input).requests).length =
            (requests (ExecutableParentLedger.prepare reference.ledger reference.bytes input).requests).length := roots.length_eq
        rw [count]

theorem reconstruct_related (history : List Observation) : Related (reconstruct history) (ExecutableSourceHistory.reconstruct history) := by
  have fold (compact reference : State) (related : Related compact reference) :
      Related (history.foldl record compact) (history.foldl ExecutableSourceHistory.record reference) := by
    induction history generalizing compact reference with
    | nil => exact related
    | cons entry rest ih => exact ih _ _ (record_related compact reference related entry)
  exact fold _ _ ⟨⟨CompactParentLedger.related_refl _,rfl⟩,rfl,List.Perm.refl _,rfl⟩

theorem parentProjection_reconstruct (history : List Observation) :
    parentProjection (reconstruct history) = CompactParentHistory.reconstruct history := by
  have fold (state : State) : parentProjection (history.foldl record state) = history.foldl CompactParentHistory.record (parentProjection state) := by
    induction history generalizing state with
    | nil => rfl
    | cons entry rest ih =>
      simp only [List.foldl_cons,ih,parentProjection_record]
  exact fold _

theorem metadataSize_le_inputWork (history : List Observation) :
    CompactParentLedger.metadataSize (reconstruct history).ledger ≤ history.length *
      (4 * ClosedByteMachineRootBudget.inputWork history ^ 2 + 2 * ClosedByteMachineRootBudget.inputWork history) := by
  have bounded := CompactParentHistory.metadataSize_le_inputWork history
  change CompactParentLedger.metadataSize (parentProjection (reconstruct history)).1 ≤ _
  rw [parentProjection_reconstruct]
  exact bounded

theorem metadataSize_le_work (code : List ClosedByteMachine.Instruction) (publicData : Input) (fuel : ℕ) (state : ClosedByteMachine.State) (world : InputIndexedOracle.World) :
    CompactParentLedger.metadataSize
      (reconstruct (OracleProgram.run (ClosedByteMachine.take code publicData fuel state) world).run.2).ledger ≤
      (OracleProgram.run (ClosedByteMachine.take code publicData fuel state) world).run.1.work *
        (4 * (OracleProgram.run (ClosedByteMachine.take code publicData fuel state) world).run.1.work ^ 2 +
          2 * (OracleProgram.run (ClosedByteMachine.take code publicData fuel state) world).run.1.work) := by
  change CompactParentLedger.metadataSize (parentProjection (reconstruct
    (OracleProgram.run (ClosedByteMachine.take code publicData fuel state) world).run.2)).1 ≤ _
  rw [parentProjection_reconstruct]
  exact CompactParentWorkStorage.metadataSize_le_work code publicData fuel state world

theorem contains_eq {compact reference : State} (related : Related compact reference)
    (key : NativeCanonicalLookupWire.Source) (log : Log) :
    ExecutableSourceSelection.contains compact key log = ExecutableSourceSelection.contains reference key log := by
  unfold ExecutableSourceSelection.contains
  congr 1
  funext index
  exact related.snapshots.any_eq

theorem select_eq {compact reference : State} (related : Related compact reference) (key : NativeCanonicalLookupWire.Source) :
    ExecutableSourceSelection.select compact key = ExecutableSourceSelection.select reference key := by
  have predicates : ExecutableSourceSelection.contains compact key = ExecutableSourceSelection.contains reference key := by
    funext log; exact contains_eq related key log
  have frozen : compact.ledger.frozen = reference.ledger.frozen := related.parents.1.frozen
  simp only [ExecutableSourceSelection.select,frozen,related.hashes,related.logs,predicates]

def selected (before : List Observation) (field : NativeGoldBatchFieldInputView.View) : Log :=
  ExecutableSourceSelection.select (reconstruct before) (field.data.context,field.data.root)

theorem selected_eq (before : List Observation) (field : NativeGoldBatchFieldInputView.View) :
    selected before field = ExecutableSourceSelection.selected before field := select_eq (reconstruct_related before) _

def recover (history : List Observation) (field : NativeGoldBatchFieldInputView.View) : Option Log :=
  (CausalFirstStreamPrefix.recover (TranscriptFrame.encodeMany field.frames) history).map (fun before => selected before field)

theorem recover_eq (dummy : Digest) (history : List Observation) (field : NativeGoldBatchFieldInputView.View) :
    recover history field = NativeGoldBatchFirstFieldSource.recover dummy history field := by
  unfold recover
  simp only [selected_eq]
  exact ExecutableSourceSelection.recover_eq dummy history field
end FormalProof4FHE.HasteBoots.CompactSourceHistory
