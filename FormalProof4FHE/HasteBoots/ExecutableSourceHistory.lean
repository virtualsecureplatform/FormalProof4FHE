module
public import FormalProof4FHE.HasteBoots.ExecutableParentLedger
public import FormalProof4FHE.HasteBoots.NativeRootFamilySourceSelection
@[expose] public section

/-! Replay the public mixed history for source selection. Only the parent
ledger, observed SHAKE bytes, complete ordered hash log and immutable snapshots
are retained. The passive stability monitor and random-oracle hash cache are
unnecessary for this projection; the proof covers arbitrary mixed histories. -/
namespace FormalProof4FHE.HasteBoots.ExecutableSourceHistory
open InputIndexedOracle (Input)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open NativeMerkleShapeFamily (Tag Height shape)
open MerkleTreeMultiExtractability
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq
abbrev Log := NativeRootFamilySourceSelection.Log
abbrev Snapshots := List (AnyCheckpoint Tag Input Unit Digest (MerklePayloadCheckpoints.configuration shape))

structure State where
  ledger : NativeParentLedger.State
  bytes : NativeShakeCache.Cache
  hashes : Log
  snapshots : Snapshots

def initial : State := ⟨ExecutableParentLedger.empty,NativeShakeCache.empty,[],[]⟩

def writeBytes (cache : NativeShakeCache.Cache) (input : Input) (offset : ℕ) : Input → NativeShakeCache.Cache
  | [] => cache
  | value :: rest => writeBytes (Function.update cache (input,offset) (some value)) input (offset+1) rest

def requests (keys : List NativeCanonicalLookupWire.Source) : List (Tag × Digest) :=
  keys.flatMap (fun key => (List.finRange 64).map (fun index => ((key.1,index),key.2)))

def freezeMany (log : Log) : List (Tag × Digest) → Snapshots → Snapshots
  | [],snapshots => snapshots
  | request :: rest,snapshots => freezeMany log rest (snapshots ++ [⟨request.1,⟨request.2,log⟩⟩])

def record (state : State) : Observation → State
  | .start input => {state with ledger := ExecutableParentLedger.discover state.ledger state.bytes input}
  | .hash input digest => {state with
      ledger := ExecutableParentLedger.discover state.ledger state.bytes input
      hashes := state.hashes ++ [⟨input,JointHashCache.decode digest⟩]}
  | .output input offset values =>
    if values = [] then {state with ledger := ExecutableParentLedger.discover state.ledger state.bytes input}
    else
      let plan := ExecutableParentLedger.prepare state.ledger state.bytes input
      { ledger := plan.next
        bytes := writeBytes state.bytes input offset values
        hashes := state.hashes
        snapshots := freezeMany state.hashes (requests plan.requests) state.snapshots }

def reconstruct (history : List Observation) : State := history.foldl record initial

def project (state : NativeRootFamilyState.State) : State :=
  ⟨state.1.1,state.1.2,state.2.hash.log,state.2.checkpoints.checkpoints⟩

theorem writeBytes_eq (cache : NativeShakeCache.Cache) (input : Input) (offset : ℕ) (values : Input) :
    writeBytes cache input offset values = NativeShakeHistory.writeBytes cache input offset values := by
  induction values generalizing cache offset with
  | nil => rfl
  | cons value rest ih => exact ih _ _

theorem requests_eq (keys : List NativeCanonicalLookupWire.Source) :
    requests keys = NativeMerkleShapeFamily.requests keys := rfl

theorem freezeMany_eq (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (roots : List (Tag × Digest)) :
    freezeMany state.hash.log roots state.checkpoints.checkpoints = (RecordRoots.state shape roots state).checkpoints.checkpoints := by
  induction roots generalizing state with
  | nil => rfl
  | cons root rest ih => exact ih (CheckpointExecution.record shape state root.1 root.2)

theorem record_eq {Payload : Type} (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (state : NativeRootFamilyState.State) (entry : Observation) :
    record (project state) entry = project (NativeRootFamilyState.record enc dummy state entry) := by
  cases entry with
  | start input =>
    simp only [record,project,NativeRootFamilyState.record,NativeParentHistory.record,
      ExecutableParentLedger.discover_eq,NativeLazyStateExecution.record]
  | hash input digest =>
    simp only [record,project,NativeRootFamilyState.record,NativeParentHistory.record,
      ExecutableParentLedger.discover_eq,NativeLazyStateExecution.record,CheckpointExecution.afterHash,
      JointHashCache.record,CachedHashHandler.observe]
  | output input offset values =>
    by_cases empty : values = []
    · subst values
      simp only [record,project,NativeRootFamilyState.record,NativeParentHistory.record,ite_true,
        ExecutableParentLedger.discover_eq,NativeShakeHistory.record,NativeShakeHistory.writeBytes]
    · simp only [record,project,NativeRootFamilyState.record,NativeParentHistory.record,empty,ite_false,
        ExecutableParentLedger.prepare_eq,writeBytes_eq,requests_eq,freezeMany_eq,
        NativeShakeHistory.record,RecordRoots.hash_eq]

theorem reconstruct_eq {Payload : Type} (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (history : List Observation) : reconstruct history = project (NativeRootFamilyHistory.reconstruct enc dummy history) := by
  have fold (state : NativeRootFamilyState.State) :
      history.foldl record (project state) = project (history.foldl (NativeRootFamilyState.record enc dummy) state) := by
    induction history generalizing state with
    | nil => rfl
    | cons entry rest ih =>
      simp only [List.foldl_cons]
      rw [record_eq enc dummy]
      exact ih _
  exact fold NativeRootFamilyHistory.initial
end FormalProof4FHE.HasteBoots.ExecutableSourceHistory
