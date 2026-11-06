module

public import FormalProof4FHE.HasteBoots.NativeRootFamilyState
@[expose] public section

/-! Complete-history reconstruction retains every native height at the same first resolved positive-read hash log. Positive raw observations derive snapshots without an input checkpoint certificate. -/
namespace FormalProof4FHE.HasteBoots.NativeRootFamilyHistory
open NativeMerkleShapeFamily (Tag Height shape)
open NativeRootFamilyState (State record)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (Input)
open MerkleTreeMultiExtractability
noncomputable section
variable {Payload : Type}

def initial : State := ((NativeParentLedger.empty,NativeShakeCache.empty),CheckpointExecution.empty shape)
def reconstruct (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (history : List Observation) : State :=
  history.foldl (record enc dummy) initial

/-- Every height for a key is retained at one common pre-read log. -/
def Covered (state : State) : Prop := ∀ key ∈ state.1.1.frozen,
  ∃ log : MerkleTreeExtractor.QueryLog Input Digest, ∀ index : Height,
    ⟨(key.1,index),⟨key.2,log⟩⟩ ∈ state.2.checkpoints.checkpoints

theorem record_retains (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (state : State) (entry : Observation) (tag : Tag)
    (checkpoint : Checkpoint Input Digest (MerklePayloadCheckpoints.configuration shape) tag)
    (present : ⟨tag,checkpoint⟩ ∈ state.2.checkpoints.checkpoints) :
    ⟨tag,checkpoint⟩ ∈ (record enc dummy state entry).2.checkpoints.checkpoints := by
  cases entry with
  | start input => exact present
  | hash input digest => exact present
  | output input offset values =>
    simp only [record]
    split
    · exact present
    · exact RecordRoots.retains shape _ state.2 tag checkpoint present

theorem fold_retains (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (state : State) (history : List Observation) (tag : Tag)
    (checkpoint : Checkpoint Input Digest (MerklePayloadCheckpoints.configuration shape) tag)
    (present : ⟨tag,checkpoint⟩ ∈ state.2.checkpoints.checkpoints) :
    ⟨tag,checkpoint⟩ ∈ (history.foldl (record enc dummy) state).2.checkpoints.checkpoints := by
  induction history generalizing state with
  | nil => exact present
  | cons entry rest ih => exact ih _ (record_retains enc dummy state entry tag checkpoint present)

theorem record_covered (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (state : State) (entry : Observation) (covered : Covered state) : Covered (record enc dummy state entry) := by
  unfold Covered at covered ⊢
  cases entry with
  | start input =>
    change ∀ key ∈ (NativeParentLedger.discover state.1.1 state.1.2 input).frozen, _
    rw [NativeParentLedger.discover_frozen]
    exact covered
  | hash input digest =>
    change ∀ key ∈ (NativeParentLedger.discover state.1.1 state.1.2 input).frozen, _
    rw [NativeParentLedger.discover_frozen]
    exact covered
  | output input offset values =>
    by_cases empty : values = []
    · simpa only [record,NativeParentHistory.record,empty,ite_true,NativeParentLedger.discover_frozen] using covered
    · simp only [record,NativeParentHistory.record,empty,ite_false]
      intro key member
      by_cases old : key ∈ state.1.1.frozen
      · obtain ⟨log,present⟩ := covered key old
        exact ⟨log,fun index => RecordRoots.retains shape _ state.2 (key.1,index) ⟨key.2,log⟩ (present index)⟩
      · have requested : key ∈ (NativeParentLedger.prepare state.1.1 state.1.2 input).requests := by
          apply (NativeParentLedger.prepare_mem _ _ _ _).mpr
          rw [NativeParentLedger.prepare_frozen] at member
          exact ⟨List.mem_toFinset.mp ((Finset.mem_union.mp member).resolve_left old),old⟩
        exact ⟨state.2.hash.log,fun index => RecordRoots.recorded shape _ state.2 ((key.1,index),key.2)
          (NativeMerkleShapeFamily.requests_member _ key requested index)⟩

theorem fold_covered (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (state : State) (history : List Observation) (covered : Covered state) :
    Covered (history.foldl (record enc dummy) state) := by
  induction history generalizing state with
  | nil => exact covered
  | cons entry rest ih => exact ih _ (record_covered enc dummy state entry covered)

theorem initial_covered : Covered initial := by
  intro key member
  exact False.elim (Finset.notMem_empty key member)

theorem reconstruct_covered (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (history : List Observation) :
    Covered (reconstruct enc dummy history) := fold_covered enc dummy initial history initial_covered

theorem read_snapshot (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (before after : List Observation) (input : Input) (offset : ℕ) (values : Input) (positive : values ≠ [])
    (key : NativeCanonicalLookupWire.Source)
    (resolved : key ∈ NativeParentLedger.resolve (reconstruct enc dummy before).1.1 (reconstruct enc dummy before).1.2 input) :
    ∃ log : MerkleTreeExtractor.QueryLog Input Digest, ∀ index : Height,
      ⟨(key.1,index),⟨key.2,log⟩⟩ ∈ (reconstruct enc dummy (before ++ .output input offset values :: after)).2.checkpoints.checkpoints := by
  have frozen : key ∈ (record enc dummy (reconstruct enc dummy before) (.output input offset values)).1.1.frozen := by
    simp only [record,NativeParentHistory.record,positive,ite_false]
    exact NativeParentLedger.prepare_remembers _ _ input key resolved
  obtain ⟨log,present⟩ := record_covered enc dummy _ (.output input offset values) (reconstruct_covered enc dummy before) key frozen
  refine ⟨log,fun index => ?_⟩
  simpa only [reconstruct,List.foldl_append,List.foldl_cons] using
    fold_retains enc dummy (record enc dummy (reconstruct enc dummy before) (.output input offset values)) after (key.1,index) ⟨key.2,log⟩ (present index)

/-- An actual raw/off-path read supplies all height snapshots; no checkpoint certificate is an input. -/
theorem direct_snapshot (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest)
    (history : List Observation) (input : Input) (offset : ℕ) (values : Input) (positive : values ≠ [])
    (observed : .output input offset values ∈ history) (key : NativeCanonicalLookupWire.Source)
    (mentioned : key ∈ NativeParentLedger.direct input) :
    ∃ log : MerkleTreeExtractor.QueryLog Input Digest, ∀ index : Height,
      ⟨(key.1,index),⟨key.2,log⟩⟩ ∈ (reconstruct enc dummy history).2.checkpoints.checkpoints := by
  obtain ⟨before,after,rfl⟩ := List.mem_iff_append.mp observed
  exact read_snapshot enc dummy before after input offset values positive key (List.mem_append_left _ mentioned)
end
end FormalProof4FHE.HasteBoots.NativeRootFamilyHistory
