module

public import FormalProof4FHE.HasteBoots.NativeGoldBatchRootMentions
public import FormalProof4FHE.HasteBoots.NativeParentStateExecution
@[expose] public section

/-! Actual direct batch frames resolve through the parent ledger. Any
nonempty raw read freezes a new key at its pre-read hash log, without a
verifier declaration or start event. Repeated keys retain prior snapshots.
Trusted context/shape identity, arbitrary orphan/pending/receipt lineage
coverage and availability/security are separate obligations. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchExposure
open NativeRootMessage (Digest)
open InputIndexedOracle (Input)
open NativeGoldColumnAuthentication (encoding)
open OracleSpec OracleComp
noncomputable section

def frame (data : NativeGoldBatchMessage.Data) : TranscriptFrame.Frame :=
  ⟨1,NativeTranscript.utf8 "mw batched row-code v1",NativeGoldBatchMessage.codec.encode data⟩
def input (before after : List TranscriptFrame.Frame) (data : NativeGoldBatchMessage.Data) :=
  TranscriptFrame.encodeMany (before++frame data::after)

theorem resolved (before after : List TranscriptFrame.Frame) (data : NativeGoldBatchMessage.Data)
    (valid : ∀ entry ∈ before++frame data::after, TranscriptFrame.Valid entry)
    (ledger : NativeParentLedger.State) (cache : NativeShakeCache.Cache) :
    (data.context,data.root) ∈ NativeParentLedger.resolve ledger cache (input before after data) := by
  have parsed := NativeRootInputView.raw_complete (before++frame data::after) valid
  have included := NativeRootInputView.recognized_sources (before++frame data::after) (frame data)
    (by simp) [(data.context,data.root)] (NativeRootInputView.batch_complete data)
  have present := included.subset (List.mem_singleton_self (data.context,data.root))
  unfold NativeParentLedger.resolve NativeParentLedger.direct
  rw [show NativeRootInputView.raw (input before after data) = some (NativeRootInputView.mentions (before++frame data::after)) from parsed]
  exact List.mem_append_left _ present

/-- Any nonempty raw read, at any offset and without a preceding start or
verifier declaration, freezes a newly mentioned key at the actual pre-read log. -/
theorem fresh_snapshot {A : Type} (dummy : Digest) (shape : Digest → BinaryTree.Skeleton)
    (before after : List TranscriptFrame.Frame) (data : NativeGoldBatchMessage.Data)
    (valid : ∀ entry ∈ before++frame data::after, TranscriptFrame.Valid entry)
    (ledger : NativeParentLedger.State) (cache : NativeShakeCache.Cache)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (fresh : (data.context,data.root) ∉ ledger.frozen)
    (offset count : ℕ) (positive : 0 < count) (next : Input → OracleProgram.Program A)
    (result : (((A × List NativeTranscript.Observation) × NativeParentLedger.State) × NativeShakeCache.Cache) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (possible : result ∈ support (NativeParentRootFreeze.execute encoding dummy shape ledger
      (.read (input before after data) offset count next) cache state)) :
    ⟨data.context,⟨data.root,state.hash.log⟩⟩ ∈ result.2.checkpoints.checkpoints := by
  exact NativeParentRootFreeze.read_snapshot encoding dummy shape ledger (input before after data) offset count next cache state positive
    (data.context,data.root) ((NativeParentLedger.prepare_mem _ _ _ _).mpr ⟨resolved before after data valid ledger cache,fresh⟩) result possible

/-- Repeated mentions retain an already recorded snapshot; they do not reset it
at a later verifier call or after later cache growth. -/
theorem snapshot {A : Type} (dummy : Digest) (shape : Digest → BinaryTree.Skeleton)
    (before after : List TranscriptFrame.Frame) (data : NativeGoldBatchMessage.Data)
    (valid : ∀ entry ∈ before++frame data::after, TranscriptFrame.Valid entry)
    (ledger : NativeParentLedger.State) (cache : NativeShakeCache.Cache)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (covered : NativeParentStateExecution.Covered ((ledger,cache),state))
    (offset count : ℕ) (positive : 0 < count) (next : Input → OracleProgram.Program A)
    (result : (((A × List NativeTranscript.Observation) × NativeParentLedger.State) × NativeShakeCache.Cache) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (possible : result ∈ support (NativeParentRootFreeze.execute encoding dummy shape ledger
      (.read (input before after data) offset count next) cache state)) :
    ∃ log : MerkleTreeExtractor.QueryLog Input Digest, ⟨data.context,⟨data.root,log⟩⟩ ∈ result.2.checkpoints.checkpoints :=
  NativeParentStateExecution.resolved_snapshot encoding dummy shape ledger (input before after data) offset count next cache state covered positive
    (data.context,data.root) (resolved before after data valid ledger cache) result possible
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchExposure
