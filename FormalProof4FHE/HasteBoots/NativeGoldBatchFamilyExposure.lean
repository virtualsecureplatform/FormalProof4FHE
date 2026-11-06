module

public import FormalProof4FHE.HasteBoots.NativeGoldBatchRootMentions
public import FormalProof4FHE.HasteBoots.NativeRootFamilyHistory
public import FormalProof4FHE.HasteBoots.NativeGoldBatchExposure
@[expose] public section

/-! Actual direct batch frames resolve through the parent ledger. Any
nonempty raw read freezes a new key at its pre-read hash log, without a
verifier declaration or start event. Repeated keys retain prior snapshots.
Trusted parameter identity and arbitrary orphan/pending/receipt lineage
coverage and availability/security are separate obligations. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchFamilyExposure
open NativeRootMessage (Digest)
open InputIndexedOracle (Input)
open NativeGoldColumnAuthentication (encoding)
open NativeMerkleShapeFamily (Tag Height shape)
open OracleSpec OracleComp
noncomputable section

open NativeGoldBatchExposure (frame input resolved)

/-- Any nonempty raw read, at any offset and without a preceding start or
verifier declaration, freezes a newly mentioned key at the actual pre-read log. -/
theorem fresh_snapshot {A : Type} (dummy : Digest) (index : Height)
    (before after : List TranscriptFrame.Frame) (data : NativeGoldBatchMessage.Data)
    (valid : ∀ entry ∈ before++frame data::after, TranscriptFrame.Valid entry)
    (ledger : NativeParentLedger.State) (cache : NativeShakeCache.Cache)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (fresh : (data.context,data.root) ∉ ledger.frozen)
    (offset count : ℕ) (positive : 0 < count) (next : Input → OracleProgram.Program A)
    (result : (((A × List NativeTranscript.Observation) × NativeParentLedger.State) × NativeShakeCache.Cache) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (possible : result ∈ support (NativeRootFamilyFreeze.execute encoding dummy ledger
      (.read (input before after data) offset count next) cache state)) :
    ⟨(data.context,index),⟨data.root,state.hash.log⟩⟩ ∈ result.2.checkpoints.checkpoints := by
  exact NativeRootFamilyFreeze.read_snapshot encoding dummy ledger (input before after data) offset count next cache state positive
    (data.context,data.root) ((NativeParentLedger.prepare_mem _ _ _ _).mpr ⟨resolved before after data valid ledger cache,fresh⟩) index result possible

/-- Repeated mentions retain an already recorded snapshot; they do not reset it
at a later verifier call or after later cache growth. -/
theorem snapshot {A : Type} (dummy : Digest) (index : Height)
    (before after : List TranscriptFrame.Frame) (data : NativeGoldBatchMessage.Data)
    (valid : ∀ entry ∈ before++frame data::after, TranscriptFrame.Valid entry)
    (ledger : NativeParentLedger.State) (cache : NativeShakeCache.Cache)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (covered : NativeRootFamilyState.Covered ((ledger,cache),state))
    (offset count : ℕ) (positive : 0 < count) (next : Input → OracleProgram.Program A)
    (result : (((A × List NativeTranscript.Observation) × NativeParentLedger.State) × NativeShakeCache.Cache) ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (possible : result ∈ support (NativeRootFamilyFreeze.execute encoding dummy ledger
      (.read (input before after data) offset count next) cache state)) :
    ∃ log : MerkleTreeExtractor.QueryLog Input Digest, ⟨(data.context,index),⟨data.root,log⟩⟩ ∈ result.2.checkpoints.checkpoints :=
  NativeRootFamilyState.resolved_snapshot encoding dummy ledger (input before after data) offset count next cache state covered positive
    (data.context,data.root) index (resolved before after data valid ledger cache) result possible
/-- The captured raw observation determines a common source log for every height,
even when it is off-path or precedes verifier declaration. -/
theorem history_snapshot (dummy : Digest) (history : List NativeTranscript.Observation)
    (before after : List TranscriptFrame.Frame) (data : NativeGoldBatchMessage.Data)
    (valid : ∀ entry ∈ before++frame data::after, TranscriptFrame.Valid entry)
    (offset : ℕ) (values : Input) (positive : values ≠ [])
    (observed : .output (input before after data) offset values ∈ history) :
    ∃ log : MerkleTreeExtractor.QueryLog Input Digest, ∀ index : Height,
      ⟨(data.context,index),⟨data.root,log⟩⟩ ∈
        (NativeRootFamilyHistory.reconstruct encoding dummy history).2.checkpoints.checkpoints := by
  obtain ⟨past,future,rfl⟩ := List.mem_iff_append.mp observed
  exact NativeRootFamilyHistory.read_snapshot encoding dummy past future (input before after data) offset values positive
    (data.context,data.root) (resolved before after data valid _ _)

end
end FormalProof4FHE.HasteBoots.NativeGoldBatchFamilyExposure
