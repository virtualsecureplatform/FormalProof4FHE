module

public import FormalProof4FHE.HasteBoots.NativeGoldBatchObservedAvailability
public import FormalProof4FHE.HasteBoots.NativeGoldBatchReadExposure
@[expose] public section

/-! Accepted native batches derive their actual context digest, computed requests, positive exposure and one immutable raw source. Only parent framing/message bounds and the global no-disagreement event are assumed at this boundary; no supplied exposure, checkpoint or height-match certificate is used. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchNativeAvailability
open NativeGoldBatchPcsProgram (Context Prepared Completion Scheduler)
open NativeGoldRawRequests (Request)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (Input World)
open NativeGoldColumnAuthentication (encoding)
open NativeMerkleShapeFamily (Tag Height height shape tag)
open NativeGoldBatchRawAvailability (Equations view)
open NativeGoldBatchFamilyAvailability (reconstructed)
open NativeGoldBatchExposure (frame input)
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

theorem accepted_native_source {Memory : Type} (dummy : Digest) (ctx : Context)
    (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory) (world : World) (work : Prepared)
    (completion : Completion Memory work.jobs.length)
    (executed : (OracleProgram.run (NativeGoldBatchPcsProgram.program ctx choose fuel memory) world).run.1 = .completed work completion)
    (parent : NativeTranscript.Transcript) (accepted : completion.status = .accepted parent)
    (history : List Observation) (truthful : ObservationReplay.Agrees world history)
    (observed : (OracleProgram.run (NativeGoldBatchPcsProgram.program ctx choose fuel memory) world).run.2.Sublist history)
    (before : List TranscriptFrame.Frame) (framed : ctx.parent.input = TranscriptFrame.encodeMany before)
    (valid : ∀ entry ∈ before, TranscriptFrame.Valid entry)
    (fits : 128 + (NativeGoldBatchBinding.queriesCodec.encode ctx.queries).length +
      (NativeGoldBatchBinding.valuesCodec.encode ctx.values).length < TranscriptFrame.lengthLimit)
    (noDisagreement : ¬CheckpointAvailability.Disagreement encoding dummy shape (reconstructed dummy history)) :
    ∃ (context : Digest) (requests : List (NativeGoldColumnWorker.Job × Request height))
      (log : MerkleTreeExtractor.QueryLog Input Digest),
      (OracleProgram.run (NativeBrakedownContext.context NativeGoldBlockCode.description.row ctx.parameters) world).run.1 = some context ∧
      NativeGoldBatchFamilyRequests.prepare context work = some requests ∧
      (∀ index : Height, ⟨(context,index),⟨work.root,log⟩⟩ ∈ (reconstructed dummy history).checkpoints.checkpoints) ∧
      ∀ entry ∈ requests,
        entry.2.payload = NativeGoldRawAvailability.frozenRaw dummy height entry.2.tag ⟨entry.2.root,log⟩ entry.2.position ∧
        Equations (view work requests)
          (NativeGoldRawAvailability.frozenValue dummy height entry.2.tag ⟨entry.2.root,log⟩ entry.2.position) entry.2.position.val := by
  have origin := NativeGoldBatchPcsProgram.completed_origin ctx choose fuel memory world work completion executed
  obtain ⟨context,hashed,frames,read⟩ := NativeGoldBatchReadExposure.prepared_exposure ctx world work origin.prepared before framed valid fits
  obtain ⟨requests,computed⟩ := NativeGoldBatchFamilyRequests.prepare_complete context ctx world work origin.prepared
  have present : .output (input before (NativeGoldBatchReadExposure.suffix work.geometry.randomCount)
      ⟨context,work.root,work.binding.queries,work.binding.values⟩) 0
      (InputIndexedOracle.bytes world (input before (NativeGoldBatchReadExposure.suffix work.geometry.randomCount)
        ⟨context,work.root,work.binding.queries,work.binding.values⟩) 0 8) ∈ history := by
    apply observed.subset
    rw [origin.log]
    exact List.mem_append_left _ read
  have positive : InputIndexedOracle.bytes world (input before (NativeGoldBatchReadExposure.suffix work.geometry.randomCount)
      ⟨context,work.root,work.binding.queries,work.binding.values⟩) 0 8 ≠ [] := by
    intro empty
    have lengths := congrArg List.length empty
    simp only [InputIndexedOracle.bytes,List.length_ofFn,List.length_nil] at lengths
    contradiction
  have noFailure : ¬ParallelColumnAvailability.Failure encoding dummy height (requests.map Prod.snd) (reconstructed dummy history) :=
    fun failure => noDisagreement (ParallelColumnAvailability.failure_implies_disagreement encoding dummy height _ _ failure)
  obtain ⟨log,snapshots,checks⟩ := NativeGoldBatchObservedAvailability.accepted_source dummy context ctx choose fuel memory world work completion
    executed parent accepted requests computed history truthful observed before (NativeGoldBatchReadExposure.suffix work.geometry.randomCount)
    frames 0 _ positive present noFailure
  exact ⟨context,requests,log,hashed,computed,snapshots,checks⟩
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchNativeAvailability
