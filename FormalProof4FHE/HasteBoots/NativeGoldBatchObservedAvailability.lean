module

public import FormalProof4FHE.HasteBoots.NativeGoldBatchFamilyAvailability
public import FormalProof4FHE.HasteBoots.NativeGoldBatchFamilyExposure
@[expose] public section

/-! Derive one immutable raw source from observed batch exposure and accepted native workers. The checkpoint is reconstructed, rather than supplied by the caller. Application soundness and first-exposure lineage remain separate. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchObservedAvailability
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
open MerkleTreeMultiExtractability
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

theorem reconstructed_eq (dummy : Digest) (history : List Observation) :
    (NativeRootFamilyHistory.reconstruct encoding dummy history).2 = reconstructed dummy history := rfl

/-- A positive raw batch observation supplies one immutable source log for all
accepted columns and response groups. No caller-supplied checkpoint is needed. -/
theorem accepted_source {Memory : Type} (dummy context : Digest) (ctx : Context)
    (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory) (world : World) (work : Prepared)
    (completion : Completion Memory work.jobs.length)
    (executed : (OracleProgram.run (NativeGoldBatchPcsProgram.program ctx choose fuel memory) world).run.1 = .completed work completion)
    (parent : NativeTranscript.Transcript) (accepted : completion.status = .accepted parent)
    (requests : List (NativeGoldColumnWorker.Job × Request height))
    (computed : NativeGoldBatchFamilyRequests.prepare context work = some requests)
    (history : List Observation) (truthful : ObservationReplay.Agrees world history)
    (observed : (OracleProgram.run (NativeGoldBatchPcsProgram.program ctx choose fuel memory) world).run.2.Sublist history)
    (before after : List TranscriptFrame.Frame)
    (valid : ∀ entry ∈ before++frame ⟨context,work.root,work.binding.queries,work.binding.values⟩::after, TranscriptFrame.Valid entry)
    (offset : ℕ) (values : Input) (positive : values ≠ [])
    (exposed : .output (input before after ⟨context,work.root,work.binding.queries,work.binding.values⟩) offset values ∈ history)
    (noFailure : ¬ParallelColumnAvailability.Failure encoding dummy height (requests.map Prod.snd) (reconstructed dummy history)) :
    ∃ log : MerkleTreeExtractor.QueryLog Input Digest,
      (∀ index : Height, ⟨(context,index),⟨work.root,log⟩⟩ ∈ (reconstructed dummy history).checkpoints.checkpoints) ∧
      ∀ entry ∈ requests,
        entry.2.payload = NativeGoldRawAvailability.frozenRaw dummy height entry.2.tag ⟨entry.2.root,log⟩ entry.2.position ∧
        Equations (view work requests)
          (NativeGoldRawAvailability.frozenValue dummy height entry.2.tag ⟨entry.2.root,log⟩ entry.2.position) entry.2.position.val := by
  obtain ⟨log,snapshots⟩ := NativeGoldBatchFamilyExposure.history_snapshot dummy history before after
    ⟨context,work.root,work.binding.queries,work.binding.values⟩ valid offset values positive exposed
  rw [reconstructed_eq] at snapshots
  refine ⟨log,snapshots,?_⟩
  have spec := NativeGoldBatchRawRequests.prepare_spec height (tag context work) work requests computed
  have each := NativeGoldBatchFamilyRequests.accepted_replays context ctx choose fuel memory world work completion
    executed parent accepted requests computed history truthful observed
  intro entry member
  have recorded : ⟨entry.2.tag,⟨entry.2.root,log⟩⟩ ∈ (reconstructed dummy history).checkpoints.checkpoints := by
    obtain ⟨bound,leaf,siblings,_,same⟩ := NativeGoldRawRequests.fromJob_spec height (tag context work) work.root entry.1 entry.2 (spec.2 entry member)
    rw [same]
    exact snapshots (tag context work).2
  have replayed : ParallelColumnAvailability.Replays encoding height entry.2 (reconstructed dummy history).hash.cache := by
    rw [NativeGoldBatchFamilyAvailability.reconstructed_hash]
    exact (each entry member).1
  refine ⟨NativeGoldRawAvailability.payload_of_no_failure dummy height (requests.map Prod.snd) entry.2
    (List.mem_map.mpr ⟨entry,member,rfl⟩) (reconstructed dummy history) replayed ⟨entry.2.root,log⟩ recorded rfl noFailure,?_⟩
  exact NativeGoldBatchFamilyAvailability.accepted_equations dummy context ctx choose fuel memory world work completion
    executed parent accepted requests computed history truthful observed noFailure entry member ⟨entry.2.root,log⟩ recorded rfl
end
end FormalProof4FHE.HasteBoots.NativeGoldBatchObservedAvailability
