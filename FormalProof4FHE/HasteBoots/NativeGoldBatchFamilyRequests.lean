module

public import FormalProof4FHE.HasteBoots.NativeGoldBatchRawRequests
public import FormalProof4FHE.HasteBoots.NativeMerkleShapeFamily
@[expose] public section

/-! Actual prepared batches select a member of the fixed causal shape family.
No context-hash-dependent shape function or external height agreement is required. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchFamilyRequests
open NativeGoldBatchPcsProgram (Context Prepared Completion Scheduler)
open NativeGoldRawRequests (Request)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (World)
open OracleProgram (run)
open NativeMerkleShapeFamily (height tag)
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

def prepare (context : Digest) (work : Prepared) :=
  NativeGoldBatchRawRequests.prepare height (tag context work) work

theorem prepare_complete (context : Digest) (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work) : ∃ result, prepare context work = some result := by
  exact NativeGoldBatchRawRequests.prepare_complete height (tag context work) ctx world work executed
    (NativeMerkleShapeFamily.tag_height context ctx world work executed).symm
theorem accepted_replays {Memory : Type} (context : Digest) (ctx : Context)
    (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory) (world : World) (work : Prepared)
    (completion : Completion Memory work.jobs.length)
    (executed : (run (NativeGoldBatchPcsProgram.program ctx choose fuel memory) world).run.1 = .completed work completion)
    (parent : NativeTranscript.Transcript) (accepted : completion.status = .accepted parent)
    (result : List (NativeGoldColumnWorker.Job × Request height)) (computed : prepare context work = some result)
    (history : List Observation)
    (truthful : ObservationReplay.Agrees world history)
    (observed : (run (NativeGoldBatchPcsProgram.program ctx choose fuel memory) world).run.2.Sublist history) :
    ∀ entry ∈ result, ParallelColumnAvailability.Replays NativeGoldColumnAuthentication.encoding height entry.2 (JointHashCache.project history).cache ∧
      NativeGoldBatchColumnWorker.check work.geometry work.width work.random work.test entry.2.payload.val work.groups entry.2.position.val = true ∧
      ∀ response ∈ work.groups, NativeGoldColumnChecks.check work.geometry work.width work.random response.1 work.test response.2 entry.2.payload.val entry.2.position.val = true := by
  have prepared := (NativeGoldBatchPcsProgram.completed_origin ctx choose fuel memory world work completion executed).prepared
  exact NativeGoldBatchRawRequests.accepted_replays height (tag context work) ctx choose fuel memory world work completion
    executed parent accepted result computed (NativeMerkleShapeFamily.tag_height context ctx world work prepared).symm history truthful observed

end
end FormalProof4FHE.HasteBoots.NativeGoldBatchFamilyRequests
