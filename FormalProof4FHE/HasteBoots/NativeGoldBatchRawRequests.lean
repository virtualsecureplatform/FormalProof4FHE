module

public import FormalProof4FHE.HasteBoots.NativeGoldBatchPaths
@[expose] public section

/-! Lossless raw availability requests come from actual checked batch workers.
Accepted causal execution supplies Merkle replay and every response-group
check in one containing truthful mixed history; no replay certificate is input. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldBatchRawRequests
open NativeGoldBatchPcsProgram (Context Prepared Completion Scheduler)
open NativeGoldRawRequests (Request)
open NativeRootMessage (Digest)
open NativeTranscript (Observation)
open InputIndexedOracle (World)
open OracleProgram (run)
open OracleSpec OracleComp
noncomputable section
local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

def prepare {Cfg : Type} (height : Cfg → ℕ) (tag : Cfg) (work : Prepared) :=
  NativeGoldRawRequests.entries height tag work.root work.jobs

theorem prepare_complete {Cfg : Type} (height : Cfg → ℕ) (tag : Cfg) (ctx : Context) (world : World) (work : Prepared)
    (executed : (run (NativeGoldBatchPcsProgram.prepareProgram ctx) world).run.1 = .prepared work)
    (matchesHeight : work.geometry.height = height tag) : ∃ result, prepare height tag work = some result := by
  apply NativeGoldRawRequests.entries_complete
  intro job member
  simpa only [matchesHeight] using NativeGoldBatchPaths.prepared_paths ctx world work executed job member

theorem prepare_spec {Cfg : Type} (height : Cfg → ℕ) (tag : Cfg) (work : Prepared)
    (result : List (NativeGoldColumnWorker.Job × Request height)) (computed : prepare height tag work = some result) :
    result.map Prod.fst = work.jobs ∧ ∀ entry ∈ result, NativeGoldRawRequests.fromJob height tag work.root entry.1 = some entry.2 :=
  NativeGoldRawRequests.entries_spec height tag work.root work.jobs result computed

/-- Both the Merkle replay and every response-group check come from the actual
accepted causal batch run in its containing truthful mixed history. -/
theorem accepted_replays {Cfg Memory : Type} (height : Cfg → ℕ) (tag : Cfg) (ctx : Context)
    (choose : Scheduler Memory) (fuel : ℕ) (memory : Memory) (world : World) (work : Prepared)
    (completion : Completion Memory work.jobs.length)
    (executed : (run (NativeGoldBatchPcsProgram.program ctx choose fuel memory) world).run.1 = .completed work completion)
    (parent : NativeTranscript.Transcript) (accepted : completion.status = .accepted parent)
    (result : List (NativeGoldColumnWorker.Job × Request height)) (computed : prepare height tag work = some result)
    (matchesHeight : work.geometry.height = height tag) (history : List Observation)
    (truthful : ObservationReplay.Agrees world history)
    (observed : (run (NativeGoldBatchPcsProgram.program ctx choose fuel memory) world).run.2.Sublist history) :
    ∀ entry ∈ result, ParallelColumnAvailability.Replays NativeGoldColumnAuthentication.encoding height entry.2 (JointHashCache.project history).cache ∧
      NativeGoldBatchColumnWorker.check work.geometry work.width work.random work.test entry.2.payload.val work.groups entry.2.position.val = true ∧
      ∀ response ∈ work.groups, NativeGoldColumnChecks.check work.geometry work.width work.random response.1 work.test response.2 entry.2.payload.val entry.2.position.val = true := by
  have spec := prepare_spec height tag work result computed
  intro entry member
  have jobMember : entry.1 ∈ work.jobs := by rw [← spec.1]; exact List.mem_map.mpr ⟨entry,member,rfl⟩
  obtain ⟨leaf,siblings,decoded,_,authenticated,allGroups,eachGroup⟩ := NativeGoldBatchPcsProgram.accepted_workers ctx choose fuel memory world work completion
    executed parent accepted history truthful observed entry.1 jobMember
  obtain ⟨bound,parsedLeaf,parsedSiblings,parsed,same⟩ := NativeGoldRawRequests.fromJob_spec height tag work.root entry.1 entry.2 (spec.2 entry member)
  have authentication : simulateQ (JointHashCache.project history).cache.toPartialImpl
      (NativeGoldColumnWorker.authentication work.geometry.height entry.1.index work.root entry.1.column) = some true := by
    simpa only [NativeGoldColumnWorker.authentication,decoded] using authenticated
  rw [matchesHeight] at authentication
  rw [same]
  refine ⟨?_,allGroups,eachGroup⟩
  simpa only [ParallelColumnAvailability.Replays,NativeGoldColumnWorker.authentication,parsed] using authentication

end
end FormalProof4FHE.HasteBoots.NativeGoldBatchRawRequests
