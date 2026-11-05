module

public import FormalProof4FHE.HasteBoots.NativeGoldRawAvailability

@[expose] public section

/-! Actual prepared raw workers transport their checks to the immutable raw
prefix word. This closes payload projection, not mixed-prefix/cache state
coupling, final claim enforcement or native scheduling refinement. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldPcsRawAvailability

open NativeGoldPcsWorkers (Prepared)
open NativeGoldRawRequests (Request)
open NativeGoldColumnAuthentication (encoding)
open NativeGoldBlockCode (Tables Stored)
open NativeBrakedownContext (Parameters)
open NativeRootMessage (Digest)
open NativeGoldPcsWire (Query)
open NativeGoldPcsOpening (Opening)
open NativeLookupRequestWire (Row)
open NativeTranscript (Transcript)
open InputIndexedOracle (Input World)
open OracleSpec OracleComp BinaryTree MerkleTreeMultiExtractability

local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

def prepare {Cfg : Type} (height : Cfg → ℕ) (tag : Cfg) (work : Prepared) :
    Option (List (NativeGoldColumnWorker.Job × Request height)) :=
  NativeGoldRawRequests.entries height tag work.root work.jobs

/-- The checked native prefix supplies all typed positions and paths. -/
theorem prepare_complete {Cfg : Type} (height : Cfg → ℕ) (tag : Cfg)
    (tables : Tables) (parameters : Parameters Stored) (transcript : Transcript)
    (root : Digest) (query : Query) (values : Row) (opening : Opening) (fuel : ℕ) (world : World) (work : Prepared)
    (success : (OracleProgram.run (NativeGoldPcsWorkers.protocol tables parameters transcript root query values opening fuel) world).run.1 = .prepared work)
    (matchesHeight : work.geometry.height = height tag) : ∃ result, prepare height tag work = some result := by
  apply NativeGoldRawRequests.entries_complete
  intro job member
  have facts := NativeGoldPcsPaths.prepared_paths tables parameters transcript root query values opening fuel world work success job member
  simpa only [matchesHeight] using facts

noncomputable section
variable {Cfg Memory : Type} [SampleableType Digest]

/-- The real pool output discharges both raw availability replay and native
coordinate checks for each computed request. No replay certificate is input. -/
theorem pool_replays (height : Cfg → ℕ) (tag : Cfg) (work : Prepared)
    (result : List (NativeGoldColumnWorker.Job × Request height)) (prepared : prepare height tag work = some result)
    (matchesHeight : work.geometry.height = height tag) (dummy : Digest)
    (choose : HashWorkerPool.Workers Input Digest work.jobs.length → Memory →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Option (Fin work.jobs.length) × Memory))
    (fuel : ℕ) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun tag => Skeleton.perfect (height tag)))
    (outcome : HashWorkerPool.Outcome Input Digest Memory work.jobs.length ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun tag => Skeleton.perfect (height tag)))
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) encoding dummy (fun tag => Skeleton.perfect (height tag)))
      (NativeGoldPcsWorkerSoundness.program work choose fuel memory)).run before))
    (accepted : HashWorkerPool.allAccepted outcome.1.workers = true) :
    ∀ entry ∈ result, ParallelColumnAvailability.Replays encoding height entry.2 outcome.2.hash.cache ∧
      NativeGoldColumnChecks.check work.geometry work.width work.random work.structured work.test work.evaluation
        entry.2.payload.val entry.2.position.val = true := by
  have spec := NativeGoldRawRequests.entries_spec height tag work.root work.jobs result prepared
  intro entry member
  have jobMember : entry.1 ∈ work.jobs := by rw [← spec.1]; exact List.mem_map.mpr ⟨entry,member,rfl⟩
  obtain ⟨index,same⟩ := List.mem_iff_get.mp jobMember
  have replay : simulateQ outcome.2.hash.cache.toPartialImpl
      (NativeGoldColumnWorker.worker work.geometry work.width work.random work.structured work.test work.evaluation work.root entry.1.index entry.1.column) = some true := by
    rw [← same]
    exact HashWorkerPool.accepted_replays encoding dummy (fun tag => Skeleton.perfect (height tag)) choose fuel
      (NativeGoldColumnWorker.workers work.geometry work.width work.random work.structured work.test work.evaluation work.root work.jobs)
      memory before outcome supported accepted index
  have computed := spec.2 entry member
  refine ⟨NativeGoldRawRequests.replay_of_worker height tag work.root work.geometry work.width work.random work.structured work.test work.evaluation
    entry.1 entry.2 computed matchesHeight outcome.2.hash.cache replay,?_⟩
  have checks := (NativeGoldColumnWorker.worker_accepts work.geometry work.width work.random work.structured work.test work.evaluation
    work.root entry.1.index entry.1.column outcome.2.hash.cache replay).2
  obtain ⟨_,_,_,_,sameRequest⟩ := NativeGoldRawRequests.fromJob_spec height tag work.root entry.1 entry.2 computed
  rw [sameRequest]
  exact checks

/-- Every recorded matching root uses its own prefix-frozen raw word. All
workers and both coordinate families share one availability exception event. -/
theorem pool_equations (height : Cfg → ℕ) (tag : Cfg) (work : Prepared)
    (result : List (NativeGoldColumnWorker.Job × Request height)) (prepared : prepare height tag work = some result)
    (matchesHeight : work.geometry.height = height tag) (dummy : Digest)
    (choose : HashWorkerPool.Workers Input Digest work.jobs.length → Memory →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Option (Fin work.jobs.length) × Memory))
    (fuel : ℕ) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun tag => Skeleton.perfect (height tag)))
    (outcome : HashWorkerPool.Outcome Input Digest Memory work.jobs.length ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun tag => Skeleton.perfect (height tag)))
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) encoding dummy (fun tag => Skeleton.perfect (height tag)))
      (NativeGoldPcsWorkerSoundness.program work choose fuel memory)).run before))
    (accepted : HashWorkerPool.allAccepted outcome.1.workers = true)
    (noFailure : ¬ParallelColumnAvailability.Failure encoding dummy height (result.map Prod.snd) outcome.2) :
    ∀ entry ∈ result, ∀ checkpoint : Checkpoint Input Digest
        (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) entry.2.tag,
      ⟨entry.2.tag,checkpoint⟩ ∈ outcome.2.checkpoints.checkpoints → checkpoint.root = entry.2.root →
      NativeGoldRawAvailability.Equations work.geometry work.width work.random work.structured work.test work.evaluation
        (NativeGoldRawAvailability.frozenValue dummy height entry.2.tag checkpoint entry.2.position) entry.2.position.val := by
  have each := pool_replays height tag work result prepared matchesHeight dummy choose fuel memory before outcome supported accepted
  intro entry member checkpoint recorded root
  have facts := each entry member
  exact NativeGoldRawAvailability.equations_of_no_failure dummy height (result.map Prod.snd) entry.2
    (List.mem_map.mpr ⟨entry,member,rfl⟩) outcome.2 facts.1 checkpoint recorded root noFailure
    work.geometry work.width work.random work.structured work.test work.evaluation facts.2

end
end FormalProof4FHE.HasteBoots.NativeGoldPcsRawAvailability
