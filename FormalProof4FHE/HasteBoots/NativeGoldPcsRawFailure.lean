module

public import FormalProof4FHE.HasteBoots.NativeGoldPcsRawAvailability

@[expose] public section

/-! The actual raw pool's failed semantic transport pays only the pre-existing
root-wide hash hazard. The bound retains scheduler work and cancellation.
Mixed native-prefix/cache coupling and complete PCS soundness remain open. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldPcsRawFailure

open NativeGoldPcsWorkers (Prepared)
open NativeGoldRawRequests (Request)
open NativeGoldColumnAuthentication (encoding)
open NativeRootMessage (Digest)
open InputIndexedOracle (Input)
open OracleSpec OracleComp BinaryTree MerkleTreeMultiExtractability

local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

noncomputable section
variable {Cfg Memory : Type} [SampleableType Digest]

def Failure (dummy : Digest) (height : Cfg → ℕ) (work : Prepared)
    (result : List (NativeGoldColumnWorker.Job × Request height))
    (outcome : HashWorkerPool.Outcome Input Digest Memory work.jobs.length ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun tag => Skeleton.perfect (height tag))) : Prop :=
  HashWorkerPool.allAccepted outcome.1.workers = true ∧
    ∃ entry ∈ result, ∃ checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) entry.2.tag,
      ⟨entry.2.tag,checkpoint⟩ ∈ outcome.2.checkpoints.checkpoints ∧ checkpoint.root = entry.2.root ∧
      ¬NativeGoldRawAvailability.Equations work.geometry work.width work.random work.structured work.test work.evaluation
        (NativeGoldRawAvailability.frozenValue dummy height entry.2.tag checkpoint entry.2.position) entry.2.position.val

theorem failure_implies_availability (height : Cfg → ℕ) (tag : Cfg) (work : Prepared)
    (result : List (NativeGoldColumnWorker.Job × Request height))
    (prepared : NativeGoldPcsRawAvailability.prepare height tag work = some result)
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
    (failure : Failure dummy height work result outcome) :
    ParallelColumnAvailability.Failure encoding dummy height (result.map Prod.snd) outcome.2 := by
  obtain ⟨accepted,entry,member,checkpoint,recorded,root,different⟩ := failure
  by_contra noFailure
  exact different (NativeGoldPcsRawAvailability.pool_equations height tag work result prepared matchesHeight dummy
    choose fuel memory before outcome supported accepted noFailure entry member checkpoint recorded root)

theorem failure_le_charge (height : Cfg → ℕ) (tag : Cfg) (work : Prepared)
    (result : List (NativeGoldColumnWorker.Job × Request height))
    (prepared : NativeGoldPcsRawAvailability.prepare height tag work = some result)
    (matchesHeight : work.geometry.height = height tag) (dummy : Digest)
    (choose : HashWorkerPool.Workers Input Digest work.jobs.length → Memory →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Option (Fin work.jobs.length) × Memory))
    (fuel : ℕ) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun tag => Skeleton.perfect (height tag)))
    (safe : CheckpointCollision.Safe encoding dummy (fun tag => Skeleton.perfect (height tag)) before) :
    Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) encoding dummy (fun tag => Skeleton.perfect (height tag))) (NativeGoldPcsWorkerSoundness.program work choose fuel memory)).run before}[
      Failure dummy height work result outcome] ≤
      ExpectedHazard.charge (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) encoding dummy (fun tag => Skeleton.perfect (height tag)))
        (CheckpointCollision.loss unifSpec (fun tag => Skeleton.perfect (height tag)))
        (NativeGoldPcsWorkerSoundness.program work choose fuel memory) before := by
  apply le_trans (prEvent_mono_of_support _ _ _ ?_)
    (CheckpointAvailability.disagreement_le_charge (QueryImpl.ofLift unifSpec ProbComp) encoding dummy
      (fun tag => Skeleton.perfect (height tag)) (NativeGoldPcsWorkerSoundness.program work choose fuel memory) before safe)
  intro outcome supported failure
  exact ParallelColumnAvailability.failure_implies_disagreement encoding dummy height _ outcome.2
    (failure_implies_availability height tag work result prepared matchesHeight dummy choose fuel memory before outcome supported failure)

end
end FormalProof4FHE.HasteBoots.NativeGoldPcsRawFailure
