module

public import FormalProof4FHE.HasteBoots.NativeGoldPcsWorkers

@[expose] public section

/-! Acceptance facts for workers prepared by an actual checked PCS prefix.
The raw pool and the mixed-oracle prefix have separate execution interfaces;
coupling their checkpoint state and full Rayon completion remains open.
No field-projected payload is substituted into the shared hash encoding. -/
namespace FormalProof4FHE.HasteBoots.NativeGoldPcsWorkerSoundness

open NativeGoldPcsWorkers (Prepared)
open InputIndexedOracle (Input World)
open NativeRootMessage (Digest)
open NativeGoldColumnAuthentication (encoding decodePath)
open OracleSpec OracleComp

local instance : DecidableEq Digest := NativeGoldColumnAuthentication.digestDecidableEq

noncomputable section
open scoped BigOperators

def program {Cfg Memory : Type} (work : Prepared)
    (choose : HashWorkerPool.Workers Input Digest work.jobs.length → Memory →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Option (Fin work.jobs.length) × Memory))
    (fuel : ℕ) (memory : Memory) :=
  NativeGoldColumnWorker.program work.geometry work.width work.random work.structured work.test work.evaluation
    work.root work.jobs choose fuel memory

variable {Cfg Memory : Type} [SampleableType Digest]

/-- The actual final pool flag entails authentication of original raw bytes
and both semantic coordinate families, for every original prepared worker.
Scheduling/cancellation cannot provide or substitute a true flag. -/
theorem accepted_checks (work : Prepared) (dummy : Digest) (shape : Cfg → BinaryTree.Skeleton)
    (choose : HashWorkerPool.Workers Input Digest work.jobs.length → Memory →
      OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (Option (Fin work.jobs.length) × Memory))
    (fuel : ℕ) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : HashWorkerPool.Outcome Input Digest Memory work.jobs.length × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) encoding dummy shape)
      (program work choose fuel memory)).run before))
    (accepted : HashWorkerPool.allAccepted outcome.1.workers = true) :
    ∀ job ∈ work.jobs, ∃ leaf siblings, decodePath work.geometry.height job.column.path.val = some (leaf,siblings) ∧
      job.column.path.val = leaf :: siblings.toList ∧
      simulateQ outcome.2.hash.cache.toPartialImpl (NativeMerkleVerifier.verifyPayload encoding work.geometry.height job.index job.column.values leaf work.root siblings) = some true ∧
      ∀ lane < work.width, ∀ component < work.geometry.blockWidth,
        (∑ row : Fin work.geometry.rows, NativeGoldColumnChecks.view work.random (lane*work.geometry.rows+row.val)*
          NativeGoldColumnChecks.view job.column.values.val (row.val*work.geometry.blockWidth+component)) =
            NativeGoldColumnChecks.view work.test (lane*work.geometry.stride+job.index*work.geometry.blockWidth+component) ∧
        (∑ row : Fin work.geometry.rows, NativeGoldColumnChecks.view work.structured (lane*work.geometry.rows+row.val)*
          NativeGoldColumnChecks.view job.column.values.val (row.val*work.geometry.blockWidth+component)) =
            NativeGoldColumnChecks.view work.evaluation (lane*work.geometry.stride+job.index*work.geometry.blockWidth+component) := by
  have each := NativeGoldColumnWorker.accepted_jobs work.geometry work.width work.random work.structured work.test work.evaluation
    dummy work.root work.jobs shape choose fuel memory before outcome supported accepted
  intro job member
  obtain ⟨leaf,siblings,parsed,path,replayed,checked⟩ := each job member
  exact ⟨leaf,siblings,parsed,path,replayed,(NativeGoldColumnChecks.check_iff _ _ _ _ _ _ _ _).mp checked⟩

end
end FormalProof4FHE.HasteBoots.NativeGoldPcsWorkerSoundness
