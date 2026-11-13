module
public import FormalProof4FHE.HasteBoots.RectangularBatchVerifier
@[expose] public section
open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
namespace FormalProof4FHE.HasteBoots.RectangularVariableHeightVerifier
open NativeBatchChecks
noncomputable section
variable {F Input Digest Cfg Response Memory : Type} [Field F] [DecidableEq F]
  [DecidableEq Input] [DecidableEq Digest] {b block front suffix claims m queries : ℕ}

theorem checks_wrong_implies_arithmetic_or_disagreement
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (heights : Cfg → ℕ) (tag : Cfg)
    (checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun cfg => Skeleton.perfect (heights cfg))) tag)
    (domain : Fin (2 ^ heights tag) ↪ F) (query : QueryFamily F b front suffix claims)
    (values : Fin claims → Fin b → F) (capacity : 2 ^ suffix ≤ m * block) (radius : ℕ)
    (testResponse : TestMatrix F (2 ^ front) b → Response → Fin b → Fin (2 ^ suffix) → F)
    (groupResponse : ℕ → TestMatrix F (2 ^ front) b → Response → Fin b → Fin (2 ^ suffix) → F)
    (data : RectangularBatchChecks.Data F Digest Response front b block (heights tag) queries)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (recorded : ⟨tag, checkpoint⟩ ∈ state.checkpoints.checkpoints)
    (replays : ∀ column ∈ data.2, ParallelColumnAvailability.Replays enc heights
      (AuthenticatedColumnChecks.request heights tag checkpoint.root column) state.hash.cache)
    (checked : RectangularBatchChecks.check (m := m) domain query values testResponse groupResponse data = true)
    (different : ∃ claim, values claim ≠ matrixEvaluation (left (front := front) (suffix := suffix) query claim)
      (right (front := front) (suffix := suffix) query claim)
      (RectangularMatrixOpeningKernel.extract domain capacity radius (AmbientRectangularSource.word (height := heights tag) enc dummy heights tag checkpoint))) :
    SharedRectangularBatchSampling.ArithmeticBad domain capacity radius
      (AmbientRectangularSource.word (height := heights tag) enc dummy heights tag checkpoint)
      (BatchQueryLayout.groupOf (front := front) (suffix := suffix) query)
      (groupLeft (front := front) (suffix := suffix) query) (right (front := front) (suffix := suffix) query)
      testResponse (fun matrix response group => groupResponse group.val matrix response) data.1 ∨
      CheckpointAvailability.Disagreement enc dummy (fun cfg => Skeleton.perfect (heights cfg)) state := by
  classical
  by_cases failure : CheckpointAvailability.Disagreement enc dummy (fun cfg => Skeleton.perfect (heights cfg)) state
  · exact Or.inr failure
  left
  obtain ⟨covered, coordinates, finished⟩ := (RectangularBatchChecks.check_iff domain query values testResponse groupResponse data).mp checked
  have noFailure : ¬ParallelColumnAvailability.Failure enc dummy heights
      (AuthenticatedColumnChecks.requests heights tag checkpoint.root data.2) state :=
    fun bad => failure (ParallelColumnAvailability.failure_implies_disagreement enc dummy _ _ state bad)
  have checks := RectangularAuthenticatedColumnChecks.batch_checks_of_authentication enc dummy
    heights tag checkpoint state recorded data.2 data.1.2 covered replays noFailure domain
    data.1.1.1 (fun group => MatrixResponse.weights (groupLeft (front := front) (suffix := suffix) query group))
    (testResponse data.1.1.1 data.1.1.2) (fun group => groupResponse group.val data.1.1.1 data.1.1.2) coordinates
  refine ⟨?_, checks.1, ?_⟩
  · obtain ⟨claim, wrong⟩ := different
    refine ⟨claim, ?_⟩
    change MatrixResponse.finishMessage (right (front := front) (suffix := suffix) query claim)
      (structured query groupResponse claim data.1.1.1 data.1.1.2) ≠ _
    rw [finished claim, group_left_eq]
    exact wrong
  · intro test
    exact checks.2 test.1 test.2

variable [SampleableType Digest] (heights : Cfg → ℕ) (tag : Cfg)
  [SampleableType (TestMatrix F (2 ^ front) b)] [SampleableType (Fin queries → Fin (2 ^ heights tag))]

/-- Computed native worker-pool acceptance discharges replay on the real
shared state, despite other contexts having unrelated tree heights. -/
theorem step_wrong_implies_arithmetic_or_disagreement
    (p : RectangularBatchVerifier.Protocol F Input Digest Cfg Response Memory b block front suffix claims m queries (heights tag))
    (dummy : Digest)
    (checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun cfg => Skeleton.perfect (heights cfg))) tag)
    (root : checkpoint.root = p.root) (capacity : 2 ^ suffix ≤ m * block) (radius : ℕ) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (outcome : ShortCircuitSequence.StepResult
      (RectangularBatchChecks.Data F Digest Response front b block (heights tag) queries) Memory ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) p.encoding dummy (fun cfg => Skeleton.perfect (heights cfg)))
      (RectangularBatchVerifier.step p memory)).run before)) (accepted : outcome.1.accepted = true)
    (recorded : ⟨tag, checkpoint⟩ ∈ outcome.2.checkpoints.checkpoints)
    (different : ∃ claim, p.values claim ≠ matrixEvaluation
      (NativeBatchChecks.left (front := front) (suffix := suffix) p.query claim)
      (NativeBatchChecks.right (front := front) (suffix := suffix) p.query claim)
      (RectangularMatrixOpeningKernel.extract p.domain capacity radius (AmbientRectangularSource.word (height := heights tag) p.encoding dummy heights tag checkpoint))) :
    SharedRectangularBatchSampling.ArithmeticBad p.domain capacity radius
      (AmbientRectangularSource.word (height := heights tag) p.encoding dummy heights tag checkpoint)
      (BatchQueryLayout.groupOf (front := front) (suffix := suffix) p.query)
      (NativeBatchChecks.groupLeft (front := front) (suffix := suffix) p.query)
      (NativeBatchChecks.right (front := front) (suffix := suffix) p.query) p.testResponse
      (fun matrix response group => p.groupResponse group.val matrix response) outcome.1.result.1 ∨
      CheckpointAvailability.Disagreement p.encoding dummy (fun cfg => Skeleton.perfect (heights cfg)) outcome.2 := by
  have verified := RectangularBatchVerifier.step_accepts_later p dummy (fun cfg => Skeleton.perfect (heights cfg)) tag memory
    before outcome supported accepted outcome.2.hash.cache le_rfl
  apply checks_wrong_implies_arithmetic_or_disagreement p.encoding dummy heights tag checkpoint p.domain p.query p.values
    capacity radius p.testResponse p.groupResponse outcome.1.result outcome.2 recorded _ verified.1 different
  intro column member
  have read := verified.2 column member
  simpa only [root, ParallelColumnAvailability.Replays, AuthenticatedColumnChecks.request] using read

end
end FormalProof4FHE.HasteBoots.RectangularVariableHeightVerifier
