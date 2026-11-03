module

public import FormalProof4FHE.HasteBoots.NativeBatchVerifier

@[expose] public section

/-!
# Native batch authentication with context-indexed tree heights

Different original roots may have different PCS layouts and tree heights.
The selected root uses height(tag), while all workers/checkpoints retain the
same shared cache and global availability event. Actual computed native step
acceptance supplies replay; no caller replay/security certificate is needed.
Dependent multi-root scheduling and its one-charge prefix bound remain to
compose with this single-root adapter.
-/

open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening

namespace FormalProof4FHE.HasteBoots.VariableHeightBatchVerifier

noncomputable section

variable {F Input Digest Cfg Response Memory : Type} [Field F] [DecidableEq F]
  [DecidableEq Input] [DecidableEq Digest] {b front suffix claims m queries : ℕ}

/-- Coverage, every grouped coordinate and every original finish value retain
one context-indexed root-wide availability exception. -/
theorem checks_wrong_implies_arithmetic_or_disagreement
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (heights : Cfg → ℕ) (tag : Cfg)
    (checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun cfg => Skeleton.perfect (heights cfg))) tag)
    (domain : Fin (2 ^ heights tag) ↪ F) (query : NativeBatchChecks.QueryFamily F b front suffix claims)
    (values : Fin claims → Fin b → F) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (testResponse : TestMatrix F (2 ^ front) b → Response → Fin b → Fin (2 ^ suffix) → F)
    (groupResponse : ℕ → TestMatrix F (2 ^ front) b → Response → Fin b → Fin (2 ^ suffix) → F)
    (data : JointMatrixOpening.Data F Digest Response (2 ^ front) b (heights tag) queries)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (recorded : ⟨tag, checkpoint⟩ ∈ state.checkpoints.checkpoints)
    (replays : ∀ column ∈ data.2, ParallelColumnAvailability.Replays enc heights
      (AuthenticatedColumnChecks.request heights tag checkpoint.root column) state.hash.cache)
    (checked : NativeBatchChecks.check (m := m) domain query values testResponse groupResponse data = true)
    (different : ∃ claim, values claim ≠ matrixEvaluation
      (NativeBatchChecks.left (front := front) (suffix := suffix) query claim)
      (NativeBatchChecks.right (front := front) (suffix := suffix) query claim)
      (MatrixOpeningSecurity.extract domain capacity radius (word enc dummy heights tag checkpoint))) :
    BatchMatrixSampling.ArithmeticBad domain capacity radius (word enc dummy heights tag checkpoint)
      (NativeBatchChecks.left (front := front) (suffix := suffix) query)
      (NativeBatchChecks.right (front := front) (suffix := suffix) query) values
      testResponse (NativeBatchChecks.structured query groupResponse) data.1 ∨
      CheckpointAvailability.Disagreement enc dummy (fun cfg => Skeleton.perfect (heights cfg)) state := by
  by_cases failure : CheckpointAvailability.Disagreement enc dummy (fun cfg => Skeleton.perfect (heights cfg)) state
  · exact Or.inr failure
  left
  obtain ⟨covered, coordinates, finished⟩ :=
    (NativeBatchChecks.check_iff domain query values testResponse groupResponse data).mp checked
  have noFailure : ¬ParallelColumnAvailability.Failure enc dummy heights
      (AuthenticatedColumnChecks.requests heights tag checkpoint.root data.2) state :=
    fun bad => failure (ParallelColumnAvailability.failure_implies_disagreement enc dummy _ _ state bad)
  have checks (claim : Fin claims) := AuthenticatedColumnChecks.matrix_pair_checks_of_authentication enc dummy heights tag checkpoint
    state recorded data.2 data.1.2 covered replays noFailure domain data.1.1.1
    (MatrixResponse.weights (NativeBatchChecks.left (front := front) (suffix := suffix) query claim))
    (testResponse data.1.1.1 data.1.1.2)
    (NativeBatchChecks.structured query groupResponse claim data.1.1.1 data.1.1.2)
    (NativeBatchChecks.coordinates_claim domain query testResponse groupResponse data coordinates claim)
  obtain ⟨claim, wrong⟩ := different
  exact ⟨⟨claim, wrong⟩, (checks claim).1, fun claim => (checks claim).2, finished⟩

variable [SampleableType Digest] (heights : Cfg → ℕ) (tag : Cfg)
  [SampleableType (TestMatrix F (2 ^ front) b)] [SampleableType (Fin queries → Fin (2 ^ heights tag))]

/-- Computed native worker-pool acceptance discharges replay on the real
shared state, despite other contexts having unrelated tree heights. -/
theorem step_wrong_implies_arithmetic_or_disagreement
    (p : NativeBatchVerifier.Protocol F Input Digest Cfg Response Memory b front suffix claims m queries (heights tag))
    (dummy : Digest)
    (checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun cfg => Skeleton.perfect (heights cfg))) tag)
    (root : checkpoint.root = p.root) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ) (memory : Memory)
    (before : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (outcome : ShortCircuitSequence.StepResult
      (JointMatrixOpening.Data F Digest Response (2 ^ front) b (heights tag) queries) Memory ×
      CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (supported : outcome ∈ support ((simulateQ
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) p.encoding dummy (fun cfg => Skeleton.perfect (heights cfg)))
      (NativeBatchVerifier.step p memory)).run before)) (accepted : outcome.1.accepted = true)
    (recorded : ⟨tag, checkpoint⟩ ∈ outcome.2.checkpoints.checkpoints)
    (different : ∃ claim, p.values claim ≠ matrixEvaluation
      (NativeBatchChecks.left (front := front) (suffix := suffix) p.query claim)
      (NativeBatchChecks.right (front := front) (suffix := suffix) p.query claim)
      (MatrixOpeningSecurity.extract p.domain capacity radius (word p.encoding dummy heights tag checkpoint))) :
    BatchMatrixSampling.ArithmeticBad p.domain capacity radius (word p.encoding dummy heights tag checkpoint)
      (NativeBatchChecks.left (front := front) (suffix := suffix) p.query)
      (NativeBatchChecks.right (front := front) (suffix := suffix) p.query) p.values p.testResponse
      (NativeBatchChecks.structured p.query p.groupResponse) outcome.1.result.1 ∨
      CheckpointAvailability.Disagreement p.encoding dummy (fun cfg => Skeleton.perfect (heights cfg)) outcome.2 := by
  have verified := NativeBatchVerifier.step_accepts_later p dummy (fun cfg => Skeleton.perfect (heights cfg)) tag memory
    before outcome supported accepted outcome.2.hash.cache le_rfl
  apply checks_wrong_implies_arithmetic_or_disagreement p.encoding dummy heights tag checkpoint p.domain p.query p.values
    capacity radius p.testResponse p.groupResponse outcome.1.result outcome.2 recorded _ verified.1 different
  intro column member
  have read := verified.2 column member
  simpa only [root, ParallelColumnAvailability.Replays, AuthenticatedColumnChecks.request] using read

end

end FormalProof4FHE.HasteBoots.VariableHeightBatchVerifier
