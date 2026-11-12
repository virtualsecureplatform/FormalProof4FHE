module
public import FormalProof4FHE.HasteBoots.NativeBatchChecks
public import FormalProof4FHE.HasteBoots.AmbientMatrixSource
@[expose] public section

/-! Native batch checks against a local source in a mixed-height shared history.
Only the opened tag's height is fixed by this matrix protocol. -/
namespace FormalProof4FHE.HasteBoots.AmbientBatchChecks
open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open InteractiveAuthenticatedOpening NativeBatchChecks
noncomputable section
variable {F Input Digest Cfg Response : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {b front suffix claims m height queries : ℕ}

/-- Accepted false native batch claims reduce to arithmetic or the one ambient
availability event, while all unrelated helper checkpoints stay in the state. -/
theorem wrong_implies_arithmetic_or_disagreement
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (heights : Cfg → ℕ) (tag : Cfg) (geometry : heights tag = height)
    (checkpoint : AmbientMatrixSource.Snapshot Input Digest heights tag)
    (domain : Fin (2^height) ↪ F) (query : QueryFamily F b front suffix claims)
    (values : Fin claims → Fin b → F) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (testResponse : TestMatrix F (2^front) b → Response → Fin b → Fin (2^suffix) → F)
    (groupResponse : ℕ → TestMatrix F (2^front) b → Response → Fin b → Fin (2^suffix) → F)
    (data : JointMatrixOpening.Data F Digest Response (2^front) b height queries)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (recorded : ⟨tag,checkpoint⟩ ∈ state.checkpoints.checkpoints)
    (replays : ∀ column ∈ data.2, ParallelColumnAvailability.Replays enc (fun _ : Cfg => height)
      (AuthenticatedColumnChecks.request (fun _ : Cfg => height) tag checkpoint.root column) state.hash.cache)
    (checked : check (m := m) domain query values testResponse groupResponse data = true)
    (different : ∃ claim, values claim ≠ matrixEvaluation (left (front := front) (suffix := suffix) query claim)
      (right (front := front) (suffix := suffix) query claim)
      (MatrixOpeningSecurity.extract domain capacity radius (AmbientMatrixSource.word enc dummy heights tag checkpoint))) :
    BatchMatrixSampling.ArithmeticBad domain capacity radius (AmbientMatrixSource.word enc dummy heights tag checkpoint)
      (left (front := front) (suffix := suffix) query) (right (front := front) (suffix := suffix) query) values
      testResponse (structured query groupResponse) data.1 ∨
      CheckpointAvailability.Disagreement enc dummy (AmbientMatrixSource.Shape heights) state := by
  subst height
  classical
  by_cases failure : CheckpointAvailability.Disagreement enc dummy (AmbientMatrixSource.Shape heights) state
  · exact Or.inr failure
  left
  obtain ⟨covered,coordinates,finished⟩ := (check_iff domain query values testResponse groupResponse data).mp checked
  have noFailure : ¬ParallelColumnAvailability.Failure enc dummy heights
      (AuthenticatedColumnChecks.requests heights tag checkpoint.root data.2) state :=
    fun bad => failure (ParallelColumnAvailability.failure_implies_disagreement enc dummy _ _ state bad)
  have checks (claim : Fin claims) := AuthenticatedColumnChecks.matrix_pair_checks_of_authentication enc dummy
    heights tag checkpoint state recorded data.2 data.1.2 covered replays noFailure domain
    data.1.1.1 (MatrixResponse.weights (left (front := front) (suffix := suffix) query claim))
    (testResponse data.1.1.1 data.1.1.2) (structured query groupResponse claim data.1.1.1 data.1.1.2)
    (coordinates_claim domain query testResponse groupResponse data coordinates claim)
  obtain ⟨claim,wrong⟩ := different
  exact ⟨⟨claim,wrong⟩,(checks claim).1,fun claim => (checks claim).2,finished⟩

end
end FormalProof4FHE.HasteBoots.AmbientBatchChecks
