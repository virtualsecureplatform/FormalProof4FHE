module
public import FormalProof4FHE.HasteBoots.NativeFactorChecks
public import FormalProof4FHE.HasteBoots.AmbientMatrixSource
@[expose] public section

/-! Single matrix-opening checks use the original local source while retaining
all unrelated contexts in the inherited mixed-height state. -/
namespace FormalProof4FHE.HasteBoots.AmbientSingleChecks
open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open InteractiveAuthenticatedOpening
noncomputable section
variable {F Input Digest Cfg Response : Type}
  [Field F] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {b front suffix m height queries : ℕ}

/-- Concrete coverage, coordinates, value checks and actual worker replay imply
arithmetic failure or the caller's one ambient availability disagreement. -/
theorem wrong_implies_arithmetic_or_disagreement
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (heights : Cfg → ℕ) (tag : Cfg) (geometry : heights tag = height)
    (checkpoint : AmbientMatrixSource.Snapshot Input Digest heights tag)
    (domain : Fin (2^height) ↪ F)
    (left : Fin (2^front) → Matrix (Fin b) (Fin b) F) (right : Fin (2^suffix) → Matrix (Fin b) (Fin b) F)
    (value : Fin b → F) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (testResponse structuredResponse : TestMatrix F (2^front) b → Response → Fin b → Fin (2^suffix) → F)
    (data : JointMatrixOpening.Data F Digest Response (2^front) b height queries)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (recorded : ⟨tag,checkpoint⟩ ∈ state.checkpoints.checkpoints)
    (replays : ∀ column ∈ data.2, ParallelColumnAvailability.Replays enc (fun _ : Cfg => height)
      (AuthenticatedColumnChecks.request (fun _ : Cfg => height) tag checkpoint.root column) state.hash.cache)
    (checked : NativeFactorChecks.check (m := m) domain left right value testResponse structuredResponse data = true)
    (different : value ≠ matrixEvaluation left right
      (MatrixOpeningSecurity.extract domain capacity radius (AmbientMatrixSource.word enc dummy heights tag checkpoint))) :
    SharedMatrixSampling.ArithmeticBad domain capacity radius (AmbientMatrixSource.word enc dummy heights tag checkpoint)
      left right testResponse structuredResponse data.1 ∨
      CheckpointAvailability.Disagreement enc dummy (AmbientMatrixSource.Shape heights) state := by
  subst height
  classical
  by_cases failure : CheckpointAvailability.Disagreement enc dummy (AmbientMatrixSource.Shape heights) state
  · exact Or.inr failure
  left
  obtain ⟨covered,coordinates,finished⟩ := (NativeFactorChecks.check_iff domain left right value testResponse structuredResponse data).mp checked
  have noFailure : ¬ParallelColumnAvailability.Failure enc dummy heights
      (AuthenticatedColumnChecks.requests heights tag checkpoint.root data.2) state :=
    fun bad => failure (ParallelColumnAvailability.failure_implies_disagreement enc dummy _ _ state bad)
  have both := AuthenticatedColumnChecks.matrix_pair_checks_of_authentication enc dummy heights tag checkpoint
    state recorded data.2 data.1.2 covered replays noFailure domain data.1.1.1 (MatrixResponse.weights left)
    (testResponse data.1.1.1 data.1.1.2) (structuredResponse data.1.1.1 data.1.1.2) coordinates
  refine ⟨?_,both.1,both.2⟩
  rwa [finished]

end
end FormalProof4FHE.HasteBoots.AmbientSingleChecks
