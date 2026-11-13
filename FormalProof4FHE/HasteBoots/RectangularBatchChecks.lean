module
public import FormalProof4FHE.HasteBoots.NativeBatchChecks
public import FormalProof4FHE.HasteBoots.RectangularAuthenticatedColumnChecks
public import FormalProof4FHE.HasteBoots.SharedRectangularBatchSampling
public import FormalProof4FHE.HasteBoots.AmbientRectangularSource
@[expose] public section
open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
namespace FormalProof4FHE.HasteBoots.RectangularBatchChecks
open NativeBatchChecks
noncomputable section
abbrev Columns (F Digest : Type) (front b block height : ℕ) :=
  List (NativeColumnLayout.Column F Digest height (2^front*b) block)
abbrev Data (F Digest Response : Type) (front b block height queries : ℕ) :=
  SampleData F Response (2^front) b height queries × Columns F Digest front b block height
variable {F Digest Response : Type} [Field F] [DecidableEq F]
  {b block front suffix claims m queries height : ℕ}

def coversCheck (columns : Columns F Digest front b block height) (draw : Fin queries → Fin (2^height)) : Bool :=
  (List.ofFn draw).all (fun position => columns.any (fun column => column.position == position))
omit [Field F] [DecidableEq F] in
theorem coversCheck_iff (columns : Columns F Digest front b block height) (draw : Fin queries → Fin (2^height)) :
    coversCheck columns draw = true ↔ NativeColumnLayout.Covers columns draw := by
  simp [coversCheck, NativeColumnLayout.Covers, List.all_eq_true, List.any_eq_true, List.mem_ofFn]

def coordinates (domain : Fin (2 ^ height) ↪ F) (query : QueryFamily F b front suffix claims)
    (testResponse : TestMatrix F (2 ^ front) b → Response → Fin b → Fin (2 ^ suffix) → F)
    (groupResponse : ℕ → TestMatrix F (2 ^ front) b → Response → Fin b → Fin (2 ^ suffix) → F)
    (data : Data F Digest Response front b block height queries) : Bool :=
  BatchColumnChecks.allCoordinates data.2 (NativeColumnLayout.flattenWeights data.1.1.1)
    (fun group => NativeColumnLayout.flattenWeights (MatrixResponse.weights (groupLeft (front := front) (suffix := suffix) query group)))
    (NativeColumnLayout.flattenResponse (RectangularMatrixOpeningKernel.encodeMessages (m := m) (codeWidth := block) domain
      (testResponse data.1.1.1 data.1.1.2)))
    (fun group => NativeColumnLayout.flattenResponse (RectangularMatrixOpeningKernel.encodeMessages (m := m) (codeWidth := block) domain
      (groupResponse group.val data.1.1.1 data.1.1.2)))

def check (domain : Fin (2 ^ height) ↪ F) (query : QueryFamily F b front suffix claims)
    (values : Fin claims → Fin b → F)
    (testResponse : TestMatrix F (2 ^ front) b → Response → Fin b → Fin (2 ^ suffix) → F)
    (groupResponse : ℕ → TestMatrix F (2 ^ front) b → Response → Fin b → Fin (2 ^ suffix) → F)
    (data : Data F Digest Response front b block height queries) : Bool :=
  coversCheck data.2 data.1.2 &&
  coordinates (m := m) domain query testResponse groupResponse data &&
  (List.ofFn fun claim : Fin claims => decide (
    MatrixResponse.finishMessage (right (front := front) (suffix := suffix) query claim)
      (structured query groupResponse claim data.1.1.1 data.1.1.2) = values claim)).all id

theorem check_iff (domain : Fin (2 ^ height) ↪ F) (query : QueryFamily F b front suffix claims)
    (values : Fin claims → Fin b → F)
    (testResponse : TestMatrix F (2 ^ front) b → Response → Fin b → Fin (2 ^ suffix) → F)
    (groupResponse : ℕ → TestMatrix F (2 ^ front) b → Response → Fin b → Fin (2 ^ suffix) → F)
    (data : Data F Digest Response front b block height queries) :
    check (m := m) domain query values testResponse groupResponse data = true ↔
      NativeColumnLayout.Covers data.2 data.1.2 ∧ coordinates (m := m) domain query testResponse groupResponse data = true ∧
      ∀ claim, MatrixResponse.finishMessage (right (front := front) (suffix := suffix) query claim)
        (structured query groupResponse claim data.1.1.1 data.1.1.2) = values claim := by
  simp [check, coversCheck_iff, List.all_eq_true, List.mem_ofFn, and_assoc]


variable {Input Cfg : Type} [DecidableEq Input] [DecidableEq Digest]

/-- Native replay plus successful literal checks yields arithmetic failure or
one root-wide exception, uniformly over all batch queries and shared columns. -/
theorem wrong_implies_arithmetic_or_disagreement
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (tag : Cfg)
    (checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun _ : Cfg => Skeleton.perfect height)) tag)
    (domain : Fin (2 ^ height) ↪ F) (query : QueryFamily F b front suffix claims)
    (values : Fin claims → Fin b → F) (capacity : 2 ^ suffix ≤ m * block) (radius : ℕ)
    (testResponse : TestMatrix F (2 ^ front) b → Response → Fin b → Fin (2 ^ suffix) → F)
    (groupResponse : ℕ → TestMatrix F (2 ^ front) b → Response → Fin b → Fin (2 ^ suffix) → F)
    (data : Data F Digest Response front b block height queries)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (recorded : ⟨tag, checkpoint⟩ ∈ state.checkpoints.checkpoints)
    (replays : ∀ column ∈ data.2, ParallelColumnAvailability.Replays enc (fun _ : Cfg => height)
      (AuthenticatedColumnChecks.request (fun _ : Cfg => height) tag checkpoint.root column) state.hash.cache)
    (checked : check (m := m) domain query values testResponse groupResponse data = true)
    (different : ∃ claim, values claim ≠ matrixEvaluation (left (front := front) (suffix := suffix) query claim)
      (right (front := front) (suffix := suffix) query claim)
      (RectangularMatrixOpeningKernel.extract domain capacity radius (AmbientRectangularSource.word (height := height) enc dummy (fun _ : Cfg => height) tag checkpoint))) :
    SharedRectangularBatchSampling.ArithmeticBad domain capacity radius
      (AmbientRectangularSource.word (height := height) enc dummy (fun _ : Cfg => height) tag checkpoint)
      (BatchQueryLayout.groupOf (front := front) (suffix := suffix) query)
      (groupLeft (front := front) (suffix := suffix) query) (right (front := front) (suffix := suffix) query)
      testResponse (fun matrix response group => groupResponse group.val matrix response) data.1 ∨
      CheckpointAvailability.Disagreement enc dummy (fun _ : Cfg => Skeleton.perfect height) state := by
  classical
  by_cases failure : CheckpointAvailability.Disagreement enc dummy (fun _ : Cfg => Skeleton.perfect height) state
  · exact Or.inr failure
  left
  obtain ⟨covered, coordinates, finished⟩ := (check_iff domain query values testResponse groupResponse data).mp checked
  have noFailure : ¬ParallelColumnAvailability.Failure enc dummy (fun _ : Cfg => height)
      (AuthenticatedColumnChecks.requests (fun _ : Cfg => height) tag checkpoint.root data.2) state :=
    fun bad => failure (ParallelColumnAvailability.failure_implies_disagreement enc dummy _ _ state bad)
  have checks := RectangularAuthenticatedColumnChecks.batch_checks_of_authentication enc dummy
    (fun _ : Cfg => height) tag checkpoint state recorded data.2 data.1.2 covered replays noFailure domain
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

end
end FormalProof4FHE.HasteBoots.RectangularBatchChecks
