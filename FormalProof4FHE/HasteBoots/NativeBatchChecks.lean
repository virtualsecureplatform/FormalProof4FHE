module

public import FormalProof4FHE.HasteBoots.BatchQueryLayout
public import FormalProof4FHE.HasteBoots.BatchColumnChecks
public import FormalProof4FHE.HasteBoots.BatchMatrixSampling
public import FormalProof4FHE.HasteBoots.NativeFactorChecks

@[expose] public section

/-!
# Coverage, grouped coordinates and every native batch finish value

Grouping is computed from trusted ordered query prefixes. Every original query,
including nonrepresentatives, checks its own suffix finish against its supplied
value. Coverage concerns the original with-replacement column draws. Actual
worker replay and these literal checks imply batch arithmetic failure or the
one common availability exception on the same final cache. No commitment
security or per-query independence certificate is assumed.
-/

open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening

namespace FormalProof4FHE.HasteBoots.NativeBatchChecks

noncomputable section

variable {F Digest Response : Type} [Field F] [DecidableEq F]
  {b front suffix claims m queries height : ℕ}

/-- Typed native position attachment: nonempty columns occur in the sorted,
deduplicated sample order before any authentication worker is started. -/
def columnsCheck {rows block : ℕ}
    (columns : List (NativeColumnLayout.Column F Digest height rows block))
    (draw : Fin queries → Fin (2 ^ height)) : Bool :=
  (!columns.isEmpty) && decide (columns.map NativeColumnLayout.Column.position = NativeColumnLayout.distinctIndices draw)

omit [Field F] [DecidableEq F] in
theorem columnsCheck_iff {rows block : ℕ}
    (columns : List (NativeColumnLayout.Column F Digest height rows block))
    (draw : Fin queries → Fin (2 ^ height)) :
    columnsCheck columns draw = true ↔ columns ≠ [] ∧
      columns.map NativeColumnLayout.Column.position = NativeColumnLayout.distinctIndices draw := by
  simp [columnsCheck]

omit [Field F] [DecidableEq F] in
theorem columnsCheck_covers {rows block : ℕ}
    (columns : List (NativeColumnLayout.Column F Digest height rows block))
    (draw : Fin queries → Fin (2 ^ height)) (checked : columnsCheck columns draw = true) :
    NativeColumnLayout.Covers columns draw := by
  intro index
  have selected : draw index ∈ columns.map NativeColumnLayout.Column.position := by
    rw [(columnsCheck_iff columns draw).mp checked |>.2]
    exact NativeColumnLayout.mem_distinctIndices draw index
  exact List.mem_map.mp selected

abbrev QueryFamily (F : Type) (b front suffix claims : ℕ) :=
  Fin claims → PackedSumcheckSubclaim.Query F b (front + suffix)

def left (query : QueryFamily F b front suffix claims) (claim : Fin claims) :=
  SubclaimSourceLayout.leftWeights (front := front) (suffix := suffix) (query claim)

def right (query : QueryFamily F b front suffix claims) (claim : Fin claims) :=
  SubclaimSourceLayout.rightWeights (front := front) (suffix := suffix) (query claim)

def groupLeft (query : QueryFamily F b front suffix claims)
    (group : Fin (BatchQueryLayout.groupCount (front := front) (suffix := suffix) query)) :=
  left (front := front) (suffix := suffix) query
    (BatchQueryLayout.representative (front := front) (suffix := suffix) query group)

def structured (query : QueryFamily F b front suffix claims)
    (response : ℕ → TestMatrix F (2 ^ front) b → Response → Fin b → Fin (2 ^ suffix) → F) (claim : Fin claims) :=
  response (BatchQueryLayout.groupOf (front := front) (suffix := suffix) query claim).val

theorem group_left_eq (query : QueryFamily F b front suffix claims) (claim : Fin claims) :
    groupLeft (front := front) (suffix := suffix) query (BatchQueryLayout.groupOf (front := front) (suffix := suffix) query claim) =
      left (front := front) (suffix := suffix) query claim :=
  BatchQueryLayout.representative_left (front := front) (suffix := suffix) query claim

def coordinates (domain : Fin (2 ^ height) ↪ F) (query : QueryFamily F b front suffix claims)
    (testResponse : TestMatrix F (2 ^ front) b → Response → Fin b → Fin (2 ^ suffix) → F)
    (groupResponse : ℕ → TestMatrix F (2 ^ front) b → Response → Fin b → Fin (2 ^ suffix) → F)
    (data : JointMatrixOpening.Data F Digest Response (2 ^ front) b height queries) : Bool :=
  BatchColumnChecks.allCoordinates data.2 (NativeColumnLayout.flattenWeights data.1.1.1)
    (fun group => NativeColumnLayout.flattenWeights (MatrixResponse.weights (groupLeft (front := front) (suffix := suffix) query group)))
    (NativeColumnLayout.flattenResponse (MatrixOpeningSecurity.encodeMessages (m := m) domain
      (testResponse data.1.1.1 data.1.1.2)))
    (fun group => NativeColumnLayout.flattenResponse (MatrixOpeningSecurity.encodeMessages (m := m) domain
      (groupResponse group.val data.1.1.1 data.1.1.2)))

def check (domain : Fin (2 ^ height) ↪ F) (query : QueryFamily F b front suffix claims)
    (values : Fin claims → Fin b → F)
    (testResponse : TestMatrix F (2 ^ front) b → Response → Fin b → Fin (2 ^ suffix) → F)
    (groupResponse : ℕ → TestMatrix F (2 ^ front) b → Response → Fin b → Fin (2 ^ suffix) → F)
    (data : JointMatrixOpening.Data F Digest Response (2 ^ front) b height queries) : Bool :=
  NativeFactorChecks.coversCheck data.2 data.1.2 &&
  coordinates (m := m) domain query testResponse groupResponse data &&
  (List.ofFn fun claim : Fin claims => decide (
    MatrixResponse.finishMessage (right (front := front) (suffix := suffix) query claim)
      (structured query groupResponse claim data.1.1.1 data.1.1.2) = values claim)).all id

theorem check_iff (domain : Fin (2 ^ height) ↪ F) (query : QueryFamily F b front suffix claims)
    (values : Fin claims → Fin b → F)
    (testResponse : TestMatrix F (2 ^ front) b → Response → Fin b → Fin (2 ^ suffix) → F)
    (groupResponse : ℕ → TestMatrix F (2 ^ front) b → Response → Fin b → Fin (2 ^ suffix) → F)
    (data : JointMatrixOpening.Data F Digest Response (2 ^ front) b height queries) :
    check (m := m) domain query values testResponse groupResponse data = true ↔
      NativeColumnLayout.Covers data.2 data.1.2 ∧ coordinates (m := m) domain query testResponse groupResponse data = true ∧
      ∀ claim, MatrixResponse.finishMessage (right (front := front) (suffix := suffix) query claim)
        (structured query groupResponse claim data.1.1.1 data.1.1.2) = values claim := by
  simp [check, NativeFactorChecks.coversCheck_iff, List.all_eq_true, List.mem_ofFn, and_assoc]

/-- Each query receives coordinate checks for its own left weights, despite
sharing the representative's structured message. Its right query stays its own. -/
theorem coordinates_claim (domain : Fin (2 ^ height) ↪ F) (query : QueryFamily F b front suffix claims)
    (testResponse : TestMatrix F (2 ^ front) b → Response → Fin b → Fin (2 ^ suffix) → F)
    (groupResponse : ℕ → TestMatrix F (2 ^ front) b → Response → Fin b → Fin (2 ^ suffix) → F)
    (data : JointMatrixOpening.Data F Digest Response (2 ^ front) b height queries)
    (checked : coordinates (m := m) domain query testResponse groupResponse data = true) (claim : Fin claims) :
    NativeColumnLayout.allCoordinates data.2 (NativeColumnLayout.flattenWeights data.1.1.1)
      (NativeColumnLayout.flattenWeights (MatrixResponse.weights (left (front := front) (suffix := suffix) query claim)))
      (NativeColumnLayout.flattenResponse (MatrixOpeningSecurity.encodeMessages (m := m) domain (testResponse data.1.1.1 data.1.1.2)))
      (NativeColumnLayout.flattenResponse (MatrixOpeningSecurity.encodeMessages (m := m) domain
        (structured query groupResponse claim data.1.1.1 data.1.1.2))) = true := by
  have pair := BatchColumnChecks.pair_coordinates data.2 _ _ _ _ checked
    (BatchQueryLayout.groupOf (front := front) (suffix := suffix) query claim)
  simpa only [group_left_eq, structured] using pair

variable {Input Cfg : Type} [DecidableEq Input] [DecidableEq Digest]

/-- Native replay plus successful literal checks yields arithmetic failure or
one root-wide exception, uniformly over all batch queries and shared columns. -/
theorem wrong_implies_arithmetic_or_disagreement
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (tag : Cfg)
    (checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun _ : Cfg => Skeleton.perfect height)) tag)
    (domain : Fin (2 ^ height) ↪ F) (query : QueryFamily F b front suffix claims)
    (values : Fin claims → Fin b → F) (capacity : 2 ^ suffix ≤ m * b) (radius : ℕ)
    (testResponse : TestMatrix F (2 ^ front) b → Response → Fin b → Fin (2 ^ suffix) → F)
    (groupResponse : ℕ → TestMatrix F (2 ^ front) b → Response → Fin b → Fin (2 ^ suffix) → F)
    (data : JointMatrixOpening.Data F Digest Response (2 ^ front) b height queries)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun _ : Cfg => Skeleton.perfect height))
    (recorded : ⟨tag, checkpoint⟩ ∈ state.checkpoints.checkpoints)
    (replays : ∀ column ∈ data.2, ParallelColumnAvailability.Replays enc (fun _ : Cfg => height)
      (AuthenticatedColumnChecks.request (fun _ : Cfg => height) tag checkpoint.root column) state.hash.cache)
    (checked : check (m := m) domain query values testResponse groupResponse data = true)
    (different : ∃ claim, values claim ≠ matrixEvaluation (left (front := front) (suffix := suffix) query claim)
      (right (front := front) (suffix := suffix) query claim)
      (MatrixOpeningSecurity.extract domain capacity radius (word enc dummy (fun _ : Cfg => height) tag checkpoint))) :
    BatchMatrixSampling.ArithmeticBad domain capacity radius (word enc dummy (fun _ : Cfg => height) tag checkpoint)
      (left (front := front) (suffix := suffix) query) (right (front := front) (suffix := suffix) query) values
      testResponse (structured query groupResponse) data.1 ∨
      CheckpointAvailability.Disagreement enc dummy (fun _ : Cfg => Skeleton.perfect height) state := by
  classical
  by_cases failure : CheckpointAvailability.Disagreement enc dummy (fun _ : Cfg => Skeleton.perfect height) state
  · exact Or.inr failure
  left
  obtain ⟨covered, coordinates, finished⟩ := (check_iff domain query values testResponse groupResponse data).mp checked
  have noFailure : ¬ParallelColumnAvailability.Failure enc dummy (fun _ : Cfg => height)
      (AuthenticatedColumnChecks.requests (fun _ : Cfg => height) tag checkpoint.root data.2) state :=
    fun bad => failure (ParallelColumnAvailability.failure_implies_disagreement enc dummy _ _ state bad)
  have checks (claim : Fin claims) := AuthenticatedColumnChecks.matrix_pair_checks_of_authentication enc dummy
    (fun _ : Cfg => height) tag checkpoint state recorded data.2 data.1.2 covered replays noFailure domain
    data.1.1.1 (MatrixResponse.weights (left (front := front) (suffix := suffix) query claim))
    (testResponse data.1.1.1 data.1.1.2) (structured query groupResponse claim data.1.1.1 data.1.1.2)
    (coordinates_claim domain query testResponse groupResponse data coordinates claim)
  obtain ⟨claim, wrong⟩ := different
  exact ⟨⟨claim, wrong⟩, (checks claim).1, fun claim => (checks claim).2, finished⟩

end

end FormalProof4FHE.HasteBoots.NativeBatchChecks
