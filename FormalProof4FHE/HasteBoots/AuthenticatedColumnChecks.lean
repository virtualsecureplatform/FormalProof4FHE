module

public import FormalProof4FHE.HasteBoots.NativeColumnLayout
public import FormalProof4FHE.HasteBoots.ParallelColumnAvailability

@[expose] public section

/-!
# Authenticated native coordinates imply fixed-word opening checks

The common hash payload is a list of field values, allowing different native
column dimensions in one shared oracle. Each opening interprets its immutable
checkpoint word at its own typed dimension with zero fallback. Outside the
joint authentication failure event, received columns equal that fixed word.
The literal native dot-product checks then give every semantic lane check on
the original ordered draws, even though transport sorts and deduplicates them.
The default equal packing/block width specializes to MatrixOpeningSecurity.
This does not assert production challenge freshness or native NTT/Rust refinement.
-/

open OracleSpec OracleComp BinaryTree MerkleTreeMultiExtractability

namespace FormalProof4FHE.HasteBoots.AuthenticatedColumnChecks

noncomputable section

variable {F Input Digest Cfg : Type} [Field F] [DecidableEq Digest]
  {width leftCount block queries m size : ℕ}

/-- Assign this verifier's context, root and index to one typed proof column. -/
def request (height : Cfg → ℕ) (tag : Cfg) (root : Digest)
    (column : NativeColumnLayout.Column F Digest (height tag) (leftCount * width) block) :
    NativeOpeningAvailability.Request (Digest := Digest) (Payload := List F) height where
  tag := tag
  root := root
  position := column.position
  payload := NativeColumnLayout.packPayload column.values
  leaf := column.leaf
  siblings := column.siblings

def requests (height : Cfg → ℕ) (tag : Cfg) (root : Digest)
    (columns : List (NativeColumnLayout.Column F Digest (height tag) (leftCount * width) block)) :
    List (NativeOpeningAvailability.Request (Digest := Digest) (Payload := List F) height) :=
  columns.map (request height tag root)

/-- This opening's typed interpretation of one prefix-only whole-payload word. -/
def frozenWord (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (height : Cfg → ℕ) (tag : Cfg)
    (checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) tag) :
    Fin (2 ^ height tag) → Fin ((leftCount * width) * block) → F :=
  fun position => NativeColumnLayout.unpackPayload ((leftCount * width) * block)
    (MerkleAvailability.word enc dummy [] (height tag) checkpoint.cumulativeLog checkpoint.root position)

/-- A replay-accepted whole column equals this opening's typed frozen word,
including when other contexts in the shared hash use different payload lengths. -/
theorem values_of_no_failure (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (height : Cfg → ℕ) (tag : Cfg)
    (checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) tag)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest)
      (fun tag => Skeleton.perfect (height tag)))
    (recorded : ⟨tag, checkpoint⟩ ∈ state.checkpoints.checkpoints)
    (columns : List (NativeColumnLayout.Column F Digest (height tag) (leftCount * width) block))
    (replays : ∀ column ∈ columns,
      ParallelColumnAvailability.Replays enc height (request height tag checkpoint.root column) state.hash.cache)
    (noFailure : ¬ParallelColumnAvailability.Failure enc dummy height
      (requests height tag checkpoint.root columns) state) :
    ∀ column ∈ columns, column.values = frozenWord enc dummy height tag checkpoint column.position := by
  intro column member
  by_contra different
  apply noFailure
  apply ParallelColumnAvailability.failure_of_word_disagreement enc dummy height _ state
    (request height tag checkpoint.root column) (List.mem_map.mpr ⟨column, member, rfl⟩) (replays column member)
    checkpoint recorded rfl []
  intro equal
  change MerkleAvailability.word enc dummy [] (height tag) checkpoint.cumulativeLog checkpoint.root column.position =
    NativeColumnLayout.packPayload column.values at equal
  apply different
  change column.values = NativeColumnLayout.unpackPayload ((leftCount * width) * block)
    (MerkleAvailability.word enc dummy [] (height tag) checkpoint.cumulativeLog checkpoint.root column.position)
  rw [equal, NativeColumnLayout.unpack_packPayload]

/-- Authentication and the native coordinate loop give the common-word lane
checks on every original draw. Packing and symbol widths remain independent. -/
theorem agrees_of_authentication (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (height : Cfg → ℕ) (tag : Cfg)
    (checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) tag)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest)
      (fun tag => Skeleton.perfect (height tag)))
    (recorded : ⟨tag, checkpoint⟩ ∈ state.checkpoints.checkpoints)
    (columns : List (NativeColumnLayout.Column F Digest (height tag) (leftCount * width) block))
    (draw : Fin queries → Fin (2 ^ height tag)) (covered : NativeColumnLayout.Covers columns draw)
    (replays : ∀ column ∈ columns,
      ParallelColumnAvailability.Replays enc height (request height tag checkpoint.root column) state.hash.cache)
    (noFailure : ¬ParallelColumnAvailability.Failure enc dummy height
      (requests height tag checkpoint.root columns) state)
    (weights : Fin (width * (leftCount * width)) → F)
    (response : Fin (width * ((2 ^ height tag) * block)) → F)
    (checked : NativeColumnLayout.Checks columns weights response) :
    ∀ lane, ColumnOpening.Agrees
      (StructuredOpening.combine (NativeColumnLayout.expandedWeights weights lane)
        (NativeColumnLayout.expandedWord (frozenWord enc dummy height tag checkpoint)))
      (NativeColumnLayout.expandedResponse response lane) draw :=
  NativeColumnLayout.agrees_of_checks columns draw covered _
    (values_of_no_failure enc dummy height tag checkpoint state recorded columns replays noFailure)
    weights response checked

/-- The documented equal-width default instantiates the exact fixed-word
checks used by the existing matrix-opening theorem, with native padded responses. -/
theorem matrix_checks_of_authentication (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (height : Cfg → ℕ) (tag : Cfg)
    (checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) tag)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest)
      (fun tag => Skeleton.perfect (height tag)))
    (recorded : ⟨tag, checkpoint⟩ ∈ state.checkpoints.checkpoints)
    (columns : List (NativeColumnLayout.Column F Digest (height tag) (leftCount * width) width))
    (draw : Fin queries → Fin (2 ^ height tag)) (covered : NativeColumnLayout.Covers columns draw)
    (replays : ∀ column ∈ columns,
      ParallelColumnAvailability.Replays enc height (request height tag checkpoint.root column) state.hash.cache)
    (noFailure : ¬ParallelColumnAvailability.Failure enc dummy height
      (requests height tag checkpoint.root columns) state)
    (domain : Fin (2 ^ height tag) → F)
    (weights : Fin width → (Fin leftCount × Fin width) → F) (messages : Fin width → Fin size → F)
    (checked : NativeColumnLayout.Checks columns (NativeColumnLayout.flattenWeights weights)
      (NativeColumnLayout.flattenResponse (MatrixOpeningSecurity.encodeMessages (m := m) domain messages))) :
    MatrixOpeningSecurity.Checks (m := m) domain
      (NativeColumnLayout.expandedWord (frozenWord enc dummy height tag checkpoint)) weights messages draw := by
  have agreed := agrees_of_authentication enc dummy height tag checkpoint state recorded columns draw covered
    replays noFailure (NativeColumnLayout.flattenWeights weights)
      (NativeColumnLayout.flattenResponse (MatrixOpeningSecurity.encodeMessages (m := m) domain messages)) checked
  simpa only [NativeColumnLayout.expanded_flattenWeights, NativeColumnLayout.expanded_flattenResponse,
    MatrixOpeningSecurity.Checks] using agreed

/-- Both native response families use the same columns and source. Applying
the coordinate loop requires only one common authentication exception event. -/
theorem matrix_pair_checks_of_authentication [DecidableEq F]
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (height : Cfg → ℕ) (tag : Cfg)
    (checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) tag)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest)
      (fun tag => Skeleton.perfect (height tag)))
    (recorded : ⟨tag, checkpoint⟩ ∈ state.checkpoints.checkpoints)
    (columns : List (NativeColumnLayout.Column F Digest (height tag) (leftCount * width) width))
    (draw : Fin queries → Fin (2 ^ height tag)) (covered : NativeColumnLayout.Covers columns draw)
    (replays : ∀ column ∈ columns,
      ParallelColumnAvailability.Replays enc height (request height tag checkpoint.root column) state.hash.cache)
    (noFailure : ¬ParallelColumnAvailability.Failure enc dummy height
      (requests height tag checkpoint.root columns) state)
    (domain : Fin (2 ^ height tag) → F)
    (testWeights structuredWeights : Fin width → (Fin leftCount × Fin width) → F)
    (testMessages structuredMessages : Fin width → Fin size → F)
    (checked : NativeColumnLayout.allCoordinates columns
      (NativeColumnLayout.flattenWeights testWeights) (NativeColumnLayout.flattenWeights structuredWeights)
      (NativeColumnLayout.flattenResponse (MatrixOpeningSecurity.encodeMessages (m := m) domain testMessages))
      (NativeColumnLayout.flattenResponse (MatrixOpeningSecurity.encodeMessages (m := m) domain structuredMessages)) = true) :
    MatrixOpeningSecurity.Checks (m := m) domain
      (NativeColumnLayout.expandedWord (frozenWord enc dummy height tag checkpoint)) testWeights testMessages draw ∧
    MatrixOpeningSecurity.Checks (m := m) domain
      (NativeColumnLayout.expandedWord (frozenWord enc dummy height tag checkpoint)) structuredWeights structuredMessages draw := by
  have both := (NativeColumnLayout.allCoordinates_eq_true_iff _ _ _ _ _).mp checked
  exact ⟨matrix_checks_of_authentication enc dummy height tag checkpoint state recorded columns draw covered
      replays noFailure domain testWeights testMessages both.1,
    matrix_checks_of_authentication enc dummy height tag checkpoint state recorded columns draw covered
      replays noFailure domain structuredWeights structuredMessages both.2⟩

/-- One coordinate-response family of an opening; all dimensions are trusted
parameters and the raw shape guards are represented by these finite types. -/
structure View (F Digest : Type) (height leftCount width block queries : ℕ) where
  root : Digest
  columns : List (NativeColumnLayout.Column F Digest height (leftCount * width) block)
  draw : Fin queries → Fin (2 ^ height)
  weights : Fin (width * (leftCount * width)) → F
  response : Fin (width * ((2 ^ height) * block)) → F

/-- Native authenticated coordinate checks pass but the corresponding
common-source checks fail for a matching immutable checkpoint. -/
def Failure (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (height : Cfg → ℕ) (tag : Cfg)
    (view : View F Digest (height tag) leftCount width block queries)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest)
      (fun tag => Skeleton.perfect (height tag))) : Prop :=
  ∃ checkpoint : Checkpoint Input Digest
      (MerklePayloadCheckpoints.configuration (fun tag => Skeleton.perfect (height tag))) tag,
    ⟨tag, checkpoint⟩ ∈ state.checkpoints.checkpoints ∧ checkpoint.root = view.root ∧
    NativeColumnLayout.Covers view.columns view.draw ∧
    (∀ column ∈ view.columns,
      ParallelColumnAvailability.Replays enc height (request height tag view.root column) state.hash.cache) ∧
    NativeColumnLayout.Checks view.columns view.weights view.response ∧
    ¬∀ lane, ColumnOpening.Agrees
      (StructuredOpening.combine (NativeColumnLayout.expandedWeights view.weights lane)
        (NativeColumnLayout.expandedWord (frozenWord enc dummy height tag checkpoint)))
      (NativeColumnLayout.expandedResponse view.response lane) view.draw

/-- A failed transport of either native response family is covered by the same
joint column-availability event; there is no additional per-coordinate loss. -/
theorem failure_implies_availability (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (height : Cfg → ℕ) (tag : Cfg)
    (view : View F Digest (height tag) leftCount width block queries)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest)
      (fun tag => Skeleton.perfect (height tag))) (failure : Failure enc dummy height tag view state) :
    ParallelColumnAvailability.Failure enc dummy height (requests height tag view.root view.columns) state := by
  obtain ⟨checkpoint, recorded, root, covered, replays, checked, different⟩ := failure
  by_contra noFailure
  apply different
  apply agrees_of_authentication enc dummy height tag checkpoint state recorded view.columns view.draw covered
    _ _ view.weights view.response checked
  · simpa only [root] using replays
  · simpa only [root] using noFailure

section Runtime

variable [DecidableEq Input] [SampleableType Digest] [Fintype Digest] {ι : Type} {base : OracleSpec ι}

/-- The complete shared-oracle execution pays only the existing hash-availability
charge for transporting native coordinate checks to the frozen common word. -/
theorem failure_le_charge (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (height : Cfg → ℕ) (tag : Cfg)
    (program : OracleComp (CheckpointExecution.Spec base Cfg Input Digest)
      (View F Digest (height tag) leftCount width block queries))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest)
      (fun tag => Skeleton.perfect (height tag)))
    (safe : CheckpointCollision.Safe enc dummy (fun tag => Skeleton.perfect (height tag)) state) :
    Pr{let result ← (simulateQ
      (CheckpointExecution.handler implBase enc dummy (fun tag => Skeleton.perfect (height tag))) program).run state}[
        Failure enc dummy height tag result.1 result.2] ≤
      ExpectedHazard.charge
        (CheckpointExecution.handler implBase enc dummy (fun tag => Skeleton.perfect (height tag)))
        (CheckpointCollision.loss base (fun tag => Skeleton.perfect (height tag))) program state := by
  apply le_trans (prEvent_mono _ _ _ ?_)
    (CheckpointAvailability.disagreement_le_charge implBase enc dummy
      (fun tag => Skeleton.perfect (height tag)) program state safe)
  intro result failure
  exact ParallelColumnAvailability.failure_implies_disagreement enc dummy height _ result.2
    (failure_implies_availability enc dummy height tag result.1 result.2 failure)

/-- Empty initialization supplies the canonical initial safety invariant. -/
theorem failure_from_empty_le_charge (implBase : QueryImpl base ProbComp)
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (height : Cfg → ℕ) (tag : Cfg)
    (program : OracleComp (CheckpointExecution.Spec base Cfg Input Digest)
      (View F Digest (height tag) leftCount width block queries)) :
    Pr{let result ← (simulateQ
      (CheckpointExecution.handler implBase enc dummy (fun tag => Skeleton.perfect (height tag))) program).run
        (CheckpointExecution.empty (fun tag => Skeleton.perfect (height tag)))}[
          Failure enc dummy height tag result.1 result.2] ≤
      ExpectedHazard.charge
        (CheckpointExecution.handler implBase enc dummy (fun tag => Skeleton.perfect (height tag)))
        (CheckpointCollision.loss base (fun tag => Skeleton.perfect (height tag))) program
        (CheckpointExecution.empty (fun tag => Skeleton.perfect (height tag))) :=
  failure_le_charge implBase enc dummy height tag program _
    (CheckpointCollision.safe_empty enc dummy (fun tag => Skeleton.perfect (height tag)))

end Runtime

end

end FormalProof4FHE.HasteBoots.AuthenticatedColumnChecks
