module
public import FormalProof4FHE.HasteBoots.AuthenticatedColumnChecks
public import FormalProof4FHE.HasteBoots.RectangularMatrixOpeningKernel
public import FormalProof4FHE.HasteBoots.BatchColumnChecks
@[expose] public section

/-! The native whole-column authentication bridge for unequal packing and
code-symbol widths. The two response families share one availability exception. -/
open OracleSpec OracleComp BinaryTree MerkleTreeMultiExtractability
namespace FormalProof4FHE.HasteBoots.RectangularAuthenticatedColumnChecks
open AuthenticatedColumnChecks
noncomputable section
variable {F Input Digest Cfg : Type} [Field F] [DecidableEq Digest]
  {width leftCount block queries m size : ℕ}

/-- Whole-column authentication and native coordinate checks imply the
rectangular fixed-word checks, preserving the independent code-symbol width. -/
theorem matrix_checks_of_authentication (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
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
    (domain : Fin (2 ^ height tag) → F)
    (weights : Fin width → (Fin leftCount × Fin width) → F) (messages : Fin width → Fin size → F)
    (checked : NativeColumnLayout.Checks columns (NativeColumnLayout.flattenWeights weights)
      (NativeColumnLayout.flattenResponse (RectangularMatrixOpeningKernel.encodeMessages (m := m) (codeWidth := block) domain messages))) :
    RectangularMatrixOpeningKernel.Checks (m := m) (codeWidth := block) domain
      (NativeColumnLayout.expandedWord (frozenWord enc dummy height tag checkpoint)) weights messages draw := by
  have agreed := agrees_of_authentication enc dummy height tag checkpoint state recorded columns draw covered
    replays noFailure (NativeColumnLayout.flattenWeights weights)
      (NativeColumnLayout.flattenResponse (RectangularMatrixOpeningKernel.encodeMessages (m := m) (codeWidth := block) domain messages)) checked
  simpa only [NativeColumnLayout.expanded_flattenWeights, NativeColumnLayout.expanded_flattenResponse,
    RectangularMatrixOpeningKernel.Checks] using agreed

/-- Both native response families use the same columns and source. Applying
the coordinate loop requires only one common authentication exception event. -/
theorem matrix_pair_checks_of_authentication [DecidableEq F]
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (height : Cfg → ℕ) (tag : Cfg)
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
    (domain : Fin (2 ^ height tag) → F)
    (testWeights structuredWeights : Fin width → (Fin leftCount × Fin width) → F)
    (testMessages structuredMessages : Fin width → Fin size → F)
    (checked : NativeColumnLayout.allCoordinates columns
      (NativeColumnLayout.flattenWeights testWeights) (NativeColumnLayout.flattenWeights structuredWeights)
      (NativeColumnLayout.flattenResponse (RectangularMatrixOpeningKernel.encodeMessages (m := m) (codeWidth := block) domain testMessages))
      (NativeColumnLayout.flattenResponse (RectangularMatrixOpeningKernel.encodeMessages (m := m) (codeWidth := block) domain structuredMessages)) = true) :
    RectangularMatrixOpeningKernel.Checks (m := m) (codeWidth := block) domain
      (NativeColumnLayout.expandedWord (frozenWord enc dummy height tag checkpoint)) testWeights testMessages draw ∧
    RectangularMatrixOpeningKernel.Checks (m := m) (codeWidth := block) domain
      (NativeColumnLayout.expandedWord (frozenWord enc dummy height tag checkpoint)) structuredWeights structuredMessages draw := by
  have both := (NativeColumnLayout.allCoordinates_eq_true_iff _ _ _ _ _).mp checked
  exact ⟨matrix_checks_of_authentication enc dummy height tag checkpoint state recorded columns draw covered
      replays noFailure domain testWeights testMessages both.1,
    matrix_checks_of_authentication enc dummy height tag checkpoint state recorded columns draw covered
      replays noFailure domain structuredWeights structuredMessages both.2⟩

/-- All groups share one authenticated word and one availability exception;
the random-test obligation remains present even for zero groups. -/
theorem batch_checks_of_authentication [DecidableEq F] {groups : ℕ}
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest) (height : Cfg → ℕ) (tag : Cfg)
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
    (domain : Fin (2 ^ height tag) → F)
    (testWeights : Fin width → (Fin leftCount × Fin width) → F)
    (structuredWeights : Fin groups → Fin width → (Fin leftCount × Fin width) → F)
    (testMessages : Fin width → Fin size → F)
    (structuredMessages : Fin groups → Fin width → Fin size → F)
    (checked : BatchColumnChecks.allCoordinates columns
      (NativeColumnLayout.flattenWeights testWeights) (fun group => NativeColumnLayout.flattenWeights (structuredWeights group))
      (NativeColumnLayout.flattenResponse (RectangularMatrixOpeningKernel.encodeMessages (m := m) (codeWidth := block) domain testMessages))
      (fun group => NativeColumnLayout.flattenResponse (RectangularMatrixOpeningKernel.encodeMessages (m := m) (codeWidth := block) domain (structuredMessages group))) = true) :
    RectangularMatrixOpeningKernel.Checks (m := m) (codeWidth := block) domain
      (NativeColumnLayout.expandedWord (frozenWord enc dummy height tag checkpoint)) testWeights testMessages draw ∧
    ∀ group, RectangularMatrixOpeningKernel.Checks (m := m) (codeWidth := block) domain
      (NativeColumnLayout.expandedWord (frozenWord enc dummy height tag checkpoint)) (structuredWeights group) (structuredMessages group) draw := by
  have checks := (BatchColumnChecks.allCoordinates_iff _ _ _ _ _).mp checked
  refine ⟨matrix_checks_of_authentication enc dummy height tag checkpoint state recorded columns draw covered
    replays noFailure domain testWeights testMessages checks.1, ?_⟩
  intro group
  exact matrix_checks_of_authentication enc dummy height tag checkpoint state recorded columns draw covered
    replays noFailure domain (structuredWeights group) (structuredMessages group) (checks.2 group)

end
end FormalProof4FHE.HasteBoots.RectangularAuthenticatedColumnChecks
