module
public import FormalProof4FHE.HasteBoots.ExecutedComparisonOwners
public import FormalProof4FHE.HasteBoots.ExecutedPaddedSourceFamily
public import FormalProof4FHE.HasteBoots.PaddedReconstructionComparison
public import FormalProof4FHE.HasteBoots.RecordedSourceWorld
public import FormalProof4FHE.HasteBoots.CheckpointHistoryChain
@[expose] public section

/-! The reached comparison's original owners are decoded with the predecessor
reconstruction descriptors. Their canonical indices are those reconstruction
slots on actual support, including newly committed borrow columns. -/
namespace FormalProof4FHE.HasteBoots.ExecutedComparisonWorld
open OracleSpec OracleComp BinaryTree
open NativeRootMessage (Digest)
noncomputable section
variable {F Cfg Input Response Memory CommitMemory Helper Result : Type}
  [Field F] [DecidableEq Input] [DecidableEq Digest]
  {H : Cfg → ℕ} {d b n : ℕ}
variable (s : PaddedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory H (2*d+2) b n)
    (comparison : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Result d)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*b) (radius : Fin (2*d+2) → ℕ)
    (before : PaddedReconstructionComparison.Before s)
    (outcome : PackedPBSComparisonStage.Outcome (PaddedReconstructionComparison.stage s comparison))

/-- Decode the actual original owners with the reconstruction's public layout;
lookup interpretation later checks that its source descriptor is this layout. -/
def sourceFamily : RecordedPaddedSourceFamily.Family F Cfg Input Digest (Fin (2*d+1)) H b where
  parameters := fun source => PaddedStageSourceInterpretation.linearParameters s capacity radius (PackedPBSComparisonReferences.linearSlot source)
  roots := outcome.1.1.1
  owners := ExecutedComparisonOwners.owners (PaddedReconstructionComparison.stage s comparison) outcome
  ownerRoots := fun _ => rfl

variable [SampleableType Digest] (dummy : Digest)
    (supported : some outcome ∈ support (PaddedReconstructionComparison.continuation s comparison dummy before))

include supported in
theorem recorded : RecordedPaddedSourceFamily.Recorded (sourceFamily s comparison capacity radius outcome) outcome.2.2.2 := by
  intro source
  exact ExecutedComparisonOwners.recorded s.encoding dummy (PaddedReconstructionComparison.stage s comparison)
    before.1.1.1 before.2.1.2.memory before.2.2 outcome
    (PaddedReconstructionComparison.reached s comparison dummy before outcome supported).2 source

include supported in
theorem root_eq (source : Fin (2*d+1)) :
    (sourceFamily s comparison capacity radius outcome).roots source =
      (ExecutedPaddedSourceFamily.linearFamily s capacity radius before.1).roots (PackedPBSComparisonReferences.linearSlot source) :=
  congrArg (fun emission => emission.1 source) (PaddedReconstructionComparison.sources s comparison dummy before outcome supported).1

variable (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (retained : CheckpointHistoryChain.Retains outcome.2.2.2 state)

include supported retained in
theorem final_recorded : RecordedPaddedSourceFamily.Recorded (sourceFamily s comparison capacity radius outcome) state :=
  CheckpointHistoryChain.family_recorded _ _ _ retained (recorded s comparison capacity radius before outcome dummy supported)

variable [Fintype F] [DecidableEq F] [SampleableType (Fin b → F)]
  [∀ factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix F (2^(s.code factor).front) b)]
  [∀ factor, SampleableType (Fin (s.code factor).queries → Fin (2^H (s.tag factor)))]
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
  (beforeSupported : before ∈ support (PaddedLinear.witness s dummy initial))

include supported beforeSupported retained in
/-- The actual reached comparison retains the predecessor reconstruction's
entire recorded family, including its newly emitted borrow roots. -/
theorem reconstruction_recorded : RecordedPaddedSourceFamily.Recorded
    (ExecutedPaddedSourceFamily.linearFamily s capacity radius before.1) state := by
  have middle : CheckpointHistoryChain.Retains before.2.2 outcome.2.2.2 := by
    intro tag saved present
    exact PackedPBSComparisonStage.retains s.encoding dummy (PaddedReconstructionComparison.stage s comparison)
      before.1.1.1 before.2.1.2.memory before.2.2 tag saved present outcome
      (PaddedReconstructionComparison.reached s comparison dummy before outcome supported).2
  exact CheckpointHistoryChain.family_recorded _ _ _ (CheckpointHistoryChain.trans middle retained)
    (ExecutedPaddedSourceFamily.linear_recorded_witness s dummy capacity radius initial before beforeSupported)

include supported beforeSupported retained in
/-- Every original comparison column is the reconstruction slot selected by
native source order. No root/owner/decoded-value association is supplied. -/
theorem source_slot (source : Fin (2*d+1)) :
    RecordedSourceWorld.slot (sourceFamily s comparison capacity radius outcome) state
      (final_recorded s comparison capacity radius before outcome dummy supported state retained) source =
    RecordedSourceWorld.slot (ExecutedPaddedSourceFamily.linearFamily s capacity radius before.1) state
      (reconstruction_recorded s comparison capacity radius before outcome dummy supported state retained initial beforeSupported)
      (PackedPBSComparisonReferences.linearSlot source) := by
  apply RecordedSourceWorld.slot_eq
  · rfl
  · exact root_eq s comparison capacity radius before outcome dummy supported source

include supported beforeSupported retained in
/-- The whole decoded comparison family agrees with the reconstruction's
canonical source slots outside the single final history exception. -/
theorem logical_on_reconstruction_or_bad (arity : ℕ)
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape H) state) :
    RecordedPaddedSourceFamily.logical (sourceFamily s comparison capacity radius outcome) s.encoding dummy arity =
      (fun source => RecordedPaddedSourceFamily.logical (RecordedSourceWorld.family state) s.encoding dummy arity
        (RecordedSourceWorld.slot (ExecutedPaddedSourceFamily.linearFamily s capacity radius before.1) state
          (reconstruction_recorded s comparison capacity radius before outcome dummy supported state retained initial beforeSupported)
          (PackedPBSComparisonReferences.linearSlot source))) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape H) state := by
  rcases RecordedSourceWorld.logical_eq_or_bad (sourceFamily s comparison capacity radius outcome)
      s.encoding dummy arity state audited
      (final_recorded s comparison capacity radius before outcome dummy supported state retained) with same | bad
  · left
    funext source
    exact (congrFun same source).trans (congrArg
      (fun index => RecordedPaddedSourceFamily.logical (RecordedSourceWorld.family state) s.encoding dummy arity index)
      (source_slot s comparison capacity radius before outcome dummy supported state retained initial beforeSupported source))
  · exact Or.inr bad

end
end FormalProof4FHE.HasteBoots.ExecutedComparisonWorld
