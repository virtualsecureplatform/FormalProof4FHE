module
public import FormalProof4FHE.HasteBoots.DecodedKnownInput
public import FormalProof4FHE.HasteBoots.CheckpointHistoryChain
public import FormalProof4FHE.HasteBoots.ExecutedKnownInputCommonFamily
public import FormalProof4FHE.HasteBoots.RecordedSourceWorld
public import FormalProof4FHE.HasteBoots.ExecutedKnownInputWorld
public import FormalProof4FHE.HasteBoots.ExecutedKeySwitchReconstruction
@[expose] public section

/-! The actual known-input check fixes the later common-family input to the
negative accumulator mask, using its literal fresh checkpoint and retention. -/
namespace FormalProof4FHE.HasteBoots.ExecutedKnownInputWorldLink
open OracleSpec OracleComp BinaryTree
open NativeRootMessage (Digest)
noncomputable section
variable {q d c lanes front suffix m queries height : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory : Type}
  [DecidableEq Input] [DecidableEq Digest] {heights : Cfg → ℕ}
variable (s : AmbientKnownInput.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
  (2^lanes) (1+c) front suffix m queries height)
  (small : 2*(2^lanes) ≤ q) (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (input : NativeGoldParameterStore.Reference)
  (accumulator : NativeBlindRotation.Cipher q (2^(c+lanes)))
  [SampleableType Digest] [SampleableType (Fin (2^lanes) → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) (2^lanes))]
  [SampleableType (Fin queries → Fin (2^height))]
variable (dummy : Digest) (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
  (outcome : AmbientKnownInput.Prefix heights (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) ×
    AmbientKnownInput.RunResult heights (F := ZMod q) (Input := Input) (Digest := Digest) (Response := Response) (Memory := Memory)
      (b := 2^lanes) (n := 1+c) (front := front) (queries := queries) (height := height))
  (supported : outcome ∈ support (AmbientKnownInput.witness heights
    (KeySwitchKnownInput.stage small enc input.root (Nat.pow_add 2 c lanes).symm accumulator s) dummy initial))

variable {ReconstructionResponse ReconstructionCommitMemory : Type}
    (reconstruction : PaddedLinear.Scheme (ZMod q) Input Digest Cfg ReconstructionResponse Memory ReconstructionCommitMemory heights (2*d+2) (2^lanes) (1+c))
    (family : PackedPBSOriginalReferences.Family d) (radix : ZMod q)
    (reconstructionCapacity : ∀ factor, 2^(reconstruction.code factor).suffix ≤ (reconstruction.code factor).m*(2^lanes))
    (reconstructionRadius : Fin (2*d+2) → ℕ)
    [∀ factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^(reconstruction.code factor).front) (2^lanes))]
    [∀ factor, SampleableType (Fin (reconstruction.code factor).queries → Fin (2^heights (reconstruction.tag factor)))]
    (reconstructionInitial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (reconstructionOutcome : PaddedLinear.Prefix (count := 2*d+2) (Input := Input) (Digest := Digest) (CommitMemory := ReconstructionCommitMemory) heights ×
      PaddedLinear.RunResult (KeySwitchPaddedReconstruction.stage reconstruction enc input family small radix))
    (reconstructionSupported : reconstructionOutcome ∈ support (PaddedLinear.witness
      (KeySwitchPaddedReconstruction.stage reconstruction enc input family small radix) dummy reconstructionInitial))
    (geometry : heights s.tag = height)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state)
    (reconstructionRetained : CheckpointHistoryChain.Retains reconstructionOutcome.2.2 state)

include supported reconstructionSupported retained in
/-- The actual fresh known-input root and reconstruction input are the same
canonical slot. The caller-root identity is derived from executed support. -/
theorem input_slot
    (routing : DecodedKnownInput.parameters (KeySwitchKnownInput.stage small enc input.root (Nat.pow_add 2 c lanes).symm accumulator s) heights geometry capacity radius =
      PaddedStageSourceInterpretation.linearParameters (KeySwitchPaddedReconstruction.stage reconstruction enc input family small radix) reconstructionCapacity reconstructionRadius DecompositionLinear.input) :
    ExecutedKnownInputWorld.slot s small enc input.root accumulator dummy capacity radius initial outcome supported geometry state retained =
      RecordedSourceWorld.slot (ExecutedKeySwitchReconstruction.sourceFamily reconstruction enc input family small radix reconstructionCapacity reconstructionRadius reconstructionOutcome.1) state (CheckpointHistoryChain.family_recorded (ExecutedKeySwitchReconstruction.sourceFamily reconstruction enc input family small radix reconstructionCapacity reconstructionRadius reconstructionOutcome.1) reconstructionOutcome.2.2 state reconstructionRetained (ExecutedKeySwitchReconstruction.sourceFamily_recorded reconstruction enc input family small radix reconstructionCapacity reconstructionRadius dummy reconstructionInitial reconstructionOutcome reconstructionSupported)) DecompositionLinear.input := by
  apply Subtype.ext
  have expected := ExecutedKeySwitchReconstruction.sourceFamily_expected_roots reconstruction enc input family small radix reconstructionCapacity reconstructionRadius dummy reconstructionInitial reconstructionOutcome reconstructionSupported
  exact congrArg₂ (RecordedSourceWorld.Address.mk) routing expected.1.symm

include supported reconstructionSupported retained in
/-- Acceptance of the actual known-input check fixes the reconstruction input
in the common final-history family, or exposes its risk or final Bad. -/
theorem negative_mask_or_risk_or_bad
    (routing : DecodedKnownInput.parameters (KeySwitchKnownInput.stage small enc input.root (Nat.pow_add 2 c lanes).symm accumulator s) heights geometry capacity radius =
      PaddedStageSourceInterpretation.linearParameters (KeySwitchPaddedReconstruction.stage reconstruction enc input family small radix) reconstructionCapacity reconstructionRadius DecompositionLinear.input)
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (passes : outcome.2.1.2.accepted = true) :
    (∀ half, PackedCipherSource.familyCipher (c := c) (lanes := lanes) (RecordedSourceWorld.family state) enc dummy
      (RecordedSourceWorld.slot (ExecutedKeySwitchReconstruction.sourceFamily reconstruction enc input family small radix reconstructionCapacity reconstructionRadius reconstructionOutcome.1) state (CheckpointHistoryChain.family_recorded (ExecutedKeySwitchReconstruction.sourceFamily reconstruction enc input family small radix reconstructionCapacity reconstructionRadius reconstructionOutcome.1) reconstructionOutcome.2.2 state reconstructionRetained (ExecutedKeySwitchReconstruction.sourceFamily_recorded reconstruction enc input family small radix reconstructionCapacity reconstructionRadius dummy reconstructionInitial reconstructionOutcome reconstructionSupported)) DecompositionLinear.input) half = -accumulator false) ∨
      AmbientKnownInput.OriginalRisk heights (KeySwitchKnownInput.stage small enc input.root (Nat.pow_add 2 c lanes).symm accumulator s) dummy capacity radius outcome ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  have same := input_slot s small enc input accumulator dummy capacity radius initial outcome supported reconstruction family radix reconstructionCapacity reconstructionRadius
    reconstructionInitial reconstructionOutcome reconstructionSupported geometry state retained reconstructionRetained routing
  have checked := ExecutedKnownInputWorld.negative_mask_or_risk_or_bad s small enc input.root accumulator dummy capacity radius initial outcome supported geometry state audited retained passes
  rw [same] at checked
  exact checked

end
end FormalProof4FHE.HasteBoots.ExecutedKnownInputWorldLink
