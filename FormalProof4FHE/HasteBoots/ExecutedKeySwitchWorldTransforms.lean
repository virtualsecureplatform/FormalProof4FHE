module
public import FormalProof4FHE.HasteBoots.AcceptedKeySwitchNTT
public import FormalProof4FHE.HasteBoots.RecordedFamilyEmbedding
public import FormalProof4FHE.HasteBoots.CheckpointHistoryChain
public import FormalProof4FHE.HasteBoots.RecordedSourceWorld
public import FormalProof4FHE.HasteBoots.ExecutedKeySwitchProduct
public import FormalProof4FHE.HasteBoots.ExecutedKeySwitchReconstruction
public import FormalProof4FHE.HasteBoots.ExecutedNTTWorldLinks
public import FormalProof4FHE.HasteBoots.ExecutedNTTWorld
@[expose] public section

/-! Canonical slots identify actual executed NTT sources with the original
reconstruction and product sources. Caller-root identities are derived from
support; only public decoder routing remains as an explicit condition. -/
namespace FormalProof4FHE.HasteBoots.ExecutedKeySwitchWorldTransforms
open OracleSpec OracleComp BinaryTree
open NativeRootMessage (Digest)
noncomputable section
variable {q c lanes d : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory : Type}
  [DecidableEq Input] [DecidableEq Digest] {heights : Cfg → ℕ}
variable (base : Fin (d+1) → Memory → PaddedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory heights (2^lanes) c 1 (2^lanes))
  (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (family : PackedPBSOriginalReferences.Family d)
  (nodesEnough : 2*(2^lanes) ≤ q) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(c+lanes+1)))

variable [SampleableType (Fin (2^lanes) → Fin 1 → ZMod q)] [SampleableType (Fin (2^lanes) → ZMod q)] [SampleableType Digest]
  [∀ index memory side, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((base index memory).code side).front) (2^lanes))]
  [∀ index memory side, SampleableType (Fin ((base index memory).code side).queries → Fin (2^heights ((base index memory).tag side)))]

variable (dummy : Digest) (memory : Memory)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
  (outcome : PaddedNTTSequence.Trace (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive) ×
    CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
  (supported : outcome ∈ support (KeySwitchPaddedNTT.witness base enc family nodesEnough
    (Nat.pow_add 2 c lanes).symm psi primitive dummy memory initial))

variable
    (capacity : ∀ index memory side, 2^((base index memory).code side).suffix ≤ ((base index memory).code side).m*(2^lanes))
    (radius : Fin (d+1) → Memory → Bool → ℕ) (passes : outcome.1.accepted = true)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (nttRetained : CheckpointHistoryChain.Retains outcome.2 state)

variable {ReconstructionResponse ReconstructionCommitMemory : Type}
    (reconstruction : PaddedLinear.Scheme (ZMod q) Input Digest Cfg ReconstructionResponse Memory ReconstructionCommitMemory heights (2*d+2) (2^lanes) (1+c))
    (input : NativeGoldParameterStore.Reference) (radix : ZMod q)
    (reconstructionCapacity : ∀ factor, 2^(reconstruction.code factor).suffix ≤ (reconstruction.code factor).m*(2^lanes))
    (reconstructionRadius : Fin (2*d+2) → ℕ)
    [∀ factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^(reconstruction.code factor).front) (2^lanes))]
    [∀ factor, SampleableType (Fin (reconstruction.code factor).queries → Fin (2^heights (reconstruction.tag factor)))]
    (reconstructionInitial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (reconstructionOutcome : PaddedLinear.Prefix (count := 2*d+2) (Input := Input) (Digest := Digest) (CommitMemory := ReconstructionCommitMemory) heights ×
      PaddedLinear.RunResult (KeySwitchPaddedReconstruction.stage reconstruction enc input family nodesEnough radix))
    (reconstructionSupported : reconstructionOutcome ∈ support (PaddedLinear.witness
      (KeySwitchPaddedReconstruction.stage reconstruction enc input family nodesEnough radix) dummy reconstructionInitial))
    (reconstructionRetained : CheckpointHistoryChain.Retains reconstructionOutcome.2.2 state)

variable {ProductResponse ProductCommitMemory : Type}
    (product : KeySwitchPaddedProduct.Scheme (q := q) (d := d) (b := 2^lanes) (n := c)
      (Input := Input) (Cfg := Cfg) (Response := ProductResponse) (Memory := Memory) (CommitMemory := ProductCommitMemory) (heights := heights))
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (productNodes : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (productCapacity : ∀ factor, 2^(product.code factor).suffix ≤ (product.code factor).m*(2^lanes))
    (productRadius : PBSHadamard.Factor d → ℕ)
    [SampleableType (PackedZeroReduction.Points (ZMod q) c (2^lanes))]
    [SampleableType (Fin (2^lanes) → Fin (2^lanes) → ZMod q)]
    [∀ factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^(product.code factor).front) (2^lanes))]
    [∀ factor, SampleableType (Fin (product.code factor).queries → Fin (2^heights (product.tag factor)))]
    (productInitial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (productOutcome : PaddedZeroCheck.Prefix (Factor := PBSHadamard.Factor d) (Input := Input) (Digest := Digest) (CommitMemory := ProductCommitMemory) heights ×
      PaddedZeroCheck.RunResult (KeySwitchPaddedProduct.stage product enc family firstSmall roundSmall productNodes))
    (productSupported : productOutcome ∈ support (PaddedZeroCheck.witness
      (KeySwitchPaddedProduct.stage product enc family firstSmall roundSmall productNodes) dummy productInitial))
    (productRetained : CheckpointHistoryChain.Retains productOutcome.2.2 state)

include supported reconstructionSupported productSupported passes nttRetained in
/-- The actual accepted NTT loop transforms the reconstruction's original digit
coefficients into the product's original evaluation factors, or exposes the
executed loop risk or final Bad. No decoded transform is assumed. -/
theorem digit_transform_or_risk_or_bad
    (coefficientRouting : ∀ (level : Fin d) memory, PaddedStageSourceInterpretation.nttParameters
      (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive (Fin.castSucc level) memory)
      (capacity (Fin.castSucc level) memory) (radius (Fin.castSucc level) memory) false =
      PaddedStageSourceInterpretation.linearParameters (KeySwitchPaddedReconstruction.stage reconstruction enc input family nodesEnough radix) reconstructionCapacity reconstructionRadius (DecompositionLinear.digit level))
    (evaluationRouting : ∀ index memory, PaddedStageSourceInterpretation.nttParameters
      (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive index memory)
      (capacity index memory) (radius index memory) true =
      PaddedStageSourceInterpretation.zeroParameters (KeySwitchPaddedProduct.stage product enc family firstSmall roundSmall productNodes) productCapacity productRadius (PackedPBSOriginalReferences.evaluationFactor index))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state) :
    let world := RecordedSourceWorld.family (F := ZMod q) (b := 2^lanes) state
    let reconstructionRecorded := CheckpointHistoryChain.family_recorded (ExecutedKeySwitchReconstruction.sourceFamily reconstruction enc input family nodesEnough radix reconstructionCapacity reconstructionRadius reconstructionOutcome.1) reconstructionOutcome.2.2 state reconstructionRetained (ExecutedKeySwitchReconstruction.sourceFamily_recorded reconstruction enc input family nodesEnough radix reconstructionCapacity reconstructionRadius dummy reconstructionInitial reconstructionOutcome reconstructionSupported)
    let productRecorded := CheckpointHistoryChain.family_recorded (ExecutedKeySwitchProduct.sourceFamily product enc family firstSmall roundSmall productNodes productCapacity productRadius productOutcome.1) productOutcome.2.2 state productRetained (ExecutedKeySwitchProduct.sourceFamily_recorded product enc family firstSmall roundSmall productNodes productCapacity productRadius dummy productInitial productOutcome productSupported)
    let coefficients := RecordedSourceWorld.slot (ExecutedKeySwitchReconstruction.sourceFamily reconstruction enc input family nodesEnough radix reconstructionCapacity reconstructionRadius reconstructionOutcome.1) state reconstructionRecorded
    let evaluations := RecordedSourceWorld.slot (ExecutedKeySwitchProduct.sourceFamily product enc family firstSmall roundSmall productNodes productCapacity productRadius productOutcome.1) state productRecorded
    (∀ level half, BlindRotationNTT.transform (c+lanes) psi
      (PackedCipherSource.familyCipher (c := c) (lanes := lanes) world enc dummy (coefficients (DecompositionLinear.digit level)) half) =
      PackedCipherSource.familyCipher (c := c) (lanes := lanes) world enc dummy (evaluations (PackedPBSOriginalReferences.evaluationFactor (Fin.castSucc level))) half) ∨
      PaddedNTTSequenceSoundness.AnyOriginalRisk (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive) enc dummy capacity radius outcome.1 ∨ CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  have checked := ExecutedNTTWorld.transform_or_risk_or_bad base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes state audited nttRetained
  dsimp only at checked ⊢
  rcases checked with transformed | risky | bad
  · left
    intro level half
    have coefficient := ExecutedNTTWorldLinks.coefficient_slot base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes state nttRetained reconstruction input radix reconstructionCapacity reconstructionRadius reconstructionInitial reconstructionOutcome reconstructionSupported reconstructionRetained coefficientRouting level
    have evaluation := ExecutedNTTWorldLinks.evaluation_slot base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes state nttRetained product firstSmall roundSmall productNodes productCapacity productRadius productInitial productOutcome productSupported productRetained evaluationRouting (Fin.castSucc level)
    dsimp only at coefficient evaluation
    rw [←coefficient,←evaluation]
    exact transformed (Fin.castSucc level) half
  · exact Or.inr (Or.inl risky)
  · exact Or.inr (Or.inr bad)

include supported productSupported passes nttRetained in
/-- The result coefficient root and the product result root are the final NTT
pair from the same accepted execution, outside its existing loop risk and Bad. -/
theorem result_transform_or_risk_or_bad
    (evaluationRouting : ∀ index memory, PaddedStageSourceInterpretation.nttParameters
      (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive index memory)
      (capacity index memory) (radius index memory) true =
      PaddedStageSourceInterpretation.zeroParameters (KeySwitchPaddedProduct.stage product enc family firstSmall roundSmall productNodes) productCapacity productRadius (PackedPBSOriginalReferences.evaluationFactor index))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state) :
    let world := RecordedSourceWorld.family (F := ZMod q) (b := 2^lanes) state
    let nttRecorded := CheckpointHistoryChain.family_recorded (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) outcome.2 state nttRetained (AcceptedKeySwitchNTT.sourceFamily_recorded base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes)
    let productRecorded := CheckpointHistoryChain.family_recorded (ExecutedKeySwitchProduct.sourceFamily product enc family firstSmall roundSmall productNodes productCapacity productRadius productOutcome.1) productOutcome.2.2 state productRetained (ExecutedKeySwitchProduct.sourceFamily_recorded product enc family firstSmall roundSmall productNodes productCapacity productRadius dummy productInitial productOutcome productSupported)
    let coefficients := RecordedSourceWorld.slot (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) state nttRecorded
    let evaluations := RecordedSourceWorld.slot (ExecutedKeySwitchProduct.sourceFamily product enc family firstSmall roundSmall productNodes productCapacity productRadius productOutcome.1) state productRecorded
    (∀ half, BlindRotationNTT.transform (c+lanes) psi
      (PackedCipherSource.familyCipher (c := c) (lanes := lanes) world enc dummy (coefficients (Fin.last d,false)) half) =
      PackedCipherSource.familyCipher (c := c) (lanes := lanes) world enc dummy (evaluations (.inr ())) half) ∨
      PaddedNTTSequenceSoundness.AnyOriginalRisk (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c lanes).symm psi primitive) enc dummy capacity radius outcome.1 ∨ CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state := by
  have checked := ExecutedNTTWorld.transform_or_risk_or_bad base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes state audited nttRetained
  dsimp only at checked ⊢
  rcases checked with transformed | risky | bad
  · left
    intro half
    have evaluation := ExecutedNTTWorldLinks.evaluation_slot base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes state nttRetained product firstSmall roundSmall productNodes productCapacity productRadius productInitial productOutcome productSupported productRetained evaluationRouting (Fin.last d)
    dsimp only at evaluation
    have factor : PackedPBSOriginalReferences.evaluationFactor (Fin.last d) = .inr () := by
      simp [PackedPBSOriginalReferences.evaluationFactor]
    rw [factor] at evaluation
    rw [←evaluation]
    exact transformed (Fin.last d) half
  · exact Or.inr (Or.inl risky)
  · exact Or.inr (Or.inr bad)


end
end FormalProof4FHE.HasteBoots.ExecutedKeySwitchWorldTransforms
