module
public import FormalProof4FHE.HasteBoots.AcceptedKeySwitchNTT
public import FormalProof4FHE.HasteBoots.RecordedFamilyEmbedding
public import FormalProof4FHE.HasteBoots.CheckpointHistoryChain
public import FormalProof4FHE.HasteBoots.RecordedSourceWorld
public import FormalProof4FHE.HasteBoots.ExecutedKeySwitchProduct
public import FormalProof4FHE.HasteBoots.ExecutedKeySwitchReconstruction
public import FormalProof4FHE.HasteBoots.ExecutedNTTWorldLinks
public import FormalProof4FHE.HasteBoots.ExecutedNTTWorld
public import FormalProof4FHE.HasteBoots.ExecutedKeySwitchWorldTransforms
public import FormalProof4FHE.HasteBoots.ExecutedKnownInputWorldLink
public import FormalProof4FHE.HasteBoots.ExecutedReconstructionWorld
public import FormalProof4FHE.HasteBoots.ExecutedProductWorld
public import FormalProof4FHE.HasteBoots.ExecutedRectangularRadix
public import FormalProof4FHE.HasteBoots.DecodedEvaluationKey
@[expose] public section

/-! Pointwise increment coverage assembled from actual supported key-switch
operations and a reached rectangular comparison. No decoded semantic relation
or externally supplied common source family is a premise. -/
namespace FormalProof4FHE.HasteBoots.ExecutedKeySwitchIncrement
open OracleSpec OracleComp BinaryTree
open NativeRootMessage (Digest)
noncomputable section
variable {q c d bits : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory : Type}
  [DecidableEq Input] [DecidableEq Digest] {heights : Cfg → ℕ}
variable (base : Fin (d+1) → Memory → PaddedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory heights (2^2) c 1 (2^2))
  (enc : MerkleOracle.Encoding Input Digest (List (ZMod q))) (family : PackedPBSOriginalReferences.Family d)
  (nodesEnough : 2*(2^2) ≤ q) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(c+2+1)))

variable [SampleableType (Fin (2^2) → Fin 1 → ZMod q)] [SampleableType (Fin (2^2) → ZMod q)] [SampleableType Digest]
  [∀ index memory side, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((base index memory).code side).front) (2^2))]
  [∀ index memory side, SampleableType (Fin ((base index memory).code side).queries → Fin (2^heights ((base index memory).tag side)))]

variable (dummy : Digest) (memory : Memory)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
  (outcome : PaddedNTTSequence.Trace (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c 2).symm psi primitive) ×
    CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
  (supported : outcome ∈ support (KeySwitchPaddedNTT.witness base enc family nodesEnough
    (Nat.pow_add 2 c 2).symm psi primitive dummy memory initial))

variable
    (capacity : ∀ index memory side, 2^((base index memory).code side).suffix ≤ ((base index memory).code side).m*(2^2))
    (radius : Fin (d+1) → Memory → Bool → ℕ) (passes : outcome.1.accepted = true)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (nttRetained : CheckpointHistoryChain.Retains outcome.2 state)

variable {ReconstructionResponse ReconstructionCommitMemory : Type}
    (reconstruction : PaddedLinear.Scheme (ZMod q) Input Digest Cfg ReconstructionResponse Memory ReconstructionCommitMemory heights (2*d+2) (2^2) (1+c))
    (input : NativeGoldParameterStore.Reference)
    (reconstructionCapacity : ∀ factor, 2^(reconstruction.code factor).suffix ≤ (reconstruction.code factor).m*(2^2))
    (reconstructionRadius : Fin (2*d+2) → ℕ)
    [∀ factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^(reconstruction.code factor).front) (2^2))]
    [∀ factor, SampleableType (Fin (reconstruction.code factor).queries → Fin (2^heights (reconstruction.tag factor)))]
    (reconstructionInitial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (reconstructionOutcome : PaddedLinear.Prefix (count := 2*d+2) (Input := Input) (Digest := Digest) (CommitMemory := ReconstructionCommitMemory) heights ×
      PaddedLinear.RunResult (KeySwitchPaddedReconstruction.stage reconstruction enc input family nodesEnough (2^bits : ZMod q)))
    (reconstructionSupported : reconstructionOutcome ∈ support (PaddedLinear.witness
      (KeySwitchPaddedReconstruction.stage reconstruction enc input family nodesEnough (2^bits : ZMod q)) dummy reconstructionInitial))
    (reconstructionRetained : CheckpointHistoryChain.Retains reconstructionOutcome.2.2 state)

variable {ProductResponse ProductCommitMemory : Type}
    (product : KeySwitchPaddedProduct.Scheme (q := q) (d := d) (b := 2^2) (n := c)
      (Input := Input) (Cfg := Cfg) (Response := ProductResponse) (Memory := Memory) (CommitMemory := ProductCommitMemory) (heights := heights))
    (firstSmall : (2*(2^2)-1)*2+1 ≤ q) (roundSmall : (2*(2^2)-1)*3+1 ≤ q)
    (productNodes : 2*(2^2) ≤ (2*(2^2)-1)*2+1)
    (productCapacity : ∀ factor, 2^(product.code factor).suffix ≤ (product.code factor).m*(2^2))
    (productRadius : PBSHadamard.Factor d → ℕ)
    [SampleableType (PackedZeroReduction.Points (ZMod q) c (2^2))]
    [SampleableType (Fin (2^2) → Fin (2^2) → ZMod q)]
    [∀ factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^(product.code factor).front) (2^2))]
    [∀ factor, SampleableType (Fin (product.code factor).queries → Fin (2^heights (product.tag factor)))]
    (productInitial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (productOutcome : PaddedZeroCheck.Prefix (Factor := PBSHadamard.Factor d) (Input := Input) (Digest := Digest) (CommitMemory := ProductCommitMemory) heights ×
      PaddedZeroCheck.RunResult (KeySwitchPaddedProduct.stage product enc family firstSmall roundSmall productNodes))
    (productSupported : productOutcome ∈ support (PaddedZeroCheck.witness
      (KeySwitchPaddedProduct.stage product enc family firstSmall roundSmall productNodes) dummy productInitial))
    (productRetained : CheckpointHistoryChain.Retains productOutcome.2.2 state)

open scoped BigOperators
open PaddedMixedWidthLookupOpeningFamily MixedWidthSharedLookupPCSAlgebra
variable {KnownResponse KnownCommitMemory : Type} {knownFront knownSuffix knownM knownQueries knownHeight : ℕ}
    (known : AmbientKnownInput.Scheme (ZMod q) Input Digest Cfg KnownResponse Memory KnownCommitMemory
      4 (1+c) knownFront knownSuffix knownM knownQueries knownHeight)
    (accumulator : NativeBlindRotation.Cipher q (2^(c+2)))
    (knownCapacity : 2^knownSuffix ≤ knownM*4) (knownRadius : ℕ)
    [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^knownFront) 4)]
    [SampleableType (Fin knownQueries → Fin (2^knownHeight))]
    (knownInitial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (knownOutcome : AmbientKnownInput.Prefix heights (Input := Input) (Digest := Digest) (CommitMemory := KnownCommitMemory) ×
      AmbientKnownInput.RunResult heights (F := ZMod q) (Input := Input) (Digest := Digest) (Response := KnownResponse) (Memory := Memory)
        (b := 4) (n := 1+c) (front := knownFront) (queries := knownQueries) (height := knownHeight))
    (knownSupported : knownOutcome ∈ support (AmbientKnownInput.witness heights
      (KeySwitchKnownInput.stage nodesEnough enc input.root (Nat.pow_add 2 c 2).symm accumulator known) dummy knownInitial))
    (knownGeometry : heights known.tag = knownHeight)
    (knownRetained : CheckpointHistoryChain.Retains knownOutcome.2.2 state)

variable {K LookupMessage LookupMemory ConfigHelperMemory RetainedMemory Result : Type}
    [Field K] [Algebra (ZMod q) K]
    {repetitions : Fin d → ℕ} {mode : Mode}
    {tag : Root (2*d+1) (∑ i, repetitions i) → Cfg}
    {g : Geometry 2 (1+c) (2*d+1) (∑ i, repetitions i)}
    {symbolWidth : Root (2*d+1) (∑ i, repetitions i) → ℕ}
    (comparison : PackedPBSComparisonStage.Scheme Cfg Input Memory
      ((Fin (∑ i, repetitions i) → Digest) × RetainedMemory) Result d)
    (comparisonOutcome : PackedPBSComparisonStage.Outcome (PaddedReconstructionComparison.stage
      (KeySwitchPaddedReconstruction.stage reconstruction enc input family nodesEnough (2^bits : ZMod q)) comparison))
    (comparisonSupported : some comparisonOutcome ∈ support (PaddedReconstructionComparison.continuation
      (KeySwitchPaddedReconstruction.stage reconstruction enc input family nodesEnough (2^bits : ZMod q)) comparison dummy reconstructionOutcome))
    (comparisonRetained : CheckpointHistoryChain.Retains comparisonOutcome.2.2.2 state)
    (config : RectangularRequestLookup.Parameters (ZMod q) K LookupMessage LookupMemory Cfg Input Digest Memory ConfigHelperMemory
      3 1 2 (1+c) (2*d+1) d (fun _ => 3) (fun _ => (2^bits)*2) repetitions mode)
    (domain : ∀ root, Fin (2^heights (tag root)) ↪ ZMod q)
    (lookupCapacity : ∀ root, 2^g.suffix root ≤ g.m root * symbolWidth root)
    (lookupRadius : Root (2*d+1) (∑ i, repetitions i) → ℕ)
    (sourceSymbols : ∀ source, symbolWidth (.inl source) = 4)

/-- The decoded final-family increment equality or one of its actual executed
lookup, reconstruction, known-input, NTT, product or history failure events. -/
def Coverage : Prop :=
    let world := RecordedSourceWorld.family (F := ZMod q) (b := 4) state
    let evaluations := RecordedSourceWorld.slot (ExecutedKeySwitchProduct.sourceFamily product enc family firstSmall roundSmall productNodes productCapacity productRadius productOutcome.1) state (CheckpointHistoryChain.family_recorded (ExecutedKeySwitchProduct.sourceFamily product enc family firstSmall roundSmall productNodes productCapacity productRadius productOutcome.1) productOutcome.2.2 state productRetained (ExecutedKeySwitchProduct.sourceFamily_recorded product enc family firstSmall roundSmall productNodes productCapacity productRadius dummy productInitial productOutcome productSupported))
    let result := RecordedSourceWorld.slot (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) state (CheckpointHistoryChain.family_recorded (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) outcome.2 state nttRetained (AcceptedKeySwitchNTT.sourceFamily_recorded base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes)) (Fin.last d,false)
    PackedCipherSource.familyCipher (c := c) (lanes := 2) world enc dummy result =
      CanonicalKeySwitch.increment bits
        (DecodedEvaluationKey.key (c+2) psi primitive
          (fun level => PackedCipherSource.familyCipher (c := c) (lanes := 2) world enc dummy (evaluations (.inl (level,true)))))
        (accumulator false) ∨
      RectangularOwnedRequestSources.OriginalFalse enc dummy config domain lookupCapacity lookupRadius comparisonOutcome ∨ PaddedLinear.OriginalRisk (KeySwitchPaddedReconstruction.stage reconstruction enc input family nodesEnough (2^bits : ZMod q)) dummy reconstructionCapacity reconstructionRadius reconstructionOutcome ∨ AmbientKnownInput.OriginalRisk heights (KeySwitchKnownInput.stage nodesEnough enc input.root (Nat.pow_add 2 c 2).symm accumulator known) dummy knownCapacity knownRadius knownOutcome ∨ PaddedNTTSequenceSoundness.AnyOriginalRisk (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c 2).symm psi primitive) enc dummy capacity radius outcome.1 ∨ PaddedZeroCheck.OriginalRisk (KeySwitchPaddedProduct.stage product enc family firstSmall roundSmall productNodes) dummy productCapacity productRadius productOutcome ∨ CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state

include supported reconstructionSupported productSupported knownSupported comparisonSupported
  passes nttRetained reconstructionRetained productRetained knownRetained comparisonRetained in
/-- The constructed final-family result is the canonical signed key-switch
increment, or one of the actual executed operation risks or final Bad occurs. -/
theorem increment_or_risks
    (coefficientRouting : ∀ (level : Fin d) memory, PaddedStageSourceInterpretation.nttParameters
      (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c 2).symm psi primitive (Fin.castSucc level) memory)
      (capacity (Fin.castSucc level) memory) (radius (Fin.castSucc level) memory) false =
      PaddedStageSourceInterpretation.linearParameters (KeySwitchPaddedReconstruction.stage reconstruction enc input family nodesEnough (2^bits : ZMod q)) reconstructionCapacity reconstructionRadius (DecompositionLinear.digit level))
    (evaluationRouting : ∀ index memory, PaddedStageSourceInterpretation.nttParameters
      (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c 2).symm psi primitive index memory)
      (capacity index memory) (radius index memory) true =
      PaddedStageSourceInterpretation.zeroParameters (KeySwitchPaddedProduct.stage product enc family firstSmall roundSmall productNodes) productCapacity productRadius (PackedPBSOriginalReferences.evaluationFactor index))

    (knownRouting : DecodedKnownInput.parameters (KeySwitchKnownInput.stage nodesEnough enc input.root (Nat.pow_add 2 c 2).symm accumulator known) heights knownGeometry knownCapacity knownRadius =
      PaddedStageSourceInterpretation.linearParameters (KeySwitchPaddedReconstruction.stage reconstruction enc input family nodesEnough (2^bits : ZMod q)) reconstructionCapacity reconstructionRadius DecompositionLinear.input)
    (lookupRouting : ∀ source, RectangularLookupSourceInterpretation.squareParameters domain lookupCapacity lookupRadius sourceSymbols source =
      PaddedStageSourceInterpretation.linearParameters (KeySwitchPaddedReconstruction.stage reconstruction enc input family nodesEnough (2^bits : ZMod q)) reconstructionCapacity reconstructionRadius (PackedPBSComparisonReferences.linearSlot source))
    (audited : CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape heights) state)
    (knownPasses : knownOutcome.2.1.2.accepted = true)
    (productPasses : PaddedZeroCheck.accepted (KeySwitchPaddedProduct.stage product enc family firstSmall roundSmall productNodes) productOutcome.2.1 = true)
    (slotOrder : config.slots = RadixLookupSources.comparisonSlots)
    (publicTables : config.tables = fun limb => RadixLookupSources.publicTable q (2^bits)
      (RadixCanonicity.modulusDigit q (2^bits) limb.val))
    (full : ∀ limb, config.active limb = 2^(2+(1+c)))
    (radixLarge : 1 < 2^bits) (radixSmall : 2^bits < q) (enough : q-1 < (2^bits)^d) :
    Coverage (bits := bits) (tag := tag) (g := g) (symbolWidth := symbolWidth)
      base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes state nttRetained reconstruction input reconstructionCapacity reconstructionRadius reconstructionOutcome product firstSmall roundSmall productNodes productCapacity productRadius productInitial productOutcome productSupported productRetained known accumulator knownCapacity knownRadius knownOutcome comparison comparisonOutcome config domain lookupCapacity lookupRadius := by
  dsimp only [Coverage]
  classical
  by_cases falseLookup : RectangularOwnedRequestSources.OriginalFalse enc dummy config domain lookupCapacity lookupRadius comparisonOutcome
  · exact Or.inr (Or.inl falseLookup)
  by_cases falseReconstruction : PaddedLinear.OriginalRisk (KeySwitchPaddedReconstruction.stage reconstruction enc input family nodesEnough (2^bits : ZMod q)) dummy reconstructionCapacity reconstructionRadius reconstructionOutcome
  · exact Or.inr (Or.inr (Or.inl falseReconstruction))
  by_cases falseKnown : AmbientKnownInput.OriginalRisk heights (KeySwitchKnownInput.stage nodesEnough enc input.root (Nat.pow_add 2 c 2).symm accumulator known) dummy knownCapacity knownRadius knownOutcome
  · exact Or.inr (Or.inr (Or.inr (Or.inl falseKnown)))
  by_cases falseNTT : PaddedNTTSequenceSoundness.AnyOriginalRisk (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c 2).symm psi primitive) enc dummy capacity radius outcome.1
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl falseNTT))))
  by_cases falseProduct : PaddedZeroCheck.OriginalRisk (KeySwitchPaddedProduct.stage product enc family firstSmall roundSmall productNodes) dummy productCapacity productRadius productOutcome
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl falseProduct)))))
  by_cases bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (bad))))))
  have reconstructed := (ExecutedReconstructionWorld.relation_or_risk_or_bad reconstruction enc input family nodesEnough (2^bits : ZMod q) reconstructionCapacity reconstructionRadius dummy reconstructionInitial reconstructionOutcome reconstructionSupported
    state audited reconstructionRetained (PaddedReconstructionComparison.reached (KeySwitchPaddedReconstruction.stage reconstruction enc input family nodesEnough (2^bits : ZMod q)) comparison dummy reconstructionOutcome comparisonOutcome comparisonSupported).1).resolve_right (fun fail => fail.elim falseReconstruction bad)
  have lookup := (ExecutedRectangularRadix.lookup_or_false_or_bad (e := 3) (padding := 1) (c := 2) (row := 1+c) (tag := tag) (g := g) (symbolWidth := symbolWidth) (radix := 2^bits) (KeySwitchPaddedReconstruction.stage reconstruction enc input family nodesEnough (2^bits : ZMod q)) comparison reconstructionCapacity reconstructionRadius reconstructionOutcome comparisonOutcome config domain lookupCapacity lookupRadius sourceSymbols lookupRouting dummy comparisonSupported reconstructionInitial reconstructionSupported state comparisonRetained audited slotOrder publicTables full).resolve_right (fun fail => fail.elim falseLookup bad)
  have masked := (ExecutedKnownInputWorldLink.negative_mask_or_risk_or_bad known nodesEnough enc input accumulator dummy knownCapacity knownRadius knownInitial knownOutcome knownSupported
    reconstruction family (2^bits : ZMod q) reconstructionCapacity reconstructionRadius reconstructionInitial reconstructionOutcome reconstructionSupported
    knownGeometry state knownRetained reconstructionRetained knownRouting audited knownPasses).resolve_right (fun fail => fail.elim falseKnown bad)
  have digits := (ExecutedKeySwitchWorldTransforms.digit_transform_or_risk_or_bad base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes state nttRetained reconstruction input (2^bits : ZMod q) reconstructionCapacity reconstructionRadius reconstructionInitial reconstructionOutcome reconstructionSupported reconstructionRetained product firstSmall roundSmall productNodes productCapacity productRadius productInitial productOutcome productSupported productRetained
    coefficientRouting evaluationRouting audited).resolve_right (fun fail => fail.elim falseNTT bad)
  have result := (ExecutedKeySwitchWorldTransforms.result_transform_or_risk_or_bad base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes state nttRetained product firstSmall roundSmall productNodes productCapacity productRadius productInitial productOutcome productSupported productRetained
    evaluationRouting audited).resolve_right (fun fail => fail.elim falseNTT bad)
  have multiplied := (ExecutedProductWorld.identity_or_risk_or_bad product enc family firstSmall roundSmall productNodes productCapacity productRadius dummy productInitial productOutcome productSupported
    state audited productRetained productPasses).resolve_right (fun fail => fail.elim falseProduct bad)
  dsimp only at reconstructed lookup masked digits result multiplied
  have reindex (left right : ℕ) (equal : left = right) :
      (∀ cell lane, RadixCanonicity.LookupAt q (2^bits)
        (fun factor => RecordedPaddedSourceFamily.logical (RecordedSourceWorld.family state) enc dummy left
          (RecordedSourceWorld.slot (ExecutedKeySwitchReconstruction.sourceFamily reconstruction enc input family nodesEnough (2^bits : ZMod q) reconstructionCapacity reconstructionRadius reconstructionOutcome.1) state (CheckpointHistoryChain.family_recorded (ExecutedKeySwitchReconstruction.sourceFamily reconstruction enc input family nodesEnough (2^bits : ZMod q) reconstructionCapacity reconstructionRadius reconstructionOutcome.1) reconstructionOutcome.2.2 state reconstructionRetained (ExecutedKeySwitchReconstruction.sourceFamily_recorded reconstruction enc input family nodesEnough (2^bits : ZMod q) reconstructionCapacity reconstructionRadius dummy reconstructionInitial reconstructionOutcome reconstructionSupported)) factor)) cell lane) →
      (∀ cell lane, RadixCanonicity.LookupAt q (2^bits)
        (fun factor => RecordedPaddedSourceFamily.logical (RecordedSourceWorld.family state) enc dummy right
          (RecordedSourceWorld.slot (ExecutedKeySwitchReconstruction.sourceFamily reconstruction enc input family nodesEnough (2^bits : ZMod q) reconstructionCapacity reconstructionRadius reconstructionOutcome.1) state (CheckpointHistoryChain.family_recorded (ExecutedKeySwitchReconstruction.sourceFamily reconstruction enc input family nodesEnough (2^bits : ZMod q) reconstructionCapacity reconstructionRadius reconstructionOutcome.1) reconstructionOutcome.2.2 state reconstructionRetained (ExecutedKeySwitchReconstruction.sourceFamily_recorded reconstruction enc input family nodesEnough (2^bits : ZMod q) reconstructionCapacity reconstructionRadius dummy reconstructionInitial reconstructionOutcome reconstructionSupported)) factor)) cell lane) := by
    cases equal
    exact id
  left
  apply DecodedEvaluationKey.family_increment_of_constraints (c := c) (lanes := 2)
    (RecordedSourceWorld.family state) enc dummy _ _ _ psi primitive bits radixLarge radixSmall enough
    reconstructed (reindex (1+c) (c+1) (Nat.add_comm 1 c) lookup) (accumulator false) masked ?_ result multiplied
  intro level half
  have factor : PackedPBSOriginalReferences.evaluationFactor (Fin.castSucc level) = .inl (level,false) := by
    simp [PackedPBSOriginalReferences.evaluationFactor,level.isLt]
  simpa only [factor] using digits level half

end
end FormalProof4FHE.HasteBoots.ExecutedKeySwitchIncrement
