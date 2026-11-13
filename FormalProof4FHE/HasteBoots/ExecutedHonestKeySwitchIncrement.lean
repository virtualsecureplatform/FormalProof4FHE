module
public import FormalProof4FHE.HasteBoots.ExecutedKeySwitchIncrement
public import FormalProof4FHE.HasteBoots.ExecutedHonestProductKey
@[expose] public section

/-! Canonical key-switch increment coverage relative to an honestly initialized
coefficient key, using supported shared setup and the retained native product. -/
namespace FormalProof4FHE.HasteBoots.ExecutedHonestKeySwitchIncrement
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

def Correct (original : NativeKeySwitch.Key q (2^(c+2)) d) : Prop :=
    let world := RecordedSourceWorld.family (F := ZMod q) (b := 4) state
    let result := RecordedSourceWorld.slot (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) state (CheckpointHistoryChain.family_recorded (AcceptedKeySwitchNTT.sourceFamily base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes) outcome.2 state nttRetained (AcceptedKeySwitchNTT.sourceFamily_recorded base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes)) (Fin.last d,false)
    PackedCipherSource.familyCipher (c := c) (lanes := 2) world enc dummy result =
      CanonicalKeySwitch.increment bits
        original
        (accumulator false)


def Coverage (original : NativeKeySwitch.Key q (2^(c+2)) d) : Prop :=
    Correct (bits := bits) base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes state nttRetained accumulator original ∨
      RectangularOwnedRequestSources.OriginalFalse enc dummy config domain lookupCapacity lookupRadius comparisonOutcome ∨ PaddedLinear.OriginalRisk (KeySwitchPaddedReconstruction.stage reconstruction enc input family nodesEnough (2^bits : ZMod q)) dummy reconstructionCapacity reconstructionRadius reconstructionOutcome ∨ AmbientKnownInput.OriginalRisk heights (KeySwitchKnownInput.stage nodesEnough enc input.root (Nat.pow_add 2 c 2).symm accumulator known) dummy knownCapacity knownRadius knownOutcome ∨ PaddedNTTSequenceSoundness.AnyOriginalRisk (KeySwitchPaddedNTT.factory base enc family nodesEnough (Nat.pow_add 2 c 2).symm psi primitive) enc dummy capacity radius outcome.1 ∨ PaddedZeroCheck.OriginalRisk (KeySwitchPaddedProduct.stage product enc family firstSmall roundSmall productNodes) dummy productCapacity productRadius productOutcome ∨ CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) state

variable {SetupIndex SetupResult : Type} {setupBase : OracleSpec SetupIndex}
    (setupImpl : QueryImpl setupBase ProbComp)
    (original : NativeKeySwitch.Key q (2^(c+2)) d)
    (built : (Fin d → Digest) × CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights))
    (setupSupported : built ∈ support ((simulateQ (CheckpointExecution.handler setupImpl enc dummy
      (AmbientMatrixSource.Shape heights))
      (ExecutedHonestProductKey.setup product productCapacity productRadius enc psi original)).run
        (CheckpointExecution.empty (AmbientMatrixSource.Shape heights))))
    (continuation : OracleComp (CheckpointExecution.Spec setupBase Cfg Input Digest) SetupResult)
    (verification : SetupResult)
    (verificationSupported : (verification,state) ∈ support ((simulateQ (CheckpointExecution.handler setupImpl enc dummy
      (AmbientMatrixSource.Shape heights)) continuation).run built.2))
    (setupRoots : family.keys = built.1)
    (honestDegree : ∀ level, (ExecutedHonestProductKey.parameters product productCapacity productRadius level).degree ≤
      2^heights (ExecutedHonestProductKey.parameters product productCapacity productRadius level).tag)
    (honestMargin : ∀ level, 2*(ExecutedHonestProductKey.parameters product productCapacity productRadius level).radius <
      Code.minDist (BlockCode.code (ExecutedHonestProductKey.parameters product productCapacity productRadius level).domain
        (ExecutedHonestProductKey.parameters product productCapacity productRadius level).degree 4 :
        Set (Fin (2^heights (ExecutedHonestProductKey.parameters product productCapacity productRadius level).tag) → Fin 4 → ZMod q)))
    (honestFits : ∀ level, c+1 ≤ (ExecutedHonestProductKey.parameters product productCapacity productRadius level).front+
      (ExecutedHonestProductKey.parameters product productCapacity productRadius level).suffix)

include supported reconstructionSupported productSupported knownSupported comparisonSupported
  passes nttRetained reconstructionRetained productRetained knownRetained comparisonRetained setupSupported verificationSupported setupRoots honestDegree honestMargin honestFits in
/-- Honest setup replaces the constructed key without changing the operation
risk events or adding a second history exception. -/
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
    (knownPasses : knownOutcome.2.1.2.accepted = true)
    (productPasses : PaddedZeroCheck.accepted (KeySwitchPaddedProduct.stage product enc family firstSmall roundSmall productNodes) productOutcome.2.1 = true)
    (slotOrder : config.slots = RadixLookupSources.comparisonSlots)
    (publicTables : config.tables = fun limb => RadixLookupSources.publicTable q (2^bits)
      (RadixCanonicity.modulusDigit q (2^bits) limb.val))
    (full : ∀ limb, config.active limb = 2^(2+(1+c)))
    (radixLarge : 1 < 2^bits) (radixSmall : 2^bits < q) (enough : q-1 < (2^bits)^d) :
    Coverage (bits := bits) (tag := tag) (g := g) (symbolWidth := symbolWidth)
      base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes state nttRetained reconstruction input reconstructionCapacity reconstructionRadius reconstructionOutcome product firstSmall roundSmall productNodes productCapacity productRadius productOutcome known accumulator knownCapacity knownRadius knownOutcome comparison comparisonOutcome config domain lookupCapacity lookupRadius original := by
  have good := CheckpointExecution.good_empty enc dummy (AmbientMatrixSource.Shape heights)
  have setupAudit := CheckpointExecution.audited_run setupImpl enc dummy (AmbientMatrixSource.Shape heights)
    (ExecutedHonestProductKey.setup product productCapacity productRadius enc psi original)
    (CheckpointExecution.empty (AmbientMatrixSource.Shape heights)) ⟨good.1, fun _ => good.2.2⟩ built setupSupported
  have audited := CheckpointExecution.audited_run setupImpl enc dummy (AmbientMatrixSource.Shape heights)
    continuation built.2 setupAudit (verification,state) verificationSupported
  have covered := ExecutedKeySwitchIncrement.increment_or_risks (bits := bits) (tag := tag) (g := g) (symbolWidth := symbolWidth)
    base enc family nodesEnough psi primitive dummy memory initial outcome supported capacity radius passes state nttRetained
    reconstruction input reconstructionCapacity reconstructionRadius reconstructionInitial reconstructionOutcome reconstructionSupported reconstructionRetained
    product firstSmall roundSmall productNodes productCapacity productRadius productInitial productOutcome productSupported productRetained
    known accumulator knownCapacity knownRadius knownInitial knownOutcome knownSupported knownGeometry knownRetained
    comparison comparisonOutcome comparisonSupported comparisonRetained config domain lookupCapacity lookupRadius sourceSymbols
    coefficientRouting evaluationRouting knownRouting lookupRouting audited knownPasses productPasses slotOrder publicTables full
    radixLarge radixSmall enough
  rcases covered with correct | failure
  · have actualRecorded := CheckpointHistoryChain.family_recorded
      (ExecutedKeySwitchProduct.sourceFamily (c := c) (lanes := 2) product enc family
        firstSmall roundSmall productNodes productCapacity productRadius productOutcome.1)
      productOutcome.2.2 state productRetained
      (ExecutedKeySwitchProduct.sourceFamily_recorded (c := c) (lanes := 2) product enc family
        firstSmall roundSmall productNodes productCapacity productRadius dummy productInitial productOutcome productSupported)
    have nativeRoots := KeySwitchPaddedProduct.witness_roots product enc family
      firstSmall roundSmall productNodes dummy productInitial productOutcome productSupported
    have honest := ExecutedHonestEvaluationKey.associated_key_or_bad setupImpl
      (ExecutedHonestProductKey.parameters product productCapacity productRadius) enc dummy psi primitive original
      built setupSupported continuation (verification,state) verificationSupported honestDegree honestMargin honestFits
      (ExecutedKeySwitchProduct.sourceFamily (c := c) (lanes := 2) product enc family
        firstSmall roundSmall productNodes productCapacity productRadius productOutcome.1)
      actualRecorded (fun level => .inl (level,true)) (fun _ => rfl)
      (fun level => (congrFun nativeRoots (.inl (level,true))).trans (congrFun setupRoots level))
    rcases honest with keyEqual | bad
    · left
      dsimp only [ExecutedKeySwitchIncrement.Correct] at correct
      dsimp only [Correct]
      rw [keyEqual] at correct
      exact correct
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr bad)))))
  · exact Or.inr failure

end
end FormalProof4FHE.HasteBoots.ExecutedHonestKeySwitchIncrement
