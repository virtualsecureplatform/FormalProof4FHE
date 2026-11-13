module
public import FormalProof4FHE.HasteBoots.PackedPBSNativeExternalProduct
public import FormalProof4FHE.HasteBoots.PackedPBSRectangularCanonicalDigits
public import FormalProof4FHE.HasteBoots.PackedPBSResultAccumulatorSource
public import FormalProof4FHE.HasteBoots.RecordedNTTProjection
public import FormalProof4FHE.HasteBoots.PackedPBSDecompositionAccumulatorInputs
public import FormalProof4FHE.HasteBoots.ExecutedAmbientRectangularRadixWidth
public import FormalProof4FHE.HasteBoots.ExecutedTransportedRectangularRadixWidth
public import FormalProof4FHE.HasteBoots.PackedPBSSecondDigitNTTAssociation
public import FormalProof4FHE.HasteBoots.PackedPBSFirstCanonicalDigits
public import FormalProof4FHE.HasteBoots.ExecutedAccumulatorInputs
public import FormalProof4FHE.HasteBoots.OwnedAmbientAccumulator
public import FormalProof4FHE.HasteBoots.AmbientSourceDescriptor
public import FormalProof4FHE.HasteBoots.DecodedAccumulatorRows
public import FormalProof4FHE.HasteBoots.CheckpointHistoryChain
@[expose] public section

/-! Retained original NTT rows and canonical accumulator-difference digits in the actual
supported PBS prefix. All predecessor support, selected factory memory and
original owners are recovered from this same retained execution. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSNativeExternalProductCoverage
open OracleSpec OracleComp
open NativeRootMessage (Digest)
open scoped BigOperators
open PaddedMixedWidthLookupOpeningFamily MixedWidthSharedLookupPCSAlgebra
noncomputable section
attribute [local irreducible] MonadAttach.support
variable {q cells lanes rows d c r k n front suffix m queries height : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory FirstMessage Message : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin (2^lanes) → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) (2^lanes))]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points (ZMod q) n (2^lanes))] [SampleableType (Fin (2^lanes) → Fin (2^lanes) → ZMod q)]

variable (length : 2^c*(2^lanes) = 2^(cells+lanes)) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^((cells+lanes)+1)))
  (family : PackedPBSOriginalReferences.Family (2*d)) (inputs : PackedPBSDecompositionReferences.Inputs)
  (base : Fin (2*d+1) → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2^lanes) c r k front suffix m queries height)
  (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor (2*d)) (PBSHadamard.Term (2*d))
    FirstMessage Message Input Digest Cfg Response Memory CommitMemory (2^lanes) n front suffix m queries height)
  (nodesEnough : 2*(2^lanes) ≤ q) (radix : ℕ)
  (linearBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) (2^lanes) front suffix m queries height)

variable {FirstRetained Selection FirstRoot Data : Type} {firstRepetitions : Fin d → ℕ}

variable {SecondRetained SecondSelection SecondRoot SecondData : Type} {secondRepetitions : Fin d → ℕ}

variable {AccResponse : Type} {accFront accSuffix accM accQueries accHeight : ℕ}

  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^accFront) (2^lanes))]
  [SampleableType (Fin accQueries → Fin (2^accHeight))]

variable (dummy : Digest)
  (first : PackedPBSComparisonStage.Scheme Cfg Input Memory ((Fin (∑ i, firstRepetitions i) → Digest) × FirstRetained)
    (Selection × ShortCircuitSequence.Outcome FirstRoot Data Memory) d)
  (second : PackedPBSComparisonStage.Scheme Cfg Input Memory ((Fin (∑ i, secondRepetitions i) → Digest) × SecondRetained)
    (SecondSelection × ShortCircuitSequence.Outcome SecondRoot SecondData Memory) d)
  (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) (2^lanes) front suffix m queries height)
  (accumulators : Fin 4 → NativeGoldParameterStore.Reference)
  (factory : Memory → AmbientAccumulator.Scheme (ZMod q) Input Digest Cfg AccResponse Memory Memory
    (2^lanes) cells rows accFront accSuffix accM accQueries accHeight)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
  (before : PackedPBSAccumulator.BeforeAccumulator (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := 2^lanes) (c := c) (r := r) (k := k) (n := n)
    (front := front) (suffix := suffix) (queries := queries) (height := height) first second)
  (outcome : PackedPBSAccumulator.AccumulatorOutcome (q := q) (Input := Input) (Cfg := Cfg)
    (Memory := Memory) (AccResponse := AccResponse) (accB := 2^lanes) (accC := cells) (accR := rows)
    (accFront := accFront) (accQueries := accQueries) (accHeight := accHeight) first.heights)
  (supported : (before,some outcome) ∈ support (PackedPBSAccumulator.witness length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase
    dummy first second secondBase accumulators factory initial))

variable {firstE firstPadding firstLookupC : ℕ}
  {FirstK FirstLookupMessage FirstLookupMemory FirstConfigHelperMemory : Type} [Field FirstK] [Algebra (ZMod q) FirstK]
  {firstMode : Mode}
  {firstTag : Root (2*d+1) (∑ i, firstRepetitions i) → Cfg}
  {firstG : Geometry firstLookupC (front+suffix) (2*d+1) (∑ i, firstRepetitions i)}
  {firstSymbolWidth : Root (2*d+1) (∑ i, firstRepetitions i) → ℕ}
  (firstConfig : RectangularRequestLookup.Parameters (ZMod q) FirstK FirstLookupMessage FirstLookupMemory Cfg Input Digest Memory FirstConfigHelperMemory
    firstE firstPadding firstLookupC (front+suffix) (2*d+1) d (fun _ => 3) (fun _ => radix*2) firstRepetitions firstMode)
  (firstDomain : ∀ root, Fin (2^first.heights (firstTag root)) ↪ ZMod q)
  (firstLookupCapacity : ∀ root, 2^firstG.suffix root ≤ firstG.m root * firstSymbolWidth root)
  (firstLookupRadius : Root (2*d+1) (∑ i, firstRepetitions i) → ℕ)
  (firstSourceSymbols : ∀ source, firstSymbolWidth (.inl source) = firstE+firstPadding)
  (firstWidth : 2^lanes = firstE+firstPadding)

variable {secondE secondPadding secondLookupC : ℕ}
  {SecondK SecondLookupMessage SecondLookupMemory SecondConfigHelperMemory : Type} [Field SecondK] [Algebra (ZMod q) SecondK]
  {secondMode : Mode}
  {secondTag : Root (2*d+1) (∑ i, secondRepetitions i) → Cfg}
  {secondG : Geometry secondLookupC (front+suffix) (2*d+1) (∑ i, secondRepetitions i)}
  {secondSymbolWidth : Root (2*d+1) (∑ i, secondRepetitions i) → ℕ}
  (secondConfig : RectangularRequestLookup.Parameters (ZMod q) SecondK SecondLookupMessage SecondLookupMemory Cfg Input Digest Memory SecondConfigHelperMemory
    secondE secondPadding secondLookupC (front+suffix) (2*d+1) d (fun _ => 3) (fun _ => radix*2) secondRepetitions secondMode)
  (secondDomain : ∀ root, Fin (2^first.heights (secondTag root)) ↪ ZMod q)
  (secondLookupCapacity : ∀ root, 2^secondG.suffix root ≤ secondG.m root * secondSymbolWidth root)
  (secondLookupRadius : Root (2*d+1) (∑ i, secondRepetitions i) → ℕ)
  (secondSourceSymbols : ∀ source, secondSymbolWidth (.inl source) = secondE+secondPadding)
  (secondWidth : 2^lanes = secondE+secondPadding)


include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- The actual accumulator external products use the honestly initialized
control rows, or existing first/second lookup/reconstruction, accumulator,
Hadamard/NTT risks or the same later Bad occur. No coefficient, transform,
key-value or external-product truth is a supplied semantic premise. -/
theorem external_products_or_risks
    (coefficients : c = cells) (rounds : r = rows+1) (dimensions : (rows+1)+cells = n+1)
    (linearEncoding : (PackedPBSDecompositionAccumulatorInputs.firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).encoding = hs.encoding)
    (nttCapacity : 2^suffix ≤ m*(2^lanes)) (nttRadius : Fin (2*d+1) → ℕ) (hadamardRadius : ℕ)
    (hadamardGeometry : ∀ factor, first.heights (hs.tag factor) = height)
    (nttGeometry : ∀ (entry : Fin (2*d+1) × Memory × NTTSequence.Child (F := ZMod q) (Input := Input) (Digest := Digest)
    (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory)
    (b := 2^lanes) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height)), entry ∈ (PackedPBSResultAccumulatorSource.originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).1.results →
      ∀ side, first.heights ((base entry.1 entry.2.1).tag side) = height)
    (nttEncoding : ∀ entry, entry ∈ (PackedPBSResultAccumulatorSource.originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).1.results → (base entry.1 entry.2.1).encoding = hs.encoding)
    (evaluationAssociated : ∀ entry member,
      TransportedOriginalNTTSource.parameters base entry first.heights nttCapacity (nttRadius entry.1) (nttGeometry entry member) true =
        TransportedOriginalHadamardSource.parameters hs first.heights nttCapacity hadamardRadius hadamardGeometry
          (PackedPBSOriginalReferences.evaluationFactor entry.1))
    (firstCapacity : 2^suffix ≤ m*(2^lanes)) (firstRadius : ℕ)
    (firstGeometry : ∀ factor, first.heights ((PackedPBSDecompositionAccumulatorInputs.firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag factor) = height)
    (firstComparisonTags : ∀ source, first.sourceTag source = firstTag (.inl source))
    (firstRouting : ∀ source, RectangularLookupSourceInterpretation.squareParameters firstDomain firstLookupCapacity firstLookupRadius firstSourceSymbols source =
      (RecordedSourceWidth.family firstWidth (PackedPBSDecompositionAccumulatorInputs.firstFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported firstCapacity firstRadius firstGeometry)).parameters (PackedPBSComparisonReferences.linearSlot source))
    (firstSlotOrder : firstConfig.slots = RadixLookupSources.comparisonSlots)
    (firstPublicTables : firstConfig.tables = fun limb => RadixLookupSources.publicTable q radix
      (RadixCanonicity.modulusDigit q radix limb.val))
    (firstFull : ∀ limb, firstConfig.active limb = 2^(firstLookupC+(front+suffix)))
    (secondCapacity : 2^suffix ≤ m*(2^lanes)) (secondRadius : ℕ)
    (secondGeometry : ∀ factor, first.heights ((PackedPBSDecompositionAccumulatorInputs.secondLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag factor) = height)
    (secondComparisonTags : ∀ source, second.sourceTag source = secondTag (.inl source))
    (secondRouting : ∀ source, RectangularLookupSourceInterpretation.squareParameters secondDomain secondLookupCapacity secondLookupRadius secondSourceSymbols source =
      (RecordedSourceWidth.family secondWidth (PackedPBSDecompositionAccumulatorInputs.secondFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported secondCapacity secondRadius secondGeometry)).parameters (PackedPBSComparisonReferences.linearSlot source))
    (secondSlotOrder : secondConfig.slots = RadixLookupSources.comparisonSlots)
    (secondPublicTables : secondConfig.tables = fun limb => RadixLookupSources.publicTable q radix
      (RadixCanonicity.modulusDigit q radix limb.val))
    (secondFull : ∀ limb, secondConfig.active limb = 2^(secondLookupC+(front+suffix)))
    (accCapacity : 2^accSuffix ≤ accM*(2^lanes)) (accRadius : ℕ)
    (accGeometry : ∀ factor, first.heights ((PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag factor) = accHeight)
    (firstInputAssociated : ExecutedAccumulatorInputs.parameters first.heights (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) accCapacity accRadius accGeometry
      (PackedPBSAccumulatorReferences.inputSlot false) = (PackedPBSDecompositionAccumulatorInputs.firstFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported firstCapacity firstRadius firstGeometry).parameters DecompositionLinear.input)
    (secondInputAssociated : ExecutedAccumulatorInputs.parameters first.heights (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) accCapacity accRadius accGeometry
      (PackedPBSAccumulatorReferences.inputSlot true) = (PackedPBSDecompositionAccumulatorInputs.secondFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported secondCapacity secondRadius secondGeometry).parameters DecompositionLinear.input)
    (firstDigitAssociated : ∀ level,
      TransportedOriginalNTTSource.parameters base (PackedPBSDifferenceDigitNTT.digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported false level) first.heights nttCapacity (nttRadius (PackedPBSDifferenceDigitNTT.digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported false level).1)
        (nttGeometry (PackedPBSDifferenceDigitNTT.digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported false level) (PackedPBSDifferenceDigitNTT.digitEntry_member length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported false level)) false =
      (PackedPBSDecompositionAccumulatorInputs.firstFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported firstCapacity firstRadius firstGeometry).parameters (DecompositionLinear.digit level))
    (secondDigitAssociated : ∀ level,
      TransportedOriginalNTTSource.parameters base (PackedPBSDifferenceDigitNTT.digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported true level) first.heights nttCapacity (nttRadius (PackedPBSDifferenceDigitNTT.digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported true level).1)
        (nttGeometry (PackedPBSDifferenceDigitNTT.digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported true level) (PackedPBSDifferenceDigitNTT.digitEntry_member length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported true level)) false =
      (PackedPBSDecompositionAccumulatorInputs.secondFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported secondCapacity secondRadius secondGeometry).parameters (DecompositionLinear.digit level))
    (resultAssociated : TransportedOriginalNTTSource.parameters base (PackedPBSResultAccumulatorSource.resultEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) first.heights nttCapacity (nttRadius (PackedPBSResultAccumulatorSource.resultEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).1)
      (nttGeometry (PackedPBSResultAccumulatorSource.resultEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSResultAccumulatorSource.resultEntry_member length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)) false =
      PackedPBSResultAccumulatorSource.externalParameters length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported accCapacity accRadius accGeometry)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state)
    (audited : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) state)
    (sound : RecordedCheckpointQueries.Sound (AmbientMatrixSource.Shape first.heights) state)
    (arithmetic : outcome.2.1.1.accepted = true) (opened : outcome.2.1.2.accepted = true)
    (radixLarge : 1 < radix) (radixSmall : radix < q) (enough : q-1 < radix^d)
    (bits : ℕ) (radix_eq : radix = 2^bits)
    (controls : HonestControlKeyTable.Controls (q := q) (cells := cells) (lanes := lanes) (rows := rows) (levels := d))
    (receipt : HonestControlKeySetup.Receipt (PackedPBSHonestControlKeys.parameters hs first nttCapacity hadamardRadius hadamardGeometry)
      hs.encoding psi controls family.keys initial.hash.log)
    (keyEnough : ∀ slot, (PackedPBSHonestControlKeys.parameters hs first nttCapacity hadamardRadius hadamardGeometry slot).degree ≤ 2^first.heights (PackedPBSHonestControlKeys.parameters hs first nttCapacity hadamardRadius hadamardGeometry slot).tag)
    (keyMargin : ∀ slot, 2*(PackedPBSHonestControlKeys.parameters hs first nttCapacity hadamardRadius hadamardGeometry slot).radius <
      Code.minDist (BlockCode.code (PackedPBSHonestControlKeys.parameters hs first nttCapacity hadamardRadius hadamardGeometry slot).domain
        (PackedPBSHonestControlKeys.parameters hs first nttCapacity hadamardRadius hadamardGeometry slot).degree (2^lanes) :
          Set (Fin (2^first.heights (PackedPBSHonestControlKeys.parameters hs first nttCapacity hadamardRadius hadamardGeometry slot).tag) → Fin (2^lanes) → ZMod q)))
 :
    (∀ position, DecodedAccumulatorRows.decode (PackedPBSDecompositionAccumulatorInputs.accumulatorSources length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported accCapacity accRadius).external position =
      NativeBlindRotation.externalProduct bits (controls position) (DecodedAccumulatorRows.decode (PackedPBSDecompositionAccumulatorInputs.accumulatorSources length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported accCapacity accRadius).difference position)) ∨
      RectangularOwnedRequestSources.OriginalFalse hs.encoding dummy firstConfig firstDomain firstLookupCapacity firstLookupRadius (PackedPBSDecompositionAccumulatorInputs.firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) ∨
      OwnedLinearSoundness.OriginalRisk (PackedPBSDecompositionAccumulatorInputs.firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy firstCapacity firstRadius (PackedPBSFirstCanonicalDigits.linearChild (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first initial before.1.1.1 (PackedPBSDecompositionAccumulatorInputs.firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSDecompositionAccumulatorInputs.firstSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)) ∨
      RectangularOwnedRequestSources.OriginalFalse hs.encoding dummy secondConfig secondDomain secondLookupCapacity secondLookupRadius (PackedPBSDecompositionAccumulatorInputs.secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) ∨
      AmbientLinear.OriginalRisk first.heights (PackedPBSDecompositionAccumulatorInputs.secondLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy secondCapacity secondRadius (PackedPBSSecondCanonicalDigits.linearChild (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before.1 (PackedPBSDecompositionAccumulatorInputs.secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSDecompositionAccumulatorInputs.secondSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)) ∨
      OwnedAmbientAccumulator.OriginalRisk first.heights (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy accCapacity accRadius outcome ∨
      OriginalFactorExceptionUnion.OriginalRisk (PackedPBSHadamardNTT.hadamard family hs) dummy nttCapacity hadamardRadius before.1.1.1.1.1 ∨
      NTTLoopProbability.AnyRisk (PackedPBSNTTLoop.factory length psi primitive family base) dummy nttCapacity nttRadius (PackedPBSResultAccumulatorSource.originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).1 ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) state := by
  classical
  by_cases failed : RectangularOwnedRequestSources.OriginalFalse hs.encoding dummy firstConfig firstDomain firstLookupCapacity firstLookupRadius (PackedPBSDecompositionAccumulatorInputs.firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) ∨
      OwnedLinearSoundness.OriginalRisk (PackedPBSDecompositionAccumulatorInputs.firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy firstCapacity firstRadius (PackedPBSFirstCanonicalDigits.linearChild (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first initial before.1.1.1 (PackedPBSDecompositionAccumulatorInputs.firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSDecompositionAccumulatorInputs.firstSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)) ∨
      RectangularOwnedRequestSources.OriginalFalse hs.encoding dummy secondConfig secondDomain secondLookupCapacity secondLookupRadius (PackedPBSDecompositionAccumulatorInputs.secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) ∨
      AmbientLinear.OriginalRisk first.heights (PackedPBSDecompositionAccumulatorInputs.secondLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy secondCapacity secondRadius (PackedPBSSecondCanonicalDigits.linearChild (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before.1 (PackedPBSDecompositionAccumulatorInputs.secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSDecompositionAccumulatorInputs.secondSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)) ∨
      OwnedAmbientAccumulator.OriginalRisk first.heights (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy accCapacity accRadius outcome ∨
      OriginalFactorExceptionUnion.OriginalRisk (PackedPBSHadamardNTT.hadamard family hs) dummy nttCapacity hadamardRadius before.1.1.1.1.1 ∨
      NTTLoopProbability.AnyRisk (PackedPBSNTTLoop.factory length psi primitive family base) dummy nttCapacity nttRadius (PackedPBSResultAccumulatorSource.originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).1 ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) state
  · exact Or.inr failed
  left
  have native : PBSHadamard.Relation
      (RecordedPaddedSourceFamily.logical (PackedPBSOriginalTransformCoverage.hadamardSources hs first second before nttCapacity hadamardRadius hadamardGeometry)
        hs.encoding dummy (n+1)) ∧ PackedPBSOriginalTransformCoverage.Transforms length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported nttCapacity nttRadius hadamardRadius hadamardGeometry := by
    rcases PackedPBSOriginalTransformCoverage.native_relations_or_risks length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported linearEncoding nttCapacity nttRadius hadamardRadius hadamardGeometry
      nttGeometry nttEncoding evaluationAssociated state retained audited with verified | hadamard | ntt | bad
    · exact verified
    · exact False.elim (failed (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (hadamard))))))))
    · exact False.elim (failed (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (ntt)))))))))
    · exact False.elim (failed (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (bad)))))))))
  have keyFits : ∀ slot, (rows+1)+cells ≤ (PackedPBSHonestControlKeys.parameters hs first nttCapacity hadamardRadius hadamardGeometry slot).front+
      (PackedPBSHonestControlKeys.parameters hs first nttCapacity hadamardRadius hadamardGeometry slot).suffix := by
    intro slot
    change (rows+1)+cells ≤ front+suffix
    have physical := hs.dimensions
    omega
  have keys := PackedPBSHonestControlKeys.keys_or_bad length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported linearEncoding nttCapacity hadamardRadius hadamardGeometry controls receipt dimensions
    state retained sound keyEnough keyMargin keyFits
  have actualKeys := keys.resolve_right (fun bad => failed (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (bad)))))))))
  have result := PackedPBSResultAccumulatorSource.retained_result_rows_eq_or_bad length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported coefficients rounds linearEncoding
    nttCapacity (nttRadius (PackedPBSResultAccumulatorSource.resultEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).1) (nttGeometry (PackedPBSResultAccumulatorSource.resultEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSResultAccumulatorSource.resultEntry_member length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported))
    (nttEncoding (PackedPBSResultAccumulatorSource.resultEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSResultAccumulatorSource.resultEntry_member length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)) accCapacity accRadius accGeometry resultAssociated state retained audited
  have actualResult : PackedPBSNativeExternalProduct.ResultRows length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported rounds nttCapacity nttRadius accCapacity accRadius :=
    result.resolve_right (fun bad => failed (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (bad)))))))))
  have actualDigits : PackedPBSNativeExternalProduct.DigitRows length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported rounds nttCapacity nttRadius accCapacity accRadius bits := by
    intro source level position half
    cases source
    · rcases PackedPBSDifferenceDigitNTT.First.canonical_digit_rows_or_risks length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported
        firstConfig firstDomain firstLookupCapacity firstLookupRadius firstSourceSymbols firstWidth
        firstCapacity firstRadius firstGeometry linearEncoding
        firstComparisonTags firstRouting firstSlotOrder firstPublicTables firstFull state retained audited radixLarge radixSmall enough
        accCapacity accRadius accGeometry firstInputAssociated arithmetic opened bits radix_eq coefficients rounds level
        nttCapacity (nttRadius (PackedPBSDifferenceDigitNTT.digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported false level).1) (nttGeometry (PackedPBSDifferenceDigitNTT.digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported false level) (PackedPBSDifferenceDigitNTT.digitEntry_member length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported false level))
        (nttEncoding (PackedPBSDifferenceDigitNTT.digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported false level) (PackedPBSDifferenceDigitNTT.digitEntry_member length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported false level)) (firstDigitAssociated level) with rows | lookup | linear | accumulator | bad
      · exact rows position half
      · exact False.elim (failed (Or.inl (lookup)))
      · exact False.elim (failed (Or.inr (Or.inl (linear))))
      · exact False.elim (failed (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (accumulator)))))))
      · exact False.elim (failed (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (bad)))))))))
    · rcases PackedPBSDifferenceDigitNTT.Second.canonical_digit_rows_or_risks length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported
        secondConfig secondDomain secondLookupCapacity secondLookupRadius secondSourceSymbols secondWidth
        secondCapacity secondRadius secondGeometry
        secondComparisonTags secondRouting secondSlotOrder secondPublicTables secondFull state retained audited radixLarge radixSmall enough
        accCapacity accRadius accGeometry secondInputAssociated arithmetic opened bits radix_eq coefficients rounds linearEncoding level
        nttCapacity (nttRadius (PackedPBSDifferenceDigitNTT.digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported true level).1) (nttGeometry (PackedPBSDifferenceDigitNTT.digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported true level) (PackedPBSDifferenceDigitNTT.digitEntry_member length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported true level))
        (nttEncoding (PackedPBSDifferenceDigitNTT.digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported true level) (PackedPBSDifferenceDigitNTT.digitEntry_member length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported true level)) (secondDigitAssociated level) with rows | lookup | linear | accumulator | bad
      · exact rows position half
      · exact False.elim (failed (Or.inr (Or.inr (Or.inl (lookup)))))
      · exact False.elim (failed (Or.inr (Or.inr (Or.inr (Or.inl (linear))))))
      · exact False.elim (failed (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (accumulator)))))))
      · exact False.elim (failed (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (bad)))))))))
  exact PackedPBSNativeExternalProduct.external_product_of_relations length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported coefficients rounds dimensions nttCapacity nttRadius hadamardRadius hadamardGeometry
    accCapacity accRadius bits controls native actualDigits actualResult actualKeys

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- Actual hash-only control setup returns this caller's roots and native
initial state. Its factual receipt is derived in the same execution history;
no extra setup safety or external-product certificate is assumed. -/
theorem external_products_from_setup_or_risks {SetupIndex : Type} {setupBase : OracleSpec SetupIndex}
    (setupImpl : QueryImpl setupBase ProbComp)
    (coefficients : c = cells) (rounds : r = rows+1) (dimensions : (rows+1)+cells = n+1)
    (linearEncoding : (PackedPBSDecompositionAccumulatorInputs.firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).encoding = hs.encoding)
    (nttCapacity : 2^suffix ≤ m*(2^lanes)) (nttRadius : Fin (2*d+1) → ℕ) (hadamardRadius : ℕ)
    (hadamardGeometry : ∀ factor, first.heights (hs.tag factor) = height)
    (nttGeometry : ∀ (entry : Fin (2*d+1) × Memory × NTTSequence.Child (F := ZMod q) (Input := Input) (Digest := Digest)
    (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory)
    (b := 2^lanes) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height)), entry ∈ (PackedPBSResultAccumulatorSource.originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).1.results →
      ∀ side, first.heights ((base entry.1 entry.2.1).tag side) = height)
    (nttEncoding : ∀ entry, entry ∈ (PackedPBSResultAccumulatorSource.originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).1.results → (base entry.1 entry.2.1).encoding = hs.encoding)
    (evaluationAssociated : ∀ entry member,
      TransportedOriginalNTTSource.parameters base entry first.heights nttCapacity (nttRadius entry.1) (nttGeometry entry member) true =
        TransportedOriginalHadamardSource.parameters hs first.heights nttCapacity hadamardRadius hadamardGeometry
          (PackedPBSOriginalReferences.evaluationFactor entry.1))
    (firstCapacity : 2^suffix ≤ m*(2^lanes)) (firstRadius : ℕ)
    (firstGeometry : ∀ factor, first.heights ((PackedPBSDecompositionAccumulatorInputs.firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag factor) = height)
    (firstComparisonTags : ∀ source, first.sourceTag source = firstTag (.inl source))
    (firstRouting : ∀ source, RectangularLookupSourceInterpretation.squareParameters firstDomain firstLookupCapacity firstLookupRadius firstSourceSymbols source =
      (RecordedSourceWidth.family firstWidth (PackedPBSDecompositionAccumulatorInputs.firstFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported firstCapacity firstRadius firstGeometry)).parameters (PackedPBSComparisonReferences.linearSlot source))
    (firstSlotOrder : firstConfig.slots = RadixLookupSources.comparisonSlots)
    (firstPublicTables : firstConfig.tables = fun limb => RadixLookupSources.publicTable q radix
      (RadixCanonicity.modulusDigit q radix limb.val))
    (firstFull : ∀ limb, firstConfig.active limb = 2^(firstLookupC+(front+suffix)))
    (secondCapacity : 2^suffix ≤ m*(2^lanes)) (secondRadius : ℕ)
    (secondGeometry : ∀ factor, first.heights ((PackedPBSDecompositionAccumulatorInputs.secondLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag factor) = height)
    (secondComparisonTags : ∀ source, second.sourceTag source = secondTag (.inl source))
    (secondRouting : ∀ source, RectangularLookupSourceInterpretation.squareParameters secondDomain secondLookupCapacity secondLookupRadius secondSourceSymbols source =
      (RecordedSourceWidth.family secondWidth (PackedPBSDecompositionAccumulatorInputs.secondFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported secondCapacity secondRadius secondGeometry)).parameters (PackedPBSComparisonReferences.linearSlot source))
    (secondSlotOrder : secondConfig.slots = RadixLookupSources.comparisonSlots)
    (secondPublicTables : secondConfig.tables = fun limb => RadixLookupSources.publicTable q radix
      (RadixCanonicity.modulusDigit q radix limb.val))
    (secondFull : ∀ limb, secondConfig.active limb = 2^(secondLookupC+(front+suffix)))
    (accCapacity : 2^accSuffix ≤ accM*(2^lanes)) (accRadius : ℕ)
    (accGeometry : ∀ factor, first.heights ((PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag factor) = accHeight)
    (firstInputAssociated : ExecutedAccumulatorInputs.parameters first.heights (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) accCapacity accRadius accGeometry
      (PackedPBSAccumulatorReferences.inputSlot false) = (PackedPBSDecompositionAccumulatorInputs.firstFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported firstCapacity firstRadius firstGeometry).parameters DecompositionLinear.input)
    (secondInputAssociated : ExecutedAccumulatorInputs.parameters first.heights (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) accCapacity accRadius accGeometry
      (PackedPBSAccumulatorReferences.inputSlot true) = (PackedPBSDecompositionAccumulatorInputs.secondFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported secondCapacity secondRadius secondGeometry).parameters DecompositionLinear.input)
    (firstDigitAssociated : ∀ level,
      TransportedOriginalNTTSource.parameters base (PackedPBSDifferenceDigitNTT.digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported false level) first.heights nttCapacity (nttRadius (PackedPBSDifferenceDigitNTT.digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported false level).1)
        (nttGeometry (PackedPBSDifferenceDigitNTT.digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported false level) (PackedPBSDifferenceDigitNTT.digitEntry_member length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported false level)) false =
      (PackedPBSDecompositionAccumulatorInputs.firstFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported firstCapacity firstRadius firstGeometry).parameters (DecompositionLinear.digit level))
    (secondDigitAssociated : ∀ level,
      TransportedOriginalNTTSource.parameters base (PackedPBSDifferenceDigitNTT.digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported true level) first.heights nttCapacity (nttRadius (PackedPBSDifferenceDigitNTT.digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported true level).1)
        (nttGeometry (PackedPBSDifferenceDigitNTT.digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported true level) (PackedPBSDifferenceDigitNTT.digitEntry_member length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported true level)) false =
      (PackedPBSDecompositionAccumulatorInputs.secondFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported secondCapacity secondRadius secondGeometry).parameters (DecompositionLinear.digit level))
    (resultAssociated : TransportedOriginalNTTSource.parameters base (PackedPBSResultAccumulatorSource.resultEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) first.heights nttCapacity (nttRadius (PackedPBSResultAccumulatorSource.resultEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).1)
      (nttGeometry (PackedPBSResultAccumulatorSource.resultEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSResultAccumulatorSource.resultEntry_member length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)) false =
      PackedPBSResultAccumulatorSource.externalParameters length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported accCapacity accRadius accGeometry)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state)
    (audited : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) state)
    (sound : RecordedCheckpointQueries.Sound (AmbientMatrixSource.Shape first.heights) state)
    (arithmetic : outcome.2.1.1.accepted = true) (opened : outcome.2.1.2.accepted = true)
    (radixLarge : 1 < radix) (radixSmall : radix < q) (enough : q-1 < radix^d)
    (bits : ℕ) (radix_eq : radix = 2^bits)
    (controls : HonestControlKeyTable.Controls (q := q) (cells := cells) (lanes := lanes) (rows := rows) (levels := d))
    (setupSupported : (family.keys,initial) ∈ support ((simulateQ
      (CheckpointExecution.handler setupImpl hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height))
      (HonestControlKeySetup.program (PackedPBSHonestControlKeys.parameters hs first nttCapacity hadamardRadius hadamardGeometry)
        hs.encoding psi controls)).run (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height))))
    (keyEnough : ∀ slot, (PackedPBSHonestControlKeys.parameters hs first nttCapacity hadamardRadius hadamardGeometry slot).degree ≤ 2^first.heights (PackedPBSHonestControlKeys.parameters hs first nttCapacity hadamardRadius hadamardGeometry slot).tag)
    (keyMargin : ∀ slot, 2*(PackedPBSHonestControlKeys.parameters hs first nttCapacity hadamardRadius hadamardGeometry slot).radius <
      Code.minDist (BlockCode.code (PackedPBSHonestControlKeys.parameters hs first nttCapacity hadamardRadius hadamardGeometry slot).domain
        (PackedPBSHonestControlKeys.parameters hs first nttCapacity hadamardRadius hadamardGeometry slot).degree (2^lanes) :
          Set (Fin (2^first.heights (PackedPBSHonestControlKeys.parameters hs first nttCapacity hadamardRadius hadamardGeometry slot).tag) → Fin (2^lanes) → ZMod q)))
 :
    (∀ position, DecodedAccumulatorRows.decode (PackedPBSDecompositionAccumulatorInputs.accumulatorSources length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported accCapacity accRadius).external position =
      NativeBlindRotation.externalProduct bits (controls position) (DecodedAccumulatorRows.decode (PackedPBSDecompositionAccumulatorInputs.accumulatorSources length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported accCapacity accRadius).difference position)) ∨
      RectangularOwnedRequestSources.OriginalFalse hs.encoding dummy firstConfig firstDomain firstLookupCapacity firstLookupRadius (PackedPBSDecompositionAccumulatorInputs.firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) ∨
      OwnedLinearSoundness.OriginalRisk (PackedPBSDecompositionAccumulatorInputs.firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy firstCapacity firstRadius (PackedPBSFirstCanonicalDigits.linearChild (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first initial before.1.1.1 (PackedPBSDecompositionAccumulatorInputs.firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSDecompositionAccumulatorInputs.firstSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)) ∨
      RectangularOwnedRequestSources.OriginalFalse hs.encoding dummy secondConfig secondDomain secondLookupCapacity secondLookupRadius (PackedPBSDecompositionAccumulatorInputs.secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) ∨
      AmbientLinear.OriginalRisk first.heights (PackedPBSDecompositionAccumulatorInputs.secondLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy secondCapacity secondRadius (PackedPBSSecondCanonicalDigits.linearChild (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before.1 (PackedPBSDecompositionAccumulatorInputs.secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSDecompositionAccumulatorInputs.secondSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)) ∨
      OwnedAmbientAccumulator.OriginalRisk first.heights (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy accCapacity accRadius outcome ∨
      OriginalFactorExceptionUnion.OriginalRisk (PackedPBSHadamardNTT.hadamard family hs) dummy nttCapacity hadamardRadius before.1.1.1.1.1 ∨
      NTTLoopProbability.AnyRisk (PackedPBSNTTLoop.factory length psi primitive family base) dummy nttCapacity nttRadius (PackedPBSResultAccumulatorSource.originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).1 ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) state := by
  have initialized := HonestControlKeySetup.initialized setupImpl
    (PackedPBSHonestControlKeys.parameters hs first nttCapacity hadamardRadius hadamardGeometry)
    hs.encoding dummy psi controls (RecordedSourceCoherence.Shape Cfg height) (family.keys,initial) setupSupported
  exact external_products_or_risks length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported firstConfig firstDomain firstLookupCapacity firstLookupRadius firstSourceSymbols firstWidth secondConfig secondDomain secondLookupCapacity secondLookupRadius secondSourceSymbols secondWidth coefficients rounds dimensions linearEncoding nttCapacity nttRadius hadamardRadius hadamardGeometry nttGeometry nttEncoding evaluationAssociated firstCapacity firstRadius firstGeometry firstComparisonTags firstRouting firstSlotOrder firstPublicTables firstFull secondCapacity secondRadius secondGeometry secondComparisonTags secondRouting secondSlotOrder secondPublicTables secondFull accCapacity accRadius accGeometry firstInputAssociated secondInputAssociated firstDigitAssociated secondDigitAssociated resultAssociated state retained audited sound arithmetic opened radixLarge radixSmall enough bits radix_eq controls initialized.1 keyEnough keyMargin

end
end FormalProof4FHE.HasteBoots.PackedPBSNativeExternalProductCoverage
