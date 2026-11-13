module
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

/-! Canonical digits with actual rectangular lookup layouts in the actual
supported PBS prefix. All predecessor support, selected factory memory and
original owners are recovered from this same retained execution. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSRectangularCanonicalDigits
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

namespace First
variable {e padding lookupC : ℕ}
  {K LookupMessage LookupMemory ConfigHelperMemory : Type} [Field K] [Algebra (ZMod q) K]
  {mode : Mode}
  {tag : Root (2*d+1) (∑ i, firstRepetitions i) → Cfg}
  {g : Geometry lookupC (front+suffix) (2*d+1) (∑ i, firstRepetitions i)}
  {symbolWidth : Root (2*d+1) (∑ i, firstRepetitions i) → ℕ}
  (config : RectangularRequestLookup.Parameters (ZMod q) K LookupMessage LookupMemory Cfg Input Digest Memory ConfigHelperMemory
    e padding lookupC (front+suffix) (2*d+1) d (fun _ => 3) (fun _ => radix*2) firstRepetitions mode)
  (domain : ∀ root, Fin (2^first.heights (tag root)) ↪ ZMod q)
  (lookupCapacity : ∀ root, 2^g.suffix root ≤ g.m root * symbolWidth root)
  (lookupRadius : Root (2*d+1) (∑ i, firstRepetitions i) → ℕ)
  (sourceSymbols : ∀ source, symbolWidth (.inl source) = e+padding)
  (width : 2^lanes = e+padding)

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- The actual first reconstruction and actual rectangular lookup enforce
canonical digits of their executed sources, without replacing lookup padding. -/
theorem canonical_digits_or_risks
    (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (geometry : ∀ factor, first.heights ((PackedPBSDecompositionAccumulatorInputs.firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag factor) = height)
    (encoding : (PackedPBSDecompositionAccumulatorInputs.firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).encoding = hs.encoding)
    (comparisonTags : ∀ source, first.sourceTag source = tag (.inl source))
    (routing : ∀ source, RectangularLookupSourceInterpretation.squareParameters domain lookupCapacity lookupRadius sourceSymbols source =
      (RecordedSourceWidth.family width (PackedPBSDecompositionAccumulatorInputs.firstFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry)).parameters (PackedPBSComparisonReferences.linearSlot source))
    (slotOrder : config.slots = RadixLookupSources.comparisonSlots)
    (publicTables : config.tables = fun limb => RadixLookupSources.publicTable q radix
      (RadixCanonicity.modulusDigit q radix limb.val))
    (full : ∀ limb, config.active limb = 2^(lookupC+(front+suffix)))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state)
    (audited : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) state)
    (radixLarge : 1 < radix) (radixSmall : radix < q) (enough : q-1 < radix^d) :
    (∀ cell lane digit,
      (RecordedPaddedSourceFamily.logical (PackedPBSDecompositionAccumulatorInputs.firstFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix) (DecompositionLinear.digit digit) cell lane).val =
        (RecordedPaddedSourceFamily.logical (PackedPBSDecompositionAccumulatorInputs.firstFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix) DecompositionLinear.input cell lane).val /
          radix^digit.val % radix) ∨
      RectangularOwnedRequestSources.OriginalFalse hs.encoding dummy config domain lookupCapacity lookupRadius (PackedPBSDecompositionAccumulatorInputs.firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) ∨
      OwnedLinearSoundness.OriginalRisk (PackedPBSDecompositionAccumulatorInputs.firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy capacity radius (PackedPBSFirstCanonicalDigits.linearChild (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first initial before.1.1.1 (PackedPBSDecompositionAccumulatorInputs.firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSDecompositionAccumulatorInputs.firstSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) state := by
  have originalAudit : CheckpointExecution.Audited (PackedPBSDecompositionAccumulatorInputs.firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).encoding dummy
      (AmbientMatrixSource.Shape first.heights) state := by
    rw [encoding]
    exact audited
  have result := ExecutedTransportedRectangularRadixWidth.canonical_digits_or_risks first (PackedPBSDecompositionAccumulatorInputs.firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy
    (PackedPBSFirstCanonicalDigits.predecessor (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first initial before.1.1.1 (PackedPBSDecompositionAccumulatorInputs.firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSDecompositionAccumulatorInputs.firstSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)).2 (PackedPBSFirstCanonicalDigits.linearChild (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first initial before.1.1.1 (PackedPBSDecompositionAccumulatorInputs.firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSDecompositionAccumulatorInputs.firstSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported))
    (PackedPBSFirstCanonicalDigits.linearExecuted (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first initial before.1.1.1 (PackedPBSDecompositionAccumulatorInputs.firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSDecompositionAccumulatorInputs.firstSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) encoding)
    (PackedPBSDecompositionAccumulatorInputs.firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSFirstCanonicalDigits.comparisonExecuted (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first initial before.1.1.1 (PackedPBSDecompositionAccumulatorInputs.firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSDecompositionAccumulatorInputs.firstSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) encoding)
    config domain lookupCapacity lookupRadius sourceSymbols width capacity radius geometry state
    (PackedPBSDecompositionAccumulatorInputs.firstRetained length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported state retained)
    originalAudit comparisonTags routing slotOrder publicTables full
    (PackedPBSFirstCanonicalDigits.linearAccepted (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first initial before.1.1.1 (PackedPBSDecompositionAccumulatorInputs.firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSDecompositionAccumulatorInputs.firstSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)) rfl radixLarge radixSmall enough
  rw [encoding] at result
  exact result

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- The same actual rectangular constraints enforce native canonical digit
polynomials at any original coefficient addresses, outside existing risks. -/
theorem canonical_polynomials_or_risks
    (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (geometry : ∀ factor, first.heights ((PackedPBSDecompositionAccumulatorInputs.firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag factor) = height)
    (encoding : (PackedPBSDecompositionAccumulatorInputs.firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).encoding = hs.encoding)
    (comparisonTags : ∀ source, first.sourceTag source = tag (.inl source))
    (routing : ∀ source, RectangularLookupSourceInterpretation.squareParameters domain lookupCapacity lookupRadius sourceSymbols source =
      (RecordedSourceWidth.family width (PackedPBSDecompositionAccumulatorInputs.firstFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry)).parameters (PackedPBSComparisonReferences.linearSlot source))
    (slotOrder : config.slots = RadixLookupSources.comparisonSlots)
    (publicTables : config.tables = fun limb => RadixLookupSources.publicTable q radix
      (RadixCanonicity.modulusDigit q radix limb.val))
    (full : ∀ limb, config.active limb = 2^(lookupC+(front+suffix)))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state)
    (audited : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) state)
    (radixLarge : 1 < radix) (radixSmall : radix < q) (enough : q-1 < radix^d)
    (bits : ℕ) (radix_eq : radix = 2^bits)
    (address : Fin (2^(cells+lanes)) → MatrixFold.Cube (front+suffix) × Fin (2^lanes)) :
    (∀ level, DecompositionBlindRotation.project (RecordedPaddedSourceFamily.logical (PackedPBSDecompositionAccumulatorInputs.firstFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix)) address (DecompositionLinear.digit level) =
      NativeBlindRotation.digit bits level (DecompositionBlindRotation.project (RecordedPaddedSourceFamily.logical (PackedPBSDecompositionAccumulatorInputs.firstFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix)) address DecompositionLinear.input)) ∨
      RectangularOwnedRequestSources.OriginalFalse hs.encoding dummy config domain lookupCapacity lookupRadius (PackedPBSDecompositionAccumulatorInputs.firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) ∨
      OwnedLinearSoundness.OriginalRisk (PackedPBSDecompositionAccumulatorInputs.firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy capacity radius (PackedPBSFirstCanonicalDigits.linearChild (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first initial before.1.1.1 (PackedPBSDecompositionAccumulatorInputs.firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSDecompositionAccumulatorInputs.firstSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) state := by
  rcases canonical_digits_or_risks length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported config domain lookupCapacity lookupRadius sourceSymbols width
    capacity radius geometry encoding comparisonTags routing slotOrder publicTables full state retained audited radixLarge radixSmall enough
      with canonical | failedLookup | failedLinear | bad
  · left
    intro level
    funext index
    let inputValue := (RecordedPaddedSourceFamily.logical (PackedPBSDecompositionAccumulatorInputs.firstFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix)) DecompositionLinear.input (address index).1 (address index).2
    let digitValue := (RecordedPaddedSourceFamily.logical (PackedPBSDecompositionAccumulatorInputs.firstFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix)) (DecompositionLinear.digit level) (address index).1 (address index).2
    have same := congrArg (fun value : ℕ => (value : ZMod q)) (canonical (address index).1 (address index).2 level)
    change (digitValue.val : ZMod q) = ((inputValue.val / radix^level.val % radix : ℕ) : ZMod q) at same
    rw [ZMod.natCast_zmod_val,radix_eq] at same
    exact same
  · exact Or.inr (Or.inl failedLookup)
  · exact Or.inr (Or.inr (Or.inl failedLinear))
  · exact Or.inr (Or.inr (Or.inr bad))

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- Matching public input decoders derives the original physical row arity. -/
theorem input_dimensions
    (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (geometry : ∀ factor, first.heights ((PackedPBSDecompositionAccumulatorInputs.firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag factor) = height)
    (accCapacity : 2^accSuffix ≤ accM*(2^lanes)) (accRadius : ℕ)
    (accGeometry : ∀ factor, first.heights ((PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag factor) = accHeight)
    (inputAssociated : ExecutedAccumulatorInputs.parameters first.heights (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) accCapacity accRadius accGeometry
      (PackedPBSAccumulatorReferences.inputSlot false) = (PackedPBSDecompositionAccumulatorInputs.firstFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry).parameters DecompositionLinear.input) : (rows+1)+cells = front+suffix := by
  have same := congrArg (fun descriptor : RecordedPaddedSource.Parameters (ZMod q) Cfg first.heights (2^lanes) =>
    descriptor.front+descriptor.suffix) inputAssociated
  change accFront+accSuffix = front+suffix at same
  have layout := (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).layout
  omega

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- Real rectangular canonical digits are native digits of the actual
accumulator difference, at every stored round and both physical output halves. -/
theorem canonical_difference_or_risks
    (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (geometry : ∀ factor, first.heights ((PackedPBSDecompositionAccumulatorInputs.firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag factor) = height)
    (encoding : (PackedPBSDecompositionAccumulatorInputs.firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).encoding = hs.encoding)
    (comparisonTags : ∀ source, first.sourceTag source = tag (.inl source))
    (routing : ∀ source, RectangularLookupSourceInterpretation.squareParameters domain lookupCapacity lookupRadius sourceSymbols source =
      (RecordedSourceWidth.family width (PackedPBSDecompositionAccumulatorInputs.firstFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry)).parameters (PackedPBSComparisonReferences.linearSlot source))
    (slotOrder : config.slots = RadixLookupSources.comparisonSlots)
    (publicTables : config.tables = fun limb => RadixLookupSources.publicTable q radix
      (RadixCanonicity.modulusDigit q radix limb.val))
    (full : ∀ limb, config.active limb = 2^(lookupC+(front+suffix)))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state)
    (audited : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) state)
    (radixLarge : 1 < radix) (radixSmall : radix < q) (enough : q-1 < radix^d)
    (accCapacity : 2^accSuffix ≤ accM*(2^lanes)) (accRadius : ℕ)
    (accGeometry : ∀ factor, first.heights ((PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag factor) = accHeight)
    (inputAssociated : ExecutedAccumulatorInputs.parameters first.heights (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) accCapacity accRadius accGeometry
      (PackedPBSAccumulatorReferences.inputSlot false) = (PackedPBSDecompositionAccumulatorInputs.firstFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry).parameters DecompositionLinear.input)
    (arithmetic : outcome.2.1.1.accepted = true) (opened : outcome.2.1.2.accepted = true)
    (bits : ℕ) (radix_eq : radix = 2^bits) :
    (∀ position outputHalf level, DecompositionBlindRotation.project (RecordedPaddedSourceFamily.logical (PackedPBSDecompositionAccumulatorInputs.firstFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix))
      (PackedHadamardRows.address (Nat.pow_add 2 cells lanes).symm (input_dimensions length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry accCapacity accRadius accGeometry inputAssociated)
        (PackedMonomialRotation.rowIndex position outputHalf)) (DecompositionLinear.digit level) =
        NativeBlindRotation.digit bits level (DecodedAccumulatorRows.decode (PackedPBSDecompositionAccumulatorInputs.accumulatorSources length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported accCapacity accRadius).difference position false)) ∨
      RectangularOwnedRequestSources.OriginalFalse hs.encoding dummy config domain lookupCapacity lookupRadius (PackedPBSDecompositionAccumulatorInputs.firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) ∨
      OwnedLinearSoundness.OriginalRisk (PackedPBSDecompositionAccumulatorInputs.firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy capacity radius (PackedPBSFirstCanonicalDigits.linearChild (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first initial before.1.1.1 (PackedPBSDecompositionAccumulatorInputs.firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSDecompositionAccumulatorInputs.firstSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)) ∨
      OwnedAmbientAccumulator.OriginalRisk first.heights (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy accCapacity accRadius outcome ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) state := by
  rcases PackedPBSDecompositionAccumulatorInputs.first_input_rows_or_risks length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry encoding
    accCapacity accRadius accGeometry inputAssociated state retained audited arithmetic opened with inputRows | accumulatorRisk | bad
  · rcases canonical_digits_or_risks length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported config domain lookupCapacity lookupRadius sourceSymbols width
      capacity radius geometry encoding comparisonTags routing slotOrder publicTables full state retained audited radixLarge radixSmall enough
        with canonical | failedLookup | failedLinear | bad
    · left
      intro position outputHalf level
      let address := PackedHadamardRows.address (Nat.pow_add 2 cells lanes).symm (input_dimensions length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry accCapacity accRadius accGeometry inputAssociated)
        (PackedMonomialRotation.rowIndex position outputHalf)
      have canonicalPoly : DecompositionBlindRotation.project (RecordedPaddedSourceFamily.logical (PackedPBSDecompositionAccumulatorInputs.firstFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix)) address (DecompositionLinear.digit level) =
          NativeBlindRotation.digit bits level (DecompositionBlindRotation.project (RecordedPaddedSourceFamily.logical (PackedPBSDecompositionAccumulatorInputs.firstFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix)) address DecompositionLinear.input) := by
        funext index
        let inputValue := (RecordedPaddedSourceFamily.logical (PackedPBSDecompositionAccumulatorInputs.firstFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix)) DecompositionLinear.input (address index).1 (address index).2
        let digitValue := (RecordedPaddedSourceFamily.logical (PackedPBSDecompositionAccumulatorInputs.firstFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix)) (DecompositionLinear.digit level) (address index).1 (address index).2
        have same := congrArg (fun value : ℕ => (value : ZMod q)) (canonical (address index).1 (address index).2 level)
        change (digitValue.val : ZMod q) = ((inputValue.val / radix^level.val % radix : ℕ) : ZMod q) at same
        rw [ZMod.natCast_zmod_val,radix_eq] at same
        exact same
      have inputPoly := (RecordedNTTProjection.same_address (PackedPBSDecompositionAccumulatorInputs.firstFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) hs.encoding dummy (Nat.pow_add 2 cells lanes).symm
        (input_dimensions length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry accCapacity accRadius accGeometry inputAssociated)
        (show (rows+1)+cells = accFront+accSuffix by have := (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).layout; omega)
        (PackedMonomialRotation.rowIndex position outputHalf) DecompositionLinear.input).trans (inputRows position outputHalf)
      exact canonicalPoly.trans (congrArg (NativeBlindRotation.digit bits level) inputPoly)
    · exact Or.inr (Or.inl failedLookup)
    · exact Or.inr (Or.inr (Or.inl failedLinear))
    · exact Or.inr (Or.inr (Or.inr (Or.inr bad)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl accumulatorRisk)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr bad)))

end First

namespace Second
variable {e padding lookupC : ℕ}
  {K LookupMessage LookupMemory ConfigHelperMemory : Type} [Field K] [Algebra (ZMod q) K]
  {mode : Mode}
  {tag : Root (2*d+1) (∑ i, secondRepetitions i) → Cfg}
  {g : Geometry lookupC (front+suffix) (2*d+1) (∑ i, secondRepetitions i)}
  {symbolWidth : Root (2*d+1) (∑ i, secondRepetitions i) → ℕ}
  (config : RectangularRequestLookup.Parameters (ZMod q) K LookupMessage LookupMemory Cfg Input Digest Memory ConfigHelperMemory
    e padding lookupC (front+suffix) (2*d+1) d (fun _ => 3) (fun _ => radix*2) secondRepetitions mode)
  (domain : ∀ root, Fin (2^first.heights (tag root)) ↪ ZMod q)
  (lookupCapacity : ∀ root, 2^g.suffix root ≤ g.m root * symbolWidth root)
  (lookupRadius : Root (2*d+1) (∑ i, secondRepetitions i) → ℕ)
  (sourceSymbols : ∀ source, symbolWidth (.inl source) = e+padding)
  (width : 2^lanes = e+padding)

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- The actual second reconstruction and actual rectangular lookup enforce
canonical digits of their executed sources, without replacing lookup padding. -/
theorem canonical_digits_or_risks
    (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (geometry : ∀ factor, first.heights ((PackedPBSDecompositionAccumulatorInputs.secondLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag factor) = height)
    (comparisonTags : ∀ source, second.sourceTag source = tag (.inl source))
    (routing : ∀ source, RectangularLookupSourceInterpretation.squareParameters domain lookupCapacity lookupRadius sourceSymbols source =
      (RecordedSourceWidth.family width (PackedPBSDecompositionAccumulatorInputs.secondFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry)).parameters (PackedPBSComparisonReferences.linearSlot source))
    (slotOrder : config.slots = RadixLookupSources.comparisonSlots)
    (publicTables : config.tables = fun limb => RadixLookupSources.publicTable q radix
      (RadixCanonicity.modulusDigit q radix limb.val))
    (full : ∀ limb, config.active limb = 2^(lookupC+(front+suffix)))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state)
    (audited : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) state)
    (radixLarge : 1 < radix) (radixSmall : radix < q) (enough : q-1 < radix^d) :
    (∀ cell lane digit,
      (RecordedPaddedSourceFamily.logical (PackedPBSDecompositionAccumulatorInputs.secondFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix) (DecompositionLinear.digit digit) cell lane).val =
        (RecordedPaddedSourceFamily.logical (PackedPBSDecompositionAccumulatorInputs.secondFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix) DecompositionLinear.input cell lane).val /
          radix^digit.val % radix) ∨
      RectangularOwnedRequestSources.OriginalFalse hs.encoding dummy config domain lookupCapacity lookupRadius (PackedPBSDecompositionAccumulatorInputs.secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) ∨
      AmbientLinear.OriginalRisk first.heights (PackedPBSDecompositionAccumulatorInputs.secondLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy capacity radius (PackedPBSSecondCanonicalDigits.linearChild (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before.1 (PackedPBSDecompositionAccumulatorInputs.secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSDecompositionAccumulatorInputs.secondSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) state := by
  have result := ExecutedAmbientRectangularRadixWidth.canonical_digits_or_risks (PackedPBSSecondComparisons.sharedScheme first.heights second) (PackedPBSDecompositionAccumulatorInputs.secondLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy
    (PackedPBSSecondCanonicalDigits.predecessor (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before.1 (PackedPBSDecompositionAccumulatorInputs.secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSDecompositionAccumulatorInputs.secondSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)).2.2.2 (PackedPBSSecondCanonicalDigits.linearChild (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before.1 (PackedPBSDecompositionAccumulatorInputs.secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSDecompositionAccumulatorInputs.secondSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported))
    (PackedPBSSecondCanonicalDigits.linearExecuted (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before.1 (PackedPBSDecompositionAccumulatorInputs.secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSDecompositionAccumulatorInputs.secondSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported))
    (PackedPBSDecompositionAccumulatorInputs.secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSSecondCanonicalDigits.comparisonExecuted (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before.1 (PackedPBSDecompositionAccumulatorInputs.secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSDecompositionAccumulatorInputs.secondSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported))
    config domain lookupCapacity lookupRadius sourceSymbols width capacity radius geometry state
    (PackedPBSDecompositionAccumulatorInputs.secondRetained length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported state retained)
    audited comparisonTags routing slotOrder publicTables full
    (PackedPBSSecondCanonicalDigits.linearAccepted (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before.1 (PackedPBSDecompositionAccumulatorInputs.secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSDecompositionAccumulatorInputs.secondSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)) rfl radixLarge radixSmall enough
  exact result

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- The same actual rectangular constraints enforce native canonical digit
polynomials at any original coefficient addresses, outside existing risks. -/
theorem canonical_polynomials_or_risks
    (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (geometry : ∀ factor, first.heights ((PackedPBSDecompositionAccumulatorInputs.secondLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag factor) = height)
    (comparisonTags : ∀ source, second.sourceTag source = tag (.inl source))
    (routing : ∀ source, RectangularLookupSourceInterpretation.squareParameters domain lookupCapacity lookupRadius sourceSymbols source =
      (RecordedSourceWidth.family width (PackedPBSDecompositionAccumulatorInputs.secondFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry)).parameters (PackedPBSComparisonReferences.linearSlot source))
    (slotOrder : config.slots = RadixLookupSources.comparisonSlots)
    (publicTables : config.tables = fun limb => RadixLookupSources.publicTable q radix
      (RadixCanonicity.modulusDigit q radix limb.val))
    (full : ∀ limb, config.active limb = 2^(lookupC+(front+suffix)))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state)
    (audited : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) state)
    (radixLarge : 1 < radix) (radixSmall : radix < q) (enough : q-1 < radix^d)
    (bits : ℕ) (radix_eq : radix = 2^bits)
    (address : Fin (2^(cells+lanes)) → MatrixFold.Cube (front+suffix) × Fin (2^lanes)) :
    (∀ level, DecompositionBlindRotation.project (RecordedPaddedSourceFamily.logical (PackedPBSDecompositionAccumulatorInputs.secondFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix)) address (DecompositionLinear.digit level) =
      NativeBlindRotation.digit bits level (DecompositionBlindRotation.project (RecordedPaddedSourceFamily.logical (PackedPBSDecompositionAccumulatorInputs.secondFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix)) address DecompositionLinear.input)) ∨
      RectangularOwnedRequestSources.OriginalFalse hs.encoding dummy config domain lookupCapacity lookupRadius (PackedPBSDecompositionAccumulatorInputs.secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) ∨
      AmbientLinear.OriginalRisk first.heights (PackedPBSDecompositionAccumulatorInputs.secondLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy capacity radius (PackedPBSSecondCanonicalDigits.linearChild (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before.1 (PackedPBSDecompositionAccumulatorInputs.secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSDecompositionAccumulatorInputs.secondSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) state := by
  rcases canonical_digits_or_risks length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported config domain lookupCapacity lookupRadius sourceSymbols width
    capacity radius geometry comparisonTags routing slotOrder publicTables full state retained audited radixLarge radixSmall enough
      with canonical | failedLookup | failedLinear | bad
  · left
    intro level
    funext index
    let inputValue := (RecordedPaddedSourceFamily.logical (PackedPBSDecompositionAccumulatorInputs.secondFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix)) DecompositionLinear.input (address index).1 (address index).2
    let digitValue := (RecordedPaddedSourceFamily.logical (PackedPBSDecompositionAccumulatorInputs.secondFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix)) (DecompositionLinear.digit level) (address index).1 (address index).2
    have same := congrArg (fun value : ℕ => (value : ZMod q)) (canonical (address index).1 (address index).2 level)
    change (digitValue.val : ZMod q) = ((inputValue.val / radix^level.val % radix : ℕ) : ZMod q) at same
    rw [ZMod.natCast_zmod_val,radix_eq] at same
    exact same
  · exact Or.inr (Or.inl failedLookup)
  · exact Or.inr (Or.inr (Or.inl failedLinear))
  · exact Or.inr (Or.inr (Or.inr bad))

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- Matching public input decoders derives the original physical row arity. -/
theorem input_dimensions
    (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (geometry : ∀ factor, first.heights ((PackedPBSDecompositionAccumulatorInputs.secondLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag factor) = height)
    (accCapacity : 2^accSuffix ≤ accM*(2^lanes)) (accRadius : ℕ)
    (accGeometry : ∀ factor, first.heights ((PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag factor) = accHeight)
    (inputAssociated : ExecutedAccumulatorInputs.parameters first.heights (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) accCapacity accRadius accGeometry
      (PackedPBSAccumulatorReferences.inputSlot true) = (PackedPBSDecompositionAccumulatorInputs.secondFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry).parameters DecompositionLinear.input) : (rows+1)+cells = front+suffix := by
  have same := congrArg (fun descriptor : RecordedPaddedSource.Parameters (ZMod q) Cfg first.heights (2^lanes) =>
    descriptor.front+descriptor.suffix) inputAssociated
  change accFront+accSuffix = front+suffix at same
  have layout := (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).layout
  omega

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- Real rectangular canonical digits are native digits of the actual
accumulator difference, at every stored round and both physical output halves. -/
theorem canonical_difference_or_risks
    (capacity : 2^suffix ≤ m*(2^lanes)) (radius : ℕ)
    (geometry : ∀ factor, first.heights ((PackedPBSDecompositionAccumulatorInputs.secondLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag factor) = height)
    (comparisonTags : ∀ source, second.sourceTag source = tag (.inl source))
    (routing : ∀ source, RectangularLookupSourceInterpretation.squareParameters domain lookupCapacity lookupRadius sourceSymbols source =
      (RecordedSourceWidth.family width (PackedPBSDecompositionAccumulatorInputs.secondFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry)).parameters (PackedPBSComparisonReferences.linearSlot source))
    (slotOrder : config.slots = RadixLookupSources.comparisonSlots)
    (publicTables : config.tables = fun limb => RadixLookupSources.publicTable q radix
      (RadixCanonicity.modulusDigit q radix limb.val))
    (full : ∀ limb, config.active limb = 2^(lookupC+(front+suffix)))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2 state)
    (audited : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) state)
    (radixLarge : 1 < radix) (radixSmall : radix < q) (enough : q-1 < radix^d)
    (accCapacity : 2^accSuffix ≤ accM*(2^lanes)) (accRadius : ℕ)
    (accGeometry : ∀ factor, first.heights ((PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).tag factor) = accHeight)
    (inputAssociated : ExecutedAccumulatorInputs.parameters first.heights (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) accCapacity accRadius accGeometry
      (PackedPBSAccumulatorReferences.inputSlot true) = (PackedPBSDecompositionAccumulatorInputs.secondFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry).parameters DecompositionLinear.input)
    (arithmetic : outcome.2.1.1.accepted = true) (opened : outcome.2.1.2.accepted = true)
    (bits : ℕ) (radix_eq : radix = 2^bits) :
    (∀ position outputHalf level, DecompositionBlindRotation.project (RecordedPaddedSourceFamily.logical (PackedPBSDecompositionAccumulatorInputs.secondFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix))
      (PackedHadamardRows.address (Nat.pow_add 2 cells lanes).symm (input_dimensions length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry accCapacity accRadius accGeometry inputAssociated)
        (PackedMonomialRotation.rowIndex position outputHalf)) (DecompositionLinear.digit level) =
        NativeBlindRotation.digit bits level (DecodedAccumulatorRows.decode (PackedPBSDecompositionAccumulatorInputs.accumulatorSources length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported accCapacity accRadius).difference position true)) ∨
      RectangularOwnedRequestSources.OriginalFalse hs.encoding dummy config domain lookupCapacity lookupRadius (PackedPBSDecompositionAccumulatorInputs.secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) ∨
      AmbientLinear.OriginalRisk first.heights (PackedPBSDecompositionAccumulatorInputs.secondLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy capacity radius (PackedPBSSecondCanonicalDigits.linearChild (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before.1 (PackedPBSDecompositionAccumulatorInputs.secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSDecompositionAccumulatorInputs.secondSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)) ∨
      OwnedAmbientAccumulator.OriginalRisk first.heights (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy accCapacity accRadius outcome ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) state := by
  rcases PackedPBSDecompositionAccumulatorInputs.second_input_rows_or_risks length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry
    accCapacity accRadius accGeometry inputAssociated state retained audited arithmetic opened with inputRows | accumulatorRisk | bad
  · rcases canonical_digits_or_risks length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported config domain lookupCapacity lookupRadius sourceSymbols width
      capacity radius geometry comparisonTags routing slotOrder publicTables full state retained audited radixLarge radixSmall enough
        with canonical | failedLookup | failedLinear | bad
    · left
      intro position outputHalf level
      let address := PackedHadamardRows.address (Nat.pow_add 2 cells lanes).symm (input_dimensions length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry accCapacity accRadius accGeometry inputAssociated)
        (PackedMonomialRotation.rowIndex position outputHalf)
      have canonicalPoly : DecompositionBlindRotation.project (RecordedPaddedSourceFamily.logical (PackedPBSDecompositionAccumulatorInputs.secondFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix)) address (DecompositionLinear.digit level) =
          NativeBlindRotation.digit bits level (DecompositionBlindRotation.project (RecordedPaddedSourceFamily.logical (PackedPBSDecompositionAccumulatorInputs.secondFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix)) address DecompositionLinear.input) := by
        funext index
        let inputValue := (RecordedPaddedSourceFamily.logical (PackedPBSDecompositionAccumulatorInputs.secondFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix)) DecompositionLinear.input (address index).1 (address index).2
        let digitValue := (RecordedPaddedSourceFamily.logical (PackedPBSDecompositionAccumulatorInputs.secondFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix)) (DecompositionLinear.digit level) (address index).1 (address index).2
        have same := congrArg (fun value : ℕ => (value : ZMod q)) (canonical (address index).1 (address index).2 level)
        change (digitValue.val : ZMod q) = ((inputValue.val / radix^level.val % radix : ℕ) : ZMod q) at same
        rw [ZMod.natCast_zmod_val,radix_eq] at same
        exact same
      have inputPoly := (RecordedNTTProjection.same_address (PackedPBSDecompositionAccumulatorInputs.secondFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) hs.encoding dummy (Nat.pow_add 2 cells lanes).symm
        (input_dimensions length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry accCapacity accRadius accGeometry inputAssociated)
        (show (rows+1)+cells = accFront+accSuffix by have := (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).layout; omega)
        (PackedMonomialRotation.rowIndex position outputHalf) DecompositionLinear.input).trans (inputRows position outputHalf)
      exact canonicalPoly.trans (congrArg (NativeBlindRotation.digit bits level) inputPoly)
    · exact Or.inr (Or.inl failedLookup)
    · exact Or.inr (Or.inr (Or.inl failedLinear))
    · exact Or.inr (Or.inr (Or.inr (Or.inr bad)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl accumulatorRisk)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr bad)))

end Second

end
end FormalProof4FHE.HasteBoots.PackedPBSRectangularCanonicalDigits
