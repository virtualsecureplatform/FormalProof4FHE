module
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
namespace FormalProof4FHE.HasteBoots.PackedPBSDifferenceDigitNTT
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

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- Every required digit slot was really executed by the accepted original loop. -/
theorem digitEntry_exists (source : Bool) (level : Fin d) :
    ∃ entry ∈ (PackedPBSResultAccumulatorSource.originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).1.results, entry.1 = PackedPBSDecompositionReferences.digitSlot source level := by
  have reached := PackedPBSHadamardNTT.reached_loop length psi primitive family base hs dummy initial
    before.1.1.1.1.1 (PackedPBSResultAccumulatorSource.originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSResultAccumulatorSource.originalSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)
  obtain ⟨incoming,child,member,_,_⟩ := PackedPBSNTTLoop.all_slots_bound length psi primitive family base hs.encoding dummy
    before.1.1.1.1.1.2.1.2.memory before.1.1.1.1.1.2.2 (PackedPBSResultAccumulatorSource.originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) reached.2.2 (PackedPBSResultAccumulatorSource.originalAccepted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)
    (PackedPBSDecompositionReferences.digitSlot source level)
  exact ⟨(_,incoming,child),member,rfl⟩

/-- Select the actual retained digit call, without replaying a child experiment. -/
def digitEntry (source : Bool) (level : Fin d) := Classical.choose (digitEntry_exists length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported source level)

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- The selected digit belongs to the actual retained trace. -/
theorem digitEntry_member (source : Bool) (level : Fin d) :
    (digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported source level) ∈ (PackedPBSResultAccumulatorSource.originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).1.results :=
  (Classical.choose_spec (digitEntry_exists length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported source level)).1

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- Its source/limb is exactly the trusted caller's original digit slot. -/
theorem digitEntry_slot (source : Bool) (level : Fin d) :
    (digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported source level).1 = PackedPBSDecompositionReferences.digitSlot source level :=
  (Classical.choose_spec (digitEntry_exists length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported source level)).2

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported in
/-- Its native algebra/opening acceptance follows from the executed loop gate. -/
theorem digitEntry_accepted (source : Bool) (level : Fin d) :
    AuthenticatedNTT.accepted (digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported source level).2.2.2.1 = true := by
  have reached := PackedPBSHadamardNTT.reached_loop length psi primitive family base hs dummy initial
    before.1.1.1.1.1 (PackedPBSResultAccumulatorSource.originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSResultAccumulatorSource.originalSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)
  exact NTTSequenceHistory.accepted_children (PackedPBSNTTLoop.factory length psi primitive family base) hs.encoding dummy
    (List.finRange (2*d+1)) before.1.1.1.1.1.2.1.2.memory before.1.1.1.1.1.2.2 (PackedPBSResultAccumulatorSource.originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) reached.2.2
    (digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported source level) (digitEntry_member length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported source level) (PackedPBSResultAccumulatorSource.originalAccepted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)

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
/-- Actual retained original NTT coefficient rows are native canonical digits
of the executed accumulator difference, with only existing native risks/Bad. -/
theorem canonical_digit_rows_or_risks
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
    (bits : ℕ) (radix_eq : radix = 2^bits)
    (coefficients : c = cells) (rounds : r = rows+1)
    (level : Fin d)
    (nttCapacity : 2^suffix ≤ m*(2^lanes)) (nttRadius : ℕ)
    (nttGeometry : ∀ side, first.heights ((base (digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported false level).1 (digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported false level).2.1).tag side) = height)
    (nttEncoding : (base (digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported false level).1 (digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported false level).2.1).encoding = hs.encoding)
    (nttAssociated : TransportedOriginalNTTSource.parameters base (digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported false level) first.heights nttCapacity nttRadius nttGeometry false =
      (PackedPBSDecompositionAccumulatorInputs.firstFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry).parameters (DecompositionLinear.digit level)) :
    (∀ position outputHalf, PackedNTTBinding.row length
      (AuthenticatedNTT.sources (base (digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported false level).1 (digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported false level).2.1) dummy nttCapacity nttRadius (digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported false level).2.2.1 false)
      (rounds.symm ▸ PackedMonomialRotation.rowIndex position outputHalf) =
      NativeBlindRotation.digit bits level (DecodedAccumulatorRows.decode
        (PackedPBSDecompositionAccumulatorInputs.accumulatorSources length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported accCapacity accRadius).difference position false)) ∨
      RectangularOwnedRequestSources.OriginalFalse hs.encoding dummy config domain lookupCapacity lookupRadius (PackedPBSDecompositionAccumulatorInputs.firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) ∨
      OwnedLinearSoundness.OriginalRisk (PackedPBSDecompositionAccumulatorInputs.firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy capacity radius (PackedPBSFirstCanonicalDigits.linearChild (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first initial before.1.1.1 (PackedPBSDecompositionAccumulatorInputs.firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSDecompositionAccumulatorInputs.firstSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)) ∨
      OwnedAmbientAccumulator.OriginalRisk first.heights (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy accCapacity accRadius outcome ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) state := by
  subst c
  subst r
  classical
  by_cases bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) state
  · exact Or.inr (Or.inr (Or.inr (Or.inr bad)))
  rcases PackedPBSRectangularCanonicalDigits.First.canonical_difference_or_risks length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported config domain lookupCapacity lookupRadius sourceSymbols width
    capacity radius geometry encoding comparisonTags routing slotOrder publicTables full state retained audited radixLarge radixSmall enough
    accCapacity accRadius accGeometry inputAssociated arithmetic opened bits radix_eq with canonical | failedLookup | failedLinear | failedAccumulator | failure
  · left
    have roots : family.coefficients (digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported false level).1 = (PackedPBSDecompositionAccumulatorInputs.firstFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry).roots (DecompositionLinear.digit level) := by
      rw [digitEntry_slot length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported false level]
      exact ((PackedPBSFirstCanonicalDigits.source_roots (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first initial before.1.1.1 (PackedPBSDecompositionAccumulatorInputs.firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSDecompositionAccumulatorInputs.firstSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) capacity radius geometry).2 level).symm
    intro position outputHalf
    have rowEqual := TransportedOriginalNTTSource.row_agrees_or_bad length psi primitive family base hs dummy initial
      before.1.1.1.1.1 (PackedPBSResultAccumulatorSource.originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSResultAccumulatorSource.originalSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported false level) (digitEntry_member length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported false level)
      first.heights nttCapacity nttRadius nttGeometry nttEncoding (PackedPBSDecompositionAccumulatorInputs.firstFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) (DecompositionLinear.digit level) false
      nttAssociated roots state (PackedPBSResultAccumulatorSource.originalRetained length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported encoding state retained) audited
      (PackedPBSDecompositionAccumulatorInputs.firstRecorded length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry encoding state retained) (PackedMonomialRotation.rowIndex position outputHalf)
    exact (rowEqual.resolve_right bad).trans (canonical position outputHalf level)
  · exact Or.inr (Or.inl failedLookup)
  · exact Or.inr (Or.inr (Or.inl failedLinear))
  · exact Or.inr (Or.inr (Or.inr (Or.inl failedAccumulator)))
  · exact False.elim (bad failure)

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
/-- Actual retained original NTT coefficient rows are native canonical digits
of the executed accumulator difference, with only existing native risks/Bad. -/
theorem canonical_digit_rows_or_risks
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
    (bits : ℕ) (radix_eq : radix = 2^bits)
    (coefficients : c = cells) (rounds : r = rows+1)
    (linearEncoding : (PackedPBSDecompositionAccumulatorInputs.firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported).encoding = hs.encoding)
    (level : Fin d)
    (nttCapacity : 2^suffix ≤ m*(2^lanes)) (nttRadius : ℕ)
    (nttGeometry : ∀ side, first.heights ((base (digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported true level).1 (digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported true level).2.1).tag side) = height)
    (nttEncoding : (base (digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported true level).1 (digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported true level).2.1).encoding = hs.encoding)
    (nttAssociated : TransportedOriginalNTTSource.parameters base (digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported true level) first.heights nttCapacity nttRadius nttGeometry false =
      (PackedPBSDecompositionAccumulatorInputs.secondFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry).parameters (DecompositionLinear.digit level)) :
    (∀ position outputHalf, PackedNTTBinding.row length
      (AuthenticatedNTT.sources (base (digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported true level).1 (digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported true level).2.1) dummy nttCapacity nttRadius (digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported true level).2.2.1 false)
      (rounds.symm ▸ PackedMonomialRotation.rowIndex position outputHalf) =
      NativeBlindRotation.digit bits level (DecodedAccumulatorRows.decode
        (PackedPBSDecompositionAccumulatorInputs.accumulatorSources length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported accCapacity accRadius).difference position true)) ∨
      RectangularOwnedRequestSources.OriginalFalse hs.encoding dummy config domain lookupCapacity lookupRadius (PackedPBSDecompositionAccumulatorInputs.secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) ∨
      AmbientLinear.OriginalRisk first.heights (PackedPBSDecompositionAccumulatorInputs.secondLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy capacity radius (PackedPBSSecondCanonicalDigits.linearChild (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before.1 (PackedPBSDecompositionAccumulatorInputs.secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSDecompositionAccumulatorInputs.secondSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported)) ∨
      OwnedAmbientAccumulator.OriginalRisk first.heights (PackedPBSDecompositionAccumulatorInputs.accumulatorScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) dummy accCapacity accRadius outcome ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) state := by
  subst c
  subst r
  classical
  by_cases bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) state
  · exact Or.inr (Or.inr (Or.inr (Or.inr bad)))
  rcases PackedPBSRectangularCanonicalDigits.Second.canonical_difference_or_risks length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported config domain lookupCapacity lookupRadius sourceSymbols width
    capacity radius geometry comparisonTags routing slotOrder publicTables full state retained audited radixLarge radixSmall enough
    accCapacity accRadius accGeometry inputAssociated arithmetic opened bits radix_eq with canonical | failedLookup | failedLinear | failedAccumulator | failure
  · left
    have roots : family.coefficients (digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported true level).1 = (PackedPBSDecompositionAccumulatorInputs.secondFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry).roots (DecompositionLinear.digit level) := by
      rw [digitEntry_slot length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported true level]
      exact ((PackedPBSSecondCanonicalDigits.source_roots (e := 2^lanes) (padding := 0) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before.1 (PackedPBSDecompositionAccumulatorInputs.secondComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSDecompositionAccumulatorInputs.secondSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) capacity radius geometry).2 level).symm
    intro position outputHalf
    have rowEqual := TransportedOriginalNTTSource.row_agrees_or_bad length psi primitive family base hs dummy initial
      before.1.1.1.1.1 (PackedPBSResultAccumulatorSource.originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (PackedPBSResultAccumulatorSource.originalSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported) (digitEntry length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported true level) (digitEntry_member length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported true level)
      first.heights nttCapacity nttRadius nttGeometry nttEncoding (PackedPBSDecompositionAccumulatorInputs.secondFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry) (DecompositionLinear.digit level) false
      nttAssociated roots state (PackedPBSResultAccumulatorSource.originalRetained length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported linearEncoding state retained) audited
      (PackedPBSDecompositionAccumulatorInputs.secondRecorded length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial before outcome supported capacity radius geometry state retained) (PackedMonomialRotation.rowIndex position outputHalf)
    exact (rowEqual.resolve_right bad).trans (canonical position outputHalf level)
  · exact Or.inr (Or.inl failedLookup)
  · exact Or.inr (Or.inr (Or.inl failedLinear))
  · exact Or.inr (Or.inr (Or.inr (Or.inl failedAccumulator)))
  · exact False.elim (bad failure)

end Second

end
end FormalProof4FHE.HasteBoots.PackedPBSDifferenceDigitNTT
