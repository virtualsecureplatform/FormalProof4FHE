module
public import FormalProof4FHE.HasteBoots.PackedPBSSecondCanonicalDigits
public import FormalProof4FHE.HasteBoots.TransportedOriginalNTTSource
public import FormalProof4FHE.HasteBoots.PackedHadamardRows
@[expose] public section

/-! Recover the original external-product NTT execution from the complete
second-comparison PBS prefix and retain its exact source owners to final history. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSSecondDigitNTTAssociation
open OracleSpec OracleComp
open NativeRootMessage (Digest)
open scoped BigOperators
open PaddedMixedWidthLookupOpeningFamily MixedWidthSharedLookupPCSAlgebra
noncomputable section
attribute [local irreducible] MonadAttach.support
variable {q log d e padding c r k n front suffix m queries height : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory FirstMessage Message : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin (e+padding) → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) (e+padding))]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points (ZMod q) n (e+padding))] [SampleableType (Fin (e+padding) → Fin (e+padding) → ZMod q)]

variable (length : 2^c*(e+padding) = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
  (family : PackedPBSOriginalReferences.Family (2*d)) (inputs : PackedPBSDecompositionReferences.Inputs)
  (base : Fin (2*d+1) → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (e+padding) c r k front suffix m queries height)
  (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor (2*d)) (PBSHadamard.Term (2*d))
    FirstMessage Message Input Digest Cfg Response Memory CommitMemory (e+padding) n front suffix m queries height)
  (nodesEnough : 2*(e+padding) ≤ q) (radix : ℕ)
  (linearBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) (e+padding) front suffix m queries height)

variable {Helper Selection FirstRoot Data : Type}

variable {SecondResult RetainedMemory : Type} {repetitions : Fin d → ℕ}

variable (dummy : Digest)
  (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper
    (Selection × ShortCircuitSequence.Outcome FirstRoot Data Memory) d)
  (second : PackedPBSComparisonStage.Scheme Cfg Input Memory
    ((Fin (∑ i, repetitions i) → Digest) × RetainedMemory) SecondResult d)
  (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) (e+padding) front suffix m queries height)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
  (before : PackedPBSSecondComparisons.SecondBefore (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := e+padding) (c := c) (r := r) (k := k) (n := n)
    (front := front) (suffix := suffix) (queries := queries) (height := height) first)
  (outcome : PackedPBSSecondComparisons.ComparisonOutcome first second)
  (supported : (before,some outcome) ∈ support (PackedPBSSecondComparisons.witness length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy first second secondBase initial))

/-- The actual reached first-comparison result before second reconstruction. -/
def firstComparison := PackedPBSSecondCanonicalDigits.predecessor length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported in
/-- Recover that same complete first-comparison prefix support. -/
theorem firstPrefixSupported : (before.1.1,some (firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported)) ∈ support (PackedPBSFirstComparisons.witness length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy first initial) := by
  have facts := Classical.choose_spec (PackedPBSSecondReconstruction.reached_reconstruction length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy first secondBase initial before.1 (PackedPBSSecondCanonicalDigits.linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) (PackedPBSSecondCanonicalDigits.reconstructionSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported))
  dsimp only [firstComparison,PackedPBSSecondCanonicalDigits.predecessor]
  rw [← facts.1]
  exact facts.2.2.1

/-- The old first-half linear return, selected from this same prefix. -/
def firstLinearChild := Classical.choose (PackedPBSFirstComparisons.reached_comparisons length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy first initial before.1.1 (firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) (firstPrefixSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported))

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported in
/-- The exact old reconstruction prefix, without another execution. -/
theorem firstReconstructionSupported : (before.1.1.1,some (firstLinearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported)) ∈ support (PackedPBSFirstReconstruction.witness length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy initial) := by
  have facts := Classical.choose_spec (PackedPBSFirstComparisons.reached_comparisons length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy first initial before.1.1 (firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) (firstPrefixSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported))
  dsimp only [firstLinearChild]
  rw [← facts.1]
  exact facts.2.2.1

/-- The original completed coefficient/evaluation NTT loop. -/
def originalLoop := Classical.choose (PackedPBSFirstReconstruction.reached_reconstruction length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy initial before.1.1.1 (firstLinearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) (firstReconstructionSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported))

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported in
/-- Its actual Hadamard-plus-NTT support is derived from the same PBS return. -/
theorem originalSupported : (before.1.1.1.1,some (originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported)) ∈ support (PackedPBSHadamardNTT.witness length psi primitive family base hs dummy initial) := by
  have facts := Classical.choose_spec (PackedPBSFirstReconstruction.reached_reconstruction length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy initial before.1.1.1 (firstLinearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) (firstReconstructionSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported))
  dsimp only [originalLoop]
  rw [← facts.1]
  exact facts.2.2.1

/-- The first reconstruction factory at its original NTT-return memory. -/
def firstLinearScheme := PackedPBSFirstReconstruction.reconstruction family inputs nodesEnough (radix : ZMod q) linearBase false (originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported).1.memory

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported in
/-- Its real continuation starts at the old NTT loop's complete final state. -/
theorem firstLinearExecuted : (firstLinearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) ∈ support (MultiCommitmentPrefix.witness hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
    (CommittedJointMatrixOpening.requests (firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported).tag (AuthenticatedLinear.factors (2*d+2)))
    (firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported).commit (AuthenticatedLinear.continuation (firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported)) (originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported).2) :=
  (Classical.choose_spec (PackedPBSFirstReconstruction.reached_reconstruction length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy initial before.1.1.1 (firstLinearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) (firstReconstructionSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported))).2.2.2

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported in
/-- Every copied original NTT checkpoint survives the actual first linear,
geometry transition, both comparisons and second linear stage into a later
retained history. No standalone owner-retention certificate is assumed. -/
theorem originalRetained
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2.2 state) :
    CheckpointHistoryChain.Retains (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape first.heights) (originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported).2) state := by
  intro tag saved recorded
  dsimp only [CheckpointShapeTransport.state,CheckpointShapeTransport.history] at recorded
  obtain ⟨⟨oldTag,oldSaved⟩,original,same⟩ := List.mem_map.mp recorded
  cases same
  have afterLinear := SequentialStageHistory.witness_retains hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
    (CommittedJointMatrixOpening.requests (firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported).tag (AuthenticatedLinear.factors (2*d+2)))
    (firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported).commit (AuthenticatedLinear.continuation (firstLinearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported))
    (originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported).2 (firstLinearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) (firstLinearExecuted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) oldTag oldSaved original
  have sameChild : before.1.1.2 = some (firstLinearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) := (Classical.choose_spec (PackedPBSFirstComparisons.reached_comparisons length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy first initial before.1.1 (firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) (firstPrefixSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported))).1
  have afterFirst := PackedPBSFirstComparisons.comparison_retains length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy first initial before.1.1 (firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported)
    (firstPrefixSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) oldTag oldSaved (by
      simpa only [PackedPBSFirstComparisons.priorState,PackedPBSReconstructionJointBound.finalState,sameChild] using afterLinear)
  have afterSecondLinear := AmbientLinear.retains first.heights (PackedPBSSecondCanonicalDigits.linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) dummy
    (firstComparison length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported).2.2.2 (PackedPBSSecondCanonicalDigits.linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) (PackedPBSSecondCanonicalDigits.linearExecuted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) oldTag
    (CheckpointShapeTransport.checkpoint (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape first.heights) oldTag oldSaved) afterFirst
  have afterSecond := PackedPBSComparisonStage.retains hs.encoding dummy (PackedPBSSecondComparisons.sharedScheme first.heights second)
    (PackedPBSSecondCanonicalDigits.linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported).1.1.1 (PackedPBSSecondCanonicalDigits.linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported).2.1.2.memory (PackedPBSSecondCanonicalDigits.linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported).2.2 oldTag
    (CheckpointShapeTransport.checkpoint (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape first.heights) oldTag oldSaved)
    afterSecondLinear outcome (PackedPBSSecondCanonicalDigits.comparisonExecuted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported)
  exact retained _ _ afterSecond

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported in
/-- Each actual retained second-half digit coefficient row is the same
original digit polynomial as the reached reconstruction, outside the single
later Bad event. Only complete public metadata association is supplied. -/
theorem digit_row_eq_or_bad
    (capacity : 2^suffix ≤ m*(e+padding)) (radius : ℕ)
    (geometry : ∀ factor, first.heights ((PackedPBSSecondCanonicalDigits.linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported).tag factor) = height)
    (level : Fin d)
    (entry : Fin (2*d+1) × Memory × NTTSequence.Child (F := ZMod q) (Input := Input) (Digest := Digest)
      (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory)
      (b := e+padding) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height))
    (member : entry ∈ (originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported).1.results)
    (slot : entry.1 = PackedPBSDecompositionReferences.digitSlot true level)
    (nttCapacity : 2^suffix ≤ m*(e+padding)) (nttRadius : ℕ)
    (nttGeometry : ∀ side, first.heights ((base entry.1 entry.2.1).tag side) = height)
    (encoding : (base entry.1 entry.2.1).encoding = hs.encoding)
    (associated : TransportedOriginalNTTSource.parameters base entry first.heights nttCapacity nttRadius nttGeometry false =
      (PackedPBSSecondCanonicalDigits.sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported capacity radius geometry).parameters (DecompositionLinear.digit level))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2.2 state)
    (audited : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) state)
    (row : MatrixFold.Cube r) :
    PackedNTTBinding.row length (AuthenticatedNTT.sources (base entry.1 entry.2.1) dummy nttCapacity nttRadius entry.2.2.1 false) row =
      DecompositionBlindRotation.project (RecordedPaddedSourceFamily.logical (PackedPBSSecondCanonicalDigits.sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix))
        (PackedHadamardRows.address length (base entry.1 entry.2.1).dimensions row) (DecompositionLinear.digit level) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) state := by
  have roots : family.coefficients entry.1 = (PackedPBSSecondCanonicalDigits.sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported capacity radius geometry).roots (DecompositionLinear.digit level) := by
    rw [slot]
    exact ((PackedPBSSecondCanonicalDigits.source_roots length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported capacity radius geometry).2 level).symm
  have recorded := PackedPBSSecondCanonicalDigits.source_recorded length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported capacity radius geometry state retained
  exact TransportedOriginalNTTSource.row_agrees_or_bad length psi primitive family base hs dummy initial before.1.1.1.1 (originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported)
    (originalSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) entry member first.heights nttCapacity nttRadius nttGeometry encoding (PackedPBSSecondCanonicalDigits.sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported capacity radius geometry)
    (DecompositionLinear.digit level) false associated roots state (originalRetained length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported state retained) audited recorded row

variable {K LookupMessage LookupMemory ConfigHelperMemory : Type} [Field K] [Algebra (ZMod q) K]
  {lookupC : ℕ} {mode : Mode}
  {tag : Root (2*d+1) (∑ i, repetitions i) → Cfg}
  {g : Geometry lookupC (front+suffix) (2*d+1) (∑ i, repetitions i)}
  {symbolWidth : Root (2*d+1) (∑ i, repetitions i) → ℕ}
  (config : RectangularRequestLookup.Parameters (ZMod q) K LookupMessage LookupMemory Cfg Input Digest Memory ConfigHelperMemory
    e padding lookupC (front+suffix) (2*d+1) d (fun _ => 3) (fun _ => radix*2) repetitions mode)
  (domain : ∀ root, Fin (2^first.heights (tag root)) ↪ ZMod q)
  (lookupCapacity : ∀ root, 2^g.suffix root ≤ g.m root * symbolWidth root)
  (lookupRadius : Root (2*d+1) (∑ i, repetitions i) → ℕ)
  (sourceSymbols : ∀ source, symbolWidth (.inl source) = e+padding)

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported in
/-- The real retained second-half coefficient row is the canonical native
digit of the executed original input polynomial, or an existing native risk
or the same final Bad occurs. No digit-source truth is supplied as a premise. -/
theorem canonical_digit_row_or_risks
    (capacity : 2^suffix ≤ m*(e+padding)) (radius : ℕ)
    (geometry : ∀ factor, first.heights ((PackedPBSSecondCanonicalDigits.linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported).tag factor) = height)
    (level : Fin d)
    (entry : Fin (2*d+1) × Memory × NTTSequence.Child (F := ZMod q) (Input := Input) (Digest := Digest)
      (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory)
      (b := e+padding) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height))
    (member : entry ∈ (originalLoop length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported).1.results)
    (slot : entry.1 = PackedPBSDecompositionReferences.digitSlot true level)
    (nttCapacity : 2^suffix ≤ m*(e+padding)) (nttRadius : ℕ)
    (nttGeometry : ∀ side, first.heights ((base entry.1 entry.2.1).tag side) = height)
    (encoding : (base entry.1 entry.2.1).encoding = hs.encoding)
    (associated : TransportedOriginalNTTSource.parameters base entry first.heights nttCapacity nttRadius nttGeometry false =
      (PackedPBSSecondCanonicalDigits.sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported capacity radius geometry).parameters (DecompositionLinear.digit level))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2.2 state)
    (audited : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) state)
    (row : MatrixFold.Cube r)
    (comparisonTags : ∀ source, second.sourceTag source = tag (.inl source))
    (lookupRouting : ∀ source, RectangularLookupSourceInterpretation.squareParameters domain lookupCapacity lookupRadius sourceSymbols source =
      (PackedPBSSecondCanonicalDigits.sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported capacity radius geometry).parameters (PackedPBSComparisonReferences.linearSlot source))
    (slotOrder : config.slots = RadixLookupSources.comparisonSlots)
    (publicTables : config.tables = fun limb => RadixLookupSources.publicTable q radix
      (RadixCanonicity.modulusDigit q radix limb.val))
    (full : ∀ limb, config.active limb = 2^(lookupC+(front+suffix)))
    (radixLarge : 1 < radix) (radixSmall : radix < q) (enough : q-1 < radix^d)
    (bits : ℕ) (radix_eq : radix = 2^bits) :
    PackedNTTBinding.row length (AuthenticatedNTT.sources (base entry.1 entry.2.1) dummy nttCapacity nttRadius entry.2.2.1 false) row =
      NativeBlindRotation.digit bits level (DecompositionBlindRotation.project (RecordedPaddedSourceFamily.logical (PackedPBSSecondCanonicalDigits.sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix)) (PackedHadamardRows.address length (base entry.1 entry.2.1).dimensions row) DecompositionLinear.input) ∨
      RectangularOwnedRequestSources.OriginalFalse hs.encoding dummy config domain lookupCapacity lookupRadius outcome ∨
      AmbientLinear.OriginalRisk first.heights (PackedPBSSecondCanonicalDigits.linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) dummy capacity radius
        (PackedPBSSecondCanonicalDigits.linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) state := by
  rcases digit_row_eq_or_bad length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported capacity radius geometry level entry member slot nttCapacity nttRadius nttGeometry encoding associated
      state retained audited row with sameRow | bad
  · rcases PackedPBSSecondCanonicalDigits.canonical_polynomials_or_risks length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported config domain lookupCapacity lookupRadius sourceSymbols
      capacity radius geometry comparisonTags lookupRouting slotOrder publicTables full state retained audited radixLarge radixSmall enough
      bits radix_eq (PackedHadamardRows.address length (base entry.1 entry.2.1).dimensions row) with canonical | failedLookup | failedLinear | bad
    · exact Or.inl (sameRow.trans (canonical level))
    · exact Or.inr (Or.inl failedLookup)
    · exact Or.inr (Or.inr (Or.inl failedLinear))
    · exact Or.inr (Or.inr (Or.inr bad))
  · exact Or.inr (Or.inr (Or.inr bad))

end
end FormalProof4FHE.HasteBoots.PackedPBSSecondDigitNTTAssociation
