module
public import FormalProof4FHE.HasteBoots.TransportedOriginalNTTSource
public import FormalProof4FHE.HasteBoots.PackedPBSFirstCanonicalDigits
public import FormalProof4FHE.HasteBoots.PackedHadamardRows
public import FormalProof4FHE.HasteBoots.PackedPBSFirstComparisons
public import FormalProof4FHE.HasteBoots.DecompositionBlindRotation
@[expose] public section

/-! Associate actual first-half canonical digits with retained original NTT rows.
The original fixed-height reconstruction is never replayed or reset. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSFirstDigitNTTAssociation
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

variable {Result RetainedMemory : Type} {repetitions : Fin d → ℕ}

variable (dummy : Digest)
  (comparison : PackedPBSComparisonStage.Scheme Cfg Input Memory
    ((Fin (∑ i, repetitions i) → Digest) × RetainedMemory) Result d)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
  (before : PackedPBSFirstComparisons.Outcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := e+padding) (c := c) (r := r) (k := k) (n := n)
    (d := d) (front := front) (suffix := suffix) (queries := queries) (height := height))
  (outcome : PackedPBSComparisonStage.Outcome comparison)
  (supported : (before,some outcome) ∈ support (PackedPBSFirstComparisons.witness length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy comparison initial))

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported in
/-- The original NTT loop is taken from the same reached reconstruction. -/
theorem originalSupported : (before.1.1,some (PackedPBSFirstCanonicalDigits.predecessor length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported)) ∈ support (PackedPBSHadamardNTT.witness length psi primitive family base hs dummy initial) := by
  have facts := Classical.choose_spec (PackedPBSFirstReconstruction.reached_reconstruction length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy initial before.1 (PackedPBSFirstCanonicalDigits.linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported) (PackedPBSFirstCanonicalDigits.reconstructionSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported))
  dsimp only [PackedPBSFirstCanonicalDigits.predecessor]
  rw [← facts.1]
  exact facts.2.2.1

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported in
/-- Copied NTT owners survive the actual reconstruction and comparison. -/
theorem originalRetained
    (encoding : (PackedPBSFirstCanonicalDigits.linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).encoding = hs.encoding)
    (state : PackedPBSComparisonStage.State comparison)
    (retained : CheckpointHistoryChain.Retains outcome.2.2.2 state) :
    CheckpointHistoryChain.Retains (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape comparison.heights) (PackedPBSFirstCanonicalDigits.predecessor length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).2) state := by
  intro tag saved recorded
  dsimp only [CheckpointShapeTransport.state,CheckpointShapeTransport.history] at recorded
  obtain ⟨⟨oldTag,oldSaved⟩,original,same⟩ := List.mem_map.mp recorded
  cases same
  have afterLinear := SequentialStageHistory.witness_retains (PackedPBSFirstCanonicalDigits.linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).encoding dummy (RecordedSourceCoherence.Shape Cfg height)
    (CommittedJointMatrixOpening.requests (PackedPBSFirstCanonicalDigits.linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).tag (AuthenticatedLinear.factors (2*d+2)))
    (PackedPBSFirstCanonicalDigits.linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).commit (AuthenticatedLinear.continuation (PackedPBSFirstCanonicalDigits.linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported))
    (PackedPBSFirstCanonicalDigits.predecessor length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).2 (PackedPBSFirstCanonicalDigits.linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported) (PackedPBSFirstCanonicalDigits.linearExecuted length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported encoding) oldTag oldSaved original
  have sameChild : before.2 = some (PackedPBSFirstCanonicalDigits.linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported) := (Classical.choose_spec (PackedPBSFirstComparisons.reached_comparisons length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy comparison initial before outcome supported)).1
  have afterComparison := PackedPBSFirstComparisons.comparison_retains length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy comparison initial before outcome supported oldTag oldSaved (by
    simpa only [PackedPBSFirstComparisons.priorState,PackedPBSReconstructionJointBound.finalState,sameChild] using afterLinear)
  exact retained _ _ afterComparison

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported in
/-- Each actual retained first-half digit coefficient row is the same
original digit polynomial as the reached reconstruction, outside the single
later Bad event. Only complete public metadata association is supplied. -/
theorem digit_row_eq_or_bad
    (capacity : 2^suffix ≤ m*(e+padding)) (radius : ℕ)
    (geometry : ∀ factor, comparison.heights ((PackedPBSFirstCanonicalDigits.linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).tag factor) = height)
    (linearEncoding : (PackedPBSFirstCanonicalDigits.linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).encoding = hs.encoding)
    (level : Fin d)
    (entry : Fin (2*d+1) × Memory × NTTSequence.Child (F := ZMod q) (Input := Input) (Digest := Digest)
      (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory)
      (b := e+padding) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height))
    (member : entry ∈ (PackedPBSFirstCanonicalDigits.predecessor length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).1.results)
    (slot : entry.1 = PackedPBSDecompositionReferences.digitSlot false level)
    (nttCapacity : 2^suffix ≤ m*(e+padding)) (nttRadius : ℕ)
    (nttGeometry : ∀ side, comparison.heights ((base entry.1 entry.2.1).tag side) = height)
    (encoding : (base entry.1 entry.2.1).encoding = hs.encoding)
    (associated : TransportedOriginalNTTSource.parameters base entry comparison.heights nttCapacity nttRadius nttGeometry false =
      (PackedPBSFirstCanonicalDigits.sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported capacity radius geometry).parameters (DecompositionLinear.digit level))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape comparison.heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2.2 state)
    (audited : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape comparison.heights) state)
    (row : MatrixFold.Cube r) :
    PackedNTTBinding.row length (AuthenticatedNTT.sources (base entry.1 entry.2.1) dummy nttCapacity nttRadius entry.2.2.1 false) row =
      DecompositionBlindRotation.project (RecordedPaddedSourceFamily.logical (PackedPBSFirstCanonicalDigits.sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix))
        (PackedHadamardRows.address length (base entry.1 entry.2.1).dimensions row) (DecompositionLinear.digit level) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape comparison.heights) state := by
  have roots : family.coefficients entry.1 = (PackedPBSFirstCanonicalDigits.sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported capacity radius geometry).roots (DecompositionLinear.digit level) := by
    rw [slot]
    exact ((PackedPBSFirstCanonicalDigits.source_roots length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported capacity radius geometry).2 level).symm
  have recorded := PackedPBSFirstCanonicalDigits.source_recorded length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported capacity radius geometry linearEncoding state retained
  exact TransportedOriginalNTTSource.row_agrees_or_bad length psi primitive family base hs dummy initial before.1.1 (PackedPBSFirstCanonicalDigits.predecessor length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported)
    (originalSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported) entry member comparison.heights nttCapacity nttRadius nttGeometry encoding (PackedPBSFirstCanonicalDigits.sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported capacity radius geometry)
    (DecompositionLinear.digit level) false associated roots state (originalRetained length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported linearEncoding state retained) audited recorded row

variable {K LookupMessage LookupMemory ConfigHelperMemory : Type} [Field K] [Algebra (ZMod q) K]
  {lookupC : ℕ} {mode : Mode}
  {tag : Root (2*d+1) (∑ i, repetitions i) → Cfg}
  {g : Geometry lookupC (front+suffix) (2*d+1) (∑ i, repetitions i)}
  {symbolWidth : Root (2*d+1) (∑ i, repetitions i) → ℕ}
  (config : RectangularRequestLookup.Parameters (ZMod q) K LookupMessage LookupMemory Cfg Input Digest Memory ConfigHelperMemory
    e padding lookupC (front+suffix) (2*d+1) d (fun _ => 3) (fun _ => radix*2) repetitions mode)
  (domain : ∀ root, Fin (2^comparison.heights (tag root)) ↪ ZMod q)
  (lookupCapacity : ∀ root, 2^g.suffix root ≤ g.m root * symbolWidth root)
  (lookupRadius : Root (2*d+1) (∑ i, repetitions i) → ℕ)
  (sourceSymbols : ∀ source, symbolWidth (.inl source) = e+padding)

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported in
/-- The real retained first-half coefficient row is the canonical native
digit of the executed original input polynomial, or an existing native risk
or the same final Bad occurs. No digit-source truth is supplied as a premise. -/
theorem canonical_digit_row_or_risks
    (capacity : 2^suffix ≤ m*(e+padding)) (radius : ℕ)
    (geometry : ∀ factor, comparison.heights ((PackedPBSFirstCanonicalDigits.linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).tag factor) = height)
    (linearEncoding : (PackedPBSFirstCanonicalDigits.linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).encoding = hs.encoding)
    (level : Fin d)
    (entry : Fin (2*d+1) × Memory × NTTSequence.Child (F := ZMod q) (Input := Input) (Digest := Digest)
      (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory)
      (b := e+padding) (c := c) (r := r) (k := k) (front := front) (queries := queries) (height := height))
    (member : entry ∈ (PackedPBSFirstCanonicalDigits.predecessor length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).1.results)
    (slot : entry.1 = PackedPBSDecompositionReferences.digitSlot false level)
    (nttCapacity : 2^suffix ≤ m*(e+padding)) (nttRadius : ℕ)
    (nttGeometry : ∀ side, comparison.heights ((base entry.1 entry.2.1).tag side) = height)
    (encoding : (base entry.1 entry.2.1).encoding = hs.encoding)
    (associated : TransportedOriginalNTTSource.parameters base entry comparison.heights nttCapacity nttRadius nttGeometry false =
      (PackedPBSFirstCanonicalDigits.sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported capacity radius geometry).parameters (DecompositionLinear.digit level))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape comparison.heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2.2 state)
    (audited : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape comparison.heights) state)
    (row : MatrixFold.Cube r)
    (comparisonTags : ∀ source, comparison.sourceTag source = tag (.inl source))
    (lookupRouting : ∀ source, RectangularLookupSourceInterpretation.squareParameters domain lookupCapacity lookupRadius sourceSymbols source =
      (PackedPBSFirstCanonicalDigits.sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported capacity radius geometry).parameters (PackedPBSComparisonReferences.linearSlot source))
    (slotOrder : config.slots = RadixLookupSources.comparisonSlots)
    (publicTables : config.tables = fun limb => RadixLookupSources.publicTable q radix
      (RadixCanonicity.modulusDigit q radix limb.val))
    (full : ∀ limb, config.active limb = 2^(lookupC+(front+suffix)))
    (radixLarge : 1 < radix) (radixSmall : radix < q) (enough : q-1 < radix^d)
    (bits : ℕ) (radix_eq : radix = 2^bits) :
    PackedNTTBinding.row length (AuthenticatedNTT.sources (base entry.1 entry.2.1) dummy nttCapacity nttRadius entry.2.2.1 false) row =
      NativeBlindRotation.digit bits level (DecompositionBlindRotation.project (RecordedPaddedSourceFamily.logical (PackedPBSFirstCanonicalDigits.sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix)) (PackedHadamardRows.address length (base entry.1 entry.2.1).dimensions row) DecompositionLinear.input) ∨
      RectangularOwnedRequestSources.OriginalFalse hs.encoding dummy config domain lookupCapacity lookupRadius outcome ∨
      OwnedLinearSoundness.OriginalRisk (PackedPBSFirstCanonicalDigits.linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported) dummy capacity radius
        (PackedPBSFirstCanonicalDigits.linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape comparison.heights) state := by
  rcases digit_row_eq_or_bad length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported capacity radius geometry linearEncoding level entry member slot nttCapacity nttRadius nttGeometry encoding associated
      state retained audited row with sameRow | bad
  · rcases PackedPBSFirstCanonicalDigits.canonical_polynomials_or_risks length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported config domain lookupCapacity lookupRadius sourceSymbols
      capacity radius geometry linearEncoding comparisonTags lookupRouting slotOrder publicTables full state retained audited radixLarge radixSmall enough
      bits radix_eq (PackedHadamardRows.address length (base entry.1 entry.2.1).dimensions row) with canonical | failedLookup | failedLinear | bad
    · exact Or.inl (sameRow.trans (canonical level))
    · exact Or.inr (Or.inl failedLookup)
    · exact Or.inr (Or.inr (Or.inl failedLinear))
    · exact Or.inr (Or.inr (Or.inr bad))
  · exact Or.inr (Or.inr (Or.inr bad))

end
end FormalProof4FHE.HasteBoots.PackedPBSFirstDigitNTTAssociation
