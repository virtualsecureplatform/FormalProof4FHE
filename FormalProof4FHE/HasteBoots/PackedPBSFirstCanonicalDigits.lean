module
public import FormalProof4FHE.HasteBoots.ExecutedTransportedRectangularRadix
public import FormalProof4FHE.HasteBoots.PackedPBSFirstComparisons
public import FormalProof4FHE.HasteBoots.DecompositionBlindRotation
@[expose] public section

/-! Canonical first-half digits through the actual PBS geometry transition.
The original fixed-height reconstruction is never replayed or reset. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSFirstCanonicalDigits
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

/-- The old-phase reconstruction whose acceptance enabled this comparison. -/
def linearChild := Classical.choose (PackedPBSFirstComparisons.reached_comparisons length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy comparison initial before outcome supported)

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported in
/-- Recover the exact old-phase reconstruction prefix support. -/
theorem reconstructionSupported : (before.1,some (linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported)) ∈ support (PackedPBSFirstReconstruction.witness length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy initial) := by
  have reached := Classical.choose_spec (PackedPBSFirstComparisons.reached_comparisons length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy comparison initial before outcome supported)
  dsimp only [linearChild]
  rw [← reached.1]
  exact reached.2.2.1

/-- The actual completed original NTT loop and its returned private memory. -/
def predecessor := Classical.choose (PackedPBSFirstReconstruction.reached_reconstruction length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy initial before.1 (linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported) (reconstructionSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported))

/-- The original configured linear scheme at that actual memory. -/
def linearScheme := PackedPBSFirstReconstruction.reconstruction family inputs nodesEnough (radix : ZMod q) linearBase false
  (predecessor length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).1.memory

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported in
/-- Actual inherited linear support. Encoding association is explicit rather
than changing the original factory or assuming the run began from empty. -/
theorem linearExecuted (encoding : (linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).encoding = hs.encoding) :
    (linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported) ∈ support (MultiCommitmentPrefix.witness (linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).encoding dummy (RecordedSourceCoherence.Shape Cfg height)
      (CommittedJointMatrixOpening.requests (linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).tag (AuthenticatedLinear.factors (2*d+2)))
      (linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).commit (AuthenticatedLinear.continuation (linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported)) (predecessor length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).2) := by
  rw [encoding]
  exact (Classical.choose_spec (PackedPBSFirstReconstruction.reached_reconstruction length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy initial before.1 (linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported) (reconstructionSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported))).2.2.2

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported in
/-- Acceptance is the actual native reconstruction/opening gate. -/
theorem linearAccepted : AuthenticatedLinear.accepted (linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).2.1 = true :=
  (Classical.choose_spec (PackedPBSFirstComparisons.reached_comparisons length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy comparison initial before outcome supported)).2.1

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported in
/-- The comparison uses the literal transported old-state return, preserving
its cache, failure bit, root owners and complete saved logs. -/
theorem comparisonExecuted (encoding : (linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).encoding = hs.encoding) :
    outcome ∈ support (PackedPBSComparisonStage.witness (linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).encoding dummy comparison
      (linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).1.1.1 (linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).2.1.2.memory (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape comparison.heights) (linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).2.2)) := by
  rw [encoding]
  exact (Classical.choose_spec (PackedPBSFirstComparisons.reached_comparisons length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy comparison initial before outcome supported)).2.2.2

/-- Construct the original first-half family using copied root/log owners. -/
def sourceFamily (capacity : 2^suffix ≤ m*(e+padding)) (radius : ℕ)
    (geometry : ∀ factor, comparison.heights ((linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).tag factor) = height) :=
  ExecutedTransportedRectangularRadix.family comparison (linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported) capacity radius geometry (linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).1

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported in
/-- The family retains the original first-half input and digit roots. -/
theorem source_roots (capacity : 2^suffix ≤ m*(e+padding)) (radius : ℕ)
    (geometry : ∀ factor, comparison.heights ((linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).tag factor) = height) :
    (sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported capacity radius geometry).roots DecompositionLinear.input = inputs.roots false ∧
      ∀ level, (sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported capacity radius geometry).roots (DecompositionLinear.digit level) =
        family.coefficients (PackedPBSDecompositionReferences.digitSlot false level) :=
  PackedPBSFirstReconstruction.reconstruction_roots length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy initial before.1 (linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported) (reconstructionSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported)

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported in
/-- Copied original owners remain recorded through the actual comparison and
any later retained history, without a new availability certificate. -/
theorem source_recorded (capacity : 2^suffix ≤ m*(e+padding)) (radius : ℕ)
    (geometry : ∀ factor, comparison.heights ((linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).tag factor) = height)
    (encoding : (linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).encoding = hs.encoding)
    (state : PackedPBSComparisonStage.State comparison)
    (retained : CheckpointHistoryChain.Retains outcome.2.2.2 state) :
    RecordedPaddedSourceFamily.Recorded (sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported capacity radius geometry) state :=
  ExecutedTransportedRectangularRadix.family_retained comparison (linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported) dummy (predecessor length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).2
    (linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported) (linearExecuted length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported encoding) outcome (comparisonExecuted length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported encoding)
    capacity radius geometry state retained

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
/-- The original first-half reconstruction and reached comparison enforce
canonical digits through the actual geometry change. No reconstructed-input
truth, lookup membership or source-value certificate is supplied. -/
theorem canonical_digits_or_risks (capacity : 2^suffix ≤ m*(e+padding)) (radius : ℕ)
    (geometry : ∀ factor, comparison.heights ((linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).tag factor) = height)
    (encoding : (linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).encoding = hs.encoding)
    (comparisonTags : ∀ source, comparison.sourceTag source = tag (.inl source))
    (routing : ∀ source, RectangularLookupSourceInterpretation.squareParameters domain lookupCapacity lookupRadius sourceSymbols source =
      (sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported capacity radius geometry).parameters (PackedPBSComparisonReferences.linearSlot source))
    (slotOrder : config.slots = RadixLookupSources.comparisonSlots)
    (publicTables : config.tables = fun limb => RadixLookupSources.publicTable q radix
      (RadixCanonicity.modulusDigit q radix limb.val))
    (full : ∀ limb, config.active limb = 2^(lookupC+(front+suffix)))
    (state : PackedPBSComparisonStage.State comparison)
    (retained : CheckpointHistoryChain.Retains outcome.2.2.2 state)
    (audited : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape comparison.heights) state)
    (radixLarge : 1 < radix) (radixSmall : radix < q) (enough : q-1 < radix^d) :
    (∀ cell lane digit, ((RecordedPaddedSourceFamily.logical (sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix)) (DecompositionLinear.digit digit) cell lane).val =
      ((RecordedPaddedSourceFamily.logical (sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix)) DecompositionLinear.input cell lane).val / radix^digit.val % radix) ∨
      RectangularOwnedRequestSources.OriginalFalse hs.encoding dummy config domain lookupCapacity lookupRadius outcome ∨
      OwnedLinearSoundness.OriginalRisk (linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported) dummy capacity radius (linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape comparison.heights) state := by
  have originalAudit : CheckpointExecution.Audited (linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).encoding dummy
      (AmbientMatrixSource.Shape comparison.heights) state := by
    rw [encoding]
    exact audited
  have result := ExecutedTransportedRectangularRadix.canonical_digits_or_risks comparison (linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported) dummy (predecessor length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).2 (linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported) (linearExecuted length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported encoding) outcome (comparisonExecuted length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported encoding) config domain lookupCapacity lookupRadius sourceSymbols capacity radius geometry state retained
    originalAudit comparisonTags routing slotOrder publicTables full (linearAccepted length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported) rfl radixLarge radixSmall enough
  rw [encoding] at result
  exact result

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported in
/-- Every actual first-half digit polynomial is the native digit of the
original input polynomial at those addresses, outside the same existing risks. -/
theorem canonical_polynomials_or_risks (capacity : 2^suffix ≤ m*(e+padding)) (radius : ℕ)
    (geometry : ∀ factor, comparison.heights ((linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).tag factor) = height)
    (encoding : (linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported).encoding = hs.encoding)
    (comparisonTags : ∀ source, comparison.sourceTag source = tag (.inl source))
    (routing : ∀ source, RectangularLookupSourceInterpretation.squareParameters domain lookupCapacity lookupRadius sourceSymbols source =
      (sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported capacity radius geometry).parameters (PackedPBSComparisonReferences.linearSlot source))
    (slotOrder : config.slots = RadixLookupSources.comparisonSlots)
    (publicTables : config.tables = fun limb => RadixLookupSources.publicTable q radix
      (RadixCanonicity.modulusDigit q radix limb.val))
    (full : ∀ limb, config.active limb = 2^(lookupC+(front+suffix)))
    (state : PackedPBSComparisonStage.State comparison)
    (retained : CheckpointHistoryChain.Retains outcome.2.2.2 state)
    (audited : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape comparison.heights) state)
    (radixLarge : 1 < radix) (radixSmall : radix < q) (enough : q-1 < radix^d)
    (bits : ℕ) (radix_eq : radix = 2^bits)
    (address : Fin (2^log) → MatrixFold.Cube (front+suffix) × Fin (e+padding)) :
    (∀ digit, DecompositionBlindRotation.project (RecordedPaddedSourceFamily.logical (sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix)) address (DecompositionLinear.digit digit) =
      NativeBlindRotation.digit bits digit (DecompositionBlindRotation.project (RecordedPaddedSourceFamily.logical (sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix)) address DecompositionLinear.input)) ∨
      RectangularOwnedRequestSources.OriginalFalse hs.encoding dummy config domain lookupCapacity lookupRadius outcome ∨
      OwnedLinearSoundness.OriginalRisk (linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported) dummy capacity radius (linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape comparison.heights) state := by
  rcases canonical_digits_or_risks length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported config domain lookupCapacity lookupRadius sourceSymbols capacity radius geometry encoding
      comparisonTags routing slotOrder publicTables full state retained audited radixLarge radixSmall enough with canonical | failedLookup | failedLinear | bad
  · left
    intro digit
    funext index
    let inputValue := (RecordedPaddedSourceFamily.logical (sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix)) DecompositionLinear.input (address index).1 (address index).2
    let digitValue := (RecordedPaddedSourceFamily.logical (sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparison initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix)) (DecompositionLinear.digit digit) (address index).1 (address index).2
    have same := congrArg (fun value : ℕ => (value : ZMod q)) (canonical (address index).1 (address index).2 digit)
    change (digitValue.val : ZMod q) = ((inputValue.val / radix^digit.val % radix : ℕ) : ZMod q) at same
    rw [ZMod.natCast_zmod_val,radix_eq] at same
    exact same
  · exact Or.inr (Or.inl failedLookup)
  · exact Or.inr (Or.inr (Or.inl failedLinear))
  · exact Or.inr (Or.inr (Or.inr bad))

end
end FormalProof4FHE.HasteBoots.PackedPBSFirstCanonicalDigits
