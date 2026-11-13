module
public import FormalProof4FHE.HasteBoots.ExecutedAmbientRectangularRadix
public import FormalProof4FHE.HasteBoots.PackedPBSSecondComparisons
public import FormalProof4FHE.HasteBoots.DecompositionBlindRotation
@[expose] public section

/-! Canonical second-half decomposition digits from the actually reached
reconstruction and comparison in the retained complete PBS prefix. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSSecondCanonicalDigits
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

/-- The reconstruction whose acceptance enabled this exact comparison. -/
def linearChild := Classical.choose (PackedPBSSecondComparisons.reached_comparisons length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy first second secondBase initial before outcome supported)

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported in
/-- Recover the actual retained second-reconstruction prefix. -/
theorem reconstructionSupported : (before.1,some (linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported)) ∈ support (PackedPBSSecondReconstruction.witness length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy first secondBase initial) := by
  have reached := Classical.choose_spec (PackedPBSSecondComparisons.reached_comparisons length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy first second secondBase initial before outcome supported)
  dsimp only [linearChild]
  rw [← reached.1]
  exact reached.2.2.1

/-- The reached first-comparison predecessor and actual opening memory. -/
def predecessor := Classical.choose (PackedPBSSecondReconstruction.reached_reconstruction length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy first secondBase initial before.1 (linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) (reconstructionSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported))

/-- Native reconstruction at that same actual predecessor memory. -/
def linearScheme := PackedPBSSecondReconstruction.reconstruction family inputs hs nodesEnough (radix : ZMod q) secondBase
  (predecessor length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported).2.2.1.2.memory

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported in
/-- Its supported execution starts from the actual inherited predecessor state. -/
theorem linearExecuted : (linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) ∈ support (AmbientLinear.witness first.heights (linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) dummy
    (predecessor length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported).2.2.2) :=
  (Classical.choose_spec (PackedPBSSecondReconstruction.reached_reconstruction length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy first secondBase initial before.1 (linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) (reconstructionSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported))).2.2.2

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported in
/-- Acceptance is the actual native reconstruction/opening gate. -/
theorem linearAccepted : AuthenticatedLinear.accepted (linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported).2.1 = true :=
  (Classical.choose_spec (PackedPBSSecondComparisons.reached_comparisons length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy first second secondBase initial before outcome supported)).2.1

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported in
/-- Comparison support uses the retained registry, returned memory and state. -/
theorem comparisonExecuted : outcome ∈ support (PackedPBSComparisonStage.witness hs.encoding dummy (PackedPBSSecondComparisons.sharedScheme first.heights second)
    (linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported).1.1.1 (linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported).2.1.2.memory (linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported).2.2) :=
  (Classical.choose_spec (PackedPBSSecondComparisons.reached_comparisons length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy first second secondBase initial before outcome supported)).2.2.2

/-- Construct the original executed digit/borrow family with its real decoder. -/
def sourceFamily (capacity : 2^suffix ≤ m*(e+padding)) (radius : ℕ)
    (geometry : ∀ factor, first.heights ((linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported).tag factor) = height) :=
  ExecutedAmbientRectangularRadix.family (PackedPBSSecondComparisons.sharedScheme first.heights second) (linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) capacity radius geometry (linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported).1

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported in
/-- The constructed family uses the original second-half input and the same
original digit roots later consumed by the external-product NTT calls. -/
theorem source_roots (capacity : 2^suffix ≤ m*(e+padding)) (radius : ℕ)
    (geometry : ∀ factor, first.heights ((linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported).tag factor) = height) :
    (sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported capacity radius geometry).roots DecompositionLinear.input = inputs.roots true ∧
      ∀ level, (sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported capacity radius geometry).roots (DecompositionLinear.digit level) =
        family.coefficients (PackedPBSDecompositionReferences.digitSlot true level) :=
  PackedPBSSecondReconstruction.roots length psi primitive family inputs base hs nodesEnough (radix : ZMod q) linearBase dummy first secondBase initial before.1 (linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) (reconstructionSupported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported)

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported in
/-- Every constructed original digit/borrow owner remains recorded in a later
retained final history; no separate source-availability receipt is supplied. -/
theorem source_recorded (capacity : 2^suffix ≤ m*(e+padding)) (radius : ℕ)
    (geometry : ∀ factor, first.heights ((linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported).tag factor) = height)
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2.2 state) :
    RecordedPaddedSourceFamily.Recorded (sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported capacity radius geometry) state :=
  ExecutedAmbientRectangularRadix.family_retained (PackedPBSSecondComparisons.sharedScheme first.heights second) (linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) dummy
    (predecessor length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported).2.2.2 (linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) (linearExecuted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) outcome (comparisonExecuted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported)
    capacity radius geometry state retained

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
/-- The actual accepted second reconstruction and reached rectangular lookup
force all original second-half digits to be canonical, outside their existing
native risk events and the one later retained-history exception. -/
theorem canonical_digits_or_risks (capacity : 2^suffix ≤ m*(e+padding)) (radius : ℕ)
    (geometry : ∀ factor, first.heights ((linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported).tag factor) = height)
    (comparisonTags : ∀ source, second.sourceTag source = tag (.inl source))
    (routing : ∀ source, RectangularLookupSourceInterpretation.squareParameters domain lookupCapacity lookupRadius sourceSymbols source =
      (sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported capacity radius geometry).parameters (PackedPBSComparisonReferences.linearSlot source))
    (slotOrder : config.slots = RadixLookupSources.comparisonSlots)
    (publicTables : config.tables = fun limb => RadixLookupSources.publicTable q radix
      (RadixCanonicity.modulusDigit q radix limb.val))
    (full : ∀ limb, config.active limb = 2^(lookupC+(front+suffix)))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2.2 state)
    (audited : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) state)
    (radixLarge : 1 < radix) (radixSmall : radix < q) (enough : q-1 < radix^d) :
    (∀ cell lane digit,
      (RecordedPaddedSourceFamily.logical (sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix) (DecompositionLinear.digit digit) cell lane).val =
      (RecordedPaddedSourceFamily.logical (sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix) DecompositionLinear.input cell lane).val /
        radix^digit.val % radix) ∨
      RectangularOwnedRequestSources.OriginalFalse hs.encoding dummy config domain lookupCapacity lookupRadius outcome ∨
      AmbientLinear.OriginalRisk first.heights (linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) dummy capacity radius (linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) state := by
  exact ExecutedAmbientRectangularRadix.canonical_digits_or_risks (PackedPBSSecondComparisons.sharedScheme first.heights second) (linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) dummy (predecessor length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported).2.2.2 (linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) (linearExecuted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) outcome (comparisonExecuted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) config domain lookupCapacity lookupRadius sourceSymbols capacity radius geometry state retained
    audited comparisonTags routing slotOrder publicTables full (linearAccepted length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) rfl radixLarge radixSmall enough

include length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported in
/-- The original executed second-half digit polynomial equals the native
coefficient-domain digit of its original input polynomial. No canonical-digit
source equality is supplied; it follows from the reached native checks. -/
theorem canonical_polynomials_or_risks (capacity : 2^suffix ≤ m*(e+padding)) (radius : ℕ)
    (geometry : ∀ factor, first.heights ((linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported).tag factor) = height)
    (comparisonTags : ∀ source, second.sourceTag source = tag (.inl source))
    (routing : ∀ source, RectangularLookupSourceInterpretation.squareParameters domain lookupCapacity lookupRadius sourceSymbols source =
      (sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported capacity radius geometry).parameters (PackedPBSComparisonReferences.linearSlot source))
    (slotOrder : config.slots = RadixLookupSources.comparisonSlots)
    (publicTables : config.tables = fun limb => RadixLookupSources.publicTable q radix
      (RadixCanonicity.modulusDigit q radix limb.val))
    (full : ∀ limb, config.active limb = 2^(lookupC+(front+suffix)))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (retained : CheckpointHistoryChain.Retains outcome.2.2.2 state)
    (audited : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) state)
    (radixLarge : 1 < radix) (radixSmall : radix < q) (enough : q-1 < radix^d)
    (bits : ℕ) (radix_eq : radix = 2^bits)
    (address : Fin (2^log) → MatrixFold.Cube (front+suffix) × Fin (e+padding)) :
    (∀ digit, DecompositionBlindRotation.project (RecordedPaddedSourceFamily.logical (sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix)) address (DecompositionLinear.digit digit) =
      NativeBlindRotation.digit bits digit (DecompositionBlindRotation.project (RecordedPaddedSourceFamily.logical (sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix)) address DecompositionLinear.input)) ∨
      RectangularOwnedRequestSources.OriginalFalse hs.encoding dummy config domain lookupCapacity lookupRadius outcome ∨
      AmbientLinear.OriginalRisk first.heights (linearScheme length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) dummy capacity radius (linearChild length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) state := by
  rcases canonical_digits_or_risks length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported config domain lookupCapacity lookupRadius sourceSymbols capacity radius geometry
      comparisonTags routing slotOrder publicTables full state retained audited radixLarge radixSmall enough with canonical | failedLookup | failedLinear | bad
  · left
    intro digit
    funext index
    let inputValue := (RecordedPaddedSourceFamily.logical (sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix)) DecompositionLinear.input (address index).1 (address index).2
    let digitValue := (RecordedPaddedSourceFamily.logical (sourceFamily length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial before outcome supported capacity radius geometry) hs.encoding dummy (front+suffix)) (DecompositionLinear.digit digit) (address index).1 (address index).2
    have same := congrArg (fun value : ℕ => (value : ZMod q)) (canonical (address index).1 (address index).2 digit)
    change (digitValue.val : ZMod q) = ((inputValue.val / radix^digit.val % radix : ℕ) : ZMod q) at same
    rw [ZMod.natCast_zmod_val,radix_eq] at same
    exact same
  · exact Or.inr (Or.inl failedLookup)
  · exact Or.inr (Or.inr (Or.inl failedLinear))
  · exact Or.inr (Or.inr (Or.inr bad))

end
end FormalProof4FHE.HasteBoots.PackedPBSSecondCanonicalDigits
