module
public import FormalProof4FHE.HasteBoots.ExecutedComparisonWorld
public import FormalProof4FHE.HasteBoots.RectangularDecodedRadix
@[expose] public section

/-! Actual reached comparison owners enforce the public radix tables on the
predecessor reconstruction's canonical final-history slots, or expose the
executed original-owner lookup failure or the single final Bad event. -/
namespace FormalProof4FHE.HasteBoots.ExecutedRectangularRadix
open OracleSpec OracleComp BinaryTree
open NativeRootMessage (Digest)
open scoped BigOperators
open PaddedMixedWidthLookupOpeningFamily MixedWidthSharedLookupPCSAlgebra
noncomputable section
variable {q e padding c row d radix : ℕ} [Fact q.Prime]
  {K Message LookupMemory ConfigHelperMemory RetainedMemory Cfg Input Response Memory CommitMemory Result : Type}
  [Field K] [Algebra (ZMod q) K] [DecidableEq Input] [DecidableEq Digest]
  {repetitions : Fin d → ℕ} {mode : Mode} {H : Cfg → ℕ}
  {tag : Root (2*d+1) (∑ i, repetitions i) → Cfg}
  {g : Geometry c row (2*d+1) (∑ i, repetitions i)}
  {symbolWidth : Root (2*d+1) (∑ i, repetitions i) → ℕ}
variable (s : PaddedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory H (2*d+2) (e+padding) row)
    (comparison : PackedPBSComparisonStage.Scheme Cfg Input Memory
      ((Fin (∑ i, repetitions i) → Digest) × RetainedMemory) Result d)
    (capacity : ∀ factor, 2^(s.code factor).suffix ≤ (s.code factor).m*(e+padding)) (radius : Fin (2*d+2) → ℕ)
    (before : PaddedReconstructionComparison.Before s)
    (outcome : PackedPBSComparisonStage.Outcome (PaddedReconstructionComparison.stage s comparison))
    (config : RectangularRequestLookup.Parameters (ZMod q) K Message LookupMemory Cfg Input Digest Memory ConfigHelperMemory
      e padding c row (2*d+1) d (fun _ => 3) (fun _ => radix*2) repetitions mode)
    (domain : ∀ root, Fin (2^H (tag root)) ↪ ZMod q)
    (lookupCapacity : ∀ root, 2^g.suffix root ≤ g.m root * symbolWidth root)
    (lookupRadius : Root (2*d+1) (∑ i, repetitions i) → ℕ)
    (sourceSymbols : ∀ source, symbolWidth (.inl source) = e+padding)
    (routing : ∀ source, RectangularLookupSourceInterpretation.squareParameters domain lookupCapacity lookupRadius sourceSymbols source =
      PaddedStageSourceInterpretation.linearParameters s capacity radius (PackedPBSComparisonReferences.linearSlot source))

/-- Literal incoming snapshots, before adaptive helper work. -/
def owners : RectangularOwnedLookupSources.Owners Input Digest H tag :=
  fun source => ⟨outcome.1.1.1 source,outcome.1.2.hash.log⟩

variable [SampleableType Digest] (dummy : Digest)
    (supported : some outcome ∈ support (PaddedReconstructionComparison.continuation s comparison dummy before))

include supported routing in
theorem owners_recorded (source : Fin (2*d+1)) :
    ((owners (tag := tag) s comparison outcome source).root = outcome.1.1.1 source) ∧
    ⟨tag (.inl source),owners (tag := tag) s comparison outcome source⟩ ∈ outcome.2.2.2.checkpoints.checkpoints := by
  constructor
  · rfl
  have sameTag : tag (.inl source) = s.tag (PackedPBSComparisonReferences.linearSlot source) :=
    congrArg RecordedPaddedSource.Parameters.tag (routing source)
  have saved := ExecutedComparisonOwners.recorded s.encoding dummy (PaddedReconstructionComparison.stage s comparison)
    before.1.1.1 before.2.1.2.memory before.2.2 outcome
    (PaddedReconstructionComparison.reached s comparison dummy before outcome supported).2 source
  simp only [ExecutedComparisonOwners.owners,PaddedReconstructionComparison.stage] at saved
  rw [←sameTag] at saved
  exact saved

variable [SampleableType (Fin (e+padding) → ZMod q)]
    [∀ factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^(s.code factor).front) (e+padding))]
    [∀ factor, SampleableType (Fin (s.code factor).queries → Fin (2^H (s.tag factor)))]
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (beforeSupported : before ∈ support (PaddedLinear.witness s dummy initial))
    (state : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (retained : CheckpointHistoryChain.Retains outcome.2.2.2 state)

include supported beforeSupported retained routing in
/-- Actual original-owner comparisons enforce all radix lookup cells on the
executed reconstruction family, without a supplied owner or source-value map. -/
theorem lookup_or_false_or_bad
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape H) state)
    (slotOrder : config.slots = RadixLookupSources.comparisonSlots)
    (publicTables : config.tables = fun limb => RadixLookupSources.publicTable q radix
      (RadixCanonicity.modulusDigit q radix limb.val))
    (full : ∀ limb, config.active limb = 2^(c+row)) :
    let reconstructionRecorded := ExecutedComparisonWorld.reconstruction_recorded s comparison capacity radius before outcome dummy supported state retained initial beforeSupported
    let factors := RecordedSourceWorld.slot (ExecutedPaddedSourceFamily.linearFamily s capacity radius before.1) state reconstructionRecorded
    (∀ cell lane, RadixCanonicity.LookupAt q radix
      (fun factor => RecordedPaddedSourceFamily.logical (RecordedSourceWorld.family state) s.encoding dummy row (factors factor)) cell lane) ∨
      RectangularOwnedRequestSources.OriginalFalse s.encoding dummy config domain lookupCapacity lookupRadius outcome ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape H) state := by
  dsimp only
  classical
  by_cases falseLookup : RectangularOwnedRequestSources.OriginalFalse s.encoding dummy config domain lookupCapacity lookupRadius outcome
  · exact Or.inr (Or.inl falseLookup)
  by_cases bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape H) state
  · exact Or.inr (Or.inr bad)
  left
  let saved := owners (tag := tag) s comparison outcome
  have recorded := owners_recorded s comparison capacity radius before outcome domain lookupCapacity lookupRadius sourceSymbols routing dummy supported
  have later : ∀ source, ⟨tag (.inl source),saved source⟩ ∈ state.checkpoints.checkpoints := by
    intro source
    exact retained _ _ (recorded source).2
  have roots : ∀ source, (saved source).root =
      (ExecutedPaddedSourceFamily.linearFamily s capacity radius before.1).roots (PackedPBSComparisonReferences.linearSlot source) := by
    intro source
    exact ExecutedComparisonWorld.root_eq s comparison capacity radius before outcome dummy supported source
  exact RectangularDecodedRadix.lookup_of_not_false s.encoding dummy config domain lookupCapacity lookupRadius sourceSymbols
    outcome saved recorded falseLookup (RecordedSourceWorld.family state)
    (RecordedSourceWorld.slot (ExecutedPaddedSourceFamily.linearFamily s capacity radius before.1) state
      (ExecutedComparisonWorld.reconstruction_recorded s comparison capacity radius before outcome dummy supported state retained initial beforeSupported))
    routing state audited (RecordedSourceWorld.recorded state) later roots bad slotOrder publicTables full

include supported beforeSupported retained routing in
/-- Reached native reconstruction and full original-owner lookup force every
actual digit to the canonical integer digit, or expose their executed risks. -/
theorem canonical_digits_or_risks
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape H) state)
    (relations : s.relations = DecompositionLinear.relations (radix : ZMod q))
    (slotOrder : config.slots = RadixLookupSources.comparisonSlots)
    (publicTables : config.tables = fun limb => RadixLookupSources.publicTable q radix
      (RadixCanonicity.modulusDigit q radix limb.val))
    (full : ∀ limb, config.active limb = 2^(c+row))
    (radixLarge : 1 < radix) (radixSmall : radix < q) (enough : q-1 < radix^d) :
    let reconstructionRecorded := ExecutedComparisonWorld.reconstruction_recorded s comparison capacity radius before outcome dummy supported state retained initial beforeSupported
    let factors := RecordedSourceWorld.slot (ExecutedPaddedSourceFamily.linearFamily s capacity radius before.1) state reconstructionRecorded
    let tables := fun factor => RecordedPaddedSourceFamily.logical (RecordedSourceWorld.family state) s.encoding dummy row (factors factor)
    (∀ cell lane digit, (tables (DecompositionLinear.digit digit) cell lane).val =
      (tables DecompositionLinear.input cell lane).val / radix^digit.val % radix) ∨
      RectangularOwnedRequestSources.OriginalFalse s.encoding dummy config domain lookupCapacity lookupRadius outcome ∨
      PaddedLinear.OriginalRisk s dummy capacity radius before ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape H) state := by
  dsimp only
  classical
  by_cases risky : PaddedLinear.OriginalRisk s dummy capacity radius before
  · exact Or.inr (Or.inr (Or.inl risky))
  by_cases bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape H) state
  · exact Or.inr (Or.inr (Or.inr bad))
  have lookup := lookup_or_false_or_bad s comparison capacity radius before outcome config domain lookupCapacity lookupRadius sourceSymbols routing
    dummy supported initial beforeSupported state retained audited slotOrder publicTables full
  dsimp only at lookup
  rcases lookup with checked | falseLookup | failed
  · have recorded := ExecutedPaddedSourceFamily.linear_recorded_witness s dummy capacity radius initial before beforeSupported
    have passes := (PaddedReconstructionComparison.reached s comparison dummy before outcome supported).1
    have linear : PackedLinear.Holds s.relations
        (PaddedLinear.originalSources s dummy capacity radius (HeterogeneousBatchOpening.snapshots H s.tag before.1)) := by
      by_contra wrong
      exact risky ⟨_,(fun factor => ⟨rfl,recorded factor⟩),wrong,passes⟩
    have original : PaddedLinear.originalSources s dummy capacity radius (HeterogeneousBatchOpening.snapshots H s.tag before.1) =
        RecordedPaddedSourceFamily.logical (ExecutedPaddedSourceFamily.linearFamily s capacity radius before.1) s.encoding dummy row := by
      funext factor
      exact ExecutedPaddedSourceFamily.linear_logical s dummy capacity radius before.1 factor
    rw [original,relations] at linear
    have same := (RecordedSourceWorld.logical_eq_or_bad (ExecutedPaddedSourceFamily.linearFamily s capacity radius before.1)
      s.encoding dummy row state audited
      (ExecutedComparisonWorld.reconstruction_recorded s comparison capacity radius before outcome dummy supported state retained initial beforeSupported)).resolve_right bad
    have reconstructed := (DecompositionLinear.holds_iff (radix : ZMod q) _).mp linear
    rw [same] at reconstructed
    left
    intro cell lane digit
    exact RadixCanonicity.digits_of_constraints radixLarge radixSmall enough _ reconstructed cell lane (checked cell lane) digit
  · exact Or.inr (Or.inl falseLookup)
  · exact (bad failed).elim

end
end FormalProof4FHE.HasteBoots.ExecutedRectangularRadix
