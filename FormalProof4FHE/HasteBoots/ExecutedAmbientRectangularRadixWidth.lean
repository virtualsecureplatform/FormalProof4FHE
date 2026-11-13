module
public import FormalProof4FHE.HasteBoots.AmbientLinear
public import FormalProof4FHE.HasteBoots.AmbientSourceDescriptor
public import FormalProof4FHE.HasteBoots.ExecutedComparisonOwners
public import FormalProof4FHE.HasteBoots.RectangularDecodedRadixWidth
public import FormalProof4FHE.HasteBoots.CheckpointHistoryChain
@[expose] public section

/-! Canonical digits of an actually executed unpadded ambient reconstruction
and its reached comparison, on one inherited shared checkpoint history. -/
namespace FormalProof4FHE.HasteBoots.ExecutedAmbientRectangularRadixWidth
open OracleSpec OracleComp BinaryTree
open NativeRootMessage (Digest)
open scoped BigOperators
open PaddedMixedWidthLookupOpeningFamily MixedWidthSharedLookupPCSAlgebra
noncomputable section
attribute [local irreducible] MonadAttach.support
variable {q e padding b c d radix front suffix m queries height : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory RetainedMemory Result : Type}
  {repetitions : Fin d → ℕ}
variable (comparison : PackedPBSComparisonStage.Scheme Cfg Input Memory
    ((Fin (∑ i, repetitions i) → Digest) × RetainedMemory) Result d)
  (s : AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) b front suffix m queries height)

/-- Construct the original reconstruction family from its physical decoders
and actual fresh prefix owners. -/
def family (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (geometry : ∀ factor, comparison.heights (s.tag factor) = height)
    (first : AmbientLinear.Prefix comparison.heights (Input := Input) (Digest := Digest)
      (CommitMemory := CommitMemory) (count := 2*d+2)) :
    RecordedPaddedSourceFamily.Family (ZMod q) Cfg Input Digest (Fin (2*d+2)) comparison.heights b where
  parameters := fun factor => AmbientSourceDescriptor.parameters (front := front) comparison.heights (s.tag factor)
    (geometry factor) s.domain capacity radius
  roots := first.1.1
  owners := AmbientCommittedBatchSafeBound.snapshots comparison.heights s.tag first
  ownerRoots := fun _ => rfl

variable [DecidableEq Digest]

/-- The literal original ambient source is this same family's logical view. -/
theorem original_logical (dummy : Digest) (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (geometry : ∀ factor, comparison.heights (s.tag factor) = height)
    (first : AmbientLinear.Prefix comparison.heights (Input := Input) (Digest := Digest)
      (CommitMemory := CommitMemory) (count := 2*d+2)) :
    AmbientLinear.originalSources comparison.heights s dummy capacity radius
      (AmbientCommittedBatchSafeBound.snapshots comparison.heights s.tag first) =
    RecordedPaddedSourceFamily.logical (family comparison s capacity radius geometry first) s.encoding dummy (front+suffix) := by
  funext factor
  exact AmbientSourceDescriptor.original s.encoding dummy comparison.heights (s.tag factor) (geometry factor)
    s.domain capacity radius rfl _

variable [DecidableEq Input] [SampleableType Digest] [SampleableType (Fin b → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]
  (dummy : Digest)
  (initial : PackedPBSComparisonStage.State comparison)
  (before : AmbientLinear.Prefix comparison.heights (Input := Input) (Digest := Digest)
      (CommitMemory := CommitMemory) (count := 2*d+2) ×
    AmbientLinear.RunResult comparison.heights (F := ZMod q) (Input := Input) (Digest := Digest)
      (Response := Response) (Memory := Memory) (count := 2*d+2) (b := b)
      (front := front) (suffix := suffix) (queries := queries) (height := height))
  (beforeSupported : before ∈ support (AmbientLinear.witness comparison.heights s dummy initial))
  (outcome : PackedPBSComparisonStage.Outcome comparison)
  (supported : outcome ∈ support (PackedPBSComparisonStage.witness s.encoding dummy comparison
    before.1.1.1 before.2.1.2.memory before.2.2))

include beforeSupported in
/-- The actual linear execution records every original family owner. -/
theorem family_recorded (capacity : 2^suffix ≤ m*b) (radius : ℕ)
    (geometry : ∀ factor, comparison.heights (s.tag factor) = height) :
    RecordedPaddedSourceFamily.Recorded (family comparison s capacity radius geometry before.1) before.2.2 := by
  intro factor
  exact AmbientLinear.fresh_recorded comparison.heights s dummy initial before beforeSupported factor

variable {K Message LookupMemory ConfigHelperMemory : Type} [Field K] [Algebra (ZMod q) K]
  {mode : Mode}
  {tag : Root (2*d+1) (∑ i, repetitions i) → Cfg}
  {g : Geometry c (front+suffix) (2*d+1) (∑ i, repetitions i)}
  {symbolWidth : Root (2*d+1) (∑ i, repetitions i) → ℕ}
  (config : RectangularRequestLookup.Parameters (ZMod q) K Message LookupMemory Cfg Input Digest Memory ConfigHelperMemory
    e padding c (front+suffix) (2*d+1) d (fun _ => 3) (fun _ => radix*2) repetitions mode)
  (domain : ∀ root, Fin (2^comparison.heights (tag root)) ↪ ZMod q)
  (lookupCapacity : ∀ root, 2^g.suffix root ≤ g.m root * symbolWidth root)
  (lookupRadius : Root (2*d+1) (∑ i, repetitions i) → ℕ)
  (sourceSymbols : ∀ source, symbolWidth (.inl source) = e+padding)
  (width : b = e+padding)

/-- Literal incoming snapshots, frozen before adaptive comparison helpers. -/
def owners : RectangularOwnedLookupSources.Owners Input Digest comparison.heights tag :=
  fun source => ⟨outcome.1.1.1 source,outcome.1.2.hash.log⟩

omit [SampleableType (Fin b → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))] in
include supported in
/-- The actual comparison records these source owners at its public tags. -/
theorem owners_recorded
    (comparisonTags : ∀ source, comparison.sourceTag source = tag (.inl source)) (source : Fin (2*d+1)) :
    (owners (tag := tag) comparison outcome source).root = outcome.1.1.1 source ∧
    ⟨tag (.inl source),owners (tag := tag) comparison outcome source⟩ ∈ outcome.2.2.2.checkpoints.checkpoints := by
  constructor
  · rfl
  have recorded := ExecutedComparisonOwners.recorded s.encoding dummy comparison before.1.1.1
    before.2.1.2.memory before.2.2 outcome supported source
  dsimp only [ExecutedComparisonOwners.owners] at recorded
  rw [comparisonTags source] at recorded
  exact recorded

variable (capacity : 2^suffix ≤ m*b) (radius : ℕ)
  (geometry : ∀ factor, comparison.heights (s.tag factor) = height)
  (state : PackedPBSComparisonStage.State comparison)
  (retained : CheckpointHistoryChain.Retains outcome.2.2.2 state)

include beforeSupported supported retained in
/-- All original reconstruction owners survive the actually reached comparison
and any later retained continuation, even on rejected comparison returns. -/
theorem family_retained :
    RecordedPaddedSourceFamily.Recorded (family comparison s capacity radius geometry before.1) state := by
  intro factor
  have recorded := family_recorded comparison s dummy initial before beforeSupported capacity radius geometry factor
  have afterComparison := PackedPBSComparisonStage.retains s.encoding dummy comparison before.1.1.1 before.2.1.2.memory
    before.2.2 (s.tag factor)
    ((family comparison s capacity radius geometry before.1).owners factor) recorded outcome supported
  exact retained _ _ afterComparison

include supported beforeSupported retained in
/-- Actual original-owner lookup enforces every public modulus-digit table on
this same reconstructed family, or exposes its existing lookup failure/Bad. -/
theorem lookup_or_false_or_bad
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape comparison.heights) state)
    (comparisonTags : ∀ source, comparison.sourceTag source = tag (.inl source))
    (routing : ∀ source, RectangularLookupSourceInterpretation.squareParameters domain lookupCapacity lookupRadius sourceSymbols source =
      (RecordedSourceWidth.family width (family comparison s capacity radius geometry before.1)).parameters (PackedPBSComparisonReferences.linearSlot source))
    (slotOrder : config.slots = RadixLookupSources.comparisonSlots)
    (publicTables : config.tables = fun limb => RadixLookupSources.publicTable q radix
      (RadixCanonicity.modulusDigit q radix limb.val))
    (full : ∀ limb, config.active limb = 2^(c+(front+suffix))) :
    (∀ cell lane, RadixCanonicity.LookupAt q radix
      (RecordedPaddedSourceFamily.logical (family comparison s capacity radius geometry before.1) s.encoding dummy (front+suffix)) cell lane) ∨
      RectangularOwnedRequestSources.OriginalFalse s.encoding dummy config domain lookupCapacity lookupRadius outcome ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape comparison.heights) state := by
  classical
  by_cases falseLookup : RectangularOwnedRequestSources.OriginalFalse s.encoding dummy config domain lookupCapacity lookupRadius outcome
  · exact Or.inr (Or.inl falseLookup)
  by_cases bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape comparison.heights) state
  · exact Or.inr (Or.inr bad)
  left
  have recorded := owners_recorded comparison s dummy before outcome supported comparisonTags
  have rootSources := PackedPBSComparisonStage.source_eq s.encoding dummy comparison before.1.1.1 before.2.1.2.memory before.2.2 outcome supported
  have roots : ∀ source, (owners (tag := tag) comparison outcome source).root =
      (family comparison s capacity radius geometry before.1).roots (PackedPBSComparisonReferences.linearSlot source) := by
    intro source
    exact congrArg (fun emission => emission.1 source) rootSources.1
  intro cell lane
  exact RectangularDecodedRadixWidth.lookup_of_not_false s.encoding dummy config domain lookupCapacity lookupRadius sourceSymbols
    outcome (owners (tag := tag) comparison outcome) recorded falseLookup (family comparison s capacity radius geometry before.1) width id
    routing state audited (family_retained comparison s dummy initial before beforeSupported outcome supported capacity radius geometry state retained)
    (fun source => retained _ _ (recorded source).2) roots bad slotOrder publicTables full cell lane

include supported beforeSupported retained in
/-- Native reconstruction, zero endpoint borrows and the reached original-owner
lookup enforce canonical integer digits of this actual original input source. -/
theorem canonical_digits_or_risks
    (audited : CheckpointExecution.Audited s.encoding dummy (AmbientMatrixSource.Shape comparison.heights) state)
    (comparisonTags : ∀ source, comparison.sourceTag source = tag (.inl source))
    (routing : ∀ source, RectangularLookupSourceInterpretation.squareParameters domain lookupCapacity lookupRadius sourceSymbols source =
      (RecordedSourceWidth.family width (family comparison s capacity radius geometry before.1)).parameters (PackedPBSComparisonReferences.linearSlot source))
    (slotOrder : config.slots = RadixLookupSources.comparisonSlots)
    (publicTables : config.tables = fun limb => RadixLookupSources.publicTable q radix
      (RadixCanonicity.modulusDigit q radix limb.val))
    (full : ∀ limb, config.active limb = 2^(c+(front+suffix)))
    (passes : AuthenticatedLinear.accepted before.2.1 = true)
    (relations : s.relations = DecompositionLinear.relations (radix : ZMod q))
    (radixLarge : 1 < radix) (radixSmall : radix < q) (enough : q-1 < radix^d) :
    (∀ cell lane digit,
      (RecordedPaddedSourceFamily.logical (family comparison s capacity radius geometry before.1) s.encoding dummy (front+suffix) (DecompositionLinear.digit digit) cell lane).val =
      (RecordedPaddedSourceFamily.logical (family comparison s capacity radius geometry before.1) s.encoding dummy (front+suffix) DecompositionLinear.input cell lane).val /
        radix^digit.val % radix) ∨
      RectangularOwnedRequestSources.OriginalFalse s.encoding dummy config domain lookupCapacity lookupRadius outcome ∨
      AmbientLinear.OriginalRisk comparison.heights s dummy capacity radius before ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape comparison.heights) state := by
  classical
  by_cases risky : AmbientLinear.OriginalRisk comparison.heights s dummy capacity radius before
  · exact Or.inr (Or.inr (Or.inl risky))
  have lookup := lookup_or_false_or_bad comparison s dummy initial before beforeSupported outcome supported config domain lookupCapacity lookupRadius sourceSymbols width capacity radius geometry state retained audited comparisonTags routing slotOrder publicTables full
  rcases lookup with checked | failedLookup | bad
  · have recorded := family_recorded comparison s dummy initial before beforeSupported capacity radius geometry
    have linear : PackedLinear.Holds s.relations
        (AmbientLinear.originalSources comparison.heights s dummy capacity radius
          (AmbientCommittedBatchSafeBound.snapshots comparison.heights s.tag before.1)) := by
      by_contra wrong
      exact risky ⟨_,(fun factor => ⟨rfl,recorded factor⟩),wrong,passes⟩
    rw [original_logical comparison s dummy capacity radius geometry before.1,relations] at linear
    have reconstructed := (DecompositionLinear.holds_iff (radix : ZMod q) _).mp linear
    left
    intro cell lane digit
    exact RadixCanonicity.digits_of_constraints radixLarge radixSmall enough _ reconstructed cell lane (checked cell lane) digit
  · exact Or.inr (Or.inl failedLookup)
  · exact Or.inr (Or.inr (Or.inr bad))

end
end FormalProof4FHE.HasteBoots.ExecutedAmbientRectangularRadixWidth
