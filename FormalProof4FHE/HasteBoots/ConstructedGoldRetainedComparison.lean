module
public import FormalProof4FHE.HasteBoots.RetainedRectangularComparisonBound
public import FormalProof4FHE.HasteBoots.RetainedPaddedComparisonJointBound
public import FormalProof4FHE.HasteBoots.ConstructedGoldPrivateLookupConditional
@[expose] public section

/-! The actual shared request verifier discharges the local comparison bound.
Averaging uses supported predecessor audits and the computed reconstruction
gate. There is no supplied child-security, replay or source-truth premise. -/
namespace FormalProof4FHE.HasteBoots.ConstructedGoldRetainedComparison
open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open NativeRootMessage (Digest)
open scoped BigOperators
open PaddedMixedWidthLookupOpeningFamily MixedWidthSharedLookupPCSAlgebra
open RetainedPaddedComparison
noncomputable section
variable {K Before Input Response Memory CommitMemory Message HelperMemory ComparisonResponse : Type}
  [Field K] [Algebra NativeFields.Goldilocks K] [DecidableEq Input] [DecidableEq Digest]
  {digits row requests : ℕ}
  {widths sizes repetitions : Fin requests → ℕ} {mode : Mode}
  (ctx : ConstructedGoldLookupProtocol.Context row (2*digits+1) (∑ i, repetitions i))
  [SampleableType Digest] [Fintype K] [DecidableEq K] [SampleableType K]
  [SampleableType (Fin 1 → K)] [SampleableType (Fin (2+row) → K)]
  [∀ root, SampleableType (InteractiveAuthenticatedOpening.TestMatrix NativeFields.Goldilocks (2^(layout (ConstructedGoldLookupProtocol.geometry ctx) root).front) (packedWidth (3+1) (3+0) root))]
  [∀ root, SampleableType (Fin (layout (ConstructedGoldLookupProtocol.geometry ctx) root).queries → Fin (2^ConstructedGoldSourceDescriptor.heights ((ConstructedGoldLookupProtocol.tag ctx) root)))]


  [∀ root, SampleableType ((Fin (2^(layout (ConstructedGoldLookupProtocol.geometry ctx) root).front) × Fin (packedWidth (3+1) (3+0) root)) → NativeFields.Goldilocks)]


/-- The actual reached comparison has a native-derived uniform rate. -/
theorem safe_bound
    (base : Memory → PaddedLinear.Scheme NativeFields.Goldilocks Input Digest ConstructedGoldSourceDescriptor.Configuration Response Memory CommitMemory ConstructedGoldSourceDescriptor.heights (2*digits+2) 4 row)
    (get : Before → Option (Reconstruction base))
    (state : Before → CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape ConstructedGoldSourceDescriptor.heights))
    (enc : MerkleOracle.Encoding Input Digest (List NativeFields.Goldilocks)) (dummy : Digest)
    (sameEncoding : ∀ memory, (base memory).encoding = enc)
    (sameTags : ∀ memory source, (base memory).tag (PackedPBSComparisonReferences.linearSlot source) = (ConstructedGoldLookupProtocol.tag ctx) (.inl source))
    (config : Memory → RectangularRequestLookup.Parameters NativeFields.Goldilocks K Message Memory ConstructedGoldSourceDescriptor.Configuration Input Digest Memory HelperMemory
      3 1 2 row (2*digits+1) requests widths sizes repetitions mode)
    (p : ℕ) [CharP K p] (small : 2*1 ≤ p)
    (radius : Root (2*digits+1) (∑ i, repetitions i) → ℕ)
    (fallback : Packet NativeFields.Goldilocks K (3+1) (2*digits+1) (2+row) (∑ i, repetitions i))
    (behavior : Memory → RectangularStagedSharedLookup.Emission (2*digits+1) (∑ i, repetitions i) Digest Memory
        (RequestLookupPairMiddle.Memory K HelperMemory repetitions) →
      RectangularSharedLookupPCS.Selection NativeFields.Goldilocks K Memory (3+1) (2*digits+1) (∑ i, repetitions i) (2+row) →
      (root : Root (2*digits+1) (∑ i, repetitions i)) →
      RectangularVariableWidthOpening.Protocol NativeFields.Goldilocks Input Digest ConstructedGoldSourceDescriptor.Configuration ComparisonResponse Memory (packedWidth (3+1) (3+0)) (fun _ => 4) ConstructedGoldSourceDescriptor.heights (ConstructedGoldLookupProtocol.tag ctx) (layout (ConstructedGoldLookupProtocol.geometry ctx)) root)
    (pairEnough : ∀ index, sizes index+1 < Fintype.card K)
    (lookupSmall : ∀ memory index, (config memory).active index < p)
    (build : Memory → RectangularStagedSharedLookup.SourceEmission (2*digits+1) Digest Memory →
      RequestLookupPairs.Vector K repetitions → OracleComp (SharedSequence.Shared ConstructedGoldSourceDescriptor.Configuration Input Digest)
        (RectangularStagedSharedLookup.HelperEmission (∑ i, repetitions i) Digest HelperMemory))
    (distance : ∀ root, 3*radius root < Code.minDist ((BlockCode.code ((ConstructedGoldLookupProtocol.domain ctx) root) ((ConstructedGoldLookupProtocol.geometry ctx).m root) ((fun _ => 4) root)).carrier :
      Set (Fin (2^ConstructedGoldSourceDescriptor.heights ((ConstructedGoldLookupProtocol.tag ctx) root)) → Fin ((fun _ => 4) root) → NativeFields.Goldilocks)))
    (prior : ProbComp Before)
    (audited : ∀ before ∈ support prior, CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape ConstructedGoldSourceDescriptor.heights) (state before)) :
    let comparison := fun memory => RectangularPBSComparisonStage.scheme (d := 3) (padding := 1) (helperPadding := 0) (c := 2) (row := row)
      (g := ConstructedGoldLookupProtocol.geometry ctx) (heights := ConstructedGoldSourceDescriptor.heights)
      (tag := ConstructedGoldLookupProtocol.tag ctx) (symbolWidth := fun _ => 4) enc (config memory) p small (ConstructedGoldLookupProtocol.domain ctx) fallback
      (behavior memory) pairEnough (build memory)
    Pr{let outcome ← (prior >>= finish base comparison get state dummy)}[
      ∃ result, outcome.2 = some result ∧
        (RectangularOwnedRequestSources.OriginalFalse enc dummy (config result.1.1) (ConstructedGoldLookupProtocol.domain ctx) (ConstructedGoldLookupProtocol.capacity ctx) radius result.2 ∧
          result.2.2.2.1.2.accepted = true) ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape ConstructedGoldSourceDescriptor.heights) (finalState base comparison state outcome)] ≤
      RequestLookupPairMiddle.errorBudget (Fintype.card K) widths sizes (fun _ => 2^(2+row)) repetitions +
      (error K mode (2+row) + RectangularStagedSharedLookup.pcsError
        (d := 3) (padding := 1) (helperPadding := 0) (g := (ConstructedGoldLookupProtocol.geometry ctx)) (symbolWidth := (fun _ => 4)) (ConstructedGoldLookupProtocol.domain ctx) radius) := by
  let : ∀ root : Root (2*digits+1) (∑ i, repetitions i), NeZero (layout (ConstructedGoldLookupProtocol.geometry ctx) root).m :=
    fun root => ⟨Nat.ne_of_gt (ConstructedGoldStagedLookup.degree_positive ctx root)⟩
  have large : ∀ root, radius root < Fintype.card NativeFields.Goldilocks :=
    fun root => ConstructedGoldPrivateLookupConditional.radius_large_of_distance ctx root (radius root) (distance root)
  exact RetainedRectangularComparisonBound.uniform_safe_bound
    (e := 3) (padding := 1) (helperPadding := 0) (c := 2) (row := row) (width := 4) (logicalN := row)
    (g := ConstructedGoldLookupProtocol.geometry ctx) (H := ConstructedGoldSourceDescriptor.heights)
    (tag := ConstructedGoldLookupProtocol.tag ctx) (symbolWidth := fun _ => 4)
    base get state enc dummy sameEncoding sameTags config p small (ConstructedGoldLookupProtocol.domain ctx)
    (ConstructedGoldStagedLookup.enough ctx) (ConstructedGoldLookupProtocol.capacity ctx) radius fallback behavior
    pairEnough lookupSmall build large distance prior audited

/-- Predecessor and reached comparison risks share the final history exclusion.
The comparison rate is derived here; composition adds no hash charge. -/
theorem safe_joint_bound
    (base : Memory → PaddedLinear.Scheme NativeFields.Goldilocks Input Digest ConstructedGoldSourceDescriptor.Configuration Response Memory CommitMemory ConstructedGoldSourceDescriptor.heights (2*digits+2) 4 row)
    (get : Before → Option (Reconstruction base))
    (state : Before → CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape ConstructedGoldSourceDescriptor.heights))
    (enc : MerkleOracle.Encoding Input Digest (List NativeFields.Goldilocks)) (dummy : Digest)
    (sameEncoding : ∀ memory, (base memory).encoding = enc)
    (sameTags : ∀ memory source, (base memory).tag (PackedPBSComparisonReferences.linearSlot source) = (ConstructedGoldLookupProtocol.tag ctx) (.inl source))
    (config : Memory → RectangularRequestLookup.Parameters NativeFields.Goldilocks K Message Memory ConstructedGoldSourceDescriptor.Configuration Input Digest Memory HelperMemory
      3 1 2 row (2*digits+1) requests widths sizes repetitions mode)
    (p : ℕ) [CharP K p] (small : 2*1 ≤ p)
    (radius : Root (2*digits+1) (∑ i, repetitions i) → ℕ)
    (fallback : Packet NativeFields.Goldilocks K (3+1) (2*digits+1) (2+row) (∑ i, repetitions i))
    (behavior : Memory → RectangularStagedSharedLookup.Emission (2*digits+1) (∑ i, repetitions i) Digest Memory
        (RequestLookupPairMiddle.Memory K HelperMemory repetitions) →
      RectangularSharedLookupPCS.Selection NativeFields.Goldilocks K Memory (3+1) (2*digits+1) (∑ i, repetitions i) (2+row) →
      (root : Root (2*digits+1) (∑ i, repetitions i)) →
      RectangularVariableWidthOpening.Protocol NativeFields.Goldilocks Input Digest ConstructedGoldSourceDescriptor.Configuration ComparisonResponse Memory (packedWidth (3+1) (3+0)) (fun _ => 4) ConstructedGoldSourceDescriptor.heights (ConstructedGoldLookupProtocol.tag ctx) (layout (ConstructedGoldLookupProtocol.geometry ctx)) root)
    (pairEnough : ∀ index, sizes index+1 < Fintype.card K)
    (lookupSmall : ∀ memory index, (config memory).active index < p)
    (build : Memory → RectangularStagedSharedLookup.SourceEmission (2*digits+1) Digest Memory →
      RequestLookupPairs.Vector K repetitions → OracleComp (SharedSequence.Shared ConstructedGoldSourceDescriptor.Configuration Input Digest)
        (RectangularStagedSharedLookup.HelperEmission (∑ i, repetitions i) Digest HelperMemory))
    (distance : ∀ root, 3*radius root < Code.minDist ((BlockCode.code ((ConstructedGoldLookupProtocol.domain ctx) root) ((ConstructedGoldLookupProtocol.geometry ctx).m root) ((fun _ => 4) root)).carrier :
      Set (Fin (2^ConstructedGoldSourceDescriptor.heights ((ConstructedGoldLookupProtocol.tag ctx) root)) → Fin ((fun _ => 4) root) → NativeFields.Goldilocks)))
    (prior : ProbComp Before)
    (audited : ∀ before ∈ support prior, CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape ConstructedGoldSourceDescriptor.heights) (state before))
    (earlier : Before → Prop) (earlierRate : ENNReal)
    (earlierBound : Pr{let before ← prior}[
      earlier before ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape ConstructedGoldSourceDescriptor.heights) (state before)] ≤ earlierRate) :
    let comparison := fun memory => RectangularPBSComparisonStage.scheme (d := 3) (padding := 1) (helperPadding := 0) (c := 2) (row := row)
      (g := ConstructedGoldLookupProtocol.geometry ctx) (heights := ConstructedGoldSourceDescriptor.heights)
      (tag := ConstructedGoldLookupProtocol.tag ctx) (symbolWidth := fun _ => 4) enc (config memory) p small (ConstructedGoldLookupProtocol.domain ctx) fallback
      (behavior memory) pairEnough (build memory)
    Pr{let outcome ← (prior >>= finish base comparison get state dummy)}[
    (earlier outcome.1 ∨ ∃ result, outcome.2 = some result ∧
      (RectangularOwnedRequestSources.OriginalFalse enc dummy (config result.1.1)
        (ConstructedGoldLookupProtocol.domain ctx) (ConstructedGoldLookupProtocol.capacity ctx) radius result.2 ∧
        result.2.2.2.1.2.accepted = true)) ∧
      ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape ConstructedGoldSourceDescriptor.heights)
        (finalState base comparison state outcome)] ≤
      earlierRate + (RequestLookupPairMiddle.errorBudget (Fintype.card K) widths sizes (fun _ => 2^(2+row)) repetitions +
      (error K mode (2+row) + RectangularStagedSharedLookup.pcsError
        (d := 3) (padding := 1) (helperPadding := 0) (g := (ConstructedGoldLookupProtocol.geometry ctx)) (symbolWidth := (fun _ => 4)) (ConstructedGoldLookupProtocol.domain ctx) radius)) := by
  dsimp only
  have comparisonBound := safe_bound ctx base get state enc dummy sameEncoding sameTags config p small radius fallback
    behavior pairEnough lookupSmall build distance prior audited
  dsimp only at comparisonBound
  exact RetainedPaddedComparisonJointBound.safe_joint_bound base
    (fun memory => RectangularPBSComparisonStage.scheme (d := 3) (padding := 1) (helperPadding := 0) (c := 2) (row := row)
      (g := ConstructedGoldLookupProtocol.geometry ctx) (heights := ConstructedGoldSourceDescriptor.heights)
      (tag := ConstructedGoldLookupProtocol.tag ctx) (symbolWidth := fun _ => 4) enc (config memory) p small (ConstructedGoldLookupProtocol.domain ctx) fallback
      (behavior memory) pairEnough (build memory)) get state dummy prior earlier
    (fun result => RectangularOwnedRequestSources.OriginalFalse enc dummy (config result.1.1)
      (ConstructedGoldLookupProtocol.domain ctx) (ConstructedGoldLookupProtocol.capacity ctx) radius result.2 ∧
      result.2.2.2.1.2.accepted = true) earlierRate _ earlierBound comparisonBound

end
end FormalProof4FHE.HasteBoots.ConstructedGoldRetainedComparison
