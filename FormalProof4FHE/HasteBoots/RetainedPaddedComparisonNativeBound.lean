module
public import FormalProof4FHE.HasteBoots.RetainedPaddedComparisonProbability
@[expose] public section

/-! The actual shared request verifier discharges the local comparison bound.
Averaging uses supported predecessor audits and the computed reconstruction
gate. There is no supplied child-security, replay or source-truth premise. -/
namespace FormalProof4FHE.HasteBoots.RetainedPaddedComparisonNativeBound
open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open NativeRootMessage (Digest)
open scoped BigOperators
open PaddedMixedWidthLookupOpeningFamily MixedWidthSharedLookupPCSAlgebra
open RetainedPaddedComparison
noncomputable section
variable {F K Before Cfg Input Response Memory CommitMemory Message HelperMemory ComparisonResponse : Type}
  [Field F] [Field K] [Algebra F K] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {H : Cfg → ℕ} {digits width logicalN e padding helperPadding c row requests : ℕ}
  {widths sizes repetitions : Fin requests → ℕ} {mode : Mode}
  {tag : Root (2*digits+1) (∑ i, repetitions i) → Cfg}
  {g : Geometry c row (2*digits+1) (∑ i, repetitions i)}
  {L : Root (2*digits+1) (∑ i, repetitions i) → Type}
  [SampleableType Digest] [Fintype K] [DecidableEq K] [SampleableType K]
  [SampleableType (Fin 1 → K)] [SampleableType (Fin (c+row) → K)]
  [∀ root, SampleableType (InteractiveAuthenticatedOpening.TestMatrix F (2^(layout g root).front) (packedWidth (e+padding) (e+helperPadding) root))]
  [∀ root, SampleableType (Fin (layout g root).queries → Fin (2^H (tag root)))]
  [∀ root, Field (L root)] [∀ root, Algebra F (L root)] [Fintype F]
  [∀ root, Fintype (L root)] [∀ root, DecidableEq (L root)]
  [∀ root, SampleableType ((Fin (2^(layout g root).front) × Fin (packedWidth (e+padding) (e+helperPadding) root)) → L root)]

/-- Native private request-pair, scalar and per-root PCS errors apply to the
actual selected comparison; all previous rejects/skips retain zero child risk. -/
theorem safe_bound
    [∀ root : Root (2*digits+1) (∑ i, repetitions i), NeZero (packedWidth (e+padding) (e+helperPadding) root)]
    [∀ root, NeZero (layout g root).m]
    (base : Memory → PaddedLinear.Scheme F Input Digest Cfg Response Memory CommitMemory H (2*digits+2) width logicalN)
    (get : Before → Option (Reconstruction base))
    (state : Before → CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape H))
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (sameEncoding : ∀ memory, (base memory).encoding = enc)
    (sameTags : ∀ memory source, (base memory).tag (PackedPBSComparisonReferences.linearSlot source) = tag (.inl source))
    (config : Memory → PaddedMixedWidthRequestSharedLookup.Parameters F K Message Memory Cfg Input Digest Memory HelperMemory
      e padding c row (2*digits+1) requests widths sizes repetitions mode)
    (p : ℕ) [CharP K p] (small : 2*1 ≤ p)
    (domain : ∀ root, Fin (2^H (tag root)) ↪ F)
    (analysisBasis : ∀ root, Module.Basis (Fin (packedWidth (e+padding) (e+helperPadding) root)) F (L root))
    (enough : ∀ root, g.m root ≤ Fintype.card (Fin (2^H (tag root))))
    (capacity : ∀ root, 2^g.suffix root ≤ g.m root * packedWidth (e+padding) (e+helperPadding) root)
    (radius : Root (2*digits+1) (∑ i, repetitions i) → ℕ)
    (fallback : Packet F K (e+padding) (2*digits+1) (c+row) (∑ i, repetitions i))
    (behavior : Memory → PaddedMixedWidthStagedSharedLookup.Emission (2*digits+1) (∑ i, repetitions i) Digest Memory
        (RequestLookupPairMiddle.Memory K HelperMemory repetitions) →
      PaddedMixedWidthSharedLookupPCS.Selection F K Memory (e+padding) (2*digits+1) (∑ i, repetitions i) (c+row) →
      (root : Root (2*digits+1) (∑ i, repetitions i)) →
      VariableWidthBatchOpening.Protocol F Input Digest Cfg ComparisonResponse Memory (packedWidth (e+padding) (e+helperPadding)) H tag (layout g) root)
    (pairEnough : ∀ index, sizes index+1 < Fintype.card K)
    (lookupSmall : ∀ memory index, (config memory).active index < p)
    (build : Memory → PaddedMixedWidthStagedSharedLookup.SourceEmission (2*digits+1) Digest Memory →
      RequestLookupPairs.Vector K repetitions → OracleComp (SharedSequence.Shared Cfg Input Digest)
        (PaddedMixedWidthStagedSharedLookup.HelperEmission (∑ i, repetitions i) Digest HelperMemory))
    (distance : ∀ root, (radius root : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := L root) (domain root)) (g.m root) :
        Set (Fin (2^H (tag root)) → L root)) : ℚ≥0)/3)
    (epsilon : ENNReal)
    (calibrated : ∀ memory,
      RequestLookupPairMiddle.errorBudget (Fintype.card K) widths sizes (config memory).active repetitions +
        (error K mode (c+row) + PaddedMixedWidthStagedSharedLookup.pcsError
          (d := e) (padding := padding) (helperPadding := helperPadding) (g := g) L domain radius) ≤ epsilon)
    (prior : ProbComp Before)
    (audited : ∀ before ∈ support prior, CheckpointExecution.Audited enc dummy (AmbientMatrixSource.Shape H) (state before)) :
    let comparison := fun memory => PaddedPBSRequestComparisonStage.scheme enc (config memory) p small domain fallback
      (behavior memory) pairEnough (build memory)
    Pr{let outcome ← (prior >>= finish base comparison get state dummy)}[
      ∃ result, outcome.2 = some result ∧
        (PaddedMixedWidthOwnedRequestSources.OriginalFalse enc dummy (config result.1.1) domain capacity radius result.2 ∧
          result.2.2.2.1.2.accepted = true) ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape H) (finalState base comparison state outcome)] ≤ epsilon := by
  dsimp only
  apply RetainedPaddedComparisonProbability.selected_safe_bound base
    (fun memory => PaddedPBSRequestComparisonStage.scheme enc (config memory) p small domain fallback
      (behavior memory) pairEnough (build memory)) get state dummy prior
    (fun result => PaddedMixedWidthOwnedRequestSources.OriginalFalse enc dummy (config result.1.1) domain capacity radius result.2 ∧
      result.2.2.2.1.2.accepted = true) epsilon
  intro before supported reconstructed selected
  have native := PaddedPBSRequestComparisonStage.false_acceptance_safe_bound analysisBasis enc dummy
    (config reconstructed.1) p small domain enough capacity radius fallback (behavior reconstructed.1)
    reconstructed.2.1.1.1 reconstructed.2.2.1.2.memory pairEnough (lookupSmall reconstructed.1)
    (build reconstructed.1) distance (state before) (audited before supported)
  have actual : child base
      (fun memory => PaddedPBSRequestComparisonStage.scheme enc (config memory) p small domain fallback
        (behavior memory) pairEnough (build memory)) dummy reconstructed (state before) =
      PackedPBSComparisonStage.witness enc dummy
        (PaddedPBSRequestComparisonStage.scheme enc (config reconstructed.1) p small domain fallback
          (behavior reconstructed.1) pairEnough (build reconstructed.1))
        reconstructed.2.1.1.1 reconstructed.2.2.1.2.memory (state before) := by
    simp only [child,PaddedReconstructionComparison.stage,PaddedPBSRequestComparisonStage.scheme,sameEncoding]
    simp only [PackedPBSComparisonStage.witness]
    simp_rw [sameTags]
  rw [actual]
  exact native.trans (calibrated reconstructed.1)

end
end FormalProof4FHE.HasteBoots.RetainedPaddedComparisonNativeBound
