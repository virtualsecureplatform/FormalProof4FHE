module
public import FormalProof4FHE.HasteBoots.RectangularOwnedLookupConditional
public import FormalProof4FHE.HasteBoots.PackedPBSComparisonStage
@[expose] public section

/-! The concrete private request comparator used after reconstruction.
Per-request tables/repetitions and per-context heights are retained. -/
open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open scoped Classical BigOperators
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening
open FormalProof4FHE.HasteBoots.PaddedMixedWidthLookupOpeningFamily
open FormalProof4FHE.HasteBoots.MixedWidthSharedLookupPCSAlgebra
namespace FormalProof4FHE.HasteBoots.RectangularPBSComparisonStage
open NativeRootMessage (Digest)
noncomputable section
variable {F K Message Memory Cfg Input Response SourceMemory HelperMemory Result : Type}
  [Field F] [Field K] [Algebra F K] [DecidableEq F] [DecidableEq Input] [DecidableEq Digest]
  {d padding helperPadding c row digits requests : ℕ} {widths sizes repetitions : Fin requests → ℕ} {mode : Mode}
  {heights : Cfg → ℕ} {tag : Root (2*digits+1) (∑ i, repetitions i) → Cfg} {g : Geometry c row (2*digits+1) (∑ i, repetitions i)} {symbolWidth : Root (2*digits+1) (∑ i, repetitions i) → ℕ}
  [SampleableType Digest] [Fintype K] [DecidableEq K] [SampleableType K]

variable [SampleableType (Fin 1 → K)] [SampleableType (Fin (c + row) → K)]
  [∀ root, SampleableType (TestMatrix F (2 ^ (layout g root).front) (packedWidth (d + padding) (d + helperPadding) root))]
  [∀ root, SampleableType (Fin (layout g root).queries → Fin (2 ^ heights (tag root)))]
    [Fintype F]
  [∀ root, SampleableType ((Fin (2 ^ (layout g root).front) × Fin (packedWidth (d + padding) (d + helperPadding) root)) → F)]

/-- Compile the actual request sampler, adaptive helpers and grouped PCS
continuation into the post-reconstruction comparison call. -/
def scheme
    (enc : MerkleOracle.Encoding Input Digest (List F))
    (config : RectangularRequestLookup.Parameters F K Message Memory Cfg Input Digest SourceMemory HelperMemory
      d padding c row (2*digits+1) requests widths sizes repetitions mode)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (fallback : Packet F K (d + padding) (2*digits+1) (c + row) (∑ i, repetitions i))
    (behavior : RectangularStagedSharedLookup.Emission (2*digits+1) (∑ i, repetitions i) Digest SourceMemory (RequestLookupPairMiddle.Memory K HelperMemory repetitions) →
      RectangularSharedLookupPCS.Selection F K Memory (d + padding) (2*digits+1) (∑ i, repetitions i) (c + row) →
      (root : Root (2*digits+1) (∑ i, repetitions i)) → Protocol F Input Digest Cfg Response Memory (packedWidth (d + padding) (d + helperPadding)) symbolWidth heights tag (layout g) root)
    (pairEnough : ∀ index, sizes index + 1 < Fintype.card K)
    (build : RectangularStagedSharedLookup.SourceEmission (2*digits+1) Digest SourceMemory → RequestLookupPairs.Vector K repetitions →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (RectangularStagedSharedLookup.HelperEmission (∑ i, repetitions i) Digest HelperMemory)) :=
  ({
    heights := heights
    sourceTag := fun source => tag (.inl source)
    helperRequests := RectangularStagedOpening.helperRequests tag (List.finRange (∑ i, repetitions i))
    helperCommit := fun first => RequestLookupPairMiddle.program config.tables pairEnough (build first)
    next := RectangularStagedSharedLookup.continuation (helperPadding := helperPadding) enc (RectangularRequestLookup.toParameters config) p small domain fallback behavior
  } : PackedPBSComparisonStage.Scheme Cfg Input SourceMemory _ _ digits)

/-- Original tuple failures selected after the actual run are bounded by
private pair, common algebra and grouped original-root PCS errors. -/
theorem false_acceptance_safe_bound [∀ root : Root (2*digits+1) (∑ i, repetitions i), NeZero (symbolWidth root)] [∀ root, NeZero (layout g root).m]
    (enc : MerkleOracle.Encoding Input Digest (List F)) (dummy : Digest)
    (config : RectangularRequestLookup.Parameters F K Message Memory Cfg Input Digest SourceMemory HelperMemory
      d padding c row (2*digits+1) requests widths sizes repetitions mode)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ F)
    (enough : ∀ root, g.m root ≤ Fintype.card (Fin (2 ^ heights (tag root))))
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * symbolWidth root) (radius : Root (2*digits+1) (∑ i, repetitions i) → ℕ)
    (fallback : Packet F K (d + padding) (2*digits+1) (c + row) (∑ i, repetitions i))
    (behavior : RectangularStagedSharedLookup.Emission (2*digits+1) (∑ i, repetitions i) Digest SourceMemory (RequestLookupPairMiddle.Memory K HelperMemory repetitions) →
      RectangularSharedLookupPCS.Selection F K Memory (d + padding) (2*digits+1) (∑ i, repetitions i) (c + row) →
      (root : Root (2*digits+1) (∑ i, repetitions i)) → Protocol F Input Digest Cfg Response Memory (packedWidth (d + padding) (d + helperPadding)) symbolWidth heights tag (layout g) root)
    (roots : Fin (2*digits+2) → Digest) (memory : SourceMemory)
    (pairEnough : ∀ index, sizes index + 1 < Fintype.card K) (lookupSmall : ∀ index, config.active index < p)
    (build : RectangularStagedSharedLookup.SourceEmission (2*digits+1) Digest SourceMemory → RequestLookupPairs.Vector K repetitions →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (RectangularStagedSharedLookup.HelperEmission (∑ i, repetitions i) Digest HelperMemory))
    (distanceLarge : ∀ root, radius root < Fintype.card F)
    (distance : ∀ root, 3*radius root < Code.minDist (BlockCode.code (domain root) (g.m root) (symbolWidth root) :
      Set (Fin (2^heights (tag root)) → Fin (symbolWidth root) → F)))
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (fun cfg => Skeleton.perfect (heights cfg)))
    (audited : CheckpointExecution.Audited enc dummy (fun cfg => Skeleton.perfect (heights cfg)) initial) :
    let experiment := PackedPBSComparisonStage.witness enc dummy
      (scheme enc config p small domain fallback behavior pairEnough build) roots memory initial
    Pr{let outcome ← experiment}[
      (RectangularOwnedRequestSources.OriginalFalse enc dummy config domain capacity radius outcome ∧
        outcome.2.2.1.2.accepted = true) ∧ ¬CheckpointCollision.Bad (fun cfg => Skeleton.perfect (heights cfg)) outcome.2.2.2] ≤
      RequestLookupPairMiddle.errorBudget (Fintype.card K) widths sizes config.active repetitions +
      ((error K mode (c + row) + RectangularStagedSharedLookup.pcsError (d := d) (padding := padding) (helperPadding := helperPadding) (g := g) (symbolWidth := symbolWidth) domain radius)) := by
  exact RectangularOwnedLookupConditional.false_acceptance_safe_bound (helperPadding := helperPadding) enc dummy config p small
    domain enough capacity radius fallback behavior (pure (PackedPBSComparisonStage.sources roots memory))
    pairEnough lookupSmall build distanceLarge distance initial audited

end
end FormalProof4FHE.HasteBoots.RectangularPBSComparisonStage
