module
public import FormalProof4FHE.HasteBoots.PackedPBSSecondComparisonProbability
public import FormalProof4FHE.HasteBoots.PackedPBSRequestComparisonStage
@[expose] public section

/-! The second comparison has the derived request-specific private-pair, common
algebra and original grouped PCS rate on the complete reached prefix. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSSecondComparisonSoundness
open BinaryTree Matrix MerkleTreeMultiExtractability
open scoped Classical BigOperators
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.VariableWidthBatchOpening
open FormalProof4FHE.HasteBoots.MixedWidthLookupOpeningFamily
open FormalProof4FHE.HasteBoots.MixedWidthSharedLookupPCSAlgebra
open PackedPBSSecondComparisons (sharedScheme beforeState finalState)
open OracleSpec OracleComp
open NativeRootMessage (Digest)
open PackedPBSHadamardNTT (HadamardOutcome LoopOutcome)
open PackedPBSFirstReconstruction (Before LinearOutcome beforeState reconstruction)
noncomputable section
variable {q log d b c r k n front suffix m queries height : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory FirstMessage Message : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin b → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points (ZMod q) n b)] [SampleableType (Fin b → Fin b → ZMod q)]

variable (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
  (family : PackedPBSOriginalReferences.Family (2*d)) (inputs : PackedPBSDecompositionReferences.Inputs)
  (base : Fin (2*d+1) → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    b c r k front suffix m queries height)
  (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor (2*d)) (PBSHadamard.Term (2*d))
    FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
  (nodesEnough : 2*b ≤ q) (radix : ZMod q)
  (linearBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) b front suffix m queries height)


variable {Helper FirstSelection FirstRoot FirstData : Type}
  (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper
    (FirstSelection × ShortCircuitSequence.Outcome FirstRoot FirstData Memory) d)
  (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) b front suffix m queries height)

variable {K LookupMessage LookupMemory LookupResponse HelperMemory : Type}
  [Field K] [Algebra (ZMod q) K] [Fintype K] [DecidableEq K] [SampleableType K]
  {e padding helperPadding lookupC lookupRow requests : ℕ}
  {widths sizes repetitions : Fin requests → ℕ} {mode : Mode}
  {tag : MixedWidthLookupOpeningFamily.Root (2*d+1) (∑ i, repetitions i) → Cfg}
  {g : Geometry lookupC lookupRow (2*d+1) (∑ i, repetitions i)}
  {L : MixedWidthLookupOpeningFamily.Root (2*d+1) (∑ i, repetitions i) → Type}
  [SampleableType (Fin 1 → K)] [SampleableType (Fin (lookupC+lookupRow) → K)]
  [∀ root, SampleableType (TestMatrix (ZMod q) (2 ^ (layout g root).front) (packedWidth (e+padding) (e+helperPadding) root))]
  [∀ root, SampleableType (Fin (layout g root).queries → Fin (2 ^ first.heights (tag root)))]
  [∀ root, Field (L root)] [∀ root, Algebra (ZMod q) (L root)]
  [∀ root, Fintype (L root)] [∀ root, DecidableEq (L root)]
  [∀ root, SampleableType ((Fin (2 ^ (layout g root).front) × Fin (packedWidth (e+padding) (e+helperPadding) root)) → L root)]

/-- Accepted false original tuples in the actual second-comparison call
have the derived pair, common algebra and original PCS rate, without a hash charge. -/
theorem original_false_comparison_bound [∀ root : MixedWidthLookupOpeningFamily.Root (2*d+1) (∑ i, repetitions i), NeZero (packedWidth (e + padding) (e + helperPadding) root)] [∀ root, NeZero (layout g root).m]
    (analysisBasis : ∀ root, Module.Basis (Fin (packedWidth (e + padding) (e + helperPadding) root)) (ZMod q) (L root))
    (dummy : Digest)
    (config : MixedWidthRequestSharedLookup.Parameters (ZMod q) K LookupMessage LookupMemory Cfg Input Digest Memory HelperMemory
      e padding lookupC lookupRow (2*d+1) requests widths sizes repetitions mode)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (domain : ∀ root, Fin (2 ^ first.heights (tag root)) ↪ (ZMod q))
    (enough : ∀ root, g.m root ≤ Fintype.card (Fin (2 ^ first.heights (tag root))))
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * packedWidth (e + padding) (e + helperPadding) root) (radius : MixedWidthLookupOpeningFamily.Root (2*d+1) (∑ i, repetitions i) → ℕ)
    (fallback : Packet (ZMod q) K (e + padding) (2*d+1) (lookupC + lookupRow) (∑ i, repetitions i))
    (behavior : MixedWidthStagedSharedLookup.Emission (2*d+1) (∑ i, repetitions i) Digest Memory (RequestLookupPairMiddle.Memory K HelperMemory repetitions) →
      MixedWidthSharedLookupPCS.Selection (ZMod q) K LookupMemory (e + padding) (2*d+1) (∑ i, repetitions i) (lookupC + lookupRow) →
      (root : MixedWidthLookupOpeningFamily.Root (2*d+1) (∑ i, repetitions i)) → Protocol (ZMod q) Input Digest Cfg LookupResponse LookupMemory (packedWidth (e + padding) (e + helperPadding)) first.heights tag (layout g) root)
    (pairEnough : ∀ index, sizes index + 1 < Fintype.card K) (lookupSmall : ∀ index, config.active index < p)
    (build : MixedWidthStagedSharedLookup.SourceEmission (2*d+1) Digest Memory → RequestLookupPairs.Vector K repetitions →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (MixedWidthStagedSharedLookup.HelperEmission (∑ i, repetitions i) Digest HelperMemory))
    (distance : ∀ root, (radius root : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := L root) (domain root)) (g.m root) :
        Set (Fin (2 ^ first.heights (tag root)) → L root)) : ℚ≥0) / 3)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial)
    (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape first.heights) initial.checkpoints)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = Skeleton.perfect (first.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)) :
    let comparator := PackedPBSRequestComparisonStage.scheme hs.encoding config p small domain fallback behavior pairEnough build
    Pr{let outcome ← (PackedPBSSecondComparisons.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first comparator secondBase initial)}[
      ∃ compared, outcome.2 = some compared ∧
        (MixedWidthOwnedRequestSources.OriginalFalse hs.encoding dummy config domain capacity radius compared ∧
          compared.2.2.1.2.accepted = true) ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState first comparator outcome)] ≤
      RequestLookupPairMiddle.errorBudget (Fintype.card K) widths sizes config.active repetitions +
      ((error K mode (lookupC + lookupRow) + MixedWidthStagedSharedLookup.pcsError (d := e) (padding := padding) (helperPadding := helperPadding) (g := g) L domain radius)) := by
  dsimp only
  refine PackedPBSSecondComparisonProbability.safe_comparison_bound length psi primitive family inputs base hs nodesEnough radix linearBase
    dummy first (PackedPBSRequestComparisonStage.scheme hs.encoding config p small domain fallback behavior pairEnough build) secondBase
    initial audited compatible restricted
    (fun _ compared => MixedWidthOwnedRequestSources.OriginalFalse hs.encoding dummy config domain capacity radius compared ∧
      compared.2.2.1.2.accepted = true) _ ?_
  intro before child _ _ _ incoming
  exact PackedPBSRequestComparisonStage.false_acceptance_safe_bound analysisBasis hs.encoding dummy config p small
    domain enough capacity radius fallback behavior child.1.1.1 child.2.1.2.memory pairEnough lookupSmall build distance _ incoming

end
end FormalProof4FHE.HasteBoots.PackedPBSSecondComparisonSoundness
