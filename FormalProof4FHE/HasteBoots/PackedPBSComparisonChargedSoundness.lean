module
public import FormalProof4FHE.HasteBoots.PackedPBSComparisonSharedExecution
public import FormalProof4FHE.HasteBoots.PackedPBSFirstComparisonSoundness
public import FormalProof4FHE.HasteBoots.PackedPBSRequestComparisonStage
@[expose] public section

/-! The actual first comparison false-tuple event and the shared exception
event have one derived arithmetic rate and one whole extended-prefix charge. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSComparisonChargedSoundness
open BinaryTree Matrix MerkleTreeMultiExtractability
open scoped Classical BigOperators
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.VariableWidthBatchOpening
open FormalProof4FHE.HasteBoots.MixedWidthLookupOpeningFamily
open FormalProof4FHE.HasteBoots.MixedWidthSharedLookupPCSAlgebra
open PackedPBSFirstComparisons (priorState finalState)
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


variable {K LookupMessage LookupMemory LookupResponse HelperMemory : Type}
  [Field K] [Algebra (ZMod q) K] [Fintype K] [DecidableEq K] [SampleableType K]
  {e padding helperPadding lookupC lookupRow requests : ℕ}
  {widths sizes repetitions : Fin requests → ℕ} {mode : Mode}
  {heights : Cfg → ℕ} {tag : Root (2*d+1) (∑ i, repetitions i) → Cfg}
  {g : Geometry lookupC lookupRow (2*d+1) (∑ i, repetitions i)}
  {L : Root (2*d+1) (∑ i, repetitions i) → Type}
  [SampleableType (Fin 1 → K)] [SampleableType (Fin (lookupC+lookupRow) → K)]
  [∀ root, SampleableType (TestMatrix (ZMod q) (2 ^ (layout g root).front) (packedWidth (e+padding) (e+helperPadding) root))]
  [∀ root, SampleableType (Fin (layout g root).queries → Fin (2 ^ heights (tag root)))]
  [∀ root, Field (L root)] [∀ root, Algebra (ZMod q) (L root)]
  [∀ root, Fintype (L root)] [∀ root, DecidableEq (L root)]
  [∀ root, SampleableType ((Fin (2 ^ (layout g root).front) × Fin (packedWidth (e+padding) (e+helperPadding) root)) → L root)]

/-- Accepted false original tuples and the shared collision/availability event are
charged once on the actual Hadamard/NTT/reconstruction/comparison program. -/
theorem false_comparison_or_bad_bound [Fintype Digest] [∀ root : Root (2*d+1) (∑ i, repetitions i), NeZero (packedWidth (e + padding) (e + helperPadding) root)] [∀ root, NeZero (layout g root).m]
    (analysisBasis : ∀ root, Module.Basis (Fin (packedWidth (e + padding) (e + helperPadding) root)) (ZMod q) (L root))
    (dummy : Digest)
    (config : MixedWidthRequestSharedLookup.Parameters (ZMod q) K LookupMessage LookupMemory Cfg Input Digest Memory HelperMemory
      e padding lookupC lookupRow (2*d+1) requests widths sizes repetitions mode)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ (ZMod q))
    (enough : ∀ root, g.m root ≤ Fintype.card (Fin (2 ^ heights (tag root))))
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * packedWidth (e + padding) (e + helperPadding) root) (radius : Root (2*d+1) (∑ i, repetitions i) → ℕ)
    (fallback : Packet (ZMod q) K (e + padding) (2*d+1) (lookupC + lookupRow) (∑ i, repetitions i))
    (behavior : MixedWidthStagedSharedLookup.Emission (2*d+1) (∑ i, repetitions i) Digest Memory (RequestLookupPairMiddle.Memory K HelperMemory repetitions) →
      MixedWidthSharedLookupPCS.Selection (ZMod q) K LookupMemory (e + padding) (2*d+1) (∑ i, repetitions i) (lookupC + lookupRow) →
      (root : Root (2*d+1) (∑ i, repetitions i)) → Protocol (ZMod q) Input Digest Cfg LookupResponse LookupMemory (packedWidth (e + padding) (e + helperPadding)) heights tag (layout g) root)
    (pairEnough : ∀ index, sizes index + 1 < Fintype.card K) (lookupSmall : ∀ index, config.active index < p)
    (build : MixedWidthStagedSharedLookup.SourceEmission (2*d+1) Digest Memory → RequestLookupPairs.Vector K repetitions →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (MixedWidthStagedSharedLookup.HelperEmission (∑ i, repetitions i) Digest HelperMemory))
    (distance : ∀ root, (radius root : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := L root) (domain root)) (g.m root) :
        Set (Fin (2 ^ heights (tag root)) → L root)) : ℚ≥0) / 3)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = Skeleton.perfect (heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)) :
    let comparator := PackedPBSRequestComparisonStage.scheme hs.encoding config p small domain fallback behavior pairEnough build
    Pr{let outcome ← (PackedPBSFirstComparisons.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy comparator
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[
      (∃ compared, outcome.2 = some compared ∧
        MixedWidthOwnedRequestSources.OriginalFalse hs.encoding dummy config domain capacity radius compared ∧
          compared.2.2.1.2.accepted = true) ∨
      CheckpointCollision.Bad _ (finalState comparator outcome)] ≤
      (RequestLookupPairMiddle.errorBudget (Fintype.card K) widths sizes config.active repetitions +
      ((error K mode (lookupC + lookupRow) + MixedWidthStagedSharedLookup.pcsError (d := e) (padding := padding) (helperPadding := helperPadding) (g := g) L domain radius))) +
      ExpectedHazard.charge (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
        (fun cfg => Skeleton.perfect (heights cfg)))
        (CheckpointCollision.loss unifSpec (fun cfg => Skeleton.perfect (heights cfg)))
        (PackedPBSFirstComparisons.program length psi primitive family inputs base hs nodesEnough radix linearBase comparator)
        (CheckpointExecution.empty (fun cfg => Skeleton.perfect (heights cfg))) := by
  dsimp only
  let s := PackedPBSRequestComparisonStage.scheme hs.encoding config p small domain fallback behavior pairEnough build
  have emptyCompatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (fun cfg => Skeleton.perfect (heights cfg))
      (CheckpointExecution.empty (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)).checkpoints := by
    intro tag entry member
    cases member
  have compatible := fun prior supported => PackedPBSComparisonSharedExecution.prefix_compatible length psi primitive
    family inputs base hs nodesEnough radix linearBase dummy (fun cfg => Skeleton.perfect (heights cfg))
    (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)) emptyCompatible restricted prior supported
  have audited := (CheckpointExecution.good_empty hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height))
  have incoming : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
      (CheckpointExecution.empty (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) :=
    ⟨audited.1,fun _ => audited.2.2⟩
  have safe := PackedPBSFirstComparisonSoundness.original_false_comparison_bound length psi primitive family inputs base hs nodesEnough radix linearBase
    analysisBasis dummy config p small domain enough capacity radius fallback behavior pairEnough lookupSmall build distance
    (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)) incoming compatible
  dsimp only at safe
  refine PackedPBSComparisonSharedExecution.risk_or_bad_bound length psi primitive family inputs base hs nodesEnough radix linearBase
    dummy s restricted
    (fun outcome => ∃ compared, outcome.2 = some compared ∧
      MixedWidthOwnedRequestSources.OriginalFalse hs.encoding dummy config domain capacity radius compared ∧
        compared.2.2.1.2.accepted = true) _ ?_
  convert safe using 1
  apply prEvent_congr
  intro outcome
  constructor
  · rintro ⟨⟨compared,equal,falseTuple,accepted⟩,clear⟩
    exact ⟨compared,equal,⟨falseTuple,accepted⟩,clear⟩
  · rintro ⟨compared,equal,⟨falseTuple,accepted⟩,clear⟩
    exact ⟨⟨compared,equal,falseTuple,accepted⟩,clear⟩

end
end FormalProof4FHE.HasteBoots.PackedPBSComparisonChargedSoundness
