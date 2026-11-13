module
public import FormalProof4FHE.HasteBoots.PackedPBSSecondRectangularHalfBound
public import FormalProof4FHE.HasteBoots.PackedPBSSecondRectangularComparison
public import FormalProof4FHE.HasteBoots.PackedPBSDecompositionJointBound
public import FormalProof4FHE.HasteBoots.RectangularPBSComparisonStage
@[expose] public section

/-! Native safe arithmetic rates from an audited shared prefix. The actual
initial state and extraction-shape compatibility are explicit. The final history
exception is bounded separately. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSSecondRectangularPrefixBound
open BinaryTree Matrix MerkleTreeMultiExtractability
open scoped Classical BigOperators
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening
open FormalProof4FHE.HasteBoots.PaddedMixedWidthLookupOpeningFamily
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
  {tag : PaddedMixedWidthLookupOpeningFamily.Root (2*d+1) (∑ i, repetitions i) → Cfg}
  {g : Geometry lookupC lookupRow (2*d+1) (∑ i, repetitions i)}
  {symbolWidth : PaddedMixedWidthLookupOpeningFamily.Root (2*d+1) (∑ i, repetitions i) → ℕ}
  [SampleableType (Fin 1 → K)] [SampleableType (Fin (lookupC+lookupRow) → K)]
  [∀ root, SampleableType (TestMatrix (ZMod q) (2 ^ (layout g root).front) (packedWidth (e+padding) (e+helperPadding) root))]
  [lookupQuerySampling : ∀ root, SampleableType (Fin (layout g root).queries → Fin (2 ^ first.heights (tag root)))]
  [∀ root, SampleableType ((Fin (2 ^ (layout g root).front) × Fin (packedWidth (e+padding) (e+helperPadding) root)) → ZMod q)]

variable {P : Type} [Field P] [Algebra (ZMod q) P] [Fintype P] [DecidableEq P]
  [SampleableType ((Fin (2^front) × Fin b) → P)]

local notation "EarlierOutcome" => PackedPBSSecondReconstructionProbability.Before
  (q := q) (Response := Response) (CommitMemory := CommitMemory)
  (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix)
  (queries := queries) (height := height) first

/-- The derived second-half rates combine with the earlier safe rate outside
the final exception, without an intermediate checkpoint charge. -/
theorem native_safe_joint_bound [NeZero m] [NeZero b] [∀ root : PaddedMixedWidthLookupOpeningFamily.Root (2*d+1) (∑ i, repetitions i), NeZero (symbolWidth root)] [∀ root, NeZero (layout g root).m]
    (dummy : Digest)
    (initialState : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (auditedInitial : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initialState)
    (compatibleInitial : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape first.heights) initialState.checkpoints)
    (config : RectangularRequestLookup.Parameters (ZMod q) K LookupMessage LookupMemory Cfg Input Digest Memory HelperMemory
      e padding lookupC lookupRow (2*d+1) requests widths sizes repetitions mode)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (domain : ∀ root, Fin (2 ^ first.heights (tag root)) ↪ (ZMod q))
    (enough : ∀ root, g.m root ≤ Fintype.card (Fin (2 ^ first.heights (tag root))))
    (capacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * symbolWidth root) (radius : PaddedMixedWidthLookupOpeningFamily.Root (2*d+1) (∑ i, repetitions i) → ℕ)
    (fallback : Packet (ZMod q) K (e + padding) (2*d+1) (lookupC + lookupRow) (∑ i, repetitions i))
    (behavior : RectangularStagedSharedLookup.Emission (2*d+1) (∑ i, repetitions i) Digest Memory (RequestLookupPairMiddle.Memory K HelperMemory repetitions) →
      RectangularSharedLookupPCS.Selection (ZMod q) K LookupMemory (e + padding) (2*d+1) (∑ i, repetitions i) (lookupC + lookupRow) →
      (root : PaddedMixedWidthLookupOpeningFamily.Root (2*d+1) (∑ i, repetitions i)) → Protocol (ZMod q) Input Digest Cfg LookupResponse LookupMemory (packedWidth (e + padding) (e + helperPadding)) symbolWidth first.heights tag (layout g) root)
    (pairEnough : ∀ index, sizes index + 1 < Fintype.card K) (lookupSmall : ∀ index, config.active index < p)
    (build : RectangularStagedSharedLookup.SourceEmission (2*d+1) Digest Memory → RequestLookupPairs.Vector K repetitions →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (RectangularStagedSharedLookup.HelperEmission (∑ i, repetitions i) Digest HelperMemory))
    (distanceLarge : ∀ root, radius root < Fintype.card (ZMod q))
    (distance : ∀ root, 3*radius root <
      Code.minDist (BlockCode.code (domain root) (g.m root) (symbolWidth root) :
        Set (Fin (2 ^ first.heights (tag root)) → Fin (symbolWidth root) → ZMod q)))
    (nativeBasis : Module.Basis (Fin b) (ZMod q) P)
    (nativeEnough : m ≤ Fintype.card (Fin (2^height))) (nativeCapacity : 2^suffix ≤ m*b)
    (nativeRadius : ℕ) (linearEpsilon : ENNReal)
    (geometry : ∀ memory factor, first.heights ((secondBase memory).tag factor) = height)
    (linearSmall : ∀ memory, (nativeRadius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := P) (secondBase memory).domain) m :
        Set (Fin (2^height) → P)) : ℚ≥0)/3)
    (linearCalibrated : ∀ memory,
      (((front+suffix : ℕ) : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^b))) +
      ((2*d+2 : ℕ) : ENNReal)*JointMatrixOpening.error (K := P) (m := m) (b := b) (queries := queries)
        (secondBase memory).domain nativeRadius ≤ linearEpsilon)
    (earlier : EarlierOutcome → Prop) (earlierRate : ENNReal)
    (earlier_bound : Pr{let before ← (PackedPBSFirstComparisons.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first
      initialState)}[
      earlier before ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (PackedPBSFirstComparisons.finalState first before)] ≤ earlierRate)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = Skeleton.perfect (first.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)) :
    let comparator := RectangularPBSComparisonStage.scheme (helperPadding := helperPadding) hs.encoding config p small domain fallback behavior pairEnough build
    Pr{let outcome ← (PackedPBSSecondComparisons.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first comparator secondBase
      initialState)}[
      ((earlier outcome.1.1 ∨ ∃ compared child, outcome.1.1.2 = some compared ∧ outcome.1.2 = some child ∧
          AmbientLinear.OriginalRisk first.heights
            (PackedPBSSecondReconstruction.reconstruction family inputs hs nodesEnough radix secondBase compared.2.2.1.2.memory)
            dummy nativeCapacity nativeRadius child) ∨
        ∃ compared, outcome.2 = some compared ∧
          (RectangularOwnedRequestSources.OriginalFalse hs.encoding dummy config domain capacity radius compared ∧
            compared.2.2.1.2.accepted = true)) ∧
      ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState first comparator outcome)] ≤
      ((earlierRate + linearEpsilon) + (RequestLookupPairMiddle.errorBudget (Fintype.card K) widths sizes config.active repetitions +
        (error K mode (lookupC + lookupRow) + RectangularStagedSharedLookup.pcsError (d := e) (padding := padding) (helperPadding := helperPadding) (g := g) (symbolWidth := symbolWidth) domain radius))) := by
  dsimp only
  let comparator := RectangularPBSComparisonStage.scheme (helperPadding := helperPadding) hs.encoding config p small domain fallback behavior pairEnough build
  have incoming := auditedInitial
  have compatible := compatibleInitial
  have linear := PackedPBSSecondReconstructionProbability.safe_second_risk_bound length psi primitive family inputs base hs
    nodesEnough radix linearBase dummy first secondBase nativeBasis nativeEnough nativeCapacity nativeRadius linearEpsilon
    geometry linearSmall linearCalibrated _ incoming compatible restricted
  have comparison := PackedPBSSecondRectangularComparison.original_false_comparison_bound length psi primitive family inputs base hs
    nodesEnough radix linearBase first secondBase dummy config p small domain enough capacity radius fallback behavior
    pairEnough lookupSmall build distanceLarge distance _ incoming compatible restricted
  dsimp only at comparison
  refine PackedPBSDecompositionJointBound.safe_joint_bound length psi primitive family inputs base hs nodesEnough radix linearBase
    dummy first comparator secondBase initialState earlier
    (fun before => ∃ compared child, before.1.2 = some compared ∧ before.2 = some child ∧
      AmbientLinear.OriginalRisk first.heights
        (PackedPBSSecondReconstruction.reconstruction family inputs hs nodesEnough radix secondBase compared.2.2.1.2.memory)
        dummy nativeCapacity nativeRadius child)
    (fun compared => RectangularOwnedRequestSources.OriginalFalse hs.encoding dummy config domain capacity radius compared ∧
      compared.2.2.1.2.accepted = true) earlierRate linearEpsilon _ earlier_bound ?_ comparison
  convert linear using 1
  apply prEvent_congr
  intro before
  constructor
  · rintro ⟨⟨compared,child,equalCompared,equalChild,risk⟩,clear⟩
    refine ⟨compared,child,equalCompared,equalChild,risk,?_⟩
    simpa only [PackedPBSSecondComparisons.beforeState,PackedPBSSecondReconstruction.finalState,equalChild] using clear
  · rintro ⟨compared,child,equalCompared,equalChild,risk,clear⟩
    refine ⟨⟨compared,child,equalCompared,equalChild,risk⟩,?_⟩
    simpa only [PackedPBSSecondComparisons.beforeState,PackedPBSSecondReconstruction.finalState,equalChild] using clear

end
end FormalProof4FHE.HasteBoots.PackedPBSSecondRectangularPrefixBound
