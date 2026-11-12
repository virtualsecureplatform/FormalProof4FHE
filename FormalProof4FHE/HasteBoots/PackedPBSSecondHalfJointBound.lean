module
public import FormalProof4FHE.HasteBoots.PackedPBSSecondComparisonSoundness
public import FormalProof4FHE.HasteBoots.PackedPBSDecompositionJointBound
public import FormalProof4FHE.HasteBoots.PackedPBSRequestComparisonStage
@[expose] public section

/-! Derived second-half arithmetic rates join the earlier safe rate and one
charge over the full two-decomposition execution. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSSecondHalfJointBound
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
  [lookupQuerySampling : ∀ root, SampleableType (Fin (layout g root).queries → Fin (2 ^ first.heights (tag root)))]
  [∀ root, Field (L root)] [∀ root, Algebra (ZMod q) (L root)]
  [∀ root, Fintype (L root)] [∀ root, DecidableEq (L root)]
  [∀ root, SampleableType ((Fin (2 ^ (layout g root).front) × Fin (packedWidth (e+padding) (e+helperPadding) root)) → L root)]

variable {P : Type} [Field P] [Algebra (ZMod q) P] [Fintype P] [DecidableEq P]
  [SampleableType ((Fin (2^front) × Fin b) → P)]

local notation "EarlierOutcome" => PackedPBSSecondReconstructionProbability.Before
  (q := q) (Response := Response) (CommitMemory := CommitMemory)
  (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix)
  (queries := queries) (height := height) first

/-- The derived second-half rates combine with the earlier safe rate outside
the final exception, without an intermediate checkpoint charge. -/
theorem native_safe_joint_bound [NeZero m] [NeZero b] [∀ root : MixedWidthLookupOpeningFamily.Root (2*d+1) (∑ i, repetitions i), NeZero (packedWidth (e + padding) (e + helperPadding) root)] [∀ root, NeZero (layout g root).m]
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
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[
      earlier before ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (PackedPBSFirstComparisons.finalState first before)] ≤ earlierRate)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = Skeleton.perfect (first.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)) :
    let comparator := PackedPBSRequestComparisonStage.scheme hs.encoding config p small domain fallback behavior pairEnough build
    Pr{let outcome ← (PackedPBSSecondComparisons.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first comparator secondBase
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[
      ((earlier outcome.1.1 ∨ ∃ compared child, outcome.1.1.2 = some compared ∧ outcome.1.2 = some child ∧
          AmbientLinear.OriginalRisk first.heights
            (PackedPBSSecondReconstruction.reconstruction family inputs hs nodesEnough radix secondBase compared.2.2.1.2.memory)
            dummy nativeCapacity nativeRadius child) ∨
        ∃ compared, outcome.2 = some compared ∧
          (MixedWidthOwnedRequestSources.OriginalFalse hs.encoding dummy config domain capacity radius compared ∧
            compared.2.2.1.2.accepted = true)) ∧
      ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState first comparator outcome)] ≤
      ((earlierRate + linearEpsilon) + (RequestLookupPairMiddle.errorBudget (Fintype.card K) widths sizes config.active repetitions +
        (error K mode (lookupC + lookupRow) + MixedWidthStagedSharedLookup.pcsError (d := e) (padding := padding) (helperPadding := helperPadding) (g := g) L domain radius))) := by
  dsimp only
  let comparator := PackedPBSRequestComparisonStage.scheme hs.encoding config p small domain fallback behavior pairEnough build
  have initial := CheckpointExecution.good_empty hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
  have incoming : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
      (CheckpointExecution.empty (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) :=
    ⟨initial.1,fun _ => initial.2.2⟩
  have compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape first.heights)
      (CheckpointExecution.empty (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)).checkpoints := by
    intro tag entry member
    cases member
  have linear := PackedPBSSecondReconstructionProbability.safe_second_risk_bound length psi primitive family inputs base hs
    nodesEnough radix linearBase dummy first secondBase nativeBasis nativeEnough nativeCapacity nativeRadius linearEpsilon
    geometry linearSmall linearCalibrated _ incoming compatible restricted
  have comparison := PackedPBSSecondComparisonSoundness.original_false_comparison_bound length psi primitive family inputs base hs
    nodesEnough radix linearBase first secondBase analysisBasis dummy config p small domain enough capacity radius fallback behavior
    pairEnough lookupSmall build distance _ incoming compatible restricted
  dsimp only at comparison
  refine PackedPBSDecompositionJointBound.safe_joint_bound length psi primitive family inputs base hs nodesEnough radix linearBase
    dummy first comparator secondBase (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)) earlier
    (fun before => ∃ compared child, before.1.2 = some compared ∧ before.2 = some child ∧
      AmbientLinear.OriginalRisk first.heights
        (PackedPBSSecondReconstruction.reconstruction family inputs hs nodesEnough radix secondBase compared.2.2.1.2.memory)
        dummy nativeCapacity nativeRadius child)
    (fun compared => MixedWidthOwnedRequestSources.OriginalFalse hs.encoding dummy config domain capacity radius compared ∧
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

/-- The actual second reconstruction and request comparison contribute their
derived rates to an earlier safe bound; the whole execution pays one charge. -/
theorem native_risk_or_bad_bound [Fintype Digest] [NeZero m] [NeZero b] [∀ root : MixedWidthLookupOpeningFamily.Root (2*d+1) (∑ i, repetitions i), NeZero (packedWidth (e + padding) (e + helperPadding) root)] [∀ root, NeZero (layout g root).m]
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
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[
      earlier before ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (PackedPBSFirstComparisons.finalState first before)] ≤ earlierRate)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = Skeleton.perfect (first.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)) :
    let comparator := PackedPBSRequestComparisonStage.scheme hs.encoding config p small domain fallback behavior pairEnough build
    Pr{let outcome ← (PackedPBSSecondComparisons.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first comparator secondBase
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[
      ((earlier outcome.1.1 ∨ ∃ compared child, outcome.1.1.2 = some compared ∧ outcome.1.2 = some child ∧
          AmbientLinear.OriginalRisk first.heights
            (PackedPBSSecondReconstruction.reconstruction family inputs hs nodesEnough radix secondBase compared.2.2.1.2.memory)
            dummy nativeCapacity nativeRadius child) ∨
        ∃ compared, outcome.2 = some compared ∧
          (MixedWidthOwnedRequestSources.OriginalFalse hs.encoding dummy config domain capacity radius compared ∧
            compared.2.2.1.2.accepted = true)) ∨
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState first comparator outcome)] ≤
      ((earlierRate + linearEpsilon) + (RequestLookupPairMiddle.errorBudget (Fintype.card K) widths sizes config.active repetitions +
        (error K mode (lookupC + lookupRow) + MixedWidthStagedSharedLookup.pcsError (d := e) (padding := padding) (helperPadding := helperPadding) (g := g) L domain radius))) +
      ExpectedHazard.charge (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
        (AmbientMatrixSource.Shape first.heights))
        (CheckpointCollision.loss unifSpec (AmbientMatrixSource.Shape first.heights))
        (PackedPBSSecondComparisons.program length psi primitive family inputs base hs nodesEnough radix linearBase first comparator secondBase)
        (CheckpointExecution.empty (AmbientMatrixSource.Shape first.heights)) := by
  dsimp only
  let comparator := PackedPBSRequestComparisonStage.scheme hs.encoding config p small domain fallback behavior pairEnough build
  have initial := CheckpointExecution.good_empty hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
  have incoming : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
      (CheckpointExecution.empty (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) :=
    ⟨initial.1,fun _ => initial.2.2⟩
  have compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape first.heights)
      (CheckpointExecution.empty (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)).checkpoints := by
    intro tag entry member
    cases member
  have linear := PackedPBSSecondReconstructionProbability.safe_second_risk_bound length psi primitive family inputs base hs
    nodesEnough radix linearBase dummy first secondBase nativeBasis nativeEnough nativeCapacity nativeRadius linearEpsilon
    geometry linearSmall linearCalibrated _ incoming compatible restricted
  have comparison := PackedPBSSecondComparisonSoundness.original_false_comparison_bound length psi primitive family inputs base hs
    nodesEnough radix linearBase first secondBase analysisBasis dummy config p small domain enough capacity radius fallback behavior
    pairEnough lookupSmall build distance _ incoming compatible restricted
  dsimp only at comparison
  refine PackedPBSDecompositionJointBound.risk_or_bad_bound length psi primitive family inputs base hs nodesEnough radix linearBase
    dummy first comparator secondBase restricted _ _ ?_
  refine PackedPBSDecompositionJointBound.safe_joint_bound length psi primitive family inputs base hs nodesEnough radix linearBase
    dummy first comparator secondBase (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)) earlier
    (fun before => ∃ compared child, before.1.2 = some compared ∧ before.2 = some child ∧
      AmbientLinear.OriginalRisk first.heights
        (PackedPBSSecondReconstruction.reconstruction family inputs hs nodesEnough radix secondBase compared.2.2.1.2.memory)
        dummy nativeCapacity nativeRadius child)
    (fun compared => MixedWidthOwnedRequestSources.OriginalFalse hs.encoding dummy config domain capacity radius compared ∧
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
end FormalProof4FHE.HasteBoots.PackedPBSSecondHalfJointBound
