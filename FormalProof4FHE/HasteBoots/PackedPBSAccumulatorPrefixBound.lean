module
public import FormalProof4FHE.HasteBoots.PackedPBSAccumulatorRectangularBound
public import FormalProof4FHE.HasteBoots.PackedPBSDecompositionPrefixBound
public import FormalProof4FHE.HasteBoots.PackedPBSAccumulatorJointBound
@[expose] public section

/-! Native safe arithmetic rates from an audited shared prefix. The actual
initial state and extraction-shape compatibility are explicit. The final history
exception is bounded separately. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSAccumulatorPrefixBound
open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open NativeRootMessage (Digest)
open PackedPBSFirstComparisons (priorState finalState)
open scoped Classical BigOperators
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening
open FormalProof4FHE.HasteBoots.PaddedMixedWidthLookupOpeningFamily
open FormalProof4FHE.HasteBoots.MixedWidthSharedLookupPCSAlgebra
noncomputable section
variable {q log d b c r k n front suffix m queries height : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin b → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points (ZMod q) n b)] [SampleableType (Fin b → Fin b → ZMod q)]
variable {P : Type} [Field P] [Algebra (ZMod q) P] [Fintype P] [DecidableEq P]
  [SampleableType (ZMod q)] [SampleableType (Fin r → ZMod q)]
  [SampleableType ((Fin (2^front) × Fin b) → P)]
  [SampleableType (Fin n → ZMod q)] [SampleableType (Fin b → ((Fin b → ZMod q) × ZMod q))]

variable {K LookupMessage LookupResponse HelperMemory : Type}
  [Field K] [Algebra (ZMod q) K] [Fintype K] [DecidableEq K] [SampleableType K]
  {e padding helperPadding lookupC lookupRow requests : ℕ}
  {widths sizes repetitions : Fin requests → ℕ} {mode : Mode}
  {heights : Cfg → ℕ} {tag : Root (2*d+1) (∑ i, repetitions i) → Cfg}
  {g : Geometry lookupC lookupRow (2*d+1) (∑ i, repetitions i)}
  {symbolWidth : Root (2*d+1) (∑ i, repetitions i) → ℕ}
  [SampleableType (Fin 1 → K)] [SampleableType (Fin (lookupC+lookupRow) → K)]
  [∀ root, SampleableType (TestMatrix (ZMod q) (2 ^ (layout g root).front) (packedWidth (e+padding) (e+helperPadding) root))]
  [∀ root, SampleableType (Fin (layout g root).queries → Fin (2 ^ heights (tag root)))]
  [∀ root, SampleableType ((Fin (2 ^ (layout g root).front) × Fin (packedWidth (e+padding) (e+helperPadding) root)) → ZMod q)]

variable {SecondK SecondLookupMessage SecondLookupResponse SecondHelperMemory : Type}
  [Field SecondK] [Algebra (ZMod q) SecondK] [Fintype SecondK] [DecidableEq SecondK] [SampleableType SecondK]
  {secondE secondPadding secondHelperPadding secondLookupC secondLookupRow secondRequests : ℕ}
  {secondWidths secondSizes secondRepetitions : Fin secondRequests → ℕ} {secondMode : Mode}
  {secondTag : Root (2*d+1) (∑ i, secondRepetitions i) → Cfg}
  {secondG : Geometry secondLookupC secondLookupRow (2*d+1) (∑ i, secondRepetitions i)}
  {secondSymbolWidth : Root (2*d+1) (∑ i, secondRepetitions i) → ℕ}
  [SampleableType (Fin 1 → SecondK)] [SampleableType (Fin (secondLookupC+secondLookupRow) → SecondK)]
  [∀ root, SampleableType (TestMatrix (ZMod q) (2 ^ (layout secondG root).front) (packedWidth (secondE+secondPadding) (secondE+secondHelperPadding) root))]
  [∀ root, SampleableType (Fin (layout secondG root).queries → Fin (2 ^ heights (secondTag root)))]
  [∀ root, SampleableType ((Fin (2 ^ (layout secondG root).front) × Fin (packedWidth (secondE+secondPadding) (secondE+secondHelperPadding) root)) → ZMod q)]

variable {AccResponse AccP : Type} {accB accC accR accFront accSuffix accM accQueries accHeight : ℕ}
  [Field AccP] [Algebra (ZMod q) AccP] [Fintype AccP] [DecidableEq AccP]
  [SampleableType (Fin accB → ZMod q)]
  [SampleableType (TestMatrix (ZMod q) (2^accFront) accB)]
  [SampleableType (Fin accQueries → Fin (2^accHeight))]
  [SampleableType ((Fin (2^accFront) × Fin accB) → AccP)]

local notation "AccScheme" => AmbientAccumulator.Scheme (ZMod q) Input Digest Cfg AccResponse Memory Memory
  accB accC accR accFront accSuffix accM accQueries accHeight

/-- All arithmetic rates through the original-source accumulator are derived
outside the shared final exception. This form extends to later stages without
paying an intermediate checkpoint charge. -/
theorem native_safe_joint_bound [NeZero m] [NeZero b] [NeZero accM] [NeZero accB]
    (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
  (family : PackedPBSOriginalReferences.Family (2*d)) (inputs : PackedPBSDecompositionReferences.Inputs)
  (base : Fin (2*d+1) → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    b c r k front suffix m queries height)
  (firstSmall : (2*b-1)*2+1 ≤ q) (roundSmall : (2*b-1)*3+1 ≤ q)
  (hadNodes : 2*b ≤ (2*b-1)*2+1)
  (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor (2*d)) (PBSHadamard.Term (2*d))
    (Fin b → Fin ((2*b-1)*2+1) → ZMod q) (Fin ((2*b-1)*3+1) → ZMod q) Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
  (nodesEnough : 2*b ≤ q) (radix : ZMod q)
  (linearBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) b front suffix m queries height)

    (nativeBasis : Module.Basis (Fin b) (ZMod q) P) (dummy : Digest)
    (initialState : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (auditedInitial : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initialState)
    (compatibleInitial : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape heights) initialState.checkpoints)
    (nativeEnough : m ≤ Fintype.card (Fin (2^height))) (nativeCapacity : 2^suffix ≤ m*b) (nativeRadius : ℕ)
    (nttEpsilon : Fin (2*d+1) → ENNReal) (linearEpsilon : ENNReal)
    (nttEncoding : ∀ slot memory, (base slot memory).encoding = hs.encoding)
    (linearEncoding : ∀ memory, (linearBase memory).encoding = hs.encoding)
    (hadSmall : (nativeRadius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := P) hs.domain) m :
        Set (Fin (2^height) → P)) : ℚ≥0)/3)
    (nttSmall : ∀ slot memory, (nativeRadius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := P) (base slot memory).domain) m :
        Set (Fin (2^height) → P)) : ℚ≥0)/3)
    (linearSmall : ∀ memory, (nativeRadius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := P) (linearBase memory).domain) m :
        Set (Fin (2^height) → P)) : ℚ≥0)/3)
    (nttCalibrated : ∀ slot memory, HadamardNTTProbability.rate (K := P) (base slot memory) nativeRadius ≤ nttEpsilon slot)
    (linearCalibrated : ∀ memory,
      (((front+suffix : ℕ) : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^b))) +
      ((2*d+2 : ℕ) : ENNReal)*JointMatrixOpening.error (K := P) (m := m) (b := b) (queries := queries)
        (linearBase memory).domain nativeRadius ≤ linearEpsilon)
    [∀ root : Root (2*d+1) (∑ i, repetitions i), NeZero (symbolWidth root)] [∀ root, NeZero (layout g root).m]
    (config : RectangularRequestLookup.Parameters (ZMod q) K LookupMessage Memory Cfg Input Digest Memory HelperMemory
      e padding lookupC lookupRow (2*d+1) requests widths sizes repetitions mode)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ (ZMod q))
    (lookupEnough : ∀ root, g.m root ≤ Fintype.card (Fin (2 ^ heights (tag root))))
    (lookupCapacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * symbolWidth root) (lookupRadius : Root (2*d+1) (∑ i, repetitions i) → ℕ)
    (fallback : Packet (ZMod q) K (e + padding) (2*d+1) (lookupC + lookupRow) (∑ i, repetitions i))
    (behavior : RectangularStagedSharedLookup.Emission (2*d+1) (∑ i, repetitions i) Digest Memory (RequestLookupPairMiddle.Memory K HelperMemory repetitions) →
      RectangularSharedLookupPCS.Selection (ZMod q) K Memory (e + padding) (2*d+1) (∑ i, repetitions i) (lookupC + lookupRow) →
      (root : Root (2*d+1) (∑ i, repetitions i)) → Protocol (ZMod q) Input Digest Cfg LookupResponse Memory (packedWidth (e + padding) (e + helperPadding)) symbolWidth heights tag (layout g) root)
    (pairEnough : ∀ index, sizes index + 1 < Fintype.card K) (lookupSmall : ∀ index, config.active index < p)
    (build : RectangularStagedSharedLookup.SourceEmission (2*d+1) Digest Memory → RequestLookupPairs.Vector K repetitions →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (RectangularStagedSharedLookup.HelperEmission (∑ i, repetitions i) Digest HelperMemory))
    (distanceLarge : ∀ root, lookupRadius root < Fintype.card (ZMod q))
    (distance : ∀ root, 3*lookupRadius root <
      Code.minDist (BlockCode.code (domain root) (g.m root) (symbolWidth root) :
        Set (Fin (2 ^ heights (tag root)) → Fin (symbolWidth root) → ZMod q)))
    [∀ root : Root (2*d+1) (∑ i, secondRepetitions i), NeZero (secondSymbolWidth root)] [∀ root, NeZero (layout secondG root).m]
    (secondConfig : RectangularRequestLookup.Parameters (ZMod q) SecondK SecondLookupMessage Memory Cfg Input Digest Memory SecondHelperMemory
      secondE secondPadding secondLookupC secondLookupRow (2*d+1) secondRequests secondWidths secondSizes secondRepetitions secondMode)
    (secondP : ℕ) [CharP SecondK secondP] (secondSmall : 2 * 1 ≤ secondP)
    (secondDomain : ∀ root, Fin (2 ^ heights (secondTag root)) ↪ (ZMod q))
    (secondLookupEnough : ∀ root, secondG.m root ≤ Fintype.card (Fin (2 ^ heights (secondTag root))))
    (secondLookupCapacity : ∀ root, 2 ^ secondG.suffix root ≤ secondG.m root * secondSymbolWidth root) (secondLookupRadius : Root (2*d+1) (∑ i, secondRepetitions i) → ℕ)
    (secondFallback : Packet (ZMod q) SecondK (secondE + secondPadding) (2*d+1) (secondLookupC + secondLookupRow) (∑ i, secondRepetitions i))
    (secondBehavior : RectangularStagedSharedLookup.Emission (2*d+1) (∑ i, secondRepetitions i) Digest Memory (RequestLookupPairMiddle.Memory SecondK SecondHelperMemory secondRepetitions) →
      RectangularSharedLookupPCS.Selection (ZMod q) SecondK Memory (secondE + secondPadding) (2*d+1) (∑ i, secondRepetitions i) (secondLookupC + secondLookupRow) →
      (root : Root (2*d+1) (∑ i, secondRepetitions i)) → Protocol (ZMod q) Input Digest Cfg SecondLookupResponse Memory (packedWidth (secondE + secondPadding) (secondE + secondHelperPadding)) secondSymbolWidth heights secondTag (layout secondG) root)
    (secondPairEnough : ∀ index, secondSizes index + 1 < Fintype.card SecondK) (secondLookupSmall : ∀ index, secondConfig.active index < secondP)
    (secondBuild : RectangularStagedSharedLookup.SourceEmission (2*d+1) Digest Memory → RequestLookupPairs.Vector SecondK secondRepetitions →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (RectangularStagedSharedLookup.HelperEmission (∑ i, secondRepetitions i) Digest SecondHelperMemory))
    (secondDistanceLarge : ∀ root, secondLookupRadius root < Fintype.card (ZMod q))
    (secondDistance : ∀ root, 3*secondLookupRadius root <
      Code.minDist (BlockCode.code (secondDomain root) (secondG.m root) (secondSymbolWidth root) :
        Set (Fin (2 ^ heights (secondTag root)) → Fin (secondSymbolWidth root) → ZMod q)))
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (secondLinearEpsilon : ENNReal)
    (secondGeometry : ∀ memory factor, heights ((secondBase memory).tag factor) = height)
    (secondLinearSmall : ∀ memory, (nativeRadius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := P) (secondBase memory).domain) m :
        Set (Fin (2^height) → P)) : ℚ≥0)/3)
    (secondLinearCalibrated : ∀ memory,
      (((front+suffix : ℕ) : ENNReal)*(((((2*b-1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^b))) +
      ((2*d+2 : ℕ) : ENNReal)*JointMatrixOpening.error (K := P) (m := m) (b := b) (queries := queries)
        (secondBase memory).domain nativeRadius ≤ secondLinearEpsilon)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (accBasis : Module.Basis (Fin accB) (ZMod q) AccP)
    (accEnough : accM ≤ Fintype.card (Fin (2^accHeight))) (accCapacity : 2^accSuffix ≤ accM*accB)
    (accRadius : ℕ) (accEpsilon : ENNReal)
    (accGeometry : ∀ memory factor, heights ((factory memory).tag factor) = accHeight)
    (accSmall : ∀ memory, (accRadius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := AccP) (factory memory).domain) accM :
        Set (Fin (2^accHeight) → AccP)) : ℚ≥0)/3)
    (accCalibrated : ∀ memory,
      ((((1+accR)+accC : ℕ) : ENNReal) * (((((2*accB-1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^accB))) +
        7 * JointMatrixOpening.error (K := AccP) (m := accM) (b := accB) (queries := accQueries)
          (factory memory).domain accRadius ≤ accEpsilon)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = Skeleton.perfect (heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base
        (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs) nodesEnough radix linearBase)) :
    let ns := AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs
    let first := RectangularPBSComparisonStage.scheme (helperPadding := helperPadding) hs.encoding config p small domain fallback behavior pairEnough build
    let second := RectangularPBSComparisonStage.scheme (helperPadding := secondHelperPadding) hs.encoding secondConfig secondP secondSmall secondDomain secondFallback secondBehavior secondPairEnough secondBuild
    Pr{let outcome ← (PackedPBSAccumulator.witness length psi primitive family inputs base ns nodesEnough radix linearBase dummy first second secondBase accumulators factory
      initialState)}[
      ((((PackedPBSReconstructionJointBound.Risk length psi primitive family inputs base ns nodesEnough radix linearBase dummy nativeCapacity nativeRadius outcome.1.1.1.1 ∨
          ∃ compared, outcome.1.1.1.2 = some compared ∧
            RectangularOwnedRequestSources.OriginalFalse hs.encoding dummy config domain lookupCapacity lookupRadius compared ∧
              compared.2.2.1.2.accepted = true) ∨
        ∃ compared child, outcome.1.1.1.2 = some compared ∧ outcome.1.1.2 = some child ∧
          AmbientLinear.OriginalRisk heights
            (PackedPBSSecondReconstruction.reconstruction family inputs ns nodesEnough radix secondBase compared.2.2.1.2.memory)
            dummy nativeCapacity nativeRadius child) ∨
        ∃ compared, outcome.1.2 = some compared ∧
          (RectangularOwnedRequestSources.OriginalFalse hs.encoding dummy secondConfig secondDomain secondLookupCapacity secondLookupRadius compared ∧
            compared.2.2.1.2.accepted = true)) ∨ ∃ compared child, outcome.1.2 = some compared ∧ outcome.2 = some child ∧
        OwnedAmbientAccumulator.OriginalRisk heights
          (PackedPBSAccumulator.accumulator family inputs ns accumulators factory compared.2.2.1.2.memory)
          dummy accCapacity accRadius child) ∧
      ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) (PackedPBSAccumulator.finalState first second outcome)] ≤
      ((((((PackedPBSHadamardNTTJointBound.rate (K := P) hs nativeRadius + ((List.finRange (2*d+1)).map nttEpsilon).sum) + linearEpsilon) +
        (RequestLookupPairMiddle.errorBudget (Fintype.card K) widths sizes config.active repetitions +
          (error K mode (lookupC+lookupRow) + RectangularStagedSharedLookup.pcsError (d := e) (padding := padding) (helperPadding := helperPadding) (g := g) (symbolWidth := symbolWidth) domain lookupRadius))) + secondLinearEpsilon) +
        (RequestLookupPairMiddle.errorBudget (Fintype.card SecondK) secondWidths secondSizes secondConfig.active secondRepetitions +
          (error SecondK secondMode (secondLookupC+secondLookupRow) + RectangularStagedSharedLookup.pcsError (d := secondE) (padding := secondPadding) (helperPadding := secondHelperPadding) (g := secondG) (symbolWidth := secondSymbolWidth) secondDomain secondLookupRadius))) + accEpsilon) := by
  have earlier := PackedPBSDecompositionPrefixBound.native_safe_joint_bound length psi primitive family inputs base firstSmall roundSmall hadNodes hs
    nodesEnough radix linearBase nativeBasis dummy initialState auditedInitial compatibleInitial nativeEnough nativeCapacity nativeRadius nttEpsilon linearEpsilon nttEncoding linearEncoding
    hadSmall nttSmall linearSmall nttCalibrated linearCalibrated config p small domain lookupEnough lookupCapacity lookupRadius
    fallback behavior pairEnough lookupSmall build distanceLarge distance secondConfig secondP secondSmall secondDomain secondLookupEnough
    secondLookupCapacity secondLookupRadius secondFallback secondBehavior secondPairEnough secondLookupSmall secondBuild secondDistanceLarge secondDistance
    secondBase secondLinearEpsilon secondGeometry secondLinearSmall secondLinearCalibrated restricted
  have incoming := auditedInitial
  have compatible := compatibleInitial
  have accumulatorBound := PackedPBSAccumulatorProbability.safe_original_accumulator_bound (P := AccP)
    length psi primitive family inputs base (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs) nodesEnough radix linearBase dummy (RectangularPBSComparisonStage.scheme (helperPadding := helperPadding) hs.encoding config p small domain fallback behavior pairEnough build) (RectangularPBSComparisonStage.scheme (helperPadding := secondHelperPadding) hs.encoding secondConfig secondP secondSmall secondDomain secondFallback secondBehavior secondPairEnough secondBuild) secondBase accumulators factory
    initialState accBasis accEnough accCapacity accRadius accEpsilon
    accGeometry accSmall accCalibrated incoming compatible restricted
  refine PackedPBSAccumulatorJointBound.safe_joint_bound length psi primitive family inputs base (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs) nodesEnough radix linearBase
    dummy (RectangularPBSComparisonStage.scheme (helperPadding := helperPadding) hs.encoding config p small domain fallback behavior pairEnough build) (RectangularPBSComparisonStage.scheme (helperPadding := secondHelperPadding) hs.encoding secondConfig secondP secondSmall secondDomain secondFallback secondBehavior secondPairEnough secondBuild) secondBase accumulators factory initialState
    (fun before => (((PackedPBSReconstructionJointBound.Risk length psi primitive family inputs base (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs) nodesEnough radix linearBase dummy nativeCapacity nativeRadius before.1.1.1 ∨
          ∃ compared, before.1.1.2 = some compared ∧
            RectangularOwnedRequestSources.OriginalFalse hs.encoding dummy config domain lookupCapacity lookupRadius compared ∧
              compared.2.2.1.2.accepted = true) ∨
        ∃ compared child, before.1.1.2 = some compared ∧ before.1.2 = some child ∧
          AmbientLinear.OriginalRisk heights
            (PackedPBSSecondReconstruction.reconstruction family inputs (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs) nodesEnough radix secondBase compared.2.2.1.2.memory)
            dummy nativeCapacity nativeRadius child) ∨
        ∃ compared, before.2 = some compared ∧
          (RectangularOwnedRequestSources.OriginalFalse hs.encoding dummy secondConfig secondDomain secondLookupCapacity secondLookupRadius compared ∧
            compared.2.2.1.2.accepted = true)))
    (fun outcome => ∃ compared child, outcome.1.2 = some compared ∧ outcome.2 = some child ∧
        OwnedAmbientAccumulator.OriginalRisk heights
          (PackedPBSAccumulator.accumulator family inputs (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs) accumulators factory compared.2.2.1.2.memory)
          dummy accCapacity accRadius child) _ accEpsilon earlier ?_
  convert accumulatorBound using 1
  apply prEvent_congr
  intro outcome
  constructor
  · rintro ⟨⟨compared,child,equalCompared,equalChild,risk⟩,clear⟩
    refine ⟨compared,child,equalCompared,equalChild,risk,?_⟩
    simpa only [PackedPBSAccumulator.finalState,equalChild] using clear
  · rintro ⟨compared,child,equalCompared,equalChild,risk,clear⟩
    refine ⟨⟨compared,child,equalCompared,equalChild,risk⟩,?_⟩
    simpa only [PackedPBSAccumulator.finalState,equalChild] using clear

end
end FormalProof4FHE.HasteBoots.PackedPBSAccumulatorPrefixBound
