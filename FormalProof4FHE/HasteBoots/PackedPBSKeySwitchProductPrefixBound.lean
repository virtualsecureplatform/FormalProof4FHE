module
public import FormalProof4FHE.HasteBoots.PackedPBSKeySwitchProductRectangularBound
public import FormalProof4FHE.HasteBoots.PackedPBSKeySwitchNTTPrefixBound
public import FormalProof4FHE.HasteBoots.PackedPBSKeySwitchProductProbability
@[expose] public section

/-! Native safe arithmetic rates from an audited shared prefix. The actual
initial state and extraction-shape compatibility are explicit. The final history
exception is bounded separately. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSKeySwitchProductPrefixBound
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

variable {lanes cells rows rounds : ℕ}
variable {MonoResponse MonoCommitMemory : Type} {monoK monoFront monoSuffix monoM monoQueries monoHeight : ℕ}
  [SampleableType (Fin monoK → Fin (rows+1) → ZMod q)] [SampleableType (Fin (2^lanes) → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^monoFront) (2^lanes))]
  [SampleableType (Fin monoQueries → Fin (2^monoHeight))]

local notation "MonoScheme" => AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg MonoResponse Memory MonoCommitMemory
  (2^lanes) cells (rows+1) monoK monoFront monoSuffix monoM monoQueries monoHeight

variable {ZeroResponse ZeroCommitMemory : Type} {zeroFront zeroSuffix zeroM zeroQueries zeroHeight : ℕ}
  [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (PackedZeroReduction.Points (ZMod q) (cells+rows) (2^lanes))]
  [SampleableType (Fin (2^lanes) → Fin (2^lanes) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^zeroFront) (2^lanes))]
  [SampleableType (Fin zeroQueries → Fin (2^zeroHeight))]

local notation "ZeroScheme" => AuthenticatedPublicZeroCheck.Scheme (ZMod q) Bool Unit Bool
  (Fin (2^lanes) → Fin ((2*(2^lanes)-1)*2+1) → ZMod q) (Fin ((2*(2^lanes)-1)*3+1) → ZMod q)
  Input Digest Cfg ZeroResponse Memory ZeroCommitMemory (2^lanes) (cells+rows) zeroFront zeroSuffix zeroM zeroQueries zeroHeight

variable {MonoP ZeroP : Type}
  [Field MonoP] [Algebra (ZMod q) MonoP] [Fintype MonoP] [DecidableEq MonoP]
  [Field ZeroP] [Algebra (ZMod q) ZeroP] [Fintype ZeroP] [DecidableEq ZeroP]
  [SampleableType (Fin (rows+1) → ZMod q)]
  [SampleableType ((Fin (2^monoFront) × Fin (2^lanes)) → MonoP)]
  [SampleableType ((Fin (2^zeroFront) × Fin (2^lanes)) → ZeroP)]

variable {InputResponse InputCommitMemory : Type} {inputB inputC inputFront inputSuffix inputM inputQueries inputHeight : ℕ}
  [SampleableType (Fin inputB → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^inputFront) inputB)]
  [SampleableType (Fin inputQueries → Fin (2^inputHeight))]
local notation "InputScheme" => AmbientKnownInput.Scheme (ZMod q) Input Digest Cfg InputResponse Memory InputCommitMemory
  inputB (1+inputC) inputFront inputSuffix inputM inputQueries inputHeight

variable {InputP : Type} [Field InputP] [Algebra (ZMod q) InputP] [Fintype InputP] [DecidableEq InputP]
  [SampleableType ((Fin (2^inputFront) × Fin inputB) → InputP)]

variable {FinalResponse FinalCommitMemory FinalP : Type} {finalD finalB finalC : ℕ}
  [Field FinalP] [Algebra (ZMod q) FinalP] [Fintype FinalP] [DecidableEq FinalP]
  [SampleableType (Fin finalB → Fin 1 → ZMod q)] [SampleableType (Fin finalB → ZMod q)]
  [SampleableType (Fin 1 → ZMod q)]

variable {ProductResponse ProductCommitMemory ProductP : Type}
  [Field ProductP] [Algebra (ZMod q) ProductP] [Fintype ProductP] [DecidableEq ProductP]
  [SampleableType (PackedZeroReduction.Points (ZMod q) finalC finalB)]
  [SampleableType (Fin finalB → Fin finalB → ZMod q)]
  [SampleableType (Fin finalC → ZMod q)] [SampleableType (Fin finalB → ((Fin finalB → ZMod q) × ZMod q))]

/-- All preceding native PBS bounds plus the final product rate share the
actual extended execution. Code/layout facts, numeric calibration and recording
scope remain explicit; no child security certificate is supplied. -/
theorem native_safe_joint_bound [NeZero m] [NeZero b] [NeZero accM] [NeZero accB] [NeZero monoM] [NeZero zeroM] [NeZero inputM] [NeZero inputB]
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
    (monoLength : 2^cells*(2^lanes) = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (zeroFirstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (zeroRoundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (zeroNodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (zeroBase : Memory → ZeroScheme)
    (monoBasis : Module.Basis (Fin (2^lanes)) (ZMod q) MonoP)
    (monoEnough : monoM ≤ Fintype.card (Fin (2^monoHeight))) (monoCapacity : 2^monoSuffix ≤ monoM*(2^lanes))
    (monoRadius : Bool → ℕ) (monoEpsilon : Bool → ENNReal)
    (monoGeometry : ∀ side memory source, heights ((monoBase side memory).tag source) = monoHeight)
    (monoSmall : ∀ side memory, (monoRadius side : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := MonoP) (monoBase side memory).domain) monoM :
        Set (Fin (2^monoHeight) → MonoP)) : ℚ≥0)/3)
    (monoCalibrated : ∀ side memory,
      (((((rows+1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^monoK) +
        (cells : ENNReal)*(((((2*(2^lanes)-1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^lanes)))) +
      (JointMatrixOpening.error (K := MonoP) (m := monoM) (b := 2^lanes) (queries := monoQueries) (monoBase side memory).domain (monoRadius side) +
        JointMatrixOpening.error (K := MonoP) (m := monoM) (b := 2^lanes) (queries := monoQueries) (monoBase side memory).domain (monoRadius side)) ≤ monoEpsilon side)
    (zeroBasis : Module.Basis (Fin (2^lanes)) (ZMod q) ZeroP)
    (zeroEnough : zeroM ≤ Fintype.card (Fin (2^zeroHeight))) (zeroCapacity : 2^zeroSuffix ≤ zeroM*(2^lanes))
    (zeroRadius : ℕ) (zeroEpsilon : ENNReal)
    (zeroGeometry : ∀ memory factor, heights ((zeroBase memory).tag factor) = zeroHeight)
    (zeroSmall : ∀ memory, (zeroRadius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := ZeroP) (zeroBase memory).domain) zeroM : Set (Fin (2^zeroHeight) → ZeroP)) : ℚ≥0)/3)
    (zeroCalibrated : ∀ memory,
      ((((cells+rows) : ENNReal)/Fintype.card (ZMod q))^(2^lanes) +
        ((((((2*(2^lanes)-1)*2+1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^lanes))) +
        ((cells+rows) : ENNReal)*((((((2*(2^lanes)-1)*3 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^lanes)))) +
      (JointMatrixOpening.error (K := ZeroP) (m := zeroM) (b := 2^lanes) (queries := zeroQueries) (zeroBase memory).domain zeroRadius +
        JointMatrixOpening.error (K := ZeroP) (m := zeroM) (b := 2^lanes) (queries := zeroQueries) (zeroBase memory).domain zeroRadius) ≤ zeroEpsilon)

    (accLength : 2^accC*accB = 2^log) (inputReference : NativeGoldParameterStore.Reference)
    (inputLength : 2^inputC*inputB = 2^log) (inputSmall : 2*inputB ≤ q) (inputBase : Memory → InputScheme)
    (inputBasis : Module.Basis (Fin inputB) (ZMod q) InputP)
    (inputEnough : inputM ≤ Fintype.card (Fin (2^inputHeight))) (inputCapacity : 2^inputSuffix ≤ inputM*inputB)
    (inputRadius : ℕ) (inputEpsilon : ENNReal)
    (inputGeometry : ∀ memory, heights (inputBase memory).tag = inputHeight)
    (inputSmallDistance : ∀ memory, (inputRadius : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := InputP) (inputBase memory).domain) inputM : Set (Fin (2^inputHeight) → InputP)) : ℚ≥0)/3)
    (inputCalibrated : ∀ memory,
      (((1+inputC : ℕ) : ENNReal)*(((((2*inputB-1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^inputB))) +
      JointMatrixOpening.error (K := InputP) (m := inputM) (b := inputB) (queries := inputQueries) (inputBase memory).domain inputRadius ≤ inputEpsilon)


    (finalFamily : PackedPBSOriginalReferences.Family finalD) (finalNodes : 2*finalB ≤ q)
    (finalLength : 2^finalC*finalB = 2^log)
    (finalBase : Fin (finalD+1) → Memory → PaddedNTT.Scheme (ZMod q) Input Digest Cfg FinalResponse Memory FinalCommitMemory heights finalB finalC 1 finalB)
    [∀ index memory side, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((finalBase index memory).code side).front) finalB)]
    [∀ index memory side, SampleableType (Fin ((finalBase index memory).code side).queries → Fin (2^heights ((finalBase index memory).tag side)))]
    [NeZero finalB] [∀ index memory side, NeZero ((finalBase index memory).code side).m]
    [∀ index memory side, SampleableType ((Fin (2^((finalBase index memory).code side).front) × Fin finalB) → FinalP)]
    (finalBasis : Module.Basis (Fin finalB) (ZMod q) FinalP)
    (finalEnough : ∀ index memory side, ((finalBase index memory).code side).m ≤
      Fintype.card (Fin (2^heights ((finalBase index memory).tag side))))
    (finalCapacity : ∀ index memory side, 2^((finalBase index memory).code side).suffix ≤ ((finalBase index memory).code side).m*finalB)
    (finalRadius : Fin (finalD+1) → Memory → Bool → ℕ) (finalEpsilon : Fin (finalD+1) → ENNReal)
    (finalSmall : ∀ index memory side, (finalRadius index memory side : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := FinalP) ((finalBase index memory).domain side))
        ((finalBase index memory).code side).m : Set (Fin (2^heights ((finalBase index memory).tag side)) → FinalP)) : ℚ≥0)/3)
    (finalCalibrated : ∀ index memory,
      ((((1 : ENNReal)/Fintype.card (ZMod q))^finalB) + (finalC : ENNReal)*(((((2*finalB-1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^finalB))) +
      (JointMatrixOpening.error (K := FinalP) (m := ((finalBase index memory).code false).m) (b := finalB)
          (queries := ((finalBase index memory).code false).queries) ((finalBase index memory).domain false) (finalRadius index memory false) +
        JointMatrixOpening.error (K := FinalP) (m := ((finalBase index memory).code true).m) (b := finalB)
          (queries := ((finalBase index memory).code true).queries) ((finalBase index memory).domain true) (finalRadius index memory true)) ≤ finalEpsilon index)


    (productFirstSmall : (2*finalB-1)*2+1 ≤ q) (productRoundSmall : (2*finalB-1)*3+1 ≤ q)
    (productNodes : 2*finalB ≤ (2*finalB-1)*2+1)
    (productBase : Memory → KeySwitchPaddedProduct.Scheme (q := q) (d := finalD) (b := finalB) (n := finalC)
      (Input := Input) (Cfg := Cfg) (Response := ProductResponse) (Memory := Memory) (CommitMemory := ProductCommitMemory) (heights := heights))
    [∀ memory factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((productBase memory).code factor).front) finalB)]
    [∀ memory factor, SampleableType (Fin ((productBase memory).code factor).queries → Fin (2^heights ((productBase memory).tag factor)))]
    [∀ memory factor, NeZero ((productBase memory).code factor).m]
    [∀ memory factor, SampleableType ((Fin (2^((productBase memory).code factor).front) × Fin finalB) → ProductP)]
    (productBasis : Module.Basis (Fin finalB) (ZMod q) ProductP)
    (productEnough : ∀ memory factor, ((productBase memory).code factor).m ≤ Fintype.card (Fin (2^heights ((productBase memory).tag factor))))
    (productCapacity : ∀ memory factor, 2^((productBase memory).code factor).suffix ≤ ((productBase memory).code factor).m*finalB)
    (productRadius : Memory → PBSHadamard.Factor finalD → ℕ) (productEpsilon : ENNReal)
    (productSmall : ∀ memory factor, (productRadius memory factor : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := ProductP) ((productBase memory).domain factor))
        ((productBase memory).code factor).m : Set (Fin (2^heights ((productBase memory).tag factor)) → ProductP)) : ℚ≥0)/3)
    (productCalibrated : ∀ memory,
      (((finalC : ENNReal)/Fintype.card (ZMod q))^finalB + ((((((2*finalB-1)*2+1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^finalB)) +
        (finalC : ENNReal)*((((((2*finalB-1)*3 : ℕ) : ENNReal)/Fintype.card (ZMod q))^finalB))) +
      ((PBSHadamard.factors finalD).map (fun factor => JointMatrixOpening.error (K := ProductP) (m := ((productBase memory).code factor).m)
        (b := finalB) (queries := ((productBase memory).code factor).queries) ((productBase memory).domain factor) (productRadius memory factor))).sum ≤ productEpsilon)

    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = Skeleton.perfect (heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base
        (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs) nodesEnough radix linearBase)) :
    let ns := AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs
    let first := RectangularPBSComparisonStage.scheme (helperPadding := helperPadding) hs.encoding config p small domain fallback behavior pairEnough build
    let second := RectangularPBSComparisonStage.scheme (helperPadding := secondHelperPadding) hs.encoding secondConfig secondP secondSmall secondDomain secondFallback secondBehavior secondPairEnough secondBuild
    Pr{let outcome ← (PackedPBSKeySwitchProduct.witness length psi primitive family inputs base ns nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase zeroFirstSmall zeroRoundSmall zeroNodesEnough rotations zeroBase
      accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase initialState)}[
      (((fun outcome => (((fun outcome => (((fun previous => (((fun prior => ((((PackedPBSReconstructionJointBound.Risk length psi primitive family inputs base ns nodesEnough radix linearBase dummy nativeCapacity nativeRadius prior.1.1.1.1 ∨
          ∃ compared, prior.1.1.1.2 = some compared ∧
            RectangularOwnedRequestSources.OriginalFalse hs.encoding dummy config domain lookupCapacity lookupRadius compared ∧
              compared.2.2.1.2.accepted = true) ∨
        ∃ compared child, prior.1.1.1.2 = some compared ∧ prior.1.1.2 = some child ∧
          AmbientLinear.OriginalRisk heights
            (PackedPBSSecondReconstruction.reconstruction family inputs ns nodesEnough radix secondBase compared.2.2.1.2.memory)
            dummy nativeCapacity nativeRadius child) ∨
        ∃ compared, prior.1.2 = some compared ∧
          (RectangularOwnedRequestSources.OriginalFalse hs.encoding dummy secondConfig secondDomain secondLookupCapacity secondLookupRadius compared ∧
            compared.2.2.1.2.accepted = true)) ∨ ∃ compared child, prior.1.2 = some compared ∧ prior.2 = some child ∧
        OwnedAmbientAccumulator.OriginalRisk heights
          (PackedPBSAccumulator.accumulator family inputs ns accumulators factory compared.2.2.1.2.memory)
          dummy accCapacity accRadius child)) previous.1.1) ∨ ((∃ ntts, previous.1.2 = some ntts ∧ AmbientNTTSequenceSoundness.AnyOriginalRisk (AmbientMonomialNTT.factory hs.encoding monoLength psi primitive (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase) heights dummy monoCapacity monoRadius ntts.1) ∨
        (∃ ntts product, previous.1.2 = some ntts ∧ previous.2 = some product ∧ AmbientPublicZeroCheck.OriginalRisk heights (MonomialPublicZeroCheck.stage zeroFirstSmall zeroRoundSmall zeroNodesEnough hs.encoding psi rotations evaluations.roots (zeroBase ntts.1.memory)) dummy zeroCapacity zeroRadius product)))) outcome.1) ∨ (∃ product acc input, outcome.1.2 = some product ∧ outcome.1.1.1.2 = some acc ∧ outcome.2 = some input ∧
        AmbientKnownInput.OriginalRisk heights
          (KeySwitchKnownInput.stage inputSmall hs.encoding inputReference.root inputLength
            (AccumulatorEndpoint.value accLength (factory acc.1.1.2).context) (inputBase product.2.1.2.memory)) dummy inputCapacity inputRadius input))) outcome.1) ∨ (∃ ntts, outcome.2 = some ntts ∧
        PaddedNTTSequenceSoundness.AnyOriginalRisk (KeySwitchPaddedNTT.factory finalBase hs.encoding finalFamily finalNodes finalLength psi primitive) hs.encoding dummy finalCapacity finalRadius ntts.1))) outcome.1) ∨ (∃ product, outcome.2 = some product ∧ PaddedZeroCheck.OriginalRisk (KeySwitchPaddedProduct.stage (productBase product.1) hs.encoding finalFamily productFirstSmall productRoundSmall productNodes) dummy
        (productCapacity product.1) (productRadius product.1) product.2)) ∧
      ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) (PackedPBSKeySwitchProduct.finalState first second finalBase productBase outcome)] ≤
      (((((((((PackedPBSHadamardNTTJointBound.rate (K := P) hs nativeRadius + ((List.finRange (2*d+1)).map nttEpsilon).sum) + linearEpsilon) +
        (RequestLookupPairMiddle.errorBudget (Fintype.card K) widths sizes config.active repetitions +
          (error K mode (lookupC+lookupRow) + RectangularStagedSharedLookup.pcsError (d := e) (padding := padding) (helperPadding := helperPadding) (g := g) (symbolWidth := symbolWidth) domain lookupRadius))) + secondLinearEpsilon) +
        (RequestLookupPairMiddle.errorBudget (Fintype.card SecondK) secondWidths secondSizes secondConfig.active secondRepetitions +
          (error SecondK secondMode (secondLookupC+secondLookupRow) + RectangularStagedSharedLookup.pcsError (d := secondE) (padding := secondPadding) (helperPadding := secondHelperPadding) (g := secondG) (symbolWidth := secondSymbolWidth) secondDomain secondLookupRadius))) + accEpsilon) + ((monoEpsilon false + monoEpsilon true) + zeroEpsilon)) + inputEpsilon) + ((List.finRange (finalD+1)).map finalEpsilon).sum) + productEpsilon := by
  have audited := auditedInitial
  have compatible := compatibleInitial
  have previous := PackedPBSKeySwitchNTTPrefixBound.native_safe_joint_bound (q := q) (log := log) (d := d) (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix) (m := m) (queries := queries) (height := height) (heights := heights) (FinalResponse := FinalResponse) (FinalCommitMemory := FinalCommitMemory) (finalD := finalD) (finalB := finalB) (finalC := finalC) (FinalP := FinalP) length psi primitive family inputs base firstSmall roundSmall hadNodes hs
    nodesEnough radix linearBase nativeBasis dummy initialState auditedInitial compatibleInitial nativeEnough nativeCapacity nativeRadius nttEpsilon linearEpsilon nttEncoding linearEncoding
    hadSmall nttSmall linearSmall nttCalibrated linearCalibrated config p small domain lookupEnough lookupCapacity lookupRadius
    fallback behavior pairEnough lookupSmall build distanceLarge distance secondConfig secondP secondSmall secondDomain secondLookupEnough
    secondLookupCapacity secondLookupRadius secondFallback secondBehavior secondPairEnough secondLookupSmall secondBuild secondDistanceLarge secondDistance
    secondBase secondLinearEpsilon secondGeometry secondLinearSmall secondLinearCalibrated accumulators factory accBasis accEnough accCapacity
    accRadius accEpsilon accGeometry accSmall accCalibrated monoLength evaluations monoBase zeroFirstSmall zeroRoundSmall zeroNodesEnough rotations zeroBase
    monoBasis monoEnough monoCapacity monoRadius monoEpsilon monoGeometry monoSmall monoCalibrated
    zeroBasis zeroEnough zeroCapacity zeroRadius zeroEpsilon zeroGeometry zeroSmall zeroCalibrated accLength inputReference inputLength inputSmall inputBase
    inputBasis inputEnough inputCapacity inputRadius inputEpsilon inputGeometry inputSmallDistance inputCalibrated finalFamily finalNodes finalLength finalBase
    finalBasis finalEnough finalCapacity finalRadius finalEpsilon finalSmall finalCalibrated restricted
  refine PackedPBSKeySwitchProductProbability.safe_joint_bound length psi primitive family inputs base (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs) nodesEnough radix linearBase dummy (RectangularPBSComparisonStage.scheme (helperPadding := helperPadding) hs.encoding config p small domain fallback behavior pairEnough build) (RectangularPBSComparisonStage.scheme (helperPadding := secondHelperPadding) hs.encoding secondConfig secondP secondSmall secondDomain secondFallback secondBehavior secondPairEnough secondBuild) secondBase accumulators factory monoLength evaluations monoBase zeroFirstSmall zeroRoundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase initialState
    (fun outcome => (((fun outcome => (((fun previous => (((fun prior => ((((PackedPBSReconstructionJointBound.Risk length psi primitive family inputs base (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs) nodesEnough radix linearBase dummy nativeCapacity nativeRadius prior.1.1.1.1 ∨
          ∃ compared, prior.1.1.1.2 = some compared ∧
            RectangularOwnedRequestSources.OriginalFalse hs.encoding dummy config domain lookupCapacity lookupRadius compared ∧
              compared.2.2.1.2.accepted = true) ∨
        ∃ compared child, prior.1.1.1.2 = some compared ∧ prior.1.1.2 = some child ∧
          AmbientLinear.OriginalRisk heights
            (PackedPBSSecondReconstruction.reconstruction family inputs (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs) nodesEnough radix secondBase compared.2.2.1.2.memory)
            dummy nativeCapacity nativeRadius child) ∨
        ∃ compared, prior.1.2 = some compared ∧
          (RectangularOwnedRequestSources.OriginalFalse hs.encoding dummy secondConfig secondDomain secondLookupCapacity secondLookupRadius compared ∧
            compared.2.2.1.2.accepted = true)) ∨ ∃ compared child, prior.1.2 = some compared ∧ prior.2 = some child ∧
        OwnedAmbientAccumulator.OriginalRisk heights
          (PackedPBSAccumulator.accumulator family inputs (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs) accumulators factory compared.2.2.1.2.memory)
          dummy accCapacity accRadius child)) previous.1.1) ∨ ((∃ ntts, previous.1.2 = some ntts ∧ AmbientNTTSequenceSoundness.AnyOriginalRisk (AmbientMonomialNTT.factory hs.encoding monoLength psi primitive (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase) heights dummy monoCapacity monoRadius ntts.1) ∨
        (∃ ntts product, previous.1.2 = some ntts ∧ previous.2 = some product ∧ AmbientPublicZeroCheck.OriginalRisk heights (MonomialPublicZeroCheck.stage zeroFirstSmall zeroRoundSmall zeroNodesEnough hs.encoding psi rotations evaluations.roots (zeroBase ntts.1.memory)) dummy zeroCapacity zeroRadius product)))) outcome.1) ∨ (∃ product acc input, outcome.1.2 = some product ∧ outcome.1.1.1.2 = some acc ∧ outcome.2 = some input ∧
        AmbientKnownInput.OriginalRisk heights
          (KeySwitchKnownInput.stage inputSmall hs.encoding inputReference.root inputLength
            (AccumulatorEndpoint.value accLength (factory acc.1.1.2).context) (inputBase product.2.1.2.memory)) dummy inputCapacity inputRadius input))) outcome.1) ∨ (∃ ntts, outcome.2 = some ntts ∧
        PaddedNTTSequenceSoundness.AnyOriginalRisk (KeySwitchPaddedNTT.factory finalBase hs.encoding finalFamily finalNodes finalLength psi primitive) hs.encoding dummy finalCapacity finalRadius ntts.1)))
    (fun outcome => ∃ product, outcome.2 = some product ∧ PaddedZeroCheck.OriginalRisk (KeySwitchPaddedProduct.stage (productBase product.1) hs.encoding finalFamily productFirstSmall productRoundSmall productNodes) dummy
        (productCapacity product.1) (productRadius product.1) product.2)
    (((((((((PackedPBSHadamardNTTJointBound.rate (K := P) hs nativeRadius + ((List.finRange (2*d+1)).map nttEpsilon).sum) + linearEpsilon) +
        (RequestLookupPairMiddle.errorBudget (Fintype.card K) widths sizes config.active repetitions +
          (error K mode (lookupC+lookupRow) + RectangularStagedSharedLookup.pcsError (d := e) (padding := padding) (helperPadding := helperPadding) (g := g) (symbolWidth := symbolWidth) domain lookupRadius))) + secondLinearEpsilon) +
        (RequestLookupPairMiddle.errorBudget (Fintype.card SecondK) secondWidths secondSizes secondConfig.active secondRepetitions +
          (error SecondK secondMode (secondLookupC+secondLookupRow) + RectangularStagedSharedLookup.pcsError (d := secondE) (padding := secondPadding) (helperPadding := secondHelperPadding) (g := secondG) (symbolWidth := secondSymbolWidth) secondDomain secondLookupRadius))) + accEpsilon) + ((monoEpsilon false + monoEpsilon true) + zeroEpsilon)) + inputEpsilon) + ((List.finRange (finalD+1)).map finalEpsilon).sum) productEpsilon ?_ ?_
  · refine le_trans ?_ previous
    apply prEvent_mono
    intro actual event
    refine ⟨event.1,?_⟩
    cases reached : actual.2 with
    | none => simpa only [PackedPBSKeySwitchProduct.beforeState,PackedPBSKeySwitchNTT.finalState,reached,RectangularPBSComparisonStage.scheme] using event.2
    | some ntts => simpa only [PackedPBSKeySwitchProduct.beforeState,PackedPBSKeySwitchNTT.finalState,reached,RectangularPBSComparisonStage.scheme] using event.2
  · exact PackedPBSKeySwitchProductProbability.safe_original_product_final_bound (ProductP := ProductP) length psi primitive family inputs base (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs) nodesEnough radix linearBase dummy (RectangularPBSComparisonStage.scheme (helperPadding := helperPadding) hs.encoding config p small domain fallback behavior pairEnough build) (RectangularPBSComparisonStage.scheme (helperPadding := secondHelperPadding) hs.encoding secondConfig secondP secondSmall secondDomain secondFallback secondBehavior secondPairEnough secondBuild) secondBase accumulators factory monoLength evaluations monoBase zeroFirstSmall zeroRoundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase
      productBasis productEnough productCapacity productRadius productEpsilon productSmall productCalibrated
      initialState compatible restricted audited

end
end FormalProof4FHE.HasteBoots.PackedPBSKeySwitchProductPrefixBound
