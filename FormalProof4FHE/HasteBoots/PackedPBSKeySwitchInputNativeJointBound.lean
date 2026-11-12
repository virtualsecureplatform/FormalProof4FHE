module
public import FormalProof4FHE.HasteBoots.PackedPBSMonomialNativeJointBound
public import FormalProof4FHE.HasteBoots.PackedPBSKeySwitchInputProbability
@[expose] public section

/-! Derived native rates through the final key-switch known-input opening share
the entire PBS prefix and its single final exception. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSKeySwitchInputNativeJointBound
open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open NativeRootMessage (Digest)
open PackedPBSFirstComparisons (priorState finalState)
open scoped Classical BigOperators
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.VariableWidthBatchOpening
open FormalProof4FHE.HasteBoots.MixedWidthLookupOpeningFamily
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
  {L : Root (2*d+1) (∑ i, repetitions i) → Type}
  [SampleableType (Fin 1 → K)] [SampleableType (Fin (lookupC+lookupRow) → K)]
  [∀ root, SampleableType (TestMatrix (ZMod q) (2 ^ (layout g root).front) (packedWidth (e+padding) (e+helperPadding) root))]
  [∀ root, SampleableType (Fin (layout g root).queries → Fin (2 ^ heights (tag root)))]
  [∀ root, Field (L root)] [∀ root, Algebra (ZMod q) (L root)]
  [∀ root, Fintype (L root)] [∀ root, DecidableEq (L root)]
  [∀ root, SampleableType ((Fin (2 ^ (layout g root).front) × Fin (packedWidth (e+padding) (e+helperPadding) root)) → L root)]

variable {SecondK SecondLookupMessage SecondLookupResponse SecondHelperMemory : Type}
  [Field SecondK] [Algebra (ZMod q) SecondK] [Fintype SecondK] [DecidableEq SecondK] [SampleableType SecondK]
  {secondE secondPadding secondHelperPadding secondLookupC secondLookupRow secondRequests : ℕ}
  {secondWidths secondSizes secondRepetitions : Fin secondRequests → ℕ} {secondMode : Mode}
  {secondTag : Root (2*d+1) (∑ i, secondRepetitions i) → Cfg}
  {secondG : Geometry secondLookupC secondLookupRow (2*d+1) (∑ i, secondRepetitions i)}
  {SecondL : Root (2*d+1) (∑ i, secondRepetitions i) → Type}
  [SampleableType (Fin 1 → SecondK)] [SampleableType (Fin (secondLookupC+secondLookupRow) → SecondK)]
  [∀ root, SampleableType (TestMatrix (ZMod q) (2 ^ (layout secondG root).front) (packedWidth (secondE+secondPadding) (secondE+secondHelperPadding) root))]
  [∀ root, SampleableType (Fin (layout secondG root).queries → Fin (2 ^ heights (secondTag root)))]
  [∀ root, Field (SecondL root)] [∀ root, Algebra (ZMod q) (SecondL root)]
  [∀ root, Fintype (SecondL root)] [∀ root, DecidableEq (SecondL root)]
  [∀ root, SampleableType ((Fin (2 ^ (layout secondG root).front) × Fin (packedWidth (secondE+secondPadding) (secondE+secondHelperPadding) root)) → SecondL root)]

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

/-- All native arithmetic rates through the padded known-input check are
derived on the extended actual PBS prefix. Only code/layout, numeric calibration
and the earlier recording scope remain explicit; no child security bound is supplied. -/
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
    [∀ root : Root (2*d+1) (∑ i, repetitions i), NeZero (packedWidth (e+padding) (e+helperPadding) root)] [∀ root, NeZero (layout g root).m]
    (analysisBasis : ∀ root, Module.Basis (Fin (packedWidth (e + padding) (e + helperPadding) root)) (ZMod q) (L root))
    (config : MixedWidthRequestSharedLookup.Parameters (ZMod q) K LookupMessage Memory Cfg Input Digest Memory HelperMemory
      e padding lookupC lookupRow (2*d+1) requests widths sizes repetitions mode)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ (ZMod q))
    (lookupEnough : ∀ root, g.m root ≤ Fintype.card (Fin (2 ^ heights (tag root))))
    (lookupCapacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * packedWidth (e + padding) (e + helperPadding) root) (lookupRadius : Root (2*d+1) (∑ i, repetitions i) → ℕ)
    (fallback : Packet (ZMod q) K (e + padding) (2*d+1) (lookupC + lookupRow) (∑ i, repetitions i))
    (behavior : MixedWidthStagedSharedLookup.Emission (2*d+1) (∑ i, repetitions i) Digest Memory (RequestLookupPairMiddle.Memory K HelperMemory repetitions) →
      MixedWidthSharedLookupPCS.Selection (ZMod q) K Memory (e + padding) (2*d+1) (∑ i, repetitions i) (lookupC + lookupRow) →
      (root : Root (2*d+1) (∑ i, repetitions i)) → Protocol (ZMod q) Input Digest Cfg LookupResponse Memory (packedWidth (e + padding) (e + helperPadding)) heights tag (layout g) root)
    (pairEnough : ∀ index, sizes index + 1 < Fintype.card K) (lookupSmall : ∀ index, config.active index < p)
    (build : MixedWidthStagedSharedLookup.SourceEmission (2*d+1) Digest Memory → RequestLookupPairs.Vector K repetitions →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (MixedWidthStagedSharedLookup.HelperEmission (∑ i, repetitions i) Digest HelperMemory))
    (distance : ∀ root, (lookupRadius root : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := L root) (domain root)) (g.m root) :
        Set (Fin (2 ^ heights (tag root)) → L root)) : ℚ≥0) / 3)
    [∀ root : Root (2*d+1) (∑ i, secondRepetitions i), NeZero (packedWidth (secondE+secondPadding) (secondE+secondHelperPadding) root)] [∀ root, NeZero (layout secondG root).m]
    (secondAnalysisBasis : ∀ root, Module.Basis (Fin (packedWidth (secondE + secondPadding) (secondE + secondHelperPadding) root)) (ZMod q) (SecondL root))
    (secondConfig : MixedWidthRequestSharedLookup.Parameters (ZMod q) SecondK SecondLookupMessage Memory Cfg Input Digest Memory SecondHelperMemory
      secondE secondPadding secondLookupC secondLookupRow (2*d+1) secondRequests secondWidths secondSizes secondRepetitions secondMode)
    (secondP : ℕ) [CharP SecondK secondP] (secondSmall : 2 * 1 ≤ secondP)
    (secondDomain : ∀ root, Fin (2 ^ heights (secondTag root)) ↪ (ZMod q))
    (secondLookupEnough : ∀ root, secondG.m root ≤ Fintype.card (Fin (2 ^ heights (secondTag root))))
    (secondLookupCapacity : ∀ root, 2 ^ secondG.suffix root ≤ secondG.m root * packedWidth (secondE + secondPadding) (secondE + secondHelperPadding) root) (secondLookupRadius : Root (2*d+1) (∑ i, secondRepetitions i) → ℕ)
    (secondFallback : Packet (ZMod q) SecondK (secondE + secondPadding) (2*d+1) (secondLookupC + secondLookupRow) (∑ i, secondRepetitions i))
    (secondBehavior : MixedWidthStagedSharedLookup.Emission (2*d+1) (∑ i, secondRepetitions i) Digest Memory (RequestLookupPairMiddle.Memory SecondK SecondHelperMemory secondRepetitions) →
      MixedWidthSharedLookupPCS.Selection (ZMod q) SecondK Memory (secondE + secondPadding) (2*d+1) (∑ i, secondRepetitions i) (secondLookupC + secondLookupRow) →
      (root : Root (2*d+1) (∑ i, secondRepetitions i)) → Protocol (ZMod q) Input Digest Cfg SecondLookupResponse Memory (packedWidth (secondE + secondPadding) (secondE + secondHelperPadding)) heights secondTag (layout secondG) root)
    (secondPairEnough : ∀ index, secondSizes index + 1 < Fintype.card SecondK) (secondLookupSmall : ∀ index, secondConfig.active index < secondP)
    (secondBuild : MixedWidthStagedSharedLookup.SourceEmission (2*d+1) Digest Memory → RequestLookupPairs.Vector SecondK secondRepetitions →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (MixedWidthStagedSharedLookup.HelperEmission (∑ i, secondRepetitions i) Digest SecondHelperMemory))
    (secondDistance : ∀ root, (secondLookupRadius root : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := SecondL root) (secondDomain root)) (secondG.m root) :
        Set (Fin (2 ^ heights (secondTag root)) → SecondL root)) : ℚ≥0) / 3)
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

    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = Skeleton.perfect (heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base
        (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs) nodesEnough radix linearBase)) :
    let ns := AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs
    let first := PackedPBSRequestComparisonStage.scheme hs.encoding config p small domain fallback behavior pairEnough build
    let second := PackedPBSRequestComparisonStage.scheme hs.encoding secondConfig secondP secondSmall secondDomain secondFallback secondBehavior secondPairEnough secondBuild
    Pr{let outcome ← (PackedPBSKeySwitchInput.witness length psi primitive family inputs base ns nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase zeroFirstSmall zeroRoundSmall zeroNodesEnough rotations zeroBase
      accLength inputReference inputLength inputSmall inputBase (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[
      (((fun previous => (((fun prior => ((((PackedPBSReconstructionJointBound.Risk length psi primitive family inputs base ns nodesEnough radix linearBase dummy nativeCapacity nativeRadius prior.1.1.1.1 ∨
          ∃ compared, prior.1.1.1.2 = some compared ∧
            MixedWidthOwnedRequestSources.OriginalFalse hs.encoding dummy config domain lookupCapacity lookupRadius compared ∧
              compared.2.2.1.2.accepted = true) ∨
        ∃ compared child, prior.1.1.1.2 = some compared ∧ prior.1.1.2 = some child ∧
          AmbientLinear.OriginalRisk heights
            (PackedPBSSecondReconstruction.reconstruction family inputs ns nodesEnough radix secondBase compared.2.2.1.2.memory)
            dummy nativeCapacity nativeRadius child) ∨
        ∃ compared, prior.1.2 = some compared ∧
          (MixedWidthOwnedRequestSources.OriginalFalse hs.encoding dummy secondConfig secondDomain secondLookupCapacity secondLookupRadius compared ∧
            compared.2.2.1.2.accepted = true)) ∨ ∃ compared child, prior.1.2 = some compared ∧ prior.2 = some child ∧
        OwnedAmbientAccumulator.OriginalRisk heights
          (PackedPBSAccumulator.accumulator family inputs ns accumulators factory compared.2.2.1.2.memory)
          dummy accCapacity accRadius child)) previous.1.1) ∨ ((∃ ntts, previous.1.2 = some ntts ∧ AmbientNTTSequenceSoundness.AnyOriginalRisk (AmbientMonomialNTT.factory hs.encoding monoLength psi primitive (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase) heights dummy monoCapacity monoRadius ntts.1) ∨
        (∃ ntts product, previous.1.2 = some ntts ∧ previous.2 = some product ∧ AmbientPublicZeroCheck.OriginalRisk heights (MonomialPublicZeroCheck.stage zeroFirstSmall zeroRoundSmall zeroNodesEnough hs.encoding psi rotations evaluations.roots (zeroBase ntts.1.memory)) dummy zeroCapacity zeroRadius product)))) outcome.1) ∨ (∃ product acc input, outcome.1.2 = some product ∧ outcome.1.1.1.2 = some acc ∧ outcome.2 = some input ∧
        AmbientKnownInput.OriginalRisk heights
          (KeySwitchKnownInput.stage inputSmall hs.encoding inputReference.root inputLength
            (AccumulatorEndpoint.value accLength (factory acc.1.1.2).context) (inputBase product.2.1.2.memory)) dummy inputCapacity inputRadius input)) ∧
      ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) (PackedPBSKeySwitchInput.finalState first second outcome)] ≤
      (((((((PackedPBSHadamardNTTJointBound.rate (K := P) hs nativeRadius + ((List.finRange (2*d+1)).map nttEpsilon).sum) + linearEpsilon) +
        (RequestLookupPairMiddle.errorBudget (Fintype.card K) widths sizes config.active repetitions +
          (error K mode (lookupC+lookupRow) + MixedWidthStagedSharedLookup.pcsError (d := e) (padding := padding) (helperPadding := helperPadding) (g := g) L domain lookupRadius))) + secondLinearEpsilon) +
        (RequestLookupPairMiddle.errorBudget (Fintype.card SecondK) secondWidths secondSizes secondConfig.active secondRepetitions +
          (error SecondK secondMode (secondLookupC+secondLookupRow) + MixedWidthStagedSharedLookup.pcsError (d := secondE) (padding := secondPadding) (helperPadding := secondHelperPadding) (g := secondG) SecondL secondDomain secondLookupRadius))) + accEpsilon) + ((monoEpsilon false + monoEpsilon true) + zeroEpsilon)) + inputEpsilon := by
  have good := CheckpointExecution.good_empty hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
  have audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
      (CheckpointExecution.empty (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) :=
    ⟨good.1,fun _ => good.2.2⟩
  have compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape heights)
      (CheckpointExecution.empty (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)).checkpoints := by
    intro tag saved member
    cases member
  refine PackedPBSKeySwitchInputProbability.safe_joint_bound length psi primitive family inputs base (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs) nodesEnough radix linearBase dummy (PackedPBSRequestComparisonStage.scheme hs.encoding config p small domain fallback behavior pairEnough build) (PackedPBSRequestComparisonStage.scheme hs.encoding secondConfig secondP secondSmall secondDomain secondFallback secondBehavior secondPairEnough secondBuild) secondBase accumulators factory monoLength evaluations monoBase zeroFirstSmall zeroRoundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height))
    (fun previous => (((fun prior => ((((PackedPBSReconstructionJointBound.Risk length psi primitive family inputs base (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs) nodesEnough radix linearBase dummy nativeCapacity nativeRadius prior.1.1.1.1 ∨
          ∃ compared, prior.1.1.1.2 = some compared ∧
            MixedWidthOwnedRequestSources.OriginalFalse hs.encoding dummy config domain lookupCapacity lookupRadius compared ∧
              compared.2.2.1.2.accepted = true) ∨
        ∃ compared child, prior.1.1.1.2 = some compared ∧ prior.1.1.2 = some child ∧
          AmbientLinear.OriginalRisk heights
            (PackedPBSSecondReconstruction.reconstruction family inputs (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs) nodesEnough radix secondBase compared.2.2.1.2.memory)
            dummy nativeCapacity nativeRadius child) ∨
        ∃ compared, prior.1.2 = some compared ∧
          (MixedWidthOwnedRequestSources.OriginalFalse hs.encoding dummy secondConfig secondDomain secondLookupCapacity secondLookupRadius compared ∧
            compared.2.2.1.2.accepted = true)) ∨ ∃ compared child, prior.1.2 = some compared ∧ prior.2 = some child ∧
        OwnedAmbientAccumulator.OriginalRisk heights
          (PackedPBSAccumulator.accumulator family inputs (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs) accumulators factory compared.2.2.1.2.memory)
          dummy accCapacity accRadius child)) previous.1.1) ∨ ((∃ ntts, previous.1.2 = some ntts ∧ AmbientNTTSequenceSoundness.AnyOriginalRisk (AmbientMonomialNTT.factory hs.encoding monoLength psi primitive (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase) heights dummy monoCapacity monoRadius ntts.1) ∨
        (∃ ntts product, previous.1.2 = some ntts ∧ previous.2 = some product ∧ AmbientPublicZeroCheck.OriginalRisk heights (MonomialPublicZeroCheck.stage zeroFirstSmall zeroRoundSmall zeroNodesEnough hs.encoding psi rotations evaluations.roots (zeroBase ntts.1.memory)) dummy zeroCapacity zeroRadius product))))
    (fun outcome => ∃ product acc input, outcome.1.2 = some product ∧ outcome.1.1.1.2 = some acc ∧ outcome.2 = some input ∧
        AmbientKnownInput.OriginalRisk heights
          (KeySwitchKnownInput.stage inputSmall hs.encoding inputReference.root inputLength
            (AccumulatorEndpoint.value accLength (factory acc.1.1.2).context) (inputBase product.2.1.2.memory)) dummy inputCapacity inputRadius input)
    (((((((PackedPBSHadamardNTTJointBound.rate (K := P) hs nativeRadius + ((List.finRange (2*d+1)).map nttEpsilon).sum) + linearEpsilon) +
        (RequestLookupPairMiddle.errorBudget (Fintype.card K) widths sizes config.active repetitions +
          (error K mode (lookupC+lookupRow) + MixedWidthStagedSharedLookup.pcsError (d := e) (padding := padding) (helperPadding := helperPadding) (g := g) L domain lookupRadius))) + secondLinearEpsilon) +
        (RequestLookupPairMiddle.errorBudget (Fintype.card SecondK) secondWidths secondSizes secondConfig.active secondRepetitions +
          (error SecondK secondMode (secondLookupC+secondLookupRow) + MixedWidthStagedSharedLookup.pcsError (d := secondE) (padding := secondPadding) (helperPadding := secondHelperPadding) (g := secondG) SecondL secondDomain secondLookupRadius))) + accEpsilon) + ((monoEpsilon false + monoEpsilon true) + zeroEpsilon)) inputEpsilon ?_ ?_
  · exact PackedPBSMonomialNativeJointBound.native_safe_joint_bound length psi primitive family inputs base firstSmall roundSmall hadNodes hs
      nodesEnough radix linearBase nativeBasis dummy nativeEnough nativeCapacity nativeRadius nttEpsilon linearEpsilon nttEncoding linearEncoding
      hadSmall nttSmall linearSmall nttCalibrated linearCalibrated analysisBasis config p small domain lookupEnough lookupCapacity lookupRadius
      fallback behavior pairEnough lookupSmall build distance secondAnalysisBasis secondConfig secondP secondSmall secondDomain secondLookupEnough
      secondLookupCapacity secondLookupRadius secondFallback secondBehavior secondPairEnough secondLookupSmall secondBuild secondDistance
      secondBase secondLinearEpsilon secondGeometry secondLinearSmall secondLinearCalibrated accumulators factory accBasis accEnough accCapacity
      accRadius accEpsilon accGeometry accSmall accCalibrated monoLength evaluations monoBase zeroFirstSmall zeroRoundSmall zeroNodesEnough rotations zeroBase
      monoBasis monoEnough monoCapacity monoRadius monoEpsilon monoGeometry monoSmall monoCalibrated
      zeroBasis zeroEnough zeroCapacity zeroRadius zeroEpsilon zeroGeometry zeroSmall zeroCalibrated restricted
  · exact PackedPBSKeySwitchInputProbability.safe_original_input_final_bound (P := InputP)
      length psi primitive family inputs base (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs) nodesEnough radix linearBase dummy (PackedPBSRequestComparisonStage.scheme hs.encoding config p small domain fallback behavior pairEnough build) (PackedPBSRequestComparisonStage.scheme hs.encoding secondConfig secondP secondSmall secondDomain secondFallback secondBehavior secondPairEnough secondBuild) secondBase accumulators factory monoLength evaluations monoBase zeroFirstSmall zeroRoundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height))
      inputBasis inputEnough inputCapacity inputRadius inputEpsilon inputGeometry inputSmallDistance inputCalibrated compatible restricted audited

/-- The derived complete arithmetic rate and final exception pay ONE charge
for the entire executed prefix, including all earlier rejected paths. This is
still a generic execution hazard, not a physical attacker-work theorem. -/
theorem native_risk_or_bad_bound [Fintype Digest] [NeZero m] [NeZero b] [NeZero accM] [NeZero accB] [NeZero monoM] [NeZero zeroM] [NeZero inputM] [NeZero inputB]
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
    [∀ root : Root (2*d+1) (∑ i, repetitions i), NeZero (packedWidth (e+padding) (e+helperPadding) root)] [∀ root, NeZero (layout g root).m]
    (analysisBasis : ∀ root, Module.Basis (Fin (packedWidth (e + padding) (e + helperPadding) root)) (ZMod q) (L root))
    (config : MixedWidthRequestSharedLookup.Parameters (ZMod q) K LookupMessage Memory Cfg Input Digest Memory HelperMemory
      e padding lookupC lookupRow (2*d+1) requests widths sizes repetitions mode)
    (p : ℕ) [CharP K p] (small : 2 * 1 ≤ p)
    (domain : ∀ root, Fin (2 ^ heights (tag root)) ↪ (ZMod q))
    (lookupEnough : ∀ root, g.m root ≤ Fintype.card (Fin (2 ^ heights (tag root))))
    (lookupCapacity : ∀ root, 2 ^ g.suffix root ≤ g.m root * packedWidth (e + padding) (e + helperPadding) root) (lookupRadius : Root (2*d+1) (∑ i, repetitions i) → ℕ)
    (fallback : Packet (ZMod q) K (e + padding) (2*d+1) (lookupC + lookupRow) (∑ i, repetitions i))
    (behavior : MixedWidthStagedSharedLookup.Emission (2*d+1) (∑ i, repetitions i) Digest Memory (RequestLookupPairMiddle.Memory K HelperMemory repetitions) →
      MixedWidthSharedLookupPCS.Selection (ZMod q) K Memory (e + padding) (2*d+1) (∑ i, repetitions i) (lookupC + lookupRow) →
      (root : Root (2*d+1) (∑ i, repetitions i)) → Protocol (ZMod q) Input Digest Cfg LookupResponse Memory (packedWidth (e + padding) (e + helperPadding)) heights tag (layout g) root)
    (pairEnough : ∀ index, sizes index + 1 < Fintype.card K) (lookupSmall : ∀ index, config.active index < p)
    (build : MixedWidthStagedSharedLookup.SourceEmission (2*d+1) Digest Memory → RequestLookupPairs.Vector K repetitions →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (MixedWidthStagedSharedLookup.HelperEmission (∑ i, repetitions i) Digest HelperMemory))
    (distance : ∀ root, (lookupRadius root : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := L root) (domain root)) (g.m root) :
        Set (Fin (2 ^ heights (tag root)) → L root)) : ℚ≥0) / 3)
    [∀ root : Root (2*d+1) (∑ i, secondRepetitions i), NeZero (packedWidth (secondE+secondPadding) (secondE+secondHelperPadding) root)] [∀ root, NeZero (layout secondG root).m]
    (secondAnalysisBasis : ∀ root, Module.Basis (Fin (packedWidth (secondE + secondPadding) (secondE + secondHelperPadding) root)) (ZMod q) (SecondL root))
    (secondConfig : MixedWidthRequestSharedLookup.Parameters (ZMod q) SecondK SecondLookupMessage Memory Cfg Input Digest Memory SecondHelperMemory
      secondE secondPadding secondLookupC secondLookupRow (2*d+1) secondRequests secondWidths secondSizes secondRepetitions secondMode)
    (secondP : ℕ) [CharP SecondK secondP] (secondSmall : 2 * 1 ≤ secondP)
    (secondDomain : ∀ root, Fin (2 ^ heights (secondTag root)) ↪ (ZMod q))
    (secondLookupEnough : ∀ root, secondG.m root ≤ Fintype.card (Fin (2 ^ heights (secondTag root))))
    (secondLookupCapacity : ∀ root, 2 ^ secondG.suffix root ≤ secondG.m root * packedWidth (secondE + secondPadding) (secondE + secondHelperPadding) root) (secondLookupRadius : Root (2*d+1) (∑ i, secondRepetitions i) → ℕ)
    (secondFallback : Packet (ZMod q) SecondK (secondE + secondPadding) (2*d+1) (secondLookupC + secondLookupRow) (∑ i, secondRepetitions i))
    (secondBehavior : MixedWidthStagedSharedLookup.Emission (2*d+1) (∑ i, secondRepetitions i) Digest Memory (RequestLookupPairMiddle.Memory SecondK SecondHelperMemory secondRepetitions) →
      MixedWidthSharedLookupPCS.Selection (ZMod q) SecondK Memory (secondE + secondPadding) (2*d+1) (∑ i, secondRepetitions i) (secondLookupC + secondLookupRow) →
      (root : Root (2*d+1) (∑ i, secondRepetitions i)) → Protocol (ZMod q) Input Digest Cfg SecondLookupResponse Memory (packedWidth (secondE + secondPadding) (secondE + secondHelperPadding)) heights secondTag (layout secondG) root)
    (secondPairEnough : ∀ index, secondSizes index + 1 < Fintype.card SecondK) (secondLookupSmall : ∀ index, secondConfig.active index < secondP)
    (secondBuild : MixedWidthStagedSharedLookup.SourceEmission (2*d+1) Digest Memory → RequestLookupPairs.Vector SecondK secondRepetitions →
      OracleComp (SharedSequence.Shared Cfg Input Digest) (MixedWidthStagedSharedLookup.HelperEmission (∑ i, secondRepetitions i) Digest SecondHelperMemory))
    (secondDistance : ∀ root, (secondLookupRadius root : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := SecondL root) (secondDomain root)) (secondG.m root) :
        Set (Fin (2 ^ heights (secondTag root)) → SecondL root)) : ℚ≥0) / 3)
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

    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = Skeleton.perfect (heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base
        (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs) nodesEnough radix linearBase)) :
    let ns := AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs
    let first := PackedPBSRequestComparisonStage.scheme hs.encoding config p small domain fallback behavior pairEnough build
    let second := PackedPBSRequestComparisonStage.scheme hs.encoding secondConfig secondP secondSmall secondDomain secondFallback secondBehavior secondPairEnough secondBuild
    Pr{let outcome ← (PackedPBSKeySwitchInput.witness length psi primitive family inputs base ns nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase zeroFirstSmall zeroRoundSmall zeroNodesEnough rotations zeroBase
      accLength inputReference inputLength inputSmall inputBase (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[
      (((fun previous => (((fun prior => ((((PackedPBSReconstructionJointBound.Risk length psi primitive family inputs base ns nodesEnough radix linearBase dummy nativeCapacity nativeRadius prior.1.1.1.1 ∨
          ∃ compared, prior.1.1.1.2 = some compared ∧
            MixedWidthOwnedRequestSources.OriginalFalse hs.encoding dummy config domain lookupCapacity lookupRadius compared ∧
              compared.2.2.1.2.accepted = true) ∨
        ∃ compared child, prior.1.1.1.2 = some compared ∧ prior.1.1.2 = some child ∧
          AmbientLinear.OriginalRisk heights
            (PackedPBSSecondReconstruction.reconstruction family inputs ns nodesEnough radix secondBase compared.2.2.1.2.memory)
            dummy nativeCapacity nativeRadius child) ∨
        ∃ compared, prior.1.2 = some compared ∧
          (MixedWidthOwnedRequestSources.OriginalFalse hs.encoding dummy secondConfig secondDomain secondLookupCapacity secondLookupRadius compared ∧
            compared.2.2.1.2.accepted = true)) ∨ ∃ compared child, prior.1.2 = some compared ∧ prior.2 = some child ∧
        OwnedAmbientAccumulator.OriginalRisk heights
          (PackedPBSAccumulator.accumulator family inputs ns accumulators factory compared.2.2.1.2.memory)
          dummy accCapacity accRadius child)) previous.1.1) ∨ ((∃ ntts, previous.1.2 = some ntts ∧ AmbientNTTSequenceSoundness.AnyOriginalRisk (AmbientMonomialNTT.factory hs.encoding monoLength psi primitive (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase) heights dummy monoCapacity monoRadius ntts.1) ∨
        (∃ ntts product, previous.1.2 = some ntts ∧ previous.2 = some product ∧ AmbientPublicZeroCheck.OriginalRisk heights (MonomialPublicZeroCheck.stage zeroFirstSmall zeroRoundSmall zeroNodesEnough hs.encoding psi rotations evaluations.roots (zeroBase ntts.1.memory)) dummy zeroCapacity zeroRadius product)))) outcome.1) ∨ (∃ product acc input, outcome.1.2 = some product ∧ outcome.1.1.1.2 = some acc ∧ outcome.2 = some input ∧
        AmbientKnownInput.OriginalRisk heights
          (KeySwitchKnownInput.stage inputSmall hs.encoding inputReference.root inputLength
            (AccumulatorEndpoint.value accLength (factory acc.1.1.2).context) (inputBase product.2.1.2.memory)) dummy inputCapacity inputRadius input)) ∨ CheckpointCollision.Bad (AmbientMatrixSource.Shape heights) (PackedPBSKeySwitchInput.finalState first second outcome)] ≤
      ((((((((PackedPBSHadamardNTTJointBound.rate (K := P) hs nativeRadius + ((List.finRange (2*d+1)).map nttEpsilon).sum) + linearEpsilon) +
        (RequestLookupPairMiddle.errorBudget (Fintype.card K) widths sizes config.active repetitions +
          (error K mode (lookupC+lookupRow) + MixedWidthStagedSharedLookup.pcsError (d := e) (padding := padding) (helperPadding := helperPadding) (g := g) L domain lookupRadius))) + secondLinearEpsilon) +
        (RequestLookupPairMiddle.errorBudget (Fintype.card SecondK) secondWidths secondSizes secondConfig.active secondRepetitions +
          (error SecondK secondMode (secondLookupC+secondLookupRow) + MixedWidthStagedSharedLookup.pcsError (d := secondE) (padding := secondPadding) (helperPadding := secondHelperPadding) (g := secondG) SecondL secondDomain secondLookupRadius))) + accEpsilon) + ((monoEpsilon false + monoEpsilon true) + zeroEpsilon)) + inputEpsilon) +
    ExpectedHazard.charge (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (AmbientMatrixSource.Shape heights))
      (CheckpointCollision.loss unifSpec (AmbientMatrixSource.Shape heights))
      (PackedPBSKeySwitchInput.program length psi primitive family inputs base ns nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase zeroFirstSmall zeroRoundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase)
      (CheckpointExecution.empty (AmbientMatrixSource.Shape heights)) := by
  have safe := native_safe_joint_bound length psi primitive family inputs base firstSmall roundSmall hadNodes hs
    nodesEnough radix linearBase nativeBasis dummy nativeEnough nativeCapacity nativeRadius nttEpsilon linearEpsilon nttEncoding linearEncoding
    hadSmall nttSmall linearSmall nttCalibrated linearCalibrated analysisBasis config p small domain lookupEnough lookupCapacity lookupRadius
    fallback behavior pairEnough lookupSmall build distance secondAnalysisBasis secondConfig secondP secondSmall secondDomain secondLookupEnough
    secondLookupCapacity secondLookupRadius secondFallback secondBehavior secondPairEnough secondLookupSmall secondBuild secondDistance
    secondBase secondLinearEpsilon secondGeometry secondLinearSmall secondLinearCalibrated accumulators factory accBasis accEnough accCapacity
    accRadius accEpsilon accGeometry accSmall accCalibrated monoLength evaluations monoBase zeroFirstSmall zeroRoundSmall zeroNodesEnough rotations zeroBase
    monoBasis monoEnough monoCapacity monoRadius monoEpsilon monoGeometry monoSmall monoCalibrated
    zeroBasis zeroEnough zeroCapacity zeroRadius zeroEpsilon zeroGeometry zeroSmall zeroCalibrated accLength inputReference inputLength inputSmall inputBase
    inputBasis inputEnough inputCapacity inputRadius inputEpsilon inputGeometry inputSmallDistance inputCalibrated restricted
  have failure := PackedPBSKeySwitchInput.final_bad_le_charge length psi primitive family inputs base (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs) nodesEnough radix linearBase dummy (PackedPBSRequestComparisonStage.scheme hs.encoding config p small domain fallback behavior pairEnough build) (PackedPBSRequestComparisonStage.scheme hs.encoding secondConfig secondP secondSmall secondDomain secondFallback secondBehavior secondPairEnough secondBuild) secondBase accumulators factory monoLength evaluations monoBase zeroFirstSmall zeroRoundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase restricted
  exact PackedPBSMonomialNativeJointBound.risk_or_bad_of_safe _ _ _ _ _ safe failure

end
end FormalProof4FHE.HasteBoots.PackedPBSKeySwitchInputNativeJointBound
