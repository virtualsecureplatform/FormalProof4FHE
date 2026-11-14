module
public import FormalProof4FHE.HasteBoots.PackedPBSRectangularComparisonPrefixBound
public import FormalProof4FHE.HasteBoots.HonestKeySetupReceipts
public import FormalProof4FHE.HasteBoots.ExecutedHonestProductKey
public import FormalProof4FHE.HasteBoots.PackedPBSNativeSetupSafeBound
public import FormalProof4FHE.HasteBoots.HonestJointKeySetup
public import FormalProof4FHE.HasteBoots.HonestJointSetupScope
@[expose] public section

/-! Derive the native safe arithmetic rate after actual control-key and
key-switch setup, retaining their shared populated oracle history. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSNativeJointSetupSafeBound
open OracleSpec OracleComp BinaryTree Matrix MerkleTreeMultiExtractability
open NativeRootMessage (Digest)
open PackedPBSFirstComparisons (priorState finalState)
open scoped Classical BigOperators
open FormalProof4FHE.HasteBoots.InteractiveAuthenticatedOpening
open FormalProof4FHE.HasteBoots.RectangularVariableWidthOpening
open FormalProof4FHE.HasteBoots.PaddedMixedWidthLookupOpeningFamily
open FormalProof4FHE.HasteBoots.MixedWidthSharedLookupPCSAlgebra
noncomputable section
variable {q log d b c r k n front suffix m queries height : ℕ} [nativeInstance1 : Fact q.Prime]
  {Input Cfg Response Memory CommitMemory : Type}
  [nativeInstance2 : DecidableEq Input] [nativeInstance3 : DecidableEq Digest] [nativeInstance4 : SampleableType Digest]
  [nativeInstance5 : SampleableType (Fin k → Fin r → ZMod q)] [nativeInstance6 : SampleableType (Fin b → ZMod q)]
  [nativeInstance7 : SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [nativeInstance8 : SampleableType (Fin queries → Fin (2^height))]
  [nativeInstance9 : SampleableType (PackedZeroReduction.Points (ZMod q) n b)] [nativeInstance10 : SampleableType (Fin b → Fin b → ZMod q)]
variable {P : Type} [nativeInstance11 : Field P] [nativeInstance12 : Algebra (ZMod q) P] [nativeInstance13 : Fintype P] [nativeInstance14 : DecidableEq P]
  [nativeInstance15 : SampleableType (ZMod q)] [nativeInstance16 : SampleableType (Fin r → ZMod q)]
  [nativeInstance17 : SampleableType ((Fin (2^front) × Fin b) → P)]
  [nativeInstance18 : SampleableType (Fin n → ZMod q)] [nativeInstance19 : SampleableType (Fin b → ((Fin b → ZMod q) × ZMod q))]

variable {K LookupMessage LookupResponse HelperMemory : Type}
  [nativeInstance20 : Field K] [nativeInstance21 : Algebra (ZMod q) K] [nativeInstance22 : Fintype K] [nativeInstance23 : DecidableEq K] [nativeInstance24 : SampleableType K]
  {e padding helperPadding lookupC lookupRow requests : ℕ}
  {widths sizes repetitions : Fin requests → ℕ} {mode : Mode}
  {heights : Cfg → ℕ} {tag : Root (2*d+1) (∑ i, repetitions i) → Cfg}
  {g : Geometry lookupC lookupRow (2*d+1) (∑ i, repetitions i)}
  {symbolWidth : Root (2*d+1) (∑ i, repetitions i) → ℕ}
  [nativeInstance25 : SampleableType (Fin 1 → K)] [nativeInstance26 : SampleableType (Fin (lookupC+lookupRow) → K)]
  [nativeInstance27 : ∀ root, SampleableType (TestMatrix (ZMod q) (2 ^ (layout g root).front) (packedWidth (e+padding) (e+helperPadding) root))]
  [nativeInstance28 : ∀ root, SampleableType (Fin (layout g root).queries → Fin (2 ^ heights (tag root)))]
  [nativeInstance29 : ∀ root, SampleableType ((Fin (2 ^ (layout g root).front) × Fin (packedWidth (e+padding) (e+helperPadding) root)) → ZMod q)]

variable {SecondK SecondLookupMessage SecondLookupResponse SecondHelperMemory : Type}
  [nativeInstance30 : Field SecondK] [nativeInstance31 : Algebra (ZMod q) SecondK] [nativeInstance32 : Fintype SecondK] [nativeInstance33 : DecidableEq SecondK] [nativeInstance34 : SampleableType SecondK]
  {secondE secondPadding secondHelperPadding secondLookupC secondLookupRow secondRequests : ℕ}
  {secondWidths secondSizes secondRepetitions : Fin secondRequests → ℕ} {secondMode : Mode}
  {secondTag : Root (2*d+1) (∑ i, secondRepetitions i) → Cfg}
  {secondG : Geometry secondLookupC secondLookupRow (2*d+1) (∑ i, secondRepetitions i)}
  {secondSymbolWidth : Root (2*d+1) (∑ i, secondRepetitions i) → ℕ}
  [nativeInstance35 : SampleableType (Fin 1 → SecondK)] [nativeInstance36 : SampleableType (Fin (secondLookupC+secondLookupRow) → SecondK)]
  [nativeInstance37 : ∀ root, SampleableType (TestMatrix (ZMod q) (2 ^ (layout secondG root).front) (packedWidth (secondE+secondPadding) (secondE+secondHelperPadding) root))]
  [nativeInstance38 : ∀ root, SampleableType (Fin (layout secondG root).queries → Fin (2 ^ heights (secondTag root)))]
  [nativeInstance39 : ∀ root, SampleableType ((Fin (2 ^ (layout secondG root).front) × Fin (packedWidth (secondE+secondPadding) (secondE+secondHelperPadding) root)) → ZMod q)]

variable {AccResponse AccP : Type} {accB accC accR accFront accSuffix accM accQueries accHeight : ℕ}
  [nativeInstance40 : Field AccP] [nativeInstance41 : Algebra (ZMod q) AccP] [nativeInstance42 : Fintype AccP] [nativeInstance43 : DecidableEq AccP]
  [nativeInstance44 : SampleableType (Fin accB → ZMod q)]
  [nativeInstance45 : SampleableType (TestMatrix (ZMod q) (2^accFront) accB)]
  [nativeInstance46 : SampleableType (Fin accQueries → Fin (2^accHeight))]
  [nativeInstance47 : SampleableType ((Fin (2^accFront) × Fin accB) → AccP)]

local notation "AccScheme" => AmbientAccumulator.Scheme (ZMod q) Input Digest Cfg AccResponse Memory Memory
  accB accC accR accFront accSuffix accM accQueries accHeight

variable {lanes cells rows rounds : ℕ}
variable {MonoResponse MonoCommitMemory : Type} {monoK monoFront monoSuffix monoM monoQueries monoHeight : ℕ}
  [nativeInstance48 : SampleableType (Fin monoK → Fin (rows+1) → ZMod q)] [nativeInstance49 : SampleableType (Fin (2^lanes) → ZMod q)]
  [nativeInstance50 : SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^monoFront) (2^lanes))]
  [nativeInstance51 : SampleableType (Fin monoQueries → Fin (2^monoHeight))]

local notation "MonoScheme" => AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg MonoResponse Memory MonoCommitMemory
  (2^lanes) cells (rows+1) monoK monoFront monoSuffix monoM monoQueries monoHeight

variable {ZeroResponse ZeroCommitMemory : Type} {zeroFront zeroSuffix zeroM zeroQueries zeroHeight : ℕ}
  [nativeInstance52 : SampleableType (Fin (cells+rows) → ZMod q)]
  [nativeInstance53 : SampleableType (PackedZeroReduction.Points (ZMod q) (cells+rows) (2^lanes))]
  [nativeInstance54 : SampleableType (Fin (2^lanes) → Fin (2^lanes) → ZMod q)]
  [nativeInstance55 : SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))]
  [nativeInstance56 : SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^zeroFront) (2^lanes))]
  [nativeInstance57 : SampleableType (Fin zeroQueries → Fin (2^zeroHeight))]

local notation "ZeroScheme" => AuthenticatedPublicZeroCheck.Scheme (ZMod q) Bool Unit Bool
  (Fin (2^lanes) → Fin ((2*(2^lanes)-1)*2+1) → ZMod q) (Fin ((2*(2^lanes)-1)*3+1) → ZMod q)
  Input Digest Cfg ZeroResponse Memory ZeroCommitMemory (2^lanes) (cells+rows) zeroFront zeroSuffix zeroM zeroQueries zeroHeight

variable {MonoP ZeroP : Type}
  [nativeInstance58 : Field MonoP] [nativeInstance59 : Algebra (ZMod q) MonoP] [nativeInstance60 : Fintype MonoP] [nativeInstance61 : DecidableEq MonoP]
  [nativeInstance62 : Field ZeroP] [nativeInstance63 : Algebra (ZMod q) ZeroP] [nativeInstance64 : Fintype ZeroP] [nativeInstance65 : DecidableEq ZeroP]
  [nativeInstance66 : SampleableType (Fin (rows+1) → ZMod q)]
  [nativeInstance67 : SampleableType ((Fin (2^monoFront) × Fin (2^lanes)) → MonoP)]
  [nativeInstance68 : SampleableType ((Fin (2^zeroFront) × Fin (2^lanes)) → ZeroP)]

variable {InputResponse InputCommitMemory : Type} {inputB inputC inputFront inputSuffix inputM inputQueries inputHeight : ℕ}
  [nativeInstance69 : SampleableType (Fin inputB → ZMod q)]
  [nativeInstance70 : SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^inputFront) inputB)]
  [nativeInstance71 : SampleableType (Fin inputQueries → Fin (2^inputHeight))]
local notation "InputScheme" => AmbientKnownInput.Scheme (ZMod q) Input Digest Cfg InputResponse Memory InputCommitMemory
  inputB (1+inputC) inputFront inputSuffix inputM inputQueries inputHeight

variable {InputP : Type} [nativeInstance72 : Field InputP] [nativeInstance73 : Algebra (ZMod q) InputP] [nativeInstance74 : Fintype InputP] [nativeInstance75 : DecidableEq InputP]
  [nativeInstance76 : SampleableType ((Fin (2^inputFront) × Fin inputB) → InputP)]

variable {FinalResponse FinalCommitMemory FinalP : Type} {finalD finalB finalC : ℕ}
  [nativeInstance77 : Field FinalP] [nativeInstance78 : Algebra (ZMod q) FinalP] [nativeInstance79 : Fintype FinalP] [nativeInstance80 : DecidableEq FinalP]
  [nativeInstance81 : SampleableType (Fin finalB → Fin 1 → ZMod q)] [nativeInstance82 : SampleableType (Fin finalB → ZMod q)]
  [nativeInstance83 : SampleableType (Fin 1 → ZMod q)]

variable {ProductResponse ProductCommitMemory ProductP : Type}
  [nativeInstance84 : Field ProductP] [nativeInstance85 : Algebra (ZMod q) ProductP] [nativeInstance86 : Fintype ProductP] [nativeInstance87 : DecidableEq ProductP]
  [nativeInstance88 : SampleableType (PackedZeroReduction.Points (ZMod q) finalC finalB)]
  [nativeInstance89 : SampleableType (Fin finalB → Fin finalB → ZMod q)]
  [nativeInstance90 : SampleableType (Fin finalC → ZMod q)] [nativeInstance91 : SampleableType (Fin finalB → ((Fin finalB → ZMod q) × ZMod q))]

variable {ReconstructionResponse ReconstructionCommitMemory ReconstructionP : Type}
  [nativeInstance92 : Field ReconstructionP] [nativeInstance93 : Algebra (ZMod q) ReconstructionP] [nativeInstance94 : Fintype ReconstructionP] [nativeInstance95 : DecidableEq ReconstructionP]

variable {CompareK CompareMessage CompareHelperMemory CompareResponse : Type}
  [nativeInstance96 : Field CompareK] [nativeInstance97 : Algebra (ZMod q) CompareK] [nativeInstance98 : Fintype CompareK] [nativeInstance99 : DecidableEq CompareK] [nativeInstance100 : SampleableType CompareK]
  {compareE comparePadding compareHelperPadding compareC compareRow compareRequests : ℕ}
  {compareWidths compareSizes compareRepetitions : Fin compareRequests → ℕ} {compareMode : Mode}
  {compareTag : PaddedMixedWidthLookupOpeningFamily.Root (2*finalD+1) (∑ i, compareRepetitions i) → Cfg}
  {compareG : PaddedMixedWidthLookupOpeningFamily.Geometry compareC compareRow (2*finalD+1) (∑ i, compareRepetitions i)}
  {compareSymbolWidth : PaddedMixedWidthLookupOpeningFamily.Root (2*finalD+1) (∑ i, compareRepetitions i) → ℕ}
  [nativeInstance101 : SampleableType (Fin 1 → CompareK)] [nativeInstance102 : SampleableType (Fin (compareC+compareRow) → CompareK)]

local notation "PriorBefore" => PackedPBSKeySwitchReconstruction.BeforeFinalReconstruction (q := q) (Response := Response) (CommitMemory := CommitMemory)
  (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix) (queries := queries) (height := height)
  (AccResponse := AccResponse) (accB := accB) (accC := accC) (accR := accR) (accFront := accFront) (accQueries := accQueries) (accHeight := accHeight)
  (MonoResponse := MonoResponse) (MonoCommitMemory := MonoCommitMemory) (lanes := lanes) (cells := cells) (rows := rows)
  (monoK := monoK) (monoFront := monoFront) (monoQueries := monoQueries) (monoHeight := monoHeight)
  (ZeroResponse := ZeroResponse) (ZeroCommitMemory := ZeroCommitMemory) (zeroFront := zeroFront) (zeroQueries := zeroQueries) (zeroHeight := zeroHeight)
  (InputResponse := InputResponse) (InputCommitMemory := InputCommitMemory) (inputB := inputB) (inputC := inputC)
  (inputFront := inputFront) (inputQueries := inputQueries) (inputHeight := inputHeight)

  (FinalResponse := FinalResponse) (FinalCommitMemory := FinalCommitMemory) (finalD := finalD) (finalB := finalB) (finalC := finalC)

  (ProductResponse := ProductResponse) (ProductCommitMemory := ProductCommitMemory)

section Native

variable [nativeInstance103 : NeZero m] [nativeInstance104 : NeZero b] [nativeInstance105 : NeZero accM] [nativeInstance106 : NeZero accB] [nativeInstance107 : NeZero monoM] [nativeInstance108 : NeZero zeroM] [nativeInstance109 : NeZero inputM] [nativeInstance110 : NeZero inputB]
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
    [nativeInstance111 : ∀ root : Root (2*d+1) (∑ i, repetitions i), NeZero (symbolWidth root)] [nativeInstance112 : ∀ root, NeZero (layout g root).m]
    (config : RectangularRequestLookup.Parameters (ZMod q) K LookupMessage Memory Cfg Input Digest Memory HelperMemory
      e padding lookupC lookupRow (2*d+1) requests widths sizes repetitions mode)
    (p : ℕ) [nativeInstance113 : CharP K p] (small : 2 * 1 ≤ p)
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
    [nativeInstance114 : ∀ root : Root (2*d+1) (∑ i, secondRepetitions i), NeZero (secondSymbolWidth root)] [nativeInstance115 : ∀ root, NeZero (layout secondG root).m]
    (secondConfig : RectangularRequestLookup.Parameters (ZMod q) SecondK SecondLookupMessage Memory Cfg Input Digest Memory SecondHelperMemory
      secondE secondPadding secondLookupC secondLookupRow (2*d+1) secondRequests secondWidths secondSizes secondRepetitions secondMode)
    (secondP : ℕ) [nativeInstance116 : CharP SecondK secondP] (secondSmall : 2 * 1 ≤ secondP)
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
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → (AmbientAccumulator.Scheme (ZMod q) Input Digest Cfg AccResponse Memory Memory
  accB accC accR accFront accSuffix accM accQueries accHeight))
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
    (monoBase : Bool → Memory → (AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg MonoResponse Memory MonoCommitMemory
  (2^lanes) cells (rows+1) monoK monoFront monoSuffix monoM monoQueries monoHeight))
    (zeroFirstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (zeroRoundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (zeroNodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (zeroBase : Memory → (AuthenticatedPublicZeroCheck.Scheme (ZMod q) Bool Unit Bool
  (Fin (2^lanes) → Fin ((2*(2^lanes)-1)*2+1) → ZMod q) (Fin ((2*(2^lanes)-1)*3+1) → ZMod q)
  Input Digest Cfg ZeroResponse Memory ZeroCommitMemory (2^lanes) (cells+rows) zeroFront zeroSuffix zeroM zeroQueries zeroHeight))
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
    (inputLength : 2^inputC*inputB = 2^log) (inputSmall : 2*inputB ≤ q) (inputBase : Memory → (AmbientKnownInput.Scheme (ZMod q) Input Digest Cfg InputResponse Memory InputCommitMemory
  inputB (1+inputC) inputFront inputSuffix inputM inputQueries inputHeight))
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
    [nativeInstance117 : ∀ index memory side, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((finalBase index memory).code side).front) finalB)]
    [nativeInstance118 : ∀ index memory side, SampleableType (Fin ((finalBase index memory).code side).queries → Fin (2^heights ((finalBase index memory).tag side)))]
    [nativeInstance119 : NeZero finalB] [nativeInstance120 : ∀ index memory side, NeZero ((finalBase index memory).code side).m]
    [nativeInstance121 : ∀ index memory side, SampleableType ((Fin (2^((finalBase index memory).code side).front) × Fin finalB) → FinalP)]
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
    [nativeInstance122 : ∀ memory factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((productBase memory).code factor).front) finalB)]
    [nativeInstance123 : ∀ memory factor, SampleableType (Fin ((productBase memory).code factor).queries → Fin (2^heights ((productBase memory).tag factor)))]
    [nativeInstance124 : ∀ memory factor, NeZero ((productBase memory).code factor).m]
    [nativeInstance125 : ∀ memory factor, SampleableType ((Fin (2^((productBase memory).code factor).front) × Fin finalB) → ProductP)]
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

    (finalRadix : ZMod q)
    (reconstructionBase : Memory → PaddedLinear.Scheme (ZMod q) Input Digest Cfg ReconstructionResponse Memory ReconstructionCommitMemory heights (2*finalD+2) finalB (1+finalC))
    [nativeInstance126 : ∀ memory factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((reconstructionBase memory).code factor).front) finalB)]
    [nativeInstance127 : ∀ memory factor, SampleableType (Fin ((reconstructionBase memory).code factor).queries → Fin (2^heights ((reconstructionBase memory).tag factor)))]
    [nativeInstance128 : ∀ memory factor, NeZero ((reconstructionBase memory).code factor).m]
    [nativeInstance129 : ∀ memory factor, SampleableType ((Fin (2^((reconstructionBase memory).code factor).front) × Fin finalB) → ReconstructionP)]
    (reconstructionBasis : Module.Basis (Fin finalB) (ZMod q) ReconstructionP)
    (reconstructionEnough : ∀ memory factor, ((reconstructionBase memory).code factor).m ≤ Fintype.card (Fin (2^heights ((reconstructionBase memory).tag factor))))
    (reconstructionCapacity : ∀ memory factor, 2^((reconstructionBase memory).code factor).suffix ≤ ((reconstructionBase memory).code factor).m*finalB)
    (reconstructionRadius : Memory → Fin (2*finalD+2) → ℕ) (reconstructionEpsilon : ENNReal)
    (reconstructionSmall : ∀ memory factor, (reconstructionRadius memory factor : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := ReconstructionP) ((reconstructionBase memory).domain factor))
        ((reconstructionBase memory).code factor).m : Set (Fin (2^heights ((reconstructionBase memory).tag factor)) → ReconstructionP)) : ℚ≥0)/3)
    (reconstructionCalibrated : ∀ memory,
      ((1+finalC : ℕ) : ENNReal)*(((((2*finalB-1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^finalB)) +
      ((AuthenticatedLinear.factors (2*finalD+2)).map (fun factor => JointMatrixOpening.error (K := ReconstructionP) (m := ((reconstructionBase memory).code factor).m)
        (b := finalB) (queries := ((reconstructionBase memory).code factor).queries) ((reconstructionBase memory).domain factor) (reconstructionRadius memory factor))).sum ≤ reconstructionEpsilon)

    (restricted : ∀ controlRoots : Fin (2*d) → Digest, CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = Skeleton.perfect (heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive (HonestControlKeySetup.withKeys family controlRoots) inputs base
        (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs) nodesEnough radix linearBase))
    [nativeInstance130 : ∀ root : PaddedMixedWidthLookupOpeningFamily.Root (2*finalD+1) (∑ i, compareRepetitions i), NeZero (compareSymbolWidth root)]
    [nativeInstance131 : ∀ root, NeZero (PaddedMixedWidthLookupOpeningFamily.layout compareG root).m]
    [nativeInstance132 : ∀ root, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^(PaddedMixedWidthLookupOpeningFamily.layout compareG root).front) (PaddedMixedWidthLookupOpeningFamily.packedWidth (compareE+comparePadding) (compareE+compareHelperPadding) root))]
    [nativeInstance133 : ∀ root, SampleableType (Fin (PaddedMixedWidthLookupOpeningFamily.layout compareG root).queries → Fin (2^heights (compareTag root)))]
    [nativeInstance134 : ∀ root, SampleableType ((Fin (2^(PaddedMixedWidthLookupOpeningFamily.layout compareG root).front) × Fin (PaddedMixedWidthLookupOpeningFamily.packedWidth (compareE+comparePadding) (compareE+compareHelperPadding) root)) → ZMod q)]
    (compareTags : ∀ memory source, (reconstructionBase memory).tag (PackedPBSComparisonReferences.linearSlot source) = compareTag (.inl source))
    (compareConfig : Memory → RectangularRequestLookup.Parameters (ZMod q) CompareK CompareMessage Memory Cfg Input Digest Memory CompareHelperMemory
      compareE comparePadding compareC compareRow (2*finalD+1) compareRequests compareWidths compareSizes compareRepetitions compareMode)
    (compareP : ℕ) [nativeInstance135 : CharP CompareK compareP] (compareSmall : 2*1 ≤ compareP)
    (compareDomain : ∀ root, Fin (2^heights (compareTag root)) ↪ (ZMod q))
    (compareEnough : ∀ root, compareG.m root ≤ Fintype.card (Fin (2^heights (compareTag root))))
    (compareCapacity : ∀ root, 2^compareG.suffix root ≤ compareG.m root * compareSymbolWidth root)
    (compareRadius : PaddedMixedWidthLookupOpeningFamily.Root (2*finalD+1) (∑ i, compareRepetitions i) → ℕ)
    (compareFallback : PaddedMixedWidthLookupOpeningFamily.Packet (ZMod q) CompareK (compareE+comparePadding) (2*finalD+1) (compareC+compareRow) (∑ i, compareRepetitions i))
    (compareBehavior : Memory → RectangularStagedSharedLookup.Emission (2*finalD+1) (∑ i, compareRepetitions i) Digest Memory
        (RequestLookupPairMiddle.Memory CompareK CompareHelperMemory compareRepetitions) →
      RectangularSharedLookupPCS.Selection (ZMod q) CompareK Memory (compareE+comparePadding) (2*finalD+1) (∑ i, compareRepetitions i) (compareC+compareRow) →
      (root : PaddedMixedWidthLookupOpeningFamily.Root (2*finalD+1) (∑ i, compareRepetitions i)) →
      RectangularVariableWidthOpening.Protocol (ZMod q) Input Digest Cfg CompareResponse Memory (PaddedMixedWidthLookupOpeningFamily.packedWidth (compareE+comparePadding) (compareE+compareHelperPadding)) compareSymbolWidth heights compareTag (PaddedMixedWidthLookupOpeningFamily.layout compareG) root)
    (comparePairEnough : ∀ index, compareSizes index+1 < Fintype.card CompareK)
    (compareLookupSmall : ∀ memory index, (compareConfig memory).active index < compareP)
    (compareBuild : Memory → RectangularStagedSharedLookup.SourceEmission (2*finalD+1) Digest Memory →
      RequestLookupPairs.Vector CompareK compareRepetitions → OracleComp (SharedSequence.Shared Cfg Input Digest)
        (RectangularStagedSharedLookup.HelperEmission (∑ i, compareRepetitions i) Digest CompareHelperMemory))
    (compareDistanceLarge : ∀ root, compareRadius root < Fintype.card (ZMod q))
    (compareDistance : ∀ root, 3*compareRadius root <
      Code.minDist (BlockCode.code (compareDomain root) (compareG.m root) (compareSymbolWidth root) :
        Set (Fin (2^heights (compareTag root)) → Fin (compareSymbolWidth root) → ZMod q)))

variable {setupC : ℕ}
  (original : NativeKeySwitch.Key q (2^(setupC+2)) finalD)
  (setupParameters : Fin finalD → RecordedPaddedSource.Parameters (ZMod q) Cfg heights 4)
  (controlParameters : Fin (2*d) → RecordedPaddedSource.Parameters (ZMod q) Cfg heights (2^lanes))
  (controls : HonestControlKeyTable.Controls (q := q) (cells := cells) (lanes := lanes) (rows := rows) (levels := d))

/-- The native safe-tail verifier starts from the supplied populated state
and literal root maps; it performs no further key setup. -/
def continuation (controlRoots : Fin (2*d) → Digest) (keyRoots : Fin finalD → Digest)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) :
    ProbComp Prop := do
  let ns := AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs
  let first := RectangularPBSComparisonStage.scheme (helperPadding := helperPadding) hs.encoding config p small domain fallback behavior pairEnough build
  let second := RectangularPBSComparisonStage.scheme (helperPadding := secondHelperPadding) hs.encoding secondConfig secondP secondSmall secondDomain secondFallback secondBehavior secondPairEnough secondBuild
  let comparison := (fun memory => RectangularPBSComparisonStage.scheme (helperPadding := compareHelperPadding) (heights := first.heights) ns.encoding (compareConfig memory) compareP compareSmall compareDomain compareFallback (compareBehavior memory) comparePairEnough (compareBuild memory))
  (fun outcome => (KeySwitchTailRisk.Risk
        (fun _ => False)
        (fun product acc input => AmbientKnownInput.OriginalRisk heights
          (KeySwitchKnownInput.stage inputSmall hs.encoding inputReference.root inputLength
            (AccumulatorEndpoint.value accLength (factory acc.1.1.2).context)
            (inputBase product.2.1.2.memory)) dummy inputCapacity inputRadius input)
        (fun ntts => PaddedNTTSequenceSoundness.AnyOriginalRisk
          (KeySwitchPaddedNTT.factory finalBase hs.encoding (ExecutedHonestProductKey.withKeys finalFamily keyRoots) finalNodes finalLength psi primitive)
          hs.encoding dummy finalCapacity finalRadius ntts.1)
        (fun product => PaddedZeroCheck.OriginalRisk
          (KeySwitchPaddedProduct.stage (productBase product.1) hs.encoding (ExecutedHonestProductKey.withKeys finalFamily keyRoots) productFirstSmall productRoundSmall productNodes)
          dummy (productCapacity product.1) (productRadius product.1) product.2)
        (fun reconstructed => PaddedLinear.OriginalRisk
          (KeySwitchPaddedReconstruction.stage (reconstructionBase reconstructed.1) hs.encoding inputReference (ExecutedHonestProductKey.withKeys finalFamily keyRoots) finalNodes finalRadix)
          dummy (reconstructionCapacity reconstructed.1) (reconstructionRadius reconstructed.1) reconstructed.2)
        (fun result => RectangularOwnedRequestSources.OriginalFalse hs.encoding dummy
          (compareConfig result.1.1) compareDomain compareCapacity compareRadius result.2)
        (fun result => result.2.2.2.1.2.accepted = true) outcome) ∧
      ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights)
        (RetainedPaddedComparison.finalState
          (fun memory => KeySwitchPaddedReconstruction.stage (reconstructionBase memory)
            ns.encoding inputReference (ExecutedHonestProductKey.withKeys finalFamily keyRoots) finalNodes finalRadix)
          comparison (PackedPBSKeySwitchReconstruction.finalState first second finalBase productBase reconstructionBase) outcome)) <$> (PackedPBSKeySwitchComparisons.witness length psi primitive (HonestControlKeySetup.withKeys family controlRoots) inputs base ns nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase zeroFirstSmall zeroRoundSmall zeroNodesEnough rotations zeroBase
      accLength inputReference inputLength inputSmall inputBase (ExecutedHonestProductKey.withKeys finalFamily keyRoots) finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase finalRadix reconstructionBase comparison initial)

/-- Both actual key setups precede the verifier in one chronological history. -/
def experiment : ProbComp Prop := do
  let built ← HonestJointKeySetup.witness controlParameters setupParameters hs.encoding psi controls original
    (QueryImpl.ofLift unifSpec ProbComp) dummy (RecordedSourceCoherence.Shape Cfg height)
  @continuation q log d b c r k n front suffix m queries height nativeInstance1 Input Cfg Response Memory CommitMemory nativeInstance2 nativeInstance3 nativeInstance4 nativeInstance5 nativeInstance6 nativeInstance7 nativeInstance8 nativeInstance9 nativeInstance10 K LookupMessage LookupResponse HelperMemory nativeInstance20 nativeInstance21 nativeInstance22 nativeInstance23 nativeInstance24 e padding helperPadding lookupC lookupRow requests widths sizes repetitions mode heights tag g symbolWidth nativeInstance25 nativeInstance26 nativeInstance27 nativeInstance28 SecondK SecondLookupMessage SecondLookupResponse SecondHelperMemory nativeInstance30 nativeInstance31 nativeInstance32 nativeInstance33 nativeInstance34 secondE secondPadding secondHelperPadding secondLookupC secondLookupRow secondRequests secondWidths secondSizes secondRepetitions secondMode secondTag secondG secondSymbolWidth nativeInstance35 nativeInstance36 nativeInstance37 nativeInstance38 AccResponse accB accC accR accFront accSuffix accM accQueries accHeight nativeInstance44 nativeInstance45 nativeInstance46 lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight nativeInstance48 nativeInstance49 nativeInstance50 nativeInstance51 ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight nativeInstance53 nativeInstance54 nativeInstance56 nativeInstance57 InputResponse InputCommitMemory inputB inputC inputFront inputSuffix inputM inputQueries inputHeight nativeInstance69 nativeInstance70 nativeInstance71 FinalResponse FinalCommitMemory finalD finalB finalC nativeInstance81 nativeInstance82 ProductResponse ProductCommitMemory nativeInstance88 nativeInstance89 ReconstructionResponse ReconstructionCommitMemory CompareK CompareMessage CompareHelperMemory CompareResponse nativeInstance96 nativeInstance97 nativeInstance98 nativeInstance99 nativeInstance100 compareE comparePadding compareHelperPadding compareC compareRow compareRequests compareWidths compareSizes compareRepetitions compareMode compareTag compareG compareSymbolWidth nativeInstance101 nativeInstance102 length psi primitive family inputs base firstSmall roundSmall hadNodes hs nodesEnough radix linearBase dummy config p nativeInstance113 small domain fallback behavior pairEnough build secondConfig secondP nativeInstance116 secondSmall secondDomain secondFallback secondBehavior secondPairEnough secondBuild secondBase accumulators factory monoLength evaluations monoBase zeroFirstSmall zeroRoundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase inputCapacity inputRadius finalFamily finalNodes finalLength finalBase nativeInstance117 finalCapacity finalRadius productFirstSmall productRoundSmall productNodes productBase nativeInstance122 productCapacity productRadius finalRadix reconstructionBase nativeInstance126 reconstructionCapacity reconstructionRadius nativeInstance132 compareConfig compareP nativeInstance135 compareSmall compareDomain compareCapacity compareRadius compareFallback compareBehavior comparePairEnough compareBuild built.1.1 built.2.1 built.2.2

/-- The same experiment uses the full raw verifier's setup geometry and
transports its actual populated setup end to the fixed-initial verifier. -/
def ambientExperiment : ProbComp Prop := do
  let built ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
    (AmbientMatrixSource.Shape heights))
    (HonestJointKeySetup.program controlParameters setupParameters hs.encoding psi controls original)).run
      (CheckpointExecution.empty (AmbientMatrixSource.Shape heights))
  @continuation q log d b c r k n front suffix m queries height nativeInstance1 Input Cfg Response Memory CommitMemory nativeInstance2 nativeInstance3 nativeInstance4 nativeInstance5 nativeInstance6 nativeInstance7 nativeInstance8 nativeInstance9 nativeInstance10 K LookupMessage LookupResponse HelperMemory nativeInstance20 nativeInstance21 nativeInstance22 nativeInstance23 nativeInstance24 e padding helperPadding lookupC lookupRow requests widths sizes repetitions mode heights tag g symbolWidth nativeInstance25 nativeInstance26 nativeInstance27 nativeInstance28 SecondK SecondLookupMessage SecondLookupResponse SecondHelperMemory nativeInstance30 nativeInstance31 nativeInstance32 nativeInstance33 nativeInstance34 secondE secondPadding secondHelperPadding secondLookupC secondLookupRow secondRequests secondWidths secondSizes secondRepetitions secondMode secondTag secondG secondSymbolWidth nativeInstance35 nativeInstance36 nativeInstance37 nativeInstance38 AccResponse accB accC accR accFront accSuffix accM accQueries accHeight nativeInstance44 nativeInstance45 nativeInstance46 lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight nativeInstance48 nativeInstance49 nativeInstance50 nativeInstance51 ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight nativeInstance53 nativeInstance54 nativeInstance56 nativeInstance57 InputResponse InputCommitMemory inputB inputC inputFront inputSuffix inputM inputQueries inputHeight nativeInstance69 nativeInstance70 nativeInstance71 FinalResponse FinalCommitMemory finalD finalB finalC nativeInstance81 nativeInstance82 ProductResponse ProductCommitMemory nativeInstance88 nativeInstance89 ReconstructionResponse ReconstructionCommitMemory CompareK CompareMessage CompareHelperMemory CompareResponse nativeInstance96 nativeInstance97 nativeInstance98 nativeInstance99 nativeInstance100 compareE comparePadding compareHelperPadding compareC compareRow compareRequests compareWidths compareSizes compareRepetitions compareMode compareTag compareG compareSymbolWidth nativeInstance101 nativeInstance102 length psi primitive family inputs base firstSmall roundSmall hadNodes hs nodesEnough radix linearBase dummy config p nativeInstance113 small domain fallback behavior pairEnough build secondConfig secondP nativeInstance116 secondSmall secondDomain secondFallback secondBehavior secondPairEnough secondBuild secondBase accumulators factory monoLength evaluations monoBase zeroFirstSmall zeroRoundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase inputCapacity inputRadius finalFamily finalNodes finalLength finalBase nativeInstance117 finalCapacity finalRadius productFirstSmall productRoundSmall productNodes productBase nativeInstance122 productCapacity productRadius finalRadix reconstructionBase nativeInstance126 reconstructionCapacity reconstructionRadius nativeInstance132 compareConfig compareP nativeInstance135 compareSmall compareDomain compareCapacity compareRadius compareFallback compareBehavior comparePairEnough compareBuild built.1.1 built.1.2
    (CheckpointShapeTransport.state (AmbientMatrixSource.Shape heights) (RecordedSourceCoherence.Shape Cfg height) built.2)

omit nativeInstance15 nativeInstance16 nativeInstance18 nativeInstance19 nativeInstance29 nativeInstance39 nativeInstance52 nativeInstance55 nativeInstance66 nativeInstance83 nativeInstance90 nativeInstance91 nativeInstance103 nativeInstance104 nativeInstance105 nativeInstance106 nativeInstance107 nativeInstance108 nativeInstance109 nativeInstance110 nativeInstance111 nativeInstance112 nativeInstance114 nativeInstance115 nativeInstance118 nativeInstance119 nativeInstance120 nativeInstance123 nativeInstance124 nativeInstance127 nativeInstance128 nativeInstance130 nativeInstance131 nativeInstance133 nativeInstance134 in
/-- Both native experiments use the same actual combined setup and verifier
history; the change of setup geometry introduces no reset or new randomness. -/
theorem experiment_eq_ambient :
    (@experiment q log d b c r k n front suffix m queries height nativeInstance1 Input Cfg Response Memory CommitMemory nativeInstance2 nativeInstance3 nativeInstance4 nativeInstance5 nativeInstance6 nativeInstance7 nativeInstance8 nativeInstance9 nativeInstance10 K LookupMessage LookupResponse HelperMemory nativeInstance20 nativeInstance21 nativeInstance22 nativeInstance23 nativeInstance24 e padding helperPadding lookupC lookupRow requests widths sizes repetitions mode heights tag g symbolWidth nativeInstance25 nativeInstance26 nativeInstance27 nativeInstance28 SecondK SecondLookupMessage SecondLookupResponse SecondHelperMemory nativeInstance30 nativeInstance31 nativeInstance32 nativeInstance33 nativeInstance34 secondE secondPadding secondHelperPadding secondLookupC secondLookupRow secondRequests secondWidths secondSizes secondRepetitions secondMode secondTag secondG secondSymbolWidth nativeInstance35 nativeInstance36 nativeInstance37 nativeInstance38 AccResponse accB accC accR accFront accSuffix accM accQueries accHeight nativeInstance44 nativeInstance45 nativeInstance46 lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight nativeInstance48 nativeInstance49 nativeInstance50 nativeInstance51 ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight nativeInstance53 nativeInstance54 nativeInstance56 nativeInstance57 InputResponse InputCommitMemory inputB inputC inputFront inputSuffix inputM inputQueries inputHeight nativeInstance69 nativeInstance70 nativeInstance71 FinalResponse FinalCommitMemory finalD finalB finalC nativeInstance81 nativeInstance82 ProductResponse ProductCommitMemory nativeInstance88 nativeInstance89 ReconstructionResponse ReconstructionCommitMemory CompareK CompareMessage CompareHelperMemory CompareResponse nativeInstance96 nativeInstance97 nativeInstance98 nativeInstance99 nativeInstance100 compareE comparePadding compareHelperPadding compareC compareRow compareRequests compareWidths compareSizes compareRepetitions compareMode compareTag compareG compareSymbolWidth nativeInstance101 nativeInstance102 length psi primitive family inputs base firstSmall roundSmall hadNodes hs nodesEnough radix linearBase dummy config p nativeInstance113 small domain fallback behavior pairEnough build secondConfig secondP nativeInstance116 secondSmall secondDomain secondFallback secondBehavior secondPairEnough secondBuild secondBase accumulators factory monoLength evaluations monoBase zeroFirstSmall zeroRoundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase inputCapacity inputRadius finalFamily finalNodes finalLength finalBase nativeInstance117 finalCapacity finalRadius productFirstSmall productRoundSmall productNodes productBase nativeInstance122 productCapacity productRadius finalRadix reconstructionBase nativeInstance126 reconstructionCapacity reconstructionRadius nativeInstance132 compareConfig compareP nativeInstance135 compareSmall compareDomain compareCapacity compareRadius compareFallback compareBehavior comparePairEnough compareBuild setupC original setupParameters controlParameters controls) = (@ambientExperiment q log d b c r k n front suffix m queries height nativeInstance1 Input Cfg Response Memory CommitMemory nativeInstance2 nativeInstance3 nativeInstance4 nativeInstance5 nativeInstance6 nativeInstance7 nativeInstance8 nativeInstance9 nativeInstance10 K LookupMessage LookupResponse HelperMemory nativeInstance20 nativeInstance21 nativeInstance22 nativeInstance23 nativeInstance24 e padding helperPadding lookupC lookupRow requests widths sizes repetitions mode heights tag g symbolWidth nativeInstance25 nativeInstance26 nativeInstance27 nativeInstance28 SecondK SecondLookupMessage SecondLookupResponse SecondHelperMemory nativeInstance30 nativeInstance31 nativeInstance32 nativeInstance33 nativeInstance34 secondE secondPadding secondHelperPadding secondLookupC secondLookupRow secondRequests secondWidths secondSizes secondRepetitions secondMode secondTag secondG secondSymbolWidth nativeInstance35 nativeInstance36 nativeInstance37 nativeInstance38 AccResponse accB accC accR accFront accSuffix accM accQueries accHeight nativeInstance44 nativeInstance45 nativeInstance46 lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight nativeInstance48 nativeInstance49 nativeInstance50 nativeInstance51 ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight nativeInstance53 nativeInstance54 nativeInstance56 nativeInstance57 InputResponse InputCommitMemory inputB inputC inputFront inputSuffix inputM inputQueries inputHeight nativeInstance69 nativeInstance70 nativeInstance71 FinalResponse FinalCommitMemory finalD finalB finalC nativeInstance81 nativeInstance82 ProductResponse ProductCommitMemory nativeInstance88 nativeInstance89 ReconstructionResponse ReconstructionCommitMemory CompareK CompareMessage CompareHelperMemory CompareResponse nativeInstance96 nativeInstance97 nativeInstance98 nativeInstance99 nativeInstance100 compareE comparePadding compareHelperPadding compareC compareRow compareRequests compareWidths compareSizes compareRepetitions compareMode compareTag compareG compareSymbolWidth nativeInstance101 nativeInstance102 length psi primitive family inputs base firstSmall roundSmall hadNodes hs nodesEnough radix linearBase dummy config p nativeInstance113 small domain fallback behavior pairEnough build secondConfig secondP nativeInstance116 secondSmall secondDomain secondFallback secondBehavior secondPairEnough secondBuild secondBase accumulators factory monoLength evaluations monoBase zeroFirstSmall zeroRoundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase inputCapacity inputRadius finalFamily finalNodes finalLength finalBase nativeInstance117 finalCapacity finalRadius productFirstSmall productRoundSmall productNodes productBase nativeInstance122 productCapacity productRadius finalRadix reconstructionBase nativeInstance126 reconstructionCapacity reconstructionRadius nativeInstance132 compareConfig compareP nativeInstance135 compareSmall compareDomain compareCapacity compareRadius compareFallback compareBehavior comparePairEnough compareBuild setupC original setupParameters controlParameters controls) := by
  unfold ambientExperiment
  rw [←HonestJointSetupScope.witness_from_empty controlParameters setupParameters hs.encoding psi controls original
    (QueryImpl.ofLift unifSpec ProbComp) dummy (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape heights)]
  simp only [bind_map_left]
  unfold experiment
  apply bind_congr
  intro built
  rw [HonestSetupContinuation.state_roundtrip]


include q log d b c r k n front suffix m queries height nativeInstance1 Input Cfg Response Memory CommitMemory nativeInstance2 nativeInstance3 nativeInstance4 nativeInstance5 nativeInstance6 nativeInstance7 nativeInstance8 nativeInstance9 nativeInstance10 P nativeInstance11 nativeInstance12 nativeInstance13 nativeInstance14 nativeInstance15 nativeInstance16 nativeInstance17 nativeInstance18 nativeInstance19 K LookupMessage LookupResponse HelperMemory nativeInstance20 nativeInstance21 nativeInstance22 nativeInstance23 nativeInstance24 e padding helperPadding lookupC lookupRow requests widths sizes repetitions mode heights tag g symbolWidth nativeInstance25 nativeInstance26 nativeInstance27 nativeInstance28 nativeInstance29 SecondK SecondLookupMessage SecondLookupResponse SecondHelperMemory nativeInstance30 nativeInstance31 nativeInstance32 nativeInstance33 nativeInstance34 secondE secondPadding secondHelperPadding secondLookupC secondLookupRow secondRequests secondWidths secondSizes secondRepetitions secondMode secondTag secondG secondSymbolWidth nativeInstance35 nativeInstance36 nativeInstance37 nativeInstance38 nativeInstance39 AccResponse AccP accB accC accR accFront accSuffix accM accQueries accHeight nativeInstance40 nativeInstance41 nativeInstance42 nativeInstance43 nativeInstance44 nativeInstance45 nativeInstance46 nativeInstance47 lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight nativeInstance48 nativeInstance49 nativeInstance50 nativeInstance51 ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight nativeInstance52 nativeInstance53 nativeInstance54 nativeInstance55 nativeInstance56 nativeInstance57 MonoP ZeroP nativeInstance58 nativeInstance59 nativeInstance60 nativeInstance61 nativeInstance62 nativeInstance63 nativeInstance64 nativeInstance65 nativeInstance66 nativeInstance67 nativeInstance68 InputResponse InputCommitMemory inputB inputC inputFront inputSuffix inputM inputQueries inputHeight nativeInstance69 nativeInstance70 nativeInstance71 InputP nativeInstance72 nativeInstance73 nativeInstance74 nativeInstance75 nativeInstance76 FinalResponse FinalCommitMemory FinalP finalD finalB finalC nativeInstance77 nativeInstance78 nativeInstance79 nativeInstance80 nativeInstance81 nativeInstance82 nativeInstance83 ProductResponse ProductCommitMemory ProductP nativeInstance84 nativeInstance85 nativeInstance86 nativeInstance87 nativeInstance88 nativeInstance89 nativeInstance90 nativeInstance91 ReconstructionResponse ReconstructionCommitMemory ReconstructionP nativeInstance92 nativeInstance93 nativeInstance94 nativeInstance95 CompareK CompareMessage CompareHelperMemory CompareResponse nativeInstance96 nativeInstance97 nativeInstance98 nativeInstance99 nativeInstance100 compareE comparePadding compareHelperPadding compareC compareRow compareRequests compareWidths compareSizes compareRepetitions compareMode compareTag compareG compareSymbolWidth nativeInstance101 nativeInstance102 nativeInstance103 nativeInstance104 nativeInstance105 nativeInstance106 nativeInstance107 nativeInstance108 nativeInstance109 nativeInstance110 length psi primitive family inputs base firstSmall roundSmall hadNodes hs nodesEnough radix linearBase nativeBasis dummy nativeEnough nativeCapacity nativeRadius nttEpsilon linearEpsilon nttEncoding linearEncoding hadSmall nttSmall linearSmall nttCalibrated linearCalibrated nativeInstance111 nativeInstance112 config p nativeInstance113 small domain lookupEnough lookupCapacity lookupRadius fallback behavior pairEnough lookupSmall build distanceLarge distance nativeInstance114 nativeInstance115 secondConfig secondP nativeInstance116 secondSmall secondDomain secondLookupEnough secondLookupCapacity secondLookupRadius secondFallback secondBehavior secondPairEnough secondLookupSmall secondBuild secondDistanceLarge secondDistance secondBase secondLinearEpsilon secondGeometry secondLinearSmall secondLinearCalibrated accumulators factory accBasis accEnough accCapacity accRadius accEpsilon accGeometry accSmall accCalibrated monoLength evaluations monoBase zeroFirstSmall zeroRoundSmall zeroNodesEnough rotations zeroBase monoBasis monoEnough monoCapacity monoRadius monoEpsilon monoGeometry monoSmall monoCalibrated zeroBasis zeroEnough zeroCapacity zeroRadius zeroEpsilon zeroGeometry zeroSmall zeroCalibrated accLength inputReference inputLength inputSmall inputBase inputBasis inputEnough inputCapacity inputRadius inputEpsilon inputGeometry inputSmallDistance inputCalibrated finalFamily finalNodes finalLength finalBase nativeInstance117 nativeInstance118 nativeInstance119 nativeInstance120 nativeInstance121 finalBasis finalEnough finalCapacity finalRadius finalEpsilon finalSmall finalCalibrated productFirstSmall productRoundSmall productNodes productBase nativeInstance122 nativeInstance123 nativeInstance124 nativeInstance125 productBasis productEnough productCapacity productRadius productEpsilon productSmall productCalibrated finalRadix reconstructionBase nativeInstance126 nativeInstance127 nativeInstance128 nativeInstance129 reconstructionBasis reconstructionEnough reconstructionCapacity reconstructionRadius reconstructionEpsilon reconstructionSmall reconstructionCalibrated restricted nativeInstance130 nativeInstance131 nativeInstance132 nativeInstance133 nativeInstance134 compareTags compareConfig compareP nativeInstance135 compareSmall compareDomain compareEnough compareCapacity compareRadius compareFallback compareBehavior comparePairEnough compareLookupSmall compareBuild compareDistanceLarge compareDistance in
/-- Derive the native safe-tail arithmetic rate after both actual key setups.
The initial audit and geometry compatibility come from that same execution;
no incoming history certificate or component probability bound is assumed. -/
theorem native_safe_tail_bound :
    prEvent (@experiment q log d b c r k n front suffix m queries height nativeInstance1 Input Cfg Response Memory CommitMemory nativeInstance2 nativeInstance3 nativeInstance4 nativeInstance5 nativeInstance6 nativeInstance7 nativeInstance8 nativeInstance9 nativeInstance10 K LookupMessage LookupResponse HelperMemory nativeInstance20 nativeInstance21 nativeInstance22 nativeInstance23 nativeInstance24 e padding helperPadding lookupC lookupRow requests widths sizes repetitions mode heights tag g symbolWidth nativeInstance25 nativeInstance26 nativeInstance27 nativeInstance28 SecondK SecondLookupMessage SecondLookupResponse SecondHelperMemory nativeInstance30 nativeInstance31 nativeInstance32 nativeInstance33 nativeInstance34 secondE secondPadding secondHelperPadding secondLookupC secondLookupRow secondRequests secondWidths secondSizes secondRepetitions secondMode secondTag secondG secondSymbolWidth nativeInstance35 nativeInstance36 nativeInstance37 nativeInstance38 AccResponse accB accC accR accFront accSuffix accM accQueries accHeight nativeInstance44 nativeInstance45 nativeInstance46 lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight nativeInstance48 nativeInstance49 nativeInstance50 nativeInstance51 ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight nativeInstance53 nativeInstance54 nativeInstance56 nativeInstance57 InputResponse InputCommitMemory inputB inputC inputFront inputSuffix inputM inputQueries inputHeight nativeInstance69 nativeInstance70 nativeInstance71 FinalResponse FinalCommitMemory finalD finalB finalC nativeInstance81 nativeInstance82 ProductResponse ProductCommitMemory nativeInstance88 nativeInstance89 ReconstructionResponse ReconstructionCommitMemory CompareK CompareMessage CompareHelperMemory CompareResponse nativeInstance96 nativeInstance97 nativeInstance98 nativeInstance99 nativeInstance100 compareE comparePadding compareHelperPadding compareC compareRow compareRequests compareWidths compareSizes compareRepetitions compareMode compareTag compareG compareSymbolWidth nativeInstance101 nativeInstance102 length psi primitive family inputs base firstSmall roundSmall hadNodes hs nodesEnough radix linearBase dummy config p nativeInstance113 small domain fallback behavior pairEnough build secondConfig secondP nativeInstance116 secondSmall secondDomain secondFallback secondBehavior secondPairEnough secondBuild secondBase accumulators factory monoLength evaluations monoBase zeroFirstSmall zeroRoundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase inputCapacity inputRadius finalFamily finalNodes finalLength finalBase nativeInstance117 finalCapacity finalRadius productFirstSmall productRoundSmall productNodes productBase nativeInstance122 productCapacity productRadius finalRadix reconstructionBase nativeInstance126 reconstructionCapacity reconstructionRadius nativeInstance132 compareConfig compareP nativeInstance135 compareSmall compareDomain compareCapacity compareRadius compareFallback compareBehavior comparePairEnough compareBuild setupC original setupParameters controlParameters controls) ≤ (((((((((((PackedPBSHadamardNTTJointBound.rate (K := P) hs nativeRadius + ((List.finRange (2*d+1)).map nttEpsilon).sum) + linearEpsilon) +
        (RequestLookupPairMiddle.errorBudget (Fintype.card K) widths sizes config.active repetitions +
          (error K mode (lookupC+lookupRow) + RectangularStagedSharedLookup.pcsError (d := e) (padding := padding) (helperPadding := helperPadding) (g := g) (symbolWidth := symbolWidth) domain lookupRadius))) + secondLinearEpsilon) +
        (RequestLookupPairMiddle.errorBudget (Fintype.card SecondK) secondWidths secondSizes secondConfig.active secondRepetitions +
          (error SecondK secondMode (secondLookupC+secondLookupRow) + RectangularStagedSharedLookup.pcsError (d := secondE) (padding := secondPadding) (helperPadding := secondHelperPadding) (g := secondG) (symbolWidth := secondSymbolWidth) secondDomain secondLookupRadius))) + accEpsilon) + ((monoEpsilon false + monoEpsilon true) + zeroEpsilon)) + inputEpsilon) + ((List.finRange (finalD+1)).map finalEpsilon).sum) + productEpsilon) + reconstructionEpsilon) + (RequestLookupPairMiddle.errorBudget (Fintype.card CompareK) compareWidths compareSizes
        (fun _ => 2^(compareC+compareRow)) compareRepetitions +
      (error CompareK compareMode (compareC+compareRow) + RectangularStagedSharedLookup.pcsError
        (d := compareE) (padding := comparePadding) (helperPadding := compareHelperPadding)
        (g := compareG) (symbolWidth := compareSymbolWidth) compareDomain compareRadius)) := by
  rw [experiment]
  apply PackedPBSNativeSetupSafeBound.prop_bind_le
  intro built supported
  have initialized := HonestJointKeySetup.initialized controlParameters setupParameters hs.encoding psi controls original
    (QueryImpl.ofLift unifSpec ProbComp) dummy (RecordedSourceCoherence.Shape Cfg height) built supported
  have bounded := @PackedPBSRectangularComparisonPrefixBound.native_safe_tail_bound q log d b c r k n front suffix m queries height nativeInstance1 Input Cfg Response Memory CommitMemory nativeInstance2 nativeInstance3 nativeInstance4 nativeInstance5 nativeInstance6 nativeInstance7 nativeInstance8 nativeInstance9 nativeInstance10 P nativeInstance11 nativeInstance12 nativeInstance13 nativeInstance14 nativeInstance15 nativeInstance16 nativeInstance17 nativeInstance18 nativeInstance19 K LookupMessage LookupResponse HelperMemory nativeInstance20 nativeInstance21 nativeInstance22 nativeInstance23 nativeInstance24 e padding helperPadding lookupC lookupRow requests widths sizes repetitions mode heights tag g symbolWidth nativeInstance25 nativeInstance26 nativeInstance27 nativeInstance28 nativeInstance29 SecondK SecondLookupMessage SecondLookupResponse SecondHelperMemory nativeInstance30 nativeInstance31 nativeInstance32 nativeInstance33 nativeInstance34 secondE secondPadding secondHelperPadding secondLookupC secondLookupRow secondRequests secondWidths secondSizes secondRepetitions secondMode secondTag secondG secondSymbolWidth nativeInstance35 nativeInstance36 nativeInstance37 nativeInstance38 nativeInstance39 AccResponse AccP accB accC accR accFront accSuffix accM accQueries accHeight nativeInstance40 nativeInstance41 nativeInstance42 nativeInstance43 nativeInstance44 nativeInstance45 nativeInstance46 nativeInstance47 lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight nativeInstance48 nativeInstance49 nativeInstance50 nativeInstance51 ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight nativeInstance52 nativeInstance53 nativeInstance54 nativeInstance55 nativeInstance56 nativeInstance57 MonoP ZeroP nativeInstance58 nativeInstance59 nativeInstance60 nativeInstance61 nativeInstance62 nativeInstance63 nativeInstance64 nativeInstance65 nativeInstance66 nativeInstance67 nativeInstance68 InputResponse InputCommitMemory inputB inputC inputFront inputSuffix inputM inputQueries inputHeight nativeInstance69 nativeInstance70 nativeInstance71 InputP nativeInstance72 nativeInstance73 nativeInstance74 nativeInstance75 nativeInstance76 FinalResponse FinalCommitMemory FinalP finalD finalB finalC nativeInstance77 nativeInstance78 nativeInstance79 nativeInstance80 nativeInstance81 nativeInstance82 nativeInstance83 ProductResponse ProductCommitMemory ProductP nativeInstance84 nativeInstance85 nativeInstance86 nativeInstance87 nativeInstance88 nativeInstance89 nativeInstance90 nativeInstance91 ReconstructionResponse ReconstructionCommitMemory ReconstructionP nativeInstance92 nativeInstance93 nativeInstance94 nativeInstance95 CompareK CompareMessage CompareHelperMemory CompareResponse nativeInstance96 nativeInstance97 nativeInstance98 nativeInstance99 nativeInstance100 compareE comparePadding compareHelperPadding compareC compareRow compareRequests compareWidths compareSizes compareRepetitions compareMode compareTag compareG compareSymbolWidth nativeInstance101 nativeInstance102 nativeInstance103 nativeInstance104 nativeInstance105 nativeInstance106 nativeInstance107 nativeInstance108 nativeInstance109 nativeInstance110 length psi primitive (HonestControlKeySetup.withKeys family built.1.1) inputs base firstSmall roundSmall hadNodes hs nodesEnough radix linearBase nativeBasis dummy built.2.2 initialized.2.2.audited (initialized.2.2.compatible (AmbientMatrixSource.Shape heights)) nativeEnough nativeCapacity nativeRadius nttEpsilon linearEpsilon nttEncoding linearEncoding hadSmall nttSmall linearSmall nttCalibrated linearCalibrated nativeInstance111 nativeInstance112 config p nativeInstance113 small domain lookupEnough lookupCapacity lookupRadius fallback behavior pairEnough lookupSmall build distanceLarge distance nativeInstance114 nativeInstance115 secondConfig secondP nativeInstance116 secondSmall secondDomain secondLookupEnough secondLookupCapacity secondLookupRadius secondFallback secondBehavior secondPairEnough secondLookupSmall secondBuild secondDistanceLarge secondDistance secondBase secondLinearEpsilon secondGeometry secondLinearSmall secondLinearCalibrated accumulators factory accBasis accEnough accCapacity accRadius accEpsilon accGeometry accSmall accCalibrated monoLength evaluations monoBase zeroFirstSmall zeroRoundSmall zeroNodesEnough rotations zeroBase monoBasis monoEnough monoCapacity monoRadius monoEpsilon monoGeometry monoSmall monoCalibrated zeroBasis zeroEnough zeroCapacity zeroRadius zeroEpsilon zeroGeometry zeroSmall zeroCalibrated accLength inputReference inputLength inputSmall inputBase inputBasis inputEnough inputCapacity inputRadius inputEpsilon inputGeometry inputSmallDistance inputCalibrated (ExecutedHonestProductKey.withKeys finalFamily built.2.1) finalNodes finalLength finalBase nativeInstance117 nativeInstance118 nativeInstance119 nativeInstance120 nativeInstance121 finalBasis finalEnough finalCapacity finalRadius finalEpsilon finalSmall finalCalibrated productFirstSmall productRoundSmall productNodes productBase nativeInstance122 nativeInstance123 nativeInstance124 nativeInstance125 productBasis productEnough productCapacity productRadius productEpsilon productSmall productCalibrated finalRadix reconstructionBase nativeInstance126 nativeInstance127 nativeInstance128 nativeInstance129 reconstructionBasis reconstructionEnough reconstructionCapacity reconstructionRadius reconstructionEpsilon reconstructionSmall reconstructionCalibrated (restricted built.1.1) nativeInstance130 nativeInstance131 nativeInstance132 nativeInstance133 nativeInstance134 compareTags compareConfig compareP nativeInstance135 compareSmall compareDomain compareEnough compareCapacity compareRadius compareFallback compareBehavior comparePairEnough compareLookupSmall compareBuild compareDistanceLarge compareDistance
  exact bounded

include q log d b c r k n front suffix m queries height nativeInstance1 Input Cfg Response Memory CommitMemory nativeInstance2 nativeInstance3 nativeInstance4 nativeInstance5 nativeInstance6 nativeInstance7 nativeInstance8 nativeInstance9 nativeInstance10 P nativeInstance11 nativeInstance12 nativeInstance13 nativeInstance14 nativeInstance15 nativeInstance16 nativeInstance17 nativeInstance18 nativeInstance19 K LookupMessage LookupResponse HelperMemory nativeInstance20 nativeInstance21 nativeInstance22 nativeInstance23 nativeInstance24 e padding helperPadding lookupC lookupRow requests widths sizes repetitions mode heights tag g symbolWidth nativeInstance25 nativeInstance26 nativeInstance27 nativeInstance28 nativeInstance29 SecondK SecondLookupMessage SecondLookupResponse SecondHelperMemory nativeInstance30 nativeInstance31 nativeInstance32 nativeInstance33 nativeInstance34 secondE secondPadding secondHelperPadding secondLookupC secondLookupRow secondRequests secondWidths secondSizes secondRepetitions secondMode secondTag secondG secondSymbolWidth nativeInstance35 nativeInstance36 nativeInstance37 nativeInstance38 nativeInstance39 AccResponse AccP accB accC accR accFront accSuffix accM accQueries accHeight nativeInstance40 nativeInstance41 nativeInstance42 nativeInstance43 nativeInstance44 nativeInstance45 nativeInstance46 nativeInstance47 lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight nativeInstance48 nativeInstance49 nativeInstance50 nativeInstance51 ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight nativeInstance52 nativeInstance53 nativeInstance54 nativeInstance55 nativeInstance56 nativeInstance57 MonoP ZeroP nativeInstance58 nativeInstance59 nativeInstance60 nativeInstance61 nativeInstance62 nativeInstance63 nativeInstance64 nativeInstance65 nativeInstance66 nativeInstance67 nativeInstance68 InputResponse InputCommitMemory inputB inputC inputFront inputSuffix inputM inputQueries inputHeight nativeInstance69 nativeInstance70 nativeInstance71 InputP nativeInstance72 nativeInstance73 nativeInstance74 nativeInstance75 nativeInstance76 FinalResponse FinalCommitMemory FinalP finalD finalB finalC nativeInstance77 nativeInstance78 nativeInstance79 nativeInstance80 nativeInstance81 nativeInstance82 nativeInstance83 ProductResponse ProductCommitMemory ProductP nativeInstance84 nativeInstance85 nativeInstance86 nativeInstance87 nativeInstance88 nativeInstance89 nativeInstance90 nativeInstance91 ReconstructionResponse ReconstructionCommitMemory ReconstructionP nativeInstance92 nativeInstance93 nativeInstance94 nativeInstance95 CompareK CompareMessage CompareHelperMemory CompareResponse nativeInstance96 nativeInstance97 nativeInstance98 nativeInstance99 nativeInstance100 compareE comparePadding compareHelperPadding compareC compareRow compareRequests compareWidths compareSizes compareRepetitions compareMode compareTag compareG compareSymbolWidth nativeInstance101 nativeInstance102 nativeInstance103 nativeInstance104 nativeInstance105 nativeInstance106 nativeInstance107 nativeInstance108 nativeInstance109 nativeInstance110 length psi primitive family inputs base firstSmall roundSmall hadNodes hs nodesEnough radix linearBase nativeBasis dummy nativeEnough nativeCapacity nativeRadius nttEpsilon linearEpsilon nttEncoding linearEncoding hadSmall nttSmall linearSmall nttCalibrated linearCalibrated nativeInstance111 nativeInstance112 config p nativeInstance113 small domain lookupEnough lookupCapacity lookupRadius fallback behavior pairEnough lookupSmall build distanceLarge distance nativeInstance114 nativeInstance115 secondConfig secondP nativeInstance116 secondSmall secondDomain secondLookupEnough secondLookupCapacity secondLookupRadius secondFallback secondBehavior secondPairEnough secondLookupSmall secondBuild secondDistanceLarge secondDistance secondBase secondLinearEpsilon secondGeometry secondLinearSmall secondLinearCalibrated accumulators factory accBasis accEnough accCapacity accRadius accEpsilon accGeometry accSmall accCalibrated monoLength evaluations monoBase zeroFirstSmall zeroRoundSmall zeroNodesEnough rotations zeroBase monoBasis monoEnough monoCapacity monoRadius monoEpsilon monoGeometry monoSmall monoCalibrated zeroBasis zeroEnough zeroCapacity zeroRadius zeroEpsilon zeroGeometry zeroSmall zeroCalibrated accLength inputReference inputLength inputSmall inputBase inputBasis inputEnough inputCapacity inputRadius inputEpsilon inputGeometry inputSmallDistance inputCalibrated finalFamily finalNodes finalLength finalBase nativeInstance117 nativeInstance118 nativeInstance119 nativeInstance120 nativeInstance121 finalBasis finalEnough finalCapacity finalRadius finalEpsilon finalSmall finalCalibrated productFirstSmall productRoundSmall productNodes productBase nativeInstance122 nativeInstance123 nativeInstance124 nativeInstance125 productBasis productEnough productCapacity productRadius productEpsilon productSmall productCalibrated finalRadix reconstructionBase nativeInstance126 nativeInstance127 nativeInstance128 nativeInstance129 reconstructionBasis reconstructionEnough reconstructionCapacity reconstructionRadius reconstructionEpsilon reconstructionSmall reconstructionCalibrated restricted nativeInstance130 nativeInstance131 nativeInstance132 nativeInstance133 nativeInstance134 compareTags compareConfig compareP nativeInstance135 compareSmall compareDomain compareEnough compareCapacity compareRadius compareFallback compareBehavior comparePairEnough compareLookupSmall compareBuild compareDistanceLarge compareDistance in
/-- The derived native arithmetic rate holds with both setups executed at
the full verifier geometry, preserving their actual shared initial history. -/
theorem native_ambient_safe_tail_bound :
    prEvent (@ambientExperiment q log d b c r k n front suffix m queries height nativeInstance1 Input Cfg Response Memory CommitMemory nativeInstance2 nativeInstance3 nativeInstance4 nativeInstance5 nativeInstance6 nativeInstance7 nativeInstance8 nativeInstance9 nativeInstance10 K LookupMessage LookupResponse HelperMemory nativeInstance20 nativeInstance21 nativeInstance22 nativeInstance23 nativeInstance24 e padding helperPadding lookupC lookupRow requests widths sizes repetitions mode heights tag g symbolWidth nativeInstance25 nativeInstance26 nativeInstance27 nativeInstance28 SecondK SecondLookupMessage SecondLookupResponse SecondHelperMemory nativeInstance30 nativeInstance31 nativeInstance32 nativeInstance33 nativeInstance34 secondE secondPadding secondHelperPadding secondLookupC secondLookupRow secondRequests secondWidths secondSizes secondRepetitions secondMode secondTag secondG secondSymbolWidth nativeInstance35 nativeInstance36 nativeInstance37 nativeInstance38 AccResponse accB accC accR accFront accSuffix accM accQueries accHeight nativeInstance44 nativeInstance45 nativeInstance46 lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight nativeInstance48 nativeInstance49 nativeInstance50 nativeInstance51 ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight nativeInstance53 nativeInstance54 nativeInstance56 nativeInstance57 InputResponse InputCommitMemory inputB inputC inputFront inputSuffix inputM inputQueries inputHeight nativeInstance69 nativeInstance70 nativeInstance71 FinalResponse FinalCommitMemory finalD finalB finalC nativeInstance81 nativeInstance82 ProductResponse ProductCommitMemory nativeInstance88 nativeInstance89 ReconstructionResponse ReconstructionCommitMemory CompareK CompareMessage CompareHelperMemory CompareResponse nativeInstance96 nativeInstance97 nativeInstance98 nativeInstance99 nativeInstance100 compareE comparePadding compareHelperPadding compareC compareRow compareRequests compareWidths compareSizes compareRepetitions compareMode compareTag compareG compareSymbolWidth nativeInstance101 nativeInstance102 length psi primitive family inputs base firstSmall roundSmall hadNodes hs nodesEnough radix linearBase dummy config p nativeInstance113 small domain fallback behavior pairEnough build secondConfig secondP nativeInstance116 secondSmall secondDomain secondFallback secondBehavior secondPairEnough secondBuild secondBase accumulators factory monoLength evaluations monoBase zeroFirstSmall zeroRoundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase inputCapacity inputRadius finalFamily finalNodes finalLength finalBase nativeInstance117 finalCapacity finalRadius productFirstSmall productRoundSmall productNodes productBase nativeInstance122 productCapacity productRadius finalRadix reconstructionBase nativeInstance126 reconstructionCapacity reconstructionRadius nativeInstance132 compareConfig compareP nativeInstance135 compareSmall compareDomain compareCapacity compareRadius compareFallback compareBehavior comparePairEnough compareBuild setupC original setupParameters controlParameters controls) ≤ (((((((((((PackedPBSHadamardNTTJointBound.rate (K := P) hs nativeRadius + ((List.finRange (2*d+1)).map nttEpsilon).sum) + linearEpsilon) +
        (RequestLookupPairMiddle.errorBudget (Fintype.card K) widths sizes config.active repetitions +
          (error K mode (lookupC+lookupRow) + RectangularStagedSharedLookup.pcsError (d := e) (padding := padding) (helperPadding := helperPadding) (g := g) (symbolWidth := symbolWidth) domain lookupRadius))) + secondLinearEpsilon) +
        (RequestLookupPairMiddle.errorBudget (Fintype.card SecondK) secondWidths secondSizes secondConfig.active secondRepetitions +
          (error SecondK secondMode (secondLookupC+secondLookupRow) + RectangularStagedSharedLookup.pcsError (d := secondE) (padding := secondPadding) (helperPadding := secondHelperPadding) (g := secondG) (symbolWidth := secondSymbolWidth) secondDomain secondLookupRadius))) + accEpsilon) + ((monoEpsilon false + monoEpsilon true) + zeroEpsilon)) + inputEpsilon) + ((List.finRange (finalD+1)).map finalEpsilon).sum) + productEpsilon) + reconstructionEpsilon) + (RequestLookupPairMiddle.errorBudget (Fintype.card CompareK) compareWidths compareSizes
        (fun _ => 2^(compareC+compareRow)) compareRepetitions +
      (error CompareK compareMode (compareC+compareRow) + RectangularStagedSharedLookup.pcsError
        (d := compareE) (padding := comparePadding) (helperPadding := compareHelperPadding)
        (g := compareG) (symbolWidth := compareSymbolWidth) compareDomain compareRadius)) := by
  rw [←experiment_eq_ambient]
  exact native_safe_tail_bound (q := q) (log := log) (d := d) (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix) (m := m) (queries := queries) (height := height) (nativeInstance1 := nativeInstance1) (Input := Input) (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory) (nativeInstance2 := nativeInstance2) (nativeInstance3 := nativeInstance3) (nativeInstance4 := nativeInstance4) (nativeInstance5 := nativeInstance5) (nativeInstance6 := nativeInstance6) (nativeInstance7 := nativeInstance7) (nativeInstance8 := nativeInstance8) (nativeInstance9 := nativeInstance9) (nativeInstance10 := nativeInstance10) (P := P) (nativeInstance11 := nativeInstance11) (nativeInstance12 := nativeInstance12) (nativeInstance13 := nativeInstance13) (nativeInstance14 := nativeInstance14) (nativeInstance15 := nativeInstance15) (nativeInstance16 := nativeInstance16) (nativeInstance17 := nativeInstance17) (nativeInstance18 := nativeInstance18) (nativeInstance19 := nativeInstance19) (K := K) (LookupMessage := LookupMessage) (LookupResponse := LookupResponse) (HelperMemory := HelperMemory) (nativeInstance20 := nativeInstance20) (nativeInstance21 := nativeInstance21) (nativeInstance22 := nativeInstance22) (nativeInstance23 := nativeInstance23) (nativeInstance24 := nativeInstance24) (e := e) (padding := padding) (helperPadding := helperPadding) (lookupC := lookupC) (lookupRow := lookupRow) (requests := requests) (widths := widths) (sizes := sizes) (repetitions := repetitions) (mode := mode) (heights := heights) (tag := tag) (g := g) (symbolWidth := symbolWidth) (nativeInstance25 := nativeInstance25) (nativeInstance26 := nativeInstance26) (nativeInstance27 := nativeInstance27) (nativeInstance28 := nativeInstance28) (nativeInstance29 := nativeInstance29) (SecondK := SecondK) (SecondLookupMessage := SecondLookupMessage) (SecondLookupResponse := SecondLookupResponse) (SecondHelperMemory := SecondHelperMemory) (nativeInstance30 := nativeInstance30) (nativeInstance31 := nativeInstance31) (nativeInstance32 := nativeInstance32) (nativeInstance33 := nativeInstance33) (nativeInstance34 := nativeInstance34) (secondE := secondE) (secondPadding := secondPadding) (secondHelperPadding := secondHelperPadding) (secondLookupC := secondLookupC) (secondLookupRow := secondLookupRow) (secondRequests := secondRequests) (secondWidths := secondWidths) (secondSizes := secondSizes) (secondRepetitions := secondRepetitions) (secondMode := secondMode) (secondTag := secondTag) (secondG := secondG) (secondSymbolWidth := secondSymbolWidth) (nativeInstance35 := nativeInstance35) (nativeInstance36 := nativeInstance36) (nativeInstance37 := nativeInstance37) (nativeInstance38 := nativeInstance38) (nativeInstance39 := nativeInstance39) (AccResponse := AccResponse) (AccP := AccP) (accB := accB) (accC := accC) (accR := accR) (accFront := accFront) (accSuffix := accSuffix) (accM := accM) (accQueries := accQueries) (accHeight := accHeight) (nativeInstance40 := nativeInstance40) (nativeInstance41 := nativeInstance41) (nativeInstance42 := nativeInstance42) (nativeInstance43 := nativeInstance43) (nativeInstance44 := nativeInstance44) (nativeInstance45 := nativeInstance45) (nativeInstance46 := nativeInstance46) (nativeInstance47 := nativeInstance47) (lanes := lanes) (cells := cells) (rows := rows) (rounds := rounds) (MonoResponse := MonoResponse) (MonoCommitMemory := MonoCommitMemory) (monoK := monoK) (monoFront := monoFront) (monoSuffix := monoSuffix) (monoM := monoM) (monoQueries := monoQueries) (monoHeight := monoHeight) (nativeInstance48 := nativeInstance48) (nativeInstance49 := nativeInstance49) (nativeInstance50 := nativeInstance50) (nativeInstance51 := nativeInstance51) (ZeroResponse := ZeroResponse) (ZeroCommitMemory := ZeroCommitMemory) (zeroFront := zeroFront) (zeroSuffix := zeroSuffix) (zeroM := zeroM) (zeroQueries := zeroQueries) (zeroHeight := zeroHeight) (nativeInstance52 := nativeInstance52) (nativeInstance53 := nativeInstance53) (nativeInstance54 := nativeInstance54) (nativeInstance55 := nativeInstance55) (nativeInstance56 := nativeInstance56) (nativeInstance57 := nativeInstance57) (MonoP := MonoP) (ZeroP := ZeroP) (nativeInstance58 := nativeInstance58) (nativeInstance59 := nativeInstance59) (nativeInstance60 := nativeInstance60) (nativeInstance61 := nativeInstance61) (nativeInstance62 := nativeInstance62) (nativeInstance63 := nativeInstance63) (nativeInstance64 := nativeInstance64) (nativeInstance65 := nativeInstance65) (nativeInstance66 := nativeInstance66) (nativeInstance67 := nativeInstance67) (nativeInstance68 := nativeInstance68) (InputResponse := InputResponse) (InputCommitMemory := InputCommitMemory) (inputB := inputB) (inputC := inputC) (inputFront := inputFront) (inputSuffix := inputSuffix) (inputM := inputM) (inputQueries := inputQueries) (inputHeight := inputHeight) (nativeInstance69 := nativeInstance69) (nativeInstance70 := nativeInstance70) (nativeInstance71 := nativeInstance71) (InputP := InputP) (nativeInstance72 := nativeInstance72) (nativeInstance73 := nativeInstance73) (nativeInstance74 := nativeInstance74) (nativeInstance75 := nativeInstance75) (nativeInstance76 := nativeInstance76) (FinalResponse := FinalResponse) (FinalCommitMemory := FinalCommitMemory) (FinalP := FinalP) (finalD := finalD) (finalB := finalB) (finalC := finalC) (nativeInstance77 := nativeInstance77) (nativeInstance78 := nativeInstance78) (nativeInstance79 := nativeInstance79) (nativeInstance80 := nativeInstance80) (nativeInstance81 := nativeInstance81) (nativeInstance82 := nativeInstance82) (nativeInstance83 := nativeInstance83) (ProductResponse := ProductResponse) (ProductCommitMemory := ProductCommitMemory) (ProductP := ProductP) (nativeInstance84 := nativeInstance84) (nativeInstance85 := nativeInstance85) (nativeInstance86 := nativeInstance86) (nativeInstance87 := nativeInstance87) (nativeInstance88 := nativeInstance88) (nativeInstance89 := nativeInstance89) (nativeInstance90 := nativeInstance90) (nativeInstance91 := nativeInstance91) (ReconstructionResponse := ReconstructionResponse) (ReconstructionCommitMemory := ReconstructionCommitMemory) (ReconstructionP := ReconstructionP) (nativeInstance92 := nativeInstance92) (nativeInstance93 := nativeInstance93) (nativeInstance94 := nativeInstance94) (nativeInstance95 := nativeInstance95) (CompareK := CompareK) (CompareMessage := CompareMessage) (CompareHelperMemory := CompareHelperMemory) (CompareResponse := CompareResponse) (nativeInstance96 := nativeInstance96) (nativeInstance97 := nativeInstance97) (nativeInstance98 := nativeInstance98) (nativeInstance99 := nativeInstance99) (nativeInstance100 := nativeInstance100) (compareE := compareE) (comparePadding := comparePadding) (compareHelperPadding := compareHelperPadding) (compareC := compareC) (compareRow := compareRow) (compareRequests := compareRequests) (compareWidths := compareWidths) (compareSizes := compareSizes) (compareRepetitions := compareRepetitions) (compareMode := compareMode) (compareTag := compareTag) (compareG := compareG) (compareSymbolWidth := compareSymbolWidth) (nativeInstance101 := nativeInstance101) (nativeInstance102 := nativeInstance102) (nativeInstance103 := nativeInstance103) (nativeInstance104 := nativeInstance104) (nativeInstance105 := nativeInstance105) (nativeInstance106 := nativeInstance106) (nativeInstance107 := nativeInstance107) (nativeInstance108 := nativeInstance108) (nativeInstance109 := nativeInstance109) (nativeInstance110 := nativeInstance110) (length := length) (psi := psi) (primitive := primitive) (family := family) (inputs := inputs) (base := base) (firstSmall := firstSmall) (roundSmall := roundSmall) (hadNodes := hadNodes) (hs := hs) (nodesEnough := nodesEnough) (radix := radix) (linearBase := linearBase) (nativeBasis := nativeBasis) (dummy := dummy) (nativeEnough := nativeEnough) (nativeCapacity := nativeCapacity) (nativeRadius := nativeRadius) (nttEpsilon := nttEpsilon) (linearEpsilon := linearEpsilon) (nttEncoding := nttEncoding) (linearEncoding := linearEncoding) (hadSmall := hadSmall) (nttSmall := nttSmall) (linearSmall := linearSmall) (nttCalibrated := nttCalibrated) (linearCalibrated := linearCalibrated) (nativeInstance111 := nativeInstance111) (nativeInstance112 := nativeInstance112) (config := config) (p := p) (nativeInstance113 := nativeInstance113) (small := small) (domain := domain) (lookupEnough := lookupEnough) (lookupCapacity := lookupCapacity) (lookupRadius := lookupRadius) (fallback := fallback) (behavior := behavior) (pairEnough := pairEnough) (lookupSmall := lookupSmall) (build := build) (distanceLarge := distanceLarge) (distance := distance) (nativeInstance114 := nativeInstance114) (nativeInstance115 := nativeInstance115) (secondConfig := secondConfig) (secondP := secondP) (nativeInstance116 := nativeInstance116) (secondSmall := secondSmall) (secondDomain := secondDomain) (secondLookupEnough := secondLookupEnough) (secondLookupCapacity := secondLookupCapacity) (secondLookupRadius := secondLookupRadius) (secondFallback := secondFallback) (secondBehavior := secondBehavior) (secondPairEnough := secondPairEnough) (secondLookupSmall := secondLookupSmall) (secondBuild := secondBuild) (secondDistanceLarge := secondDistanceLarge) (secondDistance := secondDistance) (secondBase := secondBase) (secondLinearEpsilon := secondLinearEpsilon) (secondGeometry := secondGeometry) (secondLinearSmall := secondLinearSmall) (secondLinearCalibrated := secondLinearCalibrated) (accumulators := accumulators) (factory := factory) (accBasis := accBasis) (accEnough := accEnough) (accCapacity := accCapacity) (accRadius := accRadius) (accEpsilon := accEpsilon) (accGeometry := accGeometry) (accSmall := accSmall) (accCalibrated := accCalibrated) (monoLength := monoLength) (evaluations := evaluations) (monoBase := monoBase) (zeroFirstSmall := zeroFirstSmall) (zeroRoundSmall := zeroRoundSmall) (zeroNodesEnough := zeroNodesEnough) (rotations := rotations) (zeroBase := zeroBase) (monoBasis := monoBasis) (monoEnough := monoEnough) (monoCapacity := monoCapacity) (monoRadius := monoRadius) (monoEpsilon := monoEpsilon) (monoGeometry := monoGeometry) (monoSmall := monoSmall) (monoCalibrated := monoCalibrated) (zeroBasis := zeroBasis) (zeroEnough := zeroEnough) (zeroCapacity := zeroCapacity) (zeroRadius := zeroRadius) (zeroEpsilon := zeroEpsilon) (zeroGeometry := zeroGeometry) (zeroSmall := zeroSmall) (zeroCalibrated := zeroCalibrated) (accLength := accLength) (inputReference := inputReference) (inputLength := inputLength) (inputSmall := inputSmall) (inputBase := inputBase) (inputBasis := inputBasis) (inputEnough := inputEnough) (inputCapacity := inputCapacity) (inputRadius := inputRadius) (inputEpsilon := inputEpsilon) (inputGeometry := inputGeometry) (inputSmallDistance := inputSmallDistance) (inputCalibrated := inputCalibrated) (finalFamily := finalFamily) (finalNodes := finalNodes) (finalLength := finalLength) (finalBase := finalBase) (nativeInstance117 := nativeInstance117) (nativeInstance118 := nativeInstance118) (nativeInstance119 := nativeInstance119) (nativeInstance120 := nativeInstance120) (nativeInstance121 := nativeInstance121) (finalBasis := finalBasis) (finalEnough := finalEnough) (finalCapacity := finalCapacity) (finalRadius := finalRadius) (finalEpsilon := finalEpsilon) (finalSmall := finalSmall) (finalCalibrated := finalCalibrated) (productFirstSmall := productFirstSmall) (productRoundSmall := productRoundSmall) (productNodes := productNodes) (productBase := productBase) (nativeInstance122 := nativeInstance122) (nativeInstance123 := nativeInstance123) (nativeInstance124 := nativeInstance124) (nativeInstance125 := nativeInstance125) (productBasis := productBasis) (productEnough := productEnough) (productCapacity := productCapacity) (productRadius := productRadius) (productEpsilon := productEpsilon) (productSmall := productSmall) (productCalibrated := productCalibrated) (finalRadix := finalRadix) (reconstructionBase := reconstructionBase) (nativeInstance126 := nativeInstance126) (nativeInstance127 := nativeInstance127) (nativeInstance128 := nativeInstance128) (nativeInstance129 := nativeInstance129) (reconstructionBasis := reconstructionBasis) (reconstructionEnough := reconstructionEnough) (reconstructionCapacity := reconstructionCapacity) (reconstructionRadius := reconstructionRadius) (reconstructionEpsilon := reconstructionEpsilon) (reconstructionSmall := reconstructionSmall) (reconstructionCalibrated := reconstructionCalibrated) (restricted := restricted) (nativeInstance130 := nativeInstance130) (nativeInstance131 := nativeInstance131) (nativeInstance132 := nativeInstance132) (nativeInstance133 := nativeInstance133) (nativeInstance134 := nativeInstance134) (compareTags := compareTags) (compareConfig := compareConfig) (compareP := compareP) (nativeInstance135 := nativeInstance135) (compareSmall := compareSmall) (compareDomain := compareDomain) (compareEnough := compareEnough) (compareCapacity := compareCapacity) (compareRadius := compareRadius) (compareFallback := compareFallback) (compareBehavior := compareBehavior) (comparePairEnough := comparePairEnough) (compareLookupSmall := compareLookupSmall) (compareBuild := compareBuild) (compareDistanceLarge := compareDistanceLarge) (compareDistance := compareDistance) (setupC := setupC) (original := original) (setupParameters := setupParameters) (controlParameters := controlParameters) (controls := controls)


end Native
end
end FormalProof4FHE.HasteBoots.PackedPBSNativeJointSetupSafeBound
