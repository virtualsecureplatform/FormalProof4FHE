module
public import FormalProof4FHE.HasteBoots.PackedPBSKeySwitchComparisonNativeJointBound
public import FormalProof4FHE.HasteBoots.PackedPBSKeySwitchExtractionBound
public import FormalProof4FHE.HasteBoots.PackedPBSKeySwitchExtractionExecution
public import FormalProof4FHE.HasteBoots.PackedPBSKeySwitchComparisonBound
public import FormalProof4FHE.HasteBoots.PackedPBSKeySwitchComparisonExecution
public import FormalProof4FHE.HasteBoots.RetainedPaddedComparisonJointBound
public import FormalProof4FHE.HasteBoots.PackedPBSKeySwitchReconstructionProbability
@[expose] public section

/-! All native rates through final extraction share the actual extended PBS
execution and its single final exception. The whole-prefix projection and
operational hash charge must be extended separately to this last stage. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSKeySwitchExtractionNativeJointBound
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

variable {FinalResponse FinalCommitMemory FinalP : Type} {finalD finalB finalC : ℕ}
  [Field FinalP] [Algebra (ZMod q) FinalP] [Fintype FinalP] [DecidableEq FinalP]
  [SampleableType (Fin finalB → Fin 1 → ZMod q)] [SampleableType (Fin finalB → ZMod q)]
  [SampleableType (Fin 1 → ZMod q)]

variable {ProductResponse ProductCommitMemory ProductP : Type}
  [Field ProductP] [Algebra (ZMod q) ProductP] [Fintype ProductP] [DecidableEq ProductP]
  [SampleableType (PackedZeroReduction.Points (ZMod q) finalC finalB)]
  [SampleableType (Fin finalB → Fin finalB → ZMod q)]
  [SampleableType (Fin finalC → ZMod q)] [SampleableType (Fin finalB → ((Fin finalB → ZMod q) × ZMod q))]

variable {ReconstructionResponse ReconstructionCommitMemory ReconstructionP : Type}
  [Field ReconstructionP] [Algebra (ZMod q) ReconstructionP] [Fintype ReconstructionP] [DecidableEq ReconstructionP]

variable {CompareK CompareMessage CompareHelperMemory CompareResponse : Type}
  [Field CompareK] [Algebra (ZMod q) CompareK] [Fintype CompareK] [DecidableEq CompareK] [SampleableType CompareK]
  {compareE comparePadding compareHelperPadding compareC compareRow compareRequests : ℕ}
  {compareWidths compareSizes compareRepetitions : Fin compareRequests → ℕ} {compareMode : Mode}
  {compareTag : PaddedMixedWidthLookupOpeningFamily.Root (2*finalD+1) (∑ i, compareRepetitions i) → Cfg}
  {compareG : PaddedMixedWidthLookupOpeningFamily.Geometry compareC compareRow (2*finalD+1) (∑ i, compareRepetitions i)}
  {CompareL : PaddedMixedWidthLookupOpeningFamily.Root (2*finalD+1) (∑ i, compareRepetitions i) → Type}
  [SampleableType (Fin 1 → CompareK)] [SampleableType (Fin (compareC+compareRow) → CompareK)]
  [∀ root, Field (CompareL root)] [∀ root, Algebra (ZMod q) (CompareL root)]
  [∀ root, Fintype (CompareL root)] [∀ root, DecidableEq (CompareL root)]

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

variable {extractionC extractionLanes dimension : ℕ} {ExtractionResponse ExtractionCommitMemory ExtractionP : Type}
  [Field ExtractionP] [Algebra (ZMod q) ExtractionP] [Fintype ExtractionP] [DecidableEq ExtractionP]
  [SampleableType (Fin extractionC → ZMod q)]
  [SampleableType (Fin (2^extractionLanes) → ((Fin (2^extractionLanes) → ZMod q) × ZMod q))]

/-- All native risks through extraction are bounded on the same executed
extended PBS witness, outside its one final collision exception. -/
abbrev native_safe_joint_bound [NeZero m] [NeZero b] [NeZero accM] [NeZero accB] [NeZero monoM] [NeZero zeroM] [NeZero inputM] [NeZero inputB]
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


    (finalRadix : ZMod q)
    (reconstructionBase : Memory → PaddedLinear.Scheme (ZMod q) Input Digest Cfg ReconstructionResponse Memory ReconstructionCommitMemory heights (2*finalD+2) finalB (1+finalC))
    [∀ memory factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((reconstructionBase memory).code factor).front) finalB)]
    [∀ memory factor, SampleableType (Fin ((reconstructionBase memory).code factor).queries → Fin (2^heights ((reconstructionBase memory).tag factor)))]
    [∀ memory factor, NeZero ((reconstructionBase memory).code factor).m]
    [∀ memory factor, SampleableType ((Fin (2^((reconstructionBase memory).code factor).front) × Fin finalB) → ReconstructionP)]
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

    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = Skeleton.perfect (heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base
        (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs) nodesEnough radix linearBase))
    [∀ root : PaddedMixedWidthLookupOpeningFamily.Root (2*finalD+1) (∑ i, compareRepetitions i), NeZero (PaddedMixedWidthLookupOpeningFamily.packedWidth (compareE+comparePadding) (compareE+compareHelperPadding) root)]
    [∀ root, NeZero (PaddedMixedWidthLookupOpeningFamily.layout compareG root).m]
    [∀ root, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^(PaddedMixedWidthLookupOpeningFamily.layout compareG root).front) (PaddedMixedWidthLookupOpeningFamily.packedWidth (compareE+comparePadding) (compareE+compareHelperPadding) root))]
    [∀ root, SampleableType (Fin (PaddedMixedWidthLookupOpeningFamily.layout compareG root).queries → Fin (2^heights (compareTag root)))]
    [∀ root, SampleableType ((Fin (2^(PaddedMixedWidthLookupOpeningFamily.layout compareG root).front) × Fin (PaddedMixedWidthLookupOpeningFamily.packedWidth (compareE+comparePadding) (compareE+compareHelperPadding) root)) → CompareL root)]
    (compareTags : ∀ memory source, (reconstructionBase memory).tag (PackedPBSComparisonReferences.linearSlot source) = compareTag (.inl source))
    (compareConfig : Memory → PaddedMixedWidthRequestSharedLookup.Parameters (ZMod q) CompareK CompareMessage Memory Cfg Input Digest Memory CompareHelperMemory
      compareE comparePadding compareC compareRow (2*finalD+1) compareRequests compareWidths compareSizes compareRepetitions compareMode)
    (compareP : ℕ) [CharP CompareK compareP] (compareSmall : 2*1 ≤ compareP)
    (compareDomain : ∀ root, Fin (2^heights (compareTag root)) ↪ (ZMod q))
    (compareAnalysisBasis : ∀ root, Module.Basis (Fin (PaddedMixedWidthLookupOpeningFamily.packedWidth (compareE+comparePadding) (compareE+compareHelperPadding) root)) (ZMod q) (CompareL root))
    (compareEnough : ∀ root, compareG.m root ≤ Fintype.card (Fin (2^heights (compareTag root))))
    (compareCapacity : ∀ root, 2^compareG.suffix root ≤ compareG.m root * PaddedMixedWidthLookupOpeningFamily.packedWidth (compareE+comparePadding) (compareE+compareHelperPadding) root)
    (compareRadius : PaddedMixedWidthLookupOpeningFamily.Root (2*finalD+1) (∑ i, compareRepetitions i) → ℕ)
    (compareFallback : PaddedMixedWidthLookupOpeningFamily.Packet (ZMod q) CompareK (compareE+comparePadding) (2*finalD+1) (compareC+compareRow) (∑ i, compareRepetitions i))
    (compareBehavior : Memory → PaddedMixedWidthStagedSharedLookup.Emission (2*finalD+1) (∑ i, compareRepetitions i) Digest Memory
        (RequestLookupPairMiddle.Memory CompareK CompareHelperMemory compareRepetitions) →
      PaddedMixedWidthSharedLookupPCS.Selection (ZMod q) CompareK Memory (compareE+comparePadding) (2*finalD+1) (∑ i, compareRepetitions i) (compareC+compareRow) →
      (root : PaddedMixedWidthLookupOpeningFamily.Root (2*finalD+1) (∑ i, compareRepetitions i)) →
      VariableWidthBatchOpening.Protocol (ZMod q) Input Digest Cfg CompareResponse Memory (PaddedMixedWidthLookupOpeningFamily.packedWidth (compareE+comparePadding) (compareE+compareHelperPadding)) heights compareTag (PaddedMixedWidthLookupOpeningFamily.layout compareG) root)
    (comparePairEnough : ∀ index, compareSizes index+1 < Fintype.card CompareK)
    (compareLookupSmall : ∀ memory index, (compareConfig memory).active index < compareP)
    (compareBuild : Memory → PaddedMixedWidthStagedSharedLookup.SourceEmission (2*finalD+1) Digest Memory →
      RequestLookupPairs.Vector CompareK compareRepetitions → OracleComp (SharedSequence.Shared Cfg Input Digest)
        (PaddedMixedWidthStagedSharedLookup.HelperEmission (∑ i, compareRepetitions i) Digest CompareHelperMemory))
    (compareDistance : ∀ root, (compareRadius root : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := CompareL root) (compareDomain root)) (compareG.m root) :
        Set (Fin (2^heights (compareTag root)) → CompareL root)) : ℚ≥0)/3)
    (compareEpsilon : ENNReal)
    (compareCalibrated : ∀ memory,
      RequestLookupPairMiddle.errorBudget (Fintype.card CompareK) compareWidths compareSizes (compareConfig memory).active compareRepetitions +
        (error CompareK compareMode (compareC+compareRow) + PaddedMixedWidthStagedSharedLookup.pcsError
          (d := compareE) (padding := comparePadding) (helperPadding := compareHelperPadding) (g := compareG) CompareL compareDomain compareRadius) ≤ compareEpsilon)
    (extractionLog : extractionC+extractionLanes = log) (positive : 0 < dimension)
    (output : NativePublic.Ciphertext q dimension)
    (extractionFirstSmall : (2*(2^extractionLanes)-1)*2+1 ≤ q)
    (extractionRoundSmall : (2*(2^extractionLanes)-1)*3+1 ≤ q)
    (extractionNodes : 2*(2^extractionLanes) ≤ (2*(2^extractionLanes)-1)*2+1)
    (extractionBase : Memory → KeySwitchPaddedExtraction.Scheme (q := q) (c := extractionC) (lanes := extractionLanes)
      (Input := Input) (Cfg := Cfg) (Response := ExtractionResponse) (Memory := Memory)
      (CommitMemory := ExtractionCommitMemory) (heights := heights))
    [∀ memory factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((extractionBase memory).code factor).front) (2^extractionLanes))]
    [∀ memory factor, SampleableType (Fin ((extractionBase memory).code factor).queries → Fin (2^heights ((extractionBase memory).tag factor)))]
    [SampleableType (Fin (2^extractionLanes) → ZMod q)]
    [SampleableType (PackedZeroReduction.Points (ZMod q) extractionC (2^extractionLanes))]
    [SampleableType (Fin (2^extractionLanes) → Fin (2^extractionLanes) → ZMod q)]
    [∀ memory factor, NeZero ((extractionBase memory).code factor).m]
    [∀ memory factor, SampleableType ((Fin (2^((extractionBase memory).code factor).front) × Fin (2^extractionLanes)) → ExtractionP)]
    (extractionBasis : Module.Basis (Fin (2^extractionLanes)) (ZMod q) ExtractionP)
    (extractionEnough : ∀ memory factor, ((extractionBase memory).code factor).m ≤ Fintype.card (Fin (2^heights ((extractionBase memory).tag factor))))
    (extractionCapacity : ∀ memory factor, 2^((extractionBase memory).code factor).suffix ≤ ((extractionBase memory).code factor).m*(2^extractionLanes))
    (extractionRadius : Memory → Unit → ℕ)
    (extractionSmallDistance : ∀ memory factor, (extractionRadius memory factor : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := ExtractionP) ((extractionBase memory).domain factor)) ((extractionBase memory).code factor).m :
        Set (Fin (2^heights ((extractionBase memory).tag factor)) → ExtractionP)) : ℚ≥0)/3)
    (extractionEpsilon : ENNReal)
    (extractionCalibrated : ∀ memory,
      (((extractionC : ENNReal)/Fintype.card (ZMod q))^(2^extractionLanes) +
        ((((((2*(2^extractionLanes)-1)*2+1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^extractionLanes))) +
        (extractionC : ENNReal)*((((((2*(2^extractionLanes)-1)*3 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^extractionLanes)))) +
      (([()]).map (fun factor => JointMatrixOpening.error (K := ExtractionP) (m := ((extractionBase memory).code factor).m) (b := 2^extractionLanes)
        (queries := ((extractionBase memory).code factor).queries) ((extractionBase memory).domain factor) (extractionRadius memory factor))).sum ≤ extractionEpsilon) :=
  let ns := AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs
  let first := PackedPBSRequestComparisonStage.scheme hs.encoding config p small domain fallback behavior pairEnough build
  let second := PackedPBSRequestComparisonStage.scheme hs.encoding secondConfig secondP secondSmall secondDomain secondFallback secondBehavior secondPairEnough secondBuild
  let comparison := fun memory => PaddedPBSRequestComparisonStage.scheme (heights := first.heights) ns.encoding
    (compareConfig memory) compareP compareSmall compareDomain compareFallback (compareBehavior memory) comparePairEnough (compareBuild memory)
  let initial := CheckpointExecution.empty (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)
  let good := CheckpointExecution.good_empty hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
  let audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial :=
    ⟨good.1,fun _ => good.2.2⟩
  let compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape heights)
      initial.checkpoints := by
    intro tag saved member
    cases member
  let prior := PackedPBSKeySwitchComparisons.witness length psi primitive family inputs base ns nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase zeroFirstSmall zeroRoundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase finalRadix reconstructionBase comparison initial
  let native : ((PriorBefore first second finalBase productBase × Option (PackedPBSKeySwitchReconstruction.ReconstructionChild first.heights reconstructionBase)) × Option (Sigma (RetainedPaddedComparison.Child (H := first.heights) reconstructionBase comparison))) → Memory → KeySwitchPaddedExtraction.Scheme (q := q) (c := extractionC) (lanes := extractionLanes)
      (Input := Input) (Cfg := Cfg) (Response := ExtractionResponse) (Memory := Memory)
      (CommitMemory := ExtractionCommitMemory) (heights := first.heights) := fun before memory =>
    KeySwitchPaddedExtraction.stage (extractionBase memory) ns.encoding finalFamily positive
      (fun _ => PackedPBSKeySwitchExtraction.endpoint first second finalBase productBase reconstructionBase comparison factory accLength extractionLog before)
      (fun _ => output) extractionFirstSmall extractionRoundSmall extractionNodes
  let previous := PackedPBSKeySwitchComparisonNativeJointBound.native_safe_joint_bound length psi primitive family inputs base firstSmall roundSmall hadNodes hs
    nodesEnough radix linearBase nativeBasis dummy nativeEnough nativeCapacity nativeRadius nttEpsilon linearEpsilon nttEncoding linearEncoding
    hadSmall nttSmall linearSmall nttCalibrated linearCalibrated analysisBasis config p small domain lookupEnough lookupCapacity lookupRadius
    fallback behavior pairEnough lookupSmall build distance secondAnalysisBasis secondConfig secondP secondSmall secondDomain secondLookupEnough
    secondLookupCapacity secondLookupRadius secondFallback secondBehavior secondPairEnough secondLookupSmall secondBuild secondDistance
    secondBase secondLinearEpsilon secondGeometry secondLinearSmall secondLinearCalibrated accumulators factory accBasis accEnough accCapacity
    accRadius accEpsilon accGeometry accSmall accCalibrated monoLength evaluations monoBase zeroFirstSmall zeroRoundSmall zeroNodesEnough rotations zeroBase
    monoBasis monoEnough monoCapacity monoRadius monoEpsilon monoGeometry monoSmall monoCalibrated
    zeroBasis zeroEnough zeroCapacity zeroRadius zeroEpsilon zeroGeometry zeroSmall zeroCalibrated accLength inputReference inputLength inputSmall inputBase
    inputBasis inputEnough inputCapacity inputRadius inputEpsilon inputGeometry inputSmallDistance inputCalibrated finalFamily finalNodes finalLength finalBase
    finalBasis finalEnough finalCapacity finalRadius finalEpsilon finalSmall finalCalibrated productFirstSmall productRoundSmall productNodes productBase
    productBasis productEnough productCapacity productRadius productEpsilon productSmall productCalibrated finalRadix reconstructionBase
    reconstructionBasis reconstructionEnough reconstructionCapacity reconstructionRadius reconstructionEpsilon reconstructionSmall reconstructionCalibrated restricted
    compareTags compareConfig compareP compareSmall compareDomain compareAnalysisBasis compareEnough compareCapacity compareRadius compareFallback compareBehavior comparePairEnough compareLookupSmall compareBuild compareDistance compareEpsilon compareCalibrated
  let extracted := PackedPBSKeySwitchExtractionBound.safe_extraction_bound length psi primitive family inputs base ns nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase zeroFirstSmall zeroRoundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase finalRadix reconstructionBase comparison
    extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase initial compatible restricted audited
    extractionBasis extractionEnough extractionCapacity extractionRadius extractionSmallDistance extractionEpsilon extractionCalibrated
  RetainedPaddedExtractionJointBound.safe_joint_bound (H := first.heights) native
    (PackedPBSKeySwitchExtraction.get first second finalBase productBase reconstructionBase comparison)
    (PackedPBSKeySwitchComparisons.finalState first second finalBase productBase reconstructionBase comparison)
    dummy prior
    (fun outcome => (((fun outcome => (((fun outcome => (((fun outcome => (((fun outcome => (((fun previous => (((fun prior => ((((PackedPBSReconstructionJointBound.Risk length psi primitive family inputs base ns nodesEnough radix linearBase dummy nativeCapacity nativeRadius prior.1.1.1.1 ∨
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
            (AccumulatorEndpoint.value accLength (factory acc.1.1.2).context) (inputBase product.2.1.2.memory)) dummy inputCapacity inputRadius input))) outcome.1) ∨ (∃ ntts, outcome.2 = some ntts ∧
        PaddedNTTSequenceSoundness.AnyOriginalRisk (KeySwitchPaddedNTT.factory finalBase hs.encoding finalFamily finalNodes finalLength psi primitive) hs.encoding dummy finalCapacity finalRadius ntts.1))) outcome.1) ∨ (∃ product, outcome.2 = some product ∧ PaddedZeroCheck.OriginalRisk (KeySwitchPaddedProduct.stage (productBase product.1) hs.encoding finalFamily productFirstSmall productRoundSmall productNodes) dummy
        (productCapacity product.1) (productRadius product.1) product.2))) outcome.1) ∨ (∃ reconstructed, outcome.2 = some reconstructed ∧ PaddedLinear.OriginalRisk (KeySwitchPaddedReconstruction.stage (reconstructionBase reconstructed.1) hs.encoding inputReference finalFamily finalNodes finalRadix) dummy
        (reconstructionCapacity reconstructed.1) (reconstructionRadius reconstructed.1) reconstructed.2))) outcome.1) ∨ ∃ result, outcome.2 = some result ∧
          (PaddedMixedWidthOwnedRequestSources.OriginalFalse hs.encoding dummy (compareConfig result.1.1) compareDomain compareCapacity compareRadius result.2 ∧
            result.2.2.2.1.2.accepted = true)))
    (fun result => PaddedPublicZeroCheck.OriginalRisk (native result.1.1 result.1.2) dummy
      (extractionCapacity result.1.2) (extractionRadius result.1.2) result.2)
    ((((((((((((PackedPBSHadamardNTTJointBound.rate (K := P) hs nativeRadius + ((List.finRange (2*d+1)).map nttEpsilon).sum) + linearEpsilon) +
        (RequestLookupPairMiddle.errorBudget (Fintype.card K) widths sizes config.active repetitions +
          (error K mode (lookupC+lookupRow) + MixedWidthStagedSharedLookup.pcsError (d := e) (padding := padding) (helperPadding := helperPadding) (g := g) L domain lookupRadius))) + secondLinearEpsilon) +
        (RequestLookupPairMiddle.errorBudget (Fintype.card SecondK) secondWidths secondSizes secondConfig.active secondRepetitions +
          (error SecondK secondMode (secondLookupC+secondLookupRow) + MixedWidthStagedSharedLookup.pcsError (d := secondE) (padding := secondPadding) (helperPadding := secondHelperPadding) (g := secondG) SecondL secondDomain secondLookupRadius))) + accEpsilon) + ((monoEpsilon false + monoEpsilon true) + zeroEpsilon)) + inputEpsilon) + ((List.finRange (finalD+1)).map finalEpsilon).sum) + productEpsilon) + reconstructionEpsilon) + compareEpsilon) extractionEpsilon previous extracted
/-- All native stage risks or a final collision are bounded by the derived
arithmetic/PCS rate sum plus one charge for the complete operational execution. -/
abbrev native_risk_or_bad_bound [Fintype Digest] [NeZero m] [NeZero b] [NeZero accM] [NeZero accB] [NeZero monoM] [NeZero zeroM] [NeZero inputM] [NeZero inputB]
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


    (finalRadix : ZMod q)
    (reconstructionBase : Memory → PaddedLinear.Scheme (ZMod q) Input Digest Cfg ReconstructionResponse Memory ReconstructionCommitMemory heights (2*finalD+2) finalB (1+finalC))
    [∀ memory factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((reconstructionBase memory).code factor).front) finalB)]
    [∀ memory factor, SampleableType (Fin ((reconstructionBase memory).code factor).queries → Fin (2^heights ((reconstructionBase memory).tag factor)))]
    [∀ memory factor, NeZero ((reconstructionBase memory).code factor).m]
    [∀ memory factor, SampleableType ((Fin (2^((reconstructionBase memory).code factor).front) × Fin finalB) → ReconstructionP)]
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

    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = Skeleton.perfect (heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base
        (AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs) nodesEnough radix linearBase))
    [∀ root : PaddedMixedWidthLookupOpeningFamily.Root (2*finalD+1) (∑ i, compareRepetitions i), NeZero (PaddedMixedWidthLookupOpeningFamily.packedWidth (compareE+comparePadding) (compareE+compareHelperPadding) root)]
    [∀ root, NeZero (PaddedMixedWidthLookupOpeningFamily.layout compareG root).m]
    [∀ root, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^(PaddedMixedWidthLookupOpeningFamily.layout compareG root).front) (PaddedMixedWidthLookupOpeningFamily.packedWidth (compareE+comparePadding) (compareE+compareHelperPadding) root))]
    [∀ root, SampleableType (Fin (PaddedMixedWidthLookupOpeningFamily.layout compareG root).queries → Fin (2^heights (compareTag root)))]
    [∀ root, SampleableType ((Fin (2^(PaddedMixedWidthLookupOpeningFamily.layout compareG root).front) × Fin (PaddedMixedWidthLookupOpeningFamily.packedWidth (compareE+comparePadding) (compareE+compareHelperPadding) root)) → CompareL root)]
    (compareTags : ∀ memory source, (reconstructionBase memory).tag (PackedPBSComparisonReferences.linearSlot source) = compareTag (.inl source))
    (compareConfig : Memory → PaddedMixedWidthRequestSharedLookup.Parameters (ZMod q) CompareK CompareMessage Memory Cfg Input Digest Memory CompareHelperMemory
      compareE comparePadding compareC compareRow (2*finalD+1) compareRequests compareWidths compareSizes compareRepetitions compareMode)
    (compareP : ℕ) [CharP CompareK compareP] (compareSmall : 2*1 ≤ compareP)
    (compareDomain : ∀ root, Fin (2^heights (compareTag root)) ↪ (ZMod q))
    (compareAnalysisBasis : ∀ root, Module.Basis (Fin (PaddedMixedWidthLookupOpeningFamily.packedWidth (compareE+comparePadding) (compareE+compareHelperPadding) root)) (ZMod q) (CompareL root))
    (compareEnough : ∀ root, compareG.m root ≤ Fintype.card (Fin (2^heights (compareTag root))))
    (compareCapacity : ∀ root, 2^compareG.suffix root ≤ compareG.m root * PaddedMixedWidthLookupOpeningFamily.packedWidth (compareE+comparePadding) (compareE+compareHelperPadding) root)
    (compareRadius : PaddedMixedWidthLookupOpeningFamily.Root (2*finalD+1) (∑ i, compareRepetitions i) → ℕ)
    (compareFallback : PaddedMixedWidthLookupOpeningFamily.Packet (ZMod q) CompareK (compareE+comparePadding) (2*finalD+1) (compareC+compareRow) (∑ i, compareRepetitions i))
    (compareBehavior : Memory → PaddedMixedWidthStagedSharedLookup.Emission (2*finalD+1) (∑ i, compareRepetitions i) Digest Memory
        (RequestLookupPairMiddle.Memory CompareK CompareHelperMemory compareRepetitions) →
      PaddedMixedWidthSharedLookupPCS.Selection (ZMod q) CompareK Memory (compareE+comparePadding) (2*finalD+1) (∑ i, compareRepetitions i) (compareC+compareRow) →
      (root : PaddedMixedWidthLookupOpeningFamily.Root (2*finalD+1) (∑ i, compareRepetitions i)) →
      VariableWidthBatchOpening.Protocol (ZMod q) Input Digest Cfg CompareResponse Memory (PaddedMixedWidthLookupOpeningFamily.packedWidth (compareE+comparePadding) (compareE+compareHelperPadding)) heights compareTag (PaddedMixedWidthLookupOpeningFamily.layout compareG) root)
    (comparePairEnough : ∀ index, compareSizes index+1 < Fintype.card CompareK)
    (compareLookupSmall : ∀ memory index, (compareConfig memory).active index < compareP)
    (compareBuild : Memory → PaddedMixedWidthStagedSharedLookup.SourceEmission (2*finalD+1) Digest Memory →
      RequestLookupPairs.Vector CompareK compareRepetitions → OracleComp (SharedSequence.Shared Cfg Input Digest)
        (PaddedMixedWidthStagedSharedLookup.HelperEmission (∑ i, compareRepetitions i) Digest CompareHelperMemory))
    (compareDistance : ∀ root, (compareRadius root : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := CompareL root) (compareDomain root)) (compareG.m root) :
        Set (Fin (2^heights (compareTag root)) → CompareL root)) : ℚ≥0)/3)
    (compareEpsilon : ENNReal)
    (compareCalibrated : ∀ memory,
      RequestLookupPairMiddle.errorBudget (Fintype.card CompareK) compareWidths compareSizes (compareConfig memory).active compareRepetitions +
        (error CompareK compareMode (compareC+compareRow) + PaddedMixedWidthStagedSharedLookup.pcsError
          (d := compareE) (padding := comparePadding) (helperPadding := compareHelperPadding) (g := compareG) CompareL compareDomain compareRadius) ≤ compareEpsilon)
    (extractionLog : extractionC+extractionLanes = log) (positive : 0 < dimension)
    (output : NativePublic.Ciphertext q dimension)
    (extractionFirstSmall : (2*(2^extractionLanes)-1)*2+1 ≤ q)
    (extractionRoundSmall : (2*(2^extractionLanes)-1)*3+1 ≤ q)
    (extractionNodes : 2*(2^extractionLanes) ≤ (2*(2^extractionLanes)-1)*2+1)
    (extractionBase : Memory → KeySwitchPaddedExtraction.Scheme (q := q) (c := extractionC) (lanes := extractionLanes)
      (Input := Input) (Cfg := Cfg) (Response := ExtractionResponse) (Memory := Memory)
      (CommitMemory := ExtractionCommitMemory) (heights := heights))
    [∀ memory factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((extractionBase memory).code factor).front) (2^extractionLanes))]
    [∀ memory factor, SampleableType (Fin ((extractionBase memory).code factor).queries → Fin (2^heights ((extractionBase memory).tag factor)))]
    [SampleableType (Fin (2^extractionLanes) → ZMod q)]
    [SampleableType (PackedZeroReduction.Points (ZMod q) extractionC (2^extractionLanes))]
    [SampleableType (Fin (2^extractionLanes) → Fin (2^extractionLanes) → ZMod q)]
    [∀ memory factor, NeZero ((extractionBase memory).code factor).m]
    [∀ memory factor, SampleableType ((Fin (2^((extractionBase memory).code factor).front) × Fin (2^extractionLanes)) → ExtractionP)]
    (extractionBasis : Module.Basis (Fin (2^extractionLanes)) (ZMod q) ExtractionP)
    (extractionEnough : ∀ memory factor, ((extractionBase memory).code factor).m ≤ Fintype.card (Fin (2^heights ((extractionBase memory).tag factor))))
    (extractionCapacity : ∀ memory factor, 2^((extractionBase memory).code factor).suffix ≤ ((extractionBase memory).code factor).m*(2^extractionLanes))
    (extractionRadius : Memory → Unit → ℕ)
    (extractionSmallDistance : ∀ memory factor, (extractionRadius memory factor : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := ExtractionP) ((extractionBase memory).domain factor)) ((extractionBase memory).code factor).m :
        Set (Fin (2^heights ((extractionBase memory).tag factor)) → ExtractionP)) : ℚ≥0)/3)
    (extractionEpsilon : ENNReal)
    (extractionCalibrated : ∀ memory,
      (((extractionC : ENNReal)/Fintype.card (ZMod q))^(2^extractionLanes) +
        ((((((2*(2^extractionLanes)-1)*2+1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^extractionLanes))) +
        (extractionC : ENNReal)*((((((2*(2^extractionLanes)-1)*3 : ℕ) : ENNReal)/Fintype.card (ZMod q))^(2^extractionLanes)))) +
      (([()]).map (fun factor => JointMatrixOpening.error (K := ExtractionP) (m := ((extractionBase memory).code factor).m) (b := 2^extractionLanes)
        (queries := ((extractionBase memory).code factor).queries) ((extractionBase memory).domain factor) (extractionRadius memory factor))).sum ≤ extractionEpsilon) :=
  let ns := AuthenticatedZeroCheck.nativeScheme q 2 firstSmall roundSmall hadNodes hs
  let first := PackedPBSRequestComparisonStage.scheme hs.encoding config p small domain fallback behavior pairEnough build
  let second := PackedPBSRequestComparisonStage.scheme hs.encoding secondConfig secondP secondSmall secondDomain secondFallback secondBehavior secondPairEnough secondBuild
  let comparison := fun memory => PaddedPBSRequestComparisonStage.scheme (heights := first.heights) ns.encoding
    (compareConfig memory) compareP compareSmall compareDomain compareFallback (compareBehavior memory) comparePairEnough (compareBuild memory)
  let safe := native_safe_joint_bound length psi primitive family inputs base firstSmall roundSmall hadNodes hs
    nodesEnough radix linearBase nativeBasis dummy nativeEnough nativeCapacity nativeRadius nttEpsilon linearEpsilon
    nttEncoding linearEncoding hadSmall nttSmall linearSmall nttCalibrated linearCalibrated analysisBasis config p
    small domain lookupEnough lookupCapacity lookupRadius fallback behavior pairEnough lookupSmall build
    distance secondAnalysisBasis secondConfig secondP secondSmall secondDomain secondLookupEnough secondLookupCapacity secondLookupRadius secondFallback
    secondBehavior secondPairEnough secondLookupSmall secondBuild secondDistance secondBase secondLinearEpsilon secondGeometry secondLinearSmall secondLinearCalibrated
    accumulators factory accBasis accEnough accCapacity accRadius accEpsilon accGeometry accSmall accCalibrated
    monoLength evaluations monoBase zeroFirstSmall zeroRoundSmall zeroNodesEnough rotations zeroBase monoBasis monoEnough
    monoCapacity monoRadius monoEpsilon monoGeometry monoSmall monoCalibrated zeroBasis zeroEnough zeroCapacity zeroRadius
    zeroEpsilon zeroGeometry zeroSmall zeroCalibrated accLength inputReference inputLength inputSmall inputBase inputBasis
    inputEnough inputCapacity inputRadius inputEpsilon inputGeometry inputSmallDistance inputCalibrated finalFamily finalNodes finalLength
    finalBase finalBasis finalEnough finalCapacity finalRadius finalEpsilon finalSmall finalCalibrated productFirstSmall productRoundSmall
    productNodes productBase productBasis productEnough productCapacity productRadius productEpsilon productSmall productCalibrated finalRadix
    reconstructionBase reconstructionBasis reconstructionEnough reconstructionCapacity reconstructionRadius reconstructionEpsilon reconstructionSmall reconstructionCalibrated restricted compareTags
    compareConfig compareP compareSmall compareDomain compareAnalysisBasis compareEnough compareCapacity compareRadius compareFallback compareBehavior
    comparePairEnough compareLookupSmall compareBuild compareDistance compareEpsilon compareCalibrated extractionLog positive output extractionFirstSmall
    extractionRoundSmall extractionNodes extractionBase extractionBasis extractionEnough extractionCapacity extractionRadius extractionSmallDistance extractionEpsilon extractionCalibrated
  let failure := PackedPBSKeySwitchExtractionExecution.final_bad_le_charge length psi primitive family inputs base ns nodesEnough radix linearBase
    dummy first second secondBase accumulators factory monoLength evaluations monoBase zeroFirstSmall zeroRoundSmall zeroNodesEnough rotations zeroBase
    accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes
    productBase finalRadix reconstructionBase comparison extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase restricted
  PackedPBSMonomialNativeJointBound.risk_or_bad_of_safe _ _ _ _ _ safe failure

end
end FormalProof4FHE.HasteBoots.PackedPBSKeySwitchExtractionNativeJointBound
