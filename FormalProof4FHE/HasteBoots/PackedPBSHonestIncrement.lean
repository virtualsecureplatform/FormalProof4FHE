module
public import FormalProof4FHE.HasteBoots.PackedPBSKeySwitchComparisons
public import FormalProof4FHE.HasteBoots.RetainedComparisonHistory
public import FormalProof4FHE.HasteBoots.PackedPBSKeySwitchReconstructionSupport
public import FormalProof4FHE.HasteBoots.RetainedComparisonReached
public import FormalProof4FHE.HasteBoots.ReachedPairFacts
public import FormalProof4FHE.HasteBoots.PackedPBSReachedKeySwitch
public import FormalProof4FHE.HasteBoots.PackedPBSKeySwitchComparisonsHistory
public import FormalProof4FHE.HasteBoots.ExecutedKeySwitchIncrement
public import FormalProof4FHE.HasteBoots.ExecutedHonestKeySwitchIncrement
public import FormalProof4FHE.HasteBoots.ExecutedProductKeyReceipt
public import FormalProof4FHE.HasteBoots.PackedPBSNTTQueryHistory
public import FormalProof4FHE.HasteBoots.PackedPBSComparisonQueryHistory
@[expose] public section

/-! Honest-key canonical increment coverage from the complete supported PBS
witness. Setup observations are factual hash-query receipts; child execution
and final history receipts are derived from this same PBS execution. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSHonestIncrement
open OracleSpec OracleComp
open PackedPBSKeySwitchComparisons
open NativeRootMessage (Digest)
open PackedPBSSecondComparisons (sharedScheme)
noncomputable section

-- Keep support opaque: elaboration needs program equality, not execution reduction.
attribute [local irreducible] MonadAttach.support
private theorem transfer_support {A B : Type} (p q : ProbComp (A × Option B))
    (same : p = q) {Facts : A → B → Prop}
    (facts : ∀ a b, (a,some b) ∈ support p → Facts a b) :
    ∀ a b, (a,some b) ∈ support q → Facts a b := by
  cases same
  exact facts

variable {q finalC finalD bits d b c r k n front suffix m queries height : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory FirstMessage Message : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin b → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points (ZMod q) n b)] [SampleableType (Fin b → Fin b → ZMod q)]

variable (length : 2^c*b = 2^(finalC+2)) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^((finalC+2)+1)))
  (family : PackedPBSOriginalReferences.Family (2*d)) (inputs : PackedPBSDecompositionReferences.Inputs)
  (base : Fin (2*d+1) → Memory → AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    b c r k front suffix m queries height)
  (hs : AuthenticatedZeroCheck.Scheme (ZMod q) (PBSHadamard.Factor (2*d)) (PBSHadamard.Term (2*d))
    FirstMessage Message Input Digest Cfg Response Memory CommitMemory b n front suffix m queries height)
  (nodesEnough : 2*b ≤ q) (radix : ZMod q)
  (linearBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) b front suffix m queries height)

local notation "Prior" => Outcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
  (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k) (n := n) (d := d)
  (front := front) (suffix := suffix) (queries := queries) (height := height)

variable {Helper Selection Root Data : Type}

local notation "Return" => PackedPBSKeySwitchReconstruction.ComparisonReturn (Selection := Selection) (Root := Root) (Data := Data) (Memory := Memory)

local notation "Reached" => Before (q := q) (Response := Response) (CommitMemory := CommitMemory)
  (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix)
  (queries := queries) (height := height)

local notation "Child" => LinearOutcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
  (Memory := Memory) (CommitMemory := CommitMemory) (d := d) (b := b) (front := front) (suffix := suffix)
  (queries := queries) (height := height)

local notation "Previous" => SecondBefore (q := q) (Response := Response) (CommitMemory := CommitMemory)
  (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix)
  (queries := queries) (height := height)

variable {SecondHelper SecondSelection SecondRoot SecondData : Type}

local notation "Return2" => SecondSelection × ShortCircuitSequence.Outcome SecondRoot SecondData Memory

local notation "Decomposed" => BeforeAccumulator (q := q) (Response := Response) (CommitMemory := CommitMemory)
  (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix)
  (queries := queries) (height := height)

variable {AccResponse : Type} {accB accC accR accFront accSuffix accM accQueries accHeight : ℕ}
  [SampleableType (Fin accB → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^accFront) accB)]
  [SampleableType (Fin accQueries → Fin (2^accHeight))]

local notation "AccScheme" => AmbientAccumulator.Scheme (ZMod q) Input Digest Cfg AccResponse Memory Memory
  accB accC accR accFront accSuffix accM accQueries accHeight

local notation "AccChild" => AccumulatorOutcome (q := q) (Input := Input) (Cfg := Cfg) (AccResponse := AccResponse)
  (Memory := Memory) (accB := accB) (accC := accC) (accR := accR) (accFront := accFront)
  (accQueries := accQueries) (accHeight := accHeight)

local notation "Finished" => AfterAccumulator (q := q) (Response := Response) (CommitMemory := CommitMemory)
  (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix) (queries := queries) (height := height)
  (AccResponse := AccResponse) (accB := accB) (accC := accC) (accR := accR) (accFront := accFront) (accQueries := accQueries) (accHeight := accHeight)

variable {lanes cells rows rounds : ℕ}

variable {MonoResponse MonoCommitMemory : Type} {monoK monoFront monoSuffix monoM monoQueries monoHeight : ℕ}
  [SampleableType (Fin monoK → Fin (rows+1) → ZMod q)] [SampleableType (Fin (2^lanes) → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^monoFront) (2^lanes))]
  [SampleableType (Fin monoQueries → Fin (2^monoHeight))]

local notation "MonoScheme" => AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg MonoResponse Memory MonoCommitMemory
  (2^lanes) cells (rows+1) monoK monoFront monoSuffix monoM monoQueries monoHeight

local notation "MonoChild" => MonomialOutcome (q := q) (Input := Input) (Cfg := Cfg) (Memory := Memory)
  (MonoResponse := MonoResponse) (MonoCommitMemory := MonoCommitMemory) (lanes := lanes) (cells := cells) (rows := rows)
  (monoK := monoK) (monoFront := monoFront) (monoQueries := monoQueries) (monoHeight := monoHeight)

local notation "NTTBefore" => BeforeProduct (q := q) (Response := Response) (CommitMemory := CommitMemory)
  (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix) (queries := queries) (height := height)
  (AccResponse := AccResponse) (accB := accB) (accC := accC) (accR := accR) (accFront := accFront) (accQueries := accQueries) (accHeight := accHeight)
  (MonoResponse := MonoResponse) (MonoCommitMemory := MonoCommitMemory) (lanes := lanes) (cells := cells) (rows := rows)
  (monoK := monoK) (monoFront := monoFront) (monoQueries := monoQueries) (monoHeight := monoHeight)

variable {ZeroResponse ZeroCommitMemory : Type} {zeroFront zeroSuffix zeroM zeroQueries zeroHeight : ℕ}
  [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (PackedZeroReduction.Points (ZMod q) (cells+rows) (2^lanes))]
  [SampleableType (Fin (2^lanes) → Fin (2^lanes) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^zeroFront) (2^lanes))]
  [SampleableType (Fin zeroQueries → Fin (2^zeroHeight))]

local notation "ZeroScheme" => AuthenticatedPublicZeroCheck.Scheme (ZMod q) Bool Unit Bool
  (Fin (2^lanes) → Fin ((2*(2^lanes)-1)*2+1) → ZMod q) (Fin ((2*(2^lanes)-1)*3+1) → ZMod q)
  Input Digest Cfg ZeroResponse Memory ZeroCommitMemory (2^lanes) (cells+rows) zeroFront zeroSuffix zeroM zeroQueries zeroHeight

local notation "ProductChild" => ProductOutcome (q := q) (Input := Input) (Cfg := Cfg) (Memory := Memory)
  (ZeroResponse := ZeroResponse) (ZeroCommitMemory := ZeroCommitMemory) (lanes := lanes) (cells := cells) (rows := rows)
  (zeroFront := zeroFront) (zeroQueries := zeroQueries) (zeroHeight := zeroHeight)

local notation "MonomialBefore" => BeforeInput (q := q) (Response := Response) (CommitMemory := CommitMemory)
  (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix) (queries := queries) (height := height)
  (AccResponse := AccResponse) (accB := accB) (accC := accC) (accR := accR) (accFront := accFront) (accQueries := accQueries) (accHeight := accHeight)
  (MonoResponse := MonoResponse) (MonoCommitMemory := MonoCommitMemory) (lanes := lanes) (cells := cells) (rows := rows)
  (monoK := monoK) (monoFront := monoFront) (monoQueries := monoQueries) (monoHeight := monoHeight)
  (ZeroResponse := ZeroResponse) (ZeroCommitMemory := ZeroCommitMemory) (zeroFront := zeroFront) (zeroQueries := zeroQueries) (zeroHeight := zeroHeight)

variable {InputResponse InputCommitMemory : Type} {inputFront inputSuffix inputM inputQueries inputHeight : ℕ}
  [SampleableType (Fin 4 → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^inputFront) 4)]
  [SampleableType (Fin inputQueries → Fin (2^inputHeight))]

local notation "InputScheme" => AmbientKnownInput.Scheme (ZMod q) Input Digest Cfg InputResponse Memory InputCommitMemory
  4 (1+finalC) inputFront inputSuffix inputM inputQueries inputHeight

local notation "InputChild" => InputOutcome (q := q) (Input := Input) (Cfg := Cfg) (Memory := Memory)
  (InputResponse := InputResponse) (InputCommitMemory := InputCommitMemory) (inputB := 4) (inputC := finalC)
  (inputFront := inputFront) (inputQueries := inputQueries) (inputHeight := inputHeight)

local notation "InputBefore" => BeforeNTT (q := q) (Response := Response) (CommitMemory := CommitMemory)
  (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix) (queries := queries) (height := height)
  (AccResponse := AccResponse) (accB := accB) (accC := accC) (accR := accR) (accFront := accFront) (accQueries := accQueries) (accHeight := accHeight)
  (MonoResponse := MonoResponse) (MonoCommitMemory := MonoCommitMemory) (lanes := lanes) (cells := cells) (rows := rows)
  (monoK := monoK) (monoFront := monoFront) (monoQueries := monoQueries) (monoHeight := monoHeight)
  (ZeroResponse := ZeroResponse) (ZeroCommitMemory := ZeroCommitMemory) (zeroFront := zeroFront) (zeroQueries := zeroQueries) (zeroHeight := zeroHeight)
  (InputResponse := InputResponse) (InputCommitMemory := InputCommitMemory) (inputB := 4) (inputC := finalC)
  (inputFront := inputFront) (inputQueries := inputQueries) (inputHeight := inputHeight)

variable {FinalResponse FinalCommitMemory : Type}
  [SampleableType (Fin 4 → Fin 1 → ZMod q)]

local notation "FinalBefore" => BeforeFinalProduct (q := q) (Response := Response) (CommitMemory := CommitMemory)
  (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix) (queries := queries) (height := height)
  (AccResponse := AccResponse) (accB := accB) (accC := accC) (accR := accR) (accFront := accFront) (accQueries := accQueries) (accHeight := accHeight)
  (MonoResponse := MonoResponse) (MonoCommitMemory := MonoCommitMemory) (lanes := lanes) (cells := cells) (rows := rows)
  (monoK := monoK) (monoFront := monoFront) (monoQueries := monoQueries) (monoHeight := monoHeight)
  (ZeroResponse := ZeroResponse) (ZeroCommitMemory := ZeroCommitMemory) (zeroFront := zeroFront) (zeroQueries := zeroQueries) (zeroHeight := zeroHeight)
  (InputResponse := InputResponse) (InputCommitMemory := InputCommitMemory) (inputB := 4) (inputC := finalC)
  (inputFront := inputFront) (inputQueries := inputQueries) (inputHeight := inputHeight)

variable {ProductResponse ProductCommitMemory : Type}
  [SampleableType (PackedZeroReduction.Points (ZMod q) finalC 4)]
  [SampleableType (Fin 4 → Fin 4 → ZMod q)]

local notation "ProductBefore" => PackedPBSKeySwitchReconstruction.BeforeFinalReconstruction (q := q) (Response := Response) (CommitMemory := CommitMemory)
  (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix) (queries := queries) (height := height)
  (AccResponse := AccResponse) (accB := accB) (accC := accC) (accR := accR) (accFront := accFront) (accQueries := accQueries) (accHeight := accHeight)
  (MonoResponse := MonoResponse) (MonoCommitMemory := MonoCommitMemory) (lanes := lanes) (cells := cells) (rows := rows)
  (monoK := monoK) (monoFront := monoFront) (monoQueries := monoQueries) (monoHeight := monoHeight)
  (ZeroResponse := ZeroResponse) (ZeroCommitMemory := ZeroCommitMemory) (zeroFront := zeroFront) (zeroQueries := zeroQueries) (zeroHeight := zeroHeight)
  (InputResponse := InputResponse) (InputCommitMemory := InputCommitMemory) (inputB := 4) (inputC := finalC)
  (inputFront := inputFront) (inputQueries := inputQueries) (inputHeight := inputHeight)

variable {ReconstructionResponse ReconstructionCommitMemory : Type}

open scoped BigOperators
variable {K LookupMessage LookupMemory ConfigHelperMemory RetainedMemory FinalResult : Type}
    [Field K] [Algebra (ZMod q) K]
    {repetitions : Fin finalD → ℕ} {mode : MixedWidthSharedLookupPCSAlgebra.Mode}
    {tag : PaddedMixedWidthLookupOpeningFamily.Root (2*finalD+1) (∑ i, repetitions i) → Cfg}
    {g : PaddedMixedWidthLookupOpeningFamily.Geometry 2 (1+finalC) (2*finalD+1) (∑ i, repetitions i)}
    {symbolWidth : PaddedMixedWidthLookupOpeningFamily.Root (2*finalD+1) (∑ i, repetitions i) → ℕ}

/-- Complete-witness increment coverage, with public routing and initial
history conditions separated from the operational proof. -/
structure CompleteCoverage (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^cells*(2^lanes) = 2^(finalC+2)) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (zeroNodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (zeroBase : Memory → ZeroScheme)
    (accLength : 2^accC*accB = 2^(finalC+2)) (inputReference : NativeGoldParameterStore.Reference)
    (inputLength : 2^finalC*4 = 2^(finalC+2)) (inputSmall : 2*4 ≤ q) (inputBase : Memory → InputScheme)

    (finalFamily : PackedPBSOriginalReferences.Family finalD) (finalNodes : 2*4 ≤ q)
    (finalLength : 2^finalC*4 = 2^(finalC+2))
    (finalBase : Fin (finalD+1) → Memory → PaddedNTT.Scheme (ZMod q) Input Digest Cfg FinalResponse Memory FinalCommitMemory first.heights 4 finalC 1 4)
    [∀ index memory side, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((finalBase index memory).code side).front) 4)]
    [∀ index memory side, SampleableType (Fin ((finalBase index memory).code side).queries → Fin (2^first.heights ((finalBase index memory).tag side)))]

    (productFirstSmall : (2*4-1)*2+1 ≤ q) (productRoundSmall : (2*4-1)*3+1 ≤ q)
    (productNodes : 2*4 ≤ (2*4-1)*2+1)
    (productBase : Memory → KeySwitchPaddedProduct.Scheme (q := q) (d := finalD) (b := 4) (n := finalC)
      (Input := Input) (Cfg := Cfg) (Response := ProductResponse) (Memory := Memory) (CommitMemory := ProductCommitMemory) (heights := first.heights))
    [∀ memory factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((productBase memory).code factor).front) 4)]
    [∀ memory factor, SampleableType (Fin ((productBase memory).code factor).queries → Fin (2^first.heights ((productBase memory).tag factor)))]

    (reconstructionBase : Memory → PaddedLinear.Scheme (ZMod q) Input Digest Cfg ReconstructionResponse Memory ReconstructionCommitMemory first.heights (2*finalD+2) 4 (1+finalC))
    [∀ memory factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((reconstructionBase memory).code factor).front) 4)]
    [∀ memory factor, SampleableType (Fin ((reconstructionBase memory).code factor).queries → Fin (2^first.heights ((reconstructionBase memory).tag factor)))]
    (comparisonBase : (memory : Memory) → PackedPBSComparisonStage.Scheme Cfg Input Memory ((Fin (∑ i, repetitions i) → Digest) × RetainedMemory) FinalResult finalD)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (original : NativeKeySwitch.Key q (2^(finalC+2)) finalD)
    (setupParameters : Fin finalD → RecordedPaddedSource.Parameters (ZMod q) Cfg first.heights 4)
 : Prop where
  verified :
    ∀
    (finalCapacity : ∀ index memory side, 2^((finalBase index memory).code side).suffix ≤ ((finalBase index memory).code side).m*4)
    (finalRadius : Fin (finalD+1) → Memory → Bool → ℕ)
    (productCapacity : ∀ memory factor, 2^((productBase memory).code factor).suffix ≤ ((productBase memory).code factor).m*4)
    (productRadius : Memory → PBSHadamard.Factor finalD → ℕ)
    (_ : HonestKeyQueryReceipt.Receipt setupParameters hs.encoding psi original finalFamily.keys initial.hash.log)
    (_ : CachedHashHandler.Coherent initial.hash ∧
      RecordedCheckpointQueries.Sound (RecordedSourceCoherence.Shape Cfg height) initial)
    (_ : ∀ memory level, setupParameters level =
      ExecutedHonestProductKey.parameters (productBase memory) (productCapacity memory) (productRadius memory) level)
    (_ : ∀ level, (setupParameters level).degree ≤ 2^first.heights (setupParameters level).tag)
    (_ : ∀ level, 2*(setupParameters level).radius <
      Code.minDist (BlockCode.code (setupParameters level).domain (setupParameters level).degree 4 :
        Set (Fin (2^first.heights (setupParameters level).tag) → Fin 4 → ZMod q)))
    (_ : ∀ level, finalC+1 ≤ (setupParameters level).front+(setupParameters level).suffix)
    (reconstructionCapacity : ∀ memory factor, 2^((reconstructionBase memory).code factor).suffix ≤ ((reconstructionBase memory).code factor).m*4)
    (reconstructionRadius : Memory → Fin (2*finalD+2) → ℕ)
    (inputCapacity : 2^inputSuffix ≤ inputM*4) (inputRadius : ℕ)
    (inputGeometry : ∀ memory, first.heights ((inputBase memory).tag) = inputHeight)
    (config : Memory → RectangularRequestLookup.Parameters (ZMod q) K LookupMessage LookupMemory Cfg Input Digest Memory ConfigHelperMemory
      3 1 2 (1+finalC) (2*finalD+1) finalD (fun _ => 3) (fun _ => (2^bits)*2) repetitions mode)
    (domain : ∀ root, Fin (2^first.heights (tag root)) ↪ ZMod q)
    (lookupCapacity : ∀ root, 2^g.suffix root ≤ g.m root * symbolWidth root)
    (lookupRadius : PaddedMixedWidthLookupOpeningFamily.Root (2*finalD+1) (∑ i, repetitions i) → ℕ)
    (sourceSymbols : ∀ source, symbolWidth (.inl source) = 4)
    (_ : ∀ (level : Fin finalD) memory reconstructionMemory, PaddedStageSourceInterpretation.nttParameters
      (KeySwitchPaddedNTT.factory finalBase hs.encoding finalFamily finalNodes finalLength psi primitive (Fin.castSucc level) memory)
      (finalCapacity (Fin.castSucc level) memory) (finalRadius (Fin.castSucc level) memory) false =
      PaddedStageSourceInterpretation.linearParameters
        (KeySwitchPaddedReconstruction.stage (reconstructionBase reconstructionMemory) hs.encoding inputReference finalFamily finalNodes (2^bits : ZMod q))
        (reconstructionCapacity reconstructionMemory) (reconstructionRadius reconstructionMemory) (DecompositionLinear.digit level))
    (_ : ∀ index memory productMemory, PaddedStageSourceInterpretation.nttParameters
      (KeySwitchPaddedNTT.factory finalBase hs.encoding finalFamily finalNodes finalLength psi primitive index memory)
      (finalCapacity index memory) (finalRadius index memory) true =
      PaddedStageSourceInterpretation.zeroParameters
        (KeySwitchPaddedProduct.stage (productBase productMemory) hs.encoding finalFamily productFirstSmall productRoundSmall productNodes)
        (productCapacity productMemory) (productRadius productMemory) (PackedPBSOriginalReferences.evaluationFactor index))
    (_ : ∀ knownMemory reconstructionMemory, DecodedKnownInput.parameters (c := finalC) (lanes := 2) (inputBase knownMemory)
      first.heights (inputGeometry knownMemory) inputCapacity inputRadius =
      PaddedStageSourceInterpretation.linearParameters
        (KeySwitchPaddedReconstruction.stage (reconstructionBase reconstructionMemory) hs.encoding inputReference finalFamily finalNodes (2^bits : ZMod q))
        (reconstructionCapacity reconstructionMemory) (reconstructionRadius reconstructionMemory) DecompositionLinear.input)
    (_ : ∀ memory source, RectangularLookupSourceInterpretation.squareParameters (d := 3) (padding := 1) (g := g) (tag := tag) (symbolWidth := symbolWidth) domain lookupCapacity lookupRadius sourceSymbols source =
      PaddedStageSourceInterpretation.linearParameters
        (KeySwitchPaddedReconstruction.stage (reconstructionBase memory) hs.encoding inputReference finalFamily finalNodes (2^bits : ZMod q))
        (reconstructionCapacity memory) (reconstructionRadius memory) (PackedPBSComparisonReferences.linearSlot source))
    (_ : ∀ memory, (config memory).slots = RadixLookupSources.comparisonSlots)
    (_ : ∀ memory, (config memory).tables = fun limb => RadixLookupSources.publicTable q (2^bits)
      (RadixCanonicity.modulusDigit q (2^bits) limb.val))
    (_ : ∀ memory limb, (config memory).active limb = 2^(2+(1+finalC)))
    (_ : 1 < 2^bits) (_ : 2^bits < q) (_ : q-1 < (2^bits)^finalD)
    (_ : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape first.heights) initial.checkpoints)
    (_ : CheckpointRecordScope.Scoped
      (fun cfg => RecordedSourceCoherence.Shape Cfg height cfg = BinaryTree.Skeleton.perfect (first.heights cfg))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase))
    (_ : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial)
    (before : _) (result : _)
    (_ : (before,some result) ∈ support (@PackedPBSKeySwitchComparisons.witness q (finalC+2) d b c r k n front suffix m queries height (inferInstance) Input Cfg Response Memory CommitMemory FirstMessage Message (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) length psi primitive family inputs base hs nodesEnough radix linearBase Helper Selection Root Data SecondHelper SecondSelection SecondRoot SecondData AccResponse accB accC accR accFront accSuffix accM accQueries accHeight (inferInstance) (inferInstance) (inferInstance) lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight (inferInstance) (inferInstance) (inferInstance) (inferInstance) ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight (inferInstance) (inferInstance) (inferInstance) (inferInstance) InputResponse InputCommitMemory 4 finalC inputFront inputSuffix inputM inputQueries inputHeight (inferInstance) (inferInstance) (inferInstance) FinalResponse FinalCommitMemory finalD 4 finalC (inferInstance) (inferInstance) ProductResponse ProductCommitMemory (inferInstance) (inferInstance) ReconstructionResponse ReconstructionCommitMemory (fun _ : Memory => (Fin (∑ i, repetitions i) → Digest) × RetainedMemory) (fun _ : Memory => FinalResult) dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase (inferInstance) (inferInstance) productFirstSmall productRoundSmall productNodes productBase (inferInstance) (inferInstance) (2^bits : ZMod q) reconstructionBase (inferInstance) (inferInstance) comparisonBase initial)),
    ∃ product ntts known monomial accumulator,
      before.1.2 = some product ∧ before.1.1.2 = some ntts ∧ before.1.1.1.2 = some known ∧
      before.1.1.1.1.2 = some monomial ∧ before.1.1.1.1.1.1.2 = some accumulator ∧
      ∃ (nttSupported : ntts ∈ support (KeySwitchPaddedNTT.witness finalBase hs.encoding finalFamily finalNodes finalLength psi primitive dummy known.2.1.2.memory known.2.2)) (nttPassed : ntts.1.accepted = true)
        (_ : product.2 ∈ support (PaddedZeroCheck.witness (KeySwitchPaddedProduct.stage (productBase product.1) hs.encoding finalFamily productFirstSmall productRoundSmall productNodes) dummy ntts.2))
        (nttRetained : CheckpointHistoryChain.Retains ntts.2 result.2.2.2.2)
        (_ : CheckpointHistoryChain.Retains product.2.2.2 result.2.2.2.2),
      ExecutedHonestKeySwitchIncrement.Coverage (c := finalC) (bits := bits) (tag := tag) (g := g) (symbolWidth := symbolWidth)
      (base := finalBase) (enc := hs.encoding) (family := finalFamily) (nodesEnough := finalNodes) (psi := psi) (primitive := primitive) (dummy := dummy) (memory := known.2.1.2.memory) (initial := known.2.2) (outcome := ntts) (supported := nttSupported) (capacity := finalCapacity) (radius := finalRadius) (passes := nttPassed) (state := result.2.2.2.2) (nttRetained := nttRetained) (reconstruction := reconstructionBase result.1.1) (input := inputReference) (reconstructionCapacity := reconstructionCapacity result.1.1) (reconstructionRadius := reconstructionRadius result.1.1) (reconstructionOutcome := result.1.2) (product := productBase product.1) (firstSmall := productFirstSmall) (roundSmall := productRoundSmall) (productNodes := productNodes) (productCapacity := productCapacity product.1) (productRadius := productRadius product.1) (productOutcome := product.2) (known := inputBase monomial.2.1.2.memory) (accumulator := AccumulatorEndpoint.value accLength (factory accumulator.1.1.2).context) (knownCapacity := inputCapacity) (knownRadius := inputRadius) (knownOutcome := known) (comparison := comparisonBase result.1.1) (comparisonOutcome := result.2) (config := config result.1.1) (domain := domain) (lookupCapacity := lookupCapacity) (lookupRadius := lookupRadius) original

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- Extract and retain the actual complete key-switch tail, then derive its
canonical increment or executed failure events without replay/semantic premises. -/
theorem increment_coverage (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^cells*(2^lanes) = 2^(finalC+2)) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (zeroNodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (zeroBase : Memory → ZeroScheme)
    (accLength : 2^accC*accB = 2^(finalC+2)) (inputReference : NativeGoldParameterStore.Reference)
    (inputLength : 2^finalC*4 = 2^(finalC+2)) (inputSmall : 2*4 ≤ q) (inputBase : Memory → InputScheme)

    (finalFamily : PackedPBSOriginalReferences.Family finalD) (finalNodes : 2*4 ≤ q)
    (finalLength : 2^finalC*4 = 2^(finalC+2))
    (finalBase : Fin (finalD+1) → Memory → PaddedNTT.Scheme (ZMod q) Input Digest Cfg FinalResponse Memory FinalCommitMemory first.heights 4 finalC 1 4)
    [∀ index memory side, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((finalBase index memory).code side).front) 4)]
    [∀ index memory side, SampleableType (Fin ((finalBase index memory).code side).queries → Fin (2^first.heights ((finalBase index memory).tag side)))]

    (productFirstSmall : (2*4-1)*2+1 ≤ q) (productRoundSmall : (2*4-1)*3+1 ≤ q)
    (productNodes : 2*4 ≤ (2*4-1)*2+1)
    (productBase : Memory → KeySwitchPaddedProduct.Scheme (q := q) (d := finalD) (b := 4) (n := finalC)
      (Input := Input) (Cfg := Cfg) (Response := ProductResponse) (Memory := Memory) (CommitMemory := ProductCommitMemory) (heights := first.heights))
    [∀ memory factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((productBase memory).code factor).front) 4)]
    [∀ memory factor, SampleableType (Fin ((productBase memory).code factor).queries → Fin (2^first.heights ((productBase memory).tag factor)))]

    (reconstructionBase : Memory → PaddedLinear.Scheme (ZMod q) Input Digest Cfg ReconstructionResponse Memory ReconstructionCommitMemory first.heights (2*finalD+2) 4 (1+finalC))
    [∀ memory factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((reconstructionBase memory).code factor).front) 4)]
    [∀ memory factor, SampleableType (Fin ((reconstructionBase memory).code factor).queries → Fin (2^first.heights ((reconstructionBase memory).tag factor)))]
    (comparisonBase : (memory : Memory) → PackedPBSComparisonStage.Scheme Cfg Input Memory ((Fin (∑ i, repetitions i) → Digest) × RetainedMemory) FinalResult finalD)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (original : NativeKeySwitch.Key q (2^(finalC+2)) finalD)
    (setupParameters : Fin finalD → RecordedPaddedSource.Parameters (ZMod q) Cfg first.heights 4)
 : @CompleteCoverage q finalC finalD bits d b c r k n front suffix m queries height (by assumption) Input Cfg Response Memory CommitMemory FirstMessage Message (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) length psi primitive family inputs base hs nodesEnough radix linearBase Helper Selection Root Data SecondHelper SecondSelection SecondRoot SecondData AccResponse accB accC accR accFront accSuffix accM accQueries accHeight (by assumption) (by assumption) (by assumption) lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight (by assumption) (by assumption) (by assumption) (by assumption) ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight (by assumption) (by assumption) (by assumption) (by assumption) InputResponse InputCommitMemory inputFront inputSuffix inputM inputQueries inputHeight (by assumption) (by assumption) (by assumption) FinalResponse FinalCommitMemory (by assumption) ProductResponse ProductCommitMemory (by assumption) (by assumption) ReconstructionResponse ReconstructionCommitMemory K LookupMessage LookupMemory ConfigHelperMemory RetainedMemory FinalResult (by assumption) (by assumption) repetitions mode tag g symbolWidth dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase (by assumption) (by assumption) productFirstSmall productRoundSmall productNodes productBase (by assumption) (by assumption) reconstructionBase (by assumption) (by assumption) comparisonBase initial original setupParameters := by
  refine @CompleteCoverage.mk q finalC finalD bits d b c r k n front suffix m queries height (by assumption) Input Cfg Response Memory CommitMemory FirstMessage Message (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) length psi primitive family inputs base hs nodesEnough radix linearBase Helper Selection Root Data SecondHelper SecondSelection SecondRoot SecondData AccResponse accB accC accR accFront accSuffix accM accQueries accHeight (by assumption) (by assumption) (by assumption) lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight (by assumption) (by assumption) (by assumption) (by assumption) ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight (by assumption) (by assumption) (by assumption) (by assumption) InputResponse InputCommitMemory inputFront inputSuffix inputM inputQueries inputHeight (by assumption) (by assumption) (by assumption) FinalResponse FinalCommitMemory (by assumption) ProductResponse ProductCommitMemory (by assumption) (by assumption) ReconstructionResponse ReconstructionCommitMemory K LookupMessage LookupMemory ConfigHelperMemory RetainedMemory FinalResult (by assumption) (by assumption) repetitions mode tag g symbolWidth dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase (by assumption) (by assumption) productFirstSmall productRoundSmall productNodes productBase (by assumption) (by assumption) reconstructionBase (by assumption) (by assumption) comparisonBase initial original setupParameters ?_
  intro finalCapacity finalRadius productCapacity productRadius setupReceipt initialValid setupGeometry honestDegree honestMargin honestFits reconstructionCapacity reconstructionRadius inputCapacity inputRadius inputGeometry config domain lookupCapacity lookupRadius sourceSymbols coefficientRouting evaluationRouting knownRouting lookupRouting slotOrder publicTables full radixLarge radixSmall enough compatible restricted auditedInitial before result supported
  let reachedFn := @PackedPBSReachedKeySwitch.input_facts q (finalC+2) d b c r k n front suffix m queries height (inferInstance) Input Cfg Response Memory CommitMemory FirstMessage Message (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) length psi primitive family inputs base hs nodesEnough radix linearBase Helper Selection Root Data SecondHelper SecondSelection SecondRoot SecondData AccResponse accB accC accR accFront accSuffix accM accQueries accHeight (inferInstance) (inferInstance) (inferInstance) lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight (inferInstance) (inferInstance) (inferInstance) (inferInstance) ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight (inferInstance) (inferInstance) (inferInstance) (inferInstance) InputResponse InputCommitMemory 4 finalC inputFront inputSuffix inputM inputQueries inputHeight (inferInstance) (inferInstance) (inferInstance) FinalResponse FinalCommitMemory finalD 4 finalC (inferInstance) (inferInstance) ProductResponse ProductCommitMemory (inferInstance) (inferInstance) ReconstructionResponse ReconstructionCommitMemory (fun _ : Memory => (Fin (∑ i, repetitions i) → Digest) × RetainedMemory) (fun _ : Memory => FinalResult) dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase (inferInstance) (inferInstance) productFirstSmall productRoundSmall productNodes productBase (inferInstance) (inferInstance) (2^bits : ZMod q) reconstructionBase (inferInstance) (inferInstance) comparisonBase initial
  let transferred := transfer_support _ (@PackedPBSKeySwitchComparisons.witness q (finalC+2) d b c r k n front suffix m queries height (inferInstance) Input Cfg Response Memory CommitMemory FirstMessage Message (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) length psi primitive family inputs base hs nodesEnough radix linearBase Helper Selection Root Data SecondHelper SecondSelection SecondRoot SecondData AccResponse accB accC accR accFront accSuffix accM accQueries accHeight (inferInstance) (inferInstance) (inferInstance) lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight (inferInstance) (inferInstance) (inferInstance) (inferInstance) ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight (inferInstance) (inferInstance) (inferInstance) (inferInstance) InputResponse InputCommitMemory 4 finalC inputFront inputSuffix inputM inputQueries inputHeight (inferInstance) (inferInstance) (inferInstance) FinalResponse FinalCommitMemory finalD 4 finalC (inferInstance) (inferInstance) ProductResponse ProductCommitMemory (inferInstance) (inferInstance) ReconstructionResponse ReconstructionCommitMemory (fun _ : Memory => (Fin (∑ i, repetitions i) → Digest) × RetainedMemory) (fun _ : Memory => FinalResult) dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase (inferInstance) (inferInstance) productFirstSmall productRoundSmall productNodes productBase (inferInstance) (inferInstance) (2^bits : ZMod q) reconstructionBase (inferInstance) (inferInstance) comparisonBase initial) (by rfl) reachedFn
  have reached := @transferred before result @supported
  obtain ⟨⟨product,productPresent,productPassed,productBeforeSupported,
    ⟨⟨reconstructionMemory,reconstructionSupported⟩,
      ⟨ntts,nttPresent,nttPassed,nttBeforeSupported,
        ⟨⟨productMemory,productSupported⟩,
          ⟨known,knownPresent,knownPassed,knownBeforeSupported,
            ⟨nttSupported,⟨monomial,accumulator,monomialPresent,accumulatorPresent,monomialPassed,monomialBeforeSupported,knownSupported⟩⟩⟩⟩⟩⟩⟩,
    reconstructionBeforeSupported,reconstructionPresent,reconstructionPassed,comparisonSupported⟩ := reached
  have audited := @PackedPBSKeySwitchComparisons.audited_witness q (finalC+2) d b c r k n front suffix m queries height (inferInstance) Input Cfg Response Memory CommitMemory FirstMessage Message (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) length psi primitive family inputs base hs nodesEnough radix linearBase Helper Selection Root Data SecondHelper SecondSelection SecondRoot SecondData AccResponse accB accC accR accFront accSuffix accM accQueries accHeight (inferInstance) (inferInstance) (inferInstance) lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight (inferInstance) (inferInstance) (inferInstance) (inferInstance) ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight (inferInstance) (inferInstance) (inferInstance) (inferInstance) InputResponse InputCommitMemory 4 finalC inputFront inputSuffix inputM inputQueries inputHeight (inferInstance) (inferInstance) (inferInstance) FinalResponse FinalCommitMemory finalD 4 finalC (inferInstance) (inferInstance) ProductResponse ProductCommitMemory (inferInstance) (inferInstance) ReconstructionResponse ReconstructionCommitMemory (fun _ : Memory => (Fin (∑ i, repetitions i) → Digest) × RetainedMemory) (fun _ : Memory => FinalResult) dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase (inferInstance) (inferInstance) productFirstSmall productRoundSmall productNodes productBase (inferInstance) (inferInstance) (2^bits : ZMod q) reconstructionBase (inferInstance) (inferInstance) comparisonBase initial compatible restricted auditedInitial (before,some result) (@supported)
  have history := @PackedPBSComparisonQueryHistory.query_history q (finalC+2) d b c r k n front suffix m queries height (inferInstance) Input Cfg Response Memory CommitMemory FirstMessage Message (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) length psi primitive family inputs base hs nodesEnough radix linearBase Helper Selection Root Data SecondHelper SecondSelection SecondRoot SecondData AccResponse accB accC accR accFront accSuffix accM accQueries accHeight (inferInstance) (inferInstance) (inferInstance) lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight (inferInstance) (inferInstance) (inferInstance) (inferInstance) ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight (inferInstance) (inferInstance) (inferInstance) (inferInstance) InputResponse InputCommitMemory 4 finalC inputFront inputSuffix inputM inputQueries inputHeight (inferInstance) (inferInstance) (inferInstance) FinalResponse FinalCommitMemory finalD 4 finalC (inferInstance) (inferInstance) ProductResponse ProductCommitMemory (inferInstance) (inferInstance) ReconstructionResponse ReconstructionCommitMemory (fun _ : Memory => (Fin (∑ i, repetitions i) → Digest) × RetainedMemory) (fun _ : Memory => FinalResult) dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase (inferInstance) (inferInstance) productFirstSmall productRoundSmall productNodes productBase (inferInstance) (inferInstance) (2^bits : ZMod q) reconstructionBase (inferInstance) (inferInstance) comparisonBase initial compatible restricted initialValid (before,some result) (@supported)
  have nttHistory := @PackedPBSKeySwitchComparisons.ntt_retains_witness q (finalC+2) d b c r k n front suffix m queries height (inferInstance) Input Cfg Response Memory CommitMemory FirstMessage Message (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) length psi primitive family inputs base hs nodesEnough radix linearBase Helper Selection Root Data SecondHelper SecondSelection SecondRoot SecondData AccResponse accB accC accR accFront accSuffix accM accQueries accHeight (inferInstance) (inferInstance) (inferInstance) lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight (inferInstance) (inferInstance) (inferInstance) (inferInstance) ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight (inferInstance) (inferInstance) (inferInstance) (inferInstance) InputResponse InputCommitMemory 4 finalC inputFront inputSuffix inputM inputQueries inputHeight (inferInstance) (inferInstance) (inferInstance) FinalResponse FinalCommitMemory finalD 4 finalC (inferInstance) (inferInstance) ProductResponse ProductCommitMemory (inferInstance) (inferInstance) ReconstructionResponse ReconstructionCommitMemory (fun _ : Memory => (Fin (∑ i, repetitions i) → Digest) × RetainedMemory) (fun _ : Memory => FinalResult) dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase (inferInstance) (inferInstance) productFirstSmall productRoundSmall productNodes productBase (inferInstance) (inferInstance) (2^bits : ZMod q) reconstructionBase (inferInstance) (inferInstance) comparisonBase initial (before,some result) (@supported)
  have productHistory := @PackedPBSKeySwitchComparisons.product_retains_witness q (finalC+2) d b c r k n front suffix m queries height (inferInstance) Input Cfg Response Memory CommitMemory FirstMessage Message (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) length psi primitive family inputs base hs nodesEnough radix linearBase Helper Selection Root Data SecondHelper SecondSelection SecondRoot SecondData AccResponse accB accC accR accFront accSuffix accM accQueries accHeight (inferInstance) (inferInstance) (inferInstance) lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight (inferInstance) (inferInstance) (inferInstance) (inferInstance) ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight (inferInstance) (inferInstance) (inferInstance) (inferInstance) InputResponse InputCommitMemory 4 finalC inputFront inputSuffix inputM inputQueries inputHeight (inferInstance) (inferInstance) (inferInstance) FinalResponse FinalCommitMemory finalD 4 finalC (inferInstance) (inferInstance) ProductResponse ProductCommitMemory (inferInstance) (inferInstance) ReconstructionResponse ReconstructionCommitMemory (fun _ : Memory => (Fin (∑ i, repetitions i) → Digest) × RetainedMemory) (fun _ : Memory => FinalResult) dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase (inferInstance) (inferInstance) productFirstSmall productRoundSmall productNodes productBase (inferInstance) (inferInstance) (2^bits : ZMod q) reconstructionBase (inferInstance) (inferInstance) comparisonBase initial (before,some result) (@supported)
  have reconstructionHistory := @PackedPBSKeySwitchComparisons.reconstruction_retains_witness q (finalC+2) d b c r k n front suffix m queries height (inferInstance) Input Cfg Response Memory CommitMemory FirstMessage Message (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) length psi primitive family inputs base hs nodesEnough radix linearBase Helper Selection Root Data SecondHelper SecondSelection SecondRoot SecondData AccResponse accB accC accR accFront accSuffix accM accQueries accHeight (inferInstance) (inferInstance) (inferInstance) lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight (inferInstance) (inferInstance) (inferInstance) (inferInstance) ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight (inferInstance) (inferInstance) (inferInstance) (inferInstance) InputResponse InputCommitMemory 4 finalC inputFront inputSuffix inputM inputQueries inputHeight (inferInstance) (inferInstance) (inferInstance) FinalResponse FinalCommitMemory finalD 4 finalC (inferInstance) (inferInstance) ProductResponse ProductCommitMemory (inferInstance) (inferInstance) ReconstructionResponse ReconstructionCommitMemory (fun _ : Memory => (Fin (∑ i, repetitions i) → Digest) × RetainedMemory) (fun _ : Memory => FinalResult) dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase (inferInstance) (inferInstance) productFirstSmall productRoundSmall productNodes productBase (inferInstance) (inferInstance) (2^bits : ZMod q) reconstructionBase (inferInstance) (inferInstance) comparisonBase initial (before,some result) (@supported)
  have nttRetained : CheckpointHistoryChain.Retains ntts.2 result.2.2.2.2 := by
    simpa only [PackedPBSKeySwitchProduct.beforeState,nttPresent,PackedPBSKeySwitchComparisons.finalState,
      RetainedPaddedComparison.finalState,DependentStageContinuation.finalState] using nttHistory
  have productRetained : CheckpointHistoryChain.Retains product.2.2.2 result.2.2.2.2 := by
    simpa only [PackedPBSKeySwitchProduct.finalState,productPresent,PackedPBSKeySwitchComparisons.finalState,
      RetainedPaddedComparison.finalState,DependentStageContinuation.finalState] using productHistory
  have reconstructionRetained : CheckpointHistoryChain.Retains result.1.2.2.2 result.2.2.2.2 := by
    simpa only [PackedPBSKeySwitchReconstruction.finalState,reconstructionPresent,PackedPBSKeySwitchComparisons.finalState,
      RetainedPaddedComparison.finalState,DependentStageContinuation.finalState] using reconstructionHistory
  have knownRetained : CheckpointHistoryChain.Retains known.2.2 result.2.2.2.2 := by
    apply CheckpointHistoryChain.trans (second := ntts.2) ?_ nttRetained
    intro cfg saved recorded
    exact PaddedNTTSequence.retains (KeySwitchPaddedNTT.factory finalBase hs.encoding finalFamily finalNodes finalLength psi primitive) hs.encoding dummy (List.finRange (finalD+1))
      known.2.1.2.memory known.2.2 ntts nttSupported cfg saved recorded
  refine ⟨product,ntts,known,monomial,accumulator,productPresent,nttPresent,knownPresent,monomialPresent,accumulatorPresent,
    nttSupported,nttPassed,productSupported,nttRetained,productRetained,?_⟩
  have covered := ExecutedKeySwitchIncrement.increment_or_risks finalBase hs.encoding finalFamily finalNodes psi primitive dummy
    known.2.1.2.memory known.2.2 ntts nttSupported finalCapacity finalRadius nttPassed result.2.2.2.2 nttRetained
    (reconstructionBase result.1.1) inputReference (reconstructionCapacity result.1.1) (reconstructionRadius result.1.1)
    product.2.2.2 result.1.2 reconstructionSupported reconstructionRetained
    (productBase product.1) productFirstSmall productRoundSmall productNodes (productCapacity product.1) (productRadius product.1)
    ntts.2 product.2 productSupported productRetained (inputBase monomial.2.1.2.memory) (AccumulatorEndpoint.value accLength (factory accumulator.1.1.2).context) inputCapacity inputRadius
    monomial.2.2 known knownSupported (inputGeometry monomial.2.1.2.memory) knownRetained
    (comparisonBase result.1.1) result.2 comparisonSupported (CheckpointHistoryChain.refl _)
    (config result.1.1) domain lookupCapacity lookupRadius sourceSymbols
    (fun level memory => coefficientRouting level memory result.1.1)
    (fun index memory => evaluationRouting index memory product.1)
    (knownRouting monomial.2.1.2.memory result.1.1) (lookupRouting result.1.1)
    audited knownPassed productPassed (slotOrder result.1.1) (publicTables result.1.1) (full result.1.1)
    radixLarge radixSmall enough

  rcases covered with correct | failure
  · have nttHistory := PackedPBSNTTQueryHistory.query_history length psi primitive family inputs base hs nodesEnough radix linearBase
      dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough
      rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase
      initial compatible restricted initialValid before.1.1 nttBeforeSupported
    have logPrefix : initial.hash.log <+: ntts.2.hash.log := by
      simpa only [PackedPBSKeySwitchNTT.finalState,nttPresent] using nttHistory.1
    have sourceReceipt := HonestKeyQueryReceipt.parameters_congr setupParameters
      (ExecutedHonestProductKey.parameters (productBase product.1) (productCapacity product.1) (productRadius product.1))
      (setupGeometry product.1) hs.encoding psi original finalFamily.keys initial.hash.log setupReceipt
    have receipt := HonestKeyQueryReceipt.mono _ hs.encoding psi original finalFamily.keys
      initial.hash.log ntts.2.hash.log logPrefix sourceReceipt
    have sound : RecordedCheckpointQueries.Sound (AmbientMatrixSource.Shape first.heights) result.2.2.2.2 := by
      simpa only [PackedPBSKeySwitchComparisons.finalState,RetainedPaddedComparison.finalState,
        DependentStageContinuation.finalState] using history.2.2
    have honest := ExecutedProductKeyReceipt.key_eq_or_bad (productBase product.1) (productCapacity product.1) (productRadius product.1)
      hs.encoding dummy psi primitive original finalFamily productFirstSmall productRoundSmall productNodes
      ntts.2 receipt product.2 productSupported result.2.2.2.2 productRetained audited sound
      (fun level => by simpa only [setupGeometry product.1 level] using honestDegree level)
      (fun level => HonestKeyQueryReceipt.margin_congr _ _ (setupGeometry product.1 level) (honestMargin level))
      (fun level => by simpa only [setupGeometry product.1 level] using honestFits level)
    dsimp only at honest
    rcases honest with keyEqual | bad
    · left
      dsimp only [ExecutedKeySwitchIncrement.Correct] at correct
      dsimp only [ExecutedHonestKeySwitchIncrement.Correct]
      rw [keyEqual] at correct
      exact correct
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr bad)))))
  · exact Or.inr failure

end
end FormalProof4FHE.HasteBoots.PackedPBSHonestIncrement
