module
public import FormalProof4FHE.HasteBoots.PackedPBSHonestAcceptedIncrement
@[expose] public section

/-! Correctness and accepted incorrect-increment events for the actual selected
key-switch operations in the complete retained PBS execution. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSHonestIncrementEvents
open OracleSpec OracleComp
open PackedPBSKeySwitchComparisons
open NativeRootMessage (Digest)
open PackedPBSSecondComparisons (sharedScheme)
noncomputable section

-- Keep support opaque: elaboration needs program equality, not execution reduction.
attribute [local irreducible] MonadAttach.support
/-- Read the actual return type of a probability computation. -/
abbrev ExecutionResult {A : Type} (_ : ProbComp A) : Type := A

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

variable {Helper Selection Root Data : Type}

variable {SecondHelper SecondSelection SecondRoot SecondData : Type}

variable {AccResponse : Type} {accB accC accR accFront accSuffix accM accQueries accHeight : ℕ}
  [SampleableType (Fin accB → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^accFront) accB)]
  [SampleableType (Fin accQueries → Fin (2^accHeight))]

variable {lanes cells rows rounds : ℕ}

variable {MonoResponse MonoCommitMemory : Type} {monoK monoFront monoSuffix monoM monoQueries monoHeight : ℕ}
  [SampleableType (Fin monoK → Fin (rows+1) → ZMod q)] [SampleableType (Fin (2^lanes) → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^monoFront) (2^lanes))]
  [SampleableType (Fin monoQueries → Fin (2^monoHeight))]

variable {ZeroResponse ZeroCommitMemory : Type} {zeroFront zeroSuffix zeroM zeroQueries zeroHeight : ℕ}
  [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (PackedZeroReduction.Points (ZMod q) (cells+rows) (2^lanes))]
  [SampleableType (Fin (2^lanes) → Fin (2^lanes) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^zeroFront) (2^lanes))]
  [SampleableType (Fin zeroQueries → Fin (2^zeroHeight))]

variable {InputResponse InputCommitMemory : Type} {inputFront inputSuffix inputM inputQueries inputHeight : ℕ}
  [SampleableType (Fin 4 → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^inputFront) 4)]
  [SampleableType (Fin inputQueries → Fin (2^inputHeight))]

variable {FinalResponse FinalCommitMemory : Type}
  [SampleableType (Fin 4 → Fin 1 → ZMod q)]

variable {ProductResponse ProductCommitMemory : Type}
  [SampleableType (PackedZeroReduction.Points (ZMod q) finalC 4)]
  [SampleableType (Fin 4 → Fin 4 → ZMod q)]

variable {ReconstructionResponse ReconstructionCommitMemory : Type}

open scoped BigOperators
variable {K LookupMessage LookupMemory ConfigHelperMemory RetainedMemory FinalSelection FinalRoot FinalData : Type}
    [Field K] [Algebra (ZMod q) K]
    {repetitions : Fin finalD → ℕ} {mode : MixedWidthSharedLookupPCSAlgebra.Mode}
    {tag : PaddedMixedWidthLookupOpeningFamily.Root (2*finalD+1) (∑ i, repetitions i) → Cfg}
    {g : PaddedMixedWidthLookupOpeningFamily.Geometry 2 (1+finalC) (2*finalD+1) (∑ i, repetitions i)}
    {symbolWidth : PaddedMixedWidthLookupOpeningFamily.Root (2*finalD+1) (∑ i, repetitions i) → ℕ}

variable (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper (PackedPBSKeySwitchReconstruction.ComparisonReturn (Selection := Selection) (Root := Root) (Data := Data) (Memory := Memory)) d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper (SecondSelection × ShortCircuitSequence.Outcome SecondRoot SecondData Memory) d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → (AmbientAccumulator.Scheme (ZMod q) Input Digest Cfg AccResponse Memory Memory
  accB accC accR accFront accSuffix accM accQueries accHeight))
    (monoLength : 2^cells*(2^lanes) = 2^(finalC+2)) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → (AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg MonoResponse Memory MonoCommitMemory
  (2^lanes) cells (rows+1) monoK monoFront monoSuffix monoM monoQueries monoHeight))
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (zeroNodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (zeroBase : Memory → (AuthenticatedPublicZeroCheck.Scheme (ZMod q) Bool Unit Bool
  (Fin (2^lanes) → Fin ((2*(2^lanes)-1)*2+1) → ZMod q) (Fin ((2*(2^lanes)-1)*3+1) → ZMod q)
  Input Digest Cfg ZeroResponse Memory ZeroCommitMemory (2^lanes) (cells+rows) zeroFront zeroSuffix zeroM zeroQueries zeroHeight))
    (accLength : 2^accC*accB = 2^(finalC+2)) (inputReference : NativeGoldParameterStore.Reference)
    (inputLength : 2^finalC*4 = 2^(finalC+2)) (inputSmall : 2*4 ≤ q) (inputBase : Memory → (AmbientKnownInput.Scheme (ZMod q) Input Digest Cfg InputResponse Memory InputCommitMemory
  4 (1+finalC) inputFront inputSuffix inputM inputQueries inputHeight))

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
    (comparisonBase : (memory : Memory) → PackedPBSComparisonStage.Scheme Cfg Input Memory ((Fin (∑ i, repetitions i) → Digest) × RetainedMemory) (FinalSelection × ShortCircuitSequence.Outcome FinalRoot FinalData Memory) finalD)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))

variable
    (finalCapacity : ∀ index memory side, 2^((finalBase index memory).code side).suffix ≤ ((finalBase index memory).code side).m*4)
    (finalRadius : Fin (finalD+1) → Memory → Bool → ℕ)
    (productCapacity : ∀ memory factor, 2^((productBase memory).code factor).suffix ≤ ((productBase memory).code factor).m*4)
    (productRadius : Memory → PBSHadamard.Factor finalD → ℕ)
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

variable (original : NativeKeySwitch.Key q (2^(finalC+2)) finalD)

/-- Canonical increment correctness for the operations stored by this execution's
returned comparison, using its supported operations and retained history. -/
def CorrectOutput : ExecutionResult (@PackedPBSKeySwitchComparisons.witness q (finalC+2) d b c r k n front suffix m queries height (inferInstance) Input Cfg Response Memory CommitMemory FirstMessage Message (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) length psi primitive family inputs base hs nodesEnough radix linearBase Helper Selection Root Data SecondHelper SecondSelection SecondRoot SecondData AccResponse accB accC accR accFront accSuffix accM accQueries accHeight (inferInstance) (inferInstance) (inferInstance) lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight (inferInstance) (inferInstance) (inferInstance) (inferInstance) ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight (inferInstance) (inferInstance) (inferInstance) (inferInstance) InputResponse InputCommitMemory 4 finalC inputFront inputSuffix inputM inputQueries inputHeight (inferInstance) (inferInstance) (inferInstance) FinalResponse FinalCommitMemory finalD 4 finalC (inferInstance) (inferInstance) ProductResponse ProductCommitMemory (inferInstance) (inferInstance) ReconstructionResponse ReconstructionCommitMemory (fun _ : Memory => (Fin (∑ i, repetitions i) → Digest) × RetainedMemory) (fun _ : Memory => (FinalSelection × ShortCircuitSequence.Outcome FinalRoot FinalData Memory)) dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase (inferInstance) (inferInstance) productFirstSmall productRoundSmall productNodes productBase (inferInstance) (inferInstance) (2^bits : ZMod q) reconstructionBase (inferInstance) (inferInstance) comparisonBase initial) → Prop := by
  dsimp only [ExecutionResult]
  intro outcome
  exact ∃ compared, outcome.2 = some compared ∧
  ∃ product ntts known monomial accumulator,
      outcome.1.1.2 = some product ∧ outcome.1.1.1.2 = some ntts ∧ outcome.1.1.1.1.2 = some known ∧
      outcome.1.1.1.1.1.2 = some monomial ∧ outcome.1.1.1.1.1.1.1.2 = some accumulator ∧
      ∃ (nttSupported : ntts ∈ support (KeySwitchPaddedNTT.witness finalBase hs.encoding finalFamily finalNodes finalLength psi primitive dummy known.2.1.2.memory known.2.2)) (nttPassed : ntts.1.accepted = true)
        (_ : product.2 ∈ support (PaddedZeroCheck.witness (KeySwitchPaddedProduct.stage (productBase product.1) hs.encoding finalFamily productFirstSmall productRoundSmall productNodes) dummy ntts.2))
        (nttRetained : CheckpointHistoryChain.Retains ntts.2 compared.2.2.2.2)
        (_ : CheckpointHistoryChain.Retains product.2.2.2 compared.2.2.2.2),
      ExecutedHonestKeySwitchIncrement.Correct (c := finalC) (bits := bits)
      (base := finalBase) (enc := hs.encoding) (family := finalFamily) (nodesEnough := finalNodes) (psi := psi) (primitive := primitive) (dummy := dummy) (memory := known.2.1.2.memory) (initial := known.2.2) (outcome := ntts) (supported := nttSupported) (capacity := finalCapacity) (radius := finalRadius) (passes := nttPassed) (state := compared.2.2.2.2) (nttRetained := nttRetained) (accumulator := AccumulatorEndpoint.value accLength (factory accumulator.1.1.2).context) original

/-- The actual returned comparison accepts, but the selected operations do
not satisfy the original-key canonical increment equality in the retained history. -/
def AcceptedFalse : ExecutionResult (@PackedPBSKeySwitchComparisons.witness q (finalC+2) d b c r k n front suffix m queries height (inferInstance) Input Cfg Response Memory CommitMemory FirstMessage Message (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) length psi primitive family inputs base hs nodesEnough radix linearBase Helper Selection Root Data SecondHelper SecondSelection SecondRoot SecondData AccResponse accB accC accR accFront accSuffix accM accQueries accHeight (inferInstance) (inferInstance) (inferInstance) lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight (inferInstance) (inferInstance) (inferInstance) (inferInstance) ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight (inferInstance) (inferInstance) (inferInstance) (inferInstance) InputResponse InputCommitMemory 4 finalC inputFront inputSuffix inputM inputQueries inputHeight (inferInstance) (inferInstance) (inferInstance) FinalResponse FinalCommitMemory finalD 4 finalC (inferInstance) (inferInstance) ProductResponse ProductCommitMemory (inferInstance) (inferInstance) ReconstructionResponse ReconstructionCommitMemory (fun _ : Memory => (Fin (∑ i, repetitions i) → Digest) × RetainedMemory) (fun _ : Memory => (FinalSelection × ShortCircuitSequence.Outcome FinalRoot FinalData Memory)) dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase (inferInstance) (inferInstance) productFirstSmall productRoundSmall productNodes productBase (inferInstance) (inferInstance) (2^bits : ZMod q) reconstructionBase (inferInstance) (inferInstance) comparisonBase initial) → Prop := by
  dsimp only [ExecutionResult]
  intro outcome
  exact ∃ compared, outcome.2 = some compared ∧ compared.2.2.2.1.2.accepted = true ∧
    ¬(@CorrectOutput q finalC finalD bits d b c r k n front suffix m queries height (by assumption) Input Cfg Response Memory CommitMemory FirstMessage Message (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) length psi primitive family inputs base hs nodesEnough radix linearBase Helper Selection Root Data SecondHelper SecondSelection SecondRoot SecondData AccResponse accB accC accR accFront accSuffix accM accQueries accHeight (by assumption) (by assumption) (by assumption) lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight (by assumption) (by assumption) (by assumption) (by assumption) ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight (by assumption) (by assumption) (by assumption) (by assumption) InputResponse InputCommitMemory inputFront inputSuffix inputM inputQueries inputHeight (by assumption) (by assumption) (by assumption) FinalResponse FinalCommitMemory (by assumption) ProductResponse ProductCommitMemory (by assumption) (by assumption) ReconstructionResponse ReconstructionCommitMemory RetainedMemory FinalSelection FinalRoot FinalData repetitions dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase (by assumption) (by assumption) productFirstSmall productRoundSmall productNodes productBase (by assumption) (by assumption) reconstructionBase (by assumption) (by assumption) comparisonBase initial finalCapacity finalRadius original outcome)

/-- The selected key-switch tail event and the same final history exception
used by the complete rectangular probability bound. -/
def TailFailure : ExecutionResult (@PackedPBSKeySwitchComparisons.witness q (finalC+2) d b c r k n front suffix m queries height (inferInstance) Input Cfg Response Memory CommitMemory FirstMessage Message (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) length psi primitive family inputs base hs nodesEnough radix linearBase Helper Selection Root Data SecondHelper SecondSelection SecondRoot SecondData AccResponse accB accC accR accFront accSuffix accM accQueries accHeight (inferInstance) (inferInstance) (inferInstance) lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight (inferInstance) (inferInstance) (inferInstance) (inferInstance) ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight (inferInstance) (inferInstance) (inferInstance) (inferInstance) InputResponse InputCommitMemory 4 finalC inputFront inputSuffix inputM inputQueries inputHeight (inferInstance) (inferInstance) (inferInstance) FinalResponse FinalCommitMemory finalD 4 finalC (inferInstance) (inferInstance) ProductResponse ProductCommitMemory (inferInstance) (inferInstance) ReconstructionResponse ReconstructionCommitMemory (fun _ : Memory => (Fin (∑ i, repetitions i) → Digest) × RetainedMemory) (fun _ : Memory => (FinalSelection × ShortCircuitSequence.Outcome FinalRoot FinalData Memory)) dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase (inferInstance) (inferInstance) productFirstSmall productRoundSmall productNodes productBase (inferInstance) (inferInstance) (2^bits : ZMod q) reconstructionBase (inferInstance) (inferInstance) comparisonBase initial) → Prop := by
  dsimp only [ExecutionResult]
  intro outcome
  exact KeySwitchTailRisk.Risk (fun _ => False)
      (fun mono acc known => AmbientKnownInput.OriginalRisk first.heights
        (KeySwitchKnownInput.stage inputSmall hs.encoding inputReference.root inputLength
          (AccumulatorEndpoint.value accLength (factory acc.1.1.2).context)
          (inputBase mono.2.1.2.memory)) dummy inputCapacity inputRadius known)
      (fun ntts => PaddedNTTSequenceSoundness.AnyOriginalRisk
        (KeySwitchPaddedNTT.factory finalBase hs.encoding finalFamily finalNodes finalLength psi primitive)
        hs.encoding dummy finalCapacity finalRadius ntts.1)
      (fun product => PaddedZeroCheck.OriginalRisk
        (KeySwitchPaddedProduct.stage (productBase product.1) hs.encoding finalFamily productFirstSmall productRoundSmall productNodes)
        dummy (productCapacity product.1) (productRadius product.1) product.2)
      (fun reconstructed => PaddedLinear.OriginalRisk
        (KeySwitchPaddedReconstruction.stage (reconstructionBase reconstructed.1) hs.encoding inputReference finalFamily finalNodes (2^bits : ZMod q))
        dummy (reconstructionCapacity reconstructed.1) (reconstructionRadius reconstructed.1) reconstructed.2)
      (fun compared => RectangularOwnedRequestSources.OriginalFalse hs.encoding dummy
        (config compared.1.1) domain lookupCapacity lookupRadius compared.2)
      (fun compared => compared.2.2.2.1.2.accepted = true) outcome ∨
    CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights)
      (PackedPBSKeySwitchComparisons.finalState first second finalBase productBase reconstructionBase comparisonBase outcome)

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- The probability of an accepted incorrect canonical increment is at most the
actual selected tail-risk or final-history-failure probability in the same run.
No losslessness or child probability/security certificate is a premise. -/
theorem accepted_false_event_le
    (setupParameters : Fin finalD → RecordedPaddedSource.Parameters (ZMod q) Cfg first.heights 4)
    (setupReceipt : HonestKeyQueryReceipt.Receipt setupParameters hs.encoding psi original finalFamily.keys initial.hash.log)
    (initialValid : CachedHashHandler.Coherent initial.hash ∧
      RecordedCheckpointQueries.Sound (RecordedSourceCoherence.Shape Cfg height) initial)
    (setupGeometry : ∀ memory level, setupParameters level =
      ExecutedHonestProductKey.parameters (productBase memory) (productCapacity memory) (productRadius memory) level)
    (honestDegree : ∀ level, (setupParameters level).degree ≤ 2^first.heights (setupParameters level).tag)
    (honestMargin : ∀ level, 2*(setupParameters level).radius <
      Code.minDist (BlockCode.code (setupParameters level).domain (setupParameters level).degree 4 :
        Set (Fin (2^first.heights (setupParameters level).tag) → Fin 4 → ZMod q)))
    (honestFits : ∀ level, finalC+1 ≤ (setupParameters level).front+(setupParameters level).suffix)
    (coefficientRouting : ∀ (level : Fin finalD) memory reconstructionMemory, PaddedStageSourceInterpretation.nttParameters
      (KeySwitchPaddedNTT.factory finalBase hs.encoding finalFamily finalNodes finalLength psi primitive (Fin.castSucc level) memory)
      (finalCapacity (Fin.castSucc level) memory) (finalRadius (Fin.castSucc level) memory) false =
      PaddedStageSourceInterpretation.linearParameters
        (KeySwitchPaddedReconstruction.stage (reconstructionBase reconstructionMemory) hs.encoding inputReference finalFamily finalNodes (2^bits : ZMod q))
        (reconstructionCapacity reconstructionMemory) (reconstructionRadius reconstructionMemory) (DecompositionLinear.digit level))
    (evaluationRouting : ∀ index memory productMemory, PaddedStageSourceInterpretation.nttParameters
      (KeySwitchPaddedNTT.factory finalBase hs.encoding finalFamily finalNodes finalLength psi primitive index memory)
      (finalCapacity index memory) (finalRadius index memory) true =
      PaddedStageSourceInterpretation.zeroParameters
        (KeySwitchPaddedProduct.stage (productBase productMemory) hs.encoding finalFamily productFirstSmall productRoundSmall productNodes)
        (productCapacity productMemory) (productRadius productMemory) (PackedPBSOriginalReferences.evaluationFactor index))
    (knownRouting : ∀ knownMemory reconstructionMemory, DecodedKnownInput.parameters (c := finalC) (lanes := 2) (inputBase knownMemory)
      first.heights (inputGeometry knownMemory) inputCapacity inputRadius =
      PaddedStageSourceInterpretation.linearParameters
        (KeySwitchPaddedReconstruction.stage (reconstructionBase reconstructionMemory) hs.encoding inputReference finalFamily finalNodes (2^bits : ZMod q))
        (reconstructionCapacity reconstructionMemory) (reconstructionRadius reconstructionMemory) DecompositionLinear.input)
    (lookupRouting : ∀ memory source, RectangularLookupSourceInterpretation.squareParameters (d := 3) (padding := 1) (g := g) (tag := tag) (symbolWidth := symbolWidth) domain lookupCapacity lookupRadius sourceSymbols source =
      PaddedStageSourceInterpretation.linearParameters
        (KeySwitchPaddedReconstruction.stage (reconstructionBase memory) hs.encoding inputReference finalFamily finalNodes (2^bits : ZMod q))
        (reconstructionCapacity memory) (reconstructionRadius memory) (PackedPBSComparisonReferences.linearSlot source))
    (slotOrder : ∀ memory, (config memory).slots = RadixLookupSources.comparisonSlots)
    (publicTables : ∀ memory, (config memory).tables = fun limb => RadixLookupSources.publicTable q (2^bits)
      (RadixCanonicity.modulusDigit q (2^bits) limb.val))
    (full : ∀ memory limb, (config memory).active limb = 2^(2+(1+finalC)))
    (radixLarge : 1 < 2^bits) (radixSmall : 2^bits < q) (enough : q-1 < (2^bits)^finalD)
    (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape first.heights) initial.checkpoints)
    (restricted : CheckpointRecordScope.Scoped
      (fun cfg => RecordedSourceCoherence.Shape Cfg height cfg = BinaryTree.Skeleton.perfect (first.heights cfg))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase))
    (auditedInitial : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial)
 :
    let experiment := (@PackedPBSKeySwitchComparisons.witness q (finalC+2) d b c r k n front suffix m queries height (inferInstance) Input Cfg Response Memory CommitMemory FirstMessage Message (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) length psi primitive family inputs base hs nodesEnough radix linearBase Helper Selection Root Data SecondHelper SecondSelection SecondRoot SecondData AccResponse accB accC accR accFront accSuffix accM accQueries accHeight (inferInstance) (inferInstance) (inferInstance) lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight (inferInstance) (inferInstance) (inferInstance) (inferInstance) ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight (inferInstance) (inferInstance) (inferInstance) (inferInstance) InputResponse InputCommitMemory 4 finalC inputFront inputSuffix inputM inputQueries inputHeight (inferInstance) (inferInstance) (inferInstance) FinalResponse FinalCommitMemory finalD 4 finalC (inferInstance) (inferInstance) ProductResponse ProductCommitMemory (inferInstance) (inferInstance) ReconstructionResponse ReconstructionCommitMemory (fun _ : Memory => (Fin (∑ i, repetitions i) → Digest) × RetainedMemory) (fun _ : Memory => (FinalSelection × ShortCircuitSequence.Outcome FinalRoot FinalData Memory)) dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase (inferInstance) (inferInstance) productFirstSmall productRoundSmall productNodes productBase (inferInstance) (inferInstance) (2^bits : ZMod q) reconstructionBase (inferInstance) (inferInstance) comparisonBase initial)
    Pr{let outcome ← experiment}[(@AcceptedFalse q finalC finalD bits d b c r k n front suffix m queries height (by assumption) Input Cfg Response Memory CommitMemory FirstMessage Message (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) length psi primitive family inputs base hs nodesEnough radix linearBase Helper Selection Root Data SecondHelper SecondSelection SecondRoot SecondData AccResponse accB accC accR accFront accSuffix accM accQueries accHeight (by assumption) (by assumption) (by assumption) lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight (by assumption) (by assumption) (by assumption) (by assumption) ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight (by assumption) (by assumption) (by assumption) (by assumption) InputResponse InputCommitMemory inputFront inputSuffix inputM inputQueries inputHeight (by assumption) (by assumption) (by assumption) FinalResponse FinalCommitMemory (by assumption) ProductResponse ProductCommitMemory (by assumption) (by assumption) ReconstructionResponse ReconstructionCommitMemory RetainedMemory FinalSelection FinalRoot FinalData repetitions dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase (by assumption) (by assumption) productFirstSmall productRoundSmall productNodes productBase (by assumption) (by assumption) reconstructionBase (by assumption) (by assumption) comparisonBase initial finalCapacity finalRadius original outcome)] ≤
    Pr{let outcome ← experiment}[(@TailFailure q finalC finalD bits d b c r k n front suffix m queries height (by assumption) Input Cfg Response Memory CommitMemory FirstMessage Message (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) length psi primitive family inputs base hs nodesEnough radix linearBase Helper Selection Root Data SecondHelper SecondSelection SecondRoot SecondData AccResponse accB accC accR accFront accSuffix accM accQueries accHeight (by assumption) (by assumption) (by assumption) lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight (by assumption) (by assumption) (by assumption) (by assumption) ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight (by assumption) (by assumption) (by assumption) (by assumption) InputResponse InputCommitMemory inputFront inputSuffix inputM inputQueries inputHeight (by assumption) (by assumption) (by assumption) FinalResponse FinalCommitMemory (by assumption) ProductResponse ProductCommitMemory (by assumption) (by assumption) ReconstructionResponse ReconstructionCommitMemory K LookupMessage LookupMemory ConfigHelperMemory RetainedMemory FinalSelection FinalRoot FinalData (by assumption) (by assumption) repetitions mode tag g symbolWidth dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase (by assumption) (by assumption) productFirstSmall productRoundSmall productNodes productBase (by assumption) (by assumption) reconstructionBase (by assumption) (by assumption) comparisonBase initial finalCapacity finalRadius productCapacity productRadius reconstructionCapacity reconstructionRadius inputCapacity inputRadius config domain lookupCapacity lookupRadius outcome)] := by
  dsimp only
  apply prEvent_mono_of_support
  intro outcome supported event
  obtain ⟨compared,present,passed,incorrect⟩ := event
  have same : outcome = (outcome.1,some compared) := Prod.ext rfl present
  have returnedSupported : (outcome.1,some compared) ∈ support (@PackedPBSKeySwitchComparisons.witness q (finalC+2) d b c r k n front suffix m queries height (inferInstance) Input Cfg Response Memory CommitMemory FirstMessage Message (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) length psi primitive family inputs base hs nodesEnough radix linearBase Helper Selection Root Data SecondHelper SecondSelection SecondRoot SecondData AccResponse accB accC accR accFront accSuffix accM accQueries accHeight (inferInstance) (inferInstance) (inferInstance) lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight (inferInstance) (inferInstance) (inferInstance) (inferInstance) ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight (inferInstance) (inferInstance) (inferInstance) (inferInstance) InputResponse InputCommitMemory 4 finalC inputFront inputSuffix inputM inputQueries inputHeight (inferInstance) (inferInstance) (inferInstance) FinalResponse FinalCommitMemory finalD 4 finalC (inferInstance) (inferInstance) ProductResponse ProductCommitMemory (inferInstance) (inferInstance) ReconstructionResponse ReconstructionCommitMemory (fun _ : Memory => (Fin (∑ i, repetitions i) → Digest) × RetainedMemory) (fun _ : Memory => (FinalSelection × ShortCircuitSequence.Outcome FinalRoot FinalData Memory)) dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase (inferInstance) (inferInstance) productFirstSmall productRoundSmall productNodes productBase (inferInstance) (inferInstance) (2^bits : ZMod q) reconstructionBase (inferInstance) (inferInstance) comparisonBase initial) := same ▸ supported
  let covered := @PackedPBSHonestAcceptedIncrement.accepted_increment_coverage q finalC finalD bits d b c r k n front suffix m queries height (by assumption) Input Cfg Response Memory CommitMemory FirstMessage Message (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) length psi primitive family inputs base hs nodesEnough radix linearBase Helper Selection Root Data SecondHelper SecondSelection SecondRoot SecondData AccResponse accB accC accR accFront accSuffix accM accQueries accHeight (by assumption) (by assumption) (by assumption) lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight (by assumption) (by assumption) (by assumption) (by assumption) ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight (by assumption) (by assumption) (by assumption) (by assumption) InputResponse InputCommitMemory inputFront inputSuffix inputM inputQueries inputHeight (by assumption) (by assumption) (by assumption) FinalResponse FinalCommitMemory (by assumption) ProductResponse ProductCommitMemory (by assumption) (by assumption) ReconstructionResponse ReconstructionCommitMemory K LookupMessage LookupMemory ConfigHelperMemory RetainedMemory FinalSelection FinalRoot FinalData (by assumption) (by assumption) repetitions mode tag g symbolWidth dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase (by assumption) (by assumption) productFirstSmall productRoundSmall productNodes productBase (by assumption) (by assumption) reconstructionBase (by assumption) (by assumption) comparisonBase initial original setupParameters
  let verifiedFn := @PackedPBSHonestAcceptedIncrement.AcceptedCoverage.verified q finalC finalD bits d b c r k n front suffix m queries height (by assumption) Input Cfg Response Memory CommitMemory FirstMessage Message (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) length psi primitive family inputs base hs nodesEnough radix linearBase Helper Selection Root Data SecondHelper SecondSelection SecondRoot SecondData AccResponse accB accC accR accFront accSuffix accM accQueries accHeight (by assumption) (by assumption) (by assumption) lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight (by assumption) (by assumption) (by assumption) (by assumption) ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight (by assumption) (by assumption) (by assumption) (by assumption) InputResponse InputCommitMemory inputFront inputSuffix inputM inputQueries inputHeight (by assumption) (by assumption) (by assumption) FinalResponse FinalCommitMemory (by assumption) ProductResponse ProductCommitMemory (by assumption) (by assumption) ReconstructionResponse ReconstructionCommitMemory K LookupMessage LookupMemory ConfigHelperMemory RetainedMemory FinalSelection FinalRoot FinalData (by assumption) (by assumption) repetitions mode tag g symbolWidth dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase (by assumption) (by assumption) productFirstSmall productRoundSmall productNodes productBase (by assumption) (by assumption) reconstructionBase (by assumption) (by assumption) comparisonBase initial original setupParameters @covered
  have actual := @verifiedFn finalCapacity finalRadius productCapacity productRadius setupReceipt initialValid setupGeometry honestDegree honestMargin honestFits reconstructionCapacity reconstructionRadius inputCapacity inputRadius inputGeometry config domain lookupCapacity lookupRadius sourceSymbols coefficientRouting evaluationRouting knownRouting lookupRouting slotOrder publicTables full radixLarge radixSmall enough compatible restricted auditedInitial outcome.1 compared @returnedSupported passed
  obtain ⟨product,ntts,known,monomial,accumulator,productPresent,nttPresent,knownPresent,
    monomialPresent,accumulatorPresent,nttSupported,nttPassed,productSupported,nttRetained,
    productRetained,coverage⟩ := actual
  rcases coverage with correct | risky | bad
  · apply False.elim
    apply incorrect
    exact ⟨compared,present,product,ntts,known,monomial,accumulator,productPresent,nttPresent,
      knownPresent,monomialPresent,accumulatorPresent,nttSupported,nttPassed,productSupported,
      nttRetained,productRetained,correct⟩
  · apply Or.inl
    exact same.symm ▸ risky
  · apply Or.inr
    simpa only [PackedPBSKeySwitchComparisons.finalState,RetainedPaddedComparison.finalState,
      DependentStageContinuation.finalState,present] using bad

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- Pointwise version for the actual supported return, allowing setup/PBS
composition without assuming a conditional security bound. -/
theorem accepted_false_implies_failure
    (setupParameters : Fin finalD → RecordedPaddedSource.Parameters (ZMod q) Cfg first.heights 4)
    (setupReceipt : HonestKeyQueryReceipt.Receipt setupParameters hs.encoding psi original finalFamily.keys initial.hash.log)
    (initialValid : CachedHashHandler.Coherent initial.hash ∧
      RecordedCheckpointQueries.Sound (RecordedSourceCoherence.Shape Cfg height) initial)
    (setupGeometry : ∀ memory level, setupParameters level =
      ExecutedHonestProductKey.parameters (productBase memory) (productCapacity memory) (productRadius memory) level)
    (honestDegree : ∀ level, (setupParameters level).degree ≤ 2^first.heights (setupParameters level).tag)
    (honestMargin : ∀ level, 2*(setupParameters level).radius <
      Code.minDist (BlockCode.code (setupParameters level).domain (setupParameters level).degree 4 :
        Set (Fin (2^first.heights (setupParameters level).tag) → Fin 4 → ZMod q)))
    (honestFits : ∀ level, finalC+1 ≤ (setupParameters level).front+(setupParameters level).suffix)
    (coefficientRouting : ∀ (level : Fin finalD) memory reconstructionMemory, PaddedStageSourceInterpretation.nttParameters
      (KeySwitchPaddedNTT.factory finalBase hs.encoding finalFamily finalNodes finalLength psi primitive (Fin.castSucc level) memory)
      (finalCapacity (Fin.castSucc level) memory) (finalRadius (Fin.castSucc level) memory) false =
      PaddedStageSourceInterpretation.linearParameters
        (KeySwitchPaddedReconstruction.stage (reconstructionBase reconstructionMemory) hs.encoding inputReference finalFamily finalNodes (2^bits : ZMod q))
        (reconstructionCapacity reconstructionMemory) (reconstructionRadius reconstructionMemory) (DecompositionLinear.digit level))
    (evaluationRouting : ∀ index memory productMemory, PaddedStageSourceInterpretation.nttParameters
      (KeySwitchPaddedNTT.factory finalBase hs.encoding finalFamily finalNodes finalLength psi primitive index memory)
      (finalCapacity index memory) (finalRadius index memory) true =
      PaddedStageSourceInterpretation.zeroParameters
        (KeySwitchPaddedProduct.stage (productBase productMemory) hs.encoding finalFamily productFirstSmall productRoundSmall productNodes)
        (productCapacity productMemory) (productRadius productMemory) (PackedPBSOriginalReferences.evaluationFactor index))
    (knownRouting : ∀ knownMemory reconstructionMemory, DecodedKnownInput.parameters (c := finalC) (lanes := 2) (inputBase knownMemory)
      first.heights (inputGeometry knownMemory) inputCapacity inputRadius =
      PaddedStageSourceInterpretation.linearParameters
        (KeySwitchPaddedReconstruction.stage (reconstructionBase reconstructionMemory) hs.encoding inputReference finalFamily finalNodes (2^bits : ZMod q))
        (reconstructionCapacity reconstructionMemory) (reconstructionRadius reconstructionMemory) DecompositionLinear.input)
    (lookupRouting : ∀ memory source, RectangularLookupSourceInterpretation.squareParameters (d := 3) (padding := 1) (g := g) (tag := tag) (symbolWidth := symbolWidth) domain lookupCapacity lookupRadius sourceSymbols source =
      PaddedStageSourceInterpretation.linearParameters
        (KeySwitchPaddedReconstruction.stage (reconstructionBase memory) hs.encoding inputReference finalFamily finalNodes (2^bits : ZMod q))
        (reconstructionCapacity memory) (reconstructionRadius memory) (PackedPBSComparisonReferences.linearSlot source))
    (slotOrder : ∀ memory, (config memory).slots = RadixLookupSources.comparisonSlots)
    (publicTables : ∀ memory, (config memory).tables = fun limb => RadixLookupSources.publicTable q (2^bits)
      (RadixCanonicity.modulusDigit q (2^bits) limb.val))
    (full : ∀ memory limb, (config memory).active limb = 2^(2+(1+finalC)))
    (radixLarge : 1 < 2^bits) (radixSmall : 2^bits < q) (enough : q-1 < (2^bits)^finalD)
    (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape first.heights) initial.checkpoints)
    (restricted : CheckpointRecordScope.Scoped
      (fun cfg => RecordedSourceCoherence.Shape Cfg height cfg = BinaryTree.Skeleton.perfect (first.heights cfg))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase))
    (auditedInitial : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial)
 :
    let experiment := (@PackedPBSKeySwitchComparisons.witness q (finalC+2) d b c r k n front suffix m queries height (inferInstance) Input Cfg Response Memory CommitMemory FirstMessage Message (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) length psi primitive family inputs base hs nodesEnough radix linearBase Helper Selection Root Data SecondHelper SecondSelection SecondRoot SecondData AccResponse accB accC accR accFront accSuffix accM accQueries accHeight (inferInstance) (inferInstance) (inferInstance) lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight (inferInstance) (inferInstance) (inferInstance) (inferInstance) ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight (inferInstance) (inferInstance) (inferInstance) (inferInstance) InputResponse InputCommitMemory 4 finalC inputFront inputSuffix inputM inputQueries inputHeight (inferInstance) (inferInstance) (inferInstance) FinalResponse FinalCommitMemory finalD 4 finalC (inferInstance) (inferInstance) ProductResponse ProductCommitMemory (inferInstance) (inferInstance) ReconstructionResponse ReconstructionCommitMemory (fun _ : Memory => (Fin (∑ i, repetitions i) → Digest) × RetainedMemory) (fun _ : Memory => (FinalSelection × ShortCircuitSequence.Outcome FinalRoot FinalData Memory)) dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase (inferInstance) (inferInstance) productFirstSmall productRoundSmall productNodes productBase (inferInstance) (inferInstance) (2^bits : ZMod q) reconstructionBase (inferInstance) (inferInstance) comparisonBase initial)
    ∀ outcome ∈ support experiment, (@AcceptedFalse q finalC finalD bits d b c r k n front suffix m queries height (by assumption) Input Cfg Response Memory CommitMemory FirstMessage Message (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) length psi primitive family inputs base hs nodesEnough radix linearBase Helper Selection Root Data SecondHelper SecondSelection SecondRoot SecondData AccResponse accB accC accR accFront accSuffix accM accQueries accHeight (by assumption) (by assumption) (by assumption) lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight (by assumption) (by assumption) (by assumption) (by assumption) ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight (by assumption) (by assumption) (by assumption) (by assumption) InputResponse InputCommitMemory inputFront inputSuffix inputM inputQueries inputHeight (by assumption) (by assumption) (by assumption) FinalResponse FinalCommitMemory (by assumption) ProductResponse ProductCommitMemory (by assumption) (by assumption) ReconstructionResponse ReconstructionCommitMemory RetainedMemory FinalSelection FinalRoot FinalData repetitions dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase (by assumption) (by assumption) productFirstSmall productRoundSmall productNodes productBase (by assumption) (by assumption) reconstructionBase (by assumption) (by assumption) comparisonBase initial finalCapacity finalRadius original outcome) → (@TailFailure q finalC finalD bits d b c r k n front suffix m queries height (by assumption) Input Cfg Response Memory CommitMemory FirstMessage Message (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) length psi primitive family inputs base hs nodesEnough radix linearBase Helper Selection Root Data SecondHelper SecondSelection SecondRoot SecondData AccResponse accB accC accR accFront accSuffix accM accQueries accHeight (by assumption) (by assumption) (by assumption) lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight (by assumption) (by assumption) (by assumption) (by assumption) ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight (by assumption) (by assumption) (by assumption) (by assumption) InputResponse InputCommitMemory inputFront inputSuffix inputM inputQueries inputHeight (by assumption) (by assumption) (by assumption) FinalResponse FinalCommitMemory (by assumption) ProductResponse ProductCommitMemory (by assumption) (by assumption) ReconstructionResponse ReconstructionCommitMemory K LookupMessage LookupMemory ConfigHelperMemory RetainedMemory FinalSelection FinalRoot FinalData (by assumption) (by assumption) repetitions mode tag g symbolWidth dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase (by assumption) (by assumption) productFirstSmall productRoundSmall productNodes productBase (by assumption) (by assumption) reconstructionBase (by assumption) (by assumption) comparisonBase initial finalCapacity finalRadius productCapacity productRadius reconstructionCapacity reconstructionRadius inputCapacity inputRadius config domain lookupCapacity lookupRadius outcome) := by
  dsimp only [ExecutionResult]
  intro outcome supported event
  obtain ⟨compared,present,passed,incorrect⟩ := event
  have same : outcome = (outcome.1,some compared) := Prod.ext rfl present
  have returnedSupported : (outcome.1,some compared) ∈ support (@PackedPBSKeySwitchComparisons.witness q (finalC+2) d b c r k n front suffix m queries height (inferInstance) Input Cfg Response Memory CommitMemory FirstMessage Message (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) (inferInstance) length psi primitive family inputs base hs nodesEnough radix linearBase Helper Selection Root Data SecondHelper SecondSelection SecondRoot SecondData AccResponse accB accC accR accFront accSuffix accM accQueries accHeight (inferInstance) (inferInstance) (inferInstance) lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight (inferInstance) (inferInstance) (inferInstance) (inferInstance) ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight (inferInstance) (inferInstance) (inferInstance) (inferInstance) InputResponse InputCommitMemory 4 finalC inputFront inputSuffix inputM inputQueries inputHeight (inferInstance) (inferInstance) (inferInstance) FinalResponse FinalCommitMemory finalD 4 finalC (inferInstance) (inferInstance) ProductResponse ProductCommitMemory (inferInstance) (inferInstance) ReconstructionResponse ReconstructionCommitMemory (fun _ : Memory => (Fin (∑ i, repetitions i) → Digest) × RetainedMemory) (fun _ : Memory => (FinalSelection × ShortCircuitSequence.Outcome FinalRoot FinalData Memory)) dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase (inferInstance) (inferInstance) productFirstSmall productRoundSmall productNodes productBase (inferInstance) (inferInstance) (2^bits : ZMod q) reconstructionBase (inferInstance) (inferInstance) comparisonBase initial) := same ▸ supported
  let covered := @PackedPBSHonestAcceptedIncrement.accepted_increment_coverage q finalC finalD bits d b c r k n front suffix m queries height (by assumption) Input Cfg Response Memory CommitMemory FirstMessage Message (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) length psi primitive family inputs base hs nodesEnough radix linearBase Helper Selection Root Data SecondHelper SecondSelection SecondRoot SecondData AccResponse accB accC accR accFront accSuffix accM accQueries accHeight (by assumption) (by assumption) (by assumption) lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight (by assumption) (by assumption) (by assumption) (by assumption) ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight (by assumption) (by assumption) (by assumption) (by assumption) InputResponse InputCommitMemory inputFront inputSuffix inputM inputQueries inputHeight (by assumption) (by assumption) (by assumption) FinalResponse FinalCommitMemory (by assumption) ProductResponse ProductCommitMemory (by assumption) (by assumption) ReconstructionResponse ReconstructionCommitMemory K LookupMessage LookupMemory ConfigHelperMemory RetainedMemory FinalSelection FinalRoot FinalData (by assumption) (by assumption) repetitions mode tag g symbolWidth dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase (by assumption) (by assumption) productFirstSmall productRoundSmall productNodes productBase (by assumption) (by assumption) reconstructionBase (by assumption) (by assumption) comparisonBase initial original setupParameters
  let verifiedFn := @PackedPBSHonestAcceptedIncrement.AcceptedCoverage.verified q finalC finalD bits d b c r k n front suffix m queries height (by assumption) Input Cfg Response Memory CommitMemory FirstMessage Message (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) (by assumption) length psi primitive family inputs base hs nodesEnough radix linearBase Helper Selection Root Data SecondHelper SecondSelection SecondRoot SecondData AccResponse accB accC accR accFront accSuffix accM accQueries accHeight (by assumption) (by assumption) (by assumption) lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight (by assumption) (by assumption) (by assumption) (by assumption) ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight (by assumption) (by assumption) (by assumption) (by assumption) InputResponse InputCommitMemory inputFront inputSuffix inputM inputQueries inputHeight (by assumption) (by assumption) (by assumption) FinalResponse FinalCommitMemory (by assumption) ProductResponse ProductCommitMemory (by assumption) (by assumption) ReconstructionResponse ReconstructionCommitMemory K LookupMessage LookupMemory ConfigHelperMemory RetainedMemory FinalSelection FinalRoot FinalData (by assumption) (by assumption) repetitions mode tag g symbolWidth dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase (by assumption) (by assumption) productFirstSmall productRoundSmall productNodes productBase (by assumption) (by assumption) reconstructionBase (by assumption) (by assumption) comparisonBase initial original setupParameters @covered
  have actual := @verifiedFn finalCapacity finalRadius productCapacity productRadius setupReceipt initialValid setupGeometry honestDegree honestMargin honestFits reconstructionCapacity reconstructionRadius inputCapacity inputRadius inputGeometry config domain lookupCapacity lookupRadius sourceSymbols coefficientRouting evaluationRouting knownRouting lookupRouting slotOrder publicTables full radixLarge radixSmall enough compatible restricted auditedInitial outcome.1 compared @returnedSupported passed
  obtain ⟨product,ntts,known,monomial,accumulator,productPresent,nttPresent,knownPresent,
    monomialPresent,accumulatorPresent,nttSupported,nttPassed,productSupported,nttRetained,
    productRetained,coverage⟩ := actual
  rcases coverage with correct | risky | bad
  · apply False.elim
    apply incorrect
    exact ⟨compared,present,product,ntts,known,monomial,accumulator,productPresent,nttPresent,
      knownPresent,monomialPresent,accumulatorPresent,nttSupported,nttPassed,productSupported,
      nttRetained,productRetained,correct⟩
  · apply Or.inl
    exact same.symm ▸ risky
  · apply Or.inr
    simpa only [PackedPBSKeySwitchComparisons.finalState,RetainedPaddedComparison.finalState,
      DependentStageContinuation.finalState,present] using bad

end
end FormalProof4FHE.HasteBoots.PackedPBSHonestIncrementEvents
