module
public import FormalProof4FHE.HasteBoots.PackedPBSKeySwitchExtraction
public import FormalProof4FHE.HasteBoots.RetainedExtractionHistory
public import FormalProof4FHE.HasteBoots.PackedPBSKeySwitchExtractionHistory
public import FormalProof4FHE.HasteBoots.PackedPBSReachedKeySwitch
public import FormalProof4FHE.HasteBoots.CheckpointHistoryChain
public import FormalProof4FHE.HasteBoots.PackedPBSExtractionFrame
public import FormalProof4FHE.HasteBoots.PackedPBSKeySwitchComparisonsHistory
public import FormalProof4FHE.HasteBoots.PackedPBSExtractionNTT
public import FormalProof4FHE.HasteBoots.ExecutedExtractionNTTLink
public import FormalProof4FHE.HasteBoots.PackedPBSExtractionSemantics
public import FormalProof4FHE.HasteBoots.PackedPBSHonestIncrementEvents
public import FormalProof4FHE.HasteBoots.PackedPBSHonestSetupJoint
public import FormalProof4FHE.HasteBoots.PackedPBSHonestExtractionJoint
public import FormalProof4FHE.HasteBoots.RetainedExtractionAssembly
@[expose] public section

/-! Recover the same fixed-initial complete extraction execution from the actual
joint setup and verifier, with its returned keys, state and child data unchanged. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSHonestExtractionAssembly
open OracleSpec OracleComp
open PackedPBSKeySwitchExtraction
open NativeRootMessage (Digest)
open PackedPBSSecondComparisons (sharedScheme)
noncomputable section
attribute [local irreducible] MonadAttach.support SelectedNTT.known SelectedNTT.ntt Frame.comparison
attribute [local irreducible] AcceptedKeySwitchNTT.sourceFamily
attribute [local irreducible] PaddedPublicZeroCheck.witness
variable {q finalC bits d b c r k n front suffix m queries height : ℕ} [Fact q.Prime]
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

  [SampleableType (PackedZeroReduction.Points (ZMod q) (cells+rows) (2^lanes))]
  [SampleableType (Fin (2^lanes) → Fin (2^lanes) → ZMod q)]

  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^zeroFront) (2^lanes))]
  [SampleableType (Fin zeroQueries → Fin (2^zeroHeight))]

variable {InputResponse InputCommitMemory : Type} {inputFront inputSuffix inputM inputQueries inputHeight : ℕ}

  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^inputFront) 4)]
  [SampleableType (Fin inputQueries → Fin (2^inputHeight))]

variable {FinalResponse FinalCommitMemory : Type} {finalD : ℕ}
  [SampleableType (Fin 4 → Fin 1 → ZMod q)] [SampleableType (Fin 4 → ZMod q)]

variable {ProductResponse ProductCommitMemory : Type}
  [SampleableType (PackedZeroReduction.Points (ZMod q) finalC 4)]
  [SampleableType (Fin 4 → Fin 4 → ZMod q)]

variable {ReconstructionResponse ReconstructionCommitMemory : Type}

variable {RetainedMemory FinalSelectionValue FinalRootValue FinalDataValue : Type}
  {repetitions : Fin finalD → ℕ}

variable {dimension : ℕ} {ExtractionResponse ExtractionCommitMemory : Type}

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
    (comparisonBase : (memory : Memory) → PackedPBSComparisonStage.Scheme Cfg Input Memory ((fun (_ : Memory) => (Fin (∑ i, repetitions i) → Digest) × RetainedMemory) memory) ((fun memory => (fun (_ : Memory) => FinalSelectionValue) memory × ShortCircuitSequence.Outcome ((fun (_ : Memory) => FinalRootValue) memory) ((fun (_ : Memory) => FinalDataValue) memory) Memory) memory) finalD)
    (extractionLog : finalC+2 = (finalC+2)) (positive : 0 < dimension)
    (output : NativePublic.Ciphertext q dimension)
    (extractionFirstSmall : (2*(2^2)-1)*2+1 ≤ q)
    (extractionRoundSmall : (2*(2^2)-1)*3+1 ≤ q)
    (extractionNodes : 2*(2^2) ≤ (2*(2^2)-1)*2+1)
    (extractionBase : Memory → KeySwitchPaddedExtraction.Scheme (q := q) (c := finalC) (lanes := 2)
      (Input := Input) (Cfg := Cfg) (Response := ExtractionResponse) (Memory := Memory)
      (CommitMemory := ExtractionCommitMemory) (heights := first.heights))
    [∀ memory factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((extractionBase memory).code factor).front) (2^2))]
    [∀ memory factor, SampleableType (Fin ((extractionBase memory).code factor).queries → Fin (2^first.heights ((extractionBase memory).tag factor)))]





variable (original : NativeKeySwitch.Key q (2^(finalC+2)) finalD)
    (setupParameters : Fin finalD → RecordedPaddedSource.Parameters (ZMod q) Cfg first.heights 4)



variable (previous : (PackedPBSHonestSetupJoint.JointResult (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase)) (child : Sigma (RetainedPaddedExtraction.Child (fun _ : (PackedPBSHonestSetupJoint.JointResult (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase) => extractionBase)))
    (supported : (previous,some child) ∈ support (PackedPBSHonestExtractionJoint.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase original setupParameters))

include supported in
/-- The reached joint return supplies the actual setup call from the empty state. -/
theorem setup_supported : previous.1 ∈ support ((simulateQ
    (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height))
    (HonestKeySetupReceipts.program setupParameters hs.encoding psi original)).run
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height))) :=
  (PackedPBSHonestSetupJoint.parts (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase original setupParameters previous
    (PackedPBSHonestExtractionJoint.reached length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase original setupParameters previous child supported).1).1

/-- All initial receipts, cached query invariants, audit and shape compatibility
come from that same actual setup, without an independent certificate. -/
abbrev initialized := HonestKeySetupReceipts.initialized (QueryImpl.ofLift unifSpec ProbComp)
  setupParameters hs.encoding dummy psi original (RecordedSourceCoherence.Shape Cfg height) previous.1
  (setup_supported length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase original setupParameters previous child supported)

include supported in
/-- Repackage the same extraction data under its literal comparison predecessor.
The complete witness uses the actual generated key roots and exact setup end. -/
theorem fixed_initial_supported :
    (previous.2,some (⟨(previous.2,child.1.2),child.2⟩ : Sigma (RetainedPaddedExtraction.Child (fun _ : (PackedPBSKeySwitchExtraction.BeforeExtraction (q := q) (d := d) (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix) (queries := queries) (height := height) (Input := Input) (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory) (Helper := Helper) (Selection := Selection) (Root := Root) (Data := Data) (SecondHelper := SecondHelper) (SecondSelection := SecondSelection) (SecondRoot := SecondRoot) (SecondData := SecondData) (AccResponse := AccResponse) (accB := accB) (accC := accC) (accR := accR) (accFront := accFront) (accQueries := accQueries) (accHeight := accHeight) (lanes := lanes) (cells := cells) (rows := rows) (MonoResponse := MonoResponse) (MonoCommitMemory := MonoCommitMemory) (monoK := monoK) (monoFront := monoFront) (monoQueries := monoQueries) (monoHeight := monoHeight) (ZeroResponse := ZeroResponse) (ZeroCommitMemory := ZeroCommitMemory) (zeroFront := zeroFront) (zeroQueries := zeroQueries) (zeroHeight := zeroHeight) (InputResponse := InputResponse) (InputCommitMemory := InputCommitMemory) (inputB := 4) (inputC := finalC) (inputFront := inputFront) (inputQueries := inputQueries) (inputHeight := inputHeight) (FinalResponse := FinalResponse) (FinalCommitMemory := FinalCommitMemory) (finalD := finalD) (finalB := 4) (finalC := finalC) (ProductResponse := ProductResponse) (ProductCommitMemory := ProductCommitMemory) (ReconstructionResponse := ReconstructionResponse) (ReconstructionCommitMemory := ReconstructionCommitMemory) (FinalHelper := (fun (_ : Memory) => (Fin (∑ i, repetitions i) → Digest) × RetainedMemory)) (FinalSelection := (fun (_ : Memory) => FinalSelectionValue)) (FinalRoot := (fun (_ : Memory) => FinalRootValue)) (FinalData := (fun (_ : Memory) => FinalDataValue))) first second finalBase productBase reconstructionBase comparisonBase => extractionBase)))) ∈ support (PackedPBSKeySwitchExtraction.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase (ExecutedHonestProductKey.withKeys finalFamily previous.1.1) finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase (2^bits : ZMod q) reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase previous.1.2) := by
  have actual := PackedPBSHonestExtractionJoint.reached length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase original setupParameters previous child supported
  have parts := PackedPBSHonestSetupJoint.parts (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase original setupParameters previous actual.1
  have childSupported : child.2 ∈ support (PaddedPublicZeroCheck.witness ((fun (before : (PackedPBSKeySwitchExtraction.BeforeExtraction (q := q) (d := d) (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix) (queries := queries) (height := height) (Input := Input) (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory) (Helper := Helper) (Selection := Selection) (Root := Root) (Data := Data) (SecondHelper := SecondHelper) (SecondSelection := SecondSelection) (SecondRoot := SecondRoot) (SecondData := SecondData) (AccResponse := AccResponse) (accB := accB) (accC := accC) (accR := accR) (accFront := accFront) (accQueries := accQueries) (accHeight := accHeight) (lanes := lanes) (cells := cells) (rows := rows) (MonoResponse := MonoResponse) (MonoCommitMemory := MonoCommitMemory) (monoK := monoK) (monoFront := monoFront) (monoQueries := monoQueries) (monoHeight := monoHeight) (ZeroResponse := ZeroResponse) (ZeroCommitMemory := ZeroCommitMemory) (zeroFront := zeroFront) (zeroQueries := zeroQueries) (zeroHeight := zeroHeight) (InputResponse := InputResponse) (InputCommitMemory := InputCommitMemory) (inputB := 4) (inputC := finalC) (inputFront := inputFront) (inputQueries := inputQueries) (inputHeight := inputHeight) (FinalResponse := FinalResponse) (FinalCommitMemory := FinalCommitMemory) (finalD := finalD) (finalB := 4) (finalC := finalC) (ProductResponse := ProductResponse) (ProductCommitMemory := ProductCommitMemory) (ReconstructionResponse := ReconstructionResponse) (ReconstructionCommitMemory := ReconstructionCommitMemory) (FinalHelper := (fun (_ : Memory) => (Fin (∑ i, repetitions i) → Digest) × RetainedMemory)) (FinalSelection := (fun (_ : Memory) => FinalSelectionValue)) (FinalRoot := (fun (_ : Memory) => FinalRootValue)) (FinalData := (fun (_ : Memory) => FinalDataValue))) first second finalBase productBase reconstructionBase comparisonBase) (memory : Memory) => KeySwitchPaddedExtraction.stage (extractionBase memory) hs.encoding (ExecutedHonestProductKey.withKeys finalFamily previous.1.1) positive (fun _ => PackedPBSKeySwitchExtraction.endpoint first second finalBase productBase reconstructionBase comparisonBase factory accLength extractionLog before) (fun _ => output) extractionFirstSmall extractionRoundSmall extractionNodes) previous.2 child.1.2)
      dummy ((PackedPBSKeySwitchComparisons.finalState first second finalBase productBase reconstructionBase comparisonBase) previous.2)) := by
    dsimp only
    change child.2 ∈ support (PaddedPublicZeroCheck.witness
      (KeySwitchPaddedExtraction.stage (extractionBase child.1.2) hs.encoding finalFamily positive
        (fun _ => PackedPBSKeySwitchExtraction.endpoint first second finalBase productBase reconstructionBase comparisonBase factory accLength extractionLog previous.2)
        (fun _ => output) extractionFirstSmall extractionRoundSmall extractionNodes)
      dummy (PackedPBSKeySwitchComparisons.finalState first second finalBase productBase reconstructionBase comparisonBase previous.2))
    have reached := actual.2.2.2
    unfold RetainedPaddedExtraction.child at reached
    dsimp only at reached
    have endpointEq := congrArg (fun p => PackedPBSKeySwitchExtraction.endpoint first second finalBase productBase reconstructionBase comparisonBase factory accLength extractionLog p.2) actual.2.1
    rw [endpointEq] at reached
    exact reached
  exact RetainedExtractionAssembly.bind_supported (fun (before : (PackedPBSKeySwitchExtraction.BeforeExtraction (q := q) (d := d) (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix) (queries := queries) (height := height) (Input := Input) (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory) (Helper := Helper) (Selection := Selection) (Root := Root) (Data := Data) (SecondHelper := SecondHelper) (SecondSelection := SecondSelection) (SecondRoot := SecondRoot) (SecondData := SecondData) (AccResponse := AccResponse) (accB := accB) (accC := accC) (accR := accR) (accFront := accFront) (accQueries := accQueries) (accHeight := accHeight) (lanes := lanes) (cells := cells) (rows := rows) (MonoResponse := MonoResponse) (MonoCommitMemory := MonoCommitMemory) (monoK := monoK) (monoFront := monoFront) (monoQueries := monoQueries) (monoHeight := monoHeight) (ZeroResponse := ZeroResponse) (ZeroCommitMemory := ZeroCommitMemory) (zeroFront := zeroFront) (zeroQueries := zeroQueries) (zeroHeight := zeroHeight) (InputResponse := InputResponse) (InputCommitMemory := InputCommitMemory) (inputB := 4) (inputC := finalC) (inputFront := inputFront) (inputQueries := inputQueries) (inputHeight := inputHeight) (FinalResponse := FinalResponse) (FinalCommitMemory := FinalCommitMemory) (finalD := finalD) (finalB := 4) (finalC := finalC) (ProductResponse := ProductResponse) (ProductCommitMemory := ProductCommitMemory) (ReconstructionResponse := ReconstructionResponse) (ReconstructionCommitMemory := ReconstructionCommitMemory) (FinalHelper := (fun (_ : Memory) => (Fin (∑ i, repetitions i) → Digest) × RetainedMemory)) (FinalSelection := (fun (_ : Memory) => FinalSelectionValue)) (FinalRoot := (fun (_ : Memory) => FinalRootValue)) (FinalData := (fun (_ : Memory) => FinalDataValue))) first second finalBase productBase reconstructionBase comparisonBase) (memory : Memory) => KeySwitchPaddedExtraction.stage (extractionBase memory) hs.encoding (ExecutedHonestProductKey.withKeys finalFamily previous.1.1) positive (fun _ => PackedPBSKeySwitchExtraction.endpoint first second finalBase productBase reconstructionBase comparisonBase factory accLength extractionLog before) (fun _ => output) extractionFirstSmall extractionRoundSmall extractionNodes) (PackedPBSKeySwitchExtraction.get first second finalBase productBase reconstructionBase comparisonBase) (PackedPBSKeySwitchComparisons.finalState first second finalBase productBase reconstructionBase comparisonBase) dummy
    (PackedPBSKeySwitchComparisons.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase (ExecutedHonestProductKey.withKeys finalFamily previous.1.1) finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase (2^bits : ZMod q) reconstructionBase comparisonBase previous.1.2) previous.2 child.1.2 child.2 parts.2 actual.2.2.1 childSupported

omit [∀ memory factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((extractionBase memory).code factor).front) (2^2))]
  [∀ memory factor, SampleableType (Fin ((extractionBase memory).code factor).queries → Fin (2^first.heights ((extractionBase memory).tag factor)))] in
/-- The repackaged complete witness has exactly the same final state, including
cache, transcript, every checkpoint and failure flag. -/
theorem fixed_final_state_eq :
    PackedPBSKeySwitchExtraction.finalState first second finalBase productBase reconstructionBase comparisonBase extractionBase
      (previous.2,some (⟨(previous.2,child.1.2),child.2⟩ : Sigma (RetainedPaddedExtraction.Child (fun _ : (PackedPBSKeySwitchExtraction.BeforeExtraction (q := q) (d := d) (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix) (queries := queries) (height := height) (Input := Input) (Cfg := Cfg) (Response := Response) (Memory := Memory) (CommitMemory := CommitMemory) (Helper := Helper) (Selection := Selection) (Root := Root) (Data := Data) (SecondHelper := SecondHelper) (SecondSelection := SecondSelection) (SecondRoot := SecondRoot) (SecondData := SecondData) (AccResponse := AccResponse) (accB := accB) (accC := accC) (accR := accR) (accFront := accFront) (accQueries := accQueries) (accHeight := accHeight) (lanes := lanes) (cells := cells) (rows := rows) (MonoResponse := MonoResponse) (MonoCommitMemory := MonoCommitMemory) (monoK := monoK) (monoFront := monoFront) (monoQueries := monoQueries) (monoHeight := monoHeight) (ZeroResponse := ZeroResponse) (ZeroCommitMemory := ZeroCommitMemory) (zeroFront := zeroFront) (zeroQueries := zeroQueries) (zeroHeight := zeroHeight) (InputResponse := InputResponse) (InputCommitMemory := InputCommitMemory) (inputB := 4) (inputC := finalC) (inputFront := inputFront) (inputQueries := inputQueries) (inputHeight := inputHeight) (FinalResponse := FinalResponse) (FinalCommitMemory := FinalCommitMemory) (finalD := finalD) (finalB := 4) (finalC := finalC) (ProductResponse := ProductResponse) (ProductCommitMemory := ProductCommitMemory) (ReconstructionResponse := ReconstructionResponse) (ReconstructionCommitMemory := ReconstructionCommitMemory) (FinalHelper := (fun (_ : Memory) => (Fin (∑ i, repetitions i) → Digest) × RetainedMemory)) (FinalSelection := (fun (_ : Memory) => FinalSelectionValue)) (FinalRoot := (fun (_ : Memory) => FinalRootValue)) (FinalData := (fun (_ : Memory) => FinalDataValue))) first second finalBase productBase reconstructionBase comparisonBase => extractionBase)))) =
    PackedPBSHonestExtractionJoint.finalState length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase (previous,some child) := rfl

end
end FormalProof4FHE.HasteBoots.PackedPBSHonestExtractionAssembly
