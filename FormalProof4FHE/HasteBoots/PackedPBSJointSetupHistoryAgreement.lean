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
public import FormalProof4FHE.HasteBoots.PackedPBSJointSetupIncrement
public import FormalProof4FHE.HasteBoots.PackedPBSJointSetupExtraction
public import FormalProof4FHE.HasteBoots.RetainedExtractionAssembly
public import FormalProof4FHE.HasteBoots.PackedPBSExtractionErasure
public import FormalProof4FHE.HasteBoots.DependentStageContinuationProjection
public import FormalProof4FHE.HasteBoots.RetainedPaddedExtractionProjection
public import FormalProof4FHE.HasteBoots.PackedPBSJointSetupIncrementHistoryProgram
public import FormalProof4FHE.HasteBoots.PackedPBSJointSetupExtractionHistoryProgram
public import FormalProof4FHE.HasteBoots.PackedPBSJointSetupHistoryProgram
@[expose] public section

/-! Exact raw-program agreement between the retained two-setup security game
and the established complete combined setup/verifier/extraction program. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSJointSetupHistoryAgreement
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
    [extractionTestSampler : ∀ memory factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((extractionBase memory).code factor).front) (2^2))]
    [extractionQuerySampler : ∀ memory factor, SampleableType (Fin ((extractionBase memory).code factor).queries → Fin (2^first.heights ((extractionBase memory).tag factor)))]





variable (original : NativeKeySwitch.Key q (2^(finalC+2)) finalD)
    (setupParameters : Fin finalD → RecordedPaddedSource.Parameters (ZMod q) Cfg first.heights 4)
    (controlParameters : Fin (2*d) → RecordedPaddedSource.Parameters (ZMod q) Cfg first.heights (2^lanes))
    (controls : HonestControlKeyTable.Controls (q := q) (cells := cells) (lanes := lanes) (rows := rows) (levels := d))



/-- A canonically typed suffix receives both actual setup root families. -/
def verifierSuffix (controlRoots : Fin (2*d) → Digest) (keyRoots : Fin finalD → Digest) :
    OracleComp (SharedSequence.Shared Cfg Input Digest) (((Fin finalD → Digest) × (PackedPBSHonestHistoryProgram.VerifierResult (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase)) × Option (Sigma (RetainedPaddedExtractionProjection.Child (fun _ : ((Fin finalD → Digest) × (PackedPBSHonestHistoryProgram.VerifierResult (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase)) => extractionBase)))) := do
  let compared ← PackedPBSComparisonHistoryProgram.program (bits := bits) length psi primitive (HonestControlKeySetup.withKeys family controlRoots) inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase (ExecutedHonestProductKey.withKeys finalFamily keyRoots) finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase
  DependentStageContinuationProjection.program
    (RetainedPaddedExtractionProjection.select (PackedPBSJointSetupExtractionHistoryProgram.get (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase))
    (PackedPBSJointSetupExtractionHistoryProgram.childProgram (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase) (keyRoots,compared)

omit [DecidableEq Input] [SampleableType Digest] in
/-- Erased raw gates, endpoints and sampling factories agree with the existing
combined verifier suffix after installing its generated control-key roots. -/
theorem verifierSuffix_eq (controlRoots : Fin (2*d) → Digest) (keyRoots : Fin finalD → Digest) :
    (PackedPBSJointSetupHistoryProgram.verifier (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase) controlRoots keyRoots = (verifierSuffix (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase) controlRoots keyRoots := by
  rfl

omit [DecidableEq Input] [SampleableType Digest] in
/-- Factor both actual setup calls from the same complete raw verifier. -/
theorem program_eq_setup_suffix :
    PackedPBSJointSetupExtractionHistoryProgram.program (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase original setupParameters controlParameters controls = (do
      let roots ← HonestJointKeySetup.program controlParameters setupParameters hs.encoding psi controls original
      (verifierSuffix (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase) roots.1 roots.2) := by
  simp only [PackedPBSJointSetupExtractionHistoryProgram.program,PackedPBSJointSetupIncrementHistoryProgram.program,verifierSuffix,bind_assoc,pure_bind]
  rfl

omit [DecidableEq Input] [SampleableType Digest] in
/-- Erasing the extra returned root copy gives the exact established combined
setup/verifier/extraction raw PackedPBSJointSetupExtractionHistoryProgram.program, with identical queries and samplers. -/
theorem existing_program_eq :
    Prod.snd <$> (PackedPBSJointSetupHistoryProgram.program (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase original setupParameters controlParameters controls) =
    PackedPBSJointSetupExtractionHistoryProgram.program (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase original setupParameters controlParameters controls := by
  rw [program_eq_setup_suffix]
  simp only [PackedPBSJointSetupHistoryProgram.program,map_bind,map_pure,bind_pure]
  simp only [verifierSuffix_eq]


end
end FormalProof4FHE.HasteBoots.PackedPBSJointSetupHistoryAgreement
