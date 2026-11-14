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
public import FormalProof4FHE.HasteBoots.PackedPBSExtractionErasure
public import FormalProof4FHE.HasteBoots.DependentStageContinuationProjection
public import FormalProof4FHE.HasteBoots.RetainedPaddedExtractionProjection
public import FormalProof4FHE.HasteBoots.HonestJointKeySetup
public import FormalProof4FHE.HasteBoots.PackedPBSHonestExtractionHistoryProgram
@[expose] public section

/-! Both honest key setups and the complete PBS verifier/extraction share
one oracle execution, populated cache, chronological log and final monitor. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSJointSetupHistoryProgram
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



variable (controlParameters : Fin (2*d) → RecordedPaddedSource.Parameters (ZMod q) Cfg first.heights (2^lanes))
  (controls : HonestControlKeyTable.Controls (q := q) (cells := cells) (lanes := lanes) (rows := rows) (levels := d))

/-- The verifier receives both actual setup root families, with no repeated setup. -/
def verifier (controlRoots : Fin (2*d) → Digest) (keyRoots : Fin finalD → Digest) :
    OracleComp (SharedSequence.Shared Cfg Input Digest) (((Fin finalD → Digest) × (PackedPBSHonestHistoryProgram.VerifierResult (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase)) × Option (Sigma (RetainedPaddedExtractionProjection.Child (fun _ : ((Fin finalD → Digest) × (PackedPBSHonestHistoryProgram.VerifierResult (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase)) => extractionBase)))) :=
  PackedPBSHonestExtractionHistoryProgram.verifierProgram (bits := bits) length psi primitive (HonestControlKeySetup.withKeys family controlRoots) inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase keyRoots

/-- Real control-key and key-switch setup precede the complete verifier suffix. -/
def program : OracleComp (SharedSequence.Shared Cfg Input Digest)
    (((Fin (2*d) → Digest) × (Fin finalD → Digest)) × (((Fin finalD → Digest) × (PackedPBSHonestHistoryProgram.VerifierResult (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase)) × Option (Sigma (RetainedPaddedExtractionProjection.Child (fun _ : ((Fin finalD → Digest) × (PackedPBSHonestHistoryProgram.VerifierResult (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase)) => extractionBase))))) := do
  let roots ← (HonestJointKeySetup.program controlParameters setupParameters hs.encoding psi controls original)
  let returned ← (verifier (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase) roots.1 roots.2
  pure (roots,returned)

/-- The existing complete key-switch setup/verifier/extraction suffix uses
roots produced by the actual preceding control-key setup. -/
def controlSuffix (controlRoots : Fin (2*d) → Digest) :
    OracleComp (SharedSequence.Shared Cfg Input Digest) (((Fin finalD → Digest) × (PackedPBSHonestHistoryProgram.VerifierResult (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase)) × Option (Sigma (RetainedPaddedExtractionProjection.Child (fun _ : ((Fin finalD → Digest) × (PackedPBSHonestHistoryProgram.VerifierResult (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase)) => extractionBase)))) := (PackedPBSHonestExtractionHistoryProgram.program (bits := bits) length psi primitive (HonestControlKeySetup.withKeys family controlRoots) inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase original setupParameters)

omit [DecidableEq Input] [SampleableType Digest] in
/-- Factor the actual key-switch setup inside that same canonical suffix type. -/
theorem controlSuffix_eq (controlRoots : Fin (2*d) → Digest) :
    (controlSuffix (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase original setupParameters controlRoots) = (do
      let keyRoots ← HonestKeySetupReceipts.program setupParameters hs.encoding psi original
      (verifier (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase) controlRoots keyRoots) :=
  PackedPBSHonestExtractionHistoryProgram.program_eq_setup_bind (bits := bits)
    length psi primitive (HonestControlKeySetup.withKeys family controlRoots) inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase original setupParameters

omit [DecidableEq Input] [SampleableType Digest] in
/-- Erasing the extra returned key-root copy gives the exact old complete
key-switch setup/verifier/extraction program after actual control-key setup. -/
theorem control_prefix_eq :
    (fun outcome => (outcome.1.1,outcome.2)) <$> (program (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase original setupParameters controlParameters controls) = (do
      let controlRoots ← HonestControlKeySetup.program controlParameters hs.encoding psi controls
      let returned ← (controlSuffix (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase original setupParameters controlRoots)
      pure (controlRoots,returned)) := by
  simp only [program,HonestJointKeySetup.program,controlSuffix_eq,
    map_bind,bind_assoc,pure_bind]
  simp only [map_pure]

/-- Retain actual setup ends so later soundness consumes factual initialization. -/
def witness : ProbComp ((HonestJointKeySetup.Result (levels := d) (keyLevels := finalD) (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights)) × ((((Fin finalD → Digest) × (PackedPBSHonestHistoryProgram.VerifierResult (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase)) × Option (Sigma (RetainedPaddedExtractionProjection.Child (fun _ : ((Fin finalD → Digest) × (PackedPBSHonestHistoryProgram.VerifierResult (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase)) => extractionBase)))) × CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))) := do
  let built ← HonestJointKeySetup.witness controlParameters setupParameters hs.encoding psi controls original
    (QueryImpl.ofLift unifSpec ProbComp) dummy (AmbientMatrixSource.Shape first.heights)
  let returned ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (AmbientMatrixSource.Shape first.heights)) ((verifier (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase) built.1.1 built.2.1)).run built.2.2
  pure (built,returned)

/-- The verifier starts at the final end of both real setups. -/
theorem parts (result : (HonestJointKeySetup.Result (levels := d) (keyLevels := finalD) (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights)) × ((((Fin finalD → Digest) × (PackedPBSHonestHistoryProgram.VerifierResult (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase)) × Option (Sigma (RetainedPaddedExtractionProjection.Child (fun _ : ((Fin finalD → Digest) × (PackedPBSHonestHistoryProgram.VerifierResult (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase)) => extractionBase)))) × CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))) (supported : result ∈ support (witness (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase original setupParameters controlParameters controls)) :
    result.1 ∈ support (HonestJointKeySetup.witness controlParameters setupParameters hs.encoding psi controls original
      (QueryImpl.ofLift unifSpec ProbComp) dummy (AmbientMatrixSource.Shape first.heights)) ∧
    result.2 ∈ support ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (AmbientMatrixSource.Shape first.heights)) ((verifier (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase) result.1.1.1 result.1.2.1)).run result.1.2.2) := by
  simp only [witness,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at supported
  obtain ⟨built,builtSupported,returned,returnedSupported,equal⟩ := supported
  subst result
  exact ⟨builtSupported,returnedSupported⟩

/-- One raw execution retains both root families, verifier data and complete final state. -/
theorem project_witness :
    (fun result => (((result.1.1.1,result.1.2.1),result.2.1),result.2.2)) <$> (witness (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase original setupParameters controlParameters controls) =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (AmbientMatrixSource.Shape first.heights)) (program (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase original setupParameters controlParameters controls)).run (CheckpointExecution.empty (AmbientMatrixSource.Shape first.heights)) := by
  have setupProjection := HonestJointKeySetup.project_witness controlParameters setupParameters hs.encoding psi controls original
    (QueryImpl.ofLift unifSpec ProbComp) dummy (AmbientMatrixSource.Shape first.heights)
  rw [program,simulateQ_bind,StateT.run_bind,←setupProjection]
  simp only [witness,map_bind,bind_map_left,map_pure,simulateQ_bind,StateT.run_bind,
    simulateQ_pure,StateT.run_pure]

/-- Both receipts survive the full verifier; readiness of its actual initial
state is derived from the same supported pair of setup calls. -/
theorem initialized (result : (HonestJointKeySetup.Result (levels := d) (keyLevels := finalD) (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights)) × ((((Fin finalD → Digest) × (PackedPBSHonestHistoryProgram.VerifierResult (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase)) × Option (Sigma (RetainedPaddedExtractionProjection.Child (fun _ : ((Fin finalD → Digest) × (PackedPBSHonestHistoryProgram.VerifierResult (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase)) => extractionBase)))) × CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))) (supported : result ∈ support (witness (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase original setupParameters controlParameters controls)) :
    HonestControlKeySetup.Receipt controlParameters hs.encoding psi controls result.1.1.1 result.2.2.hash.log ∧
    HonestKeyQueryReceipt.Receipt setupParameters hs.encoding psi original result.1.2.1 result.2.2.hash.log ∧
    HonestSetupContinuation.Ready hs.encoding dummy (AmbientMatrixSource.Shape first.heights) result.1.2.2 := by
  have executed := parts (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase original setupParameters controlParameters controls result supported
  have setup := HonestJointKeySetup.initialized controlParameters setupParameters hs.encoding psi controls original
    (QueryImpl.ofLift unifSpec ProbComp) dummy (AmbientMatrixSource.Shape first.heights) result.1 executed.1
  have growing := SharedHashLog.run (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (AmbientMatrixSource.Shape first.heights)
    ((verifier (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase) result.1.1.1 result.1.2.1) result.1.2.2 result.2 executed.2
  exact ⟨HonestControlKeySetup.mono controlParameters hs.encoding psi controls result.1.1.1
      result.1.2.2.hash.log result.2.2.hash.log growing setup.1,
    HonestKeyQueryReceipt.mono setupParameters hs.encoding psi original result.1.2.1
      result.1.2.2.hash.log result.2.2.hash.log growing setup.2.1,setup.2.2⟩

/-- The shared hash/cache consistency and monitor audit also hold at the actual
full final end, alongside the two factual setup receipts. -/
theorem final_history (result : (HonestJointKeySetup.Result (levels := d) (keyLevels := finalD) (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights)) × ((((Fin finalD → Digest) × (PackedPBSHonestHistoryProgram.VerifierResult (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase)) × Option (Sigma (RetainedPaddedExtractionProjection.Child (fun _ : ((Fin finalD → Digest) × (PackedPBSHonestHistoryProgram.VerifierResult (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase)) => extractionBase)))) × CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))) (supported : result ∈ support (witness (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase original setupParameters controlParameters controls)) :
    CachedHashHandler.Coherent result.2.2.hash ∧ RecordedCheckpointQueries.Sound (AmbientMatrixSource.Shape first.heights) result.2.2 ∧
    CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) result.2.2 := by
  have executed := parts (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase original setupParameters controlParameters controls result supported
  have setup := (initialized (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase original setupParameters controlParameters controls result supported).2.2
  have valid := RecordedCheckpointQueries.run (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (AmbientMatrixSource.Shape first.heights)
    ((verifier (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase) result.1.1.1 result.1.2.1) result.1.2.2 ⟨setup.coherent,setup.sound⟩ result.2 executed.2
  exact ⟨valid.1,valid.2,CheckpointExecution.audited_run (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (AmbientMatrixSource.Shape first.heights)
    ((verifier (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase) result.1.1.1 result.1.2.1) result.1.2.2 setup.audited result.2 executed.2⟩

/-- A supported raw return supplies both final receipts and an actual initialized
verifier call whose initial receipts belong to the same two setup executions. -/
theorem initialized_program
    (result : (((Fin (2*d) → Digest) × (Fin finalD → Digest)) × (((Fin finalD → Digest) × (PackedPBSHonestHistoryProgram.VerifierResult (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase)) × Option (Sigma (RetainedPaddedExtractionProjection.Child (fun _ : ((Fin finalD → Digest) × (PackedPBSHonestHistoryProgram.VerifierResult (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase)) => extractionBase))))) × CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (supported : result ∈ support ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (AmbientMatrixSource.Shape first.heights)) (program (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase original setupParameters controlParameters controls)).run (CheckpointExecution.empty (AmbientMatrixSource.Shape first.heights)))) :
    HonestControlKeySetup.Receipt controlParameters hs.encoding psi controls result.1.1.1 result.2.hash.log ∧
    HonestKeyQueryReceipt.Receipt setupParameters hs.encoding psi original result.1.1.2 result.2.hash.log ∧
    ∃ initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights),
      HonestControlKeySetup.Receipt controlParameters hs.encoding psi controls result.1.1.1 initial.hash.log ∧
      HonestKeyQueryReceipt.Receipt setupParameters hs.encoding psi original result.1.1.2 initial.hash.log ∧
      HonestSetupContinuation.Ready hs.encoding dummy (AmbientMatrixSource.Shape first.heights) initial ∧
      (result.1.2,result.2) ∈ support ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (AmbientMatrixSource.Shape first.heights)) ((verifier (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase) result.1.1.1 result.1.1.2)).run initial) := by
  rw [←project_witness (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase original setupParameters controlParameters controls,support_map,Set.mem_image] at supported
  obtain ⟨actual,present,equal⟩ := supported
  subst result
  have executed := parts (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase original setupParameters controlParameters controls actual present
  have setup := HonestJointKeySetup.initialized controlParameters setupParameters hs.encoding psi controls original
    (QueryImpl.ofLift unifSpec ProbComp) dummy (AmbientMatrixSource.Shape first.heights) actual.1 executed.1
  have final := initialized (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase original setupParameters controlParameters controls actual present
  exact ⟨final.1,final.2.1,actual.1.2.2,setup.1,setup.2.1,setup.2.2,executed.2⟩

/-- Existing fixed-initial verifier interfaces can choose their required geometry
without changing the actual initial cache, log, flag or raw execution. -/
theorem initialized_for_shape (targetShape : Cfg → BinaryTree.Skeleton)
    (result : (((Fin (2*d) → Digest) × (Fin finalD → Digest)) × (((Fin finalD → Digest) × (PackedPBSHonestHistoryProgram.VerifierResult (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase)) × Option (Sigma (RetainedPaddedExtractionProjection.Child (fun _ : ((Fin finalD → Digest) × (PackedPBSHonestHistoryProgram.VerifierResult (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase)) => extractionBase))))) × CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (supported : result ∈ support ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (AmbientMatrixSource.Shape first.heights)) (program (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase original setupParameters controlParameters controls)).run (CheckpointExecution.empty (AmbientMatrixSource.Shape first.heights)))) :
    ∃ initial : CheckpointExecution.State (Input := Input) (Digest := Digest) targetShape,
      HonestControlKeySetup.Receipt controlParameters hs.encoding psi controls result.1.1.1 initial.hash.log ∧
      HonestKeyQueryReceipt.Receipt setupParameters hs.encoding psi original result.1.1.2 initial.hash.log ∧
      HonestSetupContinuation.Ready hs.encoding dummy targetShape initial ∧
      (result.1.2,result.2) ∈ support ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (AmbientMatrixSource.Shape first.heights)) ((verifier (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase) result.1.1.1 result.1.1.2)).run
        (CheckpointShapeTransport.state targetShape (AmbientMatrixSource.Shape first.heights) initial)) := by
  obtain ⟨_,_,initial,controlReceipt,keyReceipt,ready,executed⟩ :=
    initialized_program (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase original setupParameters controlParameters controls result supported
  refine ⟨CheckpointShapeTransport.state (AmbientMatrixSource.Shape first.heights) targetShape initial,controlReceipt,keyReceipt,
    HonestSetupContinuation.transport hs.encoding dummy (AmbientMatrixSource.Shape first.heights) targetShape initial ready,?_⟩
  rw [HonestSetupContinuation.state_roundtrip]
  exact executed

/-- All real setup hashes and verifier/extraction branches share this hazard charge. -/
def charge [Fintype Digest] := ExpectedHazard.charge (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (AmbientMatrixSource.Shape first.heights))
  (CheckpointCollision.loss unifSpec (AmbientMatrixSource.Shape first.heights)) (program (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase original setupParameters controlParameters controls) (CheckpointExecution.empty (AmbientMatrixSource.Shape first.heights))

/-- One full final authentication event is charged across both key setups and
all verification/extraction work from the actual empty monitor state. -/
theorem bad_le_charge [Fintype Digest] :
    Pr{let result ← (witness (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase original setupParameters controlParameters controls)}[CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) result.2.2] ≤
    charge (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase original setupParameters controlParameters controls := by
  have bound := CheckpointCollision.failure_from_empty_le_charge (QueryImpl.ofLift unifSpec ProbComp)
    hs.encoding dummy (AmbientMatrixSource.Shape first.heights) (program (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase original setupParameters controlParameters controls)
  rw [←project_witness (bits := bits) length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase reconstructionBase comparisonBase extractionLog positive output extractionFirstSmall extractionRoundSmall extractionNodes extractionBase original setupParameters controlParameters controls,prEvent_map] at bound
  exact bound

end
end FormalProof4FHE.HasteBoots.PackedPBSJointSetupHistoryProgram
