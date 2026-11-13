module
public import FormalProof4FHE.HasteBoots.PackedPBSKeySwitchComparisons
public import FormalProof4FHE.HasteBoots.RetainedPaddedComparisonProjection
@[expose] public section

/-! One shared oracle program for the complete PBS prefix and retained final
comparison. The projection retains the actual final monitored history. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSComparisonHistoryProgram
open OracleSpec OracleComp
open PackedPBSKeySwitchComparisons
open NativeRootMessage (Digest)
open PackedPBSSecondComparisons (sharedScheme)
noncomputable section

variable {q finalC finalD bits d b c r k n front suffix m queries height : ℕ} [jointInstance1 : Fact q.Prime]
  {Input Cfg Response Memory CommitMemory FirstMessage Message : Type}
  [jointInstance2 : DecidableEq Input] [jointInstance3 : DecidableEq Digest] [jointInstance4 : SampleableType Digest]
  [jointInstance5 : SampleableType (Fin k → Fin r → ZMod q)] [jointInstance6 : SampleableType (Fin b → ZMod q)]
  [jointInstance7 : SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [jointInstance8 : SampleableType (Fin queries → Fin (2^height))]
  [jointInstance9 : SampleableType (PackedZeroReduction.Points (ZMod q) n b)] [jointInstance10 : SampleableType (Fin b → Fin b → ZMod q)]

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
  [jointInstance11 : SampleableType (Fin accB → ZMod q)]
  [jointInstance12 : SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^accFront) accB)]
  [jointInstance13 : SampleableType (Fin accQueries → Fin (2^accHeight))]

variable {lanes cells rows rounds : ℕ}

variable {MonoResponse MonoCommitMemory : Type} {monoK monoFront monoSuffix monoM monoQueries monoHeight : ℕ}
  [jointInstance14 : SampleableType (Fin monoK → Fin (rows+1) → ZMod q)] [jointInstance15 : SampleableType (Fin (2^lanes) → ZMod q)]
  [jointInstance16 : SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^monoFront) (2^lanes))]
  [jointInstance17 : SampleableType (Fin monoQueries → Fin (2^monoHeight))]

variable {ZeroResponse ZeroCommitMemory : Type} {zeroFront zeroSuffix zeroM zeroQueries zeroHeight : ℕ}
  [jointInstance18 : SampleableType (ZMod q)] [jointInstance19 : SampleableType (Fin (cells+rows) → ZMod q)]
  [jointInstance20 : SampleableType (PackedZeroReduction.Points (ZMod q) (cells+rows) (2^lanes))]
  [jointInstance21 : SampleableType (Fin (2^lanes) → Fin (2^lanes) → ZMod q)]
  [jointInstance22 : SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))]
  [jointInstance23 : SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^zeroFront) (2^lanes))]
  [jointInstance24 : SampleableType (Fin zeroQueries → Fin (2^zeroHeight))]

variable {InputResponse InputCommitMemory : Type} {inputFront inputSuffix inputM inputQueries inputHeight : ℕ}
  [jointInstance25 : SampleableType (Fin 4 → ZMod q)]
  [jointInstance26 : SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^inputFront) 4)]
  [jointInstance27 : SampleableType (Fin inputQueries → Fin (2^inputHeight))]

variable {FinalResponse FinalCommitMemory : Type}
  [jointInstance28 : SampleableType (Fin 4 → Fin 1 → ZMod q)]

variable {ProductResponse ProductCommitMemory : Type}
  [jointInstance29 : SampleableType (PackedZeroReduction.Points (ZMod q) finalC 4)]
  [jointInstance30 : SampleableType (Fin 4 → Fin 4 → ZMod q)]

variable {ReconstructionResponse ReconstructionCommitMemory : Type}

open scoped BigOperators
variable {RetainedMemory FinalSelection FinalRoot FinalData : Type}
  {repetitions : Fin finalD → ℕ}

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
    [jointInstance33 : ∀ index memory side, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((finalBase index memory).code side).front) 4)]
    [jointInstance34 : ∀ index memory side, SampleableType (Fin ((finalBase index memory).code side).queries → Fin (2^first.heights ((finalBase index memory).tag side)))]

    (productFirstSmall : (2*4-1)*2+1 ≤ q) (productRoundSmall : (2*4-1)*3+1 ≤ q)
    (productNodes : 2*4 ≤ (2*4-1)*2+1)
    (productBase : Memory → KeySwitchPaddedProduct.Scheme (q := q) (d := finalD) (b := 4) (n := finalC)
      (Input := Input) (Cfg := Cfg) (Response := ProductResponse) (Memory := Memory) (CommitMemory := ProductCommitMemory) (heights := first.heights))
    [jointInstance35 : ∀ memory factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((productBase memory).code factor).front) 4)]
    [jointInstance36 : ∀ memory factor, SampleableType (Fin ((productBase memory).code factor).queries → Fin (2^first.heights ((productBase memory).tag factor)))]

    (reconstructionBase : Memory → PaddedLinear.Scheme (ZMod q) Input Digest Cfg ReconstructionResponse Memory ReconstructionCommitMemory first.heights (2*finalD+2) 4 (1+finalC))
    [jointInstance37 : ∀ memory factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((reconstructionBase memory).code factor).front) 4)]
    [jointInstance38 : ∀ memory factor, SampleableType (Fin ((reconstructionBase memory).code factor).queries → Fin (2^first.heights ((reconstructionBase memory).tag factor)))]
    (comparisonBase : (memory : Memory) → PackedPBSComparisonStage.Scheme Cfg Input Memory ((Fin (∑ i, repetitions i) → Digest) × RetainedMemory) (FinalSelection × ShortCircuitSequence.Outcome FinalRoot FinalData Memory) finalD)


local notation "ProductBefore" => PackedPBSKeySwitchReconstruction.BeforeFinalReconstruction (q := q) (Response := Response) (CommitMemory := CommitMemory)
  (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix) (queries := queries) (height := height)
  (AccResponse := AccResponse) (accB := accB) (accC := accC) (accR := accR) (accFront := accFront) (accQueries := accQueries) (accHeight := accHeight)
  (MonoResponse := MonoResponse) (MonoCommitMemory := MonoCommitMemory) (lanes := lanes) (cells := cells) (rows := rows)
  (monoK := monoK) (monoFront := monoFront) (monoQueries := monoQueries) (monoHeight := monoHeight)
  (ZeroResponse := ZeroResponse) (ZeroCommitMemory := ZeroCommitMemory) (zeroFront := zeroFront) (zeroQueries := zeroQueries) (zeroHeight := zeroHeight)
  (InputResponse := InputResponse) (InputCommitMemory := InputCommitMemory) (inputB := 4) (inputC := finalC)
  (inputFront := inputFront) (inputQueries := inputQueries) (inputHeight := inputHeight)

  (FinalResponse := FinalResponse) (FinalCommitMemory := FinalCommitMemory) (finalD := finalD) (finalB := 4) (finalC := finalC)

  (ProductResponse := ProductResponse) (ProductCommitMemory := ProductCommitMemory)


/-- Erase only checkpoint snapshots; retain all emitted roots and actual packets. -/
def erasePrior (before : ProductBefore first second finalBase productBase ×
    Option (PackedPBSKeySwitchReconstruction.ReconstructionChild first.heights reconstructionBase)) :=
  (PackedPBSKeySwitchReconstruction.eraseBefore first second finalBase productBase before.1,
    before.2.map fun selected =>
      (⟨selected.1,(selected.2.1.1,selected.2.2.1)⟩ : RetainedPaddedComparisonProjection.Index
        reconstructionBase))

/-- A family-independent observation of all real returns, omitting only
proof snapshots so setup's actual roots may select the following program. -/
def eraseOutcome (outcome : (ProductBefore first second finalBase productBase ×
    Option (PackedPBSKeySwitchReconstruction.ReconstructionChild first.heights reconstructionBase)) ×
    Option (Sigma (RetainedPaddedComparison.Child reconstructionBase comparisonBase))) :=
  RetainedPaddedComparisonProjection.eraseOutcome reconstructionBase comparisonBase (@erasePrior q finalC finalD d b c r k n front suffix queries height jointInstance1 Input Cfg Response Memory CommitMemory Helper Selection Root Data SecondHelper SecondSelection SecondRoot SecondData AccResponse accB accC accR accFront accQueries accHeight lanes cells rows MonoResponse MonoCommitMemory monoK monoFront monoQueries monoHeight ZeroResponse ZeroCommitMemory zeroFront zeroQueries zeroHeight InputResponse InputCommitMemory inputFront inputQueries inputHeight FinalResponse FinalCommitMemory ProductResponse ProductCommitMemory ReconstructionResponse ReconstructionCommitMemory first second finalBase productBase reconstructionBase) outcome

/-- The complete predecessor and computed final comparison share one handler. -/
def program := do
  let before ← PackedPBSKeySwitchReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase (2^bits : ZMod q) reconstructionBase
  RetainedPaddedComparisonProjection.program (fun memory => KeySwitchPaddedReconstruction.stage (reconstructionBase memory) hs.encoding inputReference finalFamily finalNodes (2^bits : ZMod q)) comparisonBase (fun previous : _ × _ => previous.2) before

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- The entire retained verifier projects to one actual oracle execution,
with the inherited cache, checkpoints and persistent failure bit intact. -/
theorem project_witness
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape first.heights) initial.checkpoints)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (first.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)) :
    (fun outcome => ((@eraseOutcome q finalC finalD d b c r k n front suffix queries height jointInstance1 Input Cfg Response Memory CommitMemory Helper Selection Root Data SecondHelper SecondSelection SecondRoot SecondData AccResponse accB accC accR accFront accQueries accHeight lanes cells rows MonoResponse MonoCommitMemory monoK monoFront monoQueries monoHeight ZeroResponse ZeroCommitMemory zeroFront zeroQueries zeroHeight InputResponse InputCommitMemory inputFront inputQueries inputHeight FinalResponse FinalCommitMemory ProductResponse ProductCommitMemory ReconstructionResponse ReconstructionCommitMemory RetainedMemory FinalSelection FinalRoot FinalData repetitions first second finalBase productBase reconstructionBase comparisonBase) outcome,
      PackedPBSKeySwitchComparisons.finalState first second finalBase productBase reconstructionBase comparisonBase outcome)) <$>
      (PackedPBSKeySwitchComparisons.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase (2^bits : ZMod q) reconstructionBase comparisonBase initial) =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (AmbientMatrixSource.Shape first.heights)) (@program q finalC finalD bits d b c r k n front suffix m queries height jointInstance1 Input Cfg Response Memory CommitMemory FirstMessage Message jointInstance3 jointInstance5 jointInstance6 jointInstance7 jointInstance8 jointInstance9 jointInstance10 length psi primitive family inputs base hs nodesEnough radix linearBase Helper Selection Root Data SecondHelper SecondSelection SecondRoot SecondData AccResponse accB accC accR accFront accSuffix accM accQueries accHeight jointInstance11 jointInstance12 jointInstance13 lanes cells rows rounds MonoResponse MonoCommitMemory monoK monoFront monoSuffix monoM monoQueries monoHeight jointInstance14 jointInstance15 jointInstance16 jointInstance17 ZeroResponse ZeroCommitMemory zeroFront zeroSuffix zeroM zeroQueries zeroHeight jointInstance20 jointInstance21 jointInstance23 jointInstance24 InputResponse InputCommitMemory inputFront inputSuffix inputM inputQueries inputHeight jointInstance25 jointInstance26 jointInstance27 FinalResponse FinalCommitMemory jointInstance28 ProductResponse ProductCommitMemory jointInstance29 jointInstance30 ReconstructionResponse ReconstructionCommitMemory RetainedMemory FinalSelection FinalRoot FinalData repetitions first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase jointInstance33 jointInstance34 productFirstSmall productRoundSmall productNodes productBase jointInstance35 jointInstance36 reconstructionBase jointInstance37 jointInstance38 comparisonBase)).run
      (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape first.heights) initial) := by
  have projected := PackedPBSKeySwitchReconstruction.project_witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase (2^bits : ZMod q) reconstructionBase initial compatible restricted
  exact RetainedPaddedComparisonProjection.project_bind
    (fun memory => KeySwitchPaddedReconstruction.stage (reconstructionBase memory) hs.encoding inputReference finalFamily finalNodes (2^bits : ZMod q)) comparisonBase (@erasePrior q finalC finalD d b c r k n front suffix queries height jointInstance1 Input Cfg Response Memory CommitMemory Helper Selection Root Data SecondHelper SecondSelection SecondRoot SecondData AccResponse accB accC accR accFront accQueries accHeight lanes cells rows MonoResponse MonoCommitMemory monoK monoFront monoQueries monoHeight ZeroResponse ZeroCommitMemory zeroFront zeroQueries zeroHeight InputResponse InputCommitMemory inputFront inputQueries inputHeight FinalResponse FinalCommitMemory ProductResponse ProductCommitMemory ReconstructionResponse ReconstructionCommitMemory first second finalBase productBase reconstructionBase)
    (fun before : _ × _ => before.2) (fun before : _ × _ => before.2)
    hs.encoding dummy (by intro memory; rfl) (by intro before; rfl)
    (PackedPBSKeySwitchReconstruction.finalState first second finalBase productBase reconstructionBase) (PackedPBSKeySwitchReconstruction.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase (2^bits : ZMod q) reconstructionBase initial) (PackedPBSKeySwitchReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase (2^bits : ZMod q) reconstructionBase) (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape first.heights) initial) projected


end
end FormalProof4FHE.HasteBoots.PackedPBSComparisonHistoryProgram
