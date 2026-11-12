module
public import FormalProof4FHE.HasteBoots.PackedPBSKeySwitchReconstruction
public import FormalProof4FHE.HasteBoots.PackedPBSKeySwitchComparisons
public import FormalProof4FHE.HasteBoots.RetainedPaddedComparisonExecution
public import FormalProof4FHE.HasteBoots.KeySwitchPaddedReconstruction
public import FormalProof4FHE.HasteBoots.DependentStageContinuation
@[expose] public section

/-! Operational final comparison, exact snapshot erasure and one hash-failure
charge for the complete PBS prefix through that comparison. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSKeySwitchComparisonExecution
open OracleSpec OracleComp
open NativeRootMessage (Digest)
open PackedPBSSecondComparisons (sharedScheme)
noncomputable section
variable {q log d b c r k n front suffix m queries height : ℕ} [Fact q.Prime]
  {Input Cfg Response Memory CommitMemory FirstMessage Message : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]
  [SampleableType (Fin k → Fin r → ZMod q)] [SampleableType (Fin b → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^front) b)]
  [SampleableType (Fin queries → Fin (2^height))]
  [SampleableType (PackedZeroReduction.Points (ZMod q) n b)] [SampleableType (Fin b → Fin b → ZMod q)]
abbrev Outcome := PackedPBSFirstReconstruction.Before (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (c := c) (r := r) (k := k) (n := n) (d := d)
    (front := front) (queries := queries) (height := height) ×
  Option (PackedPBSFirstReconstruction.LinearOutcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
    (Memory := Memory) (CommitMemory := CommitMemory) (b := b) (d := d) (front := front) (suffix := suffix)
    (queries := queries) (height := height))

variable (length : 2^c*b = 2^log) (psi : ZMod q) (primitive : IsPrimitiveRoot psi (2^(log+1)))
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


abbrev ComparisonReturn := Selection × ShortCircuitSequence.Outcome Root Data Memory

local notation "Return" => PackedPBSKeySwitchReconstruction.ComparisonReturn (Selection := Selection) (Root := Root) (Data := Data) (Memory := Memory)

abbrev Before (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d) :=
  Prior × Option (PackedPBSComparisonStage.Outcome s)

local notation "Reached" => Before (q := q) (Response := Response) (CommitMemory := CommitMemory)
  (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix)
  (queries := queries) (height := height)

abbrev LinearOutcome (heights : Cfg → ℕ) :=
  AmbientLinear.Prefix heights (Input := Input) (Digest := Digest) (CommitMemory := CommitMemory) (count := 2*d+2) ×
  AmbientLinear.RunResult heights (F := ZMod q) (Input := Input) (Digest := Digest) (Response := Response)
    (Memory := Memory) (count := 2*d+2) (b := b) (front := front) (suffix := suffix) (height := height) (queries := queries)


local notation "Child" => LinearOutcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
  (Memory := Memory) (CommitMemory := CommitMemory) (d := d) (b := b) (front := front) (suffix := suffix)
  (queries := queries) (height := height)

abbrev SecondBefore (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d) :=
  Reached first × Option (Child first.heights)

local notation "Previous" => SecondBefore (q := q) (Response := Response) (CommitMemory := CommitMemory)
  (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix)
  (queries := queries) (height := height)

variable {SecondHelper SecondSelection SecondRoot SecondData : Type}
local notation "Return2" => SecondSelection × ShortCircuitSequence.Outcome SecondRoot SecondData Memory

abbrev ComparisonOutcome (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d) :=
  PackedPBSComparisonStage.Outcome (sharedScheme first.heights second)

abbrev BeforeAccumulator (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d) :=
  Previous first × Option (ComparisonOutcome first second)

local notation "Decomposed" => BeforeAccumulator (q := q) (Response := Response) (CommitMemory := CommitMemory)
  (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix)
  (queries := queries) (height := height)

variable {AccResponse : Type} {accB accC accR accFront accSuffix accM accQueries accHeight : ℕ}
  [SampleableType (Fin accB → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^accFront) accB)]
  [SampleableType (Fin accQueries → Fin (2^accHeight))]

local notation "AccScheme" => AmbientAccumulator.Scheme (ZMod q) Input Digest Cfg AccResponse Memory Memory
  accB accC accR accFront accSuffix accM accQueries accHeight

abbrev AccumulatorOutcome (heights : Cfg → ℕ) :=
  AmbientAccumulator.Prefix heights (Input := Input) (Digest := Digest) (CommitMemory := Memory) ×
  AmbientAccumulator.RunResult heights (F := ZMod q) (Input := Input) (Digest := Digest) (Response := AccResponse)
    (Memory := Memory) (b := accB) (c := accC) (r := accR) (front := accFront) (queries := accQueries) (height := accHeight)

local notation "AccChild" => AccumulatorOutcome (q := q) (Input := Input) (Cfg := Cfg) (AccResponse := AccResponse)
  (Memory := Memory) (accB := accB) (accC := accC) (accR := accR) (accFront := accFront)
  (accQueries := accQueries) (accHeight := accHeight)

abbrev AfterAccumulator (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d) :=
  Decomposed first second × Option (AccChild first.heights)

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

abbrev MonomialOutcome (heights : Cfg → ℕ) :=
  AmbientMonomialNTT.Trace heights (F := ZMod q) (Input := Input) (Digest := Digest) (Cfg := Cfg)
    (Response := MonoResponse) (Memory := Memory) (CommitMemory := MonoCommitMemory)
    (b := (2^lanes)) (c := cells) (r := (rows+1)) (k := monoK) (front := monoFront) (queries := monoQueries) (height := monoHeight) ×
  CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)

local notation "MonoChild" => MonomialOutcome (q := q) (Input := Input) (Cfg := Cfg) (Memory := Memory)
  (MonoResponse := MonoResponse) (MonoCommitMemory := MonoCommitMemory) (lanes := lanes) (cells := cells) (rows := rows)
  (monoK := monoK) (monoFront := monoFront) (monoQueries := monoQueries) (monoHeight := monoHeight)


abbrev BeforeProduct (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d) :=
  Finished first second × Option (MonoChild first.heights)

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

abbrev ProductOutcome (heights : Cfg → ℕ) :=
  AmbientPublicZeroCheck.Prefix heights (Private := Bool) (Input := Input) (Digest := Digest) (CommitMemory := ZeroCommitMemory) ×
  AmbientPublicZeroCheck.RunResult heights (F := ZMod q) (Private := Bool) (Input := Input) (Digest := Digest)
    (Response := ZeroResponse) (Memory := Memory) (b := 2^lanes) (n := cells+rows) (front := zeroFront) (queries := zeroQueries) (height := zeroHeight)

local notation "ProductChild" => ProductOutcome (q := q) (Input := Input) (Cfg := Cfg) (Memory := Memory)
  (ZeroResponse := ZeroResponse) (ZeroCommitMemory := ZeroCommitMemory) (lanes := lanes) (cells := cells) (rows := rows)
  (zeroFront := zeroFront) (zeroQueries := zeroQueries) (zeroHeight := zeroHeight)

abbrev BeforeInput (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d) :=
  NTTBefore first second × Option (ProductChild first.heights)

local notation "MonomialBefore" => BeforeInput (q := q) (Response := Response) (CommitMemory := CommitMemory)
  (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix) (queries := queries) (height := height)
  (AccResponse := AccResponse) (accB := accB) (accC := accC) (accR := accR) (accFront := accFront) (accQueries := accQueries) (accHeight := accHeight)
  (MonoResponse := MonoResponse) (MonoCommitMemory := MonoCommitMemory) (lanes := lanes) (cells := cells) (rows := rows)
  (monoK := monoK) (monoFront := monoFront) (monoQueries := monoQueries) (monoHeight := monoHeight)
  (ZeroResponse := ZeroResponse) (ZeroCommitMemory := ZeroCommitMemory) (zeroFront := zeroFront) (zeroQueries := zeroQueries) (zeroHeight := zeroHeight)

variable {InputResponse InputCommitMemory : Type} {inputB inputC inputFront inputSuffix inputM inputQueries inputHeight : ℕ}
  [SampleableType (Fin inputB → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^inputFront) inputB)]
  [SampleableType (Fin inputQueries → Fin (2^inputHeight))]
local notation "InputScheme" => AmbientKnownInput.Scheme (ZMod q) Input Digest Cfg InputResponse Memory InputCommitMemory
  inputB (1+inputC) inputFront inputSuffix inputM inputQueries inputHeight

abbrev InputOutcome (heights : Cfg → ℕ) :=
  AmbientKnownInput.Prefix heights (Input := Input) (Digest := Digest) (CommitMemory := InputCommitMemory) ×
  AmbientKnownInput.RunResult heights (F := ZMod q) (Input := Input) (Digest := Digest) (Response := InputResponse) (Memory := Memory)
    (b := inputB) (n := 1+inputC) (front := inputFront) (queries := inputQueries) (height := inputHeight)
local notation "InputChild" => InputOutcome (q := q) (Input := Input) (Cfg := Cfg) (Memory := Memory)
  (InputResponse := InputResponse) (InputCommitMemory := InputCommitMemory) (inputB := inputB) (inputC := inputC)
  (inputFront := inputFront) (inputQueries := inputQueries) (inputHeight := inputHeight)

abbrev BeforeNTT (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d) :=
  MonomialBefore first second × Option (InputChild first.heights)

local notation "InputBefore" => BeforeNTT (q := q) (Response := Response) (CommitMemory := CommitMemory)
  (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix) (queries := queries) (height := height)
  (AccResponse := AccResponse) (accB := accB) (accC := accC) (accR := accR) (accFront := accFront) (accQueries := accQueries) (accHeight := accHeight)
  (MonoResponse := MonoResponse) (MonoCommitMemory := MonoCommitMemory) (lanes := lanes) (cells := cells) (rows := rows)
  (monoK := monoK) (monoFront := monoFront) (monoQueries := monoQueries) (monoHeight := monoHeight)
  (ZeroResponse := ZeroResponse) (ZeroCommitMemory := ZeroCommitMemory) (zeroFront := zeroFront) (zeroQueries := zeroQueries) (zeroHeight := zeroHeight)
  (InputResponse := InputResponse) (InputCommitMemory := InputCommitMemory) (inputB := inputB) (inputC := inputC)
  (inputFront := inputFront) (inputQueries := inputQueries) (inputHeight := inputHeight)

variable {FinalResponse FinalCommitMemory : Type} {finalD finalB finalC : ℕ}
  [SampleableType (Fin finalB → Fin 1 → ZMod q)] [SampleableType (Fin finalB → ZMod q)]

abbrev BeforeFinalProduct (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (finalBase : Fin (finalD+1) → Memory → PaddedNTT.Scheme (ZMod q) Input Digest Cfg FinalResponse Memory FinalCommitMemory first.heights finalB finalC 1 finalB) :=
  InputBefore first second × Option (PaddedNTTSequence.Trace finalBase ×
    CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))

local notation "FinalBefore" => BeforeFinalProduct (q := q) (Response := Response) (CommitMemory := CommitMemory)
  (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix) (queries := queries) (height := height)
  (AccResponse := AccResponse) (accB := accB) (accC := accC) (accR := accR) (accFront := accFront) (accQueries := accQueries) (accHeight := accHeight)
  (MonoResponse := MonoResponse) (MonoCommitMemory := MonoCommitMemory) (lanes := lanes) (cells := cells) (rows := rows)
  (monoK := monoK) (monoFront := monoFront) (monoQueries := monoQueries) (monoHeight := monoHeight)
  (ZeroResponse := ZeroResponse) (ZeroCommitMemory := ZeroCommitMemory) (zeroFront := zeroFront) (zeroQueries := zeroQueries) (zeroHeight := zeroHeight)
  (InputResponse := InputResponse) (InputCommitMemory := InputCommitMemory) (inputB := inputB) (inputC := inputC)
  (inputFront := inputFront) (inputQueries := inputQueries) (inputHeight := inputHeight)

  (FinalResponse := FinalResponse) (FinalCommitMemory := FinalCommitMemory) (finalD := finalD) (finalB := finalB) (finalC := finalC)

variable {ProductResponse ProductCommitMemory : Type}
  [SampleableType (PackedZeroReduction.Points (ZMod q) finalC finalB)]
  [SampleableType (Fin finalB → Fin finalB → ZMod q)]

abbrev FinalProductChild (heights : Cfg → ℕ)
    (productBase : Memory → KeySwitchPaddedProduct.Scheme (q := q) (d := finalD) (b := finalB) (n := finalC)
      (Input := Input) (Cfg := Cfg) (Response := ProductResponse) (Memory := Memory) (CommitMemory := ProductCommitMemory) (heights := heights)) :=
  Sigma (fun incoming : Memory => PaddedZeroCheck.Prefix (Factor := PBSHadamard.Factor finalD)
    (Input := Input) (Digest := Digest) (CommitMemory := ProductCommitMemory) heights × PaddedZeroCheck.RunResult (productBase incoming))

abbrev BeforeFinalReconstruction (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (finalBase : Fin (finalD+1) → Memory → PaddedNTT.Scheme (ZMod q) Input Digest Cfg FinalResponse Memory FinalCommitMemory first.heights finalB finalC 1 finalB)
    (productBase : Memory → KeySwitchPaddedProduct.Scheme (q := q) (d := finalD) (b := finalB) (n := finalC)
      (Input := Input) (Cfg := Cfg) (Response := ProductResponse) (Memory := Memory) (CommitMemory := ProductCommitMemory) (heights := first.heights)) :=
  FinalBefore first second finalBase × Option (FinalProductChild first.heights productBase)

local notation "ProductBefore" => PackedPBSKeySwitchReconstruction.BeforeFinalReconstruction (q := q) (Response := Response) (CommitMemory := CommitMemory)
  (b := b) (c := c) (r := r) (k := k) (n := n) (front := front) (suffix := suffix) (queries := queries) (height := height)
  (AccResponse := AccResponse) (accB := accB) (accC := accC) (accR := accR) (accFront := accFront) (accQueries := accQueries) (accHeight := accHeight)
  (MonoResponse := MonoResponse) (MonoCommitMemory := MonoCommitMemory) (lanes := lanes) (cells := cells) (rows := rows)
  (monoK := monoK) (monoFront := monoFront) (monoQueries := monoQueries) (monoHeight := monoHeight)
  (ZeroResponse := ZeroResponse) (ZeroCommitMemory := ZeroCommitMemory) (zeroFront := zeroFront) (zeroQueries := zeroQueries) (zeroHeight := zeroHeight)
  (InputResponse := InputResponse) (InputCommitMemory := InputCommitMemory) (inputB := inputB) (inputC := inputC)
  (inputFront := inputFront) (inputQueries := inputQueries) (inputHeight := inputHeight)

  (FinalResponse := FinalResponse) (FinalCommitMemory := FinalCommitMemory) (finalD := finalD) (finalB := finalB) (finalC := finalC)

  (ProductResponse := ProductResponse) (ProductCommitMemory := ProductCommitMemory)

variable {ReconstructionResponse ReconstructionCommitMemory : Type}

abbrev ReconstructionChild (heights : Cfg → ℕ)
    (reconstructionBase : Memory → PaddedLinear.Scheme (ZMod q) Input Digest Cfg ReconstructionResponse Memory ReconstructionCommitMemory heights (2*finalD+2) finalB (1+finalC)) :=
  PackedPBSKeySwitchReconstruction.ReconstructionChild heights reconstructionBase

variable {FinalHelper FinalReturn : Memory → Type}

/-! The final shared comparison follows the actual reconstruction return.
The complete predecessor execution is retained, including all rejected and
skipped branches. Contexts, roots, private memory and full history are inherited.
The native request factory is supplied as a program, not a security certificate. -/

def program (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^cells*(2^lanes) = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (zeroNodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (zeroBase : Memory → ZeroScheme)
    (accLength : 2^accC*accB = 2^log) (inputReference : NativeGoldParameterStore.Reference)
    (inputLength : 2^inputC*inputB = 2^log) (inputSmall : 2*inputB ≤ q) (inputBase : Memory → InputScheme)
    (finalFamily : PackedPBSOriginalReferences.Family finalD) (finalNodes : 2*finalB ≤ q)
    (finalLength : 2^finalC*finalB = 2^log)
    (finalBase : Fin (finalD+1) → Memory → PaddedNTT.Scheme (ZMod q) Input Digest Cfg FinalResponse Memory FinalCommitMemory first.heights finalB finalC 1 finalB)
    [∀ index memory side, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((finalBase index memory).code side).front) finalB)]
    [∀ index memory side, SampleableType (Fin ((finalBase index memory).code side).queries → Fin (2^first.heights ((finalBase index memory).tag side)))]
    (productFirstSmall : (2*finalB-1)*2+1 ≤ q) (productRoundSmall : (2*finalB-1)*3+1 ≤ q)
    (productNodes : 2*finalB ≤ (2*finalB-1)*2+1)
    (productBase : Memory → KeySwitchPaddedProduct.Scheme (q := q) (d := finalD) (b := finalB) (n := finalC)
      (Input := Input) (Cfg := Cfg) (Response := ProductResponse) (Memory := Memory) (CommitMemory := ProductCommitMemory) (heights := first.heights))
    [∀ memory factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((productBase memory).code factor).front) finalB)]
    [∀ memory factor, SampleableType (Fin ((productBase memory).code factor).queries → Fin (2^first.heights ((productBase memory).tag factor)))]
    (finalRadix : ZMod q)
    (reconstructionBase : Memory → PaddedLinear.Scheme (ZMod q) Input Digest Cfg ReconstructionResponse Memory ReconstructionCommitMemory first.heights (2*finalD+2) finalB (1+finalC))
    [∀ memory factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((reconstructionBase memory).code factor).front) finalB)]
    [∀ memory factor, SampleableType (Fin ((reconstructionBase memory).code factor).queries → Fin (2^first.heights ((reconstructionBase memory).tag factor)))]
    (comparisonBase : (memory : Memory) → PackedPBSComparisonStage.Scheme Cfg Input Memory (FinalHelper memory) (FinalReturn memory) finalD)
 :=
  (PackedPBSKeySwitchReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase finalRadix reconstructionBase) >>=
    RetainedPaddedComparisonExecution.program (fun memory => KeySwitchPaddedReconstruction.stage (reconstructionBase memory) hs.encoding inputReference finalFamily finalNodes finalRadix) comparisonBase Prod.snd

def erasePrior (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (finalBase : Fin (finalD+1) → Memory → PaddedNTT.Scheme (ZMod q) Input Digest Cfg FinalResponse Memory FinalCommitMemory first.heights finalB finalC 1 finalB)
    (productBase : Memory → KeySwitchPaddedProduct.Scheme (q := q) (d := finalD) (b := finalB) (n := finalC)
      (Input := Input) (Cfg := Cfg) (Response := ProductResponse) (Memory := Memory) (CommitMemory := ProductCommitMemory) (heights := first.heights))
    (reconstructionBase : Memory → PaddedLinear.Scheme (ZMod q) Input Digest Cfg ReconstructionResponse Memory ReconstructionCommitMemory first.heights (2*finalD+2) finalB (1+finalC))
    (before : (ProductBefore first second finalBase productBase × Option (PackedPBSKeySwitchReconstruction.ReconstructionChild first.heights reconstructionBase))) :=
  (PackedPBSKeySwitchReconstruction.eraseBefore first second finalBase productBase before.1,
    before.2.map (RetainedPaddedComparisonExecution.eraseReconstruction reconstructionBase))

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- Erasing the complete retained witness gives exactly the native operational program. -/

abbrev project_witness (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^cells*(2^lanes) = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (zeroNodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (zeroBase : Memory → ZeroScheme)
    (accLength : 2^accC*accB = 2^log) (inputReference : NativeGoldParameterStore.Reference)
    (inputLength : 2^inputC*inputB = 2^log) (inputSmall : 2*inputB ≤ q) (inputBase : Memory → InputScheme)
    (finalFamily : PackedPBSOriginalReferences.Family finalD) (finalNodes : 2*finalB ≤ q)
    (finalLength : 2^finalC*finalB = 2^log)
    (finalBase : Fin (finalD+1) → Memory → PaddedNTT.Scheme (ZMod q) Input Digest Cfg FinalResponse Memory FinalCommitMemory first.heights finalB finalC 1 finalB)
    [∀ index memory side, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((finalBase index memory).code side).front) finalB)]
    [∀ index memory side, SampleableType (Fin ((finalBase index memory).code side).queries → Fin (2^first.heights ((finalBase index memory).tag side)))]
    (productFirstSmall : (2*finalB-1)*2+1 ≤ q) (productRoundSmall : (2*finalB-1)*3+1 ≤ q)
    (productNodes : 2*finalB ≤ (2*finalB-1)*2+1)
    (productBase : Memory → KeySwitchPaddedProduct.Scheme (q := q) (d := finalD) (b := finalB) (n := finalC)
      (Input := Input) (Cfg := Cfg) (Response := ProductResponse) (Memory := Memory) (CommitMemory := ProductCommitMemory) (heights := first.heights))
    [∀ memory factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((productBase memory).code factor).front) finalB)]
    [∀ memory factor, SampleableType (Fin ((productBase memory).code factor).queries → Fin (2^first.heights ((productBase memory).tag factor)))]
    (finalRadix : ZMod q)
    (reconstructionBase : Memory → PaddedLinear.Scheme (ZMod q) Input Digest Cfg ReconstructionResponse Memory ReconstructionCommitMemory first.heights (2*finalD+2) finalB (1+finalC))
    [∀ memory factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((reconstructionBase memory).code factor).front) finalB)]
    [∀ memory factor, SampleableType (Fin ((reconstructionBase memory).code factor).queries → Fin (2^first.heights ((reconstructionBase memory).tag factor)))]
    (comparisonBase : (memory : Memory) → PackedPBSComparisonStage.Scheme Cfg Input Memory (FinalHelper memory) (FinalReturn memory) finalD)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape first.heights) initial.checkpoints)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (first.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)) :=
  RetainedPaddedComparisonExecution.project_bind (Before := (ProductBefore first second finalBase productBase × Option (PackedPBSKeySwitchReconstruction.ReconstructionChild first.heights reconstructionBase)))
    (fun memory => KeySwitchPaddedReconstruction.stage (reconstructionBase memory) hs.encoding inputReference finalFamily finalNodes finalRadix) comparisonBase (fun previous : (ProductBefore first second finalBase productBase × Option (PackedPBSKeySwitchReconstruction.ReconstructionChild first.heights reconstructionBase)) => previous.2) (PackedPBSKeySwitchReconstruction.finalState first second finalBase productBase reconstructionBase)
    (erasePrior first second finalBase productBase reconstructionBase) Prod.snd (fun _ => rfl)
    hs.encoding dummy (fun _ => rfl)
    (PackedPBSKeySwitchReconstruction.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase finalRadix reconstructionBase initial)
    (PackedPBSKeySwitchReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase finalRadix reconstructionBase)
    (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape first.heights) initial)
    (PackedPBSKeySwitchReconstruction.project_witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase finalRadix reconstructionBase initial compatible restricted)

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- One charge covers all actually executed hash work through final comparison. -/

theorem final_bad_le_charge [Fintype Digest] (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^cells*(2^lanes) = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (firstSmall : (2*(2^lanes)-1)*2+1 ≤ q) (roundSmall : (2*(2^lanes)-1)*3+1 ≤ q)
    (zeroNodesEnough : 2*(2^lanes) ≤ (2*(2^lanes)-1)*2+1)
    (rotations : Fin rounds → Fin (2*(2^(cells+lanes)))) (zeroBase : Memory → ZeroScheme)
    (accLength : 2^accC*accB = 2^log) (inputReference : NativeGoldParameterStore.Reference)
    (inputLength : 2^inputC*inputB = 2^log) (inputSmall : 2*inputB ≤ q) (inputBase : Memory → InputScheme)
    (finalFamily : PackedPBSOriginalReferences.Family finalD) (finalNodes : 2*finalB ≤ q)
    (finalLength : 2^finalC*finalB = 2^log)
    (finalBase : Fin (finalD+1) → Memory → PaddedNTT.Scheme (ZMod q) Input Digest Cfg FinalResponse Memory FinalCommitMemory first.heights finalB finalC 1 finalB)
    [∀ index memory side, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((finalBase index memory).code side).front) finalB)]
    [∀ index memory side, SampleableType (Fin ((finalBase index memory).code side).queries → Fin (2^first.heights ((finalBase index memory).tag side)))]
    (productFirstSmall : (2*finalB-1)*2+1 ≤ q) (productRoundSmall : (2*finalB-1)*3+1 ≤ q)
    (productNodes : 2*finalB ≤ (2*finalB-1)*2+1)
    (productBase : Memory → KeySwitchPaddedProduct.Scheme (q := q) (d := finalD) (b := finalB) (n := finalC)
      (Input := Input) (Cfg := Cfg) (Response := ProductResponse) (Memory := Memory) (CommitMemory := ProductCommitMemory) (heights := first.heights))
    [∀ memory factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((productBase memory).code factor).front) finalB)]
    [∀ memory factor, SampleableType (Fin ((productBase memory).code factor).queries → Fin (2^first.heights ((productBase memory).tag factor)))]
    (finalRadix : ZMod q)
    (reconstructionBase : Memory → PaddedLinear.Scheme (ZMod q) Input Digest Cfg ReconstructionResponse Memory ReconstructionCommitMemory first.heights (2*finalD+2) finalB (1+finalC))
    [∀ memory factor, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((reconstructionBase memory).code factor).front) finalB)]
    [∀ memory factor, SampleableType (Fin ((reconstructionBase memory).code factor).queries → Fin (2^first.heights ((reconstructionBase memory).tag factor)))]
    (comparisonBase : (memory : Memory) → PackedPBSComparisonStage.Scheme Cfg Input Memory (FinalHelper memory) (FinalReturn memory) finalD)

    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (first.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)) :
    Pr{let outcome ← (PackedPBSKeySwitchReconstruction.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase finalRadix reconstructionBase (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height))) >>= (RetainedPaddedComparison.finish (Before := (ProductBefore first second finalBase productBase × Option (PackedPBSKeySwitchReconstruction.ReconstructionChild first.heights reconstructionBase))) (fun memory => KeySwitchPaddedReconstruction.stage (reconstructionBase memory) hs.encoding inputReference finalFamily finalNodes finalRadix) comparisonBase (fun previous : (ProductBefore first second finalBase productBase × Option (PackedPBSKeySwitchReconstruction.ReconstructionChild first.heights reconstructionBase)) => previous.2) (PackedPBSKeySwitchReconstruction.finalState first second finalBase productBase reconstructionBase) dummy)}[
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights)
        (RetainedPaddedComparison.finalState (fun memory => KeySwitchPaddedReconstruction.stage (reconstructionBase memory) hs.encoding inputReference finalFamily finalNodes finalRadix) comparisonBase (PackedPBSKeySwitchReconstruction.finalState first second finalBase productBase reconstructionBase) outcome)] ≤
      ExpectedHazard.charge
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (AmbientMatrixSource.Shape first.heights))
        (CheckpointCollision.loss unifSpec (AmbientMatrixSource.Shape first.heights))
        ((PackedPBSKeySwitchReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase finalRadix reconstructionBase) >>= RetainedPaddedComparisonExecution.program (fun memory => KeySwitchPaddedReconstruction.stage (reconstructionBase memory) hs.encoding inputReference finalFamily finalNodes finalRadix) comparisonBase Prod.snd) (CheckpointExecution.empty (AmbientMatrixSource.Shape first.heights)) := by
  have compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape first.heights)
      (CheckpointExecution.empty (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)).checkpoints := by
    intro tag saved member
    cases member
  have projected := PackedPBSKeySwitchReconstruction.project_witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase finalRadix reconstructionBase (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)) compatible restricted
  have emptyState : CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape first.heights)
      (CheckpointExecution.empty (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) =
      CheckpointExecution.empty (AmbientMatrixSource.Shape first.heights) := rfl
  rw [emptyState] at projected
  exact RetainedPaddedComparisonExecution.failure_from_empty (Before := (ProductBefore first second finalBase productBase × Option (PackedPBSKeySwitchReconstruction.ReconstructionChild first.heights reconstructionBase)))
    (fun memory => KeySwitchPaddedReconstruction.stage (reconstructionBase memory) hs.encoding inputReference finalFamily finalNodes finalRadix) comparisonBase (fun previous : (ProductBefore first second finalBase productBase × Option (PackedPBSKeySwitchReconstruction.ReconstructionChild first.heights reconstructionBase)) => previous.2) (PackedPBSKeySwitchReconstruction.finalState first second finalBase productBase reconstructionBase)
    (erasePrior first second finalBase productBase reconstructionBase) Prod.snd (fun _ => rfl)
    hs.encoding dummy (fun _ => rfl) (PackedPBSKeySwitchReconstruction.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase finalRadix reconstructionBase (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height))) (PackedPBSKeySwitchReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase productFirstSmall productRoundSmall productNodes productBase finalRadix reconstructionBase) projected

end
end FormalProof4FHE.HasteBoots.PackedPBSKeySwitchComparisonExecution
