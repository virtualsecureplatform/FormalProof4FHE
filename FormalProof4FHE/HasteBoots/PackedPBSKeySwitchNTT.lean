module
public import FormalProof4FHE.HasteBoots.PackedPBSKeySwitchInput
public import FormalProof4FHE.HasteBoots.KeySwitchPaddedNTT
@[expose] public section

/-! The final ordered d+1 NTT calls follow the actual accepted key-switch
known-input opening, with its returned memory and full mixed-height history. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSKeySwitchNTT
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

local notation "Return" => ComparisonReturn (Selection := Selection) (Root := Root) (Data := Data) (Memory := Memory)

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

def eraseBefore (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d) (before : InputBefore first second) :=
  (PackedPBSKeySwitchInput.eraseBefore first second before.1,before.2.map (fun input => (input.1.1,input.2.1)))

def beforeState (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d) (before : InputBefore first second) :=
  PackedPBSKeySwitchInput.finalState first second before

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
    [∀ index memory side, SampleableType (Fin ((finalBase index memory).code side).queries → Fin (2^first.heights ((finalBase index memory).tag side)))] := do
  let before ← PackedPBSKeySwitchInput.program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase
  match before.2 with
  | none => pure (before,none)
  | some input =>
    if input.2.2.accepted then
      let ntts ← KeySwitchPaddedNTT.program finalBase hs.encoding finalFamily finalNodes finalLength psi primitive input.2.2.memory
      pure (before,some ntts)
    else pure (before,none)

def finish (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (finalFamily : PackedPBSOriginalReferences.Family finalD) (finalNodes : 2*finalB ≤ q)
    (finalLength : 2^finalC*finalB = 2^log)
    (finalBase : Fin (finalD+1) → Memory → PaddedNTT.Scheme (ZMod q) Input Digest Cfg FinalResponse Memory FinalCommitMemory first.heights finalB finalC 1 finalB)
    [∀ index memory side, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((finalBase index memory).code side).front) finalB)]
    [∀ index memory side, SampleableType (Fin ((finalBase index memory).code side).queries → Fin (2^first.heights ((finalBase index memory).tag side)))]
    (before : InputBefore first second) : ProbComp (InputBefore first second × Option (PaddedNTTSequence.Trace (KeySwitchPaddedNTT.factory finalBase hs.encoding finalFamily finalNodes finalLength psi primitive) × CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))) := do
  match before.2 with
  | none => pure (before,none)
  | some input =>
    if input.2.1.2.accepted then
      let ntts ← KeySwitchPaddedNTT.witness finalBase hs.encoding finalFamily finalNodes finalLength psi primitive dummy input.2.1.2.memory input.2.2
      pure (before,some ntts)
    else pure (before,none)

def witness (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
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
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) := do
  let before ← PackedPBSKeySwitchInput.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase initial
  finish psi primitive hs dummy first second finalFamily finalNodes finalLength finalBase before

def finalState (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (finalFamily : PackedPBSOriginalReferences.Family finalD) (finalNodes : 2*finalB ≤ q)
    (finalLength : 2^finalC*finalB = 2^log)
    (finalBase : Fin (finalD+1) → Memory → PaddedNTT.Scheme (ZMod q) Input Digest Cfg FinalResponse Memory FinalCommitMemory first.heights finalB finalC 1 finalB)
    [∀ index memory side, SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^((finalBase index memory).code side).front) finalB)]
    [∀ index memory side, SampleableType (Fin ((finalBase index memory).code side).queries → Fin (2^first.heights ((finalBase index memory).tag side)))]
    (outcome : InputBefore first second × Option (PaddedNTTSequence.Trace (KeySwitchPaddedNTT.factory finalBase hs.encoding finalFamily finalNodes finalLength psi primitive) × CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))) :=
  match outcome.2 with
  | none => beforeState first second outcome.1
  | some ntts => ntts.2

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- Projection retains all prior PBS work and the actual input-opening gate,
then erases only NTT analysis data while retaining returned memory and state. -/
theorem project_witness (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
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
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape first.heights) initial.checkpoints)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (first.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)) :
    (fun outcome => ((eraseBefore first second outcome.1,outcome.2.map (fun ntts => PaddedNTTSequence.erase (KeySwitchPaddedNTT.factory finalBase hs.encoding finalFamily finalNodes finalLength psi primitive) ntts.1)),
      finalState psi primitive hs first second finalFamily finalNodes finalLength finalBase outcome)) <$>
      witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase initial =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (AmbientMatrixSource.Shape first.heights))
      (program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase)).run
      (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape first.heights) initial) := by
  simp only [program,simulateQ_bind,StateT.run_bind]
  rw [←PackedPBSKeySwitchInput.project_witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase initial compatible restricted]
  simp only [witness,map_bind,bind_map_left]
  congr 1
  funext before
  cases inputState : before.2 with
  | none => simp [finish,eraseBefore,finalState,beforeState,inputState,map_pure,simulateQ_pure,StateT.run_pure]
  | some input =>
    simp only [eraseBefore,Option.map_some]
    by_cases passed : input.2.1.2.accepted = true
    · simp only [finish,inputState,passed,ite_true,map_bind,map_pure,simulateQ_bind,StateT.run_bind,
        simulateQ_pure,StateT.run_pure,Option.map_some,finalState]
      have projected := KeySwitchPaddedNTT.project_witness finalBase hs.encoding finalFamily finalNodes finalLength psi primitive dummy input.2.1.2.memory input.2.2
      simp only [PackedPBSKeySwitchInput.finalState,inputState]
      rw [←projected]
      simp only [bind_map_left]
    · simp [finish,inputState,passed,finalState,beforeState,map_pure,simulateQ_pure,StateT.run_pure]

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- Reaching the loop derives input presence and actual acceptance, prior
support, and the exact returned-memory/shared-state handoff. -/
theorem reached_ntt (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
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
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) (before : InputBefore first second) (ntts : PaddedNTTSequence.Trace (KeySwitchPaddedNTT.factory finalBase hs.encoding finalFamily finalNodes finalLength psi primitive) × CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights))
    (supported : (before,some ntts) ∈ support (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase initial)) :
    ∃ input, before.2 = some input ∧ input.2.1.2.accepted = true ∧
      before ∈ support (PackedPBSKeySwitchInput.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase initial) ∧
      ntts ∈ support (KeySwitchPaddedNTT.witness finalBase hs.encoding finalFamily finalNodes finalLength psi primitive dummy input.2.1.2.memory input.2.2) := by
  simp only [witness,support_bind,Set.mem_iUnion] at supported
  obtain ⟨selected,selectedSupported,remainder⟩ := supported
  cases inputState : selected.2 with
  | none => simp [finish,inputState] at remainder
  | some input =>
    by_cases passed : input.2.1.2.accepted = true
    · simp only [finish,inputState,passed,ite_true,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at remainder
      obtain ⟨actual,actualSupported,same⟩ := remainder
      have sameBefore : before = selected := congrArg Prod.fst same
      have sameNTT : ntts = actual := Option.some.inj (congrArg Prod.snd same)
      subst selected
      subst actual
      exact ⟨input,inputState,passed,selectedSupported,actualSupported⟩
    · simp [finish,inputState,passed] at remainder

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- Every result retains a supported actual predecessor, including skips. -/
theorem before_supported (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
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
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) (outcome : InputBefore first second × Option (PaddedNTTSequence.Trace (KeySwitchPaddedNTT.factory finalBase hs.encoding finalFamily finalNodes finalLength psi primitive) × CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights)))
    (supported : outcome ∈ support (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase initial)) :
    outcome.1 ∈ support (PackedPBSKeySwitchInput.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase initial) := by
  simp only [witness,support_bind,Set.mem_iUnion] at supported
  obtain ⟨selected,selectedSupported,remainder⟩ := supported
  cases inputState : selected.2 with
  | none =>
    simp only [finish,inputState,support_pure,Set.mem_singleton_iff] at remainder
    have sameBefore : outcome.1 = selected := congrArg Prod.fst remainder
    rw [sameBefore]
    exact selectedSupported
  | some input =>
    by_cases passed : input.2.1.2.accepted = true
    · simp only [finish,inputState,passed,ite_true,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at remainder
      obtain ⟨actual,_,same⟩ := remainder
      have sameBefore : outcome.1 = selected := congrArg Prod.fst same
      rw [sameBefore]
      exact selectedSupported
    · have rejected : input.2.1.2.accepted = false := Bool.eq_false_iff.mpr passed
      simp only [finish,inputState,rejected,Bool.false_eq_true,ite_false,support_pure,Set.mem_singleton_iff] at remainder
      have sameBefore : outcome.1 = selected := congrArg Prod.fst remainder
      rw [sameBefore]
      exact selectedSupported

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- All preceding source owners survive the new calls and rejected paths. -/
theorem retains (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
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
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) (outcome : InputBefore first second × Option (PaddedNTTSequence.Trace (KeySwitchPaddedNTT.factory finalBase hs.encoding finalFamily finalNodes finalLength psi primitive) × CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights)))
    (supported : outcome ∈ support (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase initial))
    (tag : Cfg) (saved : AmbientMatrixSource.Snapshot Input Digest first.heights tag)
    (recorded : ⟨tag,saved⟩ ∈ (beforeState first second outcome.1).checkpoints.checkpoints) :
    ⟨tag,saved⟩ ∈ (finalState psi primitive hs first second finalFamily finalNodes finalLength finalBase outcome).checkpoints.checkpoints := by
  cases equal : outcome.2 with
  | none => simpa only [finalState,equal] using recorded
  | some ntts =>
    have present : (outcome.1,some ntts) ∈ support (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase initial) := by simpa only [←equal] using supported
    obtain ⟨input,inputState,_,_,childSupported⟩ := reached_ntt length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase initial outcome.1 ntts present
    have incoming : ⟨tag,saved⟩ ∈ input.2.2.checkpoints.checkpoints := by
      simpa only [beforeState,PackedPBSKeySwitchInput.finalState,inputState] using recorded
    simpa only [finalState,equal] using PaddedNTTSequence.retains (KeySwitchPaddedNTT.factory finalBase hs.encoding finalFamily finalNodes finalLength psi primitive) hs.encoding dummy (List.finRange (finalD+1))
      input.2.1.2.memory input.2.2 ntts childSupported tag saved incoming

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- Earlier exceptions persist through every actual loop path. -/
theorem bad_persistent (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
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
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) (outcome : InputBefore first second × Option (PaddedNTTSequence.Trace (KeySwitchPaddedNTT.factory finalBase hs.encoding finalFamily finalNodes finalLength psi primitive) × CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights)))
    (supported : outcome ∈ support (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase initial))
    (bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (beforeState first second outcome.1)) :
    CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState psi primitive hs first second finalFamily finalNodes finalLength finalBase outcome) := by
  cases equal : outcome.2 with
  | none => simpa only [finalState,equal] using bad
  | some ntts =>
    have present : (outcome.1,some ntts) ∈ support (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase initial) := by simpa only [←equal] using supported
    obtain ⟨input,inputState,_,_,childSupported⟩ := reached_ntt length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase initial outcome.1 ntts present
    have incoming : CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) input.2.2 := by
      simpa only [beforeState,PackedPBSKeySwitchInput.finalState,inputState] using bad
    simpa only [finalState,equal] using PaddedNTTSequence.bad_persistent (KeySwitchPaddedNTT.factory finalBase hs.encoding finalFamily finalNodes finalLength psi primitive) hs.encoding dummy (List.finRange (finalD+1))
      input.2.1.2.memory input.2.2 ntts childSupported incoming

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- Full-state projection derives audits on all accepted/rejected branches. -/
theorem audited_witness (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
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
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape first.heights) initial.checkpoints)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (first.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase))
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial)
    (outcome : InputBefore first second × Option (PaddedNTTSequence.Trace (KeySwitchPaddedNTT.factory finalBase hs.encoding finalFamily finalNodes finalLength psi primitive) × CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights)))
    (supported : outcome ∈ support (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase initial)) :
    CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) (finalState psi primitive hs first second finalFamily finalNodes finalLength finalBase outcome) := by
  have actual : ((eraseBefore first second outcome.1,outcome.2.map (fun ntts => PaddedNTTSequence.erase (KeySwitchPaddedNTT.factory finalBase hs.encoding finalFamily finalNodes finalLength psi primitive) ntts.1)),finalState psi primitive hs first second finalFamily finalNodes finalLength finalBase outcome) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (AmbientMatrixSource.Shape first.heights))
        (program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase)).run
        (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape first.heights) initial)) := by
    rw [←project_witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase initial compatible restricted,support_map]
    exact Set.mem_image_of_mem _ supported
  have incoming := CheckpointShapeTransport.audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
    (AmbientMatrixSource.Shape first.heights) initial compatible audited
  exact CheckpointExecution.audited_run (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy _ _ _ incoming _ actual

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- One charge covers the entire extended prefix, including earlier rejects
and all actually reached final key-switch NTT work. -/
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
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (first.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)) :
    Pr{let outcome ← (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState psi primitive hs first second finalFamily finalNodes finalLength finalBase outcome)] ≤
    ExpectedHazard.charge (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (AmbientMatrixSource.Shape first.heights))
      (CheckpointCollision.loss unifSpec (AmbientMatrixSource.Shape first.heights))
      (program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase)
      (CheckpointExecution.empty (AmbientMatrixSource.Shape first.heights)) := by
  have compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape first.heights)
      (CheckpointExecution.empty (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)).checkpoints := by
    intro tag saved member
    cases member
  have projected := project_witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)) compatible restricted
  have emptyState : CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape first.heights)
      (CheckpointExecution.empty (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) =
      CheckpointExecution.empty (AmbientMatrixSource.Shape first.heights) := rfl
  rw [emptyState] at projected
  have bound := CheckpointCollision.failure_from_empty_le_charge (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
    (AmbientMatrixSource.Shape first.heights) (program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase)
  rw [←projected,prEvent_map] at bound
  exact bound

end
end FormalProof4FHE.HasteBoots.PackedPBSKeySwitchNTT
