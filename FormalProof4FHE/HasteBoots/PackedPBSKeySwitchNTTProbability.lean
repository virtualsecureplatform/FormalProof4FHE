module
public import FormalProof4FHE.HasteBoots.PackedPBSKeySwitchNTT
public import FormalProof4FHE.HasteBoots.PackedPBSComparisonJointBound
@[expose] public section

/-! The final ordered d+1 NTT calls follow the actual accepted key-switch
known-input opening, with its returned memory and full mixed-height history. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSKeySwitchNTTProbability
open PackedPBSKeySwitchNTT (beforeState finalState)
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

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- Earlier events cannot gain probability through the actual NTT
continuation, regardless of its success or actual worker interleavings. -/
theorem earlier_event_le (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
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
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) (event : InputBefore first second → Prop) :
    Pr{let outcome ← (PackedPBSKeySwitchNTT.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase initial)}[event outcome.1] ≤
    Pr{let before ← (PackedPBSKeySwitchInput.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase initial)}[event before] := by
  unfold PackedPBSKeySwitchNTT.witness
  apply prEvent_bind_le_prEvent_of_forall_eq_zero _ _ event _
  intro before outside
  cases inputState : before.2 with
  | none => simp [PackedPBSKeySwitchNTT.finish,inputState,prEvent_norm,outside]
  | some input =>
    by_cases passed : input.2.1.2.accepted = true
    · simp only [PackedPBSKeySwitchNTT.finish,inputState,passed,ite_true,prEvent_norm]
      exact prEvent_eq_zero_of_forall_not _ _ (fun _ accepted => outside accepted)
    · have rejected : input.2.1.2.accepted = false := Bool.eq_false_iff.mpr passed
      simp [PackedPBSKeySwitchNTT.finish,inputState,rejected,prEvent_norm,outside]


omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- Earlier safe events transfer to the extended final bad event without
paying an additional authentication charge or assuming losslessness. -/
theorem earlier_safe_event_le (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
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
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) (event : InputBefore first second → Prop) :
    Pr{let outcome ← (PackedPBSKeySwitchNTT.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase initial)}[
      event outcome.1 ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState psi primitive hs first second finalFamily finalNodes finalLength finalBase outcome)] ≤
    Pr{let before ← (PackedPBSKeySwitchInput.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase initial)}[
      event before ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (beforeState first second before)] := by
  have included := prEvent_mono_of_support (PackedPBSKeySwitchNTT.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase initial)
    (fun outcome => event outcome.1 ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState psi primitive hs first second finalFamily finalNodes finalLength finalBase outcome))
    (fun outcome => event outcome.1 ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (beforeState first second outcome.1))
    (by
      intro outcome supported accepted
      refine ⟨accepted.1,?_⟩
      intro bad
      exact accepted.2 (PackedPBSKeySwitchNTT.bad_persistent length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase initial outcome supported bad))
  exact included.trans (earlier_event_le length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase initial
    (fun before => event before ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (beforeState first second before)))

omit [SampleableType (ZMod q)] [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- Abstract composition on the exact extended program. Native callers below
discharge both bound premises with derived stage theorems. -/
theorem safe_joint_bound (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
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
    (earlier : InputBefore first second → Prop)
    (inputRisk : InputBefore first second × Option (PaddedNTTSequence.Trace (KeySwitchPaddedNTT.factory finalBase hs.encoding finalFamily finalNodes finalLength psi primitive) × CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape first.heights)) → Prop)
    (earlierRate inputRate : ENNReal)
    (earlierBound : Pr{let before ← (PackedPBSKeySwitchInput.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase initial)}[
      earlier before ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (beforeState first second before)] ≤ earlierRate)
    (inputBound : Pr{let outcome ← (PackedPBSKeySwitchNTT.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase initial)}[
      inputRisk outcome ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState psi primitive hs first second finalFamily finalNodes finalLength finalBase outcome)] ≤ inputRate) :
    Pr{let outcome ← (PackedPBSKeySwitchNTT.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase initial)}[
      (earlier outcome.1 ∨ inputRisk outcome) ∧ ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState psi primitive hs first second finalFamily finalNodes finalLength finalBase outcome)] ≤ earlierRate + inputRate := by
  have previous := (earlier_safe_event_le length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase initial earlier).trans earlierBound
  exact PackedPBSComparisonJointBound.safe_union _ _ _ _ _ _ previous inputBound

variable {FinalP : Type} [Field FinalP] [Algebra (ZMod q) FinalP] [Fintype FinalP] [DecidableEq FinalP]
  [SampleableType (Fin 1 → ZMod q)]

omit [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- The final NTT sum is derived over the actual reached, audited input
returns. No replay, reset, child security bound or local hash charge is assumed. -/
theorem safe_original_ntt_bound (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
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
    [NeZero finalB] [∀ index memory side, NeZero ((finalBase index memory).code side).m]
    [∀ index memory side, SampleableType ((Fin (2^((finalBase index memory).code side).front) × Fin finalB) → FinalP)]
    (finalBasis : Module.Basis (Fin finalB) (ZMod q) FinalP)
    (finalEnough : ∀ index memory side, ((finalBase index memory).code side).m ≤
      Fintype.card (Fin (2^first.heights ((finalBase index memory).tag side))))
    (finalCapacity : ∀ index memory side, 2^((finalBase index memory).code side).suffix ≤ ((finalBase index memory).code side).m*finalB)
    (finalRadius : Fin (finalD+1) → Memory → Bool → ℕ) (finalEpsilon : Fin (finalD+1) → ENNReal)
    (finalSmall : ∀ index memory side, (finalRadius index memory side : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := FinalP) ((finalBase index memory).domain side))
        ((finalBase index memory).code side).m : Set (Fin (2^first.heights ((finalBase index memory).tag side)) → FinalP)) : ℚ≥0)/3)
    (finalCalibrated : ∀ index memory,
      ((((1 : ENNReal)/Fintype.card (ZMod q))^finalB) + (finalC : ENNReal)*(((((2*finalB-1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^finalB))) +
      (JointMatrixOpening.error (K := FinalP) (m := ((finalBase index memory).code false).m) (b := finalB)
          (queries := ((finalBase index memory).code false).queries) ((finalBase index memory).domain false) (finalRadius index memory false) +
        JointMatrixOpening.error (K := FinalP) (m := ((finalBase index memory).code true).m) (b := finalB)
          (queries := ((finalBase index memory).code true).queries) ((finalBase index memory).domain true) (finalRadius index memory true)) ≤ finalEpsilon index)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape first.heights) initial.checkpoints)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (first.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase))
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial) :
    Pr{let outcome ← (PackedPBSKeySwitchNTT.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase initial)}[
      ∃ ntts, outcome.2 = some ntts ∧
        PaddedNTTSequenceSoundness.AnyOriginalRisk (KeySwitchPaddedNTT.factory finalBase hs.encoding finalFamily finalNodes finalLength psi primitive) hs.encoding dummy finalCapacity finalRadius ntts.1 ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) ntts.2] ≤ ((List.finRange (finalD+1)).map finalEpsilon).sum := by
  classical
  unfold PackedPBSKeySwitchNTT.witness
  apply prEvent_bind_le_of_forall_le_of_support
  intro before supported
  have incoming := PackedPBSKeySwitchInput.audited_witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase initial compatible restricted audited before supported
  cases inputState : before.2 with
  | none => simp [PackedPBSKeySwitchNTT.finish,inputState,prEvent_norm]
  | some input =>
    by_cases passed : input.2.1.2.accepted = true
    · have stateAudit : CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) input.2.2 := by
        simpa only [PackedPBSKeySwitchInput.finalState,inputState] using incoming
      have conditional := KeySwitchPaddedNTT.original_safe_bound finalBase hs.encoding finalFamily finalNodes finalLength psi primitive
        dummy input.2.1.2.memory input.2.2 finalBasis finalEnough finalCapacity finalRadius finalEpsilon finalSmall finalCalibrated stateAudit
      simp only [PackedPBSKeySwitchNTT.finish,inputState,passed,ite_true,prEvent_norm]
      convert conditional using 1
      apply prEvent_congr
      intro ntts
      simp only [Option.some.injEq,exists_eq_left']
    · have rejected : input.2.1.2.accepted = false := Bool.eq_false_iff.mpr passed
      simp only [PackedPBSKeySwitchNTT.finish,inputState,rejected,Bool.false_eq_true,ite_false]
      refine (prEvent_eq_zero_of_forall_mem_support _ _ ?_).le.trans (bot_le : (0 : ENNReal) ≤ ((List.finRange (finalD+1)).map finalEpsilon).sum)
      intro actual actualSupported event
      have same := eq_of_mem_support_pure (before,none) actualSupported
      subst actual
      rcases event with ⟨_,present,_⟩
      cases present

omit [SampleableType (Fin (cells+rows) → ZMod q)]
  [SampleableType (Fin (2^lanes) → ((Fin (2^lanes) → ZMod q) × ZMod q))] in
/-- The final NTT sum is derived over the actual reached, audited input
returns. No replay, reset, child security bound or local hash charge is assumed. -/
theorem safe_original_ntt_final_bound (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
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
    [NeZero finalB] [∀ index memory side, NeZero ((finalBase index memory).code side).m]
    [∀ index memory side, SampleableType ((Fin (2^((finalBase index memory).code side).front) × Fin finalB) → FinalP)]
    (finalBasis : Module.Basis (Fin finalB) (ZMod q) FinalP)
    (finalEnough : ∀ index memory side, ((finalBase index memory).code side).m ≤
      Fintype.card (Fin (2^first.heights ((finalBase index memory).tag side))))
    (finalCapacity : ∀ index memory side, 2^((finalBase index memory).code side).suffix ≤ ((finalBase index memory).code side).m*finalB)
    (finalRadius : Fin (finalD+1) → Memory → Bool → ℕ) (finalEpsilon : Fin (finalD+1) → ENNReal)
    (finalSmall : ∀ index memory side, (finalRadius index memory side : ℚ≥0) <
      (Code.minDist (ReedSolomon.code (SymbolLift.liftedDomain (K := FinalP) ((finalBase index memory).domain side))
        ((finalBase index memory).code side).m : Set (Fin (2^first.heights ((finalBase index memory).tag side)) → FinalP)) : ℚ≥0)/3)
    (finalCalibrated : ∀ index memory,
      ((((1 : ENNReal)/Fintype.card (ZMod q))^finalB) + (finalC : ENNReal)*(((((2*finalB-1 : ℕ) : ENNReal)/Fintype.card (ZMod q))^finalB))) +
      (JointMatrixOpening.error (K := FinalP) (m := ((finalBase index memory).code false).m) (b := finalB)
          (queries := ((finalBase index memory).code false).queries) ((finalBase index memory).domain false) (finalRadius index memory false) +
        JointMatrixOpening.error (K := FinalP) (m := ((finalBase index memory).code true).m) (b := finalB)
          (queries := ((finalBase index memory).code true).queries) ((finalBase index memory).domain true) (finalRadius index memory true)) ≤ finalEpsilon index)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape first.heights) initial.checkpoints)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (first.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase))
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial) :
    Pr{let outcome ← (PackedPBSKeySwitchNTT.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase initial)}[
      (∃ ntts, outcome.2 = some ntts ∧
        PaddedNTTSequenceSoundness.AnyOriginalRisk (KeySwitchPaddedNTT.factory finalBase hs.encoding finalFamily finalNodes finalLength psi primitive) hs.encoding dummy finalCapacity finalRadius ntts.1) ∧
        ¬CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState psi primitive hs first second finalFamily finalNodes finalLength finalBase outcome)] ≤ ((List.finRange (finalD+1)).map finalEpsilon).sum := by
  have bound := safe_original_ntt_bound length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase firstSmall roundSmall zeroNodesEnough rotations zeroBase accLength inputReference inputLength inputSmall inputBase finalFamily finalNodes finalLength finalBase finalBasis finalEnough finalCapacity finalRadius finalEpsilon finalSmall finalCalibrated initial compatible restricted audited
  apply le_trans (prEvent_mono_of_support _ _ _ ?_) bound
  intro outcome supported event
  obtain ⟨⟨ntts,present,risk⟩,clear⟩ := event
  refine ⟨ntts,present,risk,?_⟩
  simpa only [finalState,present] using clear

end
end FormalProof4FHE.HasteBoots.PackedPBSKeySwitchNTTProbability
