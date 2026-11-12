module
public import FormalProof4FHE.HasteBoots.PackedPBSSecondComparisons
public import FormalProof4FHE.HasteBoots.AmbientAccumulator
public import FormalProof4FHE.HasteBoots.PackedPBSAccumulatorReferences
@[expose] public section

/-! The actual accepted second comparison gates the accumulator stage. All
seven original source roots and the entire ambient history are reused. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSAccumulator
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

/-- No replacement source is received: the root list borrows the four original
accumulator objects, original Hadamard result and both original inputs. -/
def accumulator (accumulators : Fin 4 → NativeGoldParameterStore.Reference)
    (factory : Memory → AccScheme) (memory : Memory) : AccScheme :=
  {factory memory with
    encoding := hs.encoding,
    commit := pure (PackedPBSAccumulatorReferences.roots family inputs accumulators,memory),
    initial := Prod.snd}

def eraseBefore (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d) (before : Decomposed first second) :=
  (PackedPBSSecondComparisons.eraseBefore first before.1,before.2.map (PackedPBSComparisonStage.erase (sharedScheme first.heights second)))

def beforeState (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d) (before : Decomposed first second) :=
  PackedPBSSecondComparisons.finalState first second before

/-- Every earlier rejection skips this call; entry uses the actual second
comparison opening loop's acceptance bit and final private memory. -/
def program (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme) := do
  let before ← PackedPBSSecondComparisons.program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase
  match before.2 with
  | none => pure (before,none)
  | some compared =>
    if compared.2.2.2.accepted then
      let child ← AmbientAccumulator.program (accumulator family inputs hs accumulators factory compared.2.2.2.memory)
      pure (before,some child)
    else pure (before,none)

def finish (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (before : Decomposed first second) : ProbComp (Decomposed first second × Option (AccChild first.heights)) := do
  match before.2 with
  | none => pure (before,none)
  | some compared =>
    if compared.2.2.1.2.accepted then
      let child ← AmbientAccumulator.witness first.heights
        (accumulator family inputs hs accumulators factory compared.2.2.1.2.memory) dummy compared.2.2.2
      pure (before,some child)
    else pure (before,none)

def witness (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) := do
  let before ← PackedPBSSecondComparisons.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial
  finish family inputs hs dummy first second accumulators factory before

def finalState (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (outcome : Decomposed first second × Option (AccChild first.heights)) :=
  match outcome.2 with
  | none => beforeState first second outcome.1
  | some child => child.2.2

/-- The complete second-comparison state, including both earlier halves, is
the precise predecessor of accumulator work. -/
theorem project_before (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
  (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
  (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) b front suffix m queries height)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
  (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
    (AmbientMatrixSource.Shape first.heights) initial.checkpoints)
  (restricted : CheckpointRecordScope.Scoped
    (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (first.heights tag))
    (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)) :
    (fun before => (eraseBefore first second before,beforeState first second before)) <$>
      PackedPBSSecondComparisons.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
      (AmbientMatrixSource.Shape first.heights))
      (PackedPBSSecondComparisons.program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase)).run
      (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape first.heights) initial) :=
  PackedPBSSecondComparisons.project_witness length psi primitive family inputs base hs nodesEnough radix linearBase
    dummy first second secondBase initial compatible restricted

/-- Full-state erasure follows the actual accepted second-comparison return;
no handler reset, replacement memory or supplied entry flag is introduced. -/
theorem project_witness (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
  (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
  (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) b front suffix m queries height)
  (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
  (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
    (AmbientMatrixSource.Shape first.heights) initial.checkpoints)
  (restricted : CheckpointRecordScope.Scoped
    (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (first.heights tag))
    (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)) :
    (fun outcome => ((eraseBefore first second outcome.1,outcome.2.map (fun child => (child.1.1,child.2.1))),finalState first second outcome)) <$>
      witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
      (AmbientMatrixSource.Shape first.heights))
      (program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory)).run
      (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape first.heights) initial) := by
  simp only [program,simulateQ_bind,StateT.run_bind]
  rw [←project_before length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial compatible restricted]
  simp only [witness,map_bind,bind_map_left]
  congr 1
  funext before
  cases equal : before.2 with
  | none => simp [finish,eraseBefore,finalState,equal,map_pure,simulateQ_pure,StateT.run_pure]
  | some compared =>
    simp only [eraseBefore,equal,Option.map_some,PackedPBSComparisonStage.erase]
    by_cases passed : compared.2.2.1.2.accepted = true
    · simp only [finish,equal,passed,ite_true,map_bind,map_pure,simulateQ_bind,StateT.run_bind,
        simulateQ_pure,StateT.run_pure,Option.map_some,finalState]
      let childScheme := accumulator family inputs hs accumulators factory compared.2.2.1.2.memory
      have projected := AmbientAccumulator.project_witness first.heights childScheme dummy compared.2.2.2
      have encoding : childScheme.encoding = hs.encoding := rfl
      rw [encoding] at projected
      simp only [beforeState,PackedPBSSecondComparisons.finalState,equal]
      rw [←projected]
      simp only [bind_map_left]
      rfl
    · simp [finish,equal,passed,finalState,PackedPBSComparisonStage.erase,map_pure,simulateQ_pure,StateT.run_pure]

/-- Reached accumulator calls derive the exact predecessor support, computed
comparison acceptance, private memory and inherited monitor state. -/
theorem reached_accumulator (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
  (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
  (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) b front suffix m queries height)
  (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) (before : Decomposed first second) (child : AccChild first.heights)
    (supported : (before,some child) ∈ support
      (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial)) :
    ∃ compared, before.2 = some compared ∧ compared.2.2.1.2.accepted = true ∧
      before ∈ support (PackedPBSSecondComparisons.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial) ∧
      child ∈ support (AmbientAccumulator.witness first.heights
        (accumulator family inputs hs accumulators factory compared.2.2.1.2.memory) dummy compared.2.2.2) := by
  simp only [witness,support_bind,Set.mem_iUnion] at supported
  obtain ⟨selected,selectedSupported,remainder⟩ := supported
  cases equal : selected.2 with
  | none => simp [finish,equal] at remainder
  | some compared =>
    by_cases passed : compared.2.2.1.2.accepted = true
    · simp only [finish,equal,passed,ite_true,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at remainder
      obtain ⟨actual,actualSupported,same⟩ := remainder
      have sameBefore : before = selected := congrArg Prod.fst same
      have sameChild : child = actual := Option.some.inj (congrArg Prod.snd same)
      subst selected
      subst actual
      exact ⟨compared,equal,passed,selectedSupported,actualSupported⟩
    · simp [finish,equal,passed] at remainder

/-- All seven borrowed roots are fixed on reached paths, even if later
arithmetic or authentication work rejects. -/
theorem roots (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
  (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
  (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) b front suffix m queries height)
  (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) (before : Decomposed first second) (child : AccChild first.heights)
    (supported : (before,some child) ∈ support
      (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial)) :
    child.1.1.1 = PackedPBSAccumulatorReferences.roots family inputs accumulators := by
  obtain ⟨compared,_,_,_,present⟩ := reached_accumulator length psi primitive family inputs base hs nodesEnough radix linearBase
    dummy first second secondBase accumulators factory initial before child supported
  simp only [AmbientAccumulator.witness,MultiCommitmentPrefix.witness,accumulator,simulateQ_pure,StateT.run_pure,
    pure_bind,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at present
  obtain ⟨last,_,same⟩ := present
  exact congrArg (fun outcome => outcome.1.1.1) same

/-- The inherited complete prefix is audited in its one ambient geometry. -/
theorem before_audited (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
  (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
  (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) b front suffix m queries height)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
  (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
    (AmbientMatrixSource.Shape first.heights) initial.checkpoints)
  (restricted : CheckpointRecordScope.Scoped
    (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (first.heights tag))
    (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase))
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial)
    (before : Decomposed first second)
    (supported : before ∈ support
      (PackedPBSSecondComparisons.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial)) :
    CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) (beforeState first second before) :=
  PackedPBSSecondComparisons.audited_witness length psi primitive family inputs base hs nodesEnough radix linearBase
    dummy first second secondBase initial audited compatible restricted before supported

/-- Earlier source/helper owners remain recorded through every reached call. -/
theorem retains (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
  (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
  (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) b front suffix m queries height)
  (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (before : Decomposed first second) (child : AccChild first.heights)
    (supported : (before,some child) ∈ support
      (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial))
    (tag : Cfg) (saved : AmbientMatrixSource.Snapshot Input Digest first.heights tag)
    (recorded : ⟨tag,saved⟩ ∈ (beforeState first second before).checkpoints.checkpoints) :
    ⟨tag,saved⟩ ∈ child.2.2.checkpoints.checkpoints := by
  obtain ⟨compared,equal,_,_,present⟩ := reached_accumulator length psi primitive family inputs base hs nodesEnough radix linearBase
    dummy first second secondBase accumulators factory initial before child supported
  have incoming : ⟨tag,saved⟩ ∈ compared.2.2.2.checkpoints.checkpoints := by
    simpa only [beforeState,PackedPBSSecondComparisons.finalState,equal] using recorded
  exact AmbientAccumulator.retains first.heights
    (accumulator family inputs hs accumulators factory compared.2.2.1.2.memory) dummy compared.2.2.2 child present tag saved incoming

/-- No branch can clear an inherited failure, including skipped/rejected calls. -/
theorem bad_persistent (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
  (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
  (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) b front suffix m queries height)
  (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (outcome : Decomposed first second × Option (AccChild first.heights))
    (supported : outcome ∈ support
      (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial))
    (bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (beforeState first second outcome.1)) :
    CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState first second outcome) := by
  rcases outcome with ⟨before,child⟩
  cases child with
  | none => exact bad
  | some child =>
    obtain ⟨compared,equal,_,_,present⟩ := reached_accumulator length psi primitive family inputs base hs nodesEnough radix linearBase
      dummy first second secondBase accumulators factory initial before child supported
    have incoming : CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) compared.2.2.2 := by
      simpa only [beforeState,PackedPBSSecondComparisons.finalState,equal] using bad
    exact AmbientAccumulator.bad_persistent first.heights
      (accumulator family inputs hs accumulators factory compared.2.2.1.2.memory) dummy compared.2.2.2 incoming child present

/-- The extended execution inherits its audit from actual full-state projection. -/
theorem audited_witness (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
  (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
  (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) b front suffix m queries height)
  (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
  (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
    (AmbientMatrixSource.Shape first.heights) initial.checkpoints)
  (restricted : CheckpointRecordScope.Scoped
    (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (first.heights tag))
    (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase))
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial)
    (outcome : Decomposed first second × Option (AccChild first.heights))
    (supported : outcome ∈ support
      (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial)) :
    CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) (finalState first second outcome) := by
  have actual : ((eraseBefore first second outcome.1,outcome.2.map (fun child => (child.1.1,child.2.1))),finalState first second outcome) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
        (AmbientMatrixSource.Shape first.heights))
        (program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory)).run
        (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape first.heights) initial)) := by
    rw [←project_witness length psi primitive family inputs base hs nodesEnough radix linearBase
      dummy first second secondBase accumulators factory initial compatible restricted,support_map]
    exact Set.mem_image_of_mem _ supported
  have incoming := CheckpointShapeTransport.audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
    (AmbientMatrixSource.Shape first.heights) initial compatible audited
  exact CheckpointExecution.audited_run (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy _ _ _ incoming _ actual

/-- All work through the accumulator, including rejected paths, contributes to
one final availability/collision charge on this exact extended program. -/
theorem final_bad_le_charge [Fintype Digest] (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
  (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
  (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
    (2*d+2) b front suffix m queries height)
  (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
  (restricted : CheckpointRecordScope.Scoped
    (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (first.heights tag))
    (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)) :
    Pr{let outcome ← (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState first second outcome)] ≤
    ExpectedHazard.charge (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
      (AmbientMatrixSource.Shape first.heights))
      (CheckpointCollision.loss unifSpec (AmbientMatrixSource.Shape first.heights))
      (program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory)
      (CheckpointExecution.empty (AmbientMatrixSource.Shape first.heights)) := by
  have emptyCompatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape first.heights)
      (CheckpointExecution.empty (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)).checkpoints := by
    intro tag saved member
    cases member
  have projected := project_witness length psi primitive family inputs base hs nodesEnough radix linearBase
    dummy first second secondBase accumulators factory (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)) emptyCompatible restricted
  have emptyState : CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape first.heights)
      (CheckpointExecution.empty (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) =
      CheckpointExecution.empty (AmbientMatrixSource.Shape first.heights) := rfl
  rw [emptyState] at projected
  have bound := CheckpointCollision.failure_from_empty_le_charge (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
    (AmbientMatrixSource.Shape first.heights) (program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory)
  rw [←projected,prEvent_map] at bound
  exact bound

end
end FormalProof4FHE.HasteBoots.PackedPBSAccumulator
