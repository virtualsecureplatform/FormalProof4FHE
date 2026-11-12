module
public import FormalProof4FHE.HasteBoots.PackedPBSAccumulator
public import FormalProof4FHE.HasteBoots.AmbientMonomialNTT
public import FormalProof4FHE.HasteBoots.PackedPBSMonomialReferences
@[expose] public section

/-! The two original-source monomial NTT calls follow actual accumulator
acceptance and retain the entire mixed-height PBS execution history. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSMonomialNTT
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

variable {MonoResponse MonoCommitMemory : Type} {monoB monoC monoR monoK monoFront monoSuffix monoM monoQueries monoHeight : ℕ}
  [SampleableType (Fin monoK → Fin monoR → ZMod q)] [SampleableType (Fin monoB → ZMod q)]
  [SampleableType (InteractiveAuthenticatedOpening.TestMatrix (ZMod q) (2^monoFront) monoB)]
  [SampleableType (Fin monoQueries → Fin (2^monoHeight))]

local notation "MonoScheme" => AuthenticatedNTT.Scheme (ZMod q) Input Digest Cfg MonoResponse Memory MonoCommitMemory
  monoB monoC monoR monoK monoFront monoSuffix monoM monoQueries monoHeight

abbrev MonomialOutcome (heights : Cfg → ℕ) :=
  AmbientMonomialNTT.Trace heights (F := ZMod q) (Input := Input) (Digest := Digest) (Cfg := Cfg)
    (Response := MonoResponse) (Memory := Memory) (CommitMemory := MonoCommitMemory)
    (b := monoB) (c := monoC) (r := monoR) (k := monoK) (front := monoFront) (queries := monoQueries) (height := monoHeight) ×
  CheckpointExecution.State (Input := Input) (Digest := Digest) (AmbientMatrixSource.Shape heights)

local notation "MonoChild" => MonomialOutcome (q := q) (Input := Input) (Cfg := Cfg) (Memory := Memory)
  (MonoResponse := MonoResponse) (MonoCommitMemory := MonoCommitMemory) (monoB := monoB) (monoC := monoC) (monoR := monoR)
  (monoK := monoK) (monoFront := monoFront) (monoQueries := monoQueries) (monoHeight := monoHeight)

def eraseBefore (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d) (before : Finished first second) :=
  (PackedPBSAccumulator.eraseBefore first second before.1,before.2.map (fun child => (child.1.1,child.2.1)))

def beforeState (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d) (before : Finished first second) :=
  PackedPBSAccumulator.finalState first second before

/-- Both computed accumulator flags gate the two-call loop. Native coefficient
roots come from the same retained accumulator references; returned opening
memory enters the first NTT and later rejection skips the remaining suffix. -/
def program (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^monoC*monoB = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme) := do
  let before ← PackedPBSAccumulator.program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory
  match before.2 with
  | none => pure (before,none)
  | some child =>
    if child.2.1.accepted && child.2.2.accepted then
      let ntts ← AmbientMonomialNTT.program hs.encoding monoLength psi primitive
        (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase child.2.2.memory
      pure (before,some ntts)
    else pure (before,none)

def finish (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (monoLength : 2^monoC*monoB = 2^log)
    (evaluations : PackedPBSMonomialReferences.Evaluations) (monoBase : Bool → Memory → MonoScheme)
    (before : Finished first second) : ProbComp (Finished first second × Option (MonoChild first.heights)) := do
  match before.2 with
  | none => pure (before,none)
  | some child =>
    if child.2.1.1.accepted && child.2.1.2.accepted then
      let ntts ← AmbientMonomialNTT.witness hs.encoding monoLength psi primitive
        (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase first.heights dummy child.2.1.2.memory child.2.2
      pure (before,some ntts)
    else pure (before,none)

def witness (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^monoC*monoB = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) := do
  let before ← PackedPBSAccumulator.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial
  finish psi primitive hs dummy first second accumulators monoLength evaluations monoBase before

def finalState (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (outcome : Finished first second × Option (MonoChild first.heights)) :=
  match outcome.2 with
  | none => beforeState first second outcome.1
  | some ntts => ntts.2

/-- The exact accumulator final state is inherited by monomial work. -/
theorem project_before (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
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
    (fun before => (eraseBefore first second before,beforeState first second before)) <$>
      PackedPBSAccumulator.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (AmbientMatrixSource.Shape first.heights))
      (PackedPBSAccumulator.program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory)).run
      (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape first.heights) initial) :=
  PackedPBSAccumulator.project_witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial compatible restricted

/-- Full-state erasure follows the actual accumulator gate and returned memory,
including skipped/rejected monomial NTT calls and the exact final state. -/
theorem project_witness (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^monoC*monoB = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape first.heights) initial.checkpoints)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (first.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)) :
    (fun outcome => ((eraseBefore first second outcome.1,outcome.2.map (fun ntts => AmbientNTTSequence.erase first.heights ntts.1)),finalState first second outcome)) <$>
      witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase initial =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (AmbientMatrixSource.Shape first.heights))
      (program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase)).run
      (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape first.heights) initial) := by
  simp only [program,simulateQ_bind,StateT.run_bind]
  rw [←project_before length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial compatible restricted]
  simp only [witness,map_bind,bind_map_left]
  congr 1
  funext before
  cases equal : before.2 with
  | none => simp [finish,eraseBefore,finalState,equal,map_pure,simulateQ_pure,StateT.run_pure]
  | some child =>
    simp only [eraseBefore,equal,Option.map_some]
    by_cases passed : (child.2.1.1.accepted && child.2.1.2.accepted) = true
    · simp only [finish,equal,passed,ite_true,map_bind,map_pure,simulateQ_bind,StateT.run_bind,
        simulateQ_pure,StateT.run_pure,Option.map_some,finalState]
      have projected := AmbientMonomialNTT.project_witness hs.encoding monoLength psi primitive (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase first.heights dummy child.2.1.2.memory child.2.2
      simp only [beforeState,PackedPBSAccumulator.finalState,equal]
      rw [←projected]
      simp only [bind_map_left]
    · simp [finish,equal,passed,finalState,map_pure,simulateQ_pure,StateT.run_pure]

/-- Reaching this loop derives actual accumulator support, both computed
acceptance flags and its exact returned private memory and ambient state. -/
theorem reached_ntt (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^monoC*monoB = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) (before : Finished first second) (ntts : MonoChild first.heights)
    (supported : (before,some ntts) ∈ support (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase initial)) :
    ∃ child, before.2 = some child ∧ (child.2.1.1.accepted && child.2.1.2.accepted) = true ∧
      before ∈ support (PackedPBSAccumulator.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial) ∧
      ntts ∈ support (AmbientMonomialNTT.witness hs.encoding monoLength psi primitive (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase first.heights dummy child.2.1.2.memory child.2.2) := by
  simp only [witness,support_bind,Set.mem_iUnion] at supported
  obtain ⟨selected,selectedSupported,remainder⟩ := supported
  cases equal : selected.2 with
  | none => simp [finish,equal] at remainder
  | some child =>
    by_cases passed : (child.2.1.1.accepted && child.2.1.2.accepted) = true
    · simp only [finish,equal,passed,ite_true,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at remainder
      obtain ⟨actual,actualSupported,same⟩ := remainder
      have sameBefore : before = selected := congrArg Prod.fst same
      have sameChild : ntts = actual := Option.some.inj (congrArg Prod.snd same)
      subst selected
      subst actual
      exact ⟨child,equal,passed,selectedSupported,actualSupported⟩
    · simp [finish,equal,passed] at remainder

/-- Successful loop acceptance entails both native NTT calls in their exact
trusted order, excluding any hidden skipped suffix. -/
theorem accepted_indices (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^monoC*monoB = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) (before : Finished first second) (ntts : MonoChild first.heights)
    (supported : (before,some ntts) ∈ support (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase initial)) (accepted : ntts.1.accepted = true) :
    ntts.1.results.map Prod.fst = [false,true] := by
  obtain ⟨child,_,_,_,present⟩ := reached_ntt length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase initial before ntts supported
  exact AmbientNTTSequenceSoundness.accepted_indices (AmbientMonomialNTT.factory hs.encoding monoLength psi primitive (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase)
    first.heights hs.encoding dummy [false,true] child.2.1.2.memory child.2.2 ntts present accepted

/-- Every actual retained monomial NTT uses accumulator object 0/1 and the
matching retained evaluation root, even if this or a later call rejects. -/
theorem retained_roots (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^monoC*monoB = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) (before : Finished first second) (ntts : MonoChild first.heights)
    (supported : (before,some ntts) ∈ support (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase initial))
    (entry : Bool × Memory × AmbientMonomialNTT.Child first.heights (F := ZMod q) (Input := Input) (Digest := Digest) (Cfg := Cfg)
      (Response := MonoResponse) (Memory := Memory) (CommitMemory := MonoCommitMemory)
      (b := monoB) (c := monoC) (r := monoR) (k := monoK) (front := monoFront) (queries := monoQueries) (height := monoHeight)) (member : entry ∈ ntts.1.results) :
    entry.2.2.1.1.1 = fun source => if source then evaluations.roots entry.1
      else PackedPBSMonomialReferences.coefficients accumulators entry.1 := by
  obtain ⟨child,_,_,_,present⟩ := reached_ntt length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase initial before ntts supported
  exact AmbientMonomialNTT.retained_roots hs.encoding monoLength psi primitive (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase first.heights dummy child.2.1.2.memory child.2.2 ntts present entry member

/-- Each retained original NTT source checkpoint is present at the final
loop state, ready for the later public-plan check to reuse that exact owner. -/
theorem retained_source_recorded (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^monoC*monoB = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) (before : Finished first second) (ntts : MonoChild first.heights)
    (supported : (before,some ntts) ∈ support (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase initial))
    (entry : Bool × Memory × AmbientMonomialNTT.Child first.heights (F := ZMod q) (Input := Input) (Digest := Digest) (Cfg := Cfg)
      (Response := MonoResponse) (Memory := Memory) (CommitMemory := MonoCommitMemory)
      (b := monoB) (c := monoC) (r := monoR) (k := monoK) (front := monoFront) (queries := monoQueries) (height := monoHeight)) (member : entry ∈ ntts.1.results) (source : Bool) :
    ⟨(monoBase entry.1 entry.2.1).tag source,
      AmbientCommittedBatchSafeBound.snapshots first.heights (monoBase entry.1 entry.2.1).tag entry.2.2.1 source⟩ ∈
        ntts.2.checkpoints.checkpoints := by
  obtain ⟨child,_,_,_,present⟩ := reached_ntt length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase initial before ntts supported
  obtain ⟨incoming,childSupported⟩ := AmbientNTTSequenceSoundness.retained_child_support
    (AmbientMonomialNTT.factory hs.encoding monoLength psi primitive (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase) first.heights hs.encoding dummy [false,true] child.2.1.2.memory child.2.2 ntts present entry member
  have recorded := AmbientNTT.fresh_recorded first.heights
    (AmbientMonomialNTT.factory hs.encoding monoLength psi primitive (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase entry.1 entry.2.1) dummy incoming entry.2.2 childSupported source
  exact AmbientNTTSequenceSoundness.child_retains (AmbientMonomialNTT.factory hs.encoding monoLength psi primitive (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase)
    first.heights hs.encoding dummy [false,true] child.2.1.2.memory child.2.2 ntts present entry member
    ((monoBase entry.1 entry.2.1).tag source)
    (AmbientCommittedBatchSafeBound.snapshots first.heights (monoBase entry.1 entry.2.1).tag entry.2.2.1 source) recorded

/-- The reached predecessor inherits its audit from the actual PBS prefix. -/
theorem before_audited (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
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
    (before : Finished first second) (supported : before ∈ support (PackedPBSAccumulator.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial)) :
    CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) (beforeState first second before) :=
  PackedPBSAccumulator.audited_witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory initial compatible restricted audited before supported

/-- Earlier comparison, decomposition and accumulator owners survive every
reached monomial NTT loop, independently of its acceptance. -/
theorem retains (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^monoC*monoB = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) (before : Finished first second) (ntts : MonoChild first.heights)
    (supported : (before,some ntts) ∈ support (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase initial))
    (tag : Cfg) (saved : AmbientMatrixSource.Snapshot Input Digest first.heights tag)
    (recorded : ⟨tag,saved⟩ ∈ (beforeState first second before).checkpoints.checkpoints) :
    ⟨tag,saved⟩ ∈ ntts.2.checkpoints.checkpoints := by
  obtain ⟨child,equal,_,_,present⟩ := reached_ntt length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase initial before ntts supported
  have incoming : ⟨tag,saved⟩ ∈ child.2.2.checkpoints.checkpoints := by
    simpa only [beforeState,PackedPBSAccumulator.finalState,equal] using recorded
  exact AmbientNTTSequenceSoundness.retains (AmbientMonomialNTT.factory hs.encoding monoLength psi primitive (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase)
    first.heights hs.encoding dummy [false,true] child.2.1.2.memory child.2.2 ntts present tag saved incoming

/-- Every branch preserves inherited exceptions, including skipped or rejected
NTT suffixes. There is no second geometry switch or monitor restart. -/
theorem bad_persistent (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^monoC*monoB = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) (outcome : Finished first second × Option (MonoChild first.heights))
    (supported : outcome ∈ support (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase initial))
    (bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (beforeState first second outcome.1)) :
    CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState first second outcome) := by
  rcases outcome with ⟨before,ntts⟩
  cases ntts with
  | none => exact bad
  | some ntts =>
    obtain ⟨child,equal,_,_,present⟩ := reached_ntt length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase initial before ntts supported
    have incoming : CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) child.2.2 := by
      simpa only [beforeState,PackedPBSAccumulator.finalState,equal] using bad
    exact AmbientNTTSequenceSoundness.bad_persistent (AmbientMonomialNTT.factory hs.encoding monoLength psi primitive (PackedPBSMonomialReferences.coefficients accumulators) evaluations.roots monoBase)
      first.heights hs.encoding dummy [false,true] child.2.1.2.memory child.2.2 ntts present incoming

/-- Actual full-state projection supplies the final audit on every branch. -/
theorem audited_witness (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^monoC*monoB = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape first.heights) initial.checkpoints)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (first.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase))
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial)
    (outcome : Finished first second × Option (MonoChild first.heights)) (supported : outcome ∈ support (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase initial)) :
    CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) (finalState first second outcome) := by
  have actual : ((eraseBefore first second outcome.1,outcome.2.map (fun ntts => AmbientNTTSequence.erase first.heights ntts.1)),finalState first second outcome) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (AmbientMatrixSource.Shape first.heights))
        (program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase)).run
        (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape first.heights) initial)) := by
    rw [←project_witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase initial compatible restricted,support_map]
    exact Set.mem_image_of_mem _ supported
  have incoming := CheckpointShapeTransport.audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
    (AmbientMatrixSource.Shape first.heights) initial compatible audited
  exact CheckpointExecution.audited_run (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy _ _ _ incoming _ actual

/-- All native work through both monomial NTTs, including earlier rejects,
contributes to exactly one shared final availability/collision charge. -/
theorem final_bad_le_charge [Fintype Digest] (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper Return2 d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (accumulators : Fin 4 → NativeGoldParameterStore.Reference) (factory : Memory → AccScheme)
    (monoLength : 2^monoC*monoB = 2^log) (evaluations : PackedPBSMonomialReferences.Evaluations)
    (monoBase : Bool → Memory → MonoScheme)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (first.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)) :
    Pr{let outcome ← (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState first second outcome)] ≤
    ExpectedHazard.charge (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy (AmbientMatrixSource.Shape first.heights))
      (CheckpointCollision.loss unifSpec (AmbientMatrixSource.Shape first.heights))
      (program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase)
      (CheckpointExecution.empty (AmbientMatrixSource.Shape first.heights)) := by
  have emptyCompatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape first.heights)
      (CheckpointExecution.empty (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)).checkpoints := by
    intro tag saved member
    cases member
  have projected := project_witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase accumulators factory monoLength evaluations monoBase (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)) emptyCompatible restricted
  have emptyState : CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape first.heights)
      (CheckpointExecution.empty (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) =
      CheckpointExecution.empty (AmbientMatrixSource.Shape first.heights) := rfl
  rw [emptyState] at projected
  have bound := CheckpointCollision.failure_from_empty_le_charge (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
    (AmbientMatrixSource.Shape first.heights) (program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase accumulators factory monoLength evaluations monoBase)
  rw [←projected,prEvent_map] at bound
  exact bound

end
end FormalProof4FHE.HasteBoots.PackedPBSMonomialNTT
