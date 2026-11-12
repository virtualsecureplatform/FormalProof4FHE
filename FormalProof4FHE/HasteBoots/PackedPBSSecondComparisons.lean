module
public import FormalProof4FHE.HasteBoots.PackedPBSSecondReconstructionProbability
@[expose] public section

/-! The second comparison follows the other half's successful reconstruction.
Both comparison calls share the one ambient handler and persistent history. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSSecondComparisons
open PackedPBSFirstComparisons (erasePrior)
open OracleSpec OracleComp
open NativeRootMessage (Digest)
open PackedPBSHadamardNTT (HadamardOutcome LoopOutcome)
open PackedPBSSecondReconstruction (reconstruction)
noncomputable section
section Geometry
variable {Cfg Input Memory SecondHelper SecondResult : Type} {d : ℕ}

/-- The ambient geometry is global ghost context. Source/helper programs and
requests are kept verbatim; the real program does not inspect this field. -/
abbrev sharedScheme (heights : Cfg → ℕ)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper SecondResult d) :=
  {second with heights := heights}

/-- Fixing the common monitor's context leaves the actual comparison call identical. -/
theorem shared_program (heights : Cfg → ℕ)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper SecondResult d)
    (roots : Fin (2*d+2) → Digest) (memory : Memory) :
    PackedPBSComparisonStage.program (sharedScheme heights second) roots memory =
      PackedPBSComparisonStage.program second roots memory := rfl

end Geometry

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

variable {SecondHelper SecondResult : Type}


abbrev ComparisonOutcome (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper SecondResult d) :=
  PackedPBSComparisonStage.Outcome (sharedScheme first.heights second)


def eraseBefore (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d) (before : Previous first) :=
  (PackedPBSSecondReconstruction.eraseBefore first before.1,before.2.map (fun child => (child.1.1,child.2.1)))

def beforeState (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d) (before : Previous first) :=
  PackedPBSSecondReconstruction.finalState first before

/-- The full second reconstruction (algebra AND openings) gates comparisons.
Digits/borrows and the final opening memory are reused in their native order. -/
def program (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper SecondResult d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height) := do
  let before ← PackedPBSSecondReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase first secondBase
  match before.2 with
  | none => pure (before,none)
  | some child =>
    if AuthenticatedLinear.accepted child.2 then
      let compared ← PackedPBSComparisonStage.program second child.1.1 child.2.2.memory
      pure (before,some compared)
    else pure (before,none)

def finish (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper SecondResult d)
    (before : Previous first) : ProbComp (Previous first × Option (ComparisonOutcome first second)) := do
  match before.2 with
  | none => pure (before,none)
  | some child =>
    if AuthenticatedLinear.accepted child.2.1 then
      let compared ← PackedPBSComparisonStage.witness hs.encoding dummy (sharedScheme first.heights second)
        child.1.1.1 child.2.1.2.memory child.2.2
      pure (before,some compared)
    else pure (before,none)

def witness (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper SecondResult d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) := do
  let before ← PackedPBSSecondReconstruction.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first secondBase initial
  finish hs dummy first second before

def finalState (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper SecondResult d)
    (outcome : Previous first × Option (ComparisonOutcome first second)) :=
  match outcome.2 with
  | none => beforeState first outcome.1
  | some compared => compared.2.2.2

/-- The exact ambient state after the second reconstruction is inherited. -/
theorem project_before (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape first.heights) initial.checkpoints)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (first.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)) :
    (fun before => (eraseBefore first before,beforeState first before)) <$>
      PackedPBSSecondReconstruction.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first secondBase initial =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
      (AmbientMatrixSource.Shape first.heights))
      (PackedPBSSecondReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase first secondBase)).run
      (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape first.heights) initial) :=
  PackedPBSSecondReconstruction.project_witness length psi primitive family inputs base hs nodesEnough radix linearBase
    dummy first secondBase initial compatible restricted

/-- Full-state erasure covers both decompositions in actual verification order. -/
theorem project_witness (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper SecondResult d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape first.heights) initial.checkpoints)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (first.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)) :
    (fun outcome => ((eraseBefore first outcome.1,outcome.2.map (PackedPBSComparisonStage.erase (sharedScheme first.heights second))),finalState first second outcome)) <$>
      witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
      (AmbientMatrixSource.Shape first.heights))
      (program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase)).run
      (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape first.heights) initial) := by
  simp only [program,simulateQ_bind,StateT.run_bind]
  rw [←project_before length psi primitive family inputs base hs nodesEnough radix linearBase dummy first secondBase initial compatible restricted]
  simp only [witness,map_bind,bind_map_left]
  congr 1
  funext before
  cases equal : before.2 with
  | none => simp [finish,eraseBefore,finalState,equal,map_pure,simulateQ_pure,StateT.run_pure]
  | some child =>
    simp only [eraseBefore,equal,Option.map_some]
    by_cases passed : AuthenticatedLinear.accepted child.2.1 = true
    · simp only [finish,equal,passed,ite_true,map_bind,map_pure,simulateQ_bind,StateT.run_bind,
        simulateQ_pure,StateT.run_pure,Option.map_some,finalState]
      have projected := PackedPBSComparisonStage.project_witness hs.encoding dummy (sharedScheme first.heights second)
        child.1.1.1 child.2.1.2.memory child.2.2
      rw [shared_program] at projected
      simp only [beforeState,PackedPBSSecondReconstruction.finalState,equal]
      rw [←projected]
      simp only [bind_map_left]
      rfl
    · simp [finish,equal,passed,finalState,map_pure,simulateQ_pure,StateT.run_pure]


/-- Reached comparisons derive full reconstruction acceptance and the exact
private-memory/state handoff, rather than accepting them as certificates. -/
theorem reached_comparisons (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper SecondResult d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (before : Previous first) (compared : ComparisonOutcome first second)
    (supported : (before,some compared) ∈ support
      (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial)) :
    ∃ child, before.2 = some child ∧ AuthenticatedLinear.accepted child.2.1 = true ∧
      before ∈ support (PackedPBSSecondReconstruction.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first secondBase initial) ∧
      compared ∈ support (PackedPBSComparisonStage.witness hs.encoding dummy (sharedScheme first.heights second)
        child.1.1.1 child.2.1.2.memory child.2.2) := by
  simp only [witness,support_bind,Set.mem_iUnion] at supported
  obtain ⟨selected,selectedSupported,remainder⟩ := supported
  cases equal : selected.2 with
  | none => simp [finish,equal] at remainder
  | some child =>
    by_cases passed : AuthenticatedLinear.accepted child.2.1 = true
    · simp only [finish,equal,passed,ite_true,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at remainder
      obtain ⟨actual,actualSupported,same⟩ := remainder
      have sameBefore : before = selected := congrArg Prod.fst same
      have sameCompared : compared = actual := Option.some.inj (congrArg Prod.snd same)
      subst selected
      subst actual
      exact ⟨child,equal,passed,selectedSupported,actualSupported⟩
    · simp [finish,equal,passed] at remainder

/-- The full second-half digit/borrow registry and the returned opening memory
are fixed before the comparison's fresh pair sampling and helper work. -/
theorem comparison_sources (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper SecondResult d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (before : Previous first) (compared : ComparisonOutcome first second)
    (supported : (before,some compared) ∈ support
      (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial)) :
    ∃ child, before.2 = some child ∧ AuthenticatedLinear.accepted child.2.1 = true ∧
      compared.1.1 = PackedPBSComparisonStage.sources child.1.1.1 child.2.1.2.memory := by
  obtain ⟨child,equal,passed,_,present⟩ := reached_comparisons length psi primitive family inputs base hs nodesEnough radix linearBase
    dummy first second secondBase initial before compared supported
  exact ⟨child,equal,passed,(PackedPBSComparisonStage.source_eq hs.encoding dummy (sharedScheme first.heights second) _ _ _ compared present).1⟩

/-- Supported second-comparison digits inherit the TRUE-half original roots. -/
theorem comparison_digit_roots (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper SecondResult d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (before : Previous first) (compared : ComparisonOutcome first second)
    (supported : (before,some compared) ∈ support
      (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial))
    (level : Fin d) :
    compared.1.1.1 (PackedPBSComparisonReferences.digitSlot level) =
      family.coefficients (PackedPBSDecompositionReferences.digitSlot true level) := by
  obtain ⟨child,equal,_,priorSupported,present⟩ := reached_comparisons length psi primitive family inputs base hs nodesEnough radix linearBase
    dummy first second secondBase initial before compared supported
  have childSupport : (before.1,some child) ∈ support
      (PackedPBSSecondReconstruction.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first secondBase initial) := by
    rw [←equal]
    exact priorSupported
  have roots := (PackedPBSSecondReconstruction.roots length psi primitive family inputs base hs nodesEnough radix linearBase
    dummy first secondBase initial before.1 child childSupport).2 level
  have fixed := (PackedPBSComparisonStage.source_eq hs.encoding dummy (sharedScheme first.heights second) _ _ _ compared present).1
  have source := congrArg (fun emission => emission.1 (PackedPBSComparisonReferences.digitSlot level)) fixed
  simpa only [PackedPBSComparisonStage.sources,PackedPBSComparisonReferences.linear_digit] using source.trans roots

/-- All previous source/helper owners persist through the reached second comparison. -/
theorem retains (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper SecondResult d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (before : Previous first) (compared : ComparisonOutcome first second)
    (supported : (before,some compared) ∈ support
      (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial))
    (tag : Cfg) (saved : AmbientMatrixSource.Snapshot Input Digest first.heights tag)
    (recorded : ⟨tag,saved⟩ ∈ (beforeState first before).checkpoints.checkpoints) :
    ⟨tag,saved⟩ ∈ compared.2.2.2.checkpoints.checkpoints := by
  obtain ⟨child,equal,_,_,present⟩ := reached_comparisons length psi primitive family inputs base hs nodesEnough radix linearBase
    dummy first second secondBase initial before compared supported
  have original : ⟨tag,saved⟩ ∈ child.2.2.checkpoints.checkpoints := by
    simpa only [beforeState,PackedPBSSecondReconstruction.finalState,equal] using recorded
  exact PackedPBSComparisonStage.retains hs.encoding dummy (sharedScheme first.heights second) _ _ _ tag saved original compared present

/-- Earlier exceptions persist across the final comparison and all rejected branches. -/
theorem bad_persistent (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper SecondResult d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (outcome : Previous first × Option (ComparisonOutcome first second))
    (supported : outcome ∈ support
      (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial))
    (bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (beforeState first outcome.1)) :
    CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState first second outcome) := by
  simp only [witness,support_bind,Set.mem_iUnion] at supported
  obtain ⟨before,_,present⟩ := supported
  cases equal : before.2 with
  | none =>
    simp only [finish,equal,support_pure,Set.mem_singleton_iff] at present
    subst outcome
    exact bad
  | some child =>
    by_cases passed : AuthenticatedLinear.accepted child.2.1 = true
    · simp only [finish,equal,passed,ite_true,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at present
      obtain ⟨compared,comparedSupported,same⟩ := present
      subst outcome
      have incoming : CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) child.2.2 := by
        simpa only [beforeState,PackedPBSSecondReconstruction.finalState,equal] using bad
      exact PackedPBSComparisonStage.bad_persistent hs.encoding dummy (sharedScheme first.heights second) _ _ _ incoming compared comparedSupported
    · simp [finish,equal,passed] at present
      subst outcome
      exact bad

/-- The complete two-decomposition prefix inherits its audit on actual shared state. -/
theorem audited_witness (dummy : Digest) (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper SecondResult d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial)
    (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape first.heights) initial.checkpoints)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (first.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase))
    (outcome : Previous first × Option (ComparisonOutcome first second))
    (supported : outcome ∈ support
      (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial)) :
    CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape first.heights) (finalState first second outcome) := by
  have actual : ((eraseBefore first outcome.1,outcome.2.map (PackedPBSComparisonStage.erase (sharedScheme first.heights second))),finalState first second outcome) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
        (AmbientMatrixSource.Shape first.heights))
        (program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase)).run
        (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape first.heights) initial)) := by
    rw [←project_witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase initial compatible restricted,support_map]
    exact Set.mem_image_of_mem _ supported
  have incoming := CheckpointShapeTransport.audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
    (AmbientMatrixSource.Shape first.heights) initial compatible audited
  exact CheckpointExecution.audited_run (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy _ _ _ incoming _ actual

/-- Both decompositions share one final availability/collision charge on the
actual complete prefix, with every rejected-path query retained. -/
theorem final_bad_le_charge [Fintype Digest] (dummy : Digest)
    (first : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (second : PackedPBSComparisonStage.Scheme Cfg Input Memory SecondHelper SecondResult d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (first.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)) :
    Pr{let outcome ← (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[
      CheckpointCollision.Bad (AmbientMatrixSource.Shape first.heights) (finalState first second outcome)] ≤
    ExpectedHazard.charge (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
      (AmbientMatrixSource.Shape first.heights))
      (CheckpointCollision.loss unifSpec (AmbientMatrixSource.Shape first.heights))
      (program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase)
      (CheckpointExecution.empty (AmbientMatrixSource.Shape first.heights)) := by
  have emptyCompatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape first.heights)
      (CheckpointExecution.empty (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)).checkpoints := by
    intro tag saved member
    cases member
  have projected := project_witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy first second secondBase
    (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)) emptyCompatible restricted
  have emptyState : CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape first.heights)
      (CheckpointExecution.empty (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) =
      CheckpointExecution.empty (AmbientMatrixSource.Shape first.heights) := rfl
  rw [emptyState] at projected
  have bound := CheckpointCollision.failure_from_empty_le_charge (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
    (AmbientMatrixSource.Shape first.heights) (program length psi primitive family inputs base hs nodesEnough radix linearBase first second secondBase)
  rw [←projected,prEvent_map] at bound
  exact bound

end
end FormalProof4FHE.HasteBoots.PackedPBSSecondComparisons
