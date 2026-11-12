module
public import FormalProof4FHE.HasteBoots.PackedPBSComparisonSharedExecution
public import FormalProof4FHE.HasteBoots.AmbientDecompositionSoundness
@[expose] public section

/-! Second-half reconstruction follows the first computed comparison return.
The actual ambient state keeps all first-half source/helper history and monitor. -/
namespace FormalProof4FHE.HasteBoots.PackedPBSSecondReconstruction
open PackedPBSFirstComparisons (erasePrior)
open OracleSpec OracleComp
open NativeRootMessage (Digest)
open PackedPBSHadamardNTT (HadamardOutcome LoopOutcome)
open PackedPBSFirstReconstruction (reconstruction)
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

def eraseBefore (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d) (before : Reached s) :=
  (erasePrior before.1,before.2.map (PackedPBSComparisonStage.erase s))

def beforeState (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d) (before : Reached s) :=
  PackedPBSFirstComparisons.finalState s before

/-- The global encoding overrides the factory's encoding. Only the OTHER
half's original input/digit roots are supplied; borrow roots remain received. -/
def reconstruction
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height) (memory : Memory) :=
  PackedPBSFirstReconstruction.reconstruction family inputs nodesEnough radix
    (fun state => {secondBase state with encoding := hs.encoding}) true memory

/-- Entry is gated by the comparison opening loop's computed flag, and uses
that loop's actual returned memory. Every earlier rejection skips this call. -/
def program (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height) := do
  let before ← PackedPBSFirstComparisons.program length psi primitive family inputs base hs nodesEnough radix linearBase s
  match before.2 with
  | none => pure (before,none)
  | some compared =>
    if compared.2.2.2.accepted then
      let child ← AuthenticatedLinear.program (reconstruction family inputs hs nodesEnough radix secondBase compared.2.2.2.memory)
      pure (before,some child)
    else pure (before,none)

def finish (dummy : Digest) (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height) (before : Reached s) :
    ProbComp (Reached s × Option (LinearOutcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
      (Memory := Memory) (CommitMemory := CommitMemory) (d := d) (b := b) (front := front) (suffix := suffix)
      (queries := queries) (height := height) s.heights)) := do
  match before.2 with
  | none => pure (before,none)
  | some compared =>
    if compared.2.2.1.2.accepted then
      let child ← AmbientLinear.witness s.heights
        (reconstruction family inputs hs nodesEnough radix secondBase compared.2.2.1.2.memory) dummy compared.2.2.2
      pure (before,some child)
    else pure (before,none)

def witness (dummy : Digest) (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) := do
  let before ← PackedPBSFirstComparisons.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s initial
  finish family inputs hs nodesEnough radix dummy s secondBase before

local notation "Child" => LinearOutcome (q := q) (Input := Input) (Cfg := Cfg) (Response := Response)
  (Memory := Memory) (CommitMemory := CommitMemory) (d := d) (b := b) (front := front) (suffix := suffix)
  (queries := queries) (height := height)

def finalState (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (outcome : Reached s × Option (Child s.heights)) :=
  match outcome.2 with
  | none => beforeState s outcome.1
  | some child => child.2.2


/-- The complete first comparison return has the exact ambient predecessor
state used by the second reconstruction, including all helper checkpoints. -/
theorem project_before (dummy : Digest) (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape s.heights) initial.checkpoints)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (s.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)) :
    (fun before => (eraseBefore s before,beforeState s before)) <$>
      PackedPBSFirstComparisons.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s initial =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
      (AmbientMatrixSource.Shape s.heights))
      (PackedPBSFirstComparisons.program length psi primitive family inputs base hs nodesEnough radix linearBase s)).run
      (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape s.heights) initial) :=
  PackedPBSComparisonSharedExecution.project_witness length psi primitive family inputs base hs nodesEnough radix linearBase
    dummy s initial compatible restricted

/-- Erasure preserves every shared state component on rejected and reached
paths. There is no second geometry switch or checkpoint/history reset. -/
theorem project_witness (dummy : Digest) (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape s.heights) initial.checkpoints)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (s.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)) :
    (fun outcome => ((eraseBefore s outcome.1,outcome.2.map (fun child => (child.1.1,child.2.1))),finalState s outcome)) <$>
      witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s secondBase initial =
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
      (AmbientMatrixSource.Shape s.heights))
      (program length psi primitive family inputs base hs nodesEnough radix linearBase s secondBase)).run
      (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape s.heights) initial) := by
  simp only [program,simulateQ_bind,StateT.run_bind]
  rw [←project_before length psi primitive family inputs base hs nodesEnough radix linearBase dummy s initial compatible restricted]
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
      let childScheme := reconstruction family inputs hs nodesEnough radix secondBase compared.2.2.1.2.memory
      have projected := AmbientLinear.project_witness s.heights childScheme dummy compared.2.2.2
      have encoding : childScheme.encoding = hs.encoding := rfl
      rw [encoding] at projected
      simp only [beforeState,PackedPBSFirstComparisons.finalState,equal]
      rw [←projected]
      simp only [bind_map_left]
      rfl
    · simp [finish,equal,passed,finalState,PackedPBSComparisonStage.erase,map_pure,simulateQ_pure,StateT.run_pure]

/-- Reaching the second reconstruction derives the actual earlier support,
computed comparison acceptance and precise returned memory and ambient state. -/
theorem reached_reconstruction (dummy : Digest) (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (before : Reached s) (child : Child s.heights)
    (supported : (before,some child) ∈ support
      (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s secondBase initial)) :
    ∃ compared, before.2 = some compared ∧ compared.2.2.1.2.accepted = true ∧
      before ∈ support (PackedPBSFirstComparisons.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s initial) ∧
      child ∈ support (AmbientLinear.witness s.heights
        (reconstruction family inputs hs nodesEnough radix secondBase compared.2.2.1.2.memory) dummy compared.2.2.2) := by
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

/-- The other half's original input and digit roots are fixed on every reached
branch, including subsequent linear/opening rejections. -/
theorem roots (dummy : Digest) (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (before : Reached s) (child : Child s.heights)
    (supported : (before,some child) ∈ support
      (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s secondBase initial)) :
    child.1.1.1 DecompositionLinear.input = inputs.roots true ∧
      ∀ level, child.1.1.1 (DecompositionLinear.digit level) =
        family.coefficients (PackedPBSDecompositionReferences.digitSlot true level) := by
  obtain ⟨compared,_,_,_,present⟩ := reached_reconstruction length psi primitive family inputs base hs nodesEnough radix linearBase
    dummy s secondBase initial before child supported
  exact AmbientDecompositionSoundness.roots s.heights q nodesEnough (inputs.roots true)
    (fun level => family.coefficients (PackedPBSDecompositionReferences.digitSlot true level)) radix
    {secondBase compared.2.2.1.2.memory with encoding := hs.encoding} dummy compared.2.2.2 child present


/-- The reached first-comparison state inherits the complete ambient audit. -/
theorem before_audited (dummy : Digest) (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial)
    (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape s.heights) initial.checkpoints)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (s.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase))
    (before : Reached s)
    (supported : before ∈ support
      (PackedPBSFirstComparisons.witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s initial)) :
    CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape s.heights) (beforeState s before) := by
  have actual : (eraseBefore s before,beforeState s before) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
        (AmbientMatrixSource.Shape s.heights))
        (PackedPBSFirstComparisons.program length psi primitive family inputs base hs nodesEnough radix linearBase s)).run
        (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape s.heights) initial)) := by
    rw [←project_before length psi primitive family inputs base hs nodesEnough radix linearBase dummy s initial compatible restricted,support_map]
    exact Set.mem_image_of_mem _ supported
  have incoming := CheckpointShapeTransport.audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
    (AmbientMatrixSource.Shape s.heights) initial compatible audited
  exact CheckpointExecution.audited_run (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy _ _ _ incoming _ actual

/-- Every old source/helper snapshot is retained by a reached reconstruction. -/
theorem retains (dummy : Digest) (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (before : Reached s) (child : Child s.heights)
    (supported : (before,some child) ∈ support
      (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s secondBase initial))
    (tag : Cfg) (saved : AmbientMatrixSource.Snapshot Input Digest s.heights tag)
    (recorded : ⟨tag,saved⟩ ∈ (beforeState s before).checkpoints.checkpoints) :
    ⟨tag,saved⟩ ∈ child.2.2.checkpoints.checkpoints := by
  obtain ⟨compared,equal,_,_,present⟩ := reached_reconstruction length psi primitive family inputs base hs nodesEnough radix linearBase
    dummy s secondBase initial before child supported
  have original : ⟨tag,saved⟩ ∈ compared.2.2.2.checkpoints.checkpoints := by
    simpa only [beforeState,PackedPBSFirstComparisons.finalState,equal] using recorded
  exact AmbientLinear.retains s.heights _ dummy compared.2.2.2 child present tag saved original

/-- Earlier failures and collisions survive every second-reconstruction branch. -/
theorem bad_persistent (dummy : Digest) (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (outcome : Reached s × Option (Child s.heights))
    (supported : outcome ∈ support
      (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s secondBase initial))
    (bad : CheckpointCollision.Bad (AmbientMatrixSource.Shape s.heights) (beforeState s outcome.1)) :
    CheckpointCollision.Bad (AmbientMatrixSource.Shape s.heights) (finalState s outcome) := by
  simp only [witness,support_bind,Set.mem_iUnion] at supported
  obtain ⟨before,_,present⟩ := supported
  cases equal : before.2 with
  | none =>
    simp only [finish,equal,support_pure,Set.mem_singleton_iff] at present
    subst outcome
    exact bad
  | some compared =>
    by_cases passed : compared.2.2.1.2.accepted = true
    · simp only [finish,equal,passed,ite_true,support_bind,support_pure,Set.mem_iUnion,Set.mem_singleton_iff] at present
      obtain ⟨child,childSupported,same⟩ := present
      subst outcome
      have incoming : CheckpointCollision.Bad (AmbientMatrixSource.Shape s.heights) compared.2.2.2 := by
        simpa only [beforeState,PackedPBSFirstComparisons.finalState,equal] using bad
      exact AmbientLinear.bad_persistent s.heights _ dummy _ incoming child childSupported
    · simp [finish,equal,passed] at present
      subst outcome
      exact bad

/-- Rejected and reached paths retain an audit on the actual whole run. -/
theorem audited_witness (dummy : Digest) (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height))
    (audited : CheckpointExecution.Audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height) initial)
    (compatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape s.heights) initial.checkpoints)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (s.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase))
    (outcome : Reached s × Option (Child s.heights))
    (supported : outcome ∈ support
      (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s secondBase initial)) :
    CheckpointExecution.Audited hs.encoding dummy (AmbientMatrixSource.Shape s.heights) (finalState s outcome) := by
  have actual : ((eraseBefore s outcome.1,outcome.2.map (fun child => (child.1.1,child.2.1))),finalState s outcome) ∈ support
      ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
        (AmbientMatrixSource.Shape s.heights))
        (program length psi primitive family inputs base hs nodesEnough radix linearBase s secondBase)).run
        (CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape s.heights) initial)) := by
    rw [←project_witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s secondBase initial compatible restricted,support_map]
    exact Set.mem_image_of_mem _ supported
  have incoming := CheckpointShapeTransport.audited hs.encoding dummy (RecordedSourceCoherence.Shape Cfg height)
    (AmbientMatrixSource.Shape s.heights) initial compatible audited
  exact CheckpointExecution.audited_run (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy _ _ _ incoming _ actual


/-- The extended second-reconstruction prefix retains one whole-run charge
for every earlier collision or availability failure, including rejected paths. -/
theorem final_bad_le_charge [Fintype Digest] (dummy : Digest)
    (s : PackedPBSComparisonStage.Scheme Cfg Input Memory Helper Return d)
    (secondBase : Memory → AuthenticatedLinear.Scheme (ZMod q) Input Digest Cfg Response Memory CommitMemory
      (2*d+2) b front suffix m queries height)
    (restricted : CheckpointRecordScope.Scoped
      (fun tag => RecordedSourceCoherence.Shape Cfg height tag = BinaryTree.Skeleton.perfect (s.heights tag))
      (PackedPBSFirstReconstruction.program length psi primitive family inputs base hs nodesEnough radix linearBase)) :
    Pr{let outcome ← (witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s secondBase
      (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)))}[
      CheckpointCollision.Bad (AmbientMatrixSource.Shape s.heights) (finalState s outcome)] ≤
    ExpectedHazard.charge (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
      (AmbientMatrixSource.Shape s.heights))
      (CheckpointCollision.loss unifSpec (AmbientMatrixSource.Shape s.heights))
      (program length psi primitive family inputs base hs nodesEnough radix linearBase s secondBase)
      (CheckpointExecution.empty (AmbientMatrixSource.Shape s.heights)) := by
  have emptyCompatible : CheckpointShapeTransport.Compatible (RecordedSourceCoherence.Shape Cfg height)
      (AmbientMatrixSource.Shape s.heights)
      (CheckpointExecution.empty (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)).checkpoints := by
    intro tag saved member
    cases member
  have projected := project_witness length psi primitive family inputs base hs nodesEnough radix linearBase dummy s secondBase
    (CheckpointExecution.empty (RecordedSourceCoherence.Shape Cfg height)) emptyCompatible restricted
  have emptyState : CheckpointShapeTransport.state (RecordedSourceCoherence.Shape Cfg height) (AmbientMatrixSource.Shape s.heights)
      (CheckpointExecution.empty (Input := Input) (Digest := Digest) (RecordedSourceCoherence.Shape Cfg height)) =
      CheckpointExecution.empty (AmbientMatrixSource.Shape s.heights) := rfl
  rw [emptyState] at projected
  have bound := CheckpointCollision.failure_from_empty_le_charge (QueryImpl.ofLift unifSpec ProbComp) hs.encoding dummy
    (AmbientMatrixSource.Shape s.heights) (program length psi primitive family inputs base hs nodesEnough radix linearBase s secondBase)
  rw [←projected,prEvent_map] at bound
  exact bound

end
end FormalProof4FHE.HasteBoots.PackedPBSSecondReconstruction
