module

public import FormalProof4FHE.HasteBoots.ByteLookupMiddleTrace
public import FormalProof4FHE.HasteBoots.StagedCompletedObservation
public import FormalProof4FHE.HasteBoots.ByteLookupUnbounded
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

/-!
# Unbounded byte sampling in the actual staged experiment

The source commitment is executed before sampling; both source and helper
snapshots and the actual later result/final state are retained. Every event
of this countably additive measure is the limit of the actual completed
finite executions. Erasing the snapshots yields the real query program.
This is an ideal-byte/private-coin result, not a production FS refinement.
-/

open OracleSpec OracleComp BinaryTree MeasureTheory
open scoped Classical

namespace FormalProof4FHE.HasteBoots.StagedByteLookupLimit

noncomputable section

variable {F K Cfg Input Digest Payload HelperMemory First Result : Type}
  [Field F] [Field K] [Algebra F K] [DecidableEq K]
  {p degree width size repetitions : ℕ} [Module (ZMod p) K]
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

local instance (X : Type) : MeasurableSpace X := ⊤
local instance (X Y : Type) : MeasurableSpace (X × Y) := ⊤

abbrev Second (p degree : ℕ) (K Digest HelperMemory : Type) [Zero K] (repetitions : ℕ) :=
  ByteLookupPairMiddle.Emission p degree K Digest HelperMemory repetitions

def done (second : Second p degree K Digest HelperMemory repetitions) : Prop := second.1.values ≠ none

variable (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F)
  (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
  (sourceRequests : First → List (Cfg × Digest))
  (requests : First → Second p degree K Digest HelperMemory repetitions → List (Cfg × Digest))
  (sourceCommit : OracleComp (SharedSequence.Shared Cfg Input Digest) First)
  (build : First → ByteLookupPairTyped.Raw p degree K repetitions → (Fin repetitions → StagedRepeatedLookup.Pair K) →
    OracleComp (SharedSequence.Shared Cfg Input Digest) (StagedRepeatedLookup.HelperEmission repetitions Digest HelperMemory))
  (next : First → Second p degree K Digest HelperMemory repetitions → OracleComp (SharedSequence.Shared Cfg Input Digest) Result)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)

def experiment (hashDepth inner outer : ℕ) :
    ProbComp (StagedCompletedObservation.Outcome (Input := Input) (Digest := Digest) shape First
      (Second p degree K Digest HelperMemory repetitions) Result) :=
  StagedCommitmentPrefix.witness enc dummy shape sourceRequests requests sourceCommit
    (fun first => ByteLookupPairMiddle.program basis table hashDepth inner outer repetitions (build first)) next initial

local notation "run" => experiment basis table enc dummy shape sourceRequests requests sourceCommit build next initial
local notation "complete" => StagedCompletedObservation.complete (done (p := p) (degree := degree) (K := K)
  (Digest := Digest) (HelperMemory := HelperMemory) (repetitions := repetitions))

/-- All original snapshots and later shared work survive increased byte depths. -/
theorem ordered {hashDepth inner outer hashDepth' inner' outer' : ℕ}
    (hh : hashDepth ≤ hashDepth') (hi : inner ≤ inner') (ho : outer ≤ outer') :
    CompletedObservation.LE (run hashDepth inner outer) (run hashDepth' inner' outer') complete := by
  apply StagedCompletedObservation.witness_order
  intro first state
  exact ByteLookupMiddleTrace.grows basis table enc dummy shape (build first) state hh hi ho

/-- Averaging arbitrary original source commitments does not change the exact
sampler completion probability. The original source/state remain in output. -/
theorem completion (hashDepth inner outer : ℕ) :
    Pr{let outcome ← run hashDepth inner outer}[complete outcome] =
      Pr{let observed ← ByteLookupPairTyped.sample basis table hashDepth inner outer repetitions}[observed.values ≠ none] := by
  apply StagedCompletedObservation.completion
  intro first state
  exact ByteLookupMiddleTrace.completion basis table enc dummy shape (build first) state hashDepth inner outer

/-- Countably additive full staged observation law, without conditioning any
finite approximation on successful completion. -/
def measure : Measure (StagedCompletedObservation.Outcome (Input := Input) (Digest := Digest) shape First
    (Second p degree K Digest HelperMemory repetitions) Result) :=
  CompletedObservationLimit.measure (fun n => run n n n) complete
    (fun _ _ h => ordered basis table enc dummy shape sourceRequests requests sourceCommit build next initial h h h)

local notation "law" => measure basis table enc dummy shape sourceRequests requests sourceCommit build next initial

theorem measure_apply (event : StagedCompletedObservation.Outcome (Input := Input) (Digest := Digest) shape First
    (Second p degree K Digest HelperMemory repetitions) Result → Prop) :
    law {outcome | event outcome} = ⨆ n, Pr{let outcome ← run n n n}[complete outcome ∧ event outcome] :=
  CompletedObservationLimit.measure_apply _ _ _ _

/-- The common depth is cofinal in all three independent operational depths. -/
theorem all_depths (event : StagedCompletedObservation.Outcome (Input := Input) (Digest := Digest) shape First
    (Second p degree K Digest HelperMemory repetitions) Result → Prop) :
    law {outcome | event outcome} = ⨆ outer, ⨆ inner, ⨆ hashDepth,
      Pr{let outcome ← run hashDepth inner outer}[complete outcome ∧ event outcome] := by
  rw [measure_apply]
  exact ByteLookupPairDiagonal.iSup_diagonal _
    (fun _ _ _ _ _ _ hh hi ho => ordered basis table enc dummy shape sourceRequests requests sourceCommit build next initial hh hi ho event)

theorem event_tends (event : StagedCompletedObservation.Outcome (Input := Input) (Digest := Digest) shape First
    (Second p degree K Digest HelperMemory repetitions) Result → Prop) :
    Filter.Tendsto (fun n => Pr{let outcome ← run n n n}[complete outcome ∧ event outcome])
      Filter.atTop (nhds (law {outcome | event outcome})) :=
  CompletedObservationLimit.event_tends _ _ _ _

/-- A uniform security bound for the actual finite runs passes to the full
staged observation law, with the source checkpoint retained in the event. -/
theorem event_bound (event : StagedCompletedObservation.Outcome (Input := Input) (Digest := Digest) shape First
    (Second p degree K Digest HelperMemory repetitions) Result → Prop)
    (epsilon : ENNReal) (bounded : ∀ n, Pr{let outcome ← run n n n}[complete outcome ∧ event outcome] ≤ epsilon) :
    law {outcome | event outcome} ≤ epsilon :=
  CompletedObservationLimit.event_bound _ _ _ _ _ bounded

/-- Prefix-dependent losses are retained explicitly. This supremum is not
silently identified with expected cost under the completed limit measure. -/
theorem varying_loss_bound (event : StagedCompletedObservation.Outcome (Input := Input) (Digest := Digest) shape First
    (Second p degree K Digest HelperMemory repetitions) Result → Prop)
    (epsilon : ENNReal) (loss : ℕ → ENNReal)
    (bounded : ∀ n, Pr{let outcome ← run n n n}[complete outcome ∧ event outcome] ≤ epsilon + loss n) :
    law {outcome | event outcome} ≤ epsilon + ⨆ n, loss n := by
  apply event_bound
  intro n
  exact (bounded n).trans (add_le_add le_rfl (le_iSup loss n))

/-- Erase analysis snapshots and retain the real program's final shared state. -/
def operational : Measure ((First × Second p degree K Digest HelperMemory repetitions × Result) ×
    CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :=
  @Measure.map _ _ ⊤ ⊤ (fun outcome => ((outcome.1.1, outcome.2.1.1, outcome.2.2.1), outcome.2.2.2)) law

/-- The operational measure is the limit of the actual staged query program,
not a replacement sampler with the same challenge-value marginal. -/
theorem operational_apply (event : (First × Second p degree K Digest HelperMemory repetitions × Result) ×
    CheckpointExecution.State (Input := Input) (Digest := Digest) shape → Prop) :
    operational basis table enc dummy shape sourceRequests requests sourceCommit build next initial {outcome | event outcome} =
      ⨆ n, Pr{let outcome ← ((simulateQ
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (StagedCommitmentPrefix.program sourceRequests requests sourceCommit
          (fun first => ByteLookupPairMiddle.program basis table n n n repetitions (build first)) next)).run initial)}[
          done outcome.1.2.1 ∧ event outcome] := by
  rw [operational, Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
    measure, CompletedObservationLimit.measure_apply]
  apply iSup_congr
  intro n
  rw [← StagedCommitmentPrefix.project_witness enc dummy shape sourceRequests requests sourceCommit
    (fun first => ByteLookupPairMiddle.program basis table n n n repetitions (build first)) next initial, prEvent_map]
  rfl

variable [Fintype K] [SampleableType K] [NeZero p]

/-- Almost-sure completion yields mass one on the full actual staged witness. -/
theorem probability (valid : 1 < p) (enough : size + 1 < Fintype.card K) : IsProbabilityMeasure law := by
  apply CompletedObservationLimit.probability
  simp_rw [completion]
  change (⨆ n, Pr{let observed ← ByteLookupUnbounded.steps basis table repetitions n}[
    ByteLookupUnbounded.complete observed]) = 1
  exact ByteLookupUnbounded.completion_sup valid basis table enough repetitions

/-- The original source snapshot keeps its actual law in the unbounded
experiment. Completion does not bias source commitments or their hash logs. -/
theorem source_marginal (valid : 1 < p) (enough : size + 1 < Fintype.card K)
    (event : First × CheckpointExecution.State (Input := Input) (Digest := Digest) shape → Prop) :
    law {outcome | event outcome.1} =
      Pr{let first ← ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        sourceCommit).run initial)}[event first] := by
  rw [measure_apply]
  have finite (n : ℕ) : Pr{let outcome ← run n n n}[complete outcome ∧ event outcome.1] =
      Pr{let first ← ((simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        sourceCommit).run initial)}[event first] *
      Pr{let observed ← ByteLookupPairTyped.sample basis table n n n repetitions}[observed.values ≠ none] := by
    apply StagedCompletedObservation.source_event
    intro first state
    exact ByteLookupMiddleTrace.completion basis table enc dummy shape (build first) state n n n
  simp_rw [finite]
  rw [← ENNReal.mul_iSup]
  have total : (⨆ n, Pr{let observed ← ByteLookupPairTyped.sample basis table n n n repetitions}[
      observed.values ≠ none]) = 1 := by
    change (⨆ n, Pr{let observed ← ByteLookupUnbounded.steps basis table repetitions n}[
      ByteLookupUnbounded.complete observed]) = 1
    exact ByteLookupUnbounded.completion_sup valid basis table enough repetitions
  rw [total, mul_one]

/-- The exact operational erasure also has mass one. -/
theorem operational_probability (valid : 1 < p) (enough : size + 1 < Fintype.card K) :
    IsProbabilityMeasure (operational basis table enc dummy shape sourceRequests requests sourceCommit build next initial) := by
  unfold operational
  apply (Measure.isProbabilityMeasure_map_iff Measurable.of_discrete.aemeasurable).mpr
  exact probability basis table enc dummy shape sourceRequests requests sourceCommit build next initial valid enough

end

end FormalProof4FHE.HasteBoots.StagedByteLookupLimit
