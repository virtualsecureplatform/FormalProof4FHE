module

public import FormalProof4FHE.HasteBoots.PrivateChargedSampling
public import FormalProof4FHE.HasteBoots.SharedCompletedContinuation
public import FormalProof4FHE.HasteBoots.CompletedExpectation

@[expose] public section

/-!
# Recorded expected charge in an unbounded completed continuation

The actual private sampler runs before its observation-sensitive shared
continuation. Availability loss is zero on private queries; suspension skips
the continuation and retains all partial observations. Starting the account
at zero makes suspended account mass exactly zero, so the completed-limit
mean equals the supremum of the actual whole-prefix continuation charges.
An earlier charged source prefix remains a separate composition obligation.
-/

open OracleSpec OracleComp BinaryTree MeasureTheory
open scoped Classical

namespace FormalProof4FHE.HasteBoots.SharedChargedCompletion

noncomputable section

variable {A Later Cfg Input Digest Payload : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

local instance (X : Type) : MeasurableSpace X := ⊤
local instance (X Y : Type) : MeasurableSpace (X × Y) := ⊤

def pack (shape : Cfg → Skeleton)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape × ENNReal)
    (outcome : A × Option (Later × CheckpointExecution.State (Input := Input) (Digest := Digest) shape × ENNReal)) :
    (A × Option Later) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape × ENNReal :=
  match outcome.2 with
  | none => ((outcome.1, none), initial)
  | some last => ((outcome.1, some last.1), last.2)

def finished {shape : Cfg → Skeleton}
    (outcome : (A × Option Later) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape × ENNReal) : Prop :=
  outcome.1.2 ≠ none

variable (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
  (loss : (CheckpointExecution.Spec unifSpec Cfg Input Digest).Domain →
    CheckpointExecution.State (Input := Input) (Digest := Digest) shape → ENNReal)
  (private_zero : ∀ query state, loss (.inl query) state = 0)
  (next : A → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Later)
  (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)

include private_zero in
/-- Exact interpreted program, including the unchanged existing account on
suspension and the actual final cache/log/account on completed execution. -/
theorem run_program (step : ProbComp A) (complete : A → Prop) (spent : ENNReal) :
    (simulateQ (ChargedExecution.handler
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) loss)
      (SharedCompletedContinuation.program step complete next)).run (initial, spent) =
      pack shape (initial, spent) <$> CompletedContinuation.program step complete
        (fun first => (simulateQ (ChargedExecution.handler
          (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) loss)
          (next first)).run (initial, spent)) := by
  rw [SharedCompletedContinuation.program, simulateQ_bind, StateT.run_bind,
    PrivateChargedSampling.run_probComp enc dummy shape loss private_zero, bind_map_left,
    CompletedContinuation.program, map_bind]
  congr 1
  funext first
  by_cases done : complete first
  · simp only [done, ite_true, simulateQ_map, StateT.run_map, Functor.map_map, pack]
  · simp [done, simulateQ_pure, StateT.run_pure, pack]

include private_zero in
/-- At account zero, gating by completion removes exactly zero recorded cost.
This uses the actual private/continuation query programs, not a tail bound. -/
theorem gated_account (step : ProbComp A) (complete : A → Prop) :
    (∫⁻ value, value ∂𝒟[(fun outcome => if finished outcome then outcome.2.2 else 0) <$>
      (simulateQ (ChargedExecution.handler
        (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) loss)
        (SharedCompletedContinuation.program step complete next)).run (initial, 0)]) =
      ∫⁻ value, value ∂𝒟[(fun outcome => outcome.2.2) <$>
        (simulateQ (ChargedExecution.handler
          (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) loss)
          (SharedCompletedContinuation.program step complete next)).run (initial, 0)] := by
  rw [run_program enc dummy shape loss private_zero next initial]
  simp only [Functor.map_map]
  have same : (fun outcome => if finished (pack shape (initial, 0) outcome)
      then (pack shape (initial, 0) outcome).2.2 else 0) =
      (fun outcome : A × Option (Later × CheckpointExecution.State (Input := Input) (Digest := Digest) shape × ENNReal) =>
        (pack shape (initial, 0) outcome).2.2) := by
    funext outcome
    cases tag : outcome.2 <;> simp [pack, finished, tag]
  rw [same]

variable (observations : ℕ → ProbComp A) (complete : A → Prop)
  (grows : ∀ i j, i ≤ j → CompletedObservation.LE (observations i) (observations j) complete)

def experiment (n : ℕ) :=
  (simulateQ (ChargedExecution.handler
    (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) loss)
    (SharedCompletedContinuation.program (observations n) complete next)).run (initial, 0)

local notation "run" => experiment enc dummy shape loss next initial observations complete

include private_zero grows in
/-- Full outcome/account order is inherited from the complete raw sampler
order. It allows arbitrary trace-dependent later queries and rejection flags. -/
theorem ordered {i j : ℕ} (h : i ≤ j) : CompletedObservation.LE (run i) (run j) finished := by
  simp only [experiment, run_program enc dummy shape loss private_zero next initial]
  apply CompletedObservation.map (CompletedContinuation.ordered complete _ (grows i j h))
  intro outcome
  cases tag : outcome.2 <;> simp [pack, finished, CompletedContinuation.finished, tag]

include private_zero in
/-- The recorded-account run has exactly the sampler completion probability. -/
theorem completion (n : ℕ) : Pr{let outcome ← run n}[finished outcome] =
    Pr{let first ← observations n}[complete first] := by
  rw [experiment, run_program enc dummy shape loss private_zero next initial, prEvent_map]
  refine (prEvent_congr _ _ _ ?_).trans (CompletedContinuation.completion (observations n) complete
    (fun first => (simulateQ (ChargedExecution.handler
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) loss)
      (next first)).run (initial, 0)))
  intro outcome
  cases tag : outcome.2 <;> simp [pack, finished, CompletedContinuation.finished, tag]

/-- Countably additive completed measure retaining raw observations, all later
results, the actual final shared state and the pathwise account. -/
def measure : Measure ((A × Option Later) ×
    CheckpointExecution.State (Input := Input) (Digest := Digest) shape × ENNReal) :=
  CompletedObservationLimit.measure (fun n => run n) finished
    (fun _ _ h => ordered enc dummy shape loss private_zero next initial observations complete grows h)

local notation "law" => measure enc dummy shape loss private_zero next initial observations complete grows

theorem measure_apply (event : (A × Option Later) ×
    CheckpointExecution.State (Input := Input) (Digest := Digest) shape × ENNReal → Prop) :
    law {outcome | event outcome} = ⨆ n, Pr{let outcome ← run n}[finished outcome ∧ event outcome] :=
  CompletedObservationLimit.measure_apply _ _ _ _

/-- Almost-sure private-sampler completion gives a normalized full account law. -/
theorem probability (total : (⨆ n, Pr{let first ← observations n}[complete first]) = 1) :
    IsProbabilityMeasure law := by
  apply CompletedObservationLimit.probability
  simpa only [completion enc dummy shape loss private_zero next initial] using total

/-- Dropping the account preserves every event on the original complete
shared execution, including its raw observation and final cache/log. -/
theorem erase_event (event : (A × Option Later) ×
    CheckpointExecution.State (Input := Input) (Digest := Digest) shape → Prop) :
    law {outcome | event (outcome.1, outcome.2.1)} =
      SharedCompletedContinuation.measure observations complete grows enc dummy shape next initial {outcome | event outcome} := by
  rw [measure_apply, SharedCompletedContinuation.measure_apply]
  apply iSup_congr
  intro n
  exact ChargedExecution.event _ _ _ _ _ (fun outcome => outcome.1.2 ≠ none ∧ event outcome)

/-- The expected account of the completed unbounded execution is the supremum
of actual whole-prefix charges. Suspended account zero is proved above;
no integrability, query cap or independence assumption is supplied. -/
theorem expected : (∫⁻ outcome, outcome.2.2 ∂law) =
    ⨆ n, ExpectedHazard.charge
      (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape) loss
      (SharedCompletedContinuation.program (observations n) complete next) initial := by
  rw [measure, CompletedExpectation.gated]
  apply iSup_congr
  intro n
  exact (gated_account enc dummy shape loss private_zero next initial (observations n) complete).trans
    (ChargedExecution.expected_zero _ _ _ _)

end

end FormalProof4FHE.HasteBoots.SharedChargedCompletion
