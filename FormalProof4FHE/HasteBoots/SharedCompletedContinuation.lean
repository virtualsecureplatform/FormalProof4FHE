module

public import FormalProof4FHE.HasteBoots.CompletedContinuation
public import FormalProof4FHE.HasteBoots.PrivateSampling
public import Mathlib.MeasureTheory.Measure.Map
public import Mathlib.MeasureTheory.Measure.Typeclasses.Probability

@[expose] public section

/-!
# Completed-observation limits with the actual shared cache and log

Private sampling leaves the entire incoming shared state unchanged. On
completion, the actual observation-sensitive continuation runs on that state;
on suspension, its queries are skipped and the partial observation remains.
An exact interpretation equality connects the operational program to the
joint limit construction. No native transcript-derived freshness is assumed.
-/

open OracleSpec OracleComp MeasureTheory BinaryTree
open scoped Classical

namespace FormalProof4FHE.HasteBoots.SharedCompletedContinuation

noncomputable section

variable {A Later Cfg Input Digest Payload : Type}
  [DecidableEq Input] [DecidableEq Digest] [SampleableType Digest]

local instance (X : Type) : MeasurableSpace X := ⊤
local instance (X Y : Type) : MeasurableSpace (X × Y) := ⊤

def program (step : ProbComp A) (complete : A → Prop)
    (next : A → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Later) :
    OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) (A × Option Later) := do
  let first ← PrivateSampling.embed Cfg Input Digest step
  if complete first then (fun last => (first, some last)) <$> next first
  else pure (first, none)

def pack (shape : Cfg → Skeleton)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (outcome : A × Option (Later × CheckpointExecution.State (Input := Input) (Digest := Digest) shape)) :
    (A × Option Later) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape :=
  match outcome.2 with
  | none => ((outcome.1, none), initial)
  | some last => ((outcome.1, some last.1), last.2)

/-- Exact program interpretation retains the unchanged incoming state on
suspension and the actual final cache/log after the continuation on success. -/
theorem run_program (step : ProbComp A) (complete : A → Prop)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (next : A → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Later)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program step complete next)).run initial =
      pack shape initial <$> CompletedContinuation.program step complete
        (fun first => (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
          (next first)).run initial) := by
  rw [program, simulateQ_bind, StateT.run_bind, PrivateSampling.run_probComp, bind_map_left,
    CompletedContinuation.program, map_bind]
  congr 1
  funext first
  by_cases done : complete first
  · simp only [done, ite_true, simulateQ_map, StateT.run_map, Functor.map_map, pack]
  · simp [done, simulateQ_pure, StateT.run_pure, pack]

/-- Unbounded complete joint outcomes retain the actual shared state. -/
def measure (steps : ℕ → ProbComp A) (complete : A → Prop)
    (grows : ∀ i j, i ≤ j → CompletedObservation.LE (steps i) (steps j) complete)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (next : A → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Later)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :
    Measure ((A × Option Later) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape) :=
  @Measure.map _ _ ⊤ ⊤ (pack shape initial) (CompletedContinuation.measure steps complete grows
    (fun first => (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (next first)).run initial))

theorem measure_apply (steps : ℕ → ProbComp A) (complete : A → Prop)
    (grows : ∀ i j, i ≤ j → CompletedObservation.LE (steps i) (steps j) complete)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (next : A → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Later)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (event : (A × Option Later) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape → Prop) :
    measure steps complete grows enc dummy shape next initial {outcome | event outcome} =
      ⨆ n, Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
        (program (steps n) complete next)).run initial}[outcome.1.2 ≠ none ∧ event outcome] := by
  rw [measure, Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete,
    CompletedContinuation.measure, CompletedObservationLimit.measure_apply]
  apply iSup_congr
  intro n
  rw [run_program, prEvent_map]
  apply prEvent_congr
  intro outcome
  cases tag : outcome.2 <;> simp [pack, CompletedContinuation.finished, tag]

/-- The actual shared continuation preserves every event on the earlier
complete raw observation, while its final cache/log remain in the joint law. -/
theorem earlier_marginal (steps : ℕ → ProbComp A) (complete : A → Prop)
    (grows : ∀ i j, i ≤ j → CompletedObservation.LE (steps i) (steps j) complete)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (next : A → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Later)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (event : A → Prop) :
    measure steps complete grows enc dummy shape next initial {outcome | event outcome.1.1} =
      CompletedObservationLimit.measure steps complete grows {first | event first} := by
  rw [measure, Measure.map_apply Measurable.of_discrete MeasurableSet.of_discrete]
  have same : (fun outcome => event (pack (Later := Later) shape initial outcome).1.1) =
      (fun outcome => event outcome.1) := by
    funext outcome
    cases tag : outcome.2 <;> simp [pack, tag]
  change CompletedContinuation.measure steps complete grows _
    {outcome | event (pack (Later := Later) shape initial outcome).1.1} = _
  rw [same]
  exact CompletedContinuation.earlier_marginal _ _ _ _ _

/-- All mass is on completed sampling followed by the real shared continuation. -/
theorem probability (steps : ℕ → ProbComp A) (complete : A → Prop)
    (grows : ∀ i j, i ≤ j → CompletedObservation.LE (steps i) (steps j) complete)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (next : A → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Later)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (total : (⨆ n, Pr{let value ← steps n}[complete value]) = 1) :
    IsProbabilityMeasure (measure steps complete grows enc dummy shape next initial) := by
  unfold measure
  apply (Measure.isProbabilityMeasure_map_iff (Measurable.of_discrete : Measurable (pack shape initial)).aemeasurable).mpr
  exact CompletedContinuation.probability _ _ _ _ total

/-- Any uniform bound proved for the actual finite shared executions passes
to this full observation/state measure; no oracle query cap is introduced. -/
theorem event_bound (steps : ℕ → ProbComp A) (complete : A → Prop)
    (grows : ∀ i j, i ≤ j → CompletedObservation.LE (steps i) (steps j) complete)
    (enc : MerkleOracle.Encoding Input Digest Payload) (dummy : Digest) (shape : Cfg → Skeleton)
    (next : A → OracleComp (CheckpointExecution.Spec unifSpec Cfg Input Digest) Later)
    (initial : CheckpointExecution.State (Input := Input) (Digest := Digest) shape)
    (event : (A × Option Later) × CheckpointExecution.State (Input := Input) (Digest := Digest) shape → Prop)
    (epsilon : ENNReal)
    (bounded : ∀ n, Pr{let outcome ← (simulateQ (CheckpointExecution.handler (QueryImpl.ofLift unifSpec ProbComp) enc dummy shape)
      (program (steps n) complete next)).run initial}[outcome.1.2 ≠ none ∧ event outcome] ≤ epsilon) :
    measure steps complete grows enc dummy shape next initial {outcome | event outcome} ≤ epsilon := by
  rw [measure_apply]
  exact iSup_le bounded

end

end FormalProof4FHE.HasteBoots.SharedCompletedContinuation
