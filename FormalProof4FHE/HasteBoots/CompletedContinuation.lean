module

public import FormalProof4FHE.HasteBoots.CompletedObservationLimit

@[expose] public section

/-!
# Almost-sure completed sampling followed by arbitrary adaptive work

The actual partial observation is retained on suspension and the continuation
is skipped. Completed observations start the same observation-sensitive
continuation. The limit is a probability measure on complete joint outcomes,
not a value-marginal replacement for the later execution.
-/

open OracleSpec OracleComp MeasureTheory
open scoped Classical

namespace FormalProof4FHE.HasteBoots.CompletedContinuation

noncomputable section

variable {A B : Type}
local instance : MeasurableSpace A := ⊤
local instance : MeasurableSpace (A × Option B) := ⊤

def program (step : ProbComp A) (complete : A → Prop) (next : A → ProbComp B) : ProbComp (A × Option B) := do
  let first ← step
  if complete first then (fun last => (first, some last)) <$> next first
  else pure (first, none)

def finished (outcome : A × Option B) : Prop := outcome.2 ≠ none

/-- Even a continuation which inspects every raw trace preserves the full
completed-outcome order. Every earlier completed head uses the same kernel. -/
theorem ordered {left right : ProbComp A} (complete : A → Prop) (next : A → ProbComp B)
    (grows : CompletedObservation.LE left right complete) :
    CompletedObservation.LE (program left complete next) (program right complete next) finished := by
  unfold program
  apply CompletedObservation.bind grows
  · intro value done
    simp only [done, ite_true]
    exact CompletedObservation.refl _ _
  · intro value suspended
    simp [suspended, finished, prEvent_norm]

/-- The continuation retains the original completed head event exactly;
future work is neither discarded from the program nor resampled. -/
theorem earlier_event (step : ProbComp A) (complete : A → Prop) (next : A → ProbComp B) (event : A → Prop) :
    Pr{let outcome ← program step complete next}[finished outcome ∧ event outcome.1] =
      Pr{let first ← step}[complete first ∧ event first] := by
  rw [program, prEvent_bind_eq_tsum, prEvent_eq_tsum_ite]
  apply tsum_congr
  intro first
  by_cases done : complete first <;> by_cases present : event first <;>
    simp [done, present, finished, prEvent_norm]

/-- Every completed head starts a lossless ProbComp continuation, including
runs whose computed verifier flags reject. Only sampling suspension is absent. -/
theorem completion (step : ProbComp A) (complete : A → Prop) (next : A → ProbComp B) :
    Pr{let outcome ← program step complete next}[finished outcome] = Pr{let first ← step}[complete first] := by
  simpa only [and_true] using earlier_event step complete next (fun _ => True)

/-- This measure retains both the complete head observation and the entire
later result. Its continuation may include the actual shared cache and log. -/
def measure (steps : ℕ → ProbComp A) (complete : A → Prop)
    (grows : ∀ i j, i ≤ j → CompletedObservation.LE (steps i) (steps j) complete) (next : A → ProbComp B) :
    Measure (A × Option B) :=
  CompletedObservationLimit.measure (fun n => program (steps n) complete next) finished
    (fun i j hij => ordered complete next (grows i j hij))

/-- Eventual completion gives a normalized joint measure without conditioning
on any finite prefix's completion mass. -/
theorem probability (steps : ℕ → ProbComp A) (complete : A → Prop)
    (grows : ∀ i j, i ≤ j → CompletedObservation.LE (steps i) (steps j) complete) (next : A → ProbComp B)
    (total : (⨆ n, Pr{let value ← steps n}[complete value]) = 1) :
    IsProbabilityMeasure (measure steps complete grows next) := by
  apply CompletedObservationLimit.probability
  simpa only [completion] using total

/-- Any trace-dependent joint event is the limit of its actual gated programs. -/
theorem event_tends (steps : ℕ → ProbComp A) (complete : A → Prop)
    (grows : ∀ i j, i ≤ j → CompletedObservation.LE (steps i) (steps j) complete) (next : A → ProbComp B)
    (event : A × Option B → Prop) :
    Filter.Tendsto (fun n => Pr{let outcome ← program (steps n) complete next}[finished outcome ∧ event outcome])
      Filter.atTop (nhds (measure steps complete grows next {outcome | event outcome})) :=
  CompletedObservationLimit.event_tends _ _ _ _

/-- The complete head marginal is preserved, while the actual later result
and every trace-dependent continuation choice remain in the joint measure. -/
theorem earlier_marginal (steps : ℕ → ProbComp A) (complete : A → Prop)
    (grows : ∀ i j, i ≤ j → CompletedObservation.LE (steps i) (steps j) complete) (next : A → ProbComp B)
    (event : A → Prop) :
    measure steps complete grows next {outcome | event outcome.1} =
      CompletedObservationLimit.measure steps complete grows {value | event value} := by
  rw [measure, CompletedObservationLimit.measure_apply, CompletedObservationLimit.measure_apply]
  simp only [Set.mem_ofPred_eq, earlier_event]

end

end FormalProof4FHE.HasteBoots.CompletedContinuation
