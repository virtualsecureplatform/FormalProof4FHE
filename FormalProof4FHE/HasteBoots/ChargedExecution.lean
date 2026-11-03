module

public import FormalProof4FHE.HasteBoots.ExpectedHazard

@[expose] public section

/-!
# Actual pathwise charge recording

The instrumented interpreter executes the same query handler, records its
actual next state, and adds the charge from before that query's answer.
Erasure recovers the exact original execution. The terminal recorded charge
has expectation equal to the recursive whole-run charge, even when it is
infinite. This is instrumentation, not a query-budget assumption.
-/

open OracleSpec OracleComp MeasureTheory

namespace FormalProof4FHE.HasteBoots.ChargedExecution

noncomputable section

variable {ι : Type} {spec : OracleSpec ι} {State Result : Type}

/-- Charge is assessed on the pre-response state and kept on every return. -/
def handler (impl : QueryImpl spec (StateT State ProbComp))
    (loss : spec.Domain → State → ENNReal) : QueryImpl spec (StateT (State × ENNReal) ProbComp) :=
  fun query current => (fun outcome => (outcome.1, (outcome.2, current.2 + loss query current.1))) <$>
    (impl query).run current.1

/-- Exact query semantics, including the pre-response assessment time. -/
theorem run_handler (impl : QueryImpl spec (StateT State ProbComp))
    (loss : spec.Domain → State → ENNReal) (query : spec.Domain) (current : State × ENNReal) :
    (handler impl loss query).run current =
      (fun outcome => (outcome.1, (outcome.2, current.2 + loss query current.1))) <$>
        (impl query).run current.1 := rfl

/-- The full result and original state are unchanged by recording work. -/
theorem erase (impl : QueryImpl spec (StateT State ProbComp))
    (loss : spec.Domain → State → ENNReal) (program : OracleComp spec Result)
    (initial : State) (spent : ENNReal) :
    (fun outcome => (outcome.1, outcome.2.1)) <$>
      (simulateQ (handler impl loss) program).run (initial, spent) =
      (simulateQ impl program).run initial := by
  induction program using OracleComp.inductionOn generalizing initial spent with
  | pure result => simp only [simulateQ_pure, StateT.run_pure, map_pure]
  | query_bind query next ih =>
    simp only [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, run_handler, bind_map_left,
      map_bind]
    congr 1
    funext outcome
    exact ih outcome.1 outcome.2 (spent + loss query initial)

/-- The terminal account's expectation equals the whole recursive expected
charge plus its initial account. No finiteness or independence is assumed. -/
theorem expected (impl : QueryImpl spec (StateT State ProbComp))
    (loss : spec.Domain → State → ENNReal) (program : OracleComp spec Result)
    (initial : State) (spent : ENNReal) :
    (∫⁻ value, value ∂𝒟[(fun outcome => outcome.2.2) <$>
      (simulateQ (handler impl loss) program).run (initial, spent)]) =
      spent + ExpectedHazard.charge impl loss program initial := by
  induction program using OracleComp.inductionOn generalizing initial spent with
  | pure result =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure, evalDist_pure, lintegral_dirac,
      ExpectedHazard.charge_pure, add_zero]
  | query_bind query next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, lintegral_id_evalDist_map_bind]
    simp only [run_handler, Functor.map_map, ih]
    rw [lintegral_id_evalDist_map_add, OracleComp.evalDist_map_const, lintegral_dirac,
      ExpectedHazard.charge_query_bind, add_assoc]

/-- Starting at zero identifies the expected recorded cost exactly with the
existing charge used by the native false-acceptance theorem. -/
theorem expected_zero (impl : QueryImpl spec (StateT State ProbComp))
    (loss : spec.Domain → State → ENNReal) (program : OracleComp spec Result) (initial : State) :
    (∫⁻ value, value ∂𝒟[(fun outcome => outcome.2.2) <$>
      (simulateQ (handler impl loss) program).run (initial, 0)]) =
      ExpectedHazard.charge impl loss program initial := by
  simpa only [zero_add] using expected impl loss program initial 0

/-- Every event on the real result/state retains its original probability. -/
theorem event (impl : QueryImpl spec (StateT State ProbComp))
    (loss : spec.Domain → State → ENNReal) (program : OracleComp spec Result)
    (initial : State) (spent : ENNReal) (accepted : Result × State → Prop) :
    Pr{let outcome ← (simulateQ (handler impl loss) program).run (initial, spent)}[accepted (outcome.1, outcome.2.1)] =
      Pr{let outcome ← (simulateQ impl program).run initial}[accepted outcome] := by
  rw [← erase impl loss program initial spent, prEvent_map]

end

end FormalProof4FHE.HasteBoots.ChargedExecution
