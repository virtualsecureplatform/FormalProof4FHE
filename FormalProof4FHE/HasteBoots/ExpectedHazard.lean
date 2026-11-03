module

public import VCVio.OracleComp.QueryTracking.ExpectedQueryCount

@[expose] public section

/-!
# Accumulating state-dependent hazards without a query cutoff

The implementation, full state and successful/failed return values are shared
between the terminal event and the charge. A query contributes its charge
before its continuation, so a returned failure does not erase preceding work.
No pathwise query budget is assumed. Concrete Merkle/transcript handlers must
still prove their one-step drift bound and relate the resulting charge to work.
-/

open OracleSpec OracleComp MeasureTheory

namespace FormalProof4FHE.HasteBoots.ExpectedHazard

noncomputable section

variable {ι : Type} {spec : OracleSpec ι} {State Result : Type}

/-- Expected sum of state-dependent charges along the actual interpreted run. -/
def charge (impl : QueryImpl spec (StateT State ProbComp))
    (loss : spec.Domain → State → ENNReal) (program : OracleComp spec Result) (state : State) : ENNReal :=
  OracleComp.recOn (motive := fun _ => State → ENNReal) program (fun _ _ => 0)
    (fun query _ tail current => loss query current +
      ∫⁻ value, value ∂𝒟[(fun next => tail next.1 next.2) <$> (impl query).run current]) state

@[simp] theorem charge_pure (impl : QueryImpl spec (StateT State ProbComp))
    (loss : spec.Domain → State → ENNReal) (result : Result) (state : State) :
    charge impl loss (pure result) state = 0 := rfl

@[simp] theorem charge_query_bind (impl : QueryImpl spec (StateT State ProbComp))
    (loss : spec.Domain → State → ENNReal) (query : spec.Domain)
    (next : spec.Range query → OracleComp spec Result) (state : State) :
    charge impl loss (liftM (spec.query query) >>= next) state = loss query state +
      ∫⁻ value, value ∂𝒟[(fun outcome => charge impl loss (next outcome.1) outcome.2) <$>
        (impl query).run state] := rfl

/-- An additive one-step drift bound telescopes over the entire execution.
The hazard may depend on the complete state visible before each response. -/
theorem terminal_risk_le (impl : QueryImpl spec (StateT State ProbComp))
    (loss : spec.Domain → State → ENNReal) (risk : State → ENNReal)
    (step : ∀ query state, ∫⁻ value, value ∂𝒟[(fun outcome => risk outcome.2) <$> (impl query).run state] ≤
      risk state + loss query state)
    (program : OracleComp spec Result) (state : State) :
    ∫⁻ value, value ∂𝒟[(fun outcome => risk outcome.2) <$> (simulateQ impl program).run state] ≤
      risk state + charge impl loss program state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure result =>
    simp only [simulateQ_pure, StateT.run_pure, map_pure, evalDist_pure, lintegral_dirac,
      charge_pure, add_zero, le_refl]
  | query_bind query next ih =>
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind, lintegral_id_evalDist_map_bind,
      charge_query_bind]
    calc _ ≤ ∫⁻ value, value ∂𝒟[(fun outcome => risk outcome.2 +
          charge impl loss (next outcome.1) outcome.2) <$> (impl query).run state] :=
          lintegral_id_evalDist_map_mono _ (fun outcome => ih outcome.1 outcome.2)
         _ = (∫⁻ value, value ∂𝒟[(fun outcome => risk outcome.2) <$> (impl query).run state]) +
          ∫⁻ value, value ∂𝒟[(fun outcome => charge impl loss (next outcome.1) outcome.2) <$>
            (impl query).run state] := lintegral_id_evalDist_map_add _ _ _
         _ ≤ (risk state + loss query state) +
          ∫⁻ value, value ∂𝒟[(fun outcome => charge impl loss (next outcome.1) outcome.2) <$>
            (impl query).run state] := add_le_add (step query state) le_rfl
         _ = _ := add_assoc _ _ _

/-- Markov form of unrestricted hazard accumulation for any terminal bad event. -/
theorem terminal_event_le (impl : QueryImpl spec (StateT State ProbComp))
    (loss : spec.Domain → State → ENNReal) (risk : State → ENNReal)
    (step : ∀ query state, ∫⁻ value, value ∂𝒟[(fun outcome => risk outcome.2) <$> (impl query).run state] ≤
      risk state + loss query state)
    (bad : Result × State → Prop) (dominates : ∀ outcome, bad outcome → 1 ≤ risk outcome.2)
    (program : OracleComp spec Result) (state : State) :
    Pr{let outcome ← (simulateQ impl program).run state}[bad outcome] ≤
      risk state + charge impl loss program state :=
  (prEvent_le_lintegral_id_evalDist_map _ dominates).trans (terminal_risk_le impl loss risk step program state)

/-- Indicator risk for failure of a state invariant is its actual probability. -/
theorem failure_risk_eq {Output : Type} (computation : ProbComp (Output × State))
    (good : State → Prop) :
    (∫⁻ value, value ∂𝒟[(fun outcome =>
      {state | ¬good state}.indicator (fun _ => (1 : ENNReal)) outcome.2) <$> computation]) =
      Pr{let outcome ← computation}[¬good outcome.2] := by
  classical
  let _ : MeasurableSpace (Output × State) := ⊤
  rw [lintegral_id_evalDist_map, prEvent_eq_evalDist_of_discrete]
  change (∫⁻ outcome, {outcome : Output × State | ¬good outcome.2}.indicator
    (fun _ => (1 : ENNReal)) outcome ∂𝒟[computation]) = _
  rw [lintegral_indicator_const MeasurableSet.of_discrete, one_mul]

/-- Conditional failure bounds accumulate from a good initial state, with
state-dependent losses and no maximum number of queries. -/
theorem terminal_failure_le_charge (impl : QueryImpl spec (StateT State ProbComp))
    (loss : spec.Domain → State → ENNReal) (good : State → Prop)
    (step : ∀ query state, good state →
      Pr{let outcome ← (impl query).run state}[¬good outcome.2] ≤ loss query state)
    (program : OracleComp spec Result) (state : State) (initial : good state) :
    Pr{let outcome ← (simulateQ impl program).run state}[¬good outcome.2] ≤
      charge impl loss program state := by
  classical
  let risk : State → ENNReal := {state | ¬good state}.indicator (fun _ => 1)
  have drift : ∀ query state,
      (∫⁻ value, value ∂𝒟[(fun outcome => risk outcome.2) <$> (impl query).run state]) ≤
        risk state + loss query state := by
    intro query current
    rw [failure_risk_eq]
    by_cases valid : good current
    · simpa only [risk, Set.indicator_of_notMem (show current ∉ {state | ¬good state} from
        fun invalid => invalid valid), zero_add] using step query current valid
    · have one : risk current = 1 := Set.indicator_of_mem valid _
      rw [one]
      exact (prEvent_le_one _).trans (le_add_right le_rfl)
  have bound := terminal_risk_le impl loss risk drift program state
  rw [failure_risk_eq] at bound
  have zero : risk state = 0 := Set.indicator_of_notMem (show state ∉ {state | ¬good state} from fun invalid => invalid initial) _
  simpa only [zero, zero_add] using bound

/-- Constant charges on selected query kinds are exactly VCVio's expected
charged-query count, with the very same interpreter and initial state. -/
theorem charge_const_eq_expected_count (impl : QueryImpl spec (StateT State ProbComp))
    (charged : spec.Domain → Prop) [DecidablePred charged] (coefficient : ENNReal)
    (program : OracleComp spec Result) (state : State) :
    charge impl (fun query _ => if charged query then coefficient else 0) program state =
      coefficient * expectedSimulatedQueryCount impl charged program state := by
  induction program using OracleComp.inductionOn generalizing state with
  | pure result => simp only [charge_pure, expectedSimulatedQueryCount_pure, mul_zero]
  | query_bind query next ih =>
    rw [charge_query_bind, expectedSimulatedQueryCount_query_bind]
    simp only [ih]
    have scaled :
        (∫⁻ value, value ∂𝒟[(fun outcome => coefficient *
          expectedSimulatedQueryCount impl charged (next outcome.1) outcome.2) <$> (impl query).run state]) =
        coefficient * ∫⁻ value, value ∂𝒟[(fun outcome =>
          expectedSimulatedQueryCount impl charged (next outcome.1) outcome.2) <$> (impl query).run state] := by
      let : MeasurableSpace (spec.Range query × State) := ⊤
      rw [lintegral_id_evalDist_map, lintegral_id_evalDist_map]
      exact lintegral_const_mul coefficient Measurable.of_discrete
    rw [scaled, mul_add]
    by_cases counted : charged query <;> simp only [counted, reduceIte, mul_one, mul_zero]

/-- Unrestricted expected-count corollary from a good initial state. There is
no maximum query count and no discarded failure or long-running return branch. -/
theorem terminal_event_le_mul_expected_count (impl : QueryImpl spec (StateT State ProbComp))
    (charged : spec.Domain → Prop) [DecidablePred charged] (coefficient : ENNReal)
    (risk : State → ENNReal)
    (step : ∀ query state, ∫⁻ value, value ∂𝒟[(fun outcome => risk outcome.2) <$> (impl query).run state] ≤
      risk state + if charged query then coefficient else 0)
    (bad : Result × State → Prop) (dominates : ∀ outcome, bad outcome → 1 ≤ risk outcome.2)
    (program : OracleComp spec Result) (state : State) (initial : risk state = 0) :
    Pr{let outcome ← (simulateQ impl program).run state}[bad outcome] ≤
      coefficient * expectedSimulatedQueryCount impl charged program state := by
  have bound := terminal_event_le impl (fun query _ => if charged query then coefficient else 0)
    risk step bad dominates program state
  rwa [initial, zero_add, charge_const_eq_expected_count] at bound

end

end FormalProof4FHE.HasteBoots.ExpectedHazard
