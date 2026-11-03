module

public import FormalProof4FHE.HasteBoots.OptionalRejectionLoop

@[expose] public section

/-!
# Work of completed-candidate rejection with partial inner trials

The work observation sums every retained trial, including a partially
completed last field sample. Only a completed rejected value starts another
trial. Cost/value independence is not assumed: the head's work is always
charged before its completion and acceptance conditions are considered.
-/

open OracleSpec OracleComp MeasureTheory
open scoped Classical BigOperators
open FormalProof4FHE.HasteBoots.OptionalRejectionLoop

namespace FormalProof4FHE.HasteBoots.OptionalRejectionWork

noncomputable section

variable {A Observation : Type}

private theorem expected_const {B : Type} (program : ProbComp B) (cost : ENNReal) :
    (∫⁻ value, value ∂𝒟[(fun _ => cost) <$> program]) = cost := by
  let _ : MeasurableSpace B := ⊤
  rw [lintegral_id_evalDist_map]
  simp

private theorem expected_ite {B : Type} (program : ProbComp B) (event : B → Prop) [DecidablePred event] (cost : ENNReal) :
    (∫⁻ value, value ∂𝒟[(fun value => if event value then cost else 0) <$> program]) =
      Pr{let value ← program}[event value] * cost := by
  let _ : MeasurableSpace B := ⊤
  rw [lintegral_id_evalDist_map, prEvent_eq_evalDist_of_discrete]
  have same : (fun value => if event value then cost else 0) = {value | event value}.indicator (fun _ => cost) := by
    funext value
    by_cases present : event value <;> simp [present, Set.indicator]
  rw [same, lintegral_indicator_const MeasurableSet.of_discrete, mul_comm]

def consumed (cost : Observation → ℕ) (result : Result A Observation) : ℕ := (result.trials.map cost).sum

theorem consumed_cons (cost : Observation → ℕ) (first : Observation) (tail : Result A Observation) :
    consumed cost (cons first tail) = cost first + consumed cost tail := by simp [consumed, cons]

def headCost (step : ProbComp Observation) (cost : Observation → ℕ) : ENNReal :=
  ∫⁻ value, value ∂𝒟[(fun first => (cost first : ENNReal)) <$> step]

def expectedCost (step : ProbComp Observation) (candidate : Observation → Option A) (accept : A → Prop)
    [DecidablePred accept] (cost : Observation → ℕ) (fuel : ℕ) : ENNReal :=
  ∫⁻ value, value ∂𝒟[(fun result => (consumed cost result : ENNReal)) <$> program step candidate accept fuel]

theorem expectedCost_zero (step : ProbComp Observation) (candidate : Observation → Option A) (accept : A → Prop)
    [DecidablePred accept] (cost : Observation → ℕ) : expectedCost step candidate accept cost 0 = 0 := by
  simp [expectedCost, program, consumed, evalDist_pure]

/-- Every head incurs its real work. Inner suspension does not masquerade as
a rejected candidate and therefore does not start another trial. -/
theorem expectedCost_succ_raw (step : ProbComp Observation) (candidate : Observation → Option A) (accept : A → Prop)
    [DecidablePred accept] (cost : Observation → ℕ) (fuel : ℕ) :
    expectedCost step candidate accept cost (fuel + 1) = headCost step cost +
      Pr{let first ← step}[(candidate first).elim False (fun value => ¬accept value)] * expectedCost step candidate accept cost fuel := by
  rw [expectedCost, program, lintegral_id_evalDist_map_bind]
  have point : ∀ first : Observation,
      (∫⁻ value, value ∂𝒟[(fun result : Result A Observation => (consumed cost result : ENNReal)) <$>
        (match candidate first with
         | none => pure (⟨none, [first]⟩ : Result A Observation)
         | some value => if accept value then pure (⟨some value, [first]⟩ : Result A Observation)
                         else cons first <$> program step candidate accept fuel)]) =
      (cost first : ENNReal) + if (candidate first).elim False (fun value => ¬accept value)
        then expectedCost step candidate accept cost fuel else 0 := by
    intro first
    cases candidate first with
    | none => simp [consumed, evalDist_pure]
    | some value =>
      by_cases allowed : accept value
      · simp [allowed, consumed, evalDist_pure]
      · simp only [allowed, ite_false, Functor.map_map]
        have splitCost : (fun tail : Result A Observation => (consumed cost (cons first tail) : ENNReal)) =
            (fun tail => (cost first : ENNReal) + (consumed cost tail : ENNReal)) := by
          funext tail
          rw [consumed_cons, Nat.cast_add]
        rw [splitCost, lintegral_id_evalDist_map_add, expected_const]
        simp [expectedCost, allowed]
  have observed := congrArg (fun observation : Observation → ENNReal =>
    ∫⁻ value, value ∂𝒟[observation <$> step]) (funext point)
  refine observed.trans ?_
  rw [lintegral_id_evalDist_map_add, expected_ite]
  rfl

variable [Fintype A] [SampleableType A]

theorem expectedCost_succ (step : ProbComp Observation) (candidate : Observation → Option A) (completion : ENNReal)
    (law : ∀ event : A → Prop,
      Pr{let first ← step}[(candidate first).elim False event] = completion * Pr{let value ← $ᵗ A}[event value])
    (accept : A → Prop) [DecidablePred accept] (cost : Observation → ℕ) (fuel : ℕ) :
    expectedCost step candidate accept cost (fuel + 1) = headCost step cost +
      (completion * RejectionSampling.reject (accepted accept)) * expectedCost step candidate accept cost fuel := by
  rw [expectedCost_succ_raw, law]
  have same : Pr{let value ← $ᵗ A}[¬accept value] = RejectionSampling.reject (accepted accept) := by
    unfold RejectionSampling.reject
    apply prEvent_congr
    intro value
    simp [accepted]
  rw [same]

/-- Exact work of every finite nested approximation, including inner
suspension and completed rejected candidates, without conditioning on success. -/
theorem expectedCost_formula (step : ProbComp Observation) (candidate : Observation → Option A) (completion : ENNReal)
    (law : ∀ event : A → Prop,
      Pr{let first ← step}[(candidate first).elim False event] = completion * Pr{let value ← $ᵗ A}[event value])
    (accept : A → Prop) [DecidablePred accept] (cost : Observation → ℕ) (fuel : ℕ) :
    expectedCost step candidate accept cost fuel = headCost step cost *
      (∑ attempt ∈ Finset.range fuel, (completion * RejectionSampling.reject (accepted accept)) ^ attempt) := by
  induction fuel with
  | zero => simp [expectedCost_zero]
  | succ fuel ih =>
    rw [expectedCost_succ step candidate completion law, ih, Finset.sum_range_succ']
    simp only [pow_zero, pow_succ', mul_add, mul_one]
    rw [← Finset.mul_sum]
    ac_rfl

end

end FormalProof4FHE.HasteBoots.OptionalRejectionWork
