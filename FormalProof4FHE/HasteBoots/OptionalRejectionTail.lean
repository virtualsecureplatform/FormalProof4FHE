module

public import FormalProof4FHE.HasteBoots.OptionalRejectionWork
public import FormalProof4FHE.HasteBoots.CompletedCostTransfer

@[expose] public section

/-!
# Derived support and suspension bounds for nested rejection prefixes

An incomplete inner trial stops immediately. Only a completed rejected trial
continues. The resulting suspension bound separates inner suspension from
exhausting the outer analysis prefix, while retaining every issued trial.
-/

open OracleSpec OracleComp MeasureTheory
open scoped Classical
open FormalProof4FHE.HasteBoots.OptionalRejectionLoop

namespace FormalProof4FHE.HasteBoots.OptionalRejectionTail

noncomputable section

variable {A Observation : Type}
local instance : MeasurableSpace Observation := ⊤

/-- A bound on each supported trial gives a derived bound for the finite
prefix's full work, including a partially completed last trial. -/
theorem consumed_le (step : ProbComp Observation) (candidate : Observation → Option A)
    (accept : A → Prop) [DecidablePred accept] (cost : Observation → ℕ) (budget : ℕ)
    (head_le : ∀ first ∈ support step, cost first ≤ budget) (fuel : ℕ) (result : Result A Observation)
    (supported : result ∈ support (program step candidate accept fuel)) :
    OptionalRejectionWork.consumed cost result ≤ budget * fuel := by
  induction fuel generalizing result with
  | zero =>
    simp only [program, support_pure, Set.mem_singleton_iff] at supported
    subst result
    simp [OptionalRejectionWork.consumed]
  | succ fuel ih =>
    simp only [program, support_bind, Set.mem_iUnion] at supported
    obtain ⟨first, reached, branch⟩ := supported
    have head := head_le first reached
    cases tag : candidate first with
    | none =>
      simp only [tag, support_pure, Set.mem_singleton_iff] at branch
      subst result
      simpa only [OptionalRejectionWork.consumed, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, add_zero] using head.trans (by rw [Nat.mul_succ]; omega)
    | some value =>
      by_cases allowed : accept value
      · simp only [tag, allowed, ite_true, support_pure, Set.mem_singleton_iff] at branch
        subst result
        simpa only [OptionalRejectionWork.consumed, List.map_cons, List.map_nil, List.sum_cons,
          List.sum_nil, add_zero] using head.trans (by rw [Nat.mul_succ]; omega)
      · simp only [tag, allowed, ite_false, support_map, Set.mem_image] at branch
        obtain ⟨tail, tail_reached, equal⟩ := branch
        subst result
        rw [OptionalRejectionWork.consumed_cons, Nat.mul_succ]
        exact (Nat.add_le_add head (ih tail tail_reached)).trans_eq (Nat.add_comm _ _)

/-- Exact failure recurrence from the real optional control flow. -/
theorem suspended_succ (step : ProbComp Observation) (candidate : Observation → Option A)
    (accept : A → Prop) [DecidablePred accept] (fuel : ℕ) :
    Pr{let result ← program step candidate accept (fuel + 1)}[result.value = none] =
      Pr{let first ← step}[candidate first = none] +
        Pr{let first ← step}[(candidate first).elim False (fun value => ¬accept value)] *
          Pr{let result ← program step candidate accept fuel}[result.value = none] := by
  rw [program, prEvent_bind_eq_lintegral_of_discrete]
  have point (first : Observation) :
      Pr{let result ← (match candidate first with
        | none => pure (⟨none, [first]⟩ : Result A Observation)
        | some value => if accept value then pure (⟨some value, [first]⟩ : Result A Observation)
          else cons first <$> program step candidate accept fuel)}[result.value = none] =
        (if candidate first = none then (1 : ENNReal) else 0) +
          (if (candidate first).elim False (fun value => ¬accept value) then
            Pr{let result ← program step candidate accept fuel}[result.value = none] else 0) := by
    cases tag : candidate first with
    | none => simp
    | some value =>
      by_cases allowed : accept value
      · simp [allowed]
      · simp [allowed, cons]
  have observed := congrArg (fun observation : Observation → ENNReal => ∫⁻ first, observation first ∂𝒟[step]) (funext point)
  refine observed.trans ?_
  rw [lintegral_add_left Measurable.of_discrete]
  have left := CompletedCostTransfer.indicator step (fun first => candidate first = none) 1
  have right := CompletedCostTransfer.indicator step
    (fun first => (candidate first).elim False (fun value => ¬accept value))
    Pr{let result ← program step candidate accept fuel}[result.value = none]
  rw [lintegral_id_evalDist_map] at left right
  rw [left, right, mul_one]

/-- Inner failures accumulate at most once per outer analysis step; the
remaining term is the actual completed-rejection rate to that depth. -/
theorem suspended_le (step : ProbComp Observation) (candidate : Observation → Option A)
    (accept : A → Prop) [DecidablePred accept] (fuel : ℕ) :
    Pr{let result ← program step candidate accept fuel}[result.value = none] ≤
      (fuel : ENNReal) * Pr{let first ← step}[candidate first = none] +
        Pr{let first ← step}[(candidate first).elim False (fun value => ¬accept value)] ^ fuel := by
  induction fuel with
  | zero => simp [program]
  | succ fuel ih =>
    rw [suspended_succ]
    refine (add_le_add (le_refl Pr{let first ← step}[candidate first = none])
      (mul_le_mul' (le_refl Pr{let first ← step}[(candidate first).elim False (fun value => ¬accept value)]) ih)).trans ?_
    rw [mul_add, ← pow_succ']
    have rate_le : Pr{let first ← step}[(candidate first).elim False (fun value => ¬accept value)] ≤ 1 :=
      prEvent_le_one _
    have reduced := mul_le_of_le_one_left' rate_le
      (a := (fuel : ENNReal) * Pr{let first ← step}[candidate first = none])
    calc _ ≤ Pr{let first ← step}[candidate first = none] +
          ((fuel : ENNReal) * Pr{let first ← step}[candidate first = none] +
            Pr{let first ← step}[(candidate first).elim False (fun value => ¬accept value)] ^ (fuel + 1)) :=
            add_le_add le_rfl (add_le_add reduced le_rfl)
      _ = _ := by rw [Nat.cast_add, Nat.cast_one]; ring

end

end FormalProof4FHE.HasteBoots.OptionalRejectionTail
