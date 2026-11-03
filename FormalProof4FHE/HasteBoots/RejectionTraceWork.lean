module

public import FormalProof4FHE.HasteBoots.CompletedCostTransfer
public import FormalProof4FHE.HasteBoots.RejectionTraceOrder
public import Mathlib.Analysis.SpecificLimits.Normed

@[expose] public section

/-!
# Expected work in the actual unbounded completed rejection trace

Every suspended prefix has spent exactly its depth in raw trials. Its work
mean is therefore n times the exact rejection probability to the nth power.
This term vanishes for a nonempty accepted domain, identifying the mean of
the completed trace law with the previously derived unconditional mean.
No native retry cap, empirical maximum or accepted-value substitution occurs.
-/

open OracleSpec OracleComp MeasureTheory
open scoped Classical

namespace FormalProof4FHE.HasteBoots.RejectionTraceWork

noncomputable section

variable {A : Type} [DecidableEq A] [Fintype A] [SampleableType A]
local instance : MeasurableSpace (RejectionSampling.Result A) := ⊤

omit [Fintype A] in
/-- Every finite operational approximation has its derived depth bound. This
is not a maximum retry count for the native unbounded sampler. -/
theorem length_le (accepted : Finset A) (fuel : ℕ) (result : RejectionSampling.Result A)
    (supported : result ∈ support (RejectionSampling.runPrefix accepted fuel)) : result.2.length ≤ fuel := by
  induction fuel generalizing result with
  | zero =>
    simp only [RejectionSampling.runPrefix, support_pure, Set.mem_singleton_iff] at supported
    subst result
    exact le_rfl
  | succ fuel ih =>
    simp only [RejectionSampling.runPrefix, support_bind, Set.mem_iUnion] at supported
    obtain ⟨first, _, branch⟩ := supported
    by_cases member : first ∈ accepted
    · simp only [member, ite_true, support_pure, Set.mem_singleton_iff] at branch
      subst result
      exact Nat.succ_le_succ (Nat.zero_le fuel)
    · simp only [member, ite_false, support_map, Set.mem_image] at branch
      obtain ⟨tail, reached, equal⟩ := branch
      subst result
      exact Nat.succ_le_succ (ih tail reached)

omit [Fintype A] in
/-- All rejected draws remain in the trace when an operational prefix suspends. -/
theorem suspended_length (accepted : Finset A) (fuel : ℕ) (result : RejectionSampling.Result A)
    (supported : result ∈ support (RejectionSampling.runPrefix accepted fuel)) (suspended : result.1 = none) :
    result.2.length = fuel := by
  induction fuel generalizing result with
  | zero =>
    simp only [RejectionSampling.runPrefix, support_pure, Set.mem_singleton_iff] at supported
    subst result
    rfl
  | succ fuel ih =>
    simp only [RejectionSampling.runPrefix, support_bind, Set.mem_iUnion] at supported
    obtain ⟨first, _, branch⟩ := supported
    by_cases member : first ∈ accepted
    · simp only [member, ite_true, support_pure, Set.mem_singleton_iff] at branch
      subst result
      simp at suspended
    · simp only [member, ite_false, support_map, Set.mem_image] at branch
      obtain ⟨tail, reached, equal⟩ := branch
      subst result
      simp only [List.length_cons]
      exact congrArg (· + 1) (ih tail reached suspended)

omit [Fintype A] in
/-- Exact unfinished-work mean retains every rejected candidate. -/
theorem partial_mean (accepted : Finset A) (fuel : ℕ) :
    (∫⁻ value, value ∂𝒟[(fun result : RejectionSampling.Result A =>
      if RejectionTraceOrder.complete result then 0 else (result.2.length : ENNReal)) <$>
        RejectionSampling.runPrefix accepted fuel]) =
      (fuel : ENNReal) * RejectionSampling.reject accepted ^ fuel := by
  have supported : (∫⁻ value, value ∂𝒟[(fun result : RejectionSampling.Result A =>
        if RejectionTraceOrder.complete result then 0 else (result.2.length : ENNReal)) <$>
          RejectionSampling.runPrefix accepted fuel]) =
      ∫⁻ value, value ∂𝒟[(fun result : RejectionSampling.Result A =>
        if result.1 = none then (fuel : ENNReal) else 0) <$> RejectionSampling.runPrefix accepted fuel] := by
    rw [lintegral_id_evalDist_map, lintegral_id_evalDist_map]
    apply lintegral_congr_ae
    exact (evalDist_ae_mem_support (RejectionSampling.runPrefix accepted fuel)).mono (fun result reached => by
      by_cases suspended : result.1 = none
      · simp [RejectionTraceOrder.complete, suspended, suspended_length accepted fuel result reached suspended]
      · simp [RejectionTraceOrder.complete, suspended])
  rw [supported, CompletedCostTransfer.indicator (RejectionSampling.runPrefix accepted fuel)
    (fun result => result.1 = none) (fuel : ENNReal), RejectionSampling.suspended_probability, mul_comm]

/-- Polynomial/geometric decay is a work-tail argument, stronger than mere
vanishing suspension probability. The scalar may be zero. -/
theorem geometric_tail (rho : ENNReal) (small : rho < 1) :
    Filter.Tendsto (fun n : ℕ => (n : ENNReal) * rho ^ n) Filter.atTop (nhds 0) := by
  have finite : rho ≠ ⊤ := ne_of_lt (small.trans (by simp))
  have real_small : rho.toReal < 1 := by
    simpa only [ENNReal.toReal_one] using (ENNReal.toReal_lt_toReal finite ENNReal.one_ne_top).mpr small
  have real_limit := tendsto_self_mul_const_pow_of_lt_one ENNReal.toReal_nonneg real_small
  have lifted := ENNReal.tendsto_ofReal real_limit
  simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal finite, ENNReal.ofReal_zero] using lifted

omit [Fintype A] in
/-- The actual incomplete-prefix work tends to zero on a nonempty domain. -/
theorem partial_tends_zero (accepted : Finset A) (nonempty : accepted.Nonempty) :
    Filter.Tendsto (fun fuel => ∫⁻ value, value ∂𝒟[(fun result : RejectionSampling.Result A =>
      if RejectionTraceOrder.complete result then 0 else (result.2.length : ENNReal)) <$>
        RejectionSampling.runPrefix accepted fuel]) Filter.atTop (nhds 0) := by
  simp_rw [partial_mean]
  exact geometric_tail _ (RejectionSampling.reject_lt_one accepted nonempty)

/-- Completed raw trace law built from all real operational depths. -/
def measure (accepted : Finset A) : Measure (RejectionSampling.Result A) :=
  CompletedObservationLimit.measure (RejectionSampling.runPrefix accepted) RejectionTraceOrder.complete
    (fun _ _ h => RejectionTraceOrder.monotone accepted h)

omit [Fintype A] in
/-- An empty accepted domain has no completed trace mass. Its unconditional
work must therefore not be substituted for the completed mean. -/
theorem empty_measure : measure (∅ : Finset A) = 0 := by
  apply Measure.ext
  intro event _
  rw [measure, CompletedObservationLimit.measure_apply]
  change _ = (0 : ENNReal)
  apply le_antisymm
  · apply iSup_le
    intro fuel
    apply le_of_eq
    apply (prEvent_eq_zero_iff _ _).mpr
    rintro result reached ⟨done, _⟩
    cases tag : result.1 with
    | none => exact done tag
    | some candidate =>
      have member := RejectionSampling.returned_mem (∅ : Finset A) fuel result reached candidate tag
      simp at member
  · exact bot_le

/-- The completed trace has the exact unconditional rejection-work mean,
because its missing unfinished-work contribution was proved to vanish. -/
theorem expected (accepted : Finset A) (nonempty : accepted.Nonempty) :
    (∫⁻ result, (result.2.length : ENNReal) ∂measure accepted) =
      (Fintype.card A : ENNReal) / accepted.card := by
  apply CompletedCostTransfer.of_partial_tends_zero
  · exact RejectionSampling.expectedAttempts_tends_to_fraction accepted
  · exact partial_tends_zero accepted nonempty

/-- Actual accepted-domain completion makes the trace measure normalized. -/
theorem probability (accepted : Finset A) (nonempty : accepted.Nonempty) :
    IsProbabilityMeasure (measure accepted) := by
  apply CompletedObservationLimit.probability
  have finite (n : ℕ) : Pr{let result ← RejectionSampling.runPrefix accepted n}[RejectionTraceOrder.complete result] =
      Pr{let result ← RejectionSampling.runPrefix accepted n}[result.1.elim False (fun _ => True)] := by
    apply prEvent_congr
    intro result
    cases tag : result.1 <;> simp [RejectionTraceOrder.complete, tag]
  simp_rw [finite]
  have tends := RejectionSampling.success_tends_to_uniform accepted (fun _ => True)
  have total : Pr{let value ← ($ accepted : OptionT ProbComp A)}[True] = 1 := by
    rw [ProbComp.prEvent_uniformSelectFinset]
    simp only [Finset.filter_true]
    exact ENNReal.div_self (by exact_mod_cast (Finset.card_pos.mpr nonempty).ne') (by simp)
  rw [total] at tends
  exact tendsto_nhds_unique (tendsto_atTop_iSup (RejectionSampling.success_monotone accepted (fun _ => True))) tends

end

end FormalProof4FHE.HasteBoots.RejectionTraceWork
