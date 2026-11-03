module

public import FormalProof4FHE.HasteBoots.ReciprocalDetection
public import VCVio.OracleComp.EvalDist.Sum
public import VCVio.EvalDist.Monad.Branch
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Topology.Order.MonotoneConvergence

@[expose] public section

/-!
# Operational prefixes of an unbounded ideal rejection loop

Every attempted candidate, including rejected candidates, is retained in the
ordered trace. Prefix length is an analysis approximation, not a protocol
retry budget. Successful-output probabilities and expected attempt counts
will be obtained from the increasing family of all prefixes. These are fresh
ideal field draws; transcript-byte sampling and hash work are separate.
-/

open OracleSpec OracleComp MeasureTheory
open scoped Classical BigOperators

namespace FormalProof4FHE.HasteBoots.RejectionSampling

noncomputable section

variable {A : Type} [DecidableEq A] [Fintype A] [SampleableType A]

abbrev Result (A : Type) := Option A × List A

/-- Execute at most an analysis prefix of the loop. `none` means suspended at
the next draw, with all attempted candidates retained, rather than rejection. -/
def runPrefix (accepted : Finset A) : ℕ → ProbComp (Result A)
  | 0 => pure (none, [])
  | fuel + 1 => do
    let candidate ← $ᵗ A
    if candidate ∈ accepted then pure (some candidate, [candidate])
    else (fun result => (result.1, candidate :: result.2)) <$> runPrefix accepted fuel

def reject (accepted : Finset A) : ENNReal := Pr{let candidate ← $ᵗ A}[candidate ∉ accepted]

def hit (accepted : Finset A) (event : A → Prop) : ENNReal :=
  Pr{let candidate ← $ᵗ A}[candidate ∈ accepted ∧ event candidate]

/-- The accepted first draw or a rejected draw followed by the real suffix.
The recurrence does not condition away any rejected attempts. -/
theorem success_succ (accepted : Finset A) (event : A → Prop) (fuel : ℕ) :
    Pr{let result ← runPrefix accepted (fuel + 1)}[result.1.elim False event] =
      hit accepted event + reject accepted * Pr{let result ← runPrefix accepted fuel}[result.1.elim False event] := by
  rw [runPrefix, prEvent_bind_eq_tsum, tsum_fintype]
  have step : ∀ candidate : A,
      Pr{let result ← (if candidate ∈ accepted then pure (some candidate, [candidate])
        else (fun result => (result.1, candidate :: result.2)) <$> runPrefix accepted fuel)}[result.1.elim False event] =
      if candidate ∈ accepted then (if event candidate then 1 else 0)
      else Pr{let result ← runPrefix accepted fuel}[result.1.elim False event] := by
    intro candidate
    by_cases member : candidate ∈ accepted <;> simp [member, prEvent_norm]
  simp_rw [SampleableType.prEvent_uniformSample_eq_singleton, step]
  simp_rw [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite]
  simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter,
    Finset.sum_const, nsmul_eq_mul]
  rw [hit, reject, SampleableType.prEvent_uniformSample, SampleableType.prEvent_uniformSample]
  simp only [div_eq_mul_inv]
  have same : (Finset.univ.filter (fun x : A => x ∈ accepted ∧ event x)) = accepted.filter event := by
    ext x
    simp [and_comm]
  rw [same]
  congr 1
  ac_rfl

omit [Fintype A] in
/-- Reaching the end of a prefix means that every attempted draw was rejected. -/
theorem suspended_probability (accepted : Finset A) (fuel : ℕ) :
    Pr{let result ← runPrefix accepted fuel}[result.1 = none] = reject accepted ^ fuel := by
  induction fuel with
  | zero => simp [runPrefix, prEvent_norm]
  | succ fuel ih =>
    rw [runPrefix]
    have law := prEvent_bind_eq_mul_of_ite ($ᵗ A)
      (fun candidate => if candidate ∈ accepted then pure (some candidate, [candidate])
        else (fun result => (result.1, candidate :: result.2)) <$> runPrefix accepted fuel)
      (fun candidate => candidate ∉ accepted) (fun result => result.1 = none)
      (runPrefix accepted fuel) (fun result => result.1 = none) (by
        intro candidate
        by_cases member : candidate ∈ accepted <;> simp [member, prEvent_norm])
    exact law.trans (by rw [ih, pow_succ']; rfl)

/-- Exact successful-event mass for every operational prefix. -/
theorem success_probability (accepted : Finset A) (event : A → Prop) (fuel : ℕ) :
    Pr{let result ← runPrefix accepted fuel}[result.1.elim False event] =
      (∑ attempt ∈ Finset.range fuel, reject accepted ^ attempt) * hit accepted event := by
  induction fuel with
  | zero => simp [runPrefix, prEvent_norm]
  | succ fuel ih =>
    rw [success_succ, ih, Finset.sum_range_succ']
    simp only [pow_zero, one_mul, pow_succ', add_mul]
    rw [← Finset.mul_sum]
    ac_rfl

omit [DecidableEq A] [Fintype A] in
theorem reject_lt_one (accepted : Finset A) (nonempty : accepted.Nonempty) : reject accepted < 1 := by
  have bounded : reject accepted ≤ 1 := prEvent_le_one _
  refine lt_of_le_of_ne bounded ?_
  intro equal
  have all := (SampleableType.prEvent_uniformSample_eq_one_iff (fun candidate : A => candidate ∉ accepted)).mp equal
  obtain ⟨candidate, member⟩ := nonempty
  exact all candidate member

omit [Fintype A] in
/-- Suspension vanishes in the unbounded limit; no maximum retry count is
assumed or extracted from an observed execution. -/
theorem suspension_tends_to_zero (accepted : Finset A) (nonempty : accepted.Nonempty) :
    Filter.Tendsto (fun fuel => Pr{let result ← runPrefix accepted fuel}[result.1 = none])
      Filter.atTop (nhds 0) := by
  simpa only [suspended_probability] using ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one (reject_lt_one accepted nonempty)

/-- Successful event mass of the unbounded loop, defined by all of its
operational prefixes. No finite prefix is chosen as a protocol cutoff. -/
def eventProbability (accepted : Finset A) (event : A → Prop) : ENNReal :=
  ⨆ fuel, Pr{let result ← runPrefix accepted fuel}[result.1.elim False event]

theorem hit_fraction (accepted : Finset A) (event : A → Prop) :
    hit accepted event = (accepted.filter event).card / (Fintype.card A : ENNReal) := by
  rw [hit, SampleableType.prEvent_uniformSample]
  congr 2
  congr 1
  ext x
  simp

omit [DecidableEq A] [Fintype A] in
theorem one_sub_reject (accepted : Finset A) : 1 - reject accepted = hit accepted (fun _ => True) := by
  apply ENNReal.sub_eq_of_eq_add' (by simp)
  simpa only [hit, reject, and_true, measure_univ] using
    (prEvent_add_prEvent_not ($ᵗ A) (fun candidate => candidate ∈ accepted)).symm

/-- Exact limiting law of the actual ideal rejection loop: uniform selection
on the accepted domain. Empty domains have zero successful mass. -/
theorem eventProbability_eq_uniform (accepted : Finset A) (event : A → Prop) :
    eventProbability accepted event = Pr{let candidate ← ($ accepted : OptionT ProbComp A)}[event candidate] := by
  unfold eventProbability
  simp_rw [success_probability]
  rw [← ENNReal.iSup_mul, ← ENNReal.tsum_eq_iSup_nat, ENNReal.tsum_geometric, one_sub_reject,
    hit_fraction, hit_fraction, ProbComp.prEvent_uniformSelectFinset]
  simp only [Finset.filter_true, div_eq_mul_inv]
  have nonzero : (Fintype.card A : ENNReal) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [ENNReal.mul_inv (Or.inr (ENNReal.inv_ne_top.mpr nonzero)) (Or.inl (by simp)), inv_inv]
  calc _ = ((accepted.filter event).card : ENNReal) * (accepted.card : ENNReal)⁻¹ *
        ((Fintype.card A : ENNReal) * (Fintype.card A : ENNReal)⁻¹) := by ac_rfl
       _ = _ := by rw [ENNReal.mul_inv_cancel nonzero (by simp), mul_one]

omit [DecidableEq A] [Fintype A] [SampleableType A] in
private theorem expected_one (program : ProbComp A) :
    (∫⁻ value, value ∂𝒟[(fun _ => (1 : ENNReal)) <$> program]) = 1 := by
  let _ : MeasurableSpace A := ⊤
  rw [lintegral_id_evalDist_map]
  simp

omit [DecidableEq A] [Fintype A] [SampleableType A] in
private theorem expected_ite (program : ProbComp A) (event : A → Prop) [DecidablePred event] (cost : ENNReal) :
    (∫⁻ value, value ∂𝒟[(fun value => if event value then cost else 0) <$> program]) =
      Pr{let value ← program}[event value] * cost := by
  let _ : MeasurableSpace A := ⊤
  rw [lintegral_id_evalDist_map, prEvent_eq_evalDist_of_discrete]
  have same : (fun value => if event value then cost else 0) =
      {value | event value}.indicator (fun _ => cost) := by
    funext value
    by_cases present : event value <;> simp [present, Set.indicator]
  rw [same]
  rw [lintegral_indicator_const MeasurableSet.of_discrete, mul_comm]

/-- Expected number of all candidates actually issued in an operational
prefix, including candidates rejected before suspension or success. -/
def expectedAttempts (accepted : Finset A) (fuel : ℕ) : ENNReal :=
  ∫⁻ value, value ∂𝒟[(fun result => (result.2.length : ENNReal)) <$> runPrefix accepted fuel]

omit [Fintype A] in
theorem expectedAttempts_succ (accepted : Finset A) (fuel : ℕ) :
    expectedAttempts accepted (fuel + 1) = 1 + reject accepted * expectedAttempts accepted fuel := by
  rw [expectedAttempts, runPrefix, lintegral_id_evalDist_map_bind]
  have step : ∀ candidate : A,
      (∫⁻ value, value ∂𝒟[(fun result => (result.2.length : ENNReal)) <$>
        (if candidate ∈ accepted then pure (some candidate, [candidate])
         else (fun result => (result.1, candidate :: result.2)) <$> runPrefix accepted fuel)]) =
      1 + if candidate ∉ accepted then expectedAttempts accepted fuel else 0 := by
    intro candidate
    by_cases member : candidate ∈ accepted
    · simp [member, evalDist_pure]
    · simp only [member, not_false_eq_true, ite_true, ite_false, Functor.map_map,
        List.length_cons, Nat.cast_add, Nat.cast_one]
      rw [lintegral_id_evalDist_map_add, expected_one]
      exact add_comm _ _
  simp_rw [step]
  rw [lintegral_id_evalDist_map_add, expected_one, expected_ite]
  rfl

omit [Fintype A] in
/-- Each additional possible rejected draw contributes its actual survival
probability; this is a work identity, not an observed retry maximum. -/
theorem expectedAttempts_eq_sum (accepted : Finset A) (fuel : ℕ) :
    expectedAttempts accepted fuel = ∑ attempt ∈ Finset.range fuel, reject accepted ^ attempt := by
  induction fuel with
  | zero => simp [expectedAttempts, runPrefix, evalDist_pure]
  | succ fuel ih =>
    rw [expectedAttempts_succ, ih, Finset.sum_range_succ']
    simp only [pow_zero, pow_succ', Finset.mul_sum]
    exact add_comm _ _

/-- Unbounded expected work uses every operational prefix, with no bound
assumed on the actual number of rejected candidates. -/
def totalExpectedAttempts (accepted : Finset A) : ENNReal := ⨆ fuel, expectedAttempts accepted fuel

omit [Fintype A] in
theorem totalExpectedAttempts_eq (accepted : Finset A) :
    totalExpectedAttempts accepted = (1 - reject accepted)⁻¹ := by
  unfold totalExpectedAttempts
  simp_rw [expectedAttempts_eq_sum]
  rw [← ENNReal.tsum_eq_iSup_nat, ENNReal.tsum_geometric]

theorem totalExpectedAttempts_fraction (accepted : Finset A) :
    totalExpectedAttempts accepted = (Fintype.card A : ENNReal) / accepted.card := by
  rw [totalExpectedAttempts_eq, one_sub_reject, hit_fraction]
  simp only [Finset.filter_true]
  have nonzero : (Fintype.card A : ENNReal) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inr (ENNReal.inv_ne_top.mpr nonzero)) (Or.inl (by simp)), inv_inv]
  exact mul_comm _ _

/-- Every finite operational prefix is soundly dominated by the same exact
unbounded accepted-domain law. This quantifies over all prefixes. -/
theorem prefix_event_le_uniform (accepted : Finset A) (event : A → Prop) (fuel : ℕ) :
    Pr{let result ← runPrefix accepted fuel}[result.1.elim False event] ≤
      Pr{let candidate ← ($ accepted : OptionT ProbComp A)}[event candidate] := by
  rw [← eventProbability_eq_uniform]
  exact le_iSup (fun fuel => Pr{let result ← runPrefix accepted fuel}[result.1.elim False event]) fuel

theorem totalExpectedAttempts_finite (accepted : Finset A) (nonempty : accepted.Nonempty) :
    totalExpectedAttempts accepted < ⊤ := by
  rw [totalExpectedAttempts_fraction]
  apply ENNReal.div_lt_top (by simp)
  exact_mod_cast (Finset.card_pos.mpr nonempty).ne'

/-- Longer operational prefixes preserve all earlier successful outcomes. -/
theorem success_monotone (accepted : Finset A) (event : A → Prop) :
    Monotone (fun fuel => Pr{let result ← runPrefix accepted fuel}[result.1.elim False event]) := by
  intro first second ordered
  simp only [success_probability]
  exact mul_le_mul_left (Finset.sum_le_sum_of_subset (Finset.range_mono ordered)) _

/-- The accepted-domain law is an actual limit of the operational event laws,
not merely a supremum assigned to an unrelated sampling program. -/
theorem success_tends_to_uniform (accepted : Finset A) (event : A → Prop) :
    Filter.Tendsto (fun fuel => Pr{let result ← runPrefix accepted fuel}[result.1.elim False event])
      Filter.atTop (nhds (Pr{let candidate ← ($ accepted : OptionT ProbComp A)}[event candidate])) := by
  rw [← eventProbability_eq_uniform]
  exact tendsto_atTop_iSup (success_monotone accepted event)

omit [Fintype A] in
theorem expectedAttempts_monotone (accepted : Finset A) : Monotone (expectedAttempts accepted) := by
  intro first second ordered
  simp only [expectedAttempts_eq_sum]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono ordered)

theorem expectedAttempts_tends_to_fraction (accepted : Finset A) :
    Filter.Tendsto (expectedAttempts accepted) Filter.atTop (nhds ((Fintype.card A : ENNReal) / accepted.card)) := by
  rw [← totalExpectedAttempts_fraction]
  exact tendsto_atTop_iSup (expectedAttempts_monotone accepted)

/-- Normalization of first-draw hit mass is derived from all operational
prefixes, so transported samplers can reuse the exact rejection law. -/
theorem eventProbability_eq_ratio (accepted : Finset A) (event : A → Prop) :
    eventProbability accepted event = hit accepted event / hit accepted (fun _ => True) := by
  unfold eventProbability
  simp_rw [success_probability]
  rw [← ENNReal.iSup_mul, ← ENNReal.tsum_eq_iSup_nat, ENNReal.tsum_geometric, one_sub_reject,
    div_eq_mul_inv, mul_comm]

omit [Fintype A] in
/-- Every completed prefix returns an actually accepted candidate; this is a
support statement about the program, independent of its probability law. -/
theorem returned_mem (accepted : Finset A) (fuel : ℕ) (result : Result A)
    (supported : result ∈ support (runPrefix accepted fuel)) (candidate : A)
    (returned : result.1 = some candidate) : candidate ∈ accepted := by
  induction fuel generalizing result with
  | zero =>
    simp only [runPrefix, support_pure, Set.mem_singleton_iff] at supported
    subst result
    simp at returned
  | succ fuel ih =>
    simp only [runPrefix, support_bind, Set.mem_iUnion] at supported
    obtain ⟨first, _, branch⟩ := supported
    by_cases member : first ∈ accepted
    · simp only [member, ite_true, support_pure, Set.mem_singleton_iff] at branch
      subst result
      have equal : first = candidate := Option.some.inj returned
      exact equal ▸ member
    · simp only [member, ite_false, support_map, Set.mem_image] at branch
      obtain ⟨tail, reached, equal⟩ := branch
      subst result
      exact ih tail reached returned

/-- Every finite prefix has the limiting output law scaled by its actual
completion mass. This derives the value/completion factorization. -/
theorem success_scaled (accepted : Finset A) (nonempty : accepted.Nonempty) (fuel : ℕ) (event : A → Prop) :
    Pr{let result ← runPrefix accepted fuel}[result.1.elim False event] =
      Pr{let result ← runPrefix accepted fuel}[result.1.elim False (fun _ => True)] * eventProbability accepted event := by
  have positive : 0 < hit accepted (fun _ => True) :=
    (SampleableType.prEvent_uniformSample_pos_iff _).mpr (by
      obtain ⟨value, member⟩ := nonempty
      exact ⟨value, member, trivial⟩)
  have finite : hit accepted (fun _ => True) ≠ ⊤ := ne_of_lt (prEvent_lt_top _)
  rw [success_probability, success_probability, eventProbability_eq_ratio, div_eq_mul_inv]
  calc _ = ((∑ attempt ∈ Finset.range fuel, reject accepted ^ attempt) * hit accepted event) *
        (hit accepted (fun _ => True) * (hit accepted (fun _ => True))⁻¹) := by
          rw [ENNReal.mul_inv_cancel positive.ne' finite, mul_one]
       _ = _ := by ac_rfl

/-- One full uniform trial followed, on genuine rejection only, by any
optional suffix. This is a value law and does not erase trial metadata. -/
theorem one_step_probability (accepted : Finset A) (tail : ProbComp (Option A)) (event : A → Prop) :
    Pr{let result ← ($ᵗ A >>= fun candidate => if candidate ∈ accepted then pure (some candidate) else tail)}[
      result.elim False event] = hit accepted event + reject accepted * Pr{let result ← tail}[result.elim False event] := by
  rw [prEvent_bind_eq_tsum, tsum_fintype]
  have step : ∀ candidate : A,
      Pr{let result ← (if candidate ∈ accepted then pure (some candidate) else tail)}[result.elim False event] =
      if candidate ∈ accepted then (if event candidate then 1 else 0)
      else Pr{let result ← tail}[result.elim False event] := by
    intro candidate
    by_cases member : candidate ∈ accepted <;> simp [member, prEvent_norm]
  simp_rw [SampleableType.prEvent_uniformSample_eq_singleton, step, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite]
  simp only [← Finset.sum_filter, Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
  rw [hit, reject, SampleableType.prEvent_uniformSample, SampleableType.prEvent_uniformSample]
  simp only [div_eq_mul_inv]
  have same : (Finset.univ.filter (fun candidate : A => candidate ∈ accepted ∧ event candidate)) = accepted.filter event := by
    ext candidate
    simp [and_comm]
  rw [same]
  congr 1
  ac_rfl

end

end FormalProof4FHE.HasteBoots.RejectionSampling
