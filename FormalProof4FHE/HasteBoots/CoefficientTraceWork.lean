module

public import FormalProof4FHE.HasteBoots.CanonicalTraceWork
public import FormalProof4FHE.HasteBoots.CoefficientTraceOrder

@[expose] public section

/-!
# Completed sequential coefficient traces retain their full byte cost

Each analysis prefix has at most count times depth raw chunks. The chance
of suspension is at most count times the base rejection tail. Their product
bounds unfinished byte work and tends to zero. These bounds follow from the
actual sequential program; they impose no native retry or byte budget.
-/

open OracleSpec OracleComp MeasureTheory
open scoped Classical
open FormalProof4FHE.HasteBoots.CanonicalCoefficientVector

namespace FormalProof4FHE.HasteBoots.CoefficientTraceWork

noncomputable section

local instance (p count : ℕ) : MeasurableSpace (Result p count) := ⊤

/-- A support bound for the real sequential prefix, including suspension. -/
theorem chunks_le (p fuel count : ℕ) (result : Result p count)
    (supported : result ∈ support (program p fuel count)) :
    result.chunks.length ≤ count * fuel := by
  induction count with
  | zero =>
    simp only [program, support_pure, Set.mem_singleton_iff] at supported
    subst result
    simp
  | succ count ih =>
    simp only [program, support_bind, Set.mem_iUnion] at supported
    obtain ⟨first, reached, branch⟩ := supported
    have head := RejectionTraceWork.length_le (CanonicalByteSampler.accepted p) fuel first
      (by simpa only [CanonicalByteSampler.runPrefix_eq] using reached)
    cases tag : first.1 with
    | none =>
      simp only [tag, support_pure, Set.mem_singleton_iff] at branch
      subst result
      exact head.trans (by rw [Nat.succ_mul]; omega)
    | some raw =>
      simp only [tag, support_map, Set.mem_image] at branch
      obtain ⟨tail, tail_reached, equal⟩ := branch
      subst result
      simpa only [cons, List.length_append, Nat.succ_mul, Nat.add_comm] using
        Nat.add_le_add head (ih tail tail_reached)

/-- A union bound derived from starting the next coefficient only after the
current one completes; no independence assumption is supplied by the caller. -/
theorem suspended_le (p fuel count : ℕ) :
    Pr{let result ← program p fuel count}[result.values = none] ≤
      (count : ENNReal) * RejectionSampling.reject (CanonicalByteSampler.accepted p) ^ fuel := by
  induction count with
  | zero => simp [program]
  | succ count ih =>
    rw [program]
    have bound := prEvent_bind_le_prEvent_add (CanonicalByteSampler.runPrefix p fuel)
      (fun first => match first.1 with
        | none => pure (⟨none, [], first.2⟩ : Result p (count + 1))
        | some raw => cons raw first.2 <$> program p fuel count)
      (fun first => first.1 = none) (fun result : Result p (count + 1) => result.values = none)
      (ε := (count : ENNReal) * RejectionSampling.reject (CanonicalByteSampler.accepted p) ^ fuel) (by
        intro first completed
        cases tag : first.1 with
        | none => exact (completed tag).elim
        | some raw => simpa [tag, prEvent_map, cons] using ih)
    have head_probability : Pr{let first ← CanonicalByteSampler.runPrefix p fuel}[first.1 = none] =
        RejectionSampling.reject (CanonicalByteSampler.accepted p) ^ fuel := by
      rw [CanonicalByteSampler.runPrefix_eq, RejectionSampling.suspended_probability]
    rw [head_probability] at bound
    have scalar : RejectionSampling.reject (CanonicalByteSampler.accepted p) ^ fuel +
        (count : ENNReal) * RejectionSampling.reject (CanonicalByteSampler.accepted p) ^ fuel =
        ((count + 1 : ℕ) : ENNReal) * RejectionSampling.reject (CanonicalByteSampler.accepted p) ^ fuel := by
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm]
    exact bound.trans_eq scalar

/-- Unfinished byte work is bounded by a derived cost bound times the actual
suspension probability; all partial accepted coefficients remain counted. -/
theorem partial_le (p fuel count : ℕ) :
    (∫⁻ value, value ∂𝒟[(fun result : Result p count => if CoefficientTraceOrder.complete result then 0
      else (CanonicalCoefficientWork.consumedBytes p result : ENNReal)) <$> program p fuel count]) ≤
      (CanonicalByteSampler.byteCount p : ENNReal) * (count : ENNReal) * (count : ENNReal) *
        ((fuel : ENNReal) * RejectionSampling.reject (CanonicalByteSampler.accepted p) ^ fuel) := by
  have bound : (∫⁻ value, value ∂𝒟[(fun result : Result p count => if CoefficientTraceOrder.complete result then 0
        else (CanonicalCoefficientWork.consumedBytes p result : ENNReal)) <$> program p fuel count]) ≤
      ∫⁻ value, value ∂𝒟[(fun result : Result p count => if result.values = none
        then ((CanonicalByteSampler.byteCount p * (count * fuel) : ℕ) : ENNReal) else 0) <$> program p fuel count] := by
    rw [lintegral_id_evalDist_map, lintegral_id_evalDist_map]
    apply lintegral_mono_ae
    exact (evalDist_ae_mem_support (program p fuel count)).mono (fun result reached => by
      by_cases done : result.values = none
      · simp only [CoefficientTraceOrder.complete, done, ne_eq, not_true_eq_false, ite_false, ite_true]
        exact_mod_cast Nat.mul_le_mul_left (CanonicalByteSampler.byteCount p) (chunks_le p fuel count result reached)
      · simp [CoefficientTraceOrder.complete, done])
  rw [CompletedCostTransfer.indicator] at bound
  exact bound.trans ((mul_le_mul' (suspended_le p fuel count)
    (le_refl (((CanonicalByteSampler.byteCount p * (count * fuel) : ℕ) : ENNReal)))).trans_eq (by
    simp only [Nat.cast_mul]
    ring))

/-- The work on incomplete traces vanishes, not only their probability. -/
theorem partial_tends_zero (p : ℕ) (valid : 1 < p) (count : ℕ) :
    Filter.Tendsto (fun fuel => ∫⁻ value, value ∂𝒟[(fun result : Result p count =>
      if CoefficientTraceOrder.complete result then 0 else (CanonicalCoefficientWork.consumedBytes p result : ENNReal)) <$>
        program p fuel count]) Filter.atTop (nhds 0) := by
  have tail := RejectionTraceWork.geometric_tail _
    (RejectionSampling.reject_lt_one _ (CanonicalByteSampler.accepted_nonempty p valid))
  have scaled := ENNReal.Tendsto.mul
    (tendsto_const_nhds (x := (CanonicalByteSampler.byteCount p : ENNReal) * (count : ENNReal) * (count : ENNReal)))
    (Or.inr (by simp)) tail (Or.inr (by finiteness))
  simp only [mul_zero] at scaled
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds scaled
    (fun _ => bot_le) (fun fuel => partial_le p fuel count)

/-- The full completed observation law retains raw bytes and partial memory. -/
def measure (p count : ℕ) : Measure (Result p count) :=
  CompletedObservationLimit.measure (fun fuel => program p fuel count) CoefficientTraceOrder.complete
    (fun _ _ h => CoefficientTraceOrder.coefficients p count h)

/-- Exact completed byte mean, with every rejected raw chunk retained. -/
theorem expected (p : ℕ) (valid : 1 < p) [NeZero p] (count : ℕ) :
    (∫⁻ result, (CanonicalCoefficientWork.consumedBytes p result : ENNReal) ∂measure p count) =
      (count : ENNReal) * CanonicalByteSampler.totalExpectedBytes p := by
  apply CompletedCostTransfer.of_partial_tends_zero
  · exact CanonicalCoefficientWork.expectedBytes_tends_to p valid count
  · exact partial_tends_zero p valid count

theorem expected_eq_total (p : ℕ) (valid : 1 < p) [NeZero p] (count : ℕ) :
    (∫⁻ result, (CanonicalCoefficientWork.consumedBytes p result : ENNReal) ∂measure p count) =
      CanonicalCoefficientWork.totalExpectedBytes p count := by
  rw [expected p valid, CanonicalCoefficientWork.totalExpectedBytes_eq p valid]

/-- Every requested coefficient completes almost surely; the raw trace law
is normalized without conditioning away incomplete prefixes. -/
theorem probability (p : ℕ) (valid : 1 < p) [NeZero p] (count : ℕ) :
    IsProbabilityMeasure (measure p count) := by
  apply CompletedObservationLimit.probability
  have finite (fuel : ℕ) : Pr{let result ← program p fuel count}[CoefficientTraceOrder.complete result] =
      Pr{let result ← program p fuel count}[result.values.elim False (fun _ => True)] := by
    apply prEvent_congr
    intro result
    cases tag : result.values <;> simp [CoefficientTraceOrder.complete, tag]
  simp_rw [finite]
  simpa [eventProbability] using
    uniform_values p valid count (fun _ => True)

end

end FormalProof4FHE.HasteBoots.CoefficientTraceWork
