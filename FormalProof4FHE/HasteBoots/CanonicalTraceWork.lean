module

public import FormalProof4FHE.HasteBoots.RejectionTraceWork

@[expose] public section

/-!
# Actual completed canonical-byte trace mean

The measure retains every raw chunk in the native masked-below-modulus retry
program. Its expected consumed bytes equal the unconditional prefix-work
limit because the exact unfinished-work tail vanishes. This is byte work,
not yet a conversion to SHA/XOF primitive hash work.
-/

open OracleSpec OracleComp MeasureTheory
open scoped Classical

namespace FormalProof4FHE.HasteBoots.CanonicalTraceWork

noncomputable section

local instance (p : ℕ) : MeasurableSpace (RejectionSampling.Result (CanonicalByteMask.Bytes (CanonicalByteSampler.byteCount p))) := ⊤

/-- Complete raw-byte observation measure, with no successful-mass rescaling. -/
def measure (p : ℕ) := RejectionTraceWork.measure (CanonicalByteSampler.accepted p)

/-- Its events are the limits of the actual native-guard query programs. -/
theorem measure_apply (p : ℕ)
    (event : RejectionSampling.Result (CanonicalByteMask.Bytes (CanonicalByteSampler.byteCount p)) → Prop) :
    measure p {result | event result} = ⨆ fuel, Pr{let result ← CanonicalByteSampler.runPrefix p fuel}[
      RejectionTraceOrder.complete result ∧ event result] := by
  rw [measure, RejectionTraceWork.measure, CompletedObservationLimit.measure_apply]
  simp only [CanonicalByteSampler.runPrefix_eq, Set.mem_ofPred_eq]

theorem probability (p : ℕ) (valid : 1 < p) : IsProbabilityMeasure (measure p) :=
  RejectionTraceWork.probability _ (CanonicalByteSampler.accepted_nonempty p valid)

/-- Derived support bound for a finite approximation, counting each raw
chunk's configured byte width. It imposes no native retry budget. -/
theorem consumed_le (p fuel : ℕ)
    (result : RejectionSampling.Result (CanonicalByteMask.Bytes (CanonicalByteSampler.byteCount p)))
    (supported : result ∈ support (CanonicalByteSampler.runPrefix p fuel)) :
    CanonicalByteSampler.consumedBytes p result ≤ CanonicalByteSampler.byteCount p * fuel := by
  rw [CanonicalByteSampler.runPrefix_eq] at supported
  exact Nat.mul_le_mul_left _ (RejectionTraceWork.length_le _ fuel result supported)

/-- Exact incomplete byte work includes every rejected chunk, even at the
operational suspension boundary. The width is the actual configured width. -/
theorem partial_mean (p fuel : ℕ) :
    (∫⁻ value, value ∂𝒟[(fun result => if RejectionTraceOrder.complete result then 0
      else (CanonicalByteSampler.consumedBytes p result : ENNReal)) <$> CanonicalByteSampler.runPrefix p fuel]) =
      (CanonicalByteSampler.byteCount p : ENNReal) *
        ((fuel : ENNReal) * RejectionSampling.reject (CanonicalByteSampler.accepted p) ^ fuel) := by
  rw [CanonicalByteSampler.runPrefix_eq]
  have scaled : (fun result : RejectionSampling.Result (CanonicalByteMask.Bytes (CanonicalByteSampler.byteCount p)) =>
      if RejectionTraceOrder.complete result then 0 else (CanonicalByteSampler.consumedBytes p result : ENNReal)) =
      (fun result => (CanonicalByteSampler.byteCount p : ENNReal) *
        (if RejectionTraceOrder.complete result then 0 else (result.2.length : ENNReal))) := by
    funext result
    by_cases done : RejectionTraceOrder.complete result <;>
      simp [done, CanonicalByteSampler.consumedBytes, Nat.cast_mul]
  rw [scaled, lintegral_id_evalDist_map,
    lintegral_const_mul _ Measurable.of_discrete, ← lintegral_id_evalDist_map, RejectionTraceWork.partial_mean]

/-- Vanishing unfinished byte work is derived, not inferred only from
almost-sure successful completion. No retry bound is imposed on the protocol. -/
theorem partial_tends_zero (p : ℕ) (valid : 1 < p) :
    Filter.Tendsto
      (fun fuel => ∫⁻ value, value ∂𝒟[(fun result => if RejectionTraceOrder.complete result then 0
        else (CanonicalByteSampler.consumedBytes p result : ENNReal)) <$> CanonicalByteSampler.runPrefix p fuel])
      Filter.atTop (nhds 0) := by
  simp_rw [partial_mean]
  have tail := RejectionTraceWork.geometric_tail _
    (RejectionSampling.reject_lt_one _ (CanonicalByteSampler.accepted_nonempty p valid))
  have total := ENNReal.Tendsto.mul (tendsto_const_nhds (x := (CanonicalByteSampler.byteCount p : ENNReal)))
    (Or.inr (by simp)) tail (Or.inr (by simp))
  simpa only [mul_zero] using total

/-- The mean of the actual completed native byte trace has the exact mask/
modulus formula, including all rejected raw chunks before acceptance. -/
theorem expected (p : ℕ) (valid : 1 < p) :
    (∫⁻ result, (CanonicalByteSampler.consumedBytes p result : ENNReal) ∂measure p) =
      (CanonicalByteSampler.byteCount p : ENNReal) * (((2 ^ CanonicalByteSampler.bits p : ℕ) : ENNReal) / p) := by
  change (∫⁻ result, (CanonicalByteSampler.consumedBytes p result : ENNReal)
    ∂RejectionTraceWork.measure (CanonicalByteSampler.accepted p)) = _
  simp only [CanonicalByteSampler.consumedBytes, Nat.cast_mul]
  rw [lintegral_const_mul _ Measurable.of_discrete, RejectionTraceWork.expected _ (CanonicalByteSampler.accepted_nonempty p valid),
    ← RejectionSampling.totalExpectedAttempts_fraction, CanonicalByteSampler.expected_attempts p valid]

/-- The unconditional operational byte-work limit is exactly the mean of
its completed trace measure; no unfinished-tail cost is silently dropped. -/
theorem expected_eq_total (p : ℕ) (valid : 1 < p) :
    (∫⁻ result, (CanonicalByteSampler.consumedBytes p result : ENNReal) ∂measure p) =
      CanonicalByteSampler.totalExpectedBytes p := by
  rw [expected p valid, CanonicalByteSampler.totalExpectedBytes_eq p valid]

end

end FormalProof4FHE.HasteBoots.CanonicalTraceWork
