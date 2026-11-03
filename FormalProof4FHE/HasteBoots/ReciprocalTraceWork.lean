module

public import FormalProof4FHE.HasteBoots.OptionalRejectionTail
public import FormalProof4FHE.HasteBoots.ExtensionTraceWork
public import FormalProof4FHE.HasteBoots.ByteLookupTraceOrder

@[expose] public section

/-!
# Byte work in completed reciprocal traces

Both nested analysis depths grow without imposing a native retry cap.
Suspension of a field trial and completed pole rejections are separate
events. Their derived work tails vanish, retaining all raw trial bytes.
-/

open OracleSpec OracleComp MeasureTheory
open scoped Classical
open FormalProof4FHE.HasteBoots.ByteReciprocalSampler

namespace FormalProof4FHE.HasteBoots.ReciprocalTraceWork

noncomputable section

/-- Polynomial cost growth is dominated by every strict geometric tail. -/
theorem polynomial_geometric (power : ℕ) (rho : ENNReal) (small : rho < 1) :
    Filter.Tendsto (fun n : ℕ => (n : ENNReal) ^ power * rho ^ n) Filter.atTop (nhds 0) := by
  have finite : rho ≠ ⊤ := ne_of_lt (small.trans (by simp))
  have real_small : rho.toReal < 1 := by
    simpa only [ENNReal.toReal_one] using (ENNReal.toReal_lt_toReal finite ENNReal.one_ne_top).mpr small
  have real_limit := tendsto_pow_const_mul_const_pow_of_lt_one power ENNReal.toReal_nonneg real_small
  have lifted := ENNReal.tendsto_ofReal real_limit
  simpa only [ENNReal.ofReal_mul (pow_nonneg (Nat.cast_nonneg _) _),
    ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast,
    ENNReal.ofReal_pow ENNReal.toReal_nonneg, ENNReal.ofReal_toReal finite, ENNReal.ofReal_zero] using lifted

/-- A common analysis depth is cofinal in both independent prefix depths. -/
theorem diagonal_sup (f : ℕ → ℕ → ENNReal)
    (grows : ∀ i o i' o', i ≤ i' → o ≤ o' → f i o ≤ f i' o') :
    (⨆ n, f n n) = ⨆ outer, ⨆ inner, f inner outer := by
  apply le_antisymm
  · refine iSup_le fun n => le_iSup_of_le n (le_iSup_of_le n le_rfl)
  · refine iSup_le fun outer => iSup_le fun inner => ?_
    exact (grows inner outer (max inner outer) (max inner outer) (le_max_left _ _) (le_max_right _ _)).trans
      (le_iSup (fun n => f n n) (max inner outer))

variable {p degree size : ℕ} {K : Type} [Field K] [Module (ZMod p) K]

local instance : MeasurableSpace (OptionalRejectionLoop.Result K (Trial p degree K)) := ⊤

/-- The field trial's actual suspension is the sequential coefficient
suspension, including its partial last coefficient. -/
theorem trial_suspended_le (basis : Module.Basis (Fin degree) (ZMod p) K) (inner : ℕ) :
    Pr{let trial ← step basis inner}[candidate trial = none] ≤
      (degree : ENNReal) * RejectionSampling.reject (CanonicalByteSampler.accepted p) ^ inner := by
  have same : Pr{let trial ← step basis inner}[candidate trial = none] =
      Pr{let coefficients ← CanonicalCoefficientVector.program p inner (1 * degree)}[coefficients.values = none] := by
    rw [step, CanonicalExtensionSampler.program, prEvent_map]
    apply prEvent_congr
    intro coefficients
    cases coefficients.values <;> simp [candidate]
  rw [same]
  simpa only [one_mul] using CoefficientTraceWork.suspended_le p inner (1 * degree)

/-- Every started field trial has the derived finite coefficient byte bound. -/
theorem trial_cost_le (basis : Module.Basis (Fin degree) (ZMod p) K) (inner : ℕ)
    (trial : Trial p degree K) (supported : trial ∈ support (step basis inner)) :
    cost trial ≤ CanonicalByteSampler.byteCount p * degree * inner := by
  simp only [step, CanonicalExtensionSampler.program, support_map, Set.mem_image] at supported
  obtain ⟨coefficients, reached, equal⟩ := supported
  subst trial
  simpa only [cost, CanonicalCoefficientWork.consumedBytes, one_mul, Nat.mul_assoc] using
    Nat.mul_le_mul_left (CanonicalByteSampler.byteCount p)
      (CoefficientTraceWork.chunks_le p inner (1 * degree) coefficients reached)

variable [DecidableEq K]

/-- The full prefix includes every rejected field and any partial last draw. -/
theorem consumed_le (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → K) (inner outer : ℕ)
    (result : OptionalRejectionLoop.Result K (Trial p degree K))
    (supported : result ∈ support (program basis table inner outer)) :
    consumedBytes result ≤ CanonicalByteSampler.byteCount p * degree * inner * outer :=
  OptionalRejectionTail.consumed_le (step basis inner) candidate (allow table) cost _
    (trial_cost_le basis inner) outer result supported

variable [Fintype K] [SampleableType K] [NeZero p]

/-- Completed rejected field values have their derived actual rate. -/
theorem rejected_le (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → K) (inner : ℕ) :
    Pr{let trial ← step basis inner}[(candidate trial).elim False (fun value => ¬allow table value)] ≤
      RejectionSampling.reject (ReciprocalDetection.allowed table) := by
  rw [candidate_law valid basis]
  have same : Pr{let value ← $ᵗ K}[¬allow table value] =
      RejectionSampling.reject (ReciprocalDetection.allowed table) := by
    apply prEvent_congr
    intro value
    simp [allow, ReciprocalDetection.mem_allowed]
  rw [same]
  exact mul_le_of_le_one_left' (pow_le_one₀ zero_le (CanonicalCoefficientVector.completion_le_one p inner))

/-- Inner byte failure and exhausting completed pole rejections remain
separate; no unsuccessful observation is normalized away. -/
theorem suspended_le (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → K) (inner outer : ℕ) :
    Pr{let result ← program basis table inner outer}[result.value = none] ≤
      (outer : ENNReal) * ((degree : ENNReal) * RejectionSampling.reject (CanonicalByteSampler.accepted p) ^ inner) +
        RejectionSampling.reject (ReciprocalDetection.allowed table) ^ outer := by
  exact (OptionalRejectionTail.suspended_le (step basis inner) candidate (allow table) outer).trans
    (add_le_add (mul_le_mul' le_rfl (trial_suspended_le basis inner))
      (pow_le_pow_left' (rejected_le valid basis table inner) outer))


/-- Work on incomplete reciprocal traces is bounded before taking any limit. -/
theorem partial_le (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → K) (inner outer : ℕ) :
    (∫⁻ value, value ∂𝒟[(fun result => if OptionalTraceOrder.loopComplete result then 0
      else (consumedBytes result : ENNReal)) <$> program basis table inner outer]) ≤
      ((CanonicalByteSampler.byteCount p * degree * inner * outer : ℕ) : ENNReal) *
        ((outer : ENNReal) * ((degree : ENNReal) * RejectionSampling.reject (CanonicalByteSampler.accepted p) ^ inner) +
          RejectionSampling.reject (ReciprocalDetection.allowed table) ^ outer) := by
  have bounded : (∫⁻ value, value ∂𝒟[(fun result => if OptionalTraceOrder.loopComplete result then 0
        else (consumedBytes result : ENNReal)) <$> program basis table inner outer]) ≤
      ∫⁻ value, value ∂𝒟[(fun result => if result.value = none then
        ((CanonicalByteSampler.byteCount p * degree * inner * outer : ℕ) : ENNReal) else 0) <$>
          program basis table inner outer] := by
    rw [lintegral_id_evalDist_map, lintegral_id_evalDist_map]
    apply lintegral_mono_ae
    exact (evalDist_ae_mem_support (program basis table inner outer)).mono (fun result reached => by
      by_cases done : result.value = none
      · simp only [OptionalTraceOrder.loopComplete, done, ne_eq, not_true_eq_false, ite_false, ite_true]
        exact_mod_cast consumed_le basis table inner outer result reached
      · simp [OptionalTraceOrder.loopComplete, done])
  rw [CompletedCostTransfer.indicator] at bounded
  exact bounded.trans ((mul_le_mul' (suspended_le valid basis table inner outer) le_rfl).trans_eq (mul_comm _ _))

/-- Along the cofinal common depth, neither partial inner fields nor long
completed pole rejection sequences leave unaccounted byte work. -/
theorem partial_tends_zero (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → K) (enough : size + 1 < Fintype.card K) :
    Filter.Tendsto (fun n => ∫⁻ value, value ∂𝒟[(fun result => if OptionalTraceOrder.loopComplete result then 0
      else (consumedBytes result : ENNReal)) <$> program basis table n n]) Filter.atTop (nhds 0) := by
  have bytes := polynomial_geometric 3 _
    (RejectionSampling.reject_lt_one _ (CanonicalByteSampler.accepted_nonempty p valid))
  have poles := polynomial_geometric 2 _
    (RejectionSampling.reject_lt_one _ (ReciprocalDetection.allowed_nonempty table enough))
  have first := ENNReal.Tendsto.mul
    (tendsto_const_nhds (x := (CanonicalByteSampler.byteCount p : ENNReal) * (degree : ENNReal) * (degree : ENNReal)))
    (Or.inr (by simp)) bytes (Or.inr (by finiteness))
  have second := ENNReal.Tendsto.mul
    (tendsto_const_nhds (x := (CanonicalByteSampler.byteCount p : ENNReal) * (degree : ENNReal)))
    (Or.inr (by simp)) poles (Or.inr (by finiteness))
  have total := first.add second
  simp only [mul_zero, add_zero] at total
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds total (fun _ => bot_le)
  intro n
  exact (partial_le valid basis table n n).trans_eq (by simp only [Nat.cast_mul]; ring)

/-- Full raw reciprocal observation law at all nested operational depths. -/
def measure (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → K) :=
  CompletedObservationLimit.measure (fun n => program basis table n n) OptionalTraceOrder.loopComplete
    (fun _ _ h => ByteLookupTraceOrder.reciprocal basis table h h)

/-- Work increases when the outer analysis prefix grows. -/
theorem work_monotone_outer (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → K) (inner : ℕ) : Monotone (expectedBytes basis table inner) := by
  intro first second ordered
  rw [expectedBytes_formula valid basis, expectedBytes_formula valid basis]
  exact mul_le_mul' le_rfl (Finset.sum_le_sum_of_subset (Finset.range_mono ordered))

/-- The diagonal cost limit covers all independent inner/outer prefixes. -/
theorem work_sup (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → K) :
    (⨆ n, expectedBytes basis table n n) = ByteReciprocalLimit.totalExpectedBytes basis table := by
  apply diagonal_sup
  intro inner outer inner' outer' hi ho
  exact (ByteReciprocalLimit.work_monotone_inner valid basis table outer hi).trans
    (work_monotone_outer valid basis table inner' ho)

/-- Exact completed reciprocal bytes, retaining the actual accepted-domain
cardinality and all inner and outer rejected raw trials. -/
theorem expected (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → K) (enough : size + 1 < Fintype.card K) :
    (∫⁻ result, (consumedBytes result : ENNReal) ∂measure basis table) =
      ByteReciprocalLimit.fieldCost p degree * ((Fintype.card K : ENNReal) / (ReciprocalDetection.allowed table).card) := by
  apply CompletedCostTransfer.of_partial_tends_zero
  · rw [← ByteReciprocalLimit.totalExpectedBytes_eq valid basis, ← work_sup valid basis]
    apply tendsto_atTop_iSup
    intro i j ordered
    exact (ByteReciprocalLimit.work_monotone_inner valid basis table i ordered).trans
      (work_monotone_outer valid basis table j ordered)
  · exact partial_tends_zero valid basis table enough


/-- No byte-work tail is dropped when replacing the operational supremum
by the actual completed raw-observation mean. -/
theorem expected_eq_total (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → K) (enough : size + 1 < Fintype.card K) :
    (∫⁻ result, (consumedBytes result : ENNReal) ∂measure basis table) =
      ByteReciprocalLimit.totalExpectedBytes basis table := by
  rw [expected valid basis table enough, ByteReciprocalLimit.totalExpectedBytes_eq valid basis]

omit [Fintype K] [SampleableType K] [NeZero p] in
/-- All inner and outer depths are represented in the completed trace law. -/
theorem all_depths (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → K)
    (event : OptionalRejectionLoop.Result K (Trial p degree K) → Prop) :
    measure basis table {result | event result} = ⨆ outer, ⨆ inner,
      Pr{let result ← program basis table inner outer}[OptionalTraceOrder.loopComplete result ∧ event result] := by
  rw [measure, CompletedObservationLimit.measure_apply]
  simp only [Set.mem_ofPred_eq]
  exact diagonal_sup
    (fun inner outer => Pr{let result ← program basis table inner outer}[OptionalTraceOrder.loopComplete result ∧ event result])
    (fun _ _ _ _ hi ho => ByteLookupTraceOrder.reciprocal basis table hi ho event)

/-- The completed raw reciprocal trace law is normalized without finite
successful-mass rescaling or a retry cap. -/
theorem probability (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → K) (enough : size + 1 < Fintype.card K) : IsProbabilityMeasure (measure basis table) := by
  constructor
  change measure basis table {result | True} = 1
  rw [all_depths]
  have finite (inner outer : ℕ) :
      Pr{let result ← program basis table inner outer}[OptionalTraceOrder.loopComplete result ∧ True] =
      Pr{let result ← program basis table inner outer}[result.value.elim False (fun _ => True)] := by
    apply prEvent_congr
    intro result
    cases tag : result.value <;> simp [OptionalTraceOrder.loopComplete, tag]
  simp_rw [finite]
  exact ByteReciprocalLimit.completion_probability valid basis table enough

end

end FormalProof4FHE.HasteBoots.ReciprocalTraceWork
