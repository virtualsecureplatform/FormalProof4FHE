module

public import FormalProof4FHE.HasteBoots.ReciprocalTraceWork

@[expose] public section

/-!
# Completed byte-backed pairs retain their actual conditional work

The first field challenge chooses the reciprocal domain. Work tails retain
this dependency and every raw observation; no independent-coordinate or
constant-domain substitution is made. All depths remain analysis prefixes.
-/

open OracleSpec OracleComp MeasureTheory
open scoped Classical BigOperators
open FormalProof4FHE.HasteBoots.ByteLookupPairSampler

namespace FormalProof4FHE.HasteBoots.PairTraceWork

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  {p degree width size : ℕ} [Module (ZMod p) K] [DecidableEq K]

local instance : MeasurableSpace (Result p degree K) := ⊤

/-- Every issued first-challenge and offset byte fits the derived prefix
bound, including either kind of suspension. -/
theorem consumed_le (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F)
    (hashDepth inner outer : ℕ) (result : Result p degree K)
    (supported : result ∈ support (program basis table hashDepth inner outer)) :
    ByteLookupPairWork.consumedBytes result ≤ CanonicalByteSampler.byteCount p * degree * (hashDepth + inner * outer) := by
  simp only [program, support_bind, Set.mem_iUnion] at supported
  obtain ⟨first, reached, branch⟩ := supported
  have head := ReciprocalTraceWork.trial_cost_le basis hashDepth first reached
  cases tag : ByteReciprocalSampler.candidate first with
  | none =>
    simp only [tag, support_pure, Set.mem_singleton_iff] at branch
    subst result
    simp only [ByteLookupPairWork.consumedBytes, Option.elim_none, add_zero]
    exact head.trans (by rw [Nat.mul_add]; omega)
  | some y =>
    simp only [tag, support_map, Set.mem_image] at branch
    obtain ⟨last, last_reached, equal⟩ := branch
    subst result
    have tail := ReciprocalTraceWork.consumed_le basis (hashes table y) inner outer last last_reached
    simpa only [ByteLookupPairWork.consumedBytes, finish, Option.elim_some, Nat.mul_add, Nat.mul_assoc] using
      Nat.add_le_add head tail

variable [Fintype K] [SampleableType K] [NeZero p]

/-- A finite sum retains the rejection tail of every challenge-dependent
domain. This is an auxiliary work-tail bound, not a new security loss. -/
theorem suspended_le (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (hashDepth inner outer : ℕ) :
    Pr{let result ← program basis table hashDepth inner outer}[result.value = none] ≤
      (degree : ENNReal) * RejectionSampling.reject (CanonicalByteSampler.accepted p) ^ hashDepth +
        ((outer : ENNReal) * ((degree : ENNReal) * RejectionSampling.reject (CanonicalByteSampler.accepted p) ^ inner) +
          ∑ y : K, RejectionSampling.reject (ReciprocalDetection.allowed (hashes table y)) ^ outer) := by
  rw [program]
  have bound := prEvent_bind_le_prEvent_add (ByteReciprocalSampler.step basis hashDepth)
    (fun first => match ByteReciprocalSampler.candidate first with
      | none => pure (⟨none, first, none⟩ : Result p degree K)
      | some y => finish first y <$> ByteReciprocalSampler.program basis (hashes table y) inner outer)
    (fun first => ByteReciprocalSampler.candidate first = none) (fun result => result.value = none)
    (ε := (outer : ENNReal) * ((degree : ENNReal) * RejectionSampling.reject (CanonicalByteSampler.accepted p) ^ inner) +
      ∑ y : K, RejectionSampling.reject (ReciprocalDetection.allowed (hashes table y)) ^ outer) (by
        intro first completed
        cases tag : ByteReciprocalSampler.candidate first with
        | none => exact (completed tag).elim
        | some y =>
          have tail := ReciprocalTraceWork.suspended_le valid basis (hashes table y) inner outer
          have pole_le : RejectionSampling.reject (ReciprocalDetection.allowed (hashes table y)) ^ outer ≤
              ∑ z : K, RejectionSampling.reject (ReciprocalDetection.allowed (hashes table z)) ^ outer :=
            Finset.single_le_sum (f := fun z : K =>
              RejectionSampling.reject (ReciprocalDetection.allowed (hashes table z)) ^ outer)
              (fun _ _ => zero_le) (Finset.mem_univ y)
          simpa only [tag, prEvent_map, finish, Option.map_eq_none_iff] using
            tail.trans (add_le_add le_rfl pole_le))
  exact bound.trans (add_le_add (ReciprocalTraceWork.trial_suspended_le basis hashDepth) le_rfl)

/-- Every fixed polynomial multiple of pair suspension probability vanishes.
The finite sum keeps each actual reciprocal domain, including hash collisions. -/
theorem scaled_suspension_tends_zero (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (enough : size + 1 < Fintype.card K) (power : ℕ) :
    Filter.Tendsto (fun n : ℕ => (n : ENNReal) ^ power *
      Pr{let result ← program basis table n n n}[result.value = none]) Filter.atTop (nhds 0) := by
  have bytes := ReciprocalTraceWork.polynomial_geometric power _
    (RejectionSampling.reject_lt_one _ (CanonicalByteSampler.accepted_nonempty p valid))
  have more_bytes := ReciprocalTraceWork.polynomial_geometric (power + 1) _
    (RejectionSampling.reject_lt_one _ (CanonicalByteSampler.accepted_nonempty p valid))
  have first := ENNReal.Tendsto.mul (tendsto_const_nhds (x := (degree : ENNReal)))
    (Or.inr (by simp)) bytes (Or.inr (by simp))
  have second := ENNReal.Tendsto.mul (tendsto_const_nhds (x := (degree : ENNReal)))
    (Or.inr (by simp)) more_bytes (Or.inr (by simp))
  have poles := tendsto_finsetSum Finset.univ (fun y _ => ReciprocalTraceWork.polynomial_geometric power _
    (RejectionSampling.reject_lt_one _ (ReciprocalDetection.allowed_nonempty (hashes table y) enough)))
  have total := first.add (second.add poles)
  simp only [mul_zero, Finset.sum_const_zero, add_zero] at total
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds total (fun _ => bot_le)
  intro n
  exact (mul_le_mul' le_rfl (suspended_le valid basis table n n n)).trans_eq (by
    dsimp only
    rw [mul_add, mul_add, Finset.mul_sum, pow_succ]
    ring)

omit [Fintype K] [SampleableType K] [NeZero p] in
/-- Unfinished pair work is bounded by actual suspension times the derived
finite support cost; the cost of earlier first-challenge work is retained. -/
theorem partial_le (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (n : ℕ) :
    (∫⁻ value, value ∂𝒟[(fun result => if ByteLookupTraceOrder.pairComplete result then 0
      else (ByteLookupPairWork.consumedBytes result : ENNReal)) <$> program basis table n n n]) ≤
      ((CanonicalByteSampler.byteCount p * degree * (n + n * n) : ℕ) : ENNReal) *
        Pr{let result ← program basis table n n n}[result.value = none] := by
  have bounded : (∫⁻ value, value ∂𝒟[(fun result => if ByteLookupTraceOrder.pairComplete result then 0
        else (ByteLookupPairWork.consumedBytes result : ENNReal)) <$> program basis table n n n]) ≤
      ∫⁻ value, value ∂𝒟[(fun result => if result.value = none then
        ((CanonicalByteSampler.byteCount p * degree * (n + n * n) : ℕ) : ENNReal) else 0) <$> program basis table n n n] := by
    rw [lintegral_id_evalDist_map, lintegral_id_evalDist_map]
    apply lintegral_mono_ae
    exact (evalDist_ae_mem_support (program basis table n n n)).mono (fun result reached => by
      by_cases done : result.value = none
      · simp only [ByteLookupTraceOrder.pairComplete, done, ne_eq, not_true_eq_false, ite_false, ite_true]
        exact_mod_cast consumed_le basis table n n n result reached
      · simp [ByteLookupTraceOrder.pairComplete, done])
  rw [CompletedCostTransfer.indicator] at bounded
  exact bounded.trans_eq (mul_comm _ _)

/-- Both sampling stages' incomplete byte work vanishes along common depth. -/
theorem partial_tends_zero (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (enough : size + 1 < Fintype.card K) :
    Filter.Tendsto (fun n => ∫⁻ value, value ∂𝒟[(fun result => if ByteLookupTraceOrder.pairComplete result then 0
      else (ByteLookupPairWork.consumedBytes result : ENNReal)) <$> program basis table n n n]) Filter.atTop (nhds 0) := by
  have added := (scaled_suspension_tends_zero valid basis table enough 1).add
    (scaled_suspension_tends_zero valid basis table enough 2)
  have total := ENNReal.Tendsto.mul
    (tendsto_const_nhds (x := (CanonicalByteSampler.byteCount p : ENNReal) * (degree : ENNReal)))
    (Or.inr (by simp)) added (Or.inr (by finiteness))
  simp only [mul_zero, add_zero] at total
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds total (fun _ => bot_le)
  intro n
  exact (partial_le basis table n).trans_eq (by simp only [Nat.cast_mul, Nat.cast_add]; ring)

/-- Completed full pair observations, including all conditional raw trials. -/
def measure (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F) :=
  CompletedObservationLimit.measure (fun n => program basis table n n n) ByteLookupTraceOrder.pairComplete
    (fun _ _ h => ByteLookupTraceOrder.pair basis table h h h)

/-- Exact completed byte mean equals the unconditional mean with its actual
first-challenge-dependent reciprocal domains. -/
theorem expected_eq_total (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (enough : size + 1 < Fintype.card K) :
    (∫⁻ result, (ByteLookupPairWork.consumedBytes result : ENNReal) ∂measure basis table) =
      ByteLookupPairWork.totalExpectedBytes basis table := by
  apply CompletedCostTransfer.of_partial_tends_zero
  · exact ByteLookupPairDiagonal.work_tends valid basis table
  · exact partial_tends_zero valid basis table enough

/-- Every pair completes almost surely without normalizing finite prefixes. -/
theorem probability (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (enough : size + 1 < Fintype.card K) : IsProbabilityMeasure (measure basis table) := by
  apply CompletedObservationLimit.probability
  have finite (n : ℕ) : Pr{let result ← program basis table n n n}[ByteLookupTraceOrder.pairComplete result] =
      Pr{let result ← program basis table n n n}[result.value.elim False (fun _ => True)] := by
    apply prEvent_congr
    intro result
    cases tag : result.value <;> simp [ByteLookupTraceOrder.pairComplete, tag]
  simp_rw [finite]
  rw [ByteLookupPairDiagonal.law valid basis]
  exact TupleLookupPair.sample_total table enough

end

end FormalProof4FHE.HasteBoots.PairTraceWork
