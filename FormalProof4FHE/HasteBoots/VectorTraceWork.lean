module

public import FormalProof4FHE.HasteBoots.PairTraceWork
public import FormalProof4FHE.HasteBoots.ObservedVectorTail
public import FormalProof4FHE.HasteBoots.ByteLookupUnbounded

@[expose] public section

/-!
# Completed repeated lookup traces retain every issued byte

The true repetition count multiplies the derived pair support bound and
suspension union bound. Their product proves unfinished vector work tends
to zero, including earlier successful pairs and a suspended last pair.
Proof-only typing then transfers the result to the original unbounded
typed lookup measure used by the staged native security bound.
-/

open OracleSpec OracleComp MeasureTheory
open scoped Classical

namespace FormalProof4FHE.HasteBoots.VectorTraceWork

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  {p degree width size : ℕ} [Module (ZMod p) K] [DecidableEq K]

local instance (repetitions : ℕ) : MeasurableSpace (ByteLookupPairTyped.Raw p degree K repetitions) := ⊤
local instance (repetitions : ℕ) : MeasurableSpace (ByteLookupPairTyped.Sample p degree K repetitions) := ⊤

/-- All earlier pair work and the final partial pair are included. -/
theorem consumed_le (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F)
    (n repetitions : ℕ) (result : ByteLookupPairTyped.Raw p degree K repetitions)
    (supported : result ∈ support (ByteLookupPairVector.program basis table n n n repetitions)) :
    ByteLookupPairVector.consumedBytes result ≤
      repetitions * (CanonicalByteSampler.byteCount p * degree * (n + n * n)) :=
  ObservedVectorTail.consumed_le (ByteLookupPairSampler.program basis table n n n) ByteLookupPairSampler.Result.value
    ByteLookupPairWork.consumedBytes _ (PairTraceWork.consumed_le basis table n n n) repetitions result supported

/-- Fresh calls stop on first suspension; their union bound is a theorem of
the actual vector program rather than an independence certificate. -/
theorem suspended_le (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → Fin width → F)
    (n repetitions : ℕ) :
    Pr{let result ← ByteLookupPairVector.program basis table n n n repetitions}[result.values = none] ≤
      (repetitions : ENNReal) * Pr{let result ← ByteLookupPairSampler.program basis table n n n}[result.value = none] :=
  ObservedVectorTail.suspended_le _ _ repetitions

variable [Fintype K] [SampleableType K] [NeZero p]

/-- A fixed repetition count preserves every polynomial pair-work tail. -/
theorem scaled_suspension_tends_zero (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (enough : size + 1 < Fintype.card K) (repetitions power : ℕ) :
    Filter.Tendsto (fun n : ℕ => (n : ENNReal) ^ power *
      Pr{let result ← ByteLookupPairVector.program basis table n n n repetitions}[result.values = none])
      Filter.atTop (nhds 0) := by
  have total := ENNReal.Tendsto.mul (tendsto_const_nhds (x := (repetitions : ENNReal)))
    (Or.inr (by simp)) (PairTraceWork.scaled_suspension_tends_zero valid basis table enough power) (Or.inr (by simp))
  simp only [mul_zero] at total
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds total (fun _ => bot_le)
  intro n
  exact (mul_le_mul' le_rfl (suspended_le basis table n repetitions)).trans_eq (by dsimp only; ring)

omit [Fintype K] [SampleableType K] [NeZero p] in
/-- The derived support cost is charged even when the vector is incomplete. -/
theorem partial_le (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (n repetitions : ℕ) :
    (∫⁻ value, value ∂𝒟[(fun result => if OptionalTraceOrder.vectorComplete result then 0
      else (ByteLookupPairVector.consumedBytes result : ENNReal)) <$> ByteLookupPairVector.program basis table n n n repetitions]) ≤
      ((repetitions * (CanonicalByteSampler.byteCount p * degree * (n + n * n)) : ℕ) : ENNReal) *
        Pr{let result ← ByteLookupPairVector.program basis table n n n repetitions}[result.values = none] := by
  have bounded : (∫⁻ value, value ∂𝒟[(fun result => if OptionalTraceOrder.vectorComplete result then 0
        else (ByteLookupPairVector.consumedBytes result : ENNReal)) <$> ByteLookupPairVector.program basis table n n n repetitions]) ≤
      ∫⁻ value, value ∂𝒟[(fun result => if result.values = none then
        ((repetitions * (CanonicalByteSampler.byteCount p * degree * (n + n * n)) : ℕ) : ENNReal) else 0) <$>
          ByteLookupPairVector.program basis table n n n repetitions] := by
    rw [lintegral_id_evalDist_map, lintegral_id_evalDist_map]
    apply lintegral_mono_ae
    exact (evalDist_ae_mem_support (ByteLookupPairVector.program basis table n n n repetitions)).mono (fun result reached => by
      by_cases done : result.values = none
      · simp only [OptionalTraceOrder.vectorComplete, done, ne_eq, not_true_eq_false, ite_false, ite_true]
        exact_mod_cast consumed_le basis table n repetitions result reached
      · simp [OptionalTraceOrder.vectorComplete, done])
  rw [CompletedCostTransfer.indicator] at bounded
  exact bounded.trans_eq (mul_comm _ _)

/-- Incomplete work vanishes with the real repetition count fixed; no cap
on the native byte or reciprocal rejection loops is introduced. -/
theorem partial_tends_zero (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (enough : size + 1 < Fintype.card K) (repetitions : ℕ) :
    Filter.Tendsto (fun n => ∫⁻ value, value ∂𝒟[(fun result => if OptionalTraceOrder.vectorComplete result then 0
      else (ByteLookupPairVector.consumedBytes result : ENNReal)) <$> ByteLookupPairVector.program basis table n n n repetitions])
      Filter.atTop (nhds 0) := by
  have added := (scaled_suspension_tends_zero valid basis table enough repetitions 1).add
    (scaled_suspension_tends_zero valid basis table enough repetitions 2)
  have total := ENNReal.Tendsto.mul
    (tendsto_const_nhds (x := (repetitions : ENNReal) * ((CanonicalByteSampler.byteCount p : ENNReal) * (degree : ENNReal))))
    (Or.inr (by simp)) added (Or.inr (by finiteness))
  simp only [mul_zero, add_zero] at total
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds total (fun _ => bot_le)
  intro n
  exact (partial_le basis table n repetitions).trans_eq (by simp only [Nat.cast_mul, Nat.cast_add]; ring)

omit [Fintype K] [SampleableType K] [NeZero p] in
/-- Proof-only typing changes neither completion nor any retained byte cost. -/
theorem typed_partial_mean (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (repetitions n : ℕ) :
    (∫⁻ value, value ∂𝒟[(fun observed => if ByteLookupUnbounded.complete observed then 0
      else (ByteLookupPairVector.consumedBytes observed.raw : ENNReal)) <$> ByteLookupUnbounded.steps basis table repetitions n]) =
      ∫⁻ value, value ∂𝒟[(fun result => if OptionalTraceOrder.vectorComplete result then 0
        else (ByteLookupPairVector.consumedBytes result : ENNReal)) <$> ByteLookupPairVector.program basis table n n n repetitions] := by
  rw [← ByteLookupPairTyped.sample_raw basis table n n n repetitions, Functor.map_map]
  apply congrArg (fun observation : ByteLookupPairTyped.Sample p degree K repetitions → ENNReal =>
    ∫⁻ value, value ∂𝒟[observation <$> ByteLookupPairTyped.sample basis table n n n repetitions])
  funext observed
  simp only [ByteLookupUnbounded.complete, ByteLookupTraceOrder.typed_complete observed]
  by_cases done : observed.values = none <;> simp [done]

/-- Actual completed typed lookup bytes equal the full unconditional vector
mean used by the native sampler, including every rejected raw trial. -/
theorem typed_expected_eq_total (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (enough : size + 1 < Fintype.card K) (repetitions : ℕ) :
    (∫⁻ observed, (ByteLookupPairVector.consumedBytes observed.raw : ENNReal)
      ∂ByteLookupUnbounded.measure basis table repetitions) = ByteLookupPairVector.totalExpectedBytes basis table repetitions := by
  apply CompletedCostTransfer.of_partial_tends_zero
  · have finite (n : ℕ) : (∫⁻ value, value ∂𝒟[(fun observed => (ByteLookupPairVector.consumedBytes observed.raw : ENNReal)) <$>
        ByteLookupUnbounded.steps basis table repetitions n]) = ByteLookupPairVector.expectedBytes basis table n n n repetitions := by
      change _ = (∫⁻ value, value ∂𝒟[(fun result => (ByteLookupPairVector.consumedBytes result : ENNReal)) <$>
        ByteLookupPairVector.program basis table n n n repetitions])
      rw [← ByteLookupPairTyped.sample_raw basis table n n n repetitions, Functor.map_map]
      rfl
    simp_rw [finite]
    exact tendsto_atTop_iSup (ByteLookupPairVector.work_monotone valid basis table repetitions)
  · simp_rw [typed_partial_mean]
    exact partial_tends_zero valid basis table enough repetitions

/-- The exact mean preserves the single pair's conditional-domain average
and the true repetition count, separately from field and packing degrees. -/
theorem typed_expected_formula (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (enough : size + 1 < Fintype.card K) (repetitions : ℕ) :
    (∫⁻ observed, (ByteLookupPairVector.consumedBytes observed.raw : ENNReal)
      ∂ByteLookupUnbounded.measure basis table repetitions) =
        ByteLookupPairWork.totalExpectedBytes basis table * (repetitions : ENNReal) := by
  rw [typed_expected_eq_total valid basis table enough, ByteLookupPairVector.totalExpectedBytes_eq valid basis table enough]


/-- Public size-based work bound on the actual completed typed measure. -/
theorem typed_expected_bound (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → Fin width → F) (enough : size + 1 < Fintype.card K) (repetitions : ℕ) :
    (∫⁻ observed, (ByteLookupPairVector.consumedBytes observed.raw : ENNReal)
      ∂ByteLookupUnbounded.measure basis table repetitions) ≤
        (ByteReciprocalLimit.fieldCost p degree *
          (1 + (Fintype.card K : ENNReal) / ((Fintype.card K - size - 1 : ℕ) : ENNReal))) * (repetitions : ENNReal) := by
  rw [typed_expected_eq_total valid basis table enough]
  exact ByteLookupPairVector.totalExpectedBytes_bound valid basis table enough repetitions

end

end FormalProof4FHE.HasteBoots.VectorTraceWork
