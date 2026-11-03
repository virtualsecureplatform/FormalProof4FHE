module

public import FormalProof4FHE.HasteBoots.ByteReciprocalSampler

@[expose] public section

/-!
# Unbounded byte-backed reciprocal law and work from all nested prefixes

Both inner coefficient and outer reciprocal prefixes are analysis
approximations. Their directed limits keep partial-trial work, converge to
the accepted reciprocal-domain law, and give the exact expected byte cost.
No retry cap, observed maximum or cost/value independence is assumed.
-/

open OracleSpec OracleComp MeasureTheory
open scoped Classical BigOperators
open FormalProof4FHE.HasteBoots.ByteReciprocalSampler

namespace FormalProof4FHE.HasteBoots.ByteReciprocalLimit

noncomputable section

def geometricSum (rate : ENNReal) (outer : ℕ) : ENNReal := ∑ attempt ∈ Finset.range outer, rate ^ attempt

theorem geometric_tends {rate : ℕ → ENNReal} {limit : ENNReal}
    (known : Filter.Tendsto rate Filter.atTop (nhds limit)) (outer : ℕ) :
    Filter.Tendsto (fun inner => geometricSum (rate inner) outer) Filter.atTop (nhds (geometricSum limit outer)) := by
  induction outer with
  | zero => simpa only [geometricSum, Finset.range_zero, Finset.sum_empty] using (tendsto_const_nhds (x := (0 : ENNReal)))
  | succ outer ih =>
    have total := ih.add (ENNReal.Tendsto.pow (n := outer) known)
    simpa only [geometricSum, Finset.sum_range_succ] using total

theorem geometric_ne_top (rate : ENNReal) (bounded : rate ≤ 1) (outer : ℕ) : geometricSum rate outer ≠ ⊤ := by
  apply ne_of_lt
  calc _ ≤ ∑ _ ∈ Finset.range outer, (1 : ENNReal) := Finset.sum_le_sum (fun _ _ => pow_le_one₀ zero_le bounded)
       _ = (outer : ENNReal) := by simp
       _ < ⊤ := by simp

theorem completion_monotone (p degree : ℕ) : Monotone (completion p degree) := by
  intro first second ordered
  unfold completion
  gcongr
  exact CanonicalCoefficientVector.completion_monotone p ordered

theorem completion_tends (p degree : ℕ) (valid : 1 < p) [NeZero p] :
    Filter.Tendsto (completion p degree) Filter.atTop (nhds 1) := by
  change Filter.Tendsto (fun inner => CanonicalCoefficientVector.completion p inner ^ (1 * degree)) Filter.atTop (nhds 1)
  simpa only [one_pow] using ENNReal.Tendsto.pow (n := 1 * degree) (CanonicalCoefficientVector.completion_tends_to_one p valid)

def fieldCost (p degree : ℕ) : ENNReal := ((1 * degree : ℕ) : ENNReal) * CanonicalByteSampler.totalExpectedBytes p

theorem fieldCost_ne_top (p degree : ℕ) (valid : 1 < p) : fieldCost p degree ≠ ⊤ := by
  have upper : (CanonicalByteSampler.byteCount p : ENNReal) * 2 < ⊤ :=
    lt_top_iff_ne_top.mpr (ENNReal.mul_ne_top (by simp) (by simp))
  have finite := lt_trans (CanonicalByteSampler.totalExpectedBytes_lt_twice p valid) upper
  unfold fieldCost
  exact ENNReal.mul_ne_top (by simp) finite.ne

variable {p degree size : ℕ} {K : Type} [Field K] [Module (ZMod p) K]
  [DecidableEq K] [Fintype K] [SampleableType K] [NeZero p]

omit [Module (ZMod p) K] in
theorem rate_tends (valid : 1 < p) (table : Fin size → K) :
    Filter.Tendsto (fun inner => completion p degree inner * RejectionSampling.reject (ReciprocalDetection.allowed table))
      Filter.atTop (nhds (RejectionSampling.reject (ReciprocalDetection.allowed table))) := by
  have known := ENNReal.Tendsto.mul (completion_tends p degree valid) (Or.inl (by simp))
    (tendsto_const_nhds (x := RejectionSampling.reject (ReciprocalDetection.allowed table))) (Or.inr (by simp))
  simpa only [one_mul] using known

/-- For each fixed outer prefix, completing the inner byte approximations
recovers the actual uniform-field rejection prefix law. -/
theorem probability_tends (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → K) (outer : ℕ) (event : K → Prop) :
    Filter.Tendsto (fun inner => Pr{let result ← program basis table inner outer}[result.value.elim False event])
      Filter.atTop (nhds (geometricSum (RejectionSampling.reject (ReciprocalDetection.allowed table)) outer *
        RejectionSampling.hit (ReciprocalDetection.allowed table) event)) := by
  have sums := geometric_tends (rate_tends (degree := degree) valid table) outer
  have hits := ENNReal.Tendsto.mul (completion_tends p degree valid) (Or.inl (by simp))
    (tendsto_const_nhds (x := RejectionSampling.hit (ReciprocalDetection.allowed table) event)) (Or.inr (by simp))
  have hits' : Filter.Tendsto
      (fun inner => completion p degree inner * RejectionSampling.hit (ReciprocalDetection.allowed table) event)
      Filter.atTop (nhds (RejectionSampling.hit (ReciprocalDetection.allowed table) event)) := by
    simpa only [one_mul] using hits
  have finiteHit : RejectionSampling.hit (ReciprocalDetection.allowed table) event ≠ ⊤ := ne_of_lt (prEvent_lt_top _)
  have total := ENNReal.Tendsto.mul sums (Or.inr finiteHit) hits'
    (Or.inr (geometric_ne_top _ (prEvent_le_one _) outer))
  simpa only [ByteReciprocalSampler.probability valid basis, geometricSum, one_mul, RejectionSampling.reject] using total

theorem probability_monotone_inner (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → K) (outer : ℕ) (event : K → Prop) :
    Monotone (fun inner => Pr{let result ← program basis table inner outer}[result.value.elim False event]) := by
  intro first second ordered
  dsimp only
  rw [ByteReciprocalSampler.probability valid basis, ByteReciprocalSampler.probability valid basis]
  have grows := completion_monotone p degree ordered
  gcongr

theorem probability_monotone_outer (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → K) (inner : ℕ) (event : K → Prop) :
    Monotone (fun outer => Pr{let result ← program basis table inner outer}[result.value.elim False event]) := by
  intro first second ordered
  dsimp only
  rw [ByteReciprocalSampler.probability valid basis, ByteReciprocalSampler.probability valid basis]
  exact mul_le_mul_left (Finset.sum_le_sum_of_subset (Finset.range_mono ordered)) _

theorem probability_iSup_inner (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K)
    (table : Fin size → K) (outer : ℕ) (event : K → Prop) :
    (⨆ inner, Pr{let result ← program basis table inner outer}[result.value.elim False event]) =
      geometricSum (RejectionSampling.reject (ReciprocalDetection.allowed table)) outer *
        RejectionSampling.hit (ReciprocalDetection.allowed table) event :=
  tendsto_nhds_unique (tendsto_atTop_iSup (probability_monotone_inner valid basis table outer event))
    (probability_tends valid basis table outer event)

/-- The unbounded law uses every nested operational approximation, rather
than selecting either approximation as a protocol budget. -/
def eventProbability (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → K) (event : K → Prop) : ENNReal :=
  ⨆ outer, ⨆ inner, Pr{let result ← program basis table inner outer}[result.value.elim False event]

/-- The complete raw-byte/field/reciprocal composition has the exact ideal
accepted-domain law already used by the staged lookup security theorem. -/
theorem law (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → K) (event : K → Prop) :
    eventProbability basis table event = Pr{let value ← ReciprocalDetection.sample table}[event value] := by
  unfold eventProbability
  simp_rw [probability_iSup_inner valid basis]
  have ideal := RejectionSampling.eventProbability_eq_uniform (ReciprocalDetection.allowed table) event
  unfold RejectionSampling.eventProbability at ideal
  simp_rw [RejectionSampling.success_probability] at ideal
  exact ideal

/-- Nonemptiness gives full eventual successful mass without a retry cap. -/
theorem completion_probability (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → K)
    (enough : size + 1 < Fintype.card K) : eventProbability basis table (fun _ => True) = 1 := by
  rw [law valid basis]
  exact ReciprocalDetection.sample_total table enough

/-- Work convergence includes the partially sampled last field trial. -/
theorem work_tends (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → K) (outer : ℕ) :
    Filter.Tendsto (fun inner => expectedBytes basis table inner outer) Filter.atTop
      (nhds (fieldCost p degree * geometricSum (RejectionSampling.reject (ReciprocalDetection.allowed table)) outer)) := by
  have total := ENNReal.Tendsto.mul (CanonicalCoefficientWork.expectedBytes_tends_to p valid (1 * degree))
    (Or.inr (geometric_ne_top _ (prEvent_le_one _) outer)) (geometric_tends (rate_tends (degree := degree) valid table) outer)
    (Or.inr (fieldCost_ne_top p degree valid))
  simpa only [expectedBytes_formula valid basis, geometricSum, fieldCost, RejectionSampling.reject] using total

theorem work_monotone_inner (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → K) (outer : ℕ) :
    Monotone (fun inner => expectedBytes basis table inner outer) := by
  intro first second ordered
  dsimp only
  rw [expectedBytes_formula valid basis, expectedBytes_formula valid basis]
  have grows := completion_monotone p degree ordered
  have costs := CanonicalCoefficientWork.expectedBytes_monotone p (1 * degree) ordered
  gcongr

theorem work_iSup_inner (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → K) (outer : ℕ) :
    (⨆ inner, expectedBytes basis table inner outer) =
      fieldCost p degree * geometricSum (RejectionSampling.reject (ReciprocalDetection.allowed table)) outer :=
  tendsto_nhds_unique (tendsto_atTop_iSup (work_monotone_inner valid basis table outer)) (work_tends valid basis table outer)

def totalExpectedBytes (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → K) : ENNReal :=
  ⨆ outer, ⨆ inner, expectedBytes basis table inner outer

/-- Exact unbounded bytes: one field draw's actual canonical-byte cost times
the expected accepted-domain rejection count. Cost/value independence is not
assumed; every started field trial was charged before checking its value. -/
theorem totalExpectedBytes_eq (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → K) :
    totalExpectedBytes basis table = fieldCost p degree *
      ((Fintype.card K : ENNReal) / (ReciprocalDetection.allowed table).card) := by
  unfold totalExpectedBytes
  simp_rw [work_iSup_inner valid basis]
  rw [← ENNReal.mul_iSup]
  change fieldCost p degree * (⨆ outer, ∑ attempt ∈ Finset.range outer,
    RejectionSampling.reject (ReciprocalDetection.allowed table) ^ attempt) = _
  rw [← ENNReal.tsum_eq_iSup_nat, ENNReal.tsum_geometric]
  rw [← RejectionSampling.totalExpectedAttempts_eq, RejectionSampling.totalExpectedAttempts_fraction]

/-- Public size bound retains duplicate-pole behavior in the exact formula
and never substitutes an empirical or maximum retry count. -/
theorem totalExpectedBytes_bound (valid : 1 < p) (basis : Module.Basis (Fin degree) (ZMod p) K) (table : Fin size → K) :
    totalExpectedBytes basis table ≤ fieldCost p degree *
      ((Fintype.card K : ENNReal) / ((Fintype.card K - size - 1 : ℕ) : ENNReal)) := by
  rw [totalExpectedBytes_eq valid basis]
  gcongr
  exact_mod_cast ReciprocalDetection.allowed_card_lower table

end

end FormalProof4FHE.HasteBoots.ByteReciprocalLimit
