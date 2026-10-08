/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.GaussianIntegerWeights
import FormalProof4FHE.Probability.NormalizationTV

/-!
# Whole-distribution approximation for the generated Gaussian sampler

The finite rational/integer generator is compared with the exact centered
integer Gaussian, including the finite interval's omitted tail and both
normalizers. Mapping modulo any positive modulus preserves the bound.
No ideal probability or real exponential is evaluated by the generator.
-/

open scoped BigOperators ENNReal

namespace FormalProof4FHE.GaussianSamplerTV

open GaussianIntegerWeights LatticeCrypto

/-- A unique stored outcome contributes its weight, even if that weight is zero. -/
theorem outcomeWeight_map_of_nodup {Output : Type} [DecidableEq Output]
    (weights : Output → ℕ) (values : List Output) (hvalues : values.Nodup) (output : Output) :
    WeightedSampler.outcomeWeight (values.map fun value ↦ (value, weights value)) output =
      if output ∈ values then weights output else 0 := by
  induction values with
  | nil => simp [WeightedSampler.outcomeWeight]
  | cons first rest ih =>
    have hn := List.nodup_cons.mp hvalues
    by_cases hfirst : first = output
    · subst first
      simp [WeightedSampler.outcomeWeight, ih hn.2, hn.1]
    · simp [WeightedSampler.outcomeWeight, ih hn.2, hfirst, Ne.symm hfirst]

/-- The finite list of integer outcomes in the actual generated table. -/
def cutoffValues (width : ℕ) : List ℤ :=
  (List.range (2 * width ^ 2 + 1)).map fun index : ℕ ↦ (index : ℤ) - (width ^ 2 : ℕ)

theorem cutoffValues_nodup (width : ℕ) : (cutoffValues width).Nodup := by
  apply List.Nodup.map _ List.nodup_range
  intro first second heq
  exact Int.ofNat_inj.mp (sub_left_inj.mp heq)

theorem cutoffValues_mem_iff (width : ℕ) (value : ℤ) :
    value ∈ cutoffValues width ↔ value.natAbs ≤ width ^ 2 := by
  constructor
  · intro hvalue
    obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hvalue
    have hi := List.mem_range.mp hindex
    apply Int.ofNat_le.mp
    rw [Int.natCast_natAbs, abs_le]
    constructor <;> omega
  · intro hvalue
    have hb := Int.ofNat_le.mpr hvalue
    rw [Int.natCast_natAbs, abs_le] at hb
    have hnonneg : 0 ≤ value + (width ^ 2 : ℕ) := by omega
    have hindex : ((value + (width ^ 2 : ℕ)).toNat : ℤ) = value + (width ^ 2 : ℕ) :=
      Int.toNat_of_nonneg hnonneg
    apply List.mem_map.mpr
    refine ⟨(value + (width ^ 2 : ℕ)).toNat, List.mem_range.mpr (by omega), ?_⟩
    omega

theorem entries_eq_cutoff_map (width precision : ℕ) :
    entries width precision =
      (cutoffValues width).map fun value ↦ (value, integerWeight width precision value) := by
  simp [entries, cutoffValues, List.map_map]

/-- Exact numerator of every output, including zero probabilities outside the cutoff. -/
theorem outcomeWeight_entries (width precision : ℕ) (value : ℤ) :
    WeightedSampler.outcomeWeight (entries width precision) value =
      if value.natAbs ≤ width ^ 2 then integerWeight width precision value else 0 := by
  rw [entries_eq_cutoff_map, outcomeWeight_map_of_nodup _ _ (cutoffValues_nodup width)]
  simp only [cutoffValues_mem_iff]

/-- Real form of the actual sampler's exact normalized probability. -/
theorem table_outputPMF_toReal (width precision : ℕ) (value : ℤ) :
    ((table width precision).outputPMF value).toReal =
      (if value.natAbs ≤ width ^ 2 then (integerWeight width precision value : ℝ) else 0) /
        ((table width precision).ticketCount : ℝ) := by
  rw [WeightedSampler.Table.outputPMF_apply]
  change (((WeightedSampler.outcomeWeight (entries width precision) value : ℝ≥0∞) /
      ((table width precision).ticketCount : ℝ≥0∞))).toReal = _
  rw [outcomeWeight_entries, ENNReal.toReal_div]
  by_cases hvalue : value.natAbs ≤ width ^ 2 <;> simp [hvalue]

/-- Scale the implementation PMF by its raw normalizer divided by the ideal normalizer. -/
noncomputable def normalizationScale (width precision : ℕ) : ℝ :=
  (((table width precision).ticketCount : ℝ) / (2 : ℝ) ^ precision) /
    discreteGaussianSum width 0

/-- Scaling removes the generated normalizer exactly. -/
theorem scaled_table_output (width precision : ℕ) (hwidth : 0 < width) (value : ℤ) :
    normalizationScale width precision * ((table width precision).outputPMF value).toReal =
      if value.natAbs ≤ width ^ 2 then
        ((integerWeight width precision value : ℝ) / (2 : ℝ) ^ precision) /
          discreteGaussianSum width 0 else 0 := by
  rw [normalizationScale, table_outputPMF_toReal]
  by_cases hvalue : value.natAbs ≤ width ^ 2
  · rw [if_pos hvalue, if_pos hvalue]
    have hw : (0 : ℝ) < (table width precision).ticketCount := by
      exact_mod_cast totalWeight_pos width precision
    have hz := discreteGaussianSum_pos (width : ℝ) 0 (Nat.cast_pos.mpr hwidth)
    field_simp [ne_of_gt hw, ne_of_gt hz]
  · simp [hvalue]

/-- A finite set used only to sum the cutoff's error envelope. -/
def cutoffSet (width : ℕ) : Finset ℤ := (cutoffValues width).toFinset

theorem cutoffSet_mem_iff (width : ℕ) (value : ℤ) :
    value ∈ cutoffSet width ↔ value.natAbs ≤ width ^ 2 := by
  simp only [cutoffSet, List.mem_toFinset, cutoffValues_mem_iff]

theorem cutoffSet_card (width : ℕ) : (cutoffSet width).card = 2 * width ^ 2 + 1 := by
  rw [cutoffSet, List.toFinset_card_of_nodup (cutoffValues_nodup width)]
  simp [cutoffValues]

/-- The already proved per-weight approximation envelope. -/
noncomputable def weightError (width precision : ℕ) : ℝ :=
  ((expansionPower width : ℝ) + 1) / (2 : ℝ) ^ precision

/-- Finite approximation plus the omitted ideal probability tail. -/
noncomputable def approximationBound (width precision : ℕ) : ℝ :=
  ((2 * width ^ 2 + 1 : ℕ) : ℝ) * weightError width precision +
    4 * Real.exp (-(width : ℝ) ^ 2 / 2)

/-- Pointwise comparison before renormalizing the generated table. -/
theorem scaled_error_pointwise_le (width precision : ℕ) (hwidth : 0 < width) (value : ℤ) :
    |(discreteGaussianDist width 0 (Nat.cast_pos.mpr hwidth) value).toReal -
      normalizationScale width precision * ((table width precision).outputPMF value).toReal| ≤
      (if value ∈ cutoffSet width then weightError width precision else 0) +
        (if width ^ 2 < value.natAbs then discreteGaussianPMF width 0 value else 0) := by
  rw [discreteGaussianDist_apply, scaled_table_output width precision hwidth]
  by_cases hvalue : value.natAbs ≤ width ^ 2
  · rw [if_pos hvalue, if_pos ((cutoffSet_mem_iff width value).2 hvalue),
      if_neg (not_lt_of_ge hvalue), add_zero]
    have hz := discreteGaussianSum_pos (width : ℝ) 0 (Nat.cast_pos.mpr hwidth)
    have herr := integerWeight_error_le width precision hwidth value hvalue
    have hraw : discreteGaussianWeight width 0 value =
        Real.exp (-((value : ℝ) ^ 2) / (2 * (width : ℝ) ^ 2)) := by
      simp [discreteGaussianWeight]
    unfold discreteGaussianPMF
    rw [show discreteGaussianWeight width 0 value / discreteGaussianSum width 0 -
        ((integerWeight width precision value : ℝ) / (2 : ℝ) ^ precision) /
          discreteGaussianSum width 0 =
      (discreteGaussianWeight width 0 value - (integerWeight width precision value : ℝ) /
        (2 : ℝ) ^ precision) / discreteGaussianSum width 0 by ring]
    rw [abs_div, abs_of_pos hz, hraw, abs_sub_comm]
    exact (div_le_div_of_nonneg_right herr hz.le).trans
      (div_le_self (by positivity)
        (DiscreteGaussianTail.normalizer_ge_one _ (Nat.cast_pos.mpr hwidth)))
  · have hbad : width ^ 2 < value.natAbs := Nat.lt_of_not_ge hvalue
    rw [if_neg hvalue, if_neg (fun h ↦ hvalue ((cutoffSet_mem_iff width value).1 h)),
      if_pos hbad, zero_add, sub_zero]
    rw [abs_of_nonneg (discreteGaussianPMF_nonneg width 0 (Nat.cast_pos.mpr hwidth) value)]

/-- Complete error sum, with no dependence on the coefficient modulus or an assumed certificate. -/
theorem scaled_error_sum_le (width precision : ℕ) (hwidth : 0 < width) :
    (∑' value : ℤ,
      |(discreteGaussianDist width 0 (Nat.cast_pos.mpr hwidth) value).toReal -
        normalizationScale width precision * ((table width precision).outputPMF value).toReal|) ≤
      approximationBound width precision := by
  let inside : ℤ → ℝ := fun value ↦ if value ∈ cutoffSet width then weightError width precision else 0
  let outside : ℤ → ℝ := fun value ↦
    if width ^ 2 < value.natAbs then discreteGaussianPMF width 0 value else 0
  have hinside : Summable inside := summable_of_ne_finset_zero (s := cutoffSet width) (by
    intro value hvalue
    simp [inside, hvalue])
  have houtside : Summable outside := DiscreteGaussianTail.tail_terms_summable width
    (Nat.cast_pos.mpr hwidth) (width ^ 2)
  have hinsideSum : (∑' value, inside value) = ((2 * width ^ 2 + 1 : ℕ) : ℝ) * weightError width precision := by
    rw [tsum_eq_sum (s := cutoffSet width) (fun value hvalue ↦ by simp [inside, hvalue])]
    simp [inside, cutoffSet_card]
  have herror := ((NormalizationTV.pmf_real_summable
      (discreteGaussianDist width 0 (Nat.cast_pos.mpr hwidth))).sub
      ((NormalizationTV.pmf_real_summable (table width precision).outputPMF).mul_left
        (normalizationScale width precision))).abs
  have h := herror.tsum_le_tsum (scaled_error_pointwise_le width precision hwidth)
    (hinside.add houtside)
  rw [hinside.tsum_add houtside, hinsideSum] at h
  apply h.trans
  change ((2 * width ^ 2 + 1 : ℕ) : ℝ) * weightError width precision +
      DiscreteGaussianTail.tailMass width (width ^ 2) ≤
    ((2 * width ^ 2 + 1 : ℕ) : ℝ) * weightError width precision + 4 * Real.exp (-(width : ℝ) ^ 2 / 2)
  exact add_le_add le_rfl (DiscreteGaussianTail.tailMass_square_le width hwidth)

/-- The concrete integer sampler is close to the ideal Gaussian, including normalization and tail. -/
theorem integer_etvDist_le (width precision : ℕ) (hwidth : 0 < width) :
    (table width precision).outputPMF.etvDist (discreteGaussianDist width 0 (Nat.cast_pos.mpr hwidth)) ≤
      ENNReal.ofReal (approximationBound width precision) := by
  rw [PMF.etvDist_comm]
  exact NormalizationTV.etvDist_le_of_scaled_error _ _ (normalizationScale width precision) _
    (scaled_error_sum_le width precision hwidth)

/-- The exact modular output PMF is the mapped integer output PMF. -/
theorem modular_outputPMF_eq_map (modulus width precision : ℕ) :
    (modularTable modulus width precision).outputPMF =
      (fun value : ℤ ↦ (value : ZMod modulus)) <$> (table width precision).outputPMF := by
  simp only [WeightedSampler.Table.outputPMF, modularTable_sampler_eq_map, liftM_map]

/-- Reduction modulo any positive modulus adds no TV error or modulus-size factor. -/
theorem modular_etvDist_le (modulus width precision : ℕ) [NeZero modulus] (hwidth : 0 < width) :
    (modularTable modulus width precision).outputPMF.etvDist
      (ModularGaussian.distribution modulus width (Nat.cast_pos.mpr hwidth)) ≤
        ENNReal.ofReal (approximationBound width precision) := by
  rw [modular_outputPMF_eq_map, ModularGaussian.distribution]
  exact (PMF.etvDist_map_le _ _ _).trans (integer_etvDist_le width precision hwidth)

/-- Fully proved approximation certificate; its stored table is the computable generator. -/
noncomputable def modularCertificate (modulus width precision : ℕ) [NeZero modulus] (hwidth : 0 < width) :
    WeightedSampler.Table.Certificate
      (ModularGaussian.distribution modulus width (Nat.cast_pos.mpr hwidth)) where
  table := modularTable modulus width precision
  bound := ENNReal.ofReal (approximationBound width precision)
  bound_ne_top := ENNReal.ofReal_ne_top
  valid := by
    rw [← WeightedSampler.Table.etvDist_outputPMF_eq_certificateError]
    exact modular_etvDist_le modulus width precision hwidth


/-- The certificate's runtime data are exactly the existing computable table. -/
theorem modularCertificate_table (modulus width precision : ℕ) [NeZero modulus] (hwidth : 0 < width) :
    (modularCertificate modulus width precision hwidth).table = modularTable modulus width precision := rfl

theorem modularCertificate_bound (modulus width precision : ℕ) [NeZero modulus] (hwidth : 0 < width) :
    (modularCertificate modulus width precision hwidth).bound =
      ENNReal.ofReal (approximationBound width precision) := rfl

theorem weightError_family (dimension : ℕ) :
    weightError (dimension + 1) (familyPrecision dimension) = pointwiseErrorBound dimension := by
  unfold weightError expansionPower pointwiseErrorBound
  push_cast
  ring

/-- The complete normalized sampler approximation is negligible for the concrete family.
No negligible-certificate-error premise remains. -/
theorem approximationBound_family_negligible :
    negligible (fun dimension ↦ ENNReal.ofReal
      (approximationBound (dimension + 1) (familyPrecision dimension))) := by
  have hfinite : negligible (fun dimension ↦
      ((2 * (dimension + 1) ^ 2 + 1 : ℕ) : ℝ≥0∞) *
        ENNReal.ofReal (pointwiseErrorBound dimension)) := by
    have h := negligible_polynomial_mul pointwiseErrorBound_negligible
      ((2 * (Polynomial.X + 1) ^ 2 + 1) : Polynomial ℕ)
    simpa using h
  apply negligible_of_le (g := fun dimension ↦
    ((2 * (dimension + 1) ^ 2 + 1 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (pointwiseErrorBound dimension) +
      ENNReal.ofReal (4 * Real.exp (-((dimension + 1 : ℕ) : ℝ) ^ 2 / 2)))
  · intro dimension
    unfold approximationBound
    rw [weightError_family,
      ENNReal.ofReal_add (by unfold pointwiseErrorBound; positivity) (by positivity),
      ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  · exact negligible_add hfinite DiscreteGaussianTail.gaussian_tail_bound_negligible

end FormalProof4FHE.GaussianSamplerTV
