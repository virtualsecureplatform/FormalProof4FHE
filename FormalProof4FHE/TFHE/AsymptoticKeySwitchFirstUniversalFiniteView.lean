/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.MajorityAmplificationBounds
import FormalProof4FHE.TFHE.AsymptoticKeySwitchFirstFiniteView

/-!
# Adaptive TFHE Security from Universal Polynomial-View Augmented Search

A single fixed polynomial-size majority schedule cannot make the recovery error negligible for
every possible inverse-polynomial decision advantage.  The standard search-to-decision argument
instead chooses a different polynomial schedule for each exponent in the definition of
negligibility.  This module formalizes that quantifier order.

The resulting TFHE theorem has no amplification-error or capped-residual security premise.  Its
only nonstandard cryptographic premise is security of the same native augmented scalar-search
problem for every polynomial-view schedule.  Ordinary post-cut ring and scalar LWE premises are
retained exactly as before.
-/

open ENNReal OracleComp Filter Topology

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView

open FormalProof4FHE.MajorityAmplification
open FormalProof4FHE.TFHE.Encryption.Adaptive.KeySwitchFirstFiniteView

/-! ## Canonical logarithmic schedules -/

/-- The polynomial-view schedule used for one chosen pair of inverse-polynomial strengths. -/
noncomputable def logarithmicViewSchedule {Message : Type}
    (params : Parameters Message)
    (reference : (securityParameter : ℕ) → Fin (params.lweDimension securityParameter))
    (dimensionPolynomial : Polynomial ℕ)
    (hDimension : ∀ securityParameter,
      params.lweDimension securityParameter ≤
        dimensionPolynomial.eval securityParameter)
    (warmupStrength cooldownStrength : ℕ) :
    PolynomialViewSchedule params :=
  polynomialViewScheduleOfBounds params
    (logarithmicRounds warmupStrength cooldownStrength)
    reference dimensionPolynomial
    (logarithmicViewPolynomial warmupStrength cooldownStrength)
    hDimension
    (three_pow_logarithmicRounds_le_polynomial warmupStrength cooldownStrength)

@[simp]
theorem logarithmicViewSchedule_rounds {Message : Type}
    (params : Parameters Message)
    (reference : (securityParameter : ℕ) → Fin (params.lweDimension securityParameter))
    (dimensionPolynomial : Polynomial ℕ)
    (hDimension : ∀ securityParameter,
      params.lweDimension securityParameter ≤
        dimensionPolynomial.eval securityParameter)
    (warmupStrength cooldownStrength securityParameter : ℕ) :
    (logarithmicViewSchedule params reference dimensionPolynomial hDimension
      warmupStrength cooldownStrength).rounds securityParameter =
      logarithmicRounds warmupStrength cooldownStrength securityParameter := rfl

/-! ## Connecting the analytic estimate to the TFHE residual -/

/-- The balanced threshold has the expected real presentation. -/
theorem balancedThreshold_toReal
    {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    (balancedThreshold ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget distinguisher).toReal =
      (2 - decisionAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget distinguisher) / 4 := by
  unfold balancedThreshold
  rw [ENNReal.toReal_ofReal]
  have h := decisionAdvantage_le_one ringErrorSampler keySwitchErrorSampler
    inputErrorSampler tgswGadget keySwitchGadget distinguisher
  linarith

/-- Exact real form of the summed balanced majority error. -/
theorem balancedAmplificationError_toReal
    {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    (balancedAmplificationError ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget rounds distinguisher).toReal =
      (lweDimension : ℝ) * amplifiedErrorReal rounds
        ((2 - decisionAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget distinguisher) / 4) := by
  rw [balancedAmplificationError_eq_natCast_mul, ENNReal.toReal_mul,
    ENNReal.toReal_natCast,
    amplifiedError_toReal rounds
      (balancedThreshold_le_one ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget distinguisher),
    balancedThreshold_toReal]

/-- Pointwise inverse-polynomial bound on the advantage-capped residual for a canonical
logarithmic schedule. -/
theorem balancedResidual_logarithmicViewSchedule_le
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (reference : (securityParameter : ℕ) → Fin (params.lweDimension securityParameter))
    (dimensionPolynomial : Polynomial ℕ)
    (hDimension : ∀ securityParameter,
      params.lweDimension securityParameter ≤
        dimensionPolynomial.eval securityParameter)
    (warmupStrength cooldownStrength : ℕ)
    (adversary : PolynomialQueryAdversary params)
    (securityParameter : ℕ) :
    balancedResidual params
        (logarithmicViewSchedule params reference dimensionPolynomial hDimension
          warmupStrength cooldownStrength)
        adversary securityParameter ≤
      ENNReal.ofReal
        (((((securityParameter + 1 : ℕ) : ℝ) ^ warmupStrength)⁻¹) / 2 +
          (params.lweDimension securityParameter : ℝ) *
            (((((securityParameter + 1 : ℕ) : ℝ) ^ cooldownStrength)⁻¹) / 4)) := by
  let distinguisher := bundleDistinguisher
    (Adaptive.KeySwitchFirstSecurity.toPublicDistinguisher
      (queryCount := adversary.queryCount securityParameter)
      (params.encode securityParameter)
      (adversary.run securityParameter))
  let advantage := decisionAdvantage
    (params.ringErrorSampler securityParameter)
    (params.keySwitchErrorSampler securityParameter)
    (params.inputErrorSampler securityParameter)
    (params.tgswGadget securityParameter)
    (params.keySwitchGadget securityParameter)
    distinguisher
  have hadvantage_nonneg : 0 ≤ advantage :=
    decisionAdvantage_nonneg
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.inputErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      distinguisher
  have hadvantage_one : advantage ≤ 1 :=
    decisionAdvantage_le_one
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.inputErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      distinguisher
  apply ENNReal.ofReal_le_ofReal
  have hbound := min_dimension_mul_amplifiedErrorReal_half_advantage_le
    (params.lweDimension securityParameter) warmupStrength cooldownStrength
    securityParameter hadvantage_nonneg hadvantage_one
  simpa only [balancedResidual, Adaptive.KeySwitchFirstFiniteView.balancedResidual,
    logarithmicViewSchedule_rounds, distinguisher, advantage,
    balancedAmplificationError_toReal, mul_div_assoc] using hbound

/-! ## One schedule for each negligibility exponent -/

/-- Canonical schedule selected while proving the `power`th limit in superpolynomial decay. -/
noncomputable def negligibilitySchedule {Message : Type}
    (params : Parameters Message)
    (reference : (securityParameter : ℕ) → Fin (params.lweDimension securityParameter))
    (dimensionPolynomial : Polynomial ℕ)
    (hDimension : ∀ securityParameter,
      params.lweDimension securityParameter ≤
        dimensionPolynomial.eval securityParameter)
    (power : ℕ) : PolynomialViewSchedule params :=
  logarithmicViewSchedule params reference dimensionPolynomial hDimension
    (2 + power) (2 + power + dimensionPolynomial.natDegree)

/-- After multiplying by the selected power of the security parameter, the capped residual is
bounded by a constant times an inverse square. -/
theorem pow_mul_balancedResidual_negligibilitySchedule_le
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (reference : (securityParameter : ℕ) → Fin (params.lweDimension securityParameter))
    (dimensionPolynomial : Polynomial ℕ)
    (hDimension : ∀ securityParameter,
      params.lweDimension securityParameter ≤
        dimensionPolynomial.eval securityParameter)
    (power : ℕ) (adversary : PolynomialQueryAdversary params)
    (securityParameter : ℕ) :
    (securityParameter : ENNReal) ^ power *
        balancedResidual params
          (negligibilitySchedule params reference dimensionPolynomial hDimension power)
          adversary securityParameter ≤
      ENNReal.ofReal
        ((1 / 2 + (polynomialCoefficientSum dimensionPolynomial : ℝ) / 4) *
          ((((securityParameter + 1 : ℕ) : ℝ) ^ 2)⁻¹)) := by
  let scale : ℝ := ((securityParameter + 1 : ℕ) : ℝ)
  let residualBound : ℝ :=
    (scale ^ (2 + power))⁻¹ / 2 +
      (params.lweDimension securityParameter : ℝ) *
        ((scale ^ (2 + power + dimensionPolynomial.natDegree))⁻¹ / 4)
  let finalBound : ℝ :=
    (1 / 2 + (polynomialCoefficientSum dimensionPolynomial : ℝ) / 4) *
      (scale ^ 2)⁻¹
  have hresidual := balancedResidual_logarithmicViewSchedule_le
    params reference dimensionPolynomial hDimension
    (2 + power) (2 + power + dimensionPolynomial.natDegree)
    adversary securityParameter
  have hdimensionNat : params.lweDimension securityParameter ≤
      polynomialCoefficientSum dimensionPolynomial *
        (securityParameter + 1) ^ dimensionPolynomial.natDegree :=
    (hDimension securityParameter).trans
      (polynomial_eval_le_coefficientSum_mul_add_one_pow
        dimensionPolynomial securityParameter)
  have hdimensionReal : (params.lweDimension securityParameter : ℝ) ≤
      (polynomialCoefficientSum dimensionPolynomial : ℝ) *
        scale ^ dimensionPolynomial.natDegree := by
    dsimp only [scale]
    exact_mod_cast hdimensionNat
  have hscaled : (securityParameter : ℝ) ^ power * residualBound ≤ finalBound := by
    have h := pow_mul_inverse_bounds_le_inverse_square
      power dimensionPolynomial.natDegree
      (parameter := (securityParameter : ℝ))
      (scale := scale)
      (dimension := (params.lweDimension securityParameter : ℝ))
      (coefficientSum := (polynomialCoefficientSum dimensionPolynomial : ℝ))
      (by positivity)
      (by dsimp only [scale]; positivity)
      (by dsimp only [scale]; norm_num)
      (by positivity)
      hdimensionReal
    dsimp only [residualBound, finalBound]
    convert h using 1
    all_goals ring
  calc
    (securityParameter : ENNReal) ^ power *
        balancedResidual params
          (negligibilitySchedule params reference dimensionPolynomial hDimension power)
          adversary securityParameter ≤
      (securityParameter : ENNReal) ^ power * ENNReal.ofReal residualBound := by
        gcongr
        simpa only [negligibilitySchedule, scale, residualBound] using hresidual
    _ = ENNReal.ofReal ((securityParameter : ℝ) ^ power * residualBound) := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
        ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal finalBound := ENNReal.ofReal_le_ofReal hscaled
    _ = ENNReal.ofReal
        ((1 / 2 + (polynomialCoefficientSum dimensionPolynomial : ℝ) / 4) *
          ((((securityParameter + 1 : ℕ) : ℝ) ^ 2)⁻¹)) := by
      rfl

/-- The selected schedule makes the residual disappear at the one power for which it was
constructed.  No claim is made that one fixed schedule handles every power. -/
theorem tendsto_pow_mul_balancedResidual_negligibilitySchedule_zero
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (reference : (securityParameter : ℕ) → Fin (params.lweDimension securityParameter))
    (dimensionPolynomial : Polynomial ℕ)
    (hDimension : ∀ securityParameter,
      params.lweDimension securityParameter ≤
        dimensionPolynomial.eval securityParameter)
    (power : ℕ) (adversary : PolynomialQueryAdversary params) :
    Tendsto
      (fun securityParameter : ℕ =>
        (securityParameter : ENNReal) ^ power *
          balancedResidual params
            (negligibilitySchedule params reference dimensionPolynomial hDimension power)
            adversary securityParameter)
      atTop (𝓝 0) := by
  let constant : ℝ :=
    1 / 2 + (polynomialCoefficientSum dimensionPolynomial : ℝ) / 4
  have hconstant_nonneg : 0 ≤ constant := by
    dsimp only [constant]
    positivity
  have hinv : Tendsto
      (fun securityParameter : ℕ =>
        ((securityParameter + 1 : ℕ) : ENNReal)⁻¹) atTop (𝓝 0) :=
    ENNReal.tendsto_inv_nat_nhds_zero.comp (tendsto_add_atTop_nat 1)
  have hupper : Tendsto
      (fun securityParameter : ℕ =>
        ENNReal.ofReal
          (constant * ((((securityParameter + 1 : ℕ) : ℝ) ^ 2)⁻¹)))
      atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul (ENNReal.Tendsto.pow (n := 2) hinv)
      (Or.inr (ENNReal.ofReal_ne_top : ENNReal.ofReal constant ≠ ⊤))
    convert h using 1
    · funext securityParameter
      rw [ENNReal.ofReal_mul hconstant_nonneg, ENNReal.ofReal_inv_of_pos (by positivity),
        ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_natCast]
      exact congrArg (fun value : ENNReal => ENNReal.ofReal constant * value)
        (ENNReal.inv_pow (a := ((securityParameter + 1 : ℕ) : ENNReal)) (n := 2))
    · simp
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hupper
    (fun _ => zero_le)
    (fun securityParameter =>
      pow_mul_balancedResidual_negligibilitySchedule_le params reference
        dimensionPolynomial hDimension power adversary securityParameter)

/-! ## Security from universal polynomial-view augmented search -/

/-- Predicate family for efficient augmented-search solvers, indexed by their polynomial-view
schedule. -/
abbrev UniversalSearchIsPPT {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :=
  (schedule : PolynomialViewSchedule params) → SearchAdversaryFamily params schedule → Prop

/-- **Adaptive TFHE security with no amplification-residual premise.**

Security of augmented scalar search is required for every polynomial-view schedule because the
proof selects a different logarithmic schedule for each power in superpolynomial decay.  This is
the usual asymptotic quantifier order for polynomial-loss search-to-decision reductions. -/
theorem secureAgainst_of_universal_finiteSearch_and_lwe
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (hError : ∀ securityParameter,
      Pr[⊥ | params.keySwitchErrorSampler securityParameter] = 0)
    (reference : (securityParameter : ℕ) → Fin (params.lweDimension securityParameter))
    (dimensionPolynomial : Polynomial ℕ)
    (hDimension : ∀ securityParameter,
      params.lweDimension securityParameter ≤
        dimensionPolynomial.eval securityParameter)
    (isPPT : PolynomialQueryAdversary params → Prop)
    (searchIsPPT : UniversalSearchIsPPT params)
    (realRingBatchIsPPT zeroRingBatchIsPPT :
      CutCycleSecurity.RingBatchLWEAdversaryFamily params → Prop)
    (inputBatchIsPPT : InputBatchLWEAdversaryFamily params → Prop)
    (hSearchClosed : ∀ schedule adversary, isPPT adversary →
      searchIsPPT schedule (searchReduction params schedule adversary))
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT (realRingBatchReduction params adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT (zeroRingBatchReduction params adversary))
    (hInputBatchClosed : ∀ adversary, isPPT adversary →
      inputBatchIsPPT (inputBatchLWEReduction params adversary))
    (hSearch : ∀ schedule,
      (searchSecurityGame params schedule).secureAgainst (searchIsPPT schedule))
    (hRealRingBatch :
      (CutCycleSecurity.ringBatchLWESecurityGame params).secureAgainst realRingBatchIsPPT)
    (hZeroRingBatch :
      (CutCycleSecurity.ringBatchLWESecurityGame params).secureAgainst zeroRingBatchIsPPT)
    (hInputBatch :
      (inputBatchLWESecurityGame params).secureAgainst inputBatchIsPPT) :
    (securityGame params).secureAgainst isPPT := by
  intro adversary hadversary power
  let schedule := negligibilitySchedule params reference dimensionPolynomial hDimension power
  let searchAdversary := searchReduction params schedule adversary
  have hSearchNeg : negligible (fun securityParameter =>
      2 * (searchSecurityGame params schedule).advantage
        searchAdversary securityParameter) :=
    negligible_const_mul
      (hSearch schedule searchAdversary
        (hSearchClosed schedule adversary hadversary)) (by norm_num)
  have hSearchTendsto := hSearchNeg power
  have hResidualBase :=
    tendsto_pow_mul_balancedResidual_negligibilitySchedule_zero
      params reference dimensionPolynomial hDimension power adversary
  have hResidualTendsto : Tendsto (fun (securityParameter : ℕ) =>
      (securityParameter : ENNReal) ^ power *
        (2 * (balancedResidualSecurityGame params schedule).advantage
          adversary securityParameter)) atTop (𝓝 0) := by
    have h := ENNReal.Tendsto.const_mul hResidualBase
      (Or.inr (by norm_num : (2 : ENNReal) ≠ ⊤))
    convert h using 1
    · funext securityParameter
      simp only [balancedResidualSecurityGame, schedule]
      ring
    · norm_num
  have hRealRingTendsto :=
    (hRealRingBatch (realRingBatchReduction params adversary)
      (hRealRingBatchClosed adversary hadversary)) power
  have hZeroRingTendsto :=
    (hZeroRingBatch (zeroRingBatchReduction params adversary)
      (hZeroRingBatchClosed adversary hadversary)) power
  have hInputTendsto :=
    (hInputBatch (inputBatchLWEReduction params adversary)
      (hInputBatchClosed adversary hadversary)) power
  have hUpper : Tendsto (fun (securityParameter : ℕ) =>
      (securityParameter : ENNReal) ^ power *
        (2 * (searchSecurityGame params schedule).advantage
            searchAdversary securityParameter +
          2 * (balancedResidualSecurityGame params schedule).advantage
            adversary securityParameter +
          (CutCycleSecurity.ringBatchLWESecurityGame params).advantage
            (realRingBatchReduction params adversary) securityParameter +
          (CutCycleSecurity.ringBatchLWESecurityGame params).advantage
            (zeroRingBatchReduction params adversary) securityParameter +
          (inputBatchLWESecurityGame params).advantage
            (inputBatchLWEReduction params adversary) securityParameter))
      atTop (𝓝 0) := by
    have h := hSearchTendsto.add
      (hResidualTendsto.add
        (hRealRingTendsto.add (hZeroRingTendsto.add hInputTendsto)))
    convert h using 1
    · funext securityParameter
      ring
    · norm_num
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hUpper
    (fun _ => zero_le)
    (fun securityParameter => by
      simpa only [searchAdversary, mul_comm] using
        mul_le_mul_right
          (securityGame_advantage_le_two_mul_finiteSearch_add_two_mul_residual_add_lwe
            params hError schedule adversary securityParameter)
          ((securityParameter : ENNReal) ^ power))

end FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView
