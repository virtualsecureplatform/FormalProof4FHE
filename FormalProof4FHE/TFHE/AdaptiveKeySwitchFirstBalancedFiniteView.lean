/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AdaptiveKeySwitchFirstFiniteView

/-!
# Balanced Finite-View Search Bound for Adaptive KSK-First TFHE

The generic finite-view reduction exposes an exact amplification deficit.  This module removes
that opaque term by choosing the common-fiber Markov threshold as

`(2 - decisionAdvantage) / 4`.

For decision advantage `δ`, the bad-fiber ratio then equals
`2(1 - δ) / (2 - δ)`, leaving at least `δ / (2 - δ) ≥ δ / 2`.  Consequently

`δ ≤ 2 * finiteSearchSuccess + 2 * totalAmplifiedCoordinateError`.

The same bound holds after replacing the total error by
`min(totalAmplifiedCoordinateError, δ / 2)`.  This capped residual vanishes when `δ = 0`, unlike
the raw majority error at threshold one half.  There is no maximized deficit or hidden
search-to-decision loss.
-/

open ENNReal OracleComp

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.KeySwitchFirstFiniteView

variable {Message : Type}
  {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]

/-! ## Advantage-balanced threshold -/

/-- Every augmented public-decision advantage is nonnegative. -/
theorem decisionAdvantage_nonneg
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    0 ≤ decisionAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget distinguisher := by
  unfold decisionAdvantage ProbComp.boolDistAdvantage
  exact abs_nonneg _

/-- Every augmented public-decision advantage is at most one. -/
theorem decisionAdvantage_le_one
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    decisionAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget distinguisher ≤ 1 := by
  unfold decisionAdvantage ProbComp.boolDistAdvantage
  have hreal_nonneg : 0 ≤
      (Pr[= true | realDecisionGame ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget distinguisher]).toReal :=
    ENNReal.toReal_nonneg
  have huniform_nonneg : 0 ≤
      (Pr[= true | uniformKeySwitchDecisionGame
        ringErrorSampler inputErrorSampler tgswGadget distinguisher]).toReal :=
    ENNReal.toReal_nonneg
  have hreal_one :
      (Pr[= true | realDecisionGame ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget distinguisher]).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top probOutput_le_one
  have huniform_one :
      (Pr[= true | uniformKeySwitchDecisionGame
        ringErrorSampler inputErrorSampler tgswGadget distinguisher]).toReal ≤ 1 := by
    rw [← ENNReal.toReal_one]
    exact ENNReal.toReal_mono ENNReal.one_ne_top probOutput_le_one
  rw [abs_le]
  constructor <;> linarith

/-- Threshold that balances good-fiber amplification against the bad-fiber Markov charge. -/
noncomputable def balancedThreshold
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) : ENNReal :=
  ENNReal.ofReal
    ((2 - decisionAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget distinguisher) / 4)

theorem balancedThreshold_pos
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    0 < balancedThreshold ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget distinguisher := by
  unfold balancedThreshold
  apply ENNReal.ofReal_pos.mpr
  have h := decisionAdvantage_le_one ringErrorSampler keySwitchErrorSampler
    inputErrorSampler tgswGadget keySwitchGadget distinguisher
  linarith

theorem balancedThreshold_le_one
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    balancedThreshold ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget distinguisher ≤ 1 := by
  unfold balancedThreshold
  rw [← ENNReal.ofReal_one]
  apply ENNReal.ofReal_le_ofReal
  have h := decisionAdvantage_nonneg ringErrorSampler keySwitchErrorSampler
    inputErrorSampler tgswGadget keySwitchGadget distinguisher
  linarith

/-- The explicit sum of the amplified good-fiber coordinate errors at the balanced threshold. -/
noncomputable def balancedAmplificationError
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) : ENNReal :=
  ∑ _coordinate : Fin lweDimension,
    FormalProof4FHE.MajorityAmplification.amplifiedError rounds
      (balancedThreshold ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget distinguisher)

theorem balancedAmplificationError_ne_top
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    balancedAmplificationError ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget rounds distinguisher ≠ ⊤ := by
  unfold balancedAmplificationError
  apply ENNReal.sum_ne_top.mpr
  intro coordinate _
  exact ne_top_of_le_ne_top ENNReal.one_ne_top
    (FormalProof4FHE.MajorityAmplification.amplifiedError_le_one rounds
      (balancedThreshold_le_one ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget distinguisher))

/-- The summed error is exactly the scalar dimension times one common coordinate error. -/
theorem balancedAmplificationError_eq_natCast_mul
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    balancedAmplificationError ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget rounds distinguisher =
      (lweDimension : ENNReal) *
        FormalProof4FHE.MajorityAmplification.amplifiedError rounds
          (balancedThreshold ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget keySwitchGadget distinguisher) := by
  simp [balancedAmplificationError]

/-! ## Direct two-for-one finite-search bound -/

/-- The balanced Markov ratio leaves at least half of the decision advantage after the bad-fiber
charge. -/
private theorem half_decisionAdvantage_le_one_sub_balancedRatio
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    decisionAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget distinguisher / 2 ≤
      1 -
        (ENNReal.ofReal
          ((1 - decisionAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget keySwitchGadget distinguisher) / 2) /
          balancedThreshold ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget keySwitchGadget distinguisher).toReal := by
  let advantage := decisionAdvantage ringErrorSampler keySwitchErrorSampler
    inputErrorSampler tgswGadget keySwitchGadget distinguisher
  have hadv_nonneg : 0 ≤ advantage :=
    decisionAdvantage_nonneg ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget distinguisher
  have hadv_one : advantage ≤ 1 :=
    decisionAdvantage_le_one ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget distinguisher
  have hdenom_pos : 0 < 2 - advantage := by linarith
  have hnum_nonneg : 0 ≤ (1 - advantage) / 2 := by linarith
  have hthreshold_nonneg : 0 ≤ (2 - advantage) / 4 := by linarith
  have hratio :
      (ENNReal.ofReal ((1 - advantage) / 2) /
        balancedThreshold ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget distinguisher).toReal =
        2 * (1 - advantage) / (2 - advantage) := by
    unfold balancedThreshold
    rw [ENNReal.toReal_div,
      ENNReal.toReal_ofReal hnum_nonneg,
      ENNReal.toReal_ofReal hthreshold_nonneg]
    field_simp
    ring
  change advantage / 2 ≤ 1 -
    (ENNReal.ofReal ((1 - advantage) / 2) /
      balancedThreshold ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget distinguisher).toReal
  rw [hratio]
  have hidentity :
      1 - 2 * (1 - advantage) / (2 - advantage) =
        advantage / (2 - advantage) := by
    field_simp
    ring
  rw [hidentity]
  apply (le_div_iff₀ hdenom_pos).2
  nlinarith [mul_nonneg hadv_nonneg (sub_nonneg.mpr hadv_one)]

/-- **Balanced finite-search theorem.** Augmented decision advantage is at most twice whole-key
finite-search success plus twice the explicit summed majority error. -/
theorem decisionAdvantage_le_two_mul_success_add_two_mul_balancedError
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (reference : Fin lweDimension)
    (rounds : ℕ)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    decisionAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget distinguisher ≤
      2 * (successProbability ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget rounds
        (amplifiedSolver ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget rounds distinguisher)).toReal +
      2 * (balancedAmplificationError ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget rounds distinguisher).toReal := by
  let advantage := decisionAdvantage ringErrorSampler keySwitchErrorSampler
    inputErrorSampler tgswGadget keySwitchGadget distinguisher
  let threshold := balancedThreshold ringErrorSampler keySwitchErrorSampler
    inputErrorSampler tgswGadget keySwitchGadget distinguisher
  let coordinateError := balancedAmplificationError ringErrorSampler
    keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget rounds distinguisher
  let ratio := ENNReal.ofReal ((1 - advantage) / 2) / threshold
  let totalError := coordinateError + ratio
  let success := successProbability ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget rounds
    (amplifiedSolver ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget rounds distinguisher)
  have hsuccessENN := one_sub_amplifiedErrorBound_le_successProbability
    ringErrorSampler keySwitchErrorSampler inputErrorSampler hError
    tgswGadget keySwitchGadget reference rounds threshold
    (balancedThreshold_pos ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget distinguisher)
    (balancedThreshold_le_one ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget distinguisher)
    distinguisher
  have herrorBound :
      amplifiedErrorBound ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget (fun _ ↦ rounds) threshold distinguisher =
        totalError := by
    simp only [amplifiedErrorBound, balancedAmplificationError, coordinateError,
      ratio, totalError, advantage, threshold]
  rw [herrorBound] at hsuccessENN
  have hcoordinate_ne : coordinateError ≠ ⊤ :=
    balancedAmplificationError_ne_top ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget rounds distinguisher
  have hratio_ne : ratio ≠ ⊤ := by
    apply ENNReal.div_ne_top
    · simp
    · exact ne_of_gt
        (balancedThreshold_pos ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget distinguisher)
  have htotal_ne : totalError ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨hcoordinate_ne, hratio_ne⟩
  have hone : (1 : ℝ) ≤ (1 - totalError).toReal + totalError.toReal := by
    by_cases htotal : totalError ≤ 1
    · rw [ENNReal.toReal_sub_of_le htotal ENNReal.one_ne_top, ENNReal.toReal_one]
      linarith
    · have honeError : 1 ≤ totalError := le_of_not_ge htotal
      rw [tsub_eq_zero_of_le honeError, ENNReal.toReal_zero, zero_add,
        ← ENNReal.toReal_one]
      exact ENNReal.toReal_mono htotal_ne honeError
  have hsuccessReal : (1 - totalError).toReal ≤ success.toReal := by
    exact ENNReal.toReal_mono probOutput_ne_top hsuccessENN
  have htotalReal : totalError.toReal = coordinateError.toReal + ratio.toReal := by
    exact ENNReal.toReal_add hcoordinate_ne hratio_ne
  have haccount : (1 : ℝ) ≤ success.toReal + coordinateError.toReal + ratio.toReal := by
    rw [htotalReal] at hone
    linarith
  have hhalf : advantage / 2 ≤ 1 - ratio.toReal := by
    exact half_decisionAdvantage_le_one_sub_balancedRatio
      ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget distinguisher
  dsimp only [advantage, coordinateError, success] at haccount hhalf ⊢
  linarith

/-- Explicit balanced residual. It uses the majority error only while that error is smaller than
half the decision advantage, and therefore vanishes automatically when the decision advantage is
zero. -/
noncomputable def balancedResidual
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) : ℝ :=
  min
    (balancedAmplificationError ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget rounds distinguisher).toReal
    (decisionAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget distinguisher / 2)

theorem balancedResidual_nonneg
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (rounds : ℕ)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    0 ≤ balancedResidual ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget rounds distinguisher := by
  unfold balancedResidual
  exact le_min ENNReal.toReal_nonneg
    (div_nonneg
      (decisionAdvantage_nonneg ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget distinguisher)
      (by norm_num))

/-- The balanced decision bound can use the explicit residual instead of the full majority error.
This form is suitable for asymptotics because the residual is zero on zero-advantage families. -/
theorem decisionAdvantage_le_two_mul_success_add_two_mul_balancedResidual
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (reference : Fin lweDimension)
    (rounds : ℕ)
    (distinguisher : Distinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels queryCount) :
    decisionAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget distinguisher ≤
      2 * (successProbability ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget rounds
        (amplifiedSolver ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget rounds distinguisher)).toReal +
      2 * balancedResidual ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget rounds distinguisher := by
  have hbase := decisionAdvantage_le_two_mul_success_add_two_mul_balancedError
    ringErrorSampler keySwitchErrorSampler inputErrorSampler hError
    tgswGadget keySwitchGadget reference rounds distinguisher
  unfold balancedResidual
  by_cases hsmall :
      (balancedAmplificationError ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget rounds distinguisher).toReal ≤
      decisionAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget distinguisher / 2
  · rw [min_eq_left hsmall]
    exact hbase
  · rw [min_eq_right (le_of_not_ge hsmall)]
    have hsuccess : 0 ≤
        (successProbability ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget rounds
          (amplifiedSolver ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget keySwitchGadget rounds distinguisher)).toReal :=
      ENNReal.toReal_nonneg
    linarith

/-- The adaptive public-decision interface inherits the balanced two-for-one search bound. -/
theorem adaptiveKeySwitchDecisionAdvantage_le_two_mul_success_add_two_mul_balancedError
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (reference : Fin lweDimension)
    (rounds : ℕ)
    (distinguisher : KeySwitchFirstSecurity.PublicDistinguisher
      q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount) :
    KeySwitchFirstSecurity.keySwitchDecisionAdvantage
        ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget distinguisher ≤
      2 * (successProbability ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget rounds
        (amplifiedSolver ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget rounds (bundleDistinguisher distinguisher))).toReal +
      2 * (balancedAmplificationError ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget rounds
        (bundleDistinguisher distinguisher)).toReal := by
  rw [← decisionAdvantage_eq_adaptiveSecurity]
  exact decisionAdvantage_le_two_mul_success_add_two_mul_balancedError
    ringErrorSampler keySwitchErrorSampler inputErrorSampler hError
    tgswGadget keySwitchGadget reference rounds (bundleDistinguisher distinguisher)

/-- **Complete balanced finite-view adaptive TFHE bound.** The opaque amplification deficit in
the earlier composition is replaced by twice the explicit summed majority error. -/
theorem abs_signedAdvantage_real_le_two_mul_finiteSearch_add_two_mul_error_add_two_moduleLwe_add_inputLwe
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (reference : Fin lweDimension)
    (rounds : ℕ)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (hbound : Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (Adaptive.realGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      2 * (successProbability ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget rounds
        (amplifiedSolver ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget rounds
          (bundleDistinguisher
            (KeySwitchFirstSecurity.toPublicDistinguisher
              (queryCount := queryCount) encode adversary)))).toReal +
      2 * (balancedAmplificationError ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget rounds
        (bundleDistinguisher
          (KeySwitchFirstSecurity.toPublicDistinguisher
            (queryCount := queryCount) encode adversary))).toReal +
      LearningWithErrors.advantage
        (Native.BootstrapCutSecurity.batchModuleLweProblem
          q degree ringRank tgswLevels lweDimension ringErrorSampler)
        (Native.BootstrapCutSecurity.realBatchReduction
          ringErrorSampler ($ᵗ (ZMod q)) tgswGadget
          (Adaptive.CutCycleSecurity.cutContinuation
            queryCount inputErrorSampler encode adversary)) +
      LearningWithErrors.advantage
        (Native.BootstrapCutSecurity.batchModuleLweProblem
          q degree ringRank tgswLevels lweDimension ringErrorSampler)
        (Native.BootstrapCutSecurity.zeroBatchReduction
          ringErrorSampler ($ᵗ (ZMod q))
          (Adaptive.CutCycleSecurity.cutContinuation
            queryCount inputErrorSampler encode adversary)) +
      LearningWithErrors.advantage
        (Native.KeySwitchSecurity.binaryLweProblem q lweDimension queryCount inputErrorSampler)
        (KeySwitchFirstSecurity.inputTapeReduction ringErrorSampler inputErrorSampler
          tgswGadget encode adversary) := by
  have hSecurity :=
    KeySwitchFirstSecurity.abs_signedAdvantage_real_le_decision_add_two_moduleLwe_add_inputLwe
      queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget encode adversary hbound
  have hDecision :=
    adaptiveKeySwitchDecisionAdvantage_le_two_mul_success_add_two_mul_balancedError
      ringErrorSampler keySwitchErrorSampler inputErrorSampler hError
      tgswGadget keySwitchGadget reference rounds
      (KeySwitchFirstSecurity.toPublicDistinguisher
        (queryCount := queryCount) encode adversary)
  linarith

/-- Complete adaptive bound using the explicit balanced residual. -/
theorem abs_signedAdvantage_real_le_two_mul_finiteSearch_add_two_mul_residual_add_two_moduleLwe_add_inputLwe
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (hError : Pr[⊥ | keySwitchErrorSampler] = 0)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (reference : Fin lweDimension)
    (rounds : ℕ)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (hbound : Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (Adaptive.realGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      2 * (successProbability ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget rounds
        (amplifiedSolver ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget rounds
          (bundleDistinguisher
            (KeySwitchFirstSecurity.toPublicDistinguisher
              (queryCount := queryCount) encode adversary)))).toReal +
      2 * balancedResidual ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget rounds
        (bundleDistinguisher
          (KeySwitchFirstSecurity.toPublicDistinguisher
            (queryCount := queryCount) encode adversary)) +
      LearningWithErrors.advantage
        (Native.BootstrapCutSecurity.batchModuleLweProblem
          q degree ringRank tgswLevels lweDimension ringErrorSampler)
        (Native.BootstrapCutSecurity.realBatchReduction
          ringErrorSampler ($ᵗ (ZMod q)) tgswGadget
          (Adaptive.CutCycleSecurity.cutContinuation
            queryCount inputErrorSampler encode adversary)) +
      LearningWithErrors.advantage
        (Native.BootstrapCutSecurity.batchModuleLweProblem
          q degree ringRank tgswLevels lweDimension ringErrorSampler)
        (Native.BootstrapCutSecurity.zeroBatchReduction
          ringErrorSampler ($ᵗ (ZMod q))
          (Adaptive.CutCycleSecurity.cutContinuation
            queryCount inputErrorSampler encode adversary)) +
      LearningWithErrors.advantage
        (Native.KeySwitchSecurity.binaryLweProblem q lweDimension queryCount inputErrorSampler)
        (KeySwitchFirstSecurity.inputTapeReduction ringErrorSampler inputErrorSampler
          tgswGadget encode adversary) := by
  have hSecurity :=
    KeySwitchFirstSecurity.abs_signedAdvantage_real_le_decision_add_two_moduleLwe_add_inputLwe
      queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget encode adversary hbound
  have hDecision := decisionAdvantage_le_two_mul_success_add_two_mul_balancedResidual
    ringErrorSampler keySwitchErrorSampler inputErrorSampler hError
    tgswGadget keySwitchGadget reference rounds
    (bundleDistinguisher
      (KeySwitchFirstSecurity.toPublicDistinguisher
        (queryCount := queryCount) encode adversary))
  rw [decisionAdvantage_eq_adaptiveSecurity] at hDecision
  linarith

end FormalProof4FHE.TFHE.Encryption.Adaptive.KeySwitchFirstFiniteView
