/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AdaptiveKeySwitchFirstBalancedFiniteView
import FormalProof4FHE.TFHE.AsymptoticCutCycleSecurity

/-!
# Asymptotic Adaptive TFHE Security from Finite Augmented Search

This module lifts the bounded finite-view KSK-first reduction to security-parameter families.
The circular premise is an explicit real scalar-search game whose solver receives independently
sampled BRK+KSK+input-tape views under one hidden key pair.  A schedule records both the majority
depth and a polynomial upper bound on the exact number of views
`lweDimension * 3 ^ rounds`.

The preferred complete adaptive TFHE bound has five terms:

1. finite augmented scalar-search success;
2. the explicit advantage-capped majority residual;
3. real-message binary-secret ring batch-module-LWE;
4. zero-message binary-secret ring batch-module-LWE; and
5. binary-secret scalar batch-LWE on exactly the adaptive input-tape rows.

The residual is `min(summedMajorityError, decisionAdvantage / 2)`, so it vanishes on
zero-advantage families.  Consequently, negligibility of the named augmented-search game, this
residual, and the three ordinary post-cut LWE games implies negligible adaptive TFHE advantage.
No implication from ordinary LWE/RLWE to the augmented circular-search premise or to residual
negligibility is asserted.
-/

open ENNReal OracleComp

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView

open FormalProof4FHE.TFHE.Encryption.Adaptive.KeySwitchFirstFiniteView

/-! ## Polynomial finite-view schedules -/

/-- A majority-amplification schedule with an explicit polynomial bound on the exact number of
augmented views.  The reference coordinate also records that every scalar-key dimension in the
family is nonzero, as required by the common-fiber argument. -/
structure PolynomialViewSchedule {Message : Type} (params : Parameters Message) where
  rounds : ℕ → ℕ
  reference : (securityParameter : ℕ) → Fin (params.lweDimension securityParameter)
  viewPolynomial : Polynomial ℕ
  viewCount_le : ∀ securityParameter,
    viewCount (params.lweDimension securityParameter) (rounds securityParameter) ≤
      viewPolynomial.eval securityParameter

/-- The schedule bounds the concrete number `lweDimension * 3 ^ rounds` of augmented views. -/
theorem exactViewCount_le_polynomial {Message : Type} {params : Parameters Message}
    (schedule : PolynomialViewSchedule params) (securityParameter : ℕ) :
    params.lweDimension securityParameter * 3 ^ schedule.rounds securityParameter ≤
      schedule.viewPolynomial.eval securityParameter := by
  rw [← viewCount_eq]
  exact schedule.viewCount_le securityParameter

/-- Build a polynomial-view schedule from separate polynomial bounds on the scalar dimension and
the majority-tree factor `3 ^ rounds`.  This is the form used by concrete TFHE parameter
families: logarithmic-depth amplification can be certified by supplying a polynomial bound on
the exponential tree width. -/
noncomputable def polynomialViewScheduleOfBounds {Message : Type}
    (params : Parameters Message)
    (rounds : ℕ → ℕ)
    (reference : (securityParameter : ℕ) → Fin (params.lweDimension securityParameter))
    (dimensionPolynomial amplificationPolynomial : Polynomial ℕ)
    (hDimension : ∀ securityParameter,
      params.lweDimension securityParameter ≤
        dimensionPolynomial.eval securityParameter)
    (hAmplification : ∀ securityParameter,
      3 ^ rounds securityParameter ≤
        amplificationPolynomial.eval securityParameter) :
    PolynomialViewSchedule params where
  rounds := rounds
  reference := reference
  viewPolynomial := dimensionPolynomial * amplificationPolynomial
  viewCount_le securityParameter := by
    rw [viewCount_eq, Polynomial.eval_mul]
    exact Nat.mul_le_mul
      (hDimension securityParameter) (hAmplification securityParameter)

/-! ## Augmented-search family -/

/-- A parameter-indexed finite scalar-search solver.  It retains the source query polynomial,
while the polynomial view bound is supplied once by `PolynomialViewSchedule`. -/
structure SearchAdversaryFamily {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params) where
  queryCount : ℕ → ℕ
  queryPolynomial : Polynomial ℕ
  queryCount_le : ∀ securityParameter,
    queryCount securityParameter ≤ queryPolynomial.eval securityParameter
  run : (securityParameter : ℕ) →
    Solver
      (params.q securityParameter)
      (params.degree securityParameter)
      (params.ringRank securityParameter)
      (params.tgswLevels securityParameter)
      (params.lweDimension securityParameter)
      (params.keySwitchLevels securityParameter)
      (queryCount securityParameter)
      (schedule.rounds securityParameter)

/-- The real finite augmented scalar-search game.  Its advantage is whole scalar-key recovery
success from exactly the view batch accounted for by the schedule. -/
noncomputable def searchSecurityGame {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params) :
    SecurityGame (SearchAdversaryFamily params schedule) where
  advantage solver securityParameter :=
    successProbability
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.inputErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (schedule.rounds securityParameter)
      (solver.run securityParameter)

/-- The finite augmented-search solver induced by a polynomial-query adaptive TFHE adversary. -/
noncomputable def searchReduction {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params)
    (adversary : PolynomialQueryAdversary params) :
    SearchAdversaryFamily params schedule where
  queryCount := adversary.queryCount
  queryPolynomial := adversary.queryPolynomial
  queryCount_le := adversary.queryCount_le
  run securityParameter :=
    amplifiedSolver
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.inputErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (schedule.rounds securityParameter)
      (bundleDistinguisher
        (Adaptive.KeySwitchFirstSecurity.toPublicDistinguisher
          (queryCount := adversary.queryCount securityParameter)
          (params.encode securityParameter)
          (adversary.run securityParameter)))

/-! ## Amplification loss family -/

/-- A per-adversary threshold used by the common-fiber amplification accounting. -/
abbrev ThresholdFamily {Message : Type} (params : Parameters Message) :=
  PolynomialQueryAdversary params → ℕ → ENNReal

/-- The exact finite amplification deficit, lifted to `ℝ≥0∞`. -/
noncomputable def loss {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params)
    (threshold : ThresholdFamily params)
    (adversary : PolynomialQueryAdversary params)
    (securityParameter : ℕ) : ENNReal :=
  ENNReal.ofReal
    (amplifiedLoss
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.inputErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (schedule.rounds securityParameter)
      (threshold adversary securityParameter)
      (bundleDistinguisher
        (Adaptive.KeySwitchFirstSecurity.toPublicDistinguisher
          (queryCount := adversary.queryCount securityParameter)
          (params.encode securityParameter)
          (adversary.run securityParameter))))

/-- Security game packaging of the explicit amplification deficit. -/
noncomputable def lossSecurityGame {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params)
    (threshold : ThresholdFamily params) :
    SecurityGame (PolynomialQueryAdversary params) where
  advantage := loss params schedule threshold

/-- The explicit summed majority error at the advantage-balanced threshold. -/
noncomputable def balancedError {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params)
    (adversary : PolynomialQueryAdversary params)
    (securityParameter : ℕ) : ENNReal :=
  balancedAmplificationError
    (params.ringErrorSampler securityParameter)
    (params.keySwitchErrorSampler securityParameter)
    (params.inputErrorSampler securityParameter)
    (params.tgswGadget securityParameter)
    (params.keySwitchGadget securityParameter)
    (schedule.rounds securityParameter)
    (bundleDistinguisher
      (Adaptive.KeySwitchFirstSecurity.toPublicDistinguisher
        (queryCount := adversary.queryCount securityParameter)
        (params.encode securityParameter)
        (adversary.run securityParameter)))

/-- Security game packaging of the concrete balanced majority-error term. -/
noncomputable def balancedErrorSecurityGame {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params) :
    SecurityGame (PolynomialQueryAdversary params) where
  advantage := balancedError params schedule

/-- The explicit balanced residual, lifted from the finite real-valued definition.  Unlike the
raw majority error, it is automatically zero whenever the augmented decision advantage is zero. -/
noncomputable def balancedResidual {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params)
    (adversary : PolynomialQueryAdversary params)
    (securityParameter : ℕ) : ENNReal :=
  ENNReal.ofReal
    (Adaptive.KeySwitchFirstFiniteView.balancedResidual
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.inputErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (schedule.rounds securityParameter)
      (bundleDistinguisher
        (Adaptive.KeySwitchFirstSecurity.toPublicDistinguisher
          (queryCount := adversary.queryCount securityParameter)
          (params.encode securityParameter)
          (adversary.run securityParameter))))

/-- Security game for the explicit advantage-capped balanced residual. -/
noncomputable def balancedResidualSecurityGame {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params) :
    SecurityGame (PolynomialQueryAdversary params) where
  advantage := balancedResidual params schedule

/-- One coordinate's exact iterated majority error at the balanced threshold. -/
noncomputable def coordinateBalancedError {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params)
    (adversary : PolynomialQueryAdversary params)
    (securityParameter : ℕ) : ENNReal :=
  FormalProof4FHE.MajorityAmplification.amplifiedError
    (schedule.rounds securityParameter)
    (balancedThreshold
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.inputErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (bundleDistinguisher
        (Adaptive.KeySwitchFirstSecurity.toPublicDistinguisher
          (queryCount := adversary.queryCount securityParameter)
          (params.encode securityParameter)
          (adversary.run securityParameter))))

/-- Security game for the single-coordinate analytic majority recurrence. -/
noncomputable def coordinateBalancedErrorSecurityGame {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params) :
    SecurityGame (PolynomialQueryAdversary params) where
  advantage := coordinateBalancedError params schedule

/-- The scalar dimension is bounded by the schedule's view polynomial because every coordinate
uses at least one majority-tree leaf. -/
theorem lweDimension_le_viewPolynomial {Message : Type} {params : Parameters Message}
    (schedule : PolynomialViewSchedule params) (securityParameter : ℕ) :
    params.lweDimension securityParameter ≤
      schedule.viewPolynomial.eval securityParameter := by
  calc
    params.lweDimension securityParameter ≤
        params.lweDimension securityParameter * 3 ^ schedule.rounds securityParameter :=
      Nat.le_mul_of_pos_right _ (by positivity)
    _ ≤ schedule.viewPolynomial.eval securityParameter :=
      exactViewCount_le_polynomial schedule securityParameter

/-- The total balanced error is exactly scalar dimension times the coordinate recurrence. -/
theorem balancedError_eq_natCast_mul_coordinateError
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params)
    (adversary : PolynomialQueryAdversary params)
    (securityParameter : ℕ) :
    balancedError params schedule adversary securityParameter =
      (params.lweDimension securityParameter : ENNReal) *
        coordinateBalancedError params schedule adversary securityParameter := by
  exact balancedAmplificationError_eq_natCast_mul
    (params.ringErrorSampler securityParameter)
    (params.keySwitchErrorSampler securityParameter)
    (params.inputErrorSampler securityParameter)
    (params.tgswGadget securityParameter)
    (params.keySwitchGadget securityParameter)
    (schedule.rounds securityParameter)
    (bundleDistinguisher
      (Adaptive.KeySwitchFirstSecurity.toPublicDistinguisher
        (queryCount := adversary.queryCount securityParameter)
        (params.encode securityParameter)
        (adversary.run securityParameter)))

/-- Polynomial view growth bounds the complete summed majority error by a polynomial multiple of
the single-coordinate recurrence. -/
theorem balancedError_le_viewPolynomial_mul_coordinateError
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params)
    (adversary : PolynomialQueryAdversary params)
    (securityParameter : ℕ) :
    balancedError params schedule adversary securityParameter ≤
      ((schedule.viewPolynomial.eval securityParameter : ℕ) : ENNReal) *
        coordinateBalancedError params schedule adversary securityParameter := by
  rw [balancedError_eq_natCast_mul_coordinateError]
  gcongr
  exact_mod_cast lweDimension_le_viewPolynomial schedule securityParameter

/-- Negligibility of the coordinate recurrence implies negligibility of the summed balanced
error, because the schedule already certifies a polynomial bound on the number of coordinates. -/
theorem balancedErrorSecurityGame_secureAgainst_of_coordinateError
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params)
    (isPPT : PolynomialQueryAdversary params → Prop)
    (hCoordinateError :
      (coordinateBalancedErrorSecurityGame params schedule).secureAgainst isPPT) :
    (balancedErrorSecurityGame params schedule).secureAgainst isPPT := by
  intro adversary hadversary
  exact negligible_of_le
    (balancedError_le_viewPolynomial_mul_coordinateError params schedule adversary)
    (negligible_polynomial_mul (hCoordinateError adversary hadversary)
      schedule.viewPolynomial)

/-! ## Ordinary post-cut LWE families -/

/-- The real-message ring batch-LWE reduction after the KSK has become uniform. -/
noncomputable def realRingBatchReduction {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (adversary : PolynomialQueryAdversary params) :
    CutCycleSecurity.RingBatchLWEAdversaryFamily params :=
  fun securityParameter ↦
    Native.BootstrapCutSecurity.realBatchReduction
      (params.ringErrorSampler securityParameter)
      ($ᵗ (ZMod (params.q securityParameter)))
      (params.tgswGadget securityParameter)
      (Adaptive.CutCycleSecurity.cutContinuation
        (adversary.queryCount securityParameter)
        (params.inputErrorSampler securityParameter)
        (params.encode securityParameter)
        (adversary.run securityParameter))

/-- The zero-message ring batch-LWE reduction after the KSK has become uniform. -/
noncomputable def zeroRingBatchReduction {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (adversary : PolynomialQueryAdversary params) :
    CutCycleSecurity.RingBatchLWEAdversaryFamily params :=
  fun securityParameter ↦
    Native.BootstrapCutSecurity.zeroBatchReduction
      (params.ringErrorSampler securityParameter)
      ($ᵗ (ZMod (params.q securityParameter)))
      (Adaptive.CutCycleSecurity.cutContinuation
        (adversary.queryCount securityParameter)
        (params.inputErrorSampler securityParameter)
        (params.encode securityParameter)
        (adversary.run securityParameter))

/-- The ordinary scalar input-tape batch-LWE adversary type at one parameter. -/
abbrev InputBatchLWEAdversaryAt {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (queryCount : ℕ → ℕ) (securityParameter : ℕ) :=
  LearningWithErrors.Adversary
    (Native.KeySwitchSecurity.binaryLweProblem
      (params.q securityParameter)
      (params.lweDimension securityParameter)
      (queryCount securityParameter)
      (params.inputErrorSampler securityParameter))

/-- A parameter-indexed input-tape LWE attack family with an explicit polynomial row bound. -/
structure InputBatchLWEAdversaryFamily {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] where
  queryCount : ℕ → ℕ
  queryPolynomial : Polynomial ℕ
  queryCount_le : ∀ securityParameter,
    queryCount securityParameter ≤ queryPolynomial.eval securityParameter
  run : (securityParameter : ℕ) →
    InputBatchLWEAdversaryAt params queryCount securityParameter

/-- Ordinary binary-secret scalar batch-LWE on exactly the adaptive input-tape rows. -/
noncomputable def inputBatchLWESecurityGame {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :
    SecurityGame (InputBatchLWEAdversaryFamily params) where
  advantage adversary securityParameter := ENNReal.ofReal
    (LearningWithErrors.advantage
      (Native.KeySwitchSecurity.binaryLweProblem
        (params.q securityParameter)
        (params.lweDimension securityParameter)
        (adversary.queryCount securityParameter)
        (params.inputErrorSampler securityParameter))
      (adversary.run securityParameter))

/-- The exact input-tape LWE reduction induced at every security parameter. -/
noncomputable def inputBatchLWEReduction {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (adversary : PolynomialQueryAdversary params) :
    InputBatchLWEAdversaryFamily params where
  queryCount := adversary.queryCount
  queryPolynomial := adversary.queryPolynomial
  queryCount_le := adversary.queryCount_le
  run securityParameter :=
    Adaptive.KeySwitchFirstSecurity.inputTapeReduction
      (params.ringErrorSampler securityParameter)
      (params.inputErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.encode securityParameter)
      (adversary.run securityParameter)

/-! ## Pointwise and negligible composition -/

private theorem ofReal_add_five_le (a b c d e : ℝ) :
    ENNReal.ofReal (a + b + c + d + e) ≤
      ENNReal.ofReal a + ENNReal.ofReal b + ENNReal.ofReal c +
        ENNReal.ofReal d + ENNReal.ofReal e := by
  calc
    ENNReal.ofReal (a + b + c + d + e) ≤
        ENNReal.ofReal (a + b + c + d) + ENNReal.ofReal e := ENNReal.ofReal_add_le
    _ ≤ (ENNReal.ofReal (a + b + c) + ENNReal.ofReal d) +
        ENNReal.ofReal e := add_le_add ENNReal.ofReal_add_le le_rfl
    _ ≤ ((ENNReal.ofReal (a + b) + ENNReal.ofReal c) + ENNReal.ofReal d) +
        ENNReal.ofReal e := add_le_add (add_le_add ENNReal.ofReal_add_le le_rfl) le_rfl
    _ ≤ (((ENNReal.ofReal a + ENNReal.ofReal b) + ENNReal.ofReal c) +
        ENNReal.ofReal d) + ENNReal.ofReal e :=
      add_le_add (add_le_add (add_le_add ENNReal.ofReal_add_le le_rfl) le_rfl) le_rfl

/-- **Pointwise asymptotic finite-view bound.** The exact finite adaptive theorem is lifted to
`ℝ≥0∞` at every security parameter. -/
theorem securityGame_advantage_le_finiteSearch_add_loss_add_two_ringBatchLWE_add_inputLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (hError : ∀ securityParameter,
      Pr[⊥ | params.keySwitchErrorSampler securityParameter] = 0)
    (schedule : PolynomialViewSchedule params)
    (threshold : ThresholdFamily params)
    (hthreshold_pos : ∀ adversary securityParameter,
      0 < threshold adversary securityParameter)
    (hthreshold_one : ∀ adversary securityParameter,
      threshold adversary securityParameter ≤ 1)
    (adversary : PolynomialQueryAdversary params)
    (securityParameter : ℕ) :
    (securityGame params).advantage adversary securityParameter ≤
      (searchSecurityGame params schedule).advantage
          (searchReduction params schedule adversary) securityParameter +
        (lossSecurityGame params schedule threshold).advantage
          adversary securityParameter +
        (CutCycleSecurity.ringBatchLWESecurityGame params).advantage
          (realRingBatchReduction params adversary) securityParameter +
        (CutCycleSecurity.ringBatchLWESecurityGame params).advantage
          (zeroRingBatchReduction params adversary) securityParameter +
        (inputBatchLWESecurityGame params).advantage
          (inputBatchLWEReduction params adversary) securityParameter := by
  have h :=
    Adaptive.KeySwitchFirstFiniteView.abs_signedAdvantage_real_le_finiteSearch_add_loss_add_two_moduleLwe_add_inputLwe
      (adversary.queryCount securityParameter)
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.inputErrorSampler securityParameter)
      (hError securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (schedule.reference securityParameter)
      (schedule.rounds securityParameter)
      (threshold adversary securityParameter)
      (hthreshold_pos adversary securityParameter)
      (hthreshold_one adversary securityParameter)
      (params.encode securityParameter)
      (adversary.run securityParameter)
      (adversary.isQueryBound securityParameter)
  have hLift := ENNReal.ofReal_le_ofReal h
  have hExpanded := hLift.trans
    (ofReal_add_five_le
      ((successProbability
        (params.ringErrorSampler securityParameter)
        (params.keySwitchErrorSampler securityParameter)
        (params.inputErrorSampler securityParameter)
        (params.tgswGadget securityParameter)
        (params.keySwitchGadget securityParameter)
        (schedule.rounds securityParameter)
        ((searchReduction params schedule adversary).run securityParameter)).toReal)
      (amplifiedLoss
        (params.ringErrorSampler securityParameter)
        (params.keySwitchErrorSampler securityParameter)
        (params.inputErrorSampler securityParameter)
        (params.tgswGadget securityParameter)
        (params.keySwitchGadget securityParameter)
        (schedule.rounds securityParameter)
        (threshold adversary securityParameter)
        (bundleDistinguisher
          (Adaptive.KeySwitchFirstSecurity.toPublicDistinguisher
            (queryCount := adversary.queryCount securityParameter)
            (params.encode securityParameter)
            (adversary.run securityParameter))))
      (LearningWithErrors.advantage
        (Native.BootstrapCutSecurity.batchModuleLweProblem
          (params.q securityParameter)
          (params.degree securityParameter)
          (params.ringRank securityParameter)
          (params.tgswLevels securityParameter)
          (params.lweDimension securityParameter)
          (params.ringErrorSampler securityParameter))
        ((realRingBatchReduction params adversary) securityParameter))
      (LearningWithErrors.advantage
        (Native.BootstrapCutSecurity.batchModuleLweProblem
          (params.q securityParameter)
          (params.degree securityParameter)
          (params.ringRank securityParameter)
          (params.tgswLevels securityParameter)
          (params.lweDimension securityParameter)
          (params.ringErrorSampler securityParameter))
        ((zeroRingBatchReduction params adversary) securityParameter))
      (LearningWithErrors.advantage
        (Native.KeySwitchSecurity.binaryLweProblem
          (params.q securityParameter)
          (params.lweDimension securityParameter)
          (adversary.queryCount securityParameter)
          (params.inputErrorSampler securityParameter))
        ((inputBatchLWEReduction params adversary).run securityParameter)))
  simpa only [securityGame, searchSecurityGame, searchReduction, lossSecurityGame, loss,
    CutCycleSecurity.ringBatchLWESecurityGame, inputBatchLWESecurityGame,
    inputBatchLWEReduction, successProbability,
    ENNReal.ofReal_toReal probOutput_ne_top] using hExpanded

/-- **Balanced pointwise asymptotic bound.** The arbitrary threshold and opaque loss are replaced
by a factor two on finite-search success and the concrete summed majority error. -/
theorem securityGame_advantage_le_two_mul_finiteSearch_add_two_mul_balancedError_add_lwe
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (hError : ∀ securityParameter,
      Pr[⊥ | params.keySwitchErrorSampler securityParameter] = 0)
    (schedule : PolynomialViewSchedule params)
    (adversary : PolynomialQueryAdversary params)
    (securityParameter : ℕ) :
    (securityGame params).advantage adversary securityParameter ≤
      2 * (searchSecurityGame params schedule).advantage
          (searchReduction params schedule adversary) securityParameter +
        2 * (balancedErrorSecurityGame params schedule).advantage
          adversary securityParameter +
        (CutCycleSecurity.ringBatchLWESecurityGame params).advantage
          (realRingBatchReduction params adversary) securityParameter +
        (CutCycleSecurity.ringBatchLWESecurityGame params).advantage
          (zeroRingBatchReduction params adversary) securityParameter +
        (inputBatchLWESecurityGame params).advantage
          (inputBatchLWEReduction params adversary) securityParameter := by
  have h :=
    Adaptive.KeySwitchFirstFiniteView.abs_signedAdvantage_real_le_two_mul_finiteSearch_add_two_mul_error_add_two_moduleLwe_add_inputLwe
      (adversary.queryCount securityParameter)
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.inputErrorSampler securityParameter)
      (hError securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (schedule.reference securityParameter)
      (schedule.rounds securityParameter)
      (params.encode securityParameter)
      (adversary.run securityParameter)
      (adversary.isQueryBound securityParameter)
  let finiteDistinguisher := bundleDistinguisher
    (Adaptive.KeySwitchFirstSecurity.toPublicDistinguisher
      (queryCount := adversary.queryCount securityParameter)
      (params.encode securityParameter)
      (adversary.run securityParameter))
  let searchSuccess := successProbability
    (params.ringErrorSampler securityParameter)
    (params.keySwitchErrorSampler securityParameter)
    (params.inputErrorSampler securityParameter)
    (params.tgswGadget securityParameter)
    (params.keySwitchGadget securityParameter)
    (schedule.rounds securityParameter)
    (amplifiedSolver
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.inputErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (schedule.rounds securityParameter)
      finiteDistinguisher)
  let majorityError := balancedAmplificationError
    (params.ringErrorSampler securityParameter)
    (params.keySwitchErrorSampler securityParameter)
    (params.inputErrorSampler securityParameter)
    (params.tgswGadget securityParameter)
    (params.keySwitchGadget securityParameter)
    (schedule.rounds securityParameter)
    finiteDistinguisher
  have hSearchNe : searchSuccess ≠ ⊤ := probOutput_ne_top
  have hMajorityNe : majorityError ≠ ⊤ :=
    balancedAmplificationError_ne_top
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.inputErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (schedule.rounds securityParameter)
      finiteDistinguisher
  have hSearchLift : ENNReal.ofReal (2 * searchSuccess.toReal) = 2 * searchSuccess := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_toReal hSearchNe]
    norm_num
  have hMajorityLift : ENNReal.ofReal (2 * majorityError.toReal) = 2 * majorityError := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_toReal hMajorityNe]
    norm_num
  have hLift := ENNReal.ofReal_le_ofReal h
  have hExpanded := hLift.trans
    (ofReal_add_five_le
      (2 * searchSuccess.toReal)
      (2 * majorityError.toReal)
      (LearningWithErrors.advantage
        (Native.BootstrapCutSecurity.batchModuleLweProblem
          (params.q securityParameter)
          (params.degree securityParameter)
          (params.ringRank securityParameter)
          (params.tgswLevels securityParameter)
          (params.lweDimension securityParameter)
          (params.ringErrorSampler securityParameter))
        ((realRingBatchReduction params adversary) securityParameter))
      (LearningWithErrors.advantage
        (Native.BootstrapCutSecurity.batchModuleLweProblem
          (params.q securityParameter)
          (params.degree securityParameter)
          (params.ringRank securityParameter)
          (params.tgswLevels securityParameter)
          (params.lweDimension securityParameter)
          (params.ringErrorSampler securityParameter))
        ((zeroRingBatchReduction params adversary) securityParameter))
      (LearningWithErrors.advantage
        (Native.KeySwitchSecurity.binaryLweProblem
          (params.q securityParameter)
          (params.lweDimension securityParameter)
          (adversary.queryCount securityParameter)
          (params.inputErrorSampler securityParameter))
        ((inputBatchLWEReduction params adversary).run securityParameter)))
  rw [hSearchLift, hMajorityLift] at hExpanded
  simpa only [securityGame, searchSecurityGame, searchReduction,
    balancedErrorSecurityGame, balancedError, CutCycleSecurity.ringBatchLWESecurityGame,
    inputBatchLWESecurityGame, inputBatchLWEReduction, finiteDistinguisher,
    searchSuccess, majorityError] using hExpanded

/-- **Residual pointwise asymptotic bound.** The balanced error is capped by half the decision
advantage, so this residual vanishes on zero-advantage parameter families. -/
theorem securityGame_advantage_le_two_mul_finiteSearch_add_two_mul_residual_add_lwe
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (hError : ∀ securityParameter,
      Pr[⊥ | params.keySwitchErrorSampler securityParameter] = 0)
    (schedule : PolynomialViewSchedule params)
    (adversary : PolynomialQueryAdversary params)
    (securityParameter : ℕ) :
    (securityGame params).advantage adversary securityParameter ≤
      2 * (searchSecurityGame params schedule).advantage
          (searchReduction params schedule adversary) securityParameter +
        2 * (balancedResidualSecurityGame params schedule).advantage
          adversary securityParameter +
        (CutCycleSecurity.ringBatchLWESecurityGame params).advantage
          (realRingBatchReduction params adversary) securityParameter +
        (CutCycleSecurity.ringBatchLWESecurityGame params).advantage
          (zeroRingBatchReduction params adversary) securityParameter +
        (inputBatchLWESecurityGame params).advantage
          (inputBatchLWEReduction params adversary) securityParameter := by
  have h :=
    Adaptive.KeySwitchFirstFiniteView.abs_signedAdvantage_real_le_two_mul_finiteSearch_add_two_mul_residual_add_two_moduleLwe_add_inputLwe
      (adversary.queryCount securityParameter)
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.inputErrorSampler securityParameter)
      (hError securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (schedule.reference securityParameter)
      (schedule.rounds securityParameter)
      (params.encode securityParameter)
      (adversary.run securityParameter)
      (adversary.isQueryBound securityParameter)
  let finiteDistinguisher := bundleDistinguisher
    (Adaptive.KeySwitchFirstSecurity.toPublicDistinguisher
      (queryCount := adversary.queryCount securityParameter)
      (params.encode securityParameter)
      (adversary.run securityParameter))
  let searchSuccess := successProbability
    (params.ringErrorSampler securityParameter)
    (params.keySwitchErrorSampler securityParameter)
    (params.inputErrorSampler securityParameter)
    (params.tgswGadget securityParameter)
    (params.keySwitchGadget securityParameter)
    (schedule.rounds securityParameter)
    (amplifiedSolver
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.inputErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (schedule.rounds securityParameter)
      finiteDistinguisher)
  let residualError := Adaptive.KeySwitchFirstFiniteView.balancedResidual
    (params.ringErrorSampler securityParameter)
    (params.keySwitchErrorSampler securityParameter)
    (params.inputErrorSampler securityParameter)
    (params.tgswGadget securityParameter)
    (params.keySwitchGadget securityParameter)
    (schedule.rounds securityParameter)
    finiteDistinguisher
  have hSearchNe : searchSuccess ≠ ⊤ := probOutput_ne_top
  have hSearchLift : ENNReal.ofReal (2 * searchSuccess.toReal) = 2 * searchSuccess := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
      ENNReal.ofReal_toReal hSearchNe]
    norm_num
  have hResidualLift :
      ENNReal.ofReal (2 * residualError) = 2 * ENNReal.ofReal residualError := by
    rw [ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hLift := ENNReal.ofReal_le_ofReal h
  have hExpanded := hLift.trans
    (ofReal_add_five_le
      (2 * searchSuccess.toReal)
      (2 * residualError)
      (LearningWithErrors.advantage
        (Native.BootstrapCutSecurity.batchModuleLweProblem
          (params.q securityParameter)
          (params.degree securityParameter)
          (params.ringRank securityParameter)
          (params.tgswLevels securityParameter)
          (params.lweDimension securityParameter)
          (params.ringErrorSampler securityParameter))
        ((realRingBatchReduction params adversary) securityParameter))
      (LearningWithErrors.advantage
        (Native.BootstrapCutSecurity.batchModuleLweProblem
          (params.q securityParameter)
          (params.degree securityParameter)
          (params.ringRank securityParameter)
          (params.tgswLevels securityParameter)
          (params.lweDimension securityParameter)
          (params.ringErrorSampler securityParameter))
        ((zeroRingBatchReduction params adversary) securityParameter))
      (LearningWithErrors.advantage
        (Native.KeySwitchSecurity.binaryLweProblem
          (params.q securityParameter)
          (params.lweDimension securityParameter)
          (adversary.queryCount securityParameter)
          (params.inputErrorSampler securityParameter))
        ((inputBatchLWEReduction params adversary).run securityParameter)))
  rw [hSearchLift, hResidualLift] at hExpanded
  simpa only [securityGame, searchSecurityGame, searchReduction,
    balancedResidualSecurityGame, balancedResidual,
    CutCycleSecurity.ringBatchLWESecurityGame, inputBatchLWESecurityGame,
    inputBatchLWEReduction, finiteDistinguisher, searchSuccess, residualError] using hExpanded

/-- **Asymptotic adaptive TFHE security from finite augmented search.** If the polynomial-view
real scalar-search game, the explicit amplification deficit, and all three ordinary post-cut LWE
games are secure for the corresponding reduced efficient families, then the honest adaptive TFHE
game has negligible advantage. -/
theorem secureAgainst_of_finiteSearch_and_lwe
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (hError : ∀ securityParameter,
      Pr[⊥ | params.keySwitchErrorSampler securityParameter] = 0)
    (schedule : PolynomialViewSchedule params)
    (threshold : ThresholdFamily params)
    (hthreshold_pos : ∀ adversary securityParameter,
      0 < threshold adversary securityParameter)
    (hthreshold_one : ∀ adversary securityParameter,
      threshold adversary securityParameter ≤ 1)
    (isPPT : PolynomialQueryAdversary params → Prop)
    (searchIsPPT : SearchAdversaryFamily params schedule → Prop)
    (realRingBatchIsPPT zeroRingBatchIsPPT :
      CutCycleSecurity.RingBatchLWEAdversaryFamily params → Prop)
    (inputBatchIsPPT : InputBatchLWEAdversaryFamily params → Prop)
    (hSearchClosed : ∀ adversary, isPPT adversary →
      searchIsPPT (searchReduction params schedule adversary))
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT (realRingBatchReduction params adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT (zeroRingBatchReduction params adversary))
    (hInputBatchClosed : ∀ adversary, isPPT adversary →
      inputBatchIsPPT (inputBatchLWEReduction params adversary))
    (hSearch : (searchSecurityGame params schedule).secureAgainst searchIsPPT)
    (hLoss : (lossSecurityGame params schedule threshold).secureAgainst isPPT)
    (hRealRingBatch :
      (CutCycleSecurity.ringBatchLWESecurityGame params).secureAgainst realRingBatchIsPPT)
    (hZeroRingBatch :
      (CutCycleSecurity.ringBatchLWESecurityGame params).secureAgainst zeroRingBatchIsPPT)
    (hInputBatch :
      (inputBatchLWESecurityGame params).secureAgainst inputBatchIsPPT) :
    (securityGame params).secureAgainst isPPT := by
  intro adversary hadversary
  exact negligible_of_le
    (securityGame_advantage_le_finiteSearch_add_loss_add_two_ringBatchLWE_add_inputLWE
      params hError schedule threshold hthreshold_pos hthreshold_one adversary)
    (negligible_add
      (negligible_add
        (negligible_add
          (negligible_add
            (hSearch _ (hSearchClosed adversary hadversary))
            (hLoss adversary hadversary))
          (hRealRingBatch _ (hRealRingBatchClosed adversary hadversary)))
        (hZeroRingBatch _ (hZeroRingBatchClosed adversary hadversary)))
      (hInputBatch _ (hInputBatchClosed adversary hadversary)))

/-- **Balanced asymptotic adaptive TFHE security.** Negligible polynomial-view augmented-search
success, negligible explicit majority error, and the three ordinary post-cut LWE games imply
negligible honest adaptive TFHE advantage.  Constant factors of two are absorbed by
negligibility, so no separate amplification-deficit assumption remains. -/
theorem secureAgainst_of_finiteSearch_and_balancedError_and_lwe
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (hError : ∀ securityParameter,
      Pr[⊥ | params.keySwitchErrorSampler securityParameter] = 0)
    (schedule : PolynomialViewSchedule params)
    (isPPT : PolynomialQueryAdversary params → Prop)
    (searchIsPPT : SearchAdversaryFamily params schedule → Prop)
    (realRingBatchIsPPT zeroRingBatchIsPPT :
      CutCycleSecurity.RingBatchLWEAdversaryFamily params → Prop)
    (inputBatchIsPPT : InputBatchLWEAdversaryFamily params → Prop)
    (hSearchClosed : ∀ adversary, isPPT adversary →
      searchIsPPT (searchReduction params schedule adversary))
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT (realRingBatchReduction params adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT (zeroRingBatchReduction params adversary))
    (hInputBatchClosed : ∀ adversary, isPPT adversary →
      inputBatchIsPPT (inputBatchLWEReduction params adversary))
    (hSearch : (searchSecurityGame params schedule).secureAgainst searchIsPPT)
    (hBalancedError : (balancedErrorSecurityGame params schedule).secureAgainst isPPT)
    (hRealRingBatch :
      (CutCycleSecurity.ringBatchLWESecurityGame params).secureAgainst realRingBatchIsPPT)
    (hZeroRingBatch :
      (CutCycleSecurity.ringBatchLWESecurityGame params).secureAgainst zeroRingBatchIsPPT)
    (hInputBatch :
      (inputBatchLWESecurityGame params).secureAgainst inputBatchIsPPT) :
    (securityGame params).secureAgainst isPPT := by
  intro adversary hadversary
  have hSearchNeg : negligible (fun securityParameter ↦
      2 * (searchSecurityGame params schedule).advantage
        (searchReduction params schedule adversary) securityParameter) :=
    negligible_const_mul
      (hSearch _ (hSearchClosed adversary hadversary)) (by norm_num)
  have hErrorNeg : negligible (fun securityParameter ↦
      2 * (balancedErrorSecurityGame params schedule).advantage
        adversary securityParameter) :=
    negligible_const_mul (hBalancedError adversary hadversary) (by norm_num)
  exact negligible_of_le
    (securityGame_advantage_le_two_mul_finiteSearch_add_two_mul_balancedError_add_lwe
      params hError schedule adversary)
    (negligible_add
      (negligible_add
        (negligible_add
          (negligible_add hSearchNeg hErrorNeg)
          (hRealRingBatch _ (hRealRingBatchClosed adversary hadversary)))
        (hZeroRingBatch _ (hZeroRingBatchClosed adversary hadversary)))
      (hInputBatch _ (hInputBatchClosed adversary hadversary)))

/-- **Preferred residual form of the asymptotic theorem.** The explicit residual is capped by
half the decision advantage and hence does not impose a nonzero majority-error obligation on
zero-advantage adversaries. -/
theorem secureAgainst_of_finiteSearch_and_residual_and_lwe
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (hError : ∀ securityParameter,
      Pr[⊥ | params.keySwitchErrorSampler securityParameter] = 0)
    (schedule : PolynomialViewSchedule params)
    (isPPT : PolynomialQueryAdversary params → Prop)
    (searchIsPPT : SearchAdversaryFamily params schedule → Prop)
    (realRingBatchIsPPT zeroRingBatchIsPPT :
      CutCycleSecurity.RingBatchLWEAdversaryFamily params → Prop)
    (inputBatchIsPPT : InputBatchLWEAdversaryFamily params → Prop)
    (hSearchClosed : ∀ adversary, isPPT adversary →
      searchIsPPT (searchReduction params schedule adversary))
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT (realRingBatchReduction params adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT (zeroRingBatchReduction params adversary))
    (hInputBatchClosed : ∀ adversary, isPPT adversary →
      inputBatchIsPPT (inputBatchLWEReduction params adversary))
    (hSearch : (searchSecurityGame params schedule).secureAgainst searchIsPPT)
    (hResidual : (balancedResidualSecurityGame params schedule).secureAgainst isPPT)
    (hRealRingBatch :
      (CutCycleSecurity.ringBatchLWESecurityGame params).secureAgainst realRingBatchIsPPT)
    (hZeroRingBatch :
      (CutCycleSecurity.ringBatchLWESecurityGame params).secureAgainst zeroRingBatchIsPPT)
    (hInputBatch :
      (inputBatchLWESecurityGame params).secureAgainst inputBatchIsPPT) :
    (securityGame params).secureAgainst isPPT := by
  intro adversary hadversary
  have hSearchNeg : negligible (fun securityParameter ↦
      2 * (searchSecurityGame params schedule).advantage
        (searchReduction params schedule adversary) securityParameter) :=
    negligible_const_mul
      (hSearch _ (hSearchClosed adversary hadversary)) (by norm_num)
  have hResidualNeg : negligible (fun securityParameter ↦
      2 * (balancedResidualSecurityGame params schedule).advantage
        adversary securityParameter) :=
    negligible_const_mul (hResidual adversary hadversary) (by norm_num)
  exact negligible_of_le
    (securityGame_advantage_le_two_mul_finiteSearch_add_two_mul_residual_add_lwe
      params hError schedule adversary)
    (negligible_add
      (negligible_add
        (negligible_add
          (negligible_add hSearchNeg hResidualNeg)
          (hRealRingBatch _ (hRealRingBatchClosed adversary hadversary)))
        (hZeroRingBatch _ (hZeroRingBatchClosed adversary hadversary)))
      (hInputBatch _ (hInputBatchClosed adversary hadversary)))

/-- **Coordinate-error form of the asymptotic theorem.** It is enough to prove negligibility of
one coordinate's balanced majority recurrence. The schedule's polynomial view bound absorbs the
complete scalar-coordinate sum automatically. -/
theorem secureAgainst_of_finiteSearch_and_coordinateError_and_lwe
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (hError : ∀ securityParameter,
      Pr[⊥ | params.keySwitchErrorSampler securityParameter] = 0)
    (schedule : PolynomialViewSchedule params)
    (isPPT : PolynomialQueryAdversary params → Prop)
    (searchIsPPT : SearchAdversaryFamily params schedule → Prop)
    (realRingBatchIsPPT zeroRingBatchIsPPT :
      CutCycleSecurity.RingBatchLWEAdversaryFamily params → Prop)
    (inputBatchIsPPT : InputBatchLWEAdversaryFamily params → Prop)
    (hSearchClosed : ∀ adversary, isPPT adversary →
      searchIsPPT (searchReduction params schedule adversary))
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT (realRingBatchReduction params adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT (zeroRingBatchReduction params adversary))
    (hInputBatchClosed : ∀ adversary, isPPT adversary →
      inputBatchIsPPT (inputBatchLWEReduction params adversary))
    (hSearch : (searchSecurityGame params schedule).secureAgainst searchIsPPT)
    (hCoordinateError :
      (coordinateBalancedErrorSecurityGame params schedule).secureAgainst isPPT)
    (hRealRingBatch :
      (CutCycleSecurity.ringBatchLWESecurityGame params).secureAgainst realRingBatchIsPPT)
    (hZeroRingBatch :
      (CutCycleSecurity.ringBatchLWESecurityGame params).secureAgainst zeroRingBatchIsPPT)
    (hInputBatch :
      (inputBatchLWESecurityGame params).secureAgainst inputBatchIsPPT) :
    (securityGame params).secureAgainst isPPT :=
  secureAgainst_of_finiteSearch_and_balancedError_and_lwe
    params hError schedule isPPT searchIsPPT realRingBatchIsPPT
    zeroRingBatchIsPPT inputBatchIsPPT hSearchClosed hRealRingBatchClosed
    hZeroRingBatchClosed hInputBatchClosed hSearch
    (balancedErrorSecurityGame_secureAgainst_of_coordinateError
      params schedule isPPT hCoordinateError)
    hRealRingBatch hZeroRingBatch hInputBatch

end FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView
