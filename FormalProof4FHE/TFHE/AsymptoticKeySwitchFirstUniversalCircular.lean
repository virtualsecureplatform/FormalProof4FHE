/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AdaptiveKeySwitchFirstFiniteViewCircular
import FormalProof4FHE.TFHE.AsymptoticKeySwitchFirstUniversalFiniteView

/-!
# Adaptive TFHE Security from Universal Full-Transcript Circular Decision

This module replaces the universal augmented-search premise of the logarithmic amplification
theorem by a decision-style circular pseudorandomness premise.  A recovery solver induces a
secret-aware continuation that uses the hidden scalar key only for the experiment's final equality
check.  The finite decomposition bounds its real recovery probability by:

1. the complete augmented-batch real-versus-independent circular advantage; and
2. the exact independent guessing probability `2 ^ (-lweDimension)`.

If the scalar dimension is at least the security parameter, the second term is negligible.  The
result composes with the schedule-per-exponent amplification theorem, leaving a universal
polynomial-view circular *decision* assumption rather than a circular search assumption.
-/

open ENNReal OracleComp Filter Topology

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView

open FormalProof4FHE.TFHE.Encryption.Adaptive.KeySwitchFirstFiniteView

/-! ## Circular adversary families -/

/-- Parameter-indexed full-transcript circular continuations.  Query-count data is retained
because every augmented view contains the corresponding bounded input tape. -/
structure BatchCircularAdversaryFamily {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params) where
  queryCount : ℕ → ℕ
  queryPolynomial : Polynomial ℕ
  queryCount_le : ∀ securityParameter,
    queryCount securityParameter ≤ queryPolynomial.eval securityParameter
  run : (securityParameter : ℕ) →
    BatchCircularContinuation
      (params.q securityParameter)
      (params.degree securityParameter)
      (params.ringRank securityParameter)
      (params.tgswLevels securityParameter)
      (params.lweDimension securityParameter)
      (params.keySwitchLevels securityParameter)
      (queryCount securityParameter)
      (schedule.rounds securityParameter)

/-- Security game for complete augmented-batch real-versus-independent circular decision. -/
noncomputable def batchCircularSecurityGame {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params) :
    SecurityGame (BatchCircularAdversaryFamily params schedule) where
  advantage adversary securityParameter :=
    ENNReal.ofReal
      (batchCircularAdvantage
        (params.ringErrorSampler securityParameter)
        (params.keySwitchErrorSampler securityParameter)
        (params.inputErrorSampler securityParameter)
        (params.tgswGadget securityParameter)
        (params.keySwitchGadget securityParameter)
        (schedule.rounds securityParameter)
        (adversary.run securityParameter))

/-- Turn an augmented scalar-search family into its recovery-checking circular continuation. -/
noncomputable def circularRecoveryReduction {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params)
    (solver : SearchAdversaryFamily params schedule) :
    BatchCircularAdversaryFamily params schedule where
  queryCount := solver.queryCount
  queryPolynomial := solver.queryPolynomial
  queryCount_le := solver.queryCount_le
  run securityParameter := scalarRecoveryContinuation (solver.run securityParameter)

/-- Pointwise search recovery is bounded by circular decision and exact uniform guessing. -/
theorem searchSecurityGame_advantage_le_batchCircular_add_guess
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params)
    (solver : SearchAdversaryFamily params schedule)
    (securityParameter : ℕ) :
    (searchSecurityGame params schedule).advantage solver securityParameter ≤
      (batchCircularSecurityGame params schedule).advantage
          (circularRecoveryReduction params schedule solver) securityParameter +
        ((2 : ENNReal) ^ params.lweDimension securityParameter)⁻¹ := by
  simpa [searchSecurityGame, batchCircularSecurityGame, circularRecoveryReduction] using
    (successProbability_le_batchCircularAdvantage_add_guess
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.inputErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (schedule.rounds securityParameter)
      (solver.run securityParameter))

/-! ## Negligibility of independent scalar-key guessing -/

/-- The reciprocal size of an `n`-bit key space is negligible in `n`. -/
theorem negligible_inv_two_pow :
    negligible (fun securityParameter : ℕ => ((2 : ENNReal) ^ securityParameter)⁻¹) := by
  intro power
  have hreal : Tendsto
      (fun securityParameter : ℕ =>
        (securityParameter : ℝ) ^ power * (1 / 2 : ℝ) ^ securityParameter)
      atTop (𝓝 0) :=
    tendsto_pow_const_mul_const_pow_of_lt_one power (by norm_num) (by norm_num)
  have h := (ENNReal.continuous_ofReal.tendsto 0).comp hreal
  convert h using 1
  · funext securityParameter
    change (securityParameter : ENNReal) ^ power *
        ((2 : ENNReal) ^ securityParameter)⁻¹ =
      ENNReal.ofReal
        ((securityParameter : ℝ) ^ power * (1 / 2 : ℝ) ^ securityParameter)
    rw [ENNReal.inv_pow]
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_natCast, ENNReal.ofReal_pow (by positivity)]
    have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (2 : ENNReal)⁻¹ := by
      rw [one_div, ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2)]
      norm_num
    rw [hhalf]
  · simp

/-- If the TFHE scalar dimension dominates the security parameter, exact guessing of that key is
negligible. -/
theorem binaryGuessingBound_negligible_of_securityParameter_le_dimension
    (dimension : ℕ → ℕ)
    (hDimension : ∀ securityParameter, securityParameter ≤ dimension securityParameter) :
    negligible (fun securityParameter =>
      ((2 : ENNReal) ^ dimension securityParameter)⁻¹) := by
  apply negligible_of_le (g := fun securityParameter =>
    ((2 : ENNReal) ^ securityParameter)⁻¹)
  · intro securityParameter
    rw [ENNReal.inv_pow, ENNReal.inv_pow]
    exact pow_le_pow_right_of_le_one' (by norm_num) (hDimension securityParameter)
  · exact negligible_inv_two_pow

/-! ## Search security from circular decision security -/

/-- Universal full-transcript circular decision security implies augmented scalar-search
security, provided recovery continuations remain in the admitted circular adversary class. -/
theorem searchSecurityGame_secureAgainst_of_batchCircular
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (schedule : PolynomialViewSchedule params)
    (hDimension : ∀ securityParameter,
      securityParameter ≤ params.lweDimension securityParameter)
    (searchIsPPT : SearchAdversaryFamily params schedule → Prop)
    (circularIsPPT : BatchCircularAdversaryFamily params schedule → Prop)
    (hClosed : ∀ solver, searchIsPPT solver →
      circularIsPPT (circularRecoveryReduction params schedule solver))
    (hCircular :
      (batchCircularSecurityGame params schedule).secureAgainst circularIsPPT) :
    (searchSecurityGame params schedule).secureAgainst searchIsPPT := by
  intro solver hsolver
  exact negligible_of_le
    (fun securityParameter =>
      searchSecurityGame_advantage_le_batchCircular_add_guess
        params schedule solver securityParameter)
    (negligible_add
      (hCircular (circularRecoveryReduction params schedule solver)
        (hClosed solver hsolver))
      (binaryGuessingBound_negligible_of_securityParameter_le_dimension
        params.lweDimension hDimension))

/-! ## Adaptive TFHE composition -/

/-- Predicate family for efficient full-transcript circular continuations, indexed by the
polynomial-view schedule. -/
abbrev UniversalBatchCircularIsPPT {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :=
  (schedule : PolynomialViewSchedule params) →
    BatchCircularAdversaryFamily params schedule → Prop

/-- **Adaptive TFHE security from universal full-transcript circular decision and ordinary
post-cut LWE.**

The schedule-dependent search premise is derived internally from circular decision security and
the negligible `2⁻ˡʷᵉᴰⁱᵐᵉⁿˢⁱᵒⁿ` guessing term.  The logarithmic amplification residual is already
discharged by `secureAgainst_of_universal_finiteSearch_and_lwe`. -/
theorem secureAgainst_of_universal_batchCircular_and_lwe
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (hError : ∀ securityParameter,
      Pr[⊥ | params.keySwitchErrorSampler securityParameter] = 0)
    (reference : (securityParameter : ℕ) → Fin (params.lweDimension securityParameter))
    (dimensionPolynomial : Polynomial ℕ)
    (hDimensionUpper : ∀ securityParameter,
      params.lweDimension securityParameter ≤
        dimensionPolynomial.eval securityParameter)
    (hDimensionLower : ∀ securityParameter,
      securityParameter ≤ params.lweDimension securityParameter)
    (isPPT : PolynomialQueryAdversary params → Prop)
    (circularIsPPT : UniversalBatchCircularIsPPT params)
    (realRingBatchIsPPT zeroRingBatchIsPPT :
      CutCycleSecurity.RingBatchLWEAdversaryFamily params → Prop)
    (inputBatchIsPPT : InputBatchLWEAdversaryFamily params → Prop)
    (hCircularClosed : ∀ schedule adversary, isPPT adversary →
      circularIsPPT schedule
        (circularRecoveryReduction params schedule
          (searchReduction params schedule adversary)))
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT (realRingBatchReduction params adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT (zeroRingBatchReduction params adversary))
    (hInputBatchClosed : ∀ adversary, isPPT adversary →
      inputBatchIsPPT (inputBatchLWEReduction params adversary))
    (hCircular : ∀ schedule,
      (batchCircularSecurityGame params schedule).secureAgainst
        (circularIsPPT schedule))
    (hRealRingBatch :
      (CutCycleSecurity.ringBatchLWESecurityGame params).secureAgainst realRingBatchIsPPT)
    (hZeroRingBatch :
      (CutCycleSecurity.ringBatchLWESecurityGame params).secureAgainst zeroRingBatchIsPPT)
    (hInputBatch :
      (inputBatchLWESecurityGame params).secureAgainst inputBatchIsPPT) :
    (securityGame params).secureAgainst isPPT := by
  let searchIsPPT : UniversalSearchIsPPT params :=
    fun schedule solver =>
      circularIsPPT schedule (circularRecoveryReduction params schedule solver)
  apply secureAgainst_of_universal_finiteSearch_and_lwe
    params hError reference dimensionPolynomial hDimensionUpper isPPT searchIsPPT
    realRingBatchIsPPT zeroRingBatchIsPPT inputBatchIsPPT
  · intro schedule adversary hadversary
    exact hCircularClosed schedule adversary hadversary
  · exact hRealRingBatchClosed
  · exact hZeroRingBatchClosed
  · exact hInputBatchClosed
  · intro schedule
    exact searchSecurityGame_secureAgainst_of_batchCircular
      params schedule hDimensionLower
      (searchIsPPT schedule) (circularIsPPT schedule)
      (fun _ h => h) (hCircular schedule)
  · exact hRealRingBatch
  · exact hZeroRingBatch
  · exact hInputBatch

end FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView
