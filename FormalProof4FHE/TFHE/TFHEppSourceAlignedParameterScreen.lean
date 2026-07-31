/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SourceAlignedBRKKSKJointLaw
import FormalProof4FHE.TFHE.TFHEppSubsetTechnical

/-!
# TFHEpp source-aligned correlated-error parameter screen

This file specializes the technical part of the source-aligned BRK/KSK route to the shape of
TFHEpp's default level-zero/level-one bootstrap.  It proves three facts.

* If the pre-key-switch phase contains the BRK error paired with the propagated factor and the
  aligned KSK uses the correlated error `brkError + freshError`, the complete reused BRK-error
  term cancels exactly.
* The propagated factor may depend on the complete public bootstrap state.  When the correction
  error is sampled independently afterwards, a uniform covariance-energy bound gives one
  subgaussian tail bound by conditioning and averaging; there is no reachable-factor union loss.
* The current non-bundled parameter shape has `3780` BRK rows and hence `3870720` aligned scalar
  columns.  This is strictly wider than the `5516` rows of the native subset KSK.

The arithmetic is a parameter screen, not a source-code equivalence theorem.  In particular, it
does not assert that TFHEpp currently emits the widened correlated aligned KSK, identify the C++
finite modular-Gaussian sampler with the MGF certificate, prove the two prefix-LWE assumptions,
or account for every ordinary bootstrap rounding term.
-/

set_option autoImplicit false

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.TFHEppSourceAlignedParameterScreen

noncomputable section

open SubsetKeyTrapdoorTheorems.SourceAligned

/-! ## Exact correlated-error cancellation -/

namespace CorrelatedCorrectness

/-- The BRK error accumulated before key switching cancels the matching component of the
correlated aligned-KSK error.  Only the independently sampled correction remains. -/
theorem error_pairing_cancels
    {R Factor : Type} [CommRing R] [Fintype Factor]
    (message : R) (factor brkError freshError : Factor → R) :
    message + dotProduct factor brkError -
        dotProduct factor (brkError + freshError) =
      message - dotProduct factor freshError := by
  rw [dotProduct_add]
  abel

/-- End-to-end phase form of `error_pairing_cancels`, using the actual source-aligned key-switch
operation.  The factor and the ciphertext may already depend on the complete BRK transcript. -/
theorem keySwitch_phase_eq_message_sub_fresh
    {R Prefix Suffix Factor : Type} [CommRing R]
    [Fintype Prefix] [Fintype Suffix] [Fintype Factor]
    (prefixMask : Matrix Prefix Factor R)
    (gadget : Matrix Suffix Factor R)
    (prefixSecret : Prefix → R) (suffixSecret : Suffix → R)
    (brkError freshError : Factor → R) (message : R)
    (ciphertext : FactorCiphertext R Prefix Suffix Factor)
    (phase_eq : ciphertext.phase gadget prefixSecret suffixSecret =
      message + dotProduct ciphertext.factor brkError) :
    (ciphertext.keySwitch prefixMask
        (randomGadgetKSKBody prefixMask gadget prefixSecret suffixSecret
          (brkError + freshError))).2 -
      dotProduct prefixSecret
        (ciphertext.keySwitch prefixMask
          (randomGadgetKSKBody prefixMask gadget prefixSecret suffixSecret
            (brkError + freshError))).1 =
      message - dotProduct ciphertext.factor freshError := by
  rw [FactorCiphertext.keySwitch_phase, phase_eq]
  exact error_pairing_cancels message ciphertext.factor brkError freshError

end CorrelatedCorrectness

/-! ## Transcript-adaptive factor against independent fresh noise -/

namespace AdaptiveFreshNoise

open SourceAlignedBRKKSKJointLaw.NativeCompiler
open SourceAlignedBRKKSKJointLaw.NativeCompiler.EvaluatorTail
open SourceAlignedFactorPropagation

/-- Sample a public bootstrap state first and an independent correction error second. -/
def independentProduct {State Noise : Type}
    (stateSampler : ProbComp State) (noiseSampler : ProbComp Noise) :
    ProbComp (State × Noise) :=
  stateSampler >>= fun state ↦ (fun noise ↦ (state, noise)) <$> noiseSampler

/-- For spherical covariance, covariance-proxy energy is variance times squared factor energy. -/
theorem covarianceEnergy_spherical
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (variance : ℝ) (factor : Index → ℝ) :
    covarianceEnergy (variance • (1 : Matrix Index Index ℝ)) factor =
      variance * Energy.factorEnergy factor := by
  unfold covarianceEnergy
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
  simp [Energy.factorEnergy, dotProduct, pow_two, Finset.mul_sum]

/-- Increasing a positive covariance proxy weakens the standard subgaussian exponent. -/
theorem exp_neg_sq_div_two_mono_variance
    (threshold variance varianceBound : ℝ)
    (variance_pos : 0 < variance) (variance_le : variance ≤ varianceBound) :
    Real.exp (-(threshold ^ 2) / (2 * variance)) ≤
      Real.exp (-(threshold ^ 2) / (2 * varianceBound)) := by
  have varianceBound_pos : 0 < varianceBound := variance_pos.trans_le variance_le
  apply Real.exp_le_exp.mpr
  have hquotient :
      threshold ^ 2 / (2 * varianceBound) ≤
        threshold ^ 2 / (2 * variance) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg threshold]
  simpa only [neg_div] using neg_le_neg hquotient

/-- Fixed-factor two-sided tail bound with a common upper bound on covariance energy. -/
theorem Certificate.absTail_le_uniformVariance
    {Noise Native Factor : Type} [Fintype Noise] [Fintype Native]
    {sampler : ProbComp Noise} {noiseVector : Noise → Native → ℝ}
    {residual : Factor → Native → ℝ} {covariance : Matrix Native Native ℝ}
    (certificate : Certificate Noise Native Factor sampler noiseVector residual covariance)
    (factor : Factor) (threshold varianceBound : ℝ) (threshold_nonneg : 0 ≤ threshold)
    (variance_pos : 0 < covarianceEnergy covariance (residual factor))
    (variance_le : covarianceEnergy covariance (residual factor) ≤ varianceBound) :
    Pr[(fun noise ↦ threshold ≤
        |dotProduct (residual factor) (noiseVector noise)|) | sampler].toReal ≤
      2 * Real.exp (-(threshold ^ 2) / (2 * varianceBound)) := by
  calc
    _ ≤ 2 * Real.exp (-(threshold ^ 2) /
          (2 * covarianceEnergy covariance (residual factor))) :=
      certificate.absTail factor threshold threshold_nonneg variance_pos
    _ ≤ 2 * Real.exp (-(threshold ^ 2) / (2 * varianceBound)) := by
      exact mul_le_mul_of_nonneg_left
        (exp_neg_sq_div_two_mono_variance threshold
          (covarianceEnergy covariance (residual factor)) varianceBound
          variance_pos variance_le) (by norm_num)

/-- A transcript-dependent factor costs no reachable-set union bound when the correction noise is
sampled independently after the transcript.  Conditioning fixes the factor, and averaging the
same pointwise tail estimate preserves it exactly. -/
theorem Certificate.adaptiveIndependentAbsTail
    {State Noise Native Factor : Type}
    [Fintype State] [Fintype Noise] [Fintype Native]
    {noiseSampler : ProbComp Noise} {noiseVector : Noise → Native → ℝ}
    {residual : Factor → Native → ℝ} {covariance : Matrix Native Native ℝ}
    (certificate : Certificate Noise Native Factor
      noiseSampler noiseVector residual covariance)
    (stateSampler : ProbComp State) (selectedFactor : State → Factor)
    (threshold varianceBound : ℝ) (threshold_nonneg : 0 ≤ threshold)
    (variance_pos : ∀ state ∈ support stateSampler,
      0 < covarianceEnergy covariance (residual (selectedFactor state)))
    (variance_le : ∀ state ∈ support stateSampler,
      covarianceEnergy covariance (residual (selectedFactor state)) ≤ varianceBound) :
    Pr[(fun output ↦ threshold ≤
        |dotProduct (residual (selectedFactor output.1))
          (noiseVector output.2)|) |
      independentProduct stateSampler noiseSampler].toReal ≤
        2 * Real.exp (-(threshold ^ 2) / (2 * varianceBound)) := by
  let bound := 2 * Real.exp (-(threshold ^ 2) / (2 * varianceBound))
  have probability_le :
      Pr[(fun output ↦ threshold ≤
          |dotProduct (residual (selectedFactor output.1))
            (noiseVector output.2)|) |
        independentProduct stateSampler noiseSampler] ≤ ENNReal.ofReal bound := by
    unfold independentProduct
    apply probEvent_bind_le_of_forall_le
    intro state state_mem
    rw [probEvent_map]
    change Pr[(fun noise ↦ threshold ≤
      |dotProduct (residual (selectedFactor state)) (noiseVector noise)|) |
        noiseSampler] ≤ ENNReal.ofReal bound
    rw [← ENNReal.ofReal_toReal probEvent_ne_top]
    apply ENNReal.ofReal_le_ofReal
    simpa only [bound] using
      Certificate.absTail_le_uniformVariance certificate (selectedFactor state)
        threshold varianceBound threshold_nonneg
        (variance_pos state state_mem) (variance_le state state_mem)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top probability_le
  rw [ENNReal.toReal_ofReal (by positivity : 0 ≤ bound)] at hreal
  exact hreal

end AdaptiveFreshNoise

/-! ## Default non-bundled TFHEpp shape -/

namespace Parameters

open TFHEppSubsetJointScreen.Parameters
open SourceAlignedFactorPropagation
open SourceAlignedFactorPropagation.NativeAlignment
open SourceAlignedBRKKSKJointLaw.NativeCompiler.EvaluatorTail

set_option exponentiation.threshold 1024

/-- Ring rank of the default level-one TRLWE. -/
def ringRank : ℕ := 1

/-- Number of gadget levels in the default level-one TRGSW. -/
def brkLevels : ℕ := 3

/-- Base-two logarithm of the default level-one gadget base. -/
def brkBasebit : ℕ := 6

/-- Complete number of non-bundled BRK/TGSW rows. -/
def brkRowCount : ℕ := controlRowCount ringRank brkLevels lvl0Dimension

/-- Coefficient-scalarized width of the source-aligned factor and KSK. -/
def alignedWidth : ℕ := brkRowCount * lvl1Dimension

/-- Largest absolute value emitted by the centered base-`2^6` decomposition. -/
def centeredDigitRadius : ℕ := 2 ^ (brkBasebit - 1)

/-- Worst-case factor energy if every coefficient is a centered gadget digit. -/
def factorEnergyBound : ℕ := alignedWidth * centeredDigitRadius ^ 2

/-- Integer-coordinate standard deviation corresponding to level-one `alpha = 2^-25`. -/
def lvl1IntegerSigma : ℕ := 2 ^ (32 - 25)

/-- Spherical fresh-error covariance proxy after pairing with a factor at the above bound. -/
def freshPairingVarianceBound : ℕ := lvl1IntegerSigma ^ 2 * factorEnergyBound

theorem brkRowCount_eq : brkRowCount = 3780 := by
  norm_num [brkRowCount, controlRowCount, ringRank, brkLevels,
    lvl0Dimension, TGSW.rowCount]

theorem alignedWidth_eq : alignedWidth = 3870720 := by
  norm_num [alignedWidth, brkRowCount, controlRowCount, ringRank, brkLevels,
    lvl0Dimension, lvl1Dimension, TGSW.rowCount]

theorem centeredDigitRadius_eq : centeredDigitRadius = 32 := by
  norm_num [centeredDigitRadius, brkBasebit]

theorem factorEnergyBound_eq : factorEnergyBound = 3963617280 := by
  norm_num [factorEnergyBound, alignedWidth, brkRowCount, controlRowCount,
    ringRank, brkLevels, lvl0Dimension, lvl1Dimension, centeredDigitRadius,
    brkBasebit, TGSW.rowCount]

theorem lvl1IntegerSigma_eq : lvl1IntegerSigma = 128 := by
  norm_num [lvl1IntegerSigma]

theorem freshPairingVarianceBound_eq :
    freshPairingVarianceBound = 64939905515520 := by
  norm_num [freshPairingVarianceBound, lvl1IntegerSigma, factorEnergyBound,
    alignedWidth, brkRowCount, controlRowCount, ringRank, brkLevels,
    lvl0Dimension, lvl1Dimension, centeredDigitRadius, brkBasebit,
    TGSW.rowCount]

/-- The source-aligned scalar layout is much wider than the native subset KSK layout.  This is a
shape mismatch, not an insecurity theorem. -/
theorem nativeSubsetWidth_lt_alignedWidth : lvl10KSKRows < alignedWidth := by
  norm_num [lvl10KSKRows, suffixDimension, lvl1Dimension, lvl0Dimension,
    lvl10Levels, lvl10DigitCount, alignedWidth, brkRowCount, controlRowCount,
    ringRank, brkLevels, TGSW.rowCount]

/-- Coordinatewise centered-digit bounds imply the advertised complete factor-energy bound. -/
theorem factorEnergy_le_bound
    (factor : Fin alignedWidth → ℝ)
    (coordinate_bound : ∀ coordinate,
      |factor coordinate| ≤ centeredDigitRadius) :
    Energy.factorEnergy factor ≤ factorEnergyBound := by
  unfold Energy.factorEnergy
  calc
    (∑ coordinate, factor coordinate ^ 2) ≤
        ∑ _coordinate : Fin alignedWidth, (centeredDigitRadius : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro coordinate _
      rw [← sq_abs]
      exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).2
        (coordinate_bound coordinate)
    _ = (factorEnergyBound : ℝ) := by
      simp [factorEnergyBound, nsmul_eq_mul]

/-- The coordinatewise digit premise implies the exact nominal spherical covariance-energy
budget consumed by the adaptive fresh-noise theorem. -/
theorem nominalSphericalCovarianceEnergy_le
    (factor : Fin alignedWidth → ℝ)
    (coordinate_bound : ∀ coordinate,
      |factor coordinate| ≤ centeredDigitRadius) :
    covarianceEnergy
        (((lvl1IntegerSigma : ℝ) ^ 2) •
          (1 : Matrix (Fin alignedWidth) (Fin alignedWidth) ℝ)) factor ≤
      freshPairingVarianceBound := by
  rw [AdaptiveFreshNoise.covarianceEnergy_spherical]
  calc
    (lvl1IntegerSigma : ℝ) ^ 2 * Energy.factorEnergy factor ≤
        (lvl1IntegerSigma : ℝ) ^ 2 * factorEnergyBound := by
      exact mul_le_mul_of_nonneg_left
        (factorEnergy_le_bound factor coordinate_bound) (sq_nonneg _)
    _ = (freshPairingVarianceBound : ℝ) := by
      norm_num [freshPairingVarianceBound]

/-- At the conservative integer threshold `2^28`, the nominal spherical fresh correction has
Chernoff exponent exactly `524288 / 945`.  This concerns only the fresh correction term after
exact BRK-error cancellation. -/
theorem nominalFreshExponent_eq :
    ((2 ^ 28 : ℝ) ^ 2) / (2 * freshPairingVarianceBound) =
      524288 / 945 := by
  norm_num [freshPairingVarianceBound, lvl1IntegerSigma, factorEnergyBound,
    alignedWidth, brkRowCount, controlRowCount, ringRank, brkLevels,
    lvl0Dimension, lvl1Dimension, centeredDigitRadius, brkBasebit,
    TGSW.rowCount]

end Parameters

end

end FormalProof4FHE.TFHE.TFHEppSourceAlignedParameterScreen
