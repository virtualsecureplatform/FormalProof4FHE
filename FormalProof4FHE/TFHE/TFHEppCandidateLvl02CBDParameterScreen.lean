/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.CenteredBinomialProofErrorSampler
import FormalProof4FHE.TFHE.TFHEppSourceAlignedParameterScreen
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Exact CBD parameter screen for the 27-bit lvl02 candidate

This file checks the proof-facing arithmetic for the proposed source-aligned TFHE lvl02 shape:

* modulus `2^27`;
* degree `2048`, split into a binary prefix and parity-placed ternary suffix of size `1024`;
* base-four decomposition with thirteen levels; and
* exact centered-binomial correction noise of width `eta = 2048`.

The centered-binomial MGF theorem supplies proxy `eta / 2 = 1024` directly.  No Gaussian or
finite-law comparison premise occurs in the resulting adaptive correction tail.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.TFHEppCandidateLvl02CBDParameterScreen

noncomputable section

open SourceAlignedFactorPropagation
open SourceAlignedFactorPropagation.NativeAlignment
open SourceAlignedBRKKSKJointLaw.NativeCompiler.EvaluatorTail

set_option exponentiation.threshold 1024

/-- Bit width of the target torus. -/
def modulusBits : ℕ := 27

/-- Proposed target modulus. -/
def modulus : ℕ := 2 ^ modulusBits

instance modulus_neZero : NeZero modulus := ⟨by norm_num [modulus, modulusBits]⟩

instance modulus_gt_one : Fact (1 < modulus) :=
  ⟨by norm_num [modulus, modulusBits]⟩

/-- Shared binary lvl0-prefix dimension. -/
def prefixDimension : ℕ := 1024

/-- Target negacyclic-ring degree. -/
def ringDegree : ℕ := 2048

/-- Independent parity-placed ternary suffix dimension. -/
def suffixDimension : ℕ := ringDegree - prefixDimension

/-- Rank of the target TRLWE. -/
def ringRank : ℕ := 1

/-- Number of target base-four gadget levels. -/
def brkLevels : ℕ := 13

/-- Base-two logarithm of the target gadget base. -/
def brkBasebit : ℕ := 2

/-- Covered high-order torus bits. -/
def decompositionCoverage : ℕ := brkLevels * brkBasebit

/-- Low-order bits intentionally discarded by decomposition. -/
def discardedBits : ℕ := modulusBits - decompositionCoverage

/-- Complete non-bundled BRK/TGSW row count. -/
def brkRowCount : ℕ :=
  controlRowCount ringRank brkLevels prefixDimension

/-- Coefficient-scalarized aligned-KSK width. -/
def alignedWidth : ℕ := brkRowCount * ringDegree

/-- Absolute bound for centered base-four digits. -/
def centeredDigitRadius : ℕ := 2 ^ (brkBasebit - 1)

/-- Worst-case squared factor norm. -/
def factorEnergyBound : ℕ := alignedWidth * centeredDigitRadius ^ 2

/-- Exact centered-binomial width. -/
def eta : ℕ := 2048

/-- Sharp scalar CBD proxy `eta / 2`. -/
def scalarProxy : ℕ := eta / 2

/-- Conservative Boolean decoding distance `q / 16`. -/
def correctnessThreshold : ℕ := 2 ^ (modulusBits - 4)

/-- Sharp proxy for the fresh correction pairing. -/
def freshPairingVarianceBound : ℕ := scalarProxy * factorEnergyBound

theorem modulus_eq : modulus = 134217728 := by
  norm_num [modulus, modulusBits]

theorem suffixDimension_eq : suffixDimension = 1024 := by
  norm_num [suffixDimension, ringDegree, prefixDimension]

theorem decompositionCoverage_eq : decompositionCoverage = 26 := by
  norm_num [decompositionCoverage, brkLevels, brkBasebit]

theorem discardedBits_eq : discardedBits = 1 := by
  norm_num [discardedBits, modulusBits, decompositionCoverage,
    brkLevels, brkBasebit]

theorem brkRowCount_eq : brkRowCount = 26624 := by
  norm_num [brkRowCount, controlRowCount, ringRank, brkLevels,
    prefixDimension, TGSW.rowCount]

theorem alignedWidth_eq : alignedWidth = 54525952 := by
  norm_num [alignedWidth, brkRowCount, controlRowCount, ringRank,
    brkLevels, prefixDimension, ringDegree, TGSW.rowCount]

theorem centeredDigitRadius_eq : centeredDigitRadius = 2 := by
  norm_num [centeredDigitRadius, brkBasebit]

theorem factorEnergyBound_eq : factorEnergyBound = 218103808 := by
  norm_num [factorEnergyBound, alignedWidth, brkRowCount, controlRowCount,
    ringRank, brkLevels, prefixDimension, ringDegree,
    centeredDigitRadius, brkBasebit, TGSW.rowCount]

theorem scalarProxy_eq : scalarProxy = 1024 := by
  norm_num [scalarProxy, eta]

theorem correctnessThreshold_eq : correctnessThreshold = 8388608 := by
  norm_num [correctnessThreshold, modulusBits]

theorem freshPairingVarianceBound_eq :
    freshPairingVarianceBound = 223338299392 := by
  norm_num [freshPairingVarianceBound, scalarProxy, eta,
    factorEnergyBound, alignedWidth, brkRowCount, controlRowCount,
    ringRank, brkLevels, prefixDimension, ringDegree,
    centeredDigitRadius, brkBasebit, TGSW.rowCount]

/-- The complete integer support of CBD-2048 lies strictly inside the centered `2^27` torus. -/
theorem cbd_noWrap : 2 * eta < modulus := by
  norm_num [eta, modulus, modulusBits]

/-- Coordinatewise base-four digit bounds imply the exact factor-energy budget. -/
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

/-- The exact finite CBD sampler used for the correction vector. -/
def correctionSampler : ProbComp (Fin alignedWidth → ZMod modulus) :=
  CenteredBinomialProofErrorSampler.modularVectorSampler
    modulus alignedWidth eta

/-- The correction law is exactly the IID executable CBD coefficient law. -/
theorem correctionSampler_eq_sampleIID :
    correctionSampler =
      ProbComp.sampleIID alignedWidth
        (RLWE.CenteredBinomial.coefficientSampler modulus eta) := by
  exact CenteredBinomialProofErrorSampler.modularVectorSampler_eq_sampleIID
    modulus alignedWidth eta

/-- Exact CBD error sampler for the small degree-1024 ternary RLWE source. -/
def smallRingErrorSampler : ProbComp (RLWE.Rq modulus 1024) :=
  RLWE.CenteredBinomial.sampler modulus 1024 eta

/-- Exact finite CBD evaluator-tail certificate with sharp proxy `(eta / 2) I`. -/
theorem finiteFreshNoiseCertificate {Factor : Type}
    (residual : Factor → Fin alignedWidth → ℝ) :
    Certificate
      (CenteredBinomialProofErrorSampler.VectorCoins alignedWidth eta)
      (Fin alignedWidth) Factor
      (CenteredBinomialProofErrorSampler.vectorCoinSampler alignedWidth eta)
      (CenteredBinomialProofErrorSampler.noiseVector alignedWidth eta)
      residual
      (CenteredBinomialProofErrorSampler.sphericalCovariance alignedWidth eta) :=
  CenteredBinomialProofErrorSampler.sphericalCertificate
    alignedWidth eta residual

/-- Coordinate bounds give the advertised sharp covariance-energy budget. -/
theorem finiteSamplerCovarianceEnergy_le
    (factor : Fin alignedWidth → ℝ)
    (coordinate_bound : ∀ coordinate,
      |factor coordinate| ≤ centeredDigitRadius) :
    covarianceEnergy
        (CenteredBinomialProofErrorSampler.sphericalCovariance alignedWidth eta)
        factor ≤ freshPairingVarianceBound := by
  rw [CenteredBinomialProofErrorSampler.covarianceEnergy_spherical]
  calc
    ((eta : ℝ) / 2) * ∑ index : Fin alignedWidth, factor index ^ 2 ≤
        ((eta : ℝ) / 2) * factorEnergyBound := by
      exact mul_le_mul_of_nonneg_left
        (factorEnergy_le_bound factor coordinate_bound) (by positivity)
    _ = (freshPairingVarianceBound : ℝ) := by
      norm_num [freshPairingVarianceBound, scalarProxy, eta]

/-- Adaptive two-sided correction tail for the exact CBD tape.  The selected factor may depend
on the complete preceding public bootstrap state. -/
theorem finiteSampler_adaptiveAbsTail
    {State : Type} [Fintype State]
    (stateSampler : ProbComp State)
    (selectedFactor : State → Fin alignedWidth → ℝ)
    (coordinate_bound : ∀ state ∈ support stateSampler, ∀ coordinate,
      |selectedFactor state coordinate| ≤ centeredDigitRadius)
    (energy_pos : ∀ state ∈ support stateSampler,
      0 < Energy.factorEnergy (selectedFactor state)) :
    Pr[(fun output ↦ (correctnessThreshold : ℝ) ≤
        |dotProduct (selectedFactor output.1)
          (CenteredBinomialProofErrorSampler.noiseVector
            alignedWidth eta output.2)|) |
      TFHEppSourceAlignedParameterScreen.AdaptiveFreshNoise.independentProduct stateSampler
        (CenteredBinomialProofErrorSampler.vectorCoinSampler
          alignedWidth eta)].toReal ≤
      2 * Real.exp (-((correctnessThreshold : ℝ) ^ 2) /
        (2 * freshPairingVarianceBound)) := by
  apply TFHEppSourceAlignedParameterScreen.AdaptiveFreshNoise.Certificate.adaptiveIndependentAbsTail
    (finiteFreshNoiseCertificate
      (fun factor : Fin alignedWidth → ℝ ↦ factor))
    stateSampler selectedFactor (correctnessThreshold : ℝ)
    freshPairingVarianceBound (by positivity)
  · intro state state_mem
    rw [CenteredBinomialProofErrorSampler.covarianceEnergy_spherical]
    exact mul_pos (by norm_num [eta]) (energy_pos state state_mem)
  · intro state state_mem
    exact finiteSamplerCovarianceEnergy_le (selectedFactor state)
      (coordinate_bound state state_mem)

/-- The isolated correction term has exact Chernoff exponent `2048 / 13`. -/
theorem nominalFreshExponent_eq :
    ((correctnessThreshold : ℝ) ^ 2) /
        (2 * freshPairingVarianceBound) = 2048 / 13 := by
  norm_num [correctnessThreshold, modulusBits, freshPairingVarianceBound,
    scalarProxy, eta, factorEnergyBound, alignedWidth, brkRowCount,
    controlRowCount, ringRank, brkLevels, prefixDimension, ringDegree,
    centeredDigitRadius, brkBasebit, TGSW.rowCount]

/-- The exact two-sided Chernoff expression is strictly below `2^-226`.  This turns the
decimal/logarithmic post-processing used by the parameter script into a checked binary failure
bound. -/
theorem nominalFreshTail_lt_two_pow_neg_226 :
    2 * Real.exp (-((correctnessThreshold : ℝ) ^ 2) /
        (2 * freshPairingVarianceBound)) <
      1 / (2 : ℝ) ^ 226 := by
  have hlog : (227 : ℝ) * Real.log 2 < 2048 / 13 := by
    have h := Real.log_two_lt_d9
    nlinarith
  have hexp : (2 : ℝ) ^ 227 < Real.exp (2048 / 13) := by
    calc
      (2 : ℝ) ^ 227 = Real.exp ((227 : ℕ) * Real.log 2) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
      _ < Real.exp (2048 / 13) := Real.exp_lt_exp.mpr hlog
  have hinv :
      1 / Real.exp (2048 / 13) < 1 / (2 : ℝ) ^ 227 :=
    one_div_lt_one_div_of_lt (by positivity) hexp
  calc
    2 * Real.exp (-((correctnessThreshold : ℝ) ^ 2) /
        (2 * freshPairingVarianceBound)) =
        2 * Real.exp (-(2048 / 13)) := by
          rw [show -((correctnessThreshold : ℝ) ^ 2) /
              (2 * freshPairingVarianceBound) =
                -(((correctnessThreshold : ℝ) ^ 2) /
                  (2 * freshPairingVarianceBound)) by ring,
            nominalFreshExponent_eq]
    _ = 2 * (1 / Real.exp (2048 / 13)) := by
      rw [Real.exp_neg]
      simp only [one_div]
    _ < 2 * (1 / (2 : ℝ) ^ 227) :=
      mul_lt_mul_of_pos_left hinv (by norm_num)
    _ = 1 / (2 : ℝ) ^ 226 := by norm_num

/-- Fully instantiated adaptive failure statement: every supported transcript-dependent
base-four factor has correction failure probability below `2^-226`. -/
theorem finiteSampler_adaptiveAbsTail_lt_two_pow_neg_226
    {State : Type} [Fintype State]
    (stateSampler : ProbComp State)
    (selectedFactor : State → Fin alignedWidth → ℝ)
    (coordinate_bound : ∀ state ∈ support stateSampler, ∀ coordinate,
      |selectedFactor state coordinate| ≤ centeredDigitRadius)
    (energy_pos : ∀ state ∈ support stateSampler,
      0 < Energy.factorEnergy (selectedFactor state)) :
    Pr[(fun output ↦ (correctnessThreshold : ℝ) ≤
        |dotProduct (selectedFactor output.1)
          (CenteredBinomialProofErrorSampler.noiseVector
            alignedWidth eta output.2)|) |
      TFHEppSourceAlignedParameterScreen.AdaptiveFreshNoise.independentProduct stateSampler
        (CenteredBinomialProofErrorSampler.vectorCoinSampler
          alignedWidth eta)].toReal <
      1 / (2 : ℝ) ^ 226 :=
  lt_of_le_of_lt
    (finiteSampler_adaptiveAbsTail stateSampler selectedFactor
      coordinate_bound energy_pos)
    nominalFreshTail_lt_two_pow_neg_226

end

end FormalProof4FHE.TFHE.TFHEppCandidateLvl02CBDParameterScreen
