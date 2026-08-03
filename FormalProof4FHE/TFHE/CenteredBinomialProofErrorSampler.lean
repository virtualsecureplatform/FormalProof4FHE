/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SourceAlignedProofErrorSampler

/-!
# Sharp finite MGF certificate for centered-binomial proof errors

This file turns the executable centered-binomial coin tape into the finite subgaussian
certificate consumed by the source-aligned evaluator theorem.  A width-`eta` coefficient has
the sharp proxy `eta / 2`; an IID vector therefore has spherical proxy `(eta / 2) I`.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.CenteredBinomialProofErrorSampler

noncomputable section

open FormalProof4FHE.BoundedMoment
open SourceAlignedBRKKSKJointLaw.NativeCompiler.EvaluatorTail

/-- Uniform bit-pair tape for one centered-binomial coefficient. -/
abbrev ScalarCoins (eta : ℕ) := RLWE.CenteredBinomial.CoinRow eta

/-- Exact finite sampler for one unreduced centered-binomial coefficient. -/
def scalarCoinSampler (eta : ℕ) : ProbComp (ScalarCoins eta) :=
  $ᵗ (ScalarCoins eta)

/-- Signed real decoder of one coefficient tape. -/
def decodeReal {eta : ℕ} (coins : ScalarCoins eta) : ℝ :=
  RLWE.CenteredBinomial.signedWeightReal coins

/-- The signed Hamming-weight difference is the unit-weighted sum of all bit-pair
differences. -/
theorem decodeReal_eq_weightedSum {eta : ℕ} (coins : ScalarCoins eta) :
    decodeReal coins =
      weightedSum (fun _ : Fin eta ↦ (1 : ℝ))
        RLWE.CenteredBinomial.pairDifferenceReal coins := by
  induction eta with
  | zero =>
      simp [decodeReal, RLWE.CenteredBinomial.signedWeightReal,
        RLWE.CenteredBinomial.signedWeight,
        RLWE.CenteredBinomial.positiveWeight,
        RLWE.CenteredBinomial.negativeWeight, weightedSum]
  | succ eta inductionHypothesis =>
      calc
        decodeReal coins =
            decodeReal (Fin.cons (coins 0) (Fin.tail coins)) := by
              rw [Fin.cons_self_tail]
        _ = RLWE.CenteredBinomial.pairDifferenceReal (coins 0) +
              decodeReal (Fin.tail coins) := by
                exact RLWE.CenteredBinomial.signedWeightReal_cons
                  (coins 0) (Fin.tail coins)
        _ = (1 : ℝ) * RLWE.CenteredBinomial.pairDifferenceReal (coins 0) +
              weightedSum (fun _ : Fin eta ↦ (1 : ℝ))
                RLWE.CenteredBinomial.pairDifferenceReal (Fin.tail coins) := by
                  rw [inductionHypothesis]
                  ring
        _ = weightedSum (fun _ : Fin (eta + 1) ↦ (1 : ℝ))
              RLWE.CenteredBinomial.pairDifferenceReal
              (Fin.cons (coins 0) (Fin.tail coins)) := by
                rw [weightedSum_cons]
        _ = weightedSum (fun _ : Fin (eta + 1) ↦ (1 : ℝ))
              RLWE.CenteredBinomial.pairDifferenceReal coins := by
                rw [Fin.cons_self_tail]

/-- **Sharp centered-binomial MGF.**  A width-`eta` coefficient is subgaussian with variance
proxy exactly `eta / 2`. -/
theorem expectation_exp_decodeReal_le (eta : ℕ) (rate : ℝ) :
    expectation (scalarCoinSampler eta)
        (fun coins ↦ Real.exp (rate * decodeReal coins)) ≤
      Real.exp (rate ^ 2 * ((eta : ℝ) / 2) / 2) := by
  have hIID := SourceAlignedProofErrorSampler.expectation_exp_weightedSum_le
    ($ᵗ (Bool × Bool)) RLWE.CenteredBinomial.pairDifferenceReal (1 / 2 : ℝ)
    (by
      intro scalarRate
      calc
        expectation ($ᵗ (Bool × Bool))
            (fun coin ↦ Real.exp
              (scalarRate * RLWE.CenteredBinomial.pairDifferenceReal coin)) ≤
            Real.exp (scalarRate ^ 2 / 4) :=
          SourceAlignedProofErrorSampler.expectation_exp_pairDifference_le_sharp
            scalarRate
        _ = Real.exp (scalarRate ^ 2 * (1 / 2 : ℝ) / 2) := by
          congr 1
          ring)
    eta (fun _ : Fin eta ↦ (1 : ℝ)) rate
  have hDist := FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
    (alpha := Bool × Bool) eta
  calc
    expectation (scalarCoinSampler eta)
        (fun coins ↦ Real.exp (rate * decodeReal coins)) =
      expectation (scalarCoinSampler eta)
        (fun coins ↦ Real.exp
          (rate * weightedSum (fun _ : Fin eta ↦ (1 : ℝ))
            RLWE.CenteredBinomial.pairDifferenceReal coins)) := by
              apply congrArg (expectation (scalarCoinSampler eta))
              funext coins
              rw [decodeReal_eq_weightedSum]
    _ = expectation
        (ProbComp.sampleIID eta ($ᵗ (Bool × Bool)))
        (fun coins ↦ Real.exp
          (rate * weightedSum (fun _ : Fin eta ↦ (1 : ℝ))
            RLWE.CenteredBinomial.pairDifferenceReal coins)) := by
              exact (expectation_congr_evalDist hDist _).symm
    _ ≤ Real.exp (rate ^ 2 * ((eta : ℝ) / 2) / 2) := by
      have hsum :
          (∑ _index : Fin eta, (1 : ℝ) ^ 2) = (eta : ℝ) := by simp
      rw [hsum] at hIID
      calc
        expectation (ProbComp.sampleIID eta ($ᵗ (Bool × Bool)))
            (fun coins ↦ Real.exp
              (rate * weightedSum (fun _ : Fin eta ↦ (1 : ℝ))
                RLWE.CenteredBinomial.pairDifferenceReal coins)) ≤
            Real.exp (rate ^ 2 * ((1 / 2 : ℝ) * (eta : ℝ)) / 2) := hIID
        _ = Real.exp (rate ^ 2 * ((eta : ℝ) / 2) / 2) := by
          congr 1
          ring

/-! ## IID vector certificate -/

/-- Complete independent CBD coin tape for a correction vector. -/
abbrev VectorCoins (count eta : ℕ) := Fin count → ScalarCoins eta

/-- Coordinatewise IID finite CBD sampler. -/
def vectorCoinSampler (count eta : ℕ) : ProbComp (VectorCoins count eta) :=
  ProbComp.sampleIID count (scalarCoinSampler eta)

/-- Real vector decoded from a complete CBD tape. -/
def noiseVector (count eta : ℕ) (coins : VectorCoins count eta) : Fin count → ℝ :=
  fun index ↦ decodeReal (coins index)

/-- Coordinatewise modular decoding of the same finite CBD tape. -/
def modularVector (q count eta : ℕ) (coins : VectorCoins count eta) :
    Fin count → ZMod q :=
  fun index ↦ (RLWE.CenteredBinomial.signedWeight (coins index) : ZMod q)

/-- Executable modular correction sampler backed by the exact tape used in the MGF proof. -/
def modularVectorSampler (q count eta : ℕ) [NeZero q] :
    ProbComp (Fin count → ZMod q) :=
  modularVector q count eta <$> vectorCoinSampler count eta

/-- The tape-level modular sampler is exactly the IID executable centered-binomial coefficient
sampler, not merely moment matched to it. -/
theorem modularVectorSampler_eq_sampleIID
    (q count eta : ℕ) [NeZero q] :
    modularVectorSampler q count eta =
      ProbComp.sampleIID count (RLWE.CenteredBinomial.coefficientSampler q eta) := by
  unfold modularVectorSampler modularVector vectorCoinSampler scalarCoinSampler
    ProbComp.sampleIID RLWE.CenteredBinomial.coefficientSampler
  exact FormalProof4FHE.FiniteProduct.map_fin_mOfFn_const count
    ($ᵗ (RLWE.CenteredBinomial.CoinRow eta))
    (fun coins ↦ (RLWE.CenteredBinomial.signedWeight coins : ZMod q))

/-- Sharp spherical covariance proxy `(eta / 2) I`. -/
def sphericalCovariance (count eta : ℕ) : Matrix (Fin count) (Fin count) ℝ :=
  ((eta : ℝ) / 2) • (1 : Matrix (Fin count) (Fin count) ℝ)

/-- Energy normal form for the sharp CBD covariance proxy. -/
theorem covarianceEnergy_spherical (count eta : ℕ)
    (factor : Fin count → ℝ) :
    covarianceEnergy (sphericalCovariance count eta) factor =
      ((eta : ℝ) / 2) * ∑ index : Fin count, factor index ^ 2 := by
  unfold covarianceEnergy sphericalCovariance
  rw [Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_smul]
  simp [dotProduct, pow_two, Finset.mul_sum]

/-- Every real linear functional of the decoded IID CBD vector has the sharp spherical MGF
bound. -/
theorem expectation_exp_dotProduct_noiseVector_le
    (count eta : ℕ) (factor : Fin count → ℝ) (rate : ℝ) :
    expectation (vectorCoinSampler count eta)
        (fun coins ↦ Real.exp
          (rate * dotProduct factor (noiseVector count eta coins))) ≤
      Real.exp
        (rate ^ 2 *
          covarianceEnergy (sphericalCovariance count eta) factor / 2) := by
  have hMGF := SourceAlignedProofErrorSampler.expectation_exp_weightedSum_le
    (scalarCoinSampler eta) decodeReal ((eta : ℝ) / 2)
      (expectation_exp_decodeReal_le eta) count factor rate
  rw [covarianceEnergy_spherical]
  simpa [vectorCoinSampler, noiseVector, weightedSum, dotProduct] using hMGF

/-- Concrete finite evaluator-tail certificate for exact CBD correction noise. -/
theorem sphericalCertificate (count eta : ℕ) {Factor : Type}
    (residual : Factor → Fin count → ℝ) :
    Certificate
      (VectorCoins count eta) (Fin count) Factor
      (vectorCoinSampler count eta) (noiseVector count eta) residual
      (sphericalCovariance count eta) := by
  constructor
  · intro factor
    rw [covarianceEnergy_spherical]
    exact mul_nonneg (by positivity) (Finset.sum_nonneg fun index _ ↦
      sq_nonneg (residual factor index))
  · intro factor rate
    exact expectation_exp_dotProduct_noiseVector_le
      count eta (residual factor) rate

end

end FormalProof4FHE.TFHE.CenteredBinomialProofErrorSampler
