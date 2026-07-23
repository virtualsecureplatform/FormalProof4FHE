/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AsymptoticKeySwitchFirstUniversalCircular
import FormalProof4FHE.TFHE.CenteredBinomialGrowingNoiseEndToEnd
import FormalProof4FHE.TFHE.NativeCoupledShiftedResidualBounds

/-!
# Asymptotic Native Shifted Discrete-Gaussian Bounds

The finite native shifted-evaluator analysis bounds the coupled correct-side statistical loss by

`layout * degree * (2 * compilerError + residual * exp(1 / 2) / (window + 1))`.

This module performs the missing asymptotic accounting.  It proves that polynomial BRK layout,
ring degree, and centered-binomial residual growth are absorbed by

* negligible finite-ticket compiler error; and
* an exponentially growing checked Gaussian window.

The exponential-window hypothesis is intentional and visible.  A merely polynomial Gaussian
width gives only inverse-polynomial unit-translation distance and therefore cannot establish the
cryptographic negligibility required by the reduction.
-/

open ENNReal OracleComp

namespace FormalProof4FHE.TFHE.Native.ShiftedDiscreteGaussian.Asymptotic

open FormalProof4FHE.TFHE
open FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery.AugmentedResidual.NativeShifted

noncomputable section

/-! ## Polynomial construction growth -/

/-- Polynomial bounds for every construction component occurring in the coupled correct-side
smudging expression. -/
structure PolynomialGrowth
    {q : ℕ → ℕ} [∀ securityParameter, NeZero (q securityParameter)]
    (gadgetParams : (securityParameter : ℕ) →
      Gadget.Base.Parameters (q securityParameter))
    (degree ringRank lweDimension eta : ℕ → ℕ) where
  degreePolynomial : Polynomial ℕ
  ringRankPolynomial : Polynomial ℕ
  lweDimensionPolynomial : Polynomial ℕ
  levelsPolynomial : Polynomial ℕ
  basePolynomial : Polynomial ℕ
  etaPolynomial : Polynomial ℕ
  degree_le : ∀ securityParameter,
    degree securityParameter ≤ degreePolynomial.eval securityParameter
  ringRank_le : ∀ securityParameter,
    ringRank securityParameter ≤ ringRankPolynomial.eval securityParameter
  lweDimension_le : ∀ securityParameter,
    lweDimension securityParameter ≤ lweDimensionPolynomial.eval securityParameter
  levels_le : ∀ securityParameter,
    (gadgetParams securityParameter).levels ≤ levelsPolynomial.eval securityParameter
  base_le : ∀ securityParameter,
    (gadgetParams securityParameter).base ≤ basePolynomial.eval securityParameter
  eta_le : ∀ securityParameter,
    eta securityParameter ≤ etaPolynomial.eval securityParameter

/-- Polynomial upper bound for the number of BRK ring-error rows. -/
def PolynomialGrowth.layoutPolynomial
    {q : ℕ → ℕ} [∀ securityParameter, NeZero (q securityParameter)]
    {gadgetParams : (securityParameter : ℕ) →
      Gadget.Base.Parameters (q securityParameter)}
    {degree ringRank lweDimension eta : ℕ → ℕ}
    (growth : PolynomialGrowth gadgetParams degree ringRank lweDimension eta) :
    Polynomial ℕ :=
  growth.lweDimensionPolynomial *
    ((growth.ringRankPolynomial + 1) * growth.levelsPolynomial)

/-- Polynomial upper bound for the deterministic centered-binomial residual budget. -/
def PolynomialGrowth.residualPolynomial
    {q : ℕ → ℕ} [∀ securityParameter, NeZero (q securityParameter)]
    {gadgetParams : (securityParameter : ℕ) →
      Gadget.Base.Parameters (q securityParameter)}
    {degree ringRank lweDimension eta : ℕ → ℕ}
    (growth : PolynomialGrowth gadgetParams degree ringRank lweDimension eta) :
    Polynomial ℕ :=
  growth.etaPolynomial +
    ((growth.ringRankPolynomial + 1) * growth.levelsPolynomial) *
      ((growth.degreePolynomial * growth.degreePolynomial) *
        (growth.basePolynomial * growth.etaPolynomial))

/-- Polynomial upper bound multiplying the certificate error. -/
def PolynomialGrowth.certificatePolynomial
    {q : ℕ → ℕ} [∀ securityParameter, NeZero (q securityParameter)]
    {gadgetParams : (securityParameter : ℕ) →
      Gadget.Base.Parameters (q securityParameter)}
    {degree ringRank lweDimension eta : ℕ → ℕ}
    (growth : PolynomialGrowth gadgetParams degree ringRank lweDimension eta) :
    Polynomial ℕ :=
  growth.layoutPolynomial * growth.degreePolynomial

/-- Polynomial upper bound multiplying the inverse Gaussian window. -/
def PolynomialGrowth.windowPolynomial
    {q : ℕ → ℕ} [∀ securityParameter, NeZero (q securityParameter)]
    {gadgetParams : (securityParameter : ℕ) →
      Gadget.Base.Parameters (q securityParameter)}
    {degree ringRank lweDimension eta : ℕ → ℕ}
    (growth : PolynomialGrowth gadgetParams degree ringRank lweDimension eta) :
    Polynomial ℕ :=
  growth.certificatePolynomial * growth.residualPolynomial

theorem PolynomialGrowth.layoutCount_le_polynomial
    {q : ℕ → ℕ} [∀ securityParameter, NeZero (q securityParameter)]
    {gadgetParams : (securityParameter : ℕ) →
      Gadget.Base.Parameters (q securityParameter)}
    {degree ringRank lweDimension eta : ℕ → ℕ}
    (growth : PolynomialGrowth gadgetParams degree ringRank lweDimension eta)
    (securityParameter : ℕ) :
    lweDimension securityParameter *
        TGSW.rowCount (ringRank securityParameter)
          (gadgetParams securityParameter).levels ≤
      growth.layoutPolynomial.eval securityParameter := by
  simp only [TGSW.rowCount, PolynomialGrowth.layoutPolynomial,
    Polynomial.eval_mul, Polynomial.eval_add, Polynomial.eval_one]
  exact Nat.mul_le_mul
    (growth.lweDimension_le securityParameter)
    (Nat.mul_le_mul
      (Nat.add_le_add (growth.ringRank_le securityParameter) le_rfl)
      (growth.levels_le securityParameter))

theorem PolynomialGrowth.centeredBinomialResidualBound_le_polynomial
    {q : ℕ → ℕ} [∀ securityParameter, NeZero (q securityParameter)]
    {gadgetParams : (securityParameter : ℕ) →
      Gadget.Base.Parameters (q securityParameter)}
    {degree ringRank lweDimension eta : ℕ → ℕ}
    (growth : PolynomialGrowth gadgetParams degree ringRank lweDimension eta)
    (securityParameter : ℕ) :
    Native.ShiftedResidualBounds.centeredBinomialResidualBound
        (gadgetParams securityParameter) (degree securityParameter)
        (ringRank securityParameter) (eta securityParameter) ≤
      growth.residualPolynomial.eval securityParameter := by
  simp only [Native.ShiftedResidualBounds.centeredBinomialResidualBound,
    Native.ShiftedResidualBounds.correctResidualBound,
    PolynomialGrowth.residualPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_one]
  exact Nat.add_le_add
    (growth.eta_le securityParameter)
    (Nat.mul_le_mul
      (Nat.mul_le_mul
        (Nat.add_le_add (growth.ringRank_le securityParameter) le_rfl)
        (growth.levels_le securityParameter))
      (Nat.mul_le_mul
        (Nat.mul_le_mul
          (growth.degree_le securityParameter)
          (growth.degree_le securityParameter))
        (Nat.mul_le_mul
          ((Nat.sub_le _ _).trans (growth.base_le securityParameter))
          (growth.eta_le securityParameter))))

/-! ## ENNReal accounting -/

/-- The coupled correct-side error, lifted to the asymptotic security codomain. -/
noncomputable def correctSmudgingError
    {q : ℕ → ℕ} [∀ securityParameter, NeZero (q securityParameter)]
    (gadgetParams : (securityParameter : ℕ) →
      Gadget.Base.Parameters (q securityParameter))
    (alpha : ℕ → ℝ) (halpha : ∀ securityParameter, 0 < alpha securityParameter)
    (certificate : (securityParameter : ℕ) →
      DiscreteGaussianSampler.ScalarCertificate
        (q securityParameter) (alpha securityParameter) (halpha securityParameter))
    (degree ringRank lweDimension eta : ℕ → ℕ) : ℕ → ℝ≥0∞ :=
  fun securityParameter ↦ ENNReal.ofReal
    (coupledCenteredBinomialDiscreteGaussianLinearSmudgingError
      (gadgetParams securityParameter) (certificate securityParameter)
      (degree securityParameter) (ringRank securityParameter)
      (lweDimension securityParameter) (eta securityParameter))

/-- Finite-window real upper bound from the exact modular-Gaussian calculation. -/
noncomputable def finiteWindowUpperBound
    {q : ℕ → ℕ} [∀ securityParameter, NeZero (q securityParameter)]
    (gadgetParams : (securityParameter : ℕ) →
      Gadget.Base.Parameters (q securityParameter))
    (alpha : ℕ → ℝ) (halpha : ∀ securityParameter, 0 < alpha securityParameter)
    (certificate : (securityParameter : ℕ) →
      DiscreteGaussianSampler.ScalarCertificate
        (q securityParameter) (alpha securityParameter) (halpha securityParameter))
    (degree ringRank lweDimension eta window : ℕ → ℕ)
    (securityParameter : ℕ) : ℝ :=
  ((lweDimension securityParameter *
      TGSW.rowCount (ringRank securityParameter)
        (gadgetParams securityParameter).levels : ℕ) : ℝ) *
    ((degree securityParameter : ℝ) *
      (2 * (certificate securityParameter).bound.toReal +
        (Native.ShiftedResidualBounds.centeredBinomialResidualBound
          (gadgetParams securityParameter) (degree securityParameter)
          (ringRank securityParameter) (eta securityParameter) : ℝ) *
          (Real.exp (1 / 2 : ℝ) /
            (window securityParameter + 1 : ℕ))))

theorem correctSmudgingError_le_finiteWindowUpperBound
    {q : ℕ → ℕ} [∀ securityParameter, NeZero (q securityParameter)]
    (gadgetParams : (securityParameter : ℕ) →
      Gadget.Base.Parameters (q securityParameter))
    (alpha : ℕ → ℝ) (halpha : ∀ securityParameter, 0 < alpha securityParameter)
    (certificate : (securityParameter : ℕ) →
      DiscreteGaussianSampler.ScalarCertificate
        (q securityParameter) (alpha securityParameter) (halpha securityParameter))
    (degree ringRank lweDimension eta window : ℕ → ℕ)
    (hwindow : ∀ securityParameter,
      (window securityParameter : ℝ) ≤
        ModularGaussian.integerStddev
          (q securityParameter) (alpha securityParameter))
    (securityParameter : ℕ) :
    correctSmudgingError gadgetParams alpha halpha certificate
        degree ringRank lweDimension eta securityParameter ≤
      ENNReal.ofReal
        (finiteWindowUpperBound gadgetParams alpha halpha certificate
          degree ringRank lweDimension eta window securityParameter) := by
  apply ENNReal.ofReal_le_ofReal
  exact coupledCenteredBinomialDiscreteGaussianLinearSmudgingError_le_exp_half_window
    (gadgetParams securityParameter) (certificate securityParameter)
    (degree securityParameter) (ringRank securityParameter)
    (lweDimension securityParameter) (eta securityParameter)
    (window securityParameter) (hwindow securityParameter)

/-- Expanded `ENNReal` form of the finite-window expression. -/
theorem ofReal_finiteWindowUpperBound_eq
    {q : ℕ → ℕ} [∀ securityParameter, NeZero (q securityParameter)]
    (gadgetParams : (securityParameter : ℕ) →
      Gadget.Base.Parameters (q securityParameter))
    (alpha : ℕ → ℝ) (halpha : ∀ securityParameter, 0 < alpha securityParameter)
    (certificate : (securityParameter : ℕ) →
      DiscreteGaussianSampler.ScalarCertificate
        (q securityParameter) (alpha securityParameter) (halpha securityParameter))
    (degree ringRank lweDimension eta window : ℕ → ℕ)
    (securityParameter : ℕ) :
    ENNReal.ofReal
        (finiteWindowUpperBound gadgetParams alpha halpha certificate
          degree ringRank lweDimension eta window securityParameter) =
      (lweDimension securityParameter *
          TGSW.rowCount (ringRank securityParameter)
            (gadgetParams securityParameter).levels : ℕ) *
        (degree securityParameter : ℝ≥0∞) *
          (2 * (certificate securityParameter).bound +
            (Native.ShiftedResidualBounds.centeredBinomialResidualBound
              (gadgetParams securityParameter) (degree securityParameter)
              (ringRank securityParameter) (eta securityParameter) : ℕ) *
              ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
              ((window securityParameter + 1 : ℕ) : ℝ≥0∞)⁻¹) := by
  unfold finiteWindowUpperBound
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_add (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)
      (mul_nonneg (Nat.cast_nonneg _)
        (div_nonneg (le_of_lt (Real.exp_pos _)) (Nat.cast_nonneg _))),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_toReal (certificate securityParameter).bound_ne_top,
    ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) <
      (window securityParameter + 1 : ℕ))]
  norm_cast
  rw [div_eq_mul_inv]
  push_cast
  ring

/-- Polynomial envelope separating compiler and Gaussian-window contributions. -/
noncomputable def polynomialEnvelope
    {q : ℕ → ℕ} [∀ securityParameter, NeZero (q securityParameter)]
    {gadgetParams : (securityParameter : ℕ) →
      Gadget.Base.Parameters (q securityParameter)}
    {degree ringRank lweDimension eta : ℕ → ℕ}
    (growth : PolynomialGrowth gadgetParams degree ringRank lweDimension eta)
    {alpha : ℕ → ℝ} {halpha : ∀ securityParameter, 0 < alpha securityParameter}
    (certificate : (securityParameter : ℕ) →
      DiscreteGaussianSampler.ScalarCertificate
        (q securityParameter) (alpha securityParameter) (halpha securityParameter))
    (window : ℕ → ℕ) (securityParameter : ℕ) : ℝ≥0∞ :=
  2 * (growth.certificatePolynomial.eval securityParameter : ℕ) *
      (certificate securityParameter).bound +
    ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
      (growth.windowPolynomial.eval securityParameter : ℕ) *
      ((window securityParameter + 1 : ℕ) : ℝ≥0∞)⁻¹

theorem ofReal_finiteWindowUpperBound_le_polynomialEnvelope
    {q : ℕ → ℕ} [∀ securityParameter, NeZero (q securityParameter)]
    {gadgetParams : (securityParameter : ℕ) →
      Gadget.Base.Parameters (q securityParameter)}
    {degree ringRank lweDimension eta : ℕ → ℕ}
    (growth : PolynomialGrowth gadgetParams degree ringRank lweDimension eta)
    (alpha : ℕ → ℝ) (halpha : ∀ securityParameter, 0 < alpha securityParameter)
    (certificate : (securityParameter : ℕ) →
      DiscreteGaussianSampler.ScalarCertificate
        (q securityParameter) (alpha securityParameter) (halpha securityParameter))
    (window : ℕ → ℕ) (securityParameter : ℕ) :
    ENNReal.ofReal
        (finiteWindowUpperBound gadgetParams alpha halpha certificate
          degree ringRank lweDimension eta window securityParameter) ≤
      polynomialEnvelope growth certificate window securityParameter := by
  rw [ofReal_finiteWindowUpperBound_eq]
  unfold polynomialEnvelope
  have hlayout := growth.layoutCount_le_polynomial securityParameter
  have hdegree := growth.degree_le securityParameter
  have hresidual :=
    growth.centeredBinomialResidualBound_le_polynomial securityParameter
  simp only [PolynomialGrowth.certificatePolynomial,
    PolynomialGrowth.windowPolynomial, Polynomial.eval_mul]
  have hlayout' :
      (lweDimension securityParameter *
          TGSW.rowCount (ringRank securityParameter)
            (gadgetParams securityParameter).levels : ℕ) ≤
        (growth.layoutPolynomial.eval securityParameter : ℕ) := by
    exact_mod_cast hlayout
  have hdegree' : (degree securityParameter : ℝ≥0∞) ≤
      (growth.degreePolynomial.eval securityParameter : ℕ) := by
    exact_mod_cast hdegree
  have hresidual' :
      (Native.ShiftedResidualBounds.centeredBinomialResidualBound
        (gadgetParams securityParameter) (degree securityParameter)
        (ringRank securityParameter) (eta securityParameter) : ℕ) ≤
      (growth.residualPolynomial.eval securityParameter : ℕ) := by
    exact_mod_cast hresidual
  calc
    _ = 2 *
          ((lweDimension securityParameter *
              TGSW.rowCount (ringRank securityParameter)
                (gadgetParams securityParameter).levels : ℕ) *
            (degree securityParameter : ℝ≥0∞)) *
          (certificate securityParameter).bound +
        ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
          (((lweDimension securityParameter *
                TGSW.rowCount (ringRank securityParameter)
                  (gadgetParams securityParameter).levels : ℕ) *
              (degree securityParameter : ℝ≥0∞)) *
            (Native.ShiftedResidualBounds.centeredBinomialResidualBound
              (gadgetParams securityParameter) (degree securityParameter)
              (ringRank securityParameter) (eta securityParameter) : ℕ)) *
          ((window securityParameter + 1 : ℕ) : ℝ≥0∞)⁻¹ := by ring
    _ ≤ 2 *
          ((growth.layoutPolynomial.eval securityParameter : ℕ) *
            (growth.degreePolynomial.eval securityParameter : ℕ)) *
          (certificate securityParameter).bound +
        ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
          (((growth.layoutPolynomial.eval securityParameter : ℕ) *
              (growth.degreePolynomial.eval securityParameter : ℕ)) *
            (growth.residualPolynomial.eval securityParameter : ℕ)) *
          ((window securityParameter + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
      gcongr
    _ = _ := by
      push_cast
      ring

theorem polynomialEnvelope_negligible
    {q : ℕ → ℕ} [∀ securityParameter, NeZero (q securityParameter)]
    {gadgetParams : (securityParameter : ℕ) →
      Gadget.Base.Parameters (q securityParameter)}
    {degree ringRank lweDimension eta : ℕ → ℕ}
    (growth : PolynomialGrowth gadgetParams degree ringRank lweDimension eta)
    {alpha : ℕ → ℝ} {halpha : ∀ securityParameter, 0 < alpha securityParameter}
    (certificate : (securityParameter : ℕ) →
      DiscreteGaussianSampler.ScalarCertificate
        (q securityParameter) (alpha securityParameter) (halpha securityParameter))
    (window : ℕ → ℕ)
    (hcertificate : negligible (fun securityParameter ↦
      (certificate securityParameter).bound))
    (hwindow : negligible (fun securityParameter ↦
      ((window securityParameter + 1 : ℕ) : ℝ≥0∞)⁻¹)) :
    negligible (polynomialEnvelope growth certificate window) := by
  apply negligible_add
  · simpa only [polynomialEnvelope, Pi.add_apply, mul_assoc] using
      negligible_const_mul
        (negligible_polynomial_mul hcertificate growth.certificatePolynomial)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  · simpa only [polynomialEnvelope, Pi.add_apply, mul_assoc] using
      negligible_const_mul
        (negligible_polynomial_mul hwindow growth.windowPolynomial)
        (ENNReal.ofReal_ne_top)

/-- Polynomial construction growth plus negligible compiler error and inverse window makes the
complete coupled correct-side statistical loss negligible. -/
theorem correctSmudgingError_negligible
    {q : ℕ → ℕ} [∀ securityParameter, NeZero (q securityParameter)]
    {gadgetParams : (securityParameter : ℕ) →
      Gadget.Base.Parameters (q securityParameter)}
    {degree ringRank lweDimension eta : ℕ → ℕ}
    (growth : PolynomialGrowth gadgetParams degree ringRank lweDimension eta)
    (alpha : ℕ → ℝ) (halpha : ∀ securityParameter, 0 < alpha securityParameter)
    (certificate : (securityParameter : ℕ) →
      DiscreteGaussianSampler.ScalarCertificate
        (q securityParameter) (alpha securityParameter) (halpha securityParameter))
    (window : ℕ → ℕ)
    (hwindowFits : ∀ securityParameter,
      (window securityParameter : ℝ) ≤
        ModularGaussian.integerStddev
          (q securityParameter) (alpha securityParameter))
    (hcertificate : negligible (fun securityParameter ↦
      (certificate securityParameter).bound))
    (hwindow : negligible (fun securityParameter ↦
      ((window securityParameter + 1 : ℕ) : ℝ≥0∞)⁻¹)) :
    negligible (correctSmudgingError gadgetParams alpha halpha certificate
      degree ringRank lweDimension eta) := by
  apply negligible_of_le (g := polynomialEnvelope growth certificate window)
  · intro securityParameter
    exact (correctSmudgingError_le_finiteWindowUpperBound
      gadgetParams alpha halpha certificate degree ringRank lweDimension eta window
      hwindowFits securityParameter).trans
        (ofReal_finiteWindowUpperBound_le_polynomialEnvelope
          growth alpha halpha certificate window securityParameter)
  · exact polynomialEnvelope_negligible growth certificate window
      hcertificate hwindow

/-! ## Explicit exponential window -/

/-- The inverse of `window + 1` is negligible whenever that denominator dominates `2^λ`. -/
theorem inverseWindow_negligible_of_two_pow_le
    (window : ℕ → ℕ)
    (hwindow : ∀ securityParameter,
      2 ^ securityParameter ≤ window securityParameter + 1) :
    negligible (fun securityParameter ↦
      ((window securityParameter + 1 : ℕ) : ℝ≥0∞)⁻¹) := by
  apply negligible_of_le (g := fun securityParameter ↦
    ((2 : ℝ≥0∞) ^ securityParameter)⁻¹)
  · intro securityParameter
    rw [ENNReal.inv_le_inv]
    exact_mod_cast hwindow securityParameter
  · exact Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView.negligible_inv_two_pow

/-- Main explicit endpoint: a checked `2^λ` Gaussian window absorbs every polynomial native
layout and residual factor. -/
theorem correctSmudgingError_negligible_of_two_pow_window
    {q : ℕ → ℕ} [∀ securityParameter, NeZero (q securityParameter)]
    {gadgetParams : (securityParameter : ℕ) →
      Gadget.Base.Parameters (q securityParameter)}
    {degree ringRank lweDimension eta : ℕ → ℕ}
    (growth : PolynomialGrowth gadgetParams degree ringRank lweDimension eta)
    (alpha : ℕ → ℝ) (halpha : ∀ securityParameter, 0 < alpha securityParameter)
    (certificate : (securityParameter : ℕ) →
      DiscreteGaussianSampler.ScalarCertificate
        (q securityParameter) (alpha securityParameter) (halpha securityParameter))
    (hwindowFits : ∀ securityParameter,
      ((2 ^ securityParameter : ℕ) : ℝ) ≤
        ModularGaussian.integerStddev
          (q securityParameter) (alpha securityParameter))
    (hcertificate : negligible (fun securityParameter ↦
      (certificate securityParameter).bound)) :
    negligible (correctSmudgingError gadgetParams alpha halpha certificate
      degree ringRank lweDimension eta) := by
  apply correctSmudgingError_negligible growth alpha halpha certificate
    (fun securityParameter ↦ 2 ^ securityParameter) hwindowFits hcertificate
  apply inverseWindow_negligible_of_two_pow_le
  intro securityParameter
  omega

/-- A negligible output-normal-form error composes with the now-proved negligible smudging
error.  This is the correct-side error shape installed by the direct statistical certificate. -/
theorem candidateCorrectError_negligible_of_two_pow_window
    {q : ℕ → ℕ} [∀ securityParameter, NeZero (q securityParameter)]
    {gadgetParams : (securityParameter : ℕ) →
      Gadget.Base.Parameters (q securityParameter)}
    {degree ringRank lweDimension eta : ℕ → ℕ}
    (growth : PolynomialGrowth gadgetParams degree ringRank lweDimension eta)
    (alpha : ℕ → ℝ) (halpha : ∀ securityParameter, 0 < alpha securityParameter)
    (certificate : (securityParameter : ℕ) →
      DiscreteGaussianSampler.ScalarCertificate
        (q securityParameter) (alpha securityParameter) (halpha securityParameter))
    (normalFormError : ℕ → ℝ≥0∞)
    (hwindowFits : ∀ securityParameter,
      ((2 ^ securityParameter : ℕ) : ℝ) ≤
        ModularGaussian.integerStddev
          (q securityParameter) (alpha securityParameter))
    (hcertificate : negligible (fun securityParameter ↦
      (certificate securityParameter).bound))
    (hnormalForm : negligible normalFormError) :
    negligible (fun securityParameter ↦
      normalFormError securityParameter +
        correctSmudgingError gadgetParams alpha halpha certificate
          degree ringRank lweDimension eta securityParameter) :=
  negligible_add hnormalForm
    (correctSmudgingError_negligible_of_two_pow_window
      growth alpha halpha certificate hwindowFits hcertificate)

/-- Polynomially many uses of the complete correct-side certificate still have negligible total
loss. -/
theorem polynomiallyManyCandidateCorrectErrors_negligible_of_two_pow_window
    {q : ℕ → ℕ} [∀ securityParameter, NeZero (q securityParameter)]
    {gadgetParams : (securityParameter : ℕ) →
      Gadget.Base.Parameters (q securityParameter)}
    {degree ringRank lweDimension eta : ℕ → ℕ}
    (growth : PolynomialGrowth gadgetParams degree ringRank lweDimension eta)
    (alpha : ℕ → ℝ) (halpha : ∀ securityParameter, 0 < alpha securityParameter)
    (certificate : (securityParameter : ℕ) →
      DiscreteGaussianSampler.ScalarCertificate
        (q securityParameter) (alpha securityParameter) (halpha securityParameter))
    (normalFormError : ℕ → ℝ≥0∞) (usePolynomial : Polynomial ℕ)
    (hwindowFits : ∀ securityParameter,
      ((2 ^ securityParameter : ℕ) : ℝ) ≤
        ModularGaussian.integerStddev
          (q securityParameter) (alpha securityParameter))
    (hcertificate : negligible (fun securityParameter ↦
      (certificate securityParameter).bound))
    (hnormalForm : negligible normalFormError) :
    negligible (fun securityParameter ↦
      (usePolynomial.eval securityParameter : ℕ) *
        (normalFormError securityParameter +
          correctSmudgingError gadgetParams alpha halpha certificate
            degree ringRank lweDimension eta securityParameter)) :=
  negligible_polynomial_mul
    (candidateCorrectError_negligible_of_two_pow_window
      growth alpha halpha certificate normalFormError hwindowFits
      hcertificate hnormalForm)
    usePolynomial

/-! ## Concrete growing centered-binomial dimensions -/

namespace GrowingNoise

open CenteredBinomial.GrowingNoiseEndToEnd

/-- The checked growing centered-binomial construction has polynomial layout, gadget, and
residual growth. -/
def polynomialGrowth : PolynomialGrowth decomposition ringDegree
    (fun _ ↦ 1) ringDegree errorWidth where
  degreePolynomial := 16 * (Polynomial.X + 1)
  ringRankPolynomial := 1
  lweDimensionPolynomial := 16 * (Polynomial.X + 1)
  levelsPolynomial := 6
  basePolynomial := 2 * (16 * (Polynomial.X + 1))
  etaPolynomial := Polynomial.X + 1
  degree_le := by
    intro securityParameter
    simpa [errorWidth] using
      ringDegree_le_sixteen_mul_errorWidth securityParameter
  ringRank_le := by intro securityParameter; simp
  lweDimension_le := by
    intro securityParameter
    simpa [errorWidth] using
      ringDegree_le_sixteen_mul_errorWidth securityParameter
  levels_le := by intro securityParameter; simp [decomposition]
  base_le := by
    intro securityParameter
    have hdegree := ringDegree_le_sixteen_mul_errorWidth securityParameter
    simp only [decomposition, Polynomial.eval_mul, Polynomial.eval_ofNat,
      Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_one]
    simp only [errorWidth] at hdegree
    omega
  eta_le := by intro securityParameter; simp [errorWidth]

/-- For the concrete growing dimensions, an exponentially wide checked discrete Gaussian and
negligible table compilation error give negligible coupled correct-side loss.  This theorem does
not claim that the original polynomial-modulus centered-binomial family meets the exponential
width hypothesis. -/
theorem correctSmudgingError_negligible_of_two_pow_window
    (alpha : ℕ → ℝ) (halpha : ∀ securityParameter, 0 < alpha securityParameter)
    (certificate : (securityParameter : ℕ) →
      DiscreteGaussianSampler.ScalarCertificate
        (coefficientModulus securityParameter) (alpha securityParameter)
        (halpha securityParameter))
    (hwindowFits : ∀ securityParameter,
      ((2 ^ securityParameter : ℕ) : ℝ) ≤
        ModularGaussian.integerStddev
          (coefficientModulus securityParameter) (alpha securityParameter))
    (hcertificate : negligible (fun securityParameter ↦
      (certificate securityParameter).bound)) :
    negligible (correctSmudgingError decomposition alpha halpha certificate
      ringDegree (fun _ ↦ 1) ringDegree errorWidth) :=
  Asymptotic.correctSmudgingError_negligible_of_two_pow_window
    polynomialGrowth alpha halpha certificate hwindowFits hcertificate

end GrowingNoise

end

end FormalProof4FHE.TFHE.Native.ShiftedDiscreteGaussian.Asymptotic
