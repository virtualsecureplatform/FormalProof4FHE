/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.RingSquareBinarySelectorAsymptoticSecurity
import FormalProof4FHE.TFHE.RingSquarePowerOfTwoLiftingProduction

/-!
# Fixed-Modulus Asymptotics for the Power-of-Two RGSW Selector

This file packages the proved production lifting selector as an asymptotic family for a fixed
two-adic modulus exponent.  At security parameter `lambda`, the rank slack is `lambda`, so the
all-level selector failure is bounded by a polynomial factor times `2^-lambda`.

The security endpoint no longer assumes average-case anchored binary Ring-ISIS.  Its remaining
algorithmic premise is narrowly a PPT-closure certificate for an implementation of the explicit
binary Gaussian-elimination and two-adic lifting procedure.  The selector currently defined in
Lean uses classical choice for those finite linear-algebra witnesses, so that runtime certificate
is intentionally not asserted here.
-/

open OracleComp ENNReal

namespace FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.PowerOfTwoLifting.Asymptotic

noncomputable section

namespace Base

open BinarySelectorSecurity.Asymptotic

end Base

/-- Security-parameter-indexed RGSW data at one fixed power-of-two modulus depth.  The non-anchor
mask count is determined by the proved lifting recurrence, with rank slack equal to the security
parameter. -/
structure FixedDepthParameters (depth : ℕ) where
  degreeExponent : ℕ → ℕ
  levels : ℕ → ℕ
  eta : ℕ → ℕ
  Secret : ℕ → Type
  secretSampler : (securityParameter : ℕ) → ProbComp (Secret securityParameter)
  embed : (securityParameter : ℕ) → Secret securityParameter → Fin 1 →
    ProductionRing depth (degreeExponent securityParameter)
  gadget : (securityParameter : ℕ) → Fin (levels securityParameter) →
    ProductionRing depth (degreeExponent securityParameter)
  secretBound : ℕ → ℕ
  secretBound_on_support : ∀ securityParameter secretValue,
    secretValue ∈ support (secretSampler securityParameter) →
      LatticeCrypto.cInfNorm (embed securityParameter secretValue 0) ≤
        secretBound securityParameter

/-- Forget the fixed-depth presentation and expose the generic asymptotic selector parameters. -/
def FixedDepthParameters.toParameters {depth : ℕ}
    (params : FixedDepthParameters depth) :
    BinarySelectorSecurity.Asymptotic.Parameters where
  modulusExponent := fun _securityParameter ↦ depth + 1
  degreeExponent := params.degreeExponent
  levels := params.levels
  extraCount := fun securityParameter ↦
    productionExtraCount depth (params.degreeExponent securityParameter) securityParameter
  eta := params.eta
  Secret := params.Secret
  secretSampler := params.secretSampler
  embed := params.embed
  gadget := params.gadget
  secretBound := params.secretBound
  secretBound_on_support := params.secretBound_on_support

/-- The concrete production lifting selector at every security parameter and gadget level. -/
noncomputable def liftingSelectorFamily {depth : ℕ}
    (params : FixedDepthParameters depth) :
    BinarySelectorSecurity.Asymptotic.SelectorFamily params.toParameters where
  run securityParameter :=
    productionBitSelectors depth (params.degreeExponent securityParameter)
      securityParameter (params.levels securityParameter)
      (params.gadget securityParameter)

/-- Pointwise public-mask failure bound for the asymptotic lifting family. -/
theorem publicSelectorFailureError_le {depth : ℕ}
    (params : FixedDepthParameters depth) (securityParameter : ℕ) :
    BinarySelectorSecurity.Asymptotic.publicSelectorFailureError
        params.toParameters (liftingSelectorFamily params) securityParameter ≤
      (params.levels securityParameter : ℕ) *
        ((depth + 1 : ℕ) *
          (2 / (2 : ℝ≥0∞) ^ (securityParameter + 1))) := by
  unfold BinarySelectorSecurity.Asymptotic.publicSelectorFailureError
  change
    Pr[(fun challenge : Matrix (Fin 1)
          (Fin (params.levels securityParameter *
            (productionExtraCount depth
              (params.degreeExponent securityParameter) securityParameter + 1)))
          (ProductionRing depth (params.degreeExponent securityParameter)) ↦
        ¬ @BinarySelectorSecurity.ChallengeSelectorsSucceed
          (ProductionRing depth (params.degreeExponent securityParameter))
          (productionCommRing depth (params.degreeExponent securityParameter))
          (params.levels securityParameter)
          (productionExtraCount depth
            (params.degreeExponent securityParameter) securityParameter)
          (params.gadget securityParameter)
          (productionBitSelectors depth (params.degreeExponent securityParameter)
            securityParameter (params.levels securityParameter)
            (params.gadget securityParameter)) challenge) |
      ($ᵗ Matrix (Fin 1)
        (Fin (params.levels securityParameter *
          (productionExtraCount depth
            (params.degreeExponent securityParameter) securityParameter + 1)))
        (ProductionRing depth (params.degreeExponent securityParameter)))] ≤ _
  exact productionChallengeSelectors_failure_le depth
    (params.degreeExponent securityParameter) securityParameter
    (params.levels securityParameter) (params.gadget securityParameter)

/-- The exact binary rank factor at slack `lambda` is `2^-lambda`. -/
theorem two_div_two_pow_succ_eq_inv_two_pow (securityParameter : ℕ) :
    2 / (2 : ℝ≥0∞) ^ (securityParameter + 1) =
      ((2 : ℝ≥0∞) ^ securityParameter)⁻¹ := by
  rw [pow_succ, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inr (by finiteness)) (Or.inl (by finiteness))]
  calc
    2 * (((2 : ℝ≥0∞) ^ securityParameter)⁻¹ * (2 : ℝ≥0∞)⁻¹) =
        (2 * (2 : ℝ≥0∞)⁻¹) * ((2 : ℝ≥0∞) ^ securityParameter)⁻¹ := by
      ac_rfl
    _ = ((2 : ℝ≥0∞) ^ securityParameter)⁻¹ := by
      rw [ENNReal.mul_inv_cancel (by norm_num) (by finiteness), one_mul]

/-- Polynomially many gadget levels make the concrete selector's actual public-mask failure
negligible.  The modulus depth is a fixed constant in this theorem. -/
theorem publicSelectorFailureError_negligible {depth : ℕ}
    (params : FixedDepthParameters depth)
    (levelsPolynomial : Polynomial ℕ)
    (hLevels : ∀ securityParameter,
      params.levels securityParameter ≤ levelsPolynomial.eval securityParameter) :
    negligible
      (BinarySelectorSecurity.Asymptotic.publicSelectorFailureError
        params.toParameters (liftingSelectorFamily params)) := by
  let inverseTwoPow : ℕ → ℝ≥0∞ := fun securityParameter ↦
    ((2 : ℝ≥0∞) ^ securityParameter)⁻¹
  let envelope : ℕ → ℝ≥0∞ := fun securityParameter ↦
    (depth + 1 : ℕ) *
      ((levelsPolynomial.eval securityParameter : ℕ) * inverseTwoPow securityParameter)
  apply negligible_of_le (g := envelope)
  · intro securityParameter
    calc
      BinarySelectorSecurity.Asymptotic.publicSelectorFailureError
          params.toParameters (liftingSelectorFamily params) securityParameter ≤
        (params.levels securityParameter : ℕ) *
          ((depth + 1 : ℕ) *
            (2 / (2 : ℝ≥0∞) ^ (securityParameter + 1))) :=
        publicSelectorFailureError_le params securityParameter
      _ = (depth + 1 : ℕ) *
          ((params.levels securityParameter : ℕ) * inverseTwoPow securityParameter) := by
        rw [two_div_two_pow_succ_eq_inv_two_pow]
        simp only [inverseTwoPow]
        ring
      _ ≤ (depth + 1 : ℕ) *
          ((levelsPolynomial.eval securityParameter : ℕ) *
            inverseTwoPow securityParameter) := by
        gcongr
        exact_mod_cast hLevels securityParameter
      _ = envelope securityParameter := rfl
  · apply negligible_const_mul
    · exact negligible_polynomial_mul
        Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView.negligible_inv_two_pow
        levelsPolynomial
    · exact ENNReal.natCast_ne_top (depth + 1)

/-! ## Fixed-depth size and security endpoint -/

/-- Polynomial envelope for the lifting source count when the ring degree has polynomial growth
and the two-adic depth is fixed. -/
def sourceCountPolynomial (depth : ℕ) (degreePolynomial : Polynomial ℕ) :
    Polynomial ℕ :=
  Polynomial.C (depth + 1) *
    (degreePolynomial + Polynomial.X) *
    (degreePolynomial + 1) ^ depth

theorem productionExtraCount_le_sourceCountPolynomial {depth : ℕ}
    (params : FixedDepthParameters depth)
    (degreePolynomial : Polynomial ℕ)
    (hDegree : ∀ securityParameter,
      2 ^ params.degreeExponent securityParameter ≤
        degreePolynomial.eval securityParameter)
    (securityParameter : ℕ) :
    productionExtraCount depth (params.degreeExponent securityParameter)
        securityParameter ≤
      (sourceCountPolynomial depth degreePolynomial).eval securityParameter := by
  let degree := 2 ^ params.degreeExponent securityParameter
  let degreeBound := degreePolynomial.eval securityParameter
  calc
    productionExtraCount depth (params.degreeExponent securityParameter)
        securityParameter = sourceCount depth degree securityParameter := rfl
    _ ≤ (depth + 1) * (degree + securityParameter) * (degree + 1) ^ depth :=
      sourceCount_le_depth_mul_power depth degree securityParameter
    _ ≤ (depth + 1) * (degreeBound + securityParameter) *
        (degreeBound + 1) ^ depth := by
      gcongr
      · exact hDegree securityParameter
      · exact hDegree securityParameter
    _ = (sourceCountPolynomial depth degreePolynomial).eval securityParameter := by
      simp [sourceCountPolynomial, degreeBound]

/-- Fixed-depth standalone `RGSW_S(-S)` security from the proved selector failure bound,
negligible smudging, PPT closure of the explicit selector compiler, and ordinary batch-RLWE
security. -/
theorem secureAgainst_of_liftingSelector_smudging_and_batchRLWE {depth : ℕ}
    (params : FixedDepthParameters depth)
    (widening : BinarySelectorSecurity.Asymptotic.WideningFamily params.toParameters)
    (levelsPolynomial : Polynomial ℕ)
    (hLevels : ∀ securityParameter,
      params.levels securityParameter ≤ levelsPolynomial.eval securityParameter)
    (isPPT : BinarySelectorSecurity.Asymptotic.RGSWAdversaryFamily
      params.toParameters → Prop)
    (batchRLWEIsPPT : BinarySelectorSecurity.Asymptotic.BatchRLWEAdversaryFamily
      params.toParameters → Prop)
    (hReductionClosed : ∀ adversary, isPPT adversary →
      batchRLWEIsPPT
        (BinarySelectorSecurity.Asymptotic.selectorBatchRLWEReduction
          params.toParameters widening (liftingSelectorFamily params) adversary))
    (hSmudging : negligible
      (BinarySelectorSecurity.Asymptotic.smudgingError params.toParameters widening))
    (hBatchRLWE :
      (BinarySelectorSecurity.Asymptotic.batchRLWESecurityGame params.toParameters).secureAgainst
        batchRLWEIsPPT) :
    (BinarySelectorSecurity.Asymptotic.rgswSecurityGame
      params.toParameters widening).secureAgainst isPPT := by
  exact
    BinarySelectorSecurity.Asymptotic.secureAgainst_of_negligible_publicSelectorFailure_and_batchRLWE
      params.toParameters widening (liftingSelectorFamily params)
      isPPT batchRLWEIsPPT hReductionClosed
      (publicSelectorFailureError_negligible params levelsPolynomial hLevels)
      hSmudging hBatchRLWE

/-- End-to-end fixed-depth endpoint using the existing certified two-power Gaussian window to
discharge the residual-smudging term.  The only non-hardness premise left is PPT closure for an
implementation of the explicit lifting selector. -/
theorem secureAgainst_of_liftingSelector_twoPowGaussian_and_batchRLWE {depth : ℕ}
    (params : FixedDepthParameters depth)
    (widening : BinarySelectorSecurity.Asymptotic.WideningFamily params.toParameters)
    (levelsPolynomial : Polynomial ℕ)
    (hLevels : ∀ securityParameter,
      params.levels securityParameter ≤ levelsPolynomial.eval securityParameter)
    (growth : BinarySelectorSecurity.Asymptotic.SmudgingPolynomialGrowth
      params.toParameters)
    (hwindowFits : ∀ securityParameter,
      ((2 ^ securityParameter : ℕ) : ℝ) ≤
        ModularGaussian.integerStddev
          (2 ^ params.toParameters.modulusExponent securityParameter)
          (widening.alpha securityParameter))
    (hcertificate : negligible (fun securityParameter ↦
      (widening.certificate securityParameter).bound))
    (isPPT : BinarySelectorSecurity.Asymptotic.RGSWAdversaryFamily
      params.toParameters → Prop)
    (batchRLWEIsPPT : BinarySelectorSecurity.Asymptotic.BatchRLWEAdversaryFamily
      params.toParameters → Prop)
    (hReductionClosed : ∀ adversary, isPPT adversary →
      batchRLWEIsPPT
        (BinarySelectorSecurity.Asymptotic.selectorBatchRLWEReduction
          params.toParameters widening (liftingSelectorFamily params) adversary))
    (hBatchRLWE :
      (BinarySelectorSecurity.Asymptotic.batchRLWESecurityGame params.toParameters).secureAgainst
        batchRLWEIsPPT) :
    (BinarySelectorSecurity.Asymptotic.rgswSecurityGame
      params.toParameters widening).secureAgainst isPPT := by
  apply secureAgainst_of_liftingSelector_smudging_and_batchRLWE
    params widening levelsPolynomial hLevels isPPT batchRLWEIsPPT
    hReductionClosed
  · exact
      BinarySelectorSecurity.Asymptotic.smudgingError_negligible_of_two_pow_window
        params.toParameters widening growth hwindowFits hcertificate
  · exact hBatchRLWE

end

end FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.PowerOfTwoLifting.Asymptotic
