/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.RingSquareBinarySelectorSecurity
import FormalProof4FHE.TFHE.AsymptoticKeySwitchFirstUniversalCircular

/-!
# Asymptotic Binary-Selector Security for `RGSW_S(-S)`

This file packages the finite binary-selector compiler as a runtime-aware asymptotic reduction.
It separates three obligations:

* completeness and polynomial-time implementability of the public selector family;
* negligibility of the explicit discrete-Gaussian translation loss; and
* ordinary batch-RLWE security for the reduced distinguisher family.

The counting failure is no longer an abstract premise.  If `m = kN + lambda` binary coordinates
are used for modulus `q = 2^k` and ring degree `N`, and the number of gadget levels is polynomial,
then the checked failure bound is negligible.  Thus the only unproved algorithmic content is an
efficient complete (or comparably failure-bounded) selector.
-/

open ENNReal OracleComp

namespace FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.BinarySelectorSecurity.Asymptotic

noncomputable section

open BinaryPreimageExistence

/-- Security-parameter-indexed data for the standalone ring-square distribution. -/
structure Parameters where
  modulusExponent : ℕ → ℕ
  degreeExponent : ℕ → ℕ
  levels : ℕ → ℕ
  extraCount : ℕ → ℕ
  eta : ℕ → ℕ
  Secret : ℕ → Type
  secretSampler : (securityParameter : ℕ) → ProbComp (Secret securityParameter)
  embed : (securityParameter : ℕ) → Secret securityParameter → Fin 1 →
    SingleSourceInverse.PowerOfTwo.Ring
      (modulusExponent securityParameter) (degreeExponent securityParameter)
  gadget : (securityParameter : ℕ) → Fin (levels securityParameter) →
    SingleSourceInverse.PowerOfTwo.Ring
      (modulusExponent securityParameter) (degreeExponent securityParameter)
  secretBound : ℕ → ℕ
  secretBound_on_support : ∀ securityParameter secretValue,
    secretValue ∈ support (secretSampler securityParameter) →
      LatticeCrypto.cInfNorm (embed securityParameter secretValue 0) ≤
        secretBound securityParameter

/-- Certified widening discrete Gaussians at every security parameter. -/
structure WideningFamily (params : Parameters) where
  alpha : ℕ → ℝ
  alpha_positive : ∀ securityParameter, 0 < alpha securityParameter
  certificate : (securityParameter : ℕ) →
    DiscreteGaussianSampler.ScalarCertificate
      (2 ^ params.modulusExponent securityParameter)
      (alpha securityParameter) (alpha_positive securityParameter)

/-- One public bit-selector algorithm at every security parameter and gadget level. -/
structure CompleteSelectorFamily (params : Parameters) where
  run : (securityParameter : ℕ) → Fin (params.levels securityParameter) →
    BitSelector
      (SingleSourceInverse.PowerOfTwo.Ring
        (params.modulusExponent securityParameter)
        (params.degreeExponent securityParameter))
      (params.extraCount securityParameter)
  complete : ∀ securityParameter level,
    IsCompleteBinarySelector
      (params.gadget securityParameter level)
      (run securityParameter level)

/-- A public bit-selector family with no pointwise completeness requirement.  This is the right
algorithmic object for average-case security: the selector may fail on some mask tables, provided
that its aggregate failure probability under the uniform public-mask distribution is negligible. -/
structure SelectorFamily (params : Parameters) where
  run : (securityParameter : ℕ) → Fin (params.levels securityParameter) →
    BitSelector
      (SingleSourceInverse.PowerOfTwo.Ring
        (params.modulusExponent securityParameter)
        (params.degreeExponent securityParameter))
      (params.extraCount securityParameter)

/-- Forget pointwise completeness and retain the selector algorithms. -/
def CompleteSelectorFamily.toSelectorFamily
    {params : Parameters} (selectors : CompleteSelectorFamily params) :
    SelectorFamily params where
  run := selectors.run

/-- The noncomputable exhaustive family witnesses logical completeness at every parameter.  Its
presence makes the remaining gap precise: the security endpoint still requires PPT closure of the
compiler using this family, which exhaustive choice does not provide. -/
noncomputable def exhaustiveCompleteSelectorFamily (params : Parameters) :
    CompleteSelectorFamily params where
  run securityParameter level :=
    BinaryPreimageExistence.exhaustiveCompleteBitSelector
      (params.gadget securityParameter level)
  complete securityParameter level :=
    BinaryPreimageExistence.exhaustiveCompleteBitSelector_isComplete
      (params.gadget securityParameter level)

/-- A family of distinguishers for genuine `RGSW_S(-S)`. -/
abbrev RGSWAdversaryFamily (params : Parameters) :=
  (securityParameter : ℕ) →
    Full.Distinguisher
      (SingleSourceInverse.PowerOfTwo.Ring
        (params.modulusExponent securityParameter)
        (params.degreeExponent securityParameter))
      (params.levels securityParameter)

/-- The ordinary batch-RLWE adversary type produced at one security parameter. -/
abbrev BatchRLWEAdversaryAt (params : Parameters) (securityParameter : ℕ) :=
  LearningWithErrors.Adversary
    (FormalProof4FHE.LWE.embeddedBatchProblem 1
      (params.levels securityParameter * (params.extraCount securityParameter + 1) +
        TGSW.rowCount 1 (params.levels securityParameter))
      (params.secretSampler securityParameter)
      (params.embed securityParameter)
      (RLWE.CenteredBinomial.sampler
        (2 ^ params.modulusExponent securityParameter)
        (2 ^ params.degreeExponent securityParameter)
        (params.eta securityParameter)))

/-- Families of ordinary batch-RLWE distinguishers, with efficiency classified externally. -/
structure BatchRLWEAdversaryFamily (params : Parameters) where
  run : (securityParameter : ℕ) → BatchRLWEAdversaryAt params securityParameter

/-- Genuine widened-noise `RGSW_S(-S)` security game. -/
noncomputable def rgswSecurityGame
    (params : Parameters) (widening : WideningFamily params) :
    SecurityGame (RGSWAdversaryFamily params) where
  advantage adversary securityParameter := ENNReal.ofReal
    (Full.rgswMinusSecretAdvantage
      (params.levels securityParameter)
      (params.secretSampler securityParameter)
      (params.embed securityParameter)
      (Heterogeneous.convolutionSampler
        (RLWE.CenteredBinomial.sampler
          (2 ^ params.modulusExponent securityParameter)
          (2 ^ params.degreeExponent securityParameter)
          (params.eta securityParameter))
        (DiscreteGaussianSampler.ringSampler
          (2 ^ params.degreeExponent securityParameter)
          (widening.certificate securityParameter)))
      (params.gadget securityParameter)
      (adversary securityParameter))

/-- Ordinary batch-RLWE security game under the narrow centered-binomial source law. -/
noncomputable def batchRLWESecurityGame (params : Parameters) :
    SecurityGame (BatchRLWEAdversaryFamily params) where
  advantage adversary securityParameter := ENNReal.ofReal
    (LearningWithErrors.advantage
      (FormalProof4FHE.LWE.embeddedBatchProblem 1
        (params.levels securityParameter * (params.extraCount securityParameter + 1) +
          TGSW.rowCount 1 (params.levels securityParameter))
        (params.secretSampler securityParameter)
        (params.embed securityParameter)
        (RLWE.CenteredBinomial.sampler
          (2 ^ params.modulusExponent securityParameter)
          (2 ^ params.degreeExponent securityParameter)
          (params.eta securityParameter)))
      (adversary.run securityParameter))

/-- The exact finite compiler reduction for an arbitrary average-case selector family, packaged
pointwise as an adversary family. -/
noncomputable def selectorBatchRLWEReduction
    (params : Parameters) (widening : WideningFamily params)
    (selectors : SelectorFamily params)
    (adversary : RGSWAdversaryFamily params) : BatchRLWEAdversaryFamily params where
  run securityParameter :=
    LWE.TwoBlock.convolutionReduction
      (secondErrorSampler := Heterogeneous.convolutionSampler
        (RLWE.CenteredBinomial.sampler
          (2 ^ params.modulusExponent securityParameter)
          (2 ^ params.degreeExponent securityParameter)
          (params.eta securityParameter))
        (DiscreteGaussianSampler.ringSampler
          (2 ^ params.degreeExponent securityParameter)
          (widening.certificate securityParameter)))
      (extraErrorSampler := DiscreteGaussianSampler.ringSampler
        (2 ^ params.degreeExponent securityParameter)
        (widening.certificate securityParameter))
      (Heterogeneous.reduction
        (targetErrorSampler := Heterogeneous.convolutionSampler
          (RLWE.CenteredBinomial.sampler
            (2 ^ params.modulusExponent securityParameter)
            (2 ^ params.degreeExponent securityParameter)
            (params.eta securityParameter))
          (DiscreteGaussianSampler.ringSampler
            (2 ^ params.degreeExponent securityParameter)
            (widening.certificate securityParameter)))
        (binarySelectors (selectors.run securityParameter))
        (Full.restoreDistinguisher
          (params.gadget securityParameter) (adversary securityParameter)))

/-- Complete-selector specialization of the exact finite compiler reduction. -/
noncomputable def batchRLWEReduction
    (params : Parameters) (widening : WideningFamily params)
    (selectors : CompleteSelectorFamily params)
    (adversary : RGSWAdversaryFamily params) : BatchRLWEAdversaryFamily params :=
  selectorBatchRLWEReduction params widening selectors.toSelectorFamily adversary

/-- The explicit all-level selector-failure term. -/
noncomputable def selectorFailureError (params : Parameters) : ℕ → ℝ≥0∞ :=
  fun securityParameter ↦ ENNReal.ofReal
    ((params.levels securityParameter : ℝ) *
      ((((2 ^ params.modulusExponent securityParameter) ^
          (2 ^ params.degreeExponent securityParameter) : ℕ) : ℝ) /
        (((2 ^ params.extraCount securityParameter : ℕ) : ℝ) +
          (((2 ^ params.modulusExponent securityParameter) ^
            (2 ^ params.degreeExponent securityParameter) : ℕ) : ℝ))))

/-- Actual aggregate failure probability of an arbitrary public selector family on the uniform
source-mask challenge.  This is the average-case anchored binary Ring-ISIS search error needed by
the reduction; it does not require success on every mask table that happens to have a preimage. -/
noncomputable def publicSelectorFailureError
    (params : Parameters) (selectors : SelectorFamily params) : ℕ → ℝ≥0∞ :=
  fun securityParameter ↦
    Pr[(fun challenge : Matrix (Fin 1)
          (Fin (params.levels securityParameter *
            (params.extraCount securityParameter + 1)))
          (SingleSourceInverse.PowerOfTwo.Ring
            (params.modulusExponent securityParameter)
            (params.degreeExponent securityParameter)) ↦
        ¬ ChallengeSelectorsSucceed
          (params.gadget securityParameter)
          (selectors.run securityParameter) challenge) |
      ($ᵗ Matrix (Fin 1)
        (Fin (params.levels securityParameter *
          (params.extraCount securityParameter + 1)))
        (SingleSourceInverse.PowerOfTwo.Ring
          (params.modulusExponent securityParameter)
          (params.degreeExponent securityParameter)))]

/-- Pointwise-complete selectors satisfy the explicit information-theoretic counting bound, now
viewed through the more general average-case failure interface. -/
theorem publicSelectorFailureError_le_selectorFailureError_of_complete
    (params : Parameters) (selectors : CompleteSelectorFamily params)
    (securityParameter : ℕ) :
    publicSelectorFailureError params selectors.toSelectorFamily securityParameter ≤
      selectorFailureError params securityParameter := by
  unfold publicSelectorFailureError selectorFailureError
  rw [← ENNReal.ofReal_toReal probEvent_ne_top]
  exact ENNReal.ofReal_le_ofReal
    (production_challengeSelectors_failure_toReal_le_levels_mul_card_div_add
      (params.modulusExponent securityParameter)
      (params.degreeExponent securityParameter)
      (params.levels securityParameter)
      (params.extraCount securityParameter)
      (params.gadget securityParameter)
      (selectors.run securityParameter)
      (selectors.complete securityParameter))

/-- The explicit norm-one residual-smudging term. -/
def inducedShiftBound (params : Parameters) (securityParameter : ℕ) : ℕ :=
  SelectorNoise.Native.inducedShiftBoundForDegree
    (2 ^ params.degreeExponent securityParameter)
    (params.extraCount securityParameter + 1)
    (params.secretBound securityParameter) 1
    (params.eta securityParameter)

noncomputable def smudgingError
    (params : Parameters) (widening : WideningFamily params) : ℕ → ℝ≥0∞ :=
  fun securityParameter ↦ ENNReal.ofReal
    ((params.levels securityParameter : ℝ) *
      (((2 ^ params.degreeExponent securityParameter : ℕ) : ℝ) *
        DiscreteGaussianSampler.scalarLinearShiftBound
          (widening.certificate securityParameter)
          (inducedShiftBound params securityParameter)))

/-- The complete statistical loss of the finite compiler. -/
def statisticalError
    (params : Parameters) (widening : WideningFamily params) : ℕ → ℝ≥0∞ :=
  selectorFailureError params + smudgingError params widening

/-- Pointwise finite reduction for an arbitrary selector family.  The first loss is its actual
average-case failure probability, rather than the stronger complete-selector counting bound. -/
theorem rgswSecurityGame_advantage_le_publicSelectorFailure_add_smudging_add_batchRLWE
    (params : Parameters) (widening : WideningFamily params)
    (selectors : SelectorFamily params)
    (adversary : RGSWAdversaryFamily params) (securityParameter : ℕ) :
    (rgswSecurityGame params widening).advantage adversary securityParameter ≤
      publicSelectorFailureError params selectors securityParameter +
        smudgingError params widening securityParameter +
        (batchRLWESecurityGame params).advantage
          (selectorBatchRLWEReduction params widening selectors adversary)
          securityParameter := by
  have hFinite :=
    production_rgswMinusSecretAdvantage_centeredBinomial_widenedDiscreteGaussian_le_of_binarySelectors
      (params.modulusExponent securityParameter)
      (params.degreeExponent securityParameter)
      (params.levels securityParameter)
      (params.extraCount securityParameter)
      (params.eta securityParameter)
      (widening.certificate securityParameter)
      (params.secretSampler securityParameter)
      (params.embed securityParameter)
      (params.gadget securityParameter)
      (selectors.run securityParameter)
      (adversary securityParameter)
      (params.secretBound securityParameter)
      (params.secretBound_on_support securityParameter)
  have hLift := ENNReal.ofReal_le_ofReal hFinite
  unfold publicSelectorFailureError
  change ENNReal.ofReal _ ≤
    _ + ENNReal.ofReal _ + ENNReal.ofReal _
  rw [← ENNReal.ofReal_toReal probEvent_ne_top]
  exact hLift.trans
    (ENNReal.ofReal_add_le.trans
      (add_le_add ENNReal.ofReal_add_le le_rfl))

/-- Pointwise lifting of the checked finite theorem. -/
theorem rgswSecurityGame_advantage_le_statistical_add_batchRLWE
    (params : Parameters) (widening : WideningFamily params)
    (selectors : CompleteSelectorFamily params)
    (adversary : RGSWAdversaryFamily params) (securityParameter : ℕ) :
    (rgswSecurityGame params widening).advantage adversary securityParameter ≤
      statisticalError params widening securityParameter +
        (batchRLWESecurityGame params).advantage
          (batchRLWEReduction params widening selectors adversary) securityParameter := by
  have hFinite :=
    production_rgswMinusSecretAdvantage_centeredBinomial_widenedDiscreteGaussian_le_of_completeBinarySelectors
      (params.modulusExponent securityParameter)
      (params.degreeExponent securityParameter)
      (params.levels securityParameter)
      (params.extraCount securityParameter)
      (params.eta securityParameter)
      (widening.certificate securityParameter)
      (params.secretSampler securityParameter)
      (params.embed securityParameter)
      (params.gadget securityParameter)
      (selectors.run securityParameter)
      (selectors.complete securityParameter)
      (adversary securityParameter)
      (params.secretBound securityParameter)
      (params.secretBound_on_support securityParameter)
  have hLift := ENNReal.ofReal_le_ofReal hFinite
  change ENNReal.ofReal _ ≤
    (ENNReal.ofReal _ + ENNReal.ofReal _) + ENNReal.ofReal _
  exact hLift.trans
    (ENNReal.ofReal_add_le.trans
      (add_le_add ENNReal.ofReal_add_le le_rfl))

/-- Negligible compiler losses and ordinary batch-RLWE security imply asymptotic circular
security, provided the concrete selector-based reduction preserves the chosen PPT classes. -/
theorem secureAgainst_of_negligible_errors_and_batchRLWE
    (params : Parameters) (widening : WideningFamily params)
    (selectors : CompleteSelectorFamily params)
    (isPPT : RGSWAdversaryFamily params → Prop)
    (batchRLWEIsPPT : BatchRLWEAdversaryFamily params → Prop)
    (hReductionClosed : ∀ adversary, isPPT adversary →
      batchRLWEIsPPT (batchRLWEReduction params widening selectors adversary))
    (hFailure : negligible (selectorFailureError params))
    (hSmudging : negligible (smudgingError params widening))
    (hBatchRLWE : (batchRLWESecurityGame params).secureAgainst batchRLWEIsPPT) :
    (rgswSecurityGame params widening).secureAgainst isPPT := by
  intro adversary hadversary
  apply negligible_of_le
    (rgswSecurityGame_advantage_le_statistical_add_batchRLWE
      params widening selectors adversary)
  exact negligible_add
    (negligible_add hFailure hSmudging)
    (hBatchRLWE _ (hReductionClosed adversary hadversary))

/-- Average-case selector endpoint.  Pointwise completeness is unnecessary: negligible failure
on uniform public masks, negligible residual smudging, PPT closure of the concrete compiler, and
ordinary batch-RLWE security suffice for standalone `RGSW_S(-S)` security. -/
theorem secureAgainst_of_negligible_publicSelectorFailure_and_batchRLWE
    (params : Parameters) (widening : WideningFamily params)
    (selectors : SelectorFamily params)
    (isPPT : RGSWAdversaryFamily params → Prop)
    (batchRLWEIsPPT : BatchRLWEAdversaryFamily params → Prop)
    (hReductionClosed : ∀ adversary, isPPT adversary →
      batchRLWEIsPPT
        (selectorBatchRLWEReduction params widening selectors adversary))
    (hSelectorFailure : negligible (publicSelectorFailureError params selectors))
    (hSmudging : negligible (smudgingError params widening))
    (hBatchRLWE : (batchRLWESecurityGame params).secureAgainst batchRLWEIsPPT) :
    (rgswSecurityGame params widening).secureAgainst isPPT := by
  intro adversary hadversary
  apply negligible_of_le
    (rgswSecurityGame_advantage_le_publicSelectorFailure_add_smudging_add_batchRLWE
      params widening selectors adversary)
  exact negligible_add
    (negligible_add hSelectorFailure hSmudging)
    (hBatchRLWE _ (hReductionClosed adversary hadversary))

/-- Named form of the sole algorithmic conjecture left by the short-preimage route.  It asks for
one public selector family whose aggregate failure on the random anchored binary Ring-ISIS
instances is negligible and whose use inside the reduction preserves the admitted PPT classes.
No hardness or circular-security premise is hidden in this package. -/
structure EfficientAnchoredBinaryISIS
    (params : Parameters) (widening : WideningFamily params)
    (isPPT : RGSWAdversaryFamily params → Prop)
    (batchRLWEIsPPT : BatchRLWEAdversaryFamily params → Prop) where
  selectors : SelectorFamily params
  failure_negligible : negligible (publicSelectorFailureError params selectors)
  reduction_closed : ∀ adversary, isPPT adversary →
    batchRLWEIsPPT
      (selectorBatchRLWEReduction params widening selectors adversary)

/-- The named average-case anchored binary Ring-ISIS compiler plus negligible smudging and
ordinary batch-RLWE security imply genuine standalone `RGSW_S(-S)` security. -/
theorem secureAgainst_of_efficientAnchoredBinaryISIS_and_batchRLWE
    (params : Parameters) (widening : WideningFamily params)
    (isPPT : RGSWAdversaryFamily params → Prop)
    (batchRLWEIsPPT : BatchRLWEAdversaryFamily params → Prop)
    (compiler : EfficientAnchoredBinaryISIS
      params widening isPPT batchRLWEIsPPT)
    (hSmudging : negligible (smudgingError params widening))
    (hBatchRLWE : (batchRLWESecurityGame params).secureAgainst batchRLWEIsPPT) :
    (rgswSecurityGame params widening).secureAgainst isPPT := by
  exact secureAgainst_of_negligible_publicSelectorFailure_and_batchRLWE
    params widening compiler.selectors isPPT batchRLWEIsPPT
    compiler.reduction_closed compiler.failure_negligible hSmudging hBatchRLWE

/-! ## The entropy-margin schedule -/

/-- `kN + lambda` binary choices and polynomially many levels make the complete-selector failure
term negligible. -/
theorem selectorFailureError_negligible_of_entropyMargin
    (params : Parameters)
    (levelsPolynomial : Polynomial ℕ)
    (hLevels : ∀ securityParameter,
      params.levels securityParameter ≤ levelsPolynomial.eval securityParameter)
    (hEntropy : ∀ securityParameter,
      params.extraCount securityParameter =
        params.modulusExponent securityParameter *
          (2 ^ params.degreeExponent securityParameter) + securityParameter) :
    negligible (selectorFailureError params) := by
  apply negligible_of_le
    (g := fun securityParameter ↦
      ((show ℕ from levelsPolynomial.eval securityParameter) : ℝ≥0∞) *
        ((2 : ℝ≥0∞) ^ securityParameter)⁻¹)
  · intro securityParameter
    let levelBound : ℕ := levelsPolynomial.eval securityParameter
    have hLevelBound : params.levels securityParameter ≤ levelBound :=
      hLevels securityParameter
    have hRatio := production_failureFraction_entropyMargin_le_inv_twoPow
      (params.modulusExponent securityParameter)
      (params.degreeExponent securityParameter) securityParameter
    have hLevelsReal :
        (params.levels securityParameter : ℝ) ≤
          (levelBound : ℝ) := by
      exact_mod_cast hLevelBound
    have hFailureReal :
        (params.levels securityParameter : ℝ) *
            ((((2 ^ params.modulusExponent securityParameter) ^
                (2 ^ params.degreeExponent securityParameter) : ℕ) : ℝ) /
              (((2 ^ params.extraCount securityParameter : ℕ) : ℝ) +
                (((2 ^ params.modulusExponent securityParameter) ^
                  (2 ^ params.degreeExponent securityParameter) : ℕ) : ℝ))) ≤
          (levelBound : ℝ) *
            (((2 ^ securityParameter : ℕ) : ℝ))⁻¹ := by
      calc
        _ = (params.levels securityParameter : ℝ) *
            ((((2 ^ params.modulusExponent securityParameter) ^
                (2 ^ params.degreeExponent securityParameter) : ℕ) : ℝ) /
              (((2 ^ (params.modulusExponent securityParameter *
                    (2 ^ params.degreeExponent securityParameter) + securityParameter) : ℕ) : ℝ) +
                (((2 ^ params.modulusExponent securityParameter) ^
                  (2 ^ params.degreeExponent securityParameter) : ℕ) : ℝ))) := by
          rw [hEntropy securityParameter]
        _ ≤ (params.levels securityParameter : ℝ) *
            (((2 ^ securityParameter : ℕ) : ℝ))⁻¹ := by
          exact mul_le_mul_of_nonneg_left hRatio (by positivity)
        _ ≤ _ := by
          exact mul_le_mul_of_nonneg_right
            hLevelsReal (by positivity)
    exact (ENNReal.ofReal_le_ofReal hFailureReal).trans_eq (by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
        ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_natCast]
      simp [levelBound])
  · exact negligible_polynomial_mul
      Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView.negligible_inv_two_pow
      levelsPolynomial

/-- Any pointwise-complete selector family has negligible *actual* public-mask failure under the
entropy-margin schedule.  This result is independent of runtime; the exhaustive family is a
logical inhabitant, while a cryptographic reduction still needs an efficient implementation. -/
theorem publicSelectorFailureError_negligible_of_complete_entropyMargin
    (params : Parameters) (selectors : CompleteSelectorFamily params)
    (levelsPolynomial : Polynomial ℕ)
    (hLevels : ∀ securityParameter,
      params.levels securityParameter ≤ levelsPolynomial.eval securityParameter)
    (hEntropy : ∀ securityParameter,
      params.extraCount securityParameter =
        params.modulusExponent securityParameter *
          (2 ^ params.degreeExponent securityParameter) + securityParameter) :
    negligible
      (publicSelectorFailureError params selectors.toSelectorFamily) := by
  apply negligible_of_le
    (fun securityParameter ↦
      publicSelectorFailureError_le_selectorFailureError_of_complete
        params selectors securityParameter)
  exact selectorFailureError_negligible_of_entropyMargin
    params levelsPolynomial hLevels hEntropy

/-! ## Explicit asymptotic Gaussian widening -/

/-- Polynomial bounds for the row layout factor and the deterministic induced shift. -/
structure SmudgingPolynomialGrowth (params : Parameters) where
  layoutPolynomial : Polynomial ℕ
  shiftPolynomial : Polynomial ℕ
  layout_le : ∀ securityParameter,
    params.levels securityParameter * (2 ^ params.degreeExponent securityParameter) ≤
      layoutPolynomial.eval securityParameter
  shift_le : ∀ securityParameter,
    inducedShiftBound params securityParameter ≤
      shiftPolynomial.eval securityParameter

/-- Finite-window real upper bound for the standalone ring-square smudging term. -/
noncomputable def finiteWindowSmudgingUpperBound
    (params : Parameters) (widening : WideningFamily params)
    (window : ℕ → ℕ) (securityParameter : ℕ) : ℝ :=
  (params.levels securityParameter : ℝ) *
    (((2 ^ params.degreeExponent securityParameter : ℕ) : ℝ) *
      (2 * (widening.certificate securityParameter).bound.toReal +
        (inducedShiftBound params securityParameter : ℝ) *
          (Real.exp (1 / 2 : ℝ) / (window securityParameter + 1 : ℕ))))

theorem smudgingError_le_finiteWindowUpperBound
    (params : Parameters) (widening : WideningFamily params)
    (window : ℕ → ℕ)
    (hwindow : ∀ securityParameter,
      (window securityParameter : ℝ) ≤
        ModularGaussian.integerStddev
          (2 ^ params.modulusExponent securityParameter)
          (widening.alpha securityParameter))
    (securityParameter : ℕ) :
    smudgingError params widening securityParameter ≤
      ENNReal.ofReal
        (finiteWindowSmudgingUpperBound params widening window securityParameter) := by
  unfold smudgingError finiteWindowSmudgingUpperBound
  apply ENNReal.ofReal_le_ofReal
  exact mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left
      (DiscreteGaussianSampler.scalarLinearShiftBound_le_exp_half_window
        (widening.certificate securityParameter)
        (inducedShiftBound params securityParameter)
        (window securityParameter) (hwindow securityParameter))
      (by positivity))
    (by positivity)

/-- Expanded `ENNReal` form of the finite-window upper bound. -/
theorem ofReal_finiteWindowSmudgingUpperBound_eq
    (params : Parameters) (widening : WideningFamily params)
    (window : ℕ → ℕ) (securityParameter : ℕ) :
    ENNReal.ofReal
        (finiteWindowSmudgingUpperBound params widening window securityParameter) =
      ((params.levels securityParameter : ℕ) *
          (2 ^ params.degreeExponent securityParameter : ℕ) : ℝ≥0∞) *
        (2 * (widening.certificate securityParameter).bound +
          (inducedShiftBound params securityParameter : ℕ) *
            ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
            ((window securityParameter + 1 : ℕ) : ℝ≥0∞)⁻¹) := by
  unfold finiteWindowSmudgingUpperBound
  rw [ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_add (mul_nonneg (by norm_num) ENNReal.toReal_nonneg)
      (mul_nonneg (Nat.cast_nonneg _)
        (div_nonneg (le_of_lt (Real.exp_pos _)) (Nat.cast_nonneg _))),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_toReal (widening.certificate securityParameter).bound_ne_top,
    ENNReal.ofReal_mul (Nat.cast_nonneg _),
    ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) <
      (window securityParameter + 1 : ℕ))]
  norm_cast
  rw [div_eq_mul_inv]
  push_cast
  ring

/-- Polynomial envelope separating finite sampler error from the Gaussian-window term. -/
noncomputable def smudgingPolynomialEnvelope
    (params : Parameters) (widening : WideningFamily params)
    (growth : SmudgingPolynomialGrowth params)
    (window : ℕ → ℕ) (securityParameter : ℕ) : ℝ≥0∞ :=
  2 * (growth.layoutPolynomial.eval securityParameter : ℕ) *
      (widening.certificate securityParameter).bound +
    ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
      ((growth.layoutPolynomial * growth.shiftPolynomial).eval securityParameter : ℕ) *
      ((window securityParameter + 1 : ℕ) : ℝ≥0∞)⁻¹

theorem ofReal_finiteWindowSmudgingUpperBound_le_polynomialEnvelope
    (params : Parameters) (widening : WideningFamily params)
    (growth : SmudgingPolynomialGrowth params)
    (window : ℕ → ℕ) (securityParameter : ℕ) :
    ENNReal.ofReal
        (finiteWindowSmudgingUpperBound params widening window securityParameter) ≤
      smudgingPolynomialEnvelope params widening growth window securityParameter := by
  rw [ofReal_finiteWindowSmudgingUpperBound_eq]
  unfold smudgingPolynomialEnvelope
  simp only [Polynomial.eval_mul]
  have hLayout :
      ((params.levels securityParameter : ℕ) *
          (2 ^ params.degreeExponent securityParameter : ℕ) : ℝ≥0∞) ≤
        (growth.layoutPolynomial.eval securityParameter : ℕ) := by
    exact_mod_cast growth.layout_le securityParameter
  have hShift :
      (inducedShiftBound params securityParameter : ℕ) ≤
        (growth.shiftPolynomial.eval securityParameter : ℕ) := by
    exact_mod_cast growth.shift_le securityParameter
  calc
    _ = 2 *
          ((params.levels securityParameter : ℕ) *
            (2 ^ params.degreeExponent securityParameter : ℕ) : ℝ≥0∞) *
          (widening.certificate securityParameter).bound +
        ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
          (((params.levels securityParameter : ℕ) *
              (2 ^ params.degreeExponent securityParameter : ℕ) : ℝ≥0∞) *
            (inducedShiftBound params securityParameter : ℕ)) *
          ((window securityParameter + 1 : ℕ) : ℝ≥0∞)⁻¹ := by ring
    _ ≤ 2 * (growth.layoutPolynomial.eval securityParameter : ℕ) *
          (widening.certificate securityParameter).bound +
        ENNReal.ofReal (Real.exp (1 / 2 : ℝ)) *
          ((growth.layoutPolynomial.eval securityParameter : ℕ) *
            (growth.shiftPolynomial.eval securityParameter : ℕ)) *
          ((window securityParameter + 1 : ℕ) : ℝ≥0∞)⁻¹ := by
      gcongr
    _ = _ := by
      push_cast
      ring

theorem smudgingPolynomialEnvelope_negligible
    (params : Parameters) (widening : WideningFamily params)
    (growth : SmudgingPolynomialGrowth params)
    (window : ℕ → ℕ)
    (hcertificate : negligible (fun securityParameter ↦
      (widening.certificate securityParameter).bound))
    (hwindow : negligible (fun securityParameter ↦
      ((window securityParameter + 1 : ℕ) : ℝ≥0∞)⁻¹)) :
    negligible (smudgingPolynomialEnvelope params widening growth window) := by
  apply negligible_add
  · simpa only [smudgingPolynomialEnvelope, Pi.add_apply, mul_assoc] using
      negligible_const_mul
        (negligible_polynomial_mul hcertificate growth.layoutPolynomial)
        (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
  · simpa only [smudgingPolynomialEnvelope, Pi.add_apply, mul_assoc] using
      negligible_const_mul
        (negligible_polynomial_mul hwindow
          (growth.layoutPolynomial * growth.shiftPolynomial))
        (ENNReal.ofReal_ne_top)

/-- Polynomial construction growth, negligible finite sampler error, and an exponentially large
checked Gaussian window make the exact smudging term negligible. -/
theorem smudgingError_negligible
    (params : Parameters) (widening : WideningFamily params)
    (growth : SmudgingPolynomialGrowth params)
    (window : ℕ → ℕ)
    (hwindowFits : ∀ securityParameter,
      (window securityParameter : ℝ) ≤
        ModularGaussian.integerStddev
          (2 ^ params.modulusExponent securityParameter)
          (widening.alpha securityParameter))
    (hcertificate : negligible (fun securityParameter ↦
      (widening.certificate securityParameter).bound))
    (hwindow : negligible (fun securityParameter ↦
      ((window securityParameter + 1 : ℕ) : ℝ≥0∞)⁻¹)) :
    negligible (smudgingError params widening) := by
  apply negligible_of_le
    (g := smudgingPolynomialEnvelope params widening growth window)
  · intro securityParameter
    exact (smudgingError_le_finiteWindowUpperBound
      params widening window hwindowFits securityParameter).trans
        (ofReal_finiteWindowSmudgingUpperBound_le_polynomialEnvelope
          params widening growth window securityParameter)
  · exact smudgingPolynomialEnvelope_negligible
      params widening growth window hcertificate hwindow

/-- A checked Gaussian standard deviation at least `2^lambda` supplies the negligible inverse
window automatically. -/
theorem smudgingError_negligible_of_two_pow_window
    (params : Parameters) (widening : WideningFamily params)
    (growth : SmudgingPolynomialGrowth params)
    (hwindowFits : ∀ securityParameter,
      ((2 ^ securityParameter : ℕ) : ℝ) ≤
        ModularGaussian.integerStddev
          (2 ^ params.modulusExponent securityParameter)
          (widening.alpha securityParameter))
    (hcertificate : negligible (fun securityParameter ↦
      (widening.certificate securityParameter).bound)) :
    negligible (smudgingError params widening) := by
  apply smudgingError_negligible params widening growth
    (fun securityParameter ↦ 2 ^ securityParameter) hwindowFits hcertificate
  apply negligible_of_le (g := fun securityParameter ↦
    ((2 : ℝ≥0∞) ^ securityParameter)⁻¹)
  · intro securityParameter
    rw [ENNReal.inv_le_inv]
    norm_cast
    omega
  · exact Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView.negligible_inv_two_pow

/-- With the entropy-margin schedule, only smudging negligibility, reduction efficiency, and
ordinary batch-RLWE security remain. -/
theorem secureAgainst_of_entropyMargin_smudging_and_batchRLWE
    (params : Parameters) (widening : WideningFamily params)
    (selectors : CompleteSelectorFamily params)
    (levelsPolynomial : Polynomial ℕ)
    (hLevels : ∀ securityParameter,
      params.levels securityParameter ≤ levelsPolynomial.eval securityParameter)
    (hEntropy : ∀ securityParameter,
      params.extraCount securityParameter =
        params.modulusExponent securityParameter *
          (2 ^ params.degreeExponent securityParameter) + securityParameter)
    (isPPT : RGSWAdversaryFamily params → Prop)
    (batchRLWEIsPPT : BatchRLWEAdversaryFamily params → Prop)
    (hReductionClosed : ∀ adversary, isPPT adversary →
      batchRLWEIsPPT (batchRLWEReduction params widening selectors adversary))
    (hSmudging : negligible (smudgingError params widening))
    (hBatchRLWE : (batchRLWESecurityGame params).secureAgainst batchRLWEIsPPT) :
    (rgswSecurityGame params widening).secureAgainst isPPT := by
  exact secureAgainst_of_negligible_errors_and_batchRLWE
    params widening selectors isPPT batchRLWEIsPPT hReductionClosed
    (selectorFailureError_negligible_of_entropyMargin
      params levelsPolynomial hLevels hEntropy)
    hSmudging hBatchRLWE

/-- **Asymptotic standalone `RGSW_S(-S)` security endpoint.**

The entropy-margin schedule and an exponentially large certified Gaussian window discharge both
explicit statistical terms.  What remains in the statement is exactly efficiency closure of the
complete selector compiler and ordinary batch-RLWE security. -/
theorem secureAgainst_of_entropyMargin_twoPowGaussian_and_batchRLWE
    (params : Parameters) (widening : WideningFamily params)
    (selectors : CompleteSelectorFamily params)
    (levelsPolynomial : Polynomial ℕ)
    (hLevels : ∀ securityParameter,
      params.levels securityParameter ≤ levelsPolynomial.eval securityParameter)
    (hEntropy : ∀ securityParameter,
      params.extraCount securityParameter =
        params.modulusExponent securityParameter *
          (2 ^ params.degreeExponent securityParameter) + securityParameter)
    (growth : SmudgingPolynomialGrowth params)
    (hwindowFits : ∀ securityParameter,
      ((2 ^ securityParameter : ℕ) : ℝ) ≤
        ModularGaussian.integerStddev
          (2 ^ params.modulusExponent securityParameter)
          (widening.alpha securityParameter))
    (hcertificate : negligible (fun securityParameter ↦
      (widening.certificate securityParameter).bound))
    (isPPT : RGSWAdversaryFamily params → Prop)
    (batchRLWEIsPPT : BatchRLWEAdversaryFamily params → Prop)
    (hReductionClosed : ∀ adversary, isPPT adversary →
      batchRLWEIsPPT (batchRLWEReduction params widening selectors adversary))
    (hBatchRLWE : (batchRLWESecurityGame params).secureAgainst batchRLWEIsPPT) :
    (rgswSecurityGame params widening).secureAgainst isPPT := by
  exact secureAgainst_of_entropyMargin_smudging_and_batchRLWE
    params widening selectors levelsPolynomial hLevels hEntropy
    isPPT batchRLWEIsPPT hReductionClosed
    (smudgingError_negligible_of_two_pow_window
      params widening growth hwindowFits hcertificate)
    hBatchRLWE

/-- **Average-case standalone `RGSW_S(-S)` security endpoint.**

An efficient anchored binary Ring-ISIS compiler with negligible random-instance failure, the
explicit two-power Gaussian widening schedule, and ordinary batch-RLWE security imply genuine
standalone `RGSW_S(-S)` security.  This is strictly weaker than demanding a selector that is
pointwise complete on every solvable instance. -/
theorem secureAgainst_of_efficientAnchoredBinaryISIS_twoPowGaussian_and_batchRLWE
    (params : Parameters) (widening : WideningFamily params)
    (isPPT : RGSWAdversaryFamily params → Prop)
    (batchRLWEIsPPT : BatchRLWEAdversaryFamily params → Prop)
    (compiler : EfficientAnchoredBinaryISIS
      params widening isPPT batchRLWEIsPPT)
    (growth : SmudgingPolynomialGrowth params)
    (hwindowFits : ∀ securityParameter,
      ((2 ^ securityParameter : ℕ) : ℝ) ≤
        ModularGaussian.integerStddev
          (2 ^ params.modulusExponent securityParameter)
          (widening.alpha securityParameter))
    (hcertificate : negligible (fun securityParameter ↦
      (widening.certificate securityParameter).bound))
    (hBatchRLWE : (batchRLWESecurityGame params).secureAgainst batchRLWEIsPPT) :
    (rgswSecurityGame params widening).secureAgainst isPPT := by
  exact secureAgainst_of_efficientAnchoredBinaryISIS_and_batchRLWE
    params widening isPPT batchRLWEIsPPT compiler
    (smudgingError_negligible_of_two_pow_window
      params widening growth hwindowFits hcertificate)
    hBatchRLWE

end

end FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.BinarySelectorSecurity.Asymptotic
