/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.RingSquareHiddenResidualCompiler
import FormalProof4FHE.TFHE.RingSquarePowerOfTwoLiftingProduction

/-!
# Production Hidden-Residual Security for `RGSW_S(-S)`

This file combines the fixed-modulus two-adic selector with the hidden-source-error compiler
normal form.  The selector-failure term is completely discharged by the recursive rank argument.
The remaining statistical premise is the exact distance after mixing over the random residual
`S * sum_i x_i e_i`, rather than a worst-case translation bound.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.PowerOfTwoLifting

noncomputable section

open BinaryPreimageExistence
open BinarySelectorSecurity

/-- The mask/secret prefix used by the concrete production selector. -/
abbrev ProductionMaskContext
    (depth degreeExponent slack levels : ℕ) (Secret : Type) :=
  HiddenResidual.MaskContext (ProductionRing depth degreeExponent) Secret levels
    (productionExtraCount depth degreeExponent slack + 1)

/-- Sample a production mask/secret prefix while retaining all source errors for the later hidden
residual mixture. -/
def productionMaskContextSampler
    (depth degreeExponent slack levels : ℕ) {Secret : Type}
    (secretSampler : ProbComp Secret) :
    ProbComp (ProductionMaskContext depth degreeExponent slack levels Secret) :=
  HiddenResidual.maskContextSampler (R := ProductionRing depth degreeExponent)
    levels (productionExtraCount depth degreeExponent slack + 1) secretSampler

/-- Public-mask success for the concrete lifting selectors in the hidden-residual normal form. -/
def ProductionMaskSelectorsSucceed
    (depth degreeExponent slack levels : ℕ)
    (gadget : Fin levels → ProductionRing depth degreeExponent)
    {Secret : Type}
    (context : ProductionMaskContext depth degreeExponent slack levels Secret) : Prop :=
  @HiddenResidual.ChallengeSelectorsSucceed
    (ProductionRing depth degreeExponent)
    (productionCommRing depth degreeExponent)
    levels (productionExtraCount depth degreeExponent slack + 1)
    gadget
    (binarySelectors
      (productionBitSelectors depth degreeExponent slack levels gadget))
    context.sourceChallenge

/-- The exact production statistical term.  The emitted target error is the convolution of the
narrow centered-binomial source law and the independent widening law. -/
noncomputable def productionHiddenResidualDistance
    (depth degreeExponent slack levels eta : ℕ)
    {Secret : Type} {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate
      (2 ^ (depth + 1)) alpha halpha)
    (embed : Secret → Fin 1 → ProductionRing depth degreeExponent)
    (gadget : Fin levels → ProductionRing depth degreeExponent)
    (context : ProductionMaskContext depth degreeExponent slack levels Secret) : ℝ :=
  let sourceErrorSampler := RLWE.CenteredBinomial.sampler
    (2 ^ (depth + 1)) (2 ^ degreeExponent) eta
  let wideningSampler := DiscreteGaussianSampler.ringSampler
    (2 ^ degreeExponent) certificate
  @HiddenResidual.hiddenResidualDistance
    (ProductionRing depth degreeExponent)
    Secret
    (productionCommRing depth degreeExponent)
    levels (productionExtraCount depth degreeExponent slack + 1)
    embed sourceErrorSampler
    (@Heterogeneous.convolutionSampler
      (ProductionRing depth degreeExponent)
      (productionCommRing depth degreeExponent).toAdd
      sourceErrorSampler wideningSampler)
    (binarySelectors
      (productionBitSelectors depth degreeExponent slack levels gadget))
    context

/-- The simpler analytic distance in which the target error is only the independent widening
component.  The narrow target component is removed by convolution contraction, not by a
worst-case shift bound. -/
noncomputable def productionWideningResidualDistance
    (depth degreeExponent slack levels eta : ℕ)
    {Secret : Type} {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate
      (2 ^ (depth + 1)) alpha halpha)
    (embed : Secret → Fin 1 → ProductionRing depth degreeExponent)
    (gadget : Fin levels → ProductionRing depth degreeExponent)
    (context : ProductionMaskContext depth degreeExponent slack levels Secret) : ℝ :=
  let sourceErrorSampler := RLWE.CenteredBinomial.sampler
    (2 ^ (depth + 1)) (2 ^ degreeExponent) eta
  let wideningSampler := DiscreteGaussianSampler.ringSampler
    (2 ^ degreeExponent) certificate
  @HiddenResidual.hiddenResidualDistance
    (ProductionRing depth degreeExponent)
    Secret
    (productionCommRing depth degreeExponent)
    levels (productionExtraCount depth degreeExponent slack + 1)
    embed sourceErrorSampler wideningSampler
    (binarySelectors
      (productionBitSelectors depth degreeExponent slack levels gadget))
    context

/-- Explicit finite `L²` target for the production random-residual convolution.  Unlike Pearson
chi-square, this remains total for compiled Gaussian ticket tables with support holes. -/
noncomputable def productionWideningResidualL2Loss
    (depth degreeExponent slack levels eta : ℕ)
    {Secret : Type} {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate
      (2 ^ (depth + 1)) alpha halpha)
    (embed : Secret → Fin 1 → ProductionRing depth degreeExponent)
    (gadget : Fin levels → ProductionRing depth degreeExponent)
    (context : ProductionMaskContext depth degreeExponent slack levels Secret) : ℝ :=
  let sourceErrorSampler := RLWE.CenteredBinomial.sampler
    (2 ^ (depth + 1)) (2 ^ degreeExponent) eta
  let wideningSampler := DiscreteGaussianSampler.ringSampler
    (2 ^ degreeExponent) certificate
  @HiddenResidual.hiddenResidualL2Loss
    (ProductionRing depth degreeExponent)
    Secret
    (productionCommRing depth degreeExponent)
    inferInstance
    levels (productionExtraCount depth degreeExponent slack + 1)
    embed sourceErrorSampler wideningSampler
    (binarySelectors
      (productionBitSelectors depth degreeExponent slack levels gadget))
    context

/-- The production widening-residual distance is bounded by the explicit finite `L²` sum. -/
theorem productionWideningResidualDistance_le_l2Loss
    (depth degreeExponent slack levels eta : ℕ)
    {Secret : Type} {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate
      (2 ^ (depth + 1)) alpha halpha)
    (embed : Secret → Fin 1 → ProductionRing depth degreeExponent)
    (gadget : Fin levels → ProductionRing depth degreeExponent)
    (context : ProductionMaskContext depth degreeExponent slack levels Secret) :
    productionWideningResidualDistance
        depth degreeExponent slack levels eta certificate embed gadget context ≤
      productionWideningResidualL2Loss
        depth degreeExponent slack levels eta certificate embed gadget context := by
  letI : CommRing (ProductionRing depth degreeExponent) :=
    productionCommRing depth degreeExponent
  simpa [productionWideningResidualDistance, productionWideningResidualL2Loss] using
    (HiddenResidual.hiddenResidualDistance_le_l2Loss
      (embed := embed)
      (sourceErrorSampler := RLWE.CenteredBinomial.sampler
        (2 ^ (depth + 1)) (2 ^ degreeExponent) eta)
      (targetErrorSampler := DiscreteGaussianSampler.ringSampler
        (2 ^ degreeExponent) certificate)
      (selectors := binarySelectors
        (productionBitSelectors depth degreeExponent slack levels gadget))
      context)

/-- The narrow centered-binomial component already present in each emitted target error can only
decrease the production hidden-residual distance. -/
theorem productionHiddenResidualDistance_le_widening
    (depth degreeExponent slack levels eta : ℕ)
    {Secret : Type} {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate
      (2 ^ (depth + 1)) alpha halpha)
    (embed : Secret → Fin 1 → ProductionRing depth degreeExponent)
    (gadget : Fin levels → ProductionRing depth degreeExponent)
    (context : ProductionMaskContext depth degreeExponent slack levels Secret) :
    productionHiddenResidualDistance
        depth degreeExponent slack levels eta certificate embed gadget context ≤
      productionWideningResidualDistance
        depth degreeExponent slack levels eta certificate embed gadget context := by
  letI : CommRing (ProductionRing depth degreeExponent) :=
    productionCommRing depth degreeExponent
  simpa [productionHiddenResidualDistance, productionWideningResidualDistance] using
    (HiddenResidual.hiddenResidualDistance_convolutionSampler_le_right
      (embed := embed)
      (sourceErrorSampler := RLWE.CenteredBinomial.sampler
        (2 ^ (depth + 1)) (2 ^ degreeExponent) eta)
      (commonErrorSampler := RLWE.CenteredBinomial.sampler
        (2 ^ (depth + 1)) (2 ^ degreeExponent) eta)
      (wideningSampler := DiscreteGaussianSampler.ringSampler
        (2 ^ degreeExponent) certificate)
      (selectors := binarySelectors
        (productionBitSelectors depth degreeExponent slack levels gadget))
      context)

/-- The ordinary narrow-noise batch-RLWE term generated by the concrete hidden compiler.  Naming
it fixes the production-ring dictionary once, avoiding ambiguity between equivalent native ring
presentations. -/
noncomputable def productionBatchRLWEAdvantage
    (depth degreeExponent slack levels eta : ℕ)
    {Secret : Type} {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate
      (2 ^ (depth + 1)) alpha halpha)
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → ProductionRing depth degreeExponent)
    (gadget : Fin levels → ProductionRing depth degreeExponent)
    (distinguisher : Full.Distinguisher
      (ProductionRing depth degreeExponent) levels) : ℝ :=
  letI : CommRing (ProductionRing depth degreeExponent) :=
    productionCommRing depth degreeExponent
  let extraCount := productionExtraCount depth degreeExponent slack
  let sourceErrorSampler := RLWE.CenteredBinomial.sampler
    (2 ^ (depth + 1)) (2 ^ degreeExponent) eta
  let wideningSampler := DiscreteGaussianSampler.ringSampler
    (2 ^ degreeExponent) certificate
  let targetErrorSampler :=
    @Heterogeneous.convolutionSampler
      (ProductionRing depth degreeExponent)
      (productionCommRing depth degreeExponent).toAdd
      sourceErrorSampler wideningSampler
  let selectors : Full.Selectors
      (ProductionRing depth degreeExponent) levels (extraCount + 1) :=
    binarySelectors
      (productionBitSelectors depth degreeExponent slack levels gadget)
  let samples := levels * (extraCount + 1) + TGSW.rowCount 1 levels
  @LearningWithErrors.advantage
    (Matrix (Fin 1) (Fin samples) (ProductionRing depth degreeExponent))
    Secret
    (Fin samples → ProductionRing depth degreeExponent)
    (@Pi.instAdd (Fin samples)
      (fun _index ↦ ProductionRing depth degreeExponent)
      (fun _index ↦ (productionCommRing depth degreeExponent).toAdd))
    (@FormalProof4FHE.LWE.embeddedBatchProblem
      (ProductionRing depth degreeExponent) Secret
      (productionCommRing depth degreeExponent).toSemiring
      inferInstance inferInstance
      1 samples secretSampler embed sourceErrorSampler)
    (@LWE.TwoBlock.convolutionReduction
      (ProductionRing depth degreeExponent) Secret
      (productionCommRing depth degreeExponent).toSemiring
      inferInstance inferInstance
      1 (levels * (extraCount + 1)) (TGSW.rowCount 1 levels)
      secretSampler embed sourceErrorSampler targetErrorSampler wideningSampler
      (@Heterogeneous.reduction
        (ProductionRing depth degreeExponent) Secret
        (productionCommRing depth degreeExponent)
        inferInstance inferInstance
        levels (extraCount + 1) secretSampler embed
        sourceErrorSampler targetErrorSampler selectors
        (@Full.restoreDistinguisher
          (ProductionRing depth degreeExponent)
          (productionCommRing depth degreeExponent).toAdd
          levels gadget distinguisher)))

/-- Binary challenge success implies the mask-only compiler predicate used by the hidden-residual
normal form. -/
theorem hiddenChallengeSelectorsSucceed_of_binary
    {R : Type} [CommRing R] {levels extraCount : ℕ}
    (gadget : Fin levels → R)
    (bitSelectors : Fin levels → BitSelector R extraCount)
    (challenge : Matrix (Fin 1) (Fin (levels * (extraCount + 1))) R)
    (hSuccess : BinarySelectorSecurity.ChallengeSelectorsSucceed
      gadget bitSelectors challenge) :
    HiddenResidual.ChallengeSelectorsSucceed gadget
      (binarySelectors bitSelectors) challenge := by
  intro level
  change SelectorSucceeds (gadget level)
    (binarySelectorWeights (bitSelectors level))
    (Full.sourceRowsAt (challenge, 0) level)
  apply selectorSucceeds_of_binarySelectorWeights_combination_eq
  rw [BinarySelectorSecurity.sourceMasks_sourceRowsAt_pair]
  exact hSuccess level

/-- The production selector's failure probability remains the same after source errors are moved
behind the mask/secret prefix. -/
theorem productionMaskContextSelectors_failure_toReal_le
    (depth degreeExponent slack levels : ℕ) {Secret : Type}
    (secretSampler : ProbComp Secret)
    (gadget : Fin levels → ProductionRing depth degreeExponent) :
    (Pr[(fun context :
          ProductionMaskContext depth degreeExponent slack levels Secret ↦
        ¬ ProductionMaskSelectorsSucceed
          depth degreeExponent slack levels gadget context) |
      productionMaskContextSampler
        depth degreeExponent slack levels secretSampler]).toReal ≤
      (levels : ℝ) * (depth + 1 : ℝ) *
        (2 / (2 : ℝ) ^ (slack + 1)) := by
  letI : CommRing (ProductionRing depth degreeExponent) :=
    productionCommRing depth degreeExponent
  let Extra := productionExtraCount depth degreeExponent slack
  let Ring := ProductionRing depth degreeExponent
  let Selectors : Full.Selectors Ring levels (Extra + 1) :=
    binarySelectors
      (productionBitSelectors depth degreeExponent slack levels gadget)
  have hPrefix := HiddenResidual.maskContextSelectors_failure_le_challenge
    (R := Ring) levels (Extra + 1) secretSampler gadget Selectors
  have hChallenge :
      Pr[(fun challenge : Matrix (Fin 1) (Fin (levels * (Extra + 1))) Ring ↦
          ¬ HiddenResidual.ChallengeSelectorsSucceed gadget Selectors challenge) |
        ($ᵗ Matrix (Fin 1) (Fin (levels * (Extra + 1))) Ring)] ≤
      Pr[(fun challenge : Matrix (Fin 1) (Fin (levels * (Extra + 1))) Ring ↦
          ¬ BinarySelectorSecurity.ChallengeSelectorsSucceed gadget
            (productionBitSelectors depth degreeExponent slack levels gadget)
            challenge) |
        ($ᵗ Matrix (Fin 1) (Fin (levels * (Extra + 1))) Ring)] := by
    apply probEvent_mono
    intro challenge _hChallenge hfailure hbinary
    exact hfailure
      (hiddenChallengeSelectorsSucceed_of_binary gadget
        (productionBitSelectors depth degreeExponent slack levels gadget)
        challenge hbinary)
  have hFailure := hPrefix.trans hChallenge
  have hFailureReal := ENNReal.toReal_mono probEvent_ne_top hFailure
  exact hFailureReal.trans
    (productionChallengeSelectors_failure_toReal_le
      depth degreeExponent slack levels gadget)

/-! ## Finite production theorem -/

set_option maxHeartbeats 3000000 in
/-- Genuine production `RGSW_S(-S)` security with the selector theorem fully instantiated and
the small-noise research obligation stated as a hidden random-residual distance. -/
theorem rgswMinusSecretAdvantage_centeredBinomial_hiddenResidual_le
    (depth degreeExponent slack levels eta : ℕ)
    {Secret : Type} {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate
      (2 ^ (depth + 1)) alpha halpha)
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → ProductionRing depth degreeExponent)
    (gadget : Fin levels → ProductionRing depth degreeExponent)
    (distinguisher : Full.Distinguisher
      (ProductionRing depth degreeExponent) levels)
    (bound : ℝ) (hBoundNonneg : 0 ≤ bound)
    (hResidual : ∀ context,
      context ∈ support
        (productionMaskContextSampler
          depth degreeExponent slack levels secretSampler) →
      ProductionMaskSelectorsSucceed
          depth degreeExponent slack levels gadget context →
      productionHiddenResidualDistance
          depth degreeExponent slack levels eta certificate embed gadget context ≤ bound) :
    let sourceErrorSampler := RLWE.CenteredBinomial.sampler
      (2 ^ (depth + 1)) (2 ^ degreeExponent) eta
    let wideningSampler := DiscreteGaussianSampler.ringSampler
      (2 ^ degreeExponent) certificate
    Full.rgswMinusSecretAdvantage levels secretSampler embed
        (@Heterogeneous.convolutionSampler
          (ProductionRing depth degreeExponent)
          (productionCommRing depth degreeExponent).toAdd
          sourceErrorSampler wideningSampler)
        gadget distinguisher ≤
      ((levels : ℝ) * (depth + 1 : ℝ) *
          (2 / (2 : ℝ) ^ (slack + 1)) + bound) +
        productionBatchRLWEAdvantage depth degreeExponent slack levels eta
          certificate secretSampler embed gadget distinguisher := by
  dsimp only
  letI : CommRing (ProductionRing depth degreeExponent) :=
    productionCommRing depth degreeExponent
  let sourceErrorSampler := RLWE.CenteredBinomial.sampler
    (2 ^ (depth + 1)) (2 ^ degreeExponent) eta
  let wideningSampler := DiscreteGaussianSampler.ringSampler
    (2 ^ degreeExponent) certificate
  let selectors : Full.Selectors
      (ProductionRing depth degreeExponent) levels
      (productionExtraCount depth degreeExponent slack + 1) :=
    binarySelectors
      (productionBitSelectors depth degreeExponent slack levels gadget)
  have hBase :=
    HiddenResidual.rgswMinusSecretAdvantage_le_convolution_failure_add_hiddenResidual_add_batchLWE
      levels (productionExtraCount depth degreeExponent slack + 1)
      secretSampler embed sourceErrorSampler wideningSampler gadget selectors
      distinguisher bound hBoundNonneg
      (by
        intro context hcontext hsuccess
        simpa [productionHiddenResidualDistance, sourceErrorSampler,
          wideningSampler, selectors] using
          (hResidual context hcontext hsuccess))
      (by simp [wideningSampler])
  have hFailure := productionMaskContextSelectors_failure_toReal_le
    depth degreeExponent slack levels secretSampler gadget
  have hFailure' :
      (Pr[(fun context : ProductionMaskContext
            depth degreeExponent slack levels Secret ↦
          ¬ HiddenResidual.ChallengeSelectorsSucceed gadget selectors
            context.sourceChallenge) |
        HiddenResidual.maskContextSampler
          (R := ProductionRing depth degreeExponent)
          levels (productionExtraCount depth degreeExponent slack + 1)
          secretSampler]).toReal ≤
        (levels : ℝ) * (depth + 1 : ℝ) *
          (2 / (2 : ℝ) ^ (slack + 1)) := by
    simpa [productionMaskContextSampler, ProductionMaskSelectorsSucceed,
      selectors] using hFailure
  calc
    _ ≤
        ((Pr[(fun context : ProductionMaskContext
              depth degreeExponent slack levels Secret ↦
            ¬ HiddenResidual.ChallengeSelectorsSucceed gadget selectors
              context.sourceChallenge) |
          HiddenResidual.maskContextSampler
            (R := ProductionRing depth degreeExponent)
            levels (productionExtraCount depth degreeExponent slack + 1)
            secretSampler]).toReal + bound) +
          productionBatchRLWEAdvantage depth degreeExponent slack levels eta
            certificate secretSampler embed gadget distinguisher := by
      simpa [productionBatchRLWEAdvantage, sourceErrorSampler,
        wideningSampler, selectors] using hBase
    _ ≤ _ := add_le_add (add_le_add hFailure' le_rfl) le_rfl

/-- Final finite reduction in the clean analytic form: it is enough to show that the widening
noise absorbs the *random* centered-binomial compiler residual.  The independent narrow component
of the emitted target error has already been removed by convolution contraction. -/
theorem rgswMinusSecretAdvantage_centeredBinomial_wideningResidual_le
    (depth degreeExponent slack levels eta : ℕ)
    {Secret : Type} {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate
      (2 ^ (depth + 1)) alpha halpha)
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → ProductionRing depth degreeExponent)
    (gadget : Fin levels → ProductionRing depth degreeExponent)
    (distinguisher : Full.Distinguisher
      (ProductionRing depth degreeExponent) levels)
    (bound : ℝ) (hBoundNonneg : 0 ≤ bound)
    (hWideningResidual : ∀ context,
      context ∈ support
        (productionMaskContextSampler
          depth degreeExponent slack levels secretSampler) →
      ProductionMaskSelectorsSucceed
          depth degreeExponent slack levels gadget context →
      productionWideningResidualDistance
          depth degreeExponent slack levels eta certificate embed gadget context ≤ bound) :
    let sourceErrorSampler := RLWE.CenteredBinomial.sampler
      (2 ^ (depth + 1)) (2 ^ degreeExponent) eta
    let wideningSampler := DiscreteGaussianSampler.ringSampler
      (2 ^ degreeExponent) certificate
    Full.rgswMinusSecretAdvantage levels secretSampler embed
        (@Heterogeneous.convolutionSampler
          (ProductionRing depth degreeExponent)
          (productionCommRing depth degreeExponent).toAdd
          sourceErrorSampler wideningSampler)
        gadget distinguisher ≤
      ((levels : ℝ) * (depth + 1 : ℝ) *
          (2 / (2 : ℝ) ^ (slack + 1)) + bound) +
        productionBatchRLWEAdvantage depth degreeExponent slack levels eta
          certificate secretSampler embed gadget distinguisher := by
  apply rgswMinusSecretAdvantage_centeredBinomial_hiddenResidual_le
    depth degreeExponent slack levels eta certificate secretSampler embed gadget
      distinguisher bound hBoundNonneg
  intro context hcontext hsuccess
  exact
    (productionHiddenResidualDistance_le_widening
      depth degreeExponent slack levels eta certificate embed gadget context).trans
      (hWideningResidual context hcontext hsuccess)

/-- Fully explicit second-moment interface for the production reduction.  Proving a uniform
small-noise bound for this finite `L²` expression closes the statistical term without revealing
the source errors. -/
theorem rgswMinusSecretAdvantage_centeredBinomial_wideningL2_le
    (depth degreeExponent slack levels eta : ℕ)
    {Secret : Type} {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate
      (2 ^ (depth + 1)) alpha halpha)
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → ProductionRing depth degreeExponent)
    (gadget : Fin levels → ProductionRing depth degreeExponent)
    (distinguisher : Full.Distinguisher
      (ProductionRing depth degreeExponent) levels)
    (bound : ℝ) (hBoundNonneg : 0 ≤ bound)
    (hWideningL2 : ∀ context,
      context ∈ support
        (productionMaskContextSampler
          depth degreeExponent slack levels secretSampler) →
      ProductionMaskSelectorsSucceed
          depth degreeExponent slack levels gadget context →
      productionWideningResidualL2Loss
          depth degreeExponent slack levels eta certificate embed gadget context ≤ bound) :
    let sourceErrorSampler := RLWE.CenteredBinomial.sampler
      (2 ^ (depth + 1)) (2 ^ degreeExponent) eta
    let wideningSampler := DiscreteGaussianSampler.ringSampler
      (2 ^ degreeExponent) certificate
    Full.rgswMinusSecretAdvantage levels secretSampler embed
        (@Heterogeneous.convolutionSampler
          (ProductionRing depth degreeExponent)
          (productionCommRing depth degreeExponent).toAdd
          sourceErrorSampler wideningSampler)
        gadget distinguisher ≤
      ((levels : ℝ) * (depth + 1 : ℝ) *
          (2 / (2 : ℝ) ^ (slack + 1)) + bound) +
        productionBatchRLWEAdvantage depth degreeExponent slack levels eta
          certificate secretSampler embed gadget distinguisher := by
  apply rgswMinusSecretAdvantage_centeredBinomial_wideningResidual_le
    depth degreeExponent slack levels eta certificate secretSampler embed gadget
      distinguisher bound hBoundNonneg
  intro context hcontext hsuccess
  exact
    (productionWideningResidualDistance_le_l2Loss
      depth degreeExponent slack levels eta certificate embed gadget context).trans
      (hWideningL2 context hcontext hsuccess)

end

end FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.PowerOfTwoLifting
