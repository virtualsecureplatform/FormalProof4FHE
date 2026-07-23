/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AsymptoticAdaptiveAugmentedCandidateView
import FormalProof4FHE.TFHE.CenteredBinomialGrowingNoiseCircularSearch
import FormalProof4FHE.TFHE.NativeAdaptiveShiftedCandidateEvaluator

/-!
# Growing-Noise TFHE from Public Augmented CircLWE

This module specializes the public `(BRK, KSK, input tape)` circular-security route to the
concrete growing centered-binomial family.  Its primary endpoints prove adaptive confidentiality
alone; separate convenience theorems may pair that result with the family's independently checked
probability-one Boolean refresh result.

The security-only interfaces expose public augmented CircLWE directly, reduce it through
paired-search accounting, or reduce it to one-coordinate native circular prediction plus explicit
statistical errors.  The zero-message branch is discharged by the existing ordinary joint-LWE
endpoint.  In particular, no correctness proposition occurs in the confidentiality reductions.
-/

namespace FormalProof4FHE.TFHE.CenteredBinomial.GrowingNoiseEndToEnd

open Encryption.Adaptive.Asymptotic

namespace AdaptivePublicCircular

abbrev PublicDistinguisherFamily :=
  Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.PublicDistinguisherFamily
    family.parameters

noncomputable abbrev publicCircularLWESecurityGame :=
  Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicCircularLWESecurityGame
    family.parameters

noncomputable abbrev publicZeroLWESecurityGame :=
  Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicZeroLWESecurityGame
    family.parameters

/-- Augmented paired-search solver families retain the bounded input-tape schedule. -/
abbrev AugmentedSearchSolverFamily :=
  Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedResidual.SearchSolverFamily
    family.parameters

/-- Averaged residual evaluator families for the growing centered-binomial source widths. -/
abbrev AugmentedResidualReductionFamily :=
  Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedResidual.ReductionFamily
    family.parameters errorWidth errorWidth

/-- General averaged candidate-view families, including direct whole-key diagonal isolation. -/
abbrev AugmentedCandidateReductionFamily :=
  Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.ReductionFamily
    family.parameters errorWidth errorWidth

/-- Averaged native evaluator families used without shared-context amplification. -/
abbrev AugmentedOneShotTransformerFamily :=
  Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.TransformerFamily
    family.parameters errorWidth errorWidth

/-- Direct native statistical certificate for one tape length and security parameter. -/
abbrev NativeDirectStatisticalCertificateAt
    (queryCount securityParameter : ℕ) :=
  Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery.AugmentedResidual.NativeShifted.DirectStatisticalCertificate
    (ringRank := family.parameters.ringRank securityParameter)
    (lweDimension := family.parameters.lweDimension securityParameter)
    (queryCount := queryCount)
    (decomposition securityParameter)
    (RLWE.CenteredBinomial.sampler
      (family.parameters.q securityParameter)
      (family.parameters.degree securityParameter)
      (errorWidth securityParameter))
    (family.parameters.ringErrorSampler securityParameter)
    (family.parameters.keySwitchErrorSampler securityParameter)
    (family.parameters.inputErrorSampler securityParameter)
    (family.parameters.keySwitchGadget securityParameter)

/-- Native statistical certificates uniformly available for every polynomial tape schedule. -/
abbrev NativeDirectStatisticalCertificateFamily :=
  (queryCount : ℕ → ℕ) → (securityParameter : ℕ) →
    NativeDirectStatisticalCertificateAt (queryCount securityParameter) securityParameter

/-- Install direct native certificates into the one-shot asymptotic transformer interface. -/
noncomputable def oneShotTransformerFamilyOfDirectCertificates
    (certificate : NativeDirectStatisticalCertificateFamily) :
    AugmentedOneShotTransformerFamily where
  transformerAt queryCount securityParameter :=
    (certificate queryCount securityParameter).toAveraged

/-- One-coordinate augmented circular predictors for the concrete family. -/
abbrev AugmentedCoordinatePredictorFamily :=
  Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.CoordinatePredictorFamily
    family.parameters

/-- The canonical scalar coordinate selected by the one-shot security reduction. -/
def referenceCoordinate (securityParameter : ℕ) :
    Fin (family.parameters.lweDimension securityParameter) :=
  ⟨0, by
    change 0 < ringDegree securityParameter
    exact ringDegree_pos securityParameter⟩

/-- Positive signed bias for predicting the canonical scalar coordinate. -/
noncomputable abbrev augmentedCoordinatePredictionSecurityGame :=
  Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.coordinatePredictionSecurityGame
    family.parameters errorWidth errorWidth

/-- Native correct/wrong statistical loss at the canonical scalar coordinate. -/
noncomputable abbrev augmentedOneShotStatisticalErrorSecurityGame
    (transformer : AugmentedOneShotTransformerFamily) :=
  Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.statisticalErrorSecurityGame
    family.parameters errorWidth errorWidth transformer referenceCoordinate

/-- Narrow augmented paired-search game used by the complete residual frontend. -/
noncomputable abbrev augmentedNarrowSearchSecurityGame :=
  Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedResidual.narrowSearchSecurityGame
    family.parameters errorWidth errorWidth

/-- Explicit residual, threshold, amplification, and coordinate-union loss for the growing
family's augmented public view. -/
noncomputable abbrev augmentedResidualLossSecurityGame
    (reduction : AugmentedResidualReductionFamily) :=
  Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedResidual.reductionLossSecurityGame
    family.parameters errorWidth errorWidth reduction keySwitchRecoveryLevel
      keySwitchRecoveryMargin

/-- Exact direct candidate-view, threshold, amplification, and coordinate-union loss. -/
noncomputable abbrev augmentedCandidateLossSecurityGame
    (reduction : AugmentedCandidateReductionFamily) :=
  Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.reductionLossSecurityGame
    family.parameters errorWidth errorWidth reduction keySwitchRecoveryLevel
      keySwitchRecoveryMargin

/-! ## Security-only endpoints -/

/-- Exact pointwise reduction with the native public circular term eliminated.  For the concrete
growing family, adaptive TFHE advantage is bounded by augmented paired-search success, the
explicit candidate-evaluator loss, and the three ordinary joint-LWE occurrences. -/
theorem securityGame_advantage_le_search_add_candidateLoss_add_three_jointLWE
    (reduction : AugmentedCandidateReductionFamily)
    (adversary : PolynomialQueryAdversary family.parameters)
    (securityParameter : ℕ) :
    (securityGame family.parameters).advantage adversary securityParameter ≤
      (augmentedNarrowSearchSecurityGame.advantage
          (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.toSearchSolverFamily
            family.parameters errorWidth errorWidth reduction keySwitchRecoveryLevel
            keySwitchRecoveryMargin
            (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
              family.parameters adversary)) securityParameter +
        (augmentedCandidateLossSecurityGame reduction).advantage
          (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
            family.parameters adversary) securityParameter) +
        (jointLWESecurityGame family.parameters).advantage
          (jointLWEReduction family.parameters adversary) securityParameter +
        (jointLWESecurityGame family.parameters).advantage
          (jointLWEReduction family.parameters adversary) securityParameter +
        (jointLWESecurityGame family.parameters).advantage
          (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
            family.parameters adversary) securityParameter := by
  let distinguisher :=
    Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
      family.parameters adversary
  have hTFHE :=
    Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.securityGame_advantage_le_publicCircular_add_three_jointLWE
      family.parameters adversary securityParameter
  have hCircular :=
    Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.publicCircularLWE_advantage_le_search_add_loss
      family.parameters errorWidth errorWidth reduction keySwitchRecoveryLevel
      keySwitchRecoveryMargin distinguisher securityParameter
  change (securityGame family.parameters).advantage adversary securityParameter ≤
    (publicCircularLWESecurityGame.advantage distinguisher securityParameter +
      (jointLWESecurityGame family.parameters).advantage
        (jointLWEReduction family.parameters adversary) securityParameter +
      (jointLWESecurityGame family.parameters).advantage
        (jointLWEReduction family.parameters adversary) securityParameter) +
      (jointLWESecurityGame family.parameters).advantage
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          family.parameters adversary) securityParameter at hTFHE
  calc
    _ ≤ (publicCircularLWESecurityGame.advantage distinguisher securityParameter +
          (jointLWESecurityGame family.parameters).advantage
            (jointLWEReduction family.parameters adversary) securityParameter +
          (jointLWESecurityGame family.parameters).advantage
            (jointLWEReduction family.parameters adversary) securityParameter) +
        (jointLWESecurityGame family.parameters).advantage
          (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
            family.parameters adversary) securityParameter := hTFHE
    _ ≤ _ := by
      exact add_le_add
        (add_le_add
          (add_le_add hCircular le_rfl) le_rfl) le_rfl

/-- **Pointwise security-only TFHE reduction to one-coordinate circular prediction.**

This endpoint avoids the generally non-negligible shared-cloud-key amplification term.  Its
native statistical cost is exactly the correct/wrong evaluator error for one scalar coordinate. -/
theorem securityGame_advantage_le_coordinatePrediction_add_statisticalError_add_three_jointLWE
    (transformer : AugmentedOneShotTransformerFamily)
    (adversary : PolynomialQueryAdversary family.parameters)
    (securityParameter : ℕ) :
    (securityGame family.parameters).advantage adversary securityParameter ≤
      (augmentedCoordinatePredictionSecurityGame.advantage
          (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
            family.parameters errorWidth errorWidth transformer referenceCoordinate
            (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
              family.parameters adversary)) securityParameter +
        (augmentedOneShotStatisticalErrorSecurityGame transformer).advantage
          (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
            family.parameters adversary) securityParameter) +
        (jointLWESecurityGame family.parameters).advantage
          (jointLWEReduction family.parameters adversary) securityParameter +
        (jointLWESecurityGame family.parameters).advantage
          (jointLWEReduction family.parameters adversary) securityParameter +
        (jointLWESecurityGame family.parameters).advantage
          (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
            family.parameters adversary) securityParameter := by
  let distinguisher :=
    Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
      family.parameters adversary
  have hTFHE :=
    Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.securityGame_advantage_le_publicCircular_add_three_jointLWE
      family.parameters adversary securityParameter
  have hCircular :=
    Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.publicCircularLWE_advantage_le_coordinatePrediction_add_error
      family.parameters errorWidth errorWidth transformer referenceCoordinate distinguisher
        securityParameter
  change (securityGame family.parameters).advantage adversary securityParameter ≤
    (publicCircularLWESecurityGame.advantage distinguisher securityParameter +
      (jointLWESecurityGame family.parameters).advantage
        (jointLWEReduction family.parameters adversary) securityParameter +
      (jointLWESecurityGame family.parameters).advantage
        (jointLWEReduction family.parameters adversary) securityParameter) +
      (jointLWESecurityGame family.parameters).advantage
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          family.parameters adversary) securityParameter at hTFHE
  calc
    _ ≤ (publicCircularLWESecurityGame.advantage distinguisher securityParameter +
          (jointLWESecurityGame family.parameters).advantage
            (jointLWEReduction family.parameters adversary) securityParameter +
          (jointLWESecurityGame family.parameters).advantage
            (jointLWEReduction family.parameters adversary) securityParameter) +
        (jointLWESecurityGame family.parameters).advantage
          (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
            family.parameters adversary) securityParameter := hTFHE
    _ ≤ _ := by
      exact add_le_add
        (add_le_add (add_le_add hCircular le_rfl) le_rfl) le_rfl

/-- Security-only specialization with both public circular branches left explicit. -/
theorem secureAgainst_of_publicCircular_zero_and_jointLWE
    (isPPT : PolynomialQueryAdversary family.parameters → Prop)
    (publicIsPPT : PublicDistinguisherFamily → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily family.parameters → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          family.parameters adversary))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT (jointLWEReduction family.parameters adversary))
    (hCircular : publicCircularLWESecurityGame.secureAgainst publicIsPPT)
    (hZero : publicZeroLWESecurityGame.secureAgainst publicIsPPT)
    (hJointLWE : (jointLWESecurityGame family.parameters).secureAgainst jointLWEIsPPT) :
    (securityGame family.parameters).secureAgainst isPPT :=
  Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.secureAgainst_of_publicCircular_zero_and_jointLWE
    family.parameters isPPT publicIsPPT jointLWEIsPPT hPublicClosed
    hJointLWEClosed hCircular hZero hJointLWE

/-- Security-only specialization with public augmented CircLWE as the sole circular premise. -/
theorem secureAgainst_of_publicCircular_and_jointLWE
    (isPPT : PolynomialQueryAdversary family.parameters → Prop)
    (publicIsPPT : PublicDistinguisherFamily → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily family.parameters → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          family.parameters adversary))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT (jointLWEReduction family.parameters adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          family.parameters adversary))
    (hCircular : publicCircularLWESecurityGame.secureAgainst publicIsPPT)
    (hJointLWE : (jointLWESecurityGame family.parameters).secureAgainst jointLWEIsPPT) :
    (securityGame family.parameters).secureAgainst isPPT :=
  Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.secureAgainst_of_publicCircular_and_jointLWE
    family.parameters isPPT publicIsPPT jointLWEIsPPT hPublicClosed
    hJointLWEClosed hUniformJointLWEClosed hCircular hJointLWE

/-- Security-only TFHE endpoint from augmented residual search-to-decision. -/
theorem secureAgainst_of_search_residual_and_jointLWE
    (reduction : AugmentedResidualReductionFamily)
    (isPPT : PolynomialQueryAdversary family.parameters → Prop)
    (publicIsPPT : PublicDistinguisherFamily → Prop)
    (solverIsPPT : AugmentedSearchSolverFamily → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily family.parameters → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          family.parameters adversary))
    (hSearchClosed : ∀ distinguisher, publicIsPPT distinguisher →
      solverIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedResidual.toSearchSolverFamily
          family.parameters errorWidth errorWidth reduction keySwitchRecoveryLevel
          keySwitchRecoveryMargin distinguisher))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT (jointLWEReduction family.parameters adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          family.parameters adversary))
    (hSearch : augmentedNarrowSearchSecurityGame.secureAgainst solverIsPPT)
    (hResidualLoss :
      (augmentedResidualLossSecurityGame reduction).secureAgainst publicIsPPT)
    (hJointLWE : (jointLWESecurityGame family.parameters).secureAgainst jointLWEIsPPT) :
    (securityGame family.parameters).secureAgainst isPPT := by
  have hCircular : publicCircularLWESecurityGame.secureAgainst publicIsPPT :=
    Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedResidual.publicCircularLWESecurityGame_secureAgainst_of_search_and_loss
      family.parameters errorWidth errorWidth reduction keySwitchRecoveryLevel
      keySwitchRecoveryMargin publicIsPPT solverIsPPT hSearchClosed hSearch hResidualLoss
  exact secureAgainst_of_publicCircular_and_jointLWE
    isPPT publicIsPPT jointLWEIsPPT hPublicClosed hJointLWEClosed
    hUniformJointLWEClosed hCircular hJointLWE

/-- **Security-only TFHE endpoint from native candidate evaluation.**

Narrow augmented paired-search hardness, negligible direct candidate-view loss, and ordinary
joint LWE imply adaptive TFHE confidentiality.  No correctness proposition occurs in the
statement or proof. -/
theorem secureAgainst_of_search_candidate_and_jointLWE
    (reduction : AugmentedCandidateReductionFamily)
    (isPPT : PolynomialQueryAdversary family.parameters → Prop)
    (publicIsPPT : PublicDistinguisherFamily → Prop)
    (solverIsPPT : AugmentedSearchSolverFamily → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily family.parameters → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          family.parameters adversary))
    (hSearchClosed : ∀ distinguisher, publicIsPPT distinguisher →
      solverIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.toSearchSolverFamily
          family.parameters errorWidth errorWidth reduction keySwitchRecoveryLevel
          keySwitchRecoveryMargin distinguisher))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT (jointLWEReduction family.parameters adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          family.parameters adversary))
    (hSearch : augmentedNarrowSearchSecurityGame.secureAgainst solverIsPPT)
    (hCandidateLoss :
      (augmentedCandidateLossSecurityGame reduction).secureAgainst publicIsPPT)
    (hJointLWE : (jointLWESecurityGame family.parameters).secureAgainst jointLWEIsPPT) :
    (securityGame family.parameters).secureAgainst isPPT := by
  have hCircular : publicCircularLWESecurityGame.secureAgainst publicIsPPT :=
    Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.publicCircularLWESecurityGame_secureAgainst_of_search_and_loss
      family.parameters errorWidth errorWidth reduction keySwitchRecoveryLevel
      keySwitchRecoveryMargin publicIsPPT solverIsPPT hSearchClosed hSearch hCandidateLoss
  exact secureAgainst_of_publicCircular_and_jointLWE
    isPPT publicIsPPT jointLWEIsPPT hPublicClosed hJointLWEClosed
    hUniformJointLWEClosed hCircular hJointLWE

/-- **Security-only TFHE from one-coordinate circular prediction hardness.**

Negligible prediction bias, negligible one-coordinate native evaluator error, and ordinary joint
LWE imply adaptive TFHE confidentiality.  Correctness and shared-context amplification are absent
from the statement. -/
theorem secureAgainst_of_coordinatePrediction_and_statisticalError_and_jointLWE
    (transformer : AugmentedOneShotTransformerFamily)
    (isPPT : PolynomialQueryAdversary family.parameters → Prop)
    (publicIsPPT : PublicDistinguisherFamily → Prop)
    (predictorIsPPT : AugmentedCoordinatePredictorFamily → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily family.parameters → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          family.parameters adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          family.parameters errorWidth errorWidth transformer referenceCoordinate
          distinguisher))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT (jointLWEReduction family.parameters adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          family.parameters adversary))
    (hPrediction : augmentedCoordinatePredictionSecurityGame.secureAgainst predictorIsPPT)
    (hStatisticalError :
      (augmentedOneShotStatisticalErrorSecurityGame transformer).secureAgainst publicIsPPT)
    (hJointLWE : (jointLWESecurityGame family.parameters).secureAgainst jointLWEIsPPT) :
    (securityGame family.parameters).secureAgainst isPPT := by
  have hCircular : publicCircularLWESecurityGame.secureAgainst publicIsPPT :=
    Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.publicCircularLWESecurityGame_secureAgainst_of_coordinatePrediction_and_error
      family.parameters errorWidth errorWidth transformer referenceCoordinate publicIsPPT
        predictorIsPPT hPredictorClosed hPrediction hStatisticalError
  exact secureAgainst_of_publicCircular_and_jointLWE
    isPPT publicIsPPT jointLWEIsPPT hPublicClosed hJointLWEClosed
    hUniformJointLWEClosed hCircular hJointLWE

/-- **Direct-certificate security-only endpoint.**

This version exposes exactly the two remaining native statistical sequences from the executable
shifted evaluator.  Their componentwise negligibility, one-coordinate circular-prediction
hardness, and ordinary joint LWE imply adaptive TFHE confidentiality. -/
theorem secureAgainst_of_directCertificates_coordinatePrediction_and_jointLWE
    (certificate : NativeDirectStatisticalCertificateFamily)
    (isPPT : PolynomialQueryAdversary family.parameters → Prop)
    (publicIsPPT : PublicDistinguisherFamily → Prop)
    (predictorIsPPT : AugmentedCoordinatePredictorFamily → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily family.parameters → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          family.parameters adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          family.parameters errorWidth errorWidth
          (oneShotTransformerFamilyOfDirectCertificates certificate) referenceCoordinate
          distinguisher))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT (jointLWEReduction family.parameters adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          family.parameters adversary))
    (hPrediction : augmentedCoordinatePredictionSecurityGame.secureAgainst predictorIsPPT)
    (hCorrect : ∀ distinguisher, publicIsPPT distinguisher →
      negligible (fun securityParameter ↦ ENNReal.ofReal
        ((certificate distinguisher.queryCount securityParameter).correctError
          (referenceCoordinate securityParameter))))
    (hFreshness : ∀ distinguisher, publicIsPPT distinguisher →
      negligible (fun securityParameter ↦ ENNReal.ofReal
        ((certificate distinguisher.queryCount securityParameter).freshnessError
          (referenceCoordinate securityParameter))))
    (hJointLWE : (jointLWESecurityGame family.parameters).secureAgainst jointLWEIsPPT) :
    (securityGame family.parameters).secureAgainst isPPT := by
  let transformer := oneShotTransformerFamilyOfDirectCertificates certificate
  have hStatisticalError :
      (augmentedOneShotStatisticalErrorSecurityGame transformer).secureAgainst
        publicIsPPT := by
    apply Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.statisticalErrorSecurityGame_secureAgainst_of_components
      family.parameters errorWidth errorWidth transformer referenceCoordinate publicIsPPT
    · intro distinguisher hdistinguisher
      simpa [transformer, oneShotTransformerFamilyOfDirectCertificates] using
        hCorrect distinguisher hdistinguisher
    · intro distinguisher hdistinguisher
      simpa [transformer, oneShotTransformerFamilyOfDirectCertificates] using
        hFreshness distinguisher hdistinguisher
  exact secureAgainst_of_coordinatePrediction_and_statisticalError_and_jointLWE transformer
    isPPT publicIsPPT predictorIsPPT jointLWEIsPPT hPublicClosed hPredictorClosed
    hJointLWEClosed hUniformJointLWEClosed hPrediction hStatisticalError hJointLWE

/-- Publicly evaluated TFHE confidentiality from the same circular-search decomposition.  The
evaluation compiler has zero advantage loss; its sole additional obligation is preservation of
the selected efficient-adversary class. -/
theorem evaluationSecureAgainst_of_search_candidate_and_jointLWE
    {Output : Type}
    (evaluate : PublicEvaluatorFamily (Output := Output) family.parameters)
    (reduction : AugmentedCandidateReductionFamily)
    (baseIsPPT : PolynomialQueryAdversary family.parameters → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary (Output := Output) family.parameters → Prop)
    (publicIsPPT : PublicDistinguisherFamily → Prop)
    (solverIsPPT : AugmentedSearchSolverFamily → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily family.parameters → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT (compileEvaluationAdversary family.parameters evaluate adversary))
    (hPublicClosed : ∀ adversary, baseIsPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          family.parameters adversary))
    (hSearchClosed : ∀ distinguisher, publicIsPPT distinguisher →
      solverIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.toSearchSolverFamily
          family.parameters errorWidth errorWidth reduction keySwitchRecoveryLevel
          keySwitchRecoveryMargin distinguisher))
    (hJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT (jointLWEReduction family.parameters adversary))
    (hUniformJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          family.parameters adversary))
    (hSearch : augmentedNarrowSearchSecurityGame.secureAgainst solverIsPPT)
    (hCandidateLoss :
      (augmentedCandidateLossSecurityGame reduction).secureAgainst publicIsPPT)
    (hJointLWE : (jointLWESecurityGame family.parameters).secureAgainst jointLWEIsPPT) :
    (evaluationSecurityGame family.parameters evaluate).secureAgainst evaluationIsPPT := by
  apply evaluationSecureAgainst_of_security
    family.parameters evaluate baseIsPPT evaluationIsPPT hEvaluationClosed
  exact secureAgainst_of_search_candidate_and_jointLWE reduction
    baseIsPPT publicIsPPT solverIsPPT jointLWEIsPPT hPublicClosed hSearchClosed
    hJointLWEClosed hUniformJointLWEClosed hSearch hCandidateLoss hJointLWE

/-- Publicly evaluated TFHE confidentiality from the one-coordinate prediction endpoint.  Public
evaluation has exactly zero additional advantage loss. -/
theorem evaluationSecureAgainst_of_coordinatePrediction_and_statisticalError_and_jointLWE
    {Output : Type}
    (evaluate : PublicEvaluatorFamily (Output := Output) family.parameters)
    (transformer : AugmentedOneShotTransformerFamily)
    (baseIsPPT : PolynomialQueryAdversary family.parameters → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary (Output := Output) family.parameters → Prop)
    (publicIsPPT : PublicDistinguisherFamily → Prop)
    (predictorIsPPT : AugmentedCoordinatePredictorFamily → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily family.parameters → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT (compileEvaluationAdversary family.parameters evaluate adversary))
    (hPublicClosed : ∀ adversary, baseIsPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          family.parameters adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          family.parameters errorWidth errorWidth transformer referenceCoordinate
          distinguisher))
    (hJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT (jointLWEReduction family.parameters adversary))
    (hUniformJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          family.parameters adversary))
    (hPrediction : augmentedCoordinatePredictionSecurityGame.secureAgainst predictorIsPPT)
    (hStatisticalError :
      (augmentedOneShotStatisticalErrorSecurityGame transformer).secureAgainst publicIsPPT)
    (hJointLWE : (jointLWESecurityGame family.parameters).secureAgainst jointLWEIsPPT) :
    (evaluationSecurityGame family.parameters evaluate).secureAgainst evaluationIsPPT := by
  apply evaluationSecureAgainst_of_security
    family.parameters evaluate baseIsPPT evaluationIsPPT hEvaluationClosed
  exact secureAgainst_of_coordinatePrediction_and_statisticalError_and_jointLWE transformer
    baseIsPPT publicIsPPT predictorIsPPT jointLWEIsPPT hPublicClosed hPredictorClosed
    hJointLWEClosed hUniformJointLWEClosed hPrediction hStatisticalError hJointLWE

/-- Publicly evaluated TFHE confidentiality directly from native one-shot certificates.  The
certificate's selected-coordinate correct and freshness errors are the only statistical
premises, and public evaluation adds no advantage loss. -/
theorem evaluationSecureAgainst_of_directCertificates_coordinatePrediction_and_jointLWE
    {Output : Type}
    (evaluate : PublicEvaluatorFamily (Output := Output) family.parameters)
    (certificate : NativeDirectStatisticalCertificateFamily)
    (baseIsPPT : PolynomialQueryAdversary family.parameters → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary (Output := Output) family.parameters → Prop)
    (publicIsPPT : PublicDistinguisherFamily → Prop)
    (predictorIsPPT : AugmentedCoordinatePredictorFamily → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily family.parameters → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT (compileEvaluationAdversary family.parameters evaluate adversary))
    (hPublicClosed : ∀ adversary, baseIsPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          family.parameters adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          family.parameters errorWidth errorWidth
          (oneShotTransformerFamilyOfDirectCertificates certificate) referenceCoordinate
          distinguisher))
    (hJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT (jointLWEReduction family.parameters adversary))
    (hUniformJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          family.parameters adversary))
    (hPrediction : augmentedCoordinatePredictionSecurityGame.secureAgainst predictorIsPPT)
    (hCorrect : ∀ distinguisher, publicIsPPT distinguisher →
      negligible (fun securityParameter ↦ ENNReal.ofReal
        ((certificate distinguisher.queryCount securityParameter).correctError
          (referenceCoordinate securityParameter))))
    (hFreshness : ∀ distinguisher, publicIsPPT distinguisher →
      negligible (fun securityParameter ↦ ENNReal.ofReal
        ((certificate distinguisher.queryCount securityParameter).freshnessError
          (referenceCoordinate securityParameter))))
    (hJointLWE : (jointLWESecurityGame family.parameters).secureAgainst jointLWEIsPPT) :
    (evaluationSecurityGame family.parameters evaluate).secureAgainst evaluationIsPPT := by
  apply evaluationSecureAgainst_of_security
    family.parameters evaluate baseIsPPT evaluationIsPPT hEvaluationClosed
  exact secureAgainst_of_directCertificates_coordinatePrediction_and_jointLWE certificate
    baseIsPPT publicIsPPT predictorIsPPT jointLWEIsPPT hPublicClosed hPredictorClosed
    hJointLWEClosed hUniformJointLWEClosed hPrediction hCorrect hFreshness hJointLWE

/-- **Concrete growing-noise adaptive TFHE endpoint with a public circular premise.**

Negligibility of the two public augmented BRK games and ordinary joint LWE gives adaptive
confidentiality, while functional refresh correctness holds unconditionally for the same family. -/
theorem secureAgainst_and_refreshCorrect_of_publicCircular_zero_and_jointLWE
    (isPPT : PolynomialQueryAdversary family.parameters → Prop)
    (publicIsPPT : PublicDistinguisherFamily → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily family.parameters → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          family.parameters adversary))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT (jointLWEReduction family.parameters adversary))
    (hCircular : publicCircularLWESecurityGame.secureAgainst publicIsPPT)
    (hZero : publicZeroLWESecurityGame.secureAgainst publicIsPPT)
    (hJointLWE : (jointLWESecurityGame family.parameters).secureAgainst jointLWEIsPPT) :
    (securityGame family.parameters).secureAgainst isPPT ∧ RefreshCorrect := by
  constructor
  · exact
      Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.secureAgainst_of_publicCircular_zero_and_jointLWE
        family.parameters isPPT publicIsPPT jointLWEIsPPT hPublicClosed
        hJointLWEClosed hCircular hZero hJointLWE
  · exact refreshCorrect

/-- **Preferred growing-noise endpoint.** Public augmented CircLWE is the only circular premise;
the zero-side branch is discharged by ordinary joint LWE, and probability-one refresh remains
checked for the same parameters. -/
theorem secureAgainst_and_refreshCorrect_of_publicCircular_and_jointLWE
    (isPPT : PolynomialQueryAdversary family.parameters → Prop)
    (publicIsPPT : PublicDistinguisherFamily → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily family.parameters → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          family.parameters adversary))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT (jointLWEReduction family.parameters adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          family.parameters adversary))
    (hCircular : publicCircularLWESecurityGame.secureAgainst publicIsPPT)
    (hJointLWE : (jointLWESecurityGame family.parameters).secureAgainst jointLWEIsPPT) :
    (securityGame family.parameters).secureAgainst isPPT ∧ RefreshCorrect := by
  constructor
  · exact
      Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.secureAgainst_of_publicCircular_and_jointLWE
        family.parameters isPPT publicIsPPT jointLWEIsPPT hPublicClosed
        hJointLWEClosed hUniformJointLWEClosed hCircular hJointLWE
  · exact refreshCorrect

/-- **Growing-noise adaptive TFHE from augmented residual search-to-decision.**

The public CircLWE premise of the preferred theorem is discharged by the averaged residual
candidate evaluator over `(BRK, KSK, tape)`.  The remaining computational hypotheses are narrow
augmented paired-search hardness, negligibility of the evaluator's explicit loss, and ordinary
joint LWE for the zero branch. -/
theorem secureAgainst_and_refreshCorrect_of_search_residual_and_jointLWE
    (reduction : AugmentedResidualReductionFamily)
    (isPPT : PolynomialQueryAdversary family.parameters → Prop)
    (publicIsPPT : PublicDistinguisherFamily → Prop)
    (solverIsPPT : AugmentedSearchSolverFamily → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily family.parameters → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          family.parameters adversary))
    (hSearchClosed : ∀ distinguisher, publicIsPPT distinguisher →
      solverIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedResidual.toSearchSolverFamily
          family.parameters errorWidth errorWidth reduction keySwitchRecoveryLevel
          keySwitchRecoveryMargin distinguisher))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT (jointLWEReduction family.parameters adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          family.parameters adversary))
    (hSearch : augmentedNarrowSearchSecurityGame.secureAgainst solverIsPPT)
    (hResidualLoss :
      (augmentedResidualLossSecurityGame reduction).secureAgainst publicIsPPT)
    (hJointLWE : (jointLWESecurityGame family.parameters).secureAgainst jointLWEIsPPT) :
    (securityGame family.parameters).secureAgainst isPPT ∧ RefreshCorrect := by
  have hCircular : publicCircularLWESecurityGame.secureAgainst publicIsPPT :=
    Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedResidual.publicCircularLWESecurityGame_secureAgainst_of_search_and_loss
      family.parameters errorWidth errorWidth reduction keySwitchRecoveryLevel
      keySwitchRecoveryMargin publicIsPPT solverIsPPT hSearchClosed hSearch hResidualLoss
  exact secureAgainst_and_refreshCorrect_of_publicCircular_and_jointLWE
    isPPT publicIsPPT jointLWEIsPPT hPublicClosed hJointLWEClosed
    hUniformJointLWEClosed hCircular hJointLWE

/-- **Growing-noise adaptive TFHE from general averaged candidate evaluation.**

This is the endpoint consumed by the native whole-key diagonal-isolation certificate.  It removes
the residual-witness restriction: narrow augmented paired-search hardness, negligible direct
candidate-view loss, and ordinary joint LWE imply adaptive confidentiality and the already checked
probability-one refresh theorem. -/
theorem secureAgainst_and_refreshCorrect_of_search_candidate_and_jointLWE
    (reduction : AugmentedCandidateReductionFamily)
    (isPPT : PolynomialQueryAdversary family.parameters → Prop)
    (publicIsPPT : PublicDistinguisherFamily → Prop)
    (solverIsPPT : AugmentedSearchSolverFamily → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily family.parameters → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          family.parameters adversary))
    (hSearchClosed : ∀ distinguisher, publicIsPPT distinguisher →
      solverIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.toSearchSolverFamily
          family.parameters errorWidth errorWidth reduction keySwitchRecoveryLevel
          keySwitchRecoveryMargin distinguisher))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT (jointLWEReduction family.parameters adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          family.parameters adversary))
    (hSearch : augmentedNarrowSearchSecurityGame.secureAgainst solverIsPPT)
    (hCandidateLoss :
      (augmentedCandidateLossSecurityGame reduction).secureAgainst publicIsPPT)
    (hJointLWE : (jointLWESecurityGame family.parameters).secureAgainst jointLWEIsPPT) :
    (securityGame family.parameters).secureAgainst isPPT ∧ RefreshCorrect := by
  have hCircular : publicCircularLWESecurityGame.secureAgainst publicIsPPT :=
    Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.publicCircularLWESecurityGame_secureAgainst_of_search_and_loss
      family.parameters errorWidth errorWidth reduction keySwitchRecoveryLevel
      keySwitchRecoveryMargin publicIsPPT solverIsPPT hSearchClosed hSearch hCandidateLoss
  exact secureAgainst_and_refreshCorrect_of_publicCircular_and_jointLWE
    isPPT publicIsPPT jointLWEIsPPT hPublicClosed hJointLWEClosed
    hUniformJointLWEClosed hCircular hJointLWE

end AdaptivePublicCircular

end FormalProof4FHE.TFHE.CenteredBinomial.GrowingNoiseEndToEnd
