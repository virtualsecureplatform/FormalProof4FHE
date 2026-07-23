/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AsymptoticAdaptiveAugmentedResidualCandidateView

/-!
# Asymptotic Public Augmented CircLWE from General Candidate Evaluation

This module lifts the general averaged candidate-view reduction for the complete adaptive public
view `(BRK, KSK, bounded input tape)` to security-parameter families.  Unlike the residual-only
adapter, it accepts any checked `AveragedCandidateViewTransformerReduction`, including the direct
statistical certificate obtained from whole-key diagonal isolation.
-/

open ENNReal OracleComp

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate

open FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery
open FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery

/-- Reuse the query-bounded augmented paired-search solver family. -/
abbrev SearchSolverFamily {Message : Type} (params : Parameters Message) :=
  AugmentedResidual.SearchSolverFamily params

/-- Parameter-indexed general averaged candidate reductions, uniformly available for every
bounded input-tape schedule. -/
structure ReductionFamily {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (sourceRingEta sourceKeySwitchEta : ℕ → ℕ) where
  reductionAt : (queryCount : ℕ → ℕ) → (securityParameter : ℕ) →
    AveragedCandidateViewTransformerReduction
      (params.q securityParameter)
      (params.degree securityParameter)
      (params.ringRank securityParameter)
      (params.tgswLevels securityParameter)
      (params.lweDimension securityParameter)
      (params.keySwitchLevels securityParameter)
      (queryCount securityParameter)
      (sourceRingEta securityParameter)
      (sourceKeySwitchEta securityParameter)
      (params.inputErrorSampler securityParameter)
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)

/-- Reuse the exact narrow augmented paired-search game. -/
noncomputable abbrev narrowSearchSecurityGame {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (sourceRingEta sourceKeySwitchEta : ℕ → ℕ) :=
  AugmentedResidual.narrowSearchSecurityGame params sourceRingEta sourceKeySwitchEta

/-- The finite paired-secret reduction selected for one public distinguisher schedule and one
security parameter. -/
noncomputable def pairedReductionAt {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (sourceRingEta sourceKeySwitchEta : ℕ → ℕ)
    (reduction : ReductionFamily params sourceRingEta sourceKeySwitchEta)
    (level : (securityParameter : ℕ) →
      Fin (params.keySwitchLevels securityParameter))
    (hmargin : ∀ securityParameter,
      2 * sourceKeySwitchEta securityParameter <
        BootstrappingCorrectness.centeredDistance 0
          (params.keySwitchGadget securityParameter (level securityParameter)))
    (distinguisher : PublicDistinguisherFamily params)
    (securityParameter : ℕ) :=
  (reduction.reductionAt distinguisher.queryCount securityParameter).toPairedSecretReduction
    (level securityParameter) (hmargin securityParameter)

/-- Apply the general candidate reduction pointwise while retaining the public distinguisher's
polynomial query schedule. -/
noncomputable def toSearchSolverFamily {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (sourceRingEta sourceKeySwitchEta : ℕ → ℕ)
    (reduction : ReductionFamily params sourceRingEta sourceKeySwitchEta)
    (level : (securityParameter : ℕ) →
      Fin (params.keySwitchLevels securityParameter))
    (hmargin : ∀ securityParameter,
      2 * sourceKeySwitchEta securityParameter <
        BootstrappingCorrectness.centeredDistance 0
          (params.keySwitchGadget securityParameter (level securityParameter)))
    (distinguisher : PublicDistinguisherFamily params) :
    SearchSolverFamily params where
  queryCount := distinguisher.queryCount
  queryPolynomial := distinguisher.queryPolynomial
  queryCount_le := distinguisher.queryCount_le
  run securityParameter :=
    (pairedReductionAt params sourceRingEta sourceKeySwitchEta reduction level hmargin
      distinguisher securityParameter).toSolver (distinguisher.run securityParameter)

/-- Exact candidate-view, threshold, amplification, and coordinate-union loss. -/
noncomputable def reductionLossSecurityGame {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (sourceRingEta sourceKeySwitchEta : ℕ → ℕ)
    (reduction : ReductionFamily params sourceRingEta sourceKeySwitchEta)
    (level : (securityParameter : ℕ) →
      Fin (params.keySwitchLevels securityParameter))
    (hmargin : ∀ securityParameter,
      2 * sourceKeySwitchEta securityParameter <
        BootstrappingCorrectness.centeredDistance 0
          (params.keySwitchGadget securityParameter (level securityParameter))) :
    SecurityGame (PublicDistinguisherFamily params) where
  advantage distinguisher securityParameter := ENNReal.ofReal
    ((pairedReductionAt params sourceRingEta sourceKeySwitchEta reduction level hmargin
      distinguisher securityParameter).loss (distinguisher.run securityParameter))

/-- Pointwise augmented search-to-decision accounting for a general averaged candidate view. -/
theorem publicCircularLWE_advantage_le_search_add_loss {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (sourceRingEta sourceKeySwitchEta : ℕ → ℕ)
    (reduction : ReductionFamily params sourceRingEta sourceKeySwitchEta)
    (level : (securityParameter : ℕ) →
      Fin (params.keySwitchLevels securityParameter))
    (hmargin : ∀ securityParameter,
      2 * sourceKeySwitchEta securityParameter <
        BootstrappingCorrectness.centeredDistance 0
          (params.keySwitchGadget securityParameter (level securityParameter)))
    (distinguisher : PublicDistinguisherFamily params)
    (securityParameter : ℕ) :
    (publicCircularLWESecurityGame params).advantage distinguisher securityParameter ≤
      (narrowSearchSecurityGame params sourceRingEta sourceKeySwitchEta).advantage
          (toSearchSolverFamily params sourceRingEta sourceKeySwitchEta reduction level
            hmargin distinguisher) securityParameter +
        (reductionLossSecurityGame params sourceRingEta sourceKeySwitchEta reduction level
          hmargin).advantage distinguisher securityParameter := by
  have h :=
    (pairedReductionAt params sourceRingEta sourceKeySwitchEta reduction level hmargin
      distinguisher securityParameter).advantage_le (distinguisher.run securityParameter)
  have hLift := ENNReal.ofReal_le_ofReal h
  change ENNReal.ofReal
      (LWE.AuxiliaryInput.SearchToDecision.publicAdvantage _
        (distinguisher.run securityParameter)) ≤
    LWE.AuxiliaryInput.Search.successProbability _ _ + ENNReal.ofReal _
  calc
    _ ≤ ENNReal.ofReal
        ((LWE.AuxiliaryInput.Search.successProbability _ _).toReal +
          (pairedReductionAt params sourceRingEta sourceKeySwitchEta reduction level
            hmargin distinguisher securityParameter).loss
              (distinguisher.run securityParameter)) := hLift
    _ ≤ ENNReal.ofReal
          (LWE.AuxiliaryInput.Search.successProbability _ _).toReal +
        ENNReal.ofReal
          ((pairedReductionAt params sourceRingEta sourceKeySwitchEta reduction level
            hmargin distinguisher securityParameter).loss
              (distinguisher.run securityParameter)) :=
      ENNReal.ofReal_add_le
    _ = _ := by
      simp only [LWE.AuxiliaryInput.Search.successProbability,
        ENNReal.ofReal_toReal probOutput_ne_top, toSearchSolverFamily]

/-- Negligible narrow augmented search success plus negligible general candidate-view loss
discharges the exact public augmented CircLWE premise used by adaptive TFHE security. -/
theorem publicCircularLWESecurityGame_secureAgainst_of_search_and_loss
    {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (sourceRingEta sourceKeySwitchEta : ℕ → ℕ)
    (reduction : ReductionFamily params sourceRingEta sourceKeySwitchEta)
    (level : (securityParameter : ℕ) →
      Fin (params.keySwitchLevels securityParameter))
    (hmargin : ∀ securityParameter,
      2 * sourceKeySwitchEta securityParameter <
        BootstrappingCorrectness.centeredDistance 0
          (params.keySwitchGadget securityParameter (level securityParameter)))
    (decisionIsPPT : PublicDistinguisherFamily params → Prop)
    (solverIsPPT : SearchSolverFamily params → Prop)
    (hClosed : ∀ distinguisher, decisionIsPPT distinguisher →
      solverIsPPT
        (toSearchSolverFamily params sourceRingEta sourceKeySwitchEta reduction level
          hmargin distinguisher))
    (hSearch :
      (narrowSearchSecurityGame params sourceRingEta sourceKeySwitchEta).secureAgainst
        solverIsPPT)
    (hLoss :
      (reductionLossSecurityGame params sourceRingEta sourceKeySwitchEta reduction level
        hmargin).secureAgainst decisionIsPPT) :
    (publicCircularLWESecurityGame params).secureAgainst decisionIsPPT := by
  intro distinguisher hdistinguisher
  exact negligible_of_le
    (publicCircularLWE_advantage_le_search_add_loss params sourceRingEta
      sourceKeySwitchEta reduction level hmargin distinguisher)
    (negligible_add
      (hSearch _ (hClosed distinguisher hdistinguisher))
      (hLoss distinguisher hdistinguisher))

/-! ## One-shot coordinate prediction

The averaged native laws above are sufficient for a single scalar-bit prediction, but not for
lossless repetition against one fixed cloud key.  This section records the corresponding
security endpoint without threshold amplification or a whole-key union bound. -/

namespace OneShot

/-- Parameter-indexed averaged native transformers for every bounded adaptive tape schedule. -/
structure TransformerFamily {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (sourceRingEta sourceKeySwitchEta : ℕ → ℕ) where
  transformerAt : (queryCount : ℕ → ℕ) → (securityParameter : ℕ) →
    AveragedCandidateViewTransformer
      (ringRank := params.ringRank securityParameter)
      (lweDimension := params.lweDimension securityParameter)
      (queryCount := queryCount securityParameter)
      (RLWE.CenteredBinomial.sampler
        (params.q securityParameter) (params.degree securityParameter)
        (sourceRingEta securityParameter))
      (params.ringErrorSampler securityParameter)
      (CenteredBinomial.scalarSampler
        (params.q securityParameter) (sourceKeySwitchEta securityParameter))
      (params.keySwitchErrorSampler securityParameter)
      (params.inputErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)

/-- A polynomial-tape family that predicts one selected scalar-secret coordinate from the
narrow augmented circular source. -/
structure CoordinatePredictorFamily {Message : Type} (params : Parameters Message) where
  queryCount : ℕ → ℕ
  queryPolynomial : Polynomial ℕ
  queryCount_le : ∀ securityParameter,
    queryCount securityParameter ≤ queryPolynomial.eval securityParameter
  coordinate : (securityParameter : ℕ) → Fin (params.lweDimension securityParameter)
  run : (securityParameter : ℕ) →
    CoordinateTester
      (params.q securityParameter)
      (params.degree securityParameter)
      (params.ringRank securityParameter)
      (params.tgswLevels securityParameter)
      (params.lweDimension securityParameter)
      (params.keySwitchLevels securityParameter)
      (queryCount securityParameter)

/-- Positive signed bias for predicting the selected scalar coordinate. -/
noncomputable def coordinatePredictionSecurityGame {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (sourceRingEta sourceKeySwitchEta : ℕ → ℕ) :
    SecurityGame (CoordinatePredictorFamily params) where
  advantage predictor securityParameter := ENNReal.ofReal
    (2 * (Pr[= true |
      coordinateGame
        (ringRank := params.ringRank securityParameter)
        (lweDimension := params.lweDimension securityParameter)
        (queryCount := predictor.queryCount securityParameter)
        (RLWE.CenteredBinomial.sampler
          (params.q securityParameter) (params.degree securityParameter)
          (sourceRingEta securityParameter))
        (CenteredBinomial.scalarSampler
          (params.q securityParameter) (sourceKeySwitchEta securityParameter))
        (params.inputErrorSampler securityParameter)
        (params.tgswGadget securityParameter)
        (params.keySwitchGadget securityParameter)
        (predictor.run securityParameter)
        (predictor.coordinate securityParameter)]).toReal - 1)

/-- The executable coordinate predictor induced by a public distinguisher and the native
one-shot transformer. -/
noncomputable def toCoordinatePredictorFamily {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (sourceRingEta sourceKeySwitchEta : ℕ → ℕ)
    (transformer : TransformerFamily params sourceRingEta sourceKeySwitchEta)
    (coordinate : (securityParameter : ℕ) →
      Fin (params.lweDimension securityParameter))
    (distinguisher : PublicDistinguisherFamily params) :
    CoordinatePredictorFamily params where
  queryCount := distinguisher.queryCount
  queryPolynomial := distinguisher.queryPolynomial
  queryCount_le := distinguisher.queryCount_le
  coordinate := coordinate
  run securityParameter :=
    (transformer.transformerAt distinguisher.queryCount securityParameter).toCoordinateTester
      (distinguisher.run securityParameter)

/-- Exact native correct/wrong-view error charged at the selected scalar coordinate. -/
noncomputable def statisticalErrorSecurityGame {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (sourceRingEta sourceKeySwitchEta : ℕ → ℕ)
    (transformer : TransformerFamily params sourceRingEta sourceKeySwitchEta)
    (coordinate : (securityParameter : ℕ) →
      Fin (params.lweDimension securityParameter)) :
    SecurityGame (PublicDistinguisherFamily params) where
  advantage distinguisher securityParameter := ENNReal.ofReal
    ((transformer.transformerAt distinguisher.queryCount securityParameter).correctError
        (coordinate securityParameter) +
      (transformer.transformerAt distinguisher.queryCount securityParameter).wrongError
        (coordinate securityParameter))

/-- Componentwise negligibility of the native correct and wrong view errors discharges the
combined one-coordinate statistical-error game. -/
theorem statisticalErrorSecurityGame_secureAgainst_of_components
    {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (sourceRingEta sourceKeySwitchEta : ℕ → ℕ)
    (transformer : TransformerFamily params sourceRingEta sourceKeySwitchEta)
    (coordinate : (securityParameter : ℕ) →
      Fin (params.lweDimension securityParameter))
    (decisionIsPPT : PublicDistinguisherFamily params → Prop)
    (hCorrect : ∀ distinguisher, decisionIsPPT distinguisher →
      negligible (fun securityParameter ↦ ENNReal.ofReal
        ((transformer.transformerAt distinguisher.queryCount securityParameter).correctError
          (coordinate securityParameter))))
    (hWrong : ∀ distinguisher, decisionIsPPT distinguisher →
      negligible (fun securityParameter ↦ ENNReal.ofReal
        ((transformer.transformerAt distinguisher.queryCount securityParameter).wrongError
          (coordinate securityParameter)))) :
    (statisticalErrorSecurityGame params sourceRingEta sourceKeySwitchEta transformer
      coordinate).secureAgainst decisionIsPPT := by
  intro distinguisher hdistinguisher
  apply negligible_of_le
  · intro securityParameter
    exact ENNReal.ofReal_add_le
  · exact negligible_add
      (hCorrect distinguisher hdistinguisher)
      (hWrong distinguisher hdistinguisher)

/-- Pointwise public augmented CircLWE reduction to one-coordinate prediction.  No
shared-context repetition, threshold term, or coordinate union bound occurs. -/
theorem publicCircularLWE_advantage_le_coordinatePrediction_add_error
    {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (sourceRingEta sourceKeySwitchEta : ℕ → ℕ)
    (transformer : TransformerFamily params sourceRingEta sourceKeySwitchEta)
    (coordinate : (securityParameter : ℕ) →
      Fin (params.lweDimension securityParameter))
    (distinguisher : PublicDistinguisherFamily params)
    (securityParameter : ℕ) :
    (publicCircularLWESecurityGame params).advantage distinguisher securityParameter ≤
      (coordinatePredictionSecurityGame params sourceRingEta sourceKeySwitchEta).advantage
          (toCoordinatePredictorFamily params sourceRingEta sourceKeySwitchEta transformer
            coordinate distinguisher) securityParameter +
        (statisticalErrorSecurityGame params sourceRingEta sourceKeySwitchEta transformer
          coordinate).advantage distinguisher securityParameter := by
  let finiteTransformer :=
    transformer.transformerAt distinguisher.queryCount securityParameter
  have hFinite :=
    finiteTransformer.publicAdvantage_le_coordinatePredictionBias_add_errors
      (distinguisher.run securityParameter) (coordinate securityParameter)
  have hGrouped :
      LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
          (KeySwitchFirstFiniteView.augmentedCircularProblem
            (ringRank := params.ringRank securityParameter)
            (lweDimension := params.lweDimension securityParameter)
            (queryCount := distinguisher.queryCount securityParameter)
            (params.ringErrorSampler securityParameter)
            (params.keySwitchErrorSampler securityParameter)
            (params.inputErrorSampler securityParameter)
            (params.tgswGadget securityParameter)
            (params.keySwitchGadget securityParameter))
          (distinguisher.run securityParameter) ≤
        finiteTransformer.coordinatePredictionBias
            (distinguisher.run securityParameter) (coordinate securityParameter) +
          (finiteTransformer.correctError (coordinate securityParameter) +
            finiteTransformer.wrongError (coordinate securityParameter)) := by
    linarith
  have hLift := ENNReal.ofReal_le_ofReal hGrouped
  exact hLift.trans ENNReal.ofReal_add_le

/-- Negligible one-coordinate prediction bias and negligible native statistical error imply the
public augmented CircLWE premise used by adaptive TFHE confidentiality. -/
theorem publicCircularLWESecurityGame_secureAgainst_of_coordinatePrediction_and_error
    {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (sourceRingEta sourceKeySwitchEta : ℕ → ℕ)
    (transformer : TransformerFamily params sourceRingEta sourceKeySwitchEta)
    (coordinate : (securityParameter : ℕ) →
      Fin (params.lweDimension securityParameter))
    (decisionIsPPT : PublicDistinguisherFamily params → Prop)
    (predictorIsPPT : CoordinatePredictorFamily params → Prop)
    (hClosed : ∀ distinguisher, decisionIsPPT distinguisher →
      predictorIsPPT
        (toCoordinatePredictorFamily params sourceRingEta sourceKeySwitchEta transformer
          coordinate distinguisher))
    (hPrediction :
      (coordinatePredictionSecurityGame params sourceRingEta sourceKeySwitchEta).secureAgainst
        predictorIsPPT)
    (hError :
      (statisticalErrorSecurityGame params sourceRingEta sourceKeySwitchEta transformer
        coordinate).secureAgainst decisionIsPPT) :
    (publicCircularLWESecurityGame params).secureAgainst decisionIsPPT := by
  intro distinguisher hdistinguisher
  exact negligible_of_le
    (publicCircularLWE_advantage_le_coordinatePrediction_add_error
      params sourceRingEta sourceKeySwitchEta transformer coordinate distinguisher)
    (negligible_add
      (hPrediction _ (hClosed distinguisher hdistinguisher))
      (hError distinguisher hdistinguisher))

end OneShot

end FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate
