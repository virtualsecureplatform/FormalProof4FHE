/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AdaptiveAugmentedResidualCandidateView
import FormalProof4FHE.TFHE.AsymptoticAdaptivePublicAuxiliaryInputCircular

/-!
# Asymptotic Public Augmented CircLWE from Residual Candidate Evaluation

This module lifts the finite search-to-decision reduction for the complete public adaptive view
`(BRK, KSK, bounded input tape)` to security-parameter families.  Query counts are retained in the
distinguisher and solver families, so the reduction neither erases the tape nor passes a hidden
key to a continuation.

At every security parameter, an averaged residual evaluator produces a paired-key solver for a
narrow centered-binomial augmented search problem.  The public augmented CircLWE advantage is
bounded by that solver's recovery probability plus the explicit residual, threshold, and
amplification loss.  Hence negligible search success and negligible loss imply the exact public
CircLWE premise used by the adaptive TFHE security theorem.
-/

open ENNReal OracleComp

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedResidual

open FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery
open FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery.AugmentedResidual

/-- Augmented paired-search solvers retain the polynomial tape-length schedule of the public
distinguisher from which they were generated. -/
structure SearchSolverFamily {Message : Type} (params : Parameters Message) where
  queryCount : ℕ → ℕ
  queryPolynomial : Polynomial ℕ
  queryCount_le : ∀ securityParameter,
    queryCount securityParameter ≤ queryPolynomial.eval securityParameter
  run : (securityParameter : ℕ) →
    Solver
      (params.q securityParameter)
      (params.degree securityParameter)
      (params.ringRank securityParameter)
      (params.tgswLevels securityParameter)
      (params.lweDimension securityParameter)
      (params.keySwitchLevels securityParameter)
      (queryCount securityParameter)

/-- Parameter-indexed averaged residual reductions, uniformly available for every bounded tape
schedule.  Each finite reduction itself accepts every public distinguisher of the selected size. -/
structure ReductionFamily {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (sourceRingEta sourceKeySwitchEta : ℕ → ℕ) where
  reductionAt : (queryCount : ℕ → ℕ) → (securityParameter : ℕ) →
    AveragedResidualCandidateViewTransformerReduction
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

/-- Paired-key recovery in the narrow centered-binomial augmented source distribution. -/
noncomputable def narrowSearchSecurityGame {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (sourceRingEta sourceKeySwitchEta : ℕ → ℕ) :
    SecurityGame (SearchSolverFamily params) where
  advantage solver securityParameter :=
    LWE.AuxiliaryInput.Search.successProbability
      (problem
        (ringRank := params.ringRank securityParameter)
        (lweDimension := params.lweDimension securityParameter)
        (queryCount := solver.queryCount securityParameter)
        (RLWE.CenteredBinomial.sampler
          (params.q securityParameter)
          (params.degree securityParameter)
          (sourceRingEta securityParameter))
        (CenteredBinomial.scalarSampler
          (params.q securityParameter)
          (sourceKeySwitchEta securityParameter))
        (params.inputErrorSampler securityParameter)
        (params.tgswGadget securityParameter)
        (params.keySwitchGadget securityParameter))
      (solver.run securityParameter)

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

/-- Apply the residual reduction pointwise, retaining the public distinguisher's polynomial query
schedule in the resulting augmented search solver. -/
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

/-- Exact residual, threshold, amplification, and coordinate-union loss of the augmented
reduction family. -/
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

/-- Pointwise augmented search-to-decision accounting. -/
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

/-- Negligible narrow augmented search success plus negligible evaluator loss discharges the
exact public augmented CircLWE premise used by adaptive TFHE security. -/
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

end FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedResidual
