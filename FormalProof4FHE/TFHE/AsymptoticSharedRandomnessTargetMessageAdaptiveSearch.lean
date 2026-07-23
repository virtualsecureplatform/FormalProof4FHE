/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SharedRandomnessTargetMessageAdaptiveSearchEquiv
import VCVio.CryptoFoundations.Asymptotics.Security

set_option autoImplicit false

/-!
# Asymptotic Search Foundation for Full-Target-Message Adaptive TFHE

This file lifts the finite common-search theorem for the shared-randomness nested-key model to
security-parameter families.  At every parameter, the source key is a literal prefix of the
target key and the honest BRK encrypts all extracted target-key bits under that source key.

The checked pointwise bound has exactly three terms:

* exact recovery of the nested key in the established tape-first public search experiment;
* the loss of a supplied BRK-decision-to-search reduction; and
* one ordinary blocked module-RLWE advantage.

Consequently, negligible search success, negligible reduction loss, and ordinary module-RLWE
security imply negligible adaptive TFHE advantage.  The theorem does not manufacture the
construction-specific shifted evaluator required by the PKC-style search-to-decision argument;
that object remains an explicit reduction compiler below.
-/

open ENNReal OracleComp

namespace FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.AdaptiveBRKCircLWE.SearchEquiv.Asymptotic

noncomputable section

/-- Security-parameter-indexed nested-key TFHE parameters.  The decision and search error laws
are kept separate so a noise-flooding search-to-decision reduction can widen the decision view. -/
structure Parameters (Message : Type) where
  q : ℕ → ℕ
  degree : ℕ → ℕ
  sourceRank : ℕ → ℕ
  suffixRank : ℕ → ℕ
  tgswLevels : ℕ → ℕ
  decisionErrorSampler : (securityParameter : ℕ) →
    ProbComp (RLWE.Rq (q securityParameter) (degree securityParameter + 1))
  searchErrorSampler : (securityParameter : ℕ) →
    ProbComp (RLWE.Rq (q securityParameter) (degree securityParameter + 1))
  gadget : (securityParameter : ℕ) →
    Fin (tgswLevels securityParameter) →
      RLWE.Rq (q securityParameter) (degree securityParameter + 1)
  decompose : (securityParameter : ℕ) →
    TFHE.TLWE.Ciphertext
        (RLWE.Rq (q securityParameter) (degree securityParameter + 1))
        (sourceRank securityParameter) →
      Fin (sourceRank securityParameter + 1) →
        Fin (tgswLevels securityParameter) →
          RLWE.Rq (q securityParameter) (degree securityParameter + 1)
  encode : (securityParameter : ℕ) → Message → ZMod (q securityParameter)

/-- A parameter-indexed adaptive adversary with an explicit polynomial encryption-query bound. -/
structure PolynomialQueryAdversary {Message : Type} (params : Parameters Message) where
  run : (securityParameter : ℕ) →
    AdaptiveAdversary Message
      (params.q securityParameter)
      (params.degree securityParameter + 1)
      (params.sourceRank securityParameter)
      (params.suffixRank securityParameter)
      (params.tgswLevels securityParameter)
  queryCount : ℕ → ℕ
  queryPolynomial : Polynomial ℕ
  queryCount_le : ∀ securityParameter,
    queryCount securityParameter ≤ queryPolynomial.eval securityParameter
  isQueryBound : ∀ securityParameter,
    Encryption.Adaptive.IsQueryBound
      (run securityParameter) (queryCount securityParameter)

/-- Families of solvers for the common tape-first exact nested-key recovery problem. -/
structure TapeFirstSolverFamily {Message : Type} (params : Parameters Message) where
  queryCount : ℕ → ℕ
  queryPolynomial : Polynomial ℕ
  queryCount_le : ∀ securityParameter,
    queryCount securityParameter ≤ queryPolynomial.eval securityParameter
  run : (securityParameter : ℕ) →
    AdaptiveCircularLWE.Solver
      (params.q securityParameter)
      (params.degree securityParameter + 1)
      (params.sourceRank securityParameter)
      (params.suffixRank securityParameter)
      (params.tgswLevels securityParameter)
      (queryCount securityParameter)

/-- Families of ordinary blocked module-RLWE adversaries produced by the post-circular hybrid. -/
structure ModuleLWEAdversaryFamily {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] where
  queryCount : ℕ → ℕ
  queryPolynomial : Polynomial ℕ
  queryCount_le : ∀ securityParameter,
    queryCount securityParameter ≤ queryPolynomial.eval securityParameter
  run : (securityParameter : ℕ) →
    LearningWithErrors.Adversary
      (AdaptiveReduction.problem
        (params.q securityParameter)
        (params.degree securityParameter)
        (params.sourceRank securityParameter)
        (params.suffixRank securityParameter)
        (params.tgswLevels securityParameter)
        (queryCount securityParameter)
        (params.decisionErrorSampler securityParameter))

/-- A family-level compiler for the remaining PKC-style step.  For each source adversary and
security parameter it supplies a checked monomial-BRK decision to tape-first-search reduction.
The compiler is deliberately data, not an axiom hidden inside the final theorem. -/
structure ReductionCompiler {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] where
  reduction : (adversary : PolynomialQueryAdversary params) →
    (securityParameter : ℕ) →
      CrossDecisionToTapeFirstSearchReduction
        (params.q securityParameter)
        (params.degree securityParameter)
        (params.sourceRank securityParameter)
        (params.suffixRank securityParameter)
        (params.tgswLevels securityParameter)
        (adversary.queryCount securityParameter)
        (params.decisionErrorSampler securityParameter)
        (params.searchErrorSampler securityParameter)
        (params.gadget securityParameter)

/-! ## Exact asymptotic target games and reductions -/

/-- Honest query-bounded adaptive TFHE confidentiality for the nested-key family. -/
noncomputable def securityGame {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :
    SecurityGame (PolynomialQueryAdversary params) where
  advantage adversary securityParameter := ENNReal.ofReal
    |Encryption.signedAdvantage
      (realAdaptiveGame
        (params.q securityParameter)
        (params.degree securityParameter + 1)
        (params.sourceRank securityParameter)
        (params.suffixRank securityParameter)
        (params.tgswLevels securityParameter)
        (adversary.queryCount securityParameter)
        (params.decisionErrorSampler securityParameter)
        (params.decisionErrorSampler securityParameter)
        (AdaptiveReduction.extractedErrorSampler
          (params.decisionErrorSampler securityParameter))
        (params.gadget securityParameter)
        (params.decompose securityParameter)
        (params.encode securityParameter)
        (adversary.run securityParameter))|

/-- Exact-recovery security in the tape-first public view already used by the direct FHE
CircLWE formulation.  Its advantage is a probability, not a distinguishing gap. -/
noncomputable def tapeFirstSearchSecurityGame {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :
    SecurityGame (TapeFirstSolverFamily params) where
  advantage solver securityParameter :=
    FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability
      (AdaptiveCircularLWE.searchProblem
        (params.q securityParameter)
        (params.degree securityParameter + 1)
        (params.sourceRank securityParameter)
        (params.suffixRank securityParameter)
        (params.tgswLevels securityParameter)
        (solver.queryCount securityParameter)
        (params.searchErrorSampler securityParameter)
        (params.searchErrorSampler securityParameter)
        (AdaptiveReduction.extractedErrorSampler
          (params.searchErrorSampler securityParameter))
        (params.gadget securityParameter))
      (solver.run securityParameter)

/-- The explicit loss charged by the checked decision-to-search compiler. -/
noncomputable def reductionLossSecurityGame {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (compiler : ReductionCompiler params) :
    SecurityGame (PolynomialQueryAdversary params) where
  advantage adversary securityParameter := ENNReal.ofReal
    ((compiler.reduction adversary securityParameter).loss
      (adaptiveDistinguisher
        (params.decompose securityParameter)
        (params.encode securityParameter)
        (adversary.run securityParameter)))

/-- Conventional blocked module-RLWE security for the exact post-circular transcript. -/
noncomputable def moduleLWESecurityGame {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :
    SecurityGame (ModuleLWEAdversaryFamily params) where
  advantage adversary securityParameter := ENNReal.ofReal
    (LearningWithErrors.advantage
      (AdaptiveReduction.problem
        (params.q securityParameter)
        (params.degree securityParameter)
        (params.sourceRank securityParameter)
        (params.suffixRank securityParameter)
        (params.tgswLevels securityParameter)
        (adversary.queryCount securityParameter)
        (params.decisionErrorSampler securityParameter))
      (adversary.run securityParameter))

/-- The concrete tape-first recovery solver produced from an adaptive TFHE adversary. -/
noncomputable def tapeFirstSearchReduction {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (compiler : ReductionCompiler params)
    (adversary : PolynomialQueryAdversary params) : TapeFirstSolverFamily params where
  queryCount := adversary.queryCount
  queryPolynomial := adversary.queryPolynomial
  queryCount_le := adversary.queryCount_le
  run securityParameter :=
    (compiler.reduction adversary securityParameter).toSolver
      (adaptiveDistinguisher
        (params.decompose securityParameter)
        (params.encode securityParameter)
        (adversary.run securityParameter))

/-- The ordinary module-RLWE adversary generated by the zero-BRK continuation hybrid. -/
noncomputable def moduleLWEReduction {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (adversary : PolynomialQueryAdversary params) : ModuleLWEAdversaryFamily params where
  queryCount := adversary.queryCount
  queryPolynomial := adversary.queryPolynomial
  queryCount_le := adversary.queryCount_le
  run securityParameter :=
    jointZeroReduction
      (errorSampler := params.decisionErrorSampler securityParameter)
      (params.gadget securityParameter)
      (resampleBootstrapContinuation
        (AdaptiveReduction.adaptiveViewContinuation
          (params.decompose securityParameter)
          (params.encode securityParameter)
          (adversary.run securityParameter)))

set_option maxHeartbeats 1000000
/-! ## Pointwise and negligible-security composition -/

/-- **Pointwise family theorem.**  The exact common-search finite reduction is preserved without
changing any secret relation, sampler, query count, or public view. -/
theorem securityGame_advantage_le_tapeFirstSearch_add_loss_add_moduleLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (compiler : ReductionCompiler params)
    (adversary : PolynomialQueryAdversary params)
    (securityParameter : ℕ) :
    (securityGame params).advantage adversary securityParameter ≤
      (tapeFirstSearchSecurityGame params).advantage
          (tapeFirstSearchReduction params compiler adversary) securityParameter +
        (reductionLossSecurityGame params compiler).advantage adversary
          securityParameter +
        (moduleLWESecurityGame params).advantage
          (moduleLWEReduction params adversary) securityParameter := by
  have hFinite :=
    abs_signedAdvantage_realAdaptive_le_tapeFirstSearch_add_reductionLoss_add_moduleLwe
      (params.q securityParameter)
      (params.degree securityParameter)
      (params.sourceRank securityParameter)
      (params.suffixRank securityParameter)
      (params.tgswLevels securityParameter)
      (adversary.queryCount securityParameter)
      (params.decisionErrorSampler securityParameter)
      (params.searchErrorSampler securityParameter)
      (params.gadget securityParameter)
      (params.decompose securityParameter)
      (params.encode securityParameter)
      (adversary.run securityParameter)
      (adversary.isQueryBound securityParameter)
      (compiler.reduction adversary securityParameter)
  have hLift := ENNReal.ofReal_le_ofReal hFinite
  let success :=
    FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability
      (AdaptiveCircularLWE.searchProblem
        (params.q securityParameter)
        (params.degree securityParameter + 1)
        (params.sourceRank securityParameter)
        (params.suffixRank securityParameter)
        (params.tgswLevels securityParameter)
        (adversary.queryCount securityParameter)
        (params.searchErrorSampler securityParameter)
        (params.searchErrorSampler securityParameter)
        (AdaptiveReduction.extractedErrorSampler
          (params.searchErrorSampler securityParameter))
        (params.gadget securityParameter))
      ((compiler.reduction adversary securityParameter).toSolver
        (adaptiveDistinguisher
          (params.decompose securityParameter)
          (params.encode securityParameter)
          (adversary.run securityParameter)))
  let loss :=
    (compiler.reduction adversary securityParameter).loss
      (adaptiveDistinguisher
        (params.decompose securityParameter)
        (params.encode securityParameter)
        (adversary.run securityParameter))
  let moduleAdvantage :=
    LearningWithErrors.advantage
      (AdaptiveReduction.problem
        (params.q securityParameter)
        (params.degree securityParameter)
        (params.sourceRank securityParameter)
        (params.suffixRank securityParameter)
        (params.tgswLevels securityParameter)
        (adversary.queryCount securityParameter)
        (params.decisionErrorSampler securityParameter))
      (jointZeroReduction (params.gadget securityParameter)
        (resampleBootstrapContinuation
          (AdaptiveReduction.adaptiveViewContinuation
            (params.decompose securityParameter)
            (params.encode securityParameter)
            (adversary.run securityParameter))))
  change ENNReal.ofReal
      |Encryption.signedAdvantage
        (realAdaptiveGame
          (params.q securityParameter)
          (params.degree securityParameter + 1)
          (params.sourceRank securityParameter)
          (params.suffixRank securityParameter)
          (params.tgswLevels securityParameter)
          (adversary.queryCount securityParameter)
          (params.decisionErrorSampler securityParameter)
          (params.decisionErrorSampler securityParameter)
          (AdaptiveReduction.extractedErrorSampler
            (params.decisionErrorSampler securityParameter))
          (params.gadget securityParameter)
          (params.decompose securityParameter)
          (params.encode securityParameter)
          (adversary.run securityParameter))| ≤
      success + ENNReal.ofReal loss + ENNReal.ofReal moduleAdvantage
  calc
    _ ≤ ENNReal.ofReal (success.toReal + loss + moduleAdvantage) := by
      simpa only [success, loss, moduleAdvantage] using hLift
    _ ≤ ENNReal.ofReal (success.toReal + loss) +
          ENNReal.ofReal moduleAdvantage := ENNReal.ofReal_add_le
    _ ≤ (ENNReal.ofReal success.toReal + ENNReal.ofReal loss) +
          ENNReal.ofReal moduleAdvantage :=
      add_le_add ENNReal.ofReal_add_le le_rfl
    _ = success + ENNReal.ofReal loss + ENNReal.ofReal moduleAdvantage := by
      rw [ENNReal.ofReal_toReal]
      exact probOutput_ne_top

/-- **Asymptotic adaptive TFHE security from the common circular-search foundation.**

The closure hypotheses are the only computational bookkeeping: they assert that the concrete
solver and module-RLWE transformations preserve the selected efficiency classes.  The
construction-specific shifted evaluator is represented solely by `compiler`, and its complete
loss is charged by `reductionLossSecurityGame`. -/
theorem secureAgainst_of_tapeFirstSearch_reductionLoss_and_moduleLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (compiler : ReductionCompiler params)
    (isPPT : PolynomialQueryAdversary params → Prop)
    (solverIsPPT : TapeFirstSolverFamily params → Prop)
    (moduleLWEIsPPT : ModuleLWEAdversaryFamily params → Prop)
    (hSolverClosed : ∀ adversary, isPPT adversary →
      solverIsPPT (tapeFirstSearchReduction params compiler adversary))
    (hModuleLWEClosed : ∀ adversary, isPPT adversary →
      moduleLWEIsPPT (moduleLWEReduction params adversary))
    (hSearch : (tapeFirstSearchSecurityGame params).secureAgainst solverIsPPT)
    (hLoss : (reductionLossSecurityGame params compiler).secureAgainst isPPT)
    (hModuleLWE : (moduleLWESecurityGame params).secureAgainst moduleLWEIsPPT) :
    (securityGame params).secureAgainst isPPT := by
  intro adversary hadversary
  exact negligible_of_le
    (securityGame_advantage_le_tapeFirstSearch_add_loss_add_moduleLWE
      params compiler adversary)
    (negligible_add
      (negligible_add
        (hSearch _ (hSolverClosed adversary hadversary))
        (hLoss adversary hadversary))
      (hModuleLWE _ (hModuleLWEClosed adversary hadversary)))

end

end FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.AdaptiveBRKCircLWE.SearchEquiv.Asymptotic
