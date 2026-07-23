/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AuxiliaryInputSearchToDecision
import FormalProof4FHE.TFHE.AveragedCandidateView

/-!
# Native TFHE Search-to-Decision with Widened Smudging Noise

The CircLWE search-to-decision reduction in the PKC 2024 framework starts from a narrow-error
search instance and invokes a decision distinguisher for a wider error distribution.  This module
formalizes that distinction for the native TFHE BRK+KSK view.

The source search experiment uses centered-binomial ring and key-switch errors, so the existing
exact scalar randomization and KSK completion theorems apply.  The target decision experiment may
use arbitrary ring and scalar error samplers of the same ciphertext types.  A conditional
candidate-view transformer bridges the two distributions; its correct and wrong total-variation
errors are subtracted from the target decision advantage before majority amplification.

No theorem in this module asserts the still-missing native homomorphic evaluator normal form.
Instead, it removes all generic accounting around that construction: conditional view distances
imply pointwise gaps, majority amplification gives coordinate errors, the union bound gives scalar
recovery, and the centered-binomial KSK completes the paired secret.  The final loss is exactly the
sum of amplified coordinate errors.  `NativeResidualCandidateView.lean` subsequently discharges
the conditional-distance fields from exact residual normal forms and native smudging bounds.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.SearchToDecision.Widened

/-- Cross-distribution certificate from centered-binomial native search to an arbitrary widened
native decision problem. -/
abbrev PairedSecretReduction
    (q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ)
    [NeZero q]
    (targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (targetKeySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :=
  LWE.AuxiliaryInput.SearchToDecision.CrossReduction
    (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget)
    (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.problem
      q degree ringRank tgswLevels lweDimension keySwitchLevels
      (RLWE.CenteredBinomial.sampler q degree ringEta)
      (CenteredBinomial.scalarSampler q keySwitchEta)
      tgswGadget keySwitchGadget)

/-- Scalar-only cross-distribution certificate.  The solver receives the narrow centered-binomial
view, while the advantage on the left is measured in the widened target decision experiment. -/
structure ScalarSecretReduction
    (q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ)
    [NeZero q]
    (targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (targetKeySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) where
  toScalarSolver :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) →
      Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.ScalarSolver
        q degree ringRank tgswLevels lweDimension keySwitchLevels
  loss :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) → ℝ
  loss_nonneg : ∀ distinguisher, 0 ≤ loss distinguisher
  advantage_le : ∀ distinguisher,
    LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
        (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
          targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget)
        distinguisher ≤
      (Pr[= true |
        Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.scalarGame
          (RLWE.CenteredBinomial.sampler q degree ringEta)
          (CenteredBinomial.scalarSampler q keySwitchEta)
          tgswGadget keySwitchGadget (toScalarSolver distinguisher)]).toReal +
        loss distinguisher

namespace ScalarSecretReduction

/-- Centered-binomial KSK decoding completes the narrow scalar solver without changing success,
while the widened target advantage and reduction loss are preserved. -/
noncomputable def toPairedSecretReduction
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    {targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : ScalarSecretReduction q degree ringRank tgswLevels lweDimension
      keySwitchLevels ringEta keySwitchEta targetRingErrorSampler
      targetKeySwitchErrorSampler tgswGadget keySwitchGadget)
    (level : Fin keySwitchLevels)
    (hmargin : 2 * keySwitchEta <
      BootstrappingCorrectness.centeredDistance 0 (keySwitchGadget level)) :
    PairedSecretReduction q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringEta keySwitchEta targetRingErrorSampler targetKeySwitchErrorSampler
      tgswGadget keySwitchGadget where
  toSolver := fun distinguisher =>
    Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.completeScalarSolver
      keySwitchGadget level (reduction.toScalarSolver distinguisher)
  loss := reduction.loss
  loss_nonneg := reduction.loss_nonneg
  advantage_le := by
    intro distinguisher
    have h := reduction.advantage_le distinguisher
    rw [← Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.successProbability_completeScalarSolver_eq
      (RLWE.CenteredBinomial.sampler q degree ringEta) tgswGadget keySwitchGadget
      level (reduction.toScalarSolver distinguisher) hmargin] at h
    exact h

end ScalarSecretReduction

/-- Coordinatewise narrow-search certificate with a widened target decision advantage. -/
structure CoordinateSecretReduction
    (q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ)
    [NeZero q]
    (targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (targetKeySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) where
  toTester :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) →
      Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.CoordinateTester
        q degree ringRank tgswLevels lweDimension keySwitchLevels
  coordinateError :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) →
      Fin lweDimension → ENNReal
  loss :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) → ℝ
  loss_nonneg : ∀ distinguisher, 0 ≤ loss distinguisher
  coordinateGameFailure_le : ∀ distinguisher coordinate,
    Pr[= false |
      Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.coordinateGame
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget (toTester distinguisher) coordinate] ≤
      coordinateError distinguisher coordinate
  advantage_le : ∀ distinguisher,
    LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
        (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
          targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget)
        distinguisher ≤
      (1 - ∑ coordinate, coordinateError distinguisher coordinate).toReal +
        loss distinguisher

namespace CoordinateSecretReduction

/-- The existing shared-view coordinate union bound is distribution-agnostic on the target side,
so it converts a widened coordinate certificate to scalar recovery unchanged. -/
noncomputable def toScalarSecretReduction
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    {targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : CoordinateSecretReduction q degree ringRank tgswLevels lweDimension
      keySwitchLevels ringEta keySwitchEta targetRingErrorSampler
      targetKeySwitchErrorSampler tgswGadget keySwitchGadget) :
    ScalarSecretReduction q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringEta keySwitchEta targetRingErrorSampler targetKeySwitchErrorSampler
      tgswGadget keySwitchGadget where
  toScalarSolver := fun distinguisher =>
    Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.assemble
      (reduction.toTester distinguisher)
  loss := reduction.loss
  loss_nonneg := reduction.loss_nonneg
  advantage_le := by
    intro distinguisher
    have hsuccess :=
      Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.one_sub_sum_coordinateGameError_le_scalarSuccess
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget (reduction.toTester distinguisher)
        (reduction.coordinateError distinguisher)
        (reduction.coordinateGameFailure_le distinguisher)
    have hsuccessReal := ENNReal.toReal_mono probOutput_ne_top hsuccess
    exact (reduction.advantage_le distinguisher).trans
      (add_le_add hsuccessReal le_rfl)

end CoordinateSecretReduction

/-- Cross-distribution certificate using only an averaged candidate-view law.  Since every
coordinate repetition reuses the same narrow BRK+KSK context, the certificate records an
explicit good-fiber threshold.  The resulting coordinate error contains both the iterated
majority term and the Markov bad-context term. -/
structure AveragedCandidateViewTransformerReduction
    (q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ)
    [NeZero q]
    (targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (targetKeySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) where
  toTransformer :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) →
      Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.AveragedCandidateViewTransformer
        (ringRank := ringRank) (lweDimension := lweDimension)
        (RLWE.CenteredBinomial.sampler q degree ringEta) targetRingErrorSampler
        (CenteredBinomial.scalarSampler q keySwitchEta) targetKeySwitchErrorSampler
        tgswGadget keySwitchGadget
  rounds :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) →
      Fin lweDimension → ℕ
  threshold :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) →
      Fin lweDimension → ENNReal
  threshold_pos : ∀ distinguisher coordinate, 0 < threshold distinguisher coordinate
  threshold_le_one : ∀ distinguisher coordinate, threshold distinguisher coordinate ≤ 1

namespace AveragedCandidateViewTransformerReduction

/-- Target decision advantage left after the two averaged view distances. -/
noncomputable def effectiveGap
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    {targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : AveragedCandidateViewTransformerReduction q degree ringRank tgswLevels
      lweDimension keySwitchLevels ringEta keySwitchEta targetRingErrorSampler
      targetKeySwitchErrorSampler tgswGadget keySwitchGadget)
    (distinguisher : LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels))
    (coordinate : Fin lweDimension) : ℝ :=
  LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
      (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
        targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget)
      distinguisher -
    (reduction.toTransformer distinguisher).correctError coordinate -
    (reduction.toTransformer distinguisher).wrongError coordinate

/-- Sound shared-context error assigned to one coordinate under an averaged view law. -/
noncomputable def thresholdedCoordinateError
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    {targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : AveragedCandidateViewTransformerReduction q degree ringRank tgswLevels
      lweDimension keySwitchLevels ringEta keySwitchEta targetRingErrorSampler
      targetKeySwitchErrorSampler tgswGadget keySwitchGadget)
    (distinguisher : LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels))
    (coordinate : Fin lweDimension) : ENNReal :=
  FormalProof4FHE.MajorityAmplification.amplifiedError
      (reduction.rounds distinguisher coordinate)
      (reduction.threshold distinguisher coordinate) +
    ENNReal.ofReal ((1 - reduction.effectiveGap distinguisher coordinate) / 2) /
      reduction.threshold distinguisher coordinate

/-- Averaged candidate-view laws, thresholded amplification, and the shared-view coordinate
union bound induce the complete widened coordinate certificate.  The reduction loss is exactly
the sum of the sound thresholded coordinate errors. -/
noncomputable def toCoordinateSecretReduction
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    {targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : AveragedCandidateViewTransformerReduction q degree ringRank tgswLevels
      lweDimension keySwitchLevels ringEta keySwitchEta targetRingErrorSampler
      targetKeySwitchErrorSampler tgswGadget keySwitchGadget) :
    CoordinateSecretReduction q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringEta keySwitchEta targetRingErrorSampler targetKeySwitchErrorSampler
      tgswGadget keySwitchGadget where
  toTester := fun distinguisher ↦
    Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.amplifiedTesterOfCheck
      (reduction.rounds distinguisher)
      (fun _ ↦
        Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.CandidateViewTransformer.orientation
          targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget
          distinguisher)
      ((reduction.toTransformer distinguisher).toCheck distinguisher)
  coordinateError := reduction.thresholdedCoordinateError
  loss := fun distinguisher ↦
    (∑ coordinate, reduction.thresholdedCoordinateError distinguisher coordinate).toReal
  loss_nonneg := fun _ ↦ ENNReal.toReal_nonneg
  coordinateGameFailure_le := by
    intro distinguisher coordinate
    have h :=
      (reduction.toTransformer distinguisher).amplifiedCoordinateFailure_le_threshold
        distinguisher (reduction.rounds distinguisher) coordinate
        (reduction.threshold distinguisher coordinate)
        (reduction.threshold_pos distinguisher coordinate)
        (reduction.threshold_le_one distinguisher coordinate)
    rw [candidateDecisionAdvantage_eq_publicAdvantage] at h
    simpa only [thresholdedCoordinateError, effectiveGap] using h
  advantage_le := by
    intro distinguisher
    let errors : Fin lweDimension → ENNReal :=
      reduction.thresholdedCoordinateError distinguisher
    have herrors_ne_top : ∀ coordinate, errors coordinate ≠ ⊤ := by
      intro coordinate
      apply ENNReal.add_ne_top.mpr
      constructor
      · exact ne_top_of_le_ne_top ENNReal.one_ne_top
          (FormalProof4FHE.MajorityAmplification.amplifiedError_le_one
            (reduction.rounds distinguisher coordinate)
            (reduction.threshold_le_one distinguisher coordinate))
      · apply ENNReal.div_ne_top
        · simp
        · exact ne_of_gt (reduction.threshold_pos distinguisher coordinate)
    have hsum_ne_top : (∑ coordinate, errors coordinate) ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr fun coordinate _ ↦ herrors_ne_top coordinate
    have hadv := LWE.AuxiliaryInput.SearchToDecision.publicAdvantage_le_one
      (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
        targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget)
      distinguisher
    have hone : (1 : ℝ) ≤
        (1 - ∑ coordinate, errors coordinate).toReal +
          (∑ coordinate, errors coordinate).toReal := by
      by_cases hsum : (∑ coordinate, errors coordinate) ≤ 1
      · rw [ENNReal.toReal_sub_of_le hsum ENNReal.one_ne_top, ENNReal.toReal_one]
        linarith
      · have honeSum : 1 ≤ ∑ coordinate, errors coordinate := le_of_not_ge hsum
        rw [tsub_eq_zero_of_le honeSum, ENNReal.toReal_zero, zero_add,
          ← ENNReal.toReal_one]
        exact ENNReal.toReal_mono hsum_ne_top honeSum
    change LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
        (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
          targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget)
        distinguisher ≤
      (1 - ∑ coordinate, errors coordinate).toReal +
        (∑ coordinate, errors coordinate).toReal
    exact hadv.trans hone

/-- The averaged widened transformer gives scalar-secret recovery with its explicit threshold
loss. -/
noncomputable def toScalarSecretReduction
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    {targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : AveragedCandidateViewTransformerReduction q degree ringRank tgswLevels
      lweDimension keySwitchLevels ringEta keySwitchEta targetRingErrorSampler
      targetKeySwitchErrorSampler tgswGadget keySwitchGadget) :
    ScalarSecretReduction q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringEta keySwitchEta targetRingErrorSampler targetKeySwitchErrorSampler
      tgswGadget keySwitchGadget :=
  reduction.toCoordinateSecretReduction.toScalarSecretReduction

/-- With a centered-binomial KSK decoding margin, the averaged widened transformer gives full
paired-secret recovery. -/
noncomputable def toPairedSecretReduction
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    {targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : AveragedCandidateViewTransformerReduction q degree ringRank tgswLevels
      lweDimension keySwitchLevels ringEta keySwitchEta targetRingErrorSampler
      targetKeySwitchErrorSampler tgswGadget keySwitchGadget)
    (level : Fin keySwitchLevels)
    (hmargin : 2 * keySwitchEta <
      BootstrappingCorrectness.centeredDistance 0 (keySwitchGadget level)) :
    PairedSecretReduction q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringEta keySwitchEta targetRingErrorSampler targetKeySwitchErrorSampler
      tgswGadget keySwitchGadget :=
  reduction.toScalarSecretReduction.toPairedSecretReduction level hmargin

end AveragedCandidateViewTransformerReduction

/-- The sole scheme-specific certificate for the widened route: a conditional native
shifted-evaluation/smudging transformer and a nonnegative effective distinguishing gap. -/
structure PointwiseCandidateViewTransformerReduction
    (q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ)
    [NeZero q]
    (targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (targetKeySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) where
  toTransformer :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) →
      Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.PointwiseCandidateViewTransformer
        (ringRank := ringRank) (lweDimension := lweDimension)
        (RLWE.CenteredBinomial.sampler q degree ringEta) targetRingErrorSampler
        (CenteredBinomial.scalarSampler q keySwitchEta) targetKeySwitchErrorSampler
        tgswGadget keySwitchGadget
  rounds :
    LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) →
      Fin lweDimension → ℕ
  effectiveGap_nonneg : ∀ distinguisher coordinate,
    0 ≤ LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
          (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
            targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget)
          distinguisher -
        (toTransformer distinguisher).correctError coordinate -
        (toTransformer distinguisher).wrongError coordinate

namespace PointwiseCandidateViewTransformerReduction

/-- Target decision advantage remaining after both conditional view distances. -/
noncomputable def effectiveGap
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    {targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : PointwiseCandidateViewTransformerReduction q degree ringRank tgswLevels
      lweDimension keySwitchLevels ringEta keySwitchEta targetRingErrorSampler
      targetKeySwitchErrorSampler tgswGadget keySwitchGadget)
    (distinguisher : LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels))
    (coordinate : Fin lweDimension) : ℝ :=
  LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
      (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
        targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget)
      distinguisher -
    (reduction.toTransformer distinguisher).correctError coordinate -
    (reduction.toTransformer distinguisher).wrongError coordinate

/-- Exact amplified error for one coordinate in the narrow source experiment. -/
noncomputable def amplifiedCoordinateError
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    {targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : PointwiseCandidateViewTransformerReduction q degree ringRank tgswLevels
      lweDimension keySwitchLevels ringEta keySwitchEta targetRingErrorSampler
      targetKeySwitchErrorSampler tgswGadget keySwitchGadget)
    (distinguisher : LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels))
    (coordinate : Fin lweDimension) : ENNReal :=
  FormalProof4FHE.MajorityAmplification.amplifiedError
    (reduction.rounds distinguisher coordinate)
    (ENNReal.ofReal ((1 - reduction.effectiveGap distinguisher coordinate) / 2))

/-- Conditional narrow-to-wide view laws automatically induce the amplified coordinate
certificate.  The total amplified failure is charged once as reduction loss. -/
noncomputable def toCoordinateSecretReduction
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    {targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : PointwiseCandidateViewTransformerReduction q degree ringRank tgswLevels
      lweDimension keySwitchLevels ringEta keySwitchEta targetRingErrorSampler
      targetKeySwitchErrorSampler tgswGadget keySwitchGadget) :
    CoordinateSecretReduction q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringEta keySwitchEta targetRingErrorSampler targetKeySwitchErrorSampler
      tgswGadget keySwitchGadget where
  toTester := fun distinguisher =>
    Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.amplifiedTesterOfCheck
      (reduction.rounds distinguisher)
      (fun _ =>
        Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.CandidateViewTransformer.orientation
          targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget
          distinguisher)
      ((reduction.toTransformer distinguisher).toCheck distinguisher)
  coordinateError := reduction.amplifiedCoordinateError
  loss := fun distinguisher =>
    (∑ coordinate, reduction.amplifiedCoordinateError distinguisher coordinate).toReal
  loss_nonneg := fun _ => ENNReal.toReal_nonneg
  coordinateGameFailure_le := by
    intro distinguisher coordinate
    apply Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.coordinateGame_amplifiedTesterOfCheck_failureProbability_le_of_pointwiseGap
      (RLWE.CenteredBinomial.sampler q degree ringEta)
      (CenteredBinomial.scalarSampler q keySwitchEta)
      tgswGadget keySwitchGadget (reduction.rounds distinguisher)
      (fun _ =>
        Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.CandidateViewTransformer.orientation
          targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget
          distinguisher)
      ((reduction.toTransformer distinguisher).toCheck distinguisher)
      coordinate (reduction.effectiveGap distinguisher coordinate)
      (reduction.effectiveGap_nonneg distinguisher coordinate)
    intro hiddenAndContext hsupport
    unfold effectiveGap
    rw [← candidateDecisionAdvantage_eq_publicAdvantage]
    exact
      (reduction.toTransformer distinguisher).decisionAdvantage_sub_errors_le_pointwiseCandidateCheckGap
        distinguisher coordinate hiddenAndContext hsupport
  advantage_le := by
    intro distinguisher
    let errors : Fin lweDimension → ENNReal :=
      reduction.amplifiedCoordinateError distinguisher
    have herrors_le_one : ∀ coordinate, errors coordinate ≤ 1 := by
      intro coordinate
      apply FormalProof4FHE.MajorityAmplification.amplifiedError_le_one
      exact ENNReal.ofReal_le_one.mpr (by
        have hgap := reduction.effectiveGap_nonneg distinguisher coordinate
        change 0 ≤ reduction.effectiveGap distinguisher coordinate at hgap
        linarith)
    have hsum_ne_top : (∑ coordinate, errors coordinate) ≠ ⊤ :=
      ENNReal.sum_ne_top.mpr fun coordinate _ =>
        ne_top_of_le_ne_top ENNReal.one_ne_top (herrors_le_one coordinate)
    have hadv := LWE.AuxiliaryInput.SearchToDecision.publicAdvantage_le_one
      (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
        targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget)
      distinguisher
    have hone : (1 : ℝ) ≤
        (1 - ∑ coordinate, errors coordinate).toReal +
          (∑ coordinate, errors coordinate).toReal := by
      by_cases hsum : (∑ coordinate, errors coordinate) ≤ 1
      · rw [ENNReal.toReal_sub_of_le hsum ENNReal.one_ne_top, ENNReal.toReal_one]
        linarith
      · have honeSum : 1 ≤ ∑ coordinate, errors coordinate := le_of_not_ge hsum
        rw [tsub_eq_zero_of_le honeSum, ENNReal.toReal_zero, zero_add,
          ← ENNReal.toReal_one]
        exact ENNReal.toReal_mono hsum_ne_top honeSum
    change LWE.AuxiliaryInput.SearchToDecision.publicAdvantage
        (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
          targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget)
        distinguisher ≤
      (1 - ∑ coordinate, errors coordinate).toReal +
        (∑ coordinate, errors coordinate).toReal
    exact hadv.trans hone

/-- The widened conditional transformer gives scalar-secret recovery. -/
noncomputable def toScalarSecretReduction
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    {targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : PointwiseCandidateViewTransformerReduction q degree ringRank tgswLevels
      lweDimension keySwitchLevels ringEta keySwitchEta targetRingErrorSampler
      targetKeySwitchErrorSampler tgswGadget keySwitchGadget) :
    ScalarSecretReduction q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringEta keySwitchEta targetRingErrorSampler targetKeySwitchErrorSampler
      tgswGadget keySwitchGadget :=
  reduction.toCoordinateSecretReduction.toScalarSecretReduction

/-- With the existing centered-binomial KSK margin, the widened conditional transformer gives
full paired-secret recovery. -/
noncomputable def toPairedSecretReduction
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    {targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (reduction : PointwiseCandidateViewTransformerReduction q degree ringRank tgswLevels
      lweDimension keySwitchLevels ringEta keySwitchEta targetRingErrorSampler
      targetKeySwitchErrorSampler tgswGadget keySwitchGadget)
    (level : Fin keySwitchLevels)
    (hmargin : 2 * keySwitchEta <
      BootstrappingCorrectness.centeredDistance 0 (keySwitchGadget level)) :
    PairedSecretReduction q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringEta keySwitchEta targetRingErrorSampler targetKeySwitchErrorSampler
      tgswGadget keySwitchGadget :=
  reduction.toScalarSecretReduction.toPairedSecretReduction level hmargin

end PointwiseCandidateViewTransformerReduction

/-- Narrow centered-binomial native search hardness transfers to widened native public CircLWE
decision hardness through a checked paired-secret certificate. -/
theorem publicHardAgainst_of_pairedSecretReduction
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta keySwitchEta : ℕ}
    [NeZero q]
    (targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (targetKeySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (reduction : PairedSecretReduction q degree ringRank tgswLevels lweDimension
      keySwitchLevels ringEta keySwitchEta targetRingErrorSampler
      targetKeySwitchErrorSampler tgswGadget keySwitchGadget)
    (decisionAllowed : LWE.AuxiliaryInput.SearchToDecision.PublicDistinguisher
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Challenge
        q degree ringRank tgswLevels lweDimension)
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Auxiliary
        q degree ringRank lweDimension keySwitchLevels) → Prop)
    (solverAllowed : Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.Solver
      q degree ringRank tgswLevels lweDimension keySwitchLevels → Prop)
    (searchBound lossBound : ℝ)
    (hSearch : LWE.AuxiliaryInput.SearchToDecision.RealSearchHardAgainst
      (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.problem
        q degree ringRank tgswLevels lweDimension keySwitchLevels
        (RLWE.CenteredBinomial.sampler q degree ringEta)
        (CenteredBinomial.scalarSampler q keySwitchEta)
        tgswGadget keySwitchGadget)
      solverAllowed searchBound)
    (hClosed : ∀ distinguisher, decisionAllowed distinguisher →
      solverAllowed (reduction.toSolver distinguisher))
    (hLoss : ∀ distinguisher, decisionAllowed distinguisher →
      reduction.loss distinguisher ≤ lossBound) :
    LWE.AuxiliaryInput.SearchToDecision.PublicHardAgainst
      (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
        targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget)
      decisionAllowed (searchBound + lossBound) :=
  LWE.AuxiliaryInput.SearchToDecision.publicHardAgainst_of_crossReduction
    (AuxiliaryInput.problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget)
    (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.problem
      q degree ringRank tgswLevels lweDimension keySwitchLevels
      (RLWE.CenteredBinomial.sampler q degree ringEta)
      (CenteredBinomial.scalarSampler q keySwitchEta)
      tgswGadget keySwitchGadget)
    reduction decisionAllowed solverAllowed searchBound lossBound hSearch hClosed hLoss

end FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.SearchToDecision.Widened
