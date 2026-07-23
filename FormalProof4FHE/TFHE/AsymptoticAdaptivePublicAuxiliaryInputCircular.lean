/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AdaptivePublicAuxiliaryInputCircular
import FormalProof4FHE.TFHE.AsymptoticSecurity

/-!
# Asymptotic Adaptive TFHE from Public Augmented CircLWE

This module lifts the finite public-auxiliary bridge to security-parameter families.  A public
distinguisher family carries the same polynomial query-count witness as its source adaptive
adversary.  At parameter `λ` it sees exactly one BRK, one KSK, and the bounded zero-message input
tape of `queryCount λ` rows, but neither hidden key.

The pointwise adaptive advantage is bounded by:

1. public augmented CircLWE for `(BRK, KSK, tape)`;
2. the matching zero-message auxiliary-input LWE branch; and
3. the existing ordinary joint-LWE endpoint for KSK rows and adaptive input rows.

Thus negligible security of these three public/ordinary games implies adaptive TFHE security.
No same-secret batch continuation appears in the statement.
-/

open ENNReal OracleComp

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular

open FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular

/-- Public augmented CircLWE distinguishers retain an explicit polynomial bound on the number
of input-tape rows. -/
structure PublicDistinguisherFamily {Message : Type} (params : Parameters Message) where
  queryCount : ℕ → ℕ
  queryPolynomial : Polynomial ℕ
  queryCount_le : ∀ securityParameter,
    queryCount securityParameter ≤ queryPolynomial.eval securityParameter
  run : (securityParameter : ℕ) →
    PublicDistinguisher
      (params.q securityParameter)
      (params.degree securityParameter)
      (params.ringRank securityParameter)
      (params.tgswLevels securityParameter)
      (params.lweDimension securityParameter)
      (params.keySwitchLevels securityParameter)
      (queryCount securityParameter)

/-- Public augmented CircLWE with one bounded input tape at each security parameter. -/
noncomputable def publicCircularLWESecurityGame {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :
    SecurityGame (PublicDistinguisherFamily params) where
  advantage distinguisher securityParameter := ENNReal.ofReal
    (publicCircularLweAdvantage
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.inputErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (distinguisher.run securityParameter))

/-- Zero-message-versus-uniform BRK security in the presence of the same KSK and input tape. -/
noncomputable def publicZeroLWESecurityGame {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :
    SecurityGame (PublicDistinguisherFamily params) where
  advantage distinguisher securityParameter := ENNReal.ofReal
    (publicZeroLweAdvantage
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.inputErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (distinguisher.run securityParameter))

/-- Turn a polynomial-query adaptive TFHE adversary into the public distinguisher that receives
its complete pre-sampled `(BRK, KSK, tape)` view. -/
noncomputable def publicDistinguisherReduction {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (adversary : PolynomialQueryAdversary params) : PublicDistinguisherFamily params where
  queryCount := adversary.queryCount
  queryPolynomial := adversary.queryPolynomial
  queryCount_le := adversary.queryCount_le
  run securityParameter :=
    bundleDistinguisher
      (KeySwitchFirstSecurity.toPublicDistinguisher
        (queryCount := adversary.queryCount securityParameter)
        (params.encode securityParameter)
        (adversary.run securityParameter))

/-- The public zero-side family induced by an adaptive adversary is bounded by the actual-context
and uniform-BRK-context ordinary joint-LWE reductions. -/
theorem publicZeroLWESecurityGame_advantage_le_two_jointLWE
    {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (adversary : PolynomialQueryAdversary params)
    (securityParameter : ℕ) :
    (publicZeroLWESecurityGame params).advantage
        (publicDistinguisherReduction params adversary) securityParameter ≤
      (jointLWESecurityGame params).advantage
          (jointLWEReduction params adversary) securityParameter +
        (jointLWESecurityGame params).advantage
          (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
            params adversary) securityParameter := by
  have h := publicZeroLweAdvantage_toPublic_le_two_jointLwe
    (adversary.queryCount securityParameter)
    (params.ringErrorSampler securityParameter)
    (params.keySwitchErrorSampler securityParameter)
    (params.inputErrorSampler securityParameter)
    (params.tgswGadget securityParameter)
    (params.keySwitchGadget securityParameter)
    (params.encode securityParameter)
    (adversary.run securityParameter)
    (adversary.isQueryBound securityParameter)
  have hLift := ENNReal.ofReal_le_ofReal h
  simpa only [publicZeroLWESecurityGame, publicDistinguisherReduction,
    jointLWESecurityGame, jointLWEReduction,
    MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction] using
      hLift.trans ENNReal.ofReal_add_le

/-- Pointwise asymptotic accounting for the public augmented circular route. -/
theorem securityGame_advantage_le_publicCircular_add_zero_add_jointLWE
    {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (adversary : PolynomialQueryAdversary params)
    (securityParameter : ℕ) :
    (securityGame params).advantage adversary securityParameter ≤
      (publicCircularLWESecurityGame params).advantage
          (publicDistinguisherReduction params adversary) securityParameter +
        (publicZeroLWESecurityGame params).advantage
          (publicDistinguisherReduction params adversary) securityParameter +
        (jointLWESecurityGame params).advantage
          (jointLWEReduction params adversary) securityParameter := by
  have hFinite :=
    abs_signedAdvantage_real_le_publicCircular_add_zero_add_jointLwe
      (adversary.queryCount securityParameter)
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.inputErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (params.encode securityParameter)
      (adversary.run securityParameter)
      (adversary.isQueryBound securityParameter)
  have hLift := ENNReal.ofReal_le_ofReal hFinite
  calc
    (securityGame params).advantage adversary securityParameter ≤
        ENNReal.ofReal
          (publicCircularLweAdvantage
              (params.ringErrorSampler securityParameter)
              (params.keySwitchErrorSampler securityParameter)
              (params.inputErrorSampler securityParameter)
              (params.tgswGadget securityParameter)
              (params.keySwitchGadget securityParameter)
              ((publicDistinguisherReduction params adversary).run securityParameter) +
            publicZeroLweAdvantage
              (params.ringErrorSampler securityParameter)
              (params.keySwitchErrorSampler securityParameter)
              (params.inputErrorSampler securityParameter)
              (params.tgswGadget securityParameter)
              (params.keySwitchGadget securityParameter)
              ((publicDistinguisherReduction params adversary).run securityParameter) +
            LearningWithErrors.advantage
              (Adaptive.jointLweProblem
                (params.q securityParameter)
                (params.lweDimension securityParameter)
                (Encryption.Security.keySwitchSamples
                  (params.ringRank securityParameter)
                  (params.degree securityParameter)
                  (params.keySwitchLevels securityParameter))
                (adversary.queryCount securityParameter)
                (params.keySwitchErrorSampler securityParameter)
                (params.inputErrorSampler securityParameter))
              ((jointLWEReduction params adversary).run securityParameter)) := by
      simpa only [securityGame, publicDistinguisherReduction, jointLWEReduction] using hLift
    _ ≤ ENNReal.ofReal
          (publicCircularLweAdvantage
              (params.ringErrorSampler securityParameter)
              (params.keySwitchErrorSampler securityParameter)
              (params.inputErrorSampler securityParameter)
              (params.tgswGadget securityParameter)
              (params.keySwitchGadget securityParameter)
              ((publicDistinguisherReduction params adversary).run securityParameter) +
            publicZeroLweAdvantage
              (params.ringErrorSampler securityParameter)
              (params.keySwitchErrorSampler securityParameter)
              (params.inputErrorSampler securityParameter)
              (params.tgswGadget securityParameter)
              (params.keySwitchGadget securityParameter)
              ((publicDistinguisherReduction params adversary).run securityParameter)) +
        ENNReal.ofReal
          (LearningWithErrors.advantage
            (Adaptive.jointLweProblem
              (params.q securityParameter)
              (params.lweDimension securityParameter)
              (Encryption.Security.keySwitchSamples
                (params.ringRank securityParameter)
                (params.degree securityParameter)
                (params.keySwitchLevels securityParameter))
              (adversary.queryCount securityParameter)
              (params.keySwitchErrorSampler securityParameter)
              (params.inputErrorSampler securityParameter))
            ((jointLWEReduction params adversary).run securityParameter)) :=
      ENNReal.ofReal_add_le
    _ ≤ ENNReal.ofReal
          (publicCircularLweAdvantage
            (params.ringErrorSampler securityParameter)
            (params.keySwitchErrorSampler securityParameter)
            (params.inputErrorSampler securityParameter)
            (params.tgswGadget securityParameter)
            (params.keySwitchGadget securityParameter)
            ((publicDistinguisherReduction params adversary).run securityParameter)) +
        ENNReal.ofReal
          (publicZeroLweAdvantage
            (params.ringErrorSampler securityParameter)
            (params.keySwitchErrorSampler securityParameter)
            (params.inputErrorSampler securityParameter)
            (params.tgswGadget securityParameter)
            (params.keySwitchGadget securityParameter)
            ((publicDistinguisherReduction params adversary).run securityParameter)) +
        ENNReal.ofReal
          (LearningWithErrors.advantage
            (Adaptive.jointLweProblem
              (params.q securityParameter)
              (params.lweDimension securityParameter)
              (Encryption.Security.keySwitchSamples
                (params.ringRank securityParameter)
                (params.degree securityParameter)
                (params.keySwitchLevels securityParameter))
              (adversary.queryCount securityParameter)
              (params.keySwitchErrorSampler securityParameter)
              (params.inputErrorSampler securityParameter))
            ((jointLWEReduction params adversary).run securityParameter)) := by
      exact add_le_add ENNReal.ofReal_add_le (le_refl _)
    _ = _ := by
      rfl

/-- Pointwise adaptive TFHE bound with public augmented CircLWE as the only circular term.  All
three remaining terms are conventional joint-LWE games; the actual-context reduction appears
twice and the uniform-BRK-context reduction once. -/
theorem securityGame_advantage_le_publicCircular_add_three_jointLWE
    {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (adversary : PolynomialQueryAdversary params)
    (securityParameter : ℕ) :
    (securityGame params).advantage adversary securityParameter ≤
      (publicCircularLWESecurityGame params).advantage
          (publicDistinguisherReduction params adversary) securityParameter +
        (jointLWESecurityGame params).advantage
          (jointLWEReduction params adversary) securityParameter +
        (jointLWESecurityGame params).advantage
          (jointLWEReduction params adversary) securityParameter +
        (jointLWESecurityGame params).advantage
          (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
            params adversary) securityParameter := by
  calc
    _ ≤ (publicCircularLWESecurityGame params).advantage
          (publicDistinguisherReduction params adversary) securityParameter +
        (publicZeroLWESecurityGame params).advantage
          (publicDistinguisherReduction params adversary) securityParameter +
        (jointLWESecurityGame params).advantage
          (jointLWEReduction params adversary) securityParameter :=
      securityGame_advantage_le_publicCircular_add_zero_add_jointLWE
        params adversary securityParameter
    _ ≤ (publicCircularLWESecurityGame params).advantage
          (publicDistinguisherReduction params adversary) securityParameter +
        ((jointLWESecurityGame params).advantage
            (jointLWEReduction params adversary) securityParameter +
          (jointLWESecurityGame params).advantage
            (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
              params adversary) securityParameter) +
        (jointLWESecurityGame params).advantage
          (jointLWEReduction params adversary) securityParameter := by
      exact add_le_add
        (add_le_add le_rfl
          (publicZeroLWESecurityGame_advantage_le_two_jointLWE
            params adversary securityParameter)) le_rfl
    _ = _ := by ac_rfl

/-- **Adaptive TFHE security from public augmented CircLWE.**

Closure of the public-view and joint-LWE reductions under the selected efficiency predicates,
together with negligible security of all three target games, gives negligible honest adaptive
TFHE advantage. -/
theorem secureAgainst_of_publicCircular_zero_and_jointLWE
    {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (isPPT : PolynomialQueryAdversary params → Prop)
    (publicIsPPT : PublicDistinguisherFamily params → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily params → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT (publicDistinguisherReduction params adversary))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT (jointLWEReduction params adversary))
    (hCircular : (publicCircularLWESecurityGame params).secureAgainst publicIsPPT)
    (hZero : (publicZeroLWESecurityGame params).secureAgainst publicIsPPT)
    (hJointLWE : (jointLWESecurityGame params).secureAgainst jointLWEIsPPT) :
    (securityGame params).secureAgainst isPPT := by
  intro adversary hadversary
  exact negligible_of_le
    (securityGame_advantage_le_publicCircular_add_zero_add_jointLWE params adversary)
    (negligible_add
      (negligible_add
        (hCircular _ (hPublicClosed adversary hadversary))
        (hZero _ (hPublicClosed adversary hadversary)))
      (hJointLWE _ (hJointLWEClosed adversary hadversary)))

/-- **Adaptive TFHE security with public augmented CircLWE as the sole circular premise.**

The public zero branch is discharged internally by two ordinary joint-LWE reductions. -/
theorem secureAgainst_of_publicCircular_and_jointLWE
    {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (isPPT : PolynomialQueryAdversary params → Prop)
    (publicIsPPT : PublicDistinguisherFamily params → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily params → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT (publicDistinguisherReduction params adversary))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT (jointLWEReduction params adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          params adversary))
    (hCircular : (publicCircularLWESecurityGame params).secureAgainst publicIsPPT)
    (hJointLWE : (jointLWESecurityGame params).secureAgainst jointLWEIsPPT) :
    (securityGame params).secureAgainst isPPT := by
  intro adversary hadversary
  exact negligible_of_le
    (securityGame_advantage_le_publicCircular_add_three_jointLWE params adversary)
    (negligible_add
      (negligible_add
        (negligible_add
          (hCircular _ (hPublicClosed adversary hadversary))
          (hJointLWE _ (hJointLWEClosed adversary hadversary)))
        (hJointLWE _ (hJointLWEClosed adversary hadversary)))
      (hJointLWE _ (hUniformJointLWEClosed adversary hadversary)))

end FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular
