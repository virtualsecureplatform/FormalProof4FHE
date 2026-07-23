/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AsymptoticMonomialKDM
import FormalProof4FHE.TFHE.MonomialKDMAuxiliaryInput

/-!
# Asymptotic Auxiliary-Input CircLWE for Native TFHE

This file lifts the exact finite bridge in `TFHE.MonomialKDMAuxiliaryInput` to the adaptive
asymptotic framework.  It packages two games:

* native degree-two monomial gadget-LWE versus uniform, with the real KSK retained; and
* native zero-message gadget-LWE versus uniform, with the same real KSK retained.

The existing native monomial-KDM game is negligible if both games are negligible.  Conversely,
monomial-KDM security plus the zero-message game implies CircLWE security.  Hence, whenever the
zero-message side-information term is established separately, the named CircLWE and native KDM
formulations are asymptotically equivalent.
-/

open ENNReal OracleComp

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput

/-- Native auxiliary-input CircLWE for arbitrary continuation families. -/
noncomputable def circularLWESecurityGame {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :
    SecurityGame (ContinuationFamily params) where
  advantage continuation securityParameter := ENNReal.ofReal
    (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.circularLweAdvantage
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (continuation securityParameter))

/-- Native zero-message gadget-LWE versus uniform with the real KSK retained. -/
noncomputable def zeroLWESecurityGame {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :
    SecurityGame (ContinuationFamily params) where
  advantage continuation securityParameter := ENNReal.ofReal
    (Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.zeroLweAdvantage
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (continuation securityParameter))

/-- Pointwise native monomial-KDM advantage is bounded by auxiliary-input CircLWE plus the
zero-message side-information LWE branch. -/
theorem securityGame_advantage_le_circularLWE_add_zeroLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (continuation : ContinuationFamily params) (securityParameter : ℕ) :
    (MonomialKDM.securityGame params).advantage continuation securityParameter ≤
      (circularLWESecurityGame params).advantage continuation securityParameter +
        (zeroLWESecurityGame params).advantage continuation securityParameter := by
  have h :=
    FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.monomialAdvantage_le_circularLwe_add_zeroLwe
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (continuation securityParameter)
  have hLift := ENNReal.ofReal_le_ofReal h
  exact hLift.trans ENNReal.ofReal_add_le

/-- The converse pointwise bound: CircLWE is at most monomial KDM plus the same zero branch. -/
theorem circularLWESecurityGame_advantage_le_monomial_add_zeroLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (continuation : ContinuationFamily params) (securityParameter : ℕ) :
    (circularLWESecurityGame params).advantage continuation securityParameter ≤
      (MonomialKDM.securityGame params).advantage continuation securityParameter +
        (zeroLWESecurityGame params).advantage continuation securityParameter := by
  have h :=
    FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.circularLweAdvantage_le_monomial_add_zeroLwe
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (continuation securityParameter)
  have hLift := ENNReal.ofReal_le_ofReal h
  exact hLift.trans ENNReal.ofReal_add_le

/-- Auxiliary-input CircLWE and the zero-message side-information LWE premise imply the exact
native degree-two monomial-KDM premise. -/
theorem securityGame_secureAgainst_of_circularLWE_and_zeroLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (isPPT : ContinuationFamily params → Prop)
    (hCircular : (circularLWESecurityGame params).secureAgainst isPPT)
    (hZero : (zeroLWESecurityGame params).secureAgainst isPPT) :
    (MonomialKDM.securityGame params).secureAgainst isPPT := by
  intro continuation hcontinuation
  exact negligible_of_le
    (securityGame_advantage_le_circularLWE_add_zeroLWE params continuation)
    (negligible_add
      (hCircular continuation hcontinuation)
      (hZero continuation hcontinuation))

/-- Monomial-KDM and the zero-message side-information LWE premise imply native
auxiliary-input CircLWE. -/
theorem circularLWESecurityGame_secureAgainst_of_monomial_and_zeroLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (isPPT : ContinuationFamily params → Prop)
    (hMonomial : (MonomialKDM.securityGame params).secureAgainst isPPT)
    (hZero : (zeroLWESecurityGame params).secureAgainst isPPT) :
    (circularLWESecurityGame params).secureAgainst isPPT := by
  intro continuation hcontinuation
  exact negligible_of_le
    (circularLWESecurityGame_advantage_le_monomial_add_zeroLWE params continuation)
    (negligible_add
      (hMonomial continuation hcontinuation)
      (hZero continuation hcontinuation))

/-- With the zero-message side-information branch fixed, native monomial-KDM and auxiliary-input
CircLWE security are equivalent for the same continuation class. -/
theorem securityGame_secureAgainst_iff_circularLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (isPPT : ContinuationFamily params → Prop)
    (hZero : (zeroLWESecurityGame params).secureAgainst isPPT) :
    (MonomialKDM.securityGame params).secureAgainst isPPT ↔
      (circularLWESecurityGame params).secureAgainst isPPT := by
  constructor
  · intro hMonomial
    exact circularLWESecurityGame_secureAgainst_of_monomial_and_zeroLWE
      params isPPT hMonomial hZero
  · intro hCircular
    exact securityGame_secureAgainst_of_circularLWE_and_zeroLWE
      params isPPT hCircular hZero

/-! ## Games induced by polynomial-query adaptive TFHE adversaries -/

/-- Auxiliary-input CircLWE restricted to the continuations generated by adaptive TFHE
adversaries. -/
noncomputable def adaptiveCircularLWESecurityGame {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :
    SecurityGame (PolynomialQueryAdversary params) where
  advantage adversary securityParameter :=
    (circularLWESecurityGame params).advantage
      (continuationReduction params adversary) securityParameter

/-- The corresponding induced zero-message side-information LWE game. -/
noncomputable def adaptiveZeroLWESecurityGame {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)] :
    SecurityGame (PolynomialQueryAdversary params) where
  advantage adversary securityParameter :=
    (zeroLWESecurityGame params).advantage
      (continuationReduction params adversary) securityParameter

/-- Pointwise adaptive monomial-KDM-to-CircLWE bridge. -/
theorem adaptiveSecurityGame_advantage_le_circularLWE_add_zeroLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (adversary : PolynomialQueryAdversary params) (securityParameter : ℕ) :
    (MonomialKDM.adaptiveSecurityGame params).advantage adversary securityParameter ≤
      (adaptiveCircularLWESecurityGame params).advantage adversary securityParameter +
        (adaptiveZeroLWESecurityGame params).advantage adversary securityParameter := by
  exact securityGame_advantage_le_circularLWE_add_zeroLWE
    params (continuationReduction params adversary) securityParameter

/-- Pointwise converse adaptive bridge. -/
theorem adaptiveCircularLWESecurityGame_advantage_le_monomial_add_zeroLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (adversary : PolynomialQueryAdversary params) (securityParameter : ℕ) :
    (adaptiveCircularLWESecurityGame params).advantage adversary securityParameter ≤
      (MonomialKDM.adaptiveSecurityGame params).advantage adversary securityParameter +
        (adaptiveZeroLWESecurityGame params).advantage adversary securityParameter := by
  exact circularLWESecurityGame_advantage_le_monomial_add_zeroLWE
    params (continuationReduction params adversary) securityParameter

/-- Adaptive auxiliary-input CircLWE plus the induced zero-message term implies the exact
adaptive monomial-KDM premise consumed by the TFHE security theorem. -/
theorem adaptiveSecurityGame_secureAgainst_of_circularLWE_and_zeroLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (isPPT : PolynomialQueryAdversary params → Prop)
    (hCircular : (adaptiveCircularLWESecurityGame params).secureAgainst isPPT)
    (hZero : (adaptiveZeroLWESecurityGame params).secureAgainst isPPT) :
    (MonomialKDM.adaptiveSecurityGame params).secureAgainst isPPT := by
  intro adversary hadversary
  exact negligible_of_le
    (adaptiveSecurityGame_advantage_le_circularLWE_add_zeroLWE params adversary)
    (negligible_add
      (hCircular adversary hadversary)
      (hZero adversary hadversary))

/-- With the induced zero-message term fixed, the adaptive native monomial and CircLWE games are
equivalent. -/
theorem adaptiveSecurityGame_secureAgainst_iff_circularLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (isPPT : PolynomialQueryAdversary params → Prop)
    (hZero : (adaptiveZeroLWESecurityGame params).secureAgainst isPPT) :
    (MonomialKDM.adaptiveSecurityGame params).secureAgainst isPPT ↔
      (adaptiveCircularLWESecurityGame params).secureAgainst isPPT := by
  constructor
  · intro hMonomial adversary hadversary
    exact negligible_of_le
      (adaptiveCircularLWESecurityGame_advantage_le_monomial_add_zeroLWE
        params adversary)
      (negligible_add
        (hMonomial adversary hadversary)
        (hZero adversary hadversary))
  · intro hCircular
    exact adaptiveSecurityGame_secureAgainst_of_circularLWE_and_zeroLWE
      params isPPT hCircular hZero

end FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput
