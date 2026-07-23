/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.CoefficientAffineCircularRLWE
import FormalProof4FHE.TFHE.SharedRandomnessOneCycleAsymptoticCircularEncryption

/-!
# Asymptotic TFHE Security from the Exact Restricted Circular Components

This module lifts the native one-cycle BRK factorization through the adaptive encryption and
public-evaluation security theorems.  It replaces the single opaque native circular-RLWE premise
by exactly the two secret-dependent continuation games occurring in the TFHE distribution:

* the fixed square-free outer-product table, containing only products of distinct master-key
  coefficients; and
* the diagonal coefficient-affine circular-RLWE table.

The diagonal table is not replaced by ordinary rank-one RLWE: its coefficient projectors were
proved not to be multiplication by a fixed public ring element.  Thus the theorem is an exact
asymptotic security composition and a precise research boundary, not an unsupported reduction
of either remaining component to ordinary LWE or RLWE.
-/

open ENNReal OracleComp OracleSpec

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.SharedRandomnessOneCycle.Asymptotic.CircularSecurity

noncomputable section

open FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE.AuxiliaryInput

/-! ## Security games for the two exact native components -/

/-- Security-parameter family for removal of the fixed square-free BRK table, while the
continuation retains the hidden master key and real shared KSK. -/
noncomputable def squareFreeSecurityGame {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : RingErrorFamily params) :
    SecurityGame (ContinuationFamily params) where
  advantage continuation securityParameter := ENNReal.ofReal
    (secretContinuationSquareFreeAdvantage
      (params.q securityParameter)
      (params.prefixDimension securityParameter)
      (params.suffixDimension securityParameter)
      (params.tgswLevels securityParameter)
      (params.keySwitchLevels securityParameter)
      (implementation.sampler securityParameter)
      (params.scalarErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (continuation securityParameter))

/-- Security-parameter family for the diagonal coefficient-affine circular-RLWE table, with the
same hidden master key and real shared KSK retained by the continuation. -/
noncomputable def coefficientAffineCircularLWESecurityGame {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : RingErrorFamily params) :
    SecurityGame (ContinuationFamily params) where
  advantage continuation securityParameter := ENNReal.ofReal
    (secretContinuationCircularLweAdvantage
      (params.q securityParameter)
      (params.prefixDimension securityParameter)
      (params.suffixDimension securityParameter)
      (params.tgswLevels securityParameter)
      (params.keySwitchLevels securityParameter)
      (implementation.sampler securityParameter)
      (params.scalarErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (continuation securityParameter))

/-- Pointwise native circular-RLWE advantage is bounded by the exact square-free and diagonal
coefficient-affine components, even for a secret-dependent FHE continuation. -/
theorem circularLWESecurityGame_advantage_le_squareFree_add_coefficientAffine
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : RingErrorFamily params)
    (continuation : ContinuationFamily params) (securityParameter : ℕ) :
    (circularLWESecurityGame params implementation).advantage continuation
        securityParameter ≤
      (squareFreeSecurityGame params implementation).advantage continuation
          securityParameter +
        (coefficientAffineCircularLWESecurityGame params implementation).advantage
          continuation securityParameter := by
  have h := nativeCircularLweAdvantage_le_squareFree_add_coefficientAffine
    (params.q securityParameter)
    (params.prefixDimension securityParameter)
    (params.suffixDimension securityParameter)
    (params.tgswLevels securityParameter)
    (params.keySwitchLevels securityParameter)
    (implementation.sampler securityParameter)
    (params.scalarErrorSampler securityParameter)
    (params.tgswGadget securityParameter)
    (params.keySwitchGadget securityParameter)
    (continuation securityParameter)
  exact (ENNReal.ofReal_le_ofReal h).trans ENNReal.ofReal_add_le

/-- Negligibility of the two restricted components implies the formerly opaque native
one-cycle circular-RLWE premise. -/
theorem circularLWESecurityGame_secureAgainst_of_squareFree_and_coefficientAffine
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : RingErrorFamily params)
    (isPPT : ContinuationFamily params → Prop)
    (hSquareFree : (squareFreeSecurityGame params implementation).secureAgainst isPPT)
    (hCoefficientAffine :
      (coefficientAffineCircularLWESecurityGame params implementation).secureAgainst isPPT) :
    (circularLWESecurityGame params implementation).secureAgainst isPPT := by
  intro continuation hcontinuation
  exact negligible_of_le
    (circularLWESecurityGame_advantage_le_squareFree_add_coefficientAffine
      params implementation continuation)
    (negligible_add
      (hSquareFree continuation hcontinuation)
      (hCoefficientAffine continuation hcontinuation))

/-! ## Restriction to adaptive TFHE adversaries -/

/-- Fixed square-free-table security restricted to continuations compiled from adaptive TFHE
adversaries. -/
noncomputable def adaptiveSquareFreeSecurityGame {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : RingErrorFamily params) :
    SecurityGame (PolynomialQueryAdversary params) where
  advantage adversary securityParameter :=
    (squareFreeSecurityGame params implementation).advantage
      (continuationReduction params adversary) securityParameter

/-- Diagonal coefficient-affine circular-RLWE security restricted to continuations compiled
from adaptive TFHE adversaries. -/
noncomputable def adaptiveCoefficientAffineCircularLWESecurityGame {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : RingErrorFamily params) :
    SecurityGame (PolynomialQueryAdversary params) where
  advantage adversary securityParameter :=
    (coefficientAffineCircularLWESecurityGame params implementation).advantage
      (continuationReduction params adversary) securityParameter

/-- Pointwise full adaptive TFHE bound with no generic circular-RLWE term left: only the fixed
square-free table, the diagonal coefficient-affine table, and ordinary batch LWE remain. -/
theorem implementationSecurityGame_advantage_le_squareFree_add_coefficientAffine_add_batchLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : RingErrorFamily params)
    (adversary : PolynomialQueryAdversary params) (securityParameter : ℕ) :
    (implementationSecurityGame params implementation).advantage adversary
        securityParameter ≤
      ((adaptiveSquareFreeSecurityGame params implementation).advantage adversary
          securityParameter +
        (adaptiveCoefficientAffineCircularLWESecurityGame params implementation).advantage
          adversary securityParameter) +
        (batchLWESecurityGame params).advantage
          (batchLWEReduction params adversary) securityParameter := by
  calc
    (implementationSecurityGame params implementation).advantage adversary
        securityParameter ≤
      (adaptiveCircularLWESecurityGame params implementation).advantage adversary
          securityParameter +
        (batchLWESecurityGame params).advantage
          (batchLWEReduction params adversary) securityParameter :=
      implementationSecurityGame_advantage_le_circularLWE_add_batchLWE
        params implementation adversary securityParameter
    _ ≤ _ := add_le_add
      (circularLWESecurityGame_advantage_le_squareFree_add_coefficientAffine
        params implementation (continuationReduction params adversary) securityParameter)
      le_rfl

/-- **Adaptive shared-randomness TFHE security from the exact restricted circular
components.**

If the fixed square-free table, diagonal coefficient-affine circular-RLWE table, and reduced
ordinary batch-LWE problem are negligible for the selected efficient families, then the honest
reusable-key adaptive TFHE encryption advantage is negligible. -/
theorem implementationSecureAgainst_of_squareFree_coefficientAffine_and_batchLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : RingErrorFamily params)
    (isPPT : PolynomialQueryAdversary params → Prop)
    (batchLWEIsPPT : BatchLWEAdversaryFamily params → Prop)
    (hBatchLWEClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT (batchLWEReduction params adversary))
    (hSquareFree :
      (adaptiveSquareFreeSecurityGame params implementation).secureAgainst isPPT)
    (hCoefficientAffine :
      (adaptiveCoefficientAffineCircularLWESecurityGame params implementation).secureAgainst
        isPPT)
    (hBatchLWE : (batchLWESecurityGame params).secureAgainst batchLWEIsPPT) :
    (implementationSecurityGame params implementation).secureAgainst isPPT := by
  intro adversary hadversary
  exact negligible_of_le
    (implementationSecurityGame_advantage_le_squareFree_add_coefficientAffine_add_batchLWE
      params implementation adversary)
    (negligible_add
      (negligible_add
        (hSquareFree adversary hadversary)
        (hCoefficientAffine adversary hadversary))
      (hBatchLWE _ (hBatchLWEClosed adversary hadversary)))

/-! ## Public deterministic FHE evaluation -/

/-- Public deterministic FHE evaluation adds no assumption to the exact restricted-component
security theorem. -/
theorem implementationEvaluationSecureAgainst_of_squareFree_coefficientAffine_and_batchLWE
    {Message Output : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (implementation : RingErrorFamily params)
    (evaluate : PublicEvaluatorFamily (Output := Output) params)
    (baseIsPPT : PolynomialQueryAdversary params → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary (Output := Output) params → Prop)
    (batchLWEIsPPT : BatchLWEAdversaryFamily params → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT (compileEvaluationAdversary params evaluate adversary))
    (hBatchLWEClosed : ∀ adversary, baseIsPPT adversary →
      batchLWEIsPPT (batchLWEReduction params adversary))
    (hSquareFree :
      (adaptiveSquareFreeSecurityGame params implementation).secureAgainst baseIsPPT)
    (hCoefficientAffine :
      (adaptiveCoefficientAffineCircularLWESecurityGame params implementation).secureAgainst
        baseIsPPT)
    (hBatchLWE : (batchLWESecurityGame params).secureAgainst batchLWEIsPPT) :
    (implementationEvaluationSecurityGame params implementation evaluate).secureAgainst
      evaluationIsPPT := by
  exact implementationEvaluationSecureAgainst_of_security
    params implementation evaluate baseIsPPT evaluationIsPPT hEvaluationClosed
    (implementationSecureAgainst_of_squareFree_coefficientAffine_and_batchLWE
      params implementation baseIsPPT batchLWEIsPPT hBatchLWEClosed hSquareFree
      hCoefficientAffine hBatchLWE)

end

end FormalProof4FHE.TFHE.Encryption.Adaptive.SharedRandomnessOneCycle.Asymptotic.CircularSecurity
