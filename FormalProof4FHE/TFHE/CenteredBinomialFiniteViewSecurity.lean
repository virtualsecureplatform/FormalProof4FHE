/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AsymptoticKeySwitchFirstUniversalCircular
import FormalProof4FHE.TFHE.AsymptoticKeySwitchFirstBRKCircular
import FormalProof4FHE.TFHE.CenteredBinomialInstantiation

/-!
# Centered-Binomial TFHE Security from Finite Augmented Views

This module specializes the asymptotic finite augmented-search theorem, its full-transcript
circular-decision normalization, and the sharper native one-challenge CircLWE plus
scalar-search-LWE decomposition to the executable centered-binomial TFHE family.
The sampler-totality premise is discharged exactly, and the family's scalar-dimension growth
witness supplies the polynomial-view bound.  The universal-schedule endpoint chooses logarithmic
amplification separately for every negligibility exponent, so no standalone majority-residual
security premise remains.  For the decision endpoint, the independent scalar-key guessing term
is negligible whenever the scalar dimension dominates the security parameter.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.CenteredBinomial

open Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView

/-- The executable scalar centered-binomial sampler never fails. -/
@[simp]
theorem scalarSampler_probFailure (q eta : ℕ) [NeZero q] :
    Pr[⊥ | scalarSampler q eta] = 0 := by
  simp [scalarSampler]

/-- Every centered-binomial key-switch sampler in a concrete family is total. -/
@[simp]
theorem Family.keySwitchError_probFailure {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)]
    (securityParameter : ℕ) :
    Pr[⊥ | family.parameters.keySwitchErrorSampler securityParameter] = 0 := by
  change Pr[⊥ |
    scalarSampler (family.q securityParameter)
      (family.keySwitchEta securityParameter)] = 0
  exact scalarSampler_probFailure _ _

/-- Construct the polynomial augmented-view schedule from the concrete family's scalar-dimension
bound and a polynomial bound on the majority-tree factor `3 ^ rounds`. -/
noncomputable def Family.polynomialViewSchedule {Message : Type}
    {family : Family Message}
    [∀ securityParameter, NeZero (family.q securityParameter)]
    (growth : family.PolynomialEvaluationKeyGrowth)
    (rounds : ℕ → ℕ)
    (reference : (securityParameter : ℕ) → Fin (family.lweDimension securityParameter))
    (amplificationPolynomial : Polynomial ℕ)
    (hAmplification : ∀ securityParameter,
      3 ^ rounds securityParameter ≤
        amplificationPolynomial.eval securityParameter) :
    PolynomialViewSchedule family.parameters :=
  polynomialViewScheduleOfBounds family.parameters rounds reference
    growth.lweDimensionPolynomial amplificationPolynomial
    growth.lweDimension_le hAmplification

/-- **Centered-binomial adaptive TFHE security from universal full-transcript circular
decision.**

Real augmented-batch scalar recovery is derived from the corresponding circular decision game;
the independent endpoint costs exactly `2⁻ˡʷᵉᴰⁱᵐᵉⁿˢⁱᵒⁿ`.  The lower dimension bound makes that
term negligible, while the concrete family discharges sampler totality and polynomial upper
growth. -/
theorem Family.secureAgainst_of_universal_batchCircular_and_lwe
    {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)]
    (growth : family.PolynomialEvaluationKeyGrowth)
    (reference : (securityParameter : ℕ) → Fin (family.lweDimension securityParameter))
    (hDimensionLower : ∀ securityParameter,
      securityParameter ≤ family.lweDimension securityParameter)
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters → Prop)
    (circularIsPPT : UniversalBatchCircularIsPPT family.parameters)
    (realRingBatchIsPPT zeroRingBatchIsPPT :
      Encryption.Adaptive.Asymptotic.CutCycleSecurity.RingBatchLWEAdversaryFamily
        family.parameters → Prop)
    (inputBatchIsPPT : InputBatchLWEAdversaryFamily family.parameters → Prop)
    (hCircularClosed : ∀ schedule adversary, isPPT adversary →
      circularIsPPT schedule
        (circularRecoveryReduction family.parameters schedule
          (searchReduction family.parameters schedule adversary)))
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT (realRingBatchReduction family.parameters adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT (zeroRingBatchReduction family.parameters adversary))
    (hInputBatchClosed : ∀ adversary, isPPT adversary →
      inputBatchIsPPT (inputBatchLWEReduction family.parameters adversary))
    (hCircular : ∀ schedule,
      (batchCircularSecurityGame family.parameters schedule).secureAgainst
        (circularIsPPT schedule))
    (hRealRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        family.parameters).secureAgainst realRingBatchIsPPT)
    (hZeroRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        family.parameters).secureAgainst zeroRingBatchIsPPT)
    (hInputBatch :
      (inputBatchLWESecurityGame family.parameters).secureAgainst inputBatchIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).secureAgainst isPPT :=
  Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView.secureAgainst_of_universal_batchCircular_and_lwe
    family.parameters family.keySwitchError_probFailure reference
    growth.lweDimensionPolynomial growth.lweDimension_le hDimensionLower isPPT
    circularIsPPT realRingBatchIsPPT zeroRingBatchIsPPT inputBatchIsPPT
    hCircularClosed hRealRingBatchClosed hZeroRingBatchClosed hInputBatchClosed
    hCircular hRealRingBatch hZeroRingBatch hInputBatch

/-- **Centered-binomial adaptive TFHE security from BRK-only circular security and conventional
scalar search LWE.**

All KSK and input-tape rows are compiled into one heterogeneous two-block scalar search-LWE
instance.  Circular pseudorandomness is assumed only for the same-secret batch of BRKs.  The
centered-binomial family discharges sampler totality and polynomial scalar-dimension growth. -/
theorem Family.secureAgainst_of_universal_bootstrapCircular_flatSearchLwe_and_lwe
    {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)]
    (growth : family.PolynomialEvaluationKeyGrowth)
    (reference : (securityParameter : ℕ) → Fin (family.lweDimension securityParameter))
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters → Prop)
    (circularIsPPT : UniversalBootstrapBatchCircularIsPPT family.parameters)
    (flatSearchIsPPT : UniversalFlatSideSearchLWEIsPPT family.parameters)
    (realRingBatchIsPPT zeroRingBatchIsPPT :
      Encryption.Adaptive.Asymptotic.CutCycleSecurity.RingBatchLWEAdversaryFamily
        family.parameters → Prop)
    (inputBatchIsPPT : InputBatchLWEAdversaryFamily family.parameters → Prop)
    (hCircularClosed : ∀ schedule adversary, isPPT adversary →
      circularIsPPT schedule
        (bootstrapBatchCircularReduction family.parameters schedule
          (searchReduction family.parameters schedule adversary)))
    (hFlatSearchClosed : ∀ schedule adversary, isPPT adversary →
      flatSearchIsPPT schedule
        (flatSideSearchLWEReduction family.parameters schedule
          (searchReduction family.parameters schedule adversary)))
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT (realRingBatchReduction family.parameters adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT (zeroRingBatchReduction family.parameters adversary))
    (hInputBatchClosed : ∀ adversary, isPPT adversary →
      inputBatchIsPPT (inputBatchLWEReduction family.parameters adversary))
    (hCircular : ∀ schedule,
      (bootstrapBatchCircularSecurityGame family.parameters schedule).secureAgainst
        (circularIsPPT schedule))
    (hFlatSearch : ∀ schedule,
      (flatSideSearchLWESecurityGame family.parameters schedule).secureAgainst
        (flatSearchIsPPT schedule))
    (hRealRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        family.parameters).secureAgainst realRingBatchIsPPT)
    (hZeroRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        family.parameters).secureAgainst zeroRingBatchIsPPT)
    (hInputBatch :
      (inputBatchLWESecurityGame family.parameters).secureAgainst inputBatchIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).secureAgainst isPPT :=
  Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView.secureAgainst_of_universal_bootstrapCircular_flatSearchLwe_and_lwe
    family.parameters family.keySwitchError_probFailure reference
    growth.lweDimensionPolynomial growth.lweDimension_le isPPT
    circularIsPPT flatSearchIsPPT realRingBatchIsPPT zeroRingBatchIsPPT
    inputBatchIsPPT hCircularClosed hFlatSearchClosed hRealRingBatchClosed
    hZeroRingBatchClosed hInputBatchClosed hCircular hFlatSearch
    hRealRingBatch hZeroRingBatch hInputBatch

/-- **Centered-binomial adaptive TFHE security from the existing native one-challenge
auxiliary-input CircLWE game and conventional scalar search LWE.**

The polynomial same-secret BRK batch is discharged by an exact randomized hybrid with loss equal
to its checked polynomial view count.  Thus no separate multi-view circular assumption remains:
the circular premise is the native real-versus-uniform BRK challenge retaining its real KSK. -/
theorem Family.secureAgainst_of_universal_nativeCircular_flatSearchLwe_and_lwe
    {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)]
    (growth : family.PolynomialEvaluationKeyGrowth)
    (reference : (securityParameter : ℕ) → Fin (family.lweDimension securityParameter))
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters → Prop)
    (nativeCircularIsPPT :
      Encryption.Adaptive.Asymptotic.ContinuationFamily family.parameters → Prop)
    (flatSearchIsPPT : UniversalFlatSideSearchLWEIsPPT family.parameters)
    (realRingBatchIsPPT zeroRingBatchIsPPT :
      Encryption.Adaptive.Asymptotic.CutCycleSecurity.RingBatchLWEAdversaryFamily
        family.parameters → Prop)
    (inputBatchIsPPT : InputBatchLWEAdversaryFamily family.parameters → Prop)
    (hNativeCircularClosed : ∀ schedule adversary, isPPT adversary →
      nativeCircularIsPPT
        (nativeCircularBatchReductionFamily family.parameters schedule
          (bootstrapBatchCircularReduction family.parameters schedule
            (searchReduction family.parameters schedule adversary))))
    (hFlatSearchClosed : ∀ schedule adversary, isPPT adversary →
      flatSearchIsPPT schedule
        (flatSideSearchLWEReduction family.parameters schedule
          (searchReduction family.parameters schedule adversary)))
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT (realRingBatchReduction family.parameters adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT (zeroRingBatchReduction family.parameters adversary))
    (hInputBatchClosed : ∀ adversary, isPPT adversary →
      inputBatchIsPPT (inputBatchLWEReduction family.parameters adversary))
    (hNativeCircular :
      (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.circularLWESecurityGame
        family.parameters).secureAgainst nativeCircularIsPPT)
    (hFlatSearch : ∀ schedule,
      (flatSideSearchLWESecurityGame family.parameters schedule).secureAgainst
        (flatSearchIsPPT schedule))
    (hRealRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        family.parameters).secureAgainst realRingBatchIsPPT)
    (hZeroRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        family.parameters).secureAgainst zeroRingBatchIsPPT)
    (hInputBatch :
      (inputBatchLWESecurityGame family.parameters).secureAgainst inputBatchIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).secureAgainst isPPT :=
  Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView.secureAgainst_of_universal_nativeCircular_flatSearchLwe_and_lwe
    family.parameters family.keySwitchError_probFailure reference
    growth.lweDimensionPolynomial growth.lweDimension_le isPPT
    nativeCircularIsPPT flatSearchIsPPT realRingBatchIsPPT zeroRingBatchIsPPT
    inputBatchIsPPT hNativeCircularClosed hFlatSearchClosed hRealRingBatchClosed
    hZeroRingBatchClosed hInputBatchClosed hNativeCircular hFlatSearch
    hRealRingBatch hZeroRingBatch hInputBatch

/-- **Centered-binomial adaptive TFHE security from native auxiliary-input CircLWE and one
ordinary combined-batch scalar search-LWE game.**

If the concrete KSK and input samplers coincide, all retained scalar rows form one conventional
matrix-LWE transcript.  The multi-view BRK term is still discharged from the native
one-challenge CircLWE game by the exact polynomial hybrid. -/
theorem Family.secureAgainst_of_universal_nativeCircular_ordinarySearchLwe_and_lwe
    {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)]
    (growth : family.PolynomialEvaluationKeyGrowth)
    (reference : (securityParameter : ℕ) → Fin (family.lweDimension securityParameter))
    (hScalarError : ∀ securityParameter,
      family.parameters.inputErrorSampler securityParameter =
        family.parameters.keySwitchErrorSampler securityParameter)
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters → Prop)
    (nativeCircularIsPPT :
      Encryption.Adaptive.Asymptotic.ContinuationFamily family.parameters → Prop)
    (ordinarySearchIsPPT : UniversalOrdinarySideSearchLWEIsPPT family.parameters)
    (realRingBatchIsPPT zeroRingBatchIsPPT :
      Encryption.Adaptive.Asymptotic.CutCycleSecurity.RingBatchLWEAdversaryFamily
        family.parameters → Prop)
    (inputBatchIsPPT : InputBatchLWEAdversaryFamily family.parameters → Prop)
    (hNativeCircularClosed : ∀ schedule adversary, isPPT adversary →
      nativeCircularIsPPT
        (nativeCircularBatchReductionFamily family.parameters schedule
          (bootstrapBatchCircularReduction family.parameters schedule
            (searchReduction family.parameters schedule adversary))))
    (hOrdinarySearchClosed : ∀ schedule adversary, isPPT adversary →
      ordinarySearchIsPPT schedule
        (ordinarySideSearchLWEReduction family.parameters schedule
          (searchReduction family.parameters schedule adversary)))
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT (realRingBatchReduction family.parameters adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT (zeroRingBatchReduction family.parameters adversary))
    (hInputBatchClosed : ∀ adversary, isPPT adversary →
      inputBatchIsPPT (inputBatchLWEReduction family.parameters adversary))
    (hNativeCircular :
      (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.circularLWESecurityGame
        family.parameters).secureAgainst nativeCircularIsPPT)
    (hOrdinarySearch : ∀ schedule,
      (ordinarySideSearchLWESecurityGame family.parameters schedule).secureAgainst
        (ordinarySearchIsPPT schedule))
    (hRealRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        family.parameters).secureAgainst realRingBatchIsPPT)
    (hZeroRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        family.parameters).secureAgainst zeroRingBatchIsPPT)
    (hInputBatch :
      (inputBatchLWESecurityGame family.parameters).secureAgainst inputBatchIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).secureAgainst isPPT :=
  Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView.secureAgainst_of_universal_nativeCircular_ordinarySearchLwe_and_lwe
    family.parameters family.keySwitchError_probFailure hScalarError reference
    growth.lweDimensionPolynomial growth.lweDimension_le isPPT
    nativeCircularIsPPT ordinarySearchIsPPT realRingBatchIsPPT zeroRingBatchIsPPT
    inputBatchIsPPT hNativeCircularClosed hOrdinarySearchClosed hRealRingBatchClosed
    hZeroRingBatchClosed hInputBatchClosed hNativeCircular hOrdinarySearch
    hRealRingBatch hZeroRingBatch hInputBatch

/-- **Centered-binomial adaptive TFHE security from universal polynomial-view augmented
search.**

For every negligibility exponent, the generic reduction selects a polynomial-size logarithmic
majority schedule.  The centered-binomial sampler-totality premise and the dimension-polynomial
bound are discharged by the concrete family, leaving universal augmented scalar-search hardness
and the three ordinary post-cut LWE assumptions. -/
theorem Family.secureAgainst_of_universal_finiteSearch_and_lwe
    {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)]
    (growth : family.PolynomialEvaluationKeyGrowth)
    (reference : (securityParameter : ℕ) → Fin (family.lweDimension securityParameter))
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters → Prop)
    (searchIsPPT : UniversalSearchIsPPT family.parameters)
    (realRingBatchIsPPT zeroRingBatchIsPPT :
      Encryption.Adaptive.Asymptotic.CutCycleSecurity.RingBatchLWEAdversaryFamily
        family.parameters → Prop)
    (inputBatchIsPPT : InputBatchLWEAdversaryFamily family.parameters → Prop)
    (hSearchClosed : ∀ schedule adversary, isPPT adversary →
      searchIsPPT schedule (searchReduction family.parameters schedule adversary))
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT (realRingBatchReduction family.parameters adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT (zeroRingBatchReduction family.parameters adversary))
    (hInputBatchClosed : ∀ adversary, isPPT adversary →
      inputBatchIsPPT (inputBatchLWEReduction family.parameters adversary))
    (hSearch : ∀ schedule,
      (searchSecurityGame family.parameters schedule).secureAgainst
        (searchIsPPT schedule))
    (hRealRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        family.parameters).secureAgainst realRingBatchIsPPT)
    (hZeroRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        family.parameters).secureAgainst zeroRingBatchIsPPT)
    (hInputBatch :
      (inputBatchLWESecurityGame family.parameters).secureAgainst inputBatchIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).secureAgainst isPPT :=
  Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView.secureAgainst_of_universal_finiteSearch_and_lwe
    family.parameters family.keySwitchError_probFailure reference
    growth.lweDimensionPolynomial growth.lweDimension_le isPPT searchIsPPT
    realRingBatchIsPPT zeroRingBatchIsPPT inputBatchIsPPT hSearchClosed
    hRealRingBatchClosed hZeroRingBatchClosed hInputBatchClosed hSearch
    hRealRingBatch hZeroRingBatch hInputBatch

/-- **Centered-binomial asymptotic adaptive TFHE security from finite augmented search.**

The generic theorem is instantiated with the executable centered-binomial ring, key-switch, and
input samplers.  Totality of key-switch noise is proved above.  This legacy form retains the exact
threshold-dependent deficit; the later balanced and capped-residual theorems replace it by
explicit terms. -/
theorem Family.secureAgainst_of_finiteSearch_and_lwe
    {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)]
    (schedule : PolynomialViewSchedule family.parameters)
    (threshold : ThresholdFamily family.parameters)
    (hthreshold_pos : ∀ adversary securityParameter,
      0 < threshold adversary securityParameter)
    (hthreshold_one : ∀ adversary securityParameter,
      threshold adversary securityParameter ≤ 1)
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters → Prop)
    (searchIsPPT : SearchAdversaryFamily family.parameters schedule → Prop)
    (realRingBatchIsPPT zeroRingBatchIsPPT :
      Encryption.Adaptive.Asymptotic.CutCycleSecurity.RingBatchLWEAdversaryFamily
        family.parameters → Prop)
    (inputBatchIsPPT : InputBatchLWEAdversaryFamily family.parameters → Prop)
    (hSearchClosed : ∀ adversary, isPPT adversary →
      searchIsPPT (searchReduction family.parameters schedule adversary))
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT (realRingBatchReduction family.parameters adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT (zeroRingBatchReduction family.parameters adversary))
    (hInputBatchClosed : ∀ adversary, isPPT adversary →
      inputBatchIsPPT (inputBatchLWEReduction family.parameters adversary))
    (hSearch : (searchSecurityGame family.parameters schedule).secureAgainst searchIsPPT)
    (hLoss : (lossSecurityGame family.parameters schedule threshold).secureAgainst isPPT)
    (hRealRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        family.parameters).secureAgainst realRingBatchIsPPT)
    (hZeroRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        family.parameters).secureAgainst zeroRingBatchIsPPT)
    (hInputBatch :
      (inputBatchLWESecurityGame family.parameters).secureAgainst inputBatchIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).secureAgainst isPPT :=
  Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView.secureAgainst_of_finiteSearch_and_lwe
    family.parameters family.keySwitchError_probFailure schedule threshold
    hthreshold_pos hthreshold_one isPPT searchIsPPT realRingBatchIsPPT
    zeroRingBatchIsPPT inputBatchIsPPT hSearchClosed hRealRingBatchClosed
    hZeroRingBatchClosed hInputBatchClosed hSearch hLoss hRealRingBatch
    hZeroRingBatch hInputBatch

/-- **Balanced centered-binomial finite-search security.** This stronger specialization replaces
the arbitrary threshold and opaque amplification deficit by the concrete balanced majority-error
game, with only constant-factor two losses. -/
theorem Family.secureAgainst_of_finiteSearch_and_balancedError_and_lwe
    {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)]
    (schedule : PolynomialViewSchedule family.parameters)
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters → Prop)
    (searchIsPPT : SearchAdversaryFamily family.parameters schedule → Prop)
    (realRingBatchIsPPT zeroRingBatchIsPPT :
      Encryption.Adaptive.Asymptotic.CutCycleSecurity.RingBatchLWEAdversaryFamily
        family.parameters → Prop)
    (inputBatchIsPPT : InputBatchLWEAdversaryFamily family.parameters → Prop)
    (hSearchClosed : ∀ adversary, isPPT adversary →
      searchIsPPT (searchReduction family.parameters schedule adversary))
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT (realRingBatchReduction family.parameters adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT (zeroRingBatchReduction family.parameters adversary))
    (hInputBatchClosed : ∀ adversary, isPPT adversary →
      inputBatchIsPPT (inputBatchLWEReduction family.parameters adversary))
    (hSearch : (searchSecurityGame family.parameters schedule).secureAgainst searchIsPPT)
    (hBalancedError :
      (balancedErrorSecurityGame family.parameters schedule).secureAgainst isPPT)
    (hRealRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        family.parameters).secureAgainst realRingBatchIsPPT)
    (hZeroRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        family.parameters).secureAgainst zeroRingBatchIsPPT)
    (hInputBatch :
      (inputBatchLWESecurityGame family.parameters).secureAgainst inputBatchIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).secureAgainst isPPT :=
  Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView.secureAgainst_of_finiteSearch_and_balancedError_and_lwe
    family.parameters family.keySwitchError_probFailure schedule isPPT searchIsPPT
    realRingBatchIsPPT zeroRingBatchIsPPT inputBatchIsPPT hSearchClosed
    hRealRingBatchClosed hZeroRingBatchClosed hInputBatchClosed hSearch
    hBalancedError hRealRingBatch hZeroRingBatch hInputBatch

/-- **Centered-binomial residual endpoint.** This is the preferred finite-search specialization:
the residual is explicitly capped by half the decision advantage and vanishes on zero-advantage
families. -/
theorem Family.secureAgainst_of_finiteSearch_and_residual_and_lwe
    {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)]
    (schedule : PolynomialViewSchedule family.parameters)
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters → Prop)
    (searchIsPPT : SearchAdversaryFamily family.parameters schedule → Prop)
    (realRingBatchIsPPT zeroRingBatchIsPPT :
      Encryption.Adaptive.Asymptotic.CutCycleSecurity.RingBatchLWEAdversaryFamily
        family.parameters → Prop)
    (inputBatchIsPPT : InputBatchLWEAdversaryFamily family.parameters → Prop)
    (hSearchClosed : ∀ adversary, isPPT adversary →
      searchIsPPT (searchReduction family.parameters schedule adversary))
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT (realRingBatchReduction family.parameters adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT (zeroRingBatchReduction family.parameters adversary))
    (hInputBatchClosed : ∀ adversary, isPPT adversary →
      inputBatchIsPPT (inputBatchLWEReduction family.parameters adversary))
    (hSearch : (searchSecurityGame family.parameters schedule).secureAgainst searchIsPPT)
    (hResidual :
      (balancedResidualSecurityGame family.parameters schedule).secureAgainst isPPT)
    (hRealRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        family.parameters).secureAgainst realRingBatchIsPPT)
    (hZeroRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        family.parameters).secureAgainst zeroRingBatchIsPPT)
    (hInputBatch :
      (inputBatchLWESecurityGame family.parameters).secureAgainst inputBatchIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).secureAgainst isPPT :=
  Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView.secureAgainst_of_finiteSearch_and_residual_and_lwe
    family.parameters family.keySwitchError_probFailure schedule isPPT searchIsPPT
    realRingBatchIsPPT zeroRingBatchIsPPT inputBatchIsPPT hSearchClosed
    hRealRingBatchClosed hZeroRingBatchClosed hInputBatchClosed hSearch
    hResidual hRealRingBatch hZeroRingBatch hInputBatch

/-- **Centered-binomial coordinate-error endpoint.** Polynomial view growth absorbs the full
coordinate sum, so only the single-coordinate majority recurrence must be shown negligible. -/
theorem Family.secureAgainst_of_finiteSearch_and_coordinateError_and_lwe
    {Message : Type} (family : Family Message)
    [∀ securityParameter, NeZero (family.q securityParameter)]
    (schedule : PolynomialViewSchedule family.parameters)
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters → Prop)
    (searchIsPPT : SearchAdversaryFamily family.parameters schedule → Prop)
    (realRingBatchIsPPT zeroRingBatchIsPPT :
      Encryption.Adaptive.Asymptotic.CutCycleSecurity.RingBatchLWEAdversaryFamily
        family.parameters → Prop)
    (inputBatchIsPPT : InputBatchLWEAdversaryFamily family.parameters → Prop)
    (hSearchClosed : ∀ adversary, isPPT adversary →
      searchIsPPT (searchReduction family.parameters schedule adversary))
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT (realRingBatchReduction family.parameters adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT (zeroRingBatchReduction family.parameters adversary))
    (hInputBatchClosed : ∀ adversary, isPPT adversary →
      inputBatchIsPPT (inputBatchLWEReduction family.parameters adversary))
    (hSearch : (searchSecurityGame family.parameters schedule).secureAgainst searchIsPPT)
    (hCoordinateError :
      (coordinateBalancedErrorSecurityGame family.parameters schedule).secureAgainst isPPT)
    (hRealRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        family.parameters).secureAgainst realRingBatchIsPPT)
    (hZeroRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        family.parameters).secureAgainst zeroRingBatchIsPPT)
    (hInputBatch :
      (inputBatchLWESecurityGame family.parameters).secureAgainst inputBatchIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).secureAgainst isPPT :=
  Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView.secureAgainst_of_finiteSearch_and_coordinateError_and_lwe
    family.parameters family.keySwitchError_probFailure schedule isPPT searchIsPPT
    realRingBatchIsPPT zeroRingBatchIsPPT inputBatchIsPPT hSearchClosed
    hRealRingBatchClosed hZeroRingBatchClosed hInputBatchClosed hSearch
    hCoordinateError hRealRingBatch hZeroRingBatch hInputBatch

end FormalProof4FHE.TFHE.CenteredBinomial
