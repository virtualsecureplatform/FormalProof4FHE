/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.CenteredBinomialFiniteViewSecurity
import FormalProof4FHE.TFHE.CenteredBinomialRefresh

/-!
# End-to-End Centered-Binomial TFHE Family

This module puts the conditional confidentiality theorem and the native refresh-correctness
theorem on one scalable Boolean parameter family.  At security parameter `λ` it uses ring degree
`N = λ + 1` and modulus `q = 2N`.  The latter is exactly the modulus required by the checked
signed-rotation lookup theorem.  Both gadget decompositions use base two and `2N` levels; this is
conservative but polynomial and makes exact reconstruction immediate.

The error distribution is executable centered binomial, as permitted by the finite variant of the
development.  KSK and fresh-input errors use the same width, so confidentiality reduces to the
exact native degree-two monomial-KDM game plus ordinary query-counted batch LWE.  Refresh is
correct with probability one under the two explicit public noise-margin inequalities.

Three named circular formulations are exposed.  The direct route assumes native
real-versus-uniform auxiliary-input CircLWE plus ordinary batch LWE.  One finite-view route uses a
full-transcript real-versus-independent circular decision game.  The sharper finite-view route
separates KSK and input rows into a conventional two-block scalar search-LWE instance and now
reduces its polynomial same-secret BRK batch exactly to one native CircLWE challenge with the
checked polynomial hybrid loss.  For this equal-noise family, a stronger wrapper concatenates the
two scalar blocks into one ordinary search-LWE batch.  The native circular premise remains
explicit and is not claimed to follow from ordinary LWE.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.CenteredBinomial.EndToEnd

open Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView

noncomputable section

/-- Exact base-two gadget parameters for the scalable modulus `q = 2(λ + 1)`.  Choosing the
number of levels equal to the modulus is deliberately conservative and gives a direct
`q < 2^q` capacity proof. -/
def exactRotationDecomposition (securityParameter : ℕ) :
    Gadget.Base.Parameters (2 * (securityParameter + 1)) where
  base := 2
  levels := 2 * (securityParameter + 1)
  one_lt_base := by omega
  modulus_le_capacity :=
    Nat.le_of_lt
      (show 2 * (securityParameter + 1) <
          2 ^ (2 * (securityParameter + 1)) from Nat.lt_two_pow_self)

/-- A fully specified scalable Boolean TFHE family shared by the security and correctness layers.
The scalar centered-binomial width is identical for KSK rows and fresh encryption queries. -/
def exactRotationFamily
    (ringEta scalarEta : ℕ → ℕ) : CenteredBinomial.Family Bool where
  q := fun securityParameter ↦ 2 * (securityParameter + 1)
  degree := fun securityParameter ↦ securityParameter + 1
  ringRank := fun _securityParameter ↦ 1
  lweDimension := fun securityParameter ↦ securityParameter + 1
  ringEta := ringEta
  keySwitchEta := scalarEta
  inputEta := scalarEta
  tgswDecomposition := exactRotationDecomposition
  keySwitchDecomposition := exactRotationDecomposition
  encode := fun securityParameter ↦ CenteredBinomialRefresh.inputCode securityParameter

/-- Every modulus in the exact-rotation family is nonzero. -/
instance instExactRotationFamilyNeZero
    (ringEta scalarEta : ℕ → ℕ) :
    ∀ securityParameter,
      NeZero ((exactRotationFamily ringEta scalarEta).q securityParameter) :=
  fun securityParameter ↦ ⟨by simp [exactRotationFamily]⟩

@[simp]
theorem exactRotationFamily_q (ringEta scalarEta : ℕ → ℕ)
    (securityParameter : ℕ) :
    (exactRotationFamily ringEta scalarEta).q securityParameter =
      2 * (securityParameter + 1) := rfl

@[simp]
theorem exactRotationFamily_degree (ringEta scalarEta : ℕ → ℕ)
    (securityParameter : ℕ) :
    (exactRotationFamily ringEta scalarEta).degree securityParameter =
      securityParameter + 1 := rfl

/-- The exact-rotation modulus is definitionally twice the ring degree at every parameter. -/
theorem exactRotationFamily_q_eq_two_mul_degree
    (ringEta scalarEta : ℕ → ℕ) (securityParameter : ℕ) :
    (exactRotationFamily ringEta scalarEta).q securityParameter =
      2 * (exactRotationFamily ringEta scalarEta).degree securityParameter := rfl

/-- KSK and input samplers coincide exactly, enabling the ordinary batch-LWE theorem. -/
theorem exactRotationFamily_scalarSamplers_eq
    (ringEta scalarEta : ℕ → ℕ) :
    ∀ securityParameter,
      (exactRotationFamily ringEta scalarEta).parameters.inputErrorSampler
          securityParameter =
        (exactRotationFamily ringEta scalarEta).parameters.keySwitchErrorSampler
          securityParameter :=
  (exactRotationFamily ringEta scalarEta).scalarSamplers_eq_of_eta_eq fun _ ↦ rfl

/-- All BRK and KSK dimensions of the exact-rotation family have explicit polynomial bounds. -/
def exactRotationFamily_polynomialEvaluationKeyGrowth
    (ringEta scalarEta : ℕ → ℕ) :
    (exactRotationFamily ringEta scalarEta).PolynomialEvaluationKeyGrowth where
  ringRankPolynomial := 1
  degreePolynomial := Polynomial.X + 1
  keySwitchLevelsPolynomial := 2 * (Polynomial.X + 1)
  tgswLevelsPolynomial := 2 * (Polynomial.X + 1)
  lweDimensionPolynomial := Polynomial.X + 1
  ringRank_le := by
    intro securityParameter
    simp [exactRotationFamily]
  degree_le := by
    intro securityParameter
    simp [exactRotationFamily]
  keySwitchLevels_le := by
    intro securityParameter
    simp [exactRotationFamily, exactRotationDecomposition]
  tgswLevels_le := by
    intro securityParameter
    simp [exactRotationFamily, exactRotationDecomposition]
  lweDimension_le := by
    intro securityParameter
    simp [exactRotationFamily]

/-! ## Conditional confidentiality and concrete refresh correctness -/

/-- The fully sharpened deterministic output budget of the exact-rotation family.  Even after
removing geometric trace propagation and exploiting sparse native factors, this exact `q = 2N`
model pays for every gadget row and every one of the `N` scalar controls. -/
theorem exactRotation_nativeLinearNoiseBudget_eq
    (securityParameter rowErrorBound : ℕ) :
    BootstrappingCorrectness.nativeLinearNoiseBudget securityParameter 1
        (exactRotationDecomposition securityParameter).levels
        (exactRotationDecomposition securityParameter).base
        (securityParameter + 1) rowErrorBound =
      8 * (securityParameter + 1) ^ 3 * rowErrorBound := by
  simp [BootstrappingCorrectness.nativeLinearNoiseBudget,
    BootstrappingCorrectness.linearExternalProductNoiseBudget,
    exactRotationDecomposition]
  ring

/-- **Checked parameter barrier for the exact-rotation witness.**  At coefficient modulus
`q = 2N`, no positive deterministic BRK row-error bound can satisfy the sharp output margin.
This is why a nonzero-noise production theorem must decouple the large ciphertext modulus from
the `2N` rotation index through modulus switching; further trace-bound sharpening alone cannot
repair this exact-modulus family. -/
theorem not_exactRotation_linearOutputMargin_of_pos
    (securityParameter rowErrorBound : ℕ) (hrowErrorBound : 0 < rowErrorBound)
    (zeroCode oneCode : ZMod (2 * (securityParameter + 1))) :
    ¬ 2 * BootstrappingCorrectness.nativeLinearNoiseBudget securityParameter 1
          (exactRotationDecomposition securityParameter).levels
          (exactRotationDecomposition securityParameter).base
          (securityParameter + 1) rowErrorBound <
        BootstrappingCorrectness.centeredDistance zeroCode oneCode := by
  intro hmargin
  have hdistance :
      BootstrappingCorrectness.centeredDistance zeroCode oneCode ≤
        securityParameter + 1 := by
    simpa using BootstrappingCorrectness.centeredDistance_le_half zeroCode oneCode
  have hparameter : 0 < securityParameter + 1 := by omega
  have hcofactor :
      1 ≤ 16 * (securityParameter + 1) ^ 2 * rowErrorBound := by
    apply Nat.one_le_iff_ne_zero.mpr
    exact mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 (by omega)))
      (by omega)
  have hbudget :
      securityParameter + 1 ≤
        2 * (8 * (securityParameter + 1) ^ 3 * rowErrorBound) := by
    calc
      securityParameter + 1 = (securityParameter + 1) * 1 := by simp
      _ ≤ (securityParameter + 1) *
          (16 * (securityParameter + 1) ^ 2 * rowErrorBound) :=
        Nat.mul_le_mul_left _ hcofactor
      _ = 2 * (8 * (securityParameter + 1) ^ 3 * rowErrorBound) := by ring
  rw [exactRotation_nativeLinearNoiseBudget_eq] at hmargin
  omega

/-- **Exact-rotation TFHE security from universal full-transcript circular decision.**

The scalar dimension is `securityParameter + 1`, so the independent recovery baseline is
negligible without an additional growth hypothesis.  The remaining circular premise is a
decision game on polynomially many complete augmented views; all post-cut terms are ordinary
ring or scalar batch LWE. -/
theorem secureAgainst_of_universal_batchCircular_and_lwe
    (ringEta scalarEta : ℕ → ℕ)
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      (exactRotationFamily ringEta scalarEta).parameters → Prop)
    (circularIsPPT : UniversalBatchCircularIsPPT
      (exactRotationFamily ringEta scalarEta).parameters)
    (realRingBatchIsPPT zeroRingBatchIsPPT :
      Encryption.Adaptive.Asymptotic.CutCycleSecurity.RingBatchLWEAdversaryFamily
        (exactRotationFamily ringEta scalarEta).parameters → Prop)
    (inputBatchIsPPT : InputBatchLWEAdversaryFamily
      (exactRotationFamily ringEta scalarEta).parameters → Prop)
    (hCircularClosed : ∀ schedule adversary, isPPT adversary →
      circularIsPPT schedule
        (circularRecoveryReduction
          (exactRotationFamily ringEta scalarEta).parameters schedule
          (searchReduction (exactRotationFamily ringEta scalarEta).parameters
            schedule adversary)))
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT
        (realRingBatchReduction
          (exactRotationFamily ringEta scalarEta).parameters adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT
        (zeroRingBatchReduction
          (exactRotationFamily ringEta scalarEta).parameters adversary))
    (hInputBatchClosed : ∀ adversary, isPPT adversary →
      inputBatchIsPPT
        (inputBatchLWEReduction
          (exactRotationFamily ringEta scalarEta).parameters adversary))
    (hCircular : ∀ schedule,
      (batchCircularSecurityGame
        (exactRotationFamily ringEta scalarEta).parameters schedule).secureAgainst
          (circularIsPPT schedule))
    (hRealRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst
          realRingBatchIsPPT)
    (hZeroRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst
          zeroRingBatchIsPPT)
    (hInputBatch :
      (inputBatchLWESecurityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst
          inputBatchIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame
      (exactRotationFamily ringEta scalarEta).parameters).secureAgainst isPPT :=
  (exactRotationFamily ringEta scalarEta).secureAgainst_of_universal_batchCircular_and_lwe
    (exactRotationFamily_polynomialEvaluationKeyGrowth ringEta scalarEta)
    (fun securityParameter ↦ ⟨0, by simp [exactRotationFamily]⟩)
    (by intro securityParameter; simp [exactRotationFamily])
    isPPT circularIsPPT realRingBatchIsPPT zeroRingBatchIsPPT inputBatchIsPPT
    hCircularClosed hRealRingBatchClosed hZeroRingBatchClosed hInputBatchClosed
    hCircular hRealRingBatch hZeroRingBatch hInputBatch

/-- **Exact-rotation TFHE security from BRK-only circular security and conventional scalar
search LWE.**

The circular premise now concerns only the polynomial same-secret batch of BRKs.  Every KSK and
input-tape row is compiled into a conventional heterogeneous two-block scalar search-LWE
experiment.  The remaining post-cut premises are the established ring and scalar batch-LWE
games. -/
theorem secureAgainst_of_universal_bootstrapCircular_flatSearchLwe_and_lwe
    (ringEta scalarEta : ℕ → ℕ)
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      (exactRotationFamily ringEta scalarEta).parameters → Prop)
    (circularIsPPT : UniversalBootstrapBatchCircularIsPPT
      (exactRotationFamily ringEta scalarEta).parameters)
    (flatSearchIsPPT : UniversalFlatSideSearchLWEIsPPT
      (exactRotationFamily ringEta scalarEta).parameters)
    (realRingBatchIsPPT zeroRingBatchIsPPT :
      Encryption.Adaptive.Asymptotic.CutCycleSecurity.RingBatchLWEAdversaryFamily
        (exactRotationFamily ringEta scalarEta).parameters → Prop)
    (inputBatchIsPPT : InputBatchLWEAdversaryFamily
      (exactRotationFamily ringEta scalarEta).parameters → Prop)
    (hCircularClosed : ∀ schedule adversary, isPPT adversary →
      circularIsPPT schedule
        (bootstrapBatchCircularReduction
          (exactRotationFamily ringEta scalarEta).parameters schedule
          (searchReduction (exactRotationFamily ringEta scalarEta).parameters
            schedule adversary)))
    (hFlatSearchClosed : ∀ schedule adversary, isPPT adversary →
      flatSearchIsPPT schedule
        (flatSideSearchLWEReduction
          (exactRotationFamily ringEta scalarEta).parameters schedule
          (searchReduction (exactRotationFamily ringEta scalarEta).parameters
            schedule adversary)))
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT
        (realRingBatchReduction
          (exactRotationFamily ringEta scalarEta).parameters adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT
        (zeroRingBatchReduction
          (exactRotationFamily ringEta scalarEta).parameters adversary))
    (hInputBatchClosed : ∀ adversary, isPPT adversary →
      inputBatchIsPPT
        (inputBatchLWEReduction
          (exactRotationFamily ringEta scalarEta).parameters adversary))
    (hCircular : ∀ schedule,
      (bootstrapBatchCircularSecurityGame
        (exactRotationFamily ringEta scalarEta).parameters schedule).secureAgainst
          (circularIsPPT schedule))
    (hFlatSearch : ∀ schedule,
      (flatSideSearchLWESecurityGame
        (exactRotationFamily ringEta scalarEta).parameters schedule).secureAgainst
          (flatSearchIsPPT schedule))
    (hRealRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst
          realRingBatchIsPPT)
    (hZeroRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst
          zeroRingBatchIsPPT)
    (hInputBatch :
      (inputBatchLWESecurityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst
          inputBatchIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame
      (exactRotationFamily ringEta scalarEta).parameters).secureAgainst isPPT :=
  (exactRotationFamily ringEta scalarEta).secureAgainst_of_universal_bootstrapCircular_flatSearchLwe_and_lwe
      (exactRotationFamily_polynomialEvaluationKeyGrowth ringEta scalarEta)
      (fun securityParameter ↦ ⟨0, by simp [exactRotationFamily]⟩)
      isPPT circularIsPPT flatSearchIsPPT realRingBatchIsPPT
      zeroRingBatchIsPPT inputBatchIsPPT hCircularClosed hFlatSearchClosed
      hRealRingBatchClosed hZeroRingBatchClosed hInputBatchClosed
      hCircular hFlatSearch hRealRingBatch hZeroRingBatch hInputBatch

/-- **Exact-rotation TFHE security from native one-challenge auxiliary-input CircLWE and
conventional scalar search LWE.**

The same-secret BRK batch used by logarithmic whole-key recovery is reduced by a single uniformly
random hybrid coordinate to the existing native CircLWE game.  Its exact polynomial view count
is absorbed into negligibility; every retained KSK/input row is handled by scalar search LWE. -/
theorem secureAgainst_of_universal_nativeCircular_flatSearchLwe_and_lwe
    (ringEta scalarEta : ℕ → ℕ)
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      (exactRotationFamily ringEta scalarEta).parameters → Prop)
    (nativeCircularIsPPT : Encryption.Adaptive.Asymptotic.ContinuationFamily
      (exactRotationFamily ringEta scalarEta).parameters → Prop)
    (flatSearchIsPPT : UniversalFlatSideSearchLWEIsPPT
      (exactRotationFamily ringEta scalarEta).parameters)
    (realRingBatchIsPPT zeroRingBatchIsPPT :
      Encryption.Adaptive.Asymptotic.CutCycleSecurity.RingBatchLWEAdversaryFamily
        (exactRotationFamily ringEta scalarEta).parameters → Prop)
    (inputBatchIsPPT : InputBatchLWEAdversaryFamily
      (exactRotationFamily ringEta scalarEta).parameters → Prop)
    (hNativeCircularClosed : ∀ schedule adversary, isPPT adversary →
      nativeCircularIsPPT
        (nativeCircularBatchReductionFamily
          (exactRotationFamily ringEta scalarEta).parameters schedule
          (bootstrapBatchCircularReduction
            (exactRotationFamily ringEta scalarEta).parameters schedule
            (searchReduction (exactRotationFamily ringEta scalarEta).parameters
              schedule adversary))))
    (hFlatSearchClosed : ∀ schedule adversary, isPPT adversary →
      flatSearchIsPPT schedule
        (flatSideSearchLWEReduction
          (exactRotationFamily ringEta scalarEta).parameters schedule
          (searchReduction (exactRotationFamily ringEta scalarEta).parameters
            schedule adversary)))
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT
        (realRingBatchReduction
          (exactRotationFamily ringEta scalarEta).parameters adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT
        (zeroRingBatchReduction
          (exactRotationFamily ringEta scalarEta).parameters adversary))
    (hInputBatchClosed : ∀ adversary, isPPT adversary →
      inputBatchIsPPT
        (inputBatchLWEReduction
          (exactRotationFamily ringEta scalarEta).parameters adversary))
    (hNativeCircular :
      (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.circularLWESecurityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst
          nativeCircularIsPPT)
    (hFlatSearch : ∀ schedule,
      (flatSideSearchLWESecurityGame
        (exactRotationFamily ringEta scalarEta).parameters schedule).secureAgainst
          (flatSearchIsPPT schedule))
    (hRealRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst
          realRingBatchIsPPT)
    (hZeroRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst
          zeroRingBatchIsPPT)
    (hInputBatch :
      (inputBatchLWESecurityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst
          inputBatchIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame
      (exactRotationFamily ringEta scalarEta).parameters).secureAgainst isPPT :=
  (exactRotationFamily ringEta scalarEta).secureAgainst_of_universal_nativeCircular_flatSearchLwe_and_lwe
      (exactRotationFamily_polynomialEvaluationKeyGrowth ringEta scalarEta)
      (fun securityParameter ↦ ⟨0, by simp [exactRotationFamily]⟩)
      isPPT nativeCircularIsPPT flatSearchIsPPT realRingBatchIsPPT
      zeroRingBatchIsPPT inputBatchIsPPT hNativeCircularClosed hFlatSearchClosed
      hRealRingBatchClosed hZeroRingBatchClosed hInputBatchClosed
      hNativeCircular hFlatSearch hRealRingBatch hZeroRingBatch hInputBatch

/-- **Exact-rotation TFHE security from native one-challenge auxiliary-input CircLWE and one
ordinary scalar search-LWE batch.**

The family's KSK and fresh-input centered-binomial samplers coincide definitionally, so every
retained scalar row is concatenated into a single conventional matrix-LWE transcript.  The
polynomial BRK batch is reduced exactly to the native CircLWE game. -/
theorem secureAgainst_of_universal_nativeCircular_ordinarySearchLwe_and_lwe
    (ringEta scalarEta : ℕ → ℕ)
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      (exactRotationFamily ringEta scalarEta).parameters → Prop)
    (nativeCircularIsPPT : Encryption.Adaptive.Asymptotic.ContinuationFamily
      (exactRotationFamily ringEta scalarEta).parameters → Prop)
    (ordinarySearchIsPPT : UniversalOrdinarySideSearchLWEIsPPT
      (exactRotationFamily ringEta scalarEta).parameters)
    (realRingBatchIsPPT zeroRingBatchIsPPT :
      Encryption.Adaptive.Asymptotic.CutCycleSecurity.RingBatchLWEAdversaryFamily
        (exactRotationFamily ringEta scalarEta).parameters → Prop)
    (inputBatchIsPPT : InputBatchLWEAdversaryFamily
      (exactRotationFamily ringEta scalarEta).parameters → Prop)
    (hNativeCircularClosed : ∀ schedule adversary, isPPT adversary →
      nativeCircularIsPPT
        (nativeCircularBatchReductionFamily
          (exactRotationFamily ringEta scalarEta).parameters schedule
          (bootstrapBatchCircularReduction
            (exactRotationFamily ringEta scalarEta).parameters schedule
            (searchReduction (exactRotationFamily ringEta scalarEta).parameters
              schedule adversary))))
    (hOrdinarySearchClosed : ∀ schedule adversary, isPPT adversary →
      ordinarySearchIsPPT schedule
        (ordinarySideSearchLWEReduction
          (exactRotationFamily ringEta scalarEta).parameters schedule
          (searchReduction (exactRotationFamily ringEta scalarEta).parameters
            schedule adversary)))
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT
        (realRingBatchReduction
          (exactRotationFamily ringEta scalarEta).parameters adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT
        (zeroRingBatchReduction
          (exactRotationFamily ringEta scalarEta).parameters adversary))
    (hInputBatchClosed : ∀ adversary, isPPT adversary →
      inputBatchIsPPT
        (inputBatchLWEReduction
          (exactRotationFamily ringEta scalarEta).parameters adversary))
    (hNativeCircular :
      (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.circularLWESecurityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst
          nativeCircularIsPPT)
    (hOrdinarySearch : ∀ schedule,
      (ordinarySideSearchLWESecurityGame
        (exactRotationFamily ringEta scalarEta).parameters schedule).secureAgainst
          (ordinarySearchIsPPT schedule))
    (hRealRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst
          realRingBatchIsPPT)
    (hZeroRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst
          zeroRingBatchIsPPT)
    (hInputBatch :
      (inputBatchLWESecurityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst
          inputBatchIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame
      (exactRotationFamily ringEta scalarEta).parameters).secureAgainst isPPT :=
  (exactRotationFamily ringEta scalarEta).secureAgainst_of_universal_nativeCircular_ordinarySearchLwe_and_lwe
      (exactRotationFamily_polynomialEvaluationKeyGrowth ringEta scalarEta)
      (fun securityParameter ↦ ⟨0, by simp [exactRotationFamily]⟩)
      (exactRotationFamily_scalarSamplers_eq ringEta scalarEta)
      isPPT nativeCircularIsPPT ordinarySearchIsPPT realRingBatchIsPPT
      zeroRingBatchIsPPT inputBatchIsPPT hNativeCircularClosed hOrdinarySearchClosed
      hRealRingBatchClosed hZeroRingBatchClosed hInputBatchClosed
      hNativeCircular hOrdinarySearch hRealRingBatch hZeroRingBatch hInputBatch

/-- **Conditional confidentiality of the exact-rotation centered-binomial family.**

The only computational premises are the exact native degree-two monomial-KDM game and ordinary
query-counted binary-secret batch LWE.  The former is precisely the circular-security assumption;
there is no sampler approximation premise because the honest and reference samplers coincide. -/
theorem secureAgainst_of_monomialKDM_and_batchLWE
    (ringEta scalarEta : ℕ → ℕ)
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      (exactRotationFamily ringEta scalarEta).parameters → Prop)
    (batchLWEIsPPT : Encryption.Adaptive.Asymptotic.BatchLWEAdversaryFamily
      (exactRotationFamily ringEta scalarEta).parameters → Prop)
    (hBatchLWEClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT
        (Encryption.Adaptive.Asymptotic.batchLWEReduction
          (exactRotationFamily ringEta scalarEta).parameters adversary))
    (hMonomialKDM :
      (Encryption.Adaptive.Asymptotic.MonomialKDM.adaptiveSecurityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst isPPT)
    (hBatchLWE :
      (Encryption.Adaptive.Asymptotic.batchLWESecurityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst batchLWEIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame
      (exactRotationFamily ringEta scalarEta).parameters).secureAgainst isPPT :=
  (exactRotationFamily ringEta scalarEta).secureAgainst_of_monomialKDM_and_batchLWE
    (fun _securityParameter ↦ rfl) isPPT batchLWEIsPPT hBatchLWEClosed
    hMonomialKDM hBatchLWE

/-- **Conditional confidentiality in the named auxiliary-input CircLWE formulation.**

This theorem replaces the native monomial-KDM premise above by the PKC 2024-style
real-versus-uniform CircLWE game and the explicit zero-message-versus-uniform side-information
game.  Both retain the real native KSK and use the exact centered-binomial sampler. -/
theorem secureAgainst_of_circularLWE_and_zeroLWE_and_batchLWE
    (ringEta scalarEta : ℕ → ℕ)
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      (exactRotationFamily ringEta scalarEta).parameters → Prop)
    (batchLWEIsPPT : Encryption.Adaptive.Asymptotic.BatchLWEAdversaryFamily
      (exactRotationFamily ringEta scalarEta).parameters → Prop)
    (hBatchLWEClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT
        (Encryption.Adaptive.Asymptotic.batchLWEReduction
          (exactRotationFamily ringEta scalarEta).parameters adversary))
    (hCircularLWE :
      (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.adaptiveCircularLWESecurityGame
          (exactRotationFamily ringEta scalarEta).parameters).secureAgainst isPPT)
    (hZeroLWE :
      (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.adaptiveZeroLWESecurityGame
          (exactRotationFamily ringEta scalarEta).parameters).secureAgainst isPPT)
    (hBatchLWE :
      (Encryption.Adaptive.Asymptotic.batchLWESecurityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst batchLWEIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame
      (exactRotationFamily ringEta scalarEta).parameters).secureAgainst isPPT :=
  (exactRotationFamily ringEta scalarEta).secureAgainst_of_circularLWE_and_zeroLWE_and_batchLWE
      (fun _securityParameter ↦ rfl) isPPT batchLWEIsPPT hBatchLWEClosed
      hCircularLWE hZeroLWE hBatchLWE

/-- **Strongest conditional confidentiality theorem for the exact-rotation family.**

The computational premises are the native auxiliary-input CircLWE game and ordinary
query-counted binary-secret batch LWE.  The uniform-BRK batch reduction is the only additional
efficiency-closure obligation; the former explicit zero-side security assumption has been proved
from these ordinary LWE games. -/
theorem secureAgainst_of_circularLWE_and_batchLWE
    (ringEta scalarEta : ℕ → ℕ)
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      (exactRotationFamily ringEta scalarEta).parameters → Prop)
    (batchLWEIsPPT : Encryption.Adaptive.Asymptotic.BatchLWEAdversaryFamily
      (exactRotationFamily ringEta scalarEta).parameters → Prop)
    (hBatchLWEClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT
        (Encryption.Adaptive.Asymptotic.batchLWEReduction
          (exactRotationFamily ringEta scalarEta).parameters adversary))
    (hUniformBootstrapBatchLWEClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT
        (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.uniformBootstrapBatchLWEReduction
          (exactRotationFamily ringEta scalarEta).parameters adversary))
    (hCircularLWE :
      (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.adaptiveCircularLWESecurityGame
          (exactRotationFamily ringEta scalarEta).parameters).secureAgainst isPPT)
    (hBatchLWE :
      (Encryption.Adaptive.Asymptotic.batchLWESecurityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst batchLWEIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame
      (exactRotationFamily ringEta scalarEta).parameters).secureAgainst isPPT :=
  (exactRotationFamily ringEta scalarEta).secureAgainst_of_circularLWE_and_batchLWE
    (fun _securityParameter ↦ rfl) isPPT batchLWEIsPPT hBatchLWEClosed
    hUniformBootstrapBatchLWEClosed hCircularLWE hBatchLWE

/-- Probability-one native Boolean refresh property for every member of the exact-rotation
family.  The two hypotheses are public arithmetic margins: fresh scalar noise must stay in the
correct lookup half, and the accumulated bootstrapping-key error must stay inside the decoding
radius. -/
def RefreshCorrect (ringEta scalarEta : ℕ → ℕ) : Prop :=
  ∀ (securityParameter : ℕ)
    (lweSecret : BinarySecret (securityParameter + 1))
    (ringSecret : RingBinarySecret 1 (securityParameter + 1))
    (zeroCode oneCode : ZMod (2 * (securityParameter + 1))) (bit : Bool),
    oneCode = -zeroCode →
    2 * scalarEta securityParameter < securityParameter + 1 →
    2 * BootstrappingCorrectness.nativeNoiseBudget securityParameter 1
        (exactRotationDecomposition securityParameter).levels
        (exactRotationDecomposition securityParameter).base
        (securityParameter + 1) (ringEta securityParameter) <
      BootstrappingCorrectness.centeredDistance zeroCode oneCode →
    Pr[(fun sample ↦
      CenteredBinomialCorrectness.bitTableBootstrappingResult
          (exactRotationDecomposition securityParameter) sample.1 sample.2
          ringSecret zeroCode oneCode
          (CenteredBinomialRefresh.firstHalfThreshold securityParameter) = bit) |
      CenteredBinomialRefresh.freshInputAndBootstrappingKey
        (exactRotationDecomposition securityParameter)
        (scalarEta securityParameter) (ringEta securityParameter)
        lweSecret ringSecret bit] = 1

/-- The exact-rotation centered-binomial family satisfies its refresh property.  Bounded support
eliminates a Gaussian tail event, so the probability is exactly one whenever the public margins
hold. -/
theorem refreshCorrect (ringEta scalarEta : ℕ → ℕ) :
    RefreshCorrect ringEta scalarEta := by
  intro securityParameter lweSecret ringSecret zeroCode oneCode bit
    hopposite hinputMargin houtputMargin
  exact CenteredBinomialRefresh.probEvent_fresh_bitTableBootstrappingResult_eq_one
    (exactRotationDecomposition securityParameter) lweSecret ringSecret zeroCode oneCode bit
    hopposite hinputMargin houtputMargin

/-- Probability-one native Boolean refresh under the sharp linear signed-rotation budget.  This
has the same concrete experiment as `RefreshCorrect`, but it does not geometrically amplify
errors contributed by earlier blind-rotation steps. -/
def RefreshCorrectLinear (ringEta scalarEta : ℕ → ℕ) : Prop :=
  ∀ (securityParameter : ℕ)
    (lweSecret : BinarySecret (securityParameter + 1))
    (ringSecret : RingBinarySecret 1 (securityParameter + 1))
    (zeroCode oneCode : ZMod (2 * (securityParameter + 1))) (bit : Bool),
    oneCode = -zeroCode →
    2 * scalarEta securityParameter < securityParameter + 1 →
    2 * BootstrappingCorrectness.nativeLinearNoiseBudget securityParameter 1
        (exactRotationDecomposition securityParameter).levels
        (exactRotationDecomposition securityParameter).base
        (securityParameter + 1) (ringEta securityParameter) <
      BootstrappingCorrectness.centeredDistance zeroCode oneCode →
    Pr[(fun sample ↦
      CenteredBinomialCorrectness.bitTableBootstrappingResult
          (exactRotationDecomposition securityParameter) sample.1 sample.2
          ringSecret zeroCode oneCode
          (CenteredBinomialRefresh.firstHalfThreshold securityParameter) = bit) |
      CenteredBinomialRefresh.freshInputAndBootstrappingKey
        (exactRotationDecomposition securityParameter)
        (scalarEta securityParameter) (ringEta securityParameter)
        lweSecret ringSecret bit] = 1

/-- The exact-rotation centered-binomial family satisfies the sharp linear refresh property. -/
theorem refreshCorrectLinear (ringEta scalarEta : ℕ → ℕ) :
    RefreshCorrectLinear ringEta scalarEta := by
  intro securityParameter lweSecret ringSecret zeroCode oneCode bit
    hopposite hinputMargin houtputMargin
  exact CenteredBinomialRefresh.probEvent_fresh_bitTableBootstrappingResult_eq_one_linear
    (exactRotationDecomposition securityParameter) lweSecret ringSecret zeroCode oneCode bit
    hopposite hinputMargin houtputMargin

/-- **End-to-end exact-rotation TFHE from native auxiliary-input CircLWE and one ordinary
combined-batch scalar search-LWE game.**

The first conclusion is adaptive confidentiality for the concrete centered-binomial family.  Its
polynomial BRK batch is reduced to one native CircLWE challenge, while equal KSK/input noises put
all retained scalar rows in one ordinary search-LWE transcript.  The second conclusion is the
probability-one native Boolean refresh theorem for the same parameters and samplers. -/
theorem secureAgainst_and_refreshCorrect_of_nativeCircular_ordinarySearchLwe
    (ringEta scalarEta : ℕ → ℕ)
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      (exactRotationFamily ringEta scalarEta).parameters → Prop)
    (nativeCircularIsPPT : Encryption.Adaptive.Asymptotic.ContinuationFamily
      (exactRotationFamily ringEta scalarEta).parameters → Prop)
    (ordinarySearchIsPPT : UniversalOrdinarySideSearchLWEIsPPT
      (exactRotationFamily ringEta scalarEta).parameters)
    (realRingBatchIsPPT zeroRingBatchIsPPT :
      Encryption.Adaptive.Asymptotic.CutCycleSecurity.RingBatchLWEAdversaryFamily
        (exactRotationFamily ringEta scalarEta).parameters → Prop)
    (inputBatchIsPPT : InputBatchLWEAdversaryFamily
      (exactRotationFamily ringEta scalarEta).parameters → Prop)
    (hNativeCircularClosed : ∀ schedule adversary, isPPT adversary →
      nativeCircularIsPPT
        (nativeCircularBatchReductionFamily
          (exactRotationFamily ringEta scalarEta).parameters schedule
          (bootstrapBatchCircularReduction
            (exactRotationFamily ringEta scalarEta).parameters schedule
            (searchReduction (exactRotationFamily ringEta scalarEta).parameters
              schedule adversary))))
    (hOrdinarySearchClosed : ∀ schedule adversary, isPPT adversary →
      ordinarySearchIsPPT schedule
        (ordinarySideSearchLWEReduction
          (exactRotationFamily ringEta scalarEta).parameters schedule
          (searchReduction (exactRotationFamily ringEta scalarEta).parameters
            schedule adversary)))
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT
        (realRingBatchReduction
          (exactRotationFamily ringEta scalarEta).parameters adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT
        (zeroRingBatchReduction
          (exactRotationFamily ringEta scalarEta).parameters adversary))
    (hInputBatchClosed : ∀ adversary, isPPT adversary →
      inputBatchIsPPT
        (inputBatchLWEReduction
          (exactRotationFamily ringEta scalarEta).parameters adversary))
    (hNativeCircular :
      (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.circularLWESecurityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst
          nativeCircularIsPPT)
    (hOrdinarySearch : ∀ schedule,
      (ordinarySideSearchLWESecurityGame
        (exactRotationFamily ringEta scalarEta).parameters schedule).secureAgainst
          (ordinarySearchIsPPT schedule))
    (hRealRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst
          realRingBatchIsPPT)
    (hZeroRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst
          zeroRingBatchIsPPT)
    (hInputBatch :
      (inputBatchLWESecurityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst
          inputBatchIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst isPPT ∧
      RefreshCorrect ringEta scalarEta :=
  ⟨secureAgainst_of_universal_nativeCircular_ordinarySearchLwe_and_lwe
      ringEta scalarEta isPPT nativeCircularIsPPT ordinarySearchIsPPT
      realRingBatchIsPPT zeroRingBatchIsPPT inputBatchIsPPT
      hNativeCircularClosed hOrdinarySearchClosed hRealRingBatchClosed
      hZeroRingBatchClosed hInputBatchClosed hNativeCircular hOrdinarySearch
      hRealRingBatch hZeroRingBatch hInputBatch,
    refreshCorrect ringEta scalarEta⟩

/-- **Sharp end-to-end exact-rotation TFHE theorem.**

This is the strongest native circular-security route paired with probability-one fresh Boolean
refresh under the linear signed-rotation noise budget.  The circular premise is still the explicit
native auxiliary-input CircLWE game; KSK and input rows use one ordinary search-LWE transcript. -/
theorem secureAgainst_and_refreshCorrectLinear_of_nativeCircular_ordinarySearchLwe
    (ringEta scalarEta : ℕ → ℕ)
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      (exactRotationFamily ringEta scalarEta).parameters → Prop)
    (nativeCircularIsPPT : Encryption.Adaptive.Asymptotic.ContinuationFamily
      (exactRotationFamily ringEta scalarEta).parameters → Prop)
    (ordinarySearchIsPPT : UniversalOrdinarySideSearchLWEIsPPT
      (exactRotationFamily ringEta scalarEta).parameters)
    (realRingBatchIsPPT zeroRingBatchIsPPT :
      Encryption.Adaptive.Asymptotic.CutCycleSecurity.RingBatchLWEAdversaryFamily
        (exactRotationFamily ringEta scalarEta).parameters → Prop)
    (inputBatchIsPPT : InputBatchLWEAdversaryFamily
      (exactRotationFamily ringEta scalarEta).parameters → Prop)
    (hNativeCircularClosed : ∀ schedule adversary, isPPT adversary →
      nativeCircularIsPPT
        (nativeCircularBatchReductionFamily
          (exactRotationFamily ringEta scalarEta).parameters schedule
          (bootstrapBatchCircularReduction
            (exactRotationFamily ringEta scalarEta).parameters schedule
            (searchReduction (exactRotationFamily ringEta scalarEta).parameters
              schedule adversary))))
    (hOrdinarySearchClosed : ∀ schedule adversary, isPPT adversary →
      ordinarySearchIsPPT schedule
        (ordinarySideSearchLWEReduction
          (exactRotationFamily ringEta scalarEta).parameters schedule
          (searchReduction (exactRotationFamily ringEta scalarEta).parameters
            schedule adversary)))
    (hRealRingBatchClosed : ∀ adversary, isPPT adversary →
      realRingBatchIsPPT
        (realRingBatchReduction
          (exactRotationFamily ringEta scalarEta).parameters adversary))
    (hZeroRingBatchClosed : ∀ adversary, isPPT adversary →
      zeroRingBatchIsPPT
        (zeroRingBatchReduction
          (exactRotationFamily ringEta scalarEta).parameters adversary))
    (hInputBatchClosed : ∀ adversary, isPPT adversary →
      inputBatchIsPPT
        (inputBatchLWEReduction
          (exactRotationFamily ringEta scalarEta).parameters adversary))
    (hNativeCircular :
      (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.circularLWESecurityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst
          nativeCircularIsPPT)
    (hOrdinarySearch : ∀ schedule,
      (ordinarySideSearchLWESecurityGame
        (exactRotationFamily ringEta scalarEta).parameters schedule).secureAgainst
          (ordinarySearchIsPPT schedule))
    (hRealRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst
          realRingBatchIsPPT)
    (hZeroRingBatch :
      (Encryption.Adaptive.Asymptotic.CutCycleSecurity.ringBatchLWESecurityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst
          zeroRingBatchIsPPT)
    (hInputBatch :
      (inputBatchLWESecurityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst
          inputBatchIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst isPPT ∧
      RefreshCorrectLinear ringEta scalarEta :=
  ⟨secureAgainst_of_universal_nativeCircular_ordinarySearchLwe_and_lwe
      ringEta scalarEta isPPT nativeCircularIsPPT ordinarySearchIsPPT
      realRingBatchIsPPT zeroRingBatchIsPPT inputBatchIsPPT
      hNativeCircularClosed hOrdinarySearchClosed hRealRingBatchClosed
      hZeroRingBatchClosed hInputBatchClosed hNativeCircular hOrdinarySearch
      hRealRingBatch hZeroRingBatch hInputBatch,
    refreshCorrectLinear ringEta scalarEta⟩

/-- **End-to-end theorem for the scalable centered-binomial Boolean family.**

Under native monomial-KDM circular security and ordinary batch LWE, the adaptive encryption game
has negligible advantage; independently, every fresh native Boolean refresh is correct with
probability one under the explicit deterministic margins.  Both conclusions use the same
`q = 2N` family, samplers, gadgets, and encoding. -/
theorem secureAgainst_and_refreshCorrect
    (ringEta scalarEta : ℕ → ℕ)
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      (exactRotationFamily ringEta scalarEta).parameters → Prop)
    (batchLWEIsPPT : Encryption.Adaptive.Asymptotic.BatchLWEAdversaryFamily
      (exactRotationFamily ringEta scalarEta).parameters → Prop)
    (hBatchLWEClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT
        (Encryption.Adaptive.Asymptotic.batchLWEReduction
          (exactRotationFamily ringEta scalarEta).parameters adversary))
    (hMonomialKDM :
      (Encryption.Adaptive.Asymptotic.MonomialKDM.adaptiveSecurityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst isPPT)
    (hBatchLWE :
      (Encryption.Adaptive.Asymptotic.batchLWESecurityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst batchLWEIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst isPPT ∧
      RefreshCorrect ringEta scalarEta :=
  ⟨secureAgainst_of_monomialKDM_and_batchLWE ringEta scalarEta isPPT batchLWEIsPPT
      hBatchLWEClosed hMonomialKDM hBatchLWE,
    refreshCorrect ringEta scalarEta⟩

/-- **End-to-end centered-binomial Boolean TFHE from auxiliary-input CircLWE and ordinary LWE.**
Confidentiality no longer assumes the zero-message side-information branch separately: that
branch is reduced to the actual-context and uniform-BRK-context batch-LWE games.  Native fresh
refresh correctness remains probability one under the public margins in `RefreshCorrect`. -/
theorem secureAgainst_and_refreshCorrect_of_circularLWE
    (ringEta scalarEta : ℕ → ℕ)
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      (exactRotationFamily ringEta scalarEta).parameters → Prop)
    (batchLWEIsPPT : Encryption.Adaptive.Asymptotic.BatchLWEAdversaryFamily
      (exactRotationFamily ringEta scalarEta).parameters → Prop)
    (hBatchLWEClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT
        (Encryption.Adaptive.Asymptotic.batchLWEReduction
          (exactRotationFamily ringEta scalarEta).parameters adversary))
    (hUniformBootstrapBatchLWEClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT
        (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.uniformBootstrapBatchLWEReduction
          (exactRotationFamily ringEta scalarEta).parameters adversary))
    (hCircularLWE :
      (Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput.adaptiveCircularLWESecurityGame
          (exactRotationFamily ringEta scalarEta).parameters).secureAgainst isPPT)
    (hBatchLWE :
      (Encryption.Adaptive.Asymptotic.batchLWESecurityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst batchLWEIsPPT) :
    (Encryption.Adaptive.Asymptotic.securityGame
        (exactRotationFamily ringEta scalarEta).parameters).secureAgainst isPPT ∧
      RefreshCorrect ringEta scalarEta :=
  ⟨secureAgainst_of_circularLWE_and_batchLWE
      ringEta scalarEta isPPT batchLWEIsPPT hBatchLWEClosed
      hUniformBootstrapBatchLWEClosed hCircularLWE hBatchLWE,
    refreshCorrect ringEta scalarEta⟩

end

end FormalProof4FHE.TFHE.CenteredBinomial.EndToEnd
