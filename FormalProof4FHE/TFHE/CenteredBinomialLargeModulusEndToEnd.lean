/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.CenteredBinomialDivisibleRefresh
import FormalProof4FHE.TFHE.CenteredBinomialFiniteViewSecurity

/-!
# Feasible Large-Modulus Centered-Binomial TFHE Family

This module replaces the diagnostic exact-`q = 2N` coefficient modulus by
`q = 16 N^4 = (2N)^4`.  The coefficient modulus is still divisible by the native rotation order
`2N`, so phase reduction is exact, while the output code distance is large enough for the fully
checked deterministic centered-binomial noise budget.  Both scalar and ring errors have width one,
the gadget base is `2N`, and four levels reconstruct `q` exactly.

For `N ≥ 8`, fresh Boolean refresh is proved correct with probability one with no arithmetic
margin hypotheses left to the caller.  Confidentiality remains conditional on the explicit native
auxiliary-input CircLWE and ordinary LWE/search-LWE games.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.CenteredBinomial.LargeModulusEndToEnd

open Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView

noncomputable section

/-- Ring degree `N` at security parameter `λ`. -/
def ringDegree (securityParameter : ℕ) : ℕ := securityParameter + 1

/-- Large coefficient modulus `q = 16N^4 = (2N)^4`. -/
def coefficientModulus (securityParameter : ℕ) : ℕ :=
  16 * ringDegree securityParameter ^ 4

instance instCoefficientModulusNeZero (securityParameter : ℕ) :
    NeZero (coefficientModulus securityParameter) :=
  ⟨by simp [coefficientModulus, ringDegree]⟩

/-- Four base-`2N` digits reconstruct the large modulus exactly. -/
def decomposition (securityParameter : ℕ) :
    Gadget.Base.Parameters (coefficientModulus securityParameter) where
  base := 2 * ringDegree securityParameter
  levels := 4
  one_lt_base := by
    simp [ringDegree]
    omega
  modulus_le_capacity := by
    change 16 * ringDegree securityParameter ^ 4 ≤
      (2 * ringDegree securityParameter) ^ 4
    ring_nf
    rfl

/-- The native signed-rotation order divides the coefficient modulus. -/
theorem rotationOrder_dvd_coefficientModulus (securityParameter : ℕ) :
    2 * ringDegree securityParameter ∣ coefficientModulus securityParameter := by
  refine ⟨8 * ringDegree securityParameter ^ 3, ?_⟩
  simp [coefficientModulus]
  ring

/-- Concrete centered-binomial Boolean family with unit-width ring, KSK, and input errors. -/
def family : CenteredBinomial.Family Bool where
  q := coefficientModulus
  degree := ringDegree
  ringRank := fun _ ↦ 1
  lweDimension := ringDegree
  ringEta := fun _ ↦ 1
  keySwitchEta := fun _ ↦ 1
  inputEta := fun _ ↦ 1
  tgswDecomposition := decomposition
  keySwitchDecomposition := decomposition
  encode := fun securityParameter ↦
    CenteredBinomialDivisibleRefresh.inputCode
      (coefficientModulus securityParameter) securityParameter

instance instFamilyNeZero :
    ∀ securityParameter, NeZero (family.q securityParameter) :=
  fun securityParameter ↦ ⟨by simp [family, coefficientModulus, ringDegree]⟩

/-- KSK and input error samplers coincide definitionally. -/
theorem scalarSamplers_eq :
    ∀ securityParameter,
      family.parameters.inputErrorSampler securityParameter =
        family.parameters.keySwitchErrorSampler securityParameter :=
  family.scalarSamplers_eq_of_eta_eq fun _ ↦ rfl

/-- Every evaluation-key dimension has an explicit polynomial bound. -/
def polynomialEvaluationKeyGrowth : family.PolynomialEvaluationKeyGrowth where
  ringRankPolynomial := 1
  degreePolynomial := Polynomial.X + 1
  keySwitchLevelsPolynomial := 4
  tgswLevelsPolynomial := 4
  lweDimensionPolynomial := Polynomial.X + 1
  ringRank_le := by
    intro securityParameter
    simp [family]
  degree_le := by
    intro securityParameter
    simp [family, ringDegree]
  keySwitchLevels_le := by
    intro securityParameter
    simp [family, decomposition]
  tgswLevels_le := by
    intro securityParameter
    simp [family, decomposition]
  lweDimension_le := by
    intro securityParameter
    simp [family, ringDegree]

/-! ## Fixed output codes and concrete margins -/

/-- Positive quarter-modulus output code. -/
def zeroCode (securityParameter : ℕ) : ZMod (coefficientModulus securityParameter) :=
  (4 * ringDegree securityParameter ^ 4 : ℕ)

/-- Opposite quarter-modulus output code. -/
def oneCode (securityParameter : ℕ) : ZMod (coefficientModulus securityParameter) :=
  -zeroCode securityParameter

@[simp]
theorem oneCode_eq_neg_zeroCode (securityParameter : ℕ) :
    oneCode securityParameter = -zeroCode securityParameter := rfl

/-- The two output codewords have the maximal centered distance `q/2 = 8N^4`. -/
theorem centeredDistance_zeroCode_oneCode (securityParameter : ℕ) :
    BootstrappingCorrectness.centeredDistance
        (zeroCode securityParameter) (oneCode securityParameter) =
      8 * ringDegree securityParameter ^ 4 := by
  have hdiff :
      zeroCode securityParameter - oneCode securityParameter =
        ((8 * ringDegree securityParameter ^ 4 : ℕ) :
          ZMod (coefficientModulus securityParameter)) := by
    simp only [oneCode, sub_neg_eq_add, zeroCode]
    push_cast
    ring
  rw [BootstrappingCorrectness.centeredDistance, hdiff]
  have hmodulus : coefficientModulus securityParameter =
      2 * (8 * ringDegree securityParameter ^ 4) := by
    unfold coefficientModulus
    ring_nf
  have hzlo :
      -(coefficientModulus securityParameter : ℤ) <
        ((8 * ringDegree securityParameter ^ 4 : ℕ) : ℤ) * 2 := by
    have hmodulusPosNat : 0 < coefficientModulus securityParameter := by
      simp [coefficientModulus, ringDegree]
    have hmodulusPosInt : (0 : ℤ) < coefficientModulus securityParameter := by
      exact_mod_cast hmodulusPosNat
    have hright :
        (0 : ℤ) ≤ ((8 * ringDegree securityParameter ^ 4 : ℕ) : ℤ) * 2 := by
      positivity
    omega
  have hzhi :
      ((8 * ringDegree securityParameter ^ 4 : ℕ) : ℤ) * 2 ≤
        coefficientModulus securityParameter := by
    rw [hmodulus]
    push_cast
    ring_nf
    rfl
  have hcentered := LatticeCrypto.centeredRepr_intCast_eq
    (q := coefficientModulus securityParameter)
    ((8 * ringDegree securityParameter ^ 4 : ℕ) : ℤ) hzlo hzhi
  change (LatticeCrypto.centeredRepr
    ((((8 * ringDegree securityParameter ^ 4 : ℕ) : ℤ)) :
      ZMod (coefficientModulus securityParameter))).natAbs = _
  rw [hcentered]
  exact Int.natAbs_natCast _

/-- Closed form of the sharp deterministic BRK budget for this family. -/
theorem nativeLinearNoiseBudget_eq (securityParameter : ℕ) :
    BootstrappingCorrectness.nativeLinearNoiseBudget securityParameter 1
        (decomposition securityParameter).levels
        (decomposition securityParameter).base
        (ringDegree securityParameter) 1 =
      16 * ringDegree securityParameter ^ 2 *
        (2 * ringDegree securityParameter - 1) := by
  change _ = 16 * (securityParameter + 1) ^ 2 *
    (2 * (securityParameter + 1) - 1)
  simp [BootstrappingCorrectness.nativeLinearNoiseBudget,
    BootstrappingCorrectness.linearExternalProductNoiseBudget,
    decomposition, ringDegree]
  ring

/-- At `N ≥ 8`, the sharp accumulated error fits strictly inside the quarter-modulus code
radius. -/
theorem outputMargin (securityParameter : ℕ) (hsecurity : 7 ≤ securityParameter) :
    2 * BootstrappingCorrectness.nativeLinearNoiseBudget securityParameter 1
          (decomposition securityParameter).levels
          (decomposition securityParameter).base
          (ringDegree securityParameter) 1 <
      BootstrappingCorrectness.centeredDistance
        (zeroCode securityParameter) (oneCode securityParameter) := by
  rw [nativeLinearNoiseBudget_eq, centeredDistance_zeroCode_oneCode]
  have hdegree : 8 ≤ ringDegree securityParameter := by
    simpa [ringDegree] using (show 8 ≤ securityParameter + 1 by omega)
  have hdegreePos : 0 < ringDegree securityParameter := by
    simp [ringDegree]
  have hsub : 2 * ringDegree securityParameter - 1 <
      2 * ringDegree securityParameter := by omega
  calc
    2 * (16 * ringDegree securityParameter ^ 2 *
        (2 * ringDegree securityParameter - 1)) =
        (32 * ringDegree securityParameter ^ 2) *
          (2 * ringDegree securityParameter - 1) := by ring
    _ < (32 * ringDegree securityParameter ^ 2) *
          (2 * ringDegree securityParameter) := by
      exact Nat.mul_lt_mul_of_pos_left hsub (by positivity)
    _ ≤ 8 * ringDegree securityParameter ^ 4 := by
      have hcofactor : 64 ≤ 8 * ringDegree securityParameter := by omega
      calc
        (32 * ringDegree securityParameter ^ 2) *
            (2 * ringDegree securityParameter) =
            ringDegree securityParameter ^ 3 * 64 := by ring
        _ ≤ ringDegree securityParameter ^ 3 *
            (8 * ringDegree securityParameter) :=
          Nat.mul_le_mul_left _ hcofactor
        _ = 8 * ringDegree securityParameter ^ 4 := by ring

/-! ## Probability-one refresh with no residual margin premises -/

/-- Concrete fresh Boolean refresh property for every security parameter `λ ≥ 7`. -/
def RefreshCorrect : Prop :=
  ∀ (securityParameter : ℕ), 7 ≤ securityParameter →
    ∀ (lweSecret : BinarySecret (ringDegree securityParameter))
      (ringSecret : RingBinarySecret 1 (ringDegree securityParameter))
      (bit : Bool),
    Pr[(fun sample ↦
      CenteredBinomialDivisibleRefresh.bitTableBootstrappingResult
          (decomposition securityParameter)
          (rotationOrder_dvd_coefficientModulus securityParameter)
          sample.1 sample.2 ringSecret
          (zeroCode securityParameter) (oneCode securityParameter)
          (CenteredBinomialRefresh.firstHalfThreshold securityParameter) = bit) |
      CenteredBinomialDivisibleRefresh.freshInputAndBootstrappingKey
        (decomposition securityParameter) 1 1 lweSecret ringSecret bit] = 1

/-- The large-modulus unit-noise family satisfies concrete fresh refresh correctness. -/
theorem refreshCorrect : RefreshCorrect := by
  intro securityParameter hsecurity lweSecret ringSecret bit
  apply CenteredBinomialDivisibleRefresh.probEvent_fresh_bitTableBootstrappingResult_eq_one
    (decomposition securityParameter)
    (rotationOrder_dvd_coefficientModulus securityParameter)
    lweSecret ringSecret (zeroCode securityParameter) (oneCode securityParameter) bit
  · rfl
  · omega
  · exact outputMargin securityParameter hsecurity

/-! ## Conditional confidentiality paired with concrete refresh -/

/-- **Large-modulus TFHE security and concrete nonzero-noise refresh.**

The confidentiality conclusion uses the checked strongest route: polynomially many BRKs reduce
to one native auxiliary-input CircLWE challenge, while equal KSK/input errors form one ordinary
scalar search-LWE batch; the three post-cut terms are ordinary LWE games.  The second conclusion
is unconditional functional correctness for this construction at every `λ ≥ 7`. -/
theorem secureAgainst_and_refreshCorrect_of_nativeCircular_ordinarySearchLwe
    (isPPT : Encryption.Adaptive.Asymptotic.PolynomialQueryAdversary
      family.parameters → Prop)
    (nativeCircularIsPPT : Encryption.Adaptive.Asymptotic.ContinuationFamily
      family.parameters → Prop)
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
    (Encryption.Adaptive.Asymptotic.securityGame family.parameters).secureAgainst isPPT ∧
      RefreshCorrect :=
  ⟨family.secureAgainst_of_universal_nativeCircular_ordinarySearchLwe_and_lwe
      polynomialEvaluationKeyGrowth
      (fun securityParameter ↦ ⟨0, by simp [family, ringDegree]⟩)
      scalarSamplers_eq isPPT nativeCircularIsPPT ordinarySearchIsPPT
      realRingBatchIsPPT zeroRingBatchIsPPT inputBatchIsPPT
      hNativeCircularClosed hOrdinarySearchClosed hRealRingBatchClosed
      hZeroRingBatchClosed hInputBatchClosed hNativeCircular hOrdinarySearch
      hRealRingBatch hZeroRingBatch hInputBatch,
    refreshCorrect⟩

end

end FormalProof4FHE.TFHE.CenteredBinomial.LargeModulusEndToEnd
