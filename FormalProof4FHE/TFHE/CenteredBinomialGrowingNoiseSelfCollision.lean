/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.CenteredBinomialGrowingNoiseEndToEnd
import FormalProof4FHE.TFHE.NativeDiagonalUnitRowSupportBound

/-!
# Canonical Growing-Noise Native Self-Collision Bound

This module specializes the centered-support retained-row theorem to the concrete rank-one,
six-level centered-binomial TFHE family.  It proves that the centered support consumes at most
half of the full coefficient-ring alphabet after accounting for all polynomial coefficients.
The resulting selected-diagonal equal-difference self-collision term is exponentially small in
the growing ring degree.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.CenteredBinomial.GrowingNoiseEndToEnd

noncomputable section

open FormalProof4FHE.TFHE
open Native.ShiftedCandidateEvaluator.DiagonalNormalForm

/-- The exact deterministic transformed-error envelope for one retained row in the concrete
family. -/
def retainedRowNormBound (securityParameter : ℕ) : ℕ :=
  reconstructedRowTransformedErrorNormBound (decomposition securityParameter)
    (rotationDegree securityParameter) 1 (errorWidth securityParameter)

theorem retainedRowNormBound_eq (securityParameter : ℕ) :
    retainedRowNormBound securityParameter =
      errorWidth securityParameter +
        12 * ringDegree securityParameter *
          ((2 * ringDegree securityParameter - 1) * errorWidth securityParameter) := by
  simp [retainedRowNormBound, reconstructedRowTransformedErrorNormBound, decomposition,
    TGSW.rowCount, rotationDegree_add_one]
  ring

/-- The concrete modulus is exactly the sixth power of the decomposition base. -/
theorem decomposition_exactCapacity (securityParameter : ℕ) :
    coefficientModulus securityParameter =
      (decomposition securityParameter).base ^ (decomposition securityParameter).levels := by
  simp [coefficientModulus, decomposition]
  ring

theorem decomposition_base_le_modulus (securityParameter : ℕ) :
    (decomposition securityParameter).base ≤ coefficientModulus securityParameter := by
  have hdegree : 1 ≤ ringDegree securityParameter := by
    exact ringDegree_pos securityParameter
  simp only [decomposition, coefficientModulus]
  calc
    2 * ringDegree securityParameter ≤ 64 * ringDegree securityParameter := by omega
    _ ≤ 64 * ringDegree securityParameter ^ 6 := by
      gcongr
      calc
        ringDegree securityParameter = ringDegree securityParameter * 1 := by omega
        _ ≤ ringDegree securityParameter * ringDegree securityParameter ^ 5 := by
          gcongr
          exact Nat.one_le_pow 5 (ringDegree securityParameter) (ringDegree_pos securityParameter)
        _ = ringDegree securityParameter ^ 6 := by ring

/-- The source centered-binomial width is at most one eighth of the chosen ring degree. -/
theorem eight_mul_errorWidth_le_ringDegree (securityParameter : ℕ) :
    8 * errorWidth securityParameter ≤ ringDegree securityParameter :=
  targetDegree_le_ringDegree securityParameter

/-- Twice the one-row centered support alphabet fits inside the full coefficient modulus. -/
theorem two_mul_retainedRowSupportBase_le_modulus (securityParameter : ℕ) :
    2 * (2 * retainedRowNormBound securityParameter + 1) ≤
      coefficientModulus securityParameter := by
  let degree := ringDegree securityParameter
  let width := errorWidth securityParameter
  have hdegree : 8 ≤ degree := eight_le_ringDegree securityParameter
  have hwidth : 8 * width ≤ degree := eight_mul_errorWidth_le_ringDegree securityParameter
  have hwidthLe : width ≤ degree := by omega
  have hfactor : 2 * degree - 1 ≤ 2 * degree := Nat.sub_le _ _
  have hterm :
      12 * degree * ((2 * degree - 1) * width) ≤ 24 * degree ^ 3 := by
    calc
      12 * degree * ((2 * degree - 1) * width) ≤
          12 * degree * ((2 * degree) * degree) := by
        gcongr
      _ = 24 * degree ^ 3 := by ring
  have hdegreeCube : degree ≤ degree ^ 3 := by
    calc
      degree = degree * 1 := by omega
      _ ≤ degree * degree ^ 2 := by
        gcongr
        have : 1 ≤ degree := by omega
        exact Nat.one_le_pow 2 degree (by omega)
      _ = degree ^ 3 := by ring
  have henvelope :
      width + 12 * degree * ((2 * degree - 1) * width) ≤ 25 * degree ^ 3 := by
    calc
      width + 12 * degree * ((2 * degree - 1) * width) ≤
          degree + 24 * degree ^ 3 := Nat.add_le_add hwidthLe hterm
      _ ≤ degree ^ 3 + 24 * degree ^ 3 := Nat.add_le_add_right hdegreeCube _
      _ = 25 * degree ^ 3 := by ring
  have hcube : 2 ≤ degree ^ 3 := by
    have : 2 ≤ degree := by omega
    calc
      2 ≤ degree := this
      _ ≤ degree ^ 3 := hdegreeCube
  have hcoefficient : 101 ≤ 64 * degree ^ 3 := by omega
  rw [retainedRowNormBound_eq]
  change 2 * (2 *
      (width + 12 * degree * ((2 * degree - 1) * width)) + 1) ≤
    64 * degree ^ 6
  calc
    2 * (2 * (width + 12 * degree * ((2 * degree - 1) * width)) + 1) ≤
        4 * (25 * degree ^ 3) + 2 := by omega
    _ ≤ 101 * degree ^ 3 := by omega
    _ ≤ (64 * degree ^ 3) * degree ^ 3 := by
      exact Nat.mul_le_mul_right (degree ^ 3) hcoefficient
    _ = 64 * degree ^ 6 := by ring

/-- Complete centered target-support cardinality for one retained row. -/
def retainedRowSupportCard (securityParameter : ℕ) : ℕ :=
  reconstructedRowCenteredSupportCard (decomposition securityParameter)
    (rotationDegree securityParameter) 1 (errorWidth securityParameter)

theorem retainedRowSupportCard_eq (securityParameter : ℕ) :
    retainedRowSupportCard securityParameter =
      (2 * retainedRowNormBound securityParameter + 1) ^ ringDegree securityParameter := by
  simp [retainedRowSupportCard, reconstructedRowCenteredSupportCard, retainedRowNormBound,
    rotationDegree_add_one]

/-- Coefficientwise, a factor `2^N` times the complete centered row support still fits inside
the concrete ring carrier. -/
theorem twoPow_mul_retainedRowSupportCard_le_ringCard (securityParameter : ℕ) :
    2 ^ ringDegree securityParameter * retainedRowSupportCard securityParameter ≤
      coefficientModulus securityParameter ^ ringDegree securityParameter := by
  rw [retainedRowSupportCard_eq]
  calc
    2 ^ ringDegree securityParameter *
        (2 * retainedRowNormBound securityParameter + 1) ^ ringDegree securityParameter =
      (2 * (2 * retainedRowNormBound securityParameter + 1)) ^
        ringDegree securityParameter := by
      rw [mul_pow]
    _ ≤ coefficientModulus securityParameter ^ ringDegree securityParameter :=
      Nat.pow_le_pow_left
        (two_mul_retainedRowSupportBase_le_modulus securityParameter) _

/-- Cardinality of the concrete coefficient ring. -/
theorem card_concreteRq (securityParameter : ℕ) :
    Fintype.card
        (RLWE.Rq (coefficientModulus securityParameter) (ringDegree securityParameter)) =
      coefficientModulus securityParameter ^ ringDegree securityParameter := by
  exact Gadget.Base.card_rq (ringDegree securityParameter)

/-- The rank-one moment tuple consists of twelve concrete ring values. -/
theorem card_rankOneMomentTuple (securityParameter : ℕ) :
    Fintype.card
        (Fin 1 → Fin (TGSW.rowCount 1 (decomposition securityParameter).levels) →
          RLWE.Rq (coefficientModulus securityParameter) (ringDegree securityParameter)) =
      (coefficientModulus securityParameter ^ ringDegree securityParameter) ^ 12 := by
  change Fintype.card
      (Fin 1 → Fin 12 →
        RLWE.Rq (coefficientModulus securityParameter) (ringDegree securityParameter)) = _
  rw [Fintype.card_fun, Fintype.card_fun, card_concreteRq]
  rw [Fintype.card_fin, Fintype.card_fin]
  norm_num

/-- A rank-one, six-level native TGSW ciphertext contains twenty-four concrete ring values. -/
theorem card_rankOneRingGSWCiphertext (securityParameter : ℕ) :
    Fintype.card
        (RingGSWCiphertext (coefficientModulus securityParameter)
          (ringDegree securityParameter) 1 (decomposition securityParameter).levels) =
      (coefficientModulus securityParameter ^ ringDegree securityParameter) ^ 24 := by
  change Fintype.card
      ((Fin 1 → Fin 12 →
          RLWE.Rq (coefficientModulus securityParameter) (ringDegree securityParameter)) ×
        (Fin 12 →
          RLWE.Rq (coefficientModulus securityParameter) (ringDegree securityParameter))) = _
  rw [Fintype.card_prod]
  simp only [Fintype.card_fun, Fintype.card_fin]
  rw [card_concreteRq]
  ring

/-! ## Closed finite ratio -/

/-- Concrete closed form of the generic centered-support moment bound. -/
theorem fixedErrorDifferenceCenteredSupportMomentBound_eq (securityParameter : ℕ) :
    fixedErrorDifferenceCenteredSupportMomentBound 1 (decomposition securityParameter)
        (rotationDegree securityParameter) 1 (errorWidth securityParameter) =
      ((coefficientModulus securityParameter ^ ringDegree securityParameter : ℕ) : ℝ) ^ 12 *
        (retainedRowSupportCard securityParameter : ℝ) ^ 12 := by
  unfold fixedErrorDifferenceCenteredSupportMomentBound
  rw [show TGSW.rowCount 1 (decomposition securityParameter).levels = 12 by rfl]
  rw [rotationDegree_add_one]
  change
    (Fintype.card
        (Fin 1 → Fin 12 →
          RLWE.Rq (coefficientModulus securityParameter) (ringDegree securityParameter)) : ℝ) *
        (retainedRowSupportCard securityParameter : ℝ) ^ 12 = _
  have hcard := card_rankOneMomentTuple securityParameter
  change Fintype.card
      (Fin 1 → Fin 12 →
        RLWE.Rq (coefficientModulus securityParameter) (ringDegree securityParameter)) =
      (coefficientModulus securityParameter ^ ringDegree securityParameter) ^ 12 at hcard
  rw [hcard]
  push_cast
  rfl

/-- The closed moment numerator, multiplied by `2^N`, is at most the complete native TGSW
ciphertext cardinality. -/
theorem centeredSupportMomentNumerator_mul_twoPow_le_cipherCard
    (securityParameter : ℕ) :
    (coefficientModulus securityParameter ^ ringDegree securityParameter) ^ 12 *
          retainedRowSupportCard securityParameter ^ 12 *
        2 ^ ringDegree securityParameter ≤
      (coefficientModulus securityParameter ^ ringDegree securityParameter) ^ 24 := by
  let alphabet := 2 ^ ringDegree securityParameter
  let support := retainedRowSupportCard securityParameter
  let ringCard := coefficientModulus securityParameter ^ ringDegree securityParameter
  have halphabetSupport : alphabet * support ≤ ringCard :=
    twoPow_mul_retainedRowSupportCard_le_ringCard securityParameter
  have hpow : (alphabet * support) ^ 12 ≤ ringCard ^ 12 :=
    Nat.pow_le_pow_left halphabetSupport 12
  have halphabetPos : 0 < alphabet := by
    exact Nat.pow_pos (by norm_num)
  have halphabetLePow : alphabet ≤ alphabet ^ 12 := by
    calc
      alphabet = alphabet * 1 := by omega
      _ ≤ alphabet * alphabet ^ 11 := by
        gcongr
        exact Nat.one_le_pow 11 alphabet halphabetPos
      _ = alphabet ^ 12 := by ring
  have hsupportPow : alphabet * support ^ 12 ≤ ringCard ^ 12 := by
    calc
      alphabet * support ^ 12 ≤ alphabet ^ 12 * support ^ 12 := by
        exact Nat.mul_le_mul_right (support ^ 12) halphabetLePow
      _ = (alphabet * support) ^ 12 := by rw [mul_pow]
      _ ≤ ringCard ^ 12 := hpow
  change ringCard ^ 12 * support ^ 12 * alphabet ≤ ringCard ^ 24
  calc
    ringCard ^ 12 * support ^ 12 * alphabet =
        ringCard ^ 12 * (alphabet * support ^ 12) := by ring
    _ ≤ ringCard ^ 12 * ringCard ^ 12 :=
      Nat.mul_le_mul_left (ringCard ^ 12) hsupportPow
    _ = ringCard ^ 24 := by ring

/-- The concrete centered-support moment ratio is at most `2^{-N}`. -/
theorem fixedErrorDifferenceCenteredSupportMomentRatio_le_invTwoPow
    (securityParameter : ℕ) :
    fixedErrorDifferenceCenteredSupportMomentBound 1 (decomposition securityParameter)
          (rotationDegree securityParameter) 1 (errorWidth securityParameter) /
        (Fintype.card
          (RingGSWCiphertext (coefficientModulus securityParameter)
            (ringDegree securityParameter) 1 (decomposition securityParameter).levels) : ℝ) ≤
      ((2 : ℝ) ^ ringDegree securityParameter)⁻¹ := by
  rw [fixedErrorDifferenceCenteredSupportMomentBound_eq,
    card_rankOneRingGSWCiphertext, inv_eq_one_div]
  push_cast
  have hmodulus : (0 : ℝ) < coefficientModulus securityParameter := by
    exact_mod_cast Nat.zero_lt_of_lt (one_lt_coefficientModulus securityParameter)
  have hdenominator : (0 : ℝ) <
      ((coefficientModulus securityParameter : ℝ) ^ ringDegree securityParameter) ^ 24 := by
    exact pow_pos (pow_pos hmodulus _) _
  have halphabet : (0 : ℝ) < (2 : ℝ) ^ ringDegree securityParameter := by
    positivity
  apply (div_le_div_iff₀ hdenominator halphabet).2
  norm_num only [one_mul]
  exact_mod_cast centeredSupportMomentNumerator_mul_twoPow_le_cipherCard securityParameter

/-! ## Actual native self-collision slice -/

/-- **Concrete native self-collision theorem.**  For every fixed source-error vector in the
centered-binomial support and every selected unit coordinate, the actual equal-difference
selected-diagonal collision excess is at most `2^{-N}`. -/
theorem fixedErrorDiagonalNormalizedSelfPairCollisionExcess_le_invTwoPow
    (securityParameter : ℕ) (candidate : Bool)
    (sourceError :
      DiagonalErrorVector (coefficientModulus securityParameter)
        (rotationDegree securityParameter) 1 (decomposition securityParameter).levels)
    (hsource : ∀ sourceRow,
      LatticeCrypto.cInfNorm (sourceError sourceRow) ≤ errorWidth securityParameter)
    (selected : DifferenceDigitColumn 1 (decomposition securityParameter).levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    fixedErrorDiagonalNormalizedSelfPairCollisionExcess (decomposition securityParameter)
        candidate sourceError ≤
      ((2 : ℝ) ^ ringDegree securityParameter)⁻¹ := by
  calc
    fixedErrorDiagonalNormalizedSelfPairCollisionExcess (decomposition securityParameter)
        candidate sourceError ≤
      fixedErrorDifferenceCenteredSupportMomentBound 1 (decomposition securityParameter)
          (rotationDegree securityParameter) 1 (errorWidth securityParameter) /
        (Fintype.card
          (RingGSWCiphertext (coefficientModulus securityParameter)
            (rotationDegree securityParameter + 1) 1
            (decomposition securityParameter).levels) : ℝ) :=
      fixedErrorDiagonalNormalizedSelfPairCollisionExcess_le_centeredSupportMomentRatio
        (decomposition securityParameter) (decomposition_exactCapacity securityParameter)
        (decomposition_base_le_modulus securityParameter) candidate sourceError
        (errorWidth securityParameter) hsource selected hunit
    _ ≤ ((2 : ℝ) ^ ringDegree securityParameter)⁻¹ := by
      simpa only [rotationDegree_add_one] using
        fixedErrorDifferenceCenteredSupportMomentRatio_le_invTwoPow securityParameter

/-- ENNReal form of the explicit canonical self-collision envelope. -/
def canonicalSelfCollisionBound (securityParameter : ℕ) : ENNReal :=
  ((2 : ENNReal) ^ ringDegree securityParameter)⁻¹

/-- The explicit native self-collision envelope is negligible in the security parameter. -/
theorem canonicalSelfCollisionBound_negligible :
    negligible canonicalSelfCollisionBound := by
  apply
    FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView.binaryGuessingBound_negligible_of_securityParameter_le_dimension
  intro securityParameter
  have htarget : securityParameter ≤ targetDegree securityParameter := by
    simp [targetDegree, errorWidth]
    omega
  exact htarget.trans (targetDegree_le_ringDegree securityParameter)

end

end FormalProof4FHE.TFHE.CenteredBinomial.GrowingNoiseEndToEnd
