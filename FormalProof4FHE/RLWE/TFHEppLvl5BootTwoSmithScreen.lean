/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.RankOneHNFLossinessTwoSmith
import FormalProof4FHE.RLWE.TFHEppLvl5BootRenyiObstruction

set_option exponentiation.threshold 1024

/-!
# TFHEpp `lvl5bootparam` Two-Level Smith Screen

This module kernel-checks the finite support calculation emitted by
`Parameter-Selection/python/proof/lvl5boot_two_smith.py`.

For one actual TFHEpp RLWE row, translation by the fixed quadratic term leaves the public mask
uniform.  A distinct secret difference therefore produces a displacement uniform on its
principal multiplication image.  The exact two-level Smith theorem puts at least `20905985`
bits in that image for every fixed-weight ternary difference.  Meanwhile, two signed-int64
error polynomials have fewer than `2^(65*32768)` possible coefficientwise differences.

Lean proves the underlying finite-mask overlap count for an arbitrary finite commutative ring,
the union bound over an arbitrary candidate type, the literal power-of-two ring image lower
bound, and the resulting complete-codebook probability bound below `2^-18775027`.  The weaker
128-bit corollary is immediate.

This rejects a direct statistical cluster using the actual uniform mask; it is not an attack on
computational RLWE.  The proof-only DSPR/NTRU lossy coefficient family is not instantiated by
TFHEpp.  Its first unscreened total-order threshold is recorded explicitly rather than assigning
it an invented descriptor distribution.
-/

open BigOperators

namespace FormalProof4FHE.RLWE.TFHEppLvl5BootTwoSmithScreen

open FormalProof4FHE.RLWE.PowerOfTwoQuadraticKDMStatistical

noncomputable def overlapMasks
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    (difference : R) (allowed : Finset R) : Finset R :=
  Finset.univ.filter fun mask => mask * difference ∈ allowed

theorem overlapMasks_count_eq
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    (difference : R) (allowed : Finset R) :
    ((overlapMasks difference allowed).card : ℝ) =
      ∑ target ∈ allowed, principalFiberWeight difference target := by
  rw [show ((overlapMasks difference allowed).card : ℝ) =
      ∑ mask : R, if mask * difference ∈ allowed then (1 : ℝ) else 0 by
    simp [overlapMasks]]
  simp_rw [← rightMulFiberCount]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro mask _
  calc
    (if mask * difference ∈ allowed then (1 : ℝ) else 0) =
        ∑ target ∈ allowed,
          if mask * difference = target then (1 : ℝ) else 0 := by
      symm
      simp [eq_comm]
    _ = ∑ target ∈ allowed,
          if mask * difference = target then (1 : ℝ) else 0 := rfl

theorem principalFiberWeight_le_ratio
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    (difference target : R) :
    principalFiberWeight difference target ≤
      (Fintype.card R : ℝ) /
        Fintype.card (rightMulAddHom difference).range := by
  classical
  by_cases hmember : InPrincipalIdeal difference target
  · simp [principalFiberWeight, hmember]
  · rw [principalFiberWeight, if_neg hmember]
    exact div_nonneg (by positivity) (by positivity)

theorem overlapMasks_count_le
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    (difference : R) (allowed : Finset R) :
    ((overlapMasks difference allowed).card : ℝ) ≤
      allowed.card * ((Fintype.card R : ℝ) /
        Fintype.card (rightMulAddHom difference).range) := by
  rw [overlapMasks_count_eq]
  calc
    (∑ target ∈ allowed, principalFiberWeight difference target) ≤
        ∑ _target ∈ allowed,
          ((Fintype.card R : ℝ) /
            Fintype.card (rightMulAddHom difference).range) := by
      apply Finset.sum_le_sum
      intro target _
      exact principalFiberWeight_le_ratio difference target
    _ = allowed.card * ((Fintype.card R : ℝ) /
          Fintype.card (rightMulAddHom difference).range) := by simp

theorem overlapMasks_mass_le
    {R : Type} [CommRing R] [Fintype R] [Nonempty R] [DecidableEq R]
    (difference : R) (allowed : Finset R) :
    ((overlapMasks difference allowed).card : ℝ) / Fintype.card R ≤
      (allowed.card : ℝ) /
        Fintype.card (rightMulAddHom difference).range := by
  have hring : (0 : ℝ) < Fintype.card R := by positivity
  have himage : (0 : ℝ) <
      Fintype.card (rightMulAddHom difference).range := by positivity
  calc
    ((overlapMasks difference allowed).card : ℝ) / Fintype.card R ≤
        (allowed.card * ((Fintype.card R : ℝ) /
          Fintype.card (rightMulAddHom difference).range)) /
            Fintype.card R := by
      exact div_le_div_of_nonneg_right (overlapMasks_count_le difference allowed)
        hring.le
    _ = (allowed.card : ℝ) /
          Fintype.card (rightMulAddHom difference).range := by
      field_simp

noncomputable def anyOverlapMasks
    {R Candidate : Type} [CommRing R] [Fintype R] [DecidableEq R]
    [Fintype Candidate]
    (difference : Candidate → R) (allowed : Candidate → Finset R) : Finset R :=
  Finset.univ.biUnion fun candidate =>
    overlapMasks (difference candidate) (allowed candidate)

theorem card_anyOverlapMasks_le_sum
    {R Candidate : Type} [CommRing R] [Fintype R] [DecidableEq R]
    [Fintype Candidate]
    (difference : Candidate → R) (allowed : Candidate → Finset R) :
    (anyOverlapMasks difference allowed).card ≤
      ∑ candidate, (overlapMasks (difference candidate) (allowed candidate)).card := by
  exact Finset.card_biUnion_le

theorem anyOverlapMasks_mass_le
    {R Candidate : Type} [CommRing R] [Fintype R] [Nonempty R] [DecidableEq R]
    [Fintype Candidate]
    (difference : Candidate → R) (allowed : Candidate → Finset R)
    (differenceBound imageLower : ℕ)
    (hallowed : ∀ candidate, (allowed candidate).card ≤ differenceBound)
    (himage : ∀ candidate, imageLower ≤
      Fintype.card (rightMulAddHom (difference candidate)).range)
    (himagePos : 0 < imageLower) :
    ((anyOverlapMasks difference allowed).card : ℝ) / Fintype.card R ≤
      Fintype.card Candidate *
        ((differenceBound : ℝ) / imageLower) := by
  have hring : (0 : ℝ) < Fintype.card R := by positivity
  have himagePosReal : (0 : ℝ) < imageLower := by exact_mod_cast himagePos
  calc
    ((anyOverlapMasks difference allowed).card : ℝ) / Fintype.card R ≤
        ((∑ candidate,
          (overlapMasks (difference candidate) (allowed candidate)).card : ℕ) : ℝ) /
            Fintype.card R := by
      apply div_le_div_of_nonneg_right _ hring.le
      exact_mod_cast card_anyOverlapMasks_le_sum difference allowed
    _ = ∑ candidate,
          ((overlapMasks (difference candidate) (allowed candidate)).card : ℝ) /
            Fintype.card R := by
      rw [Nat.cast_sum, Finset.sum_div]
    _ ≤ ∑ _candidate : Candidate,
          ((differenceBound : ℝ) / imageLower) := by
      apply Finset.sum_le_sum
      intro candidate _
      refine (overlapMasks_mass_le
        (difference candidate) (allowed candidate)).trans ?_
      apply div_le_div₀
      · positivity
      · exact_mod_cast hallowed candidate
      · exact himagePosReal
      · exact_mod_cast himage candidate
    _ = Fintype.card Candidate *
          ((differenceBound : ℝ) / imageLower) := by simp

theorem lvl5_completeCodebook_uniformMaskOverlap_strong_lt
    {R Candidate : Type} [CommRing R] [Fintype R] [Nonempty R] [DecidableEq R]
    [Fintype Candidate]
    (difference : Candidate → R) (allowed : Candidate → Finset R)
    (hcandidate : Fintype.card Candidate < 2 ^ 1038)
    (hallowed : ∀ candidate, (allowed candidate).card < 2 ^ 2129920)
    (himage : ∀ candidate, 2 ^ 20905985 ≤
      Fintype.card (rightMulAddHom (difference candidate)).range) :
    ((anyOverlapMasks difference allowed).card : ℝ) / Fintype.card R <
      1 / (2 : ℝ) ^ 18775027 := by
  have hbase := anyOverlapMasks_mass_le difference allowed
    (2 ^ 2129920) (2 ^ 20905985)
    (fun candidate => Nat.le_of_lt (hallowed candidate)) himage (by positivity)
  have hbaseReal :
      ((anyOverlapMasks difference allowed).card : ℝ) / Fintype.card R ≤
        Fintype.card Candidate *
          ((2 : ℝ) ^ 2129920 / (2 : ℝ) ^ 20905985) := by
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using hbase
  have hcandidateReal : (Fintype.card Candidate : ℝ) < (2 : ℝ) ^ 1038 := by
    exact_mod_cast hcandidate
  calc
    ((anyOverlapMasks difference allowed).card : ℝ) / Fintype.card R ≤
        Fintype.card Candidate *
          ((2 : ℝ) ^ 2129920 / (2 : ℝ) ^ 20905985) := hbaseReal
    _ < (2 : ℝ) ^ 1038 *
          ((2 : ℝ) ^ 2129920 / (2 : ℝ) ^ 20905985) := by
      exact mul_lt_mul_of_pos_right hcandidateReal (by positivity)
    _ = 1 / (2 : ℝ) ^ 18775027 := by
      calc
        (2 : ℝ) ^ 1038 *
            ((2 : ℝ) ^ 2129920 / (2 : ℝ) ^ 20905985) =
            (2 : ℝ) ^ (1038 + 2129920) / (2 : ℝ) ^ 20905985 := by
          rw [pow_add, mul_div_assoc]
        _ = 1 / (2 : ℝ) ^ 18775027 := by
          rw [show 20905985 = (1038 + 2129920) + 18775027 by norm_num,
            pow_add]
          field_simp

theorem lvl5_completeCodebook_uniformMaskOverlap_lt
    {R Candidate : Type} [CommRing R] [Fintype R] [Nonempty R] [DecidableEq R]
    [Fintype Candidate]
    (difference : Candidate → R) (allowed : Candidate → Finset R)
    (hcandidate : Fintype.card Candidate < 2 ^ 1038)
    (hallowed : ∀ candidate, (allowed candidate).card < 2 ^ 2129920)
    (himage : ∀ candidate, 2 ^ 20905985 ≤
      Fintype.card (rightMulAddHom (difference candidate)).range) :
    ((anyOverlapMasks difference allowed).card : ℝ) / Fintype.card R <
      1 / (2 : ℝ) ^ 128 := by
  exact (lvl5_completeCodebook_uniformMaskOverlap_strong_lt
    difference allowed hcandidate hallowed himage).trans
      (by
        apply one_div_lt_one_div_of_lt (by positivity)
        exact pow_lt_pow_right₀ (by norm_num) (by norm_num))

theorem iidInformationSetFactor_eq
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (informationSet : Finset Index) (p pNext : ℝ) :
    (∏ _index ∈ Finset.univ \ informationSet, p) *
        (∏ _index ∈ informationSet, pNext) =
      p ^ (Fintype.card Index - informationSet.card) *
        pNext ^ informationSet.card := by
  simp [Finset.card_sdiff]

open FormalProof4FHE.RLWE
open FormalProof4FHE.RLWE.RankOneHNFLossinessSparseRank
open FormalProof4FHE.RLWE.RankOneHNFLossinessSparseRankChannel
open FormalProof4FHE.RLWE.RankOneHNFLossinessTwoSmith
open FormalProof4FHE.TFHE.Native.PowerOfTwoLocalRing

set_option maxRecDepth 10000 in
/-- The concrete fixed-weight signed-ternary support itself satisfies the candidate-cardinality
premise of the complete-codebook theorem. -/
theorem lvl5EncodedFixedWeightSecret_card_lt :
    Fintype.card (EncodedFixedWeightTernarySecret (2 ^ 15) 96) < 2 ^ 1038 := by
  rw [card_encodedFixedWeightTernarySecret]
  simpa only [show 2 ^ 15 = 32768 by norm_num] using
    TFHEppLvl5BootRenyiObstruction.lvl5SecretSupportCard_lt_two_pow

set_option maxRecDepth 10000 in
theorem lvl5_literalSecretDifference_image_lower
    (e : ℕ) (he : e ≤ 1)
    (primitive : QuotientRq (2 ^ 640) (2 ^ 15))
    {polynomial : Polynomial F2} (hne : polynomial ≠ 0)
    (hdegree : polynomial.natDegree < 2 ^ 15)
    (hreduction :
      quotientCoefficientReduce
          (pow_dvd_pow 2 (by norm_num : 1 ≤ 640)) primitive =
        binaryQuotientPolynomial 15 polynomial) :
    2 ^ 20905985 ≤ Nat.card
      (rightMulAddHom
        ((2 : QuotientRq (2 ^ 640) (2 ^ 15)) ^ e * primitive)).range := by
  letI : Fact (0 < 640) := ⟨by norm_num⟩
  rw [card_quotientPowerOfTwo_twoPrimary_range
    640 15 e (by omega) primitive hne hdegree hreduction]
  apply Nat.pow_le_pow_right (by norm_num)
  have hvaluation := hasseValuation_lt_of_ne_zero (2 ^ 15) hne hdegree
  norm_num at hvaluation ⊢
  omega

noncomputable def lvl5CoefficientDifferenceInterval : Finset ℤ :=
  Finset.Icc (-((2 : ℤ) ^ 64 - 1)) ((2 : ℤ) ^ 64 - 1)

theorem card_lvl5CoefficientDifferenceInterval :
    lvl5CoefficientDifferenceInterval.card = 2 ^ 65 - 1 := by
  rw [lvl5CoefficientDifferenceInterval, Int.card_Icc]
  norm_num
  decide

abbrev Lvl5ErrorDifferenceBox :=
  Fin 32768 → (lvl5CoefficientDifferenceInterval : Finset ℤ)

theorem card_lvl5ErrorDifferenceBox_lt :
    Fintype.card Lvl5ErrorDifferenceBox < 2 ^ 2129920 := by
  rw [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe,
    card_lvl5CoefficientDifferenceInterval]
  have hpow (degree : ℕ) (hdegree : degree ≠ 0) :
      (2 ^ 65 - 1) ^ degree < (2 ^ 65) ^ degree :=
    Nat.pow_lt_pow_left (by omega) hdegree
  calc
    (2 ^ 65 - 1) ^ 32768 < (2 ^ 65) ^ 32768 := by
      exact hpow 32768 (by norm_num)
    _ = 2 ^ 2129920 := by rw [← pow_mul]

/-- First total chain order for which the coarse complete-codebook support count no longer
forces a `2^-128` overlap bound. -/
def lvl5FirstUnscreenedDescriptorOrder : ℕ := 18840435

theorem lvl5FirstUnscreenedDescriptorOrder_decompose :
    lvl5FirstUnscreenedDescriptorOrder = 574 * 32768 + 31603 := by
  norm_num [lvl5FirstUnscreenedDescriptorOrder]

/-- Even the largest possible order `2*n-1` of a bare fixed-weight ternary difference lies far
inside the screened region. -/
theorem lvl5BareSecretOrder_lt_firstUnscreened :
    2 * 32768 - 1 < lvl5FirstUnscreenedDescriptorOrder := by
  norm_num [lvl5FirstUnscreenedDescriptorOrder]

/-- Starting from the worst bare-secret order, a descriptor factor would need at least this
much additional chain order merely to escape the coarse 128-bit screen. -/
theorem lvl5DescriptorAdditionalOrder_value :
    lvl5FirstUnscreenedDescriptorOrder - (2 * 32768 - 1) =
      572 * 32768 + 31604 := by
  norm_num [lvl5FirstUnscreenedDescriptorOrder]

/-- Arithmetic origin of the threshold: every total order below the first unscreened value
leaves enough image bits for the secret-cardinality, finite-support, and 128-bit factors. -/
theorem lvl5_screenedOrder_imageBudget
    (totalOrder : ℕ) (horder : totalOrder < lvl5FirstUnscreenedDescriptorOrder) :
    1038 + 2129920 + 128 ≤ 640 * 32768 - totalOrder := by
  simp only [lvl5FirstUnscreenedDescriptorOrder] at horder
  omega

set_option maxRecDepth 10000 in
theorem lvl5_literalCompleteCodebookOverlap_lt
    {Candidate : Type} [Fintype Candidate] [Fact (0 < 640)]
    (exponent : Candidate → ℕ) (hexponent : ∀ candidate, exponent candidate ≤ 1)
    (primitive : Candidate → QuotientRq (2 ^ 640) (2 ^ 15))
    (polynomial : Candidate → Polynomial F2)
    (hne : ∀ candidate, polynomial candidate ≠ 0)
    (hdegree : ∀ candidate, (polynomial candidate).natDegree < 2 ^ 15)
    (hreduction : ∀ candidate,
      quotientCoefficientReduce
          (pow_dvd_pow 2 (by norm_num : 1 ≤ 640)) (primitive candidate) =
        binaryQuotientPolynomial 15 (polynomial candidate))
    (allowed : Candidate → Finset (QuotientRq (2 ^ 640) (2 ^ 15)))
    (hcandidate : Fintype.card Candidate < 2 ^ 1038)
    (hallowed : ∀ candidate, (allowed candidate).card < 2 ^ 2129920) :
    ((anyOverlapMasks
        (fun candidate =>
          (2 : QuotientRq (2 ^ 640) (2 ^ 15)) ^ exponent candidate *
            primitive candidate)
        allowed).card : ℝ) /
        Fintype.card (QuotientRq (2 ^ 640) (2 ^ 15)) <
      1 / (2 : ℝ) ^ 128 := by
  apply lvl5_completeCodebook_uniformMaskOverlap_lt _ allowed hcandidate hallowed
  intro candidate
  rw [← Nat.card_eq_fintype_card]
  exact lvl5_literalSecretDifference_image_lower
    (exponent candidate) (hexponent candidate) (primitive candidate)
      (hne candidate) (hdegree candidate) (hreduction candidate)

end FormalProof4FHE.RLWE.TFHEppLvl5BootTwoSmithScreen
