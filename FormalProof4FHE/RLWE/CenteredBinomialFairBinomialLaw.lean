/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.CenteredBinomialHintConcentration
import FormalProof4FHE.RLWE.CenteredBinomialMoment
import Mathlib.Data.Finset.Powerset

open OracleComp
open scoped BigOperators

/-!
# Exact Fair-Binomial Law of the Executable CBD Sampler

This file closes the distributional bridge between the implementation sampler, which draws
`eta` pairs of fair bits, and the fair-binomial coefficient tables used by the hint-concentration
calculation.  It also constructs the concrete three adjacent translates required for a uniform
ternary secret.
-/

namespace FormalProof4FHE.RLWE.CenteredBinomialFairBinomialLaw
noncomputable section

def boolWeight {A : Type} [Fintype A] (bits : A → Bool) : ℕ :=
  ∑ index, if bits index then 1 else 0

def boolSupport {A : Type} [Fintype A] (bits : A → Bool) : Finset A :=
  Finset.univ.filter fun index => bits index

theorem card_boolSupport {A : Type} [Fintype A] (bits : A → Bool) :
    (boolSupport bits).card = boolWeight bits := by
  classical
  unfold boolSupport boolWeight
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

def boolFunctionFinsetEquiv (A : Type) [Fintype A] [DecidableEq A] :
    (A → Bool) ≃ Finset A where
  toFun bits := boolSupport bits
  invFun support index := decide (index ∈ support)
  left_inv bits := by
    funext index
    cases h : bits index <;> simp [boolSupport, h]
  right_inv support := by
    ext index
    simp [boolSupport]

theorem boolWeight_membership {A : Type} [Fintype A] [DecidableEq A]
    (support : Finset A) :
    boolWeight (fun index => decide (index ∈ support)) = support.card := by
  rw [← card_boolSupport]
  congr 1
  ext index
  simp [boolSupport]

theorem card_boolWeight_fiber (A : Type) [Fintype A] [DecidableEq A] (weight : ℕ) :
    (Finset.univ.filter fun bits : A → Bool => boolWeight bits = weight).card =
      Nat.choose (Fintype.card A) weight := by
  calc
    _ = (Finset.powersetCard weight (Finset.univ : Finset A)).card := by
      apply Finset.card_bij'
          (fun bits _ => boolFunctionFinsetEquiv A bits)
          (fun support _ => (boolFunctionFinsetEquiv A).symm support)
      · intro bits hbits
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hbits
        simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and]
        simpa [boolFunctionFinsetEquiv, card_boolSupport] using hbits
      · intro support hsupport
        simp only [Finset.mem_powersetCard, Finset.subset_univ, true_and] at hsupport
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [boolFunctionFinsetEquiv, boolWeight_membership] using hsupport
      · intro bits _
        exact (boolFunctionFinsetEquiv A).symm_apply_apply bits
      · intro support _
        exact (boolFunctionFinsetEquiv A).apply_symm_apply support
    _ = _ := by rw [Finset.card_powersetCard]; simp

open FormalProof4FHE.RLWE.CenteredBinomial

def flattenedCoinBits {eta : ℕ} (coins : CoinRow eta) : Fin eta × Bool → Bool
  | (index, false) => (coins index).1
  | (index, true) => !(coins index).2

def coinRowFlattenEquiv (eta : ℕ) : CoinRow eta ≃ (Fin eta × Bool → Bool) where
  toFun := flattenedCoinBits
  invFun bits index := (bits (index, false), !(bits (index, true)))
  left_inv coins := by
    funext index
    simp [flattenedCoinBits]
  right_inv bits := by
    funext input
    obtain ⟨index, bit⟩ := input
    cases bit <;> simp [flattenedCoinBits]

def coefficientIndex {eta : ℕ} (coins : CoinRow eta) : ℕ :=
  boolWeight (flattenedCoinBits coins)

theorem coefficientIndex_le {eta : ℕ} (coins : CoinRow eta) :
    coefficientIndex coins ≤ 2 * eta := by
  calc
    coefficientIndex coins ≤ ∑ _ : Fin eta × Bool, 1 := by
      apply Finset.sum_le_sum
      intro input _
      split <;> simp
    _ = 2 * eta := by simp; omega

def coefficientIndexFin {eta : ℕ} (coins : CoinRow eta) : Fin (2 * eta + 1) :=
  ⟨coefficientIndex coins, by
    have h := coefficientIndex_le coins
    omega⟩

theorem coefficientIndex_eq_positive_add_complement {eta : ℕ} (coins : CoinRow eta) :
    coefficientIndex coins = positiveWeight coins + (eta - negativeWeight coins) := by
  have hbalance : coefficientIndex coins + negativeWeight coins =
      positiveWeight coins + eta := by
    unfold coefficientIndex boolWeight positiveWeight negativeWeight
    rw [Fintype.sum_prod_type]
    simp_rw [Fintype.sum_bool]
    simp only [flattenedCoinBits]
    rw [Finset.sum_add_distrib]
    calc
      (∑ x, (if !(coins x).2 then 1 else 0)) +
          (∑ x, if (coins x).1 then 1 else 0) +
          (∑ x, if (coins x).2 then 1 else 0) =
        (∑ x, if (coins x).1 then 1 else 0) +
          (∑ x, ((if !(coins x).2 then 1 else 0) +
            (if (coins x).2 then 1 else 0))) := by
              rw [Finset.sum_add_distrib]
              omega
      _ = (∑ x, if (coins x).1 then 1 else 0) + (∑ _x : Fin eta, 1) := by
            congr 1
            apply Finset.sum_congr rfl
            intro x _
            cases (coins x).2 <;> simp
      _ = (∑ x, if (coins x).1 then 1 else 0) + eta := by simp
  have hneg := negativeWeight_le coins
  omega

theorem coefficientIndex_int_sub_eta {eta : ℕ} (coins : CoinRow eta) :
    (coefficientIndex coins : ℤ) - eta = signedWeight coins := by
  rw [coefficientIndex_eq_positive_add_complement]
  unfold signedWeight
  have hneg := negativeWeight_le coins
  omega

theorem card_coefficientIndex_fiber (eta weight : ℕ) :
    (Finset.univ.filter fun coins : CoinRow eta => coefficientIndex coins = weight).card =
      Nat.choose (2 * eta) weight := by
  have hcard := card_boolWeight_fiber (Fin eta × Bool) weight
  rw [show Fintype.card (Fin eta × Bool) = 2 * eta by simp; omega] at hcard
  rw [← hcard]
  apply Finset.card_bij'
      (fun coins _ => coinRowFlattenEquiv eta coins)
      (fun bits _ => (coinRowFlattenEquiv eta).symm bits)
  · intro coins hcoins
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hcoins ⊢
    change coefficientIndex coins = weight at hcoins
    exact hcoins
  · intro bits hbits
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hbits ⊢
    change boolWeight ((coinRowFlattenEquiv eta) ((coinRowFlattenEquiv eta).symm bits)) = weight
    rw [(coinRowFlattenEquiv eta).apply_symm_apply]
    exact hbits
  · intro coins _
    exact (coinRowFlattenEquiv eta).symm_apply_apply coins
  · intro bits _
    exact (coinRowFlattenEquiv eta).apply_symm_apply bits

def coefficientIndexSampler (eta : ℕ) : ProbComp (Fin (2 * eta + 1)) :=
  coefficientIndexFin <$> ($ᵗ (CoinRow eta))

theorem probabilityMass_coefficientIndexSampler (eta : ℕ)
    (index : Fin (2 * eta + 1)) :
    FormalProof4FHE.WeightedSquare.probabilityMass
        (coefficientIndexSampler eta) index =
      (Nat.choose (2 * eta) index.val : ℝ) / (2 : ℝ) ^ (2 * eta) := by
  unfold FormalProof4FHE.WeightedSquare.probabilityMass coefficientIndexSampler
  rw [probOutput_map]
  simp only [Fin.ext_iff, coefficientIndexFin]
  change Pr[(fun coins : CoinRow eta => coefficientIndex coins = index.val) |
    $ᵗ (CoinRow eta)].toReal = _
  rw [probEvent_uniformSample, card_coefficientIndex_fiber]
  rw [ENNReal.toReal_div]
  · simp only [ENNReal.toReal_natCast]
    rw [show Fintype.card (CoinRow eta) = 2 ^ (2 * eta) by
      rw [Fintype.card_congr (coinRowFlattenEquiv eta)]
      simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_prod,
        Fintype.card_fin]
      congr 1
      omega]
    norm_num

/-- Signed integer represented by a fair-binomial Hamming-weight index. -/
def signedIndexValue {eta : ℕ} (index : Fin (2 * eta + 1)) : ℤ :=
  (index.val : ℤ) - eta

theorem signedIndexValue_natAbs_le {eta : ℕ} (index : Fin (2 * eta + 1)) :
    (signedIndexValue index).natAbs ≤ eta := by
  unfold signedIndexValue
  rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs, abs_le]
  constructor <;> omega

theorem coefficientSampler_eq_map_coefficientIndexSampler
    (q eta : ℕ) [NeZero q] :
    coefficientSampler q eta =
      (fun index : Fin (2 * eta + 1) => (signedIndexValue index : ZMod q)) <$>
        coefficientIndexSampler eta := by
  unfold coefficientSampler coefficientIndexSampler
  simp only [Functor.map_map]
  apply congrArg (fun transform => transform <$> ($ᵗ (CoinRow eta)))
  funext coins
  change (signedWeight coins : ZMod q) =
    (((coefficientIndex coins : ℤ) - eta : ℤ) : ZMod q)
  rw [coefficientIndex_int_sub_eta]

theorem signedIndexCast_injective
    (q eta : ℕ) [NeZero q] (hNoWrap : 2 * eta < q) :
    Function.Injective
      (fun index : Fin (2 * eta + 1) => (signedIndexValue index : ZMod q)) := by
  intro left right heq
  apply Fin.ext
  have hrepr := congrArg LatticeCrypto.centeredRepr heq
  rw [LatticeCrypto.centeredRepr_intCast_eq_of_natAbs_le
        (signedIndexValue left) (signedIndexValue_natAbs_le left) hNoWrap,
      LatticeCrypto.centeredRepr_intCast_eq_of_natAbs_le
        (signedIndexValue right) (signedIndexValue_natAbs_le right) hNoWrap] at hrepr
  unfold signedIndexValue at hrepr
  omega

theorem probabilityMass_coefficientSampler_signedIndex
    (q eta : ℕ) [NeZero q] (hNoWrap : 2 * eta < q)
    (index : Fin (2 * eta + 1)) :
    FormalProof4FHE.WeightedSquare.probabilityMass (coefficientSampler q eta)
        (signedIndexValue index : ZMod q) =
      (Nat.choose (2 * eta) index.val : ℝ) / (2 : ℝ) ^ (2 * eta) := by
  rw [coefficientSampler_eq_map_coefficientIndexSampler]
  unfold FormalProof4FHE.WeightedSquare.probabilityMass
  rw [probOutput_map_injective _ (signedIndexCast_injective q eta hNoWrap)]
  exact probabilityMass_coefficientIndexSampler eta index

open FormalProof4FHE.RLWE.CenteredBinomialHintConcentration

def ternaryLeftMass (eta : ℕ) (index : Fin (2 * eta + 3)) : ℝ :=
  (Nat.choose (2 * eta) index.val : ℝ) / (2 : ℝ) ^ (2 * eta)

def ternaryMiddleMass (eta : ℕ) (index : Fin (2 * eta + 3)) : ℝ :=
  if index.val = 0 then 0 else
    (Nat.choose (2 * eta) (index.val - 1) : ℝ) / (2 : ℝ) ^ (2 * eta)

def ternaryRightMass (eta : ℕ) (index : Fin (2 * eta + 3)) : ℝ :=
  if index.val < 2 then 0 else
    (Nat.choose (2 * eta) (index.val - 2) : ℝ) / (2 : ℝ) ^ (2 * eta)

theorem ternaryLeftMass_nonneg (eta : ℕ) (index : Fin (2 * eta + 3)) :
    0 ≤ ternaryLeftMass eta index := by
  unfold ternaryLeftMass
  positivity

theorem ternaryMiddleMass_nonneg (eta : ℕ) (index : Fin (2 * eta + 3)) :
    0 ≤ ternaryMiddleMass eta index := by
  unfold ternaryMiddleMass
  split <;> positivity

theorem ternaryRightMass_nonneg (eta : ℕ) (index : Fin (2 * eta + 3)) :
    0 ≤ ternaryRightMass eta index := by
  unfold ternaryRightMass
  split <;> positivity

theorem sum_ternaryLeftMass (eta : ℕ) : ∑ index, ternaryLeftMass eta index = 1 := by
  rw [Fin.sum_univ_castSucc]
  have hlast : ternaryLeftMass eta (Fin.last (2 * eta + 2)) = 0 := by
    simp [ternaryLeftMass, Nat.choose_eq_zero_of_lt (by omega : 2 * eta < 2 * eta + 2)]
  rw [hlast, add_zero]
  change ∑ index : Fin (2 * eta + 2), fairBinomialLeftMass eta index = 1
  exact sum_fairBinomialLeftMass eta

theorem sum_ternaryMiddleMass (eta : ℕ) : ∑ index, ternaryMiddleMass eta index = 1 := by
  rw [Fin.sum_univ_castSucc]
  have hlast : ternaryMiddleMass eta (Fin.last (2 * eta + 2)) = 0 := by
    simp [ternaryMiddleMass]
  rw [hlast, add_zero]
  change ∑ index : Fin (2 * eta + 2), fairBinomialRightMass eta index = 1
  exact sum_fairBinomialRightMass eta

theorem sum_ternaryRightMass (eta : ℕ) : ∑ index, ternaryRightMass eta index = 1 := by
  rw [Fin.sum_univ_succ]
  have hzero : ternaryRightMass eta (0 : Fin (2 * eta + 3)) = 0 := by
    simp [ternaryRightMass]
  rw [hzero, zero_add]
  rw [Fin.sum_univ_succ]
  have hone : ternaryRightMass eta ((0 : Fin (2 * eta + 2)).succ) = 0 := by
    simp [ternaryRightMass]
  rw [hone, zero_add]
  change ∑ index : Fin (2 * eta + 1),
    ternaryRightMass eta index.succ.succ = 1
  calc
    _ = ∑ index : Fin (2 * eta + 1),
        (fun j : ℕ => (Nat.choose (2 * eta) j : ℝ) /
          (2 : ℝ) ^ (2 * eta)) index := by
      apply Finset.sum_congr rfl
      intro index _
      unfold ternaryRightMass
      simp only [Fin.val_succ]
      rw [if_neg (by omega : ¬(index.val + 1 + 1 < 2))]
      congr 2
    _ = 1 := by
      rw [Fin.sum_univ_eq_sum_range
        (fun j : ℕ => (Nat.choose (2 * eta) j : ℝ) / (2 : ℝ) ^ (2 * eta))
        (2 * eta + 1), ← Finset.sum_div]
      have hsum : (∑ index ∈ Finset.range (2 * eta + 1),
          (Nat.choose (2 * eta) index : ℝ)) = (2 : ℝ) ^ (2 * eta) := by
        exact_mod_cast Nat.sum_range_choose (2 * eta)
      rw [hsum]
      norm_num

theorem ternary_left_middle_triangular (eta : ℕ) :
    triangularDiscrimination (ternaryLeftMass eta) (ternaryMiddleMass eta) =
      2 / (2 * (eta : ℝ) + 1) := by
  unfold triangularDiscrimination
  rw [Fin.sum_univ_castSucc]
  have hlast :
      (ternaryLeftMass eta (Fin.last (2 * eta + 2)) -
          ternaryMiddleMass eta (Fin.last (2 * eta + 2))) ^ 2 /
        (ternaryLeftMass eta (Fin.last (2 * eta + 2)) +
          ternaryMiddleMass eta (Fin.last (2 * eta + 2))) = 0 := by
    simp [ternaryLeftMass, ternaryMiddleMass,
      Nat.choose_eq_zero_of_lt (by omega : 2 * eta < 2 * eta + 2)]
  rw [hlast, add_zero]
  change triangularDiscrimination
    (fairBinomialLeftMass eta) (fairBinomialRightMass eta) = _
  exact fairBinomial_triangularDiscrimination eta

theorem ternary_middle_right_triangular (eta : ℕ) :
    triangularDiscrimination (ternaryMiddleMass eta) (ternaryRightMass eta) =
      2 / (2 * (eta : ℝ) + 1) := by
  unfold triangularDiscrimination
  rw [Fin.sum_univ_succ]
  have hzero :
      (ternaryMiddleMass eta (0 : Fin (2 * eta + 3)) -
          ternaryRightMass eta (0 : Fin (2 * eta + 3))) ^ 2 /
        (ternaryMiddleMass eta (0 : Fin (2 * eta + 3)) +
          ternaryRightMass eta (0 : Fin (2 * eta + 3))) = 0 := by
    simp [ternaryMiddleMass, ternaryRightMass]
  rw [hzero, zero_add]
  rw [← fairBinomial_triangularDiscrimination eta]
  unfold triangularDiscrimination
  apply Finset.sum_congr rfl
  intro index _
  by_cases hindex : index.val = 0
  · simp [ternaryMiddleMass, ternaryRightMass, fairBinomialLeftMass,
      fairBinomialRightMass, hindex]
  · have hnotSmall : ¬(index.val + 1 < 2) := by omega
    simp [ternaryMiddleMass, ternaryRightMass, fairBinomialLeftMass,
      fairBinomialRightMass, hindex, hnotSmall]

def concreteTernaryAdjacentCBDCertificate (eta : ℕ) :
    TernaryAdjacentCBDCertificate eta (Fin (2 * eta + 3)) where
  left := ternaryLeftMass eta
  middle := ternaryMiddleMass eta
  right := ternaryRightMass eta
  left_nonneg := ternaryLeftMass_nonneg eta
  middle_nonneg := ternaryMiddleMass_nonneg eta
  right_nonneg := ternaryRightMass_nonneg eta
  sum_left := sum_ternaryLeftMass eta
  sum_middle := sum_ternaryMiddleMass eta
  sum_right := sum_ternaryRightMass eta
  left_middle_triangular_eq := ternary_left_middle_triangular eta
  middle_right_triangular_eq := ternary_middle_right_triangular eta

theorem ternaryHintDensityCost_concrete_le (eta : ℕ) :
    ternaryHintDensityCost
        (ternaryLeftMass eta) (ternaryMiddleMass eta) (ternaryRightMass eta) ≤
      1 + 4 / (2 * (eta : ℝ) + 1) :=
  ternaryHintDensityCost_le_of_adjacentCBD
    (concreteTernaryAdjacentCBDCertificate eta)

end
end FormalProof4FHE.RLWE.CenteredBinomialFairBinomialLaw
