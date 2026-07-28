/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.PowerOfTwoCyclotomicChainRing
import FormalProof4FHE.RLWE.RankOneHNFLossinessGaussianCluster
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.Data.Nat.Choose.Lucas
import Mathlib.Data.Nat.Log
import Mathlib.InformationTheory.Hamming

/-!
# Sparse rank and exact exceptional-stratum bounds for rank-one RLWE

This file formalizes the two symbolic refinements used after the Gaussian-cluster screen.
The algebraic part works over the binary repeated-root polynomial ring.  It proves the
Hasse-syndrome characterization of `(X - 1)`-adic depth and the minimum coefficient weight of
each repeated-root code.  It then packages fixed-weight ternary differences and exact
rank-stratified summation bounds.

The analytic one-coordinate Gaussian/theta estimate and the identification of selected source
coordinates with uniform quotient coordinates remain explicit hypotheses.  Everything after
those local estimates--pair aggregation, exceptional-stratum counting, Markov, and union
bounds--is finite algebra proved here.
-/

open BigOperators
open Polynomial

namespace FormalProof4FHE.RLWE.RankOneHNFLossinessSparseRank

noncomputable section

abbrev F2 := ZMod 2

/-! ## Hasse syndromes -/

/-- The `j`th binary Hasse syndrome at the repeated root `1`. -/
def hasseSyndrome (polynomial : F2[X]) (j : ℕ) : F2 :=
  (Polynomial.hasseDeriv j polynomial).eval 1

/-- Vanishing of the first `level` Hasse syndromes is exactly divisibility by
`(X - 1)^level`. -/
theorem X_sub_one_pow_dvd_iff_hasseSyndrome_zero
    (polynomial : F2[X]) (level : ℕ) :
    (X - C (1 : F2)) ^ level ∣ polynomial ↔
      ∀ j < level, hasseSyndrome polynomial j = 0 := by
  rw [Polynomial.X_sub_C_pow_dvd_iff, Polynomial.X_pow_dvd_iff]
  constructor
  · intro hzero j hj
    change (Polynomial.hasseDeriv j polynomial).eval 1 = 0
    rw [← Polynomial.taylor_coeff]
    exact hzero j hj
  · intro hzero j hj
    change (Polynomial.taylor 1 polynomial).coeff j = 0
    rw [Polynomial.taylor_coeff]
    exact hzero j hj

/-- Coefficient form of a Hasse syndrome.  This is the parity-check equation used by the
enumerator: `sum_i choose(i,j) h_i = 0 (mod 2)`. -/
theorem hasseSyndrome_eq_coeff_sum (polynomial : F2[X]) (j : ℕ) :
    hasseSyndrome polynomial j =
      ∑ i ∈ polynomial.support, (i.choose j : F2) * polynomial.coeff i := by
  rw [hasseSyndrome, Polynomial.hasseDeriv_apply, Polynomial.eval_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp [Polynomial.eval_monomial]

/-- All Hasse syndromes below `level` vanish. -/
def syndromesZeroBelow (polynomial : F2[X]) (level : ℕ) : Prop :=
  ∀ j < level, hasseSyndrome polynomial j = 0

/-- Truncated `(X-1)`-adic valuation computed only from the finite Hasse syndrome vector. -/
def hasseValuation (length : ℕ) (polynomial : F2[X]) : ℕ := by
  classical
  exact Nat.findGreatest (syndromesZeroBelow polynomial) length

theorem hasseValuation_le (length : ℕ) (polynomial : F2[X]) :
    hasseValuation length polynomial ≤ length := by
  classical
  exact Nat.findGreatest_le length

theorem syndromesZeroBelow_hasseValuation (length : ℕ) (polynomial : F2[X]) :
    syndromesZeroBelow polynomial (hasseValuation length polynomial) := by
  classical
  apply Nat.findGreatest_spec (m := 0)
  · exact Nat.zero_le length
  · intro j hj
    omega

/-- Below the truncation length, divisibility, syndrome vanishing, and comparison with the
computed valuation are equivalent. -/
theorem le_hasseValuation_iff_syndromesZeroBelow
    (length : ℕ) (polynomial : F2[X]) {level : ℕ} (hlevel : level ≤ length) :
    level ≤ hasseValuation length polynomial ↔ syndromesZeroBelow polynomial level := by
  classical
  constructor
  · intro hle j hj
    exact syndromesZeroBelow_hasseValuation length polynomial j (hj.trans_le hle)
  · intro hzero
    exact Nat.le_findGreatest hlevel hzero

theorem hasseValuation_lt_of_ne_zero
    (length : ℕ) {polynomial : F2[X]} (hne : polynomial ≠ 0)
    (hdegree : polynomial.natDegree < length) :
    hasseValuation length polynomial < length := by
  apply lt_of_le_of_ne (hasseValuation_le length polynomial)
  intro heq
  apply hne
  apply Polynomial.eq_zero_of_hasseDeriv_eq_zero polynomial 1
  intro j
  by_cases hj : j < length
  · exact syndromesZeroBelow_hasseValuation length polynomial j (by simpa [heq])
  · have hdegreeJ : polynomial.natDegree < j :=
      hdegree.trans_le (Nat.le_of_not_gt hj)
    rw [Polynomial.hasseDeriv_eq_zero_of_lt_natDegree polynomial j hdegreeJ]
    simp

theorem hasseSyndrome_hasseValuation_ne_zero
    (length : ℕ) {polynomial : F2[X]} (hne : polynomial ≠ 0)
    (hdegree : polynomial.natDegree < length) :
    hasseSyndrome polynomial (hasseValuation length polynomial) ≠ 0 := by
  classical
  intro hzero
  let valuation := hasseValuation length polynomial
  have hvaluationLt : valuation < length :=
    hasseValuation_lt_of_ne_zero length hne hdegree
  have hnext : syndromesZeroBelow polynomial (valuation + 1) := by
    intro j hj
    by_cases hjv : j < valuation
    · exact syndromesZeroBelow_hasseValuation length polynomial j hjv
    · have : j = valuation := by omega
      simpa [this, valuation] using hzero
  exact (Nat.findGreatest_is_greatest
    (P := syndromesZeroBelow polynomial)
    (show hasseValuation length polynomial < valuation + 1 by simp [valuation])
    (by omega)) hnext

/-- Exact classification of a nonzero polynomial's valuation by one nonzero syndrome following
a zero prefix. -/
theorem hasseValuation_eq_iff
    (length : ℕ) {polynomial : F2[X]} (hne : polynomial ≠ 0)
    (hdegree : polynomial.natDegree < length) {level : ℕ} :
    hasseValuation length polynomial = level ↔
      level < length ∧ syndromesZeroBelow polynomial level ∧
        hasseSyndrome polynomial level ≠ 0 := by
  constructor
  · rintro rfl
    exact ⟨hasseValuation_lt_of_ne_zero length hne hdegree,
      syndromesZeroBelow_hasseValuation length polynomial,
      hasseSyndrome_hasseValuation_ne_zero length hne hdegree⟩
  · rintro ⟨hlevel, hzero, hnonzero⟩
    apply Nat.le_antisymm
    · by_contra hnot
      have hlevelLtValuation : level < hasseValuation length polynomial :=
        Nat.lt_of_not_ge hnot
      exact hnonzero
        (syndromesZeroBelow_hasseValuation length polynomial level hlevelLtValuation)
    · exact (le_hasseValuation_iff_syndromesZeroBelow
        length polynomial hlevel.le).mpr hzero

/-- The valuation is the exact repeated-root divisibility depth. -/
theorem X_sub_one_pow_hasseValuation_dvd
    (length : ℕ) (polynomial : F2[X]) :
    (X - C (1 : F2)) ^ hasseValuation length polynomial ∣ polynomial := by
  rw [X_sub_one_pow_dvd_iff_hasseSyndrome_zero]
  exact syndromesZeroBelow_hasseValuation length polynomial

/-! ## Elementary support lemmas over `F_2` -/

theorem f2_eq_one_of_ne_zero {value : F2} (hvalue : value ≠ 0) : value = 1 := by
  rcases PowerOfTwoQuadraticKDMStatistical.zmodTwo_eq_zero_or_one value with hzero | hone
  · exact (hvalue hzero).elim
  · exact hone

/-- A nonzero binary polynomial vanishing at one has positive even coefficient weight, hence
weight at least two. -/
theorem two_le_card_support_of_eval_one_eq_zero
    {polynomial : F2[X]} (hne : polynomial ≠ 0) (heval : polynomial.eval 1 = 0) :
    2 ≤ polynomial.support.card := by
  have hcast : (polynomial.support.card : F2) = 0 := by
    calc
      (polynomial.support.card : F2) =
          ∑ _i ∈ polynomial.support, (1 : F2) := by simp
      _ = ∑ i ∈ polynomial.support, polynomial.coeff i := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (f2_eq_one_of_ne_zero (Polynomial.mem_support_iff.mp hi)).symm
      _ = polynomial.eval 1 := by
        rw [polynomial.eval_eq_sum]
        apply Finset.sum_congr rfl
        intro i _hi
        simp
      _ = 0 := heval
  have heven : 2 ∣ polynomial.support.card :=
    (CharP.cast_eq_zero_iff F2 2 polynomial.support.card).mp hcast
  have hpos : 0 < polynomial.support.card := by
    simpa [Polynomial.card_support_eq_zero] using hne
  omega

/-- Shifting a polynomial of degree below `cut` by `cut` places gives disjoint coefficient
support. -/
theorem support_add_X_pow_mul_eq_union
    (polynomial : F2[X]) (cut : ℕ) (hdegree : polynomial.natDegree < cut) :
    (polynomial + X ^ cut * polynomial).support =
      polynomial.support ∪ polynomial.support.image (fun i ↦ cut + i) := by
  ext index
  simp only [Polynomial.mem_support_iff, Polynomial.coeff_add,
    Polynomial.coeff_X_pow_mul', Finset.mem_union, Finset.mem_image]
  by_cases hindex : index < cut
  · have hshift : ¬cut ≤ index := Nat.not_le.mpr hindex
    simp only [if_neg hshift, add_zero, ne_eq]
    constructor
    · intro hcoeff
      exact Or.inl hcoeff
    · rintro (hcoeff | ⟨source, hsource, hsourceIndex⟩)
      · exact hcoeff
      · omega
  · have hcut : cut ≤ index := Nat.le_of_not_gt hindex
    have hcoeffHigh : polynomial.coeff index = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      exact hdegree.trans_le hcut
    simp only [if_pos hcut, hcoeffHigh, zero_add, ne_eq, not_true_eq_false,
      false_or]
    constructor
    · intro hcoeff
      refine ⟨index - cut, hcoeff, ?_⟩
      omega
    · rintro ⟨source, hsource, hsourceIndex⟩
      have hsourceEq : source = index - cut := by omega
      simpa [hsourceEq] using hsource

/-- The two disjoint copies in `p + X^cut p` double coefficient weight. -/
theorem card_support_add_X_pow_mul
    (polynomial : F2[X]) (cut : ℕ) (hdegree : polynomial.natDegree < cut) :
    (polynomial + X ^ cut * polynomial).support.card =
      2 * polynomial.support.card := by
  rw [support_add_X_pow_mul_eq_union polynomial cut hdegree,
    Finset.card_union_of_disjoint]
  · have himage :
        (polynomial.support.image (fun i ↦ cut + i)).card =
          polynomial.support.card :=
      Finset.card_image_of_injective _ fun _left _right heq ↦
        Nat.add_left_cancel heq
    rw [himage]
    omega
  · rw [Finset.disjoint_left]
    intro index hlow hhigh
    obtain ⟨source, hsource, hsourceIndex⟩ := Finset.mem_image.mp hhigh
    have hindexDegree : index ≤ polynomial.natDegree :=
      Polynomial.le_natDegree_of_mem_supp index hlow
    omega

/-! ## Repeated-root minimum distance -/

/-- Recursive form of the exact minimum distance of the length-`2^d`, dimension-`rank`
binary repeated-root code generated by `(X - 1)^(2^d-rank)`. -/
def repeatedRootDistance : ℕ → ℕ → ℕ
  | 0, rank => if rank = 0 then 0 else 1
  | d + 1, rank =>
      let half := 2 ^ d
      if rank = 0 then 0
      else if rank ≤ half then 2 * repeatedRootDistance d rank
      else if rank < 2 * half then 2
      else 1

@[simp]
theorem repeatedRootDistance_zero : repeatedRootDistance 0 0 = 0 := by
  simp [repeatedRootDistance]

@[simp]
theorem repeatedRootDistance_zero_rank (d : ℕ) : repeatedRootDistance d 0 = 0 := by
  cases d <;> simp [repeatedRootDistance]

/-- The native repeated-root distance theorem. -/
theorem repeatedRootDistance_le_card_support
    (d rank : ℕ) (polynomial : F2[X])
    (hrankPos : 0 < rank) (hrank : rank ≤ 2 ^ d)
    (hne : polynomial ≠ 0) (hdegree : polynomial.natDegree < 2 ^ d)
    (hdivides : (X - C (1 : F2)) ^ (2 ^ d - rank) ∣ polynomial) :
    repeatedRootDistance d rank ≤ polynomial.support.card := by
  induction d generalizing rank polynomial with
  | zero =>
      have hrankOne : rank = 1 := by omega
      subst rank
      simpa [repeatedRootDistance] using
        (show 0 < polynomial.support.card by
          simpa [Polynomial.card_support_eq_zero] using hne)
  | succ d ih =>
      let half := 2 ^ d
      have hlength : 2 ^ (d + 1) = 2 * half := by
        simp [half, pow_succ, Nat.mul_comm]
      rw [hlength] at hrank hdegree hdivides
      by_cases hrankHalf : rank ≤ half
      · obtain ⟨factor, hfactor⟩ := hdivides
        let reduced : F2[X] := (X - C (1 : F2)) ^ (half - rank) * factor
        have hpowSplit :
            (X - C (1 : F2)) ^ (2 * half - rank) =
              (X - C (1 : F2)) ^ half *
                (X - C (1 : F2)) ^ (half - rank) := by
          rw [← pow_add]
          congr 1
          omega
        have hfrob : (X - C (1 : F2)) ^ half = X ^ half + 1 := by
          dsimp only [half]
          simpa [LatticeCrypto.negacyclicModulus] using
            (FormalProof4FHE.TFHE.Native.PowerOfTwoLocalRing.binary_negacyclicModulus_eq_X_sub_one_pow
              d).symm
        have hfactorForm : polynomial = (X ^ half + 1) * reduced := by
          calc
            polynomial = (X - C (1 : F2)) ^ (2 * half - rank) * factor := hfactor
            _ = ((X - C (1 : F2)) ^ half *
                (X - C (1 : F2)) ^ (half - rank)) * factor := by
              rw [hpowSplit]
            _ = (X ^ half + 1) * reduced := by
              rw [hfrob]
              simp only [reduced]
              ring
        have hpoly : polynomial = reduced + X ^ half * reduced := by
          calc
            polynomial = (X ^ half + 1) * reduced := hfactorForm
            _ = reduced + X ^ half * reduced := by ring
        have hreducedNe : reduced ≠ 0 := by
          intro hzero
          apply hne
          calc
            polynomial = reduced + X ^ half * reduced := hpoly
            _ = 0 := by simp [hzero]
        have hreducedDegree : reduced.natDegree < half := by
          have hfactorDegree :
              polynomial.natDegree = half + reduced.natDegree := by
            have hbinomialNe : (1 + X ^ half : F2[X]) ≠ 0 := by
              rw [add_comm]
              simpa only [Polynomial.C_1] using
                (Polynomial.X_pow_add_C_ne_zero
                  (pow_pos (by omega : 0 < 2) d) (1 : F2))
            calc
              polynomial.natDegree = ((X ^ half + 1) * reduced).natDegree := by
                rw [hfactorForm]
              _ = (X ^ half + 1).natDegree + reduced.natDegree := by
                rw [Polynomial.natDegree_mul
                  (by simpa [add_comm] using hbinomialNe) hreducedNe]
              _ = half + reduced.natDegree := by
                rw [show (1 : F2[X]) = C 1 by simp,
                  Polynomial.natDegree_X_pow_add_C]
          omega
        have hreducedDivides :
            (X - C (1 : F2)) ^ (half - rank) ∣ reduced := by
          exact ⟨factor, rfl⟩
        rw [repeatedRootDistance, if_neg (Nat.ne_of_gt hrankPos),
          if_pos hrankHalf, hpoly,
          card_support_add_X_pow_mul reduced half hreducedDegree]
        exact Nat.mul_le_mul_left 2
          (ih rank reduced hrankPos hrankHalf hreducedNe hreducedDegree hreducedDivides)
      · have hrankGt : half < rank := Nat.lt_of_not_ge hrankHalf
        by_cases hrankFull : rank = 2 * half
        · subst rank
          have hpositive : 0 < polynomial.support.card := by
            simpa [Polynomial.card_support_eq_zero] using hne
          simpa [repeatedRootDistance, hrankHalf, half] using hpositive
        · have hrankLt : rank < 2 * half := lt_of_le_of_ne hrank hrankFull
          have hrootDivides : X - C (1 : F2) ∣ polynomial := by
            apply dvd_trans (show X - C (1 : F2) ∣
                (X - C (1 : F2)) ^ (2 * half - rank) by
              exact dvd_pow_self (X - C (1 : F2)) (by omega))
            exact hdivides
          have heval : polynomial.eval 1 = 0 := by
            exact (Polynomial.dvd_iff_isRoot.mp hrootDivides)
          have htwo := two_le_card_support_of_eval_one_eq_zero hne heval
          simpa [repeatedRootDistance, Nat.ne_of_gt hrankPos, hrankHalf,
            hrankLt, half] using htwo

/-- Every admissible rank has a codeword attaining the lower bound, so
`repeatedRootDistance` is the exact minimum rather than only a lower estimate. -/
theorem exists_repeatedRootCodeword_minimumWeight
    (d rank : ℕ) (hrankPos : 0 < rank) (hrank : rank ≤ 2 ^ d) :
    ∃ polynomial : F2[X],
      polynomial ≠ 0 ∧ polynomial.natDegree < 2 ^ d ∧
      (X - C (1 : F2)) ^ (2 ^ d - rank) ∣ polynomial ∧
      polynomial.support.card = repeatedRootDistance d rank := by
  induction d generalizing rank with
  | zero =>
      have hrankOne : rank = 1 := by omega
      subst rank
      refine ⟨1, one_ne_zero, by simp, by simp, ?_⟩
      rw [← Polynomial.C_1, Polynomial.support_C one_ne_zero]
      simp [repeatedRootDistance]
  | succ d ih =>
      let half := 2 ^ d
      have hlength : 2 ^ (d + 1) = 2 * half := by
        simp [half, pow_succ, Nat.mul_comm]
      rw [hlength] at hrank ⊢
      by_cases hrankHalf : rank ≤ half
      · obtain ⟨reduced, hreducedNe, hreducedDegree, hreducedDivides,
          hreducedWeight⟩ := ih rank hrankPos hrankHalf
        let polynomial := reduced + X ^ half * reduced
        have hbinomialNe : (X ^ half + 1 : F2[X]) ≠ 0 := by
          simpa only [Polynomial.C_1] using
            (Polynomial.X_pow_add_C_ne_zero
              (pow_pos (by omega : 0 < 2) d) (1 : F2))
        have hpolynomialForm : polynomial = (X ^ half + 1) * reduced := by
          dsimp only [polynomial]
          ring
        have hpolynomialNe : polynomial ≠ 0 := by
          rw [hpolynomialForm]
          exact mul_ne_zero hbinomialNe hreducedNe
        have hpolynomialDegree : polynomial.natDegree < 2 * half := by
          rw [hpolynomialForm,
            Polynomial.natDegree_mul hbinomialNe hreducedNe]
          rw [show (1 : F2[X]) = C 1 by simp,
            Polynomial.natDegree_X_pow_add_C]
          omega
        have hfrob : (X - C (1 : F2)) ^ half = X ^ half + 1 := by
          dsimp only [half]
          simpa [LatticeCrypto.negacyclicModulus] using
            (FormalProof4FHE.TFHE.Native.PowerOfTwoLocalRing.binary_negacyclicModulus_eq_X_sub_one_pow
              d).symm
        have hpowSplit :
            (X - C (1 : F2)) ^ (2 * half - rank) =
              (X - C (1 : F2)) ^ half *
                (X - C (1 : F2)) ^ (half - rank) := by
          rw [← pow_add]
          congr 1
          omega
        have hpolynomialDivides :
            (X - C (1 : F2)) ^ (2 * half - rank) ∣ polynomial := by
          obtain ⟨factor, hfactor⟩ := hreducedDivides
          refine ⟨factor, ?_⟩
          rw [hpowSplit, hfrob]
          rw [hpolynomialForm, hfactor]
          ring
        refine ⟨polynomial, hpolynomialNe, hpolynomialDegree,
          hpolynomialDivides, ?_⟩
        rw [card_support_add_X_pow_mul reduced half hreducedDegree,
          repeatedRootDistance, if_neg (Nat.ne_of_gt hrankPos),
          if_pos hrankHalf, hreducedWeight]
      · have hrankGt : half < rank := Nat.lt_of_not_ge hrankHalf
        by_cases hrankFull : rank = 2 * half
        · subst rank
          refine ⟨1, one_ne_zero, by simp [half], by simp, ?_⟩
          rw [← Polynomial.C_1, Polynomial.support_C one_ne_zero]
          simp [repeatedRootDistance, hrankHalf, half]
        · have hrankLt : rank < 2 * half := lt_of_le_of_ne hrank hrankFull
          let polynomial : F2[X] := X ^ half + 1
          have hhalfPos : 0 < half := by simp [half]
          have hpolynomialNe : polynomial ≠ 0 := by
            dsimp only [polynomial]
            simpa only [Polynomial.C_1] using
              (Polynomial.X_pow_add_C_ne_zero hhalfPos (1 : F2))
          have hfrob : (X - C (1 : F2)) ^ half = polynomial := by
            dsimp only [half, polynomial]
            simpa [LatticeCrypto.negacyclicModulus] using
              (FormalProof4FHE.TFHE.Native.PowerOfTwoLocalRing.binary_negacyclicModulus_eq_X_sub_one_pow
                d).symm
          have hpolynomialDivides :
              (X - C (1 : F2)) ^ (2 * half - rank) ∣ polynomial := by
            rw [← hfrob]
            exact pow_dvd_pow _ (by omega)
          have hpolynomialWeight : polynomial.support.card = 2 := by
            dsimp only [polynomial]
            simpa [add_comm] using
              (Polynomial.card_support_binomial (R := F2)
                (k := 0) (m := half) hhalfPos.ne
                (x := 1) (y := 1) one_ne_zero one_ne_zero)
          refine ⟨polynomial, hpolynomialNe, ?_, hpolynomialDivides, ?_⟩
          · dsimp only [polynomial]
            rw [show (1 : F2[X]) = C 1 by simp,
              Polynomial.natDegree_X_pow_add_C]
            omega
          · rw [hpolynomialWeight]
            simp [repeatedRootDistance, Nat.ne_of_gt hrankPos, hrankHalf,
              hrankLt, half]

/-- Closed form of the recursive distance: if `1 ≤ rank ≤ 2^d`, then the minimum
coefficient weight is `2^(d - floor(log_2 rank))`. -/
theorem repeatedRootDistance_eq_two_pow_sub_log2
    (d rank : ℕ) (hrankPos : 0 < rank) (hrank : rank ≤ 2 ^ d) :
    repeatedRootDistance d rank = 2 ^ (d - Nat.log2 rank) := by
  induction d generalizing rank with
  | zero =>
      have hrankOne : rank = 1 := by omega
      subst rank
      simp [repeatedRootDistance]
  | succ d ih =>
      let half := 2 ^ d
      have hlength : 2 ^ (d + 1) = 2 * half := by
        simp [half, pow_succ, Nat.mul_comm]
      rw [hlength] at hrank
      by_cases hrankHalf : rank ≤ half
      · have hlogLe : Nat.log2 rank ≤ d := by
          rw [Nat.log2_eq_log_two]
          calc
            Nat.log 2 rank ≤ Nat.log 2 (2 ^ d) := Nat.log_mono_right hrankHalf
            _ = d := Nat.log_pow Nat.one_lt_two d
        rw [repeatedRootDistance, if_neg (Nat.ne_of_gt hrankPos), if_pos hrankHalf,
          ih rank hrankPos hrankHalf]
        rw [show d + 1 - Nat.log2 rank = (d - Nat.log2 rank) + 1 by omega,
          pow_succ]
        omega
      · have hrankGt : half < rank := Nat.lt_of_not_ge hrankHalf
        by_cases hrankFull : rank = 2 * half
        · subst rank
          have hlog : Nat.log2 (2 * half) = d + 1 := by
            rw [show 2 * half = 2 ^ (d + 1) by
              simp [half, pow_succ, Nat.mul_comm], Nat.log2_eq_log_two,
              Nat.log_pow Nat.one_lt_two]
          simp [repeatedRootDistance, hrankHalf, hlog, half]
        · have hrankLt : rank < 2 * half := lt_of_le_of_ne hrank hrankFull
          have hlog : Nat.log2 rank = d := by
            rw [Nat.log2_eq_log_two]
            apply Nat.log_eq_of_pow_le_of_lt_pow
            · exact hrankGt.le
            · simpa [half, pow_succ, Nat.mul_comm] using hrankLt
          simp [repeatedRootDistance, Nat.ne_of_gt hrankPos, hrankHalf,
            hrankLt, hlog, half]

/-- Inverse minimum-distance bound.  A nonzero codeword of coefficient weight at most `bound`
cannot generate fewer than `2^(d-floor(log_2 bound))` binary output coordinates. -/
theorem dyadic_rank_lower_bound_of_distance
    (d rank weight bound : ℕ)
    (hrankPos : 0 < rank) (hrank : rank ≤ 2 ^ d)
    (hweightPos : 0 < weight) (hweight : weight ≤ bound)
    (hbound : bound ≤ 2 ^ d)
    (hminimum : repeatedRootDistance d rank ≤ weight) :
    2 ^ (d - Nat.log2 bound) ≤ rank := by
  have hboundPos : 0 < bound := lt_of_lt_of_le hweightPos hweight
  have hlogBoundLe : Nat.log2 bound ≤ d := by
    rw [Nat.log2_eq_log_two]
    calc
      Nat.log 2 bound ≤ Nat.log 2 (2 ^ d) := Nat.log_mono_right hbound
      _ = d := Nat.log_pow Nat.one_lt_two d
  by_contra hcontra
  have hrankLt : rank < 2 ^ (d - Nat.log2 bound) := Nat.lt_of_not_ge hcontra
  have hpowLogRank : 2 ^ Nat.log2 rank ≤ rank := by
    rw [Nat.log2_eq_log_two]
    exact Nat.pow_log_le_self 2 (Nat.ne_of_gt hrankPos)
  have hlogRankLt : Nat.log2 rank < d - Nat.log2 bound := by
    rw [← Nat.pow_lt_pow_iff_right Nat.one_lt_two]
    exact hpowLogRank.trans_lt hrankLt
  have hlogSuccLe : Nat.log2 bound + 1 ≤ d - Nat.log2 rank := by omega
  have hboundLt : bound < 2 ^ (Nat.log2 bound + 1) := by
    rw [Nat.log2_eq_log_two]
    exact Nat.lt_pow_succ_log_self Nat.one_lt_two bound
  have hpowLe : 2 ^ (Nat.log2 bound + 1) ≤
      2 ^ (d - Nat.log2 rank) := by
    exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).mpr hlogSuccLe
  have : weight < repeatedRootDistance d rank := by
    rw [repeatedRootDistance_eq_two_pow_sub_log2 d rank hrankPos hrank]
    exact hweight.trans_lt (hboundLt.trans_le hpowLe)
  omega

/-! ## Coefficient words and fixed-weight ternary differences -/

/-- Finite support of a coefficient word. -/
def wordSupport {Index Alphabet : Type} [Fintype Index] [DecidableEq Index]
    [Zero Alphabet] [DecidableEq Alphabet] (word : Index → Alphabet) : Finset Index :=
  Finset.univ.filter fun index ↦ word index ≠ 0

@[simp]
theorem mem_wordSupport_iff
    {Index Alphabet : Type} [Fintype Index] [DecidableEq Index]
    [Zero Alphabet] [DecidableEq Alphabet] (word : Index → Alphabet) (index : Index) :
    index ∈ wordSupport word ↔ word index ≠ 0 := by
  simp [wordSupport]

/-- The ordinary polynomial with the given binary coefficient word. -/
def binaryWordPolynomial {length : ℕ} (word : Fin length → F2) : F2[X] :=
  ∑ index, Polynomial.monomial index.val (word index)

@[simp]
theorem binaryWordPolynomial_coeff
    {length : ℕ} (word : Fin length → F2) (index : Fin length) :
    (binaryWordPolynomial word).coeff index.val = word index := by
  rw [binaryWordPolynomial, Polynomial.finsetSum_coeff,
    Finset.sum_eq_single index]
  · simp
  · intro other _ hother
    rw [Polynomial.coeff_monomial, if_neg]
    intro heq
    exact hother (Fin.ext heq)
  · simp

theorem binaryWordPolynomial_coeff_eq_zero_of_length_le
    {length : ℕ} (word : Fin length → F2) (coefficient : ℕ)
    (hcoefficient : length ≤ coefficient) :
    (binaryWordPolynomial word).coeff coefficient = 0 := by
  rw [binaryWordPolynomial, Polynomial.finsetSum_coeff]
  apply Finset.sum_eq_zero
  intro index _
  simp [Polynomial.coeff_monomial,
    ne_of_lt (index.isLt.trans_le hcoefficient)]

theorem binaryWordPolynomial_eq_zero_iff
    {length : ℕ} (word : Fin length → F2) :
    binaryWordPolynomial word = 0 ↔ word = 0 := by
  constructor
  · intro hzero
    funext index
    have := congrArg (fun polynomial : F2[X] ↦ polynomial.coeff index.val) hzero
    simpa using this
  · rintro rfl
    simp [binaryWordPolynomial]

theorem binaryWordPolynomial_natDegree_lt
    {length : ℕ} (hlength : 0 < length) (word : Fin length → F2) :
    (binaryWordPolynomial word).natDegree < length := by
  by_cases hzero : binaryWordPolynomial word = 0
  · simp [hzero, hlength]
  · rw [Polynomial.natDegree_lt_iff_degree_lt hzero,
      Polynomial.degree_lt_iff_coeff_zero]
    intro coefficient hcoefficient
    exact binaryWordPolynomial_coeff_eq_zero_of_length_le word coefficient hcoefficient

/-- Polynomial coefficient weight equals word Hamming weight. -/
theorem card_support_binaryWordPolynomial
    {length : ℕ} (word : Fin length → F2) :
    (binaryWordPolynomial word).support.card = (wordSupport word).card := by
  classical
  apply Finset.card_bij
      (fun coefficient _ ↦
        ⟨coefficient, by
          by_contra hcoefficient
          have hzero := binaryWordPolynomial_coeff_eq_zero_of_length_le
            word coefficient (Nat.le_of_not_gt hcoefficient)
          exact (Polynomial.mem_support_iff.mp ‹coefficient ∈
            (binaryWordPolynomial word).support›) hzero⟩)
  · intro coefficient hcoefficient
    rw [mem_wordSupport_iff]
    rw [← binaryWordPolynomial_coeff word ⟨coefficient, _⟩]
    exact Polynomial.mem_support_iff.mp hcoefficient
  · intro left _ right _ heq
    exact congrArg Fin.val heq
  · intro index hindex
    refine ⟨index.val, ?_, ?_⟩
    · rw [Polynomial.mem_support_iff, binaryWordPolynomial_coeff]
      exact (mem_wordSupport_iff word index).mp hindex
    · rfl

/-- A concrete coefficient alphabet for `{-1,0,1}`. -/
inductive TernaryDigit where
  | neg
  | zero
  | pos
  deriving DecidableEq, Fintype

namespace TernaryDigit

def toInt : TernaryDigit → ℤ
  | neg => -1
  | zero => 0
  | pos => 1

def toF2 : TernaryDigit → F2
  | neg => 1
  | zero => 0
  | pos => 1

instance : Zero TernaryDigit := ⟨zero⟩

@[simp] theorem zero_is_zero : TernaryDigit.zero = (0 : TernaryDigit) := rfl

@[simp] theorem toF2_zero : toF2 0 = 0 := rfl

@[simp] theorem toF2_ne_zero_iff (digit : TernaryDigit) :
    toF2 digit ≠ 0 ↔ digit ≠ 0 := by
  cases digit <;> decide

end TernaryDigit

abbrev TernaryWord (length : ℕ) := Fin length → TernaryDigit

/-- A ternary word has exact Hamming weight `weight`. -/
def IsFixedWeight {length : ℕ} (weight : ℕ) (word : TernaryWord length) : Prop :=
  (wordSupport word).card = weight

/-- Reduction modulo two of an ordinary ternary difference.  Signs disappear, so it detects
exactly a support change. -/
def parityDifference {length : ℕ}
    (left right : TernaryWord length) : Fin length → F2 :=
  fun index ↦ TernaryDigit.toF2 (right index) - TernaryDigit.toF2 (left index)

/-- After dividing an even same-support difference by two, reduction modulo two detects exactly
the coefficients whose signs changed. -/
def halvedSignDifference {length : ℕ}
    (left right : TernaryWord length) : Fin length → F2 :=
  fun index ↦
    if left index ≠ 0 ∧ right index ≠ 0 ∧ left index ≠ right index then 1 else 0

theorem mem_wordSupport_parityDifference_iff
    {length : ℕ} (left right : TernaryWord length) (index : Fin length) :
    index ∈ wordSupport (parityDifference left right) ↔
      (index ∈ wordSupport left ∧ index ∉ wordSupport right) ∨
      (index ∈ wordSupport right ∧ index ∉ wordSupport left) := by
  simp only [mem_wordSupport_iff, parityDifference]
  cases left index <;> cases right index <;>
    simp [TernaryDigit.toF2]

theorem wordSupport_parityDifference_subset
    {length : ℕ} (left right : TernaryWord length) :
    wordSupport (parityDifference left right) ⊆
      wordSupport left ∪ wordSupport right := by
  intro index hindex
  rw [mem_wordSupport_parityDifference_iff] at hindex
  simp only [Finset.mem_union]
  tauto

theorem wordSupport_halvedSignDifference_subset_left
    {length : ℕ} (left right : TernaryWord length) :
    wordSupport (halvedSignDifference left right) ⊆ wordSupport left := by
  intro index hindex
  rw [mem_wordSupport_iff] at hindex ⊢
  simp only [halvedSignDifference] at hindex
  split at hindex
  · exact ‹left index ≠ 0 ∧ right index ≠ 0 ∧ left index ≠ right index›.1
  · simp at hindex

/-- If supports differ, the parity difference is nonzero. -/
theorem parityDifference_ne_zero_of_support_ne
    {length : ℕ} {left right : TernaryWord length}
    (hsupport : wordSupport left ≠ wordSupport right) :
    parityDifference left right ≠ 0 := by
  intro hzero
  apply hsupport
  ext index
  by_contra hiff
  have hxor :
      (index ∈ wordSupport left ∧ index ∉ wordSupport right) ∨
      (index ∈ wordSupport right ∧ index ∉ wordSupport left) := by
    tauto
  have hmem := (mem_wordSupport_parityDifference_iff left right index).mpr hxor
  rw [hzero, mem_wordSupport_iff] at hmem
  exact hmem rfl

/-- On equal support, distinct ternary words have a nonzero halved sign difference. -/
theorem halvedSignDifference_ne_zero_of_support_eq
    {length : ℕ} {left right : TernaryWord length}
    (hsupport : wordSupport left = wordSupport right) (hne : left ≠ right) :
    halvedSignDifference left right ≠ 0 := by
  intro hzero
  apply hne
  funext index
  by_contra hindex
  have hleftIffRight : left index ≠ 0 ↔ right index ≠ 0 := by
    simpa only [mem_wordSupport_iff] using
      Finset.ext_iff.mp hsupport index
  have hleft : left index ≠ 0 := by
    intro hleftZero
    have hrightZero : right index = 0 := not_ne_iff.mp
      (mt hleftIffRight.mpr (not_ne_iff.mpr hleftZero))
    exact hindex (hleftZero.trans hrightZero.symm)
  have hright : right index ≠ 0 := hleftIffRight.mp hleft
  have hone : halvedSignDifference left right index = 1 := by
    simp [halvedSignDifference, hleft, hright, hindex]
  have hcoefficient := congrFun hzero index
  rw [hone] at hcoefficient
  exact one_ne_zero hcoefficient

/-- The primitive binary difference: divide by two precisely in the same-support case. -/
def primitiveDifference {length : ℕ}
    (left right : TernaryWord length) : Fin length → F2 :=
  if wordSupport left = wordSupport right then
    halvedSignDifference left right
  else parityDifference left right

/-- The extracted power of two is one in the same-support case and zero otherwise. -/
def primitiveDifferenceExponent {length : ℕ}
    (left right : TernaryWord length) : ℕ :=
  if wordSupport left = wordSupport right then 1 else 0

theorem primitiveDifference_ne_zero
    {length : ℕ} {left right : TernaryWord length} (hne : left ≠ right) :
    primitiveDifference left right ≠ 0 := by
  by_cases hsupport : wordSupport left = wordSupport right
  · simp only [primitiveDifference, if_pos hsupport]
    exact halvedSignDifference_ne_zero_of_support_eq hsupport hne
  · simp only [primitiveDifference, if_neg hsupport]
    exact parityDifference_ne_zero_of_support_ne hsupport

/-- Different supports give primitive weight at most `2w`; equal supports give the sharper `w`.
This is the binary/ternary sparse-difference lemma used by the rank theorem. -/
theorem primitiveDifference_weight_bound
    {length weight : ℕ} {left right : TernaryWord length}
    (hleft : IsFixedWeight weight left) (hright : IsFixedWeight weight right) :
    (wordSupport (primitiveDifference left right)).card ≤
      if wordSupport left = wordSupport right then weight else 2 * weight := by
  by_cases hsupport : wordSupport left = wordSupport right
  · simp only [primitiveDifference, if_pos hsupport]
    calc
      (wordSupport (halvedSignDifference left right)).card ≤
          (wordSupport left).card :=
        Finset.card_le_card (wordSupport_halvedSignDifference_subset_left left right)
      _ = weight := hleft
  · simp only [primitiveDifference, if_neg hsupport]
    calc
      (wordSupport (parityDifference left right)).card ≤
          (wordSupport left ∪ wordSupport right).card :=
        Finset.card_le_card (wordSupport_parityDifference_subset left right)
      _ ≤ (wordSupport left).card + (wordSupport right).card :=
        Finset.card_union_le _ _
      _ = 2 * weight := by rw [hleft, hright]; omega

theorem primitiveDifference_weight_le_two_mul
    {length weight : ℕ} {left right : TernaryWord length}
    (hleft : IsFixedWeight weight left) (hright : IsFixedWeight weight right) :
    (wordSupport (primitiveDifference left right)).card ≤ 2 * weight := by
  have hbound := primitiveDifference_weight_bound hleft hright
  split at hbound <;> omega

/-- In the support-changing case the primitive word is literally `(right-left) mod 2`. -/
theorem parityDifference_eq_intDifference_mod_two
    {length : ℕ} (left right : TernaryWord length) (index : Fin length) :
    parityDifference left right index =
      ((TernaryDigit.toInt (right index) - TernaryDigit.toInt (left index) : ℤ) : F2) := by
  simp only [parityDifference]
  generalize hleft : left index = leftDigit
  generalize hright : right index = rightDigit
  cases leftDigit <;> cases rightDigit <;>
    decide

/-- In the equal-support case the primitive word is literally `((right-left)/2) mod 2`. -/
theorem halvedSignDifference_eq_intHalfDifference_mod_two
    {length : ℕ} {left right : TernaryWord length}
    (hsupport : wordSupport left = wordSupport right) (index : Fin length) :
    halvedSignDifference left right index =
      (((TernaryDigit.toInt (right index) - TernaryDigit.toInt (left index)) / 2 : ℤ) : F2) := by
  have hleftIffRight : left index ≠ 0 ↔ right index ≠ 0 := by
    simpa only [mem_wordSupport_iff] using Finset.ext_iff.mp hsupport index
  cases hleft : left index <;> cases hright : right index <;>
    simp_all [halvedSignDifference, TernaryDigit.toInt]

/-- Direct sparse-rank corollary for a primitive fixed-weight ternary difference.  The `rank`
hypothesis is exactly membership in its binary repeated-root multiplication ideal. -/
theorem primitiveDifference_dyadic_rank_lower_bound
    (d weight rank : ℕ) {left right : TernaryWord (2 ^ d)}
    (hne : left ≠ right)
    (hleft : IsFixedWeight weight left) (hright : IsFixedWeight weight right)
    (hrankPos : 0 < rank) (hrank : rank ≤ 2 ^ d)
    (hweightRange : 2 * weight ≤ 2 ^ d)
    (hdivides :
      (X - C (1 : F2)) ^ (2 ^ d - rank) ∣
        binaryWordPolynomial (primitiveDifference left right)) :
    2 ^ (d - Nat.log2 (2 * weight)) ≤ rank := by
  let primitive := primitiveDifference left right
  have hprimitiveNe : primitive ≠ 0 := primitiveDifference_ne_zero hne
  have hpolynomialNe : binaryWordPolynomial primitive ≠ 0 :=
    (binaryWordPolynomial_eq_zero_iff primitive).not.mpr hprimitiveNe
  have hdegree : (binaryWordPolynomial primitive).natDegree < 2 ^ d :=
    binaryWordPolynomial_natDegree_lt (pow_pos (by omega : 0 < 2) d) primitive
  have hminimum : repeatedRootDistance d rank ≤ (wordSupport primitive).card := by
    rw [← card_support_binaryWordPolynomial]
    exact repeatedRootDistance_le_card_support d rank _ hrankPos hrank
      hpolynomialNe hdegree hdivides
  have hprimitiveWeightPos : 0 < (wordSupport primitive).card := by
    rw [Finset.card_pos]
    by_contra hempty
    apply hprimitiveNe
    funext index
    by_contra hcoefficient
    have : index ∈ wordSupport primitive :=
      (mem_wordSupport_iff primitive index).mpr hcoefficient
    exact hempty ⟨index, this⟩
  exact dyadic_rank_lower_bound_of_distance d rank
    (wordSupport primitive).card (2 * weight) hrankPos hrank
    hprimitiveWeightPos (primitiveDifference_weight_le_two_mul hleft hright)
    hweightRange hminimum

/-- Exact binary repeated-root valuation of a primitive ternary difference. -/
def primitiveDifferenceValuation (d : ℕ)
    (left right : TernaryWord (2 ^ d)) : ℕ :=
  hasseValuation (2 ^ d)
    (binaryWordPolynomial (primitiveDifference left right))

/-- Rank of multiplication by the primitive difference in the binary length-`2^d` local ring.
The chain-ring image has `2^rank` elements. -/
def primitiveDifferenceRank (d : ℕ)
    (left right : TernaryWord (2 ^ d)) : ℕ :=
  2 ^ d - primitiveDifferenceValuation d left right

theorem primitiveDifferenceValuation_lt
    (d : ℕ) {left right : TernaryWord (2 ^ d)} (hne : left ≠ right) :
    primitiveDifferenceValuation d left right < 2 ^ d := by
  apply hasseValuation_lt_of_ne_zero
  · exact (binaryWordPolynomial_eq_zero_iff _).not.mpr
      (primitiveDifference_ne_zero hne)
  · exact binaryWordPolynomial_natDegree_lt
      (pow_pos (by omega : 0 < 2) d) _

theorem primitiveDifferenceRank_pos
    (d : ℕ) {left right : TernaryWord (2 ^ d)} (hne : left ≠ right) :
    0 < primitiveDifferenceRank d left right := by
  unfold primitiveDifferenceRank
  exact Nat.sub_pos_of_lt (primitiveDifferenceValuation_lt d hne)

theorem primitiveDifferenceRank_le_length
    (d : ℕ) (left right : TernaryWord (2 ^ d)) :
    primitiveDifferenceRank d left right ≤ 2 ^ d := by
  exact Nat.sub_le _ _

theorem primitiveDifference_rank_divisibility
    (d : ℕ) (left right : TernaryWord (2 ^ d)) :
    (X - C (1 : F2)) ^ (2 ^ d - primitiveDifferenceRank d left right) ∣
      binaryWordPolynomial (primitiveDifference left right) := by
  have hvaluationLe : primitiveDifferenceValuation d left right ≤ 2 ^ d :=
    hasseValuation_le _ _
  rw [primitiveDifferenceRank, Nat.sub_sub_self hvaluationLe]
  exact X_sub_one_pow_hasseValuation_dvd _ _

/-- Fully instantiated sparse-rank theorem for distinct exact-weight ternary secrets. -/
theorem primitiveDifferenceRank_dyadic_lower_bound
    (d weight : ℕ) {left right : TernaryWord (2 ^ d)}
    (hne : left ≠ right)
    (hleft : IsFixedWeight weight left) (hright : IsFixedWeight weight right)
    (hweightRange : 2 * weight ≤ 2 ^ d) :
    2 ^ (d - Nat.log2 (2 * weight)) ≤
      primitiveDifferenceRank d left right := by
  exact primitiveDifference_dyadic_rank_lower_bound d weight
    (primitiveDifferenceRank d left right) hne hleft hright
    (primitiveDifferenceRank_pos d hne)
    (primitiveDifferenceRank_le_length d left right)
    hweightRange (primitiveDifference_rank_divisibility d left right)

/-! ### Connection to the support-aware fixed-weight secret type -/

abbrev EncodedFixedWeightTernarySecret (length weight : ℕ) :=
  RankOneHNFLossinessSupportAware.FixedWeightTernarySecret length weight

def signedDigit (sign : Fin 2) : TernaryDigit :=
  if sign = 0 then TernaryDigit.neg else TernaryDigit.pos

theorem signedDigit_ne_zero (sign : Fin 2) : signedDigit sign ≠ 0 := by
  fin_cases sign <;> decide

theorem signedDigit_injective : Function.Injective signedDigit := by
  intro left right heq
  fin_cases left <;> fin_cases right <;> simp_all [signedDigit]

/-- Decode the existing support-plus-sign representation into literal ternary coefficients. -/
def decodeFixedWeightTernary
    {length weight : ℕ} (secret : EncodedFixedWeightTernarySecret length weight) :
    TernaryWord length :=
  fun index ↦
    if hindex : index ∈ secret.1.1 then signedDigit (secret.2 ⟨index, hindex⟩)
    else 0

@[simp]
theorem wordSupport_decodeFixedWeightTernary
    {length weight : ℕ} (secret : EncodedFixedWeightTernarySecret length weight) :
    wordSupport (decodeFixedWeightTernary secret) = secret.1.1 := by
  ext index
  by_cases hindex : index ∈ secret.1.1
  · simp [mem_wordSupport_iff, decodeFixedWeightTernary, hindex,
      signedDigit_ne_zero]
  · simp [mem_wordSupport_iff, decodeFixedWeightTernary, hindex]

theorem decodeFixedWeightTernary_isFixedWeight
    {length weight : ℕ} (secret : EncodedFixedWeightTernarySecret length weight) :
    IsFixedWeight weight (decodeFixedWeightTernary secret) := by
  rw [IsFixedWeight, wordSupport_decodeFixedWeightTernary]
  exact (Finset.mem_powersetCard.mp secret.1.property).2

theorem decodeFixedWeightTernary_injective
    {length weight : ℕ} :
    Function.Injective
      (decodeFixedWeightTernary : EncodedFixedWeightTernarySecret length weight →
        TernaryWord length) := by
  rintro ⟨leftSupport, leftSign⟩ ⟨rightSupport, rightSign⟩ heq
  have hsupportValue : leftSupport.1 = rightSupport.1 := by
    rw [← wordSupport_decodeFixedWeightTernary ⟨leftSupport, leftSign⟩,
      ← wordSupport_decodeFixedWeightTernary ⟨rightSupport, rightSign⟩, heq]
  have hsupport : leftSupport = rightSupport := Subtype.ext hsupportValue
  subst rightSupport
  have hsign : leftSign = rightSign := by
    funext index
    apply signedDigit_injective
    have hcoefficient := congrFun heq index.1
    simpa [decodeFixedWeightTernary, index.2] using hcoefficient
  rw [hsign]

/-- The concrete secret support has the exact cardinality used in the aggregate theorem. -/
@[simp]
theorem card_encodedFixedWeightTernarySecret (length weight : ℕ) :
    Fintype.card (EncodedFixedWeightTernarySecret length weight) =
      2 ^ weight * length.choose weight :=
  RankOneHNFLossinessSupportAware.card_fixedWeightTernarySecret length weight

def encodedPrimitivePolynomialDifference
    (d weight : ℕ)
    (left right : EncodedFixedWeightTernarySecret (2 ^ d) weight) : F2[X] :=
  binaryWordPolynomial
    (primitiveDifference
      (decodeFixedWeightTernary left) (decodeFixedWeightTernary right))

def encodedPrimitiveRank
    (d weight : ℕ)
    (left right : EncodedFixedWeightTernarySecret (2 ^ d) weight) : ℕ :=
  primitiveDifferenceRank d
    (decodeFixedWeightTernary left) (decodeFixedWeightTernary right)

theorem encodedPrimitiveRank_pos
    (d weight : ℕ)
    {left right : EncodedFixedWeightTernarySecret (2 ^ d) weight}
    (hne : left ≠ right) :
    0 < encodedPrimitiveRank d weight left right := by
  apply primitiveDifferenceRank_pos
  exact fun heq ↦ hne (decodeFixedWeightTernary_injective heq)

theorem encodedPrimitiveRank_dyadic_lower_bound
    (d weight : ℕ)
    {left right : EncodedFixedWeightTernarySecret (2 ^ d) weight}
    (hne : left ≠ right) (hweightRange : 2 * weight ≤ 2 ^ d) :
    2 ^ (d - Nat.log2 (2 * weight)) ≤
      encodedPrimitiveRank d weight left right := by
  apply primitiveDifferenceRank_dyadic_lower_bound d weight
  · exact fun heq ↦ hne (decodeFixedWeightTernary_injective heq)
  · exact decodeFixedWeightTernary_isFixedWeight left
  · exact decodeFixedWeightTernary_isFixedWeight right
  · exact hweightRange

/-! ## Lifting binary rank to uniform production coordinates -/

/-- In any certified binary chain ring, `length - valuation(value)` is literally the base-two
logarithm of the image size of multiplication by `value`. -/
theorem card_rightMulRange_eq_two_pow_rank
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    (chain : PowerOfTwoQuadraticKDMStatistical.FiniteAdicChain R) (value : R) :
    Nat.card (PowerOfTwoQuadraticKDMStatistical.rightMulAddHom value).range =
      2 ^ (chain.length - chain.valuation value) := by
  rw [chain.principal_eq value]
  exact chain.card_power (chain.valuation value) (chain.valuation_le value)

/-- A square minor whose reduction modulo two has nonzero determinant has unit determinant over
the source local ring.  This is the formal odd-determinant lifting step. -/
theorem isUnit_det_of_binary_minor
    {R Index : Type} [CommRing R] [Fintype Index] [DecidableEq Index]
    (parity : R →+* F2) [IsLocalHom parity] (minor : Matrix Index Index R)
    (hbinary : (minor.map parity).det ≠ 0) :
    IsUnit minor.det := by
  apply IsUnit.of_map parity minor.det
  rw [RingHom.map_det]
  exact isUnit_iff_ne_zero.mpr hbinary

/-- Consequently the lifted minor is a bijection on its selected coordinates. -/
theorem binary_minor_mulVec_bijective
    {R Index : Type} [CommRing R] [Fintype Index] [DecidableEq Index]
    (parity : R →+* F2) [IsLocalHom parity] (minor : Matrix Index Index R)
    (hbinary : (minor.map parity).det ≠ 0) :
    Function.Bijective minor.mulVec := by
  let invertible : Invertible minor :=
    Matrix.invertibleOfIsUnitDet minor
      (isUnit_det_of_binary_minor parity minor hbinary)
  exact (minor.toLinearEquiv' invertible).bijective

/-- Uniform selected inputs remain jointly uniform after the lifted minor and any fixed
translation (including the conditioned quadratic shift). -/
theorem binary_minor_affine_uniform
    {R Index : Type} [CommRing R] [Fintype R] [SampleableType R]
    [Fintype Index] [DecidableEq Index]
    (parity : R →+* F2) [IsLocalHom parity] (minor : Matrix Index Index R)
    (hbinary : (minor.map parity).det ≠ 0) (translation : Index → R) :
    evalDist
        ((fun input ↦ minor.mulVec input + translation) <$>
          ($ᵗ (Index → R))) =
      evalDist ($ᵗ (Index → R)) := by
  let invertible : Invertible minor :=
    Matrix.invertibleOfIsUnitDet minor
      (isUnit_det_of_binary_minor parity minor hbinary)
  let affineEquiv : (Index → R) ≃ (Index → R) :=
    (minor.toLinearEquiv' invertible).toEquiv.trans (Equiv.addRight translation)
  have haffine : (affineEquiv : (Index → R) → Index → R) =
      fun input ↦ minor.mulVec input + translation := by
    funext input
    rfl
  simpa only [haffine] using
    (evalDist_map_bijective_uniform_cross
      (α := Index → R) (β := Index → R)
      (fun input ↦ minor.mulVec input + translation) affineEquiv.bijective)

/-! ## Exact rank and valuation enumerators -/

/-- Ordered off-diagonal pairs in a finite secret support. -/
def orderedDistinctPairs (Secret : Type) [Fintype Secret] [DecidableEq Secret] :
    Finset (Secret × Secret) :=
  (Finset.univ.product Finset.univ).filter fun pair ↦ pair.1 ≠ pair.2

@[simp]
theorem mem_orderedDistinctPairs_iff
    {Secret : Type} [Fintype Secret] [DecidableEq Secret] (pair : Secret × Secret) :
    pair ∈ orderedDistinctPairs Secret ↔ pair.1 ≠ pair.2 := by
  simp [orderedDistinctPairs]

theorem card_orderedDistinctPairs
    (Secret : Type) [Fintype Secret] [DecidableEq Secret] :
    (orderedDistinctPairs Secret).card =
      Fintype.card Secret * (Fintype.card Secret - 1) := by
  let all : Finset (Secret × Secret) := Finset.univ.product Finset.univ
  let offDiagonal := all.filter fun pair ↦ pair.1 ≠ pair.2
  let diagonal := all.filter fun pair ↦ pair.1 = pair.2
  have hdiagonal : diagonal.card = Fintype.card Secret := by
    rw [← Finset.card_univ]
    apply Finset.card_bij (fun pair _ ↦ pair.1)
    · intro pair _
      simp
    · intro left hleft right hright heq
      apply Prod.ext heq
      simp only [diagonal, Finset.mem_filter] at hleft hright
      rw [← hleft.2, ← hright.2, heq]
    · intro secret _
      refine ⟨(secret, secret), ?_, rfl⟩
      simp [diagonal, all]
  have hpartition : offDiagonal.card + diagonal.card = all.card := by
    have h := Finset.card_filter_add_card_filter_not
      (s := all) (fun pair : Secret × Secret ↦ pair.1 ≠ pair.2)
    simpa [offDiagonal, diagonal] using h
  have hall : all.card = Fintype.card Secret * Fintype.card Secret := by
    simp [all]
  change offDiagonal.card = _
  rw [hdiagonal, hall] at hpartition
  calc
    offDiagonal.card =
        Fintype.card Secret * Fintype.card Secret - Fintype.card Secret :=
      Nat.eq_sub_of_add_eq hpartition
    _ = Fintype.card Secret * (Fintype.card Secret - 1) := by
      rw [Nat.mul_sub_left_distrib]
      simp

/-- Number of ordered distinct pairs on which a statistic has the exact value `level`. -/
def pairStatisticCount
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (statistic : Secret → Secret → ℕ) (level : ℕ) : ℕ :=
  ((orderedDistinctPairs Secret).filter
    fun pair ↦ statistic pair.1 pair.2 = level).card

/-- Number of ordered distinct pairs whose statistic is at least `level`. -/
def cumulativePairStatisticCount
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (statistic : Secret → Secret → ℕ) (level : ℕ) : ℕ :=
  ((orderedDistinctPairs Secret).filter
    fun pair ↦ level ≤ statistic pair.1 pair.2).card

/-- Exact strata are successive differences of cumulative strata. -/
theorem cumulativePairStatisticCount_eq_exact_add_succ
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (statistic : Secret → Secret → ℕ) (level : ℕ) :
    cumulativePairStatisticCount statistic level =
      pairStatisticCount statistic level +
        cumulativePairStatisticCount statistic (level + 1) := by
  rw [cumulativePairStatisticCount, pairStatisticCount,
    cumulativePairStatisticCount]
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext pair
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hpair, hle⟩
      rcases eq_or_lt_of_le hle with heq | hlt
      · exact Or.inl ⟨hpair, heq.symm⟩
      · exact Or.inr ⟨hpair, by omega⟩
    · rintro (⟨hpair, heq⟩ | ⟨hpair, hsucc⟩)
      · exact ⟨hpair, by omega⟩
      · exact ⟨hpair, by omega⟩
  · rw [Finset.disjoint_left]
    intro pair hexact hsucc
    simp only [Finset.mem_filter] at hexact hsucc
    omega

theorem pairStatisticCount_eq_cumulative_sub_succ
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (statistic : Secret → Secret → ℕ) (level : ℕ) :
    pairStatisticCount statistic level =
      cumulativePairStatisticCount statistic level -
        cumulativePairStatisticCount statistic (level + 1) := by
  have := cumulativePairStatisticCount_eq_exact_add_succ statistic level
  omega

/-- Count pairs by vanishing of the first `level` Hasse syndromes. -/
def syndromeCumulativePairCount
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (difference : Secret → Secret → F2[X]) (level : ℕ) : ℕ := by
  classical
  exact ((orderedDistinctPairs Secret).filter fun (pair : Secret × Secret) ↦
    syndromesZeroBelow (difference pair.1 pair.2) level).card

/-- Cumulative valuation counts are exactly zero-syndrome counts. -/
theorem cumulative_hasseValuation_count_eq_syndrome_count
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (length : ℕ) (difference : Secret → Secret → F2[X])
    (level : ℕ) (hlevel : level ≤ length) :
    cumulativePairStatisticCount
        (fun left right ↦ hasseValuation length (difference left right)) level =
      syndromeCumulativePairCount difference level := by
  unfold cumulativePairStatisticCount syndromeCumulativePairCount
  apply congrArg Finset.card
  ext pair
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hpair, hvaluation⟩
    exact ⟨hpair,
      (le_hasseValuation_iff_syndromesZeroBelow
        length (difference pair.1 pair.2) hlevel).mp hvaluation⟩
  · rintro ⟨hpair, hsyndrome⟩
    exact ⟨hpair,
      (le_hasseValuation_iff_syndromesZeroBelow
        length (difference pair.1 pair.2) hlevel).mpr hsyndrome⟩

/-- Exact exceptional-depth counts are the difference of two explicitly testable zero-syndrome
counts `C_{≥v} - C_{≥v+1}`. -/
theorem exact_hasseValuation_count_eq_syndrome_count_sub_succ
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (length : ℕ) (difference : Secret → Secret → F2[X])
    (level : ℕ) (hlevel : level < length) :
    pairStatisticCount
        (fun left right ↦ hasseValuation length (difference left right)) level =
      syndromeCumulativePairCount difference level -
        syndromeCumulativePairCount difference (level + 1) := by
  rw [pairStatisticCount_eq_cumulative_sub_succ,
    cumulative_hasseValuation_count_eq_syndrome_count length difference level hlevel.le,
    cumulative_hasseValuation_count_eq_syndrome_count length difference (level + 1) (by omega)]

/-- A rank statistic obtained as codimension of a bounded valuation. -/
def valuationRank {Secret : Type}
    (length : ℕ) (valuation : Secret → Secret → ℕ)
    (left right : Secret) : ℕ :=
  length - valuation left right

/-- Rank-`r` pairs are valuation-`length-r` pairs. -/
theorem pairStatisticCount_valuationRank
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (length : ℕ) (valuation : Secret → Secret → ℕ)
    (hvaluation : ∀ left right, valuation left right ≤ length)
    (rank : ℕ) (hrank : rank ≤ length) :
    pairStatisticCount (valuationRank length valuation) rank =
      pairStatisticCount valuation (length - rank) := by
  unfold pairStatisticCount
  congr 1
  ext pair
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hpair, heq⟩
    exact ⟨hpair, by
      have hvaluationBound := hvaluation pair.1 pair.2
      unfold valuationRank at heq
      omega⟩
  · rintro ⟨hpair, heq⟩
    exact ⟨hpair, by
      have hvaluationBound := hvaluation pair.1 pair.2
      unfold valuationRank
      omega⟩

/-- Exact rank strata of a Hasse-valued family are computable from adjacent cumulative syndrome
counts. -/
theorem exact_hasseRank_count_eq_syndrome_count_sub_succ
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (length : ℕ) (difference : Secret → Secret → F2[X])
    (rank : ℕ) (hrankPos : 0 < rank) (hrank : rank ≤ length) :
    pairStatisticCount
        (valuationRank length
          (fun left right ↦ hasseValuation length (difference left right))) rank =
      syndromeCumulativePairCount difference (length - rank) -
        syndromeCumulativePairCount difference (length - rank + 1) := by
  rw [pairStatisticCount_valuationRank length _
      (fun left right ↦ hasseValuation_le length (difference left right)) rank hrank]
  exact exact_hasseValuation_count_eq_syndrome_count_sub_succ
    length difference (length - rank) (by omega)

/-- Every bounded pair statistic partitions an arbitrary pair sum into exact strata. -/
theorem sum_orderedDistinctPairs_eq_sum_pairStatisticCount
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (statistic : Secret → Secret → ℕ) (bound : ℕ)
    (hbound : ∀ left right, left ≠ right → statistic left right ≤ bound)
    (value : ℕ → ℝ) :
    (∑ pair ∈ orderedDistinctPairs Secret,
        value (statistic pair.1 pair.2)) =
      ∑ level ∈ Finset.range (bound + 1),
        (pairStatisticCount statistic level : ℝ) * value level := by
  calc
    _ = ∑ pair ∈ orderedDistinctPairs Secret,
        ∑ level ∈ Finset.range (bound + 1),
          if statistic pair.1 pair.2 = level then value level else 0 := by
      apply Finset.sum_congr rfl
      intro pair hpair
      rw [Finset.sum_eq_single (statistic pair.1 pair.2)]
      · simp
      · intro level _ hne
        simp [hne.symm]
      · rw [Finset.mem_range]
        intro hnot
        exfalso
        apply hnot
        exact Nat.lt_succ_of_le
          (hbound pair.1 pair.2 (mem_orderedDistinctPairs_iff pair |>.mp hpair))
    _ = ∑ level ∈ Finset.range (bound + 1),
        ∑ pair ∈ orderedDistinctPairs Secret,
          if statistic pair.1 pair.2 = level then value level else 0 := by
      rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro level _
      rw [pairStatisticCount, ← Finset.sum_filter]
      simp

/-- Average number of ordered alternatives in one exact stratum. -/
def averagePairStatisticCount
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (statistic : Secret → Secret → ℕ) (level : ℕ) : ℝ :=
  (pairStatisticCount statistic level : ℝ) / Fintype.card Secret

/-- Exact rank-enumerator identity
`(1/M) sum_{s != t} theta^{rank(s,t)} = sum_r Nbar_r theta^r`. -/
theorem average_rankKernel_eq_rankEnumerator
    {Secret : Type} [Fintype Secret] [Nonempty Secret] [DecidableEq Secret]
    (rank : Secret → Secret → ℕ) (bound : ℕ)
    (hrank : ∀ left right, left ≠ right → rank left right ≤ bound)
    (theta : ℝ) :
    (∑ pair ∈ orderedDistinctPairs Secret, theta ^ rank pair.1 pair.2) /
        Fintype.card Secret =
      ∑ level ∈ Finset.range (bound + 1),
        averagePairStatisticCount rank level * theta ^ level := by
  rw [sum_orderedDistinctPairs_eq_sum_pairStatisticCount rank bound hrank]
  unfold averagePairStatisticCount
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro level _
  ring

/-- Rank-stratified aggregation.  Any local Gaussian/theta or bounded-support estimate of the
form `kernel(s,t) ≤ base^rank(s,t)` sums with the exact rank enumerator. -/
theorem average_pairKernel_le_rankEnumerator
    {Secret : Type} [Fintype Secret] [Nonempty Secret] [DecidableEq Secret]
    (rank : Secret → Secret → ℕ) (bound : ℕ)
    (hrank : ∀ left right, left ≠ right → rank left right ≤ bound)
    (kernel : Secret → Secret → ℝ) (base : ℝ)
    (hkernel : ∀ left right, left ≠ right →
      kernel left right ≤ base ^ rank left right) :
    (∑ pair ∈ orderedDistinctPairs Secret, kernel pair.1 pair.2) /
        Fintype.card Secret ≤
      ∑ level ∈ Finset.range (bound + 1),
        averagePairStatisticCount rank level * base ^ level := by
  calc
    (∑ pair ∈ orderedDistinctPairs Secret, kernel pair.1 pair.2) /
        Fintype.card Secret ≤
      (∑ pair ∈ orderedDistinctPairs Secret, base ^ rank pair.1 pair.2) /
        Fintype.card Secret := by
          apply div_le_div_of_nonneg_right
          · apply Finset.sum_le_sum
            intro pair hpair
            exact hkernel pair.1 pair.2
              (mem_orderedDistinctPairs_iff pair |>.mp hpair)
          · positivity
    _ = _ := average_rankKernel_eq_rankEnumerator rank bound hrank base

/-- Coarser full-support bound obtained by replacing the exact enumerator with a uniform minimum
rank.  This is the symbolic `(M-1) * theta^r_min` estimate. -/
theorem average_pairKernel_le_card_sub_one_mul_pow
    {Secret : Type} [Fintype Secret] [Nonempty Secret] [DecidableEq Secret]
    (rank : Secret → Secret → ℕ) (minimumRank : ℕ)
    (kernel : Secret → Secret → ℝ) (base : ℝ)
    (hbaseNonneg : 0 ≤ base) (hbaseOne : base ≤ 1)
    (hrank : ∀ left right, left ≠ right → minimumRank ≤ rank left right)
    (hkernel : ∀ left right, left ≠ right →
      kernel left right ≤ base ^ rank left right) :
    (∑ pair ∈ orderedDistinctPairs Secret, kernel pair.1 pair.2) /
        Fintype.card Secret ≤
      (Fintype.card Secret - 1) * base ^ minimumRank := by
  have hpoint : ∀ pair ∈ orderedDistinctPairs Secret,
      kernel pair.1 pair.2 ≤ base ^ minimumRank := by
    intro pair hpair
    have hne := (mem_orderedDistinctPairs_iff pair).mp hpair
    exact (hkernel pair.1 pair.2 hne).trans
      (pow_le_pow_of_le_one hbaseNonneg hbaseOne (hrank pair.1 pair.2 hne))
  calc
    (∑ pair ∈ orderedDistinctPairs Secret, kernel pair.1 pair.2) /
        Fintype.card Secret ≤
      (∑ _pair ∈ orderedDistinctPairs Secret, base ^ minimumRank) /
        Fintype.card Secret := by
      apply div_le_div_of_nonneg_right
      · exact Finset.sum_le_sum hpoint
      · positivity
    _ = ((orderedDistinctPairs Secret).card : ℝ) * base ^ minimumRank /
        Fintype.card Secret := by simp
    _ = (Fintype.card Secret - 1) * base ^ minimumRank := by
      rw [card_orderedDistinctPairs]
      rw [Nat.cast_mul, Nat.cast_sub (Fintype.card_pos_iff.mpr inferInstance)]
      have hcardNe : (Fintype.card Secret : ℝ) ≠ 0 := by positivity
      field_simp
      ring

/-! ## Finite Markov and union-bound endgames -/

/-- Finite weighted Markov inequality, stated in the exact form used for the bad-mask event. -/
theorem finiteWeightedMarkov
    {Context : Type} [Fintype Context] [DecidableEq Context]
    (mass excess : Context → ℝ) (threshold : ℝ)
    (hmass : ∀ context, 0 ≤ mass context)
    (hexcess : ∀ context, 0 ≤ excess context)
    (hthreshold : 0 < threshold) :
    (∑ context ∈ Finset.univ.filter (fun context ↦ threshold ≤ excess context),
        mass context) ≤
      (∑ context, mass context * excess context) / threshold := by
  rw [le_div_iff₀ hthreshold]
  calc
    (∑ context ∈ Finset.univ.filter (fun context ↦ threshold ≤ excess context),
        mass context) * threshold =
      ∑ context ∈ Finset.univ.filter (fun context ↦ threshold ≤ excess context),
        mass context * threshold := by rw [Finset.sum_mul]
    _ ≤ ∑ context ∈ Finset.univ.filter (fun context ↦ threshold ≤ excess context),
        mass context * excess context := by
      apply Finset.sum_le_sum
      intro context hcontext
      exact mul_le_mul_of_nonneg_left (Finset.mem_filter.mp hcontext).2 (hmass context)
    _ ≤ ∑ context, mass context * excess context := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      intro context _ _
      exact mul_nonneg (hmass context) (hexcess context)

/-- A finite weighted union bound. -/
theorem finiteWeightedUnionBound
    {Index Context : Type} [Fintype Context] [DecidableEq Context] [DecidableEq Index]
    (indices : Finset Index) (event : Index → Context → Prop)
    [∀ index context, Decidable (event index context)]
    (mass : Context → ℝ) (hmass : ∀ context, 0 ≤ mass context) :
    (∑ context ∈ Finset.univ.filter
        (fun context ↦ ∃ index ∈ indices, event index context), mass context) ≤
      ∑ index ∈ indices,
        ∑ context ∈ Finset.univ.filter (event index), mass context := by
  classical
  calc
    (∑ context ∈ Finset.univ.filter
        (fun context ↦ ∃ index ∈ indices, event index context), mass context) =
      ∑ context, if ∃ index ∈ indices, event index context then mass context else 0 := by
        rw [← Finset.sum_filter]
    _ ≤ ∑ context, ∑ index ∈ indices,
        if event index context then mass context else 0 := by
      apply Finset.sum_le_sum
      intro context _
      by_cases hunion : ∃ index ∈ indices, event index context
      · simp only [if_pos hunion]
        obtain ⟨index, hindex, hevent⟩ := hunion
        have hsingle :
            (if event index context then mass context else 0) ≤
              ∑ other ∈ indices,
                if event other context then mass context else 0 := by
          apply Finset.single_le_sum
            (s := indices)
            (f := fun other ↦ if event other context then mass context else 0)
          · intro other _
            by_cases hother : event other context
            · simp [hother, hmass context]
            · simp [hother]
          · exact hindex
        simpa [hevent] using hsingle
      · simp only [if_neg hunion]
        exact Finset.sum_nonneg fun index _ ↦ by
          by_cases hindex : event index context
          · simp [hindex, hmass context]
          · simp [hindex]
    _ = ∑ index ∈ indices,
        ∑ context, if event index context then mass context else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ index ∈ indices,
        ∑ context ∈ Finset.univ.filter (event index), mass context := by
      apply Finset.sum_congr rfl
      intro index _
      rw [← Finset.sum_filter]

/-- If total context mass is one, avoiding every competing close-shift event has mass at least
one minus the sum of the individual event masses.  This is the bounded-noise exhaustive-guessing
endgame. -/
theorem finiteExhaustiveSuccessLowerBound
    {Index Context : Type} [Fintype Context] [DecidableEq Context] [DecidableEq Index]
    (indices : Finset Index) (event : Index → Context → Prop)
    [∀ index context, Decidable (event index context)]
    (mass : Context → ℝ) (hmass : ∀ context, 0 ≤ mass context)
    (htotal : (∑ context, mass context) = 1) :
    1 - ∑ index ∈ indices,
          ∑ context ∈ Finset.univ.filter (event index), mass context ≤
      ∑ context ∈ Finset.univ.filter
        (fun context ↦ ∀ index ∈ indices, ¬event index context), mass context := by
  let bad : Context → Prop := fun context ↦ ∃ index ∈ indices, event index context
  have hunion := finiteWeightedUnionBound indices event mass hmass
  have hpartition := Finset.sum_filter_add_sum_filter_not
    Finset.univ bad mass
  have hgood :
      (∑ context ∈ Finset.univ.filter
          (fun context ↦ ∀ index ∈ indices, ¬event index context), mass context) =
        1 - ∑ context ∈ Finset.univ.filter bad, mass context := by
    have hnotBad : ∀ context, ¬bad context ↔
        ∀ index ∈ indices, ¬event index context := by
      intro context
      simp [bad]
    have hfilter : Finset.univ.filter (¬bad ·) =
        Finset.univ.filter
          (fun context ↦ ∀ index ∈ indices, ¬event index context) := by
      ext context
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact hnotBad context
    rw [hfilter] at hpartition
    rw [htotal] at hpartition
    linarith
  calc
    1 - ∑ index ∈ indices,
          ∑ context ∈ Finset.univ.filter (event index), mass context ≤
        1 - ∑ context ∈ Finset.univ.filter bad, mass context :=
      sub_le_sub_left hunion 1
    _ = _ := hgood.symm

/-! ### Fixed-weight specialization of the exact enumerator -/

theorem encodedPrimitiveRank_eq_valuationRank
    (d weight : ℕ) :
    encodedPrimitiveRank d weight =
      valuationRank (2 ^ d)
        (fun left right ↦
          hasseValuation (2 ^ d)
            (encodedPrimitivePolynomialDifference d weight left right)) := by
  funext left right
  rfl

/-- For the actual fixed-weight ternary support, every positive exact-rank count is the
difference of adjacent Hasse zero-syndrome counts. -/
theorem exact_encodedPrimitiveRank_count_eq_syndrome_count_sub_succ
    (d weight rank : ℕ) (hrankPos : 0 < rank) (hrank : rank ≤ 2 ^ d) :
    pairStatisticCount (encodedPrimitiveRank d weight) rank =
      syndromeCumulativePairCount
          (encodedPrimitivePolynomialDifference d weight) (2 ^ d - rank) -
        syndromeCumulativePairCount
          (encodedPrimitivePolynomialDifference d weight) (2 ^ d - rank + 1) := by
  rw [encodedPrimitiveRank_eq_valuationRank]
  exact exact_hasseRank_count_eq_syndrome_count_sub_succ
    (2 ^ d) (encodedPrimitivePolynomialDifference d weight)
    rank hrankPos hrank

/-- Gaussian-overlap specialization.  Once the analytic one-coordinate estimate supplies
`kernel(s,t) ≤ theta^rank(s,t)`, Lean reduces the whole fixed-weight support to its exact rank
enumerator.  The same theorem applies to a bounded-support close-shift kernel by replacing
`theta` with its one-coordinate probability `zeta`. -/
theorem average_encodedPrimitiveKernel_le_exactRankEnumerator
    (d weight : ℕ)
    [Nonempty (EncodedFixedWeightTernarySecret (2 ^ d) weight)]
    (kernel : EncodedFixedWeightTernarySecret (2 ^ d) weight →
      EncodedFixedWeightTernarySecret (2 ^ d) weight → ℝ)
    (base : ℝ)
    (hkernel : ∀ left right, left ≠ right →
      kernel left right ≤ base ^ encodedPrimitiveRank d weight left right) :
    (∑ pair ∈ orderedDistinctPairs
        (EncodedFixedWeightTernarySecret (2 ^ d) weight),
        kernel pair.1 pair.2) /
        Fintype.card (EncodedFixedWeightTernarySecret (2 ^ d) weight) ≤
      ∑ rank ∈ Finset.range (2 ^ d + 1),
        averagePairStatisticCount (encodedPrimitiveRank d weight) rank *
          base ^ rank := by
  apply average_pairKernel_le_rankEnumerator
  · intro left right _
    exact primitiveDifferenceRank_le_length d
      (decodeFixedWeightTernary left) (decodeFixedWeightTernary right)
  · exact hkernel

end

end FormalProof4FHE.RLWE.RankOneHNFLossinessSparseRank
