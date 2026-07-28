/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.RankOneHNFLossinessSparseRank
import FormalProof4FHE.Probability.FiniteAdditiveCokernel
import FormalProof4FHE.Probability.FiniteSurjectiveFiber
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Concrete channel consequences of sparse repeated-root rank

This file connects the Hasse valuation computed from a binary coefficient polynomial to
multiplication in the literal binary negacyclic quotient.  It then develops proof-carrying
interfaces for lifting that rank to a power-of-two production channel, for exact finite
overlap aggregation, and for rank-aware wrong-candidate randomization.

No implementation sampler or analytic Gaussian estimate is postulated as an axiom.  The local
channel estimates are ordinary theorem hypotheses, so a concrete sampler can discharge them by
either a theta-function argument or a finite-support counting argument.
-/

open BigOperators
open Polynomial
open scoped ENNReal

namespace FormalProof4FHE.RLWE.RankOneHNFLossinessSparseRankChannel

open RankOneHNFLossinessSparseRank
open PowerOfTwoQuadraticKDMStatistical

noncomputable section

private local instance oneExponentPositive : Fact (0 < (1 : ℕ)) := ⟨by omega⟩

/-! ## Production-coordinate certificate -/

/-- Checkable implementation-side evidence selecting `rank` source/output coordinates whose
binary multiplication minor is nonsingular.  The abstract Hasse rank theorem fixes the required
value of `rank`; this certificate identifies concrete production coordinates. -/
structure ProductionMinorCertificate
    (R : Type) [CommRing R] (parity : R →+* F2)
    {Source Output : Type} (channel : Matrix Output Source R) (rank : ℕ) where
  rows : Fin rank → Output
  columns : Fin rank → Source
  binaryDet_ne :
    (((channel.submatrix rows columns).map parity).det) ≠ 0

/-- Production-minor obligation with its size fixed to the exact Hasse rank of a primitive
ternary difference. -/
abbrev PrimitiveDifferenceProductionMinorCertificate
    (R : Type) [CommRing R] (parity : R →+* F2)
    {Source Output : Type} (channel : Matrix Output Source R)
    (d : ℕ) (left right : TernaryWord (2 ^ d)) :=
  ProductionMinorCertificate R parity channel
    (primitiveDifferenceRank d left right)

/-- A production minor certificate lifts automatically to jointly uniform selected coordinates,
after any fixed translation. -/
theorem ProductionMinorCertificate.affine_uniform
    {R : Type} [CommRing R] [Fintype R] [SampleableType R]
    (parity : R →+* F2) [IsLocalHom parity]
    {Source Output : Type} (channel : Matrix Output Source R) (rank : ℕ)
    (certificate : ProductionMinorCertificate R parity channel rank)
    (translation : Fin rank → R) :
    evalDist
        ((fun input ↦
            (channel.submatrix certificate.rows certificate.columns).mulVec input +
              translation) <$>
          ($ᵗ (Fin rank → R))) =
      evalDist ($ᵗ (Fin rank → R)) :=
by
  let minor := channel.submatrix certificate.rows certificate.columns
  let invertible : Invertible minor :=
    Matrix.invertibleOfIsUnitDet minor
      (isUnit_det_of_binary_minor parity minor certificate.binaryDet_ne)
  let affineEquiv : (Fin rank → R) ≃ (Fin rank → R) :=
    (minor.toLinearEquiv' invertible).toEquiv.trans
      (Equiv.addRight translation)
  have haffine : (affineEquiv : (Fin rank → R) → Fin rank → R) =
      fun input ↦ minor.mulVec input + translation := by
    funext input
    rfl
  simpa only [haffine] using
    (evalDist_map_bijective_uniform_cross
      (α := Fin rank → R) (β := Fin rank → R)
      (fun input ↦ minor.mulVec input + translation)
      affineEquiv.bijective)

/-- The quadratic candidate shift factors through the same secret difference as the linear
mask term. -/
theorem quadraticCandidateShift_factor
    {R : Type} [CommRing R] (a g s t : R) :
    (t - s) * a + g * (t ^ 2 - s ^ 2) =
      (t - s) * (a + g * (t + s)) := by
  ring

/-- After extracting `2^e` from the secret difference, the full quadratic channel has the same
factor.  Conditioned on the secrets, `g * (t+s)` is only a fixed translation of the uniform
mask variable. -/
theorem quadraticCandidateShift_factor_twoAdic
    {R : Type} [CommRing R] (a g s t primitive : R) (e : ℕ)
    (hdifference : t - s = (2 : R) ^ e * primitive) :
    (t - s) * a + g * (t ^ 2 - s ^ 2) =
      (2 : R) ^ e * (primitive * (a + g * (t + s))) := by
  rw [quadraticCandidateShift_factor, hdifference]
  ring

/-! ## Binary quotient valuation -/

/-- Interpret a binary polynomial in the literal degree-`2^d` negacyclic quotient. -/
def binaryQuotientPolynomial (d : ℕ) (polynomial : F2[X]) :
    QuotientRq 2 (2 ^ d) :=
  Ideal.Quotient.mk _ polynomial

/-- In characteristic two, the two conventional choices of repeated-root uniformizer agree. -/
theorem binary_one_sub_X_eq_X_sub_one :
    (C 1 - X : F2[X]) = X - C 1 := by
  have hneg (polynomial : F2[X]) : -polynomial = polynomial := by
    ext coefficient
    exact ZMod.neg_eq_self_mod_two _
  rw [sub_eq_add_neg, sub_eq_add_neg, hneg X, hneg (C 1), add_comm]

/-- Membership of a polynomial class in the `level`th binary quotient ideal is exactly
divisibility of the representative by `(X-1)^level`, up to the nilpotence length. -/
theorem binaryQuotientPolynomial_mem_adicPower_iff
    (d level : ℕ) (hlevel : level ≤ 2 ^ d) (polynomial : F2[X]) :
    binaryQuotientPolynomial d polynomial ∈
        adicPower (quotientUniformizer 2 (2 ^ d)) level ↔
      (X - C (1 : F2)) ^ level ∣ polynomial := by
  constructor
  · rintro ⟨multiplier, hmultiplier⟩
    obtain ⟨factor, rfl⟩ := Ideal.Quotient.mk_surjective multiplier
    simp only [rightMulAddHom_apply] at hmultiplier
    change Ideal.Quotient.mk _ factor *
        quotientUniformizer 2 (2 ^ d) ^ level =
      Ideal.Quotient.mk _ polynomial at hmultiplier
    rw [show quotientUniformizer 2 (2 ^ d) ^ level =
        Ideal.Quotient.mk _ ((X - C (1 : F2)) ^ level) by
          rw [← binary_one_sub_X_eq_X_sub_one]
          simp [quotientUniformizer]] at hmultiplier
    rw [← map_mul, Ideal.Quotient.mk_eq_mk_iff_sub_mem,
      Ideal.mem_span_singleton] at hmultiplier
    obtain ⟨modulusFactor, hdifference⟩ := hmultiplier
    have hmodulus :
        LatticeCrypto.negacyclicModulus F2 (2 ^ d) =
          (X - C (1 : F2)) ^ level *
            (X - C (1 : F2)) ^ (2 ^ d - level) := by
      rw [FormalProof4FHE.TFHE.Native.PowerOfTwoLocalRing.binary_negacyclicModulus_eq_X_sub_one_pow,
        ← pow_add]
      congr 1
      omega
    refine ⟨factor - (X - C (1 : F2)) ^ (2 ^ d - level) * modulusFactor, ?_⟩
    rw [hmodulus] at hdifference
    linear_combination -hdifference
  · rintro ⟨factor, rfl⟩
    refine ⟨Ideal.Quotient.mk _ factor, ?_⟩
    simp only [rightMulAddHom_apply]
    change Ideal.Quotient.mk _ factor *
        quotientUniformizer 2 (2 ^ d) ^ level =
      binaryQuotientPolynomial d
        ((X - C (1 : F2)) ^ level * factor)
    rw [show quotientUniformizer 2 (2 ^ d) ^ level =
        Ideal.Quotient.mk _ ((X - C (1 : F2)) ^ level) by
          rw [← binary_one_sub_X_eq_X_sub_one]
          simp [quotientUniformizer]]
    simp only [binaryQuotientPolynomial, map_mul]
    ring

/-- The chain valuation of a nonzero degree-bounded binary representative is exactly its
finite Hasse valuation. -/
theorem binaryQuotientPolynomial_chainValuation_eq_hasseValuation
    (d : ℕ) {polynomial : F2[X]} (hne : polynomial ≠ 0)
    (hdegree : polynomial.natDegree < 2 ^ d) :
    (quotientPowerOfTwoAdicChain 1 d).valuation
        (binaryQuotientPolynomial d polynomial) =
      hasseValuation (2 ^ d) polynomial := by
  classical
  letI : Fintype (QuotientRq 2 (2 ^ d)) :=
    PowerOfTwoQuadraticKDMStatistical.quotientPowerOfTwoRqFintype 1 d
  letI : DecidableEq (QuotientRq 2 (2 ^ d)) :=
    PowerOfTwoQuadraticKDMStatistical.quotientPowerOfTwoRqDecidableEq 1 d
  let value := binaryQuotientPolynomial d polynomial
  let valuation := hasseValuation (2 ^ d) polynomial
  have hvaluationLt : valuation < 2 ^ d :=
    hasseValuation_lt_of_ne_zero (2 ^ d) hne hdegree
  have hvalueMem : value ∈ adicPower
      (quotientUniformizer 2 (2 ^ d)) valuation := by
    rw [binaryQuotientPolynomial_mem_adicPower_iff d valuation hvaluationLt.le]
    exact X_sub_one_pow_hasseValuation_dvd _ _
  have hvalueNotMem : value ∉ adicPower
      (quotientUniformizer 2 (2 ^ d)) (valuation + 1) := by
    rw [binaryQuotientPolynomial_mem_adicPower_iff d (valuation + 1) (by omega)]
    rw [X_sub_one_pow_dvd_iff_hasseSyndrome_zero]
    intro hzero
    exact (hasseSyndrome_hasseValuation_ne_zero (2 ^ d) hne hdegree)
      (hzero valuation (by omega))
  change truncatedValuation (quotientUniformizer 2 (2 ^ d))
      (1 * 2 ^ d) value = valuation
  simp only [one_mul]
  apply Nat.le_antisymm
  · by_contra hnot
    have hsucc : valuation + 1 ≤ truncatedValuation
        (quotientUniformizer 2 (2 ^ d)) (2 ^ d) value := by omega
    exact hvalueNotMem
      (mem_adicPower_of_le_truncatedValuation
        (quotientUniformizer 2 (2 ^ d)) (2 ^ d) value hsucc)
  · apply Nat.le_findGreatest hvaluationLt.le
    exact hvalueMem

/-- Hence the Hasse rank is literally the binary multiplication-image dimension, expressed as
the base-two logarithm of its exact cardinality. -/
theorem card_binaryQuotient_rightMulRange_eq_two_pow_hasseRank
    (d : ℕ) {polynomial : F2[X]} (hne : polynomial ≠ 0)
    (hdegree : polynomial.natDegree < 2 ^ d) :
    Nat.card (rightMulAddHom (binaryQuotientPolynomial d polynomial)).range =
      2 ^ (2 ^ d - hasseValuation (2 ^ d) polynomial) := by
  letI : Fintype (QuotientRq 2 (2 ^ d)) :=
    PowerOfTwoQuadraticKDMStatistical.quotientPowerOfTwoRqFintype 1 d
  letI : DecidableEq (QuotientRq 2 (2 ^ d)) :=
    PowerOfTwoQuadraticKDMStatistical.quotientPowerOfTwoRqDecidableEq 1 d
  have hcard := RankOneHNFLossinessSparseRank.card_rightMulRange_eq_two_pow_rank
    (quotientPowerOfTwoAdicChain 1 d) (binaryQuotientPolynomial d polynomial)
  rw [quotientPowerOfTwoAdicChain_length,
    binaryQuotientPolynomial_chainValuation_eq_hasseValuation d hne hdegree] at hcard
  simpa using hcard

/-- Concrete multiplication-image cardinality for a distinct primitive ternary difference. -/
theorem card_primitiveDifference_binaryQuotient_range
    (d : ℕ) {left right : TernaryWord (2 ^ d)} (hne : left ≠ right) :
    Nat.card
        (rightMulAddHom
          (binaryQuotientPolynomial d
            (binaryWordPolynomial (primitiveDifference left right)))).range =
      2 ^ primitiveDifferenceRank d left right := by
  apply card_binaryQuotient_rightMulRange_eq_two_pow_hasseRank
  · exact (binaryWordPolynomial_eq_zero_iff _).not.mpr
      (primitiveDifference_ne_zero hne)
  · exact binaryWordPolynomial_natDegree_lt
      (pow_pos (by omega : 0 < 2) d) _

/-- The exact image-size statement can be exposed as `r` independent binary coordinates.
This is an abstract coordinate change on the image; a production implementation may replace it
with a certified nonsingular minor in order to identify concrete coefficient coordinates. -/
noncomputable def binaryQuotientRightMulRangeEquiv
    (d : ℕ) {polynomial : F2[X]} (hne : polynomial ≠ 0)
    (hdegree : polynomial.natDegree < 2 ^ d) :
    (rightMulAddHom (binaryQuotientPolynomial d polynomial)).range ≃
      (Fin (2 ^ d - hasseValuation (2 ^ d) polynomial) → F2) := by
  classical
  letI : Fintype (QuotientRq 2 (2 ^ d)) :=
    PowerOfTwoQuadraticKDMStatistical.quotientPowerOfTwoRqFintype 1 d
  letI : DecidableEq (QuotientRq 2 (2 ^ d)) :=
    PowerOfTwoQuadraticKDMStatistical.quotientPowerOfTwoRqDecidableEq 1 d
  apply Fintype.equivOfCardEq
  rw [← Nat.card_eq_fintype_card,
    card_binaryQuotient_rightMulRange_eq_two_pow_hasseRank d hne hdegree,
    Fintype.card_fun, Fintype.card_fin]
  norm_num

/-- Primitive ternary differences therefore have an image equivalent to exactly
`primitiveDifferenceRank` binary coordinates. -/
noncomputable def primitiveDifferenceBinaryRangeEquiv
    (d : ℕ) {left right : TernaryWord (2 ^ d)} (hne : left ≠ right) :
    (rightMulAddHom
      (binaryQuotientPolynomial d
        (binaryWordPolynomial (primitiveDifference left right)))).range ≃
      (Fin (primitiveDifferenceRank d left right) → F2) := by
  classical
  letI : Fintype (QuotientRq 2 (2 ^ d)) :=
    PowerOfTwoQuadraticKDMStatistical.quotientPowerOfTwoRqFintype 1 d
  letI : DecidableEq (QuotientRq 2 (2 ^ d)) :=
    PowerOfTwoQuadraticKDMStatistical.quotientPowerOfTwoRqDecidableEq 1 d
  apply Fintype.equivOfCardEq
  rw [← Nat.card_eq_fintype_card,
    card_primitiveDifference_binaryQuotient_range d hne,
    Fintype.card_fun, Fintype.card_fin]
  norm_num

/-! ## Joint two-adic-exponent/rank enumeration -/

/-- Exact number of ordered distinct pairs in one joint `(exponent, rank)` stratum. -/
def jointPairStatisticCount
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (exponent rank : Secret → Secret → ℕ) (e r : ℕ) : ℕ :=
  ((orderedDistinctPairs Secret).filter fun pair ↦
    exponent pair.1 pair.2 = e ∧ rank pair.1 pair.2 = r).card

/-- Average number of alternative secrets in one joint `(exponent, rank)` stratum. -/
def averageJointPairStatisticCount
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (exponent rank : Secret → Secret → ℕ) (e r : ℕ) : ℝ :=
  (jointPairStatisticCount exponent rank e r : ℝ) / Fintype.card Secret

/-- Every pair sum partitions exactly over two bounded statistics.  Both sides are finite
expressions, so this is also the correctness theorem for the direct executable histogram. -/
theorem sum_orderedDistinctPairs_eq_sum_jointPairStatisticCount
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (exponent rank : Secret → Secret → ℕ) (exponentBound rankBound : ℕ)
    (hexponent : ∀ left right, left ≠ right → exponent left right ≤ exponentBound)
    (hrank : ∀ left right, left ≠ right → rank left right ≤ rankBound)
    (value : ℕ → ℕ → ℝ) :
    (∑ pair ∈ orderedDistinctPairs Secret,
        value (exponent pair.1 pair.2) (rank pair.1 pair.2)) =
      ∑ e ∈ Finset.range (exponentBound + 1),
        ∑ r ∈ Finset.range (rankBound + 1),
          (jointPairStatisticCount exponent rank e r : ℝ) * value e r := by
  classical
  calc
    _ = ∑ pair ∈ orderedDistinctPairs Secret,
        ∑ e ∈ Finset.range (exponentBound + 1),
          ∑ r ∈ Finset.range (rankBound + 1),
            if exponent pair.1 pair.2 = e ∧ rank pair.1 pair.2 = r then
              value e r else 0 := by
      apply Finset.sum_congr rfl
      intro pair hpair
      have hne := (mem_orderedDistinctPairs_iff pair).mp hpair
      rw [Finset.sum_eq_single (exponent pair.1 pair.2)]
      · rw [Finset.sum_eq_single (rank pair.1 pair.2)]
        · simp
        · intro r _ hr
          simp [hr.symm]
        · intro hnot
          exact False.elim (hnot (Finset.mem_range.mpr
            (Nat.lt_succ_of_le (hrank pair.1 pair.2 hne))))
      · intro e _ he
        apply Finset.sum_eq_zero
        intro r _
        simp [he.symm]
      · intro hnot
        exact False.elim (hnot (Finset.mem_range.mpr
          (Nat.lt_succ_of_le (hexponent pair.1 pair.2 hne))))
    _ = ∑ e ∈ Finset.range (exponentBound + 1),
        ∑ r ∈ Finset.range (rankBound + 1),
          ∑ pair ∈ orderedDistinctPairs Secret,
            if exponent pair.1 pair.2 = e ∧ rank pair.1 pair.2 = r then
              value e r else 0 := by
      rw [Finset.sum_comm
        (s := orderedDistinctPairs Secret)
        (t := Finset.range (exponentBound + 1))]
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.sum_comm
        (s := orderedDistinctPairs Secret)
        (t := Finset.range (rankBound + 1))]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      apply Finset.sum_congr rfl
      intro r _
      rw [jointPairStatisticCount, ← Finset.sum_filter]
      simp

/-- Rank/exponent-stratified aggregation with an exponent-dependent one-coordinate overlap. -/
theorem average_pairKernel_le_jointEnumerator
    {Secret : Type} [Fintype Secret] [Nonempty Secret] [DecidableEq Secret]
    (exponent rank : Secret → Secret → ℕ) (exponentBound rankBound : ℕ)
    (hexponent : ∀ left right, left ≠ right → exponent left right ≤ exponentBound)
    (hrank : ∀ left right, left ≠ right → rank left right ≤ rankBound)
    (kernel : Secret → Secret → ℝ) (base : ℕ → ℝ)
    (hkernel : ∀ left right, left ≠ right →
      kernel left right ≤ base (exponent left right) ^ rank left right) :
    (∑ pair ∈ orderedDistinctPairs Secret, kernel pair.1 pair.2) /
        Fintype.card Secret ≤
      ∑ e ∈ Finset.range (exponentBound + 1),
        ∑ r ∈ Finset.range (rankBound + 1),
          averageJointPairStatisticCount exponent rank e r * base e ^ r := by
  calc
    (∑ pair ∈ orderedDistinctPairs Secret, kernel pair.1 pair.2) /
          Fintype.card Secret ≤
        (∑ pair ∈ orderedDistinctPairs Secret,
          base (exponent pair.1 pair.2) ^ rank pair.1 pair.2) /
          Fintype.card Secret := by
      apply div_le_div_of_nonneg_right
      · apply Finset.sum_le_sum
        intro pair hpair
        exact hkernel pair.1 pair.2 (mem_orderedDistinctPairs_iff pair |>.mp hpair)
      · positivity
    _ = _ := by
      rw [sum_orderedDistinctPairs_eq_sum_jointPairStatisticCount
        exponent rank exponentBound rankBound hexponent hrank
        (value := fun e r ↦ base e ^ r)]
      unfold averageJointPairStatisticCount
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro r _
      ring

/-- Number of pairs in exponent stratum `e` whose second statistic is at least `level`. -/
def jointCumulativePairStatisticCount
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (exponent statistic : Secret → Secret → ℕ) (e level : ℕ) : ℕ :=
  ((orderedDistinctPairs Secret).filter fun pair ↦
    exponent pair.1 pair.2 = e ∧ level ≤ statistic pair.1 pair.2).card

/-- Within a fixed exponent branch, exact statistic strata are adjacent cumulative differences. -/
theorem jointPairStatisticCount_eq_jointCumulative_sub_succ
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (exponent statistic : Secret → Secret → ℕ) (e level : ℕ) :
    jointPairStatisticCount exponent statistic e level =
      jointCumulativePairStatisticCount exponent statistic e level -
        jointCumulativePairStatisticCount exponent statistic e (level + 1) := by
  have hpartition :
      jointCumulativePairStatisticCount exponent statistic e level =
        jointPairStatisticCount exponent statistic e level +
          jointCumulativePairStatisticCount exponent statistic e (level + 1) := by
    rw [jointCumulativePairStatisticCount, jointPairStatisticCount,
      jointCumulativePairStatisticCount]
    rw [← Finset.card_union_of_disjoint]
    · congr 1
      ext pair
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hpair, hexponent, hle⟩
        rcases eq_or_lt_of_le hle with heq | hlt
        · exact Or.inl ⟨hpair, hexponent, heq.symm⟩
        · exact Or.inr ⟨hpair, hexponent, by omega⟩
      · rintro (⟨hpair, hexponent, heq⟩ | ⟨hpair, hexponent, hsucc⟩)
        · exact ⟨hpair, hexponent, by omega⟩
        · exact ⟨hpair, hexponent, by omega⟩
    · rw [Finset.disjoint_left]
      intro pair hexact hsucc
      simp only [Finset.mem_filter] at hexact hsucc
      omega
  omega

/-- Cumulative Hasse-syndrome count within a fixed exponent branch. -/
def jointSyndromeCumulativePairCount
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (exponent : Secret → Secret → ℕ)
    (difference : Secret → Secret → F2[X]) (e level : ℕ) : ℕ := by
  classical
  exact ((orderedDistinctPairs Secret).filter fun pair ↦
    exponent pair.1 pair.2 = e ∧
      syndromesZeroBelow (difference pair.1 pair.2) level).card

/-- In one exponent branch, cumulative Hasse valuation is exactly cumulative zero-syndrome
counting. -/
theorem jointCumulative_hasseValuation_eq_syndrome
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (exponent : Secret → Secret → ℕ)
    (length : ℕ) (difference : Secret → Secret → F2[X])
    (e level : ℕ) (hlevel : level ≤ length) :
    jointCumulativePairStatisticCount exponent
        (fun left right ↦ hasseValuation length (difference left right)) e level =
      jointSyndromeCumulativePairCount exponent difference e level := by
  unfold jointCumulativePairStatisticCount jointSyndromeCumulativePairCount
  apply congrArg Finset.card
  ext pair
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hpair, hexponent, hvaluation⟩
    exact ⟨hpair, hexponent,
      (le_hasseValuation_iff_syndromesZeroBelow
        length (difference pair.1 pair.2) hlevel).mp hvaluation⟩
  · rintro ⟨hpair, hexponent, hsyndrome⟩
    exact ⟨hpair, hexponent,
      (le_hasseValuation_iff_syndromesZeroBelow
        length (difference pair.1 pair.2) hlevel).mpr hsyndrome⟩

/-- Joint rank-`r` pairs are joint valuation-`length-r` pairs. -/
theorem jointPairStatisticCount_valuationRank
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (exponent : Secret → Secret → ℕ)
    (length : ℕ) (valuation : Secret → Secret → ℕ)
    (hvaluation : ∀ left right, valuation left right ≤ length)
    (e rank : ℕ) (hrank : rank ≤ length) :
    jointPairStatisticCount exponent (valuationRank length valuation) e rank =
      jointPairStatisticCount exponent valuation e (length - rank) := by
  unfold jointPairStatisticCount
  congr 1
  ext pair
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hpair, hexponent, heq⟩
    exact ⟨hpair, hexponent, by
      have hvaluationBound := hvaluation pair.1 pair.2
      unfold valuationRank at heq
      omega⟩
  · rintro ⟨hpair, hexponent, heq⟩
    exact ⟨hpair, hexponent, by
      have hvaluationBound := hvaluation pair.1 pair.2
      unfold valuationRank
      omega⟩

/-- Exact joint `(e,r)` counts are differences of two testable Hasse-prefix counts. -/
theorem exact_joint_hasseRank_count_eq_syndrome_count_sub_succ
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (exponent : Secret → Secret → ℕ)
    (length : ℕ) (difference : Secret → Secret → F2[X])
    (e rank : ℕ) (hrankPos : 0 < rank) (hrank : rank ≤ length) :
    jointPairStatisticCount exponent
        (valuationRank length
          (fun left right ↦ hasseValuation length (difference left right))) e rank =
      jointSyndromeCumulativePairCount exponent difference e (length - rank) -
        jointSyndromeCumulativePairCount exponent difference e (length - rank + 1) := by
  rw [jointPairStatisticCount_valuationRank exponent length _
      (fun left right ↦ hasseValuation_le length (difference left right))
      e rank hrank,
    jointPairStatisticCount_eq_jointCumulative_sub_succ,
    jointCumulative_hasseValuation_eq_syndrome exponent length difference
      e (length - rank) (by omega),
    jointCumulative_hasseValuation_eq_syndrome exponent length difference
      e (length - rank + 1) (by omega)]

/-! ### Fixed-weight ternary specialization -/

/-- Extracted two-adic exponent of an encoded fixed-weight ternary pair.  It is `1` precisely
when the supports agree, and `0` otherwise. -/
def encodedPrimitiveExponent
    (d weight : ℕ)
    (left right : EncodedFixedWeightTernarySecret (2 ^ d) weight) : ℕ :=
  primitiveDifferenceExponent
    (decodeFixedWeightTernary left) (decodeFixedWeightTernary right)

theorem encodedPrimitiveExponent_le_one
    (d weight : ℕ)
    (left right : EncodedFixedWeightTernarySecret (2 ^ d) weight) :
    encodedPrimitiveExponent d weight left right ≤ 1 := by
  unfold encodedPrimitiveExponent primitiveDifferenceExponent
  split_ifs <;> omega

/-- The exact fixed-weight ternary `(e,r)` table is given by adjacent branch-restricted Hasse
prefix counts. -/
theorem exact_encodedPrimitiveExponentRank_count_eq_syndrome_count_sub_succ
    (d weight e rank : ℕ) (hrankPos : 0 < rank) (hrank : rank ≤ 2 ^ d) :
    jointPairStatisticCount
        (encodedPrimitiveExponent d weight) (encodedPrimitiveRank d weight) e rank =
      jointSyndromeCumulativePairCount
          (encodedPrimitiveExponent d weight)
          (encodedPrimitivePolynomialDifference d weight) e (2 ^ d - rank) -
        jointSyndromeCumulativePairCount
          (encodedPrimitiveExponent d weight)
          (encodedPrimitivePolynomialDifference d weight) e (2 ^ d - rank + 1) := by
  change jointPairStatisticCount (encodedPrimitiveExponent d weight)
      (valuationRank (2 ^ d)
        (fun left right ↦ hasseValuation (2 ^ d)
          (encodedPrimitivePolynomialDifference d weight left right))) e rank = _
  exact exact_joint_hasseRank_count_eq_syndrome_count_sub_succ
    (encodedPrimitiveExponent d weight) (2 ^ d)
    (encodedPrimitivePolynomialDifference d weight) e rank hrankPos hrank

/-- Complete finite-support aggregation for fixed-weight ternary secrets, retaining both the
two-adic exponent and the actual repeated-root rank of every difference. -/
theorem average_encodedPrimitiveKernel_le_jointEnumerator
    (d weight : ℕ)
    [Nonempty (EncodedFixedWeightTernarySecret (2 ^ d) weight)]
    (kernel : EncodedFixedWeightTernarySecret (2 ^ d) weight →
      EncodedFixedWeightTernarySecret (2 ^ d) weight → ℝ)
    (base : ℕ → ℝ)
    (hkernel : ∀ left right, left ≠ right →
      kernel left right ≤
        base (encodedPrimitiveExponent d weight left right) ^
          encodedPrimitiveRank d weight left right) :
    (∑ pair ∈ orderedDistinctPairs
        (EncodedFixedWeightTernarySecret (2 ^ d) weight),
        kernel pair.1 pair.2) /
        Fintype.card (EncodedFixedWeightTernarySecret (2 ^ d) weight) ≤
      ∑ e ∈ Finset.range 2,
        ∑ rank ∈ Finset.range (2 ^ d + 1),
          averageJointPairStatisticCount
              (encodedPrimitiveExponent d weight) (encodedPrimitiveRank d weight) e rank *
            base e ^ rank := by
  apply average_pairKernel_le_jointEnumerator
  · intro left right _
    exact encodedPrimitiveExponent_le_one d weight left right
  · intro left right _
    exact primitiveDifferenceRank_le_length d
      (decodeFixedWeightTernary left) (decodeFixedWeightTernary right)
  · exact hkernel

/-! ### Executable joint histogram -/

end

/-- Computable extracted two-adic exponent of an encoded fixed-weight ternary pair. -/
def encodedPrimitiveExponentExecutable
    (d weight : ℕ)
    (left right : EncodedFixedWeightTernarySecret (2 ^ d) weight) : ℕ :=
  if left.1.1 = right.1.1 then 1 else 0

/-- Compute the primitive binary difference directly from support and sign bits, without
constructing a classical polynomial. -/
def encodedPrimitiveWordExecutable
    (d weight : ℕ)
    (left right : EncodedFixedWeightTernarySecret (2 ^ d) weight)
    (index : Fin (2 ^ d)) : F2 :=
  if hsupport : left.1.1 = right.1.1 then
    if hleft : index ∈ left.1.1 then
      if left.2 ⟨index, hleft⟩ = right.2 ⟨index, hsupport ▸ hleft⟩ then 0 else 1
    else 0
  else if (index ∈ left.1.1) = (index ∈ right.1.1) then 0 else 1

/-- Coefficient formula for one Hasse syndrome, implemented directly on a finite word. -/
def binaryWordHasseSyndromeExecutable
    {length : ℕ} (word : Fin length → F2) (j : ℕ) : F2 :=
  ∑ index, (index.val.choose j : F2) * word index

/-- Boolean test for vanishing of a finite prefix of directly computed syndromes. -/
def binaryWordSyndromesZeroBelowBool
    {length : ℕ} (word : Fin length → F2) (level : ℕ) : Bool :=
  (List.range level).all fun j ↦
    decide (binaryWordHasseSyndromeExecutable word j = 0)

/-- VM-executable truncated Hasse valuation of a fixed-length binary word. -/
def binaryWordHasseValuationExecutable
    {length : ℕ} (word : Fin length → F2) : ℕ :=
  Nat.findGreatest
    (fun level ↦ binaryWordSyndromesZeroBelowBool word level = true) length

/-- VM-executable primitive rank for an encoded fixed-weight ternary pair. -/
def encodedPrimitiveRankExecutable
    (d weight : ℕ)
    (left right : EncodedFixedWeightTernarySecret (2 ^ d) weight) : ℕ :=
  2 ^ d - binaryWordHasseValuationExecutable
    (encodedPrimitiveWordExecutable d weight left right)

/-- Direct executable `(e,r)` histogram for the fixed-weight ternary support.  This is suitable
for certified small-instance checks; a recurrence/DP is still needed at TFHEpp-scale. -/
def encodedPrimitiveExponentRankCountExecutable
    (d weight e rank : ℕ) : ℕ :=
  let Secret := EncodedFixedWeightTernarySecret (2 ^ d) weight
  (((Finset.univ : Finset Secret).product Finset.univ).filter fun pair ↦
    pair.1 ≠ pair.2 ∧
      encodedPrimitiveExponentExecutable d weight pair.1 pair.2 = e ∧
      encodedPrimitiveRankExecutable d weight pair.1 pair.2 = rank).card

noncomputable section

theorem encodedPrimitiveExponentExecutable_eq
    (d weight : ℕ)
    (left right : EncodedFixedWeightTernarySecret (2 ^ d) weight) :
    encodedPrimitiveExponentExecutable d weight left right =
      encodedPrimitiveExponent d weight left right := by
  unfold encodedPrimitiveExponentExecutable encodedPrimitiveExponent
    primitiveDifferenceExponent
  rw [wordSupport_decodeFixedWeightTernary, wordSupport_decodeFixedWeightTernary]

theorem ternary_toF2_signedDigit (sign : Fin 2) :
    TernaryDigit.toF2 (signedDigit sign) = 1 := by
  fin_cases sign <;> rfl

/-- The direct support/sign algorithm returns the same primitive word as the mathematical
ternary-difference definition. -/
theorem encodedPrimitiveWordExecutable_eq
    (d weight : ℕ)
    (left right : EncodedFixedWeightTernarySecret (2 ^ d) weight) :
    encodedPrimitiveWordExecutable d weight left right =
      primitiveDifference (decodeFixedWeightTernary left)
        (decodeFixedWeightTernary right) := by
  funext index
  unfold encodedPrimitiveWordExecutable primitiveDifference
  rw [wordSupport_decodeFixedWeightTernary, wordSupport_decodeFixedWeightTernary]
  by_cases hsupport : left.1.1 = right.1.1
  · simp only [if_pos hsupport, halvedSignDifference]
    by_cases hleft : index ∈ left.1.1
    · have hright : index ∈ right.1.1 := hsupport ▸ hleft
      simp only [hleft, dite_true]
      generalize hleftSign : left.2 ⟨index, hleft⟩ = leftSign
      generalize hrightSign : right.2 ⟨index, hright⟩ = rightSign
      fin_cases leftSign <;> fin_cases rightSign <;>
        simp_all [decodeFixedWeightTernary, signedDigit]
    · have hright : index ∉ right.1.1 := by
        simpa [← hsupport] using hleft
      simp [hleft, hright, decodeFixedWeightTernary]
  · simp only [if_neg hsupport, parityDifference]
    have hsupportSubtype : left.1 ≠ right.1 := by
      intro heq
      exact hsupport (congrArg Subtype.val heq)
    by_cases hleft : index ∈ left.1.1 <;>
      by_cases hright : index ∈ right.1.1
    · simp [hleft, hright, hsupportSubtype, decodeFixedWeightTernary,
        ternary_toF2_signedDigit]
    · simp [hleft, hright, hsupportSubtype, decodeFixedWeightTernary,
        ternary_toF2_signedDigit]
    · simp [hleft, hright, hsupportSubtype, decodeFixedWeightTernary,
        ternary_toF2_signedDigit]
    · simp [hleft, hright, hsupportSubtype, decodeFixedWeightTernary]

/-- Direct coefficient summation agrees with the polynomial Hasse derivative definition. -/
theorem binaryWordHasseSyndromeExecutable_eq
    (length j : ℕ) (word : Fin length → F2) :
    binaryWordHasseSyndromeExecutable word j =
      hasseSyndrome (binaryWordPolynomial word) j := by
  simp only [binaryWordHasseSyndromeExecutable, hasseSyndrome,
    binaryWordPolynomial]
  rw [map_sum, Polynomial.eval_finsetSum]
  simp [Polynomial.hasseDeriv_monomial]

theorem binaryWordSyndromesZeroBelowBool_eq_true_iff
    (length level : ℕ) (word : Fin length → F2) :
    binaryWordSyndromesZeroBelowBool word level = true ↔
      syndromesZeroBelow (binaryWordPolynomial word) level := by
  rw [binaryWordSyndromesZeroBelowBool, List.all_eq_true]
  simp only [decide_eq_true_eq, List.mem_range,
    binaryWordHasseSyndromeExecutable_eq]
  rfl

/-- The executable word scanner computes exactly the mathematical Hasse valuation. -/
theorem binaryWordHasseValuationExecutable_eq
    (length : ℕ) (word : Fin length → F2) :
    binaryWordHasseValuationExecutable word =
      hasseValuation length (binaryWordPolynomial word) := by
  classical
  unfold binaryWordHasseValuationExecutable hasseValuation
  have aux : ∀ bound : ℕ,
      Nat.findGreatest
          (fun level ↦ binaryWordSyndromesZeroBelowBool word level = true) bound =
        Nat.findGreatest
          (syndromesZeroBelow (binaryWordPolynomial word)) bound := by
    intro bound
    induction bound with
    | zero => rfl
    | succ bound ih =>
        simp only [Nat.findGreatest_succ]
        by_cases hzero : binaryWordSyndromesZeroBelowBool word (bound + 1) = true
        · have hzero' :=
            (binaryWordSyndromesZeroBelowBool_eq_true_iff
              length (bound + 1) word).mp hzero
          simp [hzero, hzero']
        · have hzero' :
              ¬ syndromesZeroBelow (binaryWordPolynomial word) (bound + 1) := by
            intro h
            exact hzero
              ((binaryWordSyndromesZeroBelowBool_eq_true_iff
                length (bound + 1) word).mpr h)
          simp [hzero, hzero', ih]
  exact aux length

theorem encodedPrimitiveRankExecutable_eq
    (d weight : ℕ)
    (left right : EncodedFixedWeightTernarySecret (2 ^ d) weight) :
    encodedPrimitiveRankExecutable d weight left right =
      encodedPrimitiveRank d weight left right := by
  unfold encodedPrimitiveRankExecutable encodedPrimitiveRank
    primitiveDifferenceRank primitiveDifferenceValuation
  rw [binaryWordHasseValuationExecutable_eq,
    encodedPrimitiveWordExecutable_eq]

/-- The executable histogram agrees cell-by-cell with the exact mathematical enumerator. -/
theorem encodedPrimitiveExponentRankCountExecutable_eq
    (d weight e rank : ℕ) :
    encodedPrimitiveExponentRankCountExecutable d weight e rank =
      jointPairStatisticCount
        (encodedPrimitiveExponent d weight) (encodedPrimitiveRank d weight) e rank := by
  unfold encodedPrimitiveExponentRankCountExecutable jointPairStatisticCount
    orderedDistinctPairs
  apply congrArg Finset.card
  ext pair
  simp only [Finset.mem_filter]
  rw [encodedPrimitiveExponentExecutable_eq, encodedPrimitiveRankExecutable_eq]
  tauto

/-- A kernel-decided sanity check: for degree two and weight one, the twelve ordered distinct
pairs split as eight `(e=0,r=1)` pairs and four `(e=1,r=2)` pairs. -/
theorem encodedPrimitiveExponentRankCountExecutable_degreeTwo_weightOne :
    encodedPrimitiveExponentRankCountExecutable 1 1 0 1 = 8 ∧
    encodedPrimitiveExponentRankCountExecutable 1 1 0 2 = 0 ∧
    encodedPrimitiveExponentRankCountExecutable 1 1 1 1 = 0 ∧
    encodedPrimitiveExponentRankCountExecutable 1 1 1 2 = 4 := by
  decide

/-! ## Finite-support local overlap -/

/-- Probability mass of an event under the uniform distribution on a finite type, written as
an exact finite cardinality ratio. -/
def finiteUniformEventMass
    {Sample : Type} [Fintype Sample] (event : Finset Sample) : ℝ :=
  (event.card : ℝ) / Fintype.card Sample

/-- The finite set of vectors whose coordinates lie in their respective allowed sets. -/
noncomputable def coordinateCompatibilityBox
    {Index Alphabet : Type} [Fintype Index] [DecidableEq Index] [DecidableEq Alphabet]
    (allowed : Index → Finset Alphabet) : Finset (Index → Alphabet) :=
  Fintype.piFinset allowed

/-- Exact cardinality of a coordinatewise compatibility box. -/
theorem card_coordinateCompatibilityBox
    {Index Alphabet : Type} [Fintype Index] [DecidableEq Index]
    [Fintype Alphabet] [DecidableEq Alphabet]
    (allowed : Index → Finset Alphabet) :
    (coordinateCompatibilityBox allowed).card =
        ∏ index, (allowed index).card := by
  classical
  simp [coordinateCompatibilityBox]

/-- If each selected coordinate admits at most `width` compatible residues, the whole
`r`-coordinate compatibility box has at most `width^r` elements. -/
theorem card_coordinateCompatibilityBox_le_pow
    {Index Alphabet : Type} [Fintype Index] [DecidableEq Index]
    [Fintype Alphabet] [DecidableEq Alphabet]
    (allowed : Index → Finset Alphabet) (width : ℕ)
    (hwidth : ∀ index, (allowed index).card ≤ width) :
    (coordinateCompatibilityBox allowed).card ≤
        width ^ Fintype.card Index := by
  rw [card_coordinateCompatibilityBox]
  calc
    ∏ index : Index, (allowed index).card ≤ ∏ _index : Index, width := by
      apply Finset.prod_le_prod
      · intro index _
        exact Nat.zero_le _
      · intro index _
        exact hwidth index
    _ = width ^ Fintype.card Index := by simp

/-- A completely finite proof of the local overlap factor.  No Gaussian estimate is needed:
uniform selected residues hit a coordinate box of width at most `w` with probability at most
`(w / |A|)^r`. -/
theorem finiteUniform_coordinateCompatibilityMass_le_pow
    {Index Alphabet : Type} [Fintype Index] [DecidableEq Index]
    [Fintype Alphabet] [Nonempty Alphabet] [DecidableEq Alphabet]
    (allowed : Index → Finset Alphabet) (width : ℕ)
    (hwidth : ∀ index, (allowed index).card ≤ width) :
    finiteUniformEventMass (coordinateCompatibilityBox allowed) ≤
      ((width : ℝ) / Fintype.card Alphabet) ^ Fintype.card Index := by
  classical
  unfold finiteUniformEventMass
  rw [Fintype.card_fun]
  simp only [Nat.cast_pow]
  have hcard := card_coordinateCompatibilityBox_le_pow allowed width hwidth
  have hcardReal :
      ((coordinateCompatibilityBox allowed).card : ℝ) ≤
        (width : ℝ) ^ Fintype.card Index := by
    exact_mod_cast hcard
  calc
    _ ≤ (width : ℝ) ^ Fintype.card Index /
          Fintype.card Alphabet ^ Fintype.card Index := by
      exact (div_le_div_iff_of_pos_right
        (show 0 < (Fintype.card Alphabet : ℝ) ^ Fintype.card Index by
          positivity)).2 hcardReal
    _ = ((width : ℝ) / Fintype.card Alphabet) ^ Fintype.card Index := by
      rw [div_pow]

/-- End-to-end finite-support overlap bound: coordinate box counting supplies every local
`zeta_e^r` hypothesis required by the exact joint enumerator. -/
theorem average_finiteCoordinateOverlap_le_jointEnumerator
    {Secret Alphabet : Type}
    [Fintype Secret] [Nonempty Secret] [DecidableEq Secret]
    [Fintype Alphabet] [Nonempty Alphabet] [DecidableEq Alphabet]
    (exponent rank : Secret → Secret → ℕ) (exponentBound rankBound : ℕ)
    (hexponent : ∀ left right, left ≠ right → exponent left right ≤ exponentBound)
    (hrank : ∀ left right, left ≠ right → rank left right ≤ rankBound)
    (allowed : ∀ left right, Fin (rank left right) → Finset Alphabet)
    (width : ℕ → ℕ)
    (hwidth : ∀ left right index,
      (allowed left right index).card ≤ width (exponent left right)) :
    (∑ pair ∈ orderedDistinctPairs Secret,
        finiteUniformEventMass
          (coordinateCompatibilityBox (allowed pair.1 pair.2))) /
        Fintype.card Secret ≤
      ∑ e ∈ Finset.range (exponentBound + 1),
        ∑ r ∈ Finset.range (rankBound + 1),
          averageJointPairStatisticCount exponent rank e r *
            (((width e : ℝ) / Fintype.card Alphabet) ^ r) := by
  apply average_pairKernel_le_jointEnumerator
      exponent rank exponentBound rankBound hexponent hrank
      (fun left right ↦ finiteUniformEventMass
        (coordinateCompatibilityBox (allowed left right)))
      (fun e ↦ (width e : ℝ) / Fintype.card Alphabet)
  intro left right _
  simpa using finiteUniform_coordinateCompatibilityMass_le_pow
    (allowed left right) (width (exponent left right))
    (hwidth left right)

/-! ## Rank-aware ideal randomization and its cokernel boundary -/

/-- In a certified binary chain ring, the ambient-to-principal-image cardinality ratio is
exactly `2^valuation`. -/
theorem principalCokernelRatio_eq_two_pow_valuation
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    (chain : FiniteAdicChain R) (value : R) :
    (Nat.card R : ℝ) / Nat.card (rightMulAddHom value).range =
      (2 : ℝ) ^ chain.valuation value := by
  rw [chain.card_ring, card_rightMulRange_eq_two_pow_rank chain value]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  apply (div_eq_iff (by positivity :
    (2 : ℝ) ^ (chain.length - chain.valuation value) ≠ 0)).2
  rw [← pow_add]
  congr 1
  have hvaluationLe := chain.valuation_le value
  omega

/-- The additive cokernel of multiplication has exactly `2^valuation` elements. -/
theorem card_principalCokernel_eq_two_pow_valuation
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    (chain : FiniteAdicChain R) (value : R) :
    Nat.card (R ⧸ (rightMulAddHom value).range) =
      2 ^ chain.valuation value := by
  have hlagrange :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
      (rightMulAddHom value).range
  rw [chain.card_ring, card_rightMulRange_eq_two_pow_rank chain value] at hlagrange
  apply Nat.mul_right_cancel
    (pow_pos (by omega : 0 < 2) (chain.length - chain.valuation value))
  calc
    Nat.card (R ⧸ (rightMulAddHom value).range) *
          2 ^ (chain.length - chain.valuation value) =
        2 ^ chain.length := hlagrange.symm
    _ = 2 ^ chain.valuation value *
          2 ^ (chain.length - chain.valuation value) := by
      rw [← pow_add]
      congr 1
      have hvaluationLe := chain.valuation_le value
      omega

/-- Positive valuation makes the principal multiplication image strictly smaller than the
ambient ring. -/
theorem card_rightMulRange_lt_of_valuation_pos
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    (chain : FiniteAdicChain R) (value : R)
    (hvaluation : 0 < chain.valuation value) :
    Nat.card (rightMulAddHom value).range < Nat.card R := by
  rw [card_rightMulRange_eq_two_pow_rank chain value, chain.card_ring]
  apply Nat.pow_lt_pow_right (by omega : 1 < 2)
  have hvaluationLe := chain.valuation_le value
  omega

/-- Consequently no deterministic reindexing can turn a uniform point of a proper principal
image into a full-ring uniform point: the two carriers have different cardinalities. -/
theorem no_bijective_principalRange_to_ambient_of_valuation_pos
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    (chain : FiniteAdicChain R) (value : R)
    (hvaluation : 0 < chain.valuation value) :
    ¬ ∃ reindex : (rightMulAddHom value).range → R,
        Function.Bijective reindex := by
  intro hexists
  obtain ⟨reindex, hreindex⟩ := hexists
  have hcard := Nat.card_congr (Equiv.ofBijective reindex hreindex)
  exact (Nat.ne_of_lt
    (card_rightMulRange_lt_of_valuation_pos chain value hvaluation)) hcard

/-- In particular, multiplication itself is not onto when its valuation is positive. -/
theorem rightMul_not_surjective_of_valuation_pos
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    (chain : FiniteAdicChain R) (value : R)
    (hvaluation : 0 < chain.valuation value) :
    ¬ Function.Surjective (rightMulAddHom value) := by
  intro hsurjective
  have hrange : (rightMulAddHom value).range = ⊤ :=
    AddMonoidHom.range_eq_top.mpr hsurjective
  have hcard : Nat.card (rightMulAddHom value).range = Nat.card R := by
    rw [hrange]
    simp
  exact (Nat.ne_of_lt
    (card_rightMulRange_lt_of_valuation_pos chain value hvaluation)) hcard

/-- Lagrange's theorem gives a (noncanonical) carrier equivalence between an image coordinate,
an independent cokernel coordinate, and the full ambient ring. -/
noncomputable def principalRangeTimesCokernelEquiv
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] (value : R) :
    (rightMulAddHom value).range ×
        (R ⧸ (rightMulAddHom value).range) ≃ R := by
  classical
  apply Fintype.equivOfCardEq
  rw [Fintype.card_prod]
  simp only [← Nat.card_eq_fintype_card]
  simpa only [Nat.mul_comm] using
    (AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
      (rightMulAddHom value).range).symm

/-- For the literal binary negacyclic quotient, the missing cokernel has exactly `2^v`
elements, where `v` is the Hasse valuation of the multiplier. -/
theorem card_binaryQuotient_principalCokernel_eq_two_pow_hasseValuation
    (d : ℕ) {polynomial : F2[X]} (hne : polynomial ≠ 0)
    (hdegree : polynomial.natDegree < 2 ^ d) :
    Nat.card
        (QuotientRq 2 (2 ^ d) ⧸
          (rightMulAddHom (binaryQuotientPolynomial d polynomial)).range) =
      2 ^ hasseValuation (2 ^ d) polynomial := by
  classical
  letI : Fintype (QuotientRq 2 (2 ^ d)) :=
    PowerOfTwoQuadraticKDMStatistical.quotientPowerOfTwoRqFintype 1 d
  letI : DecidableEq (QuotientRq 2 (2 ^ d)) :=
    PowerOfTwoQuadraticKDMStatistical.quotientPowerOfTwoRqDecidableEq 1 d
  have hcard := card_principalCokernel_eq_two_pow_valuation
    (quotientPowerOfTwoAdicChain 1 d)
    (binaryQuotientPolynomial d polynomial)
  rw [binaryQuotientPolynomial_chainValuation_eq_hasseValuation
    d hne hdegree] at hcard
  exact hcard

/-- A positive Hasse valuation is therefore the exact obstruction to full-ring randomization by
the binary multiplication map. -/
theorem binaryQuotient_rightMul_not_surjective_of_hasseValuation_pos
    (d : ℕ) {polynomial : F2[X]} (hne : polynomial ≠ 0)
    (hdegree : polynomial.natDegree < 2 ^ d)
    (hvaluation : 0 < hasseValuation (2 ^ d) polynomial) :
    ¬ Function.Surjective
      (rightMulAddHom (binaryQuotientPolynomial d polynomial)) := by
  classical
  letI : Fintype (QuotientRq 2 (2 ^ d)) :=
    PowerOfTwoQuadraticKDMStatistical.quotientPowerOfTwoRqFintype 1 d
  letI : DecidableEq (QuotientRq 2 (2 ^ d)) :=
    PowerOfTwoQuadraticKDMStatistical.quotientPowerOfTwoRqDecidableEq 1 d
  apply rightMul_not_surjective_of_valuation_pos
    (quotientPowerOfTwoAdicChain 1 d)
  rwa [binaryQuotientPolynomial_chainValuation_eq_hasseValuation
    d hne hdegree]

/-! ### Exact uniformity on the image -/

/-- A surjective additive map sends a uniform finite-group sample to a uniform sample.  This
local copy keeps the rank-aware RLWE result independent of TFHE's selector module. -/
theorem evalDist_map_surjective_addHom_uniform
    {Domain Codomain : Type}
    [AddGroup Domain] [Fintype Domain] [SampleableType Domain]
    [AddGroup Codomain] [Fintype Codomain] [DecidableEq Codomain]
    [SampleableType Codomain]
    (transform : Domain →+ Codomain) (hsurjective : Function.Surjective transform) :
    evalDist (transform <$> ($ᵗ Domain)) = evalDist ($ᵗ Codomain) := by
  classical
  apply evalDist_ext
  intro output
  rw [probOutput_uniformSample Codomain output,
    probOutput_map_eq_sum_fintype_ite]
  simp only [probOutput_uniformSample Domain]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hfiber :
      (Finset.univ.filter fun input : Domain ↦ output = transform input).card =
        (Finset.univ.filter fun input : Domain ↦ transform input = 0).card := by
    rw [show (Finset.univ.filter fun input : Domain ↦ output = transform input) =
        Finset.univ.filter fun input : Domain ↦ transform input = output by
      ext input
      simp [eq_comm]]
    exact AddMonoidHom.card_fiber_eq_of_mem_range transform
      (Set.mem_range.2 (hsurjective output)) (Set.mem_range.2 (hsurjective 0))
  rw [hfiber]
  let zeroFiber :=
    (Finset.univ.filter fun input : Domain ↦ transform input = 0).card
  have hzeroFiberPos : 0 < zeroFiber := by
    apply Finset.card_pos.mpr
    exact ⟨0, by simp⟩
  have hcardNat : zeroFiber * Fintype.card Codomain = Fintype.card Domain := by
    exact
      FormalProof4FHE.FiniteSurjectiveFiber.zeroFiberCard_mul_card_eq_card_of_surjective
        transform hsurjective
  have hcard :
      (zeroFiber : ℝ≥0∞) * (Fintype.card Codomain : ℝ≥0∞) =
        (Fintype.card Domain : ℝ≥0∞) := by
    exact_mod_cast hcardNat
  change (zeroFiber : ℝ≥0∞) * (Fintype.card Domain : ℝ≥0∞)⁻¹ = _
  rw [← hcard]
  have hinv :
      ((zeroFiber : ℝ≥0∞) * (Fintype.card Codomain : ℝ≥0∞))⁻¹ =
        (zeroFiber : ℝ≥0∞)⁻¹ * (Fintype.card Codomain : ℝ≥0∞)⁻¹ :=
    ENNReal.mul_inv
      (Or.inr (ENNReal.natCast_ne_top (Fintype.card Codomain)))
      (Or.inl (ENNReal.natCast_ne_top zeroFiber))
  rw [hinv]
  rw [← mul_assoc, ENNReal.mul_inv_cancel
    (Nat.cast_ne_zero.mpr hzeroFiberPos.ne')
    (ENNReal.natCast_ne_top zeroFiber), one_mul]

/-- Multiplying a uniform ring element by `difference` is exactly uniform on the principal
image `difference * R`, even when it is not uniform on the ambient ring. -/
theorem rightMul_uniform_on_principalRange
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (difference : R) [SampleableType (rightMulAddHom difference).range] :
    evalDist
        ((rightMulAddHom difference).rangeRestrict <$> ($ᵗ R)) =
      evalDist ($ᵗ (rightMulAddHom difference).range) :=
  evalDist_map_surjective_addHom_uniform
    (rightMulAddHom difference).rangeRestrict
    (AddMonoidHom.rangeRestrict_surjective (rightMulAddHom difference))

/-- Translation by any fixed element of the principal image preserves this exact ideal-uniform
distribution.  This is the correct wrong-candidate statement after conditioning on the two
secrets and their quadratic shift. -/
theorem rightMul_affine_uniform_on_principalRange
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (difference : R) [SampleableType (rightMulAddHom difference).range]
    (translation : (rightMulAddHom difference).range) :
    evalDist
        ((fun input ↦
            (rightMulAddHom difference).rangeRestrict input + translation) <$>
          ($ᵗ R)) =
      evalDist ($ᵗ (rightMulAddHom difference).range) := by
  have huniform := rightMul_uniform_on_principalRange difference
  calc
    evalDist
        ((fun input ↦
            (rightMulAddHom difference).rangeRestrict input + translation) <$>
          ($ᵗ R)) =
      evalDist
        ((fun output ↦ output + translation) <$>
          ((rightMulAddHom difference).rangeRestrict <$> ($ᵗ R))) := by
        simp only [Functor.map_map]
    _ = evalDist
        ((fun output ↦ output + translation) <$>
          ($ᵗ (rightMulAddHom difference).range)) :=
      evalDist_map_eq_of_evalDist_eq huniform (fun output ↦ output + translation)
    _ = evalDist ($ᵗ (rightMulAddHom difference).range) :=
      evalDist_add_right_uniform
        (α := (rightMulAddHom difference).range) translation

/-- Supplying an independent uniform cokernel coordinate is cardinality-sufficient to complete
an ideal-uniform point to a full-ring uniform point.  The equivalence is deliberately
noncanonical: constructing a completion that is public and independent of the hidden
difference is the remaining search-to-decision obligation. -/
theorem principalRangeTimesCokernel_uniform
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (value : R)
    [SampleableType (rightMulAddHom value).range]
    [SampleableType (R ⧸ (rightMulAddHom value).range)] :
    evalDist
        (principalRangeTimesCokernelEquiv value <$>
          ($ᵗ ((rightMulAddHom value).range ×
            (R ⧸ (rightMulAddHom value).range)))) =
      evalDist ($ᵗ R) :=
  evalDist_map_bijective_uniform_cross
    (α := (rightMulAddHom value).range ×
      (R ⧸ (rightMulAddHom value).range)) (β := R)
    (principalRangeTimesCokernelEquiv value)
    (principalRangeTimesCokernelEquiv value).bijective

/-- A single fixed-size exact cokernel filler can serve two differences only if their chain
valuations agree.  Thus varying Hasse depths cannot be hidden by one unconditioned exact filler
without padding or additional randomization. -/
theorem fixedCokernelCard_forces_equal_valuation
    {R Filler : Type} [CommRing R] [Fintype R] [DecidableEq R] [Finite Filler]
    (chain : FiniteAdicChain R) (left right : R)
    (hleft : Nat.card Filler = 2 ^ chain.valuation left)
    (hright : Nat.card Filler = 2 ^ chain.valuation right) :
    chain.valuation left = chain.valuation right := by
  apply Nat.pow_right_injective (by omega : 2 ≤ 2)
  exact hleft.symm.trans hright

/-- Contrapositive form of the preceding boundary: distinct rank strata rule out an exact
common filler cardinality. -/
theorem no_fixedCokernelCard_of_distinct_valuations
    {R Filler : Type} [CommRing R] [Fintype R] [DecidableEq R] [Finite Filler]
    (chain : FiniteAdicChain R) (left right : R)
    (hdifferent : chain.valuation left ≠ chain.valuation right) :
    ¬ (Nat.card Filler = 2 ^ chain.valuation left ∧
      Nat.card Filler = 2 ^ chain.valuation right) := by
  rintro ⟨hleft, hright⟩
  exact hdifferent
    (fixedCokernelCard_forces_equal_valuation chain left right hleft hright)

end

end FormalProof4FHE.RLWE.RankOneHNFLossinessSparseRankChannel
