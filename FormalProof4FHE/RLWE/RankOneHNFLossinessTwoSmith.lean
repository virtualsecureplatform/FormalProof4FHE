/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.RankOneHNFLossinessSparseRankChannel
import FormalProof4FHE.Probability.FiniteRowConvolution
import Mathlib.LinearAlgebra.Matrix.Block

/-!
# The two-level 2-primary profile of sparse RLWE multiplication

This module formalizes the basis-free content of `sketch/twosmith.md`.  In the literal ring

`(ZMod (2^K))[X] / (X^(2^d) + 1)`,

let `pi = 1 - X`.  If a primitive lift `h` has nonzero binary reduction of Hasse depth `v`, then
`h` is a unit times `pi^v`.  The cyclotomic identity shows that `2` is a unit times `pi^n`, where
`n = 2^d`.  Consequently `2^e h` is a unit times `pi^(e*n+v)`.  This gives the exact image size

`2^((K-e)*n-v) = 2^((K-e)*(n-v) + (K-e-1)*v)`.

These are precisely the image and cokernel cardinalities of the two-primary Smith profile with
`n-v` entries `2^e` and `v` entries `2^(e+1)`.  The proof never applies a Smith change of basis to
the error distribution.  Later sections record the low-norm Hasse information set, its weight
enumerator bound, the resulting two-level local-factor aggregation, and an invariant finite
quotient-character formula for correlated errors.
-/

open BigOperators

namespace FormalProof4FHE.RLWE.RankOneHNFLossinessTwoSmith

open Polynomial
open PowerOfTwoQuadraticKDMStatistical
open RankOneHNFLossinessSparseRank
open RankOneHNFLossinessSparseRankChannel
open FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm
open FormalProof4FHE.TFHE.Native.PowerOfTwoLocalRing

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Unit factors do not change a principal multiplication image -/

/-- Multiplying a generator by a unit does not change its principal multiplication image. -/
theorem rightMulRange_mul_isUnit
    {R : Type} [CommRing R] (value unitFactor : R) (hunit : IsUnit unitFactor) :
    (rightMulAddHom (value * unitFactor)).range =
      (rightMulAddHom value).range := by
  obtain ⟨unit, rfl⟩ := hunit
  ext target
  constructor
  · rintro ⟨multiplier, rfl⟩
    refine ⟨multiplier * (unit : R), ?_⟩
    simp only [rightMulAddHom_apply]
    ring
  · rintro ⟨multiplier, rfl⟩
    refine ⟨multiplier * (↑(unit⁻¹) : R), ?_⟩
    simp only [rightMulAddHom_apply]
    calc
      multiplier * ↑unit⁻¹ * (value * ↑unit) =
          multiplier * value * (↑unit⁻¹ * ↑unit) := by ring
      _ = multiplier * value := by
        rw [← Units.val_mul]
        simp

/-- Left placement of the unit-factor version. -/
theorem rightMulRange_isUnit_mul
    {R : Type} [CommRing R] (unitFactor value : R) (hunit : IsUnit unitFactor) :
    (rightMulAddHom (unitFactor * value)).range =
      (rightMulAddHom value).range := by
  rw [mul_comm]
  exact rightMulRange_mul_isUnit value unitFactor hunit

/-- A displayed unit-times-uniformizer factorization determines the exact chain layer. -/
theorem rightMulRange_eq_uniformizerPower_of_factorization
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    (chain : FiniteAdicChain R) (value factor : R) (level : ℕ)
    (hvalue : value = factor * chain.uniformizer ^ level)
    (hfactor : IsUnit factor) :
    (rightMulAddHom value).range =
      (rightMulAddHom (chain.uniformizer ^ level)).range := by
  rw [hvalue]
  exact rightMulRange_isUnit_mul factor (chain.uniformizer ^ level) hfactor

/-- Hence a factorization at a level within the chain gives the exact image cardinality. -/
theorem card_rightMulRange_eq_two_pow_sub_of_factorization
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    (chain : FiniteAdicChain R) (value factor : R) (level : ℕ)
    (hlevel : level ≤ chain.length)
    (hvalue : value = factor * chain.uniformizer ^ level)
    (hfactor : IsUnit factor) :
    Nat.card (rightMulAddHom value).range = 2 ^ (chain.length - level) := by
  rw [rightMulRange_eq_uniformizerPower_of_factorization
    chain value factor level hvalue hfactor]
  exact chain.card_power level hlevel

/-! ## Arithmetic of the two-level profile -/

/-- The two displayed forms of the exact number of uniform bits agree. -/
theorem twoLevelUniformBits_eq
    {K e n v : ℕ} (he : e < K) (hv : v ≤ n) :
    (K - e) * (n - v) + (K - e - 1) * v =
      (K - e) * n - v := by
  have hleft : (K - e) * (n - v) =
      (K - e) * n - (K - e) * v :=
    Nat.mul_sub_left_distrib (K - e) n v
  have hright : (K - e - 1) * v =
      (K - e) * v - v := by
    simpa only [one_mul] using Nat.mul_sub_right_distrib (K - e) 1 v
  rw [hleft, hright]
  simpa only [one_mul] using
    (Nat.sub_add_sub_cancel
      (Nat.mul_le_mul_left (K - e) hv)
      (calc
        v = 1 * v := by simp
        _ ≤ (K - e) * v := Nat.mul_le_mul_right v (by omega)))

/-- The exact profile improves the unit-minor count by `v * (K-e-1)` bits. -/
theorem twoLevelUniformBits_eq_minor_add_gain
    {K e n v : ℕ} (he : e < K) (hv : v ≤ n) :
    (K - e) * n - v =
      (K - e) * (n - v) + v * (K - e - 1) := by
  simpa only [Nat.mul_comm] using (twoLevelUniformBits_eq he hv).symm

/-- Total ramified depth `e*n+v` leaves exactly `(K-e)*n-v` binary image bits. -/
theorem totalDepth_complement_eq
    (K e n v : ℕ) :
    K * n - (e * n + v) = (K - e) * n - v := by
  rw [Nat.sub_add_eq, ← Nat.sub_mul]

/-! ## Primitive lifts retain their binary Hasse depth -/

/-- A nonzero polynomial of degree below the binary quotient degree represents a nonzero class. -/
theorem binaryQuotientPolynomial_ne_zero
    (d : ℕ) {polynomial : F2[X]} (hne : polynomial ≠ 0)
    (hdegree : polynomial.natDegree < 2 ^ d) :
    binaryQuotientPolynomial d polynomial ≠ 0 := by
  letI : Fact (0 < (1 : ℕ)) := ⟨by omega⟩
  letI : Fintype (QuotientRq 2 (2 ^ d)) :=
    PowerOfTwoQuadraticKDMStatistical.quotientPowerOfTwoRqFintype 1 d
  letI : DecidableEq (QuotientRq 2 (2 ^ d)) :=
    PowerOfTwoQuadraticKDMStatistical.quotientPowerOfTwoRqDecidableEq 1 d
  intro hzero
  have hvaluation :=
    binaryQuotientPolynomial_chainValuation_eq_hasseValuation d hne hdegree
  change truncatedValuation (quotientUniformizer 2 (2 ^ d))
      (1 * 2 ^ d) (binaryQuotientPolynomial d polynomial) =
        hasseValuation (2 ^ d) polynomial at hvaluation
  simp only [one_mul] at hvaluation
  rw [hzero, truncatedValuation_eq_length_of_eq_zero] at hvaluation
  exact (Nat.ne_of_gt (hasseValuation_lt_of_ne_zero (2 ^ d) hne hdegree))
    hvaluation

/-- Every nonzero element of the literal power-of-two quotient is a unit times the power of
`1-X` selected by its certified chain valuation. -/
theorem quotientPowerOfTwo_factor_at_valuation_isUnit
    (K d : ℕ) [hK : Fact (0 < K)]
    (value : QuotientRq (2 ^ K) (2 ^ d)) (hvalue : value ≠ 0) :
    ∃ factor : QuotientRq (2 ^ K) (2 ^ d),
      factor * quotientUniformizer (2 ^ K) (2 ^ d) ^
          (quotientPowerOfTwoAdicChain K d).valuation value = value ∧
        IsUnit factor := by
  let residue : QuotientRq (2 ^ K) (2 ^ d) →+* ZMod 2 :=
    quotientParityEval
      (pow_dvd_pow 2 (Nat.succ_le_iff.mpr hK.out))
  letI : IsLocalHom residue :=
    isLocalHom_toZModTwo_of_nilpotent_kernel residue (by
      intro element helement
      exact quotientParityEval_kernel_isNilpotent_powerOfTwo
        K hK.out d element (by simpa only [residue] using helement))
  simpa only [quotientPowerOfTwoAdicChain,
    finiteAdicChainOfPrincipalResidue, one_mul] using
    (factor_at_truncatedValuation_isUnit
      residue
      (quotientUniformizer (2 ^ K) (2 ^ d))
      (K * 2 ^ d)
      (by simpa only [residue] using
        (quotientParityEval_ker_eq_uniformizer_powerOfTwo
          K hK.out (2 ^ d)))
      (quotientUniformizer_pow_length_eq_zero K hK.out d)
      value hvalue)

/-- Every binary ramification layer has the expected cardinality, stated with modulus literally
`2` rather than the definitionally equal expression `2^1`. -/
theorem card_binaryQuotient_uniformizerPower_range
    (d level : ℕ) (hlevel : level ≤ 2 ^ d) :
    Nat.card
        (rightMulAddHom (quotientUniformizer 2 (2 ^ d) ^ level)).range =
      2 ^ (2 ^ d - level) := by
  classical
  letI : Fact (1 < (2 : ℕ)) := ⟨by omega⟩
  letI : Fintype (QuotientRq 2 (2 ^ d)) := by
    exact Fintype.ofEquiv
      (Rq 2 (2 ^ d))
      (quotientEquiv (q := 2) (pow_pos (by omega : 0 < 2) d))
  letI : DecidableEq (QuotientRq 2 (2 ^ d)) := Classical.decEq _
  let residue : QuotientRq 2 (2 ^ d) →+* ZMod 2 := quotientParityEval dvd_rfl
  letI : IsLocalHom residue :=
    isLocalHom_toZModTwo_of_nilpotent_kernel residue (by
      intro value hvalue
      exact quotientParityEval_kernel_isNilpotent_binary_powerOfTwo d value
        (by simpa only [residue] using hvalue))
  have hker : (RingHom.ker residue).toAddSubgroup =
      adicPower (quotientUniformizer 2 (2 ^ d)) 1 := by
    ext value
    obtain ⟨polynomial, rfl⟩ := Ideal.Quotient.mk_surjective value
    rw [show Ideal.Quotient.mk
          (Ideal.span {LatticeCrypto.negacyclicModulus F2 (2 ^ d)}) polynomial =
        binaryQuotientPolynomial d polynomial by rfl]
    rw [binaryQuotientPolynomial_mem_adicPower_iff d 1 (by
      have hpositive : 0 < 2 ^ d := pow_pos (by omega) d
      omega)]
    change polynomialParityEval dvd_rfl polynomial = 0 ↔ _
    simp only [polynomialParityEval, ZMod.castHom_self,
      pow_one, Polynomial.dvd_iff_isRoot, Polynomial.IsRoot]
    have heval :
        (Polynomial.eval₂RingHom (RingHom.id F2) 1) polynomial =
          polynomial.eval 1 := by
      simp
    rw [heval]
  have hcard : Nat.card (QuotientRq 2 (2 ^ d)) = 2 ^ (2 ^ d) := by
    have source := card_quotientPowerOfTwoRq 1 d
    simpa only [show (2 : ℕ) ^ 1 = 2 by norm_num, one_mul] using source
  exact card_adicPower_eq_pow_sub residue
    (quotientUniformizer 2 (2 ^ d)) (2 ^ d)
    hker (quotientUniformizer_pow_eq_zero_binary_powerOfTwo d)
    hcard level hlevel

/-- Coefficient reduction preserves the exact valuation of every primitive lift: a nonzero
binary reduction cannot hide an additional full ramification layer. -/
theorem quotientPowerOfTwo_valuation_eq_hasseValuation_of_reduction
    (K d : ℕ) [hK : Fact (0 < K)]
    (primitive : QuotientRq (2 ^ K) (2 ^ d))
    {polynomial : F2[X]} (hne : polynomial ≠ 0)
    (hdegree : polynomial.natDegree < 2 ^ d)
    (hreduction :
      quotientCoefficientReduce
          (pow_dvd_pow 2 (Nat.succ_le_iff.mpr hK.out)) primitive =
        binaryQuotientPolynomial d polynomial) :
    (quotientPowerOfTwoAdicChain K d).valuation primitive =
      hasseValuation (2 ^ d) polynomial := by
  classical
  let reduce : QuotientRq (2 ^ K) (2 ^ d) →+* QuotientRq 2 (2 ^ d) :=
    quotientCoefficientReduce
      (pow_dvd_pow 2 (Nat.succ_le_iff.mpr hK.out))
  let highChain := quotientPowerOfTwoAdicChain K d
  let level := highChain.valuation primitive
  let binaryValue := binaryQuotientPolynomial d polynomial
  change level = hasseValuation (2 ^ d) polynomial
  have hbinaryValue : binaryValue ≠ 0 :=
    binaryQuotientPolynomial_ne_zero d hne hdegree
  have hprimitive : primitive ≠ 0 := by
    intro hzero
    apply hbinaryValue
    change binaryQuotientPolynomial d polynomial = 0
    rw [← hreduction, hzero, map_zero]
  obtain ⟨factor, hfactor, hfactorUnit⟩ :=
    quotientPowerOfTwo_factor_at_valuation_isUnit K d primitive hprimitive
  have hmapped :
      reduce factor * quotientUniformizer 2 (2 ^ d) ^ level = binaryValue := by
    have := congrArg reduce hfactor
    simpa only [map_mul, map_pow, quotientCoefficientReduce_uniformizer,
      reduce, highChain, level, binaryValue, hreduction] using this
  have hmappedUnit : IsUnit (reduce factor) := IsUnit.map reduce hfactorUnit
  have hlevelLt : level < 2 ^ d := by
    by_contra hnot
    have hpowerZero :
        quotientUniformizer 2 (2 ^ d) ^ level = 0 :=
      pow_eq_zero_of_le (Nat.le_of_not_gt hnot)
        (quotientUniformizer_pow_eq_zero_binary_powerOfTwo d)
    apply hbinaryValue
    rw [← hmapped, hpowerZero, mul_zero]
  have hrange :
      (rightMulAddHom binaryValue).range =
        (rightMulAddHom (quotientUniformizer 2 (2 ^ d) ^ level)).range := by
    rw [← hmapped]
    exact rightMulRange_isUnit_mul (reduce factor)
      (quotientUniformizer 2 (2 ^ d) ^ level) hmappedUnit
  have hcardBinary :=
    card_binaryQuotient_rightMulRange_eq_two_pow_hasseRank d hne hdegree
  have hcardLevel :=
    card_binaryQuotient_uniformizerPower_range d level hlevelLt.le
  have hpowers :
      2 ^ (2 ^ d - hasseValuation (2 ^ d) polynomial) =
        2 ^ (2 ^ d - level) := by
    rw [← hcardBinary, hrange]
    exact hcardLevel
  have hexponents :
      2 ^ d - hasseValuation (2 ^ d) polynomial = 2 ^ d - level :=
    Nat.pow_right_injective (by omega : 2 ≤ 2) hpowers
  have hhasseLt := hasseValuation_lt_of_ne_zero (2 ^ d) hne hdegree
  omega

/-! ## The scalar two has ramified depth `n` -/

/-- The binary geometric polynomial occurring in `(1-X) * geom = 2`. -/
def binaryGeomPolynomial (d : ℕ) : F2[X] :=
  ∑ index ∈ Finset.range (2 ^ d), (X : F2[X]) ^ index

/-- In characteristic two and power-of-two degree, the geometric polynomial is the
`(n-1)`st power of the repeated-root uniformizer. -/
theorem binaryGeomPolynomial_eq_uniformizer_pow (d : ℕ) :
    binaryGeomPolynomial d =
      (X - C (1 : F2)) ^ (2 ^ d - 1) := by
  let n := 2 ^ d
  have hn : 0 < n := pow_pos (by omega) d
  have hgeom :
      binaryGeomPolynomial d * (X - 1) = X ^ n - 1 := by
    simpa only [binaryGeomPolynomial, n] using
      (geom_sum_mul (X : F2[X]) n)
  have hminus : (X ^ n - 1 : F2[X]) = X ^ n + 1 := by
    have hnegOne : -(1 : F2[X]) = 1 := by
      ext coefficient
      simp [ZMod.neg_eq_self_mod_two]
    rw [sub_eq_add_neg, hnegOne]
  have hmodulus :
      (X ^ n + 1 : F2[X]) = (X - C 1) ^ n := by
    simpa only [LatticeCrypto.negacyclicModulus, n] using
      (binary_negacyclicModulus_eq_X_sub_one_pow d)
  have hpower :
      (X - C (1 : F2)) ^ n =
        (X - C 1) ^ (n - 1) * (X - C 1) := by
    calc
      (X - C (1 : F2)) ^ n = (X - C 1) ^ ((n - 1) + 1) := by
        congr 1
        omega
      _ = (X - C 1) ^ (n - 1) * (X - C 1) := pow_succ _ _
  apply mul_right_cancel₀ (Polynomial.X_sub_C_ne_zero (1 : F2))
  calc
    binaryGeomPolynomial d * (X - C 1) = X ^ n - 1 := hgeom
    _ = X ^ n + 1 := hminus
    _ = (X - C 1) ^ n := hmodulus
    _ = (X - C 1) ^ (n - 1) * (X - C 1) := hpower

/-- The geometric polynomial has Hasse depth exactly `n-1`. -/
theorem hasseValuation_binaryGeomPolynomial (d : ℕ) :
    hasseValuation (2 ^ d) (binaryGeomPolynomial d) = 2 ^ d - 1 := by
  let n := 2 ^ d
  have hn : 0 < n := pow_pos (by omega) d
  have hpoly := binaryGeomPolynomial_eq_uniformizer_pow d
  have hne : binaryGeomPolynomial d ≠ 0 := by
    rw [hpoly]
    exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero (1 : F2))
  have hdegree : (binaryGeomPolynomial d).natDegree < n := by
    rw [hpoly, Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
    simp only [mul_one]
    omega
  have hzero : syndromesZeroBelow (binaryGeomPolynomial d) (n - 1) := by
    unfold syndromesZeroBelow
    apply (X_sub_one_pow_dvd_iff_hasseSyndrome_zero
      (binaryGeomPolynomial d) (n - 1)).mp
    rw [hpoly]
  have hlower : n - 1 ≤ hasseValuation n (binaryGeomPolynomial d) :=
    (le_hasseValuation_iff_syndromesZeroBelow n
      (binaryGeomPolynomial d) (by omega)).2 hzero
  have hupper : hasseValuation n (binaryGeomPolynomial d) < n :=
    hasseValuation_lt_of_ne_zero n hne hdegree
  change hasseValuation n (binaryGeomPolynomial d) = n - 1
  omega

/-- Coefficient reduction sends the high-modulus geometric element to the displayed binary
geometric polynomial. -/
theorem quotientCoefficientReduce_geomSum
    (K d : ℕ) [hK : Fact (0 < K)] :
    quotientCoefficientReduce
        (pow_dvd_pow 2 (Nat.succ_le_iff.mpr hK.out))
        (quotientGeomSum (2 ^ K) (2 ^ d)) =
      binaryQuotientPolynomial d (binaryGeomPolynomial d) := by
  unfold quotientGeomSum binaryGeomPolynomial binaryQuotientPolynomial
  rw [quotientCoefficientReduce_mk]
  congr 1
  rw [Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [Polynomial.map_pow, Polynomial.map_X]

/-- The geometric element itself has valuation `n-1` in every modulus `2^K`. -/
theorem quotientGeomSum_valuation
    (K d : ℕ) [hK : Fact (0 < K)] :
    (quotientPowerOfTwoAdicChain K d).valuation
        (quotientGeomSum (2 ^ K) (2 ^ d)) = 2 ^ d - 1 := by
  rw [quotientPowerOfTwo_valuation_eq_hasseValuation_of_reduction
    K d (quotientGeomSum (2 ^ K) (2 ^ d))
    (polynomial := binaryGeomPolynomial d)]
  · exact hasseValuation_binaryGeomPolynomial d
  · rw [binaryGeomPolynomial_eq_uniformizer_pow]
    exact pow_ne_zero _ (Polynomial.X_sub_C_ne_zero (1 : F2))
  · rw [binaryGeomPolynomial_eq_uniformizer_pow,
      Polynomial.natDegree_pow, Polynomial.natDegree_X_sub_C]
    simp only [mul_one]
    have hpositive : 0 < 2 ^ d := pow_pos (by omega) d
    omega
  · exact quotientCoefficientReduce_geomSum K d

/-- Literal total ramification: in degree `n=2^d`, the scalar `2` is a unit times `pi^n`. -/
theorem exists_isUnit_mul_uniformizer_pow_degree_eq_two
    (K d : ℕ) [hK : Fact (0 < K)] :
    ∃ factor : QuotientRq (2 ^ K) (2 ^ d),
      factor * quotientUniformizer (2 ^ K) (2 ^ d) ^ (2 ^ d) = 2 ∧
        IsUnit factor := by
  let geom := quotientGeomSum (2 ^ K) (2 ^ d)
  have hgeomNe : geom ≠ 0 := by
    intro hzero
    have hvaluation := quotientGeomSum_valuation K d
    change (quotientPowerOfTwoAdicChain K d).valuation geom = 2 ^ d - 1 at hvaluation
    rw [hzero] at hvaluation
    change truncatedValuation (quotientUniformizer (2 ^ K) (2 ^ d))
      (K * 2 ^ d) 0 = 2 ^ d - 1 at hvaluation
    rw [truncatedValuation_eq_length_of_eq_zero] at hvaluation
    have hKpositive := hK.out
    have hnpositive : 0 < 2 ^ d := pow_pos (by omega) d
    have hnle : 2 ^ d ≤ K * 2 ^ d := by
      calc
        2 ^ d = 1 * 2 ^ d := by simp
        _ ≤ K * 2 ^ d := Nat.mul_le_mul_right (2 ^ d) hKpositive
    omega
  obtain ⟨factor, hfactor, hfactorUnit⟩ :=
    quotientPowerOfTwo_factor_at_valuation_isUnit K d geom hgeomNe
  have hvaluation := quotientGeomSum_valuation K d
  change (quotientPowerOfTwoAdicChain K d).valuation geom = 2 ^ d - 1 at hvaluation
  rw [hvaluation] at hfactor
  refine ⟨factor, ?_, hfactorUnit⟩
  have hn : 0 < 2 ^ d := pow_pos (by omega) d
  let uniformizer := quotientUniformizer (2 ^ K) (2 ^ d)
  have hpower : uniformizer ^ (2 ^ d) =
      uniformizer ^ (2 ^ d - 1) * uniformizer := by
    calc
      uniformizer ^ (2 ^ d) = uniformizer ^ ((2 ^ d - 1) + 1) := by
        congr 1
        omega
      _ = uniformizer ^ (2 ^ d - 1) * uniformizer := pow_succ _ _
  calc
    factor * quotientUniformizer (2 ^ K) (2 ^ d) ^ (2 ^ d) =
        quotientUniformizer (2 ^ K) (2 ^ d) *
          (factor * quotientUniformizer (2 ^ K) (2 ^ d) ^ (2 ^ d - 1)) := by
      change factor * uniformizer ^ (2 ^ d) =
        uniformizer * (factor * uniformizer ^ (2 ^ d - 1))
      rw [hpower]
      ring
    _ = quotientUniformizer (2 ^ K) (2 ^ d) * geom := by rw [hfactor]
    _ = 2 := quotientUniformizer_mul_geomSum (2 ^ K) (2 ^ d)

/-! ## Exact two-primary layer of `2^e h` -/

/-- A primitive lift is a unit times the Hasse-selected power of the uniformizer. -/
theorem exists_isUnit_mul_uniformizer_pow_hasse_eq_primitive
    (K d : ℕ) [hK : Fact (0 < K)]
    (primitive : QuotientRq (2 ^ K) (2 ^ d))
    {polynomial : F2[X]} (hne : polynomial ≠ 0)
    (hdegree : polynomial.natDegree < 2 ^ d)
    (hreduction :
      quotientCoefficientReduce
          (pow_dvd_pow 2 (Nat.succ_le_iff.mpr hK.out)) primitive =
        binaryQuotientPolynomial d polynomial) :
    ∃ factor : QuotientRq (2 ^ K) (2 ^ d),
      factor * quotientUniformizer (2 ^ K) (2 ^ d) ^
          hasseValuation (2 ^ d) polynomial = primitive ∧
        IsUnit factor := by
  have hbinaryValue := binaryQuotientPolynomial_ne_zero d hne hdegree
  have hprimitive : primitive ≠ 0 := by
    intro hzero
    apply hbinaryValue
    rw [← hreduction, hzero, map_zero]
  obtain ⟨factor, hfactor, hfactorUnit⟩ :=
    quotientPowerOfTwo_factor_at_valuation_isUnit K d primitive hprimitive
  have hvaluation :=
    quotientPowerOfTwo_valuation_eq_hasseValuation_of_reduction
      K d primitive hne hdegree hreduction
  rw [hvaluation] at hfactor
  exact ⟨factor, hfactor, hfactorUnit⟩

/-- The complete difference `2^e h` is a unit times `pi^(e*n+v)`. -/
theorem exists_twoPrimary_factorization
    (K d e : ℕ) [hK : Fact (0 < K)]
    (primitive : QuotientRq (2 ^ K) (2 ^ d))
    {polynomial : F2[X]} (hne : polynomial ≠ 0)
    (hdegree : polynomial.natDegree < 2 ^ d)
    (hreduction :
      quotientCoefficientReduce
          (pow_dvd_pow 2 (Nat.succ_le_iff.mpr hK.out)) primitive =
        binaryQuotientPolynomial d polynomial) :
    ∃ factor : QuotientRq (2 ^ K) (2 ^ d),
      (2 : QuotientRq (2 ^ K) (2 ^ d)) ^ e * primitive =
        factor * quotientUniformizer (2 ^ K) (2 ^ d) ^
          (e * 2 ^ d + hasseValuation (2 ^ d) polynomial) ∧
      IsUnit factor := by
  obtain ⟨twoFactor, htwo, htwoUnit⟩ :=
    exists_isUnit_mul_uniformizer_pow_degree_eq_two K d
  obtain ⟨primitiveFactor, hprimitive, hprimitiveUnit⟩ :=
    exists_isUnit_mul_uniformizer_pow_hasse_eq_primitive
      K d primitive hne hdegree hreduction
  refine ⟨twoFactor ^ e * primitiveFactor, ?_, htwoUnit.pow e |>.mul hprimitiveUnit⟩
  rw [← htwo, ← hprimitive, mul_pow, ← pow_mul]
  have hexponent : 2 ^ d * e = e * 2 ^ d := Nat.mul_comm _ _
  rw [hexponent, pow_add]
  ring

/-- In a finite binary chain, a unit-times-`pi^level` factorization fixes the chain valuation. -/
theorem valuation_eq_level_of_factorization
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    (chain : FiniteAdicChain R) (value factor : R) (level : ℕ)
    (hlevel : level ≤ chain.length)
    (hvalue : value = factor * chain.uniformizer ^ level)
    (hfactor : IsUnit factor) :
    chain.valuation value = level := by
  have hcardValue := card_rightMulRange_eq_two_pow_rank chain value
  have hcardLevel := card_rightMulRange_eq_two_pow_sub_of_factorization
    chain value factor level hlevel hvalue hfactor
  have hpowers :
      2 ^ (chain.length - chain.valuation value) =
        2 ^ (chain.length - level) := by
    rw [← hcardValue, hcardLevel]
  have hexponents :
      chain.length - chain.valuation value = chain.length - level :=
    Nat.pow_right_injective (by omega : 2 ≤ 2) hpowers
  have hvaluation := chain.valuation_le value
  omega

/-- The literal chain valuation of `2^e h` is exactly `e*n+v`. -/
theorem quotientPowerOfTwo_twoPrimary_valuation
    (K d e : ℕ) [hK : Fact (0 < K)] (he : e < K)
    (primitive : QuotientRq (2 ^ K) (2 ^ d))
    {polynomial : F2[X]} (hne : polynomial ≠ 0)
    (hdegree : polynomial.natDegree < 2 ^ d)
    (hreduction :
      quotientCoefficientReduce
          (pow_dvd_pow 2 (Nat.succ_le_iff.mpr hK.out)) primitive =
        binaryQuotientPolynomial d polynomial) :
    (quotientPowerOfTwoAdicChain K d).valuation
        ((2 : QuotientRq (2 ^ K) (2 ^ d)) ^ e * primitive) =
      e * 2 ^ d + hasseValuation (2 ^ d) polynomial := by
  obtain ⟨factor, hfactor, hfactorUnit⟩ :=
    exists_twoPrimary_factorization K d e primitive hne hdegree hreduction
  have hhasseLt := hasseValuation_lt_of_ne_zero (2 ^ d) hne hdegree
  have hsuccessor : e + 1 ≤ K := Nat.succ_le_iff.mpr he
  have hlevel : e * 2 ^ d + hasseValuation (2 ^ d) polynomial ≤
      (quotientPowerOfTwoAdicChain K d).length := by
    rw [quotientPowerOfTwoAdicChain_length]
    have hmul : (e + 1) * 2 ^ d ≤ K * 2 ^ d :=
      Nat.mul_le_mul_right (2 ^ d) hsuccessor
    have hsplitting : (e + 1) * 2 ^ d = e * 2 ^ d + 2 ^ d := by
      rw [Nat.add_mul]
      simp
    omega
  apply valuation_eq_level_of_factorization
    (quotientPowerOfTwoAdicChain K d)
    ((2 : QuotientRq (2 ^ K) (2 ^ d)) ^ e * primitive)
    factor (e * 2 ^ d + hasseValuation (2 ^ d) polynomial) hlevel
  · exact hfactor
  · exact hfactorUnit

/-- **Exact two-level image cardinality.**  This is the basis-free, security-relevant content of
the two-primary Smith form. -/
theorem card_quotientPowerOfTwo_twoPrimary_range
    (K d e : ℕ) [hK : Fact (0 < K)] (he : e < K)
    (primitive : QuotientRq (2 ^ K) (2 ^ d))
    {polynomial : F2[X]} (hne : polynomial ≠ 0)
    (hdegree : polynomial.natDegree < 2 ^ d)
    (hreduction :
      quotientCoefficientReduce
          (pow_dvd_pow 2 (Nat.succ_le_iff.mpr hK.out)) primitive =
        binaryQuotientPolynomial d polynomial) :
    Nat.card
        (rightMulAddHom
          ((2 : QuotientRq (2 ^ K) (2 ^ d)) ^ e * primitive)).range =
      2 ^ ((K - e) * 2 ^ d - hasseValuation (2 ^ d) polynomial) := by
  have hcard := card_rightMulRange_eq_two_pow_rank
    (quotientPowerOfTwoAdicChain K d)
    ((2 : QuotientRq (2 ^ K) (2 ^ d)) ^ e * primitive)
  rw [quotientPowerOfTwoAdicChain_length,
    quotientPowerOfTwo_twoPrimary_valuation
      K d e he primitive hne hdegree hreduction,
    totalDepth_complement_eq] at hcard
  exact hcard

/-- Equivalent two-level form: `n-v` directions retain `K-e` bits and `v` directions retain
`K-e-1` bits. -/
theorem card_quotientPowerOfTwo_twoPrimary_range_eq_layered
    (K d e : ℕ) [hK : Fact (0 < K)] (he : e < K)
    (primitive : QuotientRq (2 ^ K) (2 ^ d))
    {polynomial : F2[X]} (hne : polynomial ≠ 0)
    (hdegree : polynomial.natDegree < 2 ^ d)
    (hreduction :
      quotientCoefficientReduce
          (pow_dvd_pow 2 (Nat.succ_le_iff.mpr hK.out)) primitive =
        binaryQuotientPolynomial d polynomial) :
    Nat.card
        (rightMulAddHom
          ((2 : QuotientRq (2 ^ K) (2 ^ d)) ^ e * primitive)).range =
      2 ^ ((K - e) * (2 ^ d - hasseValuation (2 ^ d) polynomial) +
        (K - e - 1) * hasseValuation (2 ^ d) polynomial) := by
  rw [card_quotientPowerOfTwo_twoPrimary_range
    K d e he primitive hne hdegree hreduction]
  congr 1
  exact (twoLevelUniformBits_eq he
    (hasseValuation_le (2 ^ d) polynomial)).symm

/-- The corresponding additive cokernel has exactly `2^(e*n+v)` elements. -/
theorem card_quotientPowerOfTwo_twoPrimary_cokernel
    (K d e : ℕ) [hK : Fact (0 < K)] (he : e < K)
    (primitive : QuotientRq (2 ^ K) (2 ^ d))
    {polynomial : F2[X]} (hne : polynomial ≠ 0)
    (hdegree : polynomial.natDegree < 2 ^ d)
    (hreduction :
      quotientCoefficientReduce
          (pow_dvd_pow 2 (Nat.succ_le_iff.mpr hK.out)) primitive =
        binaryQuotientPolynomial d polynomial) :
    Nat.card
        (QuotientRq (2 ^ K) (2 ^ d) ⧸
          (rightMulAddHom
            ((2 : QuotientRq (2 ^ K) (2 ^ d)) ^ e * primitive)).range) =
      2 ^ (e * 2 ^ d + hasseValuation (2 ^ d) polynomial) := by
  rw [card_principalCokernel_eq_two_pow_valuation,
    quotientPowerOfTwo_twoPrimary_valuation
      K d e he primitive hne hdegree hreduction]

/-- The concrete two-primary generator has exactly the claimed uniformizer-power principal
ideal. -/
theorem quotientPowerOfTwo_twoPrimary_range_eq_uniformizerPower
    (K d e : ℕ) [hK : Fact (0 < K)] (he : e < K)
    (primitive : QuotientRq (2 ^ K) (2 ^ d))
    {polynomial : F2[X]} (hne : polynomial ≠ 0)
    (hdegree : polynomial.natDegree < 2 ^ d)
    (hreduction :
      quotientCoefficientReduce
          (pow_dvd_pow 2 (Nat.succ_le_iff.mpr hK.out)) primitive =
        binaryQuotientPolynomial d polynomial) :
    (rightMulAddHom
        ((2 : QuotientRq (2 ^ K) (2 ^ d)) ^ e * primitive)).range =
      (rightMulAddHom
        (quotientUniformizer (2 ^ K) (2 ^ d) ^
          (e * 2 ^ d + hasseValuation (2 ^ d) polynomial))).range := by
  rw [(quotientPowerOfTwoAdicChain K d).principal_eq]
  rw [quotientPowerOfTwo_twoPrimary_valuation
    K d e he primitive hne hdegree hreduction]
  rfl

/-- Exact normalized multiplication-fiber factor for the concrete two-primary generator. -/
theorem principalFiberWeight_quotientPowerOfTwo_twoPrimary
    (K d e : ℕ) [hK : Fact (0 < K)] (he : e < K)
    (primitive target : QuotientRq (2 ^ K) (2 ^ d))
    {polynomial : F2[X]} (hne : polynomial ≠ 0)
    (hdegree : polynomial.natDegree < 2 ^ d)
    (hreduction :
      quotientCoefficientReduce
          (pow_dvd_pow 2 (Nat.succ_le_iff.mpr hK.out)) primitive =
        binaryQuotientPolynomial d polynomial) :
    principalFiberWeight
        ((2 : QuotientRq (2 ^ K) (2 ^ d)) ^ e * primitive) target =
      if InPrincipalIdeal
          (quotientUniformizer (2 ^ K) (2 ^ d) ^
            (e * 2 ^ d + hasseValuation (2 ^ d) polynomial)) target then
        (2 : ℝ) ^ (e * 2 ^ d + hasseValuation (2 ^ d) polynomial)
      else 0 := by
  rw [principalFiberWeight_eq_adic (quotientPowerOfTwoAdicChain K d)]
  rw [quotientPowerOfTwo_twoPrimary_valuation
    K d e he primitive hne hdegree hreduction]
  rfl

/-! ### Cardinal-level Smith models -/

/-- Carrier with the image cardinality of `n-v` diagonal entries `2^e` and `v` diagonal entries
`2^(e+1)`. -/
abbrev TwoPrimaryImageModel (K e n v : ℕ) :=
  (Fin (n - v) → ZMod (2 ^ (K - e))) ×
    (Fin v → ZMod (2 ^ (K - e - 1)))

/-- Carrier with the corresponding cokernel cardinality. -/
abbrev TwoPrimaryCokernelModel (e n v : ℕ) :=
  (Fin (n - v) → ZMod (2 ^ e)) ×
    (Fin v → ZMod (2 ^ (e + 1)))

@[simp]
theorem card_twoPrimaryImageModel (K e n v : ℕ) :
    Nat.card (TwoPrimaryImageModel K e n v) =
      2 ^ ((K - e) * (n - v) + (K - e - 1) * v) := by
  simp [TwoPrimaryImageModel, Nat.card_eq_fintype_card, pow_add, pow_mul]

/-- Arithmetic form of the two-level cokernel exponent. -/
theorem twoLevelCokernelBits_eq {e n v : ℕ} (hv : v ≤ n) :
    e * (n - v) + (e + 1) * v = e * n + v := by
  have hleft : e * (n - v) = e * n - e * v :=
    Nat.mul_sub_left_distrib e n v
  have hbound : e * v ≤ e * n := Nat.mul_le_mul_left e hv
  rw [hleft, Nat.add_mul]
  simp only [one_mul]
  omega

@[simp]
theorem card_twoPrimaryCokernelModel
    (e n v : ℕ) (hv : v ≤ n) :
    Nat.card (TwoPrimaryCokernelModel e n v) = 2 ^ (e * n + v) := by
  rw [show e * n + v = e * (n - v) + (e + 1) * v by
    exact (twoLevelCokernelBits_eq hv).symm]
  simp [TwoPrimaryCokernelModel, Nat.card_eq_fintype_card, pow_add, pow_mul]

/-- The concrete principal image has a carrier equivalence with its exact two-level Smith image
model.  This is deliberately a cardinal equivalence: no high-norm basis transform is applied to
the noise. -/
noncomputable def quotientPowerOfTwo_twoPrimaryRangeEquiv
    (K d e : ℕ) [hK : Fact (0 < K)] (he : e < K)
    (primitive : QuotientRq (2 ^ K) (2 ^ d))
    {polynomial : F2[X]} (hne : polynomial ≠ 0)
    (hdegree : polynomial.natDegree < 2 ^ d)
    (hreduction :
      quotientCoefficientReduce
          (pow_dvd_pow 2 (Nat.succ_le_iff.mpr hK.out)) primitive =
        binaryQuotientPolynomial d polynomial) :
    (rightMulAddHom
        ((2 : QuotientRq (2 ^ K) (2 ^ d)) ^ e * primitive)).range ≃
      TwoPrimaryImageModel K e (2 ^ d)
        (hasseValuation (2 ^ d) polynomial) := by
  classical
  apply Fintype.equivOfCardEq
  simp only [← Nat.card_eq_fintype_card,
    card_quotientPowerOfTwo_twoPrimary_range_eq_layered
      K d e he primitive hne hdegree hreduction,
    card_twoPrimaryImageModel]

/-- The concrete multiplication cokernel likewise has the exact two-level Smith cokernel
carrier. -/
noncomputable def quotientPowerOfTwo_twoPrimaryCokernelEquiv
    (K d e : ℕ) [hK : Fact (0 < K)] (he : e < K)
    (primitive : QuotientRq (2 ^ K) (2 ^ d))
    {polynomial : F2[X]} (hne : polynomial ≠ 0)
    (hdegree : polynomial.natDegree < 2 ^ d)
    (hreduction :
      quotientCoefficientReduce
          (pow_dvd_pow 2 (Nat.succ_le_iff.mpr hK.out)) primitive =
        binaryQuotientPolynomial d polynomial) :
    (QuotientRq (2 ^ K) (2 ^ d) ⧸
        (rightMulAddHom
          ((2 : QuotientRq (2 ^ K) (2 ^ d)) ^ e * primitive)).range) ≃
      TwoPrimaryCokernelModel e (2 ^ d)
        (hasseValuation (2 ^ d) polynomial) := by
  classical
  apply Fintype.equivOfCardEq
  simp only [← Nat.card_eq_fintype_card,
    card_quotientPowerOfTwo_twoPrimary_cokernel
      K d e he primitive hne hdegree hreduction,
    card_twoPrimaryCokernelModel _ _ _
      (hasseValuation_le (2 ^ d) polynomial)]

/-! ## A low-norm Hasse information set -/

/-- The square Pascal submatrix formed by the first `v` coefficient positions.  It is the
information-set minor of the Hasse parity-check matrix. -/
def hassePascalMatrix (v : ℕ) : Matrix (Fin v) (Fin v) F2 :=
  fun row column ↦ (row.val.choose column.val : F2)

/-- A message in the Hasse row space, evaluated in the ordinary coefficient basis.  Every
matrix coefficient is the reduction of a binomial coefficient and hence is literally `0` or
`1`; no integral Smith basis change occurs here. -/
def hasseDualWord (n v : ℕ) (message : Fin v → F2) : Fin n → F2 :=
  fun coordinate ↦
    ∑ row : Fin v, (coordinate.val.choose row.val : F2) * message row

/-- Restriction of a Hasse dual word to its first `v` positions. -/
def hasseInformationProjection (n v : ℕ) (hv : v ≤ n)
    (message : Fin v → F2) : Fin v → F2 :=
  fun coordinate ↦ hasseDualWord n v message (Fin.castLE hv coordinate)

theorem hassePascalMatrix_blockTriangular (v : ℕ) :
    (hassePascalMatrix v).BlockTriangular OrderDual.toDual := by
  intro row column hcolumn
  change row < column at hcolumn
  simp [hassePascalMatrix, Nat.choose_eq_zero_of_lt hcolumn]

/-- The information-set Pascal minor has determinant one over `F₂`. -/
@[simp]
theorem det_hassePascalMatrix (v : ℕ) :
    (hassePascalMatrix v).det = 1 := by
  rw [Matrix.det_of_lowerTriangular (hassePascalMatrix v)
    (hassePascalMatrix_blockTriangular v)]
  simp [hassePascalMatrix]

theorem isUnit_hassePascalMatrix (v : ℕ) :
    IsUnit (hassePascalMatrix v) := by
  rw [Matrix.isUnit_iff_isUnit_det, det_hassePascalMatrix]
  exact isUnit_one

theorem hasseInformationProjection_eq_mulVec
    (n v : ℕ) (hv : v ≤ n) (message : Fin v → F2) :
    hasseInformationProjection n v hv message =
      (hassePascalMatrix v).mulVec message := by
  funext coordinate
  simp only [hasseInformationProjection, hasseDualWord, Matrix.mulVec,
    dotProduct, hassePascalMatrix, Fin.castLE]

/-- The first `v` coefficient locations are an information set for the Hasse row space. -/
theorem hasseInformationProjection_bijective
    (n v : ℕ) (hv : v ≤ n) :
    Function.Bijective (hasseInformationProjection n v hv) := by
  have heq : hasseInformationProjection n v hv =
      (hassePascalMatrix v).mulVec := by
    funext message
    exact hasseInformationProjection_eq_mulVec n v hv message
  rw [heq]
  exact ⟨Matrix.mulVec_injective_iff_isUnit.mpr (isUnit_hassePascalMatrix v),
    Matrix.mulVec_surjective_iff_isUnit.mpr (isUnit_hassePascalMatrix v)⟩

/-- Equivalence induced by the concrete Hasse information set. -/
noncomputable def hasseInformationEquiv
    (n v : ℕ) (hv : v ≤ n) :
    (Fin v → F2) ≃ (Fin v → F2) :=
  Equiv.ofBijective (hasseInformationProjection n v hv)
    (hasseInformationProjection_bijective n v hv)

/-- Literal low-norm congruence test after division by the common power of two and reduction to
the residue field: ideal membership is exactly vanishing of the first Hasse syndromes. -/
theorem binaryQuotientPolynomial_mem_adicPower_iff_syndromesZero
    (d level : ℕ) (hlevel : level ≤ 2 ^ d) (polynomial : F2[X]) :
    binaryQuotientPolynomial d polynomial ∈
        adicPower (quotientUniformizer 2 (2 ^ d)) level ↔
      ∀ j < level, hasseSyndrome polynomial j = 0 := by
  rw [binaryQuotientPolynomial_mem_adicPower_iff d level hlevel,
    X_sub_one_pow_dvd_iff_hasseSyndrome_zero]

/-- Executable coefficient form of the preceding membership test.  Its checks are precisely
`sum_i choose(i,j) * B_i = 0` over `F₂`, as in equation (8). -/
theorem binaryWord_mem_adicPower_iff_executableHasseChecks
    (d level : ℕ) (hlevel : level ≤ 2 ^ d)
    (word : Fin (2 ^ d) → F2) :
    binaryQuotientPolynomial d (binaryWordPolynomial word) ∈
        adicPower (quotientUniformizer 2 (2 ^ d)) level ↔
      ∀ j < level, binaryWordHasseSyndromeExecutable word j = 0 := by
  rw [binaryQuotientPolynomial_mem_adicPower_iff_syndromesZero
    d level hlevel]
  constructor
  · intro hzero j hj
    rw [binaryWordHasseSyndromeExecutable_eq]
    exact hzero j hj
  · intro hzero j hj
    rw [← binaryWordHasseSyndromeExecutable_eq]
    exact hzero j hj

/-- Restricting a word along an injection cannot increase its Hamming support. -/
theorem card_wordSupport_restrict_le
    {Information Coordinate Alphabet : Type}
    [Fintype Information] [DecidableEq Information]
    [Fintype Coordinate] [DecidableEq Coordinate]
    [Zero Alphabet] [DecidableEq Alphabet]
    (information : Information → Coordinate)
    (hinjective : Function.Injective information)
    (word : Coordinate → Alphabet) :
    (wordSupport (fun index ↦ word (information index))).card ≤
      (wordSupport word).card := by
  apply Finset.card_le_card_of_injOn information
  · intro index hindex
    change information index ∈ wordSupport word
    change index ∈ wordSupport (fun index ↦ word (information index)) at hindex
    rw [mem_wordSupport_iff] at hindex ⊢
    exact hindex
  · intro left _ right _ heq
    exact hinjective heq

/-- Hasse information-set weight is at most full Hasse-codeword weight. -/
theorem card_wordSupport_hasseInformationProjection_le
    (n v : ℕ) (hv : v ≤ n) (message : Fin v → F2) :
    (wordSupport (hasseInformationProjection n v hv message)).card ≤
      (wordSupport (hasseDualWord n v message)).card := by
  exact card_wordSupport_restrict_le (Fin.castLE hv)
    (Fin.castLE_injective hv) (hasseDualWord n v message)

/-- Canonical two-element enumeration of `F₂`. -/
def finTwoEquivF2 : Fin 2 ≃ F2 :=
  (ZMod.finEquiv 2).toEquiv

@[simp]
theorem finTwoEquivF2_zero : finTwoEquivF2 0 = 0 := rfl

@[simp]
theorem finTwoEquivF2_one : finTwoEquivF2 1 = 1 := rfl

/-- A support power is a coordinate product of the corresponding binary weight. -/
theorem pow_card_wordSupport_eq_prod
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (word : Index → F2) (beta : ℝ) :
    beta ^ (wordSupport word).card =
      ∏ index : Index, if word index = 0 then 1 else beta := by
  classical
  rw [Finset.prod_ite]
  simp [wordSupport]

/-- Exact complete weight enumerator of the binary cube. -/
theorem sum_pow_card_wordSupport_f2 (Index : Type)
    [Fintype Index] [DecidableEq Index] (beta : ℝ) :
    (∑ word : Index → F2, beta ^ (wordSupport word).card) =
      (1 + beta) ^ Fintype.card Index := by
  classical
  calc
    (∑ word : Index → F2, beta ^ (wordSupport word).card) =
        ∑ word : Index → F2,
          ∏ index : Index, if word index = 0 then 1 else beta := by
      apply Finset.sum_congr rfl
      intro word _
      exact pow_card_wordSupport_eq_prod word beta
    _ = ∏ _index : Index,
          ∑ bit : F2, if bit = 0 then 1 else beta := by
      exact (Fintype.prod_sum
        (fun _index (_bit : F2) ↦ if _bit = 0 then 1 else beta)).symm
    _ = ∏ _index : Index, (1 + beta) := by
      apply Finset.prod_congr rfl
      intro _index _
      calc
        (∑ bit : F2, if bit = 0 then 1 else beta) =
            ∑ index : Fin 2,
              if finTwoEquivF2 index = 0 then 1 else beta := by
          exact (Fintype.sum_equiv finTwoEquivF2 _ _ (fun _ ↦ rfl)).symm
        _ = 1 + beta := by rw [Fin.sum_univ_two]; simp
    _ = (1 + beta) ^ Fintype.card Index := by simp

/-- The Hasse row-space weight enumerator is bounded by its information-set enumerator.  This is
the formal version of equation (13) in the sketch. -/
theorem sum_pow_card_wordSupport_hasseDualWord_le
    (n v : ℕ) (hv : v ≤ n) (beta : ℝ)
    (hbetaZero : 0 ≤ beta) (hbetaOne : beta ≤ 1) :
    (∑ message : Fin v → F2,
        beta ^ (wordSupport (hasseDualWord n v message)).card) ≤
      (1 + beta) ^ v := by
  calc
    (∑ message : Fin v → F2,
        beta ^ (wordSupport (hasseDualWord n v message)).card) ≤
        ∑ message : Fin v → F2,
          beta ^ (wordSupport
            (hasseInformationProjection n v hv message)).card := by
      apply Finset.sum_le_sum
      intro message _
      exact pow_le_pow_of_le_one hbetaZero hbetaOne
        (card_wordSupport_hasseInformationProjection_le n v hv message)
    _ = ∑ word : Fin v → F2,
          beta ^ (wordSupport word).card := by
      exact (hasseInformationEquiv n v hv).sum_comp
        (fun word ↦ beta ^ (wordSupport word).card)
    _ = (1 + beta) ^ v := by
      simpa using sum_pow_card_wordSupport_f2 (Fin v) beta

/-- Scalar IID corollary of the exact Hasse-code formula.  If `pNext / p` is the even-parity
conditional mass `(1+beta)/2`, the weight-enumerator expression is at most the proposed
two-level product `p^(n-v) * pNext^v` (equation (15)). -/
theorem iidHasseEnumerator_le_twoLevelProduct
    (n v : ℕ) (hv : v ≤ n) (p pNext beta : ℝ)
    (hp : 0 ≤ p) (hbetaZero : 0 ≤ beta) (hbetaOne : beta ≤ 1)
    (hpNext : pNext = p * ((1 + beta) / 2)) :
    p ^ n * (2 : ℝ)⁻¹ ^ v *
        (∑ message : Fin v → F2,
          beta ^ (wordSupport (hasseDualWord n v message)).card) ≤
      p ^ (n - v) * pNext ^ v := by
  calc
    p ^ n * (2 : ℝ)⁻¹ ^ v *
        (∑ message : Fin v → F2,
          beta ^ (wordSupport (hasseDualWord n v message)).card) ≤
        p ^ n * (2 : ℝ)⁻¹ ^ v * (1 + beta) ^ v := by
      apply mul_le_mul_of_nonneg_left
        (sum_pow_card_wordSupport_hasseDualWord_le
          n v hv beta hbetaZero hbetaOne)
      positivity
    _ = p ^ n * (((1 + beta) / 2) ^ v) := by
      calc
        p ^ n * (2 : ℝ)⁻¹ ^ v * (1 + beta) ^ v =
            p ^ n * ((2 : ℝ)⁻¹ ^ v * (1 + beta) ^ v) := by ring
        _ = p ^ n * (((2 : ℝ)⁻¹ * (1 + beta)) ^ v) := by
          rw [mul_pow]
        _ = p ^ n * (((1 + beta) / 2) ^ v) := by
          congr 2
          ring
    _ = p ^ (n - v) * (p * ((1 + beta) / 2)) ^ v := by
      calc
        p ^ n * (((1 + beta) / 2) ^ v) =
            (p ^ (n - v) * p ^ v) * (((1 + beta) / 2) ^ v) := by
          rw [← pow_add, Nat.sub_add_cancel hv]
        _ = p ^ (n - v) *
            (p ^ v * (((1 + beta) / 2) ^ v)) := by ring
        _ = p ^ (n - v) * (p * ((1 + beta) / 2)) ^ v := by
          rw [mul_pow]
    _ = p ^ (n - v) * pNext ^ v := by rw [hpNext]

/-- Normalizing by the ambient ring size converts raw divisibility masses into the two
normalized collision factors of equation (17). -/
theorem twoLevel_normalizedFactor_identity
    (e n v : ℕ) (hv : v ≤ n) (p pNext : ℝ) :
    (2 : ℝ) ^ (e * n + v) * (p ^ (n - v) * pNext ^ v) =
      ((2 : ℝ) ^ e * p) ^ (n - v) *
        ((2 : ℝ) ^ (e + 1) * pNext) ^ v := by
  rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul]
  have hbits := twoLevelCokernelBits_eq (e := e) hv
  calc
    (2 : ℝ) ^ (e * n + v) * (p ^ (n - v) * pNext ^ v) =
        ((2 : ℝ) ^ (e * (n - v)) * (2 : ℝ) ^ ((e + 1) * v)) *
          (p ^ (n - v) * pNext ^ v) := by
      rw [← pow_add, hbits]
    _ = (2 : ℝ) ^ (e * (n - v)) * p ^ (n - v) *
          ((2 : ℝ) ^ ((e + 1) * v) * pNext ^ v) := by ring

/-! ## Two-level local-factor aggregation -/

/-- Exponent/Hasse-depth aggregation with the exact two-level local factor from equation (22).
This is the drop-in replacement for the minor-only `base e ^ (n-v)` factor. -/
theorem average_pairKernel_le_twoLevelJointEnumerator
    {Secret : Type} [Fintype Secret] [Nonempty Secret] [DecidableEq Secret]
    (exponent depth : Secret → Secret → ℕ)
    (exponentBound degree : ℕ)
    (hexponent : ∀ left right, left ≠ right →
      exponent left right ≤ exponentBound)
    (hdepth : ∀ left right, left ≠ right → depth left right ≤ degree)
    (kernel : Secret → Secret → ℝ) (base : ℕ → ℝ)
    (hkernel : ∀ left right, left ≠ right →
      kernel left right ≤
        base (exponent left right) ^ (degree - depth left right) *
          base (exponent left right + 1) ^ depth left right) :
    (∑ pair ∈ orderedDistinctPairs Secret, kernel pair.1 pair.2) /
        Fintype.card Secret ≤
      ∑ e ∈ Finset.range (exponentBound + 1),
        ∑ v ∈ Finset.range (degree + 1),
          averageJointPairStatisticCount exponent depth e v *
            (base e ^ (degree - v) * base (e + 1) ^ v) := by
  calc
    (∑ pair ∈ orderedDistinctPairs Secret, kernel pair.1 pair.2) /
          Fintype.card Secret ≤
        (∑ pair ∈ orderedDistinctPairs Secret,
          base (exponent pair.1 pair.2) ^ (degree - depth pair.1 pair.2) *
            base (exponent pair.1 pair.2 + 1) ^ depth pair.1 pair.2) /
          Fintype.card Secret := by
      apply div_le_div_of_nonneg_right
      · apply Finset.sum_le_sum
        intro pair hpair
        exact hkernel pair.1 pair.2
          ((mem_orderedDistinctPairs_iff pair).mp hpair)
      · positivity
    _ = _ := by
      rw [sum_orderedDistinctPairs_eq_sum_jointPairStatisticCount
        exponent depth exponentBound degree hexponent hdepth
        (value := fun e v ↦ base e ^ (degree - v) * base (e + 1) ^ v)]
      unfold averageJointPairStatisticCount
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro e _
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro v _
      ring

/-- For `rowCount` conditionally independent rows, the refined one-row factor raises to the
`rowCount`th power exactly as in equation (23). -/
theorem twoLevelFactor_pow_rows
    (base : ℕ → ℝ) (e degree v rowCount : ℕ) :
    (base e ^ (degree - v) * base (e + 1) ^ v) ^ rowCount =
      (base e ^ (degree - v)) ^ rowCount *
        (base (e + 1) ^ v) ^ rowCount := by
  exact mul_pow _ _ _

/-! ## Invariant finite local overlap -/

/-- Exact finite count behind the local-overlap identity: after fixing the two error tapes,
the number of masks solving the collision is the multiplication-fiber weight. -/
theorem sum_maskedErrorCollision_eq_sum_principalFiberWeight
    {R Tape : Type} [CommRing R] [Fintype R] [DecidableEq R]
    [Fintype Tape] (difference : R) (error : Tape → R) :
    (∑ left : Tape, ∑ right : Tape, ∑ mask : R,
        if mask * difference + error left = error right then (1 : ℝ) else 0) =
      ∑ left : Tape, ∑ right : Tape,
        principalFiberWeight difference (error right - error left) := by
  classical
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  calc
    (∑ mask : R,
        if mask * difference + error left = error right then (1 : ℝ) else 0) =
        ∑ mask : R,
          if mask * difference = error right - error left then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro mask _
      split_ifs with hleft hright <;> simp_all [eq_sub_iff_add_eq]
    _ = principalFiberWeight difference (error right - error left) :=
      rightMulFiberCount difference (error right - error left)

/-- Summing multiplication-fiber weights gives the invariant ideal-membership count times the
ambient-to-image ratio.  Together with the previous theorem, division by the mask and tape
cardinalities is exactly equations (5) and (6) of the sketch. -/
theorem sum_principalFiberWeight_eq_cokernelRatio_mul_idealCount
    {R Tape : Type} [CommRing R] [Fintype R] [DecidableEq R]
    [Fintype Tape] (difference : R) (error : Tape → R) :
    (∑ left : Tape, ∑ right : Tape,
        principalFiberWeight difference (error right - error left)) =
      ((Fintype.card R : ℝ) /
          Fintype.card (rightMulAddHom difference).range) *
        (∑ left : Tape, ∑ right : Tape,
          if InPrincipalIdeal difference (error right - error left) then
            (1 : ℝ)
          else 0) := by
  classical
  unfold principalFiberWeight
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro left _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro right _
  by_cases hmember : InPrincipalIdeal difference (error right - error left) <;>
    simp [hmember]

/-- Probability form of the invariant local-overlap formula for arbitrary finite error tapes.
Uniform tapes represent arbitrary rational finite distributions by repetition. -/
theorem finite_maskedErrorCollisionMass_eq
    {R Tape : Type} [CommRing R] [Fintype R] [Nonempty R] [DecidableEq R]
    [Fintype Tape] [Nonempty Tape] (difference : R) (error : Tape → R) :
    (∑ left : Tape, ∑ right : Tape, ∑ mask : R,
        if mask * difference + error left = error right then (1 : ℝ) else 0) /
        ((Fintype.card R : ℝ) * (Fintype.card Tape : ℝ) ^ 2) =
      ((∑ left : Tape, ∑ right : Tape,
          if InPrincipalIdeal difference (error right - error left) then
            (1 : ℝ)
          else 0) /
          (Fintype.card Tape : ℝ) ^ 2) /
        Fintype.card (rightMulAddHom difference).range := by
  rw [sum_maskedErrorCollision_eq_sum_principalFiberWeight,
    sum_principalFiberWeight_eq_cokernelRatio_mul_idealCount]
  have hring : (Fintype.card R : ℝ) ≠ 0 := by positivity
  have htape : (Fintype.card Tape : ℝ) ≠ 0 := by positivity
  have himage :
      (Fintype.card (rightMulAddHom difference).range : ℝ) ≠ 0 := by
    positivity
  field_simp

/-! ## Correlated errors through quotient characters -/

/-- The two independent error draws used in the quotient convolution. -/
abbrev quotientErrorPairChoice (Tape : Type) (_side : Bool) := Tape

/-- One draw contributes positively and the other negatively in the additive quotient. -/
def quotientErrorPairContribution
    {G Tape : Type} [AddCommGroup G] (subgroup : AddSubgroup G)
    (error : Tape → G) (side : Bool) (tape : Tape) : G ⧸ subgroup :=
  if side then QuotientAddGroup.mk' subgroup (error tape)
  else -QuotientAddGroup.mk' subgroup (error tape)

/-- The two-row convolution sum is exactly the quotient class of the error difference. -/
theorem sum_quotientErrorPairContribution_eq
    {G Tape : Type} [AddCommGroup G] [Fintype Tape]
    (subgroup : AddSubgroup G) (error : Tape → G)
    (rows : Bool → Tape) :
    (∑ side : Bool,
        quotientErrorPairContribution subgroup error side (rows side)) =
      QuotientAddGroup.mk' subgroup (error (rows true) - error (rows false)) := by
  rw [Fintype.sum_bool]
  simp [quotientErrorPairContribution, sub_eq_add_neg]

/-- Thus the zero convolution fiber is precisely invariant subgroup membership; no coordinate
independence or Smith-basis norm estimate is present. -/
theorem sum_quotientErrorPairContribution_eq_zero_iff
    {G Tape : Type} [AddCommGroup G] [Fintype Tape]
    (subgroup : AddSubgroup G) (error : Tape → G)
    (rows : Bool → Tape) :
    (∑ side : Bool,
        quotientErrorPairContribution subgroup error side (rows side)) = 0 ↔
      error (rows true) - error (rows false) ∈ subgroup := by
  rw [sum_quotientErrorPairContribution_eq]
  exact QuotientAddGroup.eq_zero_iff (error (rows true) - error (rows false))

/-- Exact finite Fourier identity for an arbitrary correlated error tape, specialized to the
quotient by the principal image.  The right side is a sum of squared Fourier magnitudes. -/
theorem quotientErrorPair_fourier_identity
    {G Tape : Type} [AddCommGroup G] [Fintype G]
    [Fintype Tape]
    (subgroup : AddSubgroup G) (error : Tape → G) :
    (Fintype.card (G ⧸ subgroup) : ℂ) *
        (FormalProof4FHE.FiniteRowConvolution.rowSumZeroFiberCard
          (quotientErrorPairChoice Tape)
          (quotientErrorPairContribution subgroup error) : ℂ) =
      ∑ character : AddChar (G ⧸ subgroup) ℂ,
        (∑ tape : Tape,
          character (QuotientAddGroup.mk' subgroup (error tape))) *
        star (∑ tape : Tape,
          character (QuotientAddGroup.mk' subgroup (error tape))) := by
  rw [FormalProof4FHE.FiniteRowConvolution.card_mul_rowSumZeroFiberCard_eq_sum_prod_rowCharacterSum]
  apply Finset.sum_congr rfl
  intro character _
  rw [Fintype.prod_bool]
  congr 1
  calc
    (∑ tape : Tape,
        character (quotientErrorPairContribution subgroup error false tape)) =
        ∑ tape : Tape,
          star (character (QuotientAddGroup.mk' subgroup (error tape))) := by
      apply Finset.sum_congr rfl
      intro tape _
      simp [quotientErrorPairContribution, AddChar.map_neg_eq_conj]
    _ = star (∑ tape : Tape,
        character (QuotientAddGroup.mk' subgroup (error tape))) := by
      exact (star_sum (R := ℂ) Finset.univ
        (fun tape : Tape ↦
          character (QuotientAddGroup.mk' subgroup (error tape)))).symm

/-- Annihilator form of the same identity.  This is the exact finite-distribution version of
equation (19): after division by the square of the tape cardinality, every summand is the
squared magnitude of the Fourier expectation. -/
theorem quotientErrorPair_annihilator_fourier_identity
    {G Tape : Type} [AddCommGroup G] [Fintype G]
    [Fintype Tape]
    (subgroup : AddSubgroup G) (error : Tape → G) :
    (Fintype.card (G ⧸ subgroup) : ℂ) *
        (FormalProof4FHE.FiniteRowConvolution.rowSumZeroFiberCard
          (quotientErrorPairChoice Tape)
          (quotientErrorPairContribution subgroup error) : ℂ) =
      ∑ character :
          FormalProof4FHE.FiniteAdditiveCokernel.Annihilator subgroup,
        (∑ tape : Tape, character.1 (error tape)) *
          star (∑ tape : Tape, character.1 (error tape)) := by
  rw [quotientErrorPair_fourier_identity subgroup error]
  apply Fintype.sum_equiv
    (FormalProof4FHE.FiniteAdditiveCokernel.quotientAddCharEquivAnnihilator subgroup)
  intro character
  rfl

end

end FormalProof4FHE.RLWE.RankOneHNFLossinessTwoSmith
