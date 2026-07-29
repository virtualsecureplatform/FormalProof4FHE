/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.RankOneHNFLossinessTwoSmith
import Mathlib.Data.Finset.SymmDiff

/-!
# Exact two-level Smith/Hasse parameter certificates

This module formalizes `sketch/twosmith_exact_parameter_note.tex`.  It complements the
basis-free two-level Smith image theorem with the exact IID Hasse-code correction, rather than
pretending that a Smith basis preserves coefficient independence.

The main finite identity is

`p^n * 2^-v * sum_u beta^(wt (u H))`,

where the sum is taken over the native binary Hasse/Pascal row space.  The module also records
the exact parity-bias square identity, recursive Pascal-code evaluators, exact fixed-weight
signed-ternary pair strata, truncated valuation composition, and joint row-tuple aggregation.
-/

open BigOperators
open scoped symmDiff

namespace FormalProof4FHE.RLWE.RankOneHNFLossinessTwoSmithExact

open FormalProof4FHE.RLWE
open FormalProof4FHE.RLWE.PowerOfTwoQuadraticKDMStatistical
open FormalProof4FHE.RLWE.RankOneHNFLossinessSparseRank
open FormalProof4FHE.RLWE.RankOneHNFLossinessSparseRankChannel
open FormalProof4FHE.RLWE.RankOneHNFLossinessTwoSmith
open Polynomial

noncomputable section

attribute [local instance] Classical.propDecidable

/-! ## Difference-parity bias -/

/-- Fine collision mass after splitting every residue class into its two parity lifts. -/
def fineCollisionMass {Index : Type} [Fintype Index]
    (lower upper : Index → ℝ) : ℝ :=
  ∑ index, (lower index ^ 2 + upper index ^ 2)

/-- Collision mass after forgetting which of the two parity lifts occurred. -/
def coarseCollisionMass {Index : Type} [Fintype Index]
    (lower upper : Index → ℝ) : ℝ :=
  ∑ index, (lower index + upper index) ^ 2

/-- Numerator of the conditional parity bias `beta = (2 pNext - p) / p`. -/
def parityBiasNumerator {Index : Type} [Fintype Index]
    (lower upper : Index → ℝ) : ℝ :=
  2 * fineCollisionMass lower upper - coarseCollisionMass lower upper

/-- Conditional parity bias of an IID difference. -/
def differenceParityBias {Index : Type} [Fintype Index]
    (lower upper : Index → ℝ) : ℝ :=
  parityBiasNumerator lower upper / coarseCollisionMass lower upper

/-- The difference-parity numerator is a sum of squares. -/
theorem parityBiasNumerator_eq_sum_sq_sub
    {Index : Type} [Fintype Index] (lower upper : Index → ℝ) :
    parityBiasNumerator lower upper =
      ∑ index, (lower index - upper index) ^ 2 := by
  classical
  simp only [parityBiasNumerator, fineCollisionMass, coarseCollisionMass]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro index _
  ring

theorem parityBiasNumerator_nonneg
    {Index : Type} [Fintype Index] (lower upper : Index → ℝ) :
    0 ≤ parityBiasNumerator lower upper := by
  rw [parityBiasNumerator_eq_sum_sq_sub]
  positivity

theorem fineCollisionMass_le_coarseCollisionMass
    {Index : Type} [Fintype Index] (lower upper : Index → ℝ)
    (hlower : ∀ index, 0 ≤ lower index) (hupper : ∀ index, 0 ≤ upper index) :
    fineCollisionMass lower upper ≤ coarseCollisionMass lower upper := by
  classical
  unfold fineCollisionMass coarseCollisionMass
  apply Finset.sum_le_sum
  intro index _
  have hmul : 0 ≤ lower index * upper index :=
    mul_nonneg (hlower index) (hupper index)
  nlinarith [hmul]

theorem parityBiasNumerator_le_coarseCollisionMass
    {Index : Type} [Fintype Index] (lower upper : Index → ℝ)
    (hlower : ∀ index, 0 ≤ lower index) (hupper : ∀ index, 0 ≤ upper index) :
    parityBiasNumerator lower upper ≤ coarseCollisionMass lower upper := by
  unfold parityBiasNumerator
  have h := fineCollisionMass_le_coarseCollisionMass lower upper hlower hupper
  linarith

/-- For an IID difference, the conditional parity bias lies in `[0,1]`. -/
theorem differenceParityBias_mem_unitInterval
    {Index : Type} [Fintype Index] (lower upper : Index → ℝ)
    (hlower : ∀ index, 0 ≤ lower index) (hupper : ∀ index, 0 ≤ upper index)
    (hcoarse : 0 < coarseCollisionMass lower upper) :
    0 ≤ differenceParityBias lower upper ∧
      differenceParityBias lower upper ≤ 1 := by
  constructor
  · exact div_nonneg (parityBiasNumerator_nonneg lower upper) hcoarse.le
  · rw [differenceParityBias, div_le_one hcoarse]
    exact parityBiasNumerator_le_coarseCollisionMass lower upper hlower hupper

/-! ## Exact finite Hasse-code Fourier identity -/

/-- The real additive character of `F₂`. -/
def f2Sign (bit : F2) : ℝ := if bit = 0 then 1 else -1

@[simp] theorem f2Sign_zero : f2Sign 0 = 1 := by simp [f2Sign]
@[simp] theorem f2Sign_one : f2Sign 1 = -1 := by norm_num [f2Sign]

theorem f2Sign_add (left right : F2) :
    f2Sign (left + right) = f2Sign left * f2Sign right := by
  by_cases hleft : left = 0
  · subst left
    simp [f2Sign]
  by_cases hright : right = 0
  · subst right
    simp [f2Sign]
  have hleftOne : left = 1 := by
    fin_cases left
    · exact (hleft rfl).elim
    · rfl
  have hrightOne : right = 1 := by
    fin_cases right
    · exact (hright rfl).elim
    · rfl
  subst left
  subst right
  have hadd : (1 : F2) + 1 = 0 := by decide
  simp [f2Sign, hadd]

theorem f2Sign_sum
    {Index : Type} [DecidableEq Index]
    (indices : Finset Index) (value : Index → F2) :
    f2Sign (∑ index ∈ indices, value index) =
      ∏ index ∈ indices, f2Sign (value index) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices hindex ih =>
      simp [hindex, f2Sign_add, ih]

/-- Bernoulli mass with signed bias `beta`. -/
def biasedBitMass (beta : ℝ) (bit : F2) : ℝ :=
  if bit = 0 then (1 + beta) / 2 else (1 - beta) / 2

theorem sum_biasedBitMass (beta : ℝ) :
    ∑ bit : F2, biasedBitMass beta bit = 1 := by
  rw [← (finTwoEquivF2.sum_comp (biasedBitMass beta))]
  rw [Fin.sum_univ_two]
  simp [biasedBitMass]
  ring

theorem sum_biasedBitMass_mul_sign_mul (beta : ℝ) (coefficient : F2) :
    ∑ bit : F2,
        biasedBitMass beta bit * f2Sign (coefficient * bit) =
      if coefficient = 0 then 1 else beta := by
  rw [← (finTwoEquivF2.sum_comp
    (fun bit ↦ biasedBitMass beta bit * f2Sign (coefficient * bit)))]
  rw [Fin.sum_univ_two]
  by_cases hzero : coefficient = 0
  · simp [hzero, biasedBitMass, f2Sign]
    ring
  · have hone : coefficient = 1 := by
      fin_cases coefficient
      · exact (hzero rfl).elim
      · rfl
    simp [hone, biasedBitMass, f2Sign]
    ring

/-- Finite Fubini factorization for products of independent real weights. -/
theorem sum_pi_prod_eq_prod_sum_real
    {Row : Type} [Fintype Row] [DecidableEq Row]
    (Target : Row → Type) [(row : Row) → Fintype (Target row)]
    (weight : (row : Row) → Target row → ℝ) :
    (∑ targets : (row : Row) → Target row,
        ∏ row, weight row (targets row)) =
      ∏ row, ∑ target : Target row, weight row target := by
  exact (Fintype.prod_sum weight).symm

/-- Product mass of an IID biased binary word. -/
def biasedWordMass (n : ℕ) (beta : ℝ) (word : Fin n → F2) : ℝ :=
  ∏ coordinate, biasedBitMass beta (word coordinate)

theorem sum_biasedWordMass (n : ℕ) (beta : ℝ) :
    ∑ word : Fin n → F2, biasedWordMass n beta word = 1 := by
  classical
  unfold biasedWordMass
  rw [sum_pi_prod_eq_prod_sum_real]
  simp [sum_biasedBitMass]

/-- Native pairing between a Hasse row-space word and a coefficient word. -/
def hassePairing (n v : ℕ) (message : Fin v → F2) (word : Fin n → F2) : F2 :=
  ∑ coordinate, hasseDualWord n v message coordinate * word coordinate

/-- Vanishing of the first `v` native coefficient-basis Hasse syndromes. -/
def IsInHasseKernel (n v : ℕ) (word : Fin n → F2) : Prop :=
  ∀ row : Fin v, binaryWordHasseSyndromeExecutable word row.val = 0

theorem hassePairing_eq_sum_syndromes
    (n v : ℕ) (message : Fin v → F2) (word : Fin n → F2) :
    hassePairing n v message word =
      ∑ row, message row * binaryWordHasseSyndromeExecutable word row.val := by
  classical
  simp only [hassePairing, hasseDualWord, binaryWordHasseSyndromeExecutable]
  calc
    (∑ coordinate, (∑ row, (coordinate.val.choose row.val : F2) * message row) *
        word coordinate) =
        ∑ coordinate, ∑ row,
          message row * ((coordinate.val.choose row.val : F2) * word coordinate) := by
      apply Finset.sum_congr rfl
      intro coordinate _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro row _
      ring
    _ = ∑ row, ∑ coordinate,
          message row * ((coordinate.val.choose row.val : F2) * word coordinate) := by
      rw [Finset.sum_comm]
    _ = ∑ row, message row *
          ∑ coordinate, (coordinate.val.choose row.val : F2) * word coordinate := by
      apply Finset.sum_congr rfl
      intro row _
      rw [Finset.mul_sum]

set_option maxHeartbeats 800000 in
theorem sum_f2Sign_hassePairing
    (n v : ℕ) (word : Fin n → F2) :
    (∑ message : Fin v → F2, f2Sign (hassePairing n v message word)) =
      if IsInHasseKernel n v word then (2 : ℝ) ^ v else 0 := by
  classical
  calc
    (∑ message : Fin v → F2, f2Sign (hassePairing n v message word)) =
        ∑ message : Fin v → F2,
          ∏ row : Fin v,
            f2Sign (message row * binaryWordHasseSyndromeExecutable word row.val) := by
      apply Finset.sum_congr rfl
      intro message _
      rw [hassePairing_eq_sum_syndromes]
      simpa using f2Sign_sum Finset.univ
        (fun row : Fin v ↦
          message row * binaryWordHasseSyndromeExecutable word row.val)
    _ = ∏ row : Fin v, ∑ bit : F2,
          f2Sign (bit * binaryWordHasseSyndromeExecutable word row.val) := by
      exact sum_pi_prod_eq_prod_sum_real (fun _row : Fin v ↦ F2)
        (fun row bit ↦
          f2Sign (bit * binaryWordHasseSyndromeExecutable word row.val))
    _ = if IsInHasseKernel n v word then (2 : ℝ) ^ v else 0 := by
      by_cases hkernel : IsInHasseKernel n v word
      · rw [if_pos hkernel]
        have hzero : ∀ row : Fin v,
            binaryWordHasseSyndromeExecutable word row.val = 0 := hkernel
        simp [hzero]
      · rw [if_neg hkernel]
        simp only [IsInHasseKernel] at hkernel
        push Not at hkernel
        obtain ⟨row, hrow⟩ := hkernel
        apply Finset.prod_eq_zero (Finset.mem_univ row)
        rw [← (finTwoEquivF2.sum_comp
          (fun bit ↦ f2Sign
            (bit * binaryWordHasseSyndromeExecutable word row.val)))]
        rw [Fin.sum_univ_two]
        have hone : binaryWordHasseSyndromeExecutable word row.val = 1 := by
          generalize hvalue : binaryWordHasseSyndromeExecutable word row.val = value at hrow ⊢
          fin_cases value
          · exact (hrow rfl).elim
          · rfl
        simp [hone]

theorem hasseKernel_indicator_eq_fourier
    (n v : ℕ) (word : Fin n → F2) :
    (if IsInHasseKernel n v word then (1 : ℝ) else 0) =
      ((2 : ℝ) ^ v)⁻¹ *
        ∑ message : Fin v → F2, f2Sign (hassePairing n v message word) := by
  rw [sum_f2Sign_hassePairing]
  by_cases hkernel : IsInHasseKernel n v word
  · simp [hkernel]
  · simp [hkernel]

set_option maxHeartbeats 800000 in
theorem biasedWord_fourierExpectation
    (n v : ℕ) (beta : ℝ) (message : Fin v → F2) :
    (∑ word : Fin n → F2,
        biasedWordMass n beta word * f2Sign (hassePairing n v message word)) =
      beta ^ (wordSupport (hasseDualWord n v message)).card := by
  classical
  calc
    (∑ word : Fin n → F2,
        biasedWordMass n beta word * f2Sign (hassePairing n v message word)) =
        ∑ word : Fin n → F2,
          ∏ coordinate : Fin n,
            (biasedBitMass beta (word coordinate) *
              f2Sign (hasseDualWord n v message coordinate * word coordinate)) := by
      apply Finset.sum_congr rfl
      intro word _
      rw [biasedWordMass, hassePairing]
      rw [show f2Sign
          (∑ coordinate, hasseDualWord n v message coordinate * word coordinate) =
          ∏ coordinate,
            f2Sign (hasseDualWord n v message coordinate * word coordinate) by
        simpa using f2Sign_sum Finset.univ
          (fun coordinate : Fin n ↦
            hasseDualWord n v message coordinate * word coordinate)]
      rw [← Finset.prod_mul_distrib]
    _ = ∏ coordinate : Fin n, ∑ bit : F2,
          biasedBitMass beta bit *
            f2Sign (hasseDualWord n v message coordinate * bit) := by
      exact sum_pi_prod_eq_prod_sum_real (fun _coordinate : Fin n ↦ F2)
        (fun coordinate bit ↦
          biasedBitMass beta bit *
            f2Sign (hasseDualWord n v message coordinate * bit))
    _ = ∏ coordinate : Fin n,
          if hasseDualWord n v message coordinate = 0 then 1 else beta := by
      apply Finset.prod_congr rfl
      intro coordinate _
      exact sum_biasedBitMass_mul_sign_mul beta
        (hasseDualWord n v message coordinate)
    _ = beta ^ (wordSupport (hasseDualWord n v message)).card := by
      rw [pow_card_wordSupport_eq_prod]

/-- Exact probability mass of the native Hasse kernel under an IID biased-bit word. -/
def hasseKernelMass (n v : ℕ) (beta : ℝ) : ℝ :=
  ∑ word : Fin n → F2,
    if IsInHasseKernel n v word then biasedWordMass n beta word else 0

/-- Exact row-space weight enumerator evaluated at `beta`. -/
def hasseWeightEnumeratorValue (n v : ℕ) (beta : ℝ) : ℝ :=
  ∑ message : Fin v → F2,
    beta ^ (wordSupport (hasseDualWord n v message)).card

/-- Exact finite Fourier formula for the native Hasse constraints. -/
theorem hasseKernelMass_eq_weightEnumerator
    (n v : ℕ) (beta : ℝ) :
    hasseKernelMass n v beta =
      ((2 : ℝ) ^ v)⁻¹ * hasseWeightEnumeratorValue n v beta := by
  classical
  simp only [hasseKernelMass, hasseWeightEnumeratorValue]
  calc
    (∑ word : Fin n → F2,
        if IsInHasseKernel n v word then biasedWordMass n beta word else 0) =
        ∑ word : Fin n → F2,
          (if IsInHasseKernel n v word then (1 : ℝ) else 0) *
            biasedWordMass n beta word := by
      apply Finset.sum_congr rfl
      intro word _
      split <;> simp_all
    _ = ∑ word : Fin n → F2,
          (((2 : ℝ) ^ v)⁻¹ *
            ∑ message : Fin v → F2,
              f2Sign (hassePairing n v message word)) *
            biasedWordMass n beta word := by
      apply Finset.sum_congr rfl
      intro word _
      rw [hasseKernel_indicator_eq_fourier]
    _ = ((2 : ℝ) ^ v)⁻¹ *
          ∑ message : Fin v → F2,
            ∑ word : Fin n → F2,
              biasedWordMass n beta word *
                f2Sign (hassePairing n v message word) := by
      simp_rw [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro message _
      apply Finset.sum_congr rfl
      intro word _
      ring
    _ = ((2 : ℝ) ^ v)⁻¹ *
          ∑ message : Fin v → F2,
            beta ^ (wordSupport (hasseDualWord n v message)).card := by
      congr 1
      apply Finset.sum_congr rfl
      intro message _
      exact biasedWord_fourierExpectation n v beta message

/-- Exact IID divisibility mass after the common coefficient factor `2^e` has probability `p`
and the conditional parity bit has bias `beta`. -/
def exactHasseDivisibilityMass (n v : ℕ) (p beta : ℝ) : ℝ :=
  p ^ n * hasseKernelMass n v beta

theorem exactHasseDivisibilityMass_eq
    (n v : ℕ) (p beta : ℝ) :
    exactHasseDivisibilityMass n v p beta =
      p ^ n * ((2 : ℝ) ^ v)⁻¹ * hasseWeightEnumeratorValue n v beta := by
  rw [exactHasseDivisibilityMass, hasseKernelMass_eq_weightEnumerator]
  ring

/-- Ambient-normalized local collision factor. -/
def exactNormalizedLocalFactor
    (e n v : ℕ) (p beta : ℝ) : ℝ :=
  (2 : ℝ) ^ (e * n + v) * exactHasseDivisibilityMass n v p beta

theorem exactNormalizedLocalFactor_eq
    (e n v : ℕ) (p beta : ℝ) :
    exactNormalizedLocalFactor e n v p beta =
      ((2 : ℝ) ^ e * p) ^ n * hasseWeightEnumeratorValue n v beta := by
  rw [exactNormalizedLocalFactor, exactHasseDivisibilityMass_eq]
  have htwo : (2 : ℝ) ^ v ≠ 0 := by positivity
  rw [show e * n + v = e * n + v by rfl, pow_add, mul_assoc]
  field_simp
  rw [mul_pow, ← pow_mul]
  ring

/-- The exact Hasse correction is bounded by the two-level product certificate. -/
theorem exactNormalizedLocalFactor_le_twoLevelProduct
    (e n v : ℕ) (hv : v ≤ n) (p pNext beta : ℝ)
    (hp : 0 ≤ p) (hbetaZero : 0 ≤ beta) (hbetaOne : beta ≤ 1)
    (hpNext : pNext = p * ((1 + beta) / 2)) :
    exactNormalizedLocalFactor e n v p beta ≤
      ((2 : ℝ) ^ e * p) ^ (n - v) *
        ((2 : ℝ) ^ (e + 1) * pNext) ^ v := by
  rw [exactNormalizedLocalFactor, exactHasseDivisibilityMass_eq]
  have hbase := iidHasseEnumerator_le_twoLevelProduct
    n v hv p pNext beta hp hbetaZero hbetaOne hpNext
  have hnonneg : 0 ≤ (2 : ℝ) ^ (e * n + v) := by positivity
  calc
    (2 : ℝ) ^ (e * n + v) *
        (p ^ n * ((2 : ℝ) ^ v)⁻¹ * hasseWeightEnumeratorValue n v beta) =
        (2 : ℝ) ^ (e * n + v) *
          (p ^ n * (2 : ℝ)⁻¹ ^ v *
            ∑ message : Fin v → F2,
              beta ^ (wordSupport (hasseDualWord n v message)).card) := by
      congr 2
      rw [inv_pow]
    _ ≤ (2 : ℝ) ^ (e * n + v) * (p ^ (n - v) * pNext ^ v) :=
      mul_le_mul_of_nonneg_left hbase hnonneg
    _ = ((2 : ℝ) ^ e * p) ^ (n - v) *
          ((2 : ℝ) ^ (e + 1) * pNext) ^ v :=
      twoLevel_normalizedFactor_identity e n v hv p pNext

/-! ## Lucas block identities and recursive evaluator -/

/-- Lucas' upper-half identity below the power-of-two boundary. -/
theorem choose_pow_add_cast_f2_of_lt
    (d coordinate row : ℕ) (hrow : row < 2 ^ d) :
    (((2 ^ d + coordinate).choose row : ℕ) : F2) =
      (coordinate.choose row : F2) := by
  let N := 2 ^ d
  let p : F2[X] := (X + 1) ^ coordinate
  have hfresh : (X + 1 : F2[X]) ^ N = X ^ N + 1 := by
    dsimp [N]
    simpa using (add_pow_char_pow (X : F2[X]) 1 2 d)
  have hpoly : (X + 1 : F2[X]) ^ (N + coordinate) =
      (X ^ N + 1) * p := by
    rw [pow_add, hfresh]
  calc
    (((2 ^ d + coordinate).choose row : ℕ) : F2) =
        ((X + 1 : F2[X]) ^ (N + coordinate)).coeff row := by
      rw [Polynomial.coeff_X_add_one_pow]
    _ = ((X ^ N + 1) * p).coeff row := by rw [hpoly]
    _ = p.coeff row := by
      rw [add_mul, one_mul, Polynomial.coeff_add,
        Polynomial.coeff_X_pow_mul']
      simp [N, Nat.not_le.mpr hrow]
    _ = (coordinate.choose row : F2) := by
      simp [p, Polynomial.coeff_X_add_one_pow]

/-- Lucas' upper-right block identity at a power-of-two boundary. -/
theorem choose_pow_add_pow_add_cast_f2
    (d coordinate row : ℕ) (hcoordinate : coordinate < 2 ^ d) :
    (((2 ^ d + coordinate).choose (2 ^ d + row) : ℕ) : F2) =
      (coordinate.choose row : F2) := by
  let N := 2 ^ d
  let p : F2[X] := (X + 1) ^ coordinate
  have hfresh : (X + 1 : F2[X]) ^ N = X ^ N + 1 := by
    dsimp [N]
    simpa using (add_pow_char_pow (X : F2[X]) 1 2 d)
  have hpoly : (X + 1 : F2[X]) ^ (N + coordinate) =
      (X ^ N + 1) * p := by
    rw [pow_add, hfresh]
  have hcoefficientZero : p.coeff (N + row) = 0 := by
    rw [show p.coeff (N + row) = (coordinate.choose (N + row) : F2) by
      simp [p, Polynomial.coeff_X_add_one_pow]]
    rw [Nat.choose_eq_zero_of_lt (by omega)]
    rfl
  calc
    (((2 ^ d + coordinate).choose (2 ^ d + row) : ℕ) : F2) =
        ((X + 1 : F2[X]) ^ (N + coordinate)).coeff (N + row) := by
      rw [Polynomial.coeff_X_add_one_pow]
    _ = ((X ^ N + 1) * p).coeff (N + row) := by rw [hpoly]
    _ = p.coeff row + p.coeff (N + row) := by
      rw [add_mul, one_mul, Polynomial.coeff_add]
      congr 1
      simp [Nat.add_comm, Polynomial.coeff_X_pow_mul]
    _ = p.coeff row := by rw [hcoefficientZero, add_zero]
    _ = (coordinate.choose row : F2) := by
      simp [p, Polynomial.coeff_X_add_one_pow]

/-- The lower-left Pascal block vanishes for rows across the boundary. -/
theorem choose_cast_f2_eq_zero_of_lt_pow
    (d coordinate row : ℕ) (hcoordinate : coordinate < 2 ^ d) :
    (coordinate.choose (2 ^ d + row) : F2) = 0 := by
  rw [Nat.choose_eq_zero_of_lt (by omega)]
  rfl

/-- Split a finite sum at an additive boundary. -/
theorem sum_fin_add
    {m n : ℕ} {M : Type} [AddCommMonoid M] (value : Fin (m + n) → M) :
    (∑ index, value index) =
      (∑ index : Fin m, value (Fin.castAdd n index)) +
        ∑ index : Fin n, value (Fin.natAdd m index) := by
  calc
    (∑ index, value index) =
        ∑ index : Fin m ⊕ Fin n, value (finSumFinEquiv index) := by
      exact (finSumFinEquiv.sum_comp value).symm
    _ = _ := by
      rw [Fintype.sum_sum_type]
      simp

/-- The first half of a low-row Hasse word is the smaller Hasse word. -/
theorem hasseDualWord_low_left
    (d v : ℕ) (message : Fin v → F2) (coordinate : Fin (2 ^ d)) :
    hasseDualWord (2 ^ d + 2 ^ d) v message
        (Fin.castAdd (2 ^ d) coordinate) =
      hasseDualWord (2 ^ d) v message coordinate := by
  simp [hasseDualWord]

/-- For `v ≤ 2^d`, the second half of a low-row Hasse word repeats the first half. -/
theorem hasseDualWord_low_right
    (d v : ℕ) (hv : v ≤ 2 ^ d) (message : Fin v → F2)
    (coordinate : Fin (2 ^ d)) :
    hasseDualWord (2 ^ d + 2 ^ d) v message
        (Fin.natAdd (2 ^ d) coordinate) =
      hasseDualWord (2 ^ d) v message coordinate := by
  unfold hasseDualWord
  apply Finset.sum_congr rfl
  intro row _
  rw [show (Fin.natAdd (2 ^ d) coordinate).val = 2 ^ d + coordinate.val by rfl,
    choose_pow_add_cast_f2_of_lt d coordinate.val row.val (by omega)]

/-- Lucas' low-row block is the duplicated smaller Hasse word. -/
theorem hasseDualWord_low_eq_append
    (d v : ℕ) (hv : v ≤ 2 ^ d) (message : Fin v → F2) :
    hasseDualWord (2 ^ d + 2 ^ d) v message =
      Fin.append (hasseDualWord (2 ^ d) v message)
        (hasseDualWord (2 ^ d) v message) := by
  funext coordinate
  refine Fin.addCases ?_ ?_ coordinate
  · intro left
    rw [Fin.append_left, hasseDualWord_low_left]
  · intro right
    rw [Fin.append_right, hasseDualWord_low_right d v hv]

/-- On the first coordinate half, the upper Pascal rows vanish. -/
theorem hasseDualWord_high_left
    (d w : ℕ) (lower : Fin (2 ^ d) → F2) (upper : Fin w → F2)
    (coordinate : Fin (2 ^ d)) :
    hasseDualWord (2 ^ d + 2 ^ d) (2 ^ d + w) (Fin.append lower upper)
        (Fin.castAdd (2 ^ d) coordinate) =
      hasseDualWord (2 ^ d) (2 ^ d) lower coordinate := by
  unfold hasseDualWord
  rw [sum_fin_add]
  have hupper : (∑ row : Fin w,
      ((Fin.castAdd (2 ^ d) coordinate).val.choose
        (Fin.natAdd (2 ^ d) row).val : F2) *
          Fin.append lower upper (Fin.natAdd (2 ^ d) row)) = 0 := by
    apply Finset.sum_eq_zero
    intro row _
    rw [show (Fin.castAdd (2 ^ d) coordinate).val = coordinate.val by rfl,
      show (Fin.natAdd (2 ^ d) row).val = 2 ^ d + row.val by rfl,
      choose_cast_f2_eq_zero_of_lt_pow d coordinate.val row.val coordinate.isLt,
      zero_mul]
  rw [hupper, add_zero]
  apply Finset.sum_congr rfl
  intro row _
  simp

/-- On the second coordinate half, the full lower block and the smaller upper block add. -/
theorem hasseDualWord_high_right
    (d w : ℕ) (lower : Fin (2 ^ d) → F2) (upper : Fin w → F2)
    (coordinate : Fin (2 ^ d)) :
    hasseDualWord (2 ^ d + 2 ^ d) (2 ^ d + w) (Fin.append lower upper)
        (Fin.natAdd (2 ^ d) coordinate) =
      hasseDualWord (2 ^ d) (2 ^ d) lower coordinate +
        hasseDualWord (2 ^ d) w upper coordinate := by
  unfold hasseDualWord
  rw [sum_fin_add]
  congr 1
  · apply Finset.sum_congr rfl
    intro row _
    rw [Fin.append_left]
    change (((2 ^ d + coordinate.val).choose row.val : ℕ) : F2) * lower row =
      (coordinate.val.choose row.val : F2) * lower row
    rw [choose_pow_add_cast_f2_of_lt d coordinate.val row.val row.isLt]
  · apply Finset.sum_congr rfl
    intro row _
    rw [show (Fin.natAdd (2 ^ d) coordinate).val = 2 ^ d + coordinate.val by rfl,
      show (Fin.natAdd (2 ^ d) row).val = 2 ^ d + row.val by rfl,
      choose_pow_add_pow_add_cast_f2 d coordinate.val row.val coordinate.isLt]
    simp

/-- Lucas' high-row block has Plotkin form `(x, x + y)`. -/
theorem hasseDualWord_high_eq_append
    (d w : ℕ) (lower : Fin (2 ^ d) → F2) (upper : Fin w → F2) :
    hasseDualWord (2 ^ d + 2 ^ d) (2 ^ d + w) (Fin.append lower upper) =
      Fin.append (hasseDualWord (2 ^ d) (2 ^ d) lower)
        (fun coordinate ↦ hasseDualWord (2 ^ d) (2 ^ d) lower coordinate +
          hasseDualWord (2 ^ d) w upper coordinate) := by
  funext coordinate
  refine Fin.addCases ?_ ?_ coordinate
  · intro left
    rw [Fin.append_left, hasseDualWord_high_left]
  · intro right
    rw [Fin.append_right, hasseDualWord_high_right]

/-- Indicator-sum presentation of binary Hamming weight. -/
def binaryHammingWeight {n : ℕ} (word : Fin n → F2) : ℕ :=
  ∑ coordinate, if word coordinate = 0 then 0 else 1

/-- Hamming contribution of one binary coordinate. -/
def f2BitWeight (bit : F2) : ℕ := if bit = 0 then 0 else 1

theorem binaryHammingWeight_eq_sum_bitWeight
    {n : ℕ} (word : Fin n → F2) :
    binaryHammingWeight word = ∑ coordinate, f2BitWeight (word coordinate) := by
  rfl

theorem binaryHammingWeight_eq_card_wordSupport
    {n : ℕ} (word : Fin n → F2) :
    binaryHammingWeight word = (wordSupport word).card := by
  classical
  unfold binaryHammingWeight wordSupport
  rw [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro coordinate _
  by_cases hzero : word coordinate = 0 <;> simp [hzero]

theorem binaryHammingWeight_append
    {m n : ℕ} (left : Fin m → F2) (right : Fin n → F2) :
    binaryHammingWeight (Fin.append left right) =
      binaryHammingWeight left + binaryHammingWeight right := by
  unfold binaryHammingWeight
  rw [sum_fin_add]
  simp

theorem card_wordSupport_append
    {m n : ℕ} (left : Fin m → F2) (right : Fin n → F2) :
    (wordSupport (Fin.append left right)).card =
      (wordSupport left).card + (wordSupport right).card := by
  rw [← binaryHammingWeight_eq_card_wordSupport,
    binaryHammingWeight_append,
    binaryHammingWeight_eq_card_wordSupport,
    binaryHammingWeight_eq_card_wordSupport]

/-- The zero-row code has enumerator one. -/
@[simp]
theorem hasseWeightEnumeratorValue_zero (n : ℕ) (beta : ℝ) :
    hasseWeightEnumeratorValue n 0 beta = 1 := by
  simp [hasseWeightEnumeratorValue, hasseDualWord, wordSupport]

/-- First nontrivial base case of the Pascal recursion. -/
theorem hasseWeightEnumeratorValue_one_one (beta : ℝ) :
    hasseWeightEnumeratorValue 1 1 beta = 1 + beta := by
  have hidentity : ∀ message : Fin 1 → F2,
      hasseDualWord 1 1 message = message := by
    intro message
    funext coordinate
    fin_cases coordinate
    simp [hasseDualWord]
  unfold hasseWeightEnumeratorValue
  simp_rw [hidentity]
  simpa using sum_pow_card_wordSupport_f2 (Fin 1) beta

/-- Exact low-row Lucas recurrence. -/
theorem hasseWeightEnumeratorValue_low
    (d v : ℕ) (hv : v ≤ 2 ^ d) (beta : ℝ) :
    hasseWeightEnumeratorValue (2 ^ d + 2 ^ d) v beta =
      hasseWeightEnumeratorValue (2 ^ d) v (beta ^ 2) := by
  unfold hasseWeightEnumeratorValue
  apply Finset.sum_congr rfl
  intro message _
  rw [hasseDualWord_low_eq_append d v hv,
    card_wordSupport_append]
  rw [show (wordSupport (hasseDualWord (2 ^ d) v message)).card +
      (wordSupport (hasseDualWord (2 ^ d) v message)).card =
        2 * (wordSupport (hasseDualWord (2 ^ d) v message)).card by omega,
    pow_mul]

/-- One-coordinate Plotkin sum. -/
theorem sum_pow_plotkinBitWeight (beta : ℝ) (shift : F2) :
    (∑ bit : F2,
        beta ^ (f2BitWeight bit + f2BitWeight (bit + shift))) =
      if shift = 0 then 1 + beta ^ 2 else 2 * beta := by
  rw [← (finTwoEquivF2.sum_comp
    (fun bit ↦ beta ^ (f2BitWeight bit + f2BitWeight (bit + shift))))]
  rw [Fin.sum_univ_two]
  by_cases hzero : shift = 0
  · subst shift
    simp [f2BitWeight]
  · have hone : shift = 1 := by
      fin_cases shift
      · exact (hzero rfl).elim
      · rfl
    subst shift
    have hadd : (1 : F2) + 1 = 0 := by decide
    simp [f2BitWeight, hadd]
    ring

/-- Product of a two-valued coordinate statistic, grouped by support. -/
theorem prod_if_f2_zero
    {n : ℕ} (word : Fin n → F2) (zeroValue nonzeroValue : ℝ) :
    (∏ coordinate, if word coordinate = 0 then zeroValue else nonzeroValue) =
      zeroValue ^ (n - (wordSupport word).card) *
        nonzeroValue ^ (wordSupport word).card := by
  classical
  rw [Finset.prod_ite]
  simp only [Finset.prod_const]
  have hnonzero :
      {coordinate ∈ (Finset.univ : Finset (Fin n)) | ¬ word coordinate = 0} =
        wordSupport word := by
    ext coordinate
    simp [wordSupport]
  rw [hnonzero]
  congr 2
  have hcard := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset (Fin n)))
    (fun coordinate ↦ word coordinate = 0)
  simp only [Finset.card_univ, Fintype.card_fin] at hcard
  rw [hnonzero] at hcard
  omega

theorem card_wordSupport_plotkin
    {n : ℕ} (word shift : Fin n → F2) :
    (wordSupport
        (Fin.append word (fun coordinate ↦ word coordinate + shift coordinate))).card =
      ∑ coordinate,
        (f2BitWeight (word coordinate) +
          f2BitWeight (word coordinate + shift coordinate)) := by
  calc
    _ = binaryHammingWeight
        (Fin.append word (fun coordinate ↦ word coordinate + shift coordinate)) :=
      (binaryHammingWeight_eq_card_wordSupport _).symm
    _ = binaryHammingWeight word +
        binaryHammingWeight (fun coordinate ↦ word coordinate + shift coordinate) :=
      binaryHammingWeight_append _ _
    _ = (∑ coordinate, f2BitWeight (word coordinate)) +
        ∑ coordinate, f2BitWeight (word coordinate + shift coordinate) := by
      rw [binaryHammingWeight_eq_sum_bitWeight,
        binaryHammingWeight_eq_sum_bitWeight]
    _ = _ := by rw [← Finset.sum_add_distrib]

/-- Exact sum over the free word in the Plotkin block `(x,x+y)`. -/
theorem sum_pow_card_wordSupport_plotkin
    (n : ℕ) (beta : ℝ) (shift : Fin n → F2) :
    (∑ word : Fin n → F2,
        beta ^ (wordSupport
          (Fin.append word
            (fun coordinate ↦ word coordinate + shift coordinate))).card) =
      (1 + beta ^ 2) ^ (n - (wordSupport shift).card) *
        (2 * beta) ^ (wordSupport shift).card := by
  classical
  calc
    _ = ∑ word : Fin n → F2,
        ∏ coordinate,
          beta ^ (f2BitWeight (word coordinate) +
            f2BitWeight (word coordinate + shift coordinate)) := by
      apply Finset.sum_congr rfl
      intro word _
      rw [card_wordSupport_plotkin]
      exact (Finset.prod_pow_eq_pow_sum Finset.univ
        (fun coordinate ↦ f2BitWeight (word coordinate) +
          f2BitWeight (word coordinate + shift coordinate)) beta).symm
    _ = ∏ coordinate : Fin n, ∑ bit : F2,
          beta ^ (f2BitWeight bit + f2BitWeight (bit + shift coordinate)) := by
      exact sum_pi_prod_eq_prod_sum_real (fun _coordinate : Fin n ↦ F2)
        (fun coordinate bit ↦
          beta ^ (f2BitWeight bit + f2BitWeight (bit + shift coordinate)))
    _ = ∏ coordinate : Fin n,
          if shift coordinate = 0 then 1 + beta ^ 2 else 2 * beta := by
      apply Finset.prod_congr rfl
      intro coordinate _
      exact sum_pow_plotkinBitWeight beta (shift coordinate)
    _ = _ := prod_if_f2_zero shift (1 + beta ^ 2) (2 * beta)

theorem hasseInformationEquiv_apply_full
    (n : ℕ) (message : Fin n → F2) :
    hasseInformationEquiv n n le_rfl message =
      hasseDualWord n n message := by
  change hasseInformationProjection n n le_rfl message = _
  funext coordinate
  simp [hasseInformationProjection]

/-- Plotkin form of the high-row enumerator, before extracting the common power. -/
theorem hasseWeightEnumeratorValue_high_raw
    (d w : ℕ) (beta : ℝ) :
    hasseWeightEnumeratorValue (2 ^ d + 2 ^ d) (2 ^ d + w) beta =
      ∑ upper : Fin w → F2,
        (1 + beta ^ 2) ^
            (2 ^ d - (wordSupport (hasseDualWord (2 ^ d) w upper)).card) *
          (2 * beta) ^
            (wordSupport (hasseDualWord (2 ^ d) w upper)).card := by
  classical
  let N := 2 ^ d
  let split : (Fin N → F2) × (Fin w → F2) ≃
      (Fin (N + w) → F2) := Fin.appendEquiv N w
  unfold hasseWeightEnumeratorValue
  calc
    (∑ message : Fin (N + w) → F2,
        beta ^ (wordSupport (hasseDualWord (N + N) (N + w) message)).card) =
        ∑ pair : (Fin N → F2) × (Fin w → F2),
          beta ^ (wordSupport
            (hasseDualWord (N + N) (N + w) (split pair))).card := by
      exact (split.sum_comp (fun message ↦
        beta ^ (wordSupport
          (hasseDualWord (N + N) (N + w) message)).card)).symm
    _ = ∑ upper : Fin w → F2, ∑ lower : Fin N → F2,
          beta ^ (wordSupport
            (Fin.append (hasseDualWord N N lower)
              (fun coordinate ↦ hasseDualWord N N lower coordinate +
                hasseDualWord N w upper coordinate))).card := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro upper _
      apply Finset.sum_congr rfl
      intro lower _
      dsimp [split, N]
      have hsplit : (Fin.appendEquiv (2 ^ d) w) (lower, upper) =
          Fin.append lower upper := by
        funext coordinate
        rw [Fin.appendEquiv_apply]
      rw [hsplit, hasseDualWord_high_eq_append]
    _ = ∑ upper : Fin w → F2, ∑ word : Fin N → F2,
          beta ^ (wordSupport
            (Fin.append word
              (fun coordinate ↦ word coordinate +
                hasseDualWord N w upper coordinate))).card := by
      apply Finset.sum_congr rfl
      intro upper _
      let full : (Fin N → F2) ≃ (Fin N → F2) :=
        hasseInformationEquiv N N le_rfl
      calc
        (∑ lower : Fin N → F2,
          beta ^ (wordSupport
            (Fin.append (hasseDualWord N N lower)
              (fun coordinate ↦ hasseDualWord N N lower coordinate +
                hasseDualWord N w upper coordinate))).card) =
            ∑ lower : Fin N → F2,
              beta ^ (wordSupport
                (Fin.append (full lower)
                  (fun coordinate ↦ full lower coordinate +
                    hasseDualWord N w upper coordinate))).card := by
          apply Finset.sum_congr rfl
          intro lower _
          rw [show full lower = hasseDualWord N N lower by
            exact hasseInformationEquiv_apply_full N lower]
        _ = _ := full.sum_comp (fun word ↦
          beta ^ (wordSupport
            (Fin.append word
              (fun coordinate ↦ word coordinate +
                hasseDualWord N w upper coordinate))).card)
    _ = ∑ upper : Fin w → F2,
        (1 + beta ^ 2) ^
            (N - (wordSupport (hasseDualWord N w upper)).card) *
          (2 * beta) ^ (wordSupport (hasseDualWord N w upper)).card := by
      apply Finset.sum_congr rfl
      intro upper _
      exact sum_pow_card_wordSupport_plotkin N beta
        (hasseDualWord N w upper)

theorem pow_sub_mul_pow_eq_pow_mul_div_pow
    (base value : ℝ) (hbase : base ≠ 0) (length weight : ℕ)
    (hweight : weight ≤ length) :
    base ^ (length - weight) * value ^ weight =
      base ^ length * (value / base) ^ weight := by
  rw [div_pow]
  field_simp
  calc
    base ^ (length - weight) * value ^ weight * base ^ weight =
        (base ^ (length - weight) * base ^ weight) * value ^ weight := by ring
    _ = base ^ length * value ^ weight := by
      rw [← pow_add, Nat.sub_add_cancel hweight]
    _ = value ^ weight * base ^ length := by ring

/-- Exact high-row Lucas recurrence. -/
theorem hasseWeightEnumeratorValue_high
    (d w : ℕ) (beta : ℝ) :
    hasseWeightEnumeratorValue (2 ^ d + 2 ^ d) (2 ^ d + w) beta =
      (1 + beta ^ 2) ^ (2 ^ d) *
        hasseWeightEnumeratorValue (2 ^ d) w
          ((2 * beta) / (1 + beta ^ 2)) := by
  rw [hasseWeightEnumeratorValue_high_raw]
  unfold hasseWeightEnumeratorValue
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro upper _
  rw [pow_sub_mul_pow_eq_pow_mul_div_pow]
  · exact ne_of_gt (by positivity)
  · simpa using Finset.card_le_univ
      (wordSupport (hasseDualWord (2 ^ d) w upper))

/-- Logarithmic-depth exact evaluator furnished by the Lucas recurrences.  Instantiating
`Scalar = ℚ` gives the certificate arithmetic used by the parameter tool. -/
def lucasHasseWeightEvaluator
    {Scalar : Type} [Field Scalar] : ℕ → ℕ → Scalar → Scalar
  | 0, v, point => if v = 0 then 1 else 1 + point
  | d + 1, v, point =>
      let half := 2 ^ d
      if v ≤ half then
        lucasHasseWeightEvaluator d v (point ^ 2)
      else
        (1 + point ^ 2) ^ half *
          lucasHasseWeightEvaluator d (v - half)
            ((2 * point) / (1 + point ^ 2))

@[simp]
theorem lucasHasseWeightEvaluator_zero_zero
    {Scalar : Type} [Field Scalar] (point : Scalar) :
    lucasHasseWeightEvaluator 0 0 point = 1 := by
  simp [lucasHasseWeightEvaluator]

@[simp]
theorem lucasHasseWeightEvaluator_zero_one
    {Scalar : Type} [Field Scalar] (point : Scalar) :
    lucasHasseWeightEvaluator 0 1 point = 1 + point := by
  simp [lucasHasseWeightEvaluator]

theorem lucasHasseWeightEvaluator_succ_low
    {Scalar : Type} [Field Scalar]
    (d v : ℕ) (point : Scalar) (hv : v ≤ 2 ^ d) :
    lucasHasseWeightEvaluator (d + 1) v point =
      lucasHasseWeightEvaluator d v (point ^ 2) := by
  simp [lucasHasseWeightEvaluator, hv]

theorem lucasHasseWeightEvaluator_succ_high
    {Scalar : Type} [Field Scalar]
    (d v : ℕ) (point : Scalar) (hv : ¬v ≤ 2 ^ d) :
    lucasHasseWeightEvaluator (d + 1) v point =
      (1 + point ^ 2) ^ (2 ^ d) *
        lucasHasseWeightEvaluator d (v - 2 ^ d)
          ((2 * point) / (1 + point ^ 2)) := by
  simp [lucasHasseWeightEvaluator, hv]

/-- Soundness of the logarithmic evaluator against the native Hasse row-space sum. -/
theorem lucasHasseWeightEvaluator_real_eq
    (d v : ℕ) (hv : v ≤ 2 ^ d) (point : ℝ) :
    lucasHasseWeightEvaluator d v point =
      hasseWeightEnumeratorValue (2 ^ d) v point := by
  induction d generalizing v point with
  | zero =>
      have hvCases : v = 0 ∨ v = 1 := by omega
      rcases hvCases with rfl | rfl
      · simp [hasseWeightEnumeratorValue_zero]
      · rw [lucasHasseWeightEvaluator_zero_one]
        simpa using (hasseWeightEnumeratorValue_one_one point).symm
  | succ d ih =>
      let half := 2 ^ d
      have hlength : 2 ^ (d + 1) = half + half := by
        dsimp [half]
        rw [pow_succ]
        omega
      by_cases hlow : v ≤ half
      · rw [lucasHasseWeightEvaluator_succ_low d v point hlow,
          hlength, hasseWeightEnumeratorValue_low d v (by simpa [half] using hlow)]
        exact ih v (by simpa [half] using hlow) (point ^ 2)
      · have hhigh : half < v := Nat.lt_of_not_ge hlow
        have hremainder : v - half ≤ half := by omega
        have hvSplit : half + (v - half) = v := by omega
        rw [lucasHasseWeightEvaluator_succ_high d v point
            (by simpa [half] using hlow),
          hlength, ← hvSplit,
          hasseWeightEnumeratorValue_high d (v - half)]
        congr 1
        rw [show half + (v - half) - 2 ^ d = v - half by
          simp [half]]
        exact ih (v - half) (by simpa [half] using hremainder)
          ((2 * point) / (1 + point ^ 2))

/-! ## Dual kernel enumerator -/

/-- The complete syndrome vector is multiplication by the transpose Pascal matrix. -/
theorem hasseSyndromeVector_eq_transpose_mulVec
    (n : ℕ) (word : Fin n → F2) :
    (fun row : Fin n ↦ binaryWordHasseSyndromeExecutable word row.val) =
      (hassePascalMatrix n).transpose.mulVec word := by
  funext row
  simp [binaryWordHasseSyndromeExecutable, Matrix.mulVec, dotProduct,
    hassePascalMatrix, Matrix.transpose]

/-- All `n` Hasse checks vanish exactly on the zero word. -/
theorem isInHasseKernel_full_iff
    (n : ℕ) (word : Fin n → F2) :
    IsInHasseKernel n n word ↔ word = 0 := by
  constructor
  · intro hkernel
    have hunit : IsUnit (hassePascalMatrix n).transpose :=
      (Matrix.isUnit_transpose (hassePascalMatrix n)).2
        (isUnit_hassePascalMatrix n)
    have hinjective : Function.Injective ((hassePascalMatrix n).transpose.mulVec) :=
      Matrix.mulVec_injective_iff_isUnit.mpr hunit
    apply hinjective
    rw [← hasseSyndromeVector_eq_transpose_mulVec]
    funext row
    simp [hkernel row]
  · rintro rfl
    intro row
    simp [binaryWordHasseSyndromeExecutable]

/-- Low Hasse rows see the XOR of the two coordinate halves. -/
theorem binaryWordHasseSyndrome_append_low
    (d row : ℕ) (hrow : row < 2 ^ d)
    (left right : Fin (2 ^ d) → F2) :
    binaryWordHasseSyndromeExecutable (Fin.append left right) row =
      binaryWordHasseSyndromeExecutable
        (fun coordinate ↦ left coordinate + right coordinate) row := by
  unfold binaryWordHasseSyndromeExecutable
  rw [sum_fin_add, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro coordinate _
  rw [Fin.append_left, Fin.append_right]
  change (coordinate.val.choose row : F2) * left coordinate +
      (((2 ^ d + coordinate.val).choose row : ℕ) : F2) * right coordinate =
    (coordinate.val.choose row : F2) *
      (left coordinate + right coordinate)
  rw [choose_pow_add_cast_f2_of_lt d coordinate.val row hrow]
  ring

/-- A high Hasse row sees only the second coordinate half. -/
theorem binaryWordHasseSyndrome_append_high
    (d row : ℕ) (left right : Fin (2 ^ d) → F2) :
    binaryWordHasseSyndromeExecutable (Fin.append left right) (2 ^ d + row) =
      binaryWordHasseSyndromeExecutable right row := by
  unfold binaryWordHasseSyndromeExecutable
  rw [sum_fin_add]
  have hleft : (∑ coordinate : Fin (2 ^ d),
      ((Fin.castAdd (2 ^ d) coordinate).val.choose (2 ^ d + row) : F2) *
        Fin.append left right (Fin.castAdd (2 ^ d) coordinate)) = 0 := by
    apply Finset.sum_eq_zero
    intro coordinate _
    rw [Fin.append_left]
    change (coordinate.val.choose (2 ^ d + row) : F2) * left coordinate = 0
    rw [choose_cast_f2_eq_zero_of_lt_pow d coordinate.val row coordinate.isLt,
      zero_mul]
  rw [hleft, zero_add]
  apply Finset.sum_congr rfl
  intro coordinate _
  rw [Fin.append_right]
  change ((((2 ^ d + coordinate.val).choose (2 ^ d + row) : ℕ) : F2) *
      right coordinate) =
    (coordinate.val.choose row : F2) * right coordinate
  rw [choose_pow_add_pow_add_cast_f2 d coordinate.val row coordinate.isLt]

/-- Low-row kernel membership depends only on the XOR of the two halves. -/
theorem isInHasseKernel_append_low_iff
    (d v : ℕ) (hv : v ≤ 2 ^ d)
    (left right : Fin (2 ^ d) → F2) :
    IsInHasseKernel (2 ^ d + 2 ^ d) v (Fin.append left right) ↔
      IsInHasseKernel (2 ^ d) v
        (fun coordinate ↦ left coordinate + right coordinate) := by
  constructor <;> intro hkernel row
  · rw [← binaryWordHasseSyndrome_append_low d row.val (by omega)]
    exact hkernel row
  · rw [binaryWordHasseSyndrome_append_low d row.val (by omega)]
    exact hkernel row

theorem f2_add_eq_zero_iff_eq (left right : F2) :
    left + right = 0 ↔ left = right := by
  by_cases hleft : left = 0
  · subst left
    simp [eq_comm]
  by_cases hright : right = 0
  · subst right
    simp [hleft]
  have hleftOne : left = 1 := by
    fin_cases left
    · exact (hleft rfl).elim
    · rfl
  have hrightOne : right = 1 := by
    fin_cases right
    · exact (hright rfl).elim
    · rfl
  subst left
  subst right
  exact ⟨fun _ ↦ rfl, fun _ ↦ by decide⟩

/-- High-row kernel membership forces equal halves and the smaller upper kernel. -/
theorem isInHasseKernel_append_high_iff
    (d w : ℕ) (left right : Fin (2 ^ d) → F2) :
    IsInHasseKernel (2 ^ d + 2 ^ d) (2 ^ d + w) (Fin.append left right) ↔
      left = right ∧ IsInHasseKernel (2 ^ d) w right := by
  constructor
  · intro hkernel
    have hsumKernel : IsInHasseKernel (2 ^ d) (2 ^ d)
        (fun coordinate ↦ left coordinate + right coordinate) := by
      intro row
      rw [← binaryWordHasseSyndrome_append_low d row.val row.isLt]
      exact hkernel (Fin.castAdd w row)
    have hsumZero := (isInHasseKernel_full_iff (2 ^ d) _).mp hsumKernel
    constructor
    · funext coordinate
      have hcoordinate : left coordinate + right coordinate = 0 := by
        simpa using congrFun hsumZero coordinate
      exact (f2_add_eq_zero_iff_eq _ _).mp hcoordinate
    · intro row
      rw [← binaryWordHasseSyndrome_append_high d row.val]
      exact hkernel (Fin.natAdd (2 ^ d) row)
  · rintro ⟨heq, hupper⟩
    subst right
    intro row
    refine Fin.addCases ?_ ?_ row
    · intro low
      change binaryWordHasseSyndromeExecutable (Fin.append left left) low.val = 0
      rw [binaryWordHasseSyndrome_append_low d low.val low.isLt]
      have hzero : (fun coordinate ↦ left coordinate + left coordinate) = 0 := by
        funext coordinate
        exact (f2_add_eq_zero_iff_eq _ _).mpr rfl
      rw [hzero]
      simp [binaryWordHasseSyndromeExecutable]
    · intro high
      change binaryWordHasseSyndromeExecutable (Fin.append left left)
        (2 ^ d + high.val) = 0
      rw [binaryWordHasseSyndrome_append_high d high.val]
      exact hupper high

/-- Ordinary weight enumerator of the Hasse kernel, evaluated at a real point. -/
def hasseKernelWeightEnumeratorValue (n v : ℕ) (point : ℝ) : ℝ :=
  ∑ word : Fin n → F2,
    if IsInHasseKernel n v word then
      point ^ (wordSupport word).card
    else 0

/-- Exact coefficient count of weight-`weight` words in the Hasse kernel. -/
def hasseKernelWeightCount (n v weight : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → F2)).filter fun word ↦
    IsInHasseKernel n v word ∧ (wordSupport word).card = weight).card

/-- Reindex two words by the characteristic-two shear `(left,right) ↦
(left,left+right)`. -/
def f2WordShearEquiv (n : ℕ) :
    (Fin n → F2) × (Fin n → F2) ≃
      (Fin n → F2) × (Fin n → F2) :=
  (Equiv.refl (Fin n → F2)).prodShear
    (fun left ↦ Equiv.addLeft left)

@[simp]
theorem f2WordShearEquiv_apply
    (n : ℕ) (pair : (Fin n → F2) × (Fin n → F2)) :
    f2WordShearEquiv n pair =
      (pair.1, fun coordinate ↦ pair.1 coordinate + pair.2 coordinate) := by
  rfl

@[simp]
theorem finAppendEquiv_apply_pair
    {m n : ℕ} (left : Fin m → F2) (right : Fin n → F2) :
    (Fin.appendEquiv m n) (left, right) = Fin.append left right := by
  funext coordinate
  rw [Fin.appendEquiv_apply]

theorem f2_add_add_self (left right : F2) :
    left + (left + right) = right := by
  rw [← add_assoc]
  have hself : left + left = 0 :=
    (f2_add_eq_zero_iff_eq left left).mpr rfl
  rw [hself, zero_add]

/-- Dual low-row recursion in coefficient-safe (division-free) form. -/
theorem hasseKernelWeightEnumeratorValue_low
    (d v : ℕ) (hv : v ≤ 2 ^ d) (point : ℝ) :
    hasseKernelWeightEnumeratorValue (2 ^ d + 2 ^ d) v point =
      ∑ shift : Fin (2 ^ d) → F2,
        if IsInHasseKernel (2 ^ d) v shift then
          (1 + point ^ 2) ^ (2 ^ d - (wordSupport shift).card) *
            (2 * point) ^ (wordSupport shift).card
        else 0 := by
  classical
  let append : (Fin (2 ^ d) → F2) × (Fin (2 ^ d) → F2) ≃
      (Fin (2 ^ d + 2 ^ d) → F2) := Fin.appendEquiv (2 ^ d) (2 ^ d)
  let shear := f2WordShearEquiv (2 ^ d)
  unfold hasseKernelWeightEnumeratorValue
  calc
    (∑ word : Fin (2 ^ d + 2 ^ d) → F2,
        if IsInHasseKernel (2 ^ d + 2 ^ d) v word then
          point ^ (wordSupport word).card else 0) =
        ∑ pair : (Fin (2 ^ d) → F2) × (Fin (2 ^ d) → F2),
          if IsInHasseKernel (2 ^ d + 2 ^ d) v (append pair) then
            point ^ (wordSupport (append pair)).card else 0 := by
      exact (append.sum_comp (fun word ↦
        if IsInHasseKernel (2 ^ d + 2 ^ d) v word then
          point ^ (wordSupport word).card else 0)).symm
    _ = ∑ pair : (Fin (2 ^ d) → F2) × (Fin (2 ^ d) → F2),
          if IsInHasseKernel (2 ^ d + 2 ^ d) v (append (shear pair)) then
            point ^ (wordSupport (append (shear pair))).card else 0 := by
      exact (shear.sum_comp (fun pair ↦
        if IsInHasseKernel (2 ^ d + 2 ^ d) v (append pair) then
          point ^ (wordSupport (append pair)).card else 0)).symm
    _ = ∑ shift : Fin (2 ^ d) → F2,
          if IsInHasseKernel (2 ^ d) v shift then
            ∑ free : Fin (2 ^ d) → F2,
              point ^ (wordSupport
                (Fin.append free
                  (fun coordinate ↦ free coordinate + shift coordinate))).card
          else 0 := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro shift _
      by_cases hkernel : IsInHasseKernel (2 ^ d) v shift
      · rw [if_pos hkernel]
        apply Finset.sum_congr rfl
        intro free _
        simp only [append, shear, f2WordShearEquiv_apply,
          finAppendEquiv_apply_pair]
        rw [isInHasseKernel_append_low_iff d v hv]
        have hreduce : (fun coordinate ↦
            free coordinate + (free coordinate + shift coordinate)) = shift := by
          funext coordinate
          rw [f2_add_add_self]
        rw [hreduce, if_pos hkernel]
      · rw [if_neg hkernel]
        apply Finset.sum_eq_zero
        intro free _
        simp only [append, shear, f2WordShearEquiv_apply,
          finAppendEquiv_apply_pair]
        rw [isInHasseKernel_append_low_iff d v hv]
        have hreduce : (fun coordinate ↦
            free coordinate + (free coordinate + shift coordinate)) = shift := by
          funext coordinate
          rw [f2_add_add_self]
        rw [hreduce, if_neg hkernel]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro shift _
      by_cases hkernel : IsInHasseKernel (2 ^ d) v shift
      · rw [if_pos hkernel, if_pos hkernel]
        exact sum_pow_card_wordSupport_plotkin (2 ^ d) point shift
      · simp [hkernel]

/-- Closed dual low-row recursion from the note. -/
theorem hasseKernelWeightEnumeratorValue_low_closed
    (d v : ℕ) (hv : v ≤ 2 ^ d) (point : ℝ) :
    hasseKernelWeightEnumeratorValue (2 ^ d + 2 ^ d) v point =
      (1 + point ^ 2) ^ (2 ^ d) *
        hasseKernelWeightEnumeratorValue (2 ^ d) v
          ((2 * point) / (1 + point ^ 2)) := by
  rw [hasseKernelWeightEnumeratorValue_low d v hv]
  unfold hasseKernelWeightEnumeratorValue
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro word _
  by_cases hkernel : IsInHasseKernel (2 ^ d) v word
  · rw [if_pos hkernel, if_pos hkernel,
      pow_sub_mul_pow_eq_pow_mul_div_pow]
    · exact ne_of_gt (by positivity)
    · simpa using Finset.card_le_univ (wordSupport word)
  · simp [hkernel]

/-- Dual high-row recursion: only duplicated smaller-kernel words remain. -/
theorem hasseKernelWeightEnumeratorValue_high
    (d w : ℕ) (point : ℝ) :
    hasseKernelWeightEnumeratorValue (2 ^ d + 2 ^ d) (2 ^ d + w) point =
      hasseKernelWeightEnumeratorValue (2 ^ d) w (point ^ 2) := by
  classical
  let append : (Fin (2 ^ d) → F2) × (Fin (2 ^ d) → F2) ≃
      (Fin (2 ^ d + 2 ^ d) → F2) := Fin.appendEquiv (2 ^ d) (2 ^ d)
  unfold hasseKernelWeightEnumeratorValue
  calc
    (∑ word : Fin (2 ^ d + 2 ^ d) → F2,
        if IsInHasseKernel (2 ^ d + 2 ^ d) (2 ^ d + w) word then
          point ^ (wordSupport word).card else 0) =
        ∑ pair : (Fin (2 ^ d) → F2) × (Fin (2 ^ d) → F2),
          if IsInHasseKernel (2 ^ d + 2 ^ d) (2 ^ d + w) (append pair) then
            point ^ (wordSupport (append pair)).card else 0 := by
      exact (append.sum_comp (fun word ↦
        if IsInHasseKernel (2 ^ d + 2 ^ d) (2 ^ d + w) word then
          point ^ (wordSupport word).card else 0)).symm
    _ = ∑ right : Fin (2 ^ d) → F2,
          if IsInHasseKernel (2 ^ d) w right then
            point ^ (2 * (wordSupport right).card)
          else 0 := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro right _
      by_cases hkernel : IsInHasseKernel (2 ^ d) w right
      · rw [if_pos hkernel]
        rw [Finset.sum_eq_single right]
        · rw [show append (right, right) = Fin.append right right by
              exact finAppendEquiv_apply_pair right right]
          rw [isInHasseKernel_append_high_iff, if_pos ⟨rfl, hkernel⟩,
            card_wordSupport_append]
          congr 1
          omega
        · intro left _ hleft
          rw [show append (left, right) = Fin.append left right by
            exact finAppendEquiv_apply_pair left right]
          rw [isInHasseKernel_append_high_iff]
          simp [hleft, hkernel]
        · simp
      · rw [if_neg hkernel]
        apply Finset.sum_eq_zero
        intro left _
        rw [show append (left, right) = Fin.append left right by
          exact finAppendEquiv_apply_pair left right]
        rw [isInHasseKernel_append_high_iff]
        simp [hkernel]
    _ = ∑ right : Fin (2 ^ d) → F2,
          if IsInHasseKernel (2 ^ d) w right then
            (point ^ 2) ^ (wordSupport right).card
          else 0 := by
      apply Finset.sum_congr rfl
      intro right _
      by_cases hkernel : IsInHasseKernel (2 ^ d) w right
      · rw [if_pos hkernel, if_pos hkernel, pow_mul]
      · simp [hkernel]

theorem isInHasseKernel_iff_le_executableValuation
    (n v : ℕ) (hv : v ≤ n) (word : Fin n → F2) :
    IsInHasseKernel n v word ↔
      v ≤ binaryWordHasseValuationExecutable word := by
  rw [binaryWordHasseValuationExecutable_eq,
    le_hasseValuation_iff_syndromesZeroBelow n (binaryWordPolynomial word) hv]
  constructor
  · intro hkernel row hrow
    rw [← binaryWordHasseSyndromeExecutable_eq]
    exact hkernel ⟨row, hrow⟩
  · intro hzero row
    rw [binaryWordHasseSyndromeExecutable_eq]
    exact hzero row row.isLt

/-- Exact binary weight/valuation stratum. -/
def hasseExactValuationWeightCount (n v weight : ℕ) : ℕ :=
  ((Finset.univ : Finset (Fin n → F2)).filter fun word ↦
    binaryWordHasseValuationExecutable word = v ∧
      (wordSupport word).card = weight).card

/-- Adjacent kernel coefficients count exact Hasse valuation. -/
theorem hasseExactValuationWeightCount_eq_kernel_sub_succ
    (n v weight : ℕ) (hv : v < n) :
    hasseExactValuationWeightCount n v weight =
      hasseKernelWeightCount n v weight -
        hasseKernelWeightCount n (v + 1) weight := by
  classical
  let current : Finset (Fin n → F2) :=
    (Finset.univ.filter fun word ↦
      IsInHasseKernel n v word ∧ (wordSupport word).card = weight)
  let exact : Finset (Fin n → F2) :=
    (Finset.univ.filter fun word ↦
      binaryWordHasseValuationExecutable word = v ∧
        (wordSupport word).card = weight)
  let next : Finset (Fin n → F2) :=
    (Finset.univ.filter fun word ↦
      IsInHasseKernel n (v + 1) word ∧ (wordSupport word).card = weight)
  have hunion : current = exact ∪ next := by
    ext word
    simp only [current, exact, next, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_union]
    rw [isInHasseKernel_iff_le_executableValuation n v hv.le,
      isInHasseKernel_iff_le_executableValuation n (v + 1) (by omega)]
    constructor
    · rintro ⟨hvaluation, hweight⟩
      by_cases heq : binaryWordHasseValuationExecutable word = v
      · exact Or.inl ⟨heq, hweight⟩
      · exact Or.inr ⟨by omega, hweight⟩
    · rintro (⟨heq, hweight⟩ | ⟨hnext, hweight⟩)
      · exact ⟨by omega, hweight⟩
      · exact ⟨by omega, hweight⟩
  have hdisjoint : Disjoint exact next := by
    rw [Finset.disjoint_left]
    intro word hexact hnext
    simp only [exact, next, Finset.mem_filter, Finset.mem_univ, true_and] at hexact hnext
    rw [isInHasseKernel_iff_le_executableValuation n (v + 1) (by omega)] at hnext
    omega
  have hcard : current.card = exact.card + next.card := by
    rw [hunion, Finset.card_union_of_disjoint hdisjoint]
  change exact.card = current.card - next.card
  omega

/-! ## Exact fixed-weight signed-ternary fiber models -/

abbrev FixedCardSupport (n weight : ℕ) :=
  ↑((Finset.univ : Finset (Fin n)).powersetCard weight)

abbrev FixedCardSupportIntersectionFiber
    (n weight : ℕ) (mask : Finset (Fin n)) (inside : ℕ) :=
  {support : FixedCardSupport n weight //
    (support.1 ∩ mask).card = inside}

abbrev SupportIntersectionPieces
    (n weight : ℕ) (mask : Finset (Fin n)) (inside : ℕ) :=
  ↑(mask.powersetCard inside) ×
    ↑(((Finset.univ : Finset (Fin n)) \ mask).powersetCard (weight - inside))

/-- Split a fixed-cardinality support into its part inside a mask and its part outside. -/
noncomputable def fixedCardSupportIntersectionEquiv
    (n weight : ℕ) (mask : Finset (Fin n)) (inside : ℕ)
    (hinside : inside ≤ weight) :
    FixedCardSupportIntersectionFiber n weight mask inside ≃
      SupportIntersectionPieces n weight mask inside where
  toFun support :=
    by
      refine ⟨⟨support.1.1 ∩ mask, ?_⟩, ⟨support.1.1 \ mask, ?_⟩⟩
      · rw [Finset.mem_powersetCard]
        exact ⟨Finset.inter_subset_right, support.2⟩
      · rw [Finset.mem_powersetCard]
        constructor
        · intro coordinate hcoordinate
          have hsupport := (Finset.mem_powersetCard.mp support.1.2).1
          exact Finset.mem_sdiff.mpr
            ⟨hsupport (Finset.mem_sdiff.mp hcoordinate).1,
              (Finset.mem_sdiff.mp hcoordinate).2⟩
        · have hcard := Finset.card_sdiff_add_card_inter support.1.1 mask
          have hsupportCard := (Finset.mem_powersetCard.mp support.1.2).2
          have hintersectionCard : (support.1.1 ∩ mask).card = inside := support.2
          omega
  invFun pieces := by
    let support : Finset (Fin n) := pieces.1.1 ∪ pieces.2.1
    have hdisjoint : Disjoint pieces.1.1 pieces.2.1 := by
      rw [Finset.disjoint_left]
      intro coordinate hfirst hsecond
      have hfirstMask := (Finset.mem_powersetCard.mp pieces.1.2).1 hfirst
      exact (Finset.mem_sdiff.mp
        ((Finset.mem_powersetCard.mp pieces.2.2).1 hsecond)).2 hfirstMask
    have hsupportSubset : support ⊆ (Finset.univ : Finset (Fin n)) :=
      Finset.subset_univ _
    have hsupportCard : support.card = weight := by
      rw [Finset.card_union_of_disjoint hdisjoint]
      have hfirstCard := (Finset.mem_powersetCard.mp pieces.1.2).2
      have hsecondCard := (Finset.mem_powersetCard.mp pieces.2.2).2
      omega
    have hintersection : support ∩ mask = pieces.1.1 := by
      ext coordinate
      constructor
      · intro hcoordinate
        have hmask := (Finset.mem_inter.mp hcoordinate).2
        rcases Finset.mem_union.mp (Finset.mem_inter.mp hcoordinate).1 with hfirst | hsecond
        · exact hfirst
        · exact False.elim
            ((Finset.mem_sdiff.mp
              ((Finset.mem_powersetCard.mp pieces.2.2).1 hsecond)).2 hmask)
      · intro hfirst
        exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hfirst,
          (Finset.mem_powersetCard.mp pieces.1.2).1 hfirst⟩
    exact ⟨⟨support, Finset.mem_powersetCard.mpr
      ⟨hsupportSubset, hsupportCard⟩⟩, by
        rw [hintersection]
        exact (Finset.mem_powersetCard.mp pieces.1.2).2⟩
  left_inv support := by
    apply Subtype.ext
    apply Subtype.ext
    change (support.1.1 ∩ mask) ∪ (support.1.1 \ mask) = support.1.1
    ext coordinate
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  right_inv pieces := by
    apply Prod.ext
    · apply Subtype.ext
      change (pieces.1.1 ∪ pieces.2.1) ∩ mask = pieces.1.1
      ext coordinate
      constructor
      · intro hcoordinate
        have hunion := Finset.mem_union.mp (Finset.mem_inter.mp hcoordinate).1
        exact hunion.resolve_right fun hsecond ↦
          (Finset.mem_sdiff.mp
            ((Finset.mem_powersetCard.mp pieces.2.2).1 hsecond)).2
            (Finset.mem_inter.mp hcoordinate).2
      · intro hfirst
        exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ hfirst,
          (Finset.mem_powersetCard.mp pieces.1.2).1 hfirst⟩
    · apply Subtype.ext
      change (pieces.1.1 ∪ pieces.2.1) \ mask = pieces.2.1
      ext coordinate
      constructor
      · intro hcoordinate
        have hunion := Finset.mem_union.mp (Finset.mem_sdiff.mp hcoordinate).1
        have hnotMask := (Finset.mem_sdiff.mp hcoordinate).2
        exact hunion.resolve_left fun hfirst ↦
          hnotMask ((Finset.mem_powersetCard.mp pieces.1.2).1 hfirst)
      · intro hsecond
        exact Finset.mem_sdiff.mpr
          ⟨Finset.mem_union_right _ hsecond,
            (Finset.mem_sdiff.mp
              ((Finset.mem_powersetCard.mp pieces.2.2).1 hsecond)).2⟩

theorem card_fixedCardSupportIntersectionFiber
    (n weight : ℕ) (mask : Finset (Fin n)) (inside : ℕ)
    (hinside : inside ≤ weight) :
    Fintype.card (FixedCardSupportIntersectionFiber n weight mask inside) =
      mask.card.choose inside *
        (n - mask.card).choose (weight - inside) := by
  rw [Fintype.card_congr
    (fixedCardSupportIntersectionEquiv n weight mask inside hinside)]
  change Fintype.card
      (↑(mask.powersetCard inside) ×
        ↑(((Finset.univ : Finset (Fin n)) \ mask).powersetCard
          (weight - inside))) = _
  rw [Fintype.card_prod]
  simp only [Fintype.card_coe, Finset.card_powersetCard]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ mask)]
  simp

theorem card_symmDiff
    {Index : Type} [DecidableEq Index] (left right : Finset Index) :
    (left ∆ right).card = (left \ right).card + (right \ left).card := by
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint]
  exact Finset.disjoint_left.mpr fun coordinate hleft hright ↦
    (Finset.mem_sdiff.mp hleft).2 (Finset.mem_sdiff.mp hright).1

abbrev FixedSupportSymmDiffFiber
    (n weight : ℕ) (mask : Finset (Fin n)) :=
  {pair : FixedCardSupport n weight × FixedCardSupport n weight //
    pair.1.1 ∆ pair.2.1 = mask}

/-- Equal-cardinality support pairs with prescribed symmetric difference are parameterized by
the first support's intersection with the mask. -/
noncomputable def fixedSupportSymmDiffFiberEquiv
    (n weight a : ℕ) (mask : Finset (Fin n)) (hmask : mask.card = 2 * a) :
    FixedSupportSymmDiffFiber n weight mask ≃
      FixedCardSupportIntersectionFiber n weight mask a where
  toFun pair := by
    refine ⟨pair.1.1, ?_⟩
    have hintersection : pair.1.1.1 ∩ mask = pair.1.1.1 \ pair.1.2.1 := by
      ext coordinate
      constructor
      · intro hintersectionMem
        have ⟨hleft, hmaskMem⟩ := Finset.mem_inter.mp hintersectionMem
        have hsymm : coordinate ∈ pair.1.1.1 ∆ pair.1.2.1 :=
          Eq.mp (congrArg (fun support ↦ coordinate ∈ support) pair.2).symm hmaskMem
        rcases Finset.mem_symmDiff.mp hsymm with hcase | hcase
        · exact Finset.mem_sdiff.mpr hcase
        · exact False.elim (hcase.2 hleft)
      · intro hdifference
        have hcase := Finset.mem_sdiff.mp hdifference
        refine Finset.mem_inter.mpr ⟨hcase.1, ?_⟩
        have hsymm : coordinate ∈ pair.1.1.1 ∆ pair.1.2.1 :=
          Finset.mem_symmDiff.mpr (Or.inl hcase)
        exact Eq.mp (congrArg (fun support ↦ coordinate ∈ support) pair.2) hsymm
    rw [hintersection]
    have hsupportCards : pair.1.1.1.card = pair.1.2.1.card := by
      rw [(Finset.mem_powersetCard.mp pair.1.1.2).2,
        (Finset.mem_powersetCard.mp pair.1.2.2).2]
    have hdifferenceCards :
        (pair.1.1.1 \ pair.1.2.1).card =
          (pair.1.2.1 \ pair.1.1.1).card :=
      Finset.card_sdiff_comm hsupportCards
    have htotal : mask.card =
        (pair.1.1.1 \ pair.1.2.1).card +
          (pair.1.2.1 \ pair.1.1.1).card := by
      calc
        mask.card = (pair.1.1.1 ∆ pair.1.2.1).card :=
          congrArg Finset.card pair.2 |>.symm
        _ = _ := card_symmDiff _ _
    omega
  invFun support := by
    let rightSet := support.1.1 ∆ mask
    have hrightCard : rightSet.card = weight := by
      rw [card_symmDiff]
      have hleftParts := Finset.card_sdiff_add_card_inter support.1.1 mask
      have hmaskParts := Finset.card_sdiff_add_card_inter mask support.1.1
      have hintersectionComm : (mask ∩ support.1.1).card = a := by
        rw [Finset.inter_comm]
        exact support.2
      have hleftCard := (Finset.mem_powersetCard.mp support.1.2).2
      omega
    let right : FixedCardSupport n weight :=
      ⟨rightSet, Finset.mem_powersetCard.mpr
        ⟨Finset.subset_univ _, hrightCard⟩⟩
    exact ⟨(support.1, right), by
      change support.1.1 ∆ (support.1.1 ∆ mask) = mask
      exact symmDiff_symmDiff_cancel_left _ _⟩
  left_inv pair := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      change pair.1.1.1 ∆ mask = pair.1.2.1
      calc
        pair.1.1.1 ∆ mask =
            pair.1.1.1 ∆ (pair.1.1.1 ∆ pair.1.2.1) :=
          congrArg (fun support ↦ pair.1.1.1 ∆ support) pair.2.symm
        _ = pair.1.2.1 := symmDiff_symmDiff_cancel_left _ _
  right_inv support := by
    apply Subtype.ext
    rfl

theorem card_fixedSupportSymmDiffFiber
    (n weight a : ℕ) (mask : Finset (Fin n))
    (ha : a ≤ weight) (hmask : mask.card = 2 * a) :
    Fintype.card (FixedSupportSymmDiffFiber n weight mask) =
      (2 * a).choose a * (n - 2 * a).choose (weight - a) := by
  rw [Fintype.card_congr
    (fixedSupportSymmDiffFiberEquiv n weight a mask hmask),
    card_fixedCardSupportIntersectionFiber n weight mask a ha,
    hmask]

/-- All independent sign choices over a prescribed support-changing pair. -/
abbrev SupportChangingSignedFiber
    (n weight : ℕ) (mask : Finset (Fin n)) :=
  Σ pair : FixedSupportSymmDiffFiber n weight mask,
    (↑pair.1.1.1 → Fin 2) × (↑pair.1.2.1 → Fin 2)

theorem card_supportChangingSignedFiber
    (n weight a : ℕ) (mask : Finset (Fin n))
    (ha : a ≤ weight) (hmask : mask.card = 2 * a) :
    Fintype.card (SupportChangingSignedFiber n weight mask) =
      2 ^ (2 * weight) * (2 * a).choose a *
        (n - 2 * a).choose (weight - a) := by
  rw [Fintype.card_sigma]
  calc
    (∑ pair : FixedSupportSymmDiffFiber n weight mask,
        Fintype.card
          ((↑pair.1.1.1 → Fin 2) × (↑pair.1.2.1 → Fin 2))) =
        ∑ _pair : FixedSupportSymmDiffFiber n weight mask,
          2 ^ (2 * weight) := by
      apply Finset.sum_congr rfl
      intro pair _
      simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
        Fintype.card_coe]
      have hleft := (Finset.mem_powersetCard.mp pair.1.1.2).2
      have hright := (Finset.mem_powersetCard.mp pair.1.2.2).2
      rw [hleft, hright, ← pow_add]
      congr 1
      omega
    _ = Fintype.card (FixedSupportSymmDiffFiber n weight mask) *
        2 ^ (2 * weight) := by simp
    _ = _ := by
      rw [card_fixedSupportSymmDiffFiber n weight a mask ha hmask]
      ring

abbrev FixedSupportContainingFiber
    (n weight : ℕ) (mask : Finset (Fin n)) :=
  {support : FixedCardSupport n weight // mask ⊆ support.1}

noncomputable def fixedSupportContainingFiberEquiv
    (n weight : ℕ) (mask : Finset (Fin n)) :
    FixedSupportContainingFiber n weight mask ≃
      ↑(((Finset.univ : Finset (Fin n)).powersetCard weight).filter
        (mask ⊆ ·)) where
  toFun support := ⟨support.1.1, Finset.mem_filter.mpr
    ⟨support.1.2, support.2⟩⟩
  invFun support := ⟨⟨support.1,
    (Finset.mem_filter.mp support.2).1⟩,
      (Finset.mem_filter.mp support.2).2⟩
  left_inv support := by rfl
  right_inv support := by rfl

theorem card_fixedSupportContainingFiber
    (n weight : ℕ) (mask : Finset (Fin n)) (hmask : mask.card ≤ weight) :
    Fintype.card (FixedSupportContainingFiber n weight mask) =
      (n - mask.card).choose (weight - mask.card) := by
  rw [Fintype.card_congr (fixedSupportContainingFiberEquiv n weight mask),
    Fintype.card_coe,
    Finset.card_filter_powersetCard_subset mask Finset.univ weight
      (Finset.subset_univ mask) hmask]
  simp

/-- For equal supports, a flip mask and the first sign word uniquely determine the second. -/
abbrev SameSupportSignedFiber
    (n weight : ℕ) (flipMask : Finset (Fin n)) :=
  Σ support : FixedSupportContainingFiber n weight flipMask,
    ↑support.1.1 → Fin 2

theorem card_sameSupportSignedFiber
    (n weight b : ℕ) (flipMask : Finset (Fin n))
    (hb : b ≤ weight) (hmask : flipMask.card = b) :
    Fintype.card (SameSupportSignedFiber n weight flipMask) =
      2 ^ weight * (n - b).choose (weight - b) := by
  rw [Fintype.card_sigma]
  calc
    (∑ support : FixedSupportContainingFiber n weight flipMask,
        Fintype.card (↑support.1.1 → Fin 2)) =
        ∑ _support : FixedSupportContainingFiber n weight flipMask,
          2 ^ weight := by
      apply Finset.sum_congr rfl
      intro support _
      simp only [Fintype.card_fun, Fintype.card_fin, Fintype.card_coe]
      rw [(Finset.mem_powersetCard.mp support.1.2).2]
    _ = Fintype.card (FixedSupportContainingFiber n weight flipMask) *
        2 ^ weight := by simp
    _ = _ := by
      rw [card_fixedSupportContainingFiber n weight flipMask (by omega), hmask]
      ring

abbrev ExactValuationWeightWord (n valuation weight : ℕ) :=
  {word : Fin n → F2 //
    binaryWordHasseValuationExecutable word = valuation ∧
      (wordSupport word).card = weight}

theorem card_exactValuationWeightWord (n valuation weight : ℕ) :
    Fintype.card (ExactValuationWeightWord n valuation weight) =
      hasseExactValuationWeightCount n valuation weight := by
  unfold hasseExactValuationWeightCount
  rw [Fintype.card_subtype, Finset.card_filter]

/-- Canonical finite model for all support-changing pairs in exact valuation stratum `v`. -/
abbrev SupportChangingHistogramModel
    (n weight a valuation : ℕ) :=
  Σ maskWord : ExactValuationWeightWord n valuation (2 * a),
    SupportChangingSignedFiber n weight (wordSupport maskWord.1)

/-- The first displayed fixed-weight ternary histogram formula. -/
theorem card_supportChangingHistogramModel
    (n weight a valuation : ℕ) (ha : a ≤ weight) (hvaluation : valuation < n) :
    Fintype.card (SupportChangingHistogramModel n weight a valuation) =
      2 ^ (2 * weight) * (2 * a).choose a *
        (n - 2 * a).choose (weight - a) *
          (hasseKernelWeightCount n valuation (2 * a) -
            hasseKernelWeightCount n (valuation + 1) (2 * a)) := by
  rw [Fintype.card_sigma]
  calc
    (∑ maskWord : ExactValuationWeightWord n valuation (2 * a),
        Fintype.card
          (SupportChangingSignedFiber n weight (wordSupport maskWord.1))) =
        ∑ _maskWord : ExactValuationWeightWord n valuation (2 * a),
          2 ^ (2 * weight) * (2 * a).choose a *
            (n - 2 * a).choose (weight - a) := by
      apply Finset.sum_congr rfl
      intro maskWord _
      exact card_supportChangingSignedFiber n weight a
        (wordSupport maskWord.1) ha maskWord.2.2
    _ = Fintype.card (ExactValuationWeightWord n valuation (2 * a)) *
        (2 ^ (2 * weight) * (2 * a).choose a *
          (n - 2 * a).choose (weight - a)) := by simp
    _ = _ := by
      rw [card_exactValuationWeightWord,
        hasseExactValuationWeightCount_eq_kernel_sub_succ n valuation (2 * a)
          hvaluation]
      ring

/-- Canonical finite model for equal-support sign-flip pairs in exact valuation stratum `v`. -/
abbrev SameSupportHistogramModel
    (n weight b valuation : ℕ) :=
  Σ flipWord : ExactValuationWeightWord n valuation b,
    SameSupportSignedFiber n weight (wordSupport flipWord.1)

/-- The second displayed fixed-weight ternary histogram formula. -/
theorem card_sameSupportHistogramModel
    (n weight b valuation : ℕ) (hb : b ≤ weight) (hvaluation : valuation < n) :
    Fintype.card (SameSupportHistogramModel n weight b valuation) =
      2 ^ weight * (n - b).choose (weight - b) *
        (hasseKernelWeightCount n valuation b -
          hasseKernelWeightCount n (valuation + 1) b) := by
  rw [Fintype.card_sigma]
  calc
    (∑ flipWord : ExactValuationWeightWord n valuation b,
        Fintype.card (SameSupportSignedFiber n weight (wordSupport flipWord.1))) =
        ∑ _flipWord : ExactValuationWeightWord n valuation b,
          2 ^ weight * (n - b).choose (weight - b) := by
      apply Finset.sum_congr rfl
      intro flipWord _
      exact card_sameSupportSignedFiber n weight b
        (wordSupport flipWord.1) hb flipWord.2.2
    _ = Fintype.card (ExactValuationWeightWord n valuation b) *
        (2 ^ weight * (n - b).choose (weight - b)) := by simp
    _ = _ := by
      rw [card_exactValuationWeightWord,
        hasseExactValuationWeightCount_eq_kernel_sub_succ n valuation b hvaluation]
      ring

/-- The diagonal (zero-difference) count is the exact fixed-weight secret cardinality. -/
theorem zeroDifferenceCount_fixedWeightTernary (n weight : ℕ) :
    Fintype.card (EncodedFixedWeightTernarySecret n weight) =
      2 ^ weight * n.choose weight :=
  card_encodedFixedWeightTernarySecret n weight

/-! ## Complete descriptor valuation -/

/-- Nilpotence at the certified chain length forces zero to have the terminal valuation. -/
theorem valuation_zero_eq_length_of_uniformizer_pow_eq_zero
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    (chain : FiniteAdicChain R)
    (hnilpotent : chain.uniformizer ^ chain.length = 0) :
    chain.valuation 0 = chain.length := by
  apply valuation_eq_level_of_factorization chain 0 1 chain.length le_rfl
  · simp [hnilpotent]
  · exact isUnit_one

/-- Valuations add until the nilpotent chain length is reached.  This statement deliberately
requires actual unit-times-uniformizer factorizations; it is not derivable from ideal
cardinalities alone. -/
theorem valuation_mul_eq_min_of_unitFactorization
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    (chain : FiniteAdicChain R)
    (hnilpotent : chain.uniformizer ^ chain.length = 0)
    (factorization : ∀ value : R, value ≠ 0 →
      ∃ factor : R,
        factor * chain.uniformizer ^ chain.valuation value = value ∧
          IsUnit factor)
    (left right : R) :
    chain.valuation (left * right) =
      min chain.length (chain.valuation left + chain.valuation right) := by
  have hzero : chain.valuation 0 = chain.length :=
    valuation_zero_eq_length_of_uniformizer_pow_eq_zero chain hnilpotent
  by_cases hleft : left = 0
  · subst left
    rw [zero_mul, hzero]
    omega
  by_cases hright : right = 0
  · subst right
    rw [mul_zero, hzero]
    omega
  obtain ⟨leftFactor, hleftFactor, hleftUnit⟩ :=
    factorization left hleft
  obtain ⟨rightFactor, hrightFactor, hrightUnit⟩ :=
    factorization right hright
  let level := chain.valuation left + chain.valuation right
  have hproduct :
      left * right =
        (leftFactor * rightFactor) * chain.uniformizer ^ level := by
    dsimp only [level]
    calc
      left * right =
          (leftFactor * chain.uniformizer ^ chain.valuation left) *
            (rightFactor * chain.uniformizer ^ chain.valuation right) :=
        congrArg₂ (· * ·) hleftFactor.symm hrightFactor.symm
      _ = (leftFactor * rightFactor) *
          chain.uniformizer ^
            (chain.valuation left + chain.valuation right) := by
        rw [pow_add]
        ring
  by_cases hterminal : chain.length ≤ level
  · have hpowerZero : chain.uniformizer ^ level = 0 :=
      pow_eq_zero_of_le hterminal hnilpotent
    have hproductZero : left * right = 0 := by
      rw [hproduct, hpowerZero, mul_zero]
    rw [hproductZero, hzero, Nat.min_eq_left hterminal]
  · have hlevel : level ≤ chain.length := by omega
    rw [valuation_eq_level_of_factorization chain (left * right)
      (leftFactor * rightFactor) level hlevel hproduct
      (hleftUnit.mul hrightUnit), Nat.min_eq_right hlevel]

/-- Concrete capped-additivity for the literal power-of-two cyclotomic quotient. -/
theorem quotientPowerOfTwo_valuation_mul
    (K d : ℕ) [hK : Fact (0 < K)]
    (left right : QuotientRq (2 ^ K) (2 ^ d)) :
    (quotientPowerOfTwoAdicChain K d).valuation (left * right) =
      min (K * 2 ^ d)
        ((quotientPowerOfTwoAdicChain K d).valuation left +
          (quotientPowerOfTwoAdicChain K d).valuation right) := by
  apply valuation_mul_eq_min_of_unitFactorization
    (quotientPowerOfTwoAdicChain K d)
  · exact quotientUniformizer_pow_length_eq_zero K hK.out d
  · intro value hvalue
    exact quotientPowerOfTwo_factor_at_valuation_isUnit K d value hvalue

/-- The complete quadratic row descriptor from the note. -/
def completeDescriptorDifference {R : Type} [CommRing R]
    (secretLeft secretRight rowMask commonFactor gadget : R) : R :=
  (secretRight - secretLeft) *
    (rowMask + commonFactor * gadget * (secretRight + secretLeft))

/-- The descriptor multiplier is retained inside the valuation.  In particular, this theorem
does not assume that `rowMask + commonFactor * gadget * (t+s)` is a unit. -/
theorem quotientPowerOfTwo_completeDescriptor_valuation
    (K d : ℕ) [hK : Fact (0 < K)]
    (secretLeft secretRight rowMask commonFactor gadget :
      QuotientRq (2 ^ K) (2 ^ d)) :
    (quotientPowerOfTwoAdicChain K d).valuation
        (completeDescriptorDifference
          secretLeft secretRight rowMask commonFactor gadget) =
      min (K * 2 ^ d)
        ((quotientPowerOfTwoAdicChain K d).valuation
            (secretRight - secretLeft) +
          (quotientPowerOfTwoAdicChain K d).valuation
            (rowMask + commonFactor * gadget *
              (secretRight + secretLeft))) := by
  exact quotientPowerOfTwo_valuation_mul K d
    (secretRight - secretLeft)
    (rowMask + commonFactor * gadget * (secretRight + secretLeft))

/-- Quotient/remainder coordinates of a nonterminal valuation. -/
def valuationTwoLevelCoordinates (n level : ℕ) : ℕ × ℕ :=
  (level / n, level % n)

theorem valuationTwoLevelCoordinates_reconstruct
    (n level : ℕ) :
    (valuationTwoLevelCoordinates n level).1 * n +
        (valuationTwoLevelCoordinates n level).2 = level := by
  simp only [valuationTwoLevelCoordinates]
  simpa [Nat.mul_comm] using Nat.div_add_mod level n

theorem valuationTwoLevelCoordinates_remainder_lt
    (n level : ℕ) (hn : 0 < n) :
    (valuationTwoLevelCoordinates n level).2 < n := by
  simpa [valuationTwoLevelCoordinates] using Nat.mod_lt level hn

theorem valuationTwoLevelCoordinates_exponent_lt
    (K n level : ℕ) (hn : 0 < n) (hlevel : level < K * n) :
    (valuationTwoLevelCoordinates n level).1 < K := by
  simp only [valuationTwoLevelCoordinates]
  exact (Nat.div_lt_iff_lt_mul hn).2 (by simpa [Nat.mul_comm] using hlevel)

/-- Select the exact local factor from a complete valuation and exponent-indexed error table. -/
def exactRowFactorFromValuation
    (n level : ℕ) (divisibilityMass parityBias : ℕ → ℝ) : ℝ :=
  let coordinates := valuationTwoLevelCoordinates n level
  exactNormalizedLocalFactor coordinates.1 n coordinates.2
    (divisibilityMass coordinates.1) (parityBias coordinates.1)

theorem exactRowFactorFromValuation_eq
    (n level : ℕ) (divisibilityMass parityBias : ℕ → ℝ) :
    exactRowFactorFromValuation n level divisibilityMass parityBias =
      ((2 : ℝ) ^ (valuationTwoLevelCoordinates n level).1 *
          divisibilityMass (valuationTwoLevelCoordinates n level).1) ^ n *
        hasseWeightEnumeratorValue n
          (valuationTwoLevelCoordinates n level).2
          (parityBias (valuationTwoLevelCoordinates n level).1) := by
  unfold exactRowFactorFromValuation
  exact exactNormalizedLocalFactor_eq
    (valuationTwoLevelCoordinates n level).1 n
    (valuationTwoLevelCoordinates n level).2
    (divisibilityMass (valuationTwoLevelCoordinates n level).1)
    (parityBias (valuationTwoLevelCoordinates n level).1)

/-! ## Joint tuple aggregation -/

/-- Exact mass of one statistic cell.  It keeps the whole row tuple, so shared secrets and
descriptor values are never replaced by a product of marginal histograms. -/
def exactTupleHistogram
    {Sample Tuple : Type} [Fintype Sample] [Fintype Tuple]
    [DecidableEq Tuple]
    (mass : Sample → ℝ) (statistic : Sample → Tuple) (cell : Tuple) : ℝ :=
  ∑ sample, if statistic sample = cell then mass sample else 0

/-- Regrouping a finite weighted sum by the complete statistic tuple is exact. -/
theorem sum_exactTupleHistogram_mul
    {Sample Tuple : Type} [Fintype Sample] [Fintype Tuple]
    [DecidableEq Tuple]
    (mass : Sample → ℝ) (statistic : Sample → Tuple) (factor : Tuple → ℝ) :
    (∑ cell, exactTupleHistogram mass statistic cell * factor cell) =
      ∑ sample, mass sample * factor (statistic sample) := by
  classical
  unfold exactTupleHistogram
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro sample _
  simp [eq_comm]

/-- The tuple histogram preserves total mass. -/
theorem sum_exactTupleHistogram
    {Sample Tuple : Type} [Fintype Sample] [Fintype Tuple]
    [DecidableEq Tuple]
    (mass : Sample → ℝ) (statistic : Sample → Tuple) :
    ∑ cell, exactTupleHistogram mass statistic cell = ∑ sample, mass sample := by
  classical
  simpa using sum_exactTupleHistogram_mul mass statistic (fun _cell ↦ (1 : ℝ))

/-- Exact joint-row aggregation, stated in the form used by the certificate checker. -/
theorem jointTupleAggregation
    {Sample Row Cell : Type} [Fintype Sample] [Fintype Row] [Fintype Cell]
    [DecidableEq Cell]
    (mass : Sample → ℝ) (statistic : Sample → Row → Cell)
    (rowFactor : Row → Cell → ℝ) :
    (∑ tuple : Row → Cell,
        exactTupleHistogram mass statistic tuple *
          ∏ row, rowFactor row (tuple row)) =
      ∑ sample, mass sample *
        ∏ row, rowFactor row (statistic sample row) := by
  exact sum_exactTupleHistogram_mul mass statistic
    (fun tuple ↦ ∏ row, rowFactor row (tuple row))

/-- Conditional row independence justifies integrating independent row-local descriptors on
the inside.  Shared core values remain outside this product. -/
theorem conditionalRowLocalAggregation
    {Row : Type} [Fintype Row] [DecidableEq Row]
    (Descriptor : Row → Type)
    [(row : Row) → Fintype (Descriptor row)]
    (mass : (row : Row) → Descriptor row → ℝ)
    (rowFactor : (row : Row) → Descriptor row → ℝ) :
    (∑ descriptor : (row : Row) → Descriptor row,
        ∏ row, mass row (descriptor row) * rowFactor row (descriptor row)) =
      ∏ row, ∑ localDescriptor : Descriptor row,
        mass row localDescriptor * rowFactor row localDescriptor := by
  exact sum_pi_prod_eq_prod_sum_real Descriptor
    (fun row localDescriptor ↦
      mass row localDescriptor * rowFactor row localDescriptor)

end

end FormalProof4FHE.RLWE.RankOneHNFLossinessTwoSmithExact
