/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeTRGSWSpectralInfeasibility
import FormalProof4FHE.TFHE.TFHEppSubsetJointScreen
import FormalProof4FHE.TFHE.BootstrappingCorrectness
import FormalProof4FHE.TFHE.KeySwitchRecovery

/-!
# Concrete suffix separation for the native TFHEpp level-1-to-level-0 KSK

This module discharges the deterministic separation premise of the exhaustive native-KSK
decoder at the implementation's level-1-to-level-0 dimensions.  The prefix is binary, the
suffix is centered ternary, and the key-switch rows use seven base-four levels with the two
positive digit multipliers.  A single top, unit-multiplier row already separates any two
different suffixes whenever the centered row-error radius is less than half of `2^14`.

The result is deliberately independent of a particular error sampler.  Connecting the actual
finite C++ modular-Gaussian sampler to a high-probability centered ball is a separate analytic
compiler statement; it is not part of this finite gadget calculation.
-/

open Matrix OracleComp
open scoped BigOperators ENNReal

namespace FormalProof4FHE.TFHE.NativeTRGSWConcreteSuffixSeparation

noncomputable section

open NativeTRGSWSpectralInfeasibility
open RGSWCoefficientCircularSecurity
open TFHEppSubsetJointScreen
open BootstrappingCorrectness

/-! ## Centered balls and translate separation -/

/-- The centered modular ball of integral radius `bound`. -/
def centeredBall (q bound : ℕ) [NeZero q] : Finset (ZMod q) :=
  Finset.univ.filter fun value ↦ centeredDistance value 0 ≤ bound

@[simp]
theorem mem_centeredBall_iff {q bound : ℕ} [NeZero q] (value : ZMod q) :
    value ∈ centeredBall q bound ↔ centeredDistance value 0 ≤ bound := by
  simp [centeredBall]

/-- Translating both endpoints by the same base leaves the centered distance equal to the
distance from the error to zero. -/
theorem centeredDistance_add_self {q : ℕ} [NeZero q]
    (base error : ZMod q) :
    centeredDistance (base + error) base = centeredDistance error 0 := by
  unfold centeredDistance
  rw [show base + error - base = error - 0 by ring]

/-- The reverse orientation of `centeredDistance_add_self`. -/
theorem centeredDistance_self_add {q : ℕ} [NeZero q]
    (base error : ZMod q) :
    centeredDistance base (base + error) = centeredDistance error 0 := by
  rw [centeredDistance_symm, centeredDistance_add_self]

/-- Two centered-radius translates are disjoint when their centers are more than twice the
radius apart. -/
theorem add_ne_add_of_two_mul_lt_centeredDistance
    {q bound : ℕ} [NeZero q]
    (left right : ZMod q)
    (hfar : 2 * bound < centeredDistance left right) :
    ∀ leftError ∈ centeredBall q bound,
      ∀ rightError ∈ centeredBall q bound,
        left + leftError ≠ right + rightError := by
  intro leftError hleft rightError hright heq
  have htriangle := centeredDistance_triangle left (left + leftError) right
  rw [centeredDistance_self_add, heq, centeredDistance_add_self] at htriangle
  rw [mem_centeredBall_iff] at hleft hright
  omega

/-- Encode a centered modular ball into its integer interval of representatives. -/
def centeredBallCode
    {q bound : ℕ} [NeZero q] (value : {x : ZMod q // x ∈ centeredBall q bound}) :
    {coefficient : ℤ // coefficient ∈
      Finset.Icc (-(bound : ℤ)) (bound : ℤ)} :=
  ⟨LatticeCrypto.centeredRepr value.1, by
    rw [Finset.mem_Icc]
    have hbound :
        (LatticeCrypto.centeredRepr value.1).natAbs ≤ bound := by
      simpa [centeredDistance] using (mem_centeredBall_iff value.1).mp value.2
    constructor <;> omega⟩

theorem centeredBallCode_injective
    {q bound : ℕ} [NeZero q] :
    Function.Injective (centeredBallCode (q := q) (bound := bound)) := by
  intro left right heq
  apply Subtype.ext
  have hcoefficient := congrArg Subtype.val heq
  calc
    left.1 = ((LatticeCrypto.centeredRepr left.1 : ℤ) : ZMod q) :=
      LatticeCrypto.centeredRepr_intCast _
    _ = ((LatticeCrypto.centeredRepr right.1 : ℤ) : ZMod q) := by
      exact congrArg (fun value : ℤ ↦ (value : ZMod q)) hcoefficient
    _ = right.1 := (LatticeCrypto.centeredRepr_intCast _).symm

/-- A centered radius-`bound` subset of any modular coefficient carrier has at most
`2 * bound + 1` elements.  No no-wrap premise is needed for this upper bound. -/
theorem card_centeredBall_le (q bound : ℕ) [NeZero q] :
    (centeredBall q bound).card ≤ 2 * bound + 1 := by
  rw [← Fintype.card_coe]
  calc
    Fintype.card {value : ZMod q // value ∈ centeredBall q bound} ≤
        Fintype.card {coefficient : ℤ // coefficient ∈
          Finset.Icc (-(bound : ℤ)) (bound : ℤ)} :=
      Fintype.card_le_of_injective centeredBallCode centeredBallCode_injective
    _ = 2 * bound + 1 := by
      rw [Fintype.card_coe]
      simp
      omega

/-! ## The concrete native KSK row family -/

/-- Native level-zero ciphertext modulus (`uint16_t`). -/
abbrev lvl10Modulus : ℕ := 2 ^ 16

/-- Binary prefix dimension shared with level zero. -/
abbrev lvl10PrefixDimension : ℕ := Parameters.lvl0Dimension

/-- Centered-ternary suffix dimension of the level-one secret. -/
abbrev lvl10SuffixDimension : ℕ := Parameters.suffixDimension

/-- Number of base-four decomposition levels. -/
abbrev lvl10Levels : ℕ := Parameters.lvl10Levels

/-- Number of positive digit multiples stored at each base-four level. -/
abbrev lvl10DigitCount : ℕ := Parameters.lvl10DigitCount

/-- A full centered-ternary suffix. -/
abbrev Lvl10Suffix := Fin lvl10SuffixDimension → Fin 3

/-- We flatten `(suffix coordinate, level, digit multiplier)` in row-major order. -/
abbrev lvl10RowCount : ℕ :=
  lvl10SuffixDimension * (lvl10Levels * lvl10DigitCount)

theorem lvl10RowCount_eq : lvl10RowCount = Parameters.lvl10KSKRows := by
  norm_num [lvl10RowCount, lvl10SuffixDimension, lvl10Levels, lvl10DigitCount,
    Parameters.lvl10KSKRows, Parameters.suffixDimension, Parameters.lvl1Dimension,
    Parameters.lvl0Dimension, Parameters.lvl10Levels, Parameters.lvl10DigitCount]

/-- Row-major encoding of an implementation KSK row. -/
def encodeLvl10Row
    (coordinate : Fin lvl10SuffixDimension)
    (level : Fin lvl10Levels) (digit : Fin lvl10DigitCount) :
    Fin lvl10RowCount :=
  finProdFinEquiv (coordinate, finProdFinEquiv (level, digit))

/-- Suffix coordinate selected by a flattened row. -/
def lvl10RowCoordinate (row : Fin lvl10RowCount) : Fin lvl10SuffixDimension :=
  (finProdFinEquiv.symm row).1

/-- Decomposition level selected by a flattened row. -/
def lvl10RowLevel (row : Fin lvl10RowCount) : Fin lvl10Levels :=
  (finProdFinEquiv.symm (finProdFinEquiv.symm row).2).1

/-- Positive digit multiplier, zero-indexed as in the C++ array. -/
def lvl10RowDigit (row : Fin lvl10RowCount) : Fin lvl10DigitCount :=
  (finProdFinEquiv.symm (finProdFinEquiv.symm row).2).2

@[simp]
theorem lvl10RowCoordinate_encode
    (coordinate : Fin lvl10SuffixDimension)
    (level : Fin lvl10Levels) (digit : Fin lvl10DigitCount) :
    lvl10RowCoordinate (encodeLvl10Row coordinate level digit) = coordinate := by
  simp [lvl10RowCoordinate, encodeLvl10Row]

@[simp]
theorem lvl10RowLevel_encode
    (coordinate : Fin lvl10SuffixDimension)
    (level : Fin lvl10Levels) (digit : Fin lvl10DigitCount) :
    lvl10RowLevel (encodeLvl10Row coordinate level digit) = level := by
  simp [lvl10RowLevel, encodeLvl10Row]

@[simp]
theorem lvl10RowDigit_encode
    (coordinate : Fin lvl10SuffixDimension)
    (level : Fin lvl10Levels) (digit : Fin lvl10DigitCount) :
    lvl10RowDigit (encodeLvl10Row coordinate level digit) = digit := by
  simp [lvl10RowDigit, encodeLvl10Row]

/-- The implementation's base-four gadget value for one level and positive multiplier. -/
def lvl10Gadget
    (level : Fin lvl10Levels) (digit : Fin lvl10DigitCount) :
    ZMod lvl10Modulus :=
  (digit.val + 1) * 2 ^ (16 - (level.val + 1) * 2)

/-- Message encrypted in one native suffix-KSK row. -/
def lvl10SuffixMessage
    (row : Fin lvl10RowCount) (suffix : Lvl10Suffix) :
    ZMod lvl10Modulus :=
  embedTernaryDigit (suffix (lvl10RowCoordinate row)) *
    lvl10Gadget (lvl10RowLevel row) (lvl10RowDigit row)

/-- The top unit-multiplier row carries the digit at centered spacing `2^14`. -/
def lvl10TopCode (digit : Fin 3) : ZMod lvl10Modulus :=
  embedTernaryDigit digit * (2 ^ 14 : ZMod lvl10Modulus)

/-- The top decomposition level. -/
def lvl10TopLevel : Fin lvl10Levels :=
  ⟨0, by norm_num [lvl10Levels, Parameters.lvl10Levels]⟩

/-- The unit positive multiplier. -/
def lvl10UnitDigit : Fin lvl10DigitCount :=
  ⟨0, by norm_num [lvl10DigitCount, Parameters.lvl10DigitCount]⟩

/-- Distinct centered-ternary top-row messages are at centered distance at least `2^14`.
The `+1` and `-1` pair is farther apart, at the half-modulus distance `2^15`. -/
theorem lvl10TopCode_centeredDistance_ge
    (left right : Fin 3) (hne : left ≠ right) :
    2 ^ 14 ≤ centeredDistance (lvl10TopCode left) (lvl10TopCode right) := by
  fin_cases left <;> fin_cases right <;>
    simp_all [lvl10TopCode, centeredDistance, LatticeCrypto.centeredRepr_eq_valMinAbs,
      embedTernaryDigit] <;> native_decide

/-- The row at level zero with digit index zero is exactly the top unit-multiplier code. -/
@[simp]
theorem lvl10SuffixMessage_topUnit
    (coordinate : Fin lvl10SuffixDimension) (suffix : Lvl10Suffix) :
    lvl10SuffixMessage
        (encodeLvl10Row coordinate lvl10TopLevel lvl10UnitDigit) suffix =
      lvl10TopCode (suffix coordinate) := by
  simp [lvl10SuffixMessage, lvl10Gadget, lvl10TopCode, lvl10TopLevel,
    lvl10UnitDigit]

/-- Concrete deterministic decoder premise: for any radius below `2^13`, one top gadget row at
a differing suffix coordinate makes the two centered-error translates disjoint. -/
theorem lvl10SuffixSeparated_centeredBall
    (bound : ℕ) (hbound : 2 * bound < 2 ^ 14) :
    SuffixSeparated
      (fun _ : Fin lvl10RowCount ↦ centeredBall lvl10Modulus bound)
      lvl10SuffixMessage := by
  intro actual candidate hne
  obtain ⟨coordinate, hcoordinate⟩ := Function.ne_iff.mp hne
  let row : Fin lvl10RowCount :=
    encodeLvl10Row coordinate lvl10TopLevel lvl10UnitDigit
  refine ⟨row, ?_⟩
  have hdistance :
      2 * bound <
        centeredDistance (lvl10SuffixMessage row actual)
          (lvl10SuffixMessage row candidate) := by
    rw [show lvl10SuffixMessage row actual = lvl10TopCode (actual coordinate) by
          simp [row],
      show lvl10SuffixMessage row candidate = lvl10TopCode (candidate coordinate) by
          simp [row]]
    exact hbound.trans_le
      (lvl10TopCode_centeredDistance_ge _ _ hcoordinate.symm)
  exact add_ne_add_of_two_mul_lt_centeredDistance
    (lvl10SuffixMessage row actual) (lvl10SuffixMessage row candidate) hdistance

/-! ## Concrete exhaustive-decoder bound -/

/-- The generic native-KSK recovery theorem instantiated with the actual ternary suffix message
and centered typical balls.  The only probabilistic premise left is the tail probability of the
chosen implementation error sampler. -/
theorem probEvent_lvl10_exhaustiveKSKDecoder_failure_le
    (bound : ℕ) (hbound : 2 * bound < 2 ^ 14)
    (prefixSampler : ProbComp (Prefix lvl10PrefixDimension))
    (suffixSampler : ProbComp Lvl10Suffix)
    (errorSampler : ProbComp (Fin lvl10RowCount → ZMod lvl10Modulus))
    (errorTail : ENNReal)
    (herrorTail :
      Pr[(fun error ↦ ¬errorsTypical
          (fun _ : Fin lvl10RowCount ↦ centeredBall lvl10Modulus bound) error) |
        errorSampler] ≤ errorTail) :
    Pr[(fun sample ↦
        exhaustiveKSKDecoder
            (fun _ : Fin lvl10RowCount ↦ centeredBall lvl10Modulus bound)
            lvl10SuffixMessage sample.2 ≠ some sample.1) |
      nativeKSKKeyedSampler lvl10SuffixMessage prefixSampler suffixSampler errorSampler] ≤
      errorTail +
        ((2 ^ lvl10PrefixDimension - 1) * Fintype.card Lvl10Suffix : ℕ) *
          ∏ _row : Fin lvl10RowCount,
            ((centeredBall lvl10Modulus bound).card : ENNReal) /
              (lvl10Modulus : ENNReal) := by
  exact probEvent_exhaustiveKSKDecoder_keyed_failure_le_zmod
    (fun _ : Fin lvl10RowCount ↦ centeredBall lvl10Modulus bound)
    lvl10SuffixMessage prefixSampler suffixSampler errorSampler errorTail
    herrorTail (lvl10SuffixSeparated_centeredBall bound hbound)

/-- Fully explicit false-candidate density bound.  There are `2^630 - 1` wrong binary prefixes,
`3^394` ternary suffixes, `5516` independent rows, and at most `2 * bound + 1` accepted residuals
per `2^16`-element row carrier. -/
theorem probEvent_lvl10_exhaustiveKSKDecoder_failure_le_explicit
    (bound : ℕ) (hbound : 2 * bound < 2 ^ 14)
    (prefixSampler : ProbComp (Prefix lvl10PrefixDimension))
    (suffixSampler : ProbComp Lvl10Suffix)
    (errorSampler : ProbComp (Fin lvl10RowCount → ZMod lvl10Modulus))
    (errorTail : ENNReal)
    (herrorTail :
      Pr[(fun error ↦ ¬errorsTypical
          (fun _ : Fin lvl10RowCount ↦ centeredBall lvl10Modulus bound) error) |
        errorSampler] ≤ errorTail) :
    Pr[(fun sample ↦
        exhaustiveKSKDecoder
            (fun _ : Fin lvl10RowCount ↦ centeredBall lvl10Modulus bound)
            lvl10SuffixMessage sample.2 ≠ some sample.1) |
      nativeKSKKeyedSampler lvl10SuffixMessage prefixSampler suffixSampler errorSampler] ≤
      errorTail +
        ((2 ^ 630 - 1) * 3 ^ 394 : ℕ) *
          (((2 * bound + 1 : ℕ) : ENNReal) / (2 ^ 16 : ENNReal)) ^ 5516 := by
  calc
    _ ≤ errorTail +
        ((2 ^ lvl10PrefixDimension - 1) * Fintype.card Lvl10Suffix : ℕ) *
          ∏ row : Fin lvl10RowCount,
            ((centeredBall lvl10Modulus bound).card : ENNReal) /
              (lvl10Modulus : ENNReal) :=
      probEvent_lvl10_exhaustiveKSKDecoder_failure_le bound hbound
        prefixSampler suffixSampler errorSampler errorTail herrorTail
    _ ≤ errorTail +
        ((2 ^ lvl10PrefixDimension - 1) * Fintype.card Lvl10Suffix : ℕ) *
          ∏ _row : Fin lvl10RowCount,
            (((2 * bound + 1 : ℕ) : ENNReal) / (lvl10Modulus : ENNReal)) := by
      gcongr
      exact_mod_cast card_centeredBall_le lvl10Modulus bound
    _ = _ := by
      have hprefix : lvl10PrefixDimension = 630 := by
        rfl
      have hsuffix : Fintype.card Lvl10Suffix = 3 ^ 394 := by
        unfold Lvl10Suffix lvl10SuffixDimension
        rw [Parameters.suffixDimension_eq, Fintype.card_fun]
        simp only [Fintype.card_fin]
      have hrows : lvl10RowCount = 5516 := by
        exact lvl10RowCount_eq.trans Parameters.lvl10KSKRows_eq
      have hmodulus : lvl10Modulus = 2 ^ 16 := by
        rfl
      rw [hprefix, hsuffix, hrows, hmodulus]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      have hcast : ((2 ^ 16 : ℕ) : ENNReal) = (2 : ENNReal) ^ 16 := by
        norm_cast
      rw [hcast]

/-! ## Reduction to one scalar sampler tail -/

/-- Independent row errors built from one scalar executable sampler. -/
def lvl10IIDErrorSampler
    (scalarSampler : ProbComp (ZMod lvl10Modulus)) :
    ProbComp (Fin lvl10RowCount → ZMod lvl10Modulus) :=
  Fin.mOfFn lvl10RowCount fun _ ↦ scalarSampler

set_option maxRecDepth 20000 in
/-- A scalar centered-ball tail bound pays at most once per native KSK row. -/
theorem probEvent_lvl10IIDError_not_typical_le
    (bound : ℕ) (scalarSampler : ProbComp (ZMod lvl10Modulus))
    (scalarTail : ENNReal)
    (hscalarTail :
      Pr[(fun error ↦ error ∉ centeredBall lvl10Modulus bound) | scalarSampler] ≤
        scalarTail) :
    Pr[(fun error ↦ ¬errorsTypical
        (fun _ : Fin lvl10RowCount ↦ centeredBall lvl10Modulus bound) error) |
      lvl10IIDErrorSampler scalarSampler] ≤
      (lvl10RowCount : ENNReal) * scalarTail := by
  classical
  have hevent :
      (fun error : Fin lvl10RowCount → ZMod lvl10Modulus ↦
        ¬errorsTypical
          (fun _ : Fin lvl10RowCount ↦ centeredBall lvl10Modulus bound) error) =
      (fun error ↦ ∃ row ∈ (Finset.univ : Finset (Fin lvl10RowCount)),
        error row ∉ centeredBall lvl10Modulus bound) := by
    funext error
    apply propext
    simp [errorsTypical]
  rw [hevent]
  calc
    _ ≤ ∑ row ∈ (Finset.univ : Finset (Fin lvl10RowCount)),
        Pr[(fun error : Fin lvl10RowCount → ZMod lvl10Modulus ↦
            error row ∉ centeredBall lvl10Modulus bound) |
          lvl10IIDErrorSampler scalarSampler] :=
      probEvent_exists_finset_le_sum
        (Finset.univ : Finset (Fin lvl10RowCount))
        (lvl10IIDErrorSampler scalarSampler)
        (fun row error ↦ error row ∉ centeredBall lvl10Modulus bound)
    _ = ∑ _row : Fin lvl10RowCount,
        Pr[(fun error ↦ error ∉ centeredBall lvl10Modulus bound) | scalarSampler] := by
      apply Finset.sum_congr rfl
      intro row _
      exact FormalProof4FHE.FiniteProduct.probEvent_fin_mOfFn_apply
        lvl10RowCount (fun _ : Fin lvl10RowCount ↦ scalarSampler) row
        (fun error ↦ error ∉ centeredBall lvl10Modulus bound)
    _ ≤ ∑ _row : Fin lvl10RowCount, scalarTail := by
      exact Finset.sum_le_sum fun _ _ ↦ hscalarTail
    _ = (lvl10RowCount : ENNReal) * scalarTail := by
      simp [nsmul_eq_mul]

/-- At the concrete radius `127`, the top-row separation premise holds with a wide margin.  The
complete native KSK failure is bounded by the `5516` scalar tail charges plus an explicit
false-candidate term with residual density `255 / 2^16` per row. -/
theorem probEvent_lvl10_exhaustiveKSKDecoder_failure_le_radius127
    (prefixSampler : ProbComp (Prefix lvl10PrefixDimension))
    (suffixSampler : ProbComp Lvl10Suffix)
    (scalarSampler : ProbComp (ZMod lvl10Modulus))
    (scalarTail : ENNReal)
    (hscalarTail :
      Pr[(fun error ↦ error ∉ centeredBall lvl10Modulus 127) | scalarSampler] ≤
        scalarTail) :
    Pr[(fun sample ↦
        exhaustiveKSKDecoder
            (fun _ : Fin lvl10RowCount ↦ centeredBall lvl10Modulus 127)
            lvl10SuffixMessage sample.2 ≠ some sample.1) |
      nativeKSKKeyedSampler lvl10SuffixMessage prefixSampler suffixSampler
        (lvl10IIDErrorSampler scalarSampler)] ≤
      (5516 : ENNReal) * scalarTail +
        ((2 ^ 630 - 1) * 3 ^ 394 : ℕ) *
          ((255 : ENNReal) / (2 ^ 16 : ENNReal)) ^ 5516 := by
  have hbound : 2 * 127 < 2 ^ 14 := by norm_num
  have htail := probEvent_lvl10IIDError_not_typical_le
    127 scalarSampler scalarTail hscalarTail
  have hdecoder := probEvent_lvl10_exhaustiveKSKDecoder_failure_le_explicit
    127 hbound prefixSampler suffixSampler (lvl10IIDErrorSampler scalarSampler)
      ((lvl10RowCount : ENNReal) * scalarTail) htail
  have hrows : lvl10RowCount = 5516 :=
    lvl10RowCount_eq.trans Parameters.lvl10KSKRows_eq
  have hrowsCast : (lvl10RowCount : ENNReal) = 5516 := by
    exact_mod_cast hrows
  calc
    _ ≤ (lvl10RowCount : ENNReal) * scalarTail +
        ((2 ^ 630 - 1) * 3 ^ 394 : ℕ) *
          (((2 * 127 + 1 : ℕ) : ENNReal) / (2 ^ 16 : ENNReal)) ^ 5516 :=
      hdecoder
    _ = _ := by
      rw [hrowsCast]
      norm_num only

/-! ## Sampler-exact centered-binomial corollary -/

/-- Any centered-binomial scalar sampler of width at most `127` lies in the selected ball with
probability one. -/
theorem probEvent_centeredBinomial_not_mem_radius127_eq_zero
    (eta : ℕ) (heta : eta ≤ 127) :
    Pr[(fun error ↦ error ∉ centeredBall lvl10Modulus 127) |
      CenteredBinomial.scalarSampler lvl10Modulus eta] = 0 := by
  apply probEvent_eq_zero
  intro error herror houtside
  apply houtside
  rw [mem_centeredBall_iff]
  exact (Native.KeySwitchRecovery.centeredDistance_zero_le_of_scalarBounded
    (CenteredBinomial.scalarBounded_of_mem_support herror)).trans heta

/-- The concrete false-candidate term is at most `2^-42710`.  The deliberately coarse proof uses
`3^394 ≤ 4^394` and `255 / 2^16 ≤ 1 / 2^8`; it does not numerically expand either enormous
power. -/
theorem lvl10_radius127_falseCandidate_le_inv_twoPow :
    (((2 ^ 630 - 1) * 3 ^ 394 : ℕ) : ENNReal) *
        ((255 : ENNReal) / (2 ^ 16 : ENNReal)) ^ 5516 ≤
      1 / (2 : ENNReal) ^ 42710 := by
  have hcandidateNat :
      ((2 ^ 630 - 1) * 3 ^ 394 : ℕ) ≤ 2 ^ 1418 := by
    set_option exponentiation.threshold 2048 in
      calc
        _ ≤ 2 ^ 630 * 4 ^ 394 :=
          Nat.mul_le_mul (Nat.sub_le _ _)
            (Nat.pow_le_pow_left (by decide) _)
        _ = 2 ^ 1418 := by
          rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
  have hcandidate :
      (((2 ^ 630 - 1) * 3 ^ 394 : ℕ) : ENNReal) ≤
        (2 : ENNReal) ^ 1418 := by
    exact_mod_cast hcandidateNat
  have hdensity :
      (255 : ENNReal) / (2 ^ 16 : ENNReal) ≤
        1 / (2 ^ 8 : ENNReal) := by
    have h255 : (255 : ENNReal) ≤ 256 := by norm_num
    calc
      (255 : ENNReal) / (2 ^ 16) ≤ 256 / (2 ^ 16) :=
        ENNReal.div_le_div_right h255 _
      _ = ((256 : ENNReal) * 1) / (256 * 256) := by norm_num
      _ = 1 / 256 :=
        ENNReal.mul_div_mul_left 1 256 (by norm_num) (by norm_num)
      _ = 1 / (2 ^ 8) := by
        congr 1
        norm_num
  calc
    _ ≤ (2 : ENNReal) ^ 1418 *
        (1 / (2 ^ 8 : ENNReal)) ^ 5516 :=
      mul_le_mul' hcandidate (pow_le_pow_left₀ bot_le hdensity _)
    _ = 1 / (2 : ENNReal) ^ 42710 := by
      rw [one_div, ← ENNReal.inv_pow, ← pow_mul]
      norm_num only [show 8 * 5516 = 44128 by norm_num]
      rw [show 44128 = 1418 + 42710 by norm_num, pow_add,
        ENNReal.mul_inv (by left; positivity) (by left; simp)]
      rw [← mul_assoc, ENNReal.mul_inv_cancel (by positivity) (by simp),
        one_mul, one_div]

/-- With proof-aligned bounded centered-binomial KSK noise, the error-tail charge vanishes.  Thus
the concrete native KSK itself is information-theoretically decodable except for the displayed
uniform-column false-candidate term. -/
theorem probEvent_lvl10_centeredBinomial_exhaustiveKSKDecoder_failure_le
    (eta : ℕ) (heta : eta ≤ 127)
    (prefixSampler : ProbComp (Prefix lvl10PrefixDimension))
    (suffixSampler : ProbComp Lvl10Suffix) :
    Pr[(fun sample ↦
        exhaustiveKSKDecoder
            (fun _ : Fin lvl10RowCount ↦ centeredBall lvl10Modulus 127)
            lvl10SuffixMessage sample.2 ≠ some sample.1) |
      nativeKSKKeyedSampler lvl10SuffixMessage prefixSampler suffixSampler
        (lvl10IIDErrorSampler
          (CenteredBinomial.scalarSampler lvl10Modulus eta))] ≤
      ((2 ^ 630 - 1) * 3 ^ 394 : ℕ) *
        ((255 : ENNReal) / (2 ^ 16 : ENNReal)) ^ 5516 := by
  have htail :
      Pr[(fun error ↦ error ∉ centeredBall lvl10Modulus 127) |
        CenteredBinomial.scalarSampler lvl10Modulus eta] ≤ (0 : ENNReal) := by
    rw [probEvent_centeredBinomial_not_mem_radius127_eq_zero eta heta]
  have hdecoder := probEvent_lvl10_exhaustiveKSKDecoder_failure_le_radius127
    prefixSampler suffixSampler
      (CenteredBinomial.scalarSampler lvl10Modulus eta) 0 htail
  calc
    _ ≤ (5516 : ENNReal) * 0 +
        ((2 ^ 630 - 1) * 3 ^ 394 : ℕ) *
          ((255 : ENNReal) / (2 ^ 16 : ENNReal)) ^ 5516 := hdecoder
    _ = _ := by rw [mul_zero, zero_add]

/-- Numerical sampler-exact corollary: with bounded centered-binomial row errors, exhaustive
native KSK recovery fails with probability at most `2^-42710`. -/
theorem probEvent_lvl10_centeredBinomial_exhaustiveKSKDecoder_failure_le_inv_twoPow
    (eta : ℕ) (heta : eta ≤ 127)
    (prefixSampler : ProbComp (Prefix lvl10PrefixDimension))
    (suffixSampler : ProbComp Lvl10Suffix) :
    Pr[(fun sample ↦
        exhaustiveKSKDecoder
            (fun _ : Fin lvl10RowCount ↦ centeredBall lvl10Modulus 127)
            lvl10SuffixMessage sample.2 ≠ some sample.1) |
      nativeKSKKeyedSampler lvl10SuffixMessage prefixSampler suffixSampler
        (lvl10IIDErrorSampler
          (CenteredBinomial.scalarSampler lvl10Modulus eta))] ≤
      1 / (2 : ENNReal) ^ 42710 := by
  exact (probEvent_lvl10_centeredBinomial_exhaustiveKSKDecoder_failure_le
    eta heta prefixSampler suffixSampler).trans
      lvl10_radius127_falseCandidate_le_inv_twoPow

end

end FormalProof4FHE.TFHE.NativeTRGSWConcreteSuffixSeparation
