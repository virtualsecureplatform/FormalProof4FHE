/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.WeightedSampler
import FormalProof4FHE.Probability.DiscreteGaussianTail
import Mathlib.Data.Rat.Floor

/-!
# Computable integer approximations to Gaussian weights

A positive Taylor sum approximates `exp x` on `[0,1]`; its rational reciprocal
approximates `exp (-x)` from above. Raising that reciprocal to a polynomially
bounded natural power handles the exponent at the squared-width cutoff.
Dyadic quantization produces stored natural weights without evaluating a real
exponential. The pointwise analytic error and finite representation bounds
are distinct from a complete normalized TV and machine-bit complexity proof.
-/

open scoped BigOperators ENNReal

namespace FormalProof4FHE.GaussianIntegerWeights

/-- Finite rational Taylor sum, including the constant term. -/
def taylor (precision : ℕ) (argument : ℚ) : ℚ :=
  ∑ index ∈ Finset.range (precision + 2), argument ^ index / (index.factorial : ℚ)

/-- Rational approximation to `exp (-argument)`, before range expansion. -/
def reciprocalTaylor (precision : ℕ) (argument : ℚ) : ℚ :=
  (taylor precision argument)⁻¹

theorem cast_taylor (precision : ℕ) (argument : ℚ) :
    (taylor precision argument : ℝ) =
      ∑ index ∈ Finset.range (precision + 2), (argument : ℝ) ^ index / (index.factorial : ℝ) := by
  simp [taylor]

theorem taylor_ge_one (precision : ℕ) (argument : ℚ) (hargument : 0 ≤ argument) :
    1 ≤ taylor precision argument := by
  have hzero : (0 : ℕ) ∈ Finset.range (precision + 2) := by simp
  have h := Finset.single_le_sum (f := fun index : ℕ ↦ argument ^ index / (index.factorial : ℚ))
    (fun index _ ↦ div_nonneg (pow_nonneg hargument _) (Nat.cast_nonneg _)) hzero
  simpa [taylor] using h

theorem reciprocalTaylor_pos (precision : ℕ) (argument : ℚ) (hargument : 0 ≤ argument) :
    0 < reciprocalTaylor precision argument := by
  exact inv_pos.mpr (lt_of_lt_of_le zero_lt_one (taylor_ge_one precision argument hargument))

theorem reciprocalTaylor_le_one (precision : ℕ) (argument : ℚ) (hargument : 0 ≤ argument) :
    reciprocalTaylor precision argument ≤ 1 := by
  simpa [reciprocalTaylor] using
    inv_le_one_of_one_le₀ (taylor_ge_one precision argument hargument)

/-- Elementary factorial growth supplies an explicit binary precision bound. -/
theorem factorial_ge_two_pow (precision : ℕ) :
    2 ^ (precision + 1) ≤ (precision + 2).factorial := by
  induction precision with
  | zero => norm_num
  | succ precision ih =>
    rw [show precision + 1 + 2 = (precision + 2) + 1 by omega, Nat.factorial_succ]
    rw [show precision + 1 + 1 = (precision + 1) + 1 by omega, pow_succ]
    nlinarith [Nat.factorial_pos (precision + 2)]

/-- Taylor's analytic remainder is at most `2^-precision` on `[0,1]`. -/
theorem taylor_remainder_le (precision : ℕ) (argument : ℚ)
    (hargument : 0 ≤ argument) (hargumentOne : argument ≤ 1) :
    Real.exp argument - (taylor precision argument : ℝ) ≤
      1 / (2 : ℝ) ^ precision := by
  have ha : (0 : ℝ) ≤ argument := by exact_mod_cast hargument
  have ha1 : (argument : ℝ) ≤ 1 := by exact_mod_cast hargumentOne
  have h := Real.exp_bound (show |(argument : ℝ)| ≤ 1 by simpa [abs_of_nonneg ha])
    (show 0 < precision + 2 by omega)
  rw [abs_of_nonneg ha, ← cast_taylor] at h
  have hpow : (argument : ℝ) ^ (precision + 2) ≤ 1 := pow_le_one₀ ha ha1
  have hf : (2 : ℝ) ^ (precision + 1) ≤ ((precision + 2).factorial : ℝ) := by
    exact_mod_cast factorial_ge_two_pow precision
  have hn : (0 : ℝ) < precision + 2 := by positivity
  have hfactor : (0 : ℝ) < (precision + 2).factorial := by positivity
  have hratio : ((precision + 2 + 1 : ℕ) : ℝ) /
      ((precision + 2).factorial * (precision + 2) : ℝ) ≤
      2 / (precision + 2).factorial := by
    apply (div_le_div_iff₀ (by positivity) hfactor).2
    push_cast
    nlinarith
  have hscaled : (argument : ℝ) ^ (precision + 2) *
      ((precision + 2 + 1 : ℕ) : ℝ) /
      ((precision + 2).factorial * (precision + 2) : ℝ) ≤
      2 / (precision + 2).factorial := by
    calc
      _ ≤ ((precision + 2 + 1 : ℕ) : ℝ) /
          ((precision + 2).factorial * (precision + 2) : ℝ) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_of_le_one_left (by positivity) hpow
      _ ≤ _ := hratio
  have hbinary : 2 / ((precision + 2).factorial : ℝ) ≤ 1 / (2 : ℝ) ^ precision := by
    apply (div_le_div_iff₀ hfactor (by positivity)).2
    simpa [pow_succ, mul_comm] using hf
  exact (le_abs_self _).trans (h.trans (by
    simpa [mul_div_assoc] using hscaled.trans hbinary))

/-- The reciprocal approximation lies above the target exponential. -/
theorem exp_neg_le_reciprocalTaylor (precision : ℕ) (argument : ℚ)
    (hargument : 0 ≤ argument) :
    Real.exp (-(argument : ℝ)) ≤ (reciprocalTaylor precision argument : ℝ) := by
  have ht : (0 : ℝ) < taylor precision argument := by
    exact_mod_cast lt_of_lt_of_le zero_lt_one (taylor_ge_one precision argument hargument)
  rw [Real.exp_neg, reciprocalTaylor, Rat.cast_inv]
  apply inv_anti₀ ht
  rw [cast_taylor]
  apply Real.sum_le_exp_of_nonneg
  exact_mod_cast hargument

/-- Taking reciprocals does not enlarge the error when both positive denominators are at least one. -/
theorem reciprocalTaylor_error_le (precision : ℕ) (argument : ℚ)
    (hargument : 0 ≤ argument) (hargumentOne : argument ≤ 1) :
    |(reciprocalTaylor precision argument : ℝ) - Real.exp (-(argument : ℝ))| ≤
      1 / (2 : ℝ) ^ precision := by
  have hsum : (1 : ℝ) ≤ taylor precision argument := by
    exact_mod_cast taylor_ge_one precision argument hargument
  have hexp : (taylor precision argument : ℝ) ≤ Real.exp argument := by
    rw [cast_taylor]
    apply Real.sum_le_exp_of_nonneg
    exact_mod_cast hargument
  have hrem := taylor_remainder_le precision argument hargument hargumentOne
  have hinv := exp_neg_le_reciprocalTaylor precision argument hargument
  rw [abs_of_nonneg (sub_nonneg.mpr hinv)]
  rw [reciprocalTaylor, Rat.cast_inv, Real.exp_neg]
  have hsumpos : (0 : ℝ) < taylor precision argument := by linarith
  have hexppos := Real.exp_pos (argument : ℝ)
  have hden : (1 : ℝ) ≤ (taylor precision argument : ℝ) * Real.exp argument := by nlinarith
  have hid : (taylor precision argument : ℝ)⁻¹ - (Real.exp argument)⁻¹ =
      (Real.exp argument - (taylor precision argument : ℝ)) /
        ((taylor precision argument : ℝ) * Real.exp argument) := by
    field_simp
  rw [hid]
  exact (div_le_self (sub_nonneg.mpr hexp) hden).trans hrem

/-- Raising two numbers in the unit interval multiplies their absolute error by at most the exponent. -/
theorem power_error_le {first second : ℝ} (hfirst : 0 ≤ first) (hfirstOne : first ≤ 1)
    (hsecond : 0 ≤ second) (hsecondOne : second ≤ 1) (power : ℕ) :
    |first ^ power - second ^ power| ≤ power * |first - second| := by
  have h := abs_pow_sub_pow_le first second power
  have hmax : max |first| |second| ≤ 1 := by
    simp only [abs_of_nonneg hfirst, abs_of_nonneg hsecond]
    exact max_le hfirstOne hsecondOne
  have hmaxnonneg : 0 ≤ max |first| |second| := le_trans (abs_nonneg first) (le_max_left _ _)
  have hp : max |first| |second| ^ (power - 1) ≤ 1 := pow_le_one₀ hmaxnonneg hmax
  calc
    _ ≤ |first - second| * power * max |first| |second| ^ (power - 1) := h
    _ ≤ |first - second| * power := mul_le_of_le_one_right (by positivity) hp
    _ = _ := by ring

/-- A fixed range-expansion exponent, polynomial in the integer Gaussian width. -/
def expansionPower (width : ℕ) : ℕ := width ^ 2 + 1

/-- A rational argument at most one for every error inside the squared-width cutoff. -/
def reducedArgument (width : ℕ) (value : ℤ) : ℚ :=
  (value : ℚ) ^ 2 / (2 * (width : ℚ) ^ 2 * expansionPower width)

/-- Unnormalized rational Gaussian weight approximation. -/
def rationalWeight (width precision : ℕ) (value : ℤ) : ℚ :=
  reciprocalTaylor precision (reducedArgument width value) ^ expansionPower width

/-- Quantized integer weight, stored directly rather than expanded into repeated tickets. -/
def integerWeight (width precision : ℕ) (value : ℤ) : ℕ :=
  ⌊(2 : ℚ) ^ precision * rationalWeight width precision value⌋₊


theorem reducedArgument_nonneg (width : ℕ) (value : ℤ) :
    0 ≤ reducedArgument width value := by
  unfold reducedArgument
  positivity

theorem reducedArgument_le_one (width : ℕ) (hwidth : 0 < width) (value : ℤ)
    (hvalue : value.natAbs ≤ width ^ 2) : reducedArgument width value ≤ 1 := by
  have hw : (0 : ℚ) < width := by exact_mod_cast hwidth
  have hm : (0 : ℚ) < expansionPower width := by unfold expansionPower; positivity
  have habs : |(value : ℚ)| ≤ (width : ℚ) ^ 2 := by
    have h : (value.natAbs : ℚ) ≤ (width : ℚ) ^ 2 := by exact_mod_cast hvalue
    simpa only [Nat.cast_natAbs, Int.cast_abs] using h
  have hsquare := pow_le_pow_left₀ (abs_nonneg (value : ℚ)) habs 2
  rw [sq_abs] at hsquare
  unfold reducedArgument
  apply (div_le_one (by positivity : (0 : ℚ) < 2 * (width : ℚ) ^ 2 * expansionPower width)).2
  unfold expansionPower
  push_cast
  nlinarith [sq_nonneg (width : ℚ)]

theorem rationalWeight_pos (width precision : ℕ) (value : ℤ) :
    0 < rationalWeight width precision value := by
  apply pow_pos
  exact reciprocalTaylor_pos precision _ (reducedArgument_nonneg width value)

theorem rationalWeight_le_one (width precision : ℕ) (value : ℤ) :
    rationalWeight width precision value ≤ 1 :=
  pow_le_one₀ (le_of_lt (reciprocalTaylor_pos precision _ (reducedArgument_nonneg width value)))
    (reciprocalTaylor_le_one precision _ (reducedArgument_nonneg width value))

/-- Pointwise analytic error of the actual rational computation at the correctness cutoff. -/
theorem rationalWeight_error_le (width precision : ℕ) (hwidth : 0 < width) (value : ℤ)
    (hvalue : value.natAbs ≤ width ^ 2) :
    |(rationalWeight width precision value : ℝ) -
      Real.exp (-((value : ℝ) ^ 2) / (2 * (width : ℝ) ^ 2))| ≤
      (expansionPower width : ℝ) / (2 : ℝ) ^ precision := by
  have harg := reducedArgument_nonneg width value
  have hargOne := reducedArgument_le_one width hwidth value hvalue
  have hbase : (0 : ℝ) ≤ reciprocalTaylor precision (reducedArgument width value) := by
    exact_mod_cast (reciprocalTaylor_pos precision _ harg).le
  have hbaseOne : (reciprocalTaylor precision (reducedArgument width value) : ℝ) ≤ 1 := by
    exact_mod_cast reciprocalTaylor_le_one precision _ harg
  have htargetOne : Real.exp (-(reducedArgument width value : ℝ)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    have hargReal : (0 : ℝ) ≤ reducedArgument width value := by exact_mod_cast harg
    linarith
  have hp := power_error_le hbase hbaseOne (Real.exp_nonneg _) htargetOne (expansionPower width)
  have herr := reciprocalTaylor_error_le precision _ harg hargOne
  have hw : (0 : ℝ) < width := by exact_mod_cast hwidth
  have hm : (0 : ℝ) < expansionPower width := by unfold expansionPower; positivity
  have hexponent : (expansionPower width : ℝ) * -(reducedArgument width value : ℝ) =
      -((value : ℝ) ^ 2) / (2 * (width : ℝ) ^ 2) := by
    unfold reducedArgument
    push_cast
    field_simp
  rw [← Real.exp_nat_mul, hexponent] at hp
  unfold rationalWeight
  rw [Rat.cast_pow]
  apply hp.trans
  have hscaled := mul_le_mul_of_nonneg_left herr (Nat.cast_nonneg (expansionPower width))
  calc
    _ ≤ (expansionPower width : ℝ) * (1 / (2 : ℝ) ^ precision) := hscaled
    _ = _ := by ring

/-- Natural flooring of a nonnegative rational costs at most one dyadic unit. -/
theorem quantization_error_le (precision : ℕ) (weight : ℚ) (hweight : 0 ≤ weight) :
    |((⌊(2 : ℚ) ^ precision * weight⌋₊ : ℕ) : ℚ) / (2 : ℚ) ^ precision - weight| ≤
      1 / (2 : ℚ) ^ precision := by
  have hd : (0 : ℚ) < (2 : ℚ) ^ precision := by positivity
  have hfloor := Nat.abs_floor_sub_le (mul_nonneg hd.le hweight)
  have hidentity : ((⌊(2 : ℚ) ^ precision * weight⌋₊ : ℕ) : ℚ) / (2 : ℚ) ^ precision - weight =
      (((⌊(2 : ℚ) ^ precision * weight⌋₊ : ℕ) : ℚ) - (2 : ℚ) ^ precision * weight) /
        (2 : ℚ) ^ precision := by field_simp
  rw [hidentity, abs_div, abs_of_pos hd]
  exact div_le_div_of_nonneg_right hfloor hd.le

/-- Pointwise weight error, including the actual integer quantization. -/
theorem integerWeight_error_le (width precision : ℕ) (hwidth : 0 < width) (value : ℤ)
    (hvalue : value.natAbs ≤ width ^ 2) :
    |(integerWeight width precision value : ℝ) / (2 : ℝ) ^ precision -
      Real.exp (-((value : ℝ) ^ 2) / (2 * (width : ℝ) ^ 2))| ≤
      ((expansionPower width : ℝ) + 1) / (2 : ℝ) ^ precision := by
  have hquant : |(integerWeight width precision value : ℝ) / (2 : ℝ) ^ precision -
      (rationalWeight width precision value : ℝ)| ≤ 1 / (2 : ℝ) ^ precision := by
    have hq := quantization_error_le precision (rationalWeight width precision value)
      (rationalWeight_pos width precision value).le
    have hr : ((|((⌊(2 : ℚ) ^ precision * rationalWeight width precision value⌋₊ : ℕ) : ℚ) /
        (2 : ℚ) ^ precision - rationalWeight width precision value| : ℚ) : ℝ) ≤
        ((1 / (2 : ℚ) ^ precision : ℚ) : ℝ) := by exact_mod_cast hq
    simpa only [integerWeight, Rat.cast_abs, Rat.cast_sub, Rat.cast_div, Rat.cast_natCast,
      Rat.cast_pow, Rat.cast_ofNat, Rat.cast_one] using hr
  calc
    _ ≤ |(integerWeight width precision value : ℝ) / (2 : ℝ) ^ precision -
          (rationalWeight width precision value : ℝ)| +
        |(rationalWeight width precision value : ℝ) -
          Real.exp (-((value : ℝ) ^ 2) / (2 * (width : ℝ) ^ 2))| := abs_sub_le _ _ _
    _ ≤ 1 / (2 : ℝ) ^ precision + (expansionPower width : ℝ) / (2 : ℝ) ^ precision :=
      add_le_add hquant (rationalWeight_error_le width precision hwidth value hvalue)
    _ = _ := by ring

theorem integerWeight_le (width precision : ℕ) (value : ℤ) :
    integerWeight width precision value ≤ 2 ^ precision := by
  unfold integerWeight
  apply Nat.floor_le_of_le
  push_cast
  exact mul_le_of_le_one_right (by positivity) (rationalWeight_le_one width precision value)

theorem taylor_zero (precision : ℕ) : taylor precision 0 = 1 := by
  unfold taylor
  rw [Finset.sum_eq_single 0]
  · simp
  · intro index _ hindex
    simp [zero_pow hindex]
  · intro hzero
    exact (hzero (by simp)).elim

theorem rationalWeight_zero (width precision : ℕ) : rationalWeight width precision 0 = 1 := by
  simp [rationalWeight, reducedArgument, reciprocalTaylor, taylor_zero]

theorem integerWeight_zero (width precision : ℕ) : integerWeight width precision 0 = 2 ^ precision := by
  rw [integerWeight, rationalWeight_zero, mul_one]
  have hcast : (2 : ℚ) ^ precision = ((2 ^ precision : ℕ) : ℚ) := by norm_cast
  rw [hcast, Nat.floor_natCast]

theorem integerWeight_neg (width precision : ℕ) (value : ℤ) :
    integerWeight width precision (-value) = integerWeight width precision value := by
  simp [integerWeight, rationalWeight, reducedArgument]

/-- Exactly one stored entry per integer in the interval `[-width²,width²]`. -/
def entries (width precision : ℕ) : List (ℤ × ℕ) :=
  (List.range (2 * width ^ 2 + 1)).map fun index : ℕ ↦
    let value : ℤ := (index : ℤ) - (width ^ 2 : ℕ)
    (value, integerWeight width precision value)

theorem entries_length (width precision : ℕ) : (entries width precision).length = 2 * width ^ 2 + 1 := by
  simp [entries]

theorem entries_zero_mem (width precision : ℕ) : (0, 2 ^ precision) ∈ entries width precision := by
  unfold entries
  apply List.mem_map.mpr
  refine ⟨width ^ 2, List.mem_range.mpr (show width ^ 2 < 2 * width ^ 2 + 1 by omega), ?_⟩
  simp [integerWeight_zero]

theorem entry_weight_le_total {entries : List (ℤ × ℕ)} {entry : ℤ × ℕ}
    (hentry : entry ∈ entries) : entry.2 ≤ WeightedSampler.totalWeight entries := by
  induction entries with
  | nil => simp at hentry
  | cons first rest ih =>
    rcases List.mem_cons.mp hentry with hfirst | hrest
    · subst entry
      exact Nat.le_add_right _ _
    · exact (ih hrest).trans (Nat.le_add_left _ _)

theorem totalWeight_pos (width precision : ℕ) : 0 < WeightedSampler.totalWeight (entries width precision) := by
  have h := entry_weight_le_total (entries_zero_mem width precision)
  exact lt_of_lt_of_le (by change 0 < 2 ^ precision; positivity) h

/-- Computable finite integer-error table with polynomial entry count. -/
def table (width precision : ℕ) : WeightedSampler.Table ℤ where
  fallback := 0
  entries := entries width precision
  total_pos := totalWeight_pos width precision

theorem entries_bounded (width precision : ℕ) (entry : ℤ × ℕ)
    (hentry : entry ∈ entries width precision) : entry.1.natAbs ≤ width ^ 2 := by
  unfold entries at hentry
  obtain ⟨index, hindex, rfl⟩ := List.mem_map.mp hentry
  have hi := List.mem_range.mp hindex
  change ((index : ℤ) - (width ^ 2 : ℕ)).natAbs ≤ width ^ 2
  apply Int.ofNat_le.mp
  rw [Int.natCast_natAbs, abs_le]
  constructor <;> omega

theorem entries_weights_le (width precision : ℕ) (entry : ℤ × ℕ)
    (hentry : entry ∈ entries width precision) : entry.2 ≤ 2 ^ precision := by
  unfold entries at hentry
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp hentry
  exact integerWeight_le width precision _

/-- Denominator size is bounded despite potentially exponentially large ticket counts. -/
theorem table_ticketCount_lt (width precision : ℕ) :
    (table width precision).ticketCount < 2 ^ (precision + 2 * width ^ 2 + 1) := by
  have h := WeightedSampler.totalWeight_lt_two_pow (entries width precision) precision
    (entries_weights_le width precision)
  simpa [table, WeightedSampler.Table.ticketCount, entries_length, Nat.add_assoc] using h

/-- The generated integer noise always stays inside the squared-width correctness budget. -/
theorem table_tail_eq_zero (width precision : ℕ) :
    Pr[(fun value : ℤ ↦ width ^ 2 < value.natAbs) | (table width precision).sampler] = 0 := by
  apply WeightedSampler.Table.probEvent_eq_zero_of_entries
  intro entry hentry
  exact not_lt_of_ge (entries_bounded width precision entry hentry)


/-- Mapping outcomes preserves the compressed denominator. -/
theorem totalWeight_map_values {Output Target : Type} (mapping : Output → Target)
    (stored : List (Output × ℕ)) :
    WeightedSampler.totalWeight (stored.map fun entry ↦ (mapping entry.1, entry.2)) =
      WeightedSampler.totalWeight stored := by
  induction stored with
  | nil => rfl
  | cons entry rest ih => simp [WeightedSampler.totalWeight, ih]

/-- Mapping outcomes commutes with the actual subtraction decoder, including its fallback. -/
theorem selectList_map_values {Output Target : Type} (mapping : Output → Target)
    (stored : List (Output × ℕ)) (fallback : Output) (ticket : ℕ) :
    WeightedSampler.selectList (stored.map fun entry ↦ (mapping entry.1, entry.2))
      (mapping fallback) ticket = mapping (WeightedSampler.selectList stored fallback ticket) := by
  induction stored generalizing ticket with
  | nil => rfl
  | cons entry rest ih =>
    rcases entry with ⟨value, weight⟩
    by_cases hhead : ticket < weight <;> simp [WeightedSampler.selectList, hhead, ih]

/-- The generated finite table for modular LWE errors. No rounding of the modulus is used. -/
def modularTable (modulus width precision : ℕ) : WeightedSampler.Table (ZMod modulus) where
  fallback := 0
  entries := (entries width precision).map fun entry : ℤ × ℕ ↦ ((entry.1 : ZMod modulus), entry.2)
  total_pos := by
    rw [totalWeight_map_values]
    exact totalWeight_pos width precision

theorem modularTable_entries_length (modulus width precision : ℕ) :
    (modularTable modulus width precision).entries.length = 2 * width ^ 2 + 1 := by
  simp [modularTable, entries_length]

theorem modularTable_ticketCount_lt (modulus width precision : ℕ) :
    (modularTable modulus width precision).ticketCount < 2 ^ (precision + 2 * width ^ 2 + 1) := by
  simpa [modularTable, WeightedSampler.Table.ticketCount, totalWeight_map_values, table] using
    table_ticketCount_lt width precision

set_option backward.isDefEq.respectTransparency false in
/-- This is the actual mapped sampler law, not only equality of marginal probabilities. -/
theorem modularTable_sampler_eq_map (modulus width precision : ℕ) :
    (modularTable modulus width precision).sampler =
      (fun value : ℤ ↦ (value : ZMod modulus)) <$> (table width precision).sampler := by
  have hcount : (modularTable modulus width precision).ticketCount =
      (table width precision).ticketCount := by
    exact totalWeight_map_values (fun value : ℤ ↦ (value : ZMod modulus))
      (entries width precision)
  unfold WeightedSampler.Table.sampler
  rw [hcount, Functor.map_map]
  congr 1
  funext ticket
  simpa only [modularTable, table, Int.cast_zero] using
    selectList_map_values (fun value : ℤ ↦ (value : ZMod modulus))
      (entries width precision) 0 ticket.val

/-- Modular reduction never increases the original bounded integer error. -/
theorem modularTable_entries_bounded (modulus width precision : ℕ) [NeZero modulus]
    (entry : ZMod modulus × ℕ) (hentry : entry ∈ (modularTable modulus width precision).entries) :
    (LatticeCrypto.centeredRepr entry.1).natAbs ≤ width ^ 2 := by
  obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hentry
  exact (TFHE.NoiseBounds.centeredRepr_intCast_natAbs_le original.1).trans
    (entries_bounded width precision original horiginal)

theorem modularTable_tail_eq_zero (modulus width precision : ℕ) [NeZero modulus] :
    Pr[(fun value : ZMod modulus ↦ width ^ 2 < (LatticeCrypto.centeredRepr value).natAbs) |
      (modularTable modulus width precision).sampler] = 0 := by
  apply WeightedSampler.Table.probEvent_eq_zero_of_entries
  intro entry hentry
  exact not_lt_of_ge (modularTable_entries_bounded modulus width precision entry hentry)


/-- Polynomially growing precision for the one-secret-key GSW parameter family. -/
def familyPrecision (dimension : ℕ) : ℕ := (dimension + 1) ^ 2

/-- Explicit unnormalized, per-stored-error weight approximation envelope. -/
noncomputable def pointwiseErrorBound (dimension : ℕ) : ℝ :=
  (((dimension + 1) ^ 2 + 2 : ℕ) : ℝ) / (2 : ℝ) ^ familyPrecision dimension

theorem family_integerWeight_error_le (dimension : ℕ) (value : ℤ)
    (hvalue : value.natAbs ≤ (dimension + 1) ^ 2) :
    |(integerWeight (dimension + 1) (familyPrecision dimension) value : ℝ) /
        (2 : ℝ) ^ familyPrecision dimension -
      Real.exp (-((value : ℝ) ^ 2) / (2 * ((dimension + 1 : ℕ) : ℝ) ^ 2))| ≤
      pointwiseErrorBound dimension := by
  have h := integerWeight_error_le (dimension + 1) (familyPrecision dimension) (by omega) value hvalue
  have hbound : ((expansionPower (dimension + 1) : ℝ) + 1) /
      (2 : ℝ) ^ familyPrecision dimension = pointwiseErrorBound dimension := by
    unfold expansionPower pointwiseErrorBound
    push_cast
    ring
  rw [hbound] at h
  exact h

theorem pointwiseErrorBound_le_half_pow (dimension : ℕ) :
    pointwiseErrorBound dimension ≤ (((dimension + 1) ^ 2 + 2 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ dimension := by
  have hexponent : dimension ≤ (dimension + 1) ^ 2 := by nlinarith
  have h := pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) ≤ 1) hexponent
  have hdiv : 1 / (2 : ℝ) ^ ((dimension + 1) ^ 2) = (1 / 2 : ℝ) ^ ((dimension + 1) ^ 2) := by
    rw [one_div_pow]
  calc
    _ = (((dimension + 1) ^ 2 + 2 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ ((dimension + 1) ^ 2) := by
      unfold pointwiseErrorBound familyPrecision
      rw [div_eq_mul_one_div, hdiv]
    _ ≤ _ := mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)

/-- The computed weights have negligible uniform pointwise error at squared precision.
This statement is about unnormalized weights; a normalized TV certificate is still required. -/
theorem pointwiseErrorBound_negligible :
    negligible (fun dimension ↦ ENNReal.ofReal (pointwiseErrorBound dimension)) := by
  apply negligible_of_le (g := fun dimension ↦
    (((dimension + 1) ^ 2 + 2 : ℕ) : ℝ≥0∞) * ENNReal.ofReal ((1 / 2 : ℝ) ^ dimension))
  · intro dimension
    have h := ENNReal.ofReal_le_ofReal (pointwiseErrorBound_le_half_pow dimension)
    simpa only [ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast] using h
  · have h := negligible_polynomial_mul DiscreteGaussianTail.half_pow_negligible
      (((Polynomial.X + 1) ^ 2 + 2) : Polynomial ℕ)
    simpa using h

/-- For the chosen precision, the ticket denominator has at most `3*(dimension+1)^2+1` bits. -/
theorem family_ticketCount_lt (modulus dimension : ℕ) :
    (modularTable modulus (dimension + 1) (familyPrecision dimension)).ticketCount <
      2 ^ (3 * (dimension + 1) ^ 2 + 1) := by
  have h := modularTable_ticketCount_lt modulus (dimension + 1) (familyPrecision dimension)
  have hsum : familyPrecision dimension + 2 * (dimension + 1) ^ 2 + 1 =
      3 * (dimension + 1) ^ 2 + 1 := by unfold familyPrecision; omega
  rw [hsum] at h
  exact h

end FormalProof4FHE.GaussianIntegerWeights
