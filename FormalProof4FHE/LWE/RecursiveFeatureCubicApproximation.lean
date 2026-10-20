/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.RecursiveFeatureSecurityParameters

/-!
# A quantitative boundary for quadratic simulation of cubic controls

The exact cube-difference obstruction does not by itself exclude approximate
simulation on a uniform key distribution. Here every three-coordinate Boolean
slice has a discrepancy larger than a noise budget whenever eight times that
budget is smaller than the centered gadget weight. This forces failure on at
least one eighth of all binary keys, independently of the other coordinates.

The conclusion concerns approximation by fixed quadratic messages and coupling
under the SAME hidden key with bounded phase errors. It is not a distinguisher
for the public experiment and does not exclude other computational reductions.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.LWE.RecursiveFeatureCubicApproximation

open RecursiveFeatureGSW

def magnitude {q : ℕ} [NeZero q] (value : ZMod q) : ℕ :=
  (LatticeCrypto.centeredRepr value).natAbs

theorem difference3_sub {R : Type} [CommRing R] (first second : (Fin 3 → R) → R) :
    difference3 (fun secret ↦ first secret - second secret) = difference3 first - difference3 second := by
  simp only [difference3, mul_sub, Finset.sum_sub_distrib]

theorem magnitude_difference3_le {q : ℕ} [NeZero q] (function : (Fin 3 → ZMod q) → ZMod q)
    (bound : ℕ) (hbound : ∀ a b c, magnitude (function (corner3 a b c)) ≤ bound) :
    magnitude (difference3 function) ≤ 8 * bound := by
  have hsigned : ∀ a b c : Bool, magnitude
      ((if a then 1 else -1) * (if b then 1 else -1) * (if c then 1 else -1) *
        function (corner3 a b c)) ≤ bound := by
    intro a b c
    cases a <;> cases b <;> cases c <;>
      simpa [magnitude, LatticeCrypto.centeredRepr_natAbs_neg] using hbound _ _ _
  have hinner := fun a b ↦ RecursiveMultiplication.centered_sum_bound
    (fun c : Bool ↦ (if a then 1 else -1) * (if b then 1 else -1) * (if c then 1 else -1) *
      function (corner3 a b c)) bound (hsigned a b)
  have hmiddle := fun a ↦ RecursiveMultiplication.centered_sum_bound
    (fun b : Bool ↦ ∑ c : Bool, (if a then 1 else -1) * (if b then 1 else -1) * (if c then 1 else -1) *
      function (corner3 a b c)) (2 * bound) (by intro b; simpa using hinner a b)
  have houter := RecursiveMultiplication.centered_sum_bound
    (fun a : Bool ↦ ∑ b : Bool, ∑ c : Bool,
      (if a then 1 else -1) * (if b then 1 else -1) * (if c then 1 else -1) *
        function (corner3 a b c)) (4 * bound)
      (by intro a; simpa only [Fintype.card_bool, ← Nat.mul_assoc] using hmiddle a)
  simpa only [magnitude, difference3, Fintype.card_bool, ← Nat.mul_assoc] using houter

theorem exists_bad_corner {q : ℕ} [NeZero q] (weight : ZMod q)
    (polynomial : RecursiveQuadratic.Polynomial (ZMod q) 3 1) (bound : ℕ)
    (hweight : 8 * bound < magnitude weight) :
    ∃ a b c : Bool, bound < magnitude
      (weight * (corner3 a b c : Fin 3 → ZMod q) 0 * (corner3 a b c) 1 * (corner3 a b c) 2 -
        RecursiveQuadratic.message polynomial (corner3 a b c) 0) := by
  by_contra h
  push Not at h
  have hbound := magnitude_difference3_le
    (fun secret : Fin 3 → ZMod q ↦ weight * secret 0 * secret 1 * secret 2 -
      RecursiveQuadratic.message polynomial secret 0) bound h
  rw [difference3_sub, difference3_weighted_cubic, difference3_quadratic, sub_zero] at hbound
  omega

/-- Fix all but the first three coordinates of a quadratic message. -/
def restrictQuadratic {R : Type} [CommRing R] {k : ℕ}
    (polynomial : RecursiveQuadratic.Polynomial R (3 + k) 1) (tail : Fin k → R) :
    RecursiveQuadratic.Polynomial R 3 1 where
  quadratic := fun _ i j ↦ polynomial.quadratic 0 (i.castAdd k) (j.castAdd k)
  linear := fun _ i ↦ polynomial.linear 0 (i.castAdd k) +
    ∑ j : Fin k, tail j * (polynomial.quadratic 0 (i.castAdd k) (j.natAdd 3) +
      polynomial.quadratic 0 (j.natAdd 3) (i.castAdd k))
  constant := fun _ ↦
    dotProduct (vecMul tail (fun i j ↦ polynomial.quadratic 0 (i.natAdd 3) (j.natAdd 3))) tail +
      dotProduct (fun i ↦ polynomial.linear 0 (i.natAdd 3)) tail + polynomial.constant 0

theorem message_restrictQuadratic {R : Type} [CommRing R] {k : ℕ}
    (polynomial : RecursiveQuadratic.Polynomial R (3 + k) 1) (tail : Fin k → R) (secret : Fin 3 → R) :
    RecursiveQuadratic.message (restrictQuadratic polynomial tail) secret 0 =
      RecursiveQuadratic.message polynomial (Fin.append secret tail) 0 := by
  have hcross :
      (∑ x : Fin 3, ∑ i : Fin k,
        tail i * polynomial.quadratic 0 (x.castAdd k) (i.natAdd 3) * secret x) =
      ∑ i : Fin k, ∑ x : Fin 3,
        secret x * polynomial.quadratic 0 (x.castAdd k) (i.natAdd 3) * tail i := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro x _
    ring
  simp only [RecursiveQuadratic.message, restrictQuadratic, vecMul, dotProduct,
    Fin.sum_univ_add, Fin.append_left, Fin.append_right, Finset.sum_add_distrib,
    Finset.sum_mul, add_mul, mul_add]
  rw [hcross]
  ring

theorem binaryEmbed_append {R : Type} [CommRing R] {k : ℕ}
    (a b c : Bool) (tail : Fin k → Bool) :
    GSWSelfKey.binaryEmbed (R := R) (Fin.append ![a, b, c] tail) =
      Fin.append (corner3 a b c) (GSWSelfKey.binaryEmbed tail) := by
  funext index
  refine Fin.addCases ?_ ?_ index
  · intro i
    fin_cases i <;> simp [GSWSelfKey.binaryEmbed, corner3]
  · intro i
    simp [GSWSelfKey.binaryEmbed]

def discrepancy {q : ℕ} [NeZero q] {k : ℕ} (weight : ZMod q)
    (polynomial : RecursiveQuadratic.Polynomial (ZMod q) (3 + k) 1) (bits : Fin (3 + k) → Bool) : ℕ :=
  let secret := GSWSelfKey.binaryEmbed (R := ZMod q) bits
  magnitude (weight * secret 0 * secret 1 * secret 2 - RecursiveQuadratic.message polynomial secret 0)

/-- The discrepancy is for an actual quadratic-feature original-bit control column. -/
theorem control_discrepancy_eq {q : ℕ} [NeZero q] {k : ℕ} (params : RecursiveMultiplication.Parameters q)
    (level : Fin params.levels) (polynomial : RecursiveQuadratic.Polynomial (ZMod q) (3 + k) 1)
    (bits : Fin (3 + k) → Bool) :
    magnitude (controlMessage params (GSWSelfKey.binaryEmbed bits) 0 (some (.inr (1, 2))) level -
      RecursiveQuadratic.message polynomial (GSWSelfKey.binaryEmbed bits) 0) =
        discrepancy (TFHE.Gadget.Base.gadget params level) polynomial bits := by
  rw [controlMessage_quadratic]
  rfl

theorem exists_bad_slice {q : ℕ} [NeZero q] {k : ℕ} (weight : ZMod q)
    (polynomial : RecursiveQuadratic.Polynomial (ZMod q) (3 + k) 1) (tail : Fin k → Bool)
    (bound : ℕ) (hweight : 8 * bound < magnitude weight) :
    ∃ a b c : Bool, bound < discrepancy weight polynomial (Fin.append ![a, b, c] tail) := by
  have h := exists_bad_corner weight (restrictQuadratic polynomial (GSWSelfKey.binaryEmbed tail)) bound hweight
  simpa only [discrepancy, binaryEmbed_append, message_restrictQuadratic,
    show (0 : Fin (3 + k)) = (0 : Fin 3).castAdd k from rfl,
    show (1 : Fin (3 + k)) = (1 : Fin 3).castAdd k from by
      apply Fin.ext; simp [Nat.mod_eq_of_lt (by omega : 1 < 3 + k)],
    show (2 : Fin (3 + k)) = (2 : Fin 3).castAdd k from by
      apply Fin.ext; simp [Nat.mod_eq_of_lt (by omega : 2 < 3 + k)],
    Fin.append_left] using h

theorem bad_key_count {q : ℕ} [NeZero q] {k : ℕ} (weight : ZMod q)
    (polynomial : RecursiveQuadratic.Polynomial (ZMod q) (3 + k) 1) (bound : ℕ)
    (hweight : 8 * bound < magnitude weight) :
    2 ^ k ≤ (Finset.univ.filter fun bits : Fin (3 + k) → Bool ↦
      bound < discrepancy weight polynomial bits).card := by
  classical
  choose a b c hw using (fun tail : Fin k → Bool ↦ exists_bad_slice weight polynomial tail bound hweight)
  let embed : (Fin k → Bool) → {bits : Fin (3 + k) → Bool // bound < discrepancy weight polynomial bits} :=
    fun tail ↦ ⟨Fin.append ![a tail, b tail, c tail] tail, hw tail⟩
  have hinjective : Function.Injective embed := by
    intro first second heq
    have hbits := congrArg Subtype.val heq
    funext index
    have hindex := congrFun hbits (index.natAdd 3)
    simpa only [embed, Fin.append_right] using hindex
  have hcard := Fintype.card_le_of_injective embed hinjective
  simpa only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Fintype.card_subtype] using hcard

theorem bad_key_probability {q : ℕ} [NeZero q] {k : ℕ} (weight : ZMod q)
    (polynomial : RecursiveQuadratic.Polynomial (ZMod q) (3 + k) 1) (bound : ℕ)
    (hweight : 8 * bound < magnitude weight) :
    (1 / 8 : ℝ) ≤ (Pr[(fun bits : Fin (3 + k) → Bool ↦ bound < discrepancy weight polynomial bits) |
      ($ᵗ (Fin (3 + k) → Bool))]).toReal := by
  classical
  rw [probEvent_uniformSample, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow, Nat.cast_ofNat]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (3 + k))).mpr
  have hcount : (2 : ℝ) ^ k ≤
      ((Finset.univ.filter fun bits : Fin (3 + k) → Bool ↦ bound < discrepancy weight polynomial bits).card : ℝ) := by
    exact_mod_cast bad_key_count weight polynomial bound hweight
  rw [pow_add]
  norm_num
  linarith

/-- Two supported phase-error terms cannot absorb a message discrepancy larger than their sum. -/
theorem bounded_phase_errors_cannot_cancel {q : ℕ} [NeZero q]
    (cubic quadratic firstError secondError : ZMod q) (bound : ℕ)
    (hfirst : magnitude firstError ≤ bound) (hsecond : magnitude secondError ≤ bound)
    (hgap : 2 * bound < magnitude (cubic - quadratic)) :
    cubic + firstError ≠ quadratic + secondError := by
  intro heq
  have hdiff : cubic - quadratic = secondError - firstError := by linear_combination heq
  have hsub := TFHE.NoiseBounds.centeredRepr_sub_natAbs_le secondError firstError
  change magnitude (secondError - firstError) ≤ magnitude secondError + magnitude firstError at hsub
  rw [hdiff] at hgap
  omega

/-- This is a coupling obstruction with the hidden key fixed, not a public-key attack. -/
theorem bounded_ciphertext_coupling_bad_count {q : ℕ} [NeZero q] {k : ℕ} (weight : ZMod q)
    (polynomial : RecursiveQuadratic.Polynomial (ZMod q) (3 + k) 1) (bound : ℕ)
    (hweight : 8 * (2 * bound) < magnitude weight)
    (first second : (Fin (3 + k) → Bool) → RecursiveQuadratic.Ciphertext (ZMod q) (3 + k))
    (firstError secondError : (Fin (3 + k) → Bool) → ZMod q)
    (hfirst : ∀ bits, magnitude (firstError bits) ≤ bound)
    (hsecond : ∀ bits, magnitude (secondError bits) ≤ bound)
    (hfirstPhase : ∀ bits, let secret := GSWSelfKey.binaryEmbed (R := ZMod q) bits
      RecursiveQuadratic.decrypt secret (first bits) = weight * secret 0 * secret 1 * secret 2 + firstError bits)
    (hsecondPhase : ∀ bits, RecursiveQuadratic.decrypt (GSWSelfKey.binaryEmbed bits) (second bits) =
      RecursiveQuadratic.message polynomial (GSWSelfKey.binaryEmbed bits) 0 + secondError bits) :
    2 ^ k ≤ (Finset.univ.filter fun bits : Fin (3 + k) → Bool ↦ first bits ≠ second bits).card := by
  classical
  apply (bad_key_count weight polynomial (2 * bound) hweight).trans
  apply Finset.card_le_card
  intro bits hbits
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hbits ⊢
  intro heq
  have hphase := congrArg (RecursiveQuadratic.decrypt (GSWSelfKey.binaryEmbed (R := ZMod q) bits)) heq
  rw [hfirstPhase, hsecondPhase] at hphase
  exact bounded_phase_errors_cannot_cancel _ _ _ _ bound (hfirst bits) (hsecond bits) hbits hphase

open RecursiveQuadraticParameters RecursiveFeaturePublicKeyParameters

def topWeight (parameter : ℕ) : ZMod (modulus parameter) :=
  TFHE.Gadget.Base.gadget (params parameter) (level parameter)

def phaseErrorBound (parameter : ℕ) : ℕ := (dimension parameter + 1) * radius parameter

theorem magnitude_topWeight (parameter : ℕ) :
    magnitude (topWeight parameter) = modulus parameter / 2 := by
  simpa only [TFHE.BootstrappingCorrectness.centeredDistance, zero_sub,
    LatticeCrypto.centeredRepr_natAbs_neg, magnitude, topWeight] using gadget_distance parameter

theorem publicSamples_ge_eight (parameter : ℕ) : 8 ≤ publicSamples parameter := by
  have hscale : 1 ≤ scale parameter := by have := scale_pos parameter; omega
  have hdimension : 2 ≤ dimension parameter := by
    have hpow : 1 ≤ scale parameter ^ 5 := one_le_pow₀ hscale
    change 2 ≤ 2 * scale parameter ^ 5 * 1
    omega
  have hrows : 7 ≤ featureRows parameter := by
    change 7 ≤ dimension parameter * dimension parameter + dimension parameter + 1
    nlinarith
  have hlevels : 1 ≤ scale parameter ^ 2 := one_le_pow₀ hscale
  unfold publicSamples
  nlinarith

/-- The original fresh control phase bound is far below the robust cube threshold. -/
theorem eventually_top_weight_gap :
    ∀ᶠ parameter in Filter.atTop,
      8 * (2 * phaseErrorBound parameter) < magnitude (topWeight parameter) := by
  filter_upwards [eventually_public_quarter_margin] with parameter hmargin
  have hp := publicSamples_ge_eight parameter
  have hmargin' : 4 * publicSamples parameter * phaseErrorBound parameter < modulus parameter := by
    simpa only [selectorBound, phaseErrorBound, Nat.mul_assoc] using hmargin
  have h32 : 32 * phaseErrorBound parameter < modulus parameter := by
    nlinarith
  rw [magnitude_topWeight]
  have heven := RecursivePublicKeyParameters.modulus_eq_two_mul_half parameter
  omega

/-- Even a quadratic approximation within twice the fresh phase bound fails on a
constant fraction of uniform keys. This is not a lower bound on IND-CPA advantage. -/
theorem eventually_quadratic_approximation_failure :
    ∀ᶠ parameter in Filter.atTop, ∃ k : ℕ, dimension parameter = 3 + k ∧
      ∀ polynomial : RecursiveQuadratic.Polynomial (ZMod (modulus parameter)) (3 + k) 1,
        (1 / 8 : ℝ) ≤ (Pr[(fun bits : Fin (3 + k) → Bool ↦
          2 * phaseErrorBound parameter < discrepancy (topWeight parameter) polynomial bits) |
            ($ᵗ (Fin (3 + k) → Bool))]).toReal := by
  filter_upwards [eventually_top_weight_gap, Filter.eventually_ge_atTop 1] with parameter hgap hparameter
  have hscale : 2 ≤ scale parameter := by unfold scale; omega
  have hpower : 2 ^ 5 ≤ scale parameter ^ 5 := Nat.pow_le_pow_left hscale 5
  have hdimension : 3 ≤ dimension parameter := by
    change 3 ≤ 2 * scale parameter ^ 5 * 1
    norm_num at hpower
    omega
  refine ⟨dimension parameter - 3, by omega, ?_⟩
  intro polynomial
  exact bad_key_probability _ polynomial _ hgap

end FormalProof4FHE.LWE.RecursiveFeatureCubicApproximation
