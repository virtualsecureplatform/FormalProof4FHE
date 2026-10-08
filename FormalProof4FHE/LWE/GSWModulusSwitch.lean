/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.GSWAccumulator

/-!
# Public scaled modulus reduction for the same-key GSW lookup

For `Q = factor * p`, reduce each public coefficient by unsigned floor division by
`factor`. This is a scaled reduction, not the ring map from `ZMod Q` to `ZMod p`.
For a binary secret of dimension `n`, the total rounding residual has centered
magnitude at most `(n + 1) * (factor - 1)`. An exact additive embedding back into
`ZMod Q` gives the bit-preservation bound without any probabilistic or independence
assumption. The secret is unchanged. These are correctness results only; no claim
about ordinary-LWE security of the same-key bootstrapping controls is made here.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.LWE.GSWModulusSwitch

open TFHE.BootstrappingCorrectness

/-- Executable public coefficient reduction. -/
def down (factor p : ℕ) (value : ZMod (factor * p)) : ZMod p :=
  (value.val / factor : ZMod p)

/-- Proof-facing additive embedding, multiplying small-modulus values by `factor`. -/
noncomputable def up (factor p : ℕ) : ZMod p →+ ZMod (factor * p) :=
  ZMod.lift p ⟨{
    toFun := fun value : ℤ ↦ (factor : ZMod (factor * p)) * (value : ZMod (factor * p))
    map_zero' := by simp
    map_add' := by intros; simp [mul_add] }, by
      change (factor : ZMod (factor * p)) * ((p : ℤ) : ZMod (factor * p)) = 0
      rw [Int.cast_natCast]
      rw [← Nat.cast_mul]
      simp⟩

@[simp]
theorem up_natCast (factor p value : ℕ) :
    up factor p (value : ZMod p) = (factor * value : ℕ) := by
  unfold up
  rw [show (value : ZMod p) = ((value : ℤ) : ZMod p) by simp, ZMod.lift_coe]
  simp [Nat.cast_mul]

theorem up_eq_val (factor p : ℕ) [NeZero p] (value : ZMod p) :
    up factor p value = (factor * value.val : ℕ) := by
  conv_lhs => rw [← ZMod.natCast_zmod_val value]
  exact up_natCast factor p value.val

/-- The embedding has no unsigned wraparound. -/
theorem val_up (factor p : ℕ) [NeZero factor] [NeZero p] (value : ZMod p) :
    (up factor p value).val = factor * value.val := by
  rw [up_eq_val, ZMod.val_natCast_of_lt]
  exact Nat.mul_lt_mul_of_pos_left value.val_lt (NeZero.pos factor)

/-- Exact norm scaling, including the half-modulus tie. -/
theorem centered_up (factor p : ℕ) [NeZero factor] [NeZero p] (value : ZMod p) :
    (LatticeCrypto.centeredRepr (up factor p value)).natAbs =
      factor * (LatticeCrypto.centeredRepr value).natAbs := by
  simp only [LatticeCrypto.centeredRepr_eq_valMinAbs, ZMod.valMinAbs_natAbs_eq_min]
  rw [val_up, ← Nat.mul_sub_left_distrib, min_mul_mul_left]

/-- One coefficient's exact floor-division residual in the original coefficient ring. -/
theorem up_down (factor p : ℕ) [NeZero factor] [NeZero p] (value : ZMod (factor * p)) :
    up factor p (down factor p value) = value - (value.val % factor : ℕ) := by
  rw [down, up_natCast]
  have hdivision := Nat.mod_add_div value.val factor
  have hcast := congrArg (fun number : ℕ ↦ (number : ZMod (factor * p))) hdivision
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val] at hcast
  simp only [Nat.cast_mul]
  linear_combination hcast

/-- Public LWE phase after reducing the mask and body, under the original binary bits. -/
def switchedPhase {dimension : ℕ} (factor p : ℕ) (bits : Fin dimension → Bool)
    (mask : Fin dimension → ZMod (factor * p)) (body : ZMod (factor * p)) : ZMod p :=
  down factor p body - dotProduct (GSWSelfKey.binaryEmbed bits) (down factor p ∘ mask)

/-- Residuals are proof-only; the evaluator does not receive the secret bits. -/
def residual {dimension : ℕ} (factor p : ℕ) (bits : Fin dimension → Bool)
    (mask : Fin dimension → ZMod (factor * p)) (body : ZMod (factor * p)) :
    ZMod (factor * p) :=
  (body.val % factor : ℕ) -
    ∑ index, if bits index then ((mask index).val % factor : ZMod (factor * p)) else 0

/-- Exact phase law for public scaled rounding with one unchanged secret. -/
theorem up_switchedPhase {dimension : ℕ} (factor p : ℕ) [NeZero factor] [NeZero p]
    (bits : Fin dimension → Bool)
    (mask : Fin dimension → ZMod (factor * p)) (body : ZMod (factor * p)) :
    up factor p (switchedPhase factor p bits mask body) =
      body - dotProduct (GSWSelfKey.binaryEmbed bits) mask -
        residual factor p bits mask body := by
  have hsmall : dotProduct (GSWSelfKey.binaryEmbed bits) (down factor p ∘ mask) =
      ∑ index, if bits index then down factor p (mask index) else 0 := by
    apply Finset.sum_congr rfl
    intro index _
    cases hbit : bits index <;> simp [GSWSelfKey.binaryEmbed, hbit]
  have hlarge : dotProduct (GSWSelfKey.binaryEmbed bits) mask =
      ∑ index, if bits index then mask index else 0 := by
    apply Finset.sum_congr rfl
    intro index _
    cases hbit : bits index <;> simp [GSWSelfKey.binaryEmbed, hbit]
  simp only [switchedPhase, hsmall, map_sub, map_sum, up_down, hlarge, residual]
  have hterms : (∑ index, up factor p (if bits index then down factor p (mask index) else 0)) =
      (∑ index, if bits index then mask index else 0) -
        ∑ index, if bits index then ((mask index).val % factor : ZMod (factor * p)) else 0 := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro index _
    cases bits index <;> simp [up_down]
  rw [hterms]
  ring

/-- Deterministic bound; correlated mask coefficients and residuals are allowed. -/
theorem residual_bound {dimension : ℕ} (factor p : ℕ) [NeZero factor] [NeZero p]
    (bits : Fin dimension → Bool) (mask : Fin dimension → ZMod (factor * p))
    (body : ZMod (factor * p)) :
    (LatticeCrypto.centeredRepr (residual factor p bits mask body)).natAbs ≤
      (dimension + 1) * (factor - 1) := by
  have hrem : ∀ value : ZMod (factor * p),
      (LatticeCrypto.centeredRepr (value.val % factor : ZMod (factor * p))).natAbs ≤ factor - 1 := by
    intro value
    exact (TFHE.NoiseBounds.centeredRepr_natCast_natAbs_le _).trans
      (by have := Nat.mod_lt value.val (NeZero.pos factor); omega)
  have hterm : ∀ index : Fin dimension,
      (LatticeCrypto.centeredRepr
        (if bits index then ((mask index).val % factor : ZMod (factor * p)) else 0)).natAbs ≤ factor - 1 := by
    intro index
    cases hbit : bits index
    · simp [LatticeCrypto.centeredRepr_eq_valMinAbs]
    · simpa [hbit] using hrem (mask index)
  calc
    _ ≤ (LatticeCrypto.centeredRepr (body.val % factor : ZMod (factor * p))).natAbs +
        (LatticeCrypto.centeredRepr
          (∑ index, if bits index then ((mask index).val % factor : ZMod (factor * p)) else 0)).natAbs :=
      TFHE.NoiseBounds.centeredRepr_sub_natAbs_le _ _
    _ ≤ (factor - 1) + ∑ _index : Fin dimension, (factor - 1) := by
      apply Nat.add_le_add (hrem body)
      apply (TFHE.NoiseBounds.centeredRepr_finset_sum_natAbs_le _ _).trans
      exact Finset.sum_le_sum fun index _ ↦ hterm index
    _ = (dimension + 1) * (factor - 1) := by simp; ring

/-- Quantitative transfer of distance to any codeword with an exact scaled embedding. -/
theorem switchedPhase_distance {dimension : ℕ} (factor p : ℕ) [NeZero factor] [NeZero p]
    (bits : Fin dimension → Bool) (mask : Fin dimension → ZMod (factor * p))
    (body : ZMod (factor * p)) (code : ZMod p) (errorBound : ℕ)
    (hinput : centeredDistance (body - dotProduct (GSWSelfKey.binaryEmbed bits) mask)
      (up factor p code) ≤ errorBound) :
    factor * centeredDistance (switchedPhase factor p bits mask body) code ≤
      errorBound + (dimension + 1) * (factor - 1) := by
  rw [centeredDistance, ← centered_up]
  rw [map_sub, up_switchedPhase]
  have hrearrange : body - dotProduct (GSWSelfKey.binaryEmbed bits) mask -
      residual factor p bits mask body - up factor p code =
      (body - dotProduct (GSWSelfKey.binaryEmbed bits) mask - up factor p code) -
        residual factor p bits mask body := by ring
  rw [hrearrange]
  exact (TFHE.NoiseBounds.centeredRepr_sub_natAbs_le _ _).trans
    (Nat.add_le_add hinput (residual_bound factor p bits mask body))

/-- A strict scaled margin guarantees that public reduction preserves the input bit. -/
theorem decode_switchedPhase {dimension : ℕ} (factor p : ℕ) [NeZero factor] [NeZero p]
    (bits : Fin dimension → Bool) (mask : Fin dimension → ZMod (factor * p))
    (body : ZMod (factor * p)) (oneCode : ZMod p) (bit : Bool) (errorBound : ℕ)
    (hinput : centeredDistance (body - dotProduct (GSWSelfKey.binaryEmbed bits) mask)
      (up factor p (encodeBit 0 oneCode bit)) ≤ errorBound)
    (hmargin : 2 * (errorBound + (dimension + 1) * (factor - 1)) <
      factor * centeredDistance 0 oneCode) :
    decodeNearest 0 oneCode (switchedPhase factor p bits mask body) = bit := by
  have hbound := switchedPhase_distance factor p bits mask body
    (encodeBit 0 oneCode bit) errorBound hinput
  apply decodeNearest_encodeBit_of_distance_le 0 oneCode _
    (centeredDistance (switchedPhase factor p bits mask body) (encodeBit 0 oneCode bit)) bit
    _ le_rfl
  apply (Nat.mul_lt_mul_left (NeZero.pos factor)).mp
  nlinarith

end FormalProof4FHE.LWE.GSWModulusSwitch
