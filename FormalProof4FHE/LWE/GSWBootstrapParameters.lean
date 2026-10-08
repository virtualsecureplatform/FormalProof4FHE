/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.GSWBootstrap

/-!
# A polynomial-modulus correctness family closed under NAND and refresh

Let `s = dimension + 1`, gadget base `b = 64 * s`, and use sixteen gadget levels.
The coefficient modulus is `b^16`, the lookup modulus is `b^3`, and floor division
uses factor `b^13`. The selected gadget code is `b^15`, which becomes `b^2` after
scaling. Control errors are bounded by `s^2`. This deliberately conservative
family proves that the deterministic correctness inequalities can hold at once
with a polynomial coefficient modulus and a polynomial-sized lookup. It is not
an optimized proposal or a security instantiation. In particular, security of the
complete masked quadratic self-key view has not been reduced to ordinary LWE.
-/

open Matrix

namespace FormalProof4FHE.LWE.GSWBootstrapParameters

open GSWGadget GSWModulusSwitch GSWBootstrap TFHE.BootstrappingCorrectness

/-- Keep the arithmetic expression opaque to typeclass reduction: expanding a large
known prefix inside `ZMod` can otherwise normalize enormous successor expressions. -/
@[irreducible] def base (dimension : ℕ) : ℕ := 64 * (dimension + 1)
def factor (dimension : ℕ) : ℕ := base dimension ^ 13
def lookupModulus (dimension : ℕ) : ℕ := base dimension ^ 3
def coefficientModulus (dimension : ℕ) : ℕ := factor dimension * lookupModulus dimension

theorem base_ge (dimension : ℕ) : 64 ≤ base dimension := by
  unfold base
  omega

theorem dimension_succ_le_base (dimension : ℕ) : dimension + 1 ≤ base dimension := by
  unfold base
  omega

instance (dimension : ℕ) : NeZero (base dimension) := ⟨by have := base_ge dimension; omega⟩
instance (dimension : ℕ) : NeZero (factor dimension) := ⟨pow_ne_zero _ (NeZero.ne (base dimension))⟩
instance (dimension : ℕ) : NeZero (lookupModulus dimension) := ⟨pow_ne_zero _ (NeZero.ne (base dimension))⟩
instance (dimension : ℕ) : NeZero (coefficientModulus dimension) := ⟨by
  exact Nat.mul_ne_zero (NeZero.ne (factor dimension)) (NeZero.ne (lookupModulus dimension))⟩

/-- Public coefficient modulus is polynomial of degree sixteen in the dimension. -/
theorem coefficientModulus_eq (dimension : ℕ) :
    coefficientModulus dimension = (64 * (dimension + 1)) ^ 16 := by
  simp only [coefficientModulus, factor, lookupModulus, base, ← pow_add]

/-- A fixed sixteen-level public gadget, with exact capacity. -/
def params (dimension : ℕ) : Parameters (factor dimension * lookupModulus dimension) where
  base := base dimension
  levels := 16
  one_lt_base := by have := base_ge dimension; omega
  modulus_le_capacity := by
    simp only [factor, lookupModulus, ← pow_add]
    rfl

def level (dimension : ℕ) : Fin (params dimension).levels := ⟨15, by change 15 < 16; decide⟩
def oneCode (dimension : ℕ) : ZMod (lookupModulus dimension) := (base dimension ^ 2 : ℕ)
def keyBound (dimension : ℕ) : ℕ := (dimension + 1) ^ 2
def outputBound (dimension : ℕ) : ℕ :=
  lookupModulus dimension * dimension * growth (params dimension) (dimension + 1) * keyBound dimension
def inputBound (dimension : ℕ) : ℕ :=
  (growth (params dimension) (dimension + 1) + 1) * outputBound dimension

/-- The selected large-modulus gadget entry embeds the actual small-modulus code exactly. -/
theorem gadget_eq_up (dimension : ℕ) :
    TFHE.Gadget.Base.gadget (params dimension) (level dimension) =
      up (factor dimension) (lookupModulus dimension) (oneCode dimension) := by
  change (base dimension : ZMod (factor dimension * lookupModulus dimension)) ^ 15 =
    up (factor dimension) (lookupModulus dimension) (base dimension ^ 2 : ℕ)
  rw [up_natCast]
  have hpower : factor dimension * base dimension ^ 2 = base dimension ^ 15 := by
    unfold factor
    rw [← pow_add]
  rw [hpower, Nat.cast_pow]

/-- The small code is below half the lookup modulus and has the claimed distance. -/
theorem oneCode_distance (dimension : ℕ) : centeredDistance 0 (oneCode dimension) =
    base dimension ^ 2 := by
  have hbase := base_ge dimension
  have hhalf : base dimension ^ 2 ≤ base dimension ^ 3 / 2 := by
    apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
    rw [pow_succ]
    exact Nat.mul_le_mul_left _ (by omega : 2 ≤ base dimension)
  rw [centeredDistance_symm]
  change (LatticeCrypto.centeredRepr
    (((base dimension ^ 2 : ℕ) : ZMod (lookupModulus dimension)) - 0)).natAbs = _
  rw [sub_zero, LatticeCrypto.centeredRepr_eq_valMinAbs,
    ZMod.valMinAbs_natCast_of_le_half (n := lookupModulus dimension) hhalf]
  simp

theorem growth_le (dimension : ℕ) :
    growth (params dimension) (dimension + 1) ≤ 16 * base dimension ^ 2 := by
  unfold growth params
  calc
    _ ≤ (base dimension * 16) * base dimension := by
      gcongr
      · exact dimension_succ_le_base dimension
      · exact Nat.sub_le _ _
    _ = _ := by ring

theorem outputBound_le (dimension : ℕ) : outputBound dimension ≤ 16 * base dimension ^ 8 := by
  have hd : dimension ≤ base dimension := (Nat.le_succ _).trans (dimension_succ_le_base dimension)
  have hs := dimension_succ_le_base dimension
  unfold outputBound lookupModulus keyBound
  calc
    _ ≤ base dimension ^ 3 * base dimension * (16 * base dimension ^ 2) * base dimension ^ 2 := by
      gcongr
      exact growth_le dimension
    _ = _ := by ring

/-- Even the post-NAND error is at most one scaling factor. -/
theorem inputBound_le_factor (dimension : ℕ) : inputBound dimension ≤ factor dimension := by
  have hb := base_ge dimension
  have hb2 : 1 ≤ base dimension ^ 2 := one_le_pow₀ (by omega : 1 ≤ base dimension)
  have hg : growth (params dimension) (dimension + 1) + 1 ≤ 17 * base dimension ^ 2 := by
    have := growth_le dimension
    omega
  have hpower : 272 ≤ base dimension ^ 2 := by nlinarith
  calc
    inputBound dimension ≤ (17 * base dimension ^ 2) * (16 * base dimension ^ 8) :=
      Nat.mul_le_mul hg (outputBound_le dimension)
    _ = 272 * base dimension ^ 10 := by ring
    _ ≤ base dimension ^ 2 * base dimension ^ 10 := Nat.mul_le_mul_right _ hpower
    _ = base dimension ^ 12 := by rw [← pow_add]
    _ ≤ factor dimension := by
      unfold factor
      exact pow_le_pow_right' (by omega) (by decide : 12 ≤ 13)

theorem outputBound_le_inputBound (dimension : ℕ) : outputBound dimension ≤ inputBound dimension := by
  unfold inputBound
  exact Nat.le_mul_of_pos_left _ (by omega)

/-- The public scaled-rounding margin holds for the complete post-NAND bound. -/
theorem rounding_margin (dimension : ℕ) :
    2 * (inputBound dimension + (dimension + 1) * (factor dimension - 1)) <
      factor dimension * centeredDistance 0 (oneCode dimension) := by
  have hb := base_ge dimension
  have hs := dimension_succ_le_base dimension
  have hgap : 2 * ((dimension + 1) + 1) < base dimension ^ 2 := by nlinarith
  rw [oneCode_distance]
  calc
    _ ≤ 2 * (factor dimension + (dimension + 1) * factor dimension) := by
      gcongr
      · exact inputBound_le_factor dimension
      · exact Nat.sub_le _ _
    _ = factor dimension * (2 * ((dimension + 1) + 1)) := by ring
    _ < _ := Nat.mul_lt_mul_of_pos_left hgap (NeZero.pos (factor dimension))

/-- Large-modulus output decoding has a strict margin as well. -/
theorem output_margin (dimension : ℕ) :
    2 * outputBound dimension <
      centeredDistance 0 (TFHE.Gadget.Base.gadget (params dimension) (level dimension)) := by
  have hb := base_ge dimension
  have htwo : 2 < base dimension ^ 2 := by nlinarith
  rw [gadget_eq_up]
  have hscale : centeredDistance 0 (up (factor dimension) (lookupModulus dimension) (oneCode dimension)) =
      factor dimension * centeredDistance 0 (oneCode dimension) := by
    rw [centeredDistance_symm, centeredDistance_symm 0 (oneCode dimension)]
    simp only [centeredDistance, sub_zero]
    exact centered_up _ _ _
  rw [hscale, oneCode_distance]
  calc
    _ ≤ 2 * factor dimension := Nat.mul_le_mul_left _
      ((outputBound_le_inputBound dimension).trans (inputBound_le_factor dimension))
    _ < _ := by
      have h := Nat.mul_lt_mul_of_pos_left htwo (NeZero.pos (factor dimension))
      simpa only [Nat.mul_comm] using h

/-- NAND followed by public refresh preserves the invariant for arbitrary further gates.
The same controls and one unchanged binary secret are used at every invocation. -/
theorem noiseBound_refreshedNand {dimension : ℕ} (bits : Fin dimension → Bool)
    (controls : Fin dimension → Ciphertext (params dimension) (dimension + 1))
    (first second : Ciphertext (params dimension) (dimension + 1)) (firstBit secondBit : Bool)
    (hcontrols : ∀ index, NoiseBound (params dimension)
      (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits)) (controls index)
      (bitMessage (bits index)) (keyBound dimension))
    (hfirst : NoiseBound (params dimension) (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits))
      first (bitMessage firstBit) (outputBound dimension))
    (hsecond : NoiseBound (params dimension) (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits))
      second (bitMessage secondBit) (outputBound dimension)) :
    NoiseBound (params dimension) (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits))
      (bootstrap (params dimension) controls (nand (params dimension) first second)
        (level dimension) (oneCode dimension))
      (bitMessage (!(firstBit && secondBit))) (outputBound dimension) := by
  apply noiseBound_bootstrap (params dimension) bits controls _ (level dimension) (oneCode dimension)
    _ (inputBound dimension) (keyBound dimension) (gadget_eq_up dimension) _ hcontrols
    (rounding_margin dimension)
  have hgate := noiseBound_nand (params dimension)
    (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits)) first second firstBit secondBit
    (outputBound dimension) (outputBound dimension) hfirst hsecond
  have hbound : growth (params dimension) (dimension + 1) * outputBound dimension + outputBound dimension =
      inputBound dimension := by unfold inputBound; ring
  rwa [hbound] at hgate

/-- Correct output decryption for a refreshed NAND in this concrete family, with no
unproved parameter-feasibility premise. -/
theorem decrypt_refreshedNand {dimension : ℕ} (bits : Fin dimension → Bool)
    (controls : Fin dimension → Ciphertext (params dimension) (dimension + 1))
    (first second : Ciphertext (params dimension) (dimension + 1)) (firstBit secondBit : Bool)
    (hcontrols : ∀ index, NoiseBound (params dimension)
      (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits)) (controls index)
      (bitMessage (bits index)) (keyBound dimension))
    (hfirst : NoiseBound (params dimension) (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits))
      first (bitMessage firstBit) (outputBound dimension))
    (hsecond : NoiseBound (params dimension) (GSWOperations.extendedSecret (GSWSelfKey.binaryEmbed bits))
      second (bitMessage secondBit) (outputBound dimension)) :
    decrypt (params dimension) (GSWSelfKey.binaryEmbed bits)
      (bootstrap (params dimension) controls (nand (params dimension) first second)
        (level dimension) (oneCode dimension)) (level dimension) = !(firstBit && secondBit) :=
  decrypt_eq_bit (params dimension) (GSWSelfKey.binaryEmbed bits) _ _ _ (level dimension)
    (noiseBound_refreshedNand bits controls first second firstBit secondBit hcontrols hfirst hsecond)
    (output_margin dimension)

end FormalProof4FHE.LWE.GSWBootstrapParameters
