/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.BootstrappingCorrectness

/-!
# Recovering a residue from publicly readable noisy binary gadget multiples

For q=2^levels, a noisy observation of each a*2^j permits recovery of the
entire residue a if twice the noise radius is less than the half-modulus
codeword separation. The decoder reads the gadget levels from largest to
smallest and subtracts the already recovered low bits. It receives only
those observations, not the unknown residue or its error vector.

This is an audit tool for linking hints whose phase becomes readable to a
participant knowing its own decryption key. It is not an attack on a
same-key view whose decryption key is unknown to the adversary.
-/

namespace FormalProof4FHE.LWE.NoisyBinaryGadget

open TFHE.BootstrappingCorrectness

def bitNat (bit : Bool) : ℕ := if bit then 1 else 0

def recoverAux {q : ℕ} [NeZero q] (levels : ℕ) (samples : ℕ → ZMod q) : ℕ → ℕ
  | 0 => 0
  | steps + 1 =>
    let knownLow := recoverAux levels samples steps
    let level := levels - (steps + 1)
    let bit := decodeNearest 0 ((2 ^ (levels - 1) : ℕ) : ZMod q)
      (samples level - (knownLow : ZMod q) * ((2 ^ level : ℕ) : ZMod q))
    knownLow + 2 ^ steps * bitNat bit

def recover {q : ℕ} [NeZero q] (levels : ℕ) (samples : ℕ → ZMod q) : ZMod q :=
  (recoverAux levels samples levels : ℕ)

theorem bitNat_remainder (a : ℕ) :
    bitNat (decide (a % 2 = 1)) = a % 2 := by
  have h := Nat.mod_lt a (by decide : 0 < 2)
  by_cases ha : a % 2 = 1
  · simp [bitNat, ha]
  · have hz : a % 2 = 0 := by omega
    simp [bitNat, hz]

theorem mod_pow_succ (a steps : ℕ) :
    a % 2 ^ (steps + 1) = a % 2 ^ steps + 2 ^ steps * ((a / 2 ^ steps) % 2) := by
  have hp : 0 < 2 ^ steps := pow_pos (by decide) _
  have hr := Nat.mod_lt a hp
  have hb := Nat.mod_lt (a / 2 ^ steps) (by decide : 0 < 2)
  have hfirst := Nat.mod_add_div a (2 ^ steps)
  have hsecond := Nat.mod_add_div (a / 2 ^ steps) 2
  have hdecomp : a = a % 2 ^ steps + 2 ^ steps * ((a / 2 ^ steps) % 2) +
      2 ^ (steps + 1) * ((a / 2 ^ steps) / 2) := by
    rw [pow_succ]
    nlinarith
  have hsmall : a % 2 ^ steps + 2 ^ steps * ((a / 2 ^ steps) % 2) < 2 ^ (steps + 1) := by
    rw [pow_succ]
    nlinarith
  conv_lhs => rw [hdecomp, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hsmall]

theorem half_modulus {q levels : ℕ} [NeZero q] (hlevels : 0 < levels)
    (hq : q = 2 ^ levels) :
    2 * ((2 ^ (levels - 1) : ℕ) : ZMod q) = 0 := by
  have hpow : 2 * 2 ^ (levels - 1) = q := by
    rw [hq, ← pow_succ']
    congr 1
    omega
  rw [← Nat.cast_two, ← Nat.cast_mul, hpow, ZMod.natCast_self]

theorem half_code_distance {q levels : ℕ} [NeZero q] (hlevels : 0 < levels)
    (hq : q = 2 ^ levels) :
    centeredDistance 0 ((2 ^ (levels - 1) : ℕ) : ZMod q) = 2 ^ (levels - 1) := by
  have hpow : 2 * 2 ^ (levels - 1) = q := by
    rw [hq, ← pow_succ']
    congr 1
    omega
  have hhalf : 2 ^ (levels - 1) ≤ q / 2 := by omega
  rw [centeredDistance_symm]
  change (LatticeCrypto.centeredRepr
    (((2 ^ (levels - 1) : ℕ) : ZMod q) - 0)).natAbs = _
  rw [sub_zero, LatticeCrypto.centeredRepr_eq_valMinAbs,
    ZMod.valMinAbs_natCast_of_le_half hhalf]
  simp

theorem residual_eq_bit {q levels : ℕ} [NeZero q] (hq : q = 2 ^ levels)
    (a steps : ℕ) (hsteps : steps < levels) :
    (a : ZMod q) * ((2 ^ (levels - (steps + 1)) : ℕ) : ZMod q) -
      ((a % 2 ^ steps : ℕ) : ZMod q) * ((2 ^ (levels - (steps + 1)) : ℕ) : ZMod q) =
      encodeBit 0 ((2 ^ (levels - 1) : ℕ) : ZMod q)
        (decide ((a / 2 ^ steps) % 2 = 1)) := by
  have hprod : ((2 ^ steps : ℕ) : ZMod q) *
      ((2 ^ (levels - (steps + 1)) : ℕ) : ZMod q) =
        ((2 ^ (levels - 1) : ℕ) : ZMod q) := by
    rw [← Nat.cast_mul, ← pow_add]
    congr 2
    omega
  have hfirst : (a : ZMod q) = ((a % 2 ^ steps : ℕ) : ZMod q) +
      ((2 ^ steps : ℕ) : ZMod q) * ((a / 2 ^ steps : ℕ) : ZMod q) := by
    simpa only [Nat.cast_add, Nat.cast_mul] using
      congrArg (fun value : ℕ ↦ (value : ZMod q)) (Nat.mod_add_div a (2 ^ steps)).symm
  have hsecond : ((a / 2 ^ steps : ℕ) : ZMod q) =
      (((a / 2 ^ steps) % 2 : ℕ) : ZMod q) +
        2 * (((a / 2 ^ steps) / 2 : ℕ) : ZMod q) := by
    simpa only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
      congrArg (fun value : ℕ ↦ (value : ZMod q)) (Nat.mod_add_div (a / 2 ^ steps) 2).symm
  calc
    _ = ((a / 2 ^ steps : ℕ) : ZMod q) *
        ((2 ^ (levels - 1) : ℕ) : ZMod q) := by
      rw [hfirst]
      linear_combination ((a / 2 ^ steps : ℕ) : ZMod q) * hprod
    _ = (((a / 2 ^ steps) % 2 : ℕ) : ZMod q) *
        ((2 ^ (levels - 1) : ℕ) : ZMod q) := by
      rw [hsecond]
      have hhalf := half_modulus (q := q) (by omega : 0 < levels) hq
      linear_combination (((a / 2 ^ steps) / 2 : ℕ) : ZMod q) * hhalf
    _ = _ := by
      have hbit := bitNat_remainder (a / 2 ^ steps)
      rw [← hbit]
      cases h : decide ((a / 2 ^ steps) % 2 = 1) <;> simp [bitNat, encodeBit]

theorem recoverAux_eq_mod {q levels : ℕ} [NeZero q] (hq : q = 2 ^ levels)
    (samples : ℕ → ZMod q) (a bound : ℕ)
    (hnoise : ∀ level < levels,
      centeredDistance (samples level) ((a : ZMod q) * ((2 ^ level : ℕ) : ZMod q)) ≤ bound)
    (hmargin : 2 * bound < centeredDistance 0 ((2 ^ (levels - 1) : ℕ) : ZMod q))
    (steps : ℕ) (hsteps : steps ≤ levels) :
    recoverAux levels samples steps = a % 2 ^ steps := by
  induction steps with
  | zero => simp [recoverAux, Nat.mod_one]
  | succ steps ih =>
    have hs : steps < levels := by omega
    have hp := ih (by omega)
    have hdecode : decodeNearest 0 ((2 ^ (levels - 1) : ℕ) : ZMod q)
        (samples (levels - (steps + 1)) -
          ((a % 2 ^ steps : ℕ) : ZMod q) * ((2 ^ (levels - (steps + 1)) : ℕ) : ZMod q)) =
        decide ((a / 2 ^ steps) % 2 = 1) := by
      apply decodeNearest_encodeBit_of_distance_le _ _ _ bound _ hmargin
      rw [← residual_eq_bit hq a steps hs]
      simpa only [centeredDistance, sub_sub_sub_cancel_right] using
        hnoise (levels - (steps + 1)) (by omega)
    simp only [recoverAux, hp, hdecode, bitNat_remainder, mod_pow_succ]

theorem recover_eq {q levels : ℕ} [NeZero q] (hq : q = 2 ^ levels)
    (samples : ℕ → ZMod q) (a : ZMod q) (bound : ℕ)
    (hnoise : ∀ level < levels,
      centeredDistance (samples level) (a * ((2 ^ level : ℕ) : ZMod q)) ≤ bound)
    (hmargin : 2 * bound < centeredDistance 0 ((2 ^ (levels - 1) : ℕ) : ZMod q)) :
    recover levels samples = a := by
  have h := recoverAux_eq_mod hq samples a.val bound
    (by simpa only [ZMod.natCast_zmod_val] using hnoise) hmargin levels le_rfl
  unfold recover
  rw [h, ← hq, ZMod.natCast_mod, ZMod.natCast_zmod_val]


/-- A concrete quarter-modulus error margin suffices, without a secret-size bound. -/
theorem recover_eq_of_quarter_bound {q levels : ℕ} [NeZero q] (hlevels : 0 < levels)
    (hq : q = 2 ^ levels) (samples : ℕ → ZMod q) (a : ZMod q) (bound : ℕ)
    (hnoise : ∀ level < levels,
      centeredDistance (samples level) (a * ((2 ^ level : ℕ) : ZMod q)) ≤ bound)
    (hmargin : 4 * bound < q) :
    recover levels samples = a := by
  apply recover_eq hq samples a bound hnoise
  rw [half_code_distance hlevels hq]
  have hpow : q = 2 * 2 ^ (levels - 1) := by
    rw [hq, ← pow_succ']
    congr 1
    omega
  omega

end FormalProof4FHE.LWE.NoisyBinaryGadget
