/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/
import FormalProof4FHE.LWE.GSWBodyAdaptiveProjection
import FormalProof4FHE.LWE.GSWGadget

/-!
# Globally commuting idempotents do not bound mixed GSW errors

The explicit native binary-gadget controls below both encrypt one with noise
at most one. Their public factors reconstruct the controls, are globally
commuting idempotents, and stabilize their own controls. Their mixed product
is zero, so its decryption and the associated NAND are wrong. The factors
are noncanonical and not short; no secure sampling law is asserted. This
rules out these algebraic identities alone as a mixed-error invariant.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.LWE.GSWCommutingProjection

def rankOne {R : Type} [Mul R] {width : ℕ} (a b : Fin width → R) :
    Matrix (Fin width) (Fin width) R := fun i j ↦ a i * b j

theorem rankOne_mul {R : Type} [CommRing R] {width : ℕ}
    (a u b v : Fin width → R) :
    rankOne a u * rankOne b v =
      fun i j ↦ a i * dotProduct u b * v j := by
  ext i j
  simp only [Matrix.mul_apply, rankOne, dotProduct]
  calc
    ∑ k, (a i * u k) * (b k * v j) =
        ∑ k, (a i * (u k * b k)) * v j := by
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]

theorem vecMul_rankOne {R : Type} [CommRing R] {width : ℕ}
    (row a b : Fin width → R) :
    vecMul row (rankOne a b) = dotProduct row a • b := by
  funext j
  simp only [vecMul, dotProduct, rankOne, Pi.smul_apply, smul_eq_mul]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]

abbrev tinyParams : GSWGadget.Parameters 16 where
  base := 2
  levels := 4
  one_lt_base := by decide
  modulus_le_capacity := by decide

def tinySecret : Fin 2 → ZMod 16 := fun _ ↦ 1
def tinyLevel : Fin tinyParams.levels := ⟨3, by decide⟩

def tinyGadget : GSWGadget.Ciphertext tinyParams 3 := GSWGadget.gadget tinyParams 3

def tinyPhase : Fin 12 → ZMod 16 :=
  vecMul (GSWOperations.extendedSecret tinySecret) tinyGadget

def tinyError (index : Fin 2) : Fin 12 → ZMod 16 :=
  fun j ↦ if j.val = index.val + 1 then 1 else 0

def tinyRow (index : Fin 2) : Fin 12 → ZMod 16 := tinyPhase + tinyError index

def tinyDual (index : Fin 2) : Fin 12 → ZMod 16 := fun j ↦
  if index = 0 then (if j = 0 then 5 else if j = 2 then -1 else 0)
  else (if j = 0 then 3 else if j = 1 then -1 else 0)

def tinyFactor (index : Fin 2) : Matrix (Fin 12) (Fin 12) (ZMod 16) :=
  rankOne (tinyDual index) (tinyRow index)

def tinyControl (index : Fin 2) : GSWGadget.Ciphertext tinyParams 3 :=
  tinyGadget * tinyFactor index

set_option maxRecDepth 4096 in
theorem tiny_pairing (i j : Fin 2) :
    dotProduct (tinyRow i) (tinyDual j) = if i = j then 1 else 0 := by
  revert i j
  decide

set_option maxRecDepth 4096 in
theorem tiny_phase_pairing (i : Fin 2) :
    dotProduct tinyPhase (tinyDual i) = 1 := by
  revert i
  decide

theorem factor_pair_product (i j : Fin 2) :
    tinyFactor i * tinyFactor j = if i = j then tinyFactor i else 0 := by
  rw [tinyFactor, tinyFactor, rankOne_mul, tiny_pairing]
  by_cases hij : i = j
  · subst j
    simp only [ite_true, mul_one]
    rfl
  · simp only [if_neg hij, mul_zero, zero_mul]
    rfl

theorem factors_globally_idempotent (i : Fin 2) :
    tinyFactor i * tinyFactor i = tinyFactor i := by
  simp [factor_pair_product]

theorem factors_globally_commute (i j : Fin 2) :
    tinyFactor i * tinyFactor j = tinyFactor j * tinyFactor i := by
  by_cases hij : i = j
  · subst j
    rfl
  · simp [factor_pair_product, hij, Ne.symm hij]

theorem controls_reconstruct_and_stabilize (i : Fin 2) :
    tinyGadget * tinyFactor i = tinyControl i ∧
      tinyControl i * tinyFactor i = tinyControl i := by
  constructor
  · rfl
  · rw [tinyControl, Matrix.mul_assoc, factors_globally_idempotent]

theorem control_phase (i : Fin 2) :
    vecMul (GSWOperations.extendedSecret tinySecret) (tinyControl i) = tinyRow i := by
  rw [tinyControl, ← vecMul_vecMul]
  change vecMul tinyPhase (rankOne (tinyDual i) (tinyRow i)) = _
  rw [vecMul_rankOne, tiny_phase_pairing, one_smul]

theorem control_noise (i : Fin 2) :
    GSWOperations.noise (GSWOperations.extendedSecret tinySecret)
      tinyGadget (tinyControl i) 1 = tinyError i := by
  rw [GSWOperations.noise, control_phase]
  change (tinyPhase + tinyError i) - 1 • tinyPhase = tinyError i
  simp

theorem controls_noise_at_most_one (i : Fin 2) :
    GSWGadget.NoiseBound tinyParams (GSWOperations.extendedSecret tinySecret)
      (tinyControl i) 1 1 := by
  intro column
  change (LatticeCrypto.centeredRepr
    (GSWOperations.noise (GSWOperations.extendedSecret tinySecret)
      tinyGadget (tinyControl i) 1 column)).natAbs ≤ 1
  rw [control_noise]
  simp only [tinyError]
  split_ifs <;> decide

set_option maxRecDepth 4096 in
theorem controls_decode_one (i : Fin 2) :
    GSWGadget.decrypt tinyParams tinySecret (tinyControl i) tinyLevel = true := by
  unfold GSWGadget.decrypt
  rw [control_phase]
  revert i
  decide

theorem mixed_product_zero : tinyControl 0 * tinyFactor 1 = 0 := by
  rw [tinyControl, Matrix.mul_assoc, factor_pair_product]
  simp

set_option maxRecDepth 4096 in
theorem mixed_product_decodes_wrong :
    GSWGadget.decrypt tinyParams tinySecret (tinyControl 0 * tinyFactor 1) tinyLevel =
      false := by
  rw [mixed_product_zero]
  decide

set_option maxRecDepth 4096 in
theorem nand_decodes_wrong :
    GSWGadget.decrypt tinyParams tinySecret
      (tinyGadget - tinyControl 0 * tinyFactor 1) tinyLevel = true := by
  rw [mixed_product_zero, sub_zero]
  decide

end FormalProof4FHE.LWE.GSWCommutingProjection
