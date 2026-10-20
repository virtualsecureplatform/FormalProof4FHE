/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/
import FormalProof4FHE.LWE.GSWQuadraticPreimageRowSupport

/-!
# Testing a same-secret source at publicly gadget-shifted matrices

Two honest zero batches at A and A-G have body difference sᵀG+e₁-e₂.
Selected gadget columns therefore publicly decode every binary key coordinate
when the two errors fit the stated margin. This rules out that particular
joint-source specialization, not shifted preimage sampling itself, a source
with different correlated phases, or the WWW25 construction/applications.
-/

open Matrix

namespace FormalProof4FHE.LWE.GSWShiftedSourceDisclosure

theorem body_difference {R : Type} [CommRing R] {n m : ℕ}
    (secret : Fin n → R) (base shift : Matrix (Fin n) (Fin m) R)
    (firstError secondError : Fin m → R) :
    (vecMul secret base + firstError) -
      (vecMul secret (base - shift) + secondError) =
      vecMul secret shift + (firstError - secondError) := by
  rw [vecMul_sub]
  abel

theorem coordinate_difference {R : Type} [CommRing R] {n m : ℕ}
    (secret : Fin n → R) (base shift : Matrix (Fin n) (Fin m) R)
    (firstError secondError : Fin m → R) (weight : R) (index : Fin n) (column : Fin m)
    (hshift : ∀ row, shift row column = if row = index then weight else 0) :
    ((vecMul secret base + firstError) -
      (vecMul secret (base - shift) + secondError)) column =
      weight * secret index + (firstError column - secondError column) := by
  rw [body_difference]
  simp only [Pi.add_apply, Pi.sub_apply, vecMul, dotProduct]
  simp_rw [hshift, mul_ite, mul_zero]
  simp [mul_comm]

def recover {q n m : ℕ} [NeZero q] (weight : ZMod q)
    (positions : Fin n → Fin m) (firstBody secondBody : Fin m → ZMod q) : Fin n → Bool :=
  fun index ↦ TFHE.BootstrappingCorrectness.decodeNearest 0 weight
    (firstBody (positions index) - secondBody (positions index))

theorem recover_real {q n m : ℕ} [NeZero q] (weight : ZMod q)
    (positions : Fin n → Fin m) (base shift : Matrix (Fin n) (Fin m) (ZMod q))
    (hshift : ∀ index row, shift row (positions index) = if row = index then weight else 0)
    (bits : Fin n → Bool) (firstError secondError : Fin m → ZMod q) (bound : ℕ)
    (hfirst : ∀ index, (LatticeCrypto.centeredRepr (firstError (positions index))).natAbs ≤ bound)
    (hsecond : ∀ index, (LatticeCrypto.centeredRepr (secondError (positions index))).natAbs ≤ bound)
    (hmargin : 4 * bound < TFHE.BootstrappingCorrectness.centeredDistance 0 weight) :
    recover weight positions
      (vecMul (GSWSelfKey.binaryEmbed bits) base + firstError)
      (vecMul (GSWSelfKey.binaryEmbed bits) (base - shift) + secondError) = bits := by
  funext index
  apply TFHE.BootstrappingCorrectness.decodeNearest_encodeBit_of_distance_le
    0 weight _ (2 * bound) (bits index) (by omega)
  change TFHE.BootstrappingCorrectness.centeredDistance
    (((vecMul (GSWSelfKey.binaryEmbed bits) base + firstError) -
      (vecMul (GSWSelfKey.binaryEmbed bits) (base - shift) + secondError)) (positions index))
    (TFHE.BootstrappingCorrectness.encodeBit 0 weight (bits index)) ≤ _
  rw [coordinate_difference _ base shift firstError secondError weight index (positions index)
    (hshift index)]
  have hbit : weight * GSWSelfKey.binaryEmbed (R := ZMod q) bits index =
      TFHE.BootstrappingCorrectness.encodeBit 0 weight (bits index) := by
    cases hb : bits index <;> simp [GSWSelfKey.binaryEmbed,
      TFHE.BootstrappingCorrectness.encodeBit, hb]
  rw [hbit]
  have hh := TFHE.NoiseBounds.centeredRepr_sub_natAbs_le
    (firstError (positions index)) (secondError (positions index))
  have hf := hfirst index
  have hs := hsecond index
  unfold TFHE.BootstrappingCorrectness.centeredDistance
  simp only [add_sub_cancel_left]
  omega

end FormalProof4FHE.LWE.GSWShiftedSourceDisclosure
