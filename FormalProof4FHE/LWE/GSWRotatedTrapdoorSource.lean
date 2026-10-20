/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/
import FormalProof4FHE.LWE.GSWPrivateTrapdoor
import FormalProof4FHE.LWE.GSWTwoSidedCompiler
import Mathlib.Data.Nat.Factorization.Basic

/-!
# An ordinary-source embedding for a rotated private gadget

Programming the gadget as H*G makes its source body available from an ordinary
LWE block at H. The derived source has correlated, gadget-amplified errors.
Its private short preimages have exactly the same correction as the public
effective coefficient Q*H⁻ᵀ. Thus short private witnesses alone do not bound
the actual control error. This is a source/phase calculation, not a secure
correct bootstrapping construction or a new hardness assumption.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.LWE.GSWRotatedTrapdoorSource

def trapdoor {R : Type} [CommRing R] {p w : ℕ} (r : Matrix (Fin p) (Fin w) R) :
    Matrix (Fin (p + w)) (Fin w) R :=
  fun row column ↦ Fin.addCases (fun i ↦ r i column)
    (fun i ↦ if i = column then 1 else 0) row

/-- The simulator uses only two ordinary source transcripts and private coins. -/
def source {R : Type} [CommRing R] {n p w : ℕ}
    (base : BatchTranscript R n p) (rotation : BatchTranscript R n n)
    (g : Matrix (Fin n) (Fin w) R) (r : Matrix (Fin p) (Fin w) R) :
    BatchTranscript R n (p + w) :=
  GSWTwoSidedCompiler.join base
    (rotation.1 * g - base.1 * r, vecMul rotation.2 g - vecMul base.2 r)

theorem source_trapdoor {R : Type} [CommRing R] {n p w : ℕ}
    (base : BatchTranscript R n p) (rotation : BatchTranscript R n n)
    (g : Matrix (Fin n) (Fin w) R) (r : Matrix (Fin p) (Fin w) R) :
    (source base rotation g r).1 * trapdoor r = rotation.1 * g := by
  ext row column
  simp [source, GSWTwoSidedCompiler.join, trapdoor, Matrix.mul_apply,
    Fin.sum_univ_add, mul_ite]

theorem source_body_projection {R : Type} [CommRing R] {n p w : ℕ}
    (base : BatchTranscript R n p) (rotation : BatchTranscript R n n)
    (g : Matrix (Fin n) (Fin w) R) (r : Matrix (Fin p) (Fin w) R) :
    vecMul (source base rotation g r).2 (trapdoor r) = vecMul rotation.2 g := by
  funext column
  simp [source, GSWTwoSidedCompiler.join, trapdoor, vecMul, dotProduct,
    Fin.sum_univ_add, mul_ite]

theorem derived_error {R : Type} [CommRing R] {n p w : ℕ}
    (a : Matrix (Fin n) (Fin p) R) (h : Matrix (Fin n) (Fin n) R)
    (g : Matrix (Fin n) (Fin w) R) (r : Matrix (Fin p) (Fin w) R)
    (secret : Fin n → R) (baseError : Fin p → R) (rotationError : Fin n → R) :
    vecMul (vecMul secret h + rotationError) g -
      vecMul (vecMul secret a + baseError) r - vecMul secret (h * g - a * r) =
      vecMul rotationError g - vecMul baseError r := by
  rw [add_vecMul, add_vecMul, vecMul_sub, ← vecMul_vecMul, ← vecMul_vecMul]
  abel

theorem rotated_certificate {R : Type} [CommRing R] {n p w : ℕ}
    (base : BatchTranscript R n p) (rotation : BatchTranscript R n n)
    (g : Matrix (Fin n) (Fin w) R) (r : Matrix (Fin p) (Fin w) R)
    (d : Matrix (Fin n) (Fin w) R) (target inverse : Matrix (Fin n) (Fin n) R)
    (hinverse : rotation.1 * inverse = 1)
    (hdecomposition : d * g.transpose = target * inverse.transpose) :
    (d * (trapdoor r).transpose) * (source base rotation g r).1.transpose = target := by
  rw [Matrix.mul_assoc, ← transpose_mul, source_trapdoor, transpose_mul,
    ← Matrix.mul_assoc, hdecomposition, Matrix.mul_assoc, ← transpose_mul, hinverse]
  simp

/-- Neither the private trapdoor nor its randomness survives in the correction. -/
theorem effective_projection {R : Type} [CommRing R] {n p w : ℕ}
    (base : BatchTranscript R n p) (rotation : BatchTranscript R n n)
    (g : Matrix (Fin n) (Fin w) R) (r : Matrix (Fin p) (Fin w) R)
    (d : Matrix (Fin n) (Fin w) R) (target inverse : Matrix (Fin n) (Fin n) R)
    (hdecomposition : d * g.transpose = target * inverse.transpose) :
    (d * (trapdoor r).transpose).mulVec (source base rotation g r).2 =
      (target * inverse.transpose).mulVec rotation.2 := by
  rw [← mulVec_mulVec, mulVec_transpose, source_body_projection,
    ← mulVec_transpose g rotation.2, mulVec_mulVec, hdecomposition]

theorem actual_control_correction {R : Type} [CommRing R] {n : ℕ}
    (h inverse target : Matrix (Fin n) (Fin n) R)
    (hinverse : h * inverse = 1) (secret error : Fin n → R) :
    dotProduct secret ((target * inverse.transpose).mulVec (vecMul secret h + error)) =
      dotProduct secret (target.mulVec secret) +
        dotProduct secret ((target * inverse.transpose).mulVec error) := by
  rw [mulVec_add, dotProduct_add]
  congr 1
  rw [← mulVec_transpose h secret, mulVec_mulVec, Matrix.mul_assoc,
    ← transpose_mul, hinverse]
  simp

/-- At a power-of-two modulus every nonzero inverse error has a binary gadget
level whose scaled error is exactly half the modulus. -/
theorem exists_half_turn {levels : ℕ} (error : ZMod (2 ^ levels)) (hne : error ≠ 0) :
    ∃ level : Fin levels,
      ((2 ^ level.val : ℕ) : ZMod (2 ^ levels)) * error =
        ((2 ^ (levels - 1) : ℕ) : ZMod (2 ^ levels)) := by
  haveI : NeZero (2 ^ levels) := ⟨ne_of_gt (pow_pos (by decide) _)⟩
  obtain ⟨k, m, ⟨j, hm⟩, hval⟩ := Nat.exists_eq_two_pow_mul_odd ((ZMod.val_ne_zero error).2 hne)
  have hmpos : 0 < m := by omega
  have hpow : 2 ^ k ≤ error.val := by
    rw [hval]
    exact Nat.le_mul_of_pos_right _ hmpos
  have hk : k < levels :=
    (Nat.pow_lt_pow_iff_right Nat.one_lt_two).1 (hpow.trans_lt (ZMod.val_lt error))
  have hlevel : levels - 1 - k < levels := by omega
  have hadd : levels - 1 - k + k = levels - 1 := by omega
  have hsucc : levels - 1 + 1 = levels := by omega
  have hproduct : 2 ^ (levels - 1 - k) * error.val = 2 ^ levels * j + 2 ^ (levels - 1) := by
    rw [hval, hm, ← Nat.mul_assoc, ← pow_add, hadd, Nat.mul_add,
      Nat.mul_one, ← Nat.mul_assoc, ← pow_succ, hsucc]
  refine ⟨⟨levels - 1 - k, hlevel⟩, ?_⟩
  calc
    _ = ((2 ^ (levels - 1 - k) * error.val : ℕ) : ZMod (2 ^ levels)) := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    _ = ((2 ^ levels * j + 2 ^ (levels - 1) : ℕ) : ZMod (2 ^ levels)) := by rw [hproduct]
    _ = _ := by simp

theorem exists_maximal_centered_error {levels : ℕ} (error : ZMod (2 ^ levels)) (hne : error ≠ 0) :
    ∃ level : Fin levels,
      (LatticeCrypto.centeredRepr (((2 ^ level.val : ℕ) : ZMod (2 ^ levels)) * error)).natAbs =
        2 ^ levels / 2 := by
  obtain ⟨level, hlevel⟩ := exists_half_turn error hne
  have hpositive : 0 < levels := (Nat.zero_le level.val).trans_lt level.isLt
  have hhalf : 2 ^ levels / 2 = 2 ^ (levels - 1) := by
    rw [show levels = (levels - 1) + 1 by omega, pow_succ]
    simp
  refine ⟨level, ?_⟩
  rw [hlevel, ← hhalf, LatticeCrypto.centeredRepr_eq_valMinAbs,
    ZMod.valMinAbs_natCast_of_le_half (le_refl _), Int.natAbs_natCast]

/-- Fresh small noise cannot remove the half-modulus obstruction. -/
theorem perturbation_lower_bound {q : ℕ} [NeZero q] (error fresh : ZMod q) (E : ℕ)
    (hfresh : (LatticeCrypto.centeredRepr fresh).natAbs ≤ E) :
    (LatticeCrypto.centeredRepr error).natAbs - E ≤
      (LatticeCrypto.centeredRepr (error + fresh)).natAbs := by
  have htriangle := TFHE.NoiseBounds.centeredRepr_add_natAbs_le (error + fresh) (-fresh)
  have hcancel : error + fresh + -fresh = error := by ring
  rw [hcancel, LatticeCrypto.centeredRepr_natAbs_neg] at htriangle
  omega

theorem exists_noisy_gadget_obstruction {levels : ℕ} (error : ZMod (2 ^ levels))
    (hne : error ≠ 0) (fresh : Fin levels → ZMod (2 ^ levels)) (E : ℕ)
    (hfresh : ∀ level, (LatticeCrypto.centeredRepr (fresh level)).natAbs ≤ E) :
    ∃ level : Fin levels, 2 ^ levels / 2 - E ≤
      (LatticeCrypto.centeredRepr
        (((2 ^ level.val : ℕ) : ZMod (2 ^ levels)) * error + fresh level)).natAbs := by
  haveI : NeZero (2 ^ levels) := ⟨ne_of_gt (pow_pos (by decide) _)⟩
  obtain ⟨level, hlevel⟩ := exists_maximal_centered_error error hne
  refine ⟨level, ?_⟩
  have hbound := perturbation_lower_bound
    (((2 ^ level.val : ℕ) : ZMod (2 ^ levels)) * error) (fresh level) E (hfresh level)
  rwa [hlevel] at hbound

end FormalProof4FHE.LWE.GSWRotatedTrapdoorSource
