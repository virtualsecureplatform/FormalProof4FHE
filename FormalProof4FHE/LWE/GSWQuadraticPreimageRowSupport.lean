/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.GSWQuadraticPreimage
import FormalProof4FHE.LWE.GSWGadget
import Mathlib.Data.Int.Interval

/-!
# Public inversion exposed by row-supported quadratic certificates

A quadratic preimage supported on just one row exposes the corresponding
linear coefficient vector. This includes an off-diagonal target, which remains
necessary after binary diagonal products are replaced by affine shifts. The
same applies to the difference of a nonzero and zero preimage whose other
rows agree. Thus zero-preserving prefix builders, and
builders with target-independent shared homogeneous prefixes, cannot use this
form of shortness as a secure shortcut: the public witness projects the LWE
body onto a secret coordinate with only its short projected error.

These are exact algebraic and decoding statements. They do not rule out a
dense quadratic builder with target-dependent alternating freedom, nor do they
assert an attack on every GSW construction or prove a statistical failure rate.
-/

open Matrix OracleComp
open scoped BigOperators ENNReal

namespace FormalProof4FHE.LWE.GSWQuadraticPreimageRowSupport

def diagonalTarget {R : Type} [Zero R] {n : ℕ} (weight : R) (index : Fin n) :
    Matrix (Fin n) (Fin n) R :=
  fun row column ↦ if row = index then if column = index then weight else 0 else 0

def coordinateTarget {R : Type} [Zero R] {n : ℕ} (weight : R) (first second : Fin n) :
    Matrix (Fin n) (Fin n) R :=
  fun row column ↦ if row = first then if column = second then weight else 0 else 0

/-- The actual row forced by an arbitrary supported certificate. Diagonal
coefficients are not doubled, so this remains valid at even moduli. -/
theorem linear_row_of_supported_certificate {R : Type} [CommRing R] {n m : ℕ}
    (a b : Matrix (Fin n) (Fin m) R) (target : Matrix (Fin n) (Fin n) R) (index : Fin n)
    (u : Matrix (Fin n) (Fin n) R)
    (hcertificate : b * a.transpose = target + u - u.transpose)
    (hsupport : ∀ row, row ≠ index → ∀ column, b row column = 0) :
    a.mulVec (b index) = fun row ↦
      if row = index then target index index else target index row + target row index := by
  funext row
  change dotProduct (a row) (b index) = _
  rw [dotProduct_comm]
  change (b * a.transpose) index row = _
  have hi := congrArg (fun matrix ↦ matrix index row) hcertificate
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.transpose_apply] at hi
  by_cases hr : row = index
  · subst row
    simp only [ite_true]
    linear_combination hi
  · rw [if_neg hr]
    have hj := congrArg (fun matrix ↦ matrix row index) hcertificate
    have hz : (b * a.transpose) row index = 0 := by
      simp [Matrix.mul_apply, hsupport row hr]
    rw [hz] at hj
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.transpose_apply] at hj
    linear_combination hi + hj

theorem linear_preimage_of_supported_offDiagonal {R : Type} [CommRing R] {n m : ℕ}
    (a b : Matrix (Fin n) (Fin m) R) (weight : R) (index other : Fin n) (hne : index ≠ other)
    (u : Matrix (Fin n) (Fin n) R)
    (hcertificate : b * a.transpose = coordinateTarget weight other index + u - u.transpose)
    (hsupport : ∀ row, row ≠ index → ∀ column, b row column = 0) :
    a.mulVec (b index) = fun row ↦ if row = other then weight else 0 := by
  rw [linear_row_of_supported_certificate a b (coordinateTarget weight other index) index u hcertificate hsupport]
  funext row
  by_cases hr : row = index
  · subst row
    simp [coordinateTarget, hne]
  · simp [coordinateTarget, hne, hr]

theorem linear_preimage_of_shared_prefix_offDiagonal {R : Type} [CommRing R] {n m : ℕ}
    (a nonzero zero : Matrix (Fin n) (Fin m) R) (weight : R) (index other : Fin n) (hne : index ≠ other)
    (uNonzero uZero : Matrix (Fin n) (Fin n) R)
    (hNonzero : nonzero * a.transpose = coordinateTarget weight other index + uNonzero - uNonzero.transpose)
    (hZero : zero * a.transpose = uZero - uZero.transpose)
    (hshared : ∀ row, row ≠ index → nonzero row = zero row) :
    a.mulVec (nonzero index - zero index) = fun row ↦ if row = other then weight else 0 := by
  have hc : (nonzero - zero) * a.transpose =
      coordinateTarget weight other index + (uNonzero - uZero) - (uNonzero - uZero).transpose := by
    rw [Matrix.sub_mul, hNonzero, hZero, transpose_sub]
    abel
  exact linear_preimage_of_supported_offDiagonal a (nonzero - zero) weight index other hne
    (uNonzero - uZero) hc (by
      intro row hrow column
      simp [Matrix.sub_apply, congrFun (hshared row hrow) column])

theorem product_eq_diagonal_of_supported_certificate {R : Type} [CommRing R] {n m : ℕ}
    (a b : Matrix (Fin n) (Fin m) R) (weight : R) (index : Fin n)
    (u : Matrix (Fin n) (Fin n) R)
    (hcertificate : b * a.transpose = diagonalTarget weight index + u - u.transpose)
    (hsupport : ∀ row, row ≠ index → ∀ column, b row column = 0) :
    b * a.transpose = diagonalTarget weight index := by
  have hzero (row : Fin n) (hrow : row ≠ index) (column : Fin n) :
      (b * a.transpose) row column = 0 := by
    simp [Matrix.mul_apply, hsupport row hrow]
  ext row column
  by_cases hrow : row = index
  · subst row
    by_cases hcolumn : column = index
    · subst column
      have hc := congrArg (fun matrix ↦ matrix index index) hcertificate
      simpa [diagonalTarget] using hc
    · have hc := congrArg (fun matrix ↦ matrix column index) hcertificate
      rw [hzero column hcolumn index] at hc
      have hu : u column index = u index column := by
        apply sub_eq_zero.mp
        simpa [diagonalTarget, hcolumn] using hc.symm
      have hi := congrArg (fun matrix ↦ matrix index column) hcertificate
      simpa [diagonalTarget, hcolumn, hu] using hi
  · rw [hzero row hrow]
    simp [diagonalTarget, hrow]

theorem linear_preimage_of_supported_certificate {R : Type} [CommRing R] {n m : ℕ}
    (a b : Matrix (Fin n) (Fin m) R) (weight : R) (index : Fin n)
    (u : Matrix (Fin n) (Fin n) R)
    (hcertificate : b * a.transpose = diagonalTarget weight index + u - u.transpose)
    (hsupport : ∀ row, row ≠ index → ∀ column, b row column = 0) :
    a.mulVec (b index) = fun row ↦ if row = index then weight else 0 := by
  have hc := product_eq_diagonal_of_supported_certificate a b weight index u hcertificate hsupport
  funext row
  change dotProduct (a row) (b index) = _
  rw [dotProduct_comm]
  change (b * a.transpose) index row = _
  rw [hc]
  simp [diagonalTarget]

theorem linear_preimage_of_shared_prefix {R : Type} [CommRing R] {n m : ℕ}
    (a nonzero zero : Matrix (Fin n) (Fin m) R) (weight : R) (index : Fin n)
    (uNonzero uZero : Matrix (Fin n) (Fin n) R)
    (hNonzero : nonzero * a.transpose = diagonalTarget weight index + uNonzero - uNonzero.transpose)
    (hZero : zero * a.transpose = uZero - uZero.transpose)
    (hshared : ∀ row, row ≠ index → nonzero row = zero row) :
    a.mulVec (nonzero index - zero index) = fun row ↦ if row = index then weight else 0 := by
  have hc : (nonzero - zero) * a.transpose =
      diagonalTarget weight index + (uNonzero - uZero) - (uNonzero - uZero).transpose := by
    rw [Matrix.sub_mul, hNonzero, hZero, transpose_sub]
    abel
  exact linear_preimage_of_supported_certificate a (nonzero - zero) weight index
    (uNonzero - uZero) hc (by
      intro row hrow column
      simp [Matrix.sub_apply, congrFun (hshared row hrow) column])

theorem projection_real {R : Type} [CommRing R] {n m : ℕ}
    (a : Matrix (Fin n) (Fin m) R) (pi : Fin m → R) (weight : R) (index : Fin n)
    (hpreimage : a.mulVec pi = fun row ↦ if row = index then weight else 0)
    (secret : Fin n → R) (error : Fin m → R) :
    dotProduct pi (vecMul secret a + error) = weight * secret index + dotProduct pi error := by
  rw [dotProduct_add, dotProduct_comm pi (vecMul secret a), ← dotProduct_mulVec, hpreimage]
  simp [dotProduct, mul_ite, mul_comm]

theorem projection_noise_bound {q m : ℕ} [NeZero q]
    (pi error : Fin m → ZMod q) (H E : ℕ)
    (hpi : ∑ column, (LatticeCrypto.centeredRepr (pi column)).natAbs ≤ H)
    (herror : ∀ column, (LatticeCrypto.centeredRepr (error column)).natAbs ≤ E) :
    (LatticeCrypto.centeredRepr (dotProduct pi error)).natAbs ≤ H * E := by
  unfold dotProduct
  calc
    _ ≤ ∑ column, (LatticeCrypto.centeredRepr (pi column * error column)).natAbs :=
      TFHE.NoiseBounds.centeredRepr_finset_sum_natAbs_le _ _
    _ ≤ ∑ column, (LatticeCrypto.centeredRepr (pi column)).natAbs * E := by
      apply Finset.sum_le_sum
      intro column _
      exact (TFHE.NoiseBounds.centeredRepr_mul_natAbs_le _ _).trans
        (Nat.mul_le_mul_left _ (herror column))
    _ = (∑ column, (LatticeCrypto.centeredRepr (pi column)).natAbs) * E := by
      rw [Finset.sum_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ hpi

theorem decode_projection {q n m : ℕ} [NeZero q]
    (a : Matrix (Fin n) (Fin m) (ZMod q)) (pi : Fin m → ZMod q)
    (weight : ZMod q) (index : Fin n)
    (hpreimage : a.mulVec pi = fun row ↦ if row = index then weight else 0)
    (bits : Fin n → Bool) (error : Fin m → ZMod q) (bound : ℕ)
    (herror : (LatticeCrypto.centeredRepr (dotProduct pi error)).natAbs ≤ bound)
    (hmargin : 2 * bound < TFHE.BootstrappingCorrectness.centeredDistance 0 weight) :
    TFHE.BootstrappingCorrectness.decodeNearest 0 weight
      (dotProduct pi (vecMul (GSWSelfKey.binaryEmbed bits) a + error)) = bits index := by
  apply TFHE.BootstrappingCorrectness.decodeNearest_encodeBit_of_distance_le
    0 weight _ bound (bits index) hmargin
  rw [projection_real a pi weight index hpreimage]
  have hm : weight * GSWSelfKey.binaryEmbed (R := ZMod q) bits index =
      TFHE.BootstrappingCorrectness.encodeBit 0 weight (bits index) := by
    cases h : bits index <;> simp [GSWSelfKey.binaryEmbed, TFHE.BootstrappingCorrectness.encodeBit, h]
  rw [hm]
  simpa [TFHE.BootstrappingCorrectness.centeredDistance] using herror

def recover {q n m : ℕ} [NeZero q] (weight : ZMod q)
    (preimages : Fin n → Fin m → ZMod q) (body : Fin m → ZMod q) : Fin n → Bool :=
  fun index ↦ TFHE.BootstrappingCorrectness.decodeNearest 0 weight (dotProduct (preimages index) body)

theorem recover_real {q n m : ℕ} [NeZero q]
    (a : Matrix (Fin n) (Fin m) (ZMod q)) (weight : ZMod q)
    (preimages : Fin n → Fin m → ZMod q)
    (hpreimage : ∀ index, a.mulVec (preimages index) = fun row ↦ if row = index then weight else 0)
    (bits : Fin n → Bool) (error : Fin m → ZMod q) (bound : ℕ)
    (herror : ∀ index, (LatticeCrypto.centeredRepr (dotProduct (preimages index) error)).natAbs ≤ bound)
    (hmargin : 2 * bound < TFHE.BootstrappingCorrectness.centeredDistance 0 weight) :
    recover weight preimages (vecMul (GSWSelfKey.binaryEmbed bits) a + error) = bits := by
  funext index
  exact decode_projection a (preimages index) weight index (hpreimage index) bits error bound
    (herror index) hmargin

/-- The recovered key decrypts an independent source verification sample. -/
theorem verification_phase_of_recovery {q n : ℕ} [NeZero q]
    (bits recovered : Fin n → Bool) (hrecovered : recovered = bits)
    (mask : Fin n → ZMod q) (error : ZMod q) :
    (dotProduct (GSWSelfKey.binaryEmbed bits) mask + error) -
      dotProduct (GSWSelfKey.binaryEmbed recovered) mask = error := by
  rw [hrecovered]
  ring

noncomputable section

/-- A uniform fresh verification body rarely falls in a narrow error window,
regardless of the recovered key or the already chosen verification mask. -/
theorem card_verification_window_le {q : ℕ} [NeZero q] (E : ℕ) (shift : ZMod q) :
    Fintype.card {body : ZMod q // (LatticeCrypto.centeredRepr (body - shift)).natAbs ≤ E} ≤
      2 * E + 1 := by
  let code : {body : ZMod q // (LatticeCrypto.centeredRepr (body - shift)).natAbs ≤ E} →
      {value : ℤ // value ∈ Finset.Icc (-(E : ℤ)) (E : ℤ)} :=
    fun body ↦ ⟨LatticeCrypto.centeredRepr (body.1 - shift), by
      rw [Finset.mem_Icc]
      have hh := body.2
      constructor <;> omega⟩
  have hinjective : Function.Injective code := by
    intro left right heq
    have hc := congrArg (fun value ↦ value.1) heq
    have hmod : left.1 - shift = right.1 - shift := by
      calc
        _ = ((LatticeCrypto.centeredRepr (left.1 - shift) : ℤ) : ZMod q) :=
          LatticeCrypto.centeredRepr_intCast _
        _ = ((LatticeCrypto.centeredRepr (right.1 - shift) : ℤ) : ZMod q) :=
          congrArg (fun value : ℤ ↦ (value : ZMod q)) hc
        _ = _ := (LatticeCrypto.centeredRepr_intCast _).symm
    exact Subtype.ext (sub_left_inj.mp hmod)
  calc
    _ ≤ Fintype.card {value : ℤ // value ∈ Finset.Icc (-(E : ℤ)) (E : ℤ)} :=
      Fintype.card_le_of_injective code hinjective
    _ = 2 * E + 1 := by
      rw [Fintype.card_coe]
      simp
      omega

theorem uniform_verification_acceptance_le {q : ℕ} [NeZero q] (E : ℕ) (shift : ZMod q) :
    Pr[fun body : ZMod q ↦ (LatticeCrypto.centeredRepr (body - shift)).natAbs ≤ E | $ᵗ ZMod q] ≤
      (2 * E + 1 : ℝ≥0∞) / q := by
  rw [probEvent_uniformSample, ZMod.card]
  have hc := card_verification_window_le E shift
  rw [Fintype.card_subtype] at hc
  apply ENNReal.div_le_div_right
  exact_mod_cast hc

end

end FormalProof4FHE.LWE.GSWQuadraticPreimageRowSupport
