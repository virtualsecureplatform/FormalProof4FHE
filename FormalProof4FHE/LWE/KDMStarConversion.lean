/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.KDMStarGSW
import FormalProof4FHE.LWE.RecursiveMultiplication

/-!
# Testing quadratic-KDM conversion into the bit-specific GSW format

For a fixed anchor, every star-format phase is affine in the unknown vector u.
Deleting the recursive quadratic matrix leaves its entire uᵀTu contribution
in the phase. A single honest, zero-error quadratic-KDM ciphertext, with the
same public value on four different keys, also excludes ANY ciphertext-only
public conversion preserving phase on every key/private-coin realization.
The bounded-error version fails when four times the allowed phase discrepancy
is smaller than the centered gadget weight.

These statements concern a universal phase interface, not a computational
security attack. They do not exclude conversion using auxiliary public views
that vary with the key, distribution-specific correctness with negligible
exceptions, or a redesigned decoder/sampler. No probability-of-occurrence
claim is made for the special honest coins used in the witness.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.LWE.KDMStarConversion

theorem phase_affine {R : Type} [CommRing R] {n k : ℕ}
    (bit : Bool) (secret : Fin n → R) (view : KDMStarGSW.View R n k) (column : Fin k) :
    KDMStarGSW.phase bit secret view column =
      view none column + KDMStarGSW.anchor bit * view (some (.inl ())) column +
        ∑ row : Fin n, secret row * (view (some (.inr (.inl row))) column +
          KDMStarGSW.anchor bit * view (some (.inr (.inr row))) column) := by
  simp only [KDMStarGSW.phase, vecMul, dotProduct, Fintype.sum_option,
    Fintype.sum_sum_type, Fintype.sum_unique, KDMStarGSW.feature, one_mul]
  simp_rw [mul_add, Finset.sum_add_distrib]
  have hstar : (∑ row : Fin n, KDMStarGSW.anchor bit * secret row *
      view (some (.inr (.inr row))) column) =
      ∑ row : Fin n, secret row * (KDMStarGSW.anchor bit *
        view (some (.inr (.inr row))) column) := by
    apply Finset.sum_congr rfl
    intro row _
    ring
  rw [hstar]
  ring

/-- The straightforward candidate preserves only the body and linear terms. -/
def dropQuadratic {R : Type} [CommRing R] {n : ℕ}
    (ciphertext : RecursiveQuadratic.Ciphertext R n) : KDMStarGSW.View R n 1
  | none, _ => ciphertext.2.2
  | some (.inl _), _ => 0
  | some (.inr (.inl row)), _ => ciphertext.2.1 row
  | some (.inr (.inr _)), _ => 0

theorem phase_dropQuadratic {R : Type} [CommRing R] {n : ℕ}
    (bit : Bool) (secret : Fin n → R) (ciphertext : RecursiveQuadratic.Ciphertext R n) :
    KDMStarGSW.phase bit secret (dropQuadratic ciphertext) 0 =
      RecursiveQuadratic.decrypt secret ciphertext +
        dotProduct (vecMul secret ciphertext.1) secret := by
  rw [phase_affine]
  simp only [dropQuadratic, mul_zero, add_zero, RecursiveQuadratic.decrypt, dotProduct]
  have hlinear : (∑ row : Fin n, secret row * ciphertext.2.1 row) =
      ∑ row : Fin n, ciphertext.2.1 row * secret row := by
    apply Finset.sum_congr rfl
    intro row _
    exact mul_comm _ _
  rw [hlinear]
  ring

def corner {R : Type} [Zero R] [One R] (first second : Bool) : Fin 2 → R :=
  ![KDMStarGSW.anchor first, KDMStarGSW.anchor second]

def difference2 {R : Type} [CommRing R] (function : (Fin 2 → R) → R) : R :=
  function (corner true true) - function (corner true false) -
    function (corner false true) + function (corner false false)

theorem difference2_phase {R : Type} [CommRing R] {k : ℕ}
    (bit : Bool) (view : KDMStarGSW.View R 2 k) (column : Fin k) :
    difference2 (fun secret ↦ KDMStarGSW.phase bit secret view column) = 0 := by
  simp [difference2, phase_affine, corner, KDMStarGSW.anchor, Fin.sum_univ_succ]

theorem difference2_weighted_product {R : Type} [CommRing R] (weight : R) :
    difference2 (fun secret : Fin 2 → R ↦ weight * secret 0 * secret 1) = weight := by
  simp [difference2, corner, KDMStarGSW.anchor]

/-- The same public coefficient triple represents the quadratic KDM message
on every key. The next theorem supplies its honest zero-error private coins. -/
def canonical {R : Type} [CommRing R] (weight : R) : RecursiveQuadratic.Ciphertext R 2 :=
  (![![0, -weight], ![0, 0]], 0, 0)

theorem decrypt_canonical {R : Type} [CommRing R] (weight : R) (secret : Fin 2 → R) :
    RecursiveQuadratic.decrypt secret (canonical weight) = weight * secret 0 * secret 1 := by
  simp [RecursiveQuadratic.decrypt, canonical, vecMul, dotProduct, Fin.sum_univ_succ]
  ring

def canonicalPolynomial {R : Type} [CommRing R] (weight : R) :
    RecursiveQuadratic.Polynomial R 2 1 where
  quadratic _ := ![![0, weight], ![0, 0]]
  linear _ := 0
  constant _ := 0

theorem message_canonicalPolynomial {R : Type} [CommRing R] (weight : R) (secret : Fin 2 → R) :
    RecursiveQuadratic.message (canonicalPolynomial weight) secret 0 =
      weight * secret 0 * secret 1 := by
  simp [RecursiveQuadratic.message, canonicalPolynomial, vecMul, dotProduct, Fin.sum_univ_succ]
  ring

theorem canonical_is_fresh {R : Type} [CommRing R] (weight : R) (secret : Fin 2 → R) :
    RecursiveMultiplication.freshCiphertext secret
      (RecursiveQuadratic.message (canonicalPolynomial weight) secret 0)
      (canonical weight).1 (vecMul secret (canonical weight).1) 0 0 = canonical weight := by
  rw [message_canonicalPolynomial]
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · simp [RecursiveMultiplication.freshCiphertext, canonical]
    · simp [RecursiveMultiplication.freshCiphertext, canonical, vecMul, dotProduct,
        Fin.sum_univ_succ]
      ring

/-- No fixed output column, including one selected by an arbitrary nonlinear
public function of this input ciphertext, preserves its phase on every key. -/
theorem no_exact_phase_encoding {R : Type} [CommRing R]
    (bit : Bool) (weight : R) (hweight : weight ≠ 0) :
    ¬ ∃ output : KDMStarGSW.View R 2 1, ∀ secret : Fin 2 → R,
      KDMStarGSW.phase bit secret output 0 = RecursiveQuadratic.decrypt secret (canonical weight) := by
  rintro ⟨output, houtput⟩
  have hzero := difference2_phase bit output 0
  have hfunction : (fun secret ↦ KDMStarGSW.phase bit secret output 0) =
      (fun secret : Fin 2 → R ↦ weight * secret 0 * secret 1) := by
    funext secret
    rw [houtput, decrypt_canonical]
  rw [hfunction, difference2_weighted_product] at hzero
  exact hweight hzero

theorem no_exact_public_converter {R : Type} [CommRing R]
    (bit : Bool) (weight : R) (hweight : weight ≠ 0) :
    ¬ ∃ convert : RecursiveQuadratic.Ciphertext R 2 → KDMStarGSW.View R 2 1,
      ∀ ciphertext secret, KDMStarGSW.phase bit secret (convert ciphertext) 0 =
        RecursiveQuadratic.decrypt secret ciphertext := by
  rintro ⟨convert, hconvert⟩
  exact no_exact_phase_encoding bit weight hweight
    ⟨convert (canonical weight), hconvert (canonical weight)⟩

def magnitude {q : ℕ} [NeZero q] (value : ZMod q) : ℕ :=
  (LatticeCrypto.centeredRepr value).natAbs

theorem difference2_sub {R : Type} [CommRing R] (first second : (Fin 2 → R) → R) :
    difference2 (fun secret ↦ first secret - second secret) = difference2 first - difference2 second := by
  unfold difference2
  ring

theorem magnitude_difference2_le {q : ℕ} [NeZero q]
    (function : (Fin 2 → ZMod q) → ZMod q) (bound : ℕ)
    (hbound : ∀ first second, magnitude (function (corner first second)) ≤ bound) :
    magnitude (difference2 function) ≤ 4 * bound := by
  unfold magnitude difference2
  have hfirst := TFHE.NoiseBounds.centeredRepr_sub_natAbs_le
    (function (corner true true)) (function (corner true false))
  have hsecond := TFHE.NoiseBounds.centeredRepr_sub_natAbs_le
    (function (corner true true) - function (corner true false)) (function (corner false true))
  have hthird := TFHE.NoiseBounds.centeredRepr_add_natAbs_le
    (function (corner true true) - function (corner true false) - function (corner false true))
    (function (corner false false))
  have htt := hbound true true
  have htf := hbound true false
  have hft := hbound false true
  have hff := hbound false false
  unfold magnitude at htt htf hft hff
  omega

/-- For any fixed public output and sufficiently small phase discrepancy,
at least one honest-key corner fails. This is not an average-case attack. -/
theorem exists_bad_conversion_corner {q : ℕ} [NeZero q]
    (bit : Bool) (weight : ZMod q) (output : KDMStarGSW.View (ZMod q) 2 1)
    (bound : ℕ) (hweight : 4 * bound < magnitude weight) :
    ∃ first second : Bool, bound < magnitude
      (KDMStarGSW.phase bit (corner first second) output 0 -
        RecursiveQuadratic.decrypt (corner first second) (canonical weight)) := by
  by_contra h
  push Not at h
  have hbound := magnitude_difference2_le
    (fun secret ↦ KDMStarGSW.phase bit secret output 0 -
      RecursiveQuadratic.decrypt secret (canonical weight)) bound h
  have hquad : (fun secret : Fin 2 → ZMod q ↦ RecursiveQuadratic.decrypt secret (canonical weight)) =
      (fun secret ↦ weight * secret 0 * secret 1) := funext (decrypt_canonical weight)
  rw [difference2_sub, difference2_phase, hquad, difference2_weighted_product, zero_sub] at hbound
  have hbound' : magnitude weight ≤ 4 * bound := by
    simpa only [magnitude, LatticeCrypto.centeredRepr_natAbs_neg] using hbound
  exact (not_lt_of_ge hbound') hweight

end FormalProof4FHE.LWE.KDMStarConversion
