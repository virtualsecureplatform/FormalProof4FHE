/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/
import FormalProof4FHE.LWE.GSWTwoSidedCompiler
import FormalProof4FHE.LWE.GSWQuadraticPreimageRowSupport

/-!
# Signed-source extraction from public quadratic preimages

A public transformation of a binary-secret LWE matrix produces a matrix with
a short left relation whose coefficients all square to one. Consequently the
diagonal freedom in a quadratic certificate becomes its publicly computable
trace. Useful short two-sided certificates recover every original source bit.

The pointwise extraction and error bounds below do not assert an unconditional
impossibility theorem for arbitrary compilers or private witnesses. The
distributional and computational reduction obligations are discussed in the
research log. In particular the parity randomizer in the lifted matrix cannot
be omitted at an even modulus.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.LWE.GSWPublicPreimageBarrier

def signedSecret {R : Type} [CommRing R] {n : ℕ} (bits : Fin n → Bool) :
    Fin (n + 1) → R :=
  Fin.cases 1 (fun row ↦ 1 - 2 * GSWSelfKey.binaryEmbed bits row)

/-- Only public source masks, bodies and independently sampled parity coins
are used. The secret and source errors are not inputs. -/
def liftedMask {R : Type} [CommRing R] {n m : ℕ}
    (a : Matrix (Fin n) (Fin m) R) (body coins : Fin m → R) :
    Matrix (Fin (n + 1)) (Fin m) R :=
  fun row column ↦ Fin.cases (2 * body column - ∑ i, a i column + coins column)
    (fun i ↦ a i column) row

def liftedError {R : Type} [CommRing R] {m : ℕ} (error coins : Fin m → R) : Fin m → R :=
  fun column ↦ 2 * error column + coins column

theorem signedSecret_square {R : Type} [CommRing R] {n : ℕ} (bits : Fin n → Bool)
    (row : Fin (n + 1)) :
    signedSecret (R := R) bits row * signedSecret bits row = 1 := by
  refine Fin.cases ?_ (fun i ↦ ?_) row
  · simp [signedSecret]
  · cases h : bits i
    · simp [signedSecret, GSWSelfKey.binaryEmbed, h]
    · simp only [signedSecret, Fin.cases_succ, GSWSelfKey.binaryEmbed, h, ite_true]
      ring

theorem signed_lift_relation {R : Type} [CommRing R] {n m : ℕ}
    (a : Matrix (Fin n) (Fin m) R) (bits : Fin n → Bool) (error coins : Fin m → R) :
    vecMul (signedSecret bits)
      (liftedMask a (vecMul (GSWSelfKey.binaryEmbed bits) a + error) coins) =
      liftedError error coins := by
  funext column
  simp only [vecMul, dotProduct, Fin.sum_univ_succ, signedSecret, liftedMask,
    liftedError, Fin.cases_zero, Fin.cases_succ, Pi.add_apply, one_mul]
  simp_rw [sub_mul, one_mul, mul_assoc]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

theorem unit_square_diagonal {R : Type} [CommRing R] {n : ℕ}
    (v diagonalValues : Fin n → R) (hunit : ∀ row, v row * v row = 1) :
    dotProduct v ((Matrix.diagonal diagonalValues).mulVec v) = ∑ row, diagonalValues row := by
  simp only [dotProduct, mulVec_diagonal]
  apply Finset.sum_congr rfl
  intro row _
  calc
    v row * (diagonalValues row * v row) = diagonalValues row * (v row * v row) := by ring
    _ = diagonalValues row := by rw [hunit, mul_one]

theorem target_phase {R : Type} [CommRing R] {n : ℕ}
    (weight : R) (index : Fin n) (bits : Fin n → Bool) :
    dotProduct (signedSecret bits)
      ((GSWQuadraticPreimageRowSupport.coordinateTarget weight index.succ 0).mulVec
        (signedSecret bits)) = weight * (1 - 2 * GSWSelfKey.binaryEmbed bits index) := by
  simp [GSWQuadraticPreimageRowSupport.coordinateTarget, mulVec, dotProduct,
    ite_mul, signedSecret, mul_comm]

/-- All diagonal freedom becomes a public trace on the signed relation. -/
theorem trace_relation {R : Type} [CommRing R] {n p r : ℕ}
    (a : Matrix (Fin (n + 1)) (Fin p) R) (b : Matrix (Fin (n + 1)) (Fin r) R)
    (d : Matrix (Fin p) (Fin r) R) (weight : R) (index : Fin n)
    (bits : Fin n → Bool) (e : Fin p → R) (f : Fin r → R)
    (ha : vecMul (signedSecret bits) a = e) (hb : vecMul (signedSecret bits) b = f)
    (witness : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hcertificate : a * d * b.transpose =
      GSWQuadraticPreimageRowSupport.coordinateTarget weight index.succ 0 +
      Matrix.diagonal (fun row ↦ (a * d * b.transpose) row row) + witness - witness.transpose) :
    (∑ row, (a * d * b.transpose) row row) + weight =
      (2 * weight) * GSWSelfKey.binaryEmbed bits index + dotProduct e (d.mulVec f) := by
  have hphase : dotProduct (signedSecret bits) ((a * d * b.transpose).mulVec (signedSecret bits)) =
      dotProduct e (d.mulVec f) := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, mulVec_transpose,
      dotProduct_mulVec, ha, hb]
  rw [hcertificate, sub_mulVec, add_mulVec, add_mulVec, dotProduct_sub,
    dotProduct_add, dotProduct_add, dotProduct_transpose_mulVec,
    unit_square_diagonal _ _ (signedSecret_square bits), target_phase] at hphase
  linear_combination hphase

/-- The same trace argument applies to dense one-sided preimages; row support
is not needed. Its residual is linear, rather than bilinear, in source noise. -/
theorem one_sided_trace_relation {R : Type} [CommRing R] {n m : ℕ}
    (a preimage : Matrix (Fin (n + 1)) (Fin m) R) (weight : R) (index : Fin n)
    (bits : Fin n → Bool) (e : Fin m → R)
    (ha : vecMul (signedSecret bits) a = e)
    (witness : Matrix (Fin (n + 1)) (Fin (n + 1)) R)
    (hcertificate : preimage * a.transpose =
      GSWQuadraticPreimageRowSupport.coordinateTarget weight index.succ 0 +
      Matrix.diagonal (fun row ↦ (preimage * a.transpose) row row) + witness - witness.transpose) :
    (∑ row, (preimage * a.transpose) row row) + weight =
      (2 * weight) * GSWSelfKey.binaryEmbed bits index +
        dotProduct (signedSecret bits) (preimage.mulVec e) := by
  have hphase : dotProduct (signedSecret bits)
      ((preimage * a.transpose).mulVec (signedSecret bits)) =
      dotProduct (signedSecret bits) (preimage.mulVec e) := by
    rw [← mulVec_mulVec, mulVec_transpose, ha]
  rw [hcertificate, sub_mulVec, add_mulVec, add_mulVec, dotProduct_sub,
    dotProduct_add, dotProduct_add, dotProduct_transpose_mulVec,
    unit_square_diagonal _ _ (signedSecret_square bits), target_phase] at hphase
  linear_combination hphase

/-- This is the actual modular bilinear error, without assuming independence. -/
theorem bilinear_noise_bound {q p r : ℕ} [NeZero q]
    (d : Matrix (Fin p) (Fin r) (ZMod q)) (e : Fin p → ZMod q) (f : Fin r → ZMod q)
    (E F L : ℕ)
    (he : ∀ row, (LatticeCrypto.centeredRepr (e row)).natAbs ≤ E)
    (hf : ∀ column, (LatticeCrypto.centeredRepr (f column)).natAbs ≤ F)
    (hd : ∑ row, ∑ column, (LatticeCrypto.centeredRepr (d row column)).natAbs ≤ L) :
    (LatticeCrypto.centeredRepr (dotProduct e (d.mulVec f))).natAbs ≤ E * F * L := by
  unfold dotProduct mulVec
  calc
    _ ≤ ∑ row, (LatticeCrypto.centeredRepr
        (e row * ∑ column, d row column * f column)).natAbs :=
      TFHE.NoiseBounds.centeredRepr_finset_sum_natAbs_le _ _
    _ ≤ ∑ row, E * ((∑ column, (LatticeCrypto.centeredRepr (d row column)).natAbs) * F) := by
      apply Finset.sum_le_sum
      intro row _
      exact (TFHE.NoiseBounds.centeredRepr_mul_natAbs_le _ _).trans
        (Nat.mul_le_mul (he row)
          (GSWQuadraticPreimageRowSupport.projection_noise_bound (d row) f _ F (le_refl _) hf))
    _ = E * F * (∑ row, ∑ column, (LatticeCrypto.centeredRepr (d row column)).natAbs) := by
      simp only [mul_left_comm E, mul_comm _ F, ← Finset.mul_sum]
      ring
    _ ≤ _ := Nat.mul_le_mul_left _ hd

theorem liftedError_bound {q m : ℕ} [NeZero q] (error coins : Fin m → ZMod q)
    (E : ℕ) (he : ∀ column, (LatticeCrypto.centeredRepr (error column)).natAbs ≤ E)
    (hc : ∀ column, (LatticeCrypto.centeredRepr (coins column)).natAbs ≤ 1)
    (column : Fin m) :
    (LatticeCrypto.centeredRepr (liftedError error coins column)).natAbs ≤ 2 * E + 1 := by
  exact (TFHE.NoiseBounds.centeredRepr_add_natAbs_le _ _).trans
    (Nat.add_le_add
      ((TFHE.NoiseBounds.centeredRepr_mul_natAbs_le _ _).trans
        (Nat.mul_le_mul (TFHE.NoiseBounds.centeredRepr_natCast_natAbs_le (q := q) 2)
          (he column))) (hc column))

def recoverBit {q n p r : ℕ} [NeZero q] (weight : ZMod q)
    (a : Matrix (Fin (n + 1)) (Fin p) (ZMod q))
    (b : Matrix (Fin (n + 1)) (Fin r) (ZMod q)) (d : Matrix (Fin p) (Fin r) (ZMod q)) : Bool :=
  TFHE.BootstrappingCorrectness.decodeNearest 0 (2 * weight)
    ((∑ row, (a * d * b.transpose) row row) + weight)

theorem recoverBit_of_certificate {q n p r : ℕ} [NeZero q]
    (a : Matrix (Fin (n + 1)) (Fin p) (ZMod q))
    (b : Matrix (Fin (n + 1)) (Fin r) (ZMod q)) (d : Matrix (Fin p) (Fin r) (ZMod q))
    (weight : ZMod q) (index : Fin n) (bits : Fin n → Bool)
    (e : Fin p → ZMod q) (f : Fin r → ZMod q)
    (ha : vecMul (signedSecret bits) a = e) (hb : vecMul (signedSecret bits) b = f)
    (witness : Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod q))
    (hcertificate : a * d * b.transpose =
      GSWQuadraticPreimageRowSupport.coordinateTarget weight index.succ 0 +
      Matrix.diagonal (fun row ↦ (a * d * b.transpose) row row) + witness - witness.transpose)
    (bound : ℕ)
    (herror : (LatticeCrypto.centeredRepr (dotProduct e (d.mulVec f))).natAbs ≤ bound)
    (hmargin : 2 * bound < TFHE.BootstrappingCorrectness.centeredDistance 0 (2 * weight)) :
    recoverBit weight a b d = bits index := by
  unfold recoverBit
  rw [trace_relation a b d weight index bits e f ha hb witness hcertificate]
  apply TFHE.BootstrappingCorrectness.decodeNearest_encodeBit_of_distance_le
    0 (2 * weight) _ bound (bits index) hmargin
  have hm : (2 * weight) * GSWSelfKey.binaryEmbed (R := ZMod q) bits index =
      TFHE.BootstrappingCorrectness.encodeBit 0 (2 * weight) (bits index) := by
    cases h : bits index <;> simp [GSWSelfKey.binaryEmbed, TFHE.BootstrappingCorrectness.encodeBit, h]
  rw [hm]
  simpa [TFHE.BootstrappingCorrectness.centeredDistance] using herror

def recover {q n p r : ℕ} [NeZero q] (weight : ZMod q)
    (a : Matrix (Fin (n + 1)) (Fin p) (ZMod q))
    (b : Matrix (Fin (n + 1)) (Fin r) (ZMod q))
    (preimages : Fin n → Matrix (Fin p) (Fin r) (ZMod q)) : Fin n → Bool :=
  fun index ↦ recoverBit weight a b (preimages index)

/-- The extractor uses the public lifted source matrices and public preimages.
Neither the binary key nor either source error is supplied to `recover`. -/
theorem recover_lifted_sources {q n p r : ℕ} [NeZero q]
    (a : Matrix (Fin n) (Fin p) (ZMod q)) (b : Matrix (Fin n) (Fin r) (ZMod q))
    (bits : Fin n → Bool) (e coins₁ : Fin p → ZMod q) (f coins₂ : Fin r → ZMod q)
    (weight : ZMod q) (preimages : Fin n → Matrix (Fin p) (Fin r) (ZMod q))
    (witness : Fin n → Matrix (Fin (n + 1)) (Fin (n + 1)) (ZMod q))
    (hcertificate : ∀ index,
      let first := liftedMask a (vecMul (GSWSelfKey.binaryEmbed bits) a + e) coins₁
      let second := liftedMask b (vecMul (GSWSelfKey.binaryEmbed bits) b + f) coins₂
      first * preimages index * second.transpose =
        GSWQuadraticPreimageRowSupport.coordinateTarget weight index.succ 0 +
        Matrix.diagonal (fun row ↦ (first * preimages index * second.transpose) row row) +
        witness index - (witness index).transpose)
    (E F L : ℕ)
    (he : ∀ column, (LatticeCrypto.centeredRepr (e column)).natAbs ≤ E)
    (hf : ∀ column, (LatticeCrypto.centeredRepr (f column)).natAbs ≤ F)
    (hc₁ : ∀ column, (LatticeCrypto.centeredRepr (coins₁ column)).natAbs ≤ 1)
    (hc₂ : ∀ column, (LatticeCrypto.centeredRepr (coins₂ column)).natAbs ≤ 1)
    (hd : ∀ index, ∑ row, ∑ column,
      (LatticeCrypto.centeredRepr (preimages index row column)).natAbs ≤ L)
    (hmargin : 2 * ((2 * E + 1) * (2 * F + 1) * L) <
      TFHE.BootstrappingCorrectness.centeredDistance 0 (2 * weight)) :
    recover weight
      (liftedMask a (vecMul (GSWSelfKey.binaryEmbed bits) a + e) coins₁)
      (liftedMask b (vecMul (GSWSelfKey.binaryEmbed bits) b + f) coins₂) preimages = bits := by
  funext index
  exact recoverBit_of_certificate _ _ _ weight index bits (liftedError e coins₁)
    (liftedError f coins₂) (signed_lift_relation a bits e coins₁)
    (signed_lift_relation b bits f coins₂) (witness index) (hcertificate index) _
    (bilinear_noise_bound _ _ _ _ _ L (liftedError_bound e coins₁ E he hc₁)
      (liftedError_bound f coins₂ F hf hc₂) (hd index)) hmargin

end FormalProof4FHE.LWE.GSWPublicPreimageBarrier
