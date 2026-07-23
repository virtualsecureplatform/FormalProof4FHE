/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.GadgetDecomposition
import Mathlib.Data.Fin.Rev

/-!
# TFHE TLWE Sample Extraction

TFHE sample extraction rewrites a ring-TLWE row as a scalar TLWE row under the coefficient-flattened
ring key.  The scalar mask attached to a polynomial `a(X)` is the coefficient vector of `a(1/X)`
in the negacyclic ring: coefficient zero is unchanged, while coefficient `i > 0` is the negation
of coefficient `N - i`.

This file implements that map for the executable `Rq` carrier and proves the exact statement from
TFHE Definition 4.1: the scalar output phase is the constant coefficient of the input ring phase.
The central algebra lemma computes the constant coefficient of executable negacyclic
multiplication; no polynomial identity is assumed informally.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.TFHE.SampleExtraction

/-- Coefficients of `polynomial(1/X)` in a degree-`n+1` negacyclic ring. -/
def reciprocalCoefficients {R : Type} [Neg R] {degree : ℕ}
    (polynomial : Fin (degree + 1) → R) : Fin (degree + 1) → R :=
  Fin.cases (polynomial 0) fun coefficient ↦
    -polynomial (Fin.succ coefficient.rev)

@[simp]
theorem reciprocalCoefficients_zero {R : Type} [Neg R] {degree : ℕ}
    (polynomial : Fin (degree + 1) → R) :
    reciprocalCoefficients polynomial 0 = polynomial 0 := by
  rfl

@[simp]
theorem reciprocalCoefficients_succ {R : Type} [Neg R] {degree : ℕ}
    (polynomial : Fin (degree + 1) → R) (coefficient : Fin degree) :
    reciprocalCoefficients polynomial coefficient.succ =
      -polynomial (Fin.succ coefficient.rev) := by
  rfl

/-- At output coefficient zero, negacyclic convolution pairs coefficient zero with zero and every
positive coefficient `i` with `N-i`, with a minus sign for the unique wrapped product. -/
theorem negacyclicConvCoeff_zero {R : Type} [CommRing R] {degree : ℕ}
    (left right : Fin (degree + 1) → R) :
    LatticeCrypto.negacyclicConvCoeff left right 0 =
      ∑ coefficient, left coefficient * reciprocalCoefficients right coefficient := by
  have hzero :
      (∑ other : Fin (degree + 1),
        if ((0 : Fin (degree + 1)).val + other.val) % (degree + 1) = 0 then
          if (0 : Fin (degree + 1)).val + other.val < degree + 1 then
            left 0 * right other
          else -(left 0 * right other)
        else 0) = left 0 * right 0 := by
    rw [Finset.sum_eq_single (0 : Fin (degree + 1))]
    · simp
    · intro other _ hother
      have hval : other.val ≠ 0 := by
        intro h
        exact hother (Fin.ext h)
      simp [Nat.mod_eq_of_lt other.isLt, hval]
    · intro hnot
      exact (hnot (Finset.mem_univ 0)).elim
  have hpositive (coefficient : Fin degree) :
      (∑ other : Fin (degree + 1),
        if (coefficient.succ.val + other.val) % (degree + 1) = 0 then
          if coefficient.succ.val + other.val < degree + 1 then
            left coefficient.succ * right other
          else -(left coefficient.succ * right other)
        else 0) =
      -(left coefficient.succ * right (Fin.succ coefficient.rev)) := by
    let complement : Fin (degree + 1) := Fin.succ coefficient.rev
    have hcomplement : coefficient.succ.val + complement.val = degree + 1 := by
      simp only [complement, Fin.val_succ, Fin.val_rev]
      omega
    rw [Finset.sum_eq_single complement]
    · have hmodSelf :
          (coefficient.succ.val + complement.val) % (degree + 1) = 0 := by
        rw [hcomplement]
        exact Nat.mod_self (degree + 1)
      have hnotlt : ¬coefficient.succ.val + complement.val < degree + 1 := by
        omega
      rw [if_pos hmodSelf, if_neg hnotlt]
    · intro other _ hother
      have hmod : (coefficient.succ.val + other.val) % (degree + 1) ≠ 0 := by
        intro hzeroMod
        have hsum : coefficient.succ.val + other.val = degree + 1 := by
          by_cases hlt : coefficient.succ.val + other.val < degree + 1
          · rw [Nat.mod_eq_of_lt hlt] at hzeroMod
            omega
          · have hle : degree + 1 ≤ coefficient.succ.val + other.val :=
              Nat.le_of_not_gt hlt
            have hsub_lt :
                coefficient.succ.val + other.val - (degree + 1) < degree + 1 := by
              omega
            rw [Nat.mod_eq_sub_mod hle, Nat.mod_eq_of_lt hsub_lt] at hzeroMod
            omega
        apply hother
        apply Fin.ext
        simp only [complement, Fin.val_succ, Fin.val_rev]
        omega
      rw [if_neg hmod]
    · intro hnot
      exact (hnot (Finset.mem_univ complement)).elim
  unfold LatticeCrypto.negacyclicConvCoeff
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro coefficient _
  refine Fin.cases ?_ (fun positive ↦ ?_) coefficient
  · exact hzero
  · calc
      _ = -(left positive.succ * right positive.rev.succ) := by
        simpa only [Fin.val_zero] using hpositive positive
      _ = left positive.succ * reciprocalCoefficients right positive.succ := by
        simp only [reciprocalCoefficients_succ]
        ring

/-- The constant coefficient of one executable polynomial. -/
def constantCoefficient {q degree : ℕ} (polynomial : RLWE.Rq q (degree + 1)) : ZMod q :=
  LatticeCrypto.Poly.toPi polynomial 0

/-- The executable negacyclic product has the constant-coefficient formula used by sample
extraction. -/
theorem constantCoefficient_mul {q degree : ℕ} [NeZero q]
    (left right : RLWE.Rq q (degree + 1)) :
    constantCoefficient (left * right) =
      ∑ coefficient,
        LatticeCrypto.Poly.toPi left coefficient *
          reciprocalCoefficients (LatticeCrypto.Poly.toPi right) coefficient := by
  change (LatticeCrypto.vectorBackend (ZMod q) (degree + 1)).coeff
      ((LatticeCrypto.vectorNegacyclicRing (ZMod q) (degree + 1)).mul left right)
        (0 : Fin (degree + 1)) = _
  simp only [LatticeCrypto.vectorNegacyclicRing_mul,
    LatticeCrypto.negacyclicMulPure_coeff]
  exact negacyclicConvCoeff_zero
    (LatticeCrypto.Poly.toPi left) (LatticeCrypto.Poly.toPi right)

/-- Flatten an arbitrary ring secret into the scalar secret used by sample extraction. -/
def extractedSecret {q degree rank : ℕ}
    (secret : Fin rank → RLWE.Rq q (degree + 1)) : Fin (rank * (degree + 1)) → ZMod q :=
  fun coordinate ↦
    let indexed := finProdFinEquiv.symm coordinate
    LatticeCrypto.Poly.toPi (secret indexed.1) indexed.2

/-- Extract the scalar mask coefficients of `a(1/X)` and the constant coefficient of `b`. -/
def apply {q degree rank : ℕ}
    (ciphertext : RingCiphertext q (degree + 1) rank) :
    ScalarCiphertext q (rank * (degree + 1)) :=
  ⟨fun coordinate ↦
      let indexed := finProdFinEquiv.symm coordinate
      reciprocalCoefficients
        (LatticeCrypto.Poly.toPi (ciphertext.mask indexed.1)) indexed.2,
    constantCoefficient ciphertext.body⟩

/-- Flattened scalar inner product equals the constant coefficient of the ring inner product. -/
theorem dotProduct_extractedSecret_apply_mask {q degree rank : ℕ} [NeZero q]
    (secret : Fin rank → RLWE.Rq q (degree + 1))
    (ciphertext : RingCiphertext q (degree + 1) rank) :
    dotProduct (extractedSecret secret) (apply ciphertext).mask =
      constantCoefficient (dotProduct secret ciphertext.mask) := by
  unfold dotProduct
  calc
    (∑ coordinate : Fin (rank * (degree + 1)),
        extractedSecret secret coordinate * (apply ciphertext).mask coordinate) =
        ∑ index : Fin rank × Fin (degree + 1),
          LatticeCrypto.Poly.toPi (secret index.1) index.2 *
            reciprocalCoefficients
              (LatticeCrypto.Poly.toPi (ciphertext.mask index.1)) index.2 := by
      apply Fintype.sum_equiv finProdFinEquiv.symm
      intro coordinate
      simp [extractedSecret, apply]
    _ = ∑ component : Fin rank,
          constantCoefficient (secret component * ciphertext.mask component) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro component _
      exact (constantCoefficient_mul (secret component) (ciphertext.mask component)).symm
    _ = constantCoefficient
          (∑ component : Fin rank, secret component * ciphertext.mask component) := by
      change (∑ component : Fin rank,
          Gadget.Base.coefficientAddHom (degree + 1) 0
            (secret component * ciphertext.mask component)) =
        Gadget.Base.coefficientAddHom (degree + 1) 0
          (∑ component : Fin rank, secret component * ciphertext.mask component)
      rw [map_sum]

/-- **TFHE sample-extraction phase theorem.** The output scalar phase is exactly the constant
coefficient of the input ring phase. -/
theorem phase_apply {q degree rank : ℕ} [NeZero q]
    (secret : Fin rank → RLWE.Rq q (degree + 1))
    (ciphertext : RingCiphertext q (degree + 1) rank) :
    TLWE.phase (extractedSecret secret) (apply ciphertext) =
      constantCoefficient (TLWE.phase secret ciphertext) := by
  unfold TLWE.phase
  rw [dotProduct_extractedSecret_apply_mask]
  change constantCoefficient ciphertext.body -
      constantCoefficient (dotProduct secret ciphertext.mask) =
    Gadget.Base.coefficientAddHom (degree + 1) 0
      (ciphertext.body - dotProduct secret ciphertext.mask)
  rw [map_sub]
  rfl

/-- On a binary ring key, coefficient extraction agrees with the native `keyExtract` layout. -/
theorem extractedSecret_embedRingSecret_eq {q degree rank : ℕ}
    (secret : RingBinarySecret rank (degree + 1)) :
    extractedSecret (embedRingSecret q secret) =
      embedBinarySecret (keyExtract secret) := by
  funext coordinate
  obtain ⟨⟨component, coefficient⟩, rfl⟩ := finProdFinEquiv.surjective coordinate
  simp [extractedSecret, embedRingSecret, embedBinaryPolynomial,
    embedBinarySecret, keyExtract]

/-- Native binary-key specialization of the sample-extraction phase theorem. -/
theorem phase_apply_embedRingSecret {q degree rank : ℕ} [NeZero q]
    (secret : RingBinarySecret rank (degree + 1))
    (ciphertext : RingCiphertext q (degree + 1) rank) :
    TLWE.phase (embedBinarySecret (keyExtract secret)) (apply ciphertext) =
      constantCoefficient (TLWE.phase (embedRingSecret q secret) ciphertext) := by
  rw [← extractedSecret_embedRingSecret_eq]
  exact phase_apply (embedRingSecret q secret) ciphertext

end FormalProof4FHE.TFHE.SampleExtraction
