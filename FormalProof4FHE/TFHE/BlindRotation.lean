/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.GadgetDecomposition

/-!
# Deterministic TFHE Blind-Rotation Step

TFHE blind rotation updates an accumulator with the external product by

`H + (factor - 1) * bootstrapKeyBit`.

If the bootstrapping-key entry encrypts `message`, the ideal multiplier is
`1 + (factor - 1) * message`; for a binary message this is `1` or `factor`.  This file defines the
row-wise affine transformation and proves the exact phase recurrence.  In particular, it also
proves that every transformed TGSW row error is exactly `(factor - 1)` times the original row
error, which is the deterministic starting point for the quantitative bound in TFHE Theorem 4.6.

The executable ring gadget decomposition from `TFHE.GadgetDecomposition` is used directly, so the
one-step theorem has no abstract decomposition premise.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.TFHE

namespace TLWE

/-- Multiply every public coordinate of a TLWE row by one ring element. -/
def scale {R : Type} [Mul R] {dimension : ℕ} (factor : R)
    (ciphertext : Ciphertext R dimension) : Ciphertext R dimension :=
  ⟨fun coordinate ↦ factor * ciphertext.mask coordinate, factor * ciphertext.body⟩

/-- TLWE phase commutes with scalar multiplication over a commutative ring. -/
@[simp]
theorem phase_scale {R : Type} [CommRing R] {dimension : ℕ}
    (secret : Fin dimension → R) (factor : R) (ciphertext : Ciphertext R dimension) :
    phase secret (scale factor ciphertext) = factor * phase secret ciphertext := by
  simp only [phase, scale, dotProduct]
  have hsum :
      (∑ coordinate, secret coordinate * (factor * ciphertext.mask coordinate)) =
        factor * ∑ coordinate, secret coordinate * ciphertext.mask coordinate := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro coordinate _
    ring
  rw [hsum]
  ring

end TLWE

namespace TGSW

/-- Multiply every row coordinate of a TGSW ciphertext by one ring element. -/
def scale {R : Type} [Mul R] {dimension levels : ℕ} (factor : R)
    (ciphertext : Ciphertext R dimension levels) : Ciphertext R dimension levels :=
  (fun coordinate row ↦ factor * ciphertext.1 coordinate row,
    fun row ↦ factor * ciphertext.2 row)

/-- Selecting a row after TGSW scaling is the same as scaling the selected TLWE row. -/
@[simp]
theorem entry_scale {R : Type} [Mul R] {dimension levels : ℕ} (factor : R)
    (ciphertext : Ciphertext R dimension levels) (row : Fin (rowCount dimension levels)) :
    TLWE.entry (scale factor ciphertext) row =
      TLWE.scale factor (TLWE.entry ciphertext row) := by
  rfl

/-- All TGSW row phases scale by the public scalar. -/
theorem batchPhase_scale {R : Type} [CommRing R] {dimension levels : ℕ}
    (secret : Fin dimension → R) (factor : R)
    (ciphertext : Ciphertext R dimension levels) :
    TLWE.batchPhase secret (scale factor ciphertext) =
      fun row ↦ factor * TLWE.batchPhase secret ciphertext row := by
  funext row
  change TLWE.phase secret (TLWE.entry (scale factor ciphertext) row) =
    factor * TLWE.phase secret (TLWE.entry ciphertext row)
  rw [entry_scale, TLWE.phase_scale]

/-- The public affine TGSW transform used by one TFHE blind-rotation iteration:
`H + (factor - 1) * ciphertext`. -/
def affineFactor {R : Type} [Ring R] {dimension levels : ℕ}
    (gadget : Fin levels → R) (factor : R)
    (ciphertext : Ciphertext R dimension levels) : Ciphertext R dimension levels :=
  addGadget gadget 1 (scale (factor - 1) ciphertext)

/-- Phase of a selected affine-transformed TGSW row. -/
theorem phase_entry_affineFactor {R : Type} [CommRing R] {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R) (factor : R)
    (ciphertext : Ciphertext R dimension levels) (row : Fin (rowCount dimension levels)) :
    TLWE.phase secret (TLWE.entry (affineFactor gadget factor ciphertext) row) =
      (factor - 1) * TLWE.phase secret (TLWE.entry ciphertext row) +
        gadgetPhase secret gadget 1 row := by
  calc
    TLWE.phase secret (TLWE.entry (affineFactor gadget factor ciphertext) row) =
        TLWE.batchPhase secret
          (addGadget gadget 1 (scale (factor - 1) ciphertext)) row := by
      rfl
    _ = (TLWE.batchPhase secret (scale (factor - 1) ciphertext) +
          gadgetPhase secret gadget 1) row := by
      rw [batchPhase_addGadget]
    _ = _ := by
      rw [batchPhase_scale]
      rfl

/-- Gadget phases respect the affine plaintext transform
`message ↦ 1 + (factor - 1) * message`. -/
theorem gadgetPhase_affine {R : Type} [CommRing R] {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R)
    (factor message : R) (row : Fin (rowCount dimension levels)) :
    gadgetPhase secret gadget (1 + (factor - 1) * message) row =
      (factor - 1) * gadgetPhase secret gadget message row +
        gadgetPhase secret gadget 1 row := by
  obtain ⟨⟨block, level⟩, rfl⟩ := finProdFinEquiv.surjective row
  cases block using Fin.lastCases <;>
    simp only [gadgetPhase_last, gadgetPhase_castSucc] <;> ring

/-- The affine transform scales each original TGSW row error by exactly `factor - 1`. -/
theorem rowError_affineFactor {R : Type} [CommRing R] {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R)
    (factor message : R) (ciphertext : Ciphertext R dimension levels)
    (index : Fin (dimension + 1) × Fin levels) :
    rowError secret gadget (1 + (factor - 1) * message)
        (affineFactor gadget factor ciphertext) index =
      (factor - 1) * rowError secret gadget message ciphertext index := by
  unfold rowError
  rw [phase_entry_affineFactor, gadgetPhase_affine]
  ring

/-- Consequently, the complete weighted external-product row error is scaled by `factor - 1`. -/
theorem externalProductError_affineFactor {R : Type} [CommRing R]
    {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R)
    (factor message : R) (digits : Fin (dimension + 1) → Fin levels → R)
    (ciphertext : Ciphertext R dimension levels) :
    externalProductError secret gadget (1 + (factor - 1) * message) digits
        (affineFactor gadget factor ciphertext) =
      (factor - 1) * externalProductError secret gadget message digits ciphertext := by
  unfold externalProductError
  simp_rw [rowError_affineFactor]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  ring

end TGSW

namespace BlindRotation

/-- The proof-facing ring unit is the executable bundled unit.  The explicit degree split bridges
the two instance dictionaries used by the vector backend. -/
theorem rq_one_eq_bundled (q degree : ℕ) :
    (1 : RLWE.Rq q degree) = (RLWE.negacyclicRing q degree).one := by
  cases degree with
  | zero =>
      apply LatticeCrypto.Poly.ext_get_eq
      intro coefficient
      exact coefficient.elim0
  | succ degree => rfl

@[simp]
theorem rq_zero_coefficient {q degree : ℕ} [NeZero q] (coefficient : Fin (degree + 1)) :
    LatticeCrypto.Poly.toPi (0 : RLWE.Rq q (degree + 1)) coefficient = 0 := by
  rw [← Gadget.Base.coefficientAddHom_apply]
  exact (Gadget.Base.coefficientAddHom (degree + 1) coefficient).map_zero

@[simp]
theorem rq_one_coefficient {q degree : ℕ} [NeZero q] (coefficient : Fin (degree + 1)) :
    LatticeCrypto.Poly.toPi (1 : RLWE.Rq q (degree + 1)) coefficient =
      if coefficient.val = 0 then 1 else 0 := by
  rw [rq_one_eq_bundled]
  simp [RLWE.negacyclicRing, LatticeCrypto.vectorNegacyclicRing,
    LatticeCrypto.Poly.toPi, Vector.get, Array.getElem_ofFn]

/-- A native constant-polynomial bit is the ring's ordinary zero-or-one bit embedding at positive
degree. -/
theorem embedConstantBit_eq_embedBit {q degree : ℕ} [NeZero q] (bit : Bool) :
    embedConstantBit q (degree + 1) bit =
      (embedBit bit : RLWE.Rq q (degree + 1)) := by
  cases bit with
  | false =>
      apply LatticeCrypto.Poly.ext_get_eq
      intro coefficient
      change LatticeCrypto.Poly.toPi (embedConstantBit q (degree + 1) false) coefficient =
        LatticeCrypto.Poly.toPi
          (embedBit false : RLWE.Rq q (degree + 1)) coefficient
      simp [embedConstantBit, embedBinaryPolynomial, embedBit]
  | true =>
      apply LatticeCrypto.Poly.ext_get_eq
      intro coefficient
      change LatticeCrypto.Poly.toPi (embedConstantBit q (degree + 1) true) coefficient =
        LatticeCrypto.Poly.toPi
          (embedBit true : RLWE.Rq q (degree + 1)) coefficient
      simp [embedConstantBit, embedBinaryPolynomial, embedBit]

/-- The affine multiplier selects `1` for a zero bit and `factor` for a one bit. -/
theorem affineMultiplier_embedBit {R : Type} [CommRing R] (factor : R) (bit : Bool) :
    1 + (factor - 1) * embedBit bit = if bit then factor else 1 := by
  cases bit <;> simp [embedBit]

/-- One executable native blind-rotation update over the concrete negacyclic ring. -/
noncomputable def step {q degree rank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (factor : RLWE.Rq q degree)
    (bootstrapKeyEntry : RingGSWCiphertext q degree rank params.levels)
    (accumulator : RingCiphertext q degree rank) : RingCiphertext q degree rank :=
  TGSW.externalProduct (Gadget.Base.ringExtendedDigits params accumulator)
    (TGSW.affineFactor (Gadget.Base.ringGadget params) factor bootstrapKeyEntry)

/-- **Exact native blind-rotation recurrence.** If the selected bootstrapping-key entry is viewed
as a TGSW encryption of `message`, then the accumulator phase is multiplied by
`1 + (factor - 1) * message`.  The only extra term is exactly `(factor - 1)` times the weighted
row error of the original entry. -/
theorem phase_step {q degree rank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (secret : Fin rank → RLWE.Rq q degree) (factor message : RLWE.Rq q degree)
    (bootstrapKeyEntry : RingGSWCiphertext q degree rank params.levels)
    (accumulator : RingCiphertext q degree rank) :
    TLWE.phase secret (step params factor bootstrapKeyEntry accumulator) =
      (1 + (factor - 1) * message) * TLWE.phase secret accumulator +
        (factor - 1) *
          TGSW.externalProductError secret (Gadget.Base.ringGadget params) message
            (Gadget.Base.ringExtendedDigits params accumulator) bootstrapKeyEntry := by
  cases degree with
  | zero =>
      apply LatticeCrypto.Poly.ext_get_eq
      intro coefficient
      exact coefficient.elim0
  | succ degree =>
      unfold step
      rw [TGSW.phase_externalProduct_eq_mul_add_error secret
        (Gadget.Base.ringGadget params) (1 + (factor - 1) * message) accumulator
        (Gadget.Base.ringExtendedDigits params accumulator)
        (TGSW.affineFactor (Gadget.Base.ringGadget params) factor bootstrapKeyEntry)
        (Gadget.Base.ringExtendedDigits_decomposes params accumulator)]
      rw [TGSW.externalProductError_affineFactor]

/-- Binary-message specialization of the native blind-rotation recurrence. -/
theorem phase_step_bit {q degree rank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (secret : Fin rank → RLWE.Rq q (degree + 1))
    (factor : RLWE.Rq q (degree + 1)) (bit : Bool)
    (bootstrapKeyEntry : RingGSWCiphertext q (degree + 1) rank params.levels)
    (accumulator : RingCiphertext q (degree + 1) rank) :
    TLWE.phase secret (step params factor bootstrapKeyEntry accumulator) =
      (if bit then factor else 1) * TLWE.phase secret accumulator +
        (factor - 1) *
          TGSW.externalProductError secret (Gadget.Base.ringGadget params)
            (embedConstantBit q (degree + 1) bit)
            (Gadget.Base.ringExtendedDigits params accumulator) bootstrapKeyEntry := by
  simpa only [embedConstantBit_eq_embedBit, affineMultiplier_embedBit] using
    (phase_step params secret factor
      (embedConstantBit q (degree + 1) bit) bootstrapKeyEntry accumulator)

/-- Public controls for a sequence of blind-rotation updates. -/
structure Control (q degree rank levels : ℕ) where
  factor : RLWE.Rq q degree
  bootstrapKeyEntry : RingGSWCiphertext q degree rank levels

/-- Execute a list of blind-rotation controls, recomputing gadget digits after every update. -/
noncomputable def run {q degree rank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) :
    RingCiphertext q degree rank → List (Control q degree rank params.levels) →
      RingCiphertext q degree rank
  | accumulator, [] => accumulator
  | accumulator, control :: controls =>
      run params (step params control.factor control.bootstrapKeyEntry accumulator) controls

@[simp]
theorem run_nil {q degree rank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (accumulator : RingCiphertext q degree rank) :
    run params accumulator [] = accumulator := by
  rfl

@[simp]
theorem run_cons {q degree rank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (accumulator : RingCiphertext q degree rank)
    (control : Control q degree rank params.levels)
    (controls : List (Control q degree rank params.levels)) :
    run params accumulator (control :: controls) =
      run params (step params control.factor control.bootstrapKeyEntry accumulator) controls := by
  rfl

/-! ## Binary blind-rotation trace and exact accumulated error -/

/-- One proof-carrying blind-rotation control: the public factor and key entry, together with the
hidden bit that the key entry is intended to encrypt. -/
structure BitControl (q degree rank levels : ℕ) where
  factor : RLWE.Rq q (degree + 1)
  bit : Bool
  bootstrapKeyEntry : RingGSWCiphertext q (degree + 1) rank levels

/-- Erase the ghost bit from a binary control. -/
def BitControl.erase {q degree rank levels : ℕ}
    (control : BitControl q degree rank levels) : Control q (degree + 1) rank levels :=
  ⟨control.factor, control.bootstrapKeyEntry⟩

/-- Execute a binary blind-rotation trace.  The `bit` field is ghost specification data and is not
used by the executable update. -/
noncomputable def runBits {q degree rank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) :
    RingCiphertext q (degree + 1) rank →
      List (BitControl q degree rank params.levels) →
        RingCiphertext q (degree + 1) rank
  | accumulator, [] => accumulator
  | accumulator, control :: controls =>
      runBits params
        (step params control.factor control.bootstrapKeyEntry accumulator) controls

/-- Erasing all ghost bits turns `runBits` into the public `run` evaluator exactly. -/
theorem runBits_eq_run_map_erase {q degree rank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (accumulator : RingCiphertext q (degree + 1) rank)
    (controls : List (BitControl q degree rank params.levels)) :
    runBits params accumulator controls =
      run params accumulator (controls.map BitControl.erase) := by
  induction controls generalizing accumulator with
  | nil => rfl
  | cons control controls ih =>
      simp only [runBits, List.map_cons, run]
      exact ih (step params control.factor control.bootstrapKeyEntry accumulator)

/-- Product of all ideal bit-selected rotation factors in execution order. -/
noncomputable def idealMultiplier {q degree rank levels : ℕ} :
    List (BitControl q degree rank levels) → RLWE.Rq q (degree + 1)
  | [] => 1
  | control :: controls =>
      idealMultiplier controls * (if control.bit then control.factor else 1)

/-- The row-error contribution introduced by one binary update at its current accumulator. -/
noncomputable def stepError {q degree rank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (secret : Fin rank → RLWE.Rq q (degree + 1))
    (accumulator : RingCiphertext q (degree + 1) rank)
    (control : BitControl q degree rank params.levels) : RLWE.Rq q (degree + 1) :=
  (control.factor - 1) *
    TGSW.externalProductError secret (Gadget.Base.ringGadget params)
      (embedConstantBit q (degree + 1) control.bit)
      (Gadget.Base.ringExtendedDigits params accumulator) control.bootstrapKeyEntry

/-- Exact accumulated error: an earlier step error is multiplied by every later ideal selector. -/
noncomputable def accumulatedError {q degree rank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (secret : Fin rank → RLWE.Rq q (degree + 1)) :
    RingCiphertext q (degree + 1) rank →
      List (BitControl q degree rank params.levels) → RLWE.Rq q (degree + 1)
  | _, [] => 0
  | accumulator, control :: controls =>
      idealMultiplier controls * stepError params secret accumulator control +
        accumulatedError params secret
          (step params control.factor control.bootstrapKeyEntry accumulator) controls

/-- **Exact blind-rotation invariant.** After any list of binary controls, the accumulator phase is
the initial phase multiplied by all bit-selected factors, plus the explicitly accumulated TGSW
row-error polynomial. -/
theorem phase_runBits {q degree rank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (secret : Fin rank → RLWE.Rq q (degree + 1))
    (accumulator : RingCiphertext q (degree + 1) rank)
    (controls : List (BitControl q degree rank params.levels)) :
    TLWE.phase secret (runBits params accumulator controls) =
      idealMultiplier controls * TLWE.phase secret accumulator +
        accumulatedError params secret accumulator controls := by
  induction controls generalizing accumulator with
  | nil => simp [runBits, idealMultiplier, accumulatedError]
  | cons control controls ih =>
      rw [runBits, ih]
      rw [phase_step_bit params secret control.factor control.bit
        control.bootstrapKeyEntry accumulator]
      simp only [idealMultiplier, accumulatedError, stepError]
      ring

/-! ## Native negacyclic rotation controls -/

/-- The executable representative of `X^exponent` for an exponent modulo `2N`.  Exponents below
`N` are positive monomials; exponents from `N` through `2N-1` use `X^N = -1`. -/
def rotationMonomial (q degree : ℕ) (exponent : Fin (2 * (degree + 1))) :
    RLWE.Rq q (degree + 1) :=
  LatticeCrypto.Poly.ofPi fun coefficient ↦
    if exponent.val < degree + 1 then
      if coefficient.val = exponent.val then 1 else 0
    else if coefficient.val = exponent.val - (degree + 1) then -1 else 0

@[simp]
theorem rotationMonomial_coefficient (q degree : ℕ)
    (exponent : Fin (2 * (degree + 1))) (coefficient : Fin (degree + 1)) :
    LatticeCrypto.Poly.toPi (rotationMonomial q degree exponent) coefficient =
      if exponent.val < degree + 1 then
        if coefficient.val = exponent.val then 1 else 0
      else if coefficient.val = exponent.val - (degree + 1) then -1 else 0 := by
  simp [rotationMonomial]

/-- Exponent zero is the ring unit. -/
theorem rotationMonomial_zero {q degree : ℕ} [NeZero q] :
    rotationMonomial q degree 0 = 1 := by
  apply LatticeCrypto.Poly.ext_get_eq
  intro coefficient
  change LatticeCrypto.Poly.toPi (rotationMonomial q degree 0) coefficient =
    LatticeCrypto.Poly.toPi (1 : RLWE.Rq q (degree + 1)) coefficient
  rw [rotationMonomial_coefficient, rq_one_coefficient]
  simp

/-- Instantiate the public factors `X^{-a_i}` from rounded scalar mask exponents and pair them
with the corresponding native bootstrapping-key entries.  The bit is ghost specification data. -/
def nativeControls {q degree rank lweDimension : ℕ}
    (params : Gadget.Base.Parameters q)
    (roundExponent : ZMod q → Fin (2 * (degree + 1)))
    (input : ScalarCiphertext q lweDimension)
    (bootstrappingKey : Native.BootstrappingKey
      q (degree + 1) rank params.levels lweDimension)
    (lweSecret : BinarySecret lweDimension) :
    List (BitControl q degree rank params.levels) :=
  List.ofFn fun coordinate ↦
    { factor := rotationMonomial q degree (-roundExponent (input.mask coordinate))
      bit := lweSecret coordinate
      bootstrapKeyEntry := bootstrappingKey coordinate }

/-- The genuinely public controls used by the evaluator. -/
def publicNativeControls {q degree rank lweDimension : ℕ}
    (params : Gadget.Base.Parameters q)
    (roundExponent : ZMod q → Fin (2 * (degree + 1)))
    (input : ScalarCiphertext q lweDimension)
    (bootstrappingKey : Native.BootstrappingKey
      q (degree + 1) rank params.levels lweDimension) :
    List (Control q (degree + 1) rank params.levels) :=
  List.ofFn fun coordinate ↦
    { factor := rotationMonomial q degree (-roundExponent (input.mask coordinate))
      bootstrapKeyEntry := bootstrappingKey coordinate }

/-- Erasing the secret-bit annotations from native controls gives exactly the public controls. -/
theorem map_erase_nativeControls {q degree rank lweDimension : ℕ}
    (params : Gadget.Base.Parameters q)
    (roundExponent : ZMod q → Fin (2 * (degree + 1)))
    (input : ScalarCiphertext q lweDimension)
    (bootstrappingKey : Native.BootstrappingKey
      q (degree + 1) rank params.levels lweDimension)
    (lweSecret : BinarySecret lweDimension) :
    (nativeControls params roundExponent input bootstrappingKey lweSecret).map
        BitControl.erase =
      publicNativeControls params roundExponent input bootstrappingKey := by
  unfold nativeControls publicNativeControls
  rw [← List.ofFn_comp']
  rfl

/-- Native blind rotation over every scalar mask coordinate.  The executable input contains only
the public rounded factors and bootstrapping-key entries. -/
noncomputable def nativeBlindRotate {q degree rank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (roundExponent : ZMod q → Fin (2 * (degree + 1)))
    (input : ScalarCiphertext q lweDimension)
    (bootstrappingKey : Native.BootstrappingKey
      q (degree + 1) rank params.levels lweDimension)
    (initialAccumulator : RingCiphertext q (degree + 1) rank) :
    RingCiphertext q (degree + 1) rank :=
  run params initialAccumulator
    (publicNativeControls params roundExponent input bootstrappingKey)

/-- Exact phase invariant for the native `X^{-a_i}` blind-rotation controls. -/
theorem phase_nativeBlindRotate {q degree rank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (roundExponent : ZMod q → Fin (2 * (degree + 1)))
    (input : ScalarCiphertext q lweDimension)
    (bootstrappingKey : Native.BootstrappingKey
      q (degree + 1) rank params.levels lweDimension)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : Fin rank → RLWE.Rq q (degree + 1))
    (initialAccumulator : RingCiphertext q (degree + 1) rank) :
    TLWE.phase ringSecret
        (nativeBlindRotate params roundExponent input bootstrappingKey
          initialAccumulator) =
      idealMultiplier
          (nativeControls params roundExponent input bootstrappingKey lweSecret) *
        TLWE.phase ringSecret initialAccumulator +
      accumulatedError params ringSecret initialAccumulator
        (nativeControls params roundExponent input bootstrappingKey lweSecret) := by
  rw [nativeBlindRotate, ← map_erase_nativeControls params roundExponent input
    bootstrappingKey lweSecret, ← runBits_eq_run_map_erase]
  exact phase_runBits params ringSecret initialAccumulator
    (nativeControls params roundExponent input bootstrappingKey lweSecret)

end BlindRotation

end FormalProof4FHE.TFHE
