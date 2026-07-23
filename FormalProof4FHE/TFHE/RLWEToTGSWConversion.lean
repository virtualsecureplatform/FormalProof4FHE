/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.InternalProduct
import FormalProof4FHE.TFHE.SharpRotationNoise

/-!
# Narrow-Noise RLWE-to-TGSW Conversion

This module formalizes the standard row-wise conversion from gadget-scaled RLWE ciphertexts to
one TGSW ciphertext.  Suppose `bodyRows level` encrypts `message * gadget level`.  For every
target-key component `j`, a conversion key TGSW-encrypting `-secret j` externally multiplies that
body row.  The resulting row encrypts

`-(secret j * (message * gadget level))`,

which is exactly the mask-block phase required by a TGSW encryption of `message`; the original
body row supplies the final block.

Unlike a fresh TGSW sample, the converted ciphertext has correlated public masks and its mask-row
error contains an external-product error.  The exact identities below track that error, and the
final theorem gives a checked narrow-noise bound for the executable base decomposition.

This conversion does not by itself remove circular security.  A conversion key encrypting
`-secret j` under `secret` has ideal mask-block phase

`secret target * secret j * gadget level`.

For rank-one RLWE this is the ring square `secret^2`, rather than the complete coefficient outer
product exposed by a fresh coefficient-by-coefficient TFHE bootstrapping key.  The construction
therefore isolates a smaller quadratic circular-security boundary while retaining usable small
error.
-/

open Matrix

namespace FormalProof4FHE.TFHE.TGSW.RLWEToTGSW

/-! ## Deterministic conversion -/

/-- One converted TGSW row.  Mask blocks are external products with the corresponding
secret-component conversion key; the final block is the supplied gadget-scaled RLWE row. -/
def convertedRow {R : Type} [Semiring R] {dimension levels : ℕ}
    (bodyRows : Fin levels → TLWE.Ciphertext R dimension)
    (digits : Fin levels → Fin (dimension + 1) → Fin levels → R)
    (conversionKey : Fin dimension → Ciphertext R dimension levels)
    (index : Fin (dimension + 1) × Fin levels) : TLWE.Ciphertext R dimension :=
  Fin.lastCases (bodyRows index.2)
    (fun coordinate ↦ externalProduct (digits index.2) (conversionKey coordinate)) index.1

/-- Assemble the converted rows in the native flattened TGSW layout. -/
def convert {R : Type} [Semiring R] {dimension levels : ℕ}
    (bodyRows : Fin levels → TLWE.Ciphertext R dimension)
    (digits : Fin levels → Fin (dimension + 1) → Fin levels → R)
    (conversionKey : Fin dimension → Ciphertext R dimension levels) :
    Ciphertext R dimension levels :=
  TLWE.batchOfRows fun row ↦
    convertedRow bodyRows digits conversionKey (finProdFinEquiv.symm row)

/-- Selecting a converted mask-block row exposes the corresponding external product. -/
@[simp]
theorem entry_convert_castSucc {R : Type} [Semiring R] {dimension levels : ℕ}
    (bodyRows : Fin levels → TLWE.Ciphertext R dimension)
    (digits : Fin levels → Fin (dimension + 1) → Fin levels → R)
    (conversionKey : Fin dimension → Ciphertext R dimension levels)
    (coordinate : Fin dimension) (level : Fin levels) :
    TLWE.entry (convert bodyRows digits conversionKey)
        (finProdFinEquiv (Fin.castSucc coordinate, level)) =
      externalProduct (digits level) (conversionKey coordinate) := by
  change convertedRow bodyRows digits conversionKey
      (finProdFinEquiv.symm
        (finProdFinEquiv (Fin.castSucc coordinate, level))) = _
  rw [show finProdFinEquiv.symm
      (finProdFinEquiv (Fin.castSucc coordinate, level)) =
        (Fin.castSucc coordinate, level) by
    exact Equiv.symm_apply_apply finProdFinEquiv _]
  simp only [convertedRow, Fin.lastCases_castSucc]

/-- Selecting a converted final-block row recovers the supplied gadget-scaled RLWE row. -/
@[simp]
theorem entry_convert_last {R : Type} [Semiring R] {dimension levels : ℕ}
    (bodyRows : Fin levels → TLWE.Ciphertext R dimension)
    (digits : Fin levels → Fin (dimension + 1) → Fin levels → R)
    (conversionKey : Fin dimension → Ciphertext R dimension levels)
    (level : Fin levels) :
    TLWE.entry (convert bodyRows digits conversionKey)
        (finProdFinEquiv (Fin.last dimension, level)) = bodyRows level := by
  change convertedRow bodyRows digits conversionKey
      (finProdFinEquiv.symm
        (finProdFinEquiv (Fin.last dimension, level))) = _
  rw [show finProdFinEquiv.symm
      (finProdFinEquiv (Fin.last dimension, level)) =
        (Fin.last dimension, level) by
    exact Equiv.symm_apply_apply finProdFinEquiv _]
  simp only [convertedRow, Fin.lastCases_last]

/-- Error of one supplied body row relative to its intended gadget-scaled message. -/
def bodyRowError {R : Type} [Ring R] {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R)
    (bodyRows : Fin levels → TLWE.Ciphertext R dimension) (level : Fin levels) : R :=
  TLWE.phase secret (bodyRows level) - message * gadget level

/-- The body-row phase is its intended gadget multiple plus `bodyRowError`. -/
theorem phase_bodyRow_eq {R : Type} [Ring R] {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R)
    (bodyRows : Fin levels → TLWE.Ciphertext R dimension) (level : Fin levels) :
    TLWE.phase secret (bodyRows level) =
      message * gadget level + bodyRowError secret gadget message bodyRows level := by
  unfold bodyRowError
  abel

/-- Exact mask-block phase of the conversion.  Its only extra terms are multiplication of the
input-row error by `-secret coordinate` and the ordinary external-product row-error sum. -/
theorem phase_entry_convert_castSucc_eq
    {R : Type} [CommRing R] {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R)
    (bodyRows : Fin levels → TLWE.Ciphertext R dimension)
    (digits : Fin levels → Fin (dimension + 1) → Fin levels → R)
    (conversionKey : Fin dimension → Ciphertext R dimension levels)
    (hDecomposes : ∀ level, Gadget.Decomposes gadget (bodyRows level) (digits level))
    (coordinate : Fin dimension) (level : Fin levels) :
    TLWE.phase secret
        (TLWE.entry (convert bodyRows digits conversionKey)
          (finProdFinEquiv (Fin.castSucc coordinate, level))) =
      gadgetPhase secret gadget message
          (finProdFinEquiv (Fin.castSucc coordinate, level)) +
        (-secret coordinate) * bodyRowError secret gadget message bodyRows level +
        externalProductError secret gadget (-secret coordinate) (digits level)
          (conversionKey coordinate) := by
  rw [entry_convert_castSucc]
  rw [phase_externalProduct_eq_mul_add_error secret gadget (-secret coordinate)
    (bodyRows level) (digits level) (conversionKey coordinate) (hDecomposes level)]
  rw [phase_bodyRow_eq secret gadget message bodyRows level, gadgetPhase_castSucc]
  ring

/-- Exact final-block phase of the conversion. -/
theorem phase_entry_convert_last_eq
    {R : Type} [CommRing R] {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R)
    (bodyRows : Fin levels → TLWE.Ciphertext R dimension)
    (digits : Fin levels → Fin (dimension + 1) → Fin levels → R)
    (conversionKey : Fin dimension → Ciphertext R dimension levels)
    (level : Fin levels) :
    TLWE.phase secret
        (TLWE.entry (convert bodyRows digits conversionKey)
          (finProdFinEquiv (Fin.last dimension, level))) =
      gadgetPhase secret gadget message
          (finProdFinEquiv (Fin.last dimension, level)) +
        bodyRowError secret gadget message bodyRows level := by
  rw [entry_convert_last, phase_bodyRow_eq, gadgetPhase_last]

/-- Converted mask-row error in the native `TGSW.rowError` convention. -/
theorem rowError_convert_castSucc_eq
    {R : Type} [CommRing R] {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R)
    (bodyRows : Fin levels → TLWE.Ciphertext R dimension)
    (digits : Fin levels → Fin (dimension + 1) → Fin levels → R)
    (conversionKey : Fin dimension → Ciphertext R dimension levels)
    (hDecomposes : ∀ level, Gadget.Decomposes gadget (bodyRows level) (digits level))
    (coordinate : Fin dimension) (level : Fin levels) :
    rowError secret gadget message (convert bodyRows digits conversionKey)
        (Fin.castSucc coordinate, level) =
      (-secret coordinate) * bodyRowError secret gadget message bodyRows level +
        externalProductError secret gadget (-secret coordinate) (digits level)
          (conversionKey coordinate) := by
  unfold rowError
  rw [phase_entry_convert_castSucc_eq secret gadget message bodyRows digits conversionKey
    hDecomposes coordinate level]
  ring

/-- Converted final-row error is exactly the input body-row error. -/
theorem rowError_convert_last_eq
    {R : Type} [CommRing R] {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R)
    (bodyRows : Fin levels → TLWE.Ciphertext R dimension)
    (digits : Fin levels → Fin (dimension + 1) → Fin levels → R)
    (conversionKey : Fin dimension → Ciphertext R dimension levels)
    (level : Fin levels) :
    rowError secret gadget message (convert bodyRows digits conversionKey)
        (Fin.last dimension, level) =
      bodyRowError secret gadget message bodyRows level := by
  unfold rowError
  rw [phase_entry_convert_last_eq secret gadget message bodyRows digits conversionKey level]
  ring

/-! ## The remaining circular message -/

/-- A conversion key for component `source` TGSW-encrypts `-secret source`.  Its ideal mask row
at component `target` is the gadget-scaled pairwise product of the two secret components. -/
theorem conversionKey_maskPhase_eq_product
    {R : Type} [CommRing R] {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R)
    (source target : Fin dimension) (level : Fin levels) :
    gadgetPhase secret gadget (-secret source)
        (finProdFinEquiv (Fin.castSucc target, level)) =
      secret target * secret source * gadget level := by
  rw [gadgetPhase_castSucc]
  ring

/-- At rank one the conversion-key mask message is exactly the ring square. -/
theorem conversionKey_maskPhase_rankOne_eq_square
    {R : Type} [CommRing R] {levels : ℕ}
    (secret : Fin 1 → R) (gadget : Fin levels → R) (level : Fin levels) :
    gadgetPhase secret gadget (-secret 0)
        (finProdFinEquiv (Fin.castSucc (0 : Fin 1), level)) =
      secret 0 * secret 0 * gadget level := by
  exact conversionKey_maskPhase_eq_product secret gadget 0 0 level

/-- The final block of the same conversion key is only linear in the selected secret component. -/
theorem conversionKey_bodyPhase_eq_linear
    {R : Type} [CommRing R] {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R)
    (source : Fin dimension) (level : Fin levels) :
    gadgetPhase secret gadget (-secret source)
        (finProdFinEquiv (Fin.last dimension, level)) =
      -(secret source * gadget level) := by
  rw [gadgetPhase_last]
  ring

/-! ## Checked narrow-noise bound -/

/-- Worst-case mask-row error budget for RLWE-to-TGSW conversion with executable base digits. -/
def maskRowNoiseBudget
    (degree dimension levels base secretBound bodyErrorBound conversionRowErrorBound : ℕ) : ℕ :=
  (degree + 1) * (secretBound * bodyErrorBound) +
    ((dimension + 1) * levels) *
      ((degree + 1) * ((base - 1) * conversionRowErrorBound))

noncomputable section

local instance conversionRqCommRing (q degree : ℕ) :
    CommRing (RLWE.Rq q degree) :=
  LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree

local instance conversionRqAddCommGroup (q degree : ℕ) :
    AddCommGroup (RLWE.Rq q degree) :=
  (conversionRqCommRing q degree).toAddCommGroup

local instance conversionRqAdd (q degree : ℕ) : Add (RLWE.Rq q degree) :=
  (conversionRqAddCommGroup q degree).toAdd

local instance conversionRqSub (q degree : ℕ) : Sub (RLWE.Rq q degree) :=
  (conversionRqAddCommGroup q degree).toSub

local instance conversionRqNeg (q degree : ℕ) : Neg (RLWE.Rq q degree) :=
  (conversionRqAddCommGroup q degree).toNeg

local instance conversionRqZero (q degree : ℕ) : Zero (RLWE.Rq q degree) :=
  (conversionRqAddCommGroup q degree).toZero

local instance conversionRqMul (q degree : ℕ) : Mul (RLWE.Rq q degree) :=
  (conversionRqCommRing q degree).toMul

local instance conversionRqOne (q degree : ℕ) : One (RLWE.Rq q degree) :=
  (conversionRqCommRing q degree).toAddGroupWithOne.toOne

local instance conversionRqRing (q degree : ℕ) : Ring (RLWE.Rq q degree) :=
  (conversionRqCommRing q degree).toRing

local instance conversionRqSemiring (q degree : ℕ) : Semiring (RLWE.Rq q degree) :=
  (conversionRqCommRing q degree).toSemiring

/- Concrete wrappers fix one coherent proof-facing ring dictionary in theorem statements.  This
avoids accidentally mixing the executable operation instances with the generic `CommRing`
operations consumed by `TGSW.rowError`. -/

noncomputable def ringNeg {q degree : ℕ} (value : RLWE.Rq q degree) : RLWE.Rq q degree :=
  @Neg.neg (RLWE.Rq q degree) (conversionRqNeg q degree) value

noncomputable def ringBodyRowError {q degree dimension levels : ℕ}
    (secret : Fin dimension → RLWE.Rq q degree)
    (gadget : Fin levels → RLWE.Rq q degree) (message : RLWE.Rq q degree)
    (bodyRows : Fin levels → TLWE.Ciphertext (RLWE.Rq q degree) dimension)
    (level : Fin levels) : RLWE.Rq q degree :=
  @bodyRowError (RLWE.Rq q degree) (conversionRqRing q degree)
    dimension levels secret gadget message bodyRows level

noncomputable def ringConvert {q degree dimension levels : ℕ}
    (bodyRows : Fin levels → TLWE.Ciphertext (RLWE.Rq q degree) dimension)
    (digits : Fin levels → Fin (dimension + 1) → Fin levels → RLWE.Rq q degree)
    (conversionKey : Fin dimension →
      Ciphertext (RLWE.Rq q degree) dimension levels) :
    Ciphertext (RLWE.Rq q degree) dimension levels :=
  @convert (RLWE.Rq q degree) (conversionRqSemiring q degree)
    dimension levels bodyRows digits conversionKey

noncomputable def ringRowError {q degree dimension levels : ℕ}
    (secret : Fin dimension → RLWE.Rq q degree)
    (gadget : Fin levels → RLWE.Rq q degree) (message : RLWE.Rq q degree)
    (ciphertext : Ciphertext (RLWE.Rq q degree) dimension levels)
    (index : Fin (dimension + 1) × Fin levels) : RLWE.Rq q degree :=
  @rowError (RLWE.Rq q degree) (conversionRqRing q degree)
    dimension levels secret gadget message ciphertext index

/-- The exact conversion remains in the small-noise regime whenever the input body rows and the
single conversion key have the displayed small centered-coefficient bounds. -/
theorem cInfNorm_rowError_convert_castSucc_le
    {q degree dimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (secret : Fin dimension → RLWE.Rq q (degree + 1))
    (message : RLWE.Rq q (degree + 1))
    (bodyRows : Fin params.levels →
      TLWE.Ciphertext (RLWE.Rq q (degree + 1)) dimension)
    (conversionKey : Fin dimension →
      Ciphertext (RLWE.Rq q (degree + 1)) dimension params.levels)
    (secretBound bodyErrorBound conversionRowErrorBound : ℕ)
    (hSecret : ∀ coordinate,
      LatticeCrypto.cInfNorm (ringNeg (secret coordinate)) ≤ secretBound)
    (hBody : ∀ level,
      LatticeCrypto.cInfNorm
        (ringBodyRowError secret (Gadget.Base.ringGadget params) message bodyRows level) ≤
          bodyErrorBound)
    (hConversion : ∀ coordinate index,
      LatticeCrypto.cInfNorm
        (ringRowError secret (Gadget.Base.ringGadget params)
          (ringNeg (secret coordinate)) (conversionKey coordinate) index) ≤
            conversionRowErrorBound)
    (coordinate : Fin dimension) (level : Fin params.levels) :
    LatticeCrypto.cInfNorm
        (ringRowError secret (Gadget.Base.ringGadget params) message
          (ringConvert bodyRows
            (fun level ↦ Gadget.Base.ringExtendedDigits params (bodyRows level))
            conversionKey)
          (Fin.castSucc coordinate, level)) ≤
      maskRowNoiseBudget degree dimension params.levels params.base
        secretBound bodyErrorBound conversionRowErrorBound := by
  unfold ringRowError ringConvert
  have hBody' := hBody
  unfold ringBodyRowError at hBody'
  have hConversion' := hConversion
  unfold ringRowError ringNeg at hConversion'
  have hSecret' := hSecret
  unfold ringNeg at hSecret'
  rw [rowError_convert_castSucc_eq secret (Gadget.Base.ringGadget params) message
    bodyRows (fun level ↦ Gadget.Base.ringExtendedDigits params (bodyRows level))
    conversionKey (fun level ↦ Gadget.Base.ringExtendedDigits_decomposes params
      (bodyRows level)) coordinate level]
  unfold maskRowNoiseBudget
  apply (NoiseBounds.cInfNorm_add_le _ _).trans
  apply Nat.add_le_add
  · have hmul := SharpRotationNoise.cInfNorm_mul_le_linear
      (-secret coordinate)
      (bodyRowError secret (Gadget.Base.ringGadget params) message bodyRows level)
    exact hmul.trans (Nat.mul_le_mul_left (degree + 1)
      (Nat.mul_le_mul
        (hSecret' coordinate)
        (hBody' level)))
  · exact SharpRotationNoise.cInfNorm_externalProductError_ringDigits_le_linear
      params secret (-secret coordinate) (bodyRows level) (conversionKey coordinate)
      conversionRowErrorBound (hConversion' coordinate)

/-- Final-block rows do not pay the conversion-key external-product cost. -/
theorem cInfNorm_rowError_convert_last_le
    {q degree dimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (secret : Fin dimension → RLWE.Rq q (degree + 1))
    (message : RLWE.Rq q (degree + 1))
    (bodyRows : Fin params.levels →
      TLWE.Ciphertext (RLWE.Rq q (degree + 1)) dimension)
    (conversionKey : Fin dimension →
      Ciphertext (RLWE.Rq q (degree + 1)) dimension params.levels)
    (bodyErrorBound : ℕ)
    (hBody : ∀ level,
      LatticeCrypto.cInfNorm
        (ringBodyRowError secret (Gadget.Base.ringGadget params) message bodyRows level) ≤
          bodyErrorBound)
    (level : Fin params.levels) :
    LatticeCrypto.cInfNorm
        (ringRowError secret (Gadget.Base.ringGadget params) message
          (ringConvert bodyRows
            (fun level ↦ Gadget.Base.ringExtendedDigits params (bodyRows level))
            conversionKey)
          (Fin.last dimension, level)) ≤ bodyErrorBound := by
  unfold ringRowError ringConvert
  rw [rowError_convert_last_eq]
  simpa only [ringBodyRowError] using hBody level

end

end FormalProof4FHE.TFHE.TGSW.RLWEToTGSW
