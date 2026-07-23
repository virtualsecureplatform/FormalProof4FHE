/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.BootstrappingSecurity

/-!
# Deterministic TFHE Evaluation Identities

This file begins the functional-correctness layer for the native finite-modulus TFHE model.  It
formalizes the exact algebra needed before analytic noise bounds:

* phases commute with finite linear combinations of TLWE rows;
* a TGSW--TLWE external product carries the product of the two plaintext phases plus the explicit
  weighted TGSW error; and
* key switching preserves the source phase up to the explicit weighted key-switch error whenever
  the supplied gadget digits recompose the source mask.

Gadget decomposition algorithms and norm bounds are deliberately separate.  The theorems accept
digits together with an exact recomposition hypothesis, so later executable decomposers can plug
into these identities without changing the cryptographic games.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE

namespace TLWE

/-- Componentwise addition of two individually represented TLWE rows. -/
def add {R : Type} [Add R] {dimension : ℕ}
    (left right : Ciphertext R dimension) : Ciphertext R dimension :=
  ⟨left.mask + right.mask, left.body + right.body⟩

/-- TLWE phase is additive in the public row. -/
@[simp]
theorem phase_add {R : Type} [CommRing R] {dimension : ℕ}
    (secret : Fin dimension → R) (left right : Ciphertext R dimension) :
    phase secret (add left right) = phase secret left + phase secret right := by
  simp only [phase, add, dotProduct, Pi.add_apply]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  ring

/-- Finite linear combination of individually represented TLWE rows. -/
def linearCombination {R Index : Type} [Semiring R] [Fintype Index]
    {dimension : ℕ} (weight : Index → R)
    (rows : Index → Ciphertext R dimension) : Ciphertext R dimension :=
  ⟨fun coordinate ↦ ∑ index, weight index * (rows index).mask coordinate,
    ∑ index, weight index * (rows index).body⟩

/-- TLWE phase is linear in the public row. -/
theorem phase_linearCombination {R Index : Type} [CommRing R] [Fintype Index]
    {dimension : ℕ} (secret : Fin dimension → R)
    (weight : Index → R) (rows : Index → Ciphertext R dimension) :
    phase secret (linearCombination weight rows) =
      ∑ index, weight index * phase secret (rows index) := by
  classical
  simp only [phase, linearCombination, dotProduct]
  simp_rw [Finset.mul_sum, mul_sub]
  rw [Finset.sum_comm]
  rw [Finset.sum_sub_distrib]
  simp_rw [Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro index _
  apply Finset.sum_congr rfl
  intro coordinate _
  ring

/-- Negate the mask of a TLWE row while subtracting its body from a supplied scalar body.  This is
the affine form used by key switching. -/
def subtractFromBody {R : Type} [Ring R] {dimension : ℕ}
    (body : R) (row : Ciphertext R dimension) : Ciphertext R dimension :=
  ⟨-row.mask, body - row.body⟩

/-- The phase of `subtractFromBody body row` is `body - phase(row)`. -/
theorem phase_subtractFromBody {R : Type} [CommRing R] {dimension : ℕ}
    (secret : Fin dimension → R) (body : R) (row : Ciphertext R dimension) :
    phase secret (subtractFromBody body row) = body - phase secret row := by
  simp only [phase, subtractFromBody, dotProduct, Pi.neg_apply]
  simp_rw [mul_neg]
  rw [Finset.sum_neg_distrib]
  ring

end TLWE

namespace Gadget

/-- Recompose one extended-coordinate gadget block from its digits. -/
def recompose {R : Type} [Semiring R] {levels : ℕ}
    (gadget : Fin levels → R) (digits : Fin levels → R) : R :=
  ∑ level, digits level * gadget level

/-- The mask followed by the body is the extended TLWE vector decomposed by TGSW. -/
def extendedCiphertext {R : Type} {dimension : ℕ}
    (ciphertext : TLWE.Ciphertext R dimension) : Fin (dimension + 1) → R :=
  Fin.snoc ciphertext.mask ciphertext.body

/-- Exact gadget-decomposition predicate for every extended coordinate of a TLWE row. -/
def Decomposes {R : Type} [Semiring R] {dimension levels : ℕ}
    (gadget : Fin levels → R)
    (ciphertext : TLWE.Ciphertext R dimension)
    (digits : Fin (dimension + 1) → Fin levels → R) : Prop :=
  ∀ block, recompose gadget (digits block) = extendedCiphertext ciphertext block

/-- Exact gadget-decomposition predicate for the mask coordinates used by key switching. -/
def DecomposesMask {R : Type} [Semiring R]
    {sourceDimension levels : ℕ}
    (gadget : Fin levels → R)
    (ciphertext : TLWE.Ciphertext R sourceDimension)
    (digits : Fin sourceDimension → Fin levels → R) : Prop :=
  ∀ coordinate, recompose gadget (digits coordinate) = ciphertext.mask coordinate

/-- Approximate gadget-decomposition contract.  The supplied digits exactly recompose the input
plus an explicit residual row.  Analytic bounds on that residual are intentionally separate. -/
def DecomposesWithError {R : Type} [Semiring R] {dimension levels : ℕ}
    (gadget : Fin levels → R)
    (ciphertext residual : TLWE.Ciphertext R dimension)
    (digits : Fin (dimension + 1) → Fin levels → R) : Prop :=
  Decomposes gadget (TLWE.add ciphertext residual) digits

/-- Residual produced by any proposed digit vector: `digits · gadget - ciphertext`, coordinate by
coordinate over the extended TLWE row. -/
def decompositionError {R : Type} [Ring R] {dimension levels : ℕ}
    (gadget : Fin levels → R)
    (ciphertext : TLWE.Ciphertext R dimension)
    (digits : Fin (dimension + 1) → Fin levels → R) :
    TLWE.Ciphertext R dimension :=
  ⟨fun coordinate ↦
      recompose gadget (digits (Fin.castSucc coordinate)) - ciphertext.mask coordinate,
    recompose gadget (digits (Fin.last dimension)) - ciphertext.body⟩

/-- The computed decomposition residual satisfies the approximate contract exactly. -/
theorem decomposesWithError_decompositionError {R : Type} [CommRing R]
    {dimension levels : ℕ} (gadget : Fin levels → R)
    (ciphertext : TLWE.Ciphertext R dimension)
    (digits : Fin (dimension + 1) → Fin levels → R) :
    DecomposesWithError gadget ciphertext
      (decompositionError gadget ciphertext digits) digits := by
  intro block
  cases block using Fin.lastCases <;>
    simp [TLWE.add, decompositionError, extendedCiphertext]

/-- Exact decomposition is the zero-residual specialization of the approximate contract. -/
theorem decomposesWithError_zero_iff {R : Type} [CommRing R]
    {dimension levels : ℕ} (gadget : Fin levels → R)
    (ciphertext : TLWE.Ciphertext R dimension)
    (digits : Fin (dimension + 1) → Fin levels → R) :
    DecomposesWithError gadget ciphertext (TLWE.trivial 0) digits ↔
      Decomposes gadget ciphertext digits := by
  simp only [DecomposesWithError, Decomposes]
  constructor
  · intro h block
    simpa [TLWE.add, TLWE.trivial, extendedCiphertext] using h block
  · intro h block
    simpa [TLWE.add, TLWE.trivial, extendedCiphertext] using h block

end Gadget

namespace TGSW

/-- Interpret extended-coordinate gadget digits as weights for the rows of a TGSW ciphertext. -/
def externalProduct {R : Type} [Semiring R] {dimension levels : ℕ}
    (digits : Fin (dimension + 1) → Fin levels → R)
    (ciphertext : Ciphertext R dimension levels) : TLWE.Ciphertext R dimension :=
  TLWE.linearCombination
    (fun index : Fin (dimension + 1) × Fin levels ↦ digits index.1 index.2)
    (fun index ↦ TLWE.entry ciphertext (finProdFinEquiv index))

/-- The phase of an external product is the corresponding weighted sum of TGSW row phases. -/
theorem phase_externalProduct {R : Type} [CommRing R] {dimension levels : ℕ}
    (secret : Fin dimension → R)
    (digits : Fin (dimension + 1) → Fin levels → R)
    (ciphertext : Ciphertext R dimension levels) :
    TLWE.phase secret (externalProduct digits ciphertext) =
      ∑ index : Fin (dimension + 1) × Fin levels,
        digits index.1 index.2 *
          TLWE.phase secret (TLWE.entry ciphertext (finProdFinEquiv index)) := by
  exact TLWE.phase_linearCombination secret _ _

/-- Row-wise deviation of a TGSW ciphertext from its ideal gadget phase. -/
def rowError {R : Type} [Ring R] {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R)
    (ciphertext : Ciphertext R dimension levels)
    (index : Fin (dimension + 1) × Fin levels) : R :=
  TLWE.phase secret (TLWE.entry ciphertext (finProdFinEquiv index)) -
    gadgetPhase secret gadget message (finProdFinEquiv index)

/-- Weighted aggregate of all TGSW row errors used by one external product. -/
def externalProductError {R : Type} [Ring R] {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R)
    (digits : Fin (dimension + 1) → Fin levels → R)
    (ciphertext : Ciphertext R dimension levels) : R :=
  ∑ index : Fin (dimension + 1) × Fin levels,
    digits index.1 index.2 * rowError secret gadget message ciphertext index

/-- Exact gadget recomposition turns the weighted ideal TGSW phases into
`message * phase(input)`. -/
theorem weighted_gadgetPhase_eq_mul_phase {R : Type} [CommRing R]
    {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R)
    (input : TLWE.Ciphertext R dimension)
    (digits : Fin (dimension + 1) → Fin levels → R)
    (hDecomposes : Gadget.Decomposes gadget input digits) :
    (∑ index : Fin (dimension + 1) × Fin levels,
      digits index.1 index.2 *
        gadgetPhase secret gadget message (finProdFinEquiv index)) =
      message * TLWE.phase secret input := by
  classical
  have hMask (coordinate : Fin dimension) :
      (∑ level, digits (Fin.castSucc coordinate) level *
        gadgetPhase secret gadget message
          (finProdFinEquiv (Fin.castSucc coordinate, level))) =
        -(message * secret coordinate * input.mask coordinate) := by
    simp_rw [gadgetPhase_castSucc]
    calc
      _ = ∑ level, -(message * secret coordinate *
          (digits (Fin.castSucc coordinate) level * gadget level)) := by
        apply Finset.sum_congr rfl
        intro level _
        ring
      _ = -(∑ level, message * secret coordinate *
          (digits (Fin.castSucc coordinate) level * gadget level)) := by
        rw [Finset.sum_neg_distrib]
      _ = -(message * secret coordinate *
          Gadget.recompose gadget (digits (Fin.castSucc coordinate))) := by
        simp [Gadget.recompose, Finset.mul_sum]
      _ = _ := by
        rw [hDecomposes (Fin.castSucc coordinate)]
        simp [Gadget.extendedCiphertext]
  have hLast :
      (∑ level, digits (Fin.last dimension) level *
        gadgetPhase secret gadget message
          (finProdFinEquiv (Fin.last dimension, level))) =
        message * input.body := by
    simp_rw [gadgetPhase_last]
    calc
      _ = ∑ level, message *
          (digits (Fin.last dimension) level * gadget level) := by
        apply Finset.sum_congr rfl
        intro level _
        ring
      _ = message * Gadget.recompose gadget (digits (Fin.last dimension)) := by
        simp [Gadget.recompose, Finset.mul_sum]
      _ = _ := by
        rw [hDecomposes (Fin.last dimension)]
        simp [Gadget.extendedCiphertext]
  rw [Fintype.sum_prod_type, Fin.sum_univ_castSucc]
  simp_rw [hMask]
  rw [hLast]
  simp only [TLWE.phase, dotProduct]
  have hFactor :
      (∑ coordinate, message * secret coordinate * input.mask coordinate) =
        message * ∑ coordinate, secret coordinate * input.mask coordinate := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro coordinate _
    ring
  rw [Finset.sum_neg_distrib]
  rw [hFactor]
  ring

/-- Approximate-recomposition counterpart of `weighted_gadgetPhase_eq_mul_phase`.  The complete
effect of gadget rounding is the plaintext multiplier times the TLWE phase of the explicit
decomposition residual. -/
theorem weighted_gadgetPhase_eq_mul_phase_add_decompositionError
    {R : Type} [CommRing R] {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R)
    (input residual : TLWE.Ciphertext R dimension)
    (digits : Fin (dimension + 1) → Fin levels → R)
    (hDecomposes : Gadget.DecomposesWithError gadget input residual digits) :
    (∑ index : Fin (dimension + 1) × Fin levels,
      digits index.1 index.2 *
        gadgetPhase secret gadget message (finProdFinEquiv index)) =
      message * TLWE.phase secret input + message * TLWE.phase secret residual := by
  have h := weighted_gadgetPhase_eq_mul_phase secret gadget message
    (TLWE.add input residual) digits hDecomposes
  rw [TLWE.phase_add, mul_add] at h
  exact h

/-- **Exact external-product correctness identity.** With exact gadget recomposition, multiplying
a TGSW encryption of `message` by a TLWE input produces phase
`message * phase(input) + weightedRowError`. -/
theorem phase_externalProduct_eq_mul_add_error {R : Type} [CommRing R]
    {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R)
    (input : TLWE.Ciphertext R dimension)
    (digits : Fin (dimension + 1) → Fin levels → R)
    (ciphertext : Ciphertext R dimension levels)
    (hDecomposes : Gadget.Decomposes gadget input digits) :
    TLWE.phase secret (externalProduct digits ciphertext) =
      message * TLWE.phase secret input +
        externalProductError secret gadget message digits ciphertext := by
  rw [phase_externalProduct]
  have hrow (index : Fin (dimension + 1) × Fin levels) :
      TLWE.phase secret (TLWE.entry ciphertext (finProdFinEquiv index)) =
        gadgetPhase secret gadget message (finProdFinEquiv index) +
          (TLWE.phase secret (TLWE.entry ciphertext (finProdFinEquiv index)) -
            gadgetPhase secret gadget message (finProdFinEquiv index)) := by
    ring
  calc
    _ = ∑ index : Fin (dimension + 1) × Fin levels,
        digits index.1 index.2 *
          (gadgetPhase secret gadget message (finProdFinEquiv index) +
            (TLWE.phase secret (TLWE.entry ciphertext (finProdFinEquiv index)) -
              gadgetPhase secret gadget message (finProdFinEquiv index))) := by
      apply Finset.sum_congr rfl
      intro index _
      exact congrArg (fun value ↦ digits index.1 index.2 * value) (hrow index)
    _ = (∑ index : Fin (dimension + 1) × Fin levels,
          digits index.1 index.2 *
            gadgetPhase secret gadget message (finProdFinEquiv index)) +
        ∑ index : Fin (dimension + 1) × Fin levels,
          digits index.1 index.2 *
            (TLWE.phase secret (TLWE.entry ciphertext (finProdFinEquiv index)) -
              gadgetPhase secret gadget message (finProdFinEquiv index)) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
    _ = _ := by
      rw [weighted_gadgetPhase_eq_mul_phase secret gadget message input digits hDecomposes]
      rfl

/-- **Exact approximate-decomposition external-product identity.**  For a decomposition with
explicit residual `delta`, the output phase is

`message * phase(input) + message * phase(delta) + weightedRowError`.

This is the algebraic core of TFHE Theorem 3.14 before placing norm bounds on the last two terms. -/
theorem phase_externalProduct_eq_mul_add_decompositionError_add_rowError
    {R : Type} [CommRing R] {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R)
    (input residual : TLWE.Ciphertext R dimension)
    (digits : Fin (dimension + 1) → Fin levels → R)
    (ciphertext : Ciphertext R dimension levels)
    (hDecomposes : Gadget.DecomposesWithError gadget input residual digits) :
    TLWE.phase secret (externalProduct digits ciphertext) =
      message * TLWE.phase secret input +
        message * TLWE.phase secret residual +
        externalProductError secret gadget message digits ciphertext := by
  rw [phase_externalProduct]
  have hrow (index : Fin (dimension + 1) × Fin levels) :
      TLWE.phase secret (TLWE.entry ciphertext (finProdFinEquiv index)) =
        gadgetPhase secret gadget message (finProdFinEquiv index) +
          rowError secret gadget message ciphertext index := by
    unfold rowError
    ring
  calc
    _ = ∑ index : Fin (dimension + 1) × Fin levels,
        digits index.1 index.2 *
          (gadgetPhase secret gadget message (finProdFinEquiv index) +
            rowError secret gadget message ciphertext index) := by
      apply Finset.sum_congr rfl
      intro index _
      exact congrArg (fun value ↦ digits index.1 index.2 * value) (hrow index)
    _ = (∑ index : Fin (dimension + 1) × Fin levels,
          digits index.1 index.2 *
            gadgetPhase secret gadget message (finProdFinEquiv index)) +
        externalProductError secret gadget message digits ciphertext := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib]
      rfl
    _ = _ := by
      rw [weighted_gadgetPhase_eq_mul_phase_add_decompositionError secret gadget message
        input residual digits hDecomposes]

/-- Unconditional form using the residual computed from the supplied digits.  This theorem lets
an executable decomposition algorithm plug directly into external-product correctness. -/
theorem phase_externalProduct_eq_mul_add_computedDecompositionError_add_rowError
    {R : Type} [CommRing R] {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R)
    (input : TLWE.Ciphertext R dimension)
    (digits : Fin (dimension + 1) → Fin levels → R)
    (ciphertext : Ciphertext R dimension levels) :
    TLWE.phase secret (externalProduct digits ciphertext) =
      message * TLWE.phase secret input +
        message * TLWE.phase secret (Gadget.decompositionError gadget input digits) +
        externalProductError secret gadget message digits ciphertext := by
  exact phase_externalProduct_eq_mul_add_decompositionError_add_rowError
    secret gadget message input (Gadget.decompositionError gadget input digits)
    digits ciphertext (Gadget.decomposesWithError_decompositionError gadget input digits)

namespace KeySwitch

/-- View a flattened key-switch table as rows indexed by source coordinate and gadget level. -/
def row {R : Type} {targetDimension sourceDimension levels : ℕ}
    (keySwitchKey : TLWE.BatchCiphertext R targetDimension (sourceDimension * levels))
    (index : Fin sourceDimension × Fin levels) : TLWE.Ciphertext R targetDimension :=
  TLWE.entry keySwitchKey (finProdFinEquiv index)

/-- Deterministic key switching using supplied gadget digits for the source mask. -/
def apply {R : Type} [CommRing R]
    {targetDimension sourceDimension levels : ℕ}
    (digits : Fin sourceDimension → Fin levels → R)
    (input : TLWE.Ciphertext R sourceDimension)
    (keySwitchKey : TLWE.BatchCiphertext R targetDimension (sourceDimension * levels)) :
    TLWE.Ciphertext R targetDimension :=
  TLWE.subtractFromBody input.body
    (TLWE.linearCombination
      (fun index : Fin sourceDimension × Fin levels ↦ digits index.1 index.2)
      (row keySwitchKey))

/-- Error of one key-switch row relative to its intended gadget-scaled source-key message. -/
def rowError {R : Type} [Ring R]
    {targetDimension sourceDimension levels : ℕ}
    (targetSecret : Fin targetDimension → R)
    (sourceSecret : Fin sourceDimension → R)
    (gadget : Fin levels → R)
    (keySwitchKey : TLWE.BatchCiphertext R targetDimension (sourceDimension * levels))
    (index : Fin sourceDimension × Fin levels) : R :=
  TLWE.phase targetSecret (row keySwitchKey index) -
    sourceSecret index.1 * gadget index.2

/-- Weighted key-switch error accumulated by the supplied gadget digits. -/
def error {R : Type} [Ring R]
    {targetDimension sourceDimension levels : ℕ}
    (targetSecret : Fin targetDimension → R)
    (sourceSecret : Fin sourceDimension → R)
    (gadget : Fin levels → R)
    (digits : Fin sourceDimension → Fin levels → R)
    (keySwitchKey : TLWE.BatchCiphertext R targetDimension (sourceDimension * levels)) : R :=
  ∑ index : Fin sourceDimension × Fin levels,
    digits index.1 index.2 *
      rowError targetSecret sourceSecret gadget keySwitchKey index

/-- Exact mask recomposition turns the gadget-scaled source-key messages in a key-switch table
into the source TLWE mask inner product. -/
theorem weighted_message_eq_dotProduct {R : Type} [CommRing R]
    {sourceDimension levels : ℕ}
    (sourceSecret : Fin sourceDimension → R)
    (gadget : Fin levels → R)
    (input : TLWE.Ciphertext R sourceDimension)
    (digits : Fin sourceDimension → Fin levels → R)
    (hDecomposes : Gadget.DecomposesMask gadget input digits) :
    (∑ index : Fin sourceDimension × Fin levels,
      digits index.1 index.2 * (sourceSecret index.1 * gadget index.2)) =
      dotProduct sourceSecret input.mask := by
  classical
  rw [Fintype.sum_prod_type]
  simp only [dotProduct]
  apply Finset.sum_congr rfl
  intro coordinate _
  calc
    (∑ level, digits coordinate level *
        (sourceSecret coordinate * gadget level)) =
        ∑ level, sourceSecret coordinate *
          (digits coordinate level * gadget level) := by
      apply Finset.sum_congr rfl
      intro level _
      ring
    _ = sourceSecret coordinate *
        Gadget.recompose gadget (digits coordinate) := by
      simp [Gadget.recompose, Finset.mul_sum]
    _ = sourceSecret coordinate * input.mask coordinate := by
      rw [hDecomposes coordinate]

/-- **Exact key-switch correctness identity.** If the supplied digits recompose the source mask,
key switching preserves the source phase up to the explicitly accumulated key-switch-row error. -/
theorem phase_apply_eq_phase_sub_error {R : Type} [CommRing R]
    {targetDimension sourceDimension levels : ℕ}
    (targetSecret : Fin targetDimension → R)
    (sourceSecret : Fin sourceDimension → R)
    (gadget : Fin levels → R)
    (digits : Fin sourceDimension → Fin levels → R)
    (input : TLWE.Ciphertext R sourceDimension)
    (keySwitchKey : TLWE.BatchCiphertext R targetDimension (sourceDimension * levels))
    (hDecomposes : Gadget.DecomposesMask gadget input digits) :
    TLWE.phase targetSecret (apply digits input keySwitchKey) =
      TLWE.phase sourceSecret input -
        error targetSecret sourceSecret gadget digits keySwitchKey := by
  unfold apply
  rw [TLWE.phase_subtractFromBody, TLWE.phase_linearCombination]
  have hrow (index : Fin sourceDimension × Fin levels) :
      TLWE.phase targetSecret (row keySwitchKey index) =
        sourceSecret index.1 * gadget index.2 +
          (TLWE.phase targetSecret (row keySwitchKey index) -
            sourceSecret index.1 * gadget index.2) := by
    ring
  have hsplit :
      (∑ index : Fin sourceDimension × Fin levels,
        digits index.1 index.2 *
          TLWE.phase targetSecret (row keySwitchKey index)) =
        (∑ index : Fin sourceDimension × Fin levels,
          digits index.1 index.2 *
            (sourceSecret index.1 * gadget index.2)) +
          error targetSecret sourceSecret gadget digits keySwitchKey := by
    calc
      _ = ∑ index : Fin sourceDimension × Fin levels,
          digits index.1 index.2 *
            (sourceSecret index.1 * gadget index.2 +
              (TLWE.phase targetSecret (row keySwitchKey index) -
                sourceSecret index.1 * gadget index.2)) := by
        apply Finset.sum_congr rfl
        intro index _
        exact congrArg (fun value ↦ digits index.1 index.2 * value) (hrow index)
      _ = (∑ index : Fin sourceDimension × Fin levels,
            digits index.1 index.2 *
              (sourceSecret index.1 * gadget index.2)) +
          ∑ index : Fin sourceDimension × Fin levels,
            digits index.1 index.2 *
              (TLWE.phase targetSecret (row keySwitchKey index) -
                sourceSecret index.1 * gadget index.2) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
      _ = _ := by
        rfl
  rw [hsplit]
  rw [weighted_message_eq_dotProduct sourceSecret gadget input digits hDecomposes]
  simp only [TLWE.phase]
  ring

end KeySwitch

end TGSW

end FormalProof4FHE.TFHE
