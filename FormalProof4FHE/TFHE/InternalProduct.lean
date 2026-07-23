/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.Evaluation

/-!
# Native TGSW Internal-Product and CMux Normal Forms

The TFHE internal product decomposes every row of one TGSW ciphertext and externally multiplies
those digits by a second TGSW ciphertext.  This file defines that deterministic operation and
proves its exact row-phase normal form.  It also proves that a pure message-one gadget reconstructs
an exactly decomposed TLWE row as a complete ciphertext, and derives complete-ciphertext zero/one
CMux endpoint identities with one explicit homogeneous-control internal-product perturbation.

If the control and data ciphertexts carry messages `muControl` and `muData`, respectively, then
each output row has the ideal gadget phase for `muControl * muData` plus exactly three residual
terms:

* `muControl` times the data-ciphertext row error;
* `muControl` times the phase of the gadget-decomposition residual; and
* the weighted control-ciphertext row error from the external product.

The theorems are purely algebraic.  In particular, they do **not** assert that the perturbation's
derived public masks are fresh or uniformly distributed.  That quantitative distributional
statement is a separate obligation for a native TFHE circular-security candidate evaluator.
-/

open Matrix

namespace FormalProof4FHE.TFHE

namespace TLWE

/-- Assemble a batch ciphertext from individually represented TLWE rows. -/
def batchOfRows {R : Type} {dimension samples : ℕ}
    (rows : Fin samples → Ciphertext R dimension) : BatchCiphertext R dimension samples :=
  (fun coordinate sample ↦ (rows sample).mask coordinate,
    fun sample ↦ (rows sample).body)

/-- Selecting a row from `batchOfRows` recovers the original row definitionally. -/
@[simp]
theorem entry_batchOfRows {R : Type} {dimension samples : ℕ}
    (rows : Fin samples → Ciphertext R dimension) (sample : Fin samples) :
    entry (batchOfRows rows) sample = rows sample := by
  rfl

/-- Componentwise subtraction of two individually represented TLWE rows. -/
def sub {R : Type} [Sub R] {dimension : ℕ}
    (left right : Ciphertext R dimension) : Ciphertext R dimension :=
  ⟨left.mask - right.mask, left.body - right.body⟩

/-- TLWE phase is compatible with componentwise subtraction. -/
@[simp]
theorem phase_sub {R : Type} [CommRing R] {dimension : ℕ}
    (secret : Fin dimension → R) (left right : Ciphertext R dimension) :
    phase secret (sub left right) = phase secret left - phase secret right := by
  simp only [phase, sub, dotProduct, Pi.sub_apply]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  ring

end TLWE

namespace TGSW

/-- Componentwise addition of native TGSW ciphertext rows. -/
def add {R : Type} [Add R] {dimension levels : ℕ}
    (left right : Ciphertext R dimension levels) : Ciphertext R dimension levels :=
  TLWE.batchOfRows fun row ↦ TLWE.add (TLWE.entry left row) (TLWE.entry right row)

/-- Selecting a row commutes with native TGSW addition. -/
@[simp]
theorem entry_add {R : Type} [Add R] {dimension levels : ℕ}
    (left right : Ciphertext R dimension levels)
    (row : Fin (rowCount dimension levels)) :
    TLWE.entry (add left right) row =
      TLWE.add (TLWE.entry left row) (TLWE.entry right row) := by
  rfl

/-- Componentwise subtraction of native TGSW ciphertext rows. -/
def sub {R : Type} [Sub R] {dimension levels : ℕ}
    (left right : Ciphertext R dimension levels) : Ciphertext R dimension levels :=
  TLWE.batchOfRows fun row ↦ TLWE.sub (TLWE.entry left row) (TLWE.entry right row)

/-- Selecting a row commutes with native TGSW subtraction. -/
@[simp]
theorem entry_sub {R : Type} [Sub R] {dimension levels : ℕ}
    (left right : Ciphertext R dimension levels)
    (row : Fin (rowCount dimension levels)) :
    TLWE.entry (sub left right) row =
      TLWE.sub (TLWE.entry left row) (TLWE.entry right row) := by
  rfl

/-- Native TGSW internal product with caller-supplied gadget digits for every data row.

For each data row, the operation is the ordinary TGSW--TLWE external product with the control
ciphertext.  The data ciphertext itself occurs in the correctness contract through the supplied
digits and decomposition residuals. -/
def internalProductWithDigits {R : Type} [Semiring R] {dimension levels : ℕ}
    (digits : Fin (rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (control : Ciphertext R dimension levels) : Ciphertext R dimension levels :=
  TLWE.batchOfRows fun row ↦ externalProduct (digits row) control

/-- Selecting one row of the internal product is the corresponding external product. -/
@[simp]
theorem entry_internalProductWithDigits {R : Type} [Semiring R]
    {dimension levels : ℕ}
    (digits : Fin (rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (control : Ciphertext R dimension levels)
    (row : Fin (rowCount dimension levels)) :
    TLWE.entry (internalProductWithDigits digits control) row =
      externalProduct (digits row) control := by
  rfl

/-- The external product distributes over componentwise addition of TGSW ciphertexts. -/
theorem externalProduct_add
    {R : Type} [CommSemiring R] {dimension levels : ℕ}
    (digits : Fin (dimension + 1) → Fin levels → R)
    (left right : Ciphertext R dimension levels) :
    externalProduct digits (add left right) =
      TLWE.add (externalProduct digits left) (externalProduct digits right) := by
  rw [TLWE.Ciphertext.mk.injEq]
  constructor
  · funext coordinate
    simp [externalProduct, TLWE.linearCombination, add, TLWE.batchOfRows,
      TLWE.entry, TLWE.add, mul_add, Finset.sum_add_distrib]
  · simp [externalProduct, TLWE.linearCombination, add, TLWE.batchOfRows,
      TLWE.entry, TLWE.add, mul_add, Finset.sum_add_distrib]

/-- Adding a message-one gadget to a homogeneous TGSW ciphertext separates into the pure
gadget matrix and the homogeneous ciphertext. -/
theorem addGadget_one_eq_add_pure
    {R : Type} [CommSemiring R] {dimension levels : ℕ}
    (gadget : Fin levels → R)
    (homogeneous : Ciphertext R dimension levels) :
    addGadget gadget 1 homogeneous =
      add (addGadget gadget 1 0) homogeneous := by
  apply Prod.ext
  · funext coordinate row
    simp [addGadget, add, TLWE.batchOfRows, TLWE.add, TLWE.entry,
      Matrix.add_apply, add_comm]
  · funext row
    simp [addGadget, add, TLWE.batchOfRows, TLWE.add, TLWE.entry, add_comm]

/-- Exact digit decomposition makes the external product by a pure message-one gadget matrix
reconstruct the complete input TLWE ciphertext, including its public mask. -/
theorem externalProduct_pureGadget_one
    {R : Type} [CommRing R] {dimension levels : ℕ}
    (gadget : Fin levels → R)
    (input : TLWE.Ciphertext R dimension)
    (digits : Fin (dimension + 1) → Fin levels → R)
    (hDecomposes : Gadget.Decomposes gadget input digits) :
    externalProduct digits (addGadget gadget 1 0) = input := by
  classical
  rcases input with ⟨inputMask, inputBody⟩
  rw [TLWE.Ciphertext.mk.injEq]
  constructor
  · funext coordinate
    have hentry (index : Fin (dimension + 1) × Fin levels) :
        (TLWE.entry (addGadget gadget 1 0) (finProdFinEquiv index)).mask coordinate =
          if index.1.val = coordinate.val then gadget index.2 else 0 := by
      simp [TLWE.entry, addGadget, gadgetMaskShift, rowIndex]
    simp only [externalProduct, TLWE.linearCombination]
    rw [Fintype.sum_prod_type]
    simp_rw [hentry]
    rw [Finset.sum_eq_single (Fin.castSucc coordinate)]
    · simpa [Gadget.recompose, Gadget.extendedCiphertext] using
        hDecomposes (Fin.castSucc coordinate)
    · intro block _ hblock
      have hne : block.val ≠ coordinate.val := by
        intro hval
        exact hblock (Fin.ext hval)
      simp [hne]
    · simp
  · have hentry (index : Fin (dimension + 1) × Fin levels) :
        (TLWE.entry (addGadget gadget 1 0) (finProdFinEquiv index)).body =
          if index.1.val = dimension then gadget index.2 else 0 := by
      simp [TLWE.entry, addGadget, gadgetBodyShift, rowIndex]
    simp only [externalProduct, TLWE.linearCombination]
    rw [Fintype.sum_prod_type]
    simp_rw [hentry]
    rw [Finset.sum_eq_single (Fin.last dimension)]
    · simpa [Gadget.recompose, Gadget.extendedCiphertext] using
        hDecomposes (Fin.last dimension)
    · intro block _ hblock
      have hne : block.val ≠ dimension := by
        intro hval
        apply hblock
        apply Fin.ext
        simpa using hval
      simp [hne]
    · simp

/-- A message-one gadget control acts as the identity, while its homogeneous part contributes
one explicit external-product perturbation. -/
theorem externalProduct_addGadget_one
    {R : Type} [CommRing R] {dimension levels : ℕ}
    (gadget : Fin levels → R)
    (input : TLWE.Ciphertext R dimension)
    (digits : Fin (dimension + 1) → Fin levels → R)
    (homogeneous : Ciphertext R dimension levels)
    (hDecomposes : Gadget.Decomposes gadget input digits) :
    externalProduct digits (addGadget gadget 1 homogeneous) =
      TLWE.add input (externalProduct digits homogeneous) := by
  rw [addGadget_one_eq_add_pure, externalProduct_add,
    externalProduct_pureGadget_one gadget input digits hDecomposes]

/-- Rowwise, a message-one gadget control returns the data ciphertext plus exactly the internal
product with the control's homogeneous part. -/
theorem internalProductWithDigits_addGadget_one
    {R : Type} [CommRing R] {dimension levels : ℕ}
    (gadget : Fin levels → R)
    (data homogeneous : Ciphertext R dimension levels)
    (digits : Fin (rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (hDecomposes : ∀ row,
      Gadget.Decomposes gadget (TLWE.entry data row) (digits row)) :
    internalProductWithDigits digits (addGadget gadget 1 homogeneous) =
      add data (internalProductWithDigits digits homogeneous) := by
  apply Prod.ext
  · funext coordinate row
    change (externalProduct (digits row) (addGadget gadget 1 homogeneous)).mask
        coordinate =
      (TLWE.add (TLWE.entry data row)
        (externalProduct (digits row) homogeneous)).mask coordinate
    rw [externalProduct_addGadget_one gadget (TLWE.entry data row)
      (digits row) homogeneous (hDecomposes row)]
  · funext row
    change (externalProduct (digits row) (addGadget gadget 1 homogeneous)).body =
      (TLWE.add (TLWE.entry data row)
        (externalProduct (digits row) homogeneous)).body
    rw [externalProduct_addGadget_one gadget (TLWE.entry data row)
      (digits row) homogeneous (hDecomposes row)]

/-- Multiplying a gadget phase by a public scalar multiplies its encoded message. -/
theorem mul_gadgetPhase {R : Type} [CommRing R] {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R)
    (left right : R) (row : Fin (rowCount dimension levels)) :
    left * gadgetPhase secret gadget right row =
      gadgetPhase secret gadget (left * right) row := by
  obtain ⟨⟨block, level⟩, rfl⟩ := finProdFinEquiv.surjective row
  cases block using Fin.lastCases <;>
    simp only [gadgetPhase_last, gadgetPhase_castSucc] <;> ring

/-- Gadget phases are additive in their encoded message. -/
theorem gadgetPhase_add {R : Type} [CommRing R] {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R)
    (left right : R) (row : Fin (rowCount dimension levels)) :
    gadgetPhase secret gadget left row + gadgetPhase secret gadget right row =
      gadgetPhase secret gadget (left + right) row := by
  obtain ⟨⟨block, level⟩, rfl⟩ := finProdFinEquiv.surjective row
  cases block using Fin.lastCases <;>
    simp only [gadgetPhase_last, gadgetPhase_castSucc] <;> ring

/-- Gadget phases commute with subtraction of their encoded messages. -/
theorem gadgetPhase_sub {R : Type} [CommRing R] {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R)
    (left right : R) (row : Fin (rowCount dimension levels)) :
    gadgetPhase secret gadget left row - gadgetPhase secret gadget right row =
      gadgetPhase secret gadget (left - right) row := by
  obtain ⟨⟨block, level⟩, rfl⟩ := finProdFinEquiv.surjective row
  cases block using Fin.lastCases <;>
    simp only [gadgetPhase_last, gadgetPhase_castSucc] <;> ring

/-- Subtracting two TGSW ciphertexts subtracts their row errors exactly. -/
theorem rowError_sub {R : Type} [CommRing R] {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R)
    (leftMessage rightMessage : R)
    (left right : Ciphertext R dimension levels)
    (index : Fin (dimension + 1) × Fin levels) :
    rowError secret gadget (leftMessage - rightMessage) (sub left right) index =
      rowError secret gadget leftMessage left index -
        rowError secret gadget rightMessage right index := by
  unfold rowError
  rw [entry_sub, TLWE.phase_sub, ← gadgetPhase_sub]
  ring

/-- Complete row residual for an internal product with explicit decomposition residuals. -/
def internalProductRowResidual {R : Type} [Ring R] {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R)
    (controlMessage dataMessage : R)
    (data : Ciphertext R dimension levels)
    (decompositionResidual : Fin (rowCount dimension levels) →
      TLWE.Ciphertext R dimension)
    (digits : Fin (rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (control : Ciphertext R dimension levels)
    (index : Fin (dimension + 1) × Fin levels) : R :=
  controlMessage * rowError secret gadget dataMessage data index +
    controlMessage *
      TLWE.phase secret (decompositionResidual (finProdFinEquiv index)) +
    externalProductError secret gadget controlMessage
      (digits (finProdFinEquiv index)) control

/-- **Exact TGSW internal-product row identity.**  Under an explicit approximate decomposition
contract for every data row, the output encodes the product message plus the three named residual
terms in `internalProductRowResidual`. -/
theorem phase_entry_internalProductWithDigits_eq_gadgetPhase_add_residual
    {R : Type} [CommRing R] {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R)
    (controlMessage dataMessage : R)
    (data : Ciphertext R dimension levels)
    (decompositionResidual : Fin (rowCount dimension levels) →
      TLWE.Ciphertext R dimension)
    (digits : Fin (rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (control : Ciphertext R dimension levels)
    (hDecomposes : ∀ row, Gadget.DecomposesWithError gadget
      (TLWE.entry data row) (decompositionResidual row) (digits row))
    (index : Fin (dimension + 1) × Fin levels) :
    TLWE.phase secret
        (TLWE.entry (internalProductWithDigits digits control) (finProdFinEquiv index)) =
      gadgetPhase secret gadget (controlMessage * dataMessage) (finProdFinEquiv index) +
        internalProductRowResidual secret gadget controlMessage dataMessage data
          decompositionResidual digits control index := by
  rw [entry_internalProductWithDigits]
  rw [phase_externalProduct_eq_mul_add_decompositionError_add_rowError
    secret gadget controlMessage
    (TLWE.entry data (finProdFinEquiv index))
    (decompositionResidual (finProdFinEquiv index))
    (digits (finProdFinEquiv index)) control
    (hDecomposes (finProdFinEquiv index))]
  have hDataPhase :
      TLWE.phase secret (TLWE.entry data (finProdFinEquiv index)) =
        gadgetPhase secret gadget dataMessage (finProdFinEquiv index) +
          rowError secret gadget dataMessage data index := by
    unfold rowError
    ring
  rw [hDataPhase, mul_add, mul_gadgetPhase]
  unfold internalProductRowResidual
  ring

/-- Row residual obtained when the supplied digits define their own decomposition residual. -/
def computedInternalProductRowResidual {R : Type} [Ring R]
    {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R)
    (controlMessage dataMessage : R)
    (data : Ciphertext R dimension levels)
    (digits : Fin (rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (control : Ciphertext R dimension levels)
    (index : Fin (dimension + 1) × Fin levels) : R :=
  internalProductRowResidual secret gadget controlMessage dataMessage data
    (fun row ↦ Gadget.decompositionError gadget (TLWE.entry data row) (digits row))
    digits control index

/-- Unconditional internal-product normal form using the decomposition residual computed from
the supplied row digits.  An executable digitizer can therefore instantiate this theorem without
an additional algebraic proof obligation. -/
theorem phase_entry_internalProductWithDigits_eq_gadgetPhase_add_computedResidual
    {R : Type} [CommRing R] {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R)
    (controlMessage dataMessage : R)
    (data : Ciphertext R dimension levels)
    (digits : Fin (rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (control : Ciphertext R dimension levels)
    (index : Fin (dimension + 1) × Fin levels) :
    TLWE.phase secret
        (TLWE.entry (internalProductWithDigits digits control) (finProdFinEquiv index)) =
      gadgetPhase secret gadget (controlMessage * dataMessage) (finProdFinEquiv index) +
        computedInternalProductRowResidual secret gadget controlMessage dataMessage
          data digits control index := by
  exact phase_entry_internalProductWithDigits_eq_gadgetPhase_add_residual
    secret gadget controlMessage dataMessage data
    (fun row ↦ Gadget.decompositionError gadget (TLWE.entry data row) (digits row))
    digits control
    (fun row ↦ Gadget.decomposesWithError_decompositionError
      gadget (TLWE.entry data row) (digits row))
    index

/-- The message selected by a CMux with an arbitrary ring-valued control.  For a control bit this
is `falseMessage` at zero and `trueMessage` at one. -/
def cmuxMessage {R : Type} [Ring R]
    (controlMessage trueMessage falseMessage : R) : R :=
  falseMessage + controlMessage * (trueMessage - falseMessage)

@[simp]
theorem cmuxMessage_zero {R : Type} [Ring R] (trueMessage falseMessage : R) :
    cmuxMessage 0 trueMessage falseMessage = falseMessage := by
  simp [cmuxMessage]

@[simp]
theorem cmuxMessage_one {R : Type} [Ring R] (trueMessage falseMessage : R) :
    cmuxMessage 1 trueMessage falseMessage = trueMessage := by
  simp [cmuxMessage]

/-- Native TGSW CMux with supplied digits for every row of `ifTrue - ifFalse`.

It computes `ifFalse + control * (ifTrue - ifFalse)` row by row. -/
def cmuxWithDigits {R : Type} [CommRing R] {dimension levels : ℕ}
    (digits : Fin (rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (control _ifTrue ifFalse : Ciphertext R dimension levels) :
    Ciphertext R dimension levels :=
  add ifFalse (internalProductWithDigits digits control)

/-- A message-zero gadget control selects the false ciphertext, plus exactly the internal-product
perturbation contributed by the control's homogeneous part.  This is an equality of complete
ciphertexts, not only of their phases. -/
theorem cmuxWithDigits_addGadget_zero
    {R : Type} [CommRing R] {dimension levels : ℕ}
    (gadget : Fin levels → R)
    (homogeneous ifTrue ifFalse : Ciphertext R dimension levels)
    (digits : Fin (rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R) :
    cmuxWithDigits digits (addGadget gadget 0 homogeneous) ifTrue ifFalse =
      add ifFalse (internalProductWithDigits digits homogeneous) := by
  simp [cmuxWithDigits]

/-- Under exact decomposition of `ifTrue - ifFalse`, a message-one gadget control selects the
true ciphertext, plus exactly the internal-product perturbation contributed by the control's
homogeneous part.  This is an equality of complete ciphertexts. -/
theorem cmuxWithDigits_addGadget_one
    {R : Type} [CommRing R] {dimension levels : ℕ}
    (gadget : Fin levels → R)
    (homogeneous ifTrue ifFalse : Ciphertext R dimension levels)
    (digits : Fin (rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (hDecomposes : ∀ row,
      Gadget.Decomposes gadget (TLWE.entry (sub ifTrue ifFalse) row) (digits row)) :
    cmuxWithDigits digits (addGadget gadget 1 homogeneous) ifTrue ifFalse =
      add ifTrue (internalProductWithDigits digits homogeneous) := by
  unfold cmuxWithDigits
  rw [internalProductWithDigits_addGadget_one gadget (sub ifTrue ifFalse)
    homogeneous digits hDecomposes]
  apply Prod.ext
  · funext coordinate row
    simp [add, sub, TLWE.batchOfRows, TLWE.add, TLWE.sub, TLWE.entry]
    ring
  · funext row
    simp [add, sub, TLWE.batchOfRows, TLWE.add, TLWE.sub, TLWE.entry]
    ring

/-- Complete row residual of native CMux with explicit residuals for decomposing
`ifTrue - ifFalse`. -/
def cmuxRowResidual {R : Type} [CommRing R] {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R)
    (controlMessage trueMessage falseMessage : R)
    (control ifTrue ifFalse : Ciphertext R dimension levels)
    (decompositionResidual : Fin (rowCount dimension levels) →
      TLWE.Ciphertext R dimension)
    (digits : Fin (rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (index : Fin (dimension + 1) × Fin levels) : R :=
  rowError secret gadget falseMessage ifFalse index +
    internalProductRowResidual secret gadget controlMessage
      (trueMessage - falseMessage) (sub ifTrue ifFalse)
      decompositionResidual digits control index

/-- **Exact native CMux row identity.**  The output carries `cmuxMessage` plus the false-branch
row error and the complete internal-product residual. -/
theorem phase_entry_cmuxWithDigits_eq_gadgetPhase_add_residual
    {R : Type} [CommRing R] {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R)
    (controlMessage trueMessage falseMessage : R)
    (control ifTrue ifFalse : Ciphertext R dimension levels)
    (decompositionResidual : Fin (rowCount dimension levels) →
      TLWE.Ciphertext R dimension)
    (digits : Fin (rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (hDecomposes : ∀ row, Gadget.DecomposesWithError gadget
      (TLWE.entry (sub ifTrue ifFalse) row)
      (decompositionResidual row) (digits row))
    (index : Fin (dimension + 1) × Fin levels) :
    TLWE.phase secret
        (TLWE.entry (cmuxWithDigits digits control ifTrue ifFalse)
          (finProdFinEquiv index)) =
      gadgetPhase secret gadget
          (cmuxMessage controlMessage trueMessage falseMessage)
          (finProdFinEquiv index) +
        cmuxRowResidual secret gadget controlMessage trueMessage falseMessage
          control ifTrue ifFalse decompositionResidual digits index := by
  rw [show TLWE.entry (cmuxWithDigits digits control ifTrue ifFalse)
      (finProdFinEquiv index) =
      TLWE.add (TLWE.entry ifFalse (finProdFinEquiv index))
        (TLWE.entry (internalProductWithDigits digits control)
          (finProdFinEquiv index)) by rfl]
  rw [TLWE.phase_add]
  rw [phase_entry_internalProductWithDigits_eq_gadgetPhase_add_residual
    secret gadget controlMessage (trueMessage - falseMessage)
    (sub ifTrue ifFalse) decompositionResidual digits control hDecomposes index]
  have hFalsePhase :
      TLWE.phase secret (TLWE.entry ifFalse (finProdFinEquiv index)) =
        gadgetPhase secret gadget falseMessage (finProdFinEquiv index) +
          rowError secret gadget falseMessage ifFalse index := by
    unfold rowError
    ring
  rw [hFalsePhase]
  unfold cmuxMessage cmuxRowResidual
  rw [← gadgetPhase_add]
  ring

/-- CMux residual using the decomposition residual computed from each supplied digit vector. -/
def computedCmuxRowResidual {R : Type} [CommRing R] {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R)
    (controlMessage trueMessage falseMessage : R)
    (control ifTrue ifFalse : Ciphertext R dimension levels)
    (digits : Fin (rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (index : Fin (dimension + 1) × Fin levels) : R :=
  cmuxRowResidual secret gadget controlMessage trueMessage falseMessage
    control ifTrue ifFalse
    (fun row ↦ Gadget.decompositionError gadget
      (TLWE.entry (sub ifTrue ifFalse) row) (digits row))
    digits index

/-- With a zero control message, every data-row and decomposition term vanishes.  The complete
computed CMux residual is exactly the retained false-branch row error plus the weighted
zero-control row error. -/
theorem computedCmuxRowResidual_zero
    {R : Type} [CommRing R] {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R)
    (trueMessage falseMessage : R)
    (control ifTrue ifFalse : Ciphertext R dimension levels)
    (digits : Fin (rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (index : Fin (dimension + 1) × Fin levels) :
    computedCmuxRowResidual secret gadget 0 trueMessage falseMessage
        control ifTrue ifFalse digits index =
      rowError secret gadget falseMessage ifFalse index +
        externalProductError secret gadget 0
          (digits (finProdFinEquiv index)) control := by
  simp [computedCmuxRowResidual, cmuxRowResidual, internalProductRowResidual]

/-- Unconditional native CMux normal form for caller-supplied row digits. -/
theorem phase_entry_cmuxWithDigits_eq_gadgetPhase_add_computedResidual
    {R : Type} [CommRing R] {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R)
    (controlMessage trueMessage falseMessage : R)
    (control ifTrue ifFalse : Ciphertext R dimension levels)
    (digits : Fin (rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (index : Fin (dimension + 1) × Fin levels) :
    TLWE.phase secret
        (TLWE.entry (cmuxWithDigits digits control ifTrue ifFalse)
          (finProdFinEquiv index)) =
      gadgetPhase secret gadget
          (cmuxMessage controlMessage trueMessage falseMessage)
          (finProdFinEquiv index) +
        computedCmuxRowResidual secret gadget controlMessage trueMessage falseMessage
          control ifTrue ifFalse digits index := by
  exact phase_entry_cmuxWithDigits_eq_gadgetPhase_add_residual
    secret gadget controlMessage trueMessage falseMessage control ifTrue ifFalse
    (fun row ↦ Gadget.decompositionError gadget
      (TLWE.entry (sub ifTrue ifFalse) row) (digits row))
    digits
    (fun row ↦ Gadget.decomposesWithError_decompositionError gadget
      (TLWE.entry (sub ifTrue ifFalse) row) (digits row))
    index

end TGSW

end FormalProof4FHE.TFHE
