/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.Evaluation
import FormalProof4FHE.TFHE.MonomialKDM
import FormalProof4FHE.TFHE.BlindRotation
import FormalProof4FHE.TFHE.CoefficientStructuredLWE

set_option autoImplicit false

/-!
# The Complete Native BRK Spans Its Quadratic Monomials

One native TGSW encryption of one secret message exposes only the rank-one family obtained by
multiplying that message into each encryption-key component.  A complete self bootstrapping key,
however, contains one such TGSW ciphertext for every secret-message coordinate.  This file makes
the distinction precise.

At a fixed gadget level, a public linear combination of the mask-block rows has phase equal to an
arbitrary weighted bilinear form in the message vector and encryption key, plus the corresponding
explicit linear combination of row errors.  When the message vector is the encryption key, this
is an arbitrary quadratic form.  For the native ring key, coefficient extraction shows that the
complete target-message table contains every Boolean coefficient product.

These are deterministic algebraic statements.  They do not assert that general adaptive
degree-two KDM security follows from the native fixed-table game, and they do not reduce the
native circular game to ordinary LWE/RLWE.  They identify exactly why a single nonce translation
is rank one while the joint full-BRK object carries the complete outer-product table.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.TFHE.TGSW.MonomialKDM.FullTable

/-- The weighted bilinear form represented by a complete table of message-by-secret products. -/
def crossBilinearForm {R : Type} [CommRing R]
    {messageCount dimension : ℕ}
    (weight : Fin messageCount → Fin dimension → R)
    (secret : Fin dimension → R) (message : Fin messageCount → R) : R :=
  ∑ messageCoordinate, ∑ secretCoordinate,
    weight messageCoordinate secretCoordinate *
      (secret secretCoordinate * message messageCoordinate)

/-- Select all mask-block rows at one gadget level and combine them publicly. -/
def maskRowCombination {R : Type} [Semiring R]
    {messageCount dimension levels : ℕ}
    (weight : Fin messageCount → Fin dimension → R)
    (level : Fin levels)
    (ciphertexts : Fin messageCount → Ciphertext R dimension levels) :
    TLWE.Ciphertext R dimension :=
  TLWE.linearCombination
    (fun index : Fin messageCount × Fin dimension ↦ weight index.1 index.2)
    (fun index ↦ TLWE.entry (ciphertexts index.1)
      (finProdFinEquiv (Fin.castSucc index.2, level)))

/-- The error accumulated by the same public mask-row combination. -/
def maskRowErrorCombination {R : Type} [CommRing R]
    {messageCount dimension levels : ℕ}
    (weight : Fin messageCount → Fin dimension → R)
    (secret : Fin dimension → R) (gadget : Fin levels → R)
    (message : Fin messageCount → R) (level : Fin levels)
    (ciphertexts : Fin messageCount → Ciphertext R dimension levels) : R :=
  ∑ messageCoordinate, ∑ secretCoordinate,
    weight messageCoordinate secretCoordinate *
      rowError secret gadget (message messageCoordinate)
        (ciphertexts messageCoordinate) (Fin.castSucc secretCoordinate, level)

/-- The weighted ideal phases of all selected mask rows are exactly the negative gadget-scaled
bilinear form. -/
theorem sum_weight_mul_mask_gadgetPhase_eq
    {R : Type} [CommRing R] {messageCount dimension levels : ℕ}
    (weight : Fin messageCount → Fin dimension → R)
    (secret : Fin dimension → R) (gadget : Fin levels → R)
    (message : Fin messageCount → R) (level : Fin levels) :
    (∑ messageCoordinate, ∑ secretCoordinate,
      weight messageCoordinate secretCoordinate *
        gadgetPhase secret gadget (message messageCoordinate)
          (finProdFinEquiv (Fin.castSucc secretCoordinate, level))) =
      -(crossBilinearForm weight secret message * gadget level) := by
  classical
  simp_rw [gadgetPhase_castSucc]
  unfold crossBilinearForm
  calc
    (∑ messageCoordinate, ∑ secretCoordinate,
        weight messageCoordinate secretCoordinate *
          -(secret secretCoordinate * (message messageCoordinate * gadget level))) =
      ∑ messageCoordinate, ∑ secretCoordinate,
        -((weight messageCoordinate secretCoordinate *
          (secret secretCoordinate * message messageCoordinate)) * gadget level) := by
        apply Finset.sum_congr rfl
        intro messageCoordinate _
        apply Finset.sum_congr rfl
        intro secretCoordinate _
        ring
    _ = -(∑ messageCoordinate, ∑ secretCoordinate,
        (weight messageCoordinate secretCoordinate *
          (secret secretCoordinate * message messageCoordinate)) * gadget level) := by
      simp only [Finset.sum_neg_distrib]
    _ = -((∑ messageCoordinate, ∑ secretCoordinate,
        weight messageCoordinate secretCoordinate *
          (secret secretCoordinate * message messageCoordinate)) * gadget level) := by
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro messageCoordinate _
      rw [Finset.sum_mul]

/-- Exact phase of a public linear combination of the complete mask-row table. -/
theorem phase_maskRowCombination_eq
    {R : Type} [CommRing R] {messageCount dimension levels : ℕ}
    (weight : Fin messageCount → Fin dimension → R)
    (secret : Fin dimension → R) (gadget : Fin levels → R)
    (message : Fin messageCount → R) (level : Fin levels)
    (ciphertexts : Fin messageCount → Ciphertext R dimension levels) :
    TLWE.phase secret (maskRowCombination weight level ciphertexts) =
      -(crossBilinearForm weight secret message * gadget level) +
        maskRowErrorCombination weight secret gadget message level ciphertexts := by
  classical
  unfold maskRowCombination
  rw [TLWE.phase_linearCombination]
  rw [Fintype.sum_prod_type]
  calc
    (∑ messageCoordinate, ∑ secretCoordinate,
        weight messageCoordinate secretCoordinate *
          TLWE.phase secret
            (TLWE.entry (ciphertexts messageCoordinate)
              (finProdFinEquiv (Fin.castSucc secretCoordinate, level)))) =
      (∑ messageCoordinate, ∑ secretCoordinate,
        weight messageCoordinate secretCoordinate *
          (gadgetPhase secret gadget (message messageCoordinate)
              (finProdFinEquiv (Fin.castSucc secretCoordinate, level)) +
            rowError secret gadget (message messageCoordinate)
              (ciphertexts messageCoordinate) (Fin.castSucc secretCoordinate, level))) := by
        apply Finset.sum_congr rfl
        intro messageCoordinate _
        apply Finset.sum_congr rfl
        intro secretCoordinate _
        congr 1
        simp only [rowError]
        ring
    _ = (∑ messageCoordinate, ∑ secretCoordinate,
          weight messageCoordinate secretCoordinate *
            gadgetPhase secret gadget (message messageCoordinate)
              (finProdFinEquiv (Fin.castSucc secretCoordinate, level))) +
        maskRowErrorCombination weight secret gadget message level ciphertexts := by
      simp only [maskRowErrorCombination]
      simp_rw [mul_add, Finset.sum_add_distrib]
    _ = _ := by
      rw [sum_weight_mul_mask_gadgetPhase_eq]

/-- The quadratic form obtained when the complete message vector is the encryption key itself. -/
def selfQuadraticForm {R : Type} [CommRing R] {dimension : ℕ}
    (weight : Fin dimension → Fin dimension → R)
    (secret : Fin dimension → R) : R :=
  crossBilinearForm weight secret secret

@[simp]
theorem selfQuadraticForm_eq_sum {R : Type} [CommRing R] {dimension : ℕ}
    (weight : Fin dimension → Fin dimension → R)
    (secret : Fin dimension → R) :
    selfQuadraticForm weight secret =
      ∑ first, ∑ second,
        weight first second * (secret second * secret first) :=
  rfl

/-- A complete self-BRK therefore linearly exposes every weighted quadratic form, with the exact
combined row error shown explicitly. -/
theorem phase_selfMaskRowCombination_eq
    {R : Type} [CommRing R] {dimension levels : ℕ}
    (weight : Fin dimension → Fin dimension → R)
    (secret : Fin dimension → R) (gadget : Fin levels → R)
    (level : Fin levels)
    (ciphertexts : Fin dimension → Ciphertext R dimension levels) :
    TLWE.phase secret (maskRowCombination weight level ciphertexts) =
      -(selfQuadraticForm weight secret * gadget level) +
        maskRowErrorCombination weight secret gadget secret level ciphertexts := by
  exact phase_maskRowCombination_eq weight secret gadget secret level ciphertexts

/-! ## Boolean diagonal/off-diagonal decomposition -/

/-- The diagonal part of a weighted quadratic form on a binary secret.  Boolean idempotence
turns this part into an ordinary linear form. -/
def diagonalLinearForm {R : Type} [CommRing R] {dimension : ℕ}
    (weight : Fin dimension → Fin dimension → R)
    (secret : BinarySecret dimension) : R :=
  ∑ coordinate, weight coordinate coordinate * embedBit (secret coordinate)

/-- The genuinely nonlinear part of a weighted quadratic form on a binary secret.  It contains
only products of two distinct secret coordinates. -/
def offDiagonalQuadraticForm {R : Type} [CommRing R] {dimension : ℕ}
    (weight : Fin dimension → Fin dimension → R)
    (secret : BinarySecret dimension) : R :=
  ∑ first, ∑ second ∈ Finset.univ.erase first,
    weight first second *
      (embedBit (secret second) * embedBit (secret first))

/-- **Exact Boolean quadratic decomposition.**  A complete self-BRK does not require arbitrary
degree-two behavior: its diagonal products collapse to an affine term, and the entire remaining
non-affine obligation is the fixed table of square-free off-diagonal products. -/
theorem selfQuadraticForm_embedBinarySecret_eq_diagonal_add_offDiagonal
    {R : Type} [CommRing R] {dimension : ℕ}
    (weight : Fin dimension → Fin dimension → R)
    (secret : BinarySecret dimension) :
    selfQuadraticForm weight (embedBinarySecret secret) =
      diagonalLinearForm weight secret + offDiagonalQuadraticForm weight secret := by
  classical
  unfold selfQuadraticForm crossBilinearForm diagonalLinearForm offDiagonalQuadraticForm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro first _
  rw [← Finset.add_sum_erase Finset.univ
    (fun second ↦ weight first second *
      (embedBinarySecret secret second * embedBinarySecret secret first))
    (Finset.mem_univ first)]
  by_cases hbit : secret first = true
  · simp [embedBinarySecret, embedBit, hbit]
  · have hfalse : secret first = false := Bool.eq_false_of_not_eq_true hbit
    simp [embedBinarySecret, embedBit, hfalse]

/-- The same decomposition at the level of the publicly obtainable full-BRK phase.  The first
summand is affine circular information; only `offDiagonalQuadraticForm` needs a genuinely
degree-two security argument. -/
theorem phase_selfMaskRowCombination_embedBinarySecret_eq
    {R : Type} [CommRing R] {dimension levels : ℕ}
    (weight : Fin dimension → Fin dimension → R)
    (secret : BinarySecret dimension) (gadget : Fin levels → R)
    (level : Fin levels)
    (ciphertexts : Fin dimension → Ciphertext R dimension levels) :
    TLWE.phase (embedBinarySecret secret)
        (maskRowCombination weight level ciphertexts) =
      -((diagonalLinearForm weight secret + offDiagonalQuadraticForm weight secret) *
          gadget level) +
        maskRowErrorCombination weight (embedBinarySecret secret) gadget
          (embedBinarySecret secret) level ciphertexts := by
  rw [phase_selfMaskRowCombination_eq,
    selfQuadraticForm_embedBinarySecret_eq_diagonal_add_offDiagonal]

/-- With a one-coordinate binary key there are no off-diagonal monomials, so the complete
quadratic form is exactly affine.  This algebraic collapse does not by itself provide a secure
TFHE parameter family: a one-bit LWE secret has only constant entropy. -/
theorem selfQuadraticForm_fin_one_eq_affine
    {R : Type} [CommRing R]
    (weight : Fin 1 → Fin 1 → R)
    (secret : BinarySecret 1) :
    selfQuadraticForm weight (embedBinarySecret secret) =
      weight 0 0 * embedBit (secret 0) := by
  rw [selfQuadraticForm_embedBinarySecret_eq_diagonal_add_offDiagonal]
  simp [diagonalLinearForm, offDiagonalQuadraticForm]

end FormalProof4FHE.TFHE.TGSW.MonomialKDM.FullTable

namespace FormalProof4FHE.TFHE.Native.FullBRKQuadraticSpan

open TGSW

noncomputable section

/-- One entry of the actual ring-valued outer-product table in a target-message self BRK. -/
def extractedOuterProduct
    (q degree ringRank : ℕ)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (messageCoordinate : Fin (ringRank * (degree + 1)))
    (maskComponent : Fin ringRank) : RLWE.Rq q (degree + 1) :=
  embedRingSecret q ringSecret maskComponent *
    embedConstantBit q (degree + 1) (keyExtract ringSecret messageCoordinate)

/-- The abstract cross-monomial coordinate is definitionally the native extracted-key outer
product. -/
@[simp]
theorem crossMonomial_eq_extractedOuterProduct
    (q degree ringRank : ℕ)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (messageCoordinate : Fin (ringRank * (degree + 1)))
    (maskComponent : Fin ringRank) :
    TGSW.MonomialKDM.crossMonomial (embedRingSecret q ringSecret)
        (embedConstantBit q (degree + 1)
          (keyExtract ringSecret messageCoordinate)) maskComponent =
      extractedOuterProduct q degree ringRank ringSecret messageCoordinate maskComponent :=
  rfl

/-- Reading a coefficient of a native outer-product entry gives exactly the product of the two
corresponding Boolean key coefficients. -/
@[simp]
theorem extractedOuterProduct_coefficient
    (q degree ringRank : ℕ) [NeZero q]
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (messageComponent maskComponent : Fin ringRank)
    (messageCoefficient maskCoefficient : Fin (degree + 1)) :
    LatticeCrypto.Poly.toPi
        (extractedOuterProduct q degree ringRank ringSecret
          (finProdFinEquiv (messageComponent, messageCoefficient)) maskComponent)
        maskCoefficient =
      (embedBit (ringSecret maskComponent maskCoefficient) : ZMod q) *
        embedBit (ringSecret messageComponent messageCoefficient) := by
  rw [extractedOuterProduct, keyExtract_apply,
    BlindRotation.embedConstantBit_eq_embedBit]
  cases hmessage : ringSecret messageComponent messageCoefficient <;>
    simp [embedBit, embedRingSecret, embedBinaryPolynomial]

/-- On the coefficient-table diagonal, the apparent quadratic product is exactly the original
Boolean secret coefficient. -/
@[simp]
theorem extractedOuterProduct_diagonal_coefficient
    (q degree ringRank : ℕ) [NeZero q]
    (ringSecret : RingBinarySecret ringRank (degree + 1))
  (component : Fin ringRank) (coefficient : Fin (degree + 1)) :
    LatticeCrypto.Poly.toPi
        (extractedOuterProduct q degree ringRank ringSecret
          (finProdFinEquiv (component, coefficient)) component)
        coefficient =
      (embedBit (ringSecret component coefficient) : ZMod q) := by
  rw [extractedOuterProduct_coefficient]
  cases ringSecret component coefficient <;> simp [embedBit]

/-! ## Native ring-valued diagonal/square-free split -/

/-- The unique coefficient of one native outer-product entry that is a Boolean square.  Every
other coefficient is zero. -/
def extractedDiagonalPart
    (q degree ringRank : ℕ)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (messageComponent : Fin ringRank)
    (messageCoefficient : Fin (degree + 1))
    (maskComponent : Fin ringRank) : RLWE.Rq q (degree + 1) :=
  LatticeCrypto.Poly.ofPi fun maskCoefficient ↦
    if maskComponent = messageComponent ∧ maskCoefficient = messageCoefficient then
      (embedBit (ringSecret messageComponent messageCoefficient) : ZMod q)
    else 0

/-- Coefficient description of the native diagonal polynomial. -/
@[simp]
theorem extractedDiagonalPart_coefficient
    (q degree ringRank : ℕ)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (messageComponent : Fin ringRank)
    (messageCoefficient : Fin (degree + 1))
    (maskComponent : Fin ringRank) (maskCoefficient : Fin (degree + 1)) :
    LatticeCrypto.Poly.toPi
        (extractedDiagonalPart q degree ringRank ringSecret messageComponent
          messageCoefficient maskComponent) maskCoefficient =
      if maskComponent = messageComponent ∧ maskCoefficient = messageCoefficient then
        (embedBit (ringSecret messageComponent messageCoefficient) : ZMod q)
      else 0 := by
  simp [extractedDiagonalPart]

/-- Remove the unique Boolean-square coefficient from one native ring-valued outer-product
entry.  The result contains only products of distinct complete key coordinates. -/
def extractedSquareFreePart
    (q degree ringRank : ℕ)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (messageComponent : Fin ringRank)
    (messageCoefficient : Fin (degree + 1))
    (maskComponent : Fin ringRank) : RLWE.Rq q (degree + 1) :=
  extractedOuterProduct q degree ringRank ringSecret
      (finProdFinEquiv (messageComponent, messageCoefficient)) maskComponent -
    extractedDiagonalPart q degree ringRank ringSecret messageComponent
      messageCoefficient maskComponent

/-- Exact native ring decomposition into its affine Boolean diagonal and square-free remainder. -/
theorem extractedOuterProduct_eq_diagonal_add_squareFree
    (q degree ringRank : ℕ)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (messageComponent : Fin ringRank)
    (messageCoefficient : Fin (degree + 1))
    (maskComponent : Fin ringRank) :
    extractedOuterProduct q degree ringRank ringSecret
        (finProdFinEquiv (messageComponent, messageCoefficient)) maskComponent =
      extractedDiagonalPart q degree ringRank ringSecret messageComponent
          messageCoefficient maskComponent +
        extractedSquareFreePart q degree ringRank ringSecret messageComponent
          messageCoefficient maskComponent := by
  unfold extractedSquareFreePart
  abel

/-- The square-free remainder is zero at its sole would-be diagonal coefficient. -/
@[simp]
theorem extractedSquareFreePart_diagonal_coefficient
    (q degree ringRank : ℕ) [NeZero q]
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (component : Fin ringRank) (coefficient : Fin (degree + 1)) :
    LatticeCrypto.Poly.toPi
        (extractedSquareFreePart q degree ringRank ringSecret component coefficient component)
        coefficient = 0 := by
  rw [extractedSquareFreePart]
  change (Native.CoefficientStructuredLWE.coefficientAddEquiv q (degree + 1)
      (extractedOuterProduct q degree ringRank ringSecret
          (finProdFinEquiv (component, coefficient)) component -
        extractedDiagonalPart q degree ringRank ringSecret component coefficient component))
      coefficient = 0
  have hsub := congrArg (fun value ↦ value coefficient)
    ((Native.CoefficientStructuredLWE.coefficientAddEquiv q (degree + 1)).map_sub
      (extractedOuterProduct q degree ringRank ringSecret
        (finProdFinEquiv (component, coefficient)) component)
      (extractedDiagonalPart q degree ringRank ringSecret component coefficient component))
  rw [hsub]
  change LatticeCrypto.Poly.toPi
      (extractedOuterProduct q degree ringRank ringSecret
        (finProdFinEquiv (component, coefficient)) component) coefficient -
      LatticeCrypto.Poly.toPi
        (extractedDiagonalPart q degree ringRank ringSecret component coefficient component)
        coefficient = 0
  rw [extractedOuterProduct_diagonal_coefficient, extractedDiagonalPart_coefficient]
  simp

/-- Away from the one diagonal location, the square-free remainder is exactly the original
product of two distinct Boolean key coordinates. -/
@[simp]
theorem extractedSquareFreePart_coefficient_of_not_diagonal
    (q degree ringRank : ℕ) [NeZero q]
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (messageComponent maskComponent : Fin ringRank)
    (messageCoefficient maskCoefficient : Fin (degree + 1))
    (hnotDiagonal : ¬ (maskComponent = messageComponent ∧
      maskCoefficient = messageCoefficient)) :
    LatticeCrypto.Poly.toPi
        (extractedSquareFreePart q degree ringRank ringSecret messageComponent
          messageCoefficient maskComponent) maskCoefficient =
      (embedBit (ringSecret maskComponent maskCoefficient) : ZMod q) *
        embedBit (ringSecret messageComponent messageCoefficient) := by
  rw [extractedSquareFreePart]
  change (Native.CoefficientStructuredLWE.coefficientAddEquiv q (degree + 1)
      (extractedOuterProduct q degree ringRank ringSecret
          (finProdFinEquiv (messageComponent, messageCoefficient)) maskComponent -
        extractedDiagonalPart q degree ringRank ringSecret messageComponent
          messageCoefficient maskComponent)) maskCoefficient = _
  have hsub := congrArg (fun value ↦ value maskCoefficient)
    ((Native.CoefficientStructuredLWE.coefficientAddEquiv q (degree + 1)).map_sub
      (extractedOuterProduct q degree ringRank ringSecret
        (finProdFinEquiv (messageComponent, messageCoefficient)) maskComponent)
      (extractedDiagonalPart q degree ringRank ringSecret messageComponent
        messageCoefficient maskComponent))
  rw [hsub]
  change LatticeCrypto.Poly.toPi
      (extractedOuterProduct q degree ringRank ringSecret
        (finProdFinEquiv (messageComponent, messageCoefficient)) maskComponent)
        maskCoefficient -
      LatticeCrypto.Poly.toPi
        (extractedDiagonalPart q degree ringRank ringSecret messageComponent
          messageCoefficient maskComponent) maskCoefficient = _
  rw [extractedOuterProduct_coefficient, extractedDiagonalPart_coefficient]
  simp [hnotDiagonal]

/-- Diagonal coordinates for all mask components of one native self-key message. -/
def diagonalCross
    (q degree ringRank : ℕ)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (messageComponent : Fin ringRank)
    (messageCoefficient : Fin (degree + 1)) :
    Fin ringRank → RLWE.Rq q (degree + 1) :=
  fun maskComponent ↦ extractedDiagonalPart q degree ringRank ringSecret
    messageComponent messageCoefficient maskComponent

/-- Square-free coordinates for all mask components of one native self-key message. -/
def squareFreeCross
    (q degree ringRank : ℕ)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (messageComponent : Fin ringRank)
    (messageCoefficient : Fin (degree + 1)) :
    Fin ringRank → RLWE.Rq q (degree + 1) :=
  fun maskComponent ↦ extractedSquareFreePart q degree ringRank ringSecret
    messageComponent messageCoefficient maskComponent

/-- The actual self-key monomial vector splits exactly into its diagonal and square-free native
ring vectors. -/
theorem crossMonomial_eq_diagonalCross_add_squareFreeCross
    (q degree ringRank : ℕ)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (messageComponent : Fin ringRank)
    (messageCoefficient : Fin (degree + 1)) :
    TGSW.MonomialKDM.crossMonomial (embedRingSecret q ringSecret)
        (embedConstantBit q (degree + 1)
          (keyExtract ringSecret
            (finProdFinEquiv (messageComponent, messageCoefficient)))) =
      diagonalCross q degree ringRank ringSecret messageComponent messageCoefficient +
        squareFreeCross q degree ringRank ringSecret messageComponent messageCoefficient := by
  funext maskComponent
  rw [crossMonomial_eq_extractedOuterProduct]
  exact extractedOuterProduct_eq_diagonal_add_squareFree q degree ringRank ringSecret
    messageComponent messageCoefficient maskComponent

/-- Exact phase split for every row of one native self-key TGSW entry.  The first summand is
affine in the Boolean coefficient vector; the second contains only square-free products. -/
theorem gadgetPhase_self_eq_diagonal_add_squareFree
    (q degree ringRank levels : ℕ)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (messageComponent : Fin ringRank)
    (messageCoefficient : Fin (degree + 1)) :
    TGSW.gadgetPhase (embedRingSecret q ringSecret) gadget
        (embedConstantBit q (degree + 1)
          (keyExtract ringSecret
            (finProdFinEquiv (messageComponent, messageCoefficient)))) =
      (TGSW.CircularBoundary.affinePhasePart gadget
          (embedConstantBit q (degree + 1)
            (keyExtract ringSecret
              (finProdFinEquiv (messageComponent, messageCoefficient)))) +
        TGSW.MonomialKDM.monomialPhasePart gadget
          (diagonalCross q degree ringRank ringSecret messageComponent
            messageCoefficient)) +
      TGSW.MonomialKDM.monomialPhasePart gadget
        (squareFreeCross q degree ringRank ringSecret messageComponent
          messageCoefficient) := by
  rw [TGSW.MonomialKDM.gadgetPhase_eq_expandedGadgetPhase]
  unfold TGSW.MonomialKDM.expandedGadgetPhase
  rw [crossMonomial_eq_diagonalCross_add_squareFreeCross,
    TGSW.MonomialKDM.monomialPhasePart_add]
  simp only [add_assoc]

/-- Native direct TGSW encryption written with the diagonal and square-free phase contributions
as separate summands. -/
noncomputable def splitDirectEncrypt
    (q degree ringRank levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (messageComponent : Fin ringRank)
    (messageCoefficient : Fin (degree + 1)) :
    ProbComp (RingGSWCiphertext q (degree + 1) ringRank levels) :=
  TLWE.batchEncrypt ringRank (TGSW.rowCount ringRank levels) errorSampler
    (embedRingSecret q ringSecret)
    ((TGSW.CircularBoundary.affinePhasePart gadget
          (embedConstantBit q (degree + 1)
            (keyExtract ringSecret
              (finProdFinEquiv (messageComponent, messageCoefficient)))) +
        TGSW.MonomialKDM.monomialPhasePart gadget
          (diagonalCross q degree ringRank ringSecret messageComponent
            messageCoefficient)) +
      TGSW.MonomialKDM.monomialPhasePart gadget
        (squareFreeCross q degree ringRank ringSecret messageComponent
          messageCoefficient))

/-- The split sampler is definitionally distribution-preserving with respect to the actual
normalized native TGSW entry. -/
theorem directEncrypt_eq_splitDirectEncrypt
    (q degree ringRank levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (messageComponent : Fin ringRank)
    (messageCoefficient : Fin (degree + 1)) :
    TGSW.directEncrypt ringRank levels errorSampler (embedRingSecret q ringSecret) gadget
        (embedConstantBit q (degree + 1)
          (keyExtract ringSecret
            (finProdFinEquiv (messageComponent, messageCoefficient)))) =
      splitDirectEncrypt q degree ringRank levels errorSampler ringSecret gadget
        messageComponent messageCoefficient := by
  unfold TGSW.directEncrypt splitDirectEncrypt
  rw [gadgetPhase_self_eq_diagonal_add_squareFree]

/-! The following degree-generic interface is convenient for shared-prefix constructions, whose
ring length is written as a sum rather than syntactically as a successor.  Its specialization to
`degree + 1` is definitionally the positive-degree split above. -/

/-- Degree-generic diagonal cross vector for one extracted self-key coefficient. -/
def diagonalCrossAtDegree
    (q degree ringRank : ℕ)
    (ringSecret : RingBinarySecret ringRank degree)
    (messageComponent : Fin ringRank) (messageCoefficient : Fin degree) :
    Fin ringRank → RLWE.Rq q degree :=
  fun maskComponent ↦ LatticeCrypto.Poly.ofPi fun maskCoefficient ↦
    if maskComponent = messageComponent ∧ maskCoefficient = messageCoefficient then
      (embedBit (ringSecret messageComponent messageCoefficient) : ZMod q)
    else 0

/-- Degree-generic square-free remainder after removing the unique Boolean diagonal. -/
def squareFreeCrossAtDegree
    (q degree ringRank : ℕ)
    (ringSecret : RingBinarySecret ringRank degree)
    (messageComponent : Fin ringRank) (messageCoefficient : Fin degree) :
    Fin ringRank → RLWE.Rq q degree :=
  fun maskComponent ↦
    TGSW.MonomialKDM.crossMonomial (embedRingSecret q ringSecret)
        (embedConstantBit q degree
          (keyExtract ringSecret
            (finProdFinEquiv (messageComponent, messageCoefficient)))) maskComponent -
      diagonalCrossAtDegree q degree ringRank ringSecret messageComponent messageCoefficient
        maskComponent

/-- At positive degree the generic diagonal vector is the coefficient-explicit diagonal proved
above. -/
theorem diagonalCrossAtDegree_succ_eq_diagonalCross
    (q degree ringRank : ℕ)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (messageComponent : Fin ringRank) (messageCoefficient : Fin (degree + 1)) :
    diagonalCrossAtDegree q (degree + 1) ringRank ringSecret messageComponent
        messageCoefficient =
      diagonalCross q degree ringRank ringSecret messageComponent messageCoefficient := by
  rfl

/-- At positive degree the generic remainder is exactly the coefficient-explicit square-free
vector proved above. -/
theorem squareFreeCrossAtDegree_succ_eq_squareFreeCross
    (q degree ringRank : ℕ)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (messageComponent : Fin ringRank) (messageCoefficient : Fin (degree + 1)) :
    squareFreeCrossAtDegree q (degree + 1) ringRank ringSecret messageComponent
        messageCoefficient =
      squareFreeCross q degree ringRank ringSecret messageComponent messageCoefficient := by
  rfl

/-- The degree-generic native monomial is exactly diagonal plus square-free remainder. -/
theorem crossMonomial_eq_diagonalCrossAtDegree_add_squareFreeCrossAtDegree
    (q degree ringRank : ℕ)
    (ringSecret : RingBinarySecret ringRank degree)
    (messageComponent : Fin ringRank) (messageCoefficient : Fin degree) :
    TGSW.MonomialKDM.crossMonomial (embedRingSecret q ringSecret)
        (embedConstantBit q degree
          (keyExtract ringSecret
            (finProdFinEquiv (messageComponent, messageCoefficient)))) =
      diagonalCrossAtDegree q degree ringRank ringSecret messageComponent messageCoefficient +
        squareFreeCrossAtDegree q degree ringRank ringSecret messageComponent
          messageCoefficient := by
  cases degree with
  | zero => exact messageCoefficient.elim0
  | succ degree =>
      simpa only [diagonalCrossAtDegree_succ_eq_diagonalCross,
        squareFreeCrossAtDegree_succ_eq_squareFreeCross] using
        (crossMonomial_eq_diagonalCross_add_squareFreeCross q degree ringRank
          ringSecret messageComponent messageCoefficient)

/-- Degree-generic row-phase split used by the exact shared-prefix security hybrid. -/
theorem gadgetPhase_self_eq_diagonalAtDegree_add_squareFreeAtDegree
    (q degree ringRank levels : ℕ)
    (ringSecret : RingBinarySecret ringRank degree)
    (gadget : Fin levels → RLWE.Rq q degree)
    (messageComponent : Fin ringRank) (messageCoefficient : Fin degree) :
    TGSW.gadgetPhase (embedRingSecret q ringSecret) gadget
        (embedConstantBit q degree
          (keyExtract ringSecret
            (finProdFinEquiv (messageComponent, messageCoefficient)))) =
      (TGSW.CircularBoundary.affinePhasePart gadget
          (embedConstantBit q degree
            (keyExtract ringSecret
              (finProdFinEquiv (messageComponent, messageCoefficient)))) +
        TGSW.MonomialKDM.monomialPhasePart gadget
          (diagonalCrossAtDegree q degree ringRank ringSecret messageComponent
            messageCoefficient)) +
      TGSW.MonomialKDM.monomialPhasePart gadget
        (squareFreeCrossAtDegree q degree ringRank ringSecret messageComponent
          messageCoefficient) := by
  cases degree with
  | zero => exact messageCoefficient.elim0
  | succ degree =>
      simpa only [diagonalCrossAtDegree_succ_eq_diagonalCross,
        squareFreeCrossAtDegree_succ_eq_squareFreeCross] using
        (gadgetPhase_self_eq_diagonal_add_squareFree q degree ringRank levels
          ringSecret gadget messageComponent messageCoefficient)

/-- The ring-valued quadratic form obtainable by weighting all entries of the native extracted
outer-product table. -/
def extractedQuadraticForm
    (q degree ringRank : ℕ)
    (weight : Fin (ringRank * (degree + 1)) → Fin ringRank →
      RLWE.Rq q (degree + 1))
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    RLWE.Rq q (degree + 1) :=
  ∑ messageCoordinate, ∑ maskComponent,
    weight messageCoordinate maskComponent *
      extractedOuterProduct q degree ringRank ringSecret messageCoordinate maskComponent

/-- Publicly combine one fixed-level mask row from every entry of a full target-message BRK. -/
def maskRowCombination
    (q degree ringRank levels : ℕ)
    (weight : Fin (ringRank * (degree + 1)) → Fin ringRank →
      RLWE.Rq q (degree + 1))
    (level : Fin levels)
    (bootstrappingKey :
      Native.BootstrappingKey q (degree + 1) ringRank levels
        (ringRank * (degree + 1))) :
    RingCiphertext q (degree + 1) ringRank :=
  TGSW.MonomialKDM.FullTable.maskRowCombination weight level bootstrappingKey

/-- Exact combined row error for the native full target-message BRK. -/
def maskRowErrorCombination
    (q degree ringRank levels : ℕ)
    (weight : Fin (ringRank * (degree + 1)) → Fin ringRank →
      RLWE.Rq q (degree + 1))
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (level : Fin levels)
    (bootstrappingKey :
      Native.BootstrappingKey q (degree + 1) ringRank levels
        (ringRank * (degree + 1))) : RLWE.Rq q (degree + 1) :=
  TGSW.MonomialKDM.FullTable.maskRowErrorCombination weight
    (embedRingSecret q ringSecret) gadget
    (fun messageCoordinate ↦ embedConstantBit q (degree + 1)
      (keyExtract ringSecret messageCoordinate)) level bootstrappingKey

/-- In the actual full target-message BRK, any weighted native coefficient-outer-product form is
the ideal phase of a public mask-row combination, up to its explicit combined error. -/
theorem phase_maskRowCombination_eq
    (q degree ringRank levels : ℕ)
    (weight : Fin (ringRank * (degree + 1)) → Fin ringRank →
      RLWE.Rq q (degree + 1))
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (level : Fin levels)
    (bootstrappingKey :
      Native.BootstrappingKey q (degree + 1) ringRank levels
        (ringRank * (degree + 1))) :
    TLWE.phase (embedRingSecret q ringSecret)
        (maskRowCombination q degree ringRank levels weight level bootstrappingKey) =
      -(extractedQuadraticForm q degree ringRank weight ringSecret * gadget level) +
        maskRowErrorCombination q degree ringRank levels weight ringSecret gadget level
          bootstrappingKey := by
  simpa only [maskRowCombination, maskRowErrorCombination, extractedQuadraticForm,
    extractedOuterProduct, TGSW.MonomialKDM.FullTable.crossBilinearForm] using
    (TGSW.MonomialKDM.FullTable.phase_maskRowCombination_eq weight
      (embedRingSecret q ringSecret) gadget
      (fun messageCoordinate ↦ embedConstantBit q (degree + 1)
        (keyExtract ringSecret messageCoordinate)) level bootstrappingKey)

end

end FormalProof4FHE.TFHE.Native.FullBRKQuadraticSpan
