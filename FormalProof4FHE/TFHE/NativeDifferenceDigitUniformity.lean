/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.GadgetDigitUniformity
import FormalProof4FHE.TFHE.NativeDiagonalDeterminantNormalForm

/-!
# Uniform Digit Tensor of the Native Difference Ciphertext

At exact gadget capacity, every coefficient of every extended coordinate of every row of a
uniform native TGSW difference ciphertext decomposes to an independent uniform base digit.  This
module proves that claim as one exact distributional equality by composing explicit finite
equivalences.

It also connects the finite digit tensor back to the ring-valued entries of the selected-diagonal
identity-plus-digit matrix.  Thus future determinant estimates can work directly with an IID
`Fin base` tensor without changing the native evaluator distribution.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm

noncomputable section

open FormalProof4FHE.TFHE

variable {q degree ringRank : ℕ} [NeZero q]

/-- A TLWE row is equivalent to its mask-followed-by-body extended coordinate function. -/
def tlweExtendedEquiv {R : Type} {dimension : ℕ} :
    TLWE.Ciphertext R dimension ≃ (Fin (dimension + 1) → R) where
  toFun := Gadget.extendedCiphertext
  invFun := fun extended =>
    ⟨fun coordinate => extended coordinate.castSucc, extended (Fin.last dimension)⟩
  left_inv := by
    intro ciphertext
    rw [TLWE.Ciphertext.mk.injEq]
    constructor
    · funext coordinate
      simp [Gadget.extendedCiphertext]
    · simp [Gadget.extendedCiphertext]
  right_inv := by
    intro extended
    funext coordinate
    refine Fin.lastCases ?_ (fun maskCoordinate => ?_) coordinate
    · simp [Gadget.extendedCiphertext]
    · simp [Gadget.extendedCiphertext]

/-- A batched TLWE ciphertext is equivalent to its function of individually represented rows. -/
def batchRowsEquiv {R : Type} {dimension samples : ℕ} :
    TLWE.BatchCiphertext R dimension samples ≃
      (Fin samples → TLWE.Ciphertext R dimension) where
  toFun := TLWE.entry
  invFun := fun rows =>
    (fun coordinate sample => (rows sample).mask coordinate,
      fun sample => (rows sample).body)
  left_inv := by
    intro ciphertext
    cases ciphertext
    rfl
  right_inv := by
    intro rows
    funext sample
    rw [TLWE.Ciphertext.mk.injEq]
    exact ⟨rfl, rfl⟩

/-- A batched TLWE ciphertext is equivalently the tensor of all extended row coordinates. -/
def batchExtendedEquiv {R : Type} {dimension samples : ℕ} :
    TLWE.BatchCiphertext R dimension samples ≃
      (Fin samples → Fin (dimension + 1) → R) :=
  batchRowsEquiv.trans
    (Equiv.piCongrRight fun _ => tlweExtendedEquiv)

/-- Finite coefficient digits of every extended coordinate of every native difference row. -/
def differenceDigitCoefficientVector
    (params : Gadget.Base.Parameters q)
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    Fin (TGSW.rowCount ringRank params.levels) →
      Fin (ringRank + 1) → Fin (degree + 1) →
        Fin params.levels → Fin params.base :=
  fun row block coefficient =>
    Gadget.Base.ringCoefficientDigitVector params
      (Gadget.extendedCiphertext (TLWE.entry difference row) block) coefficient

/-- At exact capacity, the complete native difference ciphertext is equivalent to its full base
digit tensor. -/
noncomputable def differenceDigitCoefficientEquiv
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels) :
    RingGSWCiphertext q (degree + 1) ringRank params.levels ≃
      (Fin (TGSW.rowCount ringRank params.levels) →
        Fin (ringRank + 1) → Fin (degree + 1) →
          Fin params.levels → Fin params.base) :=
  (batchExtendedEquiv (R := RLWE.Rq q (degree + 1))
      (dimension := ringRank)
      (samples := TGSW.rowCount ringRank params.levels)).trans
    (Equiv.piCongrRight fun _row =>
      Equiv.piCongrRight fun _block =>
        Gadget.Base.ringCoefficientDigitEquiv params hcapacity)

@[simp]
theorem differenceDigitCoefficientEquiv_apply
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    differenceDigitCoefficientEquiv params hcapacity difference =
      differenceDigitCoefficientVector params difference := by
  rfl

/-- The complete coefficient-digit map is bijective at exact capacity. -/
theorem differenceDigitCoefficientVector_bijective
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels) :
    Function.Bijective (differenceDigitCoefficientVector
      (degree := degree) (ringRank := ringRank) params) := by
  have hfun :
      differenceDigitCoefficientVector (degree := degree) (ringRank := ringRank) params =
        differenceDigitCoefficientEquiv (degree := degree) (ringRank := ringRank)
          params hcapacity := by
    funext difference
    exact (differenceDigitCoefficientEquiv_apply params hcapacity difference).symm
  rw [hfun]
  exact (differenceDigitCoefficientEquiv (degree := degree) (ringRank := ringRank)
    params hcapacity).bijective

/-- **Exact native difference-digit law.** Mapping a uniform TGSW difference ciphertext to all of
its coefficient digits gives the uniform distribution on the complete tensor, hence every digit
is mutually independent and uniform in `Fin base`. -/
theorem differenceDigitCoefficientVector_uniform_evalDist
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels) :
    evalDist
        (differenceDigitCoefficientVector (degree := degree) (ringRank := ringRank) params <$>
          ($ᵗ RingGSWCiphertext q (degree + 1) ringRank params.levels)) =
      evalDist
        ($ᵗ (Fin (TGSW.rowCount ringRank params.levels) →
          Fin (ringRank + 1) → Fin (degree + 1) →
            Fin params.levels → Fin params.base)) :=
  evalDist_map_bijective_uniform_cross
    (α := RingGSWCiphertext q (degree + 1) ringRank params.levels)
    (β := Fin (TGSW.rowCount ringRank params.levels) →
      Fin (ringRank + 1) → Fin (degree + 1) →
        Fin params.levels → Fin params.base)
    (differenceDigitCoefficientVector (degree := degree) (ringRank := ringRank) params)
    (differenceDigitCoefficientVector_bijective
      (degree := degree) (ringRank := ringRank) params hcapacity)

/-- The IID finite digit tensor casts coefficientwise to the exact ring-valued digit used in the
selected-diagonal row matrix. -/
theorem differenceDigitCoefficientVector_cast
    (params : Gadget.Base.Parameters q)
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels)
    (row : Fin (TGSW.rowCount ringRank params.levels))
    (block : Fin (ringRank + 1)) (coefficient : Fin (degree + 1))
    (level : Fin params.levels) :
    ((differenceDigitCoefficientVector params difference row block coefficient level).val :
        ZMod q) =
      LatticeCrypto.Poly.toPi
        (differenceEntryDigits params difference row block level) coefficient := by
  exact Gadget.Base.ringCoefficientDigitVector_cast params
    (Gadget.extendedCiphertext (TLWE.entry difference row) block) coefficient level

end

end FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm
