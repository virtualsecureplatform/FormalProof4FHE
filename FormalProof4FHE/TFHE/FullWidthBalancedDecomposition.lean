/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.GadgetDigitUniformity
import Mathlib.Data.Fin.Rev

/-!
# Full-Width Balanced Double Decomposition

This file isolates the representation argument used by TFHEpp's multi-limb double-decomposition
path.  At exact capacity, adding the public centering offset, extracting every base digit,
subtracting half the base, and reversing the digit order is a bijection.  Applying this scalar
map coefficientwise and reshaping `rows * levels` outputs therefore remains a bijection: the
expanded rows contain exactly the same information as the ordinary rows.

The output digit is represented as an integer in the half-open centered interval
`[-half, base - half)`.  This matches the signed low-limb value passed to TFHEpp's digit FFT.
-/

namespace FormalProof4FHE.TFHE.Gadget.Base

noncomputable section

variable {q : ℕ} [NeZero q]

/-- The signed representatives obtained by subtracting `half` from a digit in `[0, base)`. -/
def BalancedDigit (base half : ℕ) :=
  { value : ℤ // -(half : ℤ) ≤ value ∧ value < (base : ℤ) - half }

/-- Subtracting the public half-base offset is a bijection from unsigned to balanced digits. -/
def finBalancedDigitEquiv (base half : ℕ) : Fin base ≃ BalancedDigit base half where
  toFun digit := ⟨(digit.val : ℤ) - half, by omega⟩
  invFun digit := ⟨Int.toNat (digit.val + half), by
    have hlow := digit.property.1
    have hupp := digit.property.2
    have hnonneg : 0 ≤ digit.val + (half : ℤ) := by omega
    rw [Int.toNat_lt hnonneg]
    omega⟩
  left_inv digit := by
    apply Fin.ext
    simp
  right_inv digit := by
    apply Subtype.ext
    have hlow := digit.property.1
    have hnonneg : 0 ≤ digit.val + (half : ℤ) := by omega
    change ((Int.toNat (digit.val + half) : ℕ) : ℤ) - half = digit.val
    rw [Int.toNat_of_nonneg hnonneg]
    omega

instance balancedDigitFintype (base half : ℕ) : Fintype (BalancedDigit base half) :=
  Fintype.ofEquiv (Fin base) (finBalancedDigitEquiv base half)

/-- Reverse a fixed-length vector.  TFHEpp emits the most-significant decomposition digit first,
whereas `Nat.digitsAppend` and `digitVector` use little-endian order. -/
def reverseVectorEquiv (length : ℕ) (Entry : Type) :
    (Fin length → Entry) ≃ (Fin length → Entry) where
  toFun vector index := vector index.rev
  invFun vector index := vector index.rev
  left_inv vector := by
    funext index
    simp
  right_inv vector := by
    funext index
    simp

/-- The public centering offset: half a base unit in every full-width radix position. -/
def balancedOffset (params : Parameters q) (half : ℕ) : ZMod q :=
  ∑ level : Fin params.levels, (half * params.base ^ level.val : ℕ)

/-- Exact scalar model of TFHEpp's full-width balanced auxiliary decomposition.

It first adds the public centering offset modulo `q`, decomposes all digits, subtracts `half`
from each digit, and reverses the level order to the implementation's most-significant-first
layout. -/
def balancedDigitEquiv (params : Parameters q)
    (hcapacity : q = params.base ^ params.levels) (half : ℕ) :
    ZMod q ≃ (Fin params.levels → BalancedDigit params.base half) :=
  (Equiv.addRight (balancedOffset params half)).trans <|
    (digitEquiv params hcapacity).trans <|
      (Equiv.piCongrRight fun _ ↦ finBalancedDigitEquiv params.base half).trans <|
        reverseVectorEquiv params.levels (BalancedDigit params.base half)

/-- The full-width balanced scalar decomposition is bijective. -/
theorem balancedDigitEquiv_bijective (params : Parameters q)
    (hcapacity : q = params.base ^ params.levels) (half : ℕ) :
    Function.Bijective (balancedDigitEquiv params hcapacity half) :=
  (balancedDigitEquiv params hcapacity half).bijective

/-- Transpose the scalar digit level to the outside of a row. -/
def transposeRowDigitsEquiv (Component Coordinate Level : Type)
    (Digit : Type) :
    (Component → Coordinate → Level → Digit) ≃
      (Level → Component → Coordinate → Digit) where
  toFun row level component coordinate := row component coordinate level
  invFun row component coordinate level := row level component coordinate
  left_inv _ := rfl
  right_inv _ := rfl

/-- Apply the full-width balanced decomposition independently to every coefficient of one
multi-component ring row. -/
def balancedRowEquiv (params : Parameters q)
    (hcapacity : q = params.base ^ params.levels) (half degree components : ℕ) :
    (Fin components → Fin degree → ZMod q) ≃
      (Fin params.levels → Fin components → Fin degree →
        BalancedDigit params.base half) :=
  (Equiv.piCongrRight fun _ ↦
      Equiv.piCongrRight fun _ ↦ balancedDigitEquiv params hcapacity half).trans <|
    transposeRowDigitsEquiv (Fin components) (Fin degree) (Fin params.levels)
      (BalancedDigit params.base half)

/-- Flatten the implementation's `(ordinary row, auxiliary level)` pair into one row index. -/
def flattenRowLevelsEquiv (rows levels : ℕ) (Entry : Type) :
    (Fin rows → Fin levels → Entry) ≃ (Fin (rows * levels) → Entry) where
  toFun table index :=
    table (finProdFinEquiv.symm index).1 (finProdFinEquiv.symm index).2
  invFun table row level := table (finProdFinEquiv (row, level))
  left_inv table := by
    funext row level
    simp
  right_inv table := by
    funext index
    change table (finProdFinEquiv (finProdFinEquiv.symm index)) = table index
    rw [finProdFinEquiv.apply_symm_apply]

/-- The complete double-decomposition/row-expansion map.  In particular, expanding `rows`
ordinary rows to `rows * levels` balanced rows is an exact public re-encoding, not a lossy
postprocessing step. -/
def balancedRowsEquiv (params : Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (half degree components rows : ℕ) :
    (Fin rows → Fin components → Fin degree → ZMod q) ≃
      (Fin (rows * params.levels) → Fin components → Fin degree →
        BalancedDigit params.base half) :=
  (Equiv.piCongrRight fun _ ↦
      balancedRowEquiv params hcapacity half degree components).trans <|
    flattenRowLevelsEquiv rows params.levels
      (Fin components → Fin degree → BalancedDigit params.base half)

/-- The complete full-width balanced row expansion is bijective. -/
theorem balancedRowsEquiv_bijective (params : Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (half degree components rows : ℕ) :
    Function.Bijective
      (balancedRowsEquiv params hcapacity half degree components rows) :=
  (balancedRowsEquiv params hcapacity half degree components rows).bijective

end

end FormalProof4FHE.TFHE.Gadget.Base
