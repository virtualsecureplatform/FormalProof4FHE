/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.MultiKeyAffine
import FormalProof4FHE.TFHE.BootstrappingSecurity

/-!
# Exact Affine/Bilinear Boundary in the TFHE Bootstrapping Key

`LWE.MultiKeyAffine` proves that arbitrary fixed affine cycles of direct fresh binary-secret LWE
rows reduce exactly to ordinary LWE.  Native TFHE does not fit that theorem: after the exact TGSW
normalization, each mask-block phase contains the product of a scalar-key bit and a ring-key
component.

This module records that boundary as checked algebra.  It splits every normalized TGSW gadget
phase into:

* an affine body-gadget part, which occupies only the final block; and
* a cross-key part, which occupies the mask blocks and is exactly bilinear.

The cross-key part vanishes after replacing the encrypted scalar-key bit by zero, explaining why
the post-cut bootstrapping-key hop in `TFHE.CutCycleSecurity` reduces to ordinary ring LWE.  For the
intact native cycle it remains present, so the affine multi-key theorem cannot discharge the
native circular-security premise.
-/

open Matrix

namespace FormalProof4FHE.TFHE.TGSW.CircularBoundary

/-- The body-gadget contribution to the direct TGSW phase. -/
def affinePhasePart {R : Type} [Ring R] {dimension levels : ℕ}
    (gadget : Fin levels → R) (message : R) :
    Fin (rowCount dimension levels) → R :=
  gadgetBodyShift gadget message

/-- The secret-dependent mask-gadget contribution to the direct TGSW phase. -/
def crossKeyPhasePart {R : Type} [Ring R] {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R) :
    Fin (rowCount dimension levels) → R :=
  -(vecMul secret (gadgetMaskShift gadget message))

/-- Every direct gadget phase is exactly its affine part plus its cross-key part. -/
theorem gadgetPhase_eq_affine_add_cross {R : Type} [Ring R]
    {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R) :
    gadgetPhase secret gadget message =
      affinePhasePart gadget message + crossKeyPhasePart secret gadget message := by
  funext row
  simp only [gadgetPhase, affinePhasePart, crossKeyPhasePart,
    Pi.add_apply, Pi.neg_apply, sub_eq_add_neg]

/-- The final gadget block contains exactly the affine message multiple. -/
theorem affinePhasePart_last {R : Type} [Ring R]
    {dimension levels : ℕ}
    (gadget : Fin levels → R) (message : R) (level : Fin levels) :
    affinePhasePart (dimension := dimension) gadget message
        (finProdFinEquiv (Fin.last dimension, level)) =
      message * gadget level := by
  simp [affinePhasePart, gadgetBodyShift, rowIndex]

/-- The cross-key contribution is zero in the final gadget block. -/
theorem crossKeyPhasePart_last {R : Type} [Ring R]
    {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R)
    (level : Fin levels) :
    crossKeyPhasePart secret gadget message
        (finProdFinEquiv (Fin.last dimension, level)) = 0 := by
  have hsplit := congrFun
    (gadgetPhase_eq_affine_add_cross secret gadget message)
    (finProdFinEquiv (Fin.last dimension, level))
  simp only [Pi.add_apply] at hsplit
  rw [gadgetPhase_last, affinePhasePart_last] at hsplit
  simpa using hsplit

/-- A mask-coordinate block has no affine body-gadget contribution. -/
theorem affinePhasePart_castSucc {R : Type} [Ring R]
    {dimension levels : ℕ}
    (gadget : Fin levels → R) (message : R)
    (coordinate : Fin dimension) (level : Fin levels) :
    affinePhasePart gadget message
        (finProdFinEquiv (Fin.castSucc coordinate, level)) = 0 := by
  have hne : coordinate.val ≠ dimension := Nat.ne_of_lt coordinate.isLt
  simp [affinePhasePart, gadgetBodyShift, rowIndex, hne]

/-- A mask-coordinate block is exactly the bilinear cross-key product. -/
theorem crossKeyPhasePart_castSucc {R : Type} [CommRing R]
    {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R) (message : R)
    (coordinate : Fin dimension) (level : Fin levels) :
    crossKeyPhasePart secret gadget message
        (finProdFinEquiv (Fin.castSucc coordinate, level)) =
      -(secret coordinate * (message * gadget level)) := by
  have hsplit := congrFun
    (gadgetPhase_eq_affine_add_cross secret gadget message)
    (finProdFinEquiv (Fin.castSucc coordinate, level))
  simp only [Pi.add_apply] at hsplit
  rw [gadgetPhase_castSucc, affinePhasePart_castSucc] at hsplit
  simpa using hsplit.symm

/-- Replacing the encrypted message by zero removes the entire cross-key obstruction. -/
@[simp]
theorem crossKeyPhasePart_zero_message {R : Type} [Ring R]
    {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R) :
    crossKeyPhasePart secret gadget 0 = 0 := by
  funext row
  simp [crossKeyPhasePart, gadgetMaskShift, Matrix.vecMul, dotProduct]

/-- A zero encryption key also removes the cross-key contribution. -/
@[simp]
theorem crossKeyPhasePart_zero_secret {R : Type} [Ring R]
    {dimension levels : ℕ}
    (gadget : Fin levels → R) (message : R) :
    crossKeyPhasePart (0 : Fin dimension → R) gadget message = 0 := by
  funext row
  simp [crossKeyPhasePart]

/-- At the zero-message cut, the normalized gadget phase is purely affine (and in fact zero). -/
theorem gadgetPhase_zero_eq_affinePart {R : Type} [Ring R]
    {dimension levels : ℕ}
    (secret : Fin dimension → R) (gadget : Fin levels → R) :
    gadgetPhase secret gadget 0 = affinePhasePart gadget 0 := by
  rw [gadgetPhase_eq_affine_add_cross, crossKeyPhasePart_zero_message]
  simp

end FormalProof4FHE.TFHE.TGSW.CircularBoundary
