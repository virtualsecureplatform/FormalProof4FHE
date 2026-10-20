/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/
import FormalProof4FHE.LWE.GSWGadget
import FormalProof4FHE.LWE.GSWPairLocalCompiler

/-!
# Redundant public digits and constant affine control corrections

A fixed reconstructed digit factor preserves the quadratic four-corner
coefficient of a constant affine control sampler. This includes signed and
redundant factors with no digit-size restriction. At an initial gadget branch,
such a factor cannot give uniformly small native errors below the four-corner
threshold. The statement fixes the correction and factor across keys; it
does not cover factors/corrections chosen using secret-dependent source bodies,
or a different reachable-state invariant. No security assumption is used.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.LWE.GSWRedundantDigits

def affineControl {R : Type} [CommRing R] {width : ℕ}
    (raw shift : Matrix (Fin 2) (Fin width) R) (constant : Fin width → R)
    (secret : Fin 2 → R) : Matrix (Fin 3) (Fin width) R :=
  GSWOperations.ciphertextMatrix (raw - shift, vecMul secret raw + constant)

theorem affineControl_phase {R : Type} [CommRing R] {width : ℕ}
    (raw shift : Matrix (Fin 2) (Fin width) R) (constant : Fin width → R)
    (secret : Fin 2 → R) :
    vecMul (GSWOperations.extendedSecret secret) (affineControl raw shift constant secret) =
      constant + vecMul secret shift := by
  rw [affineControl, GSWOperations.vecMul_ciphertextMatrix, vecMul_sub]
  funext column
  simp only [Pi.add_apply, Pi.sub_apply]
  ring

def productError {R : Type} [CommRing R] {width columns : ℕ}
    (raw shift : Matrix (Fin 2) (Fin width) R) (constant : Fin width → R)
    (target : Matrix (Fin 3) (Fin columns) R)
    (factor : Matrix (Fin width) (Fin columns) R) (a b : Bool) : Fin columns → R :=
  GSWOperations.noise (GSWOperations.extendedSecret (KDMStarConversion.corner a b))
    target (affineControl raw shift constant (KDMStarConversion.corner a b) * factor)
    (KDMStarGSW.anchor a)

/-- Raw independent masks cancel from the phase. Reconstruction fixes the
quadratic coefficient through the target's second secret-coordinate row. -/
theorem productError_as_residual {R : Type} [CommRing R] {width columns : ℕ}
    (raw shift : Matrix (Fin 2) (Fin width) R) (constant : Fin width → R)
    (target : Matrix (Fin 3) (Fin columns) R)
    (factor : Matrix (Fin width) (Fin columns) R) (a b : Bool) (column : Fin columns) :
    productError raw shift constant target factor a b column =
      GSWPairLocalCompiler.residual (vecMul constant factor column)
        ((shift * factor) 0 column - target 0 column + target 1 column)
        ((shift * factor) 1 column) (target 2 column) a b := by
  unfold productError GSWOperations.noise
  rw [← vecMul_vecMul, affineControl_phase, add_vecMul, vecMul_vecMul]
  cases a <;> cases b <;>
    simp [vecMul, dotProduct, GSWOperations.extendedSecret,
      KDMStarConversion.corner, KDMStarGSW.anchor, GSWPairLocalCompiler.residual,
      Fin.sum_univ_succ] <;> ring

theorem productError_four_corner {R : Type} [CommRing R] {width columns : ℕ}
    (raw shift : Matrix (Fin 2) (Fin width) R) (constant : Fin width → R)
    (target : Matrix (Fin 3) (Fin columns) R)
    (factor : Matrix (Fin width) (Fin columns) R) (column : Fin columns) :
    productError raw shift constant target factor true true column -
      productError raw shift constant target factor true false column -
      productError raw shift constant target factor false true column +
      productError raw shift constant target factor false false column = target 2 column := by
  simp only [productError_as_residual]
  exact GSWPairLocalCompiler.four_corner_identity _ _ _ _

/-- A fixed factor reconstructing G cannot uniformly reduce these errors
below one quarter of the selected gadget weight, regardless of its size. -/
theorem exists_bad_reconstructed_corner {q width columns : ℕ} [NeZero q]
    (raw shift : Matrix (Fin 2) (Fin width) (ZMod q)) (constant : Fin width → ZMod q)
    (gadget : Matrix (Fin 3) (Fin width) (ZMod q))
    (target : Matrix (Fin 3) (Fin columns) (ZMod q))
    (factor : Matrix (Fin width) (Fin columns) (ZMod q))
    (hreconstruct : gadget * factor = target) (column : Fin columns) (bound : ℕ)
    (hweight : 4 * bound < KDMStarConversion.magnitude (target 2 column)) :
    ∃ a b, bound < KDMStarConversion.magnitude
      (productError raw shift constant (gadget * factor) factor a b column) := by
  rw [hreconstruct]
  simp_rw [productError_as_residual]
  exact GSWPairLocalCompiler.exists_bad_pair _ _ _ _ bound hweight

/-- The bound applies to an actual initial-gadget mask column of native GSW,
with any signed/redundant factor reconstructing that gadget. -/
theorem initial_gadget_bad_corner {q : ℕ} [NeZero q]
    (params : GSWGadget.Parameters q)
    (raw shift : Matrix (Fin 2) (Fin (3 * params.levels)) (ZMod q))
    (constant : Fin (3 * params.levels) → ZMod q)
    (factor : Matrix (Fin (3 * params.levels)) (Fin (3 * params.levels)) (ZMod q))
    (hreconstruct : GSWGadget.gadget params 3 * factor = GSWGadget.gadget params 3)
    (level : Fin params.levels) (bound : ℕ)
    (hweight : 4 * bound < KDMStarConversion.magnitude (TFHE.Gadget.Base.gadget params level)) :
    ∃ a b, bound < KDMStarConversion.magnitude
      (productError raw shift constant (GSWGadget.gadget params 3) factor a b
        (finProdFinEquiv (2, level))) := by
  have hw : 4 * bound < KDMStarConversion.magnitude
      (GSWGadget.gadget params 3 2 (finProdFinEquiv (2, level))) := by
    simpa [GSWGadget.gadget] using hweight
  simpa only [hreconstruct] using exists_bad_reconstructed_corner raw shift constant
    (GSWGadget.gadget params 3) (GSWGadget.gadget params 3) factor hreconstruct
    (finProdFinEquiv (2, level)) bound hw

/-- Public kernel additions preserve exact ciphertext reconstruction. -/
theorem kernel_add_reconstructs {R : Type} [CommRing R] {rows width columns : ℕ}
    (gadget : Matrix (Fin rows) (Fin width) R)
    (factor kernel : Matrix (Fin width) (Fin columns) R)
    (target : Matrix (Fin rows) (Fin columns) R)
    (hreconstruct : gadget * factor = target) (hkernel : gadget * kernel = 0) :
    gadget * (factor + kernel) = target := by
  rw [Matrix.mul_add, hreconstruct, hkernel, add_zero]

end FormalProof4FHE.LWE.GSWRedundantDigits
