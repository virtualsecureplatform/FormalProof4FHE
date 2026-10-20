/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/
import FormalProof4FHE.LWE.GSWPairLocalCompiler
import FormalProof4FHE.LWE.GSWGadget

/-!
# Testing a public correction with correlated midpoint errors

The affine midpoint of a quadratic bit target has a signed-product residual.
This correlation is not a correctness invariant of native GSW multiplication:
the explicit zero-fresh-noise sampler realizations below have q/8 control
errors and correctly decoded controls, but their native product and NAND
decode incorrectly. This finite witness does not establish an asymptotic
failure probability or exclude another correlated error law/decoder.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.LWE.GSWCorrelatedMidpoint

theorem midpoint_residual {R : Type} [CommRing R] (v : R) (a b : Bool) :
    GSWPairLocalCompiler.residual v (-2 * v) (-2 * v) (4 * v) a b =
      v * (1 - 2 * KDMStarGSW.anchor a) * (1 - 2 * KDMStarGSW.anchor b) := by
  unfold GSWPairLocalCompiler.residual
  ring

def tinyParams : GSWGadget.Parameters 16 where
  base := 2
  levels := 4
  one_lt_base := by decide
  modulus_le_capacity := by decide

def tinySecret : Fin 2 → ZMod 16 := 0
def tinyLevel : Fin tinyParams.levels := ⟨3, by decide⟩

def tinyConstant (column : Fin 12) : ZMod 16 :=
  if column.val / 4 = 0 then 0 else ((2 ^ (column.val % 4) / 4 : ℕ) : ZMod 16)

/-- Public full signed-product midpoint shift, including the diagonal. -/
def tinyShift (index : Fin 2) : Matrix (Fin 2) (Fin 12) (ZMod 16) := fun row column ↦
  let w : ℕ := 2 ^ (column.val % 4)
  if column.val / 4 = 0 then (if row = index then (w : ZMod 16) else 0)
  else -((w / 2 : ℕ) : ZMod 16) * ((if row = index then 1 else 0) +
    (if row.val + 1 = column.val / 4 then 1 else 0))

/-- At the zero secret and zero fresh error, the raw body is zero. -/
def tinyControl (index : Fin 2) (rawMask : Matrix (Fin 2) (Fin 12) (ZMod 16)) :
    GSWGadget.Ciphertext tinyParams 3 :=
  GSWOperations.ciphertextMatrix (rawMask - tinyShift index, tinyConstant)

/-- Every prescribed stored mask is attainable by a raw uniform-mask draw. -/
def tinyRawMask (index : Fin 2) (value : ZMod 16) : Matrix (Fin 2) (Fin 12) (ZMod 16) :=
  fun row column ↦ tinyShift index row column + value

def first : GSWGadget.Ciphertext tinyParams 3 := tinyControl 0 (tinyRawMask 0 0)
def second : GSWGadget.Ciphertext tinyParams 3 := tinyControl 1 (tinyRawMask 1 12)

private theorem zero_phase (ciphertext : GSWGadget.Ciphertext tinyParams 3) :
    vecMul (GSWOperations.extendedSecret tinySecret) ciphertext = ciphertext 0 := by
  funext column
  simp [vecMul, dotProduct, GSWOperations.extendedSecret, tinySecret, Fin.sum_univ_succ]

set_option maxRecDepth 4096 in
theorem controls_decode_zero :
    GSWGadget.decrypt tinyParams tinySecret first tinyLevel = false ∧
      GSWGadget.decrypt tinyParams tinySecret second tinyLevel = false := by
  simp only [GSWGadget.decrypt]
  rw [zero_phase, zero_phase]
  decide

set_option maxRecDepth 4096 in
theorem controls_noise_at_most_eighth :
    GSWGadget.NoiseBound tinyParams (GSWOperations.extendedSecret tinySecret) first 0 2 ∧
      GSWGadget.NoiseBound tinyParams (GSWOperations.extendedSecret tinySecret) second 0 2 := by
  simp only [GSWGadget.NoiseBound, GSWOperations.noise, zero_smul, sub_zero]
  rw [zero_phase, zero_phase]
  decide

set_option maxRecDepth 4096 in
theorem product_body_phase :
    vecMul (GSWOperations.extendedSecret tinySecret)
      (GSWGadget.multiply tinyParams first second) ⟨3, by decide⟩ = (6 : ZMod 16) := by
  rw [zero_phase]
  change (∑ row : Fin 12, first 0 row *
    GSWGadget.digitMatrix tinyParams second row ⟨3, by decide⟩) = (6 : ZMod 16)
  norm_num [GSWGadget.multiply, Matrix.mul_apply, Fin.sum_univ_succ,
    first, second, tinyControl, tinyRawMask, GSWOperations.ciphertextMatrix,
    tinyConstant, tinyShift, tinyParams, GSWGadget.digitMatrix,
    TFHE.Gadget.Base.digit, TFHE.Gadget.Base.natDigit, TFHE.Gadget.Base.digitList,
    finProdFinEquiv]
  decide

set_option maxRecDepth 4096 in
theorem product_decodes_wrong :
    GSWGadget.decrypt tinyParams tinySecret (GSWGadget.multiply tinyParams first second) tinyLevel = true := by
  unfold GSWGadget.decrypt
  change TFHE.BootstrappingCorrectness.decodeNearest 0 8
    (vecMul (GSWOperations.extendedSecret tinySecret)
      (GSWGadget.multiply tinyParams first second) ⟨3, by decide⟩) = true
  rw [product_body_phase]
  decide

set_option maxRecDepth 4096 in
theorem nand_decodes_wrong :
    GSWGadget.decrypt tinyParams tinySecret (GSWGadget.nand tinyParams first second) tinyLevel = false := by
  unfold GSWGadget.decrypt GSWGadget.nand
  rw [vecMul_sub]
  change TFHE.BootstrappingCorrectness.decodeNearest 0 8
    ((vecMul (GSWOperations.extendedSecret tinySecret) (GSWGadget.gadget tinyParams 3))
      ⟨3, by decide⟩ - (vecMul (GSWOperations.extendedSecret tinySecret)
        (GSWGadget.multiply tinyParams first second)) ⟨3, by decide⟩) = false
  rw [product_body_phase, zero_phase]
  decide

end FormalProof4FHE.LWE.GSWCorrelatedMidpoint
