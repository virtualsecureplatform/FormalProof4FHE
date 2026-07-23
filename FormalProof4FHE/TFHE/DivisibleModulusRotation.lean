/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.RotationLookup

/-!
# Exact Native Rotation from a Larger Divisible Modulus

Native blind rotation needs exponents modulo `2N`, but ciphertext coefficients should live at a
much larger modulus to leave room for noise.  When `2N` divides the coefficient modulus `q`, the
canonical quotient map `ZMod q → ZMod (2N)` is additive.  This file composes that quotient with
the `ZMod`/`Fin` equivalence and proves exact phase arithmetic: body and mask exponents may be
mapped independently with no rounding accumulation.

This divisible-modulus construction is a checked exact bridge toward production-style modulus
switching.  It already decouples coefficient distance from the signed-rotation group and avoids
the nonzero-noise obstruction of the special `q = 2N` witness.
-/

open Matrix

namespace FormalProof4FHE.TFHE.RotationLookup

noncomputable section

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing

/-- Exact exponent reduction from a coefficient modulus divisible by the rotation modulus. -/
def divisibleRoundExponent {q degree : ℕ}
    (hdiv : 2 * (degree + 1) ∣ q) :
    ZMod q → Fin (2 * (degree + 1)) :=
  (ZMod.finEquiv (2 * (degree + 1))).symm ∘
    ZMod.castHom hdiv (ZMod (2 * (degree + 1)))

@[simp]
theorem finEquiv_divisibleRoundExponent {q degree : ℕ}
    (hdiv : 2 * (degree + 1) ∣ q) (value : ZMod q) :
    ZMod.finEquiv (2 * (degree + 1))
        (divisibleRoundExponent hdiv value) =
      ZMod.castHom hdiv (ZMod (2 * (degree + 1))) value := by
  exact (ZMod.finEquiv (2 * (degree + 1))).apply_symm_apply _

/-- Additivity of exact divisible-modulus reduction makes the native body-minus-mask exponent
equal the reduced TLWE phase. -/
theorem nativePhaseExponent_divisibleRoundExponent
    {q degree lweDimension : ℕ}
    (hdiv : 2 * (degree + 1) ∣ q)
    (input : ScalarCiphertext q lweDimension)
    (lweSecret : BinarySecret lweDimension) :
    nativePhaseExponent (divisibleRoundExponent hdiv) input lweSecret =
      divisibleRoundExponent hdiv
        (TLWE.phase (embedBinarySecret lweSecret) input) := by
  let exponentEquiv := ZMod.finEquiv (2 * (degree + 1))
  let reduce := ZMod.castHom hdiv (ZMod (2 * (degree + 1)))
  apply exponentEquiv.injective
  rw [finEquiv_divisibleRoundExponent]
  unfold nativePhaseExponent nativeMaskExponent
  simp only [map_add, map_sum, apply_ite, map_neg, map_zero]
  have hround (value : ZMod q) :
      exponentEquiv (divisibleRoundExponent hdiv value) = reduce value :=
    finEquiv_divisibleRoundExponent hdiv value
  simp_rw [hround]
  have hterm (coordinate : Fin lweDimension) :
      (if lweSecret coordinate then -reduce (input.mask coordinate) else 0) =
        -reduce (embedBit (lweSecret coordinate) * input.mask coordinate) := by
    cases lweSecret coordinate <;> simp [embedBit, reduce]
  simp_rw [hterm]
  rw [Finset.sum_neg_distrib]
  unfold TLWE.phase dotProduct embedBinarySecret
  simp only [map_sub, map_sum, map_mul]
  abel

/-- The noiseless divisible-modulus native trace reads the table at the exactly reduced scalar
phase. -/
theorem idealExtractedPhase_divisibleRoundExponent
    {q degree rank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hdiv : 2 * (degree + 1) ∣ q)
    (input : ScalarCiphertext q lweDimension)
    (bootstrappingKey : Native.BootstrappingKey
      q (degree + 1) rank params.levels lweDimension)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : Fin rank → RLWE.Rq q (degree + 1))
    (testVector : RLWE.Rq q (degree + 1)) :
    BootstrappingCorrectness.idealExtractedPhase ringSecret
        (testVectorAccumulator (divisibleRoundExponent hdiv input.body) testVector)
        (BlindRotation.nativeControls params (divisibleRoundExponent hdiv) input
          bootstrappingKey lweSecret) =
      coefficientLookup testVector
        (divisibleRoundExponent hdiv
          (TLWE.phase (embedBinarySecret lweSecret) input)) := by
  rw [idealExtractedPhase_testVectorAccumulator_nativeControls]
  rw [nativePhaseExponent_divisibleRoundExponent]

/-- **Closed Boolean-table correctness at a larger divisible coefficient modulus.**  The native
rotation group remains `Fin (2N)`, while row errors and output codewords live in `ZMod q`. -/
theorem decode_nativeBlindRotate_apply_bitTable_divisible_linear
    {q degree rank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hdiv : 2 * (degree + 1) ∣ q)
    (input : ScalarCiphertext q lweDimension)
    (bootstrappingKey : Native.BootstrappingKey
      q (degree + 1) rank params.levels lweDimension)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : Fin rank → RLWE.Rq q (degree + 1))
    (zeroCode oneCode : ZMod q)
    (firstHalfBit : Fin (degree + 1) → Bool)
    (rowErrorBound : ℕ)
    (hopposite : oneCode = -zeroCode)
    (hrows : ∀ coordinate index,
      LatticeCrypto.cInfNorm
        (TGSW.rowError (R := RLWE.Rq q (degree + 1)) ringSecret
          (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) (lweSecret coordinate))
          (bootstrappingKey coordinate) index) ≤ rowErrorBound)
    (hmargin :
      2 * BootstrappingCorrectness.nativeLinearNoiseBudget degree rank
          params.levels params.base lweDimension rowErrorBound <
        BootstrappingCorrectness.centeredDistance zeroCode oneCode) :
    BootstrappingCorrectness.decodeNearest zeroCode oneCode
        (TLWE.phase (SampleExtraction.extractedSecret ringSecret)
          (SampleExtraction.apply
            (BlindRotation.nativeBlindRotate params (divisibleRoundExponent hdiv) input
              bootstrappingKey
                (testVectorAccumulator (divisibleRoundExponent hdiv input.body)
                  (bitTableTestVector zeroCode oneCode firstHalfBit))))) =
      antiPeriodicBit firstHalfBit
        (divisibleRoundExponent hdiv
          (TLWE.phase (embedBinarySecret lweSecret) input)) := by
  apply BootstrappingCorrectness.decode_nativeBlindRotate_apply_linear params
    (divisibleRoundExponent hdiv) input bootstrappingKey lweSecret ringSecret
    (testVectorAccumulator (divisibleRoundExponent hdiv input.body)
      (bitTableTestVector zeroCode oneCode firstHalfBit))
    zeroCode oneCode
    (antiPeriodicBit firstHalfBit
      (divisibleRoundExponent hdiv
        (TLWE.phase (embedBinarySecret lweSecret) input)))
    rowErrorBound hrows
  · rw [idealExtractedPhase_divisibleRoundExponent]
    exact coefficientLookup_bitTableTestVector zeroCode oneCode firstHalfBit _ hopposite
  · exact hmargin

end

end FormalProof4FHE.TFHE.RotationLookup
