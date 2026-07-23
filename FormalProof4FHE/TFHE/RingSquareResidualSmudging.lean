/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeShiftedDiscreteGaussianBounds
import FormalProof4FHE.TFHE.RingSquareActualNormalForm

/-!
# Residual Smudging for the `RGSW_S(-S)` Short-Preimage Compiler

The exact short-preimage compiler produces upper-row residual

`e_target + S * sum_i x_i e_i`.

This file isolates the statistical comparison that is needed after the algebraic and ordinary-
RLWE reductions.  Translating an independently sampled target error by a fixed induced residual
costs exactly its additive shift distance.  Random bounded residuals cost no more than the same
worst-case shift bound.  For the executable coefficientwise discrete-Gaussian sampler, the bound
is instantiated by the existing certified finite-window estimate.

These theorems do not claim that the shift is small.  They expose the precise quantitative
condition under which a narrow target error can absorb the compiler-induced correlated residual.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.ResidualSmudging

noncomputable section

/-- Add a fixed compiler residual after independently sampling the target-row error. -/
def shiftedErrorSampler {R : Type} [Add R]
    (errorSampler : ProbComp R) (shift : R) : ProbComp R :=
  (fun error ↦ error + shift) <$> errorSampler

/-- The fixed-residual comparison is exactly the ordinary additive translation distance. -/
theorem tvDist_shiftedErrorSampler_eq_addShiftDistance
    {R : Type} [AddCommGroup R]
    (errorSampler : ProbComp R) (shift : R) :
    tvDist (shiftedErrorSampler errorSampler shift) errorSampler =
      FormalProof4FHE.FiniteProduct.addShiftDistance errorSampler shift := by
  unfold shiftedErrorSampler FormalProof4FHE.FiniteProduct.addShiftDistance
  congr 2
  funext error
  exact add_comm error shift

/-- Sample an arbitrary residual first and add it to an independent target error. -/
def randomShiftedErrorSampler {R : Type} [Add R]
    (shiftSampler errorSampler : ProbComp R) : ProbComp R :=
  shiftSampler >>= fun shift ↦ shiftedErrorSampler errorSampler shift

/-- A support-wise fixed-shift bound lifts to an arbitrary random compiler residual. -/
theorem tvDist_randomShiftedErrorSampler_le
    {R : Type} [AddCommGroup R]
    (shiftSampler errorSampler : ProbComp R) (bound : ℝ)
    (hshift : ∀ shift, shift ∈ support shiftSampler →
      FormalProof4FHE.FiniteProduct.addShiftDistance errorSampler shift ≤ bound) :
    tvDist (randomShiftedErrorSampler shiftSampler errorSampler) errorSampler ≤ bound := by
  let constant : ProbComp R := shiftSampler >>= fun _shift ↦ errorSampler
  have hconstant : evalDist constant = evalDist errorSampler := by
    apply evalDist_ext
    intro output
    unfold constant
    rw [probOutput_bind_const, probFailure_eq_zero]
    simp
  have hmixture :
      tvDist
          (shiftSampler >>= fun shift ↦ shiftedErrorSampler errorSampler shift)
          constant ≤ bound := by
    unfold constant
    apply tvDist_bind_left_le_const
    intro shift hsupport
    rw [tvDist_shiftedErrorSampler_eq_addShiftDistance]
    exact hshift shift hsupport
  unfold randomShiftedErrorSampler
  unfold tvDist at hmixture ⊢
  rwa [hconstant] at hmixture

/-- The exact correlated residual contributed by a successful short preimage. -/
def inducedShift {R Index : Type} [CommRing R] [Fintype Index]
    (secret : Fin 1 → R) (weight : Index → R)
    (sourceRows : Index → TLWE.Ciphertext R 1) : R :=
  secret 0 * TLWE.phase secret (preimageCombination weight sourceRows)

/-- The same residual shift after the weighted source error has been isolated as one ring
element. -/
def inducedShiftFromError {R : Type} [Mul R]
    (secret weightedSourceError : R) : R :=
  secret * weightedSourceError

/-- Restatement of the compiler residual identity in terms of `inducedShift`. -/
theorem residual_squareFromPreimage_eq_target_add_inducedShift
    {R Index : Type} [CommRing R] [Fintype Index]
    (secret : Fin 1 → R) (gadget : R) (weight : Index → R)
    (sourceRows : Index → TLWE.Ciphertext R 1)
    (targetRow : TLWE.Ciphertext R 1)
    (hPreimage : HasGadgetPreimage gadget weight sourceRows) :
    TLWE.phase secret (squareFromPreimage weight sourceRows targetRow) -
        secret 0 * secret 0 * gadget =
      TLWE.phase secret targetRow + inducedShift secret weight sourceRows := by
  exact residual_squareFromPreimage secret gadget weight sourceRows targetRow hPreimage

/-- Ciphertext-level normal form: on a successful preimage, compiling an assembled zero-message
target row is exactly a fresh-mask square row whose error is translated by `inducedShift`. -/
theorem squareFromPreimage_assemble_zero_eq_assembleSquareRow
    {R Index : Type} [CommRing R] [Fintype Index]
    (secret targetMask : Fin 1 → R) (gadget targetError : R)
    (weight : Index → R) (sourceRows : Index → TLWE.Ciphertext R 1)
    (hPreimage : HasGadgetPreimage gadget weight sourceRows) :
    squareFromPreimage weight sourceRows
        (TLWE.assemble secret targetMask 0 targetError) =
      assembleSquareRow secret gadget
        (targetError + inducedShift secret weight sourceRows)
        (fun _coordinate ↦
          targetMask 0 - gadgetApproximation weight sourceRows) := by
  have hApproximation :=
    gadgetApproximation_eq_mul_add_phase secret gadget weight sourceRows hPreimage
  rw [TLWE.Ciphertext.mk.injEq]
  constructor
  · funext coordinate
    simp [squareFromPreimage, squareFromApproximation, Row.subtractMask,
      assembleSquareRow, TLWE.assemble]
  · change
      dotProduct secret targetMask + 0 + targetError =
        dotProduct secret
            (fun _coordinate ↦
              targetMask 0 - gadgetApproximation weight sourceRows) +
          secret 0 * secret 0 * gadget +
            (targetError +
              secret 0 * TLWE.phase secret (preimageCombination weight sourceRows))
    have hTargetDot : dotProduct secret targetMask = secret 0 * targetMask 0 := by
      simp [dotProduct]
    have hOutputDot :
        dotProduct secret
            (fun _coordinate ↦
              targetMask 0 - gadgetApproximation weight sourceRows) =
          secret 0 *
            (targetMask 0 - gadgetApproximation weight sourceRows) := by
      simp [dotProduct]
    rw [hTargetDot, hOutputDot, hApproximation]
    ring

/-- A fixed-secret honest square row whose independently sampled error is translated by a fixed
compiler residual. -/
def fixedSecretShiftedSquareRowSampler
    {R : Type} [CommRing R] [SampleableType R]
    (secret : Fin 1 → R) (errorSampler : ProbComp R)
    (gadget shift : R) : ProbComp (TLWE.Ciphertext R 1) := do
  let mask ← $ᵗ (Fin 1 → R)
  let error ← errorSampler
  return assembleSquareRow secret gadget (error + shift) mask

/-- The corresponding fixed-secret native row with an untranslated target error. -/
def fixedSecretSquareRowSampler
    {R : Type} [CommRing R] [SampleableType R]
    (secret : Fin 1 → R) (errorSampler : ProbComp R)
    (gadget : R) : ProbComp (TLWE.Ciphertext R 1) := do
  let mask ← $ᵗ (Fin 1 → R)
  let error ← errorSampler
  return assembleSquareRow secret gadget error mask

/-- Fresh uniform masks are common postprocessing: the complete row distance is at most the
translation distance of its target error. -/
theorem tvDist_fixedSecretShiftedSquareRowSampler_le_addShiftDistance
    {R : Type} [CommRing R] [SampleableType R]
    (secret : Fin 1 → R) (errorSampler : ProbComp R)
    (gadget shift : R) :
    tvDist
        (fixedSecretShiftedSquareRowSampler secret errorSampler gadget shift)
        (fixedSecretSquareRowSampler secret errorSampler gadget) ≤
      FormalProof4FHE.FiniteProduct.addShiftDistance errorSampler shift := by
  unfold fixedSecretShiftedSquareRowSampler fixedSecretSquareRowSampler
  apply tvDist_bind_left_le_const'
  intro mask
  let assemble := fun error ↦ assembleSquareRow secret gadget error mask
  calc
    tvDist
        (errorSampler >>= fun error ↦ pure (assemble (error + shift)))
        (errorSampler >>= fun error ↦ pure (assemble error)) =
      tvDist
        (assemble <$> shiftedErrorSampler errorSampler shift)
        (assemble <$> errorSampler) := by
          simp [shiftedErrorSampler, assemble, monad_norm]
    _ ≤ tvDist (shiftedErrorSampler errorSampler shift) errorSampler :=
      tvDist_map_le (m := ProbComp) assemble _ _
    _ = FormalProof4FHE.FiniteProduct.addShiftDistance errorSampler shift :=
      tvDist_shiftedErrorSampler_eq_addShiftDistance errorSampler shift

/-- A common random context may determine the secret and the correlated residual.  A
support-wise translation bound lifts to the complete row mixture without exposing that context
to the distinguisher. -/
theorem tvDist_contextualShiftedSquareRows_le
    {R Context : Type} [CommRing R] [SampleableType R]
    (contextSampler : ProbComp Context)
    (secret : Context → Fin 1 → R) (shift : Context → R)
    (errorSampler : ProbComp R) (gadget : R) (bound : ℝ)
    (hShift : ∀ context, context ∈ support contextSampler →
      FormalProof4FHE.FiniteProduct.addShiftDistance
        errorSampler (shift context) ≤ bound) :
    tvDist
        (contextSampler >>= fun context ↦
          fixedSecretShiftedSquareRowSampler
            (secret context) errorSampler gadget (shift context))
        (contextSampler >>= fun context ↦
          fixedSecretSquareRowSampler (secret context) errorSampler gadget) ≤ bound := by
  apply tvDist_bind_left_le_const
  intro context hcontext
  exact
    (tvDist_fixedSecretShiftedSquareRowSampler_le_addShiftDistance
      (secret context) errorSampler gadget (shift context)).trans
      (hShift context hcontext)

namespace Native

local instance residualRqCommRing (q degree : ℕ) :
    CommRing (RLWE.Rq q (degree + 1)) :=
  NoiseBounds.positiveRqCommRing

local instance residualRqRing (q degree : ℕ) :
    Ring (RLWE.Rq q (degree + 1)) :=
  NoiseBounds.positiveRqRing

/-- Coefficient-norm bound for the isolated shift `S * sum_i x_i e_i`. -/
theorem cInfNorm_inducedShiftFromError_le
    {q degree : ℕ} [NeZero q]
    (secret weightedSourceError : RLWE.Rq q (degree + 1))
    (secretBound weightedSourceBound : ℕ)
    (hSecret : LatticeCrypto.cInfNorm secret ≤ secretBound)
    (hWeighted : LatticeCrypto.cInfNorm weightedSourceError ≤ weightedSourceBound) :
    LatticeCrypto.cInfNorm
        (@inducedShiftFromError (RLWE.Rq q (degree + 1))
          (residualRqCommRing q degree).toMul secret weightedSourceError) ≤
      (degree + 1) * (secretBound * weightedSourceBound) := by
  unfold inducedShiftFromError
  exact (SharpRotationNoise.cInfNorm_mul_le_linear
      secret weightedSourceError).trans
    (Nat.mul_le_mul_left (degree + 1) (Nat.mul_le_mul hSecret hWeighted))

/-- Certified discrete-Gaussian absorption of one fixed compiler residual. -/
theorem tvDist_shiftedErrorSampler_discreteGaussian_le
    {q degree : ℕ} [NeZero q]
    {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (shift : RLWE.Rq q (degree + 1)) (shiftBound : ℕ)
    (hShift : LatticeCrypto.cInfNorm shift ≤ shiftBound) :
    tvDist
        (shiftedErrorSampler
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate) shift)
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate) ≤
      ((degree + 1 : ℕ) : ℝ) *
        DiscreteGaussianSampler.scalarLinearShiftBound certificate shiftBound := by
  rw [tvDist_shiftedErrorSampler_eq_addShiftDistance]
  exact DiscreteGaussianSampler.addShiftDistance_ringSampler_le_degree_mul_scalarLinearShiftBound
    (degree + 1) certificate shiftBound shift hShift

/-- The concrete fixed-source compiler residual is absorbed with the norm bound supplied by the
short-preimage analysis. -/
theorem tvDist_inducedShiftedError_discreteGaussian_le
    {q degree : ℕ} [NeZero q]
    {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (secret weightedSourceError : RLWE.Rq q (degree + 1))
    (secretBound weightedSourceBound : ℕ)
    (hSecret : LatticeCrypto.cInfNorm secret ≤ secretBound)
    (hWeighted : LatticeCrypto.cInfNorm weightedSourceError ≤ weightedSourceBound) :
    tvDist
        (shiftedErrorSampler
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
          (@inducedShiftFromError (RLWE.Rq q (degree + 1))
            (residualRqCommRing q degree).toMul secret weightedSourceError))
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate) ≤
      ((degree + 1 : ℕ) : ℝ) *
        DiscreteGaussianSampler.scalarLinearShiftBound certificate
          ((degree + 1) * (secretBound * weightedSourceBound)) := by
  apply tvDist_shiftedErrorSampler_discreteGaussian_le
  exact cInfNorm_inducedShiftFromError_le secret weightedSourceError
    secretBound weightedSourceBound hSecret hWeighted

/-- Any random compiler residual whose complete support is coefficient-bounded is absorbed by
the same certified discrete-Gaussian envelope. -/
theorem tvDist_randomShiftedError_discreteGaussian_le
    {q degree : ℕ} [NeZero q]
    {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (shiftSampler : ProbComp (RLWE.Rq q (degree + 1))) (shiftBound : ℕ)
    (hShift : ∀ shift, shift ∈ support shiftSampler →
      LatticeCrypto.cInfNorm shift ≤ shiftBound) :
    tvDist
        (randomShiftedErrorSampler shiftSampler
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate))
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate) ≤
      ((degree + 1 : ℕ) : ℝ) *
        DiscreteGaussianSampler.scalarLinearShiftBound certificate shiftBound := by
  apply tvDist_randomShiftedErrorSampler_le
  intro shift hsupport
  exact DiscreteGaussianSampler.addShiftDistance_ringSampler_le_degree_mul_scalarLinearShiftBound
    (degree + 1) certificate shiftBound shift (hShift shift hsupport)

end Native

end

end FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.ResidualSmudging
