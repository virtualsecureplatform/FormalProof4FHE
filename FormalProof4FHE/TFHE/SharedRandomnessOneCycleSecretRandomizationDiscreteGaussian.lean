/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SharedRandomnessOneCycleSecretRandomization
import FormalProof4FHE.TFHE.NativeShiftedDiscreteGaussianBounds
import FormalProof4FHE.TFHE.SymmetricDiscreteGaussianSampler

/-!
# Discrete-Gaussian Bound for the One-Cycle Complement Shear

This module instantiates the quantitative rank-one BRK complement theorem with the repository's
certified executable modular discrete-Gaussian sampler.  Exact ticket-count symmetry removes the
body-row negation.  The remaining mask-row translation is controlled by the existing certified
Gaussian shift estimate.

The endpoint uses the universal centered-norm bound `q / 2` for the product of the all-one offset
with an arbitrary body error.  It is therefore unconditional for a symmetric certificate but
deliberately conservative.  The displayed loss becomes negligible only when the certified
Gaussian width and table-approximation error make that explicit expression negligible; this file
does not claim that the standard narrow TFHE parameters do so.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle.SecretRandomization

noncomputable section

open FormalProof4FHE.TFHE

/- The executable `Rq` carrier has several definitionally different algebra dictionaries.  Use
the proof-facing commutative-ring dictionary required by the generic shear theorem and bridge its
operations to the executable negacyclic implementation below. -/
local instance rqCommRingForComplementShear (q degree : ℕ) :
    CommRing (RLWE.Rq q degree) :=
  LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree

local instance rqAddForComplementShear (q degree : ℕ) : Add (RLWE.Rq q degree) :=
  (LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree).toAdd

local instance rqMulForComplementShear (q degree : ℕ) : Mul (RLWE.Rq q degree) :=
  (LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree).toMul

local instance rqNegForComplementShear (q degree : ℕ) : Neg (RLWE.Rq q degree) :=
  (LatticeCrypto.vectorNegacyclicRing_instCommRing
    (ZMod q) degree).toAddCommGroup.toNeg

/-- Proof-facing and executable negacyclic multiplication agree extensionally. -/
theorem rqProofMul_eq_executable {q degree : ℕ}
    (left right : RLWE.Rq q degree) :
    @Mul.mul (RLWE.Rq q degree)
        (LatticeCrypto.vectorNegacyclicRing_instCommRing
          (ZMod q) degree).toMul left right =
      @Mul.mul (RLWE.Rq q degree)
        (RLWE.negacyclicRing q degree).instMulPoly left right := by
  apply (Native.CoefficientStructuredLWE.coefficientEquiv q degree).injective
  rw [Native.CoefficientStructuredLWE.coefficientEquiv_semiring_mul]
  exact (Native.CoefficientStructuredLWE.coefficientEquiv_mul
    q degree left right).symm

/-- A symmetric certified discrete-Gaussian ring sampler has complement-shear defect at most
`levels * degree` times its certified scalar translation cost at the universal shift `q / 2`. -/
theorem rankOneComplementNoiseDistance_discreteGaussian_le
    {q degree levels : ℕ} [NeZero q]
    {alpha : ℝ} {halpha : 0 < alpha}
    (certificate :
      DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (hsymmetric : DiscreteGaussianSampler.TicketNegationSymmetric certificate)
    (offset : RLWE.Rq q degree) :
    rankOneComplementNoiseDistance (levels := levels)
        (DiscreteGaussianSampler.ringSampler degree certificate) offset ≤
      (levels : ℝ) *
        ((degree : ℝ) *
          DiscreteGaussianSampler.scalarLinearShiftBound certificate (q / 2)) := by
  apply rankOneComplementNoiseDistance_le_mul_addShiftDistance
  · have hexecutable := DiscreteGaussianSampler.ringSampler_negationSymmetric
      degree certificate hsymmetric
    intro error
    change Pr[= Native.ShiftedCandidateEvaluator.proofNeg error |
        DiscreteGaussianSampler.ringSampler degree certificate] = _
    rw [Native.ShiftedCandidateEvaluator.proofNeg_eq_neg]
    exact hexecutable error
  · intro error
    change FormalProof4FHE.FiniteProduct.addShiftDistance
        (DiscreteGaussianSampler.ringSampler degree certificate)
        (@Mul.mul (RLWE.Rq q degree)
          (LatticeCrypto.vectorNegacyclicRing_instCommRing
            (ZMod q) degree).toMul offset error) ≤ _
    rw [rqProofMul_eq_executable]
    rw [Native.ConditionalSmudging.addShiftDistance_rq_eq_executable]
    let executableShift : RLWE.Rq q degree :=
      @Mul.mul (RLWE.Rq q degree)
        (RLWE.negacyclicRing q degree).instMulPoly offset error
    exact
      DiscreteGaussianSampler.addShiftDistance_ringSampler_le_degree_mul_scalarLinearShiftBound
        degree certificate (q / 2) executableShift
          (LatticeCrypto.cInfNorm_le_halfq executableShift)

/-- Joint BRK+KSK global-complement theorem with a fully explicit certified discrete-Gaussian
BRK loss.  The negation-symmetric KSK remains exact and contributes no statistical term. -/
theorem globalComplementEvaluationKeyPair_discreteGaussian_tvDist_le
    {q degree tgswLevels lweDimension sourceDimension keySwitchLevels : ℕ}
    [NeZero q]
    {alpha : ℝ} {halpha : 0 < alpha}
    (ringCertificate :
      DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (hringSymmetric :
      DiscreteGaussianSampler.TicketNegationSymmetric ringCertificate)
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret 1 (degree + 1))
    (sourceSecret : BinarySecret sourceDimension)
    (hkeySwitchNoise :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        keySwitchErrorSampler) :
    tvDist (globalComplementEvaluationKeyPair
        (embedBinaryPolynomial q (degree + 1) (allTruePolynomial (degree + 1)))
        tgswGadget keySwitchGadget <$>
      (do
        let bootstrappingKey ←
          Native.generateBootstrappingKey q (degree + 1) 1 tgswLevels
            lweDimension
            (DiscreteGaussianSampler.ringSampler (degree + 1) ringCertificate)
            tgswGadget lweSecret ringSecret
        let keySwitchKey ←
          Native.generateKeySwitchKey q lweDimension sourceDimension
            keySwitchLevels keySwitchErrorSampler keySwitchGadget sourceSecret
              lweSecret
        return (bootstrappingKey, keySwitchKey)))
      (do
        let bootstrappingKey ←
          Native.generateBootstrappingKey q (degree + 1) 1 tgswLevels
            lweDimension
            (DiscreteGaussianSampler.ringSampler (degree + 1) ringCertificate)
            tgswGadget (globalComplementAction lweSecret true)
              (maskedRingSecret ringSecret
                (fun _ _ ↦ true : RingBinarySecret 1 (degree + 1)))
        let keySwitchKey ←
          Native.generateKeySwitchKey q lweDimension sourceDimension
            keySwitchLevels keySwitchErrorSampler keySwitchGadget
              (globalComplementAction sourceSecret true)
              (globalComplementAction lweSecret true)
        return (bootstrappingKey, keySwitchKey)) ≤
      (lweDimension : ℝ) *
        ((tgswLevels : ℝ) *
          (((degree + 1 : ℕ) : ℝ) *
            DiscreteGaussianSampler.scalarLinearShiftBound
              ringCertificate (q / 2))) := by
  calc
    _ ≤ (lweDimension : ℝ) *
        rankOneComplementNoiseDistance (levels := tgswLevels)
          (DiscreteGaussianSampler.ringSampler (degree + 1) ringCertificate)
          (embedBinaryPolynomial q (degree + 1)
            (allTruePolynomial (degree + 1))) :=
      globalComplementEvaluationKeyPair_generate_tvDist_le
        (DiscreteGaussianSampler.ringSampler (degree + 1) ringCertificate)
        keySwitchErrorSampler tgswGadget keySwitchGadget lweSecret ringSecret
        sourceSecret hkeySwitchNoise
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (rankOneComplementNoiseDistance_discreteGaussian_le
        ringCertificate hringSymmetric
          (embedBinaryPolynomial q (degree + 1)
            (allTruePolynomial (degree + 1))))
      (Nat.cast_nonneg lweDimension)

end

end FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle.SecretRandomization
