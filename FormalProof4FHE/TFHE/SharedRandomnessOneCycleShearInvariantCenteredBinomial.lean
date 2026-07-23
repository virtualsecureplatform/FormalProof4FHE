/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SharedRandomnessOneCycleShearInvariantNoise
import FormalProof4FHE.TFHE.CenteredBinomialInstantiation
import FormalProof4FHE.TFHE.CenteredBinomialCorrectness
import FormalProof4FHE.TFHE.SharpRotationNoise
import FormalProof4FHE.TFHE.NativeShiftedCandidateEvaluator

/-!
# Centered-Binomial Shear-Invariant One-Cycle Evaluation Keys

This module instantiates the exact shear-orbit construction with the executable coefficientwise
centered-binomial ring sampler and the centered-binomial scalar KSK sampler.  The BRK uses a
hidden uniform orbit bit per TGSW entry, so its complete error vector is correlated but exactly
invariant under global-complement conjugation.  The KSK retains the ordinary independent scalar
centered-binomial law.

The result is an unconditional exact global-complement law for the complete rank-one BRK plus
shared-randomness KSK evaluation key.  It removes the earlier Gaussian translation term and does
not require wide uniform errors.  The remaining circular-security obligation is the nonlinear
relative-key evaluator.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle.SecretRandomization

noncomputable section

/-- Complete correlated rank-one TGSW error vector obtained by shear-orbit averaging IID
centered-binomial ring errors. -/
def centeredBinomialShearErrorVector
    (q degree levels ringEta : ℕ) [NeZero q] :
    ProbComp (Fin (TGSW.rowCount 1 levels) → RLWE.Rq q (degree + 1)) :=
  rankOneShearSymmetrizedIIDErrorVector
    (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
    (embedBinaryPolynomial q (degree + 1) (allTruePolynomial (degree + 1)))

/-- The centered-binomial orbit sampler is exactly complement-shear invariant. -/
theorem centeredBinomialShearErrorVector_invariant
    (q degree levels ringEta : ℕ) [NeZero q] :
    RankOneComplementErrorVectorInvariant
      (centeredBinomialShearErrorVector q degree levels ringEta)
      (embedBinaryPolynomial q (degree + 1)
        (allTruePolynomial (degree + 1))) :=
  rankOneShearSymmetrizedIIDErrorVector_invariant _ _

/-- The all-one complement offset has coefficient infinity norm at most one. -/
theorem cInfNorm_embedBinaryPolynomial_allTrue_le_one
    {q degree : ℕ} [NeZero q] :
    LatticeCrypto.cInfNorm
      (embedBinaryPolynomial q (degree + 1) (allTruePolynomial (degree + 1))) ≤ 1 := by
  apply LatticeCrypto.cInfNorm_le_of_coeff_le
  intro coefficient
  have hcoefficient :
      (embedBinaryPolynomial q (degree + 1)
        (allTruePolynomial (degree + 1))).get coefficient = 1 := by
    change (LatticeCrypto.Poly.toPi
      (LatticeCrypto.Poly.ofPi (fun _ : Fin (degree + 1) ↦ (1 : ZMod q))))
        coefficient = 1
    rw [LatticeCrypto.Poly.toPi_ofPi]
  rw [hcoefficient]
  simpa using NoiseBounds.centeredRepr_natCast_natAbs_le (q := q) 1

/-- Orbit symmetrization preserves a polynomial narrowness bound.  Every resulting row has norm
at most `(degree + 2) * ringEta`; this covers both the untouched IID branch and the sheared branch.
The estimate uses the linear negacyclic convolution bound. -/
theorem centeredBinomialShearErrorVector_cInfNorm_le
    {q degree levels ringEta : ℕ} [NeZero q]
    {errors : Fin (TGSW.rowCount 1 levels) → RLWE.Rq q (degree + 1)}
    (herrors : errors ∈ support
      (centeredBinomialShearErrorVector q degree levels ringEta))
    (row : Fin (TGSW.rowCount 1 levels)) :
    LatticeCrypto.cInfNorm (errors row) ≤
      ringEta + (degree + 1) * ringEta := by
  unfold centeredBinomialShearErrorVector
    rankOneShearSymmetrizedIIDErrorVector
    rankOneShearSymmetrizedErrorVector at herrors
  obtain ⟨baseErrors, hbaseErrors, hcase⟩ :=
    mem_support_involutiveSymmetrization_cases
      (rankOneComplementErrorShear
        (embedBinaryPolynomial q (degree + 1)
          (allTruePolynomial (degree + 1))))
      (ProbComp.sampleIID (TGSW.rowCount 1 levels)
        (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)) herrors
  have hbase (baseRow : Fin (TGSW.rowCount 1 levels)) :
      LatticeCrypto.cInfNorm (baseErrors baseRow) ≤ ringEta := by
    apply CenteredBinomialCorrectness.cInfNorm_le_eta_of_mem_support
    apply FormalProof4FHE.FiniteProduct.mem_support_fin_mOfFn_apply
      (TGSW.rowCount 1 levels)
      (fun _ ↦ RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
      baseErrors hbaseErrors baseRow
  rcases hcase with hplain | hsheared
  · subst errors
    exact (hbase row).trans (Nat.le_add_right _ _)
  · subst errors
    by_cases hmask : (TGSW.rowIndex row).1 = 0
    · rw [rankOne_row_eq_maskRow_of_index_eq_zero row hmask]
      simp only [rankOneComplementErrorShear_maskRow]
      refine (NoiseBounds.cInfNorm_add_le _ _).trans ?_
      apply Nat.add_le_add (hbase (rankOneMaskRow (TGSW.rowIndex row).2))
      refine (SharpRotationNoise.cInfNorm_mul_le_linear _ _).trans ?_
      apply Nat.mul_le_mul_left (degree + 1)
      simpa using Nat.mul_le_mul
        (cInfNorm_embedBinaryPolynomial_allTrue_le_one
          (q := q) (degree := degree))
        (hbase (rankOneBodyRow (TGSW.rowIndex row).2))
    · rw [rankOne_row_eq_bodyRow_of_index_ne_zero row hmask]
      simp only [rankOneComplementErrorShear_bodyRow]
      change LatticeCrypto.cInfNorm
        (FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.proofNeg
          (baseErrors (rankOneBodyRow (TGSW.rowIndex row).2))) ≤ _
      let bodyError := baseErrors (rankOneBodyRow (TGSW.rowIndex row).2)
      have hnorm : LatticeCrypto.cInfNorm
          (FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.proofNeg bodyError) =
          LatticeCrypto.cInfNorm bodyError :=
        (congrArg LatticeCrypto.cInfNorm
          (FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.proofNeg_eq_neg
            bodyError)).trans (LatticeCrypto.cInfNorm_neg bodyError)
      calc
        _ = LatticeCrypto.cInfNorm bodyError := hnorm
        _ ≤ ringEta := hbase _
        _ ≤ _ := Nat.le_add_right _ _

/-- The complete centered-binomial BRK plus shared-randomness KSK distribution transports
exactly under global complement. -/
theorem globalComplementEvaluationKeyPair_centeredBinomialShear_evalDist
    {q degree tgswLevels lweDimension sourceDimension keySwitchLevels : ℕ}
    [NeZero q]
    (ringEta keySwitchEta : ℕ)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (lweSecret : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret 1 (degree + 1))
    (sourceSecret : BinarySecret sourceDimension) :
    let offset :=
      embedBinaryPolynomial q (degree + 1) (allTruePolynomial (degree + 1))
    let ringErrorVectorSampler :=
      centeredBinomialShearErrorVector q degree tgswLevels ringEta
    evalDist (globalComplementEvaluationKeyPair offset
        tgswGadget keySwitchGadget <$>
      (do
        let bootstrappingKey ←
          generateBootstrappingKeyWithErrorVector q degree tgswLevels
            lweDimension ringErrorVectorSampler tgswGadget lweSecret ringSecret
        let keySwitchKey ←
          Native.generateKeySwitchKey q lweDimension sourceDimension
            keySwitchLevels (CenteredBinomial.scalarSampler q keySwitchEta)
              keySwitchGadget sourceSecret lweSecret
        return (bootstrappingKey, keySwitchKey))) =
      evalDist (do
        let bootstrappingKey ←
          generateBootstrappingKeyWithErrorVector q degree tgswLevels
            lweDimension ringErrorVectorSampler tgswGadget
              (globalComplementAction lweSecret true)
              (maskedRingSecret ringSecret
                (fun _ _ ↦ true : RingBinarySecret 1 (degree + 1)))
        let keySwitchKey ←
          Native.generateKeySwitchKey q lweDimension sourceDimension
            keySwitchLevels (CenteredBinomial.scalarSampler q keySwitchEta)
              keySwitchGadget
              (globalComplementAction sourceSecret true)
              (globalComplementAction lweSecret true)
        return (bootstrappingKey, keySwitchKey)) := by
  dsimp only
  apply globalComplementEvaluationKeyPair_generateWithErrorVector_evalDist
  · exact centeredBinomialShearErrorVector_invariant q degree tgswLevels ringEta
  · exact CenteredBinomial.scalar_probOutput_neg q keySwitchEta

end

end FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle.SecretRandomization
