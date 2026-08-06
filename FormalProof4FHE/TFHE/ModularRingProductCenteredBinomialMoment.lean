/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.RingProductCenteredBinomialMoment

open OracleComp
open scoped BigOperators

/-!
# Executable Modular CBD Ring-Product Moment

This file transfers the real independent-CBD negacyclic coefficient calculation to the actual
product of two executable `Rq` samples.  The deterministic bridge exposes both required no-wrap
conditions: scalar CBD coefficients must satisfy `2 eta < q`, and the complete convolution must
satisfy `2 * (N * eta^2) < q`.
-/

namespace FormalProof4FHE.TFHE.ModularRingProductCenteredBinomialMoment
noncomputable section

open FormalProof4FHE.BoundedMoment
open FormalProof4FHE.RLWE.CenteredBinomial
open FormalProof4FHE.TFHE.RingProductCenteredBinomialMoment
open FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.CenteredBinomialAnchorMoment

attribute [local instance] FormalProof4FHE.TFHE.NoiseBounds.positiveRqCommRing
  FormalProof4FHE.TFHE.NoiseBounds.positiveRqRing

abbrev Ring (q degree : ℕ) := FormalProof4FHE.RLWE.Rq q (degree + 1)

def productIntegerSum (q degree : ℕ) [NeZero q]
    (output : Fin (degree + 1)) (left right : Ring q degree) : ℤ :=
  ∑ input : Fin (degree + 1),
    if input.val ≤ output.val then
      LatticeCrypto.centeredRepr (left.get input) *
        LatticeCrypto.centeredRepr
          (right.get (FormalProof4FHE.TFHE.SharpRotationNoise.sourceIndex input output))
    else
      -(LatticeCrypto.centeredRepr (left.get input) *
        LatticeCrypto.centeredRepr
          (right.get (FormalProof4FHE.TFHE.SharpRotationNoise.sourceIndex input output)))

theorem productIntegerSum_natAbs_le
    (q degree eta : ℕ) [NeZero q]
    (output : Fin (degree + 1)) {left right : Ring q degree}
    (hleft : left ∈ support (sampler q (degree + 1) eta))
    (hright : right ∈ support (sampler q (degree + 1) eta))
    (hCoefficientNoWrap : 2 * eta < q) :
    (productIntegerSum q degree output left right).natAbs ≤
      (degree + 1) * eta ^ 2 := by
  unfold productIntegerSum
  calc
    (∑ input : Fin (degree + 1),
        if input.val ≤ output.val then
          LatticeCrypto.centeredRepr (left.get input) *
            LatticeCrypto.centeredRepr
              (right.get (FormalProof4FHE.TFHE.SharpRotationNoise.sourceIndex input output))
        else
          -(LatticeCrypto.centeredRepr (left.get input) *
            LatticeCrypto.centeredRepr
              (right.get (FormalProof4FHE.TFHE.SharpRotationNoise.sourceIndex input output)))).natAbs ≤
      ∑ input : Fin (degree + 1),
        (if input.val ≤ output.val then
          LatticeCrypto.centeredRepr (left.get input) *
            LatticeCrypto.centeredRepr
              (right.get (FormalProof4FHE.TFHE.SharpRotationNoise.sourceIndex input output))
        else
          -(LatticeCrypto.centeredRepr (left.get input) *
            LatticeCrypto.centeredRepr
              (right.get (FormalProof4FHE.TFHE.SharpRotationNoise.sourceIndex input output)))).natAbs := by
          exact Int.natAbs_sum_le _ _
    _ ≤ ∑ _input : Fin (degree + 1), eta ^ 2 := by
      apply Finset.sum_le_sum
      intro input _
      split
      · rw [Int.natAbs_mul]
        simpa [pow_two] using Nat.mul_le_mul
          (centeredRepr_get_natAbs_le_of_mem_support hleft input hCoefficientNoWrap)
          (centeredRepr_get_natAbs_le_of_mem_support hright _ hCoefficientNoWrap)
      · rw [Int.natAbs_neg, Int.natAbs_mul]
        simpa [pow_two] using Nat.mul_le_mul
          (centeredRepr_get_natAbs_le_of_mem_support hleft input hCoefficientNoWrap)
          (centeredRepr_get_natAbs_le_of_mem_support hright _ hCoefficientNoWrap)
    _ = (degree + 1) * eta ^ 2 := by simp

theorem ringCoefficientLift_mul_eq_realNegacyclicProductCoefficient
    (q degree eta : ℕ) [NeZero q]
    (output : Fin (degree + 1)) {left right : Ring q degree}
    (hleft : left ∈ support (sampler q (degree + 1) eta))
    (hright : right ∈ support (sampler q (degree + 1) eta))
    (hCoefficientNoWrap : 2 * eta < q)
    (hProductNoWrap : 2 * ((degree + 1) * eta ^ 2) < q) :
    ringCoefficientLift q output (left * right) =
      realNegacyclicProductCoefficient output
        (coefficientVector left, coefficientVector right) := by
  let integerSum := productIntegerSum q degree output left right
  have hterm (input : Fin (degree + 1)) :
      (if input.val ≤ output.val then
          left.get input *
            right.get (FormalProof4FHE.TFHE.SharpRotationNoise.sourceIndex input output)
        else
          -(left.get input *
            right.get (FormalProof4FHE.TFHE.SharpRotationNoise.sourceIndex input output))) =
        ((if input.val ≤ output.val then
            LatticeCrypto.centeredRepr (left.get input) *
              LatticeCrypto.centeredRepr
                (right.get (FormalProof4FHE.TFHE.SharpRotationNoise.sourceIndex input output))
          else
            -(LatticeCrypto.centeredRepr (left.get input) *
              LatticeCrypto.centeredRepr
                (right.get (FormalProof4FHE.TFHE.SharpRotationNoise.sourceIndex input output))) : ℤ) :
          ZMod q) := by
    have hleftCast := LatticeCrypto.centeredRepr_intCast (left.get input)
    have hrightCast := LatticeCrypto.centeredRepr_intCast
      (right.get (FormalProof4FHE.TFHE.SharpRotationNoise.sourceIndex input output))
    have hmulCast :
        left.get input *
            right.get (FormalProof4FHE.TFHE.SharpRotationNoise.sourceIndex input output) =
          ((LatticeCrypto.centeredRepr (left.get input) *
            LatticeCrypto.centeredRepr
              (right.get (FormalProof4FHE.TFHE.SharpRotationNoise.sourceIndex input output)) : ℤ) :
            ZMod q) := by
      calc
        _ = ((LatticeCrypto.centeredRepr (left.get input) : ℤ) : ZMod q) *
            ((LatticeCrypto.centeredRepr
              (right.get (FormalProof4FHE.TFHE.SharpRotationNoise.sourceIndex input output)) : ℤ) :
                ZMod q) := congrArg₂ (fun x y : ZMod q => x * y) hleftCast hrightCast
        _ = _ := by push_cast; rfl
    split
    · exact hmulCast
    · simpa using congrArg Neg.neg hmulCast
  have hmul :
      (left * right).get output =
        LatticeCrypto.negacyclicConvCoeff
          (fun input => left.get input) (fun input => right.get input) output :=
    FormalProof4FHE.TFHE.NoiseBounds.mul_coefficient left right output
  have hproductCast : (left * right).get output = (integerSum : ZMod q) := by
    rw [hmul, FormalProof4FHE.TFHE.SharpRotationNoise.negacyclicConvCoeff_eq_sum_source]
    simp_rw [hterm]
    unfold integerSum productIntegerSum
    push_cast
    rfl
  have hbound : integerSum.natAbs ≤ (degree + 1) * eta ^ 2 :=
    productIntegerSum_natAbs_le q degree eta output hleft hright hCoefficientNoWrap
  unfold ringCoefficientLift centeredCoefficientLift
  rw [hproductCast,
    LatticeCrypto.centeredRepr_intCast_eq_of_natAbs_le
      integerSum hbound hProductNoWrap]
  unfold realNegacyclicProductCoefficient weightedSum signedLeftWeight
    sourceIndexTableEquiv coefficientVector integerSum productIntegerSum
  simp only [centeredCoefficientLift, Equiv.coe_fn_mk]
  push_cast
  apply Finset.sum_congr rfl
  intro input _
  split <;> ring

def independentRingPairSampler (q degree eta : ℕ) [NeZero q] :
    ProbComp (Ring q degree × Ring q degree) := do
  let left ← sampler q (degree + 1) eta
  let right ← sampler q (degree + 1) eta
  return (left, right)

def modularRingProductCoefficient (q : ℕ) [NeZero q] {degree : ℕ}
    (output : Fin (degree + 1)) (pair : Ring q degree × Ring q degree) : ℝ :=
  ringCoefficientLift q output (pair.1 * pair.2)

theorem expectation_sampler_sum_ringCoefficientLift_sq
    (q degree eta : ℕ) [NeZero q] (hCoefficientNoWrap : 2 * eta < q) :
    expectation (sampler q (degree + 1) eta)
        (fun error => ∑ coefficient,
          ringCoefficientLift q coefficient error ^ 2) =
      ((degree + 1 : ℕ) : ℝ) * ((eta : ℝ) / 2) := by
  calc
    _ = expectation
        (coefficientVector <$> sampler q (degree + 1) eta)
        (fun values => ∑ coefficient,
          centeredCoefficientLift q (values coefficient) ^ 2) := by
            rw [expectation_map]
            rfl
    _ = expectation
        (ProbComp.sampleIID (degree + 1) (coefficientSampler q eta))
        (fun values => ∑ coefficient,
          centeredCoefficientLift q (values coefficient) ^ 2) :=
      expectation_congr_evalDist
        (coefficientVector_sampler_evalDist q (degree + 1) eta)
        (fun values => ∑ coefficient,
          centeredCoefficientLift q (values coefficient) ^ 2)
    _ = ((degree + 1 : ℕ) : ℝ) * ((eta : ℝ) / 2) :=
      expectation_sampleIID_sum_sq q eta (degree + 1) hCoefficientNoWrap

theorem secondMoment_modularRingProductCoefficient
    (q degree eta : ℕ) [NeZero q] (output : Fin (degree + 1))
    (hCoefficientNoWrap : 2 * eta < q)
    (hProductNoWrap : 2 * ((degree + 1) * eta ^ 2) < q) :
    secondMoment (independentRingPairSampler q degree eta)
        (modularRingProductCoefficient q output) =
      ((degree + 1 : ℕ) : ℝ) * ((eta : ℝ) / 2) ^ 2 := by
  unfold secondMoment independentRingPairSampler
  rw [expectation_bind]
  have hinner (left : Ring q degree)
      (hleft : left ∈ support (sampler q (degree + 1) eta)) :
      expectation
          (sampler q (degree + 1) eta >>= fun right => pure (left, right))
          (fun pair => modularRingProductCoefficient q output pair ^ 2) =
        ((eta : ℝ) / 2) *
          ∑ input, ringCoefficientLift q input left ^ 2 := by
    calc
      _ = expectation (sampler q (degree + 1) eta)
          (fun right => realNegacyclicProductCoefficient output
            (coefficientVector left, coefficientVector right) ^ 2) := by
              rw [expectation_bind]
              apply Finset.sum_congr rfl
              intro right _
              rw [expectation_pure]
              simp only [modularRingProductCoefficient]
              by_cases hright : right ∈ support (sampler q (degree + 1) eta)
              · rw [ringCoefficientLift_mul_eq_realNegacyclicProductCoefficient
                  q degree eta output hleft hright hCoefficientNoWrap hProductNoWrap]
              · rw [probOutput_eq_zero_of_not_mem_support hright,
                  ENNReal.toReal_zero, zero_mul, zero_mul]
      _ = secondMoment
          (permutedCoefficientVector output <$> sampler q (degree + 1) eta)
          (weightedSum (signedLeftWeight output (coefficientVector left))
            (centeredCoefficientLift q)) := by
              rw [secondMoment_map]
              rfl
      _ = secondMoment
          (ProbComp.sampleIID (degree + 1) (coefficientSampler q eta))
          (weightedSum (signedLeftWeight output (coefficientVector left))
            (centeredCoefficientLift q)) := by
              apply secondMoment_congr_evalDist
              exact permutedCoefficientVector_sampler_evalDist q degree eta output
      _ = ((eta : ℝ) / 2) * ∑ input,
          signedLeftWeight output (coefficientVector left) input ^ 2 := by
            exact secondMoment_sampleIID_coefficientSampler_weightedSum
              q eta (degree + 1)
                (signedLeftWeight output (coefficientVector left)) hCoefficientNoWrap
      _ = ((eta : ℝ) / 2) *
          ∑ input, ringCoefficientLift q input left ^ 2 := by
            congr 1
            apply Finset.sum_congr rfl
            intro input _
            rw [signedLeftWeight_sq]
            rfl
  calc
    (∑ left,
        Pr[= left | sampler q (degree + 1) eta].toReal *
          expectation
            (sampler q (degree + 1) eta >>= fun right => pure (left, right))
            (fun pair => modularRingProductCoefficient q output pair ^ 2)) =
      ∑ left,
        Pr[= left | sampler q (degree + 1) eta].toReal *
          (((eta : ℝ) / 2) *
            ∑ input, ringCoefficientLift q input left ^ 2) := by
              apply Finset.sum_congr rfl
              intro left _
              by_cases hleft : left ∈ support (sampler q (degree + 1) eta)
              · rw [hinner left hleft]
              · rw [probOutput_eq_zero_of_not_mem_support hleft, ENNReal.toReal_zero,
                  zero_mul, zero_mul]
    _ = expectation (sampler q (degree + 1) eta)
        (fun left => ((eta : ℝ) / 2) *
          ∑ input, ringCoefficientLift q input left ^ 2) := by rfl
    _ = ((eta : ℝ) / 2) *
        expectation (sampler q (degree + 1) eta)
          (fun left => ∑ input, ringCoefficientLift q input left ^ 2) :=
      expectation_const_mul _ _ _
    _ = ((eta : ℝ) / 2) *
        (((degree + 1 : ℕ) : ℝ) * ((eta : ℝ) / 2)) := by
      rw [expectation_sampler_sum_ringCoefficientLift_sq
        q degree eta hCoefficientNoWrap]
    _ = ((degree + 1 : ℕ) : ℝ) * ((eta : ℝ) / 2) ^ 2 := by ring

theorem modularRingProductCoefficient_tail
    (q degree eta : ℕ) [NeZero q] (output : Fin (degree + 1))
    (hCoefficientNoWrap : 2 * eta < q)
    (hProductNoWrap : 2 * ((degree + 1) * eta ^ 2) < q)
    (threshold : ℝ) (hthreshold : 0 < threshold) :
    Pr[(fun pair => threshold ^ 2 ≤
          modularRingProductCoefficient q output pair ^ 2) |
        independentRingPairSampler q degree eta].toReal ≤
      (((degree + 1 : ℕ) : ℝ) * ((eta : ℝ) / 2) ^ 2) /
        threshold ^ 2 := by
  rw [← secondMoment_modularRingProductCoefficient q degree eta output
    hCoefficientNoWrap hProductNoWrap]
  exact probEvent_sq_ge_toReal_le _ _ threshold hthreshold

theorem modularRingProduct_allCoefficients_tail
    (q degree eta : ℕ) [NeZero q]
    (hCoefficientNoWrap : 2 * eta < q)
    (hProductNoWrap : 2 * ((degree + 1) * eta ^ 2) < q)
    (threshold : ℝ) (hthreshold : 0 < threshold) :
    Pr[(fun pair => ∃ output : Fin (degree + 1), threshold ^ 2 ≤
          modularRingProductCoefficient q output pair ^ 2) |
        independentRingPairSampler q degree eta].toReal ≤
      (((degree + 1 : ℕ) : ℝ) ^ 2 * ((eta : ℝ) / 2) ^ 2) /
        threshold ^ 2 := by
  let ringSampler := independentRingPairSampler q degree eta
  let event : Fin (degree + 1) → (Ring q degree × Ring q degree) → Prop :=
    fun output pair => threshold ^ 2 ≤ modularRingProductCoefficient q output pair ^ 2
  have hunion :
      Pr[(fun pair => ∃ output : Fin (degree + 1), event output pair) | ringSampler] ≤
        ∑ output : Fin (degree + 1), Pr[event output | ringSampler] := by
    simpa only [Finset.mem_univ, true_and] using
      (probEvent_exists_finset_le_sum
        (Finset.univ : Finset (Fin (degree + 1))) ringSampler event)
  have hsumNeTop :
      (∑ output : Fin (degree + 1), Pr[event output | ringSampler]) ≠ ⊤ := by
    exact ENNReal.sum_ne_top.mpr (fun _ _ => probEvent_ne_top)
  have hreal := ENNReal.toReal_mono hsumNeTop hunion
  have htoRealSum :
      (∑ output : Fin (degree + 1), Pr[event output | ringSampler]).toReal =
        ∑ output : Fin (degree + 1), Pr[event output | ringSampler].toReal := by
    rw [ENNReal.toReal_sum]
    intro _ _
    exact probEvent_ne_top
  rw [htoRealSum] at hreal
  calc
    _ ≤ ∑ _output : Fin (degree + 1),
        (((degree + 1 : ℕ) : ℝ) * ((eta : ℝ) / 2) ^ 2) /
          threshold ^ 2 := by
      refine hreal.trans (Finset.sum_le_sum ?_)
      intro output _
      exact modularRingProductCoefficient_tail q degree eta output
        hCoefficientNoWrap hProductNoWrap threshold hthreshold
    _ = _ := by simp; ring

end
end FormalProof4FHE.TFHE.ModularRingProductCenteredBinomialMoment
