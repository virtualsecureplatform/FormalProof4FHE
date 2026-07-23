/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.CenteredBinomialMoment
import FormalProof4FHE.TFHE.RingSquareBinaryAnchoredResidual
import FormalProof4FHE.TFHE.SharpRotationNoise

/-!
# Centered-Binomial Moment of the Anchored `RGSW_S(-S)` Residual

For a fixed nonzero binary ring secret `S`, every coefficient of `S * e` is a signed permutation
weighted sum of the independent coefficients of a fresh centered-binomial error `e`.  When the
complete convolution stays inside the centered interval, its second moment is therefore

`(eta / 2) * HammingWeight(S)`,

and in particular at least `eta / 2`.  Combined with the anchored-selector normal form, this
shows that enlarging the source pool cannot make the native hidden residual statistically
negligible in the ordinary correctness-compatible no-wrap regime.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler

noncomputable section

open BinaryPreimageExistence
open BinarySelectorSecurity
open FormalProof4FHE.BoundedMoment

namespace CenteredBinomialAnchorMoment

open FormalProof4FHE.RLWE.CenteredBinomial

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing

abbrev Ring (q degree : ℕ) := RLWE.Rq q (degree + 1)

/-! ## The negacyclic source-coordinate permutation -/

/-- At a fixed output coefficient, the negacyclic source-index map is an involution. -/
theorem sourceIndex_involutive {degree : ℕ} (output : Fin (degree + 1)) :
    Function.Involutive
      (fun input ↦ SharpRotationNoise.sourceIndex input output) := by
  intro input
  have hmod := SharpRotationNoise.add_sourceIndex_mod input output
  have hmod' :
      ((SharpRotationNoise.sourceIndex input output).val + input.val) %
          (degree + 1) = output.val := by
    simpa [Nat.add_comm] using hmod
  exact (SharpRotationNoise.eq_sourceIndex_of_add_mod_eq
    (SharpRotationNoise.sourceIndex input output) input output hmod').symm

/-- The source-index involution bundled as a finite equivalence. -/
def sourceIndexEquiv {degree : ℕ} (output : Fin (degree + 1)) :
    Fin (degree + 1) ≃ Fin (degree + 1) where
  toFun input := SharpRotationNoise.sourceIndex input output
  invFun input := SharpRotationNoise.sourceIndex input output
  left_inv := sourceIndex_involutive output
  right_inv := sourceIndex_involutive output

/-- Reindex a coefficient table by the fixed-output source permutation. -/
def sourceIndexTableEquiv (A : Type) {degree : ℕ}
    (output : Fin (degree + 1)) :
    (Fin (degree + 1) → A) ≃ (Fin (degree + 1) → A) where
  toFun values input :=
    values (SharpRotationNoise.sourceIndex input output)
  invFun values input :=
    values (SharpRotationNoise.sourceIndex input output)
  left_inv values := by
    funext input
    exact congrArg values (sourceIndex_involutive output input)
  right_inv values := by
    funext input
    exact congrArg values (sourceIndex_involutive output input)

/-- An IID vector is invariant under the negacyclic source-coordinate permutation. -/
theorem sourceIndexTableEquiv_sampleIID_evalDist
    {A : Type} [Finite A] {degree : ℕ}
    (sampler : ProbComp A) (output : Fin (degree + 1)) :
    evalDist
        (sourceIndexTableEquiv A output <$>
          ProbComp.sampleIID (degree + 1) sampler) =
      evalDist (ProbComp.sampleIID (degree + 1) sampler) := by
  letI : Fintype A := Fintype.ofFinite A
  letI : DecidableEq A := Classical.decEq A
  apply evalDist_ext
  intro values
  rw [probOutput_map_equiv]
  simp only [ProbComp.sampleIID,
    FormalProof4FHE.FiniteProduct.probOutput_fin_mOfFn]
  change
    (∏ input,
        Pr[= values (SharpRotationNoise.sourceIndex input output) | sampler]) =
      ∏ input, Pr[= values input | sampler]
  apply Fintype.prod_equiv (sourceIndexEquiv output)
  intro input
  rfl

/-! ## Signed binary convolution row -/

/-- Integer coefficient multiplying one permuted error coordinate in a binary-secret
negacyclic convolution row. -/
def binaryWeightInt {degree : ℕ}
    (secret : Fin (degree + 1) → Bool) (output input : Fin (degree + 1)) : ℤ :=
  if input.val ≤ output.val then
    if secret input then 1 else 0
  else
    -(if secret input then 1 else 0)

/-- Real form of the signed binary convolution weight. -/
def binaryWeightReal {degree : ℕ}
    (secret : Fin (degree + 1) → Bool) (output input : Fin (degree + 1)) : ℝ :=
  (binaryWeightInt secret output input : ℝ)

/-- Coefficients of an error, permuted into the order used by one negacyclic convolution row. -/
def permutedCoefficientVector {q degree : ℕ}
    (output : Fin (degree + 1)) (error : Ring q degree) :
    Fin (degree + 1) → ZMod q :=
  fun input ↦ error.get (SharpRotationNoise.sourceIndex input output)

/-- The permuted coefficient vector of a centered-binomial ring error remains an IID vector of
centered-binomial scalar coefficients. -/
theorem permutedCoefficientVector_sampler_evalDist
    (q degree eta : ℕ) [NeZero q] (output : Fin (degree + 1)) :
    evalDist
        (permutedCoefficientVector output <$>
          sampler q (degree + 1) eta) =
      evalDist
        (ProbComp.sampleIID (degree + 1) (coefficientSampler q eta)) := by
  have hCoefficients := coefficientVector_sampler_evalDist
    q (degree + 1) eta
  have hReindex := evalDist_map_eq_of_evalDist_eq hCoefficients
    (sourceIndexTableEquiv (ZMod q) output)
  calc
    evalDist
        (permutedCoefficientVector output <$>
          sampler q (degree + 1) eta) =
      evalDist
        (sourceIndexTableEquiv (ZMod q) output <$>
          (coefficientVector <$> sampler q (degree + 1) eta)) := by
            simp only [Functor.map_map]
            apply congrArg evalDist
            apply congrArg (fun transform ↦
              transform <$> sampler q (degree + 1) eta)
            funext error
            rfl
    _ = evalDist
        (sourceIndexTableEquiv (ZMod q) output <$>
          ProbComp.sampleIID (degree + 1) (coefficientSampler q eta)) :=
            hReindex
    _ = evalDist
        (ProbComp.sampleIID (degree + 1) (coefficientSampler q eta)) :=
          sourceIndexTableEquiv_sampleIID_evalDist
            (coefficientSampler q eta) output

/-- A signed binary weight has absolute value at most one. -/
theorem binaryWeightInt_natAbs_le_one {degree : ℕ}
    (secret : Fin (degree + 1) → Bool) (output input : Fin (degree + 1)) :
    (binaryWeightInt secret output input).natAbs ≤ 1 := by
  unfold binaryWeightInt
  split <;> cases hbit : secret input <;> simp

/-- A selected binary coefficient contributes a weight whose square is one. -/
theorem binaryWeightReal_sq_eq_one_of_true {degree : ℕ}
    (secret : Fin (degree + 1) → Bool) (output input : Fin (degree + 1))
    (hbit : secret input = true) :
    binaryWeightReal secret output input ^ 2 = 1 := by
  unfold binaryWeightReal binaryWeightInt
  split <;> simp

/-! ## Deterministic no-wrap convolution identity -/

/-- A supported centered-binomial ring coefficient has centered magnitude at most `eta`. -/
theorem centeredRepr_get_natAbs_le_of_mem_support
    {q degree eta : ℕ} [NeZero q]
    {error : RLWE.Rq q degree}
    (hError : error ∈ support (sampler q degree eta))
    (coefficient : Fin degree) (hNoWrap : 2 * eta < q) :
    (LatticeCrypto.centeredRepr (error.get coefficient)).natAbs ≤ eta := by
  obtain ⟨value, hValue, hCoefficient⟩ :=
    coeffBounded_of_mem_support hError coefficient
  have hValueNatAbs : value.natAbs ≤ eta := by
    rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]
    exact hValue
  rw [hCoefficient,
    LatticeCrypto.centeredRepr_intCast_eq_of_natAbs_le
      value hValueNatAbs hNoWrap]
  exact hValueNatAbs

/-- The integer signed convolution sum has magnitude at most `N * eta`. -/
theorem binaryWeightedCenteredError_natAbs_le
    {q degree eta : ℕ} [NeZero q]
    (secret : Fin (degree + 1) → Bool)
    (output : Fin (degree + 1))
    {error : Ring q degree}
    (hError : error ∈ support (sampler q (degree + 1) eta))
    (hNoWrap : 2 * eta < q) :
    (∑ input : Fin (degree + 1),
        binaryWeightInt secret output input *
          LatticeCrypto.centeredRepr
            (error.get (SharpRotationNoise.sourceIndex input output))).natAbs ≤
      (degree + 1) * eta := by
  let term : Fin (degree + 1) → ℤ := fun input ↦
    binaryWeightInt secret output input *
      LatticeCrypto.centeredRepr
        (error.get (SharpRotationNoise.sourceIndex input output))
  calc
    (∑ input : Fin (degree + 1), term input).natAbs ≤
        ∑ input : Fin (degree + 1), (term input).natAbs := by
          simpa using Int.natAbs_sum_le (Finset.univ : Finset (Fin (degree + 1))) term
    _ ≤ ∑ _input : Fin (degree + 1), eta := by
      apply Finset.sum_le_sum
      intro input _
      rw [Int.natAbs_mul]
      calc
        (binaryWeightInt secret output input).natAbs *
            (LatticeCrypto.centeredRepr
              (error.get (SharpRotationNoise.sourceIndex input output))).natAbs ≤
          1 * eta := Nat.mul_le_mul
            (binaryWeightInt_natAbs_le_one secret output input)
            (centeredRepr_get_natAbs_le_of_mem_support hError _ hNoWrap)
        _ = eta := one_mul eta
    _ = (degree + 1) * eta := by simp

/-- In the small-noise regime, the centered output coefficient of binary-secret negacyclic
multiplication is exactly the corresponding real weighted sum. -/
theorem ringCoefficientLift_embedBinaryPolynomial_mul_error
    (q degree eta : ℕ) [NeZero q]
    (secret : Fin (degree + 1) → Bool)
    (output : Fin (degree + 1))
    {error : Ring q degree}
    (hError : error ∈ support (sampler q (degree + 1) eta))
    (hCoefficientNoWrap : 2 * eta < q)
    (hConvolutionNoWrap : 2 * ((degree + 1) * eta) < q) :
    ringCoefficientLift q output
        (embedBinaryPolynomial q (degree + 1) secret * error) =
      weightedSum (binaryWeightReal secret output)
        (centeredCoefficientLift q)
        (permutedCoefficientVector output error) := by
  let integerSum : ℤ :=
    ∑ input : Fin (degree + 1),
      binaryWeightInt secret output input *
        LatticeCrypto.centeredRepr
          (error.get (SharpRotationNoise.sourceIndex input output))
  have hTerm (input : Fin (degree + 1)) :
      (if input.val ≤ output.val then
          (embedBinaryPolynomial q (degree + 1) secret).get input *
            error.get (SharpRotationNoise.sourceIndex input output)
        else
          -((embedBinaryPolynomial q (degree + 1) secret).get input *
            error.get (SharpRotationNoise.sourceIndex input output))) =
        ((binaryWeightInt secret output input *
          LatticeCrypto.centeredRepr
            (error.get (SharpRotationNoise.sourceIndex input output)) : ℤ) : ZMod q) := by
    have hErrorCast := LatticeCrypto.centeredRepr_intCast
      (error.get (SharpRotationNoise.sourceIndex input output))
    have hSecretGet :
        (embedBinaryPolynomial q (degree + 1) secret).get input =
          if secret input then 1 else 0 := by
      simp [embedBinaryPolynomial, LatticeCrypto.Poly.ofPi, Vector.get, embedBit]
    rw [hSecretGet]
    unfold binaryWeightInt
    split
    · cases hbit : secret input
      · simp
      · simpa [hbit] using hErrorCast
    · cases hbit : secret input
      · simp
      · simpa [hbit] using congrArg Neg.neg hErrorCast
  have hMul :
      (embedBinaryPolynomial q (degree + 1) secret * error).get output =
        LatticeCrypto.negacyclicConvCoeff
          (fun input ↦
            (embedBinaryPolynomial q (degree + 1) secret).get input)
          (fun input ↦ error.get input) output := by
    exact NoiseBounds.mul_coefficient
      (embedBinaryPolynomial q (degree + 1) secret) error output
  have hProductCast :
      (embedBinaryPolynomial q (degree + 1) secret * error).get output =
        (integerSum : ZMod q) := by
    rw [hMul]
    rw [SharpRotationNoise.negacyclicConvCoeff_eq_sum_source]
    simp_rw [hTerm]
    unfold integerSum
    push_cast
    rfl
  have hIntegerSumBound : integerSum.natAbs ≤ (degree + 1) * eta := by
    exact binaryWeightedCenteredError_natAbs_le secret output hError
      hCoefficientNoWrap
  unfold ringCoefficientLift centeredCoefficientLift
  rw [hProductCast,
    LatticeCrypto.centeredRepr_intCast_eq_of_natAbs_le
      integerSum hIntegerSumBound hConvolutionNoWrap]
  unfold weightedSum binaryWeightReal permutedCoefficientVector integerSum
  push_cast
  rfl

/-! ## Exact and lower-bounded anchor moments -/

/-- Exact second moment of one output coefficient of `S * e` for a binary secret. -/
theorem secondMoment_embedBinaryPolynomial_mul_sampler
    (q degree eta : ℕ) [NeZero q]
    (secret : Fin (degree + 1) → Bool)
    (output : Fin (degree + 1))
    (hCoefficientNoWrap : 2 * eta < q)
    (hConvolutionNoWrap : 2 * ((degree + 1) * eta) < q) :
    secondMoment
        ((fun error : Ring q degree ↦
          embedBinaryPolynomial q (degree + 1) secret * error) <$>
          sampler q (degree + 1) eta)
        (ringCoefficientLift q output) =
      ((eta : ℝ) / 2) *
        ∑ input, binaryWeightReal secret output input ^ 2 := by
  rw [secondMoment_map]
  calc
    expectation (sampler q (degree + 1) eta)
        (fun error ↦
          ringCoefficientLift q output
            (embedBinaryPolynomial q (degree + 1) secret * error) ^ 2) =
      expectation (sampler q (degree + 1) eta)
        (fun error ↦
          weightedSum (binaryWeightReal secret output)
            (centeredCoefficientLift q)
            (permutedCoefficientVector output error) ^ 2) := by
              apply expectation_congr_on_support
              intro error hError
              rw [ringCoefficientLift_embedBinaryPolynomial_mul_error
                q degree eta secret output hError hCoefficientNoWrap
                  hConvolutionNoWrap]
    _ = secondMoment
        (permutedCoefficientVector output <$>
          sampler q (degree + 1) eta)
        (weightedSum (binaryWeightReal secret output)
          (centeredCoefficientLift q)) := by
            rw [secondMoment_map]
    _ = secondMoment
        (ProbComp.sampleIID (degree + 1) (coefficientSampler q eta))
        (weightedSum (binaryWeightReal secret output)
          (centeredCoefficientLift q)) :=
            secondMoment_congr_evalDist
              (permutedCoefficientVector_sampler_evalDist q degree eta output)
              (weightedSum (binaryWeightReal secret output)
                (centeredCoefficientLift q))
    _ = ((eta : ℝ) / 2) *
        ∑ input, binaryWeightReal secret output input ^ 2 :=
      secondMoment_sampleIID_coefficientSampler_weightedSum
        q eta (degree + 1) (binaryWeightReal secret output)
          hCoefficientNoWrap

/-- A nonzero binary secret forces at least one unit squared convolution weight. -/
theorem one_le_sum_sq_binaryWeightReal_of_true
    {degree : ℕ} (secret : Fin (degree + 1) → Bool)
    (output selected : Fin (degree + 1)) (hSelected : secret selected = true) :
    (1 : ℝ) ≤ ∑ input, binaryWeightReal secret output input ^ 2 := by
  rw [← binaryWeightReal_sq_eq_one_of_true secret output selected hSelected]
  exact Finset.single_le_sum
    (s := Finset.univ)
    (f := fun input ↦ binaryWeightReal secret output input ^ 2)
    (fun input _ ↦ sq_nonneg (binaryWeightReal secret output input))
    (Finset.mem_univ selected)

/-- Every coefficient of `S * e` has second moment at least `eta / 2` for a nonzero binary
secret `S`. -/
theorem eta_div_two_le_secondMoment_embedBinaryPolynomial_mul_sampler
    (q degree eta : ℕ) [NeZero q]
    (secret : Fin (degree + 1) → Bool)
    (selected : Fin (degree + 1)) (hSelected : secret selected = true)
    (output : Fin (degree + 1))
    (hCoefficientNoWrap : 2 * eta < q)
    (hConvolutionNoWrap : 2 * ((degree + 1) * eta) < q) :
    (eta : ℝ) / 2 ≤
      secondMoment
        ((fun error : Ring q degree ↦
          embedBinaryPolynomial q (degree + 1) secret * error) <$>
          sampler q (degree + 1) eta)
        (ringCoefficientLift q output) := by
  rw [secondMoment_embedBinaryPolynomial_mul_sampler q degree eta secret output
    hCoefficientNoWrap hConvolutionNoWrap]
  calc
    (eta : ℝ) / 2 = ((eta : ℝ) / 2) * 1 := by ring
    _ ≤ ((eta : ℝ) / 2) *
        ∑ input, binaryWeightReal secret output input ^ 2 := by
      exact mul_le_mul_of_nonneg_left
        (one_le_sum_sq_binaryWeightReal_of_true secret output selected hSelected)
        (by positivity)

/-- The same lower bound for the anchor sampler used by the actual binary-selector compiler. -/
theorem eta_div_two_le_secondMoment_binaryAnchorResidualSampler
    (q degree eta : ℕ) [NeZero q]
    {Secret : Type} (embed : Secret → Fin 1 → Ring q degree)
    (secretValue : Secret)
    (secret : Fin (degree + 1) → Bool)
    (hEmbed : embed secretValue 0 =
      embedBinaryPolynomial q (degree + 1) secret)
    (selected : Fin (degree + 1)) (hSelected : secret selected = true)
    (output : Fin (degree + 1))
    (hCoefficientNoWrap : 2 * eta < q)
    (hConvolutionNoWrap : 2 * ((degree + 1) * eta) < q) :
    (eta : ℝ) / 2 ≤
      secondMoment
        (HiddenResidual.binaryAnchorResidualSampler embed
          (sampler q (degree + 1) eta) secretValue)
        (ringCoefficientLift q output) := by
  unfold HiddenResidual.binaryAnchorResidualSampler
  rw [hEmbed]
  exact eta_div_two_le_secondMoment_embedBinaryPolynomial_mul_sampler
    q degree eta secret selected hSelected output hCoefficientNoWrap
      hConvolutionNoWrap

/-- **Concrete small-noise obstruction for native binary `RGSW_S(-S)`.**  For a nonzero binary
ring secret and centered-binomial source errors, the complete hidden-residual statistical distance
is at least `(eta/2)/(2B²)` under the displayed correctness-compatible centered/no-wrap
hypotheses.  The lower bound is independent of the selector pool size and success probability. -/
theorem eta_div_two_div_le_hiddenResidualDistance
    (q degree eta levels extraCount : ℕ) [NeZero q]
    {Secret : Type} (embed : Secret → Fin 1 → Ring q degree)
    (targetErrorSampler : ProbComp (Ring q degree))
    (bitSelectors : Fin levels → BitSelector (Ring q degree) extraCount)
    (context : HiddenResidual.MaskContext
      (Ring q degree) Secret levels (extraCount + 1))
    (level : Fin levels)
    (secret : Fin (degree + 1) → Bool)
    (hEmbed : embed context.secretValue 0 =
      embedBinaryPolynomial q (degree + 1) secret)
    (selected : Fin (degree + 1)) (hSelected : secret selected = true)
    (output : Fin (degree + 1))
    (hCoefficientNoWrap : 2 * eta < q)
    (hConvolutionNoWrap : 2 * ((degree + 1) * eta) < q)
    (bound : ℝ) (hBoundPos : 0 < bound)
    (hAnchorTailAdd : ∀ anchorValue,
      anchorValue ∈ support
        (HiddenResidual.binaryAnchorResidualSampler embed
          (sampler q (degree + 1) eta) context.secretValue) →
      ∀ tailValue,
      tailValue ∈ support
        (HiddenResidual.binaryTailResidualSampler embed
          (sampler q (degree + 1) eta) bitSelectors context level) →
        ringCoefficientLift q output (anchorValue + tailValue) =
          ringCoefficientLift q output anchorValue +
            ringCoefficientLift q output tailValue)
    (hAnchorCentered :
      mean
        (HiddenResidual.binaryAnchorResidualSampler embed
          (sampler q (degree + 1) eta) context.secretValue)
        (ringCoefficientLift q output) = 0)
    (hTailCentered :
      mean
        (HiddenResidual.binaryTailResidualSampler embed
          (sampler q (degree + 1) eta) bitSelectors context level)
        (ringCoefficientLift q output) = 0)
    (hResidualTargetAdd : ∀ residualValue,
      residualValue ∈ support
        (HiddenResidual.upperResidualCoordinateSampler embed
          (sampler q (degree + 1) eta)
          (binarySelectors bitSelectors) context level) →
      ∀ noiseValue,
      noiseValue ∈ support
        (HiddenResidual.upperTargetErrorCoordinateSampler
          levels targetErrorSampler level) →
        ringCoefficientLift q output (residualValue + noiseValue) =
          ringCoefficientLift q output residualValue +
            ringCoefficientLift q output noiseValue)
    (hTargetCentered :
      mean
        (HiddenResidual.upperTargetErrorCoordinateSampler
          levels targetErrorSampler level)
        (ringCoefficientLift q output) = 0)
    (hTargetSupport : ∀ value,
      value ∈ support
        (HiddenResidual.upperTargetErrorCoordinateSampler
          levels targetErrorSampler level) →
        |ringCoefficientLift q output value| ≤ bound)
    (hShiftedSupport : ∀ value,
      value ∈ support
        (independentAdd
          (HiddenResidual.upperResidualCoordinateSampler embed
            (sampler q (degree + 1) eta)
            (binarySelectors bitSelectors) context level)
          (HiddenResidual.upperTargetErrorCoordinateSampler
            levels targetErrorSampler level)) →
        |ringCoefficientLift q output value| ≤ bound) :
    ((eta : ℝ) / 2) / (2 * bound ^ 2) ≤
      HiddenResidual.hiddenResidualDistance embed
        (sampler q (degree + 1) eta) targetErrorSampler
        (binarySelectors bitSelectors) context := by
  have hAnchorMoment :=
    eta_div_two_le_secondMoment_binaryAnchorResidualSampler
      q degree eta embed context.secretValue secret hEmbed selected hSelected output
        hCoefficientNoWrap hConvolutionNoWrap
  have hMomentDistance :=
    HiddenResidual.binaryAnchorSecondMoment_div_le_hiddenResidualDistance
      embed (sampler q (degree + 1) eta) targetErrorSampler bitSelectors
        context level bound (ringCoefficientLift q output) hBoundPos
        hAnchorTailAdd hAnchorCentered hTailCentered hResidualTargetAdd
        hTargetCentered hTargetSupport hShiftedSupport
  have hDenominatorPos : 0 < 2 * bound ^ 2 := by positivity
  exact (div_le_div_of_nonneg_right hAnchorMoment hDenominatorPos.le).trans
    hMomentDistance

end CenteredBinomialAnchorMoment

end

end FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler
