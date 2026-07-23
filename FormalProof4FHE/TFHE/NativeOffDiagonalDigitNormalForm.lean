/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeDifferenceDigitUniformity
import FormalProof4FHE.TFHE.CenteredBinomialCorrectness
import FormalProof4FHE.TFHE.NativeShiftedResidualBounds

/-!
# IID Digit Normal Form for the Native Off-Diagonal Residual

At exact gadget capacity, the uniform native difference ciphertext is equivalent to one tensor
of mutually independent uniform base digits.  This file transports the off-diagonal error-only
normal form through that equivalence.  The resulting residual contains no ciphertext-valued
random input: it is a deterministic function of the base-digit tensor and centered-binomial coin
tables.

This is an exact distributional normalization, not a smoothing estimate.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm

noncomputable section

open FormalProof4FHE.TFHE

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing

variable {q degree ringRank lweDimension : ℕ} [NeZero q]

/-- All coefficient digits of every extended coordinate of every native difference row. -/
abbrev OffDiagonalDifferenceDigitTensor
    (params : Gadget.Base.Parameters q) :=
  Fin (TGSW.rowCount ringRank params.levels) →
    Fin (ringRank + 1) → Fin (degree + 1) →
      Fin params.levels → Fin params.base

/-- Decode an exact-capacity coefficient-digit tensor back to the unique native difference
ciphertext. -/
noncomputable def differenceFromDigitTensor
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (digits : OffDiagonalDifferenceDigitTensor
      (degree := degree) (ringRank := ringRank) params) :
    RingGSWCiphertext q (degree + 1) ringRank params.levels :=
  (DiagonalNormalForm.differenceDigitCoefficientEquiv
    (degree := degree) (ringRank := ringRank) params hcapacity).symm digits

@[simp]
theorem differenceDigitCoefficientVector_differenceFromDigitTensor
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (digits : OffDiagonalDifferenceDigitTensor
      (degree := degree) (ringRank := ringRank) params) :
    DiagonalNormalForm.differenceDigitCoefficientVector params
        (differenceFromDigitTensor params hcapacity digits) =
      digits := by
  exact (DiagonalNormalForm.differenceDigitCoefficientEquiv
    (degree := degree) (ringRank := ringRank) params hcapacity).apply_symm_apply digits

/-- Cast one coefficient-digit tensor to the ring-valued digit tensor consumed by the native
internal product. -/
def ringDigitsFromCoefficientTensor
    (params : Gadget.Base.Parameters q)
    (digits : OffDiagonalDifferenceDigitTensor
      (degree := degree) (ringRank := ringRank) params) :
    Fin (TGSW.rowCount ringRank params.levels) →
      Fin (ringRank + 1) → Fin params.levels → RLWE.Rq q (degree + 1) :=
  fun row block level =>
    LatticeCrypto.Poly.ofPi fun coefficient =>
      ((digits row block coefficient level).val : ZMod q)

/-- Casting the coefficient digits of a concrete difference ciphertext reconstructs exactly the
ring-valued digits used by the evaluator. -/
theorem ringDigitsFromCoefficientTensor_difference
    (params : Gadget.Base.Parameters q)
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    ringDigitsFromCoefficientTensor params
        (DiagonalNormalForm.differenceDigitCoefficientVector params difference) =
      DiagonalNormalForm.differenceEntryDigits params difference := by
  funext row block level
  apply LatticeCrypto.Poly.ext_get_eq
  intro coefficient
  calc
    LatticeCrypto.Poly.toPi
        (ringDigitsFromCoefficientTensor params
          (DiagonalNormalForm.differenceDigitCoefficientVector params difference)
          row block level) coefficient =
        ((DiagonalNormalForm.differenceDigitCoefficientVector params difference
          row block coefficient level).val : ZMod q) := by
      simp [ringDigitsFromCoefficientTensor]
    _ = LatticeCrypto.Poly.toPi
        (DiagonalNormalForm.differenceEntryDigits params difference row block level)
          coefficient :=
      DiagonalNormalForm.differenceDigitCoefficientVector_cast params difference
        row block coefficient level

/-- Decoding an exact-capacity digit tensor and digitizing it again gives the direct cast of the
original finite digits. -/
theorem differenceEntryDigits_differenceFromDigitTensor
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (digits : OffDiagonalDifferenceDigitTensor
      (degree := degree) (ringRank := ringRank) params) :
    DiagonalNormalForm.differenceEntryDigits params
        (differenceFromDigitTensor params hcapacity digits) =
      ringDigitsFromCoefficientTensor params digits := by
  rw [← ringDigitsFromCoefficientTensor_difference params
    (differenceFromDigitTensor params hcapacity digits)]
  rw [differenceDigitCoefficientVector_differenceFromDigitTensor]

/-! ## Deterministic support of the real digit residual -/

/-- Every explicitly supplied base digit has centered coefficient norm at most `base - 1`. -/
theorem cInfNorm_ringDigitsFromCoefficientTensor_le
    (params : Gadget.Base.Parameters q)
    (digits : OffDiagonalDifferenceDigitTensor
      (degree := degree) (ringRank := ringRank) params)
    (row : Fin (TGSW.rowCount ringRank params.levels))
    (block : Fin (ringRank + 1)) (level : Fin params.levels) :
    LatticeCrypto.cInfNorm
        (ringDigitsFromCoefficientTensor params digits row block level) ≤
      params.base - 1 := by
  apply LatticeCrypto.cInfNorm_le_of_coeff_le
  intro coefficient
  change (LatticeCrypto.centeredRepr
      (LatticeCrypto.Poly.toPi
        (ringDigitsFromCoefficientTensor params digits row block level)
        coefficient)).natAbs ≤ params.base - 1
  rw [show LatticeCrypto.Poly.toPi
      (ringDigitsFromCoefficientTensor params digits row block level) coefficient =
        ((digits row block coefficient level).val : ZMod q) by
    simp [ringDigitsFromCoefficientTensor]]
  calc
    (LatticeCrypto.centeredRepr
        ((digits row block coefficient level).val : ZMod q)).natAbs ≤
        ((digits row block coefficient level).val : ℤ).natAbs :=
      NoiseBounds.centeredRepr_natCast_natAbs_le _
    _ = (digits row block coefficient level).val := by simp
    _ ≤ params.base - 1 := by
      have := (digits row block coefficient level).isLt
      omega

/-- Centered-binomial bit-pair decoding always lies in its advertised support interval. -/
theorem cInfNorm_centeredBinomialErrorVectorFromCoins_le
    (count eta : ℕ)
    (coins : RLWE.CenteredBinomial.ErrorVectorCoinTable
      count (degree + 1) eta) (row : Fin count) :
    LatticeCrypto.cInfNorm
        (RLWE.CenteredBinomial.errorVectorFromCoins
          q count (degree + 1) eta coins row) ≤ eta := by
  exact CenteredBinomialCorrectness.cInfNorm_le_of_coeffBounded
    (RLWE.CenteredBinomial.errorFromCoins_coeffBounded
      q (degree + 1) eta (coins row))

/-- Selecting the candidate-dependent sign does not change centered coefficient norm. -/
@[simp]
theorem cInfNorm_signedControlValue
    (candidate : Bool) (value : RLWE.Rq q (degree + 1)) :
    LatticeCrypto.cInfNorm
        (@signedControlValue (RLWE.Rq q (degree + 1))
          NoiseBounds.positiveRqRing candidate value) =
      LatticeCrypto.cInfNorm value := by
  cases candidate
  · rfl
  · exact LatticeCrypto.cInfNorm_neg value

/-- The digit-weighted part of one residual row has the same explicit `N²` convolution bound
used by the native residual analysis. -/
theorem cInfNorm_perturbationErrorOperator_ringDigits_le
    (params : Gadget.Base.Parameters q) (eta : ℕ) (candidate : Bool)
    (digits : OffDiagonalDifferenceDigitTensor
      (degree := degree) (ringRank := ringRank) params)
    (controlError : OffDiagonalErrorVector q degree ringRank params.levels)
    (hcontrol : ∀ row, LatticeCrypto.cInfNorm (controlError row) ≤ eta)
    (row : Fin (TGSW.rowCount ringRank params.levels)) :
    LatticeCrypto.cInfNorm
        (@perturbationErrorOperator (RLWE.Rq q (degree + 1))
          NoiseBounds.positiveRqCommRing ringRank params.levels candidate
          (ringDigitsFromCoefficientTensor params digits) controlError row) ≤
      ((ringRank + 1) * params.levels) *
        (((degree + 1) * (degree + 1)) * ((params.base - 1) * eta)) := by
  letI : CommRing (RLWE.Rq q (degree + 1)) :=
    NoiseBounds.positiveRqCommRing
  unfold perturbationErrorOperator
  calc
    LatticeCrypto.cInfNorm
        (@Finset.sum (Fin (ringRank + 1) × Fin params.levels)
          (RLWE.Rq q (degree + 1)) NoiseBounds.positiveRqRing.toAddCommMonoid
          Finset.univ (fun index ↦
            ringDigitsFromCoefficientTensor params digits row index.1 index.2 *
              signedControlValue candidate
                (controlError (finProdFinEquiv index)))) ≤
        ∑ index : Fin (ringRank + 1) × Fin params.levels,
          LatticeCrypto.cInfNorm
            (ringDigitsFromCoefficientTensor params digits row index.1 index.2 *
              signedControlValue candidate (controlError (finProdFinEquiv index))) := by
      simpa using NoiseBounds.cInfNorm_finset_sum_le
        (fun index : Fin (ringRank + 1) × Fin params.levels ↦
          ringDigitsFromCoefficientTensor params digits row index.1 index.2 *
            signedControlValue candidate (controlError (finProdFinEquiv index)))
        Finset.univ
    _ ≤ ∑ _index : Fin (ringRank + 1) × Fin params.levels,
        ((degree + 1) * (degree + 1)) * ((params.base - 1) * eta) := by
      apply Finset.sum_le_sum
      intro index _
      exact (NoiseBounds.cInfNorm_mul_le
        (ringDigitsFromCoefficientTensor params digits row index.1 index.2)
        (signedControlValue candidate (controlError (finProdFinEquiv index)))).trans
          (Nat.mul_le_mul_left _ (Nat.mul_le_mul
            (cInfNorm_ringDigitsFromCoefficientTensor_le params digits
              row index.1 index.2)
            (by simpa using hcontrol (finProdFinEquiv index))))
    _ = ((ringRank + 1) * params.levels) *
        (((degree + 1) * (degree + 1)) * ((params.base - 1) * eta)) := by
      simp [Fintype.card_prod]

/-- Uniform inputs of the digit-normal-form residual. -/
abbrev CenteredBinomialDigitResidualCoins
    (params : Gadget.Base.Parameters q) (eta : ℕ) :=
  OffDiagonalDifferenceDigitTensor
      (degree := degree) (ringRank := ringRank) params ×
    RLWE.CenteredBinomial.ErrorVectorCoinTable
      (TGSW.rowCount ringRank params.levels) (degree + 1) eta

/-- Evaluate the complete off-diagonal residual directly from IID base digits and
centered-binomial bit-pair tables. -/
def centeredBinomialResidualFromDigitCoins
    (params : Gadget.Base.Parameters q)
    (eta : ℕ) (candidate : Bool)
    (controlError : OffDiagonalErrorVector q degree ringRank params.levels)
    (coins : CenteredBinomialDigitResidualCoins
      (degree := degree) (ringRank := ringRank) params eta) :
    OffDiagonalErrorVector q degree ringRank params.levels :=
  perturbationErrorOperator candidate
      (ringDigitsFromCoefficientTensor params coins.1) controlError +
    RLWE.CenteredBinomial.errorVectorFromCoins q
      (TGSW.rowCount ringRank params.levels) (degree + 1) eta coins.2

/-- Every row of the explicit real residual has polynomially bounded centered support whenever
the generated control errors use the same centered-binomial width. -/
theorem cInfNorm_centeredBinomialResidualFromDigitCoins_le
    (params : Gadget.Base.Parameters q) (eta : ℕ) (candidate : Bool)
    (controlError : OffDiagonalErrorVector q degree ringRank params.levels)
    (hcontrol : ∀ row, LatticeCrypto.cInfNorm (controlError row) ≤ eta)
    (coins : CenteredBinomialDigitResidualCoins
      (degree := degree) (ringRank := ringRank) params eta)
    (row : Fin (TGSW.rowCount ringRank params.levels)) :
    LatticeCrypto.cInfNorm
        (centeredBinomialResidualFromDigitCoins
          params eta candidate controlError coins row) ≤
      Native.ShiftedResidualBounds.centeredBinomialResidualBound
        params (degree + 1) ringRank eta := by
  unfold centeredBinomialResidualFromDigitCoins
  change LatticeCrypto.cInfNorm
      (perturbationErrorOperator candidate
          (ringDigitsFromCoefficientTensor params coins.1) controlError row +
        RLWE.CenteredBinomial.errorVectorFromCoins q
          (TGSW.rowCount ringRank params.levels) (degree + 1) eta coins.2 row) ≤ _
  refine (NoiseBounds.cInfNorm_add_le _ _).trans ?_
  have hPerturbation := cInfNorm_perturbationErrorOperator_ringDigits_le
    params eta candidate coins.1 controlError hcontrol row
  have hSource := cInfNorm_centeredBinomialErrorVectorFromCoins_le
    (q := q) (degree := degree)
    (TGSW.rowCount ringRank params.levels) eta coins.2 row
  simpa only [Native.ShiftedResidualBounds.centeredBinomialResidualBound,
    Native.ShiftedResidualBounds.correctResidualBound, Nat.add_comm] using
      Nat.add_le_add hPerturbation hSource

/-- In the canonical generated-control experiment, both the control and fresh source rows obey
the same deterministic centered-binomial residual bound for every choice of finite coins. -/
theorem cInfNorm_centeredBinomialResidualFromGeneratedDigitCoins_le
    (params : Gadget.Base.Parameters q) (eta : ℕ) (candidate : Bool)
    (controlCoins : RLWE.CenteredBinomial.ErrorVectorCoinTable
      (TGSW.rowCount ringRank params.levels) (degree + 1) eta)
    (coins : CenteredBinomialDigitResidualCoins
      (degree := degree) (ringRank := ringRank) params eta)
    (row : Fin (TGSW.rowCount ringRank params.levels)) :
    LatticeCrypto.cInfNorm
        (centeredBinomialResidualFromDigitCoins params eta candidate
          (RLWE.CenteredBinomial.errorVectorFromCoins q
            (TGSW.rowCount ringRank params.levels) (degree + 1) eta controlCoins)
          coins row) ≤
      Native.ShiftedResidualBounds.centeredBinomialResidualBound
        params (degree + 1) ringRank eta := by
  apply cInfNorm_centeredBinomialResidualFromDigitCoins_le
  intro controlRow
  exact cInfNorm_centeredBinomialErrorVectorFromCoins_le
    (q := q) (degree := degree)
    (TGSW.rowCount ringRank params.levels) eta controlCoins controlRow

/-- The completely explicit real residual sampler after fixing the generated control coins. -/
noncomputable def generatedCenteredBinomialDigitResidualSampler
    (params : Gadget.Base.Parameters q) (eta : ℕ) (candidate : Bool)
    (controlCoins : RLWE.CenteredBinomial.ErrorVectorCoinTable
      (TGSW.rowCount ringRank params.levels) (degree + 1) eta) :
    ProbComp (OffDiagonalErrorVector q degree ringRank params.levels) :=
  centeredBinomialResidualFromDigitCoins params eta candidate
      (RLWE.CenteredBinomial.errorVectorFromCoins q
        (TGSW.rowCount ringRank params.levels) (degree + 1) eta controlCoins) <$>
    ($ᵗ (CenteredBinomialDigitResidualCoins
      (degree := degree) (ringRank := ringRank) params eta))

/-- Efficient row test that recognizes the deterministic support ball of the real residual. -/
def residualRowWithinCenteredBinomialBound
    (params : Gadget.Base.Parameters q) (eta : ℕ)
    (row : Fin (TGSW.rowCount ringRank params.levels))
    (error : OffDiagonalErrorVector q degree ringRank params.levels) : Bool :=
  decide (LatticeCrypto.cInfNorm (error row) ≤
    Native.ShiftedResidualBounds.centeredBinomialResidualBound
      params (degree + 1) ringRank eta)

/-- The support-ball test accepts every possible output of the explicit real sampler. -/
theorem residualRowWithinCenteredBinomialBound_of_mem_support
    (params : Gadget.Base.Parameters q) (eta : ℕ) (candidate : Bool)
    (controlCoins : RLWE.CenteredBinomial.ErrorVectorCoinTable
      (TGSW.rowCount ringRank params.levels) (degree + 1) eta)
    (row : Fin (TGSW.rowCount ringRank params.levels))
    {error : OffDiagonalErrorVector q degree ringRank params.levels}
    (herror : error ∈ support
      (generatedCenteredBinomialDigitResidualSampler
        params eta candidate controlCoins)) :
    residualRowWithinCenteredBinomialBound params eta row error = true := by
  unfold generatedCenteredBinomialDigitResidualSampler at herror
  rw [support_map, Set.mem_image] at herror
  obtain ⟨coins, _hcoins, rfl⟩ := herror
  simp only [residualRowWithinCenteredBinomialBound, decide_eq_true_eq]
  exact cInfNorm_centeredBinomialResidualFromGeneratedDigitCoins_le
    params eta candidate controlCoins coins row

/-- The norm-threshold test accepts the real residual with probability one. -/
theorem probOutput_residualRowWithinCenteredBinomialBound_generated_eq_one
    (params : Gadget.Base.Parameters q) (eta : ℕ) (candidate : Bool)
    (controlCoins : RLWE.CenteredBinomial.ErrorVectorCoinTable
      (TGSW.rowCount ringRank params.levels) (degree + 1) eta)
    (row : Fin (TGSW.rowCount ringRank params.levels)) :
    Pr[= true |
      residualRowWithinCenteredBinomialBound params eta row <$>
        generatedCenteredBinomialDigitResidualSampler
          params eta candidate controlCoins] = 1 := by
  rw [probOutput_eq_one_iff_forall]
  constructor
  · simp
  · intro accepted haccepted
    rw [support_map, Set.mem_image] at haccepted
    obtain ⟨error, herror, rfl⟩ := haccepted
    exact residualRowWithinCenteredBinomialBound_of_mem_support
      params eta candidate controlCoins row herror

/-- A target residual law can be statistically close to the real law only if it places nearly
all of its mass inside the real law's deterministic support ball.  This is the formal
norm-threshold obstruction to replacing narrow centered-binomial residuals by an arbitrarily
wider statistical target. -/
theorem one_sub_targetSupportBallMass_le_tvDist_generatedDigitResidual
    (params : Gadget.Base.Parameters q) (eta : ℕ) (candidate : Bool)
    (controlCoins : RLWE.CenteredBinomial.ErrorVectorCoinTable
      (TGSW.rowCount ringRank params.levels) (degree + 1) eta)
    (row : Fin (TGSW.rowCount ringRank params.levels))
    (target : ProbComp (OffDiagonalErrorVector q degree ringRank params.levels)) :
    1 - Pr[= true |
        residualRowWithinCenteredBinomialBound params eta row <$> target].toReal ≤
      tvDist
        (generatedCenteredBinomialDigitResidualSampler
          params eta candidate controlCoins) target := by
  let test := residualRowWithinCenteredBinomialBound
    (degree := degree) (ringRank := ringRank) params eta row
  let real := generatedCenteredBinomialDigitResidualSampler
    (degree := degree) (ringRank := ringRank) params eta candidate controlCoins
  have hreal : Pr[= true | test <$> real] = 1 := by
    exact probOutput_residualRowWithinCenteredBinomialBound_generated_eq_one
      params eta candidate controlCoins row
  have hprob := abs_probOutput_toReal_sub_le_tvDist
    (test <$> real) (test <$> target)
  have hmap := tvDist_map_le (m := ProbComp) test real target
  calc
    1 - Pr[= true | test <$> target].toReal =
        |Pr[= true | test <$> real].toReal -
          Pr[= true | test <$> target].toReal| := by
      rw [hreal]
      simp only [ENNReal.toReal_one]
      rw [abs_of_nonneg]
      exact sub_nonneg.mpr
        (ENNReal.toReal_mono ENNReal.one_ne_top probOutput_le_one)
    _ ≤ tvDist (test <$> real) (test <$> target) := hprob
    _ ≤ tvDist real target := hmap

/-- The old ciphertext-coin map and the new digit-coin map agree through exact-capacity
decoding. -/
theorem centeredBinomialResidualFromDigitCoins_eq_decode
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (eta : ℕ) (candidate : Bool)
    (controlError : OffDiagonalErrorVector q degree ringRank params.levels)
    (coins : CenteredBinomialDigitResidualCoins
      (degree := degree) (ringRank := ringRank) params eta) :
    centeredBinomialResidualFromDigitCoins params eta candidate controlError coins =
      centeredBinomialResidualFromCoins params eta candidate controlError
        (differenceFromDigitTensor params hcapacity coins.1, coins.2) := by
  unfold centeredBinomialResidualFromDigitCoins centeredBinomialResidualFromCoins
  change
    perturbationErrorOperator candidate
        (ringDigitsFromCoefficientTensor params coins.1) controlError +
      RLWE.CenteredBinomial.errorVectorFromCoins q
        (TGSW.rowCount ringRank params.levels) (degree + 1) eta coins.2 =
    perturbationErrorOperator candidate
        (DiagonalNormalForm.differenceEntryDigits params
          (differenceFromDigitTensor params hcapacity coins.1)) controlError +
      RLWE.CenteredBinomial.errorVectorFromCoins q
        (TGSW.rowCount ringRank params.levels) (degree + 1) eta coins.2
  rw [differenceEntryDigits_differenceFromDigitTensor]

/-- At exact capacity, the centered-binomial residual law is the deterministic image of a fully
IID finite base-digit/bit-pair source. -/
theorem errorOnlyResidualSampler_centeredBinomial_evalDist_eq_uniformDigitCoins
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (eta : ℕ) (candidate : Bool)
    (controlError : OffDiagonalErrorVector q degree ringRank params.levels) :
    evalDist
        (errorOnlyResidualSampler params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          candidate controlError) =
      evalDist
        (centeredBinomialResidualFromDigitCoins params eta candidate controlError <$>
          ($ᵗ (CenteredBinomialDigitResidualCoins
            (degree := degree) (ringRank := ringRank) params eta))) := by
  let OldCoins := CenteredBinomialResidualCoins
    q degree ringRank params.levels eta
  let DigitCoins := CenteredBinomialDigitResidualCoins
    (degree := degree) (ringRank := ringRank) params eta
  let coinEquiv : OldCoins ≃ DigitCoins :=
    Equiv.prodCongr
      (DiagonalNormalForm.differenceDigitCoefficientEquiv
        (degree := degree) (ringRank := ringRank) params hcapacity)
      (Equiv.refl _)
  let oldTransform := centeredBinomialResidualFromCoins
    (ringRank := ringRank) params eta candidate controlError
  let digitTransform := centeredBinomialResidualFromDigitCoins
    (ringRank := ringRank) params eta candidate controlError
  have hOld := errorOnlyResidualSampler_centeredBinomial_evalDist_eq_uniformCoins
    (ringRank := ringRank) params candidate controlError eta
  have hUniform :
      evalDist (coinEquiv.symm <$> ($ᵗ DigitCoins)) =
        evalDist ($ᵗ OldCoins) :=
    evalDist_map_bijective_uniform_cross
      (α := DigitCoins) (β := OldCoins)
      coinEquiv.symm coinEquiv.symm.bijective
  have hMapped := evalDist_map_eq_of_evalDist_eq hUniform oldTransform
  have hPoint :
      (fun coins : DigitCoins => oldTransform (coinEquiv.symm coins)) =
        digitTransform := by
    funext coins
    exact (centeredBinomialResidualFromDigitCoins_eq_decode
      (ringRank := ringRank) params hcapacity eta candidate controlError coins).symm
  calc
    _ = evalDist (oldTransform <$> ($ᵗ OldCoins)) := by
      simpa only [OldCoins, oldTransform] using hOld
    _ = evalDist (oldTransform <$> (coinEquiv.symm <$> ($ᵗ DigitCoins))) :=
      hMapped.symm
    _ = evalDist (digitTransform <$> ($ᵗ DigitCoins)) := by
      rw [Functor.map_map, hPoint]
    _ = _ := by
      rfl

/-- Fiber-count `L²` quantity after replacing the opaque uniform difference ciphertext by its
IID coefficient-digit tensor. -/
noncomputable def centeredBinomialDigitResidualFiberL2Loss
    (params : Gadget.Base.Parameters q)
    (eta : ℕ) {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (candidate : Bool)
    (controlError : OffDiagonalErrorVector q degree ringRank params.levels) : ℝ :=
  FormalProof4FHE.ConditionalCollision.twoUniformImagesL2Loss
    (centeredBinomialResidualFromDigitCoins params eta candidate controlError)
    (DiscreteGaussianSampler.ringErrorVectorFromTickets
      (TGSW.rowCount ringRank params.levels) (degree + 1) certificate)

/-- The conditional off-diagonal `L²` loss is exactly the IID digit/ticket fiber count at exact
gadget capacity. -/
theorem errorOnlyResidualL2Loss_centeredBinomial_ringSampler_eq_digitFiber
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (eta : ℕ) {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (candidate : Bool)
    (controlError : OffDiagonalErrorVector q degree ringRank params.levels) :
    errorOnlyResidualL2Loss params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
        candidate controlError =
      centeredBinomialDigitResidualFiberL2Loss params eta certificate
        candidate controlError := by
  have hReal :=
    errorOnlyResidualSampler_centeredBinomial_evalDist_eq_uniformDigitCoins
      (ringRank := ringRank) params hcapacity eta candidate controlError
  have hIdeal :=
    DiscreteGaussianSampler.sampleIID_ringSampler_evalDist_eq_uniformTickets
      (TGSW.rowCount ringRank params.levels) (degree + 1) certificate
  unfold errorOnlyResidualL2Loss targetErrorVectorSampler
  calc
    FormalProof4FHE.ConditionalCollision.l2Loss
        (errorOnlyResidualSampler params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          candidate controlError)
        (ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)) =
      FormalProof4FHE.ConditionalCollision.l2Loss
        (centeredBinomialResidualFromDigitCoins params eta candidate controlError <$>
          ($ᵗ (CenteredBinomialDigitResidualCoins
            (degree := degree) (ringRank := ringRank) params eta)))
        (DiscreteGaussianSampler.ringErrorVectorFromTickets
            (TGSW.rowCount ringRank params.levels) (degree + 1) certificate <$>
          ($ᵗ (DiscreteGaussianSampler.RingErrorVectorTicketCoins
            (TGSW.rowCount ringRank params.levels) (degree + 1) certificate))) :=
      FormalProof4FHE.ConditionalCollision.l2Loss_congr hReal hIdeal
    _ = centeredBinomialDigitResidualFiberL2Loss params eta certificate
          candidate controlError := by
      exact
        FormalProof4FHE.ConditionalCollision.l2Loss_uniformImages_eq_twoUniformImagesL2Loss
          (centeredBinomialResidualFromDigitCoins params eta candidate controlError)
          (DiscreteGaussianSampler.ringErrorVectorFromTickets
            (TGSW.rowCount ringRank params.levels) (degree + 1) certificate)

/-- The previous ciphertext-coin fiber formula and the IID digit-tensor formula are exactly the
same quantity at full gadget capacity. -/
theorem centeredBinomialResidualFiberL2Loss_eq_digitFiber
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (eta : ℕ) {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (candidate : Bool)
    (controlError : OffDiagonalErrorVector q degree ringRank params.levels) :
    centeredBinomialResidualFiberL2Loss params eta certificate
        candidate controlError =
      centeredBinomialDigitResidualFiberL2Loss params eta certificate
        candidate controlError := by
  rw [← errorOnlyResidualL2Loss_centeredBinomial_ringSampler_eq_fiber
    (ringRank := ringRank) params eta certificate candidate controlError]
  exact errorOnlyResidualL2Loss_centeredBinomial_ringSampler_eq_digitFiber
    (ringRank := ringRank) params hcapacity eta certificate candidate controlError

/-- Complete generated-control average after exposing both the control errors and the difference
ciphertext as uniform finite coin/digit tensors. -/
noncomputable def averagedCenteredBinomialDigitResidualFiberL2Loss
    (params : Gadget.Base.Parameters q)
    (eta : ℕ) {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (candidate : Bool) (coordinate : Fin lweDimension) : ℝ :=
  let ControlCoins := RLWE.CenteredBinomial.ErrorVectorCoinTable
    (TGSW.rowCount ringRank params.levels) (degree + 1) eta
  (Fintype.card ControlCoins : ℝ)⁻¹ *
    ∑ controlCoins : ControlCoins,
      ∑ _outputCoordinate ∈ Finset.univ.erase coordinate,
        centeredBinomialDigitResidualFiberL2Loss params eta certificate candidate
          (RLWE.CenteredBinomial.errorVectorFromCoins q
            (TGSW.rowCount ringRank params.levels) (degree + 1) eta controlCoins)

/-- The generated-control error-only loss is exactly the fully explicit IID
digit/bit-pair/ticket fiber average. -/
theorem averagedOffDiagonalErrorOnlyL2Loss_centeredBinomial_ringSampler_eq_digitFiber
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (eta : ℕ) {alpha : ℝ} {halpha : 0 < alpha}
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (candidate : Bool) (coordinate : Fin lweDimension) :
    averagedOffDiagonalErrorOnlyL2Loss (ringRank := ringRank) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
        candidate coordinate =
      averagedCenteredBinomialDigitResidualFiberL2Loss
        (degree := degree) (ringRank := ringRank)
        params eta certificate candidate coordinate := by
  rw [averagedOffDiagonalErrorOnlyL2Loss_centeredBinomial_ringSampler_eq_fiber
    (ringRank := ringRank) params eta certificate candidate coordinate]
  unfold averagedCenteredBinomialResidualFiberL2Loss
    averagedCenteredBinomialDigitResidualFiberL2Loss
  simp_rw [centeredBinomialResidualFiberL2Loss_eq_digitFiber
    (ringRank := ringRank) params hcapacity eta certificate candidate]

end

end FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm
