/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.LeftoverHash
import FormalProof4FHE.TFHE.NativeOffDiagonalResidualNormalForm
import FormalProof4FHE.TFHE.SamplerReplacement

/-!
# Residual Normal Form for the Selected Native TFHE Diagonal

The selected coordinate of the shifted-CMux evaluator reuses one TGSW ciphertext both as the
retained base and as the zero-message control.  This prevents the independent-translation
argument used at every off-diagonal coordinate.

After the independent difference ciphertext is fixed, however, its gadget digits are fixed.
The remaining self-correlated operation is therefore a linear row operator on the homogeneous
part of the selected TGSW ciphertext.  Exactly the same operator acts on every public mask
column and on the source error vector.  This file exposes that operator and reduces the complete
diagonal distance to two finite, explicit quantities:

* a fiber-second-moment loss for the transformed uniform public mask matrix; and
* the distance between the transformed source-error vector and the target-error vector.

This reduction neither assumes that digit decomposition is linear nor treats `ZMod q` as a
field.  The digitized difference is conditioned on before the linear row operator is formed.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm

noncomputable section

open FormalProof4FHE.TFHE

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing

variable {q degree ringRank : ℕ}

/-- The sign applied to the homogeneous control by correct scalar-bit toggling. -/
def signedValue {R : Type} [Ring R] (candidate : Bool) (value : R) : R :=
  if candidate then -value else value

/-- Once the difference digits are fixed, the selected diagonal acts linearly on the vector of
homogeneous TGSW rows. -/
def rowOperator {R : Type} [CommRing R] {dimension levels : ℕ}
    (candidate : Bool)
    (digits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (values : Fin (TGSW.rowCount dimension levels) → R) :
    Fin (TGSW.rowCount dimension levels) → R :=
  fun row => values row +
    ∑ index : Fin (dimension + 1) × Fin levels,
      digits row index.1 index.2 *
        signedValue candidate (values (finProdFinEquiv index))

/-- The induced action on every public mask column. -/
def challengeOperator {R : Type} [CommRing R] {dimension levels : ℕ}
    (candidate : Bool)
    (digits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (challenge : Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R) :
    Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R :=
  fun coordinate => rowOperator candidate digits (challenge coordinate)

/-- Complete homogeneous-ciphertext form of the selected diagonal row operator. -/
def homogeneousTransform {R : Type} [CommRing R] {dimension levels : ℕ}
    (candidate : Bool)
    (digits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (homogeneous : TGSW.Ciphertext R dimension levels) :
    TGSW.Ciphertext R dimension levels :=
  TGSW.add homogeneous
    (TGSW.internalProductWithDigits digits
      (if candidate then
        ScalarSecretRandomization.negateCiphertext homogeneous
      else homogeneous))

@[simp]
theorem signedValue_false {R : Type} [Ring R] (value : R) :
    signedValue false value = value := by
  simp [signedValue]

@[simp]
theorem signedValue_true {R : Type} [Ring R] (value : R) :
    signedValue true value = -value := by
  simp [signedValue]

/-- The complete ciphertext transform applies `rowOperator` independently to every mask column
and to the body column. -/
theorem homogeneousTransform_eq_rowOperator {R : Type} [CommRing R]
    {dimension levels : ℕ} (candidate : Bool)
    (digits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (homogeneous : TGSW.Ciphertext R dimension levels) :
    homogeneousTransform candidate digits homogeneous =
      (fun coordinate => rowOperator candidate digits (homogeneous.1 coordinate),
        rowOperator candidate digits homogeneous.2) := by
  cases candidate <;> apply Prod.ext
  · funext coordinate row
    change homogeneous.1 coordinate row +
        (∑ index, digits row index.1 index.2 *
          homogeneous.1 coordinate (finProdFinEquiv index)) =
      homogeneous.1 coordinate row +
        (∑ index, digits row index.1 index.2 *
          homogeneous.1 coordinate (finProdFinEquiv index))
    rfl
  · funext row
    change homogeneous.2 row +
        (∑ index, digits row index.1 index.2 *
          homogeneous.2 (finProdFinEquiv index)) =
      homogeneous.2 row +
        (∑ index, digits row index.1 index.2 *
          homogeneous.2 (finProdFinEquiv index))
    rfl
  · funext coordinate row
    change homogeneous.1 coordinate row +
        (∑ index, digits row index.1 index.2 *
          (-homogeneous.1 coordinate (finProdFinEquiv index))) =
      homogeneous.1 coordinate row +
        (∑ index, digits row index.1 index.2 *
          (-homogeneous.1 coordinate (finProdFinEquiv index)))
    rfl
  · funext row
    change homogeneous.2 row +
        (∑ index, digits row index.1 index.2 *
          (-homogeneous.2 (finProdFinEquiv index))) =
      homogeneous.2 row +
        (∑ index, digits row index.1 index.2 *
          (-homogeneous.2 (finProdFinEquiv index)))
    rfl

/-- The row operator is additive. -/
theorem rowOperator_add {R : Type} [CommRing R] {dimension levels : ℕ}
    (candidate : Bool)
    (digits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (left right : Fin (TGSW.rowCount dimension levels) → R) :
    rowOperator candidate digits (left + right) =
      rowOperator candidate digits left + rowOperator candidate digits right := by
  funext row
  simp only [rowOperator, Pi.add_apply]
  cases candidate <;>
    simp only [signedValue_false, signedValue_true, neg_add_rev,
      mul_add, Finset.sum_add_distrib] <;> ring

/-- The candidate-dependent sign commutes with a finite linear combination. -/
theorem signedValue_sum_mul {R Index : Type} [CommRing R] [Fintype Index]
    (candidate : Bool) (coefficient values : Index → R) :
    signedValue candidate (∑ index, coefficient index * values index) =
      ∑ index, coefficient index * signedValue candidate (values index) := by
  cases candidate
  · simp
  · simp only [signedValue_true, mul_neg, Finset.sum_neg_distrib]

/-- Applying the row operator to the shared-secret mask product commutes with forming that
product from the transformed challenge matrix. -/
theorem rowOperator_vecMul {R : Type} [CommRing R] {dimension levels : ℕ}
    (candidate : Bool)
    (digits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (secret : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R) :
    rowOperator candidate digits (Matrix.vecMul secret challenge) =
      Matrix.vecMul secret (challengeOperator candidate digits challenge) := by
  funext row
  simp only [rowOperator, challengeOperator, Matrix.vecMul, dotProduct]
  simp_rw [signedValue_sum_mul]
  simp_rw [Finset.mul_sum, mul_add]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro coordinate _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro index _
  ring

/-- Exact assembly normal form: the same selected-diagonal operator transforms the public
challenge matrix and the error vector. -/
theorem homogeneousTransform_batchAssemble_zero {R : Type} [CommRing R]
    {dimension levels : ℕ} (candidate : Bool)
    (digits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (secret : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R)
    (error : Fin (TGSW.rowCount dimension levels) → R) :
    homogeneousTransform candidate digits
        (TLWE.batchAssemble secret challenge 0 error) =
      TLWE.batchAssemble secret
        (challengeOperator candidate digits challenge) 0
        (rowOperator candidate digits error) := by
  rw [homogeneousTransform_eq_rowOperator]
  apply Prod.ext
  · rfl
  · funext row
    simp only [TLWE.batchAssemble, add_zero, Pi.add_apply]
    rw [← rowOperator_vecMul candidate digits secret challenge,
      ← Pi.add_apply, ← rowOperator_add]

/-- Adding a homogeneous perturbation after attaching a gadget message is the same as attaching
the gadget message after the homogeneous addition. -/
theorem add_addGadget {R : Type} [CommRing R] {dimension levels : ℕ}
    (gadget : Fin levels → R) (message : R)
    (homogeneous perturbation : TGSW.Ciphertext R dimension levels) :
    TGSW.add (TGSW.addGadget gadget message homogeneous) perturbation =
      TGSW.addGadget gadget message (TGSW.add homogeneous perturbation) := by
  apply Prod.ext
  · funext coordinate row
    change (homogeneous.1 coordinate row +
        TGSW.gadgetMaskShift gadget message coordinate row) +
        perturbation.1 coordinate row =
      (homogeneous.1 coordinate row + perturbation.1 coordinate row) +
        TGSW.gadgetMaskShift gadget message coordinate row
    abel
  · funext row
    change (homogeneous.2 row + TGSW.gadgetBodyShift gadget message row) +
        perturbation.2 row =
      (homogeneous.2 row + perturbation.2 row) +
        TGSW.gadgetBodyShift gadget message row
    abel

/-- Exact digits seen by the selected diagonal after independent-difference
reparameterization. -/
def differenceEntryDigits [NeZero q]
    (params : Gadget.Base.Parameters q)
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    Fin (TGSW.rowCount ringRank params.levels) →
      Fin (ringRank + 1) → Fin params.levels → RLWE.Rq q (degree + 1) :=
  fun row => Gadget.Base.ringExtendedDigits params (TLWE.entry difference row)

/-- Correct toggling removes the selected structured control's gadget message and leaves only
its candidate-dependent signed homogeneous part. -/
theorem candidateHomogeneousPart_structured_correct [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (homogeneous : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    candidateHomogeneousPart params proofZero candidate
        (TGSW.addGadget (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) candidate) homogeneous) =
      if candidate then ScalarSecretRandomization.negateCiphertext homogeneous
      else homogeneous := by
  rw [BlindRotation.embedConstantBit_eq_embedBit]
  unfold candidateHomogeneousPart
  rw [proofNeg_eq_neg, proofZero_eq_zero, neg_zero]
  unfold proofAddGadget candidateControl
  rw [TGSW.addGadget_zero]
  simpa only [TGSW.addGadget_zero] using
    (toggleTGSW_correct (Gadget.Base.ringGadget params) candidate homogeneous)

/-- The concrete diagonal perturbation of a structured correct control is the internal product
of the fixed difference digits with the signed homogeneous source. -/
theorem controlPerturbation_structured_correct [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (homogeneous difference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    OffDiagonalNormalForm.controlPerturbation params candidate
        (TGSW.addGadget (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) candidate) homogeneous)
        difference =
      TGSW.internalProductWithDigits (differenceEntryDigits params difference)
        (if candidate then ScalarSecretRandomization.negateCiphertext homogeneous
        else homogeneous) := by
  unfold OffDiagonalNormalForm.controlPerturbation differenceEntryDigits
  rw [candidateHomogeneousPart_structured_correct]

/-- Complete selected-diagonal identity for a structured source ciphertext. -/
theorem add_controlPerturbation_structured_correct [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (homogeneous difference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    TGSW.add
        (TGSW.addGadget (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) candidate) homogeneous)
        (OffDiagonalNormalForm.controlPerturbation params candidate
          (TGSW.addGadget (Gadget.Base.ringGadget params)
            (embedConstantBit q (degree + 1) candidate) homogeneous)
          difference) =
      TGSW.addGadget (Gadget.Base.ringGadget params)
        (embedConstantBit q (degree + 1) candidate)
        (homogeneousTransform candidate (differenceEntryDigits params difference)
          homogeneous) := by
  rw [controlPerturbation_structured_correct, add_addGadget]
  rfl

/-- Difference-first normal form of the selected diagonal.  Conditional on the complete uniform
difference ciphertext, the homogeneous source is transformed by `rowOperator`. -/
noncomputable def operatorDiagonalExperiment [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    ProbComp (RingGSWCiphertext q (degree + 1) ringRank params.levels) := do
  let difference ←
    $ᵗ RingGSWCiphertext q (degree + 1) ringRank params.levels
  let homogeneous ←
    TLWE.batchEncrypt ringRank (TGSW.rowCount ringRank params.levels)
      sourceErrorSampler (embedRingSecret q ringSecret) 0
  return TGSW.addGadget (Gadget.Base.ringGadget params)
    (embedConstantBit q (degree + 1) candidate)
    (homogeneousTransform candidate (differenceEntryDigits params difference)
      homogeneous)

set_option maxHeartbeats 800000 in
/-- The actual averaged self-correlated diagonal is exactly the difference-first linear-operator
experiment. -/
theorem diagonalExperiment_evalDist_eq_operator [NeZero q]
    {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    evalDist
        (OffDiagonalNormalForm.diagonalExperiment params sourceErrorSampler
          hidden ringSecret coordinate) =
      evalDist
        (operatorDiagonalExperiment params sourceErrorSampler
          (hidden coordinate) ringSecret) := by
  let candidate := hidden coordinate
  let message := embedConstantBit q (degree + 1) candidate
  let secret := embedRingSecret q ringSecret
  let Difference : ProbComp
      (RingGSWCiphertext q (degree + 1) ringRank params.levels) :=
    $ᵗ RingGSWCiphertext q (degree + 1) ringRank params.levels
  let Direct := TGSW.directEncrypt ringRank params.levels sourceErrorSampler
    secret (Gadget.Base.ringGadget params) message
  let Structured := TGSW.encrypt ringRank params.levels sourceErrorSampler
    secret (Gadget.Base.ringGadget params) message
  let finish := fun
      (control difference :
        RingGSWCiphertext q (degree + 1) ringRank params.levels) =>
    (pure (TGSW.add control
      (OffDiagonalNormalForm.controlPerturbation params candidate control difference)) :
      ProbComp (RingGSWCiphertext q (degree + 1) ringRank params.levels))
  have hStart :
      evalDist
          (OffDiagonalNormalForm.diagonalExperiment params sourceErrorSampler
            hidden ringSecret coordinate) =
        evalDist (Direct >>= fun control => Difference >>= finish control) := by
    simp [OffDiagonalNormalForm.diagonalExperiment,
      OffDiagonalNormalForm.factorizedCoordinateSampler,
      OffDiagonalNormalForm.directEntrySampler, Direct, Difference, finish,
      candidate, message, secret]
  rw [hStart]
  calc
    _ = evalDist (Difference >>= fun difference =>
        Direct >>= fun control => finish control difference) :=
      evalDist_bind_bind_swap Direct Difference finish
    _ = evalDist (Difference >>= fun difference =>
        Structured >>= fun control => finish control difference) := by
      refine evalDist_bind_congr' Difference fun difference => ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        (TGSW.encrypt_evalDist_eq_directEncrypt ringRank params.levels
          sourceErrorSampler secret (Gadget.Base.ringGadget params) message).symm
        (fun control => finish control difference)
    _ = evalDist
        (operatorDiagonalExperiment params sourceErrorSampler candidate ringSecret) := by
      unfold operatorDiagonalExperiment Structured TGSW.encrypt
      simp only [bind_assoc, pure_bind]
      refine evalDist_bind_congr' Difference fun difference => ?_
      refine evalDist_bind_congr'
        (TLWE.batchEncrypt ringRank (TGSW.rowCount ringRank params.levels)
          sourceErrorSampler secret 0) fun homogeneous => ?_
      apply congrArg evalDist
      apply congrArg pure
      simpa only [finish, candidate, message, secret] using
        (add_controlPerturbation_structured_correct
          params candidate homogeneous difference)

/-- Public mask-matrix space of one selected native TGSW entry. -/
abbrev DiagonalChallenge (q degree ringRank levels : ℕ) :=
  Matrix (Fin ringRank)
    (Fin (TGSW.rowCount ringRank levels)) (RLWE.Rq q (degree + 1))

/-- Error-vector space of one selected native TGSW entry. -/
abbrev DiagonalErrorVector (q degree ringRank levels : ℕ) :=
  Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1)

/-- Conditional selected-diagonal sampler after fixing the complete uniform difference
ciphertext.  Its transformed challenge and transformed source errors remain independent. -/
noncomputable def conditionalOperatorExperiment [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    ProbComp (RingGSWCiphertext q (degree + 1) ringRank params.levels) :=
  SamplerReplacement.independentPair
    (challengeOperator candidate (differenceEntryDigits params difference) <$>
      ($ᵗ DiagonalChallenge q degree ringRank params.levels))
    (rowOperator candidate (differenceEntryDigits params difference) <$>
      ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) sourceErrorSampler)
    (fun challenge error =>
      TGSW.addGadget (Gadget.Base.ringGadget params)
        (embedConstantBit q (degree + 1) candidate)
        (TLWE.batchAssemble (embedRingSecret q ringSecret) challenge 0 error))

/-- Fiber second moment of the fixed-difference linear map on the complete public challenge
matrix. -/
noncomputable def diagonalChallengeFiberSecondMoment [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ :=
  FormalProof4FHE.LeftoverHash.fiberSecondMoment
    (challengeOperator candidate (differenceEntryDigits params difference) :
      DiagonalChallenge q degree ringRank params.levels →
        DiagonalChallenge q degree ringRank params.levels)

/-- Collision/fiber loss for the transformed uniform public challenge matrix. -/
noncomputable def diagonalChallengeFiberLoss [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ :=
  Real.sqrt
      (diagonalChallengeFiberSecondMoment params candidate difference /
          Fintype.card (DiagonalChallenge q degree ringRank params.levels) - 1) /
    2

/-- Distance between the fixed-difference transformed source-error vector and fresh independent
target errors. -/
noncomputable def diagonalErrorVectorDistance [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ :=
  tvDist
    (rowOperator candidate (differenceEntryDigits params difference) <$>
      ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) sourceErrorSampler)
    (ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) targetErrorSampler)

/-- Complete fixed-difference diagonal loss: public-mask fiber defect plus transformed-error
distance. -/
noncomputable def conditionalDiagonalOperatorLoss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ :=
  diagonalChallengeFiberLoss params candidate difference +
    diagonalErrorVectorDistance params sourceErrorSampler targetErrorSampler
      candidate difference

/-- Exact average of the conditional diagonal-operator losses under the evaluator's complete
uniform difference ciphertext. -/
noncomputable def averagedDiagonalOperatorLoss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) : ℝ :=
  ∑' difference : RingGSWCiphertext q (degree + 1) ringRank params.levels,
    Pr[= difference |
      ($ᵗ RingGSWCiphertext q (degree + 1) ringRank params.levels)].toReal *
      conditionalDiagonalOperatorLoss params sourceErrorSampler targetErrorSampler
        candidate difference

/-- A coordinate-independent diagonal budget covering both possible encrypted scalar bits. -/
noncomputable def worstCaseDiagonalOperatorLoss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))) : ℝ :=
  max
    (averagedDiagonalOperatorLoss (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler false)
    (averagedDiagonalOperatorLoss (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler true)

theorem diagonalChallengeFiberLoss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    0 ≤ diagonalChallengeFiberLoss params candidate difference := by
  exact div_nonneg (Real.sqrt_nonneg _) (by norm_num)

theorem diagonalErrorVectorDistance_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    0 ≤ diagonalErrorVectorDistance params sourceErrorSampler targetErrorSampler
      candidate difference :=
  tvDist_nonneg _ _

theorem conditionalDiagonalOperatorLoss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    0 ≤ conditionalDiagonalOperatorLoss params sourceErrorSampler targetErrorSampler
      candidate difference :=
  add_nonneg (diagonalChallengeFiberLoss_nonneg params candidate difference)
    (diagonalErrorVectorDistance_nonneg params sourceErrorSampler targetErrorSampler
      candidate difference)

theorem averagedDiagonalOperatorLoss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) :
    0 ≤ averagedDiagonalOperatorLoss (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler candidate := by
  unfold averagedDiagonalOperatorLoss
  exact tsum_nonneg fun difference =>
    mul_nonneg ENNReal.toReal_nonneg
      (conditionalDiagonalOperatorLoss_nonneg params sourceErrorSampler
        targetErrorSampler candidate difference)

theorem worstCaseDiagonalOperatorLoss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))) :
    0 ≤ worstCaseDiagonalOperatorLoss (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler := by
  exact (averagedDiagonalOperatorLoss_nonneg (ringRank := ringRank) params
    sourceErrorSampler targetErrorSampler false).trans
      (le_max_left _ _)

/-- The transformed uniform challenge matrix is controlled by the exact fiber-second-moment
excess of its fixed-difference row operator. -/
theorem tvDist_transformedChallenge_uniform_le_fiberLoss [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    tvDist
        (challengeOperator candidate (differenceEntryDigits params difference) <$>
          ($ᵗ DiagonalChallenge q degree ringRank params.levels))
        ($ᵗ DiagonalChallenge q degree ringRank params.levels) ≤
      diagonalChallengeFiberLoss params candidate difference := by
  simpa only [diagonalChallengeFiberLoss,
    diagonalChallengeFiberSecondMoment] using
    (FormalProof4FHE.LeftoverHash.tvDist_map_uniform_le_sqrt_fiberExcess
      (challengeOperator candidate (differenceEntryDigits params difference) :
        DiagonalChallenge q degree ringRank params.levels →
          DiagonalChallenge q degree ringRank params.levels))

/-- Conditional on one fixed difference ciphertext, independent replacement of the transformed
public mask and transformed error vector bounds the complete selected-diagonal ciphertext. -/
theorem tvDist_conditionalOperator_target_le [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    tvDist
        (conditionalOperatorExperiment params sourceErrorSampler candidate
          ringSecret difference)
        (TGSW.encrypt ringRank params.levels targetErrorSampler
          (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) candidate)) ≤
      conditionalDiagonalOperatorLoss params sourceErrorSampler targetErrorSampler
        candidate difference := by
  let Challenge : ProbComp (DiagonalChallenge q degree ringRank params.levels) :=
    $ᵗ DiagonalChallenge q degree ringRank params.levels
  let SourceErrors : ProbComp (DiagonalErrorVector q degree ringRank params.levels) :=
    ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) sourceErrorSampler
  let TargetErrors : ProbComp (DiagonalErrorVector q degree ringRank params.levels) :=
    ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) targetErrorSampler
  let transformChallenge :=
    challengeOperator candidate (differenceEntryDigits params difference)
  let transformError :=
    rowOperator candidate (differenceEntryDigits params difference)
  let combine := fun
      (challenge : DiagonalChallenge q degree ringRank params.levels)
      (error : DiagonalErrorVector q degree ringRank params.levels) =>
    TGSW.addGadget (Gadget.Base.ringGadget params)
      (embedConstantBit q (degree + 1) candidate)
      (TLWE.batchAssemble (embedRingSecret q ringSecret) challenge 0 error)
  have hPair := SamplerReplacement.tvDist_independentPair_le
    (transformChallenge <$> Challenge) Challenge
    (transformError <$> SourceErrors) TargetErrors combine
  have hMask : tvDist (transformChallenge <$> Challenge) Challenge ≤
      diagonalChallengeFiberLoss params candidate difference := by
    simpa only [Challenge, transformChallenge] using
      (tvDist_transformedChallenge_uniform_le_fiberLoss
        params candidate difference)
  have hBound := hPair.trans (add_le_add hMask le_rfl)
  have hTarget :
      TGSW.encrypt ringRank params.levels targetErrorSampler
          (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) candidate) =
        SamplerReplacement.independentPair Challenge TargetErrors combine := by
    simp [TGSW.encrypt, TLWE.batchEncrypt, SamplerReplacement.independentPair,
      Challenge, TargetErrors, combine, monad_norm]
  rw [hTarget]
  simpa only [conditionalOperatorExperiment, conditionalDiagonalOperatorLoss,
    diagonalErrorVectorDistance, Challenge, SourceErrors, TargetErrors,
    transformChallenge, transformError, combine] using hBound

/-- Expanding the source batch sampler and applying the deterministic assembly identity gives
the shared-difference mixture of conditional operator experiments exactly. -/
theorem operatorDiagonalExperiment_evalDist_eq_conditioned [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    evalDist (operatorDiagonalExperiment params sourceErrorSampler candidate ringSecret) =
      evalDist
        (($ᵗ RingGSWCiphertext q (degree + 1) ringRank params.levels) >>= fun difference =>
          conditionalOperatorExperiment params sourceErrorSampler candidate
            ringSecret difference) := by
  unfold operatorDiagonalExperiment conditionalOperatorExperiment
  simp only [TLWE.batchEncrypt, SamplerReplacement.independentPair,
    map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  refine evalDist_bind_congr'
    ($ᵗ RingGSWCiphertext q (degree + 1) ringRank params.levels) fun difference => ?_
  refine evalDist_bind_congr'
    ($ᵗ DiagonalChallenge q degree ringRank params.levels) fun challenge => ?_
  refine evalDist_bind_congr'
    (ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) sourceErrorSampler) fun error => ?_
  apply congrArg evalDist
  apply congrArg pure
  exact congrArg
    (TGSW.addGadget (Gadget.Base.ringGadget params)
      (embedConstantBit q (degree + 1) candidate))
    (homogeneousTransform_batchAssemble_zero candidate
      (differenceEntryDigits params difference) (embedRingSecret q ringSecret)
      challenge error)

/-- Averaging the fixed-difference mask-fiber and transformed-error bounds controls the complete
selected diagonal against a fresh target-noise structured TGSW entry. -/
theorem tvDist_operatorDiagonalExperiment_target_le_averaged [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    tvDist
        (operatorDiagonalExperiment params sourceErrorSampler candidate ringSecret)
        (TGSW.encrypt ringRank params.levels targetErrorSampler
          (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) candidate)) ≤
      averagedDiagonalOperatorLoss (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler candidate := by
  let Difference : ProbComp
      (RingGSWCiphertext q (degree + 1) ringRank params.levels) :=
    $ᵗ RingGSWCiphertext q (degree + 1) ringRank params.levels
  let Conditional := fun
      difference : RingGSWCiphertext q (degree + 1) ringRank params.levels =>
    conditionalOperatorExperiment params sourceErrorSampler candidate
      ringSecret difference
  let Target := TGSW.encrypt ringRank params.levels targetErrorSampler
    (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
    (embedConstantBit q (degree + 1) candidate)
  have hMixture :=
    FormalProof4FHE.FiniteProduct.tvDist_bind_left_le_expectation
      Difference Conditional (fun _ => Target)
  have hAverage :
      (∑' difference,
          Pr[= difference | Difference].toReal *
            tvDist (Conditional difference) Target) ≤
        averagedDiagonalOperatorLoss (ringRank := ringRank) params
          sourceErrorSampler targetErrorSampler candidate := by
    unfold averagedDiagonalOperatorLoss
    apply Summable.tsum_le_tsum
    · intro difference
      exact mul_le_mul_of_nonneg_left
        (tvDist_conditionalOperator_target_le params sourceErrorSampler
          targetErrorSampler candidate ringSecret difference)
        ENNReal.toReal_nonneg
    · exact Summable.of_finite
    · exact Summable.of_finite
  have hBound := hMixture.trans hAverage
  have hTargetConst :
      evalDist (Difference >>= fun _ => Target) = evalDist Target :=
    FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
      Difference (by simp [Difference]) Target
  unfold tvDist at hBound ⊢
  rw [← hTargetConst]
  rw [operatorDiagonalExperiment_evalDist_eq_conditioned
    params sourceErrorSampler candidate ringSecret]
  simpa only [Difference, Conditional, Target] using hBound

/-- **Selected-diagonal finite reduction.**  The actual self-correlated diagonal is close to one
fresh direct target entry by the explicit average of its public-mask fiber loss and transformed
source-to-target error-vector distance. -/
theorem tvDist_diagonalExperiment_directEntry_le_averagedOperatorLoss [NeZero q]
    {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    tvDist
        (OffDiagonalNormalForm.diagonalExperiment params sourceErrorSampler
          hidden ringSecret coordinate)
        (OffDiagonalNormalForm.directEntrySampler params targetErrorSampler
          hidden ringSecret coordinate) ≤
      averagedDiagonalOperatorLoss (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler (hidden coordinate) := by
  have h := tvDist_operatorDiagonalExperiment_target_le_averaged
    params sourceErrorSampler targetErrorSampler (hidden coordinate) ringSecret
  unfold tvDist at h ⊢
  rw [diagonalExperiment_evalDist_eq_operator
    params sourceErrorSampler hidden ringSecret coordinate]
  unfold OffDiagonalNormalForm.directEntrySampler
  rw [← TGSW.encrypt_evalDist_eq_directEncrypt ringRank params.levels
    targetErrorSampler (embedRingSecret q ringSecret)
    (Gadget.Base.ringGadget params)
    (embedConstantBit q (degree + 1) (hidden coordinate))]
  exact h

/-- Uniform form of the selected-diagonal reduction, suitable for a whole-key certificate that
must quantify over every hidden key. -/
theorem tvDist_diagonalExperiment_directEntry_le_worstCaseOperatorLoss [NeZero q]
    {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    tvDist
        (OffDiagonalNormalForm.diagonalExperiment params sourceErrorSampler
          hidden ringSecret coordinate)
        (OffDiagonalNormalForm.directEntrySampler params targetErrorSampler
          hidden ringSecret coordinate) ≤
      worstCaseDiagonalOperatorLoss (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler := by
  have h := tvDist_diagonalExperiment_directEntry_le_averagedOperatorLoss
    params sourceErrorSampler targetErrorSampler hidden ringSecret coordinate
  cases hbit : hidden coordinate
  · exact h.trans (by
      simpa only [hbit, worstCaseDiagonalOperatorLoss] using
        (le_max_left
          (averagedDiagonalOperatorLoss (ringRank := ringRank) params
            sourceErrorSampler targetErrorSampler false)
          (averagedDiagonalOperatorLoss (ringRank := ringRank) params
            sourceErrorSampler targetErrorSampler true)))
  · exact h.trans (by
      simpa only [hbit, worstCaseDiagonalOperatorLoss] using
        (le_max_right
          (averagedDiagonalOperatorLoss (ringRank := ringRank) params
            sourceErrorSampler targetErrorSampler false)
          (averagedDiagonalOperatorLoss (ringRank := ringRank) params
            sourceErrorSampler targetErrorSampler true)))

/-! ## Sharper marginal-error reduction

The preceding conditional bound is useful but may overcount: the mixture over the uniform
difference ciphertext can itself smooth the transformed source-error law.  The following
hybrid replaces only the public challenge conditionally, then drops the difference and compares
the resulting mixed error marginal with the target error vector.
-/

/-- Conditional experiment after replacing only the transformed public challenge by a fresh
uniform challenge.  The fixed-difference transformed source error remains unchanged. -/
noncomputable def maskReplacedConditionalExperiment [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    ProbComp (RingGSWCiphertext q (degree + 1) ringRank params.levels) :=
  SamplerReplacement.independentPair
    ($ᵗ DiagonalChallenge q degree ringRank params.levels)
    (rowOperator candidate (differenceEntryDigits params difference) <$>
      ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) sourceErrorSampler)
    (fun challenge error =>
      TGSW.addGadget (Gadget.Base.ringGadget params)
        (embedConstantBit q (degree + 1) candidate)
        (TLWE.batchAssemble (embedRingSecret q ringSecret) challenge 0 error))

/-- Marginal transformed-error sampler retaining all smoothing from the evaluator's uniform
difference ciphertext. -/
noncomputable def mixedDiagonalErrorSampler [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) :
    ProbComp (DiagonalErrorVector q degree ringRank params.levels) := do
  let difference ←
    $ᵗ RingGSWCiphertext q (degree + 1) ringRank params.levels
  rowOperator candidate (differenceEntryDigits params difference) <$>
    ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) sourceErrorSampler

/-- Complete mask-replaced diagonal experiment, with the now-hidden difference retained only
inside its transformed-error marginal. -/
noncomputable def maskReplacedDiagonalExperiment [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    ProbComp (RingGSWCiphertext q (degree + 1) ringRank params.levels) :=
  SamplerReplacement.independentPair
    ($ᵗ DiagonalChallenge q degree ringRank params.levels)
    (mixedDiagonalErrorSampler (ringRank := ringRank) params
      sourceErrorSampler candidate)
    (fun challenge error =>
      TGSW.addGadget (Gadget.Base.ringGadget params)
        (embedConstantBit q (degree + 1) candidate)
        (TLWE.batchAssemble (embedRingSecret q ringSecret) challenge 0 error))

/-- Expected challenge-map fiber loss, retaining no conditional error-distance term. -/
noncomputable def averagedDiagonalChallengeFiberLoss [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool) : ℝ :=
  ∑' difference : RingGSWCiphertext q (degree + 1) ringRank params.levels,
    Pr[= difference |
      ($ᵗ RingGSWCiphertext q (degree + 1) ringRank params.levels)].toReal *
      diagonalChallengeFiberLoss params candidate difference

/-- Distance from the full mixed transformed-error marginal to fresh independent target
errors. -/
noncomputable def mixedDiagonalErrorDistance [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) : ℝ :=
  tvDist
    (mixedDiagonalErrorSampler (ringRank := ringRank) params
      sourceErrorSampler candidate)
    (ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) targetErrorSampler)

/-- Sharper selected-diagonal budget: average only the mask-fiber loss, then compare the entire
mixed transformed-error marginal once. -/
noncomputable def sharpDiagonalOperatorLoss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) : ℝ :=
  averagedDiagonalChallengeFiberLoss (degree := degree) (ringRank := ringRank)
      params candidate +
    mixedDiagonalErrorDistance (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler candidate

/-- Coordinate-independent sharp diagonal budget covering both encrypted scalar bits. -/
noncomputable def worstCaseSharpDiagonalOperatorLoss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))) : ℝ :=
  max
    (sharpDiagonalOperatorLoss (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler false)
    (sharpDiagonalOperatorLoss (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler true)

/-- Replacing only the fixed-difference transformed challenge costs at most its fiber loss. -/
theorem tvDist_conditionalOperator_maskReplaced_le_fiberLoss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    tvDist
        (conditionalOperatorExperiment params sourceErrorSampler candidate
          ringSecret difference)
        (maskReplacedConditionalExperiment params sourceErrorSampler candidate
          ringSecret difference) ≤
      diagonalChallengeFiberLoss params candidate difference := by
  let Challenge : ProbComp (DiagonalChallenge q degree ringRank params.levels) :=
    $ᵗ DiagonalChallenge q degree ringRank params.levels
  let Errors : ProbComp (DiagonalErrorVector q degree ringRank params.levels) :=
    rowOperator candidate (differenceEntryDigits params difference) <$>
      ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) sourceErrorSampler
  let transformChallenge :=
    challengeOperator candidate (differenceEntryDigits params difference)
  let combine := fun
      (challenge : DiagonalChallenge q degree ringRank params.levels)
      (error : DiagonalErrorVector q degree ringRank params.levels) =>
    TGSW.addGadget (Gadget.Base.ringGadget params)
      (embedConstantBit q (degree + 1) candidate)
      (TLWE.batchAssemble (embedRingSecret q ringSecret) challenge 0 error)
  have hPair := SamplerReplacement.tvDist_independentPair_le
    (transformChallenge <$> Challenge) Challenge Errors Errors combine
  calc
    _ ≤ tvDist (transformChallenge <$> Challenge) Challenge + tvDist Errors Errors := by
      simpa only [conditionalOperatorExperiment, maskReplacedConditionalExperiment,
        Challenge, Errors, transformChallenge, combine] using hPair
    _ = tvDist (transformChallenge <$> Challenge) Challenge := by
      rw [tvDist_self, add_zero]
    _ ≤ _ := by
      simpa only [Challenge, transformChallenge] using
        (tvDist_transformedChallenge_uniform_le_fiberLoss
          params candidate difference)

/-- Once the public challenge is replaced, the uniform difference can be hidden entirely inside
the marginal transformed-error sampler. -/
theorem bind_maskReplacedConditional_evalDist_eq_maskReplacedDiagonal [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    evalDist
        (($ᵗ RingGSWCiphertext q (degree + 1) ringRank params.levels) >>= fun difference =>
          maskReplacedConditionalExperiment params sourceErrorSampler candidate
            ringSecret difference) =
      evalDist
        (maskReplacedDiagonalExperiment (ringRank := ringRank) params
          sourceErrorSampler candidate ringSecret) := by
  let Difference : ProbComp
      (RingGSWCiphertext q (degree + 1) ringRank params.levels) :=
    $ᵗ RingGSWCiphertext q (degree + 1) ringRank params.levels
  let Challenge : ProbComp (DiagonalChallenge q degree ringRank params.levels) :=
    $ᵗ DiagonalChallenge q degree ringRank params.levels
  let SourceErrors : ProbComp (DiagonalErrorVector q degree ringRank params.levels) :=
    ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) sourceErrorSampler
  let Errors := fun
      difference : RingGSWCiphertext q (degree + 1) ringRank params.levels =>
    rowOperator candidate (differenceEntryDigits params difference) <$> SourceErrors
  let combine := fun
      (challenge : DiagonalChallenge q degree ringRank params.levels)
      (error : DiagonalErrorVector q degree ringRank params.levels) =>
    TGSW.addGadget (Gadget.Base.ringGadget params)
      (embedConstantBit q (degree + 1) candidate)
      (TLWE.batchAssemble (embedRingSecret q ringSecret) challenge 0 error)
  let finish := fun
      (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels)
      (challenge : DiagonalChallenge q degree ringRank params.levels) =>
    combine challenge <$> Errors difference
  have hSwap := evalDist_bind_bind_swap Difference Challenge finish
  simpa [maskReplacedConditionalExperiment, maskReplacedDiagonalExperiment,
    mixedDiagonalErrorSampler, SamplerReplacement.independentPair,
    Difference, Challenge, SourceErrors, Errors, combine, finish,
    map_eq_bind_pure_comp, bind_assoc, monad_norm] using hSwap

/-- Replacing the transformed public challenge throughout the diagonal mixture costs only the
expected challenge fiber loss. -/
theorem tvDist_operatorDiagonal_maskReplaced_le_averagedFiber [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    tvDist
        (operatorDiagonalExperiment params sourceErrorSampler candidate ringSecret)
        (maskReplacedDiagonalExperiment (ringRank := ringRank) params
          sourceErrorSampler candidate ringSecret) ≤
      averagedDiagonalChallengeFiberLoss (degree := degree) (ringRank := ringRank)
        params candidate := by
  let Difference : ProbComp
      (RingGSWCiphertext q (degree + 1) ringRank params.levels) :=
    $ᵗ RingGSWCiphertext q (degree + 1) ringRank params.levels
  let Original := fun
      difference : RingGSWCiphertext q (degree + 1) ringRank params.levels =>
    conditionalOperatorExperiment params sourceErrorSampler candidate
      ringSecret difference
  let Replaced := fun
      difference : RingGSWCiphertext q (degree + 1) ringRank params.levels =>
    maskReplacedConditionalExperiment params sourceErrorSampler candidate
      ringSecret difference
  have hMixture :=
    FormalProof4FHE.FiniteProduct.tvDist_bind_left_le_expectation
      Difference Original Replaced
  have hAverage :
      (∑' difference,
          Pr[= difference | Difference].toReal *
            tvDist (Original difference) (Replaced difference)) ≤
        averagedDiagonalChallengeFiberLoss (degree := degree) (ringRank := ringRank)
          params candidate := by
    unfold averagedDiagonalChallengeFiberLoss
    apply Summable.tsum_le_tsum
    · intro difference
      exact mul_le_mul_of_nonneg_left
        (tvDist_conditionalOperator_maskReplaced_le_fiberLoss
          params sourceErrorSampler candidate ringSecret difference)
        ENNReal.toReal_nonneg
    · exact Summable.of_finite
    · exact Summable.of_finite
  have hBound := hMixture.trans hAverage
  unfold tvDist at hBound ⊢
  rw [operatorDiagonalExperiment_evalDist_eq_conditioned
    params sourceErrorSampler candidate ringSecret]
  rw [← bind_maskReplacedConditional_evalDist_eq_maskReplacedDiagonal
    params sourceErrorSampler candidate ringSecret]
  simpa only [Difference, Original, Replaced] using hBound

/-- After mask replacement, shared fresh masks add no loss: only the mixed transformed-error
marginal must be compared with the target independent errors. -/
theorem tvDist_maskReplacedDiagonal_target_le_mixedError [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    tvDist
        (maskReplacedDiagonalExperiment (ringRank := ringRank) params
          sourceErrorSampler candidate ringSecret)
        (TGSW.encrypt ringRank params.levels targetErrorSampler
          (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) candidate)) ≤
      mixedDiagonalErrorDistance (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler candidate := by
  let Challenge : ProbComp (DiagonalChallenge q degree ringRank params.levels) :=
    $ᵗ DiagonalChallenge q degree ringRank params.levels
  let MixedErrors : ProbComp (DiagonalErrorVector q degree ringRank params.levels) :=
    mixedDiagonalErrorSampler (ringRank := ringRank) params
      sourceErrorSampler candidate
  let TargetErrors : ProbComp (DiagonalErrorVector q degree ringRank params.levels) :=
    ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) targetErrorSampler
  let combine := fun
      (challenge : DiagonalChallenge q degree ringRank params.levels)
      (error : DiagonalErrorVector q degree ringRank params.levels) =>
    TGSW.addGadget (Gadget.Base.ringGadget params)
      (embedConstantBit q (degree + 1) candidate)
      (TLWE.batchAssemble (embedRingSecret q ringSecret) challenge 0 error)
  have hPair := SamplerReplacement.tvDist_independentPair_le
    Challenge Challenge MixedErrors TargetErrors combine
  have hTarget :
      TGSW.encrypt ringRank params.levels targetErrorSampler
          (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) candidate) =
        SamplerReplacement.independentPair Challenge TargetErrors combine := by
    simp [TGSW.encrypt, TLWE.batchEncrypt, SamplerReplacement.independentPair,
      Challenge, TargetErrors, combine, monad_norm]
  rw [hTarget]
  calc
    _ ≤ tvDist Challenge Challenge + tvDist MixedErrors TargetErrors := by
      simpa only [maskReplacedDiagonalExperiment, Challenge, MixedErrors,
        TargetErrors, combine] using hPair
    _ = tvDist MixedErrors TargetErrors := by rw [tvDist_self, zero_add]
    _ = _ := by
      rfl

theorem averagedDiagonalChallengeFiberLoss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool) :
    0 ≤ averagedDiagonalChallengeFiberLoss (degree := degree) (ringRank := ringRank)
      params candidate := by
  unfold averagedDiagonalChallengeFiberLoss
  exact tsum_nonneg fun difference =>
    mul_nonneg ENNReal.toReal_nonneg
      (diagonalChallengeFiberLoss_nonneg params candidate difference)

theorem mixedDiagonalErrorDistance_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) :
    0 ≤ mixedDiagonalErrorDistance (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler candidate :=
  tvDist_nonneg _ _

theorem sharpDiagonalOperatorLoss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) :
    0 ≤ sharpDiagonalOperatorLoss (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler candidate :=
  add_nonneg
    (averagedDiagonalChallengeFiberLoss_nonneg (ringRank := ringRank) params candidate)
    (mixedDiagonalErrorDistance_nonneg (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler candidate)

theorem worstCaseSharpDiagonalOperatorLoss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))) :
    0 ≤ worstCaseSharpDiagonalOperatorLoss (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler := by
  exact (sharpDiagonalOperatorLoss_nonneg (ringRank := ringRank) params
    sourceErrorSampler targetErrorSampler false).trans (le_max_left _ _)

/-- **Sharp selected-diagonal reduction.**  The public-mask cost is averaged conditionally, but
the random-difference smoothing of the transformed source errors is retained in one marginal
distance. -/
theorem tvDist_operatorDiagonalExperiment_target_le_sharp [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    tvDist
        (operatorDiagonalExperiment params sourceErrorSampler candidate ringSecret)
        (TGSW.encrypt ringRank params.levels targetErrorSampler
          (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) candidate)) ≤
      sharpDiagonalOperatorLoss (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler candidate := by
  let Middle := maskReplacedDiagonalExperiment (ringRank := ringRank) params
    sourceErrorSampler candidate ringSecret
  let Target := TGSW.encrypt ringRank params.levels targetErrorSampler
    (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
    (embedConstantBit q (degree + 1) candidate)
  calc
    _ ≤ tvDist
          (operatorDiagonalExperiment params sourceErrorSampler candidate ringSecret)
          Middle + tvDist Middle Target :=
      tvDist_triangle _ _ _
    _ ≤ averagedDiagonalChallengeFiberLoss (degree := degree)
          (ringRank := ringRank) params candidate +
        mixedDiagonalErrorDistance (ringRank := ringRank) params
          sourceErrorSampler targetErrorSampler candidate :=
      add_le_add
        (tvDist_operatorDiagonal_maskReplaced_le_averagedFiber
          params sourceErrorSampler candidate ringSecret)
        (tvDist_maskReplacedDiagonal_target_le_mixedError
          params sourceErrorSampler targetErrorSampler candidate ringSecret)
    _ = _ := rfl

/-- Sharp reduction for the actual self-correlated diagonal against a fresh direct target
entry. -/
theorem tvDist_diagonalExperiment_directEntry_le_sharpOperatorLoss [NeZero q]
    {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    tvDist
        (OffDiagonalNormalForm.diagonalExperiment params sourceErrorSampler
          hidden ringSecret coordinate)
        (OffDiagonalNormalForm.directEntrySampler params targetErrorSampler
          hidden ringSecret coordinate) ≤
      sharpDiagonalOperatorLoss (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler (hidden coordinate) := by
  have h := tvDist_operatorDiagonalExperiment_target_le_sharp
    params sourceErrorSampler targetErrorSampler (hidden coordinate) ringSecret
  unfold tvDist at h ⊢
  rw [diagonalExperiment_evalDist_eq_operator
    params sourceErrorSampler hidden ringSecret coordinate]
  unfold OffDiagonalNormalForm.directEntrySampler
  rw [← TGSW.encrypt_evalDist_eq_directEncrypt ringRank params.levels
    targetErrorSampler (embedRingSecret q ringSecret)
    (Gadget.Base.ringGadget params)
    (embedConstantBit q (degree + 1) (hidden coordinate))]
  exact h

/-- Uniform sharp selected-diagonal bound for the whole-key certificate. -/
theorem tvDist_diagonalExperiment_directEntry_le_worstCaseSharpOperatorLoss [NeZero q]
    {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    tvDist
        (OffDiagonalNormalForm.diagonalExperiment params sourceErrorSampler
          hidden ringSecret coordinate)
        (OffDiagonalNormalForm.directEntrySampler params targetErrorSampler
          hidden ringSecret coordinate) ≤
      worstCaseSharpDiagonalOperatorLoss (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler := by
  have h := tvDist_diagonalExperiment_directEntry_le_sharpOperatorLoss
    params sourceErrorSampler targetErrorSampler hidden ringSecret coordinate
  cases hbit : hidden coordinate
  · exact h.trans (by
      simpa only [hbit, worstCaseSharpDiagonalOperatorLoss] using
        (le_max_left
          (sharpDiagonalOperatorLoss (ringRank := ringRank) params
            sourceErrorSampler targetErrorSampler false)
          (sharpDiagonalOperatorLoss (ringRank := ringRank) params
            sourceErrorSampler targetErrorSampler true)))
  · exact h.trans (by
      simpa only [hbit, worstCaseSharpDiagonalOperatorLoss] using
        (le_max_right
          (sharpDiagonalOperatorLoss (ringRank := ringRank) params
            sourceErrorSampler targetErrorSampler false)
          (sharpDiagonalOperatorLoss (ringRank := ringRank) params
            sourceErrorSampler targetErrorSampler true)))

/-! ## Exact diagonal rank-failure route -/

/-- Pointwise lifting: if the fixed-difference row operator is bijective, applying it to every
public mask column is bijective on the complete challenge matrix. -/
theorem challengeOperator_bijective_of_rowOperator {R : Type} [CommRing R]
    {dimension levels : ℕ} (candidate : Bool)
    (digits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (hrow : Function.Bijective (rowOperator candidate digits)) :
    Function.Bijective (challengeOperator candidate digits :
      Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R →
        Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R) := by
  constructor
  · intro left right heq
    funext coordinate
    apply hrow.1
    exact congrFun heq coordinate
  · intro output
    choose input hinput using fun coordinate => hrow.2 (output coordinate)
    refine ⟨input, ?_⟩
    funext coordinate
    exact hinput coordinate

/-- A good fixed-difference row rank gives exact uniform transport of the complete public
challenge matrix. -/
theorem transformedChallenge_uniform_evalDist_of_rowOperator_bijective [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels)
    (hrow : Function.Bijective
      (rowOperator candidate (differenceEntryDigits params difference) :
        DiagonalErrorVector q degree ringRank params.levels →
          DiagonalErrorVector q degree ringRank params.levels)) :
    evalDist
        (challengeOperator candidate (differenceEntryDigits params difference) <$>
          ($ᵗ DiagonalChallenge q degree ringRank params.levels)) =
      evalDist ($ᵗ DiagonalChallenge q degree ringRank params.levels) :=
  evalDist_map_bijective_uniform_cross
    (α := DiagonalChallenge q degree ringRank params.levels)
    (β := DiagonalChallenge q degree ringRank params.levels)
    (challengeOperator candidate (differenceEntryDigits params difference))
    (challengeOperator_bijective_of_rowOperator candidate
      (differenceEntryDigits params difference) hrow)

/-- At every good-rank difference, replacing the transformed challenge costs exactly zero while
retaining the same transformed-error continuation. -/
theorem conditionalOperator_maskReplaced_evalDist_of_rowOperator_bijective [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels)
    (hrow : Function.Bijective
      (rowOperator candidate (differenceEntryDigits params difference) :
        DiagonalErrorVector q degree ringRank params.levels →
          DiagonalErrorVector q degree ringRank params.levels)) :
    evalDist
        (conditionalOperatorExperiment params sourceErrorSampler candidate
          ringSecret difference) =
      evalDist
        (maskReplacedConditionalExperiment params sourceErrorSampler candidate
          ringSecret difference) := by
  let Errors : ProbComp (DiagonalErrorVector q degree ringRank params.levels) :=
    rowOperator candidate (differenceEntryDigits params difference) <$>
      ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) sourceErrorSampler
  let combine := fun
      (challenge : DiagonalChallenge q degree ringRank params.levels)
      (error : DiagonalErrorVector q degree ringRank params.levels) =>
    TGSW.addGadget (Gadget.Base.ringGadget params)
      (embedConstantBit q (degree + 1) candidate)
      (TLWE.batchAssemble (embedRingSecret q ringSecret) challenge 0 error)
  have hChallenge :=
    transformedChallenge_uniform_evalDist_of_rowOperator_bijective
      params candidate difference hrow
  have hBind := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    hChallenge (fun challenge => combine challenge <$> Errors)
  simpa only [conditionalOperatorExperiment, maskReplacedConditionalExperiment,
    SamplerReplacement.independentPair, Errors, combine] using hBind

/-- Bad-rank predicate for one uniform difference ciphertext. -/
def DiagonalRowRankFailure [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) : Prop :=
  ¬ Function.Bijective
    (rowOperator candidate (differenceEntryDigits params difference) :
      DiagonalErrorVector q degree ringRank params.levels →
        DiagonalErrorVector q degree ringRank params.levels)

/-- Probability that the exact fixed-difference diagonal row operator is not a permutation. -/
noncomputable def diagonalRowRankFailureProbability [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool) : ℝ :=
  Pr[DiagonalRowRankFailure params candidate |
    ($ᵗ RingGSWCiphertext q (degree + 1) ringRank params.levels)].toReal

/-- The entire diagonal mask-replacement hop is bounded by one exact bad-rank probability. -/
theorem tvDist_operatorDiagonal_maskReplaced_le_rankFailure [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    tvDist
        (operatorDiagonalExperiment params sourceErrorSampler candidate ringSecret)
        (maskReplacedDiagonalExperiment (ringRank := ringRank) params
          sourceErrorSampler candidate ringSecret) ≤
      diagonalRowRankFailureProbability (degree := degree) (ringRank := ringRank)
        params candidate := by
  classical
  let Difference : ProbComp
      (RingGSWCiphertext q (degree + 1) ringRank params.levels) :=
    $ᵗ RingGSWCiphertext q (degree + 1) ringRank params.levels
  let Original := fun
      difference : RingGSWCiphertext q (degree + 1) ringRank params.levels =>
    conditionalOperatorExperiment params sourceErrorSampler candidate
      ringSecret difference
  let Replaced := fun
      difference : RingGSWCiphertext q (degree + 1) ringRank params.levels =>
    maskReplacedConditionalExperiment params sourceErrorSampler candidate
      ringSecret difference
  have hpoint : ∀ difference,
      tvDist (Original difference) (Replaced difference) ≤
        Pr[DiagonalRowRankFailure params candidate |
          (pure difference : ProbComp
            (RingGSWCiphertext q (degree + 1) ringRank params.levels))].toReal := by
    intro difference
    rw [probEvent_pure]
    by_cases hrow : Function.Bijective
        (rowOperator candidate (differenceEntryDigits params difference) :
          DiagonalErrorVector q degree ringRank params.levels →
            DiagonalErrorVector q degree ringRank params.levels)
    · have heq :=
        conditionalOperator_maskReplaced_evalDist_of_rowOperator_bijective
          params sourceErrorSampler candidate ringSecret difference hrow
      have hnotFailure : ¬ DiagonalRowRankFailure params candidate difference :=
        fun hfailure => hfailure hrow
      unfold tvDist
      rw [heq, SPMF.tvDist_self]
      simp only [hnotFailure, if_false, ENNReal.toReal_zero]
      exact le_rfl
    · have hfailure : DiagonalRowRankFailure params candidate difference := hrow
      simpa only [hfailure, if_true, ENNReal.toReal_one] using
        (tvDist_le_one (Original difference) (Replaced difference))
  have hMixture :=
    FormalProof4FHE.FiniteProduct.tvDist_bind_left_le_probEvent_cont
      Difference Original Replaced
      (fun difference =>
        (pure difference : ProbComp
          (RingGSWCiphertext q (degree + 1) ringRank params.levels)))
      (DiagonalRowRankFailure params candidate) hpoint
  unfold tvDist at hMixture ⊢
  rw [operatorDiagonalExperiment_evalDist_eq_conditioned
    params sourceErrorSampler candidate ringSecret]
  rw [← bind_maskReplacedConditional_evalDist_eq_maskReplacedDiagonal
    params sourceErrorSampler candidate ringSecret]
  simpa [Difference, Original, Replaced, diagonalRowRankFailureProbability,
    monad_norm] using hMixture

/-- Selected-diagonal budget using the exact probability of a non-bijective row operator for
the public-mask hop, followed by the full mixed transformed-error marginal distance. -/
noncomputable def rankSharpDiagonalOperatorLoss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) : ℝ :=
  diagonalRowRankFailureProbability (degree := degree) (ringRank := ringRank)
      params candidate +
    mixedDiagonalErrorDistance (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler candidate

/-- Coordinate-independent rank-failure budget covering both encrypted scalar bits. -/
noncomputable def worstCaseRankSharpDiagonalOperatorLoss [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))) : ℝ :=
  max
    (rankSharpDiagonalOperatorLoss (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler false)
    (rankSharpDiagonalOperatorLoss (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler true)

theorem diagonalRowRankFailureProbability_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool) :
    0 ≤ diagonalRowRankFailureProbability (degree := degree) (ringRank := ringRank)
      params candidate :=
  ENNReal.toReal_nonneg

theorem rankSharpDiagonalOperatorLoss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) :
    0 ≤ rankSharpDiagonalOperatorLoss (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler candidate :=
  add_nonneg
    (diagonalRowRankFailureProbability_nonneg (ringRank := ringRank) params candidate)
    (mixedDiagonalErrorDistance_nonneg (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler candidate)

theorem worstCaseRankSharpDiagonalOperatorLoss_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))) :
    0 ≤ worstCaseRankSharpDiagonalOperatorLoss (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler := by
  exact (rankSharpDiagonalOperatorLoss_nonneg (ringRank := ringRank) params
    sourceErrorSampler targetErrorSampler false).trans (le_max_left _ _)

/-- **Rank-failure selected-diagonal reduction.**  A bijective fixed-difference row operator
transports the uniform public challenge exactly; the remaining mask cost is precisely localized
to the bad-rank event, while all error smoothing stays in one mixed marginal. -/
theorem tvDist_operatorDiagonalExperiment_target_le_rankSharp [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    tvDist
        (operatorDiagonalExperiment params sourceErrorSampler candidate ringSecret)
        (TGSW.encrypt ringRank params.levels targetErrorSampler
          (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) candidate)) ≤
      rankSharpDiagonalOperatorLoss (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler candidate := by
  let Middle := maskReplacedDiagonalExperiment (ringRank := ringRank) params
    sourceErrorSampler candidate ringSecret
  let Target := TGSW.encrypt ringRank params.levels targetErrorSampler
    (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
    (embedConstantBit q (degree + 1) candidate)
  calc
    _ ≤ tvDist
          (operatorDiagonalExperiment params sourceErrorSampler candidate ringSecret)
          Middle + tvDist Middle Target :=
      tvDist_triangle _ _ _
    _ ≤ diagonalRowRankFailureProbability (degree := degree)
          (ringRank := ringRank) params candidate +
        mixedDiagonalErrorDistance (ringRank := ringRank) params
          sourceErrorSampler targetErrorSampler candidate :=
      add_le_add
        (tvDist_operatorDiagonal_maskReplaced_le_rankFailure
          params sourceErrorSampler candidate ringSecret)
        (tvDist_maskReplacedDiagonal_target_le_mixedError
          params sourceErrorSampler targetErrorSampler candidate ringSecret)
    _ = _ := rfl

/-- Rank-failure reduction for the actual self-correlated diagonal against a fresh direct target
entry. -/
theorem tvDist_diagonalExperiment_directEntry_le_rankSharpOperatorLoss [NeZero q]
    {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    tvDist
        (OffDiagonalNormalForm.diagonalExperiment params sourceErrorSampler
          hidden ringSecret coordinate)
        (OffDiagonalNormalForm.directEntrySampler params targetErrorSampler
          hidden ringSecret coordinate) ≤
      rankSharpDiagonalOperatorLoss (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler (hidden coordinate) := by
  have h := tvDist_operatorDiagonalExperiment_target_le_rankSharp
    params sourceErrorSampler targetErrorSampler (hidden coordinate) ringSecret
  unfold tvDist at h ⊢
  rw [diagonalExperiment_evalDist_eq_operator
    params sourceErrorSampler hidden ringSecret coordinate]
  unfold OffDiagonalNormalForm.directEntrySampler
  rw [← TGSW.encrypt_evalDist_eq_directEncrypt ringRank params.levels
    targetErrorSampler (embedRingSecret q ringSecret)
    (Gadget.Base.ringGadget params)
    (embedConstantBit q (degree + 1) (hidden coordinate))]
  exact h

/-- Uniform rank-failure selected-diagonal bound for the whole-key certificate. -/
theorem tvDist_diagonalExperiment_directEntry_le_worstCaseRankSharpOperatorLoss [NeZero q]
    {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    tvDist
        (OffDiagonalNormalForm.diagonalExperiment params sourceErrorSampler
          hidden ringSecret coordinate)
        (OffDiagonalNormalForm.directEntrySampler params targetErrorSampler
          hidden ringSecret coordinate) ≤
      worstCaseRankSharpDiagonalOperatorLoss (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler := by
  have h := tvDist_diagonalExperiment_directEntry_le_rankSharpOperatorLoss
    params sourceErrorSampler targetErrorSampler hidden ringSecret coordinate
  cases hbit : hidden coordinate
  · exact h.trans (by
      simpa only [hbit, worstCaseRankSharpDiagonalOperatorLoss] using
        (le_max_left
          (rankSharpDiagonalOperatorLoss (ringRank := ringRank) params
            sourceErrorSampler targetErrorSampler false)
          (rankSharpDiagonalOperatorLoss (ringRank := ringRank) params
            sourceErrorSampler targetErrorSampler true)))
  · exact h.trans (by
      simpa only [hbit, worstCaseRankSharpDiagonalOperatorLoss] using
        (le_max_right
          (rankSharpDiagonalOperatorLoss (ringRank := ringRank) params
            sourceErrorSampler targetErrorSampler false)
          (rankSharpDiagonalOperatorLoss (ringRank := ringRank) params
            sourceErrorSampler targetErrorSampler true)))

end

end FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm
