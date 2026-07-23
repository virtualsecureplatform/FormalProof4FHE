/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.AffineCircular
import FormalProof4FHE.RLWE.CenteredBinomialMoment
import FormalProof4FHE.TFHE.RingSquareTopWeightSecurity
import FormalProof4FHE.TFHE.SharpRotationNoise

/-!
# Scalar Marginals of the Highest Two-Adic `RGSW_S(-S)` Row

For a fixed output coefficient, negacyclic multiplication is an ordinary scalar dot product.
The scalar mask is a signed permutation of the coefficients of the public ring mask, and hence
is uniform whenever the ring mask is uniform.  The highest two-adic square message is already a
fixed coefficient-linear function of the Boolean secret.  Consequently every one-coefficient
marginal of the native top `RGSW_S(-S)` row is an exact direct affine circular-LWE problem and
reduces losslessly to ordinary binary-secret scalar LWE with the selected error coefficient.

This does not prove joint native-ring security.  Extracting every output coefficient from one
ring mask produces a highly constrained matrix of scalar masks.  In particular, every diagonal
entry of that matrix is the constant coefficient of the same ring mask.  In degree at least two
and over a nontrivial coefficient ring, the common-mask map is therefore not surjective onto the
space of independent scalar-LWE challenge matrices.  The positive marginal theorem and this
explicit coupling obstruction isolate the remaining gap without changing the narrow error law.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.TGSW.RingSquare.TopWeightSampleExtraction

open FormalProof4FHE.TFHE
open FormalProof4FHE.TFHE.Native
open FormalProof4FHE.TFHE.Native.CoefficientStructuredLWE
open FormalProof4FHE.TFHE.Native.CoefficientAffineCircularRLWE
open FormalProof4FHE.TFHE.TGSW.RingSquare.TopWeightCoefficientAffine

noncomputable section

/-! ## The mask seen by an arbitrary output coefficient -/

/-- Scalar-LWE mask induced by selecting one output coefficient of a negacyclic product.  It is
the unique signed permutation of the public ring-mask coefficients appearing in that output. -/
def extractedMask {R : Type} [Neg R] {degree : ℕ}
    (output : Fin (degree + 1)) (challenge : Fin (degree + 1) → R) :
    Fin (degree + 1) → R :=
  fun input ↦
    if input.val ≤ output.val then
      challenge (SharpRotationNoise.sourceIndex input output)
    else
      -challenge (SharpRotationNoise.sourceIndex input output)

/-- Selecting an arbitrary coefficient of a negacyclic product is exactly a scalar dot product
against `extractedMask`. -/
theorem negacyclicProduct_apply_eq_dotProduct
    {q degree : ℕ}
    (secret challenge : CoefficientStructuredLWE.Coefficients q (degree + 1))
    (output : Fin (degree + 1)) :
    CoefficientStructuredLWE.negacyclicProduct secret challenge output =
      dotProduct secret (extractedMask output challenge) := by
  unfold CoefficientStructuredLWE.negacyclicProduct dotProduct
  rw [SharpRotationNoise.negacyclicConvCoeff_eq_sum_source]
  apply Finset.sum_congr rfl
  intro input _
  by_cases hinput : input.val ≤ output.val <;>
    simp [extractedMask, hinput]

/-- The source coordinate lies before the selected output exactly when the input coordinate
does. -/
theorem sourceIndex_le_output_iff {degree : ℕ}
    (input output : Fin (degree + 1)) :
    (SharpRotationNoise.sourceIndex input output).val ≤ output.val ↔
      input.val ≤ output.val := by
  by_cases hinput : input.val ≤ output.val
  · rw [SharpRotationNoise.sourceIndex_val_of_le input output hinput]
    omega
  · rw [SharpRotationNoise.sourceIndex_val_of_not_le input output hinput]
    omega

/-- The source-coordinate permutation for one output coefficient is an involution. -/
theorem sourceIndex_sourceIndex {degree : ℕ}
    (input output : Fin (degree + 1)) :
    SharpRotationNoise.sourceIndex
        (SharpRotationNoise.sourceIndex input output) output = input := by
  apply Fin.ext
  by_cases hinput : input.val ≤ output.val
  · have hsource :
        (SharpRotationNoise.sourceIndex input output).val ≤ output.val :=
      (sourceIndex_le_output_iff input output).2 hinput
    rw [SharpRotationNoise.sourceIndex_val_of_le _ output hsource,
      SharpRotationNoise.sourceIndex_val_of_le input output hinput]
    omega
  · have hsource :
        ¬(SharpRotationNoise.sourceIndex input output).val ≤ output.val :=
      (not_congr (sourceIndex_le_output_iff input output)).2 hinput
    rw [SharpRotationNoise.sourceIndex_val_of_not_le _ output hsource,
      SharpRotationNoise.sourceIndex_val_of_not_le input output hinput]
    omega

/-- For every selected output, the signed extraction permutation is its own inverse. -/
theorem extractedMask_involutive {R : Type} [AddGroup R] {degree : ℕ}
    (output : Fin (degree + 1)) (challenge : Fin (degree + 1) → R) :
    extractedMask output (extractedMask output challenge) = challenge := by
  funext input
  by_cases hinput : input.val ≤ output.val
  · have hsource :
        (SharpRotationNoise.sourceIndex input output).val ≤ output.val :=
      (sourceIndex_le_output_iff input output).2 hinput
    simp [extractedMask, hinput, hsource, sourceIndex_sourceIndex]
  · have hsource :
        ¬(SharpRotationNoise.sourceIndex input output).val ≤ output.val :=
      (not_congr (sourceIndex_le_output_iff input output)).2 hinput
    simp [extractedMask, hinput, hsource, sourceIndex_sourceIndex]

/-- Selecting one output coefficient sends a uniform ring mask to a uniform scalar-LWE mask by
an explicit equivalence. -/
def extractedMaskEquiv {R : Type} [AddGroup R] {degree : ℕ}
    (output : Fin (degree + 1)) :
    (Fin (degree + 1) → R) ≃ (Fin (degree + 1) → R) where
  toFun := extractedMask output
  invFun := extractedMask output
  left_inv := extractedMask_involutive output
  right_inv := extractedMask_involutive output

/-- Apply the selected-coefficient mask equivalence to every rank-one public row. -/
def extractedChallengeEquiv (q degree sampleCount : ℕ)
    (output : Fin (degree + 1)) :
    CoefficientStructuredLWE.Challenge q (degree + 1) 1 sampleCount ≃
      Matrix (Fin (degree + 1)) (Fin sampleCount) (ZMod q) where
  toFun := fun challenge input sample ↦
    extractedMask output (challenge 0 sample) input
  invFun := fun challenge _ sample ↦
    extractedMask output (fun input ↦ challenge input sample)
  left_inv := by
    intro challenge
    funext row sample input
    rw [Subsingleton.elim row 0]
    exact congrFun (extractedMask_involutive output (challenge 0 sample)) input
  right_inv := by
    intro challenge
    funext input sample
    exact congrFun
      (extractedMask_involutive output (fun coordinate ↦ challenge coordinate sample)) input

/-! ## The common-mask consistency obstruction -/

/-- Matrix containing the scalar masks obtained by extracting every output coefficient from one
common ring mask.  Columns are output coefficients and rows are scalar-secret coordinates. -/
def allExtractedMasks {R : Type} [Neg R] {degree : ℕ}
    (challenge : Fin (degree + 1) → R) :
    Matrix (Fin (degree + 1)) (Fin (degree + 1)) R :=
  fun input output ↦ extractedMask output challenge input

@[simp]
theorem sourceIndex_self {degree : ℕ} (coordinate : Fin (degree + 1)) :
    SharpRotationNoise.sourceIndex coordinate coordinate = 0 := by
  apply Fin.ext
  rw [SharpRotationNoise.sourceIndex_val_of_le coordinate coordinate (le_refl _)]
  simp

/-- Every diagonal entry of the all-coefficient scalar mask matrix is the same constant
coefficient of the common ring mask. -/
theorem allExtractedMasks_diagonal {R : Type} [AddGroup R] {degree : ℕ}
    (challenge : Fin (degree + 1) → R) (coordinate : Fin (degree + 1)) :
    allExtractedMasks challenge coordinate coordinate = challenge 0 := by
  simp [allExtractedMasks, extractedMask]

/-- A matrix whose first diagonal entry is one and whose other entries are zero. -/
def unequalDiagonalMatrix (R : Type) [Zero R] [One R] (extra : ℕ) :
    Matrix (Fin (extra + 2)) (Fin (extra + 2)) R :=
  fun input output ↦
    if input = CoefficientAffineCircularRLWE.firstCoordinate extra ∧
        output = CoefficientAffineCircularRLWE.firstCoordinate extra then 1 else 0

/-- In degree at least two, scalar masks independently sampled for all output coefficients cannot
be reconstructed from one common ring mask.  The image has a constant diagonal, whereas the full
matrix space does not. -/
theorem allExtractedMasks_not_surjective
    {R : Type} [Ring R] (extra : ℕ) (hone : (1 : R) ≠ 0) :
    ¬Function.Surjective
      (allExtractedMasks :
        (Fin (extra + 2) → R) → Matrix (Fin (extra + 2)) (Fin (extra + 2)) R) := by
  intro hsurjective
  obtain ⟨challenge, hchallenge⟩ :=
    hsurjective (unequalDiagonalMatrix R extra)
  let first := CoefficientAffineCircularRLWE.firstCoordinate extra
  let second := CoefficientAffineCircularRLWE.secondCoordinate extra
  have hdiagonal :
      allExtractedMasks challenge first first =
        allExtractedMasks challenge second second := by
    rw [allExtractedMasks_diagonal, allExtractedMasks_diagonal]
  have hwitness :
      unequalDiagonalMatrix R extra first first =
        unequalDiagonalMatrix R extra second second := by
    rw [← hchallenge]
    exact hdiagonal
  apply hone
  simpa [unequalDiagonalMatrix, first, second,
    CoefficientAffineCircularRLWE.firstCoordinate,
    CoefficientAffineCircularRLWE.secondCoordinate] using hwitness

/-! ## Exact top-row affine-LWE marginal -/

/-- Coefficient matrix of a family of coefficient-linear operators after selecting one output
coordinate. -/
noncomputable def operatorMarginalCoefficients
    {q degree sampleCount : ℕ}
    (operators : Fin sampleCount →
      CoefficientAffineCircularRLWE.CoefficientOperator q (degree + 1))
    (output : Fin (degree + 1)) :
    LWE.AffineCircular.Coefficients (ZMod q) (degree + 1) sampleCount :=
  fun input sample ↦ LinearMap.toMatrix' (operators sample) output input

/-- Evaluating the scalar affine coefficient matrix is exactly evaluation of the original
coefficient-linear operator at the selected output. -/
theorem vecMul_operatorMarginalCoefficients
    {q degree sampleCount : ℕ}
    (operators : Fin sampleCount →
      CoefficientAffineCircularRLWE.CoefficientOperator q (degree + 1))
    (output : Fin (degree + 1))
    (value : Fin (degree + 1) → ZMod q)
    (sample : Fin sampleCount) :
    vecMul value (operatorMarginalCoefficients operators output) sample =
      operators sample value output := by
  calc
    vecMul value (operatorMarginalCoefficients operators output) sample =
        ∑ input, LinearMap.toMatrix' (operators sample) output input * value input := by
      unfold vecMul dotProduct operatorMarginalCoefficients
      apply Finset.sum_congr rfl
      intro input _
      exact mul_comm _ _
    _ = (LinearMap.toMatrix' (operators sample) *ᵥ value) output := rfl
    _ = operators sample value output := by simp

/-- Public affine coefficients of the selected top-row output coefficient. -/
noncomputable def topMarginalCoefficients
    (exponent degree : ℕ) (output : Fin (degree + 1)) :
    LWE.AffineCircular.Coefficients
      (ZMod (2 ^ (exponent + 1))) (degree + 1) (TGSW.rowCount 1 1) :=
  operatorMarginalCoefficients (topRGSWOperators exponent degree) output

/-- The selected coefficient of the original ring-error law; no widening or convolution is
introduced. -/
def topMarginalErrorSampler
    (exponent degree : ℕ) (output : Fin (degree + 1))
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))) :
    ProbComp (ZMod (2 ^ (exponent + 1))) :=
  (fun error ↦ CoefficientStructuredLWE.coefficientEquiv
      (2 ^ (exponent + 1)) (degree + 1) error output) <$> errorSampler

/-- Direct scalar affine circular-LWE problem represented by one arbitrary output coefficient of
the native top `RGSW_S(-S)` row. -/
noncomputable def topMarginalProblem
    (exponent degree : ℕ) (output : Fin (degree + 1))
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))) :
    LearningWithErrors.Problem
      (Matrix (Fin (degree + 1)) (Fin (TGSW.rowCount 1 1))
        (ZMod (2 ^ (exponent + 1))))
      (RingBinarySecret 1 (degree + 1))
      (Fin (TGSW.rowCount 1 1) → ZMod (2 ^ (exponent + 1))) := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  exact LWE.AffineCircular.problem
    (degree + 1) (TGSW.rowCount 1 1)
    (sampleRingSecret 1 (degree + 1))
    (fun ringSecret ↦ CoefficientStructuredLWE.binaryCoefficients
      (2 ^ (exponent + 1)) (ringSecret 0))
    (topMarginalCoefficients exponent degree output) 0
    (topMarginalErrorSampler exponent degree output errorSampler)

/-- Public projection from the complete coefficient transcript to one selected body coefficient.
The complete public ring masks are retained through their signed scalar-mask equivalence. -/
def projectCoefficientTranscript
    (q degree sampleCount : ℕ) (output : Fin (degree + 1))
    (transcript : CoefficientStructuredLWE.Transcript
      q (degree + 1) 1 sampleCount) :
    LWE.BatchTranscript (ZMod q) (degree + 1) sampleCount :=
  (extractedChallengeEquiv q degree sampleCount output transcript.1,
    fun sample ↦ transcript.2 sample output)

/-- The transformed public challenges in the coefficient problem are exactly uniform scalar-LWE
challenge matrices. -/
theorem topMarginal_sampleChallenge_evalDist
    (exponent degree : ℕ) (output : Fin (degree + 1))
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))) :
    evalDist
        (extractedChallengeEquiv (2 ^ (exponent + 1)) degree
            (TGSW.rowCount 1 1) output <$>
          (topRGSWCoefficientProblem exponent degree errorSampler).sampleChallenge) =
      evalDist
        (topMarginalProblem exponent degree output errorSampler).sampleChallenge := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  let ordinary := CoefficientStructuredLWE.problem
    (2 ^ (exponent + 1)) (degree + 1) 1 (TGSW.rowCount 1 1) errorSampler
  have huniform := CoefficientStructuredLWE.problem_sampleChallenge_evalDist_eq_uniform
    (2 ^ (exponent + 1)) (degree + 1) 1 (TGSW.rowCount 1 1) errorSampler
  have hmapped := evalDist_map_eq_of_evalDist_eq huniform
    (extractedChallengeEquiv (2 ^ (exponent + 1)) degree
      (TGSW.rowCount 1 1) output)
  calc
    _ = evalDist
        (extractedChallengeEquiv (2 ^ (exponent + 1)) degree
            (TGSW.rowCount 1 1) output <$>
          ordinary.sampleChallenge) := by
      rfl
    _ = evalDist
        (extractedChallengeEquiv (2 ^ (exponent + 1)) degree
            (TGSW.rowCount 1 1) output <$>
          ($ᵗ CoefficientStructuredLWE.Challenge
            (2 ^ (exponent + 1)) (degree + 1) 1 (TGSW.rowCount 1 1))) := hmapped
    _ = evalDist
        ($ᵗ Matrix (Fin (degree + 1)) (Fin (TGSW.rowCount 1 1))
          (ZMod (2 ^ (exponent + 1)))) :=
      evalDist_map_bijective_uniform_cross
        (α := CoefficientStructuredLWE.Challenge
          (2 ^ (exponent + 1)) (degree + 1) 1 (TGSW.rowCount 1 1))
        (β := Matrix (Fin (degree + 1)) (Fin (TGSW.rowCount 1 1))
          (ZMod (2 ^ (exponent + 1))))
        (extractedChallengeEquiv (2 ^ (exponent + 1)) degree
          (TGSW.rowCount 1 1) output)
        (extractedChallengeEquiv (2 ^ (exponent + 1)) degree
          (TGSW.rowCount 1 1) output).bijective
    _ = _ := by rfl

/-- Selecting the same coefficient from every IID ring-error row gives IID samples from the
selected coefficient law exactly. -/
theorem topMarginal_sampleError_evalDist
    (exponent degree : ℕ) (output : Fin (degree + 1))
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))) :
    evalDist
        ((fun errors sample ↦ errors sample output) <$>
          (topRGSWCoefficientProblem exponent degree errorSampler).sampleError) =
      evalDist
        (topMarginalProblem exponent degree output errorSampler).sampleError := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  let transform := fun error : RLWE.Rq (2 ^ (exponent + 1)) (degree + 1) ↦
    CoefficientStructuredLWE.coefficientEquiv
      (2 ^ (exponent + 1)) (degree + 1) error output
  have hmap := FormalProof4FHE.FiniteProduct.map_fin_mOfFn_const
    (TGSW.rowCount 1 1) errorSampler transform
  unfold topRGSWCoefficientProblem topMarginalProblem
  dsimp only
  unfold CoefficientStructuredLWE.problem LWE.AffineCircular.problem
  dsimp only
  unfold topMarginalErrorSampler
  simp only [Functor.map_map,
    CoefficientStructuredLWE.outputEquiv]
  change evalDist
      ((fun errors sample ↦ transform (errors sample)) <$>
        ProbComp.sampleIID (TGSW.rowCount 1 1) errorSampler) =
    evalDist (ProbComp.sampleIID (TGSW.rowCount 1 1)
      (transform <$> errorSampler))
  simpa only [ProbComp.sampleIID] using congrArg evalDist hmap

/-- Projecting a uniform coefficient-vector output onto one coefficient gives the canonical
uniform scalar output vector. -/
theorem selectCoefficient_uniform_evalDist
    (q degree sampleCount : ℕ) [NeZero q] (output : Fin (degree + 1)) :
    evalDist
        ((fun values sample ↦ values sample output) <$>
          ($ᵗ CoefficientStructuredLWE.Output q (degree + 1) sampleCount)) =
      evalDist ($ᵗ (Fin sampleCount → ZMod q)) := by
  let Vector := CoefficientStructuredLWE.Coefficients q (degree + 1)
  let select := fun value : Vector ↦ value output
  have hfull :=
    (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
      (alpha := Vector) sampleCount).symm
  have hmapped := evalDist_map_eq_of_evalDist_eq hfull
    (fun values sample ↦ select (values sample))
  have hcommute := FormalProof4FHE.FiniteProduct.map_fin_mOfFn_const
    sampleCount ($ᵗ Vector) select
  have hcoordinate :
      evalDist (select <$> ($ᵗ Vector)) = evalDist ($ᵗ (ZMod q)) := by
    exact FormalProof4FHE.FiniteProduct.evalDist_map_apply_uniformSample_fun output
  have hproduct :
      evalDist (ProbComp.sampleIID sampleCount (select <$> ($ᵗ Vector))) =
        evalDist (ProbComp.sampleIID sampleCount ($ᵗ (ZMod q))) := by
    apply FormalProof4FHE.FiniteProduct.evalDist_fin_mOfFn_congr
    intro _
    exact hcoordinate
  calc
    _ = evalDist
        ((fun values sample ↦ select (values sample)) <$>
          ProbComp.sampleIID sampleCount ($ᵗ Vector)) := hmapped
    _ = evalDist (ProbComp.sampleIID sampleCount (select <$> ($ᵗ Vector))) := by
      simpa only [ProbComp.sampleIID] using congrArg evalDist hcommute
    _ = evalDist (ProbComp.sampleIID sampleCount ($ᵗ (ZMod q))) := hproduct
    _ = _ := FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform sampleCount

/-- The ideal branch of the complete coefficient problem projects exactly to the ideal branch of
the scalar marginal problem. -/
theorem topMarginal_sampleUniform_evalDist
    (exponent degree : ℕ) (output : Fin (degree + 1))
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))) :
    evalDist
        ((fun values sample ↦ values sample output) <$>
          (topRGSWCoefficientProblem exponent degree errorSampler).sampleUniform) =
      evalDist
        (topMarginalProblem exponent degree output errorSampler).sampleUniform := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  let ordinary := CoefficientStructuredLWE.problem
    (2 ^ (exponent + 1)) (degree + 1) 1 (TGSW.rowCount 1 1) errorSampler
  have huniform := CoefficientStructuredLWE.problem_sampleUniform_evalDist_eq_uniform
    (2 ^ (exponent + 1)) (degree + 1) 1 (TGSW.rowCount 1 1) errorSampler
  have hmapped := evalDist_map_eq_of_evalDist_eq huniform
    (fun values sample ↦ values sample output)
  calc
    _ = evalDist
        ((fun values sample ↦ values sample output) <$> ordinary.sampleUniform) := by
      rfl
    _ = evalDist
        ((fun values sample ↦ values sample output) <$>
          ($ᵗ CoefficientStructuredLWE.Output (2 ^ (exponent + 1))
            (degree + 1) (TGSW.rowCount 1 1))) := hmapped
    _ = evalDist ($ᵗ (Fin (TGSW.rowCount 1 1) →
        ZMod (2 ^ (exponent + 1)))) :=
      selectCoefficient_uniform_evalDist
        (2 ^ (exponent + 1)) degree (TGSW.rowCount 1 1) output
    _ = _ := by rfl

/-- The selected native top-row noiseless coefficient is exactly the noiseless output of the
direct affine circular-LWE marginal after the signed mask equivalence. -/
theorem topMarginalProblem_noiseless_eq_nativeCoefficient
    (exponent degree : ℕ) (output : Fin (degree + 1))
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)))
    (ringSecret : RingBinarySecret 1 (degree + 1))
    (challenge : CoefficientStructuredLWE.Challenge
      (2 ^ (exponent + 1)) (degree + 1) 1 (TGSW.rowCount 1 1)) :
    (topMarginalProblem exponent degree output errorSampler).noiseless
        ringSecret
        (extractedChallengeEquiv (2 ^ (exponent + 1)) degree
          (TGSW.rowCount 1 1) output challenge) =
      fun sample ↦
        (topRGSWCoefficientProblem exponent degree errorSampler).noiseless
          ringSecret challenge sample output := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  funext sample
  unfold topMarginalProblem LWE.AffineCircular.problem
    LWE.AffineCircular.affineMessage
  change
    dotProduct
          (CoefficientStructuredLWE.binaryCoefficients
            (2 ^ (exponent + 1)) (ringSecret 0))
          (extractedMask output (challenge 0 sample)) +
        (vecMul
            (CoefficientStructuredLWE.binaryCoefficients
              (2 ^ (exponent + 1)) (ringSecret 0))
            (topMarginalCoefficients exponent degree output) sample + 0) = _
  rw [← negacyclicProduct_apply_eq_dotProduct]
  unfold topMarginalCoefficients
  rw [vecMul_operatorMarginalCoefficients]
  simp only [add_zero]
  rfl

/-- Projecting the complete real coefficient-affine top-row transcript onto any one output
coefficient gives exactly the corresponding direct affine scalar-LWE distribution. -/
theorem project_topRGSWCoefficientDistr_evalDist_eq_topMarginalDistr
    (exponent degree : ℕ) (output : Fin (degree + 1))
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))) :
    evalDist
        (LearningWithErrors.distr
            (topRGSWCoefficientProblem exponent degree errorSampler) >>=
          fun transcript ↦ pure
            (projectCoefficientTranscript
              (2 ^ (exponent + 1)) degree (TGSW.rowCount 1 1) output transcript)) =
      evalDist (LearningWithErrors.distr
        (topMarginalProblem exponent degree output errorSampler)) := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  let Top := topRGSWCoefficientProblem exponent degree errorSampler
  let Marginal := topMarginalProblem exponent degree output errorSampler
  let ChallengeMap := extractedChallengeEquiv
    (2 ^ (exponent + 1)) degree (TGSW.rowCount 1 1) output
  let ErrorMap := fun errors : CoefficientStructuredLWE.Output
      (2 ^ (exponent + 1)) (degree + 1) (TGSW.rowCount 1 1) ↦
    fun sample ↦ errors sample output
  let Challenges := ChallengeMap <$> Top.sampleChallenge
  let Errors := ErrorMap <$> Top.sampleError
  let Secrets := sampleRingSecret 1 (degree + 1)
  let finish := fun
      (challenge : Matrix (Fin (degree + 1)) (Fin (TGSW.rowCount 1 1))
        (ZMod (2 ^ (exponent + 1))))
      (ringSecret : RingBinarySecret 1 (degree + 1))
      (error : Fin (TGSW.rowCount 1 1) → ZMod (2 ^ (exponent + 1))) ↦
    (pure (challenge, Marginal.noiseless ringSecret challenge + error) :
      ProbComp (LWE.BatchTranscript (ZMod (2 ^ (exponent + 1)))
        (degree + 1) (TGSW.rowCount 1 1)))
  have hsource :
      (LearningWithErrors.distr Top >>= fun transcript ↦ pure
          (projectCoefficientTranscript
            (2 ^ (exponent + 1)) degree (TGSW.rowCount 1 1) output transcript)) =
        (Challenges >>= fun challenge ↦
          Secrets >>= fun ringSecret ↦ Errors >>= finish challenge ringSecret) := by
    unfold LearningWithErrors.distr
    simp only [Challenges, Errors, map_eq_bind_pure_comp, bind_assoc,
      pure_bind, Function.comp_apply]
    apply bind_congr
    intro challenge
    apply bind_congr
    intro ringSecret
    apply bind_congr
    intro error
    apply congrArg pure
    apply Prod.ext
    · rfl
    · funext sample
      change
        (Top.noiseless ringSecret challenge + error) sample output =
          Marginal.noiseless ringSecret (ChallengeMap challenge) sample +
            ErrorMap error sample
      rw [show Marginal.noiseless ringSecret (ChallengeMap challenge) =
          fun row ↦ Top.noiseless ringSecret challenge row output by
        exact topMarginalProblem_noiseless_eq_nativeCoefficient
          exponent degree output errorSampler ringSecret challenge]
      rfl
  have htarget :
      LearningWithErrors.distr Marginal =
        (Marginal.sampleChallenge >>= fun challenge ↦
          Secrets >>= fun ringSecret ↦ Marginal.sampleError >>= finish challenge ringSecret) := by
    have hsecret : Marginal.sampleSecret = Secrets := by rfl
    unfold LearningWithErrors.distr
    rw [hsecret]
  have hchallenge : evalDist Challenges = evalDist Marginal.sampleChallenge := by
    exact topMarginal_sampleChallenge_evalDist exponent degree output errorSampler
  have herror : evalDist Errors = evalDist Marginal.sampleError := by
    exact topMarginal_sampleError_evalDist exponent degree output errorSampler
  rw [hsource, htarget]
  calc
    evalDist (Challenges >>= fun challenge ↦
        Secrets >>= fun ringSecret ↦ Errors >>= finish challenge ringSecret) =
      evalDist (Marginal.sampleChallenge >>= fun challenge ↦
        Secrets >>= fun ringSecret ↦ Errors >>= finish challenge ringSecret) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        hchallenge (fun challenge ↦
          Secrets >>= fun ringSecret ↦ Errors >>= finish challenge ringSecret)
    _ = evalDist (Marginal.sampleChallenge >>= fun challenge ↦
        Secrets >>= fun ringSecret ↦
          Marginal.sampleError >>= finish challenge ringSecret) := by
      apply evalDist_bind_congr'
      intro challenge
      apply evalDist_bind_congr'
      intro ringSecret
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        herror (finish challenge ringSecret)

/-- Projecting the complete ideal coefficient transcript onto one output coefficient gives
exactly the ideal scalar-LWE marginal distribution. -/
theorem project_topRGSWCoefficientUniformDistr_evalDist_eq_topMarginalUniformDistr
    (exponent degree : ℕ) (output : Fin (degree + 1))
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))) :
    evalDist
        (LearningWithErrors.uniformDistr
            (topRGSWCoefficientProblem exponent degree errorSampler) >>=
          fun transcript ↦ pure
            (projectCoefficientTranscript
              (2 ^ (exponent + 1)) degree (TGSW.rowCount 1 1) output transcript)) =
      evalDist (LearningWithErrors.uniformDistr
        (topMarginalProblem exponent degree output errorSampler)) := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  let Top := topRGSWCoefficientProblem exponent degree errorSampler
  let Marginal := topMarginalProblem exponent degree output errorSampler
  let ChallengeMap := extractedChallengeEquiv
    (2 ^ (exponent + 1)) degree (TGSW.rowCount 1 1) output
  let OutputMap := fun values : CoefficientStructuredLWE.Output
      (2 ^ (exponent + 1)) (degree + 1) (TGSW.rowCount 1 1) ↦
    fun sample ↦ values sample output
  let Challenges := ChallengeMap <$> Top.sampleChallenge
  let Outputs := OutputMap <$> Top.sampleUniform
  have hsource :
      (LearningWithErrors.uniformDistr Top >>= fun transcript ↦ pure
          (projectCoefficientTranscript
            (2 ^ (exponent + 1)) degree (TGSW.rowCount 1 1) output transcript)) =
        (Challenges >>= fun challenge ↦ Outputs >>= fun values ↦ pure (challenge, values)) := by
    unfold LearningWithErrors.uniformDistr
    simp [Challenges, Outputs, ChallengeMap, OutputMap,
      projectCoefficientTranscript, map_eq_bind_pure_comp, bind_assoc]
  have htarget :
      LearningWithErrors.uniformDistr Marginal =
        (Marginal.sampleChallenge >>= fun challenge ↦
          Marginal.sampleUniform >>= fun values ↦ pure (challenge, values)) := by
    rfl
  have hchallenge : evalDist Challenges = evalDist Marginal.sampleChallenge := by
    exact topMarginal_sampleChallenge_evalDist exponent degree output errorSampler
  have houtput : evalDist Outputs = evalDist Marginal.sampleUniform := by
    exact topMarginal_sampleUniform_evalDist exponent degree output errorSampler
  rw [hsource, htarget]
  calc
    evalDist (Challenges >>= fun challenge ↦
        Outputs >>= fun values ↦ pure (challenge, values)) =
      evalDist (Marginal.sampleChallenge >>= fun challenge ↦
        Outputs >>= fun values ↦ pure (challenge, values)) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        hchallenge (fun challenge ↦ Outputs >>= fun values ↦ pure (challenge, values))
    _ = evalDist (Marginal.sampleChallenge >>= fun challenge ↦
        Marginal.sampleUniform >>= fun values ↦ pure (challenge, values)) := by
      apply evalDist_bind_congr'
      intro challenge
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        houtput (fun values ↦ pure (challenge, values))

/-- Lift a scalar marginal adversary to the complete coefficient transcript by retaining the
complete public masks and selecting one body coefficient from every top-row sample. -/
def liftMarginalAdversary
    {exponent degree : ℕ} {output : Fin (degree + 1)}
    {errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1))}
    (adversary : LearningWithErrors.Adversary
      (topMarginalProblem exponent degree output errorSampler)) :
    LearningWithErrors.Adversary
      (topRGSWCoefficientProblem exponent degree errorSampler) :=
  fun transcript ↦ adversary
    (projectCoefficientTranscript
      (2 ^ (exponent + 1)) degree (TGSW.rowCount 1 1) output transcript)

/-- Exact real-game identity for the lifted scalar-marginal adversary. -/
theorem liftMarginalAdversary_game0_evalDist_eq
    (exponent degree : ℕ) (output : Fin (degree + 1))
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)))
    (adversary : LearningWithErrors.Adversary
      (topMarginalProblem exponent degree output errorSampler)) :
    evalDist (LearningWithErrors.game0
        (topRGSWCoefficientProblem exponent degree errorSampler)
        (liftMarginalAdversary adversary)) =
      evalDist (LearningWithErrors.game0
        (topMarginalProblem exponent degree output errorSampler) adversary) := by
  rw [LearningWithErrors.game0, LearningWithErrors.game0]
  unfold liftMarginalAdversary
  rw [show
      (LearningWithErrors.distr
          (topRGSWCoefficientProblem exponent degree errorSampler) >>=
        fun transcript ↦ adversary
          (projectCoefficientTranscript
            (2 ^ (exponent + 1)) degree (TGSW.rowCount 1 1) output transcript)) =
      ((LearningWithErrors.distr
          (topRGSWCoefficientProblem exponent degree errorSampler) >>=
        fun transcript ↦ pure
          (projectCoefficientTranscript
            (2 ^ (exponent + 1)) degree (TGSW.rowCount 1 1) output transcript)) >>=
        adversary) by simp]
  rw [evalDist_bind,
    project_topRGSWCoefficientDistr_evalDist_eq_topMarginalDistr,
    ← evalDist_bind]

/-- Exact ideal-game identity for the lifted scalar-marginal adversary. -/
theorem liftMarginalAdversary_game1_evalDist_eq
    (exponent degree : ℕ) (output : Fin (degree + 1))
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)))
    (adversary : LearningWithErrors.Adversary
      (topMarginalProblem exponent degree output errorSampler)) :
    evalDist (LearningWithErrors.game1
        (topRGSWCoefficientProblem exponent degree errorSampler)
        (liftMarginalAdversary adversary)) =
      evalDist (LearningWithErrors.game1
        (topMarginalProblem exponent degree output errorSampler) adversary) := by
  rw [LearningWithErrors.game1, LearningWithErrors.game1]
  unfold liftMarginalAdversary
  rw [show
      (LearningWithErrors.uniformDistr
          (topRGSWCoefficientProblem exponent degree errorSampler) >>=
        fun transcript ↦ adversary
          (projectCoefficientTranscript
            (2 ^ (exponent + 1)) degree (TGSW.rowCount 1 1) output transcript)) =
      ((LearningWithErrors.uniformDistr
          (topRGSWCoefficientProblem exponent degree errorSampler) >>=
        fun transcript ↦ pure
          (projectCoefficientTranscript
            (2 ^ (exponent + 1)) degree (TGSW.rowCount 1 1) output transcript)) >>=
        adversary) by simp]
  rw [evalDist_bind,
    project_topRGSWCoefficientUniformDistr_evalDist_eq_topMarginalUniformDistr,
    ← evalDist_bind]

/-- Restricting the complete coefficient transcript to one body coefficient preserves the
scalar-marginal distinguishing advantage exactly. -/
theorem liftMarginalAdversary_advantage_eq
    (exponent degree : ℕ) (output : Fin (degree + 1))
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)))
    (adversary : LearningWithErrors.Adversary
      (topMarginalProblem exponent degree output errorSampler)) :
    LearningWithErrors.advantage
        (topRGSWCoefficientProblem exponent degree errorSampler)
        (liftMarginalAdversary adversary) =
      LearningWithErrors.advantage
        (topMarginalProblem exponent degree output errorSampler) adversary := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage,
    FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (liftMarginalAdversary_game0_evalDist_eq
        exponent degree output errorSampler adversary) true,
    evalDist_ext_iff.mp
      (liftMarginalAdversary_game1_evalDist_eq
        exponent degree output errorSampler adversary) true]

/-- Every adversary against one output coefficient of the highest two-adic native row has exactly
the advantage of an explicit ordinary binary-secret scalar-LWE adversary, with the selected
coefficient of the original narrow error and no security loss. -/
theorem topMarginalAdvantage_eq_lwe
    (exponent degree : ℕ) (output : Fin (degree + 1))
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)))
    (adversary : LearningWithErrors.Adversary
      (topMarginalProblem exponent degree output errorSampler)) :
    LearningWithErrors.advantage
        (topMarginalProblem exponent degree output errorSampler) adversary =
      LearningWithErrors.advantage
        (LWE.AffineCircular.ordinaryProblem
          (degree + 1) (TGSW.rowCount 1 1)
          (sampleRingSecret 1 (degree + 1))
          (fun ringSecret ↦ CoefficientStructuredLWE.binaryCoefficients
            (2 ^ (exponent + 1)) (ringSecret 0))
          (topMarginalErrorSampler exponent degree output errorSampler))
        (LWE.AffineCircular.reduction adversary) := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  exact LWE.AffineCircular.advantage_eq_lwe
    (degree + 1) (TGSW.rowCount 1 1)
    (sampleRingSecret 1 (degree + 1))
    (fun ringSecret ↦ CoefficientStructuredLWE.binaryCoefficients
      (2 ^ (exponent + 1)) (ringSecret 0))
    (topMarginalCoefficients exponent degree output) 0
    (topMarginalErrorSampler exponent degree output errorSampler) adversary

/-- Complete coefficient-game statement for a distinguisher that uses one selected body
coefficient: its advantage is exactly ordinary binary-secret scalar LWE. -/
theorem liftedTopMarginalAdvantage_eq_lwe
    (exponent degree : ℕ) (output : Fin (degree + 1))
    (errorSampler : ProbComp (RLWE.Rq (2 ^ (exponent + 1)) (degree + 1)))
    (adversary : LearningWithErrors.Adversary
      (topMarginalProblem exponent degree output errorSampler)) :
    LearningWithErrors.advantage
        (topRGSWCoefficientProblem exponent degree errorSampler)
        (liftMarginalAdversary adversary) =
      LearningWithErrors.advantage
        (LWE.AffineCircular.ordinaryProblem
          (degree + 1) (TGSW.rowCount 1 1)
          (sampleRingSecret 1 (degree + 1))
          (fun ringSecret ↦ CoefficientStructuredLWE.binaryCoefficients
            (2 ^ (exponent + 1)) (ringSecret 0))
          (topMarginalErrorSampler exponent degree output errorSampler))
        (LWE.AffineCircular.reduction adversary) := by
  rw [liftMarginalAdversary_advantage_eq,
    topMarginalAdvantage_eq_lwe]

/-- For centered-binomial ring error, the selected marginal error is exactly the one-coefficient
centered-binomial law with the same width `eta`. -/
theorem topMarginalErrorSampler_centeredBinomial_evalDist
    (exponent degree eta : ℕ) (output : Fin (degree + 1)) :
    evalDist
        (topMarginalErrorSampler exponent degree output
          (RLWE.CenteredBinomial.sampler
            (2 ^ (exponent + 1)) (degree + 1) eta)) =
      evalDist
        (RLWE.CenteredBinomial.coefficientSampler
          (2 ^ (exponent + 1)) eta) := by
  letI : NeZero (2 ^ (exponent + 1)) := ⟨pow_ne_zero _ (by omega)⟩
  simpa [topMarginalErrorSampler,
    CoefficientStructuredLWE.coefficientEquiv,
    LatticeCrypto.Poly.toPi, Vector.get] using
      (RLWE.CenteredBinomial.sampler_get_evalDist
        (2 ^ (exponent + 1)) (degree + 1) eta output)

end

end FormalProof4FHE.TFHE.TGSW.RingSquare.TopWeightSampleExtraction
