/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SharedRandomnessTargetMessageAdaptiveRelativeGuessCheck

set_option autoImplicit false

/-!
# Whole-Key One-Shot Recovery for Direct Adaptive TFHE CircLWE

The one-coordinate candidate tester is run once for every coefficient of
`KeyExtract(S_source || S_suffix)` on the same supplied public view.  A finite union bound converts
the marginal coordinate errors into exact recovery of both nested ring-key blocks.  No
independence between coordinate-success events is assumed.

The resulting cross-distribution search-to-decision certificate has an explicit loss equal to
the sum of the one-shot coordinate errors.  This loss is generally too large for production
parameters without amplification; sound shared-context amplification requires an additional
conditional-fiber law and is intentionally not inferred here.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.AdaptiveCircularLWE

noncomputable section

open FormalProof4FHE.LWE.AuxiliaryInput.SearchToDecision

/-! ## Exact inverse of the extracted nested target key -/

/-- Reassemble an extracted target scalar key and split its source-prefix and suffix ring blocks. -/
def nestedSecretOfTargetMessages
    {suffixRank degree : ℕ}
    (messages : BinarySecret (targetScalarDimension 1 suffixRank degree)) :
    Secret 1 suffixRank degree :=
  let target : RingBinarySecret (1 + suffixRank) degree := keyUnextract messages
  (fun component coefficient ↦ target (Fin.castAdd suffixRank component) coefficient,
    fun component coefficient ↦ target (Fin.natAdd 1 component) coefficient)

/-- Splitting and re-appending a reassembled target ring key is the identity. -/
theorem targetRingSecret_nestedSecretOfTargetMessages
    {suffixRank degree : ℕ}
    (messages : BinarySecret (targetScalarDimension 1 suffixRank degree)) :
    targetRingSecret (nestedSecretOfTargetMessages messages).1
        (nestedSecretOfTargetMessages messages).2 =
      (keyUnextract messages : RingBinarySecret (1 + suffixRank) degree) := by
  funext component coefficient
  refine Fin.addCases ?_ ?_ component
  · intro sourceComponent
    simp [targetRingSecret, nestedSecretOfTargetMessages,
      FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.appendRingSecret]
  · intro suffixComponent
    simp [targetRingSecret, nestedSecretOfTargetMessages,
      FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.appendRingSecret]

/-- Re-extracting a reconstructed nested key recovers the supplied scalar vector. -/
@[simp]
theorem targetMessages_nestedSecretOfTargetMessages
    {suffixRank degree : ℕ}
    (messages : BinarySecret (targetScalarDimension 1 suffixRank degree)) :
    targetMessages (nestedSecretOfTargetMessages messages).1
        (nestedSecretOfTargetMessages messages).2 = messages := by
  unfold targetMessages
  rw [targetRingSecret_nestedSecretOfTargetMessages]
  exact keyExtract_keyUnextract messages

/-- Reconstructing the messages of an existing nested key recovers that key. -/
@[simp]
theorem nestedSecretOfTargetMessages_targetMessages
    {suffixRank degree : ℕ}
    (secret : Secret 1 suffixRank degree) :
    nestedSecretOfTargetMessages (targetMessages secret.1 secret.2) = secret := by
  apply Prod.ext
  · funext component coefficient
    simp [nestedSecretOfTargetMessages, targetMessages, targetRingSecret,
      FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.appendRingSecret]
  · funext component coefficient
    simp [nestedSecretOfTargetMessages, targetMessages, targetRingSecret,
      FormalProof4FHE.TFHE.SharedRandomnessKeyExtension.Native.appendRingSecret]

/-- `targetMessages` is an equivalence between the nested rank-one key and its extracted vector. -/
def targetMessagesEquiv (suffixRank degree : ℕ) :
    Secret 1 suffixRank degree ≃
      BinarySecret (targetScalarDimension 1 suffixRank degree) where
  toFun := fun secret ↦ targetMessages secret.1 secret.2
  invFun := nestedSecretOfTargetMessages
  left_inv := nestedSecretOfTargetMessages_targetMessages
  right_inv := targetMessages_nestedSecretOfTargetMessages

@[simp]
theorem nestedSecretOfTargetMessages_eq_iff
    {suffixRank degree : ℕ}
    (messages : BinarySecret (targetScalarDimension 1 suffixRank degree))
    (secret : Secret 1 suffixRank degree) :
    nestedSecretOfTargetMessages messages = secret ↔
      messages = targetMessages secret.1 secret.2 := by
  constructor
  · intro h
    rw [← h, targetMessages_nestedSecretOfTargetMessages]
  · intro h
    rw [h, nestedSecretOfTargetMessages_targetMessages]

namespace RelativeEvaluationMaterialEvaluator

/-! ## Executable coordinate and whole-key solvers -/

/-- One coordinate tester as a function of one fixed public direct-CircLWE view. -/
def targetCoordinateTester
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (distinguisher : DirectDistinguisher q degree suffixRank levels queryCount)
    (coordinate : Fin (targetScalarDimension 1 suffixRank (degree + 1)))
    (view : View q (degree + 1) 1 suffixRank levels queryCount) : ProbComp Bool :=
  FormalProof4FHE.BinaryGuessCheck.tester
    (candidateOrientation wideBootstrapErrorSampler wideExtensionErrorSampler
      inputErrorSampler gadget distinguisher)
    (evaluator.candidateCheck coordinate distinguisher) view

/-- Run every one-shot coordinate tester on the same immutable supplied view. -/
def targetScalarSolver
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (distinguisher : DirectDistinguisher q degree suffixRank levels queryCount)
    (view : View q (degree + 1) 1 suffixRank levels queryCount) :
    ProbComp (BinarySecret (targetScalarDimension 1 suffixRank (degree + 1))) :=
  Fin.mOfFn (targetScalarDimension 1 suffixRank (degree + 1)) fun coordinate ↦
    evaluator.targetCoordinateTester inputErrorSampler distinguisher coordinate view

/-- Public exact-nested-key solver obtained by inverting coefficient extraction. -/
def targetNestedSolver
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (distinguisher : DirectDistinguisher q degree suffixRank levels queryCount) :
    Solver q (degree + 1) 1 suffixRank levels queryCount :=
  fun challenge auxiliary ↦
    nestedSecretOfTargetMessages <$>
      evaluator.targetScalarSolver inputErrorSampler distinguisher (challenge, auxiliary)

/-! ## Common-view joint experiment and coordinate marginals -/

/-- Hidden extracted target key paired with the vector assembled from all one-shot tests. -/
def targetScalarJointGame
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (distinguisher : DirectDistinguisher q degree suffixRank levels queryCount) :
    ProbComp
      (BinarySecret (targetScalarDimension 1 suffixRank (degree + 1)) ×
        BinarySecret (targetScalarDimension 1 suffixRank (degree + 1))) := do
  let secret ← sampleNestedSecret 1 suffixRank (degree + 1)
  let view ← sampleRealView q (degree + 1) 1 suffixRank levels queryCount
    narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler gadget secret
  let recovered ← evaluator.targetScalarSolver inputErrorSampler distinguisher view
  return (targetMessages secret.1 secret.2, recovered)

/-- Standalone correctness game for one coordinate tester in the same narrow source view. -/
def targetCoordinateGame
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (distinguisher : DirectDistinguisher q degree suffixRank levels queryCount)
    (coordinate : Fin (targetScalarDimension 1 suffixRank (degree + 1))) : ProbComp Bool := do
  let secret ← sampleNestedSecret 1 suffixRank (degree + 1)
  let view ← sampleRealView q (degree + 1) 1 suffixRank levels queryCount
    narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler gadget secret
  let recovered ←
    evaluator.targetCoordinateTester inputErrorSampler distinguisher coordinate view
  return decide (recovered = targetMessages secret.1 secret.2 coordinate)

/-- The direct `BinaryGuessCheck.game` presentation is the standalone coordinate game. -/
theorem targetCoordinateGame_eq_coordinateRecoveryGame
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (distinguisher : DirectDistinguisher q degree suffixRank levels queryCount)
    (coordinate : Fin (targetScalarDimension 1 suffixRank (degree + 1))) :
    evaluator.targetCoordinateGame inputErrorSampler distinguisher coordinate =
      evaluator.coordinateRecoveryGame inputErrorSampler distinguisher coordinate := by
  simp [targetCoordinateGame, coordinateRecoveryGame, targetCoordinateSource,
    targetCoordinateTester, FormalProof4FHE.BinaryGuessCheck.game, bind_assoc, monad_norm]

/-- Projecting the assembled common-view experiment to one coordinate gives its standalone
correctness game exactly. -/
theorem evalDist_map_targetScalarJointGame_coordinate_eq_targetCoordinateGame
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (distinguisher : DirectDistinguisher q degree suffixRank levels queryCount)
    (coordinate : Fin (targetScalarDimension 1 suffixRank (degree + 1))) :
    evalDist
        ((fun output ↦ decide (output.2 coordinate = output.1 coordinate)) <$>
          evaluator.targetScalarJointGame inputErrorSampler distinguisher) =
      evalDist (evaluator.targetCoordinateGame inputErrorSampler distinguisher coordinate) := by
  simp only [targetScalarJointGame, targetCoordinateGame, targetScalarSolver,
    map_eq_bind_pure_comp, bind_assoc]
  apply evalDist_bind_congr'
  intro secret
  apply evalDist_bind_congr'
  intro view
  simp only [pure_bind, Function.comp_apply]
  have h := FormalProof4FHE.FiniteProduct.evalDist_map_fin_mOfFn_apply
    (targetScalarDimension 1 suffixRank (degree + 1))
    (fun index ↦ evaluator.targetCoordinateTester inputErrorSampler
      distinguisher index view)
    coordinate
    (fun recovered ↦ decide
      (recovered = targetMessages secret.1 secret.2 coordinate))
  rw [map_eq_bind_pure_comp, map_eq_bind_pure_comp] at h
  simpa only [Function.comp_def] using h

/-- The whole extracted-key equality game. -/
def targetScalarRecoveryGame
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (distinguisher : DirectDistinguisher q degree suffixRank levels queryCount) :
    ProbComp Bool :=
  (fun output ↦ decide (output.2 = output.1)) <$>
    evaluator.targetScalarJointGame inputErrorSampler distinguisher

/-- Exact nested-key search by the public solver is the extracted-vector equality game. -/
theorem searchGame_targetNestedSolver_eq_targetScalarRecoveryGame
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (distinguisher : DirectDistinguisher q degree suffixRank levels queryCount) :
    FormalProof4FHE.LWE.AuxiliaryInput.Search.game
        (searchProblem q (degree + 1) 1 suffixRank levels queryCount
          narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler gadget)
        (evaluator.targetNestedSolver inputErrorSampler distinguisher) =
      evaluator.targetScalarRecoveryGame inputErrorSampler distinguisher := by
  simp [FormalProof4FHE.LWE.AuxiliaryInput.Search.game, searchProblem,
    FormalProof4FHE.LWE.AuxiliaryInput.Search.exactRecoveryProblem, problem,
    targetNestedSolver, targetScalarRecoveryGame, targetScalarJointGame,
    sampleRealView, nestedSecretOfTargetMessages_eq_iff,
    map_eq_bind_pure_comp, bind_assoc, monad_norm]

/-! ## Finite union bound and explicit whole-key loss -/

/-- Failure probability of one assembled coordinate inside the common-view joint experiment. -/
noncomputable def targetCoordinateFailureProbability
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (distinguisher : DirectDistinguisher q degree suffixRank levels queryCount)
    (coordinate : Fin (targetScalarDimension 1 suffixRank (degree + 1))) : ENNReal :=
  Pr[(fun output ↦ output.2 coordinate ≠ output.1 coordinate) |
    evaluator.targetScalarJointGame inputErrorSampler distinguisher]

/-- The joint coordinate error is exactly failure in `coordinateRecoveryGame`. -/
theorem targetCoordinateFailureProbability_eq_coordinateRecoveryGame
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (distinguisher : DirectDistinguisher q degree suffixRank levels queryCount)
    (coordinate : Fin (targetScalarDimension 1 suffixRank (degree + 1))) :
    evaluator.targetCoordinateFailureProbability inputErrorSampler distinguisher coordinate =
      Pr[= false |
        evaluator.coordinateRecoveryGame inputErrorSampler distinguisher coordinate] := by
  unfold targetCoordinateFailureProbability
  calc
    _ = Pr[= false |
        (fun output ↦ decide (output.2 coordinate = output.1 coordinate)) <$>
          evaluator.targetScalarJointGame inputErrorSampler distinguisher] := by
      rw [probOutput_map]
      congr 1
      funext output
      simp
    _ = Pr[= false |
        evaluator.targetCoordinateGame inputErrorSampler distinguisher coordinate] :=
      probOutput_congr rfl
        (evaluator.evalDist_map_targetScalarJointGame_coordinate_eq_targetCoordinateGame
          inputErrorSampler distinguisher coordinate)
    _ = _ := by
      rw [targetCoordinateGame_eq_coordinateRecoveryGame]

/-- Whole extracted-key failure is contained in the union of coordinate failures. -/
theorem targetWholeKeyFailure_le_sum_coordinateFailure
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (distinguisher : DirectDistinguisher q degree suffixRank levels queryCount) :
    Pr[(fun output ↦ output.2 ≠ output.1) |
        evaluator.targetScalarJointGame inputErrorSampler distinguisher] ≤
      ∑ coordinate,
        evaluator.targetCoordinateFailureProbability inputErrorSampler distinguisher
          coordinate := by
  classical
  let experiment := evaluator.targetScalarJointGame inputErrorSampler distinguisher
  have hevent :
      (fun output :
          BinarySecret (targetScalarDimension 1 suffixRank (degree + 1)) ×
            BinarySecret (targetScalarDimension 1 suffixRank (degree + 1)) ↦
        output.2 ≠ output.1) =
      (fun output ↦ ∃ coordinate ∈
          (Finset.univ : Finset
            (Fin (targetScalarDimension 1 suffixRank (degree + 1)))),
        output.2 coordinate ≠ output.1 coordinate) := by
    funext output
    apply propext
    constructor
    · intro hne
      by_contra hnone
      have hall : ∀ coordinate, output.2 coordinate = output.1 coordinate := by
        intro coordinate
        by_contra hcoordinate
        exact hnone ⟨coordinate, Finset.mem_univ coordinate, hcoordinate⟩
      exact hne (funext hall)
    · rintro ⟨coordinate, _hcoordinate, hne⟩ heq
      exact hne (congrFun heq coordinate)
  rw [show evaluator.targetScalarJointGame inputErrorSampler distinguisher = experiment
      from rfl, hevent]
  simpa [targetCoordinateFailureProbability, experiment] using
    (probEvent_exists_finset_le_sum
      (Finset.univ : Finset
        (Fin (targetScalarDimension 1 suffixRank (degree + 1))))
      experiment (fun coordinate output ↦ output.2 coordinate ≠ output.1 coordinate))

/-- Per-coordinate error bounds assemble into exact nested-key search success. -/
theorem one_sub_sum_coordinateError_le_targetNestedSearchSuccess
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (distinguisher : DirectDistinguisher q degree suffixRank levels queryCount)
    (error : Fin (targetScalarDimension 1 suffixRank (degree + 1)) → ENNReal)
    (hcoordinate : ∀ coordinate,
      Pr[= false |
        evaluator.coordinateRecoveryGame inputErrorSampler distinguisher coordinate] ≤
          error coordinate) :
    1 - ∑ coordinate, error coordinate ≤
      FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability
        (searchProblem q (degree + 1) 1 suffixRank levels queryCount
          narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler gadget)
        (evaluator.targetNestedSolver inputErrorSampler distinguisher) := by
  classical
  let experiment := evaluator.targetScalarJointGame inputErrorSampler distinguisher
  have hfailure : Pr[(fun output ↦ output.2 ≠ output.1) | experiment] ≤
      ∑ coordinate, error coordinate := by
    exact (evaluator.targetWholeKeyFailure_le_sum_coordinateFailure
      inputErrorSampler distinguisher).trans
      (Finset.sum_le_sum fun coordinate _ ↦ by
        rw [targetCoordinateFailureProbability_eq_coordinateRecoveryGame]
        exact hcoordinate coordinate)
  have hsuccess : 1 - ∑ coordinate, error coordinate ≤
      Pr[(fun output ↦ output.2 = output.1) | experiment] :=
    probEvent_one_sub_le_of_compl_le probFailure_eq_zero hfailure
  unfold FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability
  rw [searchGame_targetNestedSolver_eq_targetScalarRecoveryGame]
  unfold targetScalarRecoveryGame
  rw [probOutput_map]
  simpa only [decide_eq_true_eq, experiment] using hsuccess

/-- One-shot error assigned to every extracted target-key coordinate. -/
noncomputable def targetCoordinateError
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (distinguisher : DirectDistinguisher q degree suffixRank levels queryCount) : ENNReal :=
  ENNReal.ofReal
    ((1 - (publicAdvantage
      (problem q (degree + 1) 1 suffixRank levels queryCount
        wideBootstrapErrorSampler wideExtensionErrorSampler inputErrorSampler gadget)
      distinguisher - 2 * evaluator.candidateErrorBudget)) / 2)

/-- The explicit summed one-shot loss of whole-key coordinate assembly. -/
noncomputable def targetFullRecoveryLoss
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (distinguisher : DirectDistinguisher q degree suffixRank levels queryCount) : ℝ :=
  (∑ _coordinate : Fin (targetScalarDimension 1 suffixRank (degree + 1)),
    evaluator.targetCoordinateError inputErrorSampler distinguisher).toReal

theorem targetFullRecoveryLoss_nonneg
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (distinguisher : DirectDistinguisher q degree suffixRank levels queryCount) :
    0 ≤ evaluator.targetFullRecoveryLoss inputErrorSampler distinguisher :=
  ENNReal.toReal_nonneg

/-- The concrete whole-key solver attains the finite union-bound lower bound. -/
theorem one_sub_sum_targetCoordinateError_le_targetNestedSearchSuccess
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (hInputError : Pr[⊥ | inputErrorSampler] = 0)
    (hextensionSymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        wideExtensionErrorSampler)
    (distinguisher : DirectDistinguisher q degree suffixRank levels queryCount) :
    1 - ∑ _coordinate : Fin (targetScalarDimension 1 suffixRank (degree + 1)),
        evaluator.targetCoordinateError inputErrorSampler distinguisher ≤
      FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability
        (searchProblem q (degree + 1) 1 suffixRank levels queryCount
          narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler gadget)
        (evaluator.targetNestedSolver inputErrorSampler distinguisher) := by
  apply evaluator.one_sub_sum_coordinateError_le_targetNestedSearchSuccess
  intro coordinate
  exact evaluator.coordinateRecoveryGame_failureProbability_publicAdvantage_le
    inputErrorSampler hInputError hextensionSymmetric distinguisher coordinate

/-! ## Checked cross-distribution reduction -/

/-- Public decision advantage is bounded by concrete narrow exact recovery plus the summed
one-shot coordinate loss. -/
theorem publicAdvantage_le_targetNestedSearchSuccess_add_fullRecoveryLoss
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (hInputError : Pr[⊥ | inputErrorSampler] = 0)
    (hextensionSymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        wideExtensionErrorSampler)
    (distinguisher : DirectDistinguisher q degree suffixRank levels queryCount) :
    publicAdvantage
        (problem q (degree + 1) 1 suffixRank levels queryCount
          wideBootstrapErrorSampler wideExtensionErrorSampler inputErrorSampler gadget)
        distinguisher ≤
      (FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability
        (searchProblem q (degree + 1) 1 suffixRank levels queryCount
          narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler gadget)
        (evaluator.targetNestedSolver inputErrorSampler distinguisher)).toReal +
      evaluator.targetFullRecoveryLoss inputErrorSampler distinguisher := by
  let errors : Fin (targetScalarDimension 1 suffixRank (degree + 1)) → ENNReal :=
    fun _ ↦ evaluator.targetCoordinateError inputErrorSampler distinguisher
  have herrors_ne_top : ∀ coordinate, errors coordinate ≠ ⊤ := by
    intro coordinate
    simp [errors, targetCoordinateError]
  have hsum_ne_top : (∑ coordinate, errors coordinate) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun coordinate _ ↦ herrors_ne_top coordinate
  have hadv := publicAdvantage_le_one
    (problem q (degree + 1) 1 suffixRank levels queryCount
      wideBootstrapErrorSampler wideExtensionErrorSampler inputErrorSampler gadget)
    distinguisher
  have hone : (1 : ℝ) ≤
      (1 - ∑ coordinate, errors coordinate).toReal +
        (∑ coordinate, errors coordinate).toReal := by
    by_cases hsum : (∑ coordinate, errors coordinate) ≤ 1
    · rw [ENNReal.toReal_sub_of_le hsum ENNReal.one_ne_top, ENNReal.toReal_one]
      linarith
    · have honeSum : 1 ≤ ∑ coordinate, errors coordinate := le_of_not_ge hsum
      rw [tsub_eq_zero_of_le honeSum, ENNReal.toReal_zero, zero_add,
        ← ENNReal.toReal_one]
      exact ENNReal.toReal_mono hsum_ne_top honeSum
  have hsuccess := evaluator.one_sub_sum_targetCoordinateError_le_targetNestedSearchSuccess
    inputErrorSampler hInputError hextensionSymmetric distinguisher
  have hsuccessReal := ENNReal.toReal_mono probOutput_ne_top hsuccess
  change publicAdvantage
      (problem q (degree + 1) 1 suffixRank levels queryCount
        wideBootstrapErrorSampler wideExtensionErrorSampler inputErrorSampler gadget)
      distinguisher ≤
    (FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability
      (searchProblem q (degree + 1) 1 suffixRank levels queryCount
        narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler gadget)
      (evaluator.targetNestedSolver inputErrorSampler distinguisher)).toReal +
      (∑ coordinate, errors coordinate).toReal
  exact hadv.trans (hone.trans (add_le_add hsuccessReal le_rfl))

/-- Fully checked narrow-search/wide-decision certificate induced by the evaluator. -/
noncomputable def toTargetCrossReduction
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (hInputError : Pr[⊥ | inputErrorSampler] = 0)
    (hextensionSymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        wideExtensionErrorSampler) :
    CrossDecisionToSearchReduction q (degree + 1) 1 suffixRank levels queryCount
      wideBootstrapErrorSampler wideExtensionErrorSampler inputErrorSampler
      narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler gadget where
  toSolver := evaluator.targetNestedSolver inputErrorSampler
  loss := evaluator.targetFullRecoveryLoss inputErrorSampler
  loss_nonneg := evaluator.targetFullRecoveryLoss_nonneg inputErrorSampler
  advantage_le := evaluator.publicAdvantage_le_targetNestedSearchSuccess_add_fullRecoveryLoss
    inputErrorSampler hInputError hextensionSymmetric

/-- **Conditional end-to-end adaptive TFHE circular-security bound.**

The concrete public guess/check solver recovers both nested keys in the narrow search problem,
and the only reduction loss is the displayed finite sum of one-shot coordinate errors.  The
statement is conditional on `evaluator`, whose nonlinear relative ring-key-shift component is the
remaining research obligation. -/
theorem abs_signedAdvantage_realAdaptive_le_targetNestedSearch_add_fullRecoveryLoss
    {Message : Type}
    {q degree suffixRank levels queryCount : ℕ} [NeZero q]
    {narrowBootstrapErrorSampler narrowExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {wideBootstrapErrorSampler wideExtensionErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1))}
    {gadget : Fin levels → RLWE.Rq q (degree + 1)}
    (evaluator : RelativeEvaluationMaterialEvaluator q degree suffixRank levels
      narrowBootstrapErrorSampler narrowExtensionErrorSampler
      wideBootstrapErrorSampler wideExtensionErrorSampler gadget)
    (inputErrorSampler : ProbComp (ZMod q))
    (hInputError : Pr[⊥ | inputErrorSampler] = 0)
    (hextensionSymmetric :
      FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.NegationSymmetric
        wideExtensionErrorSampler)
    (decompose : TFHE.TLWE.Ciphertext (RLWE.Rq q (degree + 1)) 1 →
      Fin 2 → Fin levels → RLWE.Rq q (degree + 1))
    (encode : Message → ZMod q)
    (adversary : AdaptiveAdversary Message q (degree + 1) 1 suffixRank levels)
    (hbound : Encryption.Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (realAdaptiveGame q (degree + 1) 1 suffixRank levels queryCount
        wideBootstrapErrorSampler wideExtensionErrorSampler inputErrorSampler gadget
        decompose encode adversary)| ≤
      (FormalProof4FHE.LWE.AuxiliaryInput.Search.successProbability
        (searchProblem q (degree + 1) 1 suffixRank levels queryCount
          narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler gadget)
        (evaluator.targetNestedSolver (queryCount := queryCount) inputErrorSampler
          (adaptiveDistinguisher (queryCount := queryCount)
            decompose encode adversary))).toReal +
      evaluator.targetFullRecoveryLoss (queryCount := queryCount) inputErrorSampler
        (adaptiveDistinguisher (queryCount := queryCount)
          decompose encode adversary) := by
  simpa only [toTargetCrossReduction, targetNestedSolver, targetFullRecoveryLoss] using
    (abs_signedAdvantage_realAdaptive_le_narrowSearch_add_reductionLoss
      q (degree + 1) 1 suffixRank levels queryCount
      wideBootstrapErrorSampler wideExtensionErrorSampler inputErrorSampler
      narrowBootstrapErrorSampler narrowExtensionErrorSampler inputErrorSampler gadget
      decompose encode adversary hbound
      (evaluator.toTargetCrossReduction inputErrorSampler hInputError
        hextensionSymmetric))

end RelativeEvaluationMaterialEvaluator

end

end FormalProof4FHE.TFHE.Native.SharedRandomnessTargetMessages.AdaptiveCircularLWE
