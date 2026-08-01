/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.OddSecretReduction
import FormalProof4FHE.TFHE.SourceAlignedDenseJointLaw

/-!
# Exact Ring-to-Scalar Transport for the Source-Aligned Suffix Problem

The source-aligned BRK suffix problem publishes the full scalar matrix induced by uniform ring
masks and the ordinary coefficient vector of every ring body.  This file proves that this is an
exact public representation of rank-one ring LWE:

* the induced scalar-gadget adjoint identity transports the noiseless bodies;
* ordinary coefficient flattening is a bijection on complete output vectors; and
* real and uniform games, hence distinguishing advantages, are preserved exactly.

Combined with `RLWE.OddSecretReduction`, this removes the separate suffix-PRG premise for a
parity-placed secret: the scalar suffix source reduces to ordinary half-degree RLWE.
-/

set_option autoImplicit false

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.SourceAlignedSuffixRLWEReduction

noncomputable section

open SourceAlignedFactorPropagation.Extraction
open SourceAlignedBRKKSKJointLaw.Algebra

/-- Ring masks before their full source-aligned scalar expansion. -/
abbrev RingChallenge (q degree samples : ℕ) :=
  Matrix (Fin 1) (Fin samples) (RLWE.Rq q (degree + 1))

/-- Complete scalarized source-aligned challenge. -/
abbrev ScalarChallenge (q degree samples : ℕ) :=
  Matrix (Fin (1 * (degree + 1))) (Fin (samples * (degree + 1))) (ZMod q)

/-- Complete ordinary-coefficient flattening is a carrier equivalence. -/
def bodyCoefficientEquiv (q degree rank : ℕ) :
    (Fin rank → RLWE.Rq q (degree + 1)) ≃
      (Fin (rank * (degree + 1)) → ZMod q) where
  toFun := bodyCoefficients
  invFun coefficients component :=
    (TFHE.Native.CoefficientStructuredLWE.coefficientEquiv q (degree + 1)).symm
      (fun coefficient ↦ coefficients (finProdFinEquiv (component, coefficient)))
  left_inv value := by
    funext component
    change
      (TFHE.Native.CoefficientStructuredLWE.coefficientEquiv q (degree + 1)).symm
          (fun coefficient ↦ bodyCoefficients value
            (finProdFinEquiv (component, coefficient))) =
        value component
    apply (TFHE.Native.CoefficientStructuredLWE.coefficientEquiv q
      (degree + 1)).injective
    rw [Equiv.apply_symm_apply]
    funext coefficient
    unfold bodyCoefficients SampleExtraction.extractedSecret
    simp only [Equiv.symm_apply_apply]
    unfold TFHE.Native.CoefficientStructuredLWE.coefficientEquiv
    rfl
  right_inv value := by
    funext coordinate
    obtain ⟨⟨component, coefficient⟩, rfl⟩ := finProdFinEquiv.surjective coordinate
    unfold bodyCoefficients SampleExtraction.extractedSecret
    simp only [Equiv.symm_apply_apply]
    change
      (TFHE.Native.CoefficientStructuredLWE.coefficientEquiv q (degree + 1))
          ((TFHE.Native.CoefficientStructuredLWE.coefficientEquiv q
            (degree + 1)).symm
              (fun coefficient ↦ value (finProdFinEquiv (component, coefficient))))
          coefficient =
        value (finProdFinEquiv (component, coefficient))
    have h := congrFun
      ((TFHE.Native.CoefficientStructuredLWE.coefficientEquiv q
        (degree + 1)).apply_symm_apply
          (fun coefficient ↦ value (finProdFinEquiv (component, coefficient))))
      coefficient
    exact h

@[simp]
theorem bodyCoefficientEquiv_apply (q degree rank : ℕ)
    (value : Fin rank → RLWE.Rq q (degree + 1)) :
    bodyCoefficientEquiv q degree rank value = bodyCoefficients value := by
  rfl

@[simp]
theorem bodyCoefficientEquiv_add (q degree rank : ℕ)
    (left right : Fin rank → RLWE.Rq q (degree + 1)) :
    bodyCoefficientEquiv q degree rank (left + right) =
      bodyCoefficientEquiv q degree rank left +
        bodyCoefficientEquiv q degree rank right := by
  rw [bodyCoefficientEquiv_apply, bodyCoefficientEquiv_apply,
    bodyCoefficientEquiv_apply]
  funext coordinate
  obtain ⟨⟨component, coefficient⟩, rfl⟩ := finProdFinEquiv.surjective coordinate
  unfold bodyCoefficients SampleExtraction.extractedSecret
  simp only [Equiv.symm_apply_apply, Pi.add_apply]
  change
    TFHE.Native.CoefficientStructuredLWE.coefficientEquiv q (degree + 1)
        (left component + right component) coefficient =
      (TFHE.Native.CoefficientStructuredLWE.coefficientEquiv q (degree + 1)
          (left component) +
        TFHE.Native.CoefficientStructuredLWE.coefficientEquiv q (degree + 1)
          (right component)) coefficient
  exact congrFun
    (TFHE.Native.CoefficientStructuredLWE.coefficientEquiv_add q (degree + 1)
      (left component) (right component)) coefficient

/-- Full scalarization of a rank-one ring-mask batch. -/
def scalarizeChallenge {q degree samples : ℕ}
    (challenge : RingChallenge q degree samples) : ScalarChallenge q degree samples :=
  inducedScalarGadget challenge

/-- Map a complete ring transcript to its source-aligned scalar presentation. -/
def transcriptMap (q degree samples : ℕ) :
    (RingChallenge q degree samples ×
      (Fin samples → RLWE.Rq q (degree + 1))) →
      (ScalarChallenge q degree samples ×
        (Fin (samples * (degree + 1)) → ZMod q)) :=
  fun transcript ↦
    (scalarizeChallenge transcript.1,
      bodyCoefficientEquiv q degree samples transcript.2)

/-- Rank-one ring LWE with an arbitrary secret type and embedding. -/
noncomputable def ringProblem {Secret : Type} (q degree samples : ℕ) [NeZero q]
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → RLWE.Rq q (degree + 1))
    (ringErrorSampler : ProbComp (RLWE.Rq q (degree + 1))) :=
  LWE.embeddedBatchProblem 1 samples secretSampler embed ringErrorSampler

/-- Its complete source-aligned scalar presentation.  The scalar error is the coefficient image
of the entire IID ring-error vector, so correlations within and across coefficients are retained
exactly. -/
noncomputable def scalarProblem {Secret : Type} (q degree samples : ℕ) [NeZero q]
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → RLWE.Rq q (degree + 1))
    (ringErrorSampler : ProbComp (RLWE.Rq q (degree + 1))) :=
  SourceAlignedDenseJointLaw.suffixProblem
    (scalarizeChallenge <$> ($ᵗ RingChallenge q degree samples))
    ((fun secret ↦ bodyCoefficientEquiv q degree 1 (embed secret)) <$>
      secretSampler)
    (bodyCoefficientEquiv q degree samples <$>
      ProbComp.sampleIID samples ringErrorSampler)

/-- The induced scalar gadget transports the complete rank-one noiseless output. -/
theorem bodyCoefficientEquiv_vecMul {Secret : Type}
    (q degree samples : ℕ) [NeZero q]
    (embed : Secret → Fin 1 → RLWE.Rq q (degree + 1))
    (secret : Secret) (challenge : RingChallenge q degree samples) :
    bodyCoefficientEquiv q degree samples (vecMul (embed secret) challenge) =
      (scalarizeChallenge challenge).transpose *ᵥ
        bodyCoefficientEquiv q degree 1 (embed secret) := by
  rw [bodyCoefficientEquiv_apply, bodyCoefficientEquiv_apply]
  have hvec : vecMul (embed secret) challenge =
      challenge.transpose *ᵥ embed secret := by
    simpa using (Matrix.vecMul_transpose challenge.transpose (embed secret))
  rw [hvec]
  exact (inducedScalarGadget_transpose_mulVec challenge (embed secret)).symm

/-- Deterministic real-transcript assembly commutes with scalarization. -/
theorem transcriptMap_real {Secret : Type}
    (q degree samples : ℕ) [NeZero q]
    (embed : Secret → Fin 1 → RLWE.Rq q (degree + 1))
    (challenge : RingChallenge q degree samples) (secret : Secret)
    (error : Fin samples → RLWE.Rq q (degree + 1)) :
    transcriptMap q degree samples
        (challenge, vecMul (embed secret) challenge + error) =
      (scalarizeChallenge challenge,
        (scalarizeChallenge challenge).transpose *ᵥ
            bodyCoefficientEquiv q degree 1 (embed secret) +
          bodyCoefficientEquiv q degree samples error) := by
  apply Prod.ext
  · rfl
  · change bodyCoefficientEquiv q degree samples
        (vecMul (embed secret) challenge + error) = _
    rw [bodyCoefficientEquiv_add, bodyCoefficientEquiv_vecMul]

@[simp]
theorem transcriptMap_real_add {Secret : Type}
    (q degree samples : ℕ) [NeZero q]
    (embed : Secret → Fin 1 → RLWE.Rq q (degree + 1))
    (challenge : RingChallenge q degree samples) (secret : Secret)
    (error : Fin samples → RLWE.Rq q (degree + 1)) :
    transcriptMap q degree samples
        (challenge, vecMul (embed secret) challenge + error) =
      (scalarizeChallenge challenge,
        (scalarizeChallenge challenge).transpose *ᵥ
            bodyCoefficientEquiv q degree 1 (embed secret) +
          bodyCoefficientEquiv q degree samples error) := by
  exact transcriptMap_real q degree samples embed challenge secret error

/-! ## Exact game transport -/

/-- Uniform complete ring bodies become uniform complete coefficient bodies under flattening. -/
theorem bodyCoefficientEquiv_uniform_evalDist (q degree rank : ℕ) [NeZero q] :
    evalDist (bodyCoefficientEquiv q degree rank <$>
        ($ᵗ (Fin rank → RLWE.Rq q (degree + 1)))) =
      evalDist ($ᵗ (Fin (rank * (degree + 1)) → ZMod q)) := by
  exact evalDist_map_bijective_uniform_cross
    (α := Fin rank → RLWE.Rq q (degree + 1))
    (β := Fin (rank * (degree + 1)) → ZMod q)
    (bodyCoefficientEquiv q degree rank)
    (bodyCoefficientEquiv q degree rank).bijective

/-- Mapping the rank-one ring real transcript gives exactly the complete source-aligned scalar
real transcript. -/
theorem real_evalDist {Secret : Type}
    (q degree samples : ℕ) [NeZero q]
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → RLWE.Rq q (degree + 1))
    (ringErrorSampler : ProbComp (RLWE.Rq q (degree + 1))) :
    evalDist (LearningWithErrors.distr
          (ringProblem q degree samples secretSampler embed ringErrorSampler) >>=
        fun transcript ↦ pure (transcriptMap q degree samples transcript)) =
      evalDist (LearningWithErrors.distr
        (scalarProblem q degree samples secretSampler embed ringErrorSampler)) := by
  simp [LearningWithErrors.distr, ringProblem, LWE.embeddedBatchProblem,
    scalarProblem, SourceAlignedDenseJointLaw.suffixProblem,
    bind_assoc, monad_norm]

/-- Mapping the rank-one ring uniform transcript gives exactly the complete source-aligned scalar
uniform transcript. -/
theorem uniform_evalDist {Secret : Type}
    (q degree samples : ℕ) [NeZero q]
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → RLWE.Rq q (degree + 1))
    (ringErrorSampler : ProbComp (RLWE.Rq q (degree + 1))) :
    evalDist (LearningWithErrors.uniformDistr
          (ringProblem q degree samples secretSampler embed ringErrorSampler) >>=
        fun transcript ↦ pure (transcriptMap q degree samples transcript)) =
    evalDist (LearningWithErrors.uniformDistr
        (scalarProblem q degree samples secretSampler embed ringErrorSampler)) := by
  letI : SampleableType
      (Fin (samples * (degree + 1)) → ZMod q) :=
    instSampleableTypePiFintype
  let challengeSampler : ProbComp (RingChallenge q degree samples) :=
    $ᵗ RingChallenge q degree samples
  let ringUniform : ProbComp (Fin samples → RLWE.Rq q (degree + 1)) :=
    $ᵗ (Fin samples → RLWE.Rq q (degree + 1))
  let scalarUniform : ProbComp
      (Fin (samples * (degree + 1)) → ZMod q) :=
    $ᵗ (Fin (samples * (degree + 1)) → ZMod q)
  let mappedUniform := bodyCoefficientEquiv q degree samples <$> ringUniform
  let finish : RingChallenge q degree samples →
      (Fin (samples * (degree + 1)) → ZMod q) →
      ProbComp (ScalarChallenge q degree samples ×
        (Fin (samples * (degree + 1)) → ZMod q)) :=
    fun challenge output ↦
        pure (scalarizeChallenge challenge, output)
  have hUniform : evalDist mappedUniform = evalDist scalarUniform := by
    exact evalDist_map_bijective_uniform_cross
      (α := Fin samples → RLWE.Rq q (degree + 1))
      (β := Fin (samples * (degree + 1)) → ZMod q)
      (bodyCoefficientEquiv q degree samples)
      (bodyCoefficientEquiv q degree samples).bijective
  have left_eq :
      (LearningWithErrors.uniformDistr
          (ringProblem q degree samples secretSampler embed ringErrorSampler) >>=
        fun transcript ↦ pure (transcriptMap q degree samples transcript)) =
      (challengeSampler >>= fun challenge ↦
        mappedUniform >>= finish challenge) := by
    simp [LearningWithErrors.uniformDistr, ringProblem, LWE.embeddedBatchProblem,
      challengeSampler, mappedUniform, ringUniform, finish, transcriptMap,
      monad_norm]
  have right_eq :
      LearningWithErrors.uniformDistr
          (scalarProblem q degree samples secretSampler embed ringErrorSampler) =
      (challengeSampler >>= fun challenge ↦
        scalarUniform >>= finish challenge) := by
    simp [LearningWithErrors.uniformDistr, scalarProblem,
      SourceAlignedDenseJointLaw.suffixProblem, challengeSampler,
      scalarUniform, finish, bind_assoc, monad_norm]
  rw [left_eq, right_eq]
  refine evalDist_bind_congr' challengeSampler fun challenge ↦ ?_
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    hUniform (finish challenge)

/-- Preprocess a complete source-aligned scalar adversary with exact ring scalarization. -/
noncomputable def ringAdversary {Secret : Type}
    {q degree samples : ℕ} [NeZero q]
    {secretSampler : ProbComp Secret}
    {embed : Secret → Fin 1 → RLWE.Rq q (degree + 1)}
    {ringErrorSampler : ProbComp (RLWE.Rq q (degree + 1))}
    (adversary : LearningWithErrors.Adversary
      (scalarProblem q degree samples secretSampler embed ringErrorSampler)) :
    LearningWithErrors.Adversary
      (ringProblem q degree samples secretSampler embed ringErrorSampler) :=
  fun transcript ↦ adversary (transcriptMap q degree samples transcript)

/-- Exact equality of real-game outputs under ring scalarization. -/
theorem game0_evalDist_eq {Secret : Type}
    (q degree samples : ℕ) [NeZero q]
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → RLWE.Rq q (degree + 1))
    (ringErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (adversary : LearningWithErrors.Adversary
      (scalarProblem q degree samples secretSampler embed ringErrorSampler)) :
    evalDist (LearningWithErrors.game0
        (scalarProblem q degree samples secretSampler embed ringErrorSampler)
        adversary) =
      evalDist (LearningWithErrors.game0
        (ringProblem q degree samples secretSampler embed ringErrorSampler)
        (ringAdversary adversary)) := by
  rw [LearningWithErrors.game0, LearningWithErrors.game0]
  change evalDist (LearningWithErrors.distr
      (scalarProblem q degree samples secretSampler embed ringErrorSampler) >>=
        adversary) =
    evalDist (LearningWithErrors.distr
      (ringProblem q degree samples secretSampler embed ringErrorSampler) >>=
        fun transcript ↦ adversary (transcriptMap q degree samples transcript))
  rw [show (LearningWithErrors.distr
      (ringProblem q degree samples secretSampler embed ringErrorSampler) >>=
        fun transcript ↦ adversary (transcriptMap q degree samples transcript)) =
    ((LearningWithErrors.distr
        (ringProblem q degree samples secretSampler embed ringErrorSampler) >>=
      fun transcript ↦ pure (transcriptMap q degree samples transcript)) >>=
        adversary) by simp [bind_assoc, monad_norm]]
  rw [evalDist_bind, evalDist_bind,
    real_evalDist q degree samples secretSampler embed ringErrorSampler]

/-- Exact equality of uniform-game outputs under ring scalarization. -/
theorem game1_evalDist_eq {Secret : Type}
    (q degree samples : ℕ) [NeZero q]
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → RLWE.Rq q (degree + 1))
    (ringErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (adversary : LearningWithErrors.Adversary
      (scalarProblem q degree samples secretSampler embed ringErrorSampler)) :
    evalDist (LearningWithErrors.game1
        (scalarProblem q degree samples secretSampler embed ringErrorSampler)
        adversary) =
      evalDist (LearningWithErrors.game1
        (ringProblem q degree samples secretSampler embed ringErrorSampler)
        (ringAdversary adversary)) := by
  rw [LearningWithErrors.game1, LearningWithErrors.game1]
  change evalDist (LearningWithErrors.uniformDistr
      (scalarProblem q degree samples secretSampler embed ringErrorSampler) >>=
        adversary) =
    evalDist (LearningWithErrors.uniformDistr
      (ringProblem q degree samples secretSampler embed ringErrorSampler) >>=
        fun transcript ↦ adversary (transcriptMap q degree samples transcript))
  rw [show (LearningWithErrors.uniformDistr
      (ringProblem q degree samples secretSampler embed ringErrorSampler) >>=
        fun transcript ↦ adversary (transcriptMap q degree samples transcript)) =
    ((LearningWithErrors.uniformDistr
        (ringProblem q degree samples secretSampler embed ringErrorSampler) >>=
      fun transcript ↦ pure (transcriptMap q degree samples transcript)) >>=
        adversary) by simp [bind_assoc, monad_norm]]
  rw [evalDist_bind, evalDist_bind,
    uniform_evalDist q degree samples secretSampler embed ringErrorSampler]

/-- Exact main transport theorem: the complete scalarized source-aligned suffix advantage is one
rank-one ring-LWE advantage, with no loss and no additional assumption. -/
theorem advantage_eq_ring {Secret : Type}
    (q degree samples : ℕ) [NeZero q]
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → RLWE.Rq q (degree + 1))
    (ringErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (adversary : LearningWithErrors.Adversary
      (scalarProblem q degree samples secretSampler embed ringErrorSampler)) :
    LearningWithErrors.advantage
        (scalarProblem q degree samples secretSampler embed ringErrorSampler)
        adversary =
      LearningWithErrors.advantage
        (ringProblem q degree samples secretSampler embed ringErrorSampler)
        (ringAdversary adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage,
    FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (game0_evalDist_eq q degree samples secretSampler embed ringErrorSampler adversary) true,
    evalDist_ext_iff.mp
      (game1_evalDist_eq q degree samples secretSampler embed ringErrorSampler adversary) true]

/-- Any concrete bound for the underlying ring problem transfers exactly to its complete
source-aligned scalar presentation. -/
theorem advantage_le_of_ring {Secret : Type}
    (q degree samples : ℕ) [NeZero q]
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin 1 → RLWE.Rq q (degree + 1))
    (ringErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (bound : ℝ)
    (hring : ∀ ringDistinguisher : LearningWithErrors.Adversary
        (ringProblem q degree samples secretSampler embed ringErrorSampler),
      LearningWithErrors.advantage
        (ringProblem q degree samples secretSampler embed ringErrorSampler)
        ringDistinguisher ≤ bound)
    (adversary : LearningWithErrors.Adversary
      (scalarProblem q degree samples secretSampler embed ringErrorSampler)) :
    LearningWithErrors.advantage
        (scalarProblem q degree samples secretSampler embed ringErrorSampler)
        adversary ≤ bound := by
  rw [advantage_eq_ring q degree samples secretSampler embed ringErrorSampler]
  exact hring _

end

end FormalProof4FHE.TFHE.SourceAlignedSuffixRLWEReduction
