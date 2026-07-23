/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.SampleRestriction

/-!
# Direct Affine Circular LWE Hints

This module formalizes the exact coefficient-shift argument for a fixed batch of direct LWE
encryptions of affine functions of their own encryption secret.  If the public affine messages are

`message_j(s) = sum_i s_i * coefficients_{i,j} + offset_j`,

then translating the ordinary LWE challenge matrix by `-coefficients` absorbs every linear term at
once.  Translating the output by `offset` accounts for the constant terms.  Both translations are
permutations, so the real and uniform games are preserved exactly and there is no hybrid loss.

This is a genuine one-key affine KDM/circular-security theorem for *direct fresh LWE rows*.  It does
not identify a structured GSW/TGSW/TRGSW bootstrapping ciphertext with such rows, and therefore does
not by itself prove native TFHE bootstrapping-key security.
-/

open Matrix OracleComp

namespace FormalProof4FHE.LWE.AffineCircular

/-- Public linear coefficients of a fixed affine-message batch. -/
abbrev Coefficients (R : Type) (dimension samples : ℕ) :=
  Matrix (Fin dimension) (Fin samples) R

/-- Constant terms of a fixed affine-message batch. -/
abbrev Offset (R : Type) (samples : ℕ) := Fin samples → R

/-- Evaluate every public affine function on the embedded encryption secret. -/
def affineMessage {R Secret : Type} [Semiring R]
    {dimension samples : ℕ}
    (embed : Secret → Fin dimension → R)
    (coefficients : Coefficients R dimension samples)
    (offset : Offset R samples) (secret : Secret) : Fin samples → R :=
  vecMul (embed secret) coefficients + offset

/-- Direct LWE hints encrypting a fixed batch of affine functions of the same encryption secret. -/
def problem {R Secret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (dimension samples : ℕ)
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin dimension → R)
    (coefficients : Coefficients R dimension samples)
    (offset : Offset R samples)
    (errorSampler : ProbComp R) :
    LearningWithErrors.Problem
      (Matrix (Fin dimension) (Fin samples) R) Secret (Fin samples → R) where
  sampleChallenge := $ᵗ Matrix (Fin dimension) (Fin samples) R
  sampleSecret := secretSampler
  sampleError := ProbComp.sampleIID samples errorSampler
  noiseless := fun secret challenge ↦
    vecMul (embed secret) challenge + affineMessage embed coefficients offset secret
  sampleUniform := $ᵗ (Fin samples → R)

/-- The ordinary embedded-secret batch-LWE problem underlying the circular-hint reduction. -/
abbrev ordinaryProblem {R Secret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (dimension samples : ℕ)
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin dimension → R)
    (errorSampler : ProbComp R) :=
  FormalProof4FHE.LWE.embeddedBatchProblem
    dimension samples secretSampler embed errorSampler

/-- Translate the public LWE coefficients to absorb the linear KDM term. -/
def shiftChallenge {R : Type} [Sub R] {dimension samples : ℕ}
    (coefficients : Coefficients R dimension samples)
    (challenge : Matrix (Fin dimension) (Fin samples) R) :
    Matrix (Fin dimension) (Fin samples) R :=
  challenge - coefficients

/-- Translate an ordinary transcript into a direct affine circular-hint transcript. -/
def shiftTranscript {R : Type} [AddGroup R] {dimension samples : ℕ}
    (coefficients : Coefficients R dimension samples)
    (offset : Offset R samples)
    (transcript : BatchTranscript R dimension samples) :
    BatchTranscript R dimension samples :=
  (shiftChallenge coefficients transcript.1, transcript.2 + offset)

/-- Inverse translation from an affine circular-hint transcript to an ordinary transcript. -/
def unshiftTranscript {R : Type} [AddGroup R] {dimension samples : ℕ}
    (coefficients : Coefficients R dimension samples)
    (offset : Offset R samples)
    (transcript : BatchTranscript R dimension samples) :
    BatchTranscript R dimension samples :=
  (transcript.1 + coefficients, transcript.2 - offset)

@[simp]
theorem unshiftTranscript_shiftTranscript {R : Type} [AddGroup R]
    {dimension samples : ℕ}
    (coefficients : Coefficients R dimension samples)
    (offset : Offset R samples)
    (transcript : BatchTranscript R dimension samples) :
    unshiftTranscript coefficients offset (shiftTranscript coefficients offset transcript) =
      transcript := by
  rcases transcript with ⟨challenge, output⟩
  simp [shiftTranscript, unshiftTranscript, shiftChallenge]

@[simp]
theorem shiftTranscript_unshiftTranscript {R : Type} [AddGroup R]
    {dimension samples : ℕ}
    (coefficients : Coefficients R dimension samples)
    (offset : Offset R samples)
    (transcript : BatchTranscript R dimension samples) :
    shiftTranscript coefficients offset (unshiftTranscript coefficients offset transcript) =
      transcript := by
  rcases transcript with ⟨challenge, output⟩
  simp [shiftTranscript, unshiftTranscript, shiftChallenge]

/-- The complete transcript translation is a permutation. -/
theorem shiftTranscript_bijective {R : Type} [AddGroup R]
    {dimension samples : ℕ}
    (coefficients : Coefficients R dimension samples)
    (offset : Offset R samples) :
    Function.Bijective (shiftTranscript coefficients offset) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨unshiftTranscript coefficients offset,
      unshiftTranscript_shiftTranscript coefficients offset,
      shiftTranscript_unshiftTranscript coefficients offset⟩

/-- Translating only the challenge matrix is a permutation. -/
theorem shiftChallenge_bijective {R : Type} [AddGroup R]
    {dimension samples : ℕ}
    (coefficients : Coefficients R dimension samples) :
    Function.Bijective (shiftChallenge coefficients) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨(fun challenge ↦ challenge + coefficients), ?_, ?_⟩
  · intro challenge
    simp [shiftChallenge]
  · intro challenge
    simp [shiftChallenge]

/-- The transcript shift turns an ordinary real sample into the corresponding affine-message
sample exactly. -/
theorem shiftTranscript_real {R Secret : Type} [Ring R]
    {dimension samples : ℕ}
    (embed : Secret → Fin dimension → R)
    (coefficients : Coefficients R dimension samples)
    (offset : Offset R samples)
    (secret : Secret)
    (challenge : Matrix (Fin dimension) (Fin samples) R)
    (error : Fin samples → R) :
    shiftTranscript coefficients offset
        (challenge, vecMul (embed secret) challenge + error) =
      (shiftChallenge coefficients challenge,
        (vecMul (embed secret) (shiftChallenge coefficients challenge) +
          affineMessage embed coefficients offset secret) + error) := by
  apply Prod.ext
  · rfl
  · funext sample
    simp only [shiftTranscript, shiftChallenge, affineMessage,
      Pi.add_apply, Matrix.vecMul, dotProduct, Matrix.sub_apply]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib]
    abel

/-- Push a direct affine-hint distinguisher through the exact transcript translation. -/
def reduction {R Secret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    {dimension samples : ℕ}
    {secretSampler : ProbComp Secret}
    {embed : Secret → Fin dimension → R}
    {coefficients : Coefficients R dimension samples}
    {offset : Offset R samples}
    {errorSampler : ProbComp R}
    (adversary : LearningWithErrors.Adversary
      (problem dimension samples secretSampler embed coefficients offset errorSampler)) :
    LearningWithErrors.Adversary
      (ordinaryProblem dimension samples secretSampler embed errorSampler) :=
  fun transcript ↦ adversary (shiftTranscript coefficients offset transcript)

/-- The real affine-hint distribution is exactly an ordinary LWE distribution followed by the
public transcript translation. -/
theorem real_evalDist {R Secret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (dimension samples : ℕ)
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin dimension → R)
    (coefficients : Coefficients R dimension samples)
    (offset : Offset R samples)
    (errorSampler : ProbComp R) :
    evalDist (LearningWithErrors.distr
          (ordinaryProblem dimension samples secretSampler embed errorSampler) >>=
        fun transcript ↦ pure (shiftTranscript coefficients offset transcript)) =
      evalDist (LearningWithErrors.distr
        (problem dimension samples secretSampler embed coefficients offset errorSampler)) := by
  let challenges : ProbComp (Matrix (Fin dimension) (Fin samples) R) :=
    $ᵗ Matrix (Fin dimension) (Fin samples) R
  let errors : ProbComp (Fin samples → R) :=
    ProbComp.sampleIID samples errorSampler
  let finish : Matrix (Fin dimension) (Fin samples) R → Secret →
      (Fin samples → R) → ProbComp (BatchTranscript R dimension samples) :=
    fun challenge secret error ↦ pure (challenge,
        (vecMul (embed secret) challenge +
          affineMessage embed coefficients offset secret) + error)
  let shift := shiftChallenge coefficients
  have left_eq :
      (LearningWithErrors.distr
          (ordinaryProblem dimension samples secretSampler embed errorSampler) >>=
        fun transcript ↦ pure (shiftTranscript coefficients offset transcript)) =
      (challenges >>= fun challenge ↦
        secretSampler >>= fun secret ↦
        errors >>= fun error ↦
        finish (shift challenge) secret error) := by
    simp [LearningWithErrors.distr, ordinaryProblem,
      FormalProof4FHE.LWE.embeddedBatchProblem, challenges, errors, finish, shift,
      shiftTranscript_real, monad_norm]
  have right_eq :
      LearningWithErrors.distr
          (problem dimension samples secretSampler embed coefficients offset errorSampler) =
      (challenges >>= fun challenge ↦
        secretSampler >>= fun secret ↦
        errors >>= fun error ↦
        finish challenge secret error) := by
    simp [LearningWithErrors.distr, problem, challenges, errors, finish, monad_norm]
  rw [left_eq, right_eq]
  apply evalDist_ext
  intro transcript
  simpa only [challenges, shift] using
    (probOutput_bind_bijective_uniform_cross
      (α := Matrix (Fin dimension) (Fin samples) R)
      (β := Matrix (Fin dimension) (Fin samples) R)
      (shiftChallenge coefficients) (shiftChallenge_bijective coefficients)
      (fun challenge ↦
        secretSampler >>= fun secret ↦
        errors >>= fun error ↦
        finish challenge secret error) transcript)

/-- The uniform branch of the ordinary problem is the canonical uniform transcript sampler. -/
theorem ordinary_uniformDistr_eq_uniformSample {R Secret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (dimension samples : ℕ)
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin dimension → R)
    (errorSampler : ProbComp R) :
    LearningWithErrors.uniformDistr
        (ordinaryProblem dimension samples secretSampler embed errorSampler) =
      ($ᵗ (BatchTranscript R dimension samples)) := by
  unfold LearningWithErrors.uniformDistr ordinaryProblem
    FormalProof4FHE.LWE.embeddedBatchProblem
  have uniformProduct :
      ($ᵗ (BatchTranscript R dimension samples) :
        ProbComp (BatchTranscript R dimension samples)) =
      Prod.mk <$> ($ᵗ Matrix (Fin dimension) (Fin samples) R) <*>
        ($ᵗ (Fin samples → R)) := rfl
  rw [uniformProduct]
  simp [monad_norm]

/-- The uniform branch of the affine-hint problem is the same canonical uniform transcript. -/
theorem uniformDistr_eq_uniformSample {R Secret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (dimension samples : ℕ)
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin dimension → R)
    (coefficients : Coefficients R dimension samples)
    (offset : Offset R samples)
    (errorSampler : ProbComp R) :
    LearningWithErrors.uniformDistr
        (problem dimension samples secretSampler embed coefficients offset errorSampler) =
      ($ᵗ (BatchTranscript R dimension samples)) := by
  unfold LearningWithErrors.uniformDistr problem
  have uniformProduct :
      ($ᵗ (BatchTranscript R dimension samples) :
        ProbComp (BatchTranscript R dimension samples)) =
      Prod.mk <$> ($ᵗ Matrix (Fin dimension) (Fin samples) R) <*>
        ($ᵗ (Fin samples → R)) := rfl
  rw [uniformProduct]
  simp [monad_norm]

/-- The transcript translation also maps the ordinary uniform branch exactly to the affine-hint
uniform branch. -/
theorem uniform_evalDist {R Secret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (dimension samples : ℕ)
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin dimension → R)
    (coefficients : Coefficients R dimension samples)
    (offset : Offset R samples)
    (errorSampler : ProbComp R) :
    evalDist (LearningWithErrors.uniformDistr
          (ordinaryProblem dimension samples secretSampler embed errorSampler) >>=
        fun transcript ↦ pure (shiftTranscript coefficients offset transcript)) =
      evalDist (LearningWithErrors.uniformDistr
        (problem dimension samples secretSampler embed coefficients offset errorSampler)) := by
  rw [ordinary_uniformDistr_eq_uniformSample dimension samples secretSampler embed errorSampler,
    uniformDistr_eq_uniformSample dimension samples secretSampler embed
      coefficients offset errorSampler]
  simpa [map_eq_bind_pure_comp, monad_norm] using
    (evalDist_map_bijective_uniform_cross
      (α := BatchTranscript R dimension samples)
      (β := BatchTranscript R dimension samples)
      (shiftTranscript coefficients offset)
      (shiftTranscript_bijective coefficients offset))

/-- Exact real-game equality for the affine circular-hint reduction. -/
theorem game0_evalDist_eq {R Secret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (dimension samples : ℕ)
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin dimension → R)
    (coefficients : Coefficients R dimension samples)
    (offset : Offset R samples)
    (errorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem dimension samples secretSampler embed coefficients offset errorSampler)) :
    evalDist (LearningWithErrors.game0
        (problem dimension samples secretSampler embed coefficients offset errorSampler)
        adversary) =
      evalDist (LearningWithErrors.game0
        (ordinaryProblem dimension samples secretSampler embed errorSampler)
        (reduction adversary)) := by
  rw [LearningWithErrors.game0, LearningWithErrors.game0]
  simp only [reduction]
  rw [show (LearningWithErrors.distr
        (ordinaryProblem dimension samples secretSampler embed errorSampler) >>=
      fun transcript ↦ adversary (shiftTranscript coefficients offset transcript)) =
    ((LearningWithErrors.distr
        (ordinaryProblem dimension samples secretSampler embed errorSampler) >>=
      fun transcript ↦ pure (shiftTranscript coefficients offset transcript)) >>= adversary) by
    simp [bind_assoc, monad_norm]]
  rw [evalDist_bind, evalDist_bind,
    real_evalDist dimension samples secretSampler embed coefficients offset errorSampler]

/-- Exact uniform-game equality for the affine circular-hint reduction. -/
theorem game1_evalDist_eq {R Secret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (dimension samples : ℕ)
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin dimension → R)
    (coefficients : Coefficients R dimension samples)
    (offset : Offset R samples)
    (errorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem dimension samples secretSampler embed coefficients offset errorSampler)) :
    evalDist (LearningWithErrors.game1
        (problem dimension samples secretSampler embed coefficients offset errorSampler)
        adversary) =
      evalDist (LearningWithErrors.game1
        (ordinaryProblem dimension samples secretSampler embed errorSampler)
        (reduction adversary)) := by
  rw [LearningWithErrors.game1, LearningWithErrors.game1]
  simp only [reduction]
  rw [show (LearningWithErrors.uniformDistr
        (ordinaryProblem dimension samples secretSampler embed errorSampler) >>=
      fun transcript ↦ adversary (shiftTranscript coefficients offset transcript)) =
    ((LearningWithErrors.uniformDistr
        (ordinaryProblem dimension samples secretSampler embed errorSampler) >>=
      fun transcript ↦ pure (shiftTranscript coefficients offset transcript)) >>= adversary) by
    simp [bind_assoc, monad_norm]]
  rw [evalDist_bind, evalDist_bind,
    uniform_evalDist dimension samples secretSampler embed coefficients offset errorSampler]

/-- **Exact affine circular-security theorem.** A fixed batch of direct fresh LWE encryptions of
arbitrary public affine functions of the same secret has exactly the advantage of one ordinary
batch-LWE distinguisher. -/
theorem advantage_eq_lwe {R Secret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (dimension samples : ℕ)
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin dimension → R)
    (coefficients : Coefficients R dimension samples)
    (offset : Offset R samples)
    (errorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem dimension samples secretSampler embed coefficients offset errorSampler)) :
    LearningWithErrors.advantage
        (problem dimension samples secretSampler embed coefficients offset errorSampler)
        adversary =
      LearningWithErrors.advantage
        (ordinaryProblem dimension samples secretSampler embed errorSampler)
        (reduction adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage,
    FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (game0_evalDist_eq dimension samples secretSampler embed coefficients offset
        errorSampler adversary) true,
    evalDist_ext_iff.mp
      (game1_evalDist_eq dimension samples secretSampler embed coefficients offset
        errorSampler adversary) true]

/-- Any ordinary-LWE bound transfers to direct fixed affine circular hints with no loss. -/
theorem hardAgainst_of_lwe {R Secret : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (dimension samples : ℕ)
    (secretSampler : ProbComp Secret)
    (embed : Secret → Fin dimension → R)
    (coefficients : Coefficients R dimension samples)
    (offset : Offset R samples)
    (errorSampler : ProbComp R)
    (circularAllowed : LearningWithErrors.Adversary
      (problem dimension samples secretSampler embed coefficients offset errorSampler) → Prop)
    (lweAllowed : LearningWithErrors.Adversary
      (ordinaryProblem dimension samples secretSampler embed errorSampler) → Prop)
    (bound : ℝ)
    (hReductionClosed : ∀ adversary, circularAllowed adversary →
      lweAllowed (reduction adversary))
    (hLWE : FormalProof4FHE.LWE.HardAgainst
      (ordinaryProblem dimension samples secretSampler embed errorSampler)
      lweAllowed bound) :
    FormalProof4FHE.LWE.HardAgainst
      (problem dimension samples secretSampler embed coefficients offset errorSampler)
      circularAllowed bound := by
  intro adversary hadversary
  rw [advantage_eq_lwe dimension samples secretSampler embed coefficients offset
    errorSampler adversary]
  exact hLWE _ (hReductionClosed adversary hadversary)

end FormalProof4FHE.LWE.AffineCircular
