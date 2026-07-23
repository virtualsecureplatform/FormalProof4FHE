/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.ParallelBatch

/-!
# Direct Multi-Key Affine Circular LWE

This module formalizes the binary master-mask argument for a fixed batch of direct LWE hints.
There are `users` independent binary keys of one common dimension.  A row encrypted under any
target key may contain an arbitrary public affine function of every source key.  The complete
joint real/zero-hint distinguishing problem reduces exactly to ordinary binary-secret LWE with
`users * samples` rows; there is no hybrid or statistical loss.

The reduction samples one master key `x` and public-to-the-reduction masks `r_i`, and represents
the user keys as `s_i = x xor r_i`.  Over the coefficient ring this is

`embed(s_i) = sign(r_i) * embed(x) + embed(r_i)`.

The diagonal signs are units, so each target challenge matrix is translated and sign-flipped by
a bijection.  This is the direct-hint affine KDM baseline underlying the ACPS-style master-key
simulation.  It deliberately does **not** cover the bilinear gadget-phase messages in native
TFHE's TRGSW bootstrapping key.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.LWE.MultiKeyAffine

/-- One binary vector. -/
abbrev BinaryVector (dimension : ℕ) := Fin dimension → Bool

/-- A family of binary vectors, one per user. -/
abbrev BinaryKeys (users dimension : ℕ) := Fin users → BinaryVector dimension

/-- Public affine coefficients indexed by source user, target user, secret coordinate, and row. -/
abbrev Coefficients (R : Type) (users dimension samples : ℕ) :=
  Fin users → Fin users → Fin dimension → Fin samples → R

/-- Public affine constants indexed by target user and row. -/
abbrev Offsets (R : Type) (users samples : ℕ) :=
  Fin users → Fin samples → R

/-- Embed a bit as zero or one. -/
def embedBit {R : Type} [Zero R] [One R] (bit : Bool) : R :=
  if bit then 1 else 0

/-- The diagonal sign selected by a binary mask. -/
def maskSign {R : Type} [Ring R] (mask : Bool) : R :=
  if mask then -1 else 1

/-- Toggle a master bit exactly when the corresponding mask bit is true. -/
def maskedBit (master mask : Bool) : Bool :=
  if mask then !master else master

/-- Derive all user keys from one master key and independent binary masks. -/
def deriveKeys {users dimension : ℕ}
    (master : BinaryVector dimension) (masks : BinaryKeys users dimension) :
    BinaryKeys users dimension :=
  fun user coordinate ↦ maskedBit (master coordinate) (masks user coordinate)

@[simp]
theorem maskedBit_involutive (master mask : Bool) :
    maskedBit master (maskedBit master mask) = mask := by
  cases master <;> cases mask <;> rfl

@[simp]
theorem deriveKeys_involutive {users dimension : ℕ}
    (master : BinaryVector dimension) (masks : BinaryKeys users dimension) :
    deriveKeys master (deriveKeys master masks) = masks := by
  funext user coordinate
  exact maskedBit_involutive (master coordinate) (masks user coordinate)

/-- For a fixed master key, toggling by masks is a permutation of complete key families. -/
def deriveKeysEquiv {users dimension : ℕ} (master : BinaryVector dimension) :
    BinaryKeys users dimension ≃ BinaryKeys users dimension where
  toFun := deriveKeys master
  invFun := deriveKeys master
  left_inv := deriveKeys_involutive master
  right_inv := deriveKeys_involutive master

/-- The Boolean master-mask identity inside any coefficient ring. -/
theorem embed_maskedBit {R : Type} [Ring R] (master mask : Bool) :
    embedBit (R := R) (maskedBit master mask) =
      maskSign mask * embedBit master + embedBit mask := by
  cases master <;> cases mask <;> simp [maskedBit, maskSign, embedBit]

/-- Evaluate the fixed public affine message family on a tuple of binary keys. -/
def affineMessage {R : Type} [Semiring R] {users dimension samples : ℕ}
    (coefficients : Coefficients R users dimension samples)
    (offsets : Offsets R users samples)
    (keys : BinaryKeys users dimension) :
    FormalProof4FHE.LWE.ParallelBatch.Output R users samples :=
  fun target sample ↦ offsets target sample +
    ∑ source, ∑ coordinate,
      embedBit (R := R) (keys source coordinate) *
        coefficients source target coordinate sample

/-- The master-secret coefficient shift induced by all masked source keys. -/
def coefficientShift {R : Type} [Ring R] {users dimension samples : ℕ}
    (masks : BinaryKeys users dimension)
    (coefficients : Coefficients R users dimension samples) :
    FormalProof4FHE.LWE.ParallelBatch.Challenge R dimension users samples :=
  fun target coordinate sample ↦
    ∑ source, maskSign (R := R) (masks source coordinate) *
      coefficients source target coordinate sample

/-- The constant part of every affine message after introducing the master masks. -/
def maskedOffset {R : Type} [Semiring R] {users dimension samples : ℕ}
    (masks : BinaryKeys users dimension)
    (coefficients : Coefficients R users dimension samples)
    (offsets : Offsets R users samples) :
    FormalProof4FHE.LWE.ParallelBatch.Output R users samples :=
  fun target sample ↦ offsets target sample +
    ∑ source, ∑ coordinate,
      embedBit (R := R) (masks source coordinate) *
        coefficients source target coordinate sample

/-- Translate and sign-flip the master LWE challenge for every target key. -/
def transformChallenge {R : Type} [Ring R] {users dimension samples : ℕ}
    (masks : BinaryKeys users dimension)
    (coefficients : Coefficients R users dimension samples)
    (challenge : FormalProof4FHE.LWE.ParallelBatch.Challenge
      R dimension users samples) :
    FormalProof4FHE.LWE.ParallelBatch.Challenge R dimension users samples :=
  fun target coordinate sample ↦
    maskSign (R := R) (masks target coordinate) *
      (challenge target coordinate sample -
        coefficientShift masks coefficients target coordinate sample)

/-- Inverse of `transformChallenge`. -/
def untransformChallenge {R : Type} [Ring R] {users dimension samples : ℕ}
    (masks : BinaryKeys users dimension)
    (coefficients : Coefficients R users dimension samples)
    (challenge : FormalProof4FHE.LWE.ParallelBatch.Challenge
      R dimension users samples) :
    FormalProof4FHE.LWE.ParallelBatch.Challenge R dimension users samples :=
  fun target coordinate sample ↦
    maskSign (R := R) (masks target coordinate) *
      challenge target coordinate sample +
        coefficientShift masks coefficients target coordinate sample

@[simp]
theorem maskSign_sq {R : Type} [Ring R] (mask : Bool) :
    maskSign (R := R) mask * maskSign mask = 1 := by
  cases mask <;> simp [maskSign]

@[simp]
theorem untransformChallenge_transformChallenge {R : Type} [Ring R]
    {users dimension samples : ℕ}
    (masks : BinaryKeys users dimension)
    (coefficients : Coefficients R users dimension samples)
    (challenge : FormalProof4FHE.LWE.ParallelBatch.Challenge
      R dimension users samples) :
    untransformChallenge masks coefficients
      (transformChallenge masks coefficients challenge) = challenge := by
  funext target coordinate sample
  cases hmask : masks target coordinate <;>
    simp [untransformChallenge, transformChallenge, maskSign, hmask]

@[simp]
theorem transformChallenge_untransformChallenge {R : Type} [Ring R]
    {users dimension samples : ℕ}
    (masks : BinaryKeys users dimension)
    (coefficients : Coefficients R users dimension samples)
    (challenge : FormalProof4FHE.LWE.ParallelBatch.Challenge
      R dimension users samples) :
    transformChallenge masks coefficients
      (untransformChallenge masks coefficients challenge) = challenge := by
  funext target coordinate sample
  cases hmask : masks target coordinate <;>
    simp [untransformChallenge, transformChallenge, maskSign, hmask]

/-- The challenge transformation is a permutation for every fixed mask family. -/
theorem transformChallenge_bijective {R : Type} [Ring R]
    {users dimension samples : ℕ}
    (masks : BinaryKeys users dimension)
    (coefficients : Coefficients R users dimension samples) :
    Function.Bijective (transformChallenge masks coefficients) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨untransformChallenge masks coefficients,
      untransformChallenge_transformChallenge masks coefficients,
      transformChallenge_untransformChallenge masks coefficients⟩

@[simp]
theorem maskSign_pow_two {R : Type} [Ring R] (mask : Bool) :
    maskSign (R := R) mask ^ 2 = 1 := by
  cases mask <;> simp [maskSign]

@[simp]
theorem maskSign_mul_middle {R : Type} [CommRing R]
    (mask : Bool) (left right : R) :
    maskSign (R := R) mask * left * (maskSign mask * right) = left * right := by
  cases mask <;> simp [maskSign]

/-- Expanding the coefficient shift and interchanging its two finite sums. -/
theorem sum_embed_mul_coefficientShift {R : Type} [CommRing R]
    {users dimension samples : ℕ}
    (master : BinaryVector dimension)
    (masks : BinaryKeys users dimension)
    (coefficients : Coefficients R users dimension samples)
    (target : Fin users) (sample : Fin samples) :
    (∑ coordinate, embedBit (R := R) (master coordinate) *
      coefficientShift masks coefficients target coordinate sample) =
      ∑ source, ∑ coordinate,
        maskSign (R := R) (masks source coordinate) *
          embedBit (master coordinate) * coefficients source target coordinate sample := by
  simp only [coefficientShift]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro source _
  apply Finset.sum_congr rfl
  intro coordinate _
  ring

/-- Transform one master-secret transcript into all target-key affine transcripts. -/
def transformTranscript {R : Type} [CommRing R] {users dimension samples : ℕ}
    (masks : BinaryKeys users dimension)
    (coefficients : Coefficients R users dimension samples)
    (offsets : Offsets R users samples)
    (transcript : FormalProof4FHE.LWE.ParallelBatch.Transcript
      R dimension users samples) :
    FormalProof4FHE.LWE.ParallelBatch.Transcript R dimension users samples :=
  let challenge := transformChallenge masks coefficients transcript.1
  (challenge, fun target sample ↦
    transcript.2 target sample +
      dotProduct (fun coordinate ↦ embedBit (R := R) (masks target coordinate))
        (fun coordinate ↦ challenge target coordinate sample) +
      maskedOffset masks coefficients offsets target sample)

/-- Undo the triangular transcript transformation. -/
def untransformTranscript {R : Type} [CommRing R] {users dimension samples : ℕ}
    (masks : BinaryKeys users dimension)
    (coefficients : Coefficients R users dimension samples)
    (offsets : Offsets R users samples)
    (transcript : FormalProof4FHE.LWE.ParallelBatch.Transcript
      R dimension users samples) :
    FormalProof4FHE.LWE.ParallelBatch.Transcript R dimension users samples :=
  (untransformChallenge masks coefficients transcript.1,
    fun target sample ↦
      transcript.2 target sample -
        dotProduct (fun coordinate ↦ embedBit (R := R) (masks target coordinate))
          (fun coordinate ↦ transcript.1 target coordinate sample) -
        maskedOffset masks coefficients offsets target sample)

@[simp]
theorem untransformTranscript_transformTranscript {R : Type} [CommRing R]
    {users dimension samples : ℕ}
    (masks : BinaryKeys users dimension)
    (coefficients : Coefficients R users dimension samples)
    (offsets : Offsets R users samples)
    (transcript : FormalProof4FHE.LWE.ParallelBatch.Transcript
      R dimension users samples) :
    untransformTranscript masks coefficients offsets
      (transformTranscript masks coefficients offsets transcript) = transcript := by
  apply Prod.ext
  · exact untransformChallenge_transformChallenge masks coefficients transcript.1
  · funext target sample
    simp [untransformTranscript, transformTranscript]
    abel

@[simp]
theorem transformTranscript_untransformTranscript {R : Type} [CommRing R]
    {users dimension samples : ℕ}
    (masks : BinaryKeys users dimension)
    (coefficients : Coefficients R users dimension samples)
    (offsets : Offsets R users samples)
    (transcript : FormalProof4FHE.LWE.ParallelBatch.Transcript
      R dimension users samples) :
    transformTranscript masks coefficients offsets
      (untransformTranscript masks coefficients offsets transcript) = transcript := by
  apply Prod.ext
  · exact transformChallenge_untransformChallenge masks coefficients transcript.1
  · funext target sample
    simp [untransformTranscript, transformTranscript]
    abel

/-- The complete triangular transcript transformation is a permutation. -/
theorem transformTranscript_bijective {R : Type} [CommRing R]
    {users dimension samples : ℕ}
    (masks : BinaryKeys users dimension)
    (coefficients : Coefficients R users dimension samples)
    (offsets : Offsets R users samples) :
    Function.Bijective (transformTranscript masks coefficients offsets) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨untransformTranscript masks coefficients offsets,
      untransformTranscript_transformTranscript masks coefficients offsets,
      transformTranscript_untransformTranscript masks coefficients offsets⟩

/-- Deterministic direct multi-key affine transcript assembly. -/
def directTranscript {R : Type} [CommRing R] {users dimension samples : ℕ}
    (coefficients : Coefficients R users dimension samples)
    (offsets : Offsets R users samples)
    (keys : BinaryKeys users dimension)
    (challenge : FormalProof4FHE.LWE.ParallelBatch.Challenge
      R dimension users samples)
    (error : FormalProof4FHE.LWE.ParallelBatch.Output R users samples) :
    FormalProof4FHE.LWE.ParallelBatch.Transcript R dimension users samples :=
  (challenge, fun target ↦
    vecMul (fun coordinate ↦ embedBit (R := R) (keys target coordinate))
      (challenge target) + affineMessage coefficients offsets keys target + error target)

/-- The master-mask transcript transformation has exactly the desired direct affine phases. -/
theorem transformTranscript_real {R : Type} [CommRing R]
    {users dimension samples : ℕ}
    (master : BinaryVector dimension)
    (masks : BinaryKeys users dimension)
    (coefficients : Coefficients R users dimension samples)
    (offsets : Offsets R users samples)
    (challenge : FormalProof4FHE.LWE.ParallelBatch.Challenge
      R dimension users samples)
    (error : FormalProof4FHE.LWE.ParallelBatch.Output R users samples) :
    transformTranscript masks coefficients offsets
        (FormalProof4FHE.LWE.ParallelBatch.realTranscript
          (fun key coordinate ↦ embedBit (R := R) (key coordinate))
          challenge master error) =
      directTranscript coefficients offsets (deriveKeys master masks)
        (transformChallenge masks coefficients challenge) error := by
  apply Prod.ext
  · rfl
  · funext target sample
    simp only [transformTranscript, directTranscript,
      FormalProof4FHE.LWE.ParallelBatch.realTranscript,
      affineMessage, maskedOffset, deriveKeys, Pi.add_apply,
      Matrix.vecMul, dotProduct]
    simp_rw [embed_maskedBit (R := R)]
    simp_rw [add_mul]
    simp_rw [Finset.sum_add_distrib]
    simp only [transformChallenge]
    simp_rw [maskSign_mul_middle]
    simp_rw [mul_sub]
    simp_rw [Finset.sum_sub_distrib]
    rw [sum_embed_mul_coefficientShift master masks coefficients target sample]
    ring

/-- Canonical direct multi-key affine LWE problem with independent uniform binary keys. -/
noncomputable def problem {R : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (dimension users samples : ℕ)
    (coefficients : Coefficients R users dimension samples)
    (offsets : Offsets R users samples)
    (errorSampler : ProbComp R) :
    LearningWithErrors.Problem
      (FormalProof4FHE.LWE.ParallelBatch.Challenge R dimension users samples)
      (BinaryKeys users dimension)
      (FormalProof4FHE.LWE.ParallelBatch.Output R users samples) where
  sampleChallenge := Fin.mOfFn users fun _ ↦
    $ᵗ Matrix (Fin dimension) (Fin samples) R
  sampleSecret := $ᵗ (BinaryKeys users dimension)
  sampleError := Fin.mOfFn users fun _ ↦ ProbComp.sampleIID samples errorSampler
  noiseless := fun keys challenge target ↦
    vecMul (fun coordinate ↦ embedBit (R := R) (keys target coordinate))
      (challenge target) + affineMessage coefficients offsets keys target
  sampleUniform := Fin.mOfFn users fun _ ↦ $ᵗ (Fin samples → R)

/-- Ordinary parallel binary-secret LWE supplying the master transcript. -/
noncomputable def masterProblem {R : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (dimension users samples : ℕ) (errorSampler : ProbComp R) :=
  FormalProof4FHE.LWE.ParallelBatch.problem dimension users samples
    ($ᵗ (BinaryVector dimension))
    (fun key coordinate ↦ embedBit (R := R) (key coordinate)) errorSampler

/-- Sample user keys through a hidden master key and independent masks. -/
noncomputable def derivedKeySampler (users dimension : ℕ) :
    ProbComp (BinaryKeys users dimension) := do
  let master ← $ᵗ (BinaryVector dimension)
  let masks ← $ᵗ (BinaryKeys users dimension)
  return deriveKeys master masks

/-- For a fixed master key, uniform masks map to a uniform complete key family. -/
theorem deriveKeys_uniform_evalDist (users dimension : ℕ)
    (master : BinaryVector dimension) :
    evalDist (deriveKeys master <$> ($ᵗ (BinaryKeys users dimension))) =
      evalDist ($ᵗ (BinaryKeys users dimension)) :=
  evalDist_map_bijective_uniform_cross
    (α := BinaryKeys users dimension) (β := BinaryKeys users dimension)
    (deriveKeys master) (deriveKeysEquiv master).bijective

/-- The master-mask representation produces exactly independent uniform user keys. -/
theorem derivedKeySampler_evalDist (users dimension : ℕ) :
    evalDist (derivedKeySampler users dimension) =
      evalDist ($ᵗ (BinaryKeys users dimension)) := by
  unfold derivedKeySampler
  calc
    _ = evalDist (($ᵗ (BinaryVector dimension)) >>= fun _ ↦
        ($ᵗ (BinaryKeys users dimension))) := by
      refine evalDist_bind_congr' ($ᵗ (BinaryVector dimension)) fun master ↦ ?_
      simpa only [map_eq_bind_pure_comp, Function.comp_def] using
        deriveKeys_uniform_evalDist users dimension master
    _ = _ :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        ($ᵗ (BinaryVector dimension)) (by simp) _

/-- The internal master/mask context used by the reduction. -/
noncomputable def masterMaskContextSampler (users dimension : ℕ) :
    ProbComp (BinaryVector dimension × BinaryKeys users dimension) := do
  let master ← $ᵗ (BinaryVector dimension)
  let masks ← $ᵗ (BinaryKeys users dimension)
  return (master, masks)

/-- The parallel challenge sampler used by both the ordinary and multi-key problems. -/
noncomputable def challengeSampler {R : Type} [SampleableType R]
    (dimension users samples : ℕ) :
    ProbComp (FormalProof4FHE.LWE.ParallelBatch.Challenge
      R dimension users samples) :=
  Fin.mOfFn users fun _ ↦ $ᵗ Matrix (Fin dimension) (Fin samples) R

/-- The parallel error sampler used by both problems. -/
def errorVectorSampler {R : Type} (users samples : ℕ) (errorSampler : ProbComp R) :
    ProbComp (FormalProof4FHE.LWE.ParallelBatch.Output R users samples) :=
  Fin.mOfFn users fun _ ↦ ProbComp.sampleIID samples errorSampler

/-- Independent uniform matrix blocks are uniform on the complete challenge space. -/
theorem challengeSampler_evalDist_eq_uniform {R : Type}
    [Fintype R] [SampleableType R] (dimension users samples : ℕ) :
    evalDist (challengeSampler (R := R) dimension users samples) =
      evalDist ($ᵗ (FormalProof4FHE.LWE.ParallelBatch.Challenge
        R dimension users samples)) := by
  simpa [challengeSampler, ProbComp.sampleIID] using
    (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
      (alpha := Matrix (Fin dimension) (Fin samples) R) users)

/-- For fixed masks, the challenge transformation preserves the parallel challenge sampler. -/
theorem transformChallenge_sampler_evalDist {R : Type}
    [CommRing R] [Fintype R] [SampleableType R]
    {users dimension samples : ℕ}
    (masks : BinaryKeys users dimension)
    (coefficients : Coefficients R users dimension samples) :
    evalDist (transformChallenge masks coefficients <$>
        challengeSampler (R := R) dimension users samples) =
      evalDist (challengeSampler (R := R) dimension users samples) := by
  let uniform : ProbComp
      (FormalProof4FHE.LWE.ParallelBatch.Challenge R dimension users samples) :=
    $ᵗ (FormalProof4FHE.LWE.ParallelBatch.Challenge R dimension users samples)
  have hSampler := challengeSampler_evalDist_eq_uniform
    (R := R) dimension users samples
  calc
    _ = evalDist (transformChallenge masks coefficients <$> uniform) := by
      simpa only [evalDist_map] using congrArg
        (fun distribution ↦ transformChallenge masks coefficients <$> distribution) hSampler
    _ = evalDist uniform :=
      evalDist_map_bijective_uniform_cross
        (α := FormalProof4FHE.LWE.ParallelBatch.Challenge
          R dimension users samples)
        (β := FormalProof4FHE.LWE.ParallelBatch.Challenge
          R dimension users samples)
        (transformChallenge masks coefficients)
        (transformChallenge_bijective masks coefficients)
    _ = _ := hSampler.symm

/-- A context-dependent permutation may be moved across an independent sampler. -/
theorem evalDist_context_transform_of_preserving
    {Value Context Output : Type}
    (sampler : ProbComp Value) (contextSampler : ProbComp Context)
    (transform : Context → Value → Value)
    (hPreserve : ∀ context,
      evalDist (transform context <$> sampler) = evalDist sampler)
    (finish : Context → Value → ProbComp Output) :
    evalDist (sampler >>= fun value ↦
      contextSampler >>= fun context ↦ finish context (transform context value)) =
    evalDist (sampler >>= fun value ↦
      contextSampler >>= fun context ↦ finish context value) := by
  calc
    _ = evalDist (contextSampler >>= fun context ↦
        sampler >>= fun value ↦ finish context (transform context value)) :=
      evalDist_bind_bind_swap sampler contextSampler
        (fun value context ↦ finish context (transform context value))
    _ = evalDist (contextSampler >>= fun context ↦
        sampler >>= fun value ↦ finish context value) := by
      refine evalDist_bind_congr' contextSampler fun context ↦ ?_
      rw [show (sampler >>= fun value ↦ finish context (transform context value)) =
          ((transform context <$> sampler) >>= finish context) by
            simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind],
        evalDist_bind, hPreserve context, ← evalDist_bind]
    _ = _ :=
      (evalDist_bind_bind_swap sampler contextSampler
        (fun value context ↦ finish context value)).symm

/-- The same direct affine problem, temporarily represented by a hidden master and masks. -/
noncomputable def maskedProblem {R : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (dimension users samples : ℕ)
    (coefficients : Coefficients R users dimension samples)
    (offsets : Offsets R users samples)
    (errorSampler : ProbComp R) :
    LearningWithErrors.Problem
      (FormalProof4FHE.LWE.ParallelBatch.Challenge R dimension users samples)
      (BinaryKeys users dimension)
      (FormalProof4FHE.LWE.ParallelBatch.Output R users samples) where
  sampleChallenge := challengeSampler dimension users samples
  sampleSecret := derivedKeySampler users dimension
  sampleError := errorVectorSampler users samples errorSampler
  noiseless := fun keys challenge target ↦
    vecMul (fun coordinate ↦ embedBit (R := R) (keys target coordinate))
      (challenge target) + affineMessage coefficients offsets keys target
  sampleUniform := Fin.mOfFn users fun _ ↦ $ᵗ (Fin samples → R)

/-- Replacing the hidden master-mask secret sampler by independent uniform keys is exact. -/
theorem maskedProblem_distr_evalDist_eq_problem {R : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (dimension users samples : ℕ)
    (coefficients : Coefficients R users dimension samples)
    (offsets : Offsets R users samples)
    (errorSampler : ProbComp R) :
    evalDist (LearningWithErrors.distr
      (maskedProblem dimension users samples coefficients offsets errorSampler)) =
    evalDist (LearningWithErrors.distr
      (problem dimension users samples coefficients offsets errorSampler)) := by
  let challenges := challengeSampler (R := R) dimension users samples
  let errors := errorVectorSampler users samples errorSampler
  let finish := fun
      (challenge : FormalProof4FHE.LWE.ParallelBatch.Challenge
        R dimension users samples)
      (keys : BinaryKeys users dimension)
      (error : FormalProof4FHE.LWE.ParallelBatch.Output R users samples) ↦
        (pure (directTranscript coefficients offsets keys challenge error) :
          ProbComp (FormalProof4FHE.LWE.ParallelBatch.Transcript
            R dimension users samples))
  change evalDist (challenges >>= fun challenge ↦
      derivedKeySampler users dimension >>= fun keys ↦
      errors >>= fun error ↦ finish challenge keys error) =
    evalDist (challenges >>= fun challenge ↦
      ($ᵗ (BinaryKeys users dimension)) >>= fun keys ↦
      errors >>= fun error ↦ finish challenge keys error)
  refine evalDist_bind_congr' challenges fun challenge ↦ ?_
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (derivedKeySampler_evalDist users dimension)
    (fun keys ↦ errors >>= fun error ↦ finish challenge keys error)

/-- The transformed real master-LWE distribution is exactly the canonical multi-key affine
distribution with independent user keys. -/
theorem real_evalDist {R : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (dimension users samples : ℕ)
    (coefficients : Coefficients R users dimension samples)
    (offsets : Offsets R users samples)
    (errorSampler : ProbComp R) :
    evalDist (LearningWithErrors.distr
          (masterProblem dimension users samples errorSampler) >>= fun transcript ↦
        ($ᵗ (BinaryKeys users dimension)) >>= fun masks ↦
        pure (transformTranscript masks coefficients offsets transcript)) =
      evalDist (LearningWithErrors.distr
        (problem dimension users samples coefficients offsets errorSampler)) := by
  let challenges := challengeSampler (R := R) dimension users samples
  let contexts := masterMaskContextSampler users dimension
  let errors := errorVectorSampler users samples errorSampler
  let embed : BinaryVector dimension → Fin dimension → R :=
    fun key coordinate ↦ embedBit (R := R) (key coordinate)
  let sourceTranscript := fun
      (challenge : FormalProof4FHE.LWE.ParallelBatch.Challenge
        R dimension users samples)
      (master : BinaryVector dimension)
      (error : FormalProof4FHE.LWE.ParallelBatch.Output R users samples) ↦
        FormalProof4FHE.LWE.ParallelBatch.realTranscript embed challenge master error
  let finish := fun
      (context : BinaryVector dimension × BinaryKeys users dimension)
      (challenge : FormalProof4FHE.LWE.ParallelBatch.Challenge
        R dimension users samples) ↦
        errors >>= fun error ↦ pure
          (directTranscript coefficients offsets
            (deriveKeys context.1 context.2) challenge error)
  have hSource :
      evalDist (LearningWithErrors.distr
            (masterProblem dimension users samples errorSampler) >>= fun transcript ↦
          ($ᵗ (BinaryKeys users dimension)) >>= fun masks ↦
          pure (transformTranscript masks coefficients offsets transcript)) =
        evalDist (challenges >>= fun challenge ↦
          contexts >>= fun context ↦
          finish context (transformChallenge context.2 coefficients challenge)) := by
    have hMasterDistr :
        LearningWithErrors.distr
          (masterProblem dimension users samples errorSampler) =
        (challenges >>= fun challenge ↦
          ($ᵗ (BinaryVector dimension)) >>= fun master ↦
          errors >>= fun error ↦
          pure (sourceTranscript challenge master error)) := by
      simp [LearningWithErrors.distr, masterProblem,
        FormalProof4FHE.LWE.ParallelBatch.problem,
        FormalProof4FHE.LWE.ParallelBatch.realTranscript,
        FormalProof4FHE.LWE.ParallelBatch.pointwiseAdd_eq_add,
        challenges, challengeSampler, errors, errorVectorSampler,
        sourceTranscript, embed, monad_norm]
    rw [hMasterDistr]
    simp only [bind_assoc, pure_bind]
    change evalDist (challenges >>= fun challenge ↦
        ($ᵗ (BinaryVector dimension)) >>= fun master ↦
        errors >>= fun error ↦
        ($ᵗ (BinaryKeys users dimension)) >>= fun masks ↦
        pure (transformTranscript masks coefficients offsets
          (sourceTranscript challenge master error))) = _
    calc
      _ = evalDist (challenges >>= fun challenge ↦
          ($ᵗ (BinaryVector dimension)) >>= fun master ↦
          ($ᵗ (BinaryKeys users dimension)) >>= fun masks ↦
          errors >>= fun error ↦
          pure (transformTranscript masks coefficients offsets
            (sourceTranscript challenge master error))) := by
        refine evalDist_bind_congr' challenges fun challenge ↦ ?_
        refine evalDist_bind_congr' ($ᵗ (BinaryVector dimension)) fun master ↦ ?_
        exact evalDist_bind_bind_swap errors ($ᵗ (BinaryKeys users dimension))
          (fun error masks ↦ pure (transformTranscript masks coefficients offsets
            (sourceTranscript challenge master error)))
      _ = _ := by
        simp only [contexts, masterMaskContextSampler, finish, bind_assoc, pure_bind]
        refine evalDist_bind_congr' challenges fun challenge ↦ ?_
        refine evalDist_bind_congr' ($ᵗ (BinaryVector dimension)) fun master ↦ ?_
        refine evalDist_bind_congr' ($ᵗ (BinaryKeys users dimension)) fun masks ↦ ?_
        refine evalDist_bind_congr' errors fun error ↦ ?_
        simpa only [sourceTranscript, embed] using congrArg evalDist
          (congrArg pure
            (transformTranscript_real master masks coefficients offsets challenge error))
  rw [hSource]
  calc
    _ = evalDist (challenges >>= fun challenge ↦
        contexts >>= fun context ↦ finish context challenge) :=
      evalDist_context_transform_of_preserving challenges contexts
        (fun context ↦ transformChallenge context.2 coefficients)
        (fun context ↦ transformChallenge_sampler_evalDist context.2 coefficients)
        finish
    _ = evalDist (LearningWithErrors.distr
        (maskedProblem dimension users samples coefficients offsets errorSampler)) := by
      simp only [LearningWithErrors.distr, maskedProblem]
      change evalDist (challenges >>= fun challenge ↦
          contexts >>= fun context ↦ finish context challenge) =
        evalDist (challenges >>= fun challenge ↦
          derivedKeySampler users dimension >>= fun keys ↦
          errors >>= fun error ↦
          pure (directTranscript coefficients offsets keys challenge error))
      refine evalDist_bind_congr' challenges fun challenge ↦ ?_
      simp [contexts, masterMaskContextSampler, derivedKeySampler, finish,
        bind_assoc, monad_norm]
    _ = _ := maskedProblem_distr_evalDist_eq_problem
      dimension users samples coefficients offsets errorSampler

/-- The multi-key and master problems use the same public uniform transcript sampler. -/
theorem problem_uniformDistr_eq_masterProblem {R : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (dimension users samples : ℕ)
    (coefficients : Coefficients R users dimension samples)
    (offsets : Offsets R users samples)
    (errorSampler : ProbComp R) :
    LearningWithErrors.uniformDistr
        (problem dimension users samples coefficients offsets errorSampler) =
      LearningWithErrors.uniformDistr
        (masterProblem dimension users samples errorSampler) := by
  rfl

/-- A fixed master-mask transcript transformation preserves the complete public uniform branch. -/
theorem transformTranscript_uniform_evalDist {R : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (dimension users samples : ℕ)
    (coefficients : Coefficients R users dimension samples)
    (offsets : Offsets R users samples)
    (errorSampler : ProbComp R)
    (masks : BinaryKeys users dimension) :
    evalDist (transformTranscript masks coefficients offsets <$>
        LearningWithErrors.uniformDistr
          (masterProblem dimension users samples errorSampler)) =
      evalDist (LearningWithErrors.uniformDistr
        (masterProblem dimension users samples errorSampler)) := by
  let uniform : ProbComp
      (FormalProof4FHE.LWE.ParallelBatch.Transcript R dimension users samples) :=
    $ᵗ (FormalProof4FHE.LWE.ParallelBatch.Transcript R dimension users samples)
  have hUniform :
      evalDist (LearningWithErrors.uniformDistr
          (masterProblem dimension users samples errorSampler)) =
        evalDist uniform := by
    simpa only [masterProblem] using
      (FormalProof4FHE.LWE.ParallelBatch.uniformDistr_evalDist_eq_uniformSample
        dimension users samples ($ᵗ (BinaryVector dimension))
        (fun key coordinate ↦ embedBit (R := R) (key coordinate)) errorSampler)
  calc
    _ = evalDist (transformTranscript masks coefficients offsets <$> uniform) := by
      simpa only [evalDist_map] using congrArg
        (fun distribution ↦ transformTranscript masks coefficients offsets <$> distribution)
        hUniform
    _ = evalDist uniform :=
      evalDist_map_bijective_uniform_cross
        (α := FormalProof4FHE.LWE.ParallelBatch.Transcript
          R dimension users samples)
        (β := FormalProof4FHE.LWE.ParallelBatch.Transcript
          R dimension users samples)
        (transformTranscript masks coefficients offsets)
        (transformTranscript_bijective masks coefficients offsets)
    _ = _ := hUniform.symm

/-- Sampling masks and transforming the master uniform branch still gives the canonical
multi-key uniform branch. -/
theorem uniform_evalDist {R : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (dimension users samples : ℕ)
    (coefficients : Coefficients R users dimension samples)
    (offsets : Offsets R users samples)
    (errorSampler : ProbComp R) :
    evalDist (LearningWithErrors.uniformDistr
          (masterProblem dimension users samples errorSampler) >>= fun transcript ↦
        ($ᵗ (BinaryKeys users dimension)) >>= fun masks ↦
        pure (transformTranscript masks coefficients offsets transcript)) =
      evalDist (LearningWithErrors.uniformDistr
        (problem dimension users samples coefficients offsets errorSampler)) := by
  let source := LearningWithErrors.uniformDistr
    (masterProblem dimension users samples errorSampler)
  let masksSampler : ProbComp (BinaryKeys users dimension) :=
    $ᵗ (BinaryKeys users dimension)
  calc
    _ = evalDist (source >>= fun transcript ↦
        masksSampler >>= fun _ ↦ pure transcript) :=
      evalDist_context_transform_of_preserving source masksSampler
        (fun masks ↦ transformTranscript masks coefficients offsets)
        (fun masks ↦ transformTranscript_uniform_evalDist
          dimension users samples coefficients offsets errorSampler masks)
        (fun _ transcript ↦ pure transcript)
    _ = evalDist (source >>= fun transcript ↦ pure transcript) := by
      refine evalDist_bind_congr' source fun transcript ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        masksSampler (by simp [masksSampler]) (pure transcript)
    _ = evalDist source := by simp [monad_norm]
    _ = _ := by
      rw [problem_uniformDistr_eq_masterProblem
        dimension users samples coefficients offsets errorSampler]

/-- Reduction from a direct multi-key affine distinguisher to ordinary master-key LWE. -/
noncomputable def reduction {R : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    {dimension users samples : ℕ}
    {coefficients : Coefficients R users dimension samples}
    {offsets : Offsets R users samples}
    {errorSampler : ProbComp R}
    (adversary : LearningWithErrors.Adversary
      (problem dimension users samples coefficients offsets errorSampler)) :
    LearningWithErrors.Adversary
      (masterProblem dimension users samples errorSampler) :=
  fun transcript ↦ do
    let masks ← $ᵗ (BinaryKeys users dimension)
    adversary (transformTranscript masks coefficients offsets transcript)

/-- Exact real-game equality for the multi-key affine reduction. -/
theorem game0_evalDist_eq {R : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (dimension users samples : ℕ)
    (coefficients : Coefficients R users dimension samples)
    (offsets : Offsets R users samples)
    (errorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem dimension users samples coefficients offsets errorSampler)) :
    evalDist (LearningWithErrors.game0
        (problem dimension users samples coefficients offsets errorSampler) adversary) =
      evalDist (LearningWithErrors.game0
        (masterProblem dimension users samples errorSampler) (reduction adversary)) := by
  rw [LearningWithErrors.game0, LearningWithErrors.game0]
  simp only [reduction]
  rw [show (LearningWithErrors.distr
          (masterProblem dimension users samples errorSampler) >>= fun transcript ↦
        ($ᵗ (BinaryKeys users dimension)) >>= fun masks ↦
        adversary (transformTranscript masks coefficients offsets transcript)) =
      ((LearningWithErrors.distr
            (masterProblem dimension users samples errorSampler) >>= fun transcript ↦
          ($ᵗ (BinaryKeys users dimension)) >>= fun masks ↦
          pure (transformTranscript masks coefficients offsets transcript)) >>= adversary) by
        simp only [bind_assoc, pure_bind],
    evalDist_bind, evalDist_bind,
    real_evalDist dimension users samples coefficients offsets errorSampler]

/-- Exact uniform-game equality for the multi-key affine reduction. -/
theorem game1_evalDist_eq {R : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (dimension users samples : ℕ)
    (coefficients : Coefficients R users dimension samples)
    (offsets : Offsets R users samples)
    (errorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem dimension users samples coefficients offsets errorSampler)) :
    evalDist (LearningWithErrors.game1
        (problem dimension users samples coefficients offsets errorSampler) adversary) =
      evalDist (LearningWithErrors.game1
        (masterProblem dimension users samples errorSampler) (reduction adversary)) := by
  rw [LearningWithErrors.game1, LearningWithErrors.game1]
  simp only [reduction]
  rw [show (LearningWithErrors.uniformDistr
          (masterProblem dimension users samples errorSampler) >>= fun transcript ↦
        ($ᵗ (BinaryKeys users dimension)) >>= fun masks ↦
        adversary (transformTranscript masks coefficients offsets transcript)) =
      ((LearningWithErrors.uniformDistr
            (masterProblem dimension users samples errorSampler) >>= fun transcript ↦
          ($ᵗ (BinaryKeys users dimension)) >>= fun masks ↦
          pure (transformTranscript masks coefficients offsets transcript)) >>= adversary) by
        simp only [bind_assoc, pure_bind],
    evalDist_bind, evalDist_bind,
    uniform_evalDist dimension users samples coefficients offsets errorSampler]

/-- The direct multi-key affine advantage is exactly one ordinary parallel master-LWE
advantage. -/
theorem advantage_eq_master {R : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (dimension users samples : ℕ)
    (coefficients : Coefficients R users dimension samples)
    (offsets : Offsets R users samples)
    (errorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem dimension users samples coefficients offsets errorSampler)) :
    LearningWithErrors.advantage
        (problem dimension users samples coefficients offsets errorSampler) adversary =
      LearningWithErrors.advantage
        (masterProblem dimension users samples errorSampler) (reduction adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage,
    FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (game0_evalDist_eq dimension users samples coefficients offsets errorSampler adversary) true,
    evalDist_ext_iff.mp
      (game1_evalDist_eq dimension users samples coefficients offsets errorSampler adversary) true]

/-- The composed reduction to one conventional batch of `users * samples` rows. -/
noncomputable def batchReduction {R : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    {dimension users samples : ℕ}
    {coefficients : Coefficients R users dimension samples}
    {offsets : Offsets R users samples}
    {errorSampler : ProbComp R}
    (adversary : LearningWithErrors.Adversary
      (problem dimension users samples coefficients offsets errorSampler)) :
    LearningWithErrors.Adversary
      (FormalProof4FHE.LWE.embeddedBatchProblem dimension (users * samples)
        ($ᵗ (BinaryVector dimension))
        (fun key coordinate ↦ embedBit (R := R) (key coordinate)) errorSampler) :=
  FormalProof4FHE.LWE.ParallelBatch.reduction (reduction adversary)

/-- **Exact direct affine clique/circular-security theorem.** A fixed family of fresh LWE rows
under `users` independent binary target keys, carrying arbitrary affine functions of all `users`
keys, has exactly the advantage of one ordinary binary-secret batch-LWE adversary on
`users * samples` rows. -/
theorem advantage_eq_batch {R : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (dimension users samples : ℕ)
    (coefficients : Coefficients R users dimension samples)
    (offsets : Offsets R users samples)
    (errorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem dimension users samples coefficients offsets errorSampler)) :
    LearningWithErrors.advantage
        (problem dimension users samples coefficients offsets errorSampler) adversary =
      LearningWithErrors.advantage
        (FormalProof4FHE.LWE.embeddedBatchProblem dimension (users * samples)
          ($ᵗ (BinaryVector dimension))
          (fun key coordinate ↦ embedBit (R := R) (key coordinate)) errorSampler)
        (batchReduction adversary) := by
  rw [advantage_eq_master dimension users samples coefficients offsets errorSampler adversary]
  exact FormalProof4FHE.LWE.ParallelBatch.advantage_eq_batch
    dimension users samples ($ᵗ (BinaryVector dimension))
    (fun key coordinate ↦ embedBit (R := R) (key coordinate)) errorSampler
    (reduction adversary)

/-- Hardness of the ordinary combined batch transfers to the entire direct affine multi-key
family for any reduction-closed adversary classes. -/
theorem hardAgainst_of_batch {R : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (dimension users samples : ℕ)
    (coefficients : Coefficients R users dimension samples)
    (offsets : Offsets R users samples)
    (errorSampler : ProbComp R)
    (allowed : LearningWithErrors.Adversary
      (problem dimension users samples coefficients offsets errorSampler) → Prop)
    (batchAllowed : LearningWithErrors.Adversary
      (FormalProof4FHE.LWE.embeddedBatchProblem dimension (users * samples)
        ($ᵗ (BinaryVector dimension))
        (fun key coordinate ↦ embedBit (R := R) (key coordinate)) errorSampler) → Prop)
    (bound : ℝ)
    (hClosed : ∀ adversary, allowed adversary → batchAllowed (batchReduction adversary))
    (hBatch : FormalProof4FHE.LWE.HardAgainst
      (FormalProof4FHE.LWE.embeddedBatchProblem dimension (users * samples)
        ($ᵗ (BinaryVector dimension))
        (fun key coordinate ↦ embedBit (R := R) (key coordinate)) errorSampler)
      batchAllowed bound) :
    FormalProof4FHE.LWE.HardAgainst
      (problem dimension users samples coefficients offsets errorSampler) allowed bound := by
  intro adversary hadversary
  rw [advantage_eq_batch dimension users samples coefficients offsets errorSampler adversary]
  exact hBatch _ (hClosed adversary hadversary)

end FormalProof4FHE.LWE.MultiKeyAffine
