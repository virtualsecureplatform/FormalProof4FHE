/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.SharedRandomness.Basic

/-!
# Reduction from Shared-Randomness LWE to Ordinary LWE

This module formalizes the reduction in Theorem 6 of
Bergerat--Chillotti--Ligier--Orfila--Roux-Langlois--Tap.  Its ordinary-LWE input is represented as
two blocks of `m` samples sharing one length-`n` secret; this is the matrix form of `2m` ordinary
LWE samples.

The reduction uses the first block to create the noisier short-secret samples by adding an
independent error vector.  It uses the second block to create the long-secret samples by sampling
the missing rows and secret suffix.
-/

open Matrix OracleComp

namespace FormalProof4FHE.SharedRandomness

/-- Two blocks of ordinary LWE challenge matrices, sharing one secret. -/
abbrev TwoBatchChallenge (R : Type) (n m : ℕ) :=
  Matrix (Fin n) (Fin m) R × Matrix (Fin n) (Fin m) R

/-- Two blocks of ordinary LWE right-hand sides. -/
abbrev TwoBatchOutput (R : Type) (m : ℕ) :=
  (Fin m → R) × (Fin m → R)

/-- A public transcript containing two ordinary-LWE blocks. -/
abbrev TwoBatchTranscript (R : Type) (n m : ℕ) :=
  TwoBatchChallenge R n m × TwoBatchOutput R m

/-- Ordinary LWE presented as two independent `m`-sample blocks under the same secret. -/
def twoBatchProblem {R : Type} [Semiring R] [DecidableEq R] [SampleableType R]
    (n m : ℕ) (secretSampler : ProbComp (Fin n → R))
    (errorSampler : ProbComp R) :
    LearningWithErrors.Problem
      (TwoBatchChallenge R n m) (Fin n → R) (TwoBatchOutput R m) where
  sampleChallenge := $ᵗ (TwoBatchChallenge R n m)
  sampleSecret := secretSampler
  sampleError := do
    let firstError ← ProbComp.sampleIID m errorSampler
    let secondError ← ProbComp.sampleIID m errorSampler
    return (firstError, secondError)
  noiseless := fun secret challenge ↦
    (vecMul secret challenge.1, vecMul secret challenge.2)
  sampleUniform := $ᵗ (TwoBatchOutput R m)

/-- The two-block ordinary-LWE source problem over `ZMod q` with a uniform secret. -/
def zmodTwoBatchProblem (n m q : ℕ) [NeZero q]
    (errorSampler : ProbComp (ZMod q)) :
    LearningWithErrors.Problem
      (TwoBatchChallenge (ZMod q) n m) (Fin n → ZMod q)
      (TwoBatchOutput (ZMod q) m) :=
  twoBatchProblem n m ($ᵗ (Fin n → ZMod q)) errorSampler

/-- The randomized transcript transformation used in the shared-randomness reduction. -/
def liftTranscript {R : Type} [Semiring R] [SampleableType R]
    (k m : ℕ)
    (suffixSampler : ProbComp (Fin k → R))
    (extraErrorSampler : ProbComp R)
    {n : ℕ} (sample : TwoBatchTranscript R n m) :
    ProbComp (Transcript R n k m) := do
  let extraRows ← $ᵗ Matrix (Fin k) (Fin m) R
  let suffix ← suffixSampler
  let extraError ← ProbComp.sampleIID m extraErrorSampler
  return ((sample.1.1, appendRows sample.1.2 extraRows),
      (sample.2.1 + extraError, sample.2.2 + vecMul suffix extraRows))

/-- The deterministic part of `liftTranscript`, after all its randomness has been exposed. -/
def assembleTranscript {R : Type} [Semiring R] {n k m : ℕ}
    (extraError : Fin m → R) (suffix : Fin k → R)
    (randomness : TwoBatchTranscript R n m × Matrix (Fin k) (Fin m) R) :
    Transcript R n k m :=
  ((randomness.1.1.1, appendRows randomness.1.1.2 randomness.2),
    (randomness.1.2.1 + extraError,
      randomness.1.2.2 + vecMul suffix randomness.2))

/-- Inverse of `assembleTranscript` when the coefficient type is an additive group. -/
def disassembleTranscript {R : Type} [Ring R] {n k m : ℕ}
    (extraError : Fin m → R) (suffix : Fin k → R)
    (transcript : Transcript R n k m) :
    TwoBatchTranscript R n m × Matrix (Fin k) (Fin m) R :=
  let blocks := splitRows transcript.1.2
  (((transcript.1.1, blocks.1),
      (transcript.2.1 - extraError,
        transcript.2.2 - vecMul suffix blocks.2)),
    blocks.2)

@[simp]
theorem disassemble_assemble {R : Type} [Ring R] {n k m : ℕ}
    (extraError : Fin m → R) (suffix : Fin k → R)
    (randomness : TwoBatchTranscript R n m × Matrix (Fin k) (Fin m) R) :
    disassembleTranscript extraError suffix
        (assembleTranscript extraError suffix randomness) = randomness := by
  rcases randomness with ⟨⟨⟨firstMatrix, secondMatrix⟩, firstOutput, secondOutput⟩, extraRows⟩
  simp [assembleTranscript, disassembleTranscript]

@[simp]
theorem assemble_disassemble {R : Type} [Ring R] {n k m : ℕ}
    (extraError : Fin m → R) (suffix : Fin k → R)
    (transcript : Transcript R n k m) :
    assembleTranscript extraError suffix
        (disassembleTranscript extraError suffix transcript) = transcript := by
  rcases transcript with ⟨⟨firstMatrix, largeMatrix⟩, firstOutput, secondOutput⟩
  simp [assembleTranscript, disassembleTranscript]

/-- For fixed added error and secret suffix, transcript assembly is a bijection. -/
theorem assembleTranscript_bijective {R : Type} [Ring R] {n k m : ℕ}
    (extraError : Fin m → R) (suffix : Fin k → R) :
    Function.Bijective (assembleTranscript (n := n) extraError suffix) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨disassembleTranscript extraError suffix, ?_, ?_⟩
  · exact disassemble_assemble extraError suffix
  · exact assemble_disassemble extraError suffix

/-- Independent uniform source data and extra rows assemble to a uniform target transcript. -/
theorem assemble_uniform_evalDist {R : Type} [Ring R] [Finite R] [SampleableType R]
    {n k m : ℕ} (extraError : Fin m → R) (suffix : Fin k → R) :
    𝒟[do
      let source ← $ᵗ (TwoBatchTranscript R n m)
      let extraRows ← $ᵗ Matrix (Fin k) (Fin m) R
      return assembleTranscript extraError suffix (source, extraRows)] =
    𝒟[$ᵗ (Transcript R n k m)] := by
  have uniformProduct :
      ($ᵗ (TwoBatchTranscript R n m × Matrix (Fin k) (Fin m) R) :
        ProbComp (TwoBatchTranscript R n m × Matrix (Fin k) (Fin m) R)) =
      Prod.mk <$> ($ᵗ (TwoBatchTranscript R n m)) <*>
        ($ᵗ Matrix (Fin k) (Fin m) R) := rfl
  rw [show (do
      let source ← $ᵗ (TwoBatchTranscript R n m)
      let extraRows ← $ᵗ Matrix (Fin k) (Fin m) R
      return assembleTranscript extraError suffix (source, extraRows)) =
      assembleTranscript extraError suffix <$>
        ($ᵗ (TwoBatchTranscript R n m × Matrix (Fin k) (Fin m) R)) by
    rw [uniformProduct]
    simp [monad_norm]]
  exact evalDist_map_bijective_uniform_cross
    (α := TwoBatchTranscript R n m × Matrix (Fin k) (Fin m) R)
    (β := Transcript R n k m)
    (assembleTranscript extraError suffix)
    (assembleTranscript_bijective extraError suffix)

/-- The uniform branch of a two-block LWE problem is the canonical uniform transcript sampler. -/
theorem twoBatch_uniformDistr_eq_uniformSample {R : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (n m : ℕ) (secretSampler : ProbComp (Fin n → R)) (errorSampler : ProbComp R) :
    LearningWithErrors.uniformDistr
        (twoBatchProblem n m secretSampler errorSampler) =
      ($ᵗ (TwoBatchTranscript R n m)) := by
  unfold LearningWithErrors.uniformDistr twoBatchProblem
  have uniformProduct :
      ($ᵗ (TwoBatchTranscript R n m) : ProbComp (TwoBatchTranscript R n m)) =
      Prod.mk <$> ($ᵗ (TwoBatchChallenge R n m)) <*>
        ($ᵗ (TwoBatchOutput R m)) := rfl
  rw [uniformProduct]
  simp [monad_norm]

/-- The uniform branch of shared-randomness LWE is its canonical uniform transcript sampler. -/
theorem problem_uniformDistr_eq_uniformSample {R : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (n k m : ℕ)
    (prefixSampler : ProbComp (Fin n → R))
    (suffixSampler : ProbComp (Fin k → R))
    (smallErrorSampler largeErrorSampler : ProbComp R) :
    LearningWithErrors.uniformDistr
        (problem n k m prefixSampler suffixSampler smallErrorSampler largeErrorSampler) =
      ($ᵗ (Transcript R n k m)) := by
  unfold LearningWithErrors.uniformDistr problem
  have uniformProduct :
      ($ᵗ (Transcript R n k m) : ProbComp (Transcript R n k m)) =
      Prod.mk <$> ($ᵗ (Challenge R n k m)) <*> ($ᵗ (Output R m)) := rfl
  rw [uniformProduct]
  simp [monad_norm]

/-- A never-failing, value-irrelevant probabilistic prefix can be dropped. -/
theorem evalDist_bind_const_of_probFailure_eq_zero {α β : Type}
    (sampler : ProbComp α) (hSampler : Pr[⊥ | sampler] = 0)
    (continuation : ProbComp β) :
    𝒟[sampler >>= fun _ ↦ continuation] = 𝒟[continuation] := by
  refine evalDist_ext fun output ↦ ?_
  rw [probOutput_bind_const, hSampler]
  simp

/-- The transcript transformation maps the source uniform branch exactly to the
shared-randomness uniform branch. -/
theorem uniform_branch_evalDist_eq {R : Type}
    [Ring R] [Finite R] [DecidableEq R] [SampleableType R]
    (n k m : ℕ)
    (prefixSampler : ProbComp (Fin n → R))
    (suffixSampler : ProbComp (Fin k → R))
    (smallErrorSampler largeErrorSampler extraErrorSampler : ProbComp R)
    (hSuffix : Pr[⊥ | suffixSampler] = 0)
    (hExtraError : Pr[⊥ | ProbComp.sampleIID m extraErrorSampler] = 0) :
    𝒟[LearningWithErrors.uniformDistr
          (twoBatchProblem n m prefixSampler largeErrorSampler) >>=
        liftTranscript k m suffixSampler extraErrorSampler] =
      𝒟[LearningWithErrors.uniformDistr
        (problem n k m prefixSampler suffixSampler smallErrorSampler largeErrorSampler)] := by
  rw [twoBatch_uniformDistr_eq_uniformSample,
    problem_uniformDistr_eq_uniformSample]
  change
    𝒟[(($ᵗ (TwoBatchTranscript R n m)) >>= fun source ↦
      ($ᵗ Matrix (Fin k) (Fin m) R) >>= fun extraRows ↦
      suffixSampler >>= fun suffix ↦
      ProbComp.sampleIID m extraErrorSampler >>= fun extraError ↦
      pure (assembleTranscript extraError suffix (source, extraRows)))] =
    𝒟[$ᵗ (Transcript R n k m)]
  let uniformRandomness :
      ProbComp (TwoBatchTranscript R n m × Matrix (Fin k) (Fin m) R) := do
    let source ← $ᵗ (TwoBatchTranscript R n m)
    let extraRows ← $ᵗ Matrix (Fin k) (Fin m) R
    return (source, extraRows)
  calc
    _ = 𝒟[uniformRandomness >>= fun randomness ↦
          suffixSampler >>= fun suffix ↦
          ProbComp.sampleIID m extraErrorSampler >>= fun extraError ↦
          pure (assembleTranscript extraError suffix randomness)] := by
      congr 1
      simp [uniformRandomness, bind_assoc, monad_norm]
    _ = 𝒟[suffixSampler >>= fun suffix ↦
          uniformRandomness >>= fun randomness ↦
          ProbComp.sampleIID m extraErrorSampler >>= fun extraError ↦
          pure (assembleTranscript extraError suffix randomness)] :=
      evalDist_bind_bind_swap uniformRandomness suffixSampler _
    _ = 𝒟[suffixSampler >>= fun suffix ↦
          ProbComp.sampleIID m extraErrorSampler >>= fun extraError ↦
          uniformRandomness >>= fun randomness ↦
          pure (assembleTranscript extraError suffix randomness)] := by
      refine evalDist_bind_congr' suffixSampler fun suffix ↦ ?_
      exact evalDist_bind_bind_swap uniformRandomness
        (ProbComp.sampleIID m extraErrorSampler) _
    _ = 𝒟[suffixSampler >>= fun _ ↦
          ProbComp.sampleIID m extraErrorSampler >>= fun _ ↦
          ($ᵗ (Transcript R n k m))] := by
      refine evalDist_bind_congr' suffixSampler fun suffix ↦ ?_
      refine evalDist_bind_congr' (ProbComp.sampleIID m extraErrorSampler) fun extraError ↦ ?_
      simpa only [uniformRandomness, bind_assoc, pure_bind] using
        (assemble_uniform_evalDist extraError suffix)
    _ = 𝒟[suffixSampler >>= fun _ ↦ ($ᵗ (Transcript R n k m))] := by
      refine evalDist_bind_congr' suffixSampler fun _ ↦ ?_
      exact evalDist_bind_const_of_probFailure_eq_zero
        (ProbComp.sampleIID m extraErrorSampler) hExtraError _
    _ = _ := evalDist_bind_const_of_probFailure_eq_zero suffixSampler hSuffix _

/-- The real distribution produced by the reduction, with every independent draw made explicit. -/
def reducedRealDistr {R : Type} [Semiring R] [SampleableType R]
    (n k m : ℕ)
    (prefixSampler : ProbComp (Fin n → R))
    (suffixSampler : ProbComp (Fin k → R))
    (largeErrorSampler extraErrorSampler : ProbComp R) :
    ProbComp (Transcript R n k m) := do
  let challenge ← $ᵗ (TwoBatchChallenge R n m)
  let head ← prefixSampler
  let firstError ← ProbComp.sampleIID m largeErrorSampler
  let secondError ← ProbComp.sampleIID m largeErrorSampler
  let extraRows ← $ᵗ Matrix (Fin k) (Fin m) R
  let suffix ← suffixSampler
  let extraError ← ProbComp.sampleIID m extraErrorSampler
  return ((challenge.1, appendRows challenge.2 extraRows),
      (vecMul head challenge.1 + (firstError + extraError),
        vecMul (Fin.append head suffix) (appendRows challenge.2 extraRows) + secondError))

/-- On the real branch, the source LWE samples followed by `liftTranscript` are exactly the
explicit reduced real distribution. -/
theorem source_real_branch_evalDist_eq_reduced {R : Type}
    [CommSemiring R] [DecidableEq R] [SampleableType R]
    (n k m : ℕ)
    (prefixSampler : ProbComp (Fin n → R))
    (suffixSampler : ProbComp (Fin k → R))
    (largeErrorSampler extraErrorSampler : ProbComp R) :
    𝒟[LearningWithErrors.distr
          (twoBatchProblem n m prefixSampler largeErrorSampler) >>=
        liftTranscript k m suffixSampler extraErrorSampler] =
      𝒟[reducedRealDistr n k m prefixSampler suffixSampler
        largeErrorSampler extraErrorSampler] := by
  congr 1
  simp [LearningWithErrors.distr, twoBatchProblem, liftTranscript, reducedRealDistr,
    vecMul_appendRows, monad_norm, add_comm, add_left_comm]

/-- Assemble the two source challenge matrices and the new rows into a shared-randomness
challenge. -/
def assembleChallenge {R : Type} {n k m : ℕ}
    (randomness : TwoBatchChallenge R n m × Matrix (Fin k) (Fin m) R) :
    Challenge R n k m :=
  (randomness.1.1, appendRows randomness.1.2 randomness.2)

/-- Inverse of `assembleChallenge`. -/
def disassembleChallenge {R : Type} {n k m : ℕ}
    (challenge : Challenge R n k m) :
    TwoBatchChallenge R n m × Matrix (Fin k) (Fin m) R :=
  let blocks := splitRows challenge.2
  ((challenge.1, blocks.1), blocks.2)

@[simp]
theorem disassemble_assembleChallenge {R : Type} {n k m : ℕ}
    (randomness : TwoBatchChallenge R n m × Matrix (Fin k) (Fin m) R) :
    disassembleChallenge (assembleChallenge randomness) = randomness := by
  rcases randomness with ⟨⟨smallMatrix, secondMatrix⟩, extraRows⟩
  simp [assembleChallenge, disassembleChallenge]

@[simp]
theorem assemble_disassembleChallenge {R : Type} {n k m : ℕ}
    (challenge : Challenge R n k m) :
    assembleChallenge (disassembleChallenge challenge) = challenge := by
  rcases challenge with ⟨smallMatrix, largeMatrix⟩
  simp [assembleChallenge, disassembleChallenge]

/-- Challenge assembly is a bijection. -/
theorem assembleChallenge_bijective {R : Type} {n k m : ℕ} :
    Function.Bijective (assembleChallenge (R := R) (n := n) (k := k) (m := m)) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨disassembleChallenge, ?_, ?_⟩
  · exact disassemble_assembleChallenge
  · exact assemble_disassembleChallenge

/-- Sampling the two source matrices and the extra rows produces a uniform shared-randomness
challenge. -/
theorem assembledChallenge_uniform_evalDist {R : Type}
    [Finite R] [SampleableType R] {n k m : ℕ} :
    𝒟[do
      let sourceChallenge ← $ᵗ (TwoBatchChallenge R n m)
      let extraRows ← $ᵗ Matrix (Fin k) (Fin m) R
      return assembleChallenge (sourceChallenge, extraRows)] =
      𝒟[$ᵗ (Challenge R n k m)] := by
  have uniformProduct :
      ($ᵗ (TwoBatchChallenge R n m × Matrix (Fin k) (Fin m) R) :
        ProbComp (TwoBatchChallenge R n m × Matrix (Fin k) (Fin m) R)) =
      Prod.mk <$> ($ᵗ (TwoBatchChallenge R n m)) <*>
        ($ᵗ Matrix (Fin k) (Fin m) R) := rfl
  rw [show (do
      let sourceChallenge ← $ᵗ (TwoBatchChallenge R n m)
      let extraRows ← $ᵗ Matrix (Fin k) (Fin m) R
      return assembleChallenge (sourceChallenge, extraRows)) =
      assembleChallenge <$>
        ($ᵗ (TwoBatchChallenge R n m × Matrix (Fin k) (Fin m) R)) by
    rw [uniformProduct]
    simp [monad_norm]]
  exact evalDist_map_bijective_uniform_cross
    (α := TwoBatchChallenge R n m × Matrix (Fin k) (Fin m) R)
    (β := Challenge R n k m)
    assembleChallenge assembleChallenge_bijective

/-- Two independent vectors drawn from the large-secret error distribution. -/
def pairedErrorSampler {R : Type} (m : ℕ) (largeErrorSampler : ProbComp R) :
    ProbComp (Output R m) := do
  let firstError ← ProbComp.sampleIID m largeErrorSampler
  let secondError ← ProbComp.sampleIID m largeErrorSampler
  return (firstError, secondError)

/-- Add an independent widening error to the first of two large-secret error vectors. -/
def widenedErrorSampler {R : Type} [Add R] (m : ℕ)
    (largeErrorSampler extraErrorSampler : ProbComp R) :
    ProbComp (Output R m) := do
  let errors ← pairedErrorSampler m largeErrorSampler
  let extraError ← ProbComp.sampleIID m extraErrorSampler
  return (errors.1 + extraError, errors.2)

/-- The scalar convolution condition from Theorem 6, stated after IID lifting to `m` coordinates. -/
def VectorErrorConvolution {R : Type} [Add R] (m : ℕ)
    (smallErrorSampler largeErrorSampler extraErrorSampler : ProbComp R) : Prop :=
  𝒟[do
    let largeError ← ProbComp.sampleIID m largeErrorSampler
    let extraError ← ProbComp.sampleIID m extraErrorSampler
    return largeError + extraError] =
    𝒟[ProbComp.sampleIID m smallErrorSampler]

/-- Under the convolution condition, widening the first large-error vector gives exactly the
small-error/large-error pair used by shared-randomness LWE. -/
theorem widenedErrorSampler_evalDist_eq {R : Type} [AddCommMonoid R]
    (m : ℕ) (smallErrorSampler largeErrorSampler extraErrorSampler : ProbComp R)
    (hConvolution : VectorErrorConvolution m smallErrorSampler
      largeErrorSampler extraErrorSampler) :
    𝒟[widenedErrorSampler m largeErrorSampler extraErrorSampler] =
      𝒟[do
        let smallError ← ProbComp.sampleIID m smallErrorSampler
        let largeError ← ProbComp.sampleIID m largeErrorSampler
        return (smallError, largeError)] := by
  unfold widenedErrorSampler pairedErrorSampler VectorErrorConvolution at *
  calc
    _ = 𝒟[do
        let firstError ← ProbComp.sampleIID m largeErrorSampler
        let secondError ← ProbComp.sampleIID m largeErrorSampler
        let extraError ← ProbComp.sampleIID m extraErrorSampler
        return (firstError + extraError, secondError)] := by
      congr 1
      simp [bind_assoc, monad_norm]
    _ = 𝒟[do
        let firstError ← ProbComp.sampleIID m largeErrorSampler
        let extraError ← ProbComp.sampleIID m extraErrorSampler
        let secondError ← ProbComp.sampleIID m largeErrorSampler
        return (firstError + extraError, secondError)] := by
      refine evalDist_bind_congr' (ProbComp.sampleIID m largeErrorSampler) fun firstError ↦ ?_
      exact evalDist_bind_bind_swap
        (ProbComp.sampleIID m largeErrorSampler)
        (ProbComp.sampleIID m extraErrorSampler) _
    _ = 𝒟[(do
          let firstError ← ProbComp.sampleIID m largeErrorSampler
          let extraError ← ProbComp.sampleIID m extraErrorSampler
          return firstError + extraError) >>= fun smallError ↦
        ProbComp.sampleIID m largeErrorSampler >>= fun largeError ↦
        pure (smallError, largeError)] := by
      congr 1
      simp [bind_assoc, monad_norm]
    _ = _ := by
      let combined : ProbComp (Fin m → R) := do
        let firstError ← ProbComp.sampleIID m largeErrorSampler
        let extraError ← ProbComp.sampleIID m extraErrorSampler
        return firstError + extraError
      let continuation (smallError : Fin m → R) : ProbComp (Output R m) := do
        let largeError ← ProbComp.sampleIID m largeErrorSampler
        return (smallError, largeError)
      change 𝒟[combined >>= continuation] =
        𝒟[ProbComp.sampleIID m smallErrorSampler >>= continuation]
      calc
        _ = 𝒟[combined] >>= fun smallError ↦ 𝒟[continuation smallError] :=
          evalDist_bind combined continuation
        _ = 𝒟[ProbComp.sampleIID m smallErrorSampler] >>=
              fun smallError ↦ 𝒟[continuation smallError] := by
          rw [show 𝒟[combined] = 𝒟[ProbComp.sampleIID m smallErrorSampler] by
            simpa only [combined] using hConvolution]
        _ = _ := (evalDist_bind (ProbComp.sampleIID m smallErrorSampler) continuation).symm

/-- Replacing a sampler by a distributionally equal sampler preserves every continuation. -/
theorem evalDist_bind_eq_of_evalDist_eq {α β : Type}
    {first second : ProbComp α} (h : 𝒟[first] = 𝒟[second])
    (continuation : α → ProbComp β) :
    𝒟[first >>= continuation] = 𝒟[second >>= continuation] := by
  rw [evalDist_bind, evalDist_bind, h]

/-- IID sampling preserves equality of the one-coordinate evaluation distributions. -/
theorem sampleIID_evalDist_congr {R : Type} (m : ℕ)
    {first second : ProbComp R} (h : 𝒟[first] = 𝒟[second]) :
    𝒟[ProbComp.sampleIID m first] = 𝒟[ProbComp.sampleIID m second] := by
  induction m with
  | zero => simp [ProbComp.sampleIID, Fin.mOfFn]
  | succ m ih =>
      let firstTail := ProbComp.sampleIID m first
      let secondTail := ProbComp.sampleIID m second
      change 𝒟[first >>= fun head ↦
          firstTail >>= fun tail ↦
            pure (Fin.cons (α := fun _ ↦ R) head tail)] =
        𝒟[second >>= fun head ↦
          secondTail >>= fun tail ↦
            pure (Fin.cons (α := fun _ ↦ R) head tail)]
      calc
        _ = 𝒟[second >>= fun head ↦
            firstTail >>= fun tail ↦
              pure (Fin.cons (α := fun _ ↦ R) head tail)] :=
          evalDist_bind_eq_of_evalDist_eq h _
        _ = _ := by
          refine evalDist_bind_congr' second fun head ↦ ?_
          exact evalDist_bind_eq_of_evalDist_eq
            (by simpa only [firstTail, secondTail] using ih) _

/-- IID repetition of a never-failing scalar sampler is never failing. -/
theorem probFailure_sampleIID_eq_zero {R : Type} (m : ℕ) (sampler : ProbComp R)
    (hSampler : Pr[⊥ | sampler] = 0) :
    Pr[⊥ | ProbComp.sampleIID m sampler] = 0 := by
  induction m with
  | zero => simp [ProbComp.sampleIID, Fin.mOfFn]
  | succ m ih =>
      simp only [ProbComp.sampleIID, Fin.mOfFn]
      have headNeverFails : NeverFail sampler :=
        NeverFail.of_probFailure_eq_zero sampler hSampler
      have tailNeverFails : NeverFail (Fin.mOfFn m fun _ ↦ sampler) :=
        NeverFail.of_probFailure_eq_zero _ (by simpa only [ProbComp.sampleIID] using ih)
      have allNeverFail : NeverFail (do
          let head ← sampler
          let tail ← Fin.mOfFn m fun _ ↦ sampler
          pure (Fin.cons (α := fun _ ↦ R) head tail)) := by
        apply NeverFail.bind_of_forall (hx := headNeverFails)
      exact allNeverFail.probFailure_eq_zero

/-- Sampling two IID vectors in blocks and adding them has the same distribution as sampling
their coordinatewise convolution independently. -/
theorem sampleIID_add_evalDist {R : Type} [Add R] (m : ℕ)
    (first second : ProbComp R) :
    𝒟[do
      let firstVector ← ProbComp.sampleIID m first
      let secondVector ← ProbComp.sampleIID m second
      return firstVector + secondVector] =
    𝒟[ProbComp.sampleIID m (do
      let x ← first
      let y ← second
      return x + y)] := by
  induction m with
  | zero =>
      have empty_eq : (![] : Fin 0 → R) = Fin.elim0 := by
        funext i
        exact i.elim0
      simp [ProbComp.sampleIID, Fin.mOfFn, empty_eq]
  | succ m ih =>
      let firstTail := ProbComp.sampleIID m first
      let secondTail := ProbComp.sampleIID m second
      let coordinate : ProbComp R := do
        let x ← first
        let y ← second
        return x + y
      let tailSum : ProbComp (Fin m → R) := do
        let xs ← firstTail
        let ys ← secondTail
        return xs + ys
      have cons_add (x y : R) (xs ys : Fin m → R) :
          Fin.cons (α := fun _ ↦ R) x xs + Fin.cons (α := fun _ ↦ R) y ys =
            Fin.cons (α := fun _ ↦ R) (x + y) (xs + ys) := by
        funext i
        refine Fin.cases ?_ (fun j ↦ ?_) i <;> simp
      simp only [ProbComp.sampleIID, Fin.mOfFn]
      simp only [bind_assoc, pure_bind]
      change 𝒟[first >>= fun x ↦
          firstTail >>= fun xs ↦
          second >>= fun y ↦
          secondTail >>= fun ys ↦
          pure (Fin.cons (α := fun _ ↦ R) x xs +
            Fin.cons (α := fun _ ↦ R) y ys)] =
        𝒟[first >>= fun x ↦
          second >>= fun y ↦
          ProbComp.sampleIID m coordinate >>= fun tail ↦
          pure (Fin.cons (α := fun _ ↦ R) (x + y) tail)]
      calc
        _ = 𝒟[first >>= fun x ↦
            second >>= fun y ↦
            firstTail >>= fun xs ↦
            secondTail >>= fun ys ↦
            pure (Fin.cons (α := fun _ ↦ R) x xs +
              Fin.cons (α := fun _ ↦ R) y ys)] := by
          refine evalDist_bind_congr' first fun x ↦ ?_
          exact evalDist_bind_bind_swap firstTail second _
        _ = 𝒟[coordinate >>= fun head ↦
            tailSum >>= fun tail ↦
              pure (Fin.cons (α := fun _ ↦ R) head tail)] := by
          congr 1
          simp [coordinate, tailSum, cons_add, bind_assoc, monad_norm]
        _ = 𝒟[coordinate >>= fun head ↦
            ProbComp.sampleIID m coordinate >>= fun tail ↦
            pure (Fin.cons (α := fun _ ↦ R) head tail)] := by
          refine evalDist_bind_congr' coordinate fun head ↦ ?_
          exact evalDist_bind_eq_of_evalDist_eq
            (by simpa only [tailSum, coordinate] using ih) _
        _ = _ := by
          congr 1
          simp [coordinate, bind_assoc, monad_norm]

/-- The one-coordinate form of the error-convolution premise in Theorem 6. -/
def ScalarErrorConvolution {R : Type} [Add R]
    (smallErrorSampler largeErrorSampler extraErrorSampler : ProbComp R) : Prop :=
  𝒟[do
    let largeError ← largeErrorSampler
    let extraError ← extraErrorSampler
    return largeError + extraError] = 𝒟[smallErrorSampler]

/-- The scalar error-convolution premise lifts to every IID batch size. -/
theorem vectorErrorConvolution_of_scalar {R : Type} [Add R]
    (m : ℕ) (smallErrorSampler largeErrorSampler extraErrorSampler : ProbComp R)
    (hConvolution : ScalarErrorConvolution smallErrorSampler
      largeErrorSampler extraErrorSampler) :
    VectorErrorConvolution m smallErrorSampler largeErrorSampler extraErrorSampler := by
  unfold ScalarErrorConvolution at hConvolution
  unfold VectorErrorConvolution
  calc
    _ = 𝒟[ProbComp.sampleIID m (do
        let largeError ← largeErrorSampler
        let extraError ← extraErrorSampler
        return largeError + extraError)] :=
      sampleIID_add_evalDist m largeErrorSampler extraErrorSampler
    _ = _ := sampleIID_evalDist_congr m hConvolution

/-- Deterministically form a real shared-randomness transcript from its three sampled parts. -/
def realTranscript {R : Type} [Semiring R] {n k m : ℕ}
    (challenge : Challenge R n k m) (secret : Secret R n k)
    (errors : Output R m) : Transcript R n k m :=
  (challenge,
    (vecMul secret.1 challenge.1 + errors.1,
      vecMul (Fin.append secret.1 secret.2) challenge.2 + errors.2))

/-- The target real distribution after replacing its uniform long matrix by two row blocks and
its small error by a large error plus the widening error. -/
def expandedSharedRealDistr {R : Type} [Semiring R] [SampleableType R]
    (n k m : ℕ)
    (prefixSampler : ProbComp (Fin n → R))
    (suffixSampler : ProbComp (Fin k → R))
    (largeErrorSampler extraErrorSampler : ProbComp R) :
    ProbComp (Transcript R n k m) := do
  let sourceChallenge ← $ᵗ (TwoBatchChallenge R n m)
  let extraRows ← $ᵗ Matrix (Fin k) (Fin m) R
  let head ← prefixSampler
  let suffix ← suffixSampler
  let errors ← pairedErrorSampler m largeErrorSampler
  let extraError ← ProbComp.sampleIID m extraErrorSampler
  return realTranscript
    (assembleChallenge (sourceChallenge, extraRows)) (head, suffix)
    (errors.1 + extraError, errors.2)

/-- The standard shared-randomness real branch equals its fully expanded form whenever the
error-convolution premise holds. -/
theorem target_real_branch_evalDist_eq_expanded {R : Type}
    [CommSemiring R] [Finite R] [DecidableEq R] [SampleableType R]
    (n k m : ℕ)
    (prefixSampler : ProbComp (Fin n → R))
    (suffixSampler : ProbComp (Fin k → R))
    (smallErrorSampler largeErrorSampler extraErrorSampler : ProbComp R)
    (hConvolution : VectorErrorConvolution m smallErrorSampler
      largeErrorSampler extraErrorSampler) :
    𝒟[LearningWithErrors.distr
        (problem n k m prefixSampler suffixSampler
          smallErrorSampler largeErrorSampler)] =
      𝒟[expandedSharedRealDistr n k m prefixSampler suffixSampler
        largeErrorSampler extraErrorSampler] := by
  let targetChallenge : ProbComp (Challenge R n k m) := $ᵗ (Challenge R n k m)
  let assembledChallenge : ProbComp (Challenge R n k m) := do
    let sourceChallenge ← $ᵗ (TwoBatchChallenge R n m)
    let extraRows ← $ᵗ Matrix (Fin k) (Fin m) R
    return assembleChallenge (sourceChallenge, extraRows)
  let targetSecret : ProbComp (Secret R n k) := do
    let head ← prefixSampler
    let suffix ← suffixSampler
    return (head, suffix)
  let targetErrors : ProbComp (Output R m) := do
    let smallError ← ProbComp.sampleIID m smallErrorSampler
    let largeError ← ProbComp.sampleIID m largeErrorSampler
    return (smallError, largeError)
  let widenedErrors : ProbComp (Output R m) :=
    widenedErrorSampler m largeErrorSampler extraErrorSampler
  have hChallenge : 𝒟[assembledChallenge] = 𝒟[targetChallenge] := by
    simpa only [assembledChallenge, targetChallenge] using
      (assembledChallenge_uniform_evalDist (R := R) (n := n) (k := k) (m := m))
  have hErrors : 𝒟[widenedErrors] = 𝒟[targetErrors] := by
    simpa only [widenedErrors, targetErrors] using
      (widenedErrorSampler_evalDist_eq m smallErrorSampler
        largeErrorSampler extraErrorSampler hConvolution)
  change 𝒟[targetChallenge >>= fun challenge ↦
      targetSecret >>= fun secret ↦
      targetErrors >>= fun errors ↦
      pure (realTranscript challenge secret errors)] =
    𝒟[expandedSharedRealDistr n k m prefixSampler suffixSampler
      largeErrorSampler extraErrorSampler]
  calc
    _ = 𝒟[assembledChallenge >>= fun challenge ↦
        targetSecret >>= fun secret ↦
        targetErrors >>= fun errors ↦
        pure (realTranscript challenge secret errors)] :=
      evalDist_bind_eq_of_evalDist_eq hChallenge.symm _
    _ = 𝒟[assembledChallenge >>= fun challenge ↦
        targetSecret >>= fun secret ↦
        widenedErrors >>= fun errors ↦
        pure (realTranscript challenge secret errors)] := by
      refine evalDist_bind_congr' assembledChallenge fun challenge ↦ ?_
      refine evalDist_bind_congr' targetSecret fun secret ↦ ?_
      exact evalDist_bind_eq_of_evalDist_eq hErrors.symm _
    _ = _ := by
      congr 1
      simp [assembledChallenge, targetSecret, widenedErrors, widenedErrorSampler,
        pairedErrorSampler, expandedSharedRealDistr, bind_assoc, monad_norm]

/-- The same reduced real distribution, grouping the two source error vectors into one draw. -/
def sourceOrderedRealDistr {R : Type} [Semiring R] [SampleableType R]
    (n k m : ℕ)
    (prefixSampler : ProbComp (Fin n → R))
    (suffixSampler : ProbComp (Fin k → R))
    (largeErrorSampler extraErrorSampler : ProbComp R) :
    ProbComp (Transcript R n k m) := do
  let sourceChallenge ← $ᵗ (TwoBatchChallenge R n m)
  let head ← prefixSampler
  let errors ← pairedErrorSampler m largeErrorSampler
  let extraRows ← $ᵗ Matrix (Fin k) (Fin m) R
  let suffix ← suffixSampler
  let extraError ← ProbComp.sampleIID m extraErrorSampler
  return realTranscript
    (assembleChallenge (sourceChallenge, extraRows)) (head, suffix)
    (errors.1 + extraError, errors.2)

/-- Grouping the two consecutive source errors does not change the reduced computation. -/
theorem reducedRealDistr_eq_sourceOrdered {R : Type}
    [CommSemiring R] [SampleableType R]
    (n k m : ℕ)
    (prefixSampler : ProbComp (Fin n → R))
    (suffixSampler : ProbComp (Fin k → R))
    (largeErrorSampler extraErrorSampler : ProbComp R) :
    reducedRealDistr n k m prefixSampler suffixSampler
        largeErrorSampler extraErrorSampler =
      sourceOrderedRealDistr n k m prefixSampler suffixSampler
        largeErrorSampler extraErrorSampler := by
  simp [reducedRealDistr, sourceOrderedRealDistr, pairedErrorSampler,
    realTranscript, assembleChallenge, vecMul_appendRows, bind_assoc, monad_norm]

/-- Reordering the independent challenge-row, secret-suffix, and error draws changes no output
probability. -/
theorem sourceOrdered_evalDist_eq_expanded {R : Type}
    [CommSemiring R] [SampleableType R]
    (n k m : ℕ)
    (prefixSampler : ProbComp (Fin n → R))
    (suffixSampler : ProbComp (Fin k → R))
    (largeErrorSampler extraErrorSampler : ProbComp R) :
    𝒟[sourceOrderedRealDistr n k m prefixSampler suffixSampler
        largeErrorSampler extraErrorSampler] =
      𝒟[expandedSharedRealDistr n k m prefixSampler suffixSampler
        largeErrorSampler extraErrorSampler] := by
  let challenges : ProbComp (TwoBatchChallenge R n m) :=
    $ᵗ (TwoBatchChallenge R n m)
  let errors : ProbComp (Output R m) := pairedErrorSampler m largeErrorSampler
  let rows : ProbComp (Matrix (Fin k) (Fin m) R) :=
    $ᵗ Matrix (Fin k) (Fin m) R
  let extraErrors : ProbComp (Fin m → R) :=
    ProbComp.sampleIID m extraErrorSampler
  let finish (challenge : TwoBatchChallenge R n m) (head : Fin n → R)
      (error : Output R m) (extraRows : Matrix (Fin k) (Fin m) R)
      (suffix : Fin k → R) (extraError : Fin m → R) :
      ProbComp (Transcript R n k m) :=
    pure (realTranscript (assembleChallenge (challenge, extraRows)) (head, suffix)
      (error.1 + extraError, error.2))
  change 𝒟[challenges >>= fun challenge ↦
      prefixSampler >>= fun head ↦
      errors >>= fun error ↦
      rows >>= fun extraRows ↦
      suffixSampler >>= fun suffix ↦
      extraErrors >>= fun extraError ↦
      finish challenge head error extraRows suffix extraError] =
    𝒟[challenges >>= fun challenge ↦
      rows >>= fun extraRows ↦
      prefixSampler >>= fun head ↦
      suffixSampler >>= fun suffix ↦
      errors >>= fun error ↦
      extraErrors >>= fun extraError ↦
      finish challenge head error extraRows suffix extraError]
  calc
    _ = 𝒟[challenges >>= fun challenge ↦
        prefixSampler >>= fun head ↦
        rows >>= fun extraRows ↦
        errors >>= fun error ↦
        suffixSampler >>= fun suffix ↦
        extraErrors >>= fun extraError ↦
        finish challenge head error extraRows suffix extraError] := by
      refine evalDist_bind_congr' challenges fun challenge ↦ ?_
      refine evalDist_bind_congr' prefixSampler fun head ↦ ?_
      exact evalDist_bind_bind_swap errors rows _
    _ = 𝒟[challenges >>= fun challenge ↦
        rows >>= fun extraRows ↦
        prefixSampler >>= fun head ↦
        errors >>= fun error ↦
        suffixSampler >>= fun suffix ↦
        extraErrors >>= fun extraError ↦
        finish challenge head error extraRows suffix extraError] := by
      refine evalDist_bind_congr' challenges fun challenge ↦ ?_
      exact evalDist_bind_bind_swap prefixSampler rows _
    _ = _ := by
      refine evalDist_bind_congr' challenges fun challenge ↦ ?_
      refine evalDist_bind_congr' rows fun extraRows ↦ ?_
      refine evalDist_bind_congr' prefixSampler fun head ↦ ?_
      exact evalDist_bind_bind_swap errors suffixSampler _

/-- The randomized reduction maps real two-block LWE samples to real shared-randomness samples. -/
theorem real_branch_evalDist_eq {R : Type}
    [CommSemiring R] [Finite R] [DecidableEq R] [SampleableType R]
    (n k m : ℕ)
    (prefixSampler : ProbComp (Fin n → R))
    (suffixSampler : ProbComp (Fin k → R))
    (smallErrorSampler largeErrorSampler extraErrorSampler : ProbComp R)
    (hConvolution : VectorErrorConvolution m smallErrorSampler
      largeErrorSampler extraErrorSampler) :
    𝒟[LearningWithErrors.distr
          (twoBatchProblem n m prefixSampler largeErrorSampler) >>=
        liftTranscript k m suffixSampler extraErrorSampler] =
      𝒟[LearningWithErrors.distr
        (problem n k m prefixSampler suffixSampler
          smallErrorSampler largeErrorSampler)] := by
  calc
    _ = 𝒟[reducedRealDistr n k m prefixSampler suffixSampler
          largeErrorSampler extraErrorSampler] :=
      source_real_branch_evalDist_eq_reduced n k m prefixSampler suffixSampler
        largeErrorSampler extraErrorSampler
    _ = 𝒟[sourceOrderedRealDistr n k m prefixSampler suffixSampler
          largeErrorSampler extraErrorSampler] := by
      rw [reducedRealDistr_eq_sourceOrdered]
    _ = 𝒟[expandedSharedRealDistr n k m prefixSampler suffixSampler
          largeErrorSampler extraErrorSampler] :=
      sourceOrdered_evalDist_eq_expanded n k m prefixSampler suffixSampler
        largeErrorSampler extraErrorSampler
    _ = _ := (target_real_branch_evalDist_eq_expanded n k m prefixSampler suffixSampler
      smallErrorSampler largeErrorSampler extraErrorSampler hConvolution).symm

/-- Turn a shared-randomness distinguisher into a two-block ordinary-LWE distinguisher. -/
def reduction {R : Type} [Semiring R] [SampleableType R]
    {n k m : ℕ}
    (suffixSampler : ProbComp (Fin k → R))
    (extraErrorSampler : ProbComp R)
    {source : LearningWithErrors.Problem
      (TwoBatchChallenge R n m) (Fin n → R) (TwoBatchOutput R m)}
    {target : LearningWithErrors.Problem
      (Challenge R n k m) (Secret R n k) (Output R m)}
    (adversary : LearningWithErrors.Adversary target) :
    LearningWithErrors.Adversary source := fun sample ↦ do
  adversary (← liftTranscript k m suffixSampler extraErrorSampler sample)

section ExactGameHop

variable {R : Type} [Semiring R] [SampleableType R]
  {n k m : ℕ}
  (suffixSampler : ProbComp (Fin k → R))
  (extraErrorSampler : ProbComp R)
  (source : LearningWithErrors.Problem
    (TwoBatchChallenge R n m) (Fin n → R) (TwoBatchOutput R m))
  (target : LearningWithErrors.Problem
    (Challenge R n k m) (Secret R n k) (Output R m))

/-- A real-branch distribution identity is preserved by every downstream adversary. -/
theorem game0_reduction_evalDist_eq
    (adversary : LearningWithErrors.Adversary target)
    (hReal :
      𝒟[LearningWithErrors.distr source >>= liftTranscript k m suffixSampler extraErrorSampler] =
        𝒟[LearningWithErrors.distr target]) :
    𝒟[LearningWithErrors.game0 target adversary] =
      𝒟[LearningWithErrors.game0 source
        (reduction suffixSampler extraErrorSampler adversary)] := by
  rw [LearningWithErrors.game0, LearningWithErrors.game0]
  simp only [reduction]
  rw [← bind_assoc]
  rw [evalDist_bind, evalDist_bind, hReal]

/-- A uniform-branch distribution identity is preserved by every downstream adversary. -/
theorem game1_reduction_evalDist_eq
    (adversary : LearningWithErrors.Adversary target)
    (hUniform :
      𝒟[LearningWithErrors.uniformDistr source >>=
          liftTranscript k m suffixSampler extraErrorSampler] =
        𝒟[LearningWithErrors.uniformDistr target]) :
    𝒟[LearningWithErrors.game1 target adversary] =
      𝒟[LearningWithErrors.game1 source
        (reduction suffixSampler extraErrorSampler adversary)] := by
  rw [LearningWithErrors.game1, LearningWithErrors.game1]
  simp only [reduction]
  rw [← bind_assoc]
  rw [evalDist_bind, evalDist_bind, hUniform]

/-- Exact reduction theorem: if the randomized transformation maps both source branches to the
corresponding shared-randomness branches, the two distinguishing advantages are equal. -/
theorem advantage_eq
    (adversary : LearningWithErrors.Adversary target)
    (hReal :
      𝒟[LearningWithErrors.distr source >>= liftTranscript k m suffixSampler extraErrorSampler] =
        𝒟[LearningWithErrors.distr target])
    (hUniform :
      𝒟[LearningWithErrors.uniformDistr source >>=
          liftTranscript k m suffixSampler extraErrorSampler] =
        𝒟[LearningWithErrors.uniformDistr target]) :
    LearningWithErrors.advantage target adversary =
      LearningWithErrors.advantage source
        (reduction suffixSampler extraErrorSampler adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage,
    FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (game0_reduction_evalDist_eq suffixSampler extraErrorSampler source target adversary hReal)
      true,
    evalDist_ext_iff.mp
      (game1_reduction_evalDist_eq suffixSampler extraErrorSampler source target adversary hUniform)
      true]

end ExactGameHop

section TheoremSix

/-- Formal version of Theorem 6 for an arbitrary finite commutative coefficient ring.

Every shared-randomness distinguisher has exactly the advantage of the constructed distinguisher
against two `m`-sample ordinary-LWE blocks.  The scalar convolution premise is lifted internally
to the full error vectors. -/
theorem advantage_eq_twoBatch {R : Type}
    [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]
    (n k m : ℕ)
    (prefixSampler : ProbComp (Fin n → R))
    (suffixSampler : ProbComp (Fin k → R))
    (smallErrorSampler largeErrorSampler extraErrorSampler : ProbComp R)
    (hConvolution : ScalarErrorConvolution smallErrorSampler
      largeErrorSampler extraErrorSampler)
    (hSuffix : Pr[⊥ | suffixSampler] = 0)
    (hExtraError : Pr[⊥ | extraErrorSampler] = 0)
    (adversary : LearningWithErrors.Adversary
      (problem n k m prefixSampler suffixSampler
        smallErrorSampler largeErrorSampler)) :
    LearningWithErrors.advantage
        (problem n k m prefixSampler suffixSampler
          smallErrorSampler largeErrorSampler) adversary =
      LearningWithErrors.advantage
        (twoBatchProblem n m prefixSampler largeErrorSampler)
        (reduction suffixSampler extraErrorSampler adversary) := by
  let source := twoBatchProblem n m prefixSampler largeErrorSampler
  let target := problem n k m prefixSampler suffixSampler
    smallErrorSampler largeErrorSampler
  have hVector : VectorErrorConvolution m smallErrorSampler
      largeErrorSampler extraErrorSampler :=
    vectorErrorConvolution_of_scalar m smallErrorSampler largeErrorSampler
      extraErrorSampler hConvolution
  have hReal :
      𝒟[LearningWithErrors.distr source >>=
          liftTranscript k m suffixSampler extraErrorSampler] =
        𝒟[LearningWithErrors.distr target] := by
    simpa only [source, target] using
      (real_branch_evalDist_eq n k m prefixSampler suffixSampler
        smallErrorSampler largeErrorSampler extraErrorSampler hVector)
  have hUniform :
      𝒟[LearningWithErrors.uniformDistr source >>=
          liftTranscript k m suffixSampler extraErrorSampler] =
        𝒟[LearningWithErrors.uniformDistr target] := by
    simpa only [source, target] using
      (uniform_branch_evalDist_eq n k m prefixSampler suffixSampler
        smallErrorSampler largeErrorSampler extraErrorSampler hSuffix
        (probFailure_sampleIID_eq_zero m extraErrorSampler hExtraError))
  exact advantage_eq suffixSampler extraErrorSampler source target adversary hReal hUniform

/-- `ZMod q` specialization of Theorem 6 with uniform nested secrets. -/
theorem zmod_advantage_eq_twoBatch {q : ℕ} [NeZero q]
    (n k m : ℕ)
    (smallErrorSampler largeErrorSampler extraErrorSampler : ProbComp (ZMod q))
    (hConvolution : ScalarErrorConvolution smallErrorSampler
      largeErrorSampler extraErrorSampler)
    (hExtraError : Pr[⊥ | extraErrorSampler] = 0)
    (adversary : LearningWithErrors.Adversary
      (zmodProblem n k m q smallErrorSampler largeErrorSampler)) :
    LearningWithErrors.advantage
        (zmodProblem n k m q smallErrorSampler largeErrorSampler) adversary =
      LearningWithErrors.advantage
        (zmodTwoBatchProblem n m q largeErrorSampler)
        (reduction ($ᵗ (Fin k → ZMod q)) extraErrorSampler adversary) := by
  simpa only [zmodProblem, zmodTwoBatchProblem] using
    (advantage_eq_twoBatch n k m
      ($ᵗ (Fin n → ZMod q)) ($ᵗ (Fin k → ZMod q))
      smallErrorSampler largeErrorSampler extraErrorSampler
      hConvolution (by simp) hExtraError adversary)

end TheoremSix

end FormalProof4FHE.SharedRandomness
