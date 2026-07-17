/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.Security
import FormalProof4FHE.SharedRandomness.Ordinary

/-!
# Restricting a Batch of LWE Samples

This file proves the exact sample-count monotonicity used by the shared-randomness
key-switching-key reduction.  A transcript with `discarded + retained` columns can be restricted
to its final `retained` columns.  Both the real and uniform branches then have exactly the
distribution of a fresh `retained`-sample LWE transcript.

The theorem is stated for an arbitrary finite coefficient semiring and an arbitrary secret type
with an explicit embedding into the coefficient vector.  In particular it applies without loss to
ordinary, binary, and block-binary secret distributions.  The only totality premise says that the
scalar error sampler does not fail; it is needed because `ProbComp` has subprobability semantics and
the discarded errors are genuinely sampled by the larger game.
-/

open Matrix OracleComp

namespace FormalProof4FHE.LWE

/-- Public matrix and noisy output of an `m`-sample matrix-LWE problem. -/
abbrev BatchTranscript (R : Type) (n m : ℕ) :=
  Matrix (Fin n) (Fin m) R × (Fin m → R)

/-- Split a vector after its first `discarded` coordinates. -/
def splitBatchOutput {R : Type} {discarded retained : ℕ}
    (output : Fin (discarded + retained) → R) :
    (Fin discarded → R) × (Fin retained → R) :=
  (fun j ↦ output (Fin.castAdd retained j),
    fun j ↦ output (Fin.natAdd discarded j))

/-- Concatenate the discarded and retained vector blocks. -/
def appendBatchOutput {R : Type} {discarded retained : ℕ}
    (output : (Fin discarded → R) × (Fin retained → R)) :
    Fin (discarded + retained) → R :=
  Fin.append output.1 output.2

@[simp]
theorem splitBatchOutput_appendBatchOutput {R : Type} {discarded retained : ℕ}
    (output : (Fin discarded → R) × (Fin retained → R)) :
    splitBatchOutput (appendBatchOutput output) = output := by
  rcases output with ⟨first, second⟩
  apply Prod.ext
  · funext i
    exact Fin.append_left first second i
  · funext i
    exact Fin.append_right first second i

@[simp]
theorem appendBatchOutput_splitBatchOutput {R : Type} {discarded retained : ℕ}
    (output : Fin (discarded + retained) → R) :
    appendBatchOutput (splitBatchOutput output) = output := by
  exact Fin.append_castAdd_natAdd

/-- Splitting a vector into two consecutive blocks is a bijection. -/
theorem splitBatchOutput_bijective {R : Type} {discarded retained : ℕ} :
    Function.Bijective
      (splitBatchOutput :
        (Fin (discarded + retained) → R) →
          (Fin discarded → R) × (Fin retained → R)) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨appendBatchOutput, ?_, ?_⟩
  · exact appendBatchOutput_splitBatchOutput
  · exact splitBatchOutput_appendBatchOutput

/-- Split a matrix into its first `discarded` and final `retained` columns. -/
def splitBatchColumns {R : Type} {n discarded retained : ℕ}
    (matrix : Matrix (Fin n) (Fin (discarded + retained)) R) :
    Matrix (Fin n) (Fin discarded) R × Matrix (Fin n) (Fin retained) R :=
  (fun i j ↦ matrix i (Fin.castAdd retained j),
    fun i j ↦ matrix i (Fin.natAdd discarded j))

/-- Concatenate two consecutive matrix-column blocks. -/
def appendBatchColumns {R : Type} {n discarded retained : ℕ}
    (matrices :
      Matrix (Fin n) (Fin discarded) R × Matrix (Fin n) (Fin retained) R) :
    Matrix (Fin n) (Fin (discarded + retained)) R :=
  fun i ↦ Fin.append (matrices.1 i) (matrices.2 i)

@[simp]
theorem splitBatchColumns_appendBatchColumns {R : Type} {n discarded retained : ℕ}
    (matrices :
      Matrix (Fin n) (Fin discarded) R × Matrix (Fin n) (Fin retained) R) :
    splitBatchColumns (appendBatchColumns matrices) = matrices := by
  rcases matrices with ⟨first, second⟩
  apply Prod.ext
  · funext i j
    exact Fin.append_left (first i) (second i) j
  · funext i j
    exact Fin.append_right (first i) (second i) j

@[simp]
theorem appendBatchColumns_splitBatchColumns {R : Type} {n discarded retained : ℕ}
    (matrix : Matrix (Fin n) (Fin (discarded + retained)) R) :
    appendBatchColumns (splitBatchColumns matrix) = matrix := by
  funext i
  exact Fin.append_castAdd_natAdd

/-- Splitting matrix columns is a bijection. -/
theorem splitBatchColumns_bijective {R : Type} {n discarded retained : ℕ} :
    Function.Bijective
      (splitBatchColumns :
        Matrix (Fin n) (Fin (discarded + retained)) R →
          Matrix (Fin n) (Fin discarded) R × Matrix (Fin n) (Fin retained) R) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨appendBatchColumns, ?_, ?_⟩
  · exact appendBatchColumns_splitBatchColumns
  · exact splitBatchColumns_appendBatchColumns

/-- Split a public transcript into discarded and retained transcript blocks. -/
def splitBatchTranscriptAt {R : Type} {n discarded retained : ℕ}
    (transcript : BatchTranscript R n (discarded + retained)) :
    BatchTranscript R n discarded × BatchTranscript R n retained :=
  let matrices := splitBatchColumns transcript.1
  let outputs := splitBatchOutput transcript.2
  ((matrices.1, outputs.1), (matrices.2, outputs.2))

/-- Reassemble two consecutive public transcript blocks. -/
def appendBatchTranscriptAt {R : Type} {n discarded retained : ℕ}
    (transcripts :
      BatchTranscript R n discarded × BatchTranscript R n retained) :
    BatchTranscript R n (discarded + retained) :=
  (appendBatchColumns (transcripts.1.1, transcripts.2.1),
    appendBatchOutput (transcripts.1.2, transcripts.2.2))

@[simp]
theorem splitBatchTranscriptAt_appendBatchTranscriptAt
    {R : Type} {n discarded retained : ℕ}
    (transcripts :
      BatchTranscript R n discarded × BatchTranscript R n retained) :
    splitBatchTranscriptAt (appendBatchTranscriptAt transcripts) = transcripts := by
  rcases transcripts with ⟨⟨firstMatrix, firstOutput⟩, secondMatrix, secondOutput⟩
  simp [splitBatchTranscriptAt, appendBatchTranscriptAt]

@[simp]
theorem appendBatchTranscriptAt_splitBatchTranscriptAt
    {R : Type} {n discarded retained : ℕ}
    (transcript : BatchTranscript R n (discarded + retained)) :
    appendBatchTranscriptAt (splitBatchTranscriptAt transcript) = transcript := by
  rcases transcript with ⟨matrix, output⟩
  simp [splitBatchTranscriptAt, appendBatchTranscriptAt]

/-- Splitting a full transcript into consecutive transcript blocks is a bijection. -/
theorem splitBatchTranscriptAt_bijective
    {R : Type} {n discarded retained : ℕ} :
    Function.Bijective
      (splitBatchTranscriptAt :
        BatchTranscript R n (discarded + retained) →
          BatchTranscript R n discarded × BatchTranscript R n retained) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨appendBatchTranscriptAt, ?_, ?_⟩
  · exact appendBatchTranscriptAt_splitBatchTranscriptAt
  · exact splitBatchTranscriptAt_appendBatchTranscriptAt

/-- Keep only the final `retained` columns of a public transcript. -/
def retainBatchSuffix {R : Type} {n discarded retained : ℕ}
    (transcript : BatchTranscript R n (discarded + retained)) :
    BatchTranscript R n retained :=
  (splitBatchTranscriptAt transcript).2

/-- Keeping a suffix commutes with vector--matrix multiplication. -/
theorem splitBatchOutput_vecMul {R : Type} [NonUnitalNonAssocSemiring R]
    {n discarded retained : ℕ} (secret : Fin n → R)
    (matrix : Matrix (Fin n) (Fin (discarded + retained)) R) :
    splitBatchOutput (vecMul secret matrix) =
      (vecMul secret (splitBatchColumns matrix).1,
        vecMul secret (splitBatchColumns matrix).2) := by
  apply Prod.ext <;> rfl

/-- Keeping a suffix commutes with coordinatewise addition. -/
theorem splitBatchOutput_add {R : Type} [Add R] {discarded retained : ℕ}
    (first second : Fin (discarded + retained) → R) :
    splitBatchOutput (first + second) =
      ((splitBatchOutput first).1 + (splitBatchOutput second).1,
        (splitBatchOutput first).2 + (splitBatchOutput second).2) := by
  apply Prod.ext <;> rfl

/-- Retaining a suffix of a real linear transcript retains exactly the corresponding signal and
error coordinates. -/
theorem retainBatchSuffix_real {R : Type} [Semiring R]
    {n discarded retained : ℕ} (secret : Fin n → R)
    (challenge : Matrix (Fin n) (Fin (discarded + retained)) R)
    (error : Fin (discarded + retained) → R) :
    retainBatchSuffix (challenge, vecMul secret challenge + error) =
      ((splitBatchColumns challenge).2,
        vecMul secret (splitBatchColumns challenge).2 + (splitBatchOutput error).2) := by
  apply Prod.ext
  · rfl
  · funext j
    rfl

/-- Splitting an IID vector gives two independently sampled consecutive IID blocks. -/
theorem splitBatchOutput_sampleIID_evalDist {R : Type} [Finite R]
    (discarded retained : ℕ) (sampler : ProbComp R) :
    𝒟[splitBatchOutput <$> ProbComp.sampleIID (discarded + retained) sampler] =
      𝒟[do
        let first ← ProbComp.sampleIID discarded sampler
        let second ← ProbComp.sampleIID retained sampler
        return (first, second)] := by
  refine evalDist_ext fun output ↦ ?_
  calc
    Pr[= output |
        splitBatchOutput <$> ProbComp.sampleIID (discarded + retained) sampler] =
        Pr[= appendBatchOutput output |
          ProbComp.sampleIID (discarded + retained) sampler] := by
      simpa using
        (probOutput_map_injective
          (ProbComp.sampleIID (discarded + retained) sampler)
          splitBatchOutput_bijective.injective (appendBatchOutput output))
    _ = ∏ i : Fin (discarded + retained),
          Pr[= appendBatchOutput output i | sampler] :=
      FormalProof4FHE.SharedRandomness.probOutput_sampleIID
        (discarded + retained) sampler (appendBatchOutput output)
    _ = (∏ i : Fin discarded, Pr[= output.1 i | sampler]) *
          ∏ i : Fin retained, Pr[= output.2 i | sampler] := by
      rw [Fin.prod_univ_add]
      congr 1
      · apply Finset.prod_congr rfl
        intro i _
        rw [appendBatchOutput, Fin.append_left]
      · apply Finset.prod_congr rfl
        intro i _
        rw [appendBatchOutput, Fin.append_right]
    _ = Pr[= output | do
          let first ← ProbComp.sampleIID discarded sampler
          let second ← ProbComp.sampleIID retained sampler
          return (first, second)] := by
      symm
      simp [FormalProof4FHE.SharedRandomness.probOutput_sampleIID]
  rfl

/-- Restricting a uniform full matrix to its final columns is exactly uniform. -/
theorem retainBatchSuffix_uniformMatrix_evalDist {R : Type}
    [Finite R] [SampleableType R] (n discarded retained : ℕ) :
    𝒟[(fun matrix ↦ (splitBatchColumns matrix).2) <$>
        ($ᵗ Matrix (Fin n) (Fin (discarded + retained)) R)] =
      𝒟[$ᵗ Matrix (Fin n) (Fin retained) R] := by
  let split :=
    splitBatchColumns (R := R) (n := n) (discarded := discarded)
      (retained := retained)
  have hsplit :
      𝒟[split <$> ($ᵗ Matrix (Fin n) (Fin (discarded + retained)) R)] =
        𝒟[$ᵗ (Matrix (Fin n) (Fin discarded) R ×
          Matrix (Fin n) (Fin retained) R)] :=
    evalDist_map_bijective_uniform_cross
      (α := Matrix (Fin n) (Fin (discarded + retained)) R)
      (β := Matrix (Fin n) (Fin discarded) R × Matrix (Fin n) (Fin retained) R)
      split
      (splitBatchColumns_bijective
        (R := R) (n := n) (discarded := discarded) (retained := retained))
  have hsnd :
      𝒟[Prod.snd <$> ($ᵗ (Matrix (Fin n) (Fin discarded) R ×
          Matrix (Fin n) (Fin retained) R))] =
        𝒟[$ᵗ Matrix (Fin n) (Fin retained) R] := by
    let swap := Equiv.prodComm
      (Matrix (Fin n) (Fin discarded) R) (Matrix (Fin n) (Fin retained) R)
    have hswap :
        𝒟[swap <$> ($ᵗ (Matrix (Fin n) (Fin discarded) R ×
            Matrix (Fin n) (Fin retained) R))] =
          𝒟[$ᵗ (Matrix (Fin n) (Fin retained) R ×
            Matrix (Fin n) (Fin discarded) R)] :=
      evalDist_map_bijective_uniform_cross
        (α := Matrix (Fin n) (Fin discarded) R × Matrix (Fin n) (Fin retained) R)
        (β := Matrix (Fin n) (Fin retained) R × Matrix (Fin n) (Fin discarded) R)
        swap swap.bijective
    calc
      _ = 𝒟[Prod.fst <$> (swap <$>
          ($ᵗ (Matrix (Fin n) (Fin discarded) R ×
            Matrix (Fin n) (Fin retained) R)))] := by
        simp [swap, Functor.map_map]
      _ = 𝒟[Prod.fst <$> ($ᵗ (Matrix (Fin n) (Fin retained) R ×
          Matrix (Fin n) (Fin discarded) R))] := by
        simpa only [evalDist_map] using
          congrArg (fun distribution ↦ Prod.fst <$> distribution) hswap
      _ = _ := evalDist_map_fst_uniformSample_prod
  calc
    _ = 𝒟[Prod.snd <$> (split <$>
        ($ᵗ Matrix (Fin n) (Fin (discarded + retained)) R))] := by
      simp [split, Functor.map_map]
    _ = 𝒟[Prod.snd <$> ($ᵗ (Matrix (Fin n) (Fin discarded) R ×
        Matrix (Fin n) (Fin retained) R))] := by
      simpa only [evalDist_map] using
        congrArg (fun distribution ↦ Prod.snd <$> distribution) hsplit
    _ = _ := hsnd

/-- Restricting an IID vector to its final coordinates is exact when discarded draws cannot
fail. -/
theorem retainBatchSuffix_sampleIID_evalDist {R : Type} [Finite R]
    (discarded retained : ℕ) (sampler : ProbComp R)
    (hSampler : Pr[⊥ | sampler] = 0) :
    𝒟[(fun output ↦ (splitBatchOutput output).2) <$>
        ProbComp.sampleIID (discarded + retained) sampler] =
      𝒟[ProbComp.sampleIID retained sampler] := by
  let split :=
    splitBatchOutput (R := R) (discarded := discarded) (retained := retained)
  let first := ProbComp.sampleIID discarded sampler
  let second := ProbComp.sampleIID retained sampler
  have hsplit :
      𝒟[split <$> ProbComp.sampleIID (discarded + retained) sampler] =
        𝒟[do
          let firstOutput ← first
          let secondOutput ← second
          return (firstOutput, secondOutput)] := by
    simpa only [split, first, second] using
      (splitBatchOutput_sampleIID_evalDist discarded retained sampler)
  have hFirst : Pr[⊥ | first] = 0 := by
    exact FormalProof4FHE.SharedRandomness.probFailure_sampleIID_eq_zero
      discarded sampler hSampler
  calc
    _ = 𝒟[Prod.snd <$> (split <$>
        ProbComp.sampleIID (discarded + retained) sampler)] := by
      simp [split, Functor.map_map]
    _ = 𝒟[Prod.snd <$> (do
          let firstOutput ← first
          let secondOutput ← second
          return (firstOutput, secondOutput))] := by
      simpa only [evalDist_map] using
        congrArg (fun distribution ↦ Prod.snd <$> distribution) hsplit
    _ = 𝒟[first >>= fun _ ↦ second] := by
      simp [first, second, monad_norm]
    _ = 𝒟[second] :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        first hFirst second
    _ = _ := rfl

/-- Matrix LWE with an arbitrary secret type and an explicit coefficient-vector embedding. -/
def embeddedBatchProblem {R Secret : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (n samples : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin n → R) (errorSampler : ProbComp R) :
    LearningWithErrors.Problem
      (Matrix (Fin n) (Fin samples) R) Secret (Fin samples → R) where
  sampleChallenge := $ᵗ Matrix (Fin n) (Fin samples) R
  sampleSecret := secretSampler
  sampleError := ProbComp.sampleIID samples errorSampler
  noiseless := fun secret challenge ↦ vecMul (embed secret) challenge
  sampleUniform := $ᵗ (Fin samples → R)

/-- Restrict an adversary for `retained` samples to the final columns of a
`discarded + retained`-sample transcript. -/
def sampleRestrictionReduction {R Secret : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    {n discarded retained : ℕ} {secretSampler : ProbComp Secret}
    {embed : Secret → Fin n → R} {errorSampler : ProbComp R}
    (adversary : LearningWithErrors.Adversary
      (embeddedBatchProblem n retained secretSampler embed errorSampler)) :
    LearningWithErrors.Adversary
      (embeddedBatchProblem n (discarded + retained) secretSampler embed errorSampler) :=
  fun transcript ↦ adversary (retainBatchSuffix transcript)

/-- Restricting the real branch of a larger batch gives exactly the smaller real branch. -/
theorem retainBatchSuffix_real_evalDist {R Secret : Type}
    [Semiring R] [Finite R] [DecidableEq R] [SampleableType R]
    (n discarded retained : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin n → R) (errorSampler : ProbComp R)
    (hError : Pr[⊥ | errorSampler] = 0) :
    𝒟[LearningWithErrors.distr
          (embeddedBatchProblem n (discarded + retained)
            secretSampler embed errorSampler) >>=
        fun transcript ↦ pure (retainBatchSuffix transcript)] =
      𝒟[LearningWithErrors.distr
        (embeddedBatchProblem n retained secretSampler embed errorSampler)] := by
  let fullChallenge : ProbComp (Matrix (Fin n) (Fin (discarded + retained)) R) :=
    $ᵗ Matrix (Fin n) (Fin (discarded + retained)) R
  let retainedChallenge : ProbComp (Matrix (Fin n) (Fin retained) R) :=
    (fun matrix ↦ (splitBatchColumns matrix).2) <$> fullChallenge
  let targetChallenge : ProbComp (Matrix (Fin n) (Fin retained) R) :=
    $ᵗ Matrix (Fin n) (Fin retained) R
  let fullError : ProbComp (Fin (discarded + retained) → R) :=
    ProbComp.sampleIID (discarded + retained) errorSampler
  let retainedError : ProbComp (Fin retained → R) :=
    (fun output ↦ (splitBatchOutput output).2) <$> fullError
  let targetError : ProbComp (Fin retained → R) :=
    ProbComp.sampleIID retained errorSampler
  have hChallenge : 𝒟[retainedChallenge] = 𝒟[targetChallenge] := by
    simpa only [retainedChallenge, fullChallenge, targetChallenge] using
      (retainBatchSuffix_uniformMatrix_evalDist (R := R) n discarded retained)
  have hErrors : 𝒟[retainedError] = 𝒟[targetError] := by
    simpa only [retainedError, fullError, targetError] using
      (retainBatchSuffix_sampleIID_evalDist discarded retained errorSampler hError)
  have left_eq :
      (LearningWithErrors.distr
          (embeddedBatchProblem n (discarded + retained)
            secretSampler embed errorSampler) >>=
        fun transcript ↦ pure (retainBatchSuffix transcript)) =
      (retainedChallenge >>= fun challenge ↦
        secretSampler >>= fun secret ↦
        retainedError >>= fun error ↦
        pure (challenge, vecMul (embed secret) challenge + error)) := by
    simp [LearningWithErrors.distr, embeddedBatchProblem, retainedChallenge, fullChallenge,
      retainedError, fullError, retainBatchSuffix_real, bind_assoc, monad_norm]
  have right_eq :
      LearningWithErrors.distr
          (embeddedBatchProblem n retained secretSampler embed errorSampler) =
      (targetChallenge >>= fun challenge ↦
        secretSampler >>= fun secret ↦
        targetError >>= fun error ↦
        pure (challenge, vecMul (embed secret) challenge + error)) := by
    simp [LearningWithErrors.distr, embeddedBatchProblem, targetChallenge, targetError,
      monad_norm]
  rw [left_eq, right_eq]
  calc
    _ = 𝒟[targetChallenge >>= fun challenge ↦
        secretSampler >>= fun secret ↦
        retainedError >>= fun error ↦
        pure (challenge, vecMul (embed secret) challenge + error)] :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hChallenge _
    _ = _ := by
      refine evalDist_bind_congr' targetChallenge fun challenge ↦ ?_
      refine evalDist_bind_congr' secretSampler fun secret ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hErrors _

/-- Restricting the uniform branch of a larger batch gives exactly the smaller uniform branch. -/
theorem retainBatchSuffix_uniform_evalDist {R Secret : Type}
    [Semiring R] [Finite R] [DecidableEq R] [SampleableType R]
    (n discarded retained : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin n → R) (errorSampler : ProbComp R) :
    𝒟[LearningWithErrors.uniformDistr
          (embeddedBatchProblem n (discarded + retained)
            secretSampler embed errorSampler) >>=
        fun transcript ↦ pure (retainBatchSuffix transcript)] =
      𝒟[LearningWithErrors.uniformDistr
        (embeddedBatchProblem n retained secretSampler embed errorSampler)] := by
  let fullChallenge : ProbComp (Matrix (Fin n) (Fin (discarded + retained)) R) :=
    $ᵗ Matrix (Fin n) (Fin (discarded + retained)) R
  let fullOutput : ProbComp (Fin (discarded + retained) → R) :=
    $ᵗ (Fin (discarded + retained) → R)
  let retainedChallenge : ProbComp (Matrix (Fin n) (Fin retained) R) :=
    (fun matrix ↦ (splitBatchColumns matrix).2) <$> fullChallenge
  let retainedOutput : ProbComp (Fin retained → R) :=
    (fun output ↦ (splitBatchOutput output).2) <$> fullOutput
  have hChallenge :
      𝒟[retainedChallenge] = 𝒟[$ᵗ Matrix (Fin n) (Fin retained) R] := by
    simpa only [retainedChallenge, fullChallenge] using
      (retainBatchSuffix_uniformMatrix_evalDist (R := R) n discarded retained)
  have hOutput : 𝒟[retainedOutput] = 𝒟[$ᵗ (Fin retained → R)] := by
    let injection : Fin retained → Fin (discarded + retained) := Fin.natAdd discarded
    simpa only [retainedOutput, fullOutput, splitBatchOutput, Function.comp_def,
      injection, bind_pure_comp] using
      (evalDist_uniformSample_map_comp_injective
        (R := R) (e := injection) (Fin.natAdd_injective retained discarded))
  have left_eq :
      (LearningWithErrors.uniformDistr
          (embeddedBatchProblem n (discarded + retained)
            secretSampler embed errorSampler) >>=
        fun transcript ↦ pure (retainBatchSuffix transcript)) =
      (retainedChallenge >>= fun challenge ↦
        retainedOutput >>= fun output ↦ pure (challenge, output)) := by
    simp [LearningWithErrors.uniformDistr, embeddedBatchProblem, retainBatchSuffix,
      splitBatchTranscriptAt, retainedChallenge, retainedOutput, fullChallenge, fullOutput,
      bind_assoc, monad_norm]
  have right_eq :
      LearningWithErrors.uniformDistr
          (embeddedBatchProblem n retained secretSampler embed errorSampler) =
      (($ᵗ Matrix (Fin n) (Fin retained) R) >>= fun challenge ↦
        ($ᵗ (Fin retained → R)) >>= fun output ↦ pure (challenge, output)) := by
    simp [LearningWithErrors.uniformDistr, embeddedBatchProblem, monad_norm]
  rw [left_eq, right_eq]
  calc
    _ = 𝒟[($ᵗ Matrix (Fin n) (Fin retained) R) >>= fun challenge ↦
        retainedOutput >>= fun output ↦ pure (challenge, output)] :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hChallenge _
    _ = _ := by
      refine evalDist_bind_congr' ($ᵗ Matrix (Fin n) (Fin retained) R) fun challenge ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hOutput _

/-- The real games of sample restriction are distributionally identical. -/
theorem sampleRestriction_game0_evalDist_eq {R Secret : Type}
    [Semiring R] [Finite R] [DecidableEq R] [SampleableType R]
    (n discarded retained : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin n → R) (errorSampler : ProbComp R)
    (hError : Pr[⊥ | errorSampler] = 0)
    (adversary : LearningWithErrors.Adversary
      (embeddedBatchProblem n retained secretSampler embed errorSampler)) :
    𝒟[LearningWithErrors.game0
        (embeddedBatchProblem n retained secretSampler embed errorSampler) adversary] =
      𝒟[LearningWithErrors.game0
        (embeddedBatchProblem n (discarded + retained)
          secretSampler embed errorSampler)
        (sampleRestrictionReduction adversary)] := by
  rw [LearningWithErrors.game0, LearningWithErrors.game0]
  simp only [sampleRestrictionReduction]
  rw [show (LearningWithErrors.distr
        (embeddedBatchProblem n (discarded + retained)
          secretSampler embed errorSampler) >>=
      fun transcript ↦ adversary (retainBatchSuffix transcript)) =
      ((LearningWithErrors.distr
          (embeddedBatchProblem n (discarded + retained)
            secretSampler embed errorSampler) >>=
        fun transcript ↦ pure (retainBatchSuffix transcript)) >>= adversary) by
    simp [bind_assoc, monad_norm]]
  rw [evalDist_bind, evalDist_bind,
    retainBatchSuffix_real_evalDist n discarded retained secretSampler embed
      errorSampler hError]

/-- The uniform games of sample restriction are distributionally identical. -/
theorem sampleRestriction_game1_evalDist_eq {R Secret : Type}
    [Semiring R] [Finite R] [DecidableEq R] [SampleableType R]
    (n discarded retained : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin n → R) (errorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (embeddedBatchProblem n retained secretSampler embed errorSampler)) :
    𝒟[LearningWithErrors.game1
        (embeddedBatchProblem n retained secretSampler embed errorSampler) adversary] =
      𝒟[LearningWithErrors.game1
        (embeddedBatchProblem n (discarded + retained)
          secretSampler embed errorSampler)
        (sampleRestrictionReduction adversary)] := by
  rw [LearningWithErrors.game1, LearningWithErrors.game1]
  simp only [sampleRestrictionReduction]
  rw [show (LearningWithErrors.uniformDistr
        (embeddedBatchProblem n (discarded + retained)
          secretSampler embed errorSampler) >>=
      fun transcript ↦ adversary (retainBatchSuffix transcript)) =
      ((LearningWithErrors.uniformDistr
          (embeddedBatchProblem n (discarded + retained)
            secretSampler embed errorSampler) >>=
        fun transcript ↦ pure (retainBatchSuffix transcript)) >>= adversary) by
    simp [bind_assoc, monad_norm]]
  rw [evalDist_bind, evalDist_bind,
    retainBatchSuffix_uniform_evalDist n discarded retained secretSampler embed errorSampler]

/-- Exact sample-count monotonicity: every `retained`-sample adversary has exactly the advantage
of its suffix-restriction reduction against `discarded + retained` samples. -/
theorem sampleRestriction_advantage_eq {R Secret : Type}
    [Semiring R] [Finite R] [DecidableEq R] [SampleableType R]
    (n discarded retained : ℕ) (secretSampler : ProbComp Secret)
    (embed : Secret → Fin n → R) (errorSampler : ProbComp R)
    (hError : Pr[⊥ | errorSampler] = 0)
    (adversary : LearningWithErrors.Adversary
      (embeddedBatchProblem n retained secretSampler embed errorSampler)) :
    LearningWithErrors.advantage
        (embeddedBatchProblem n retained secretSampler embed errorSampler) adversary =
      LearningWithErrors.advantage
        (embeddedBatchProblem n (discarded + retained)
          secretSampler embed errorSampler)
        (sampleRestrictionReduction adversary) := by
  rw [advantage_eq_boolDistAdvantage, advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (sampleRestriction_game0_evalDist_eq n discarded retained secretSampler embed
        errorSampler hError adversary) true,
    evalDist_ext_iff.mp
      (sampleRestriction_game1_evalDist_eq n discarded retained secretSampler embed
        errorSampler adversary) true]

end FormalProof4FHE.LWE
