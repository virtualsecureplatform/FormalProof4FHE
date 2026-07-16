/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.SharedRandomness.Reduction

/-!
# Two LWE Blocks as `m + m` Ordinary Samples

Theorem 6 is naturally described using two blocks of `m` samples.  This module proves that this
presentation is distributionally identical to the ordinary matrix LWE problem with `m + m`
columns, and composes that equivalence with the shared-randomness reduction.
-/

open Matrix OracleComp

namespace FormalProof4FHE.SharedRandomness

/-- Split a vector indexed by `Fin (m + m)` into its first and second `m` coordinates. -/
def splitOutput {R : Type} {m : ℕ} (output : Fin (m + m) → R) : Output R m :=
  (fun j ↦ output (Fin.castAdd m j), fun j ↦ output (Fin.natAdd m j))

/-- Concatenate two length-`m` output vectors. -/
def appendOutput {R : Type} {m : ℕ} (output : Output R m) : Fin (m + m) → R :=
  Fin.append output.1 output.2

@[simp]
theorem splitOutput_appendOutput {R : Type} {m : ℕ} (output : Output R m) :
    splitOutput (appendOutput output) = output := by
  rcases output with ⟨first, second⟩
  apply Prod.ext
  · funext i
    exact Fin.append_left first second i
  · funext i
    exact Fin.append_right first second i

@[simp]
theorem appendOutput_splitOutput {R : Type} {m : ℕ} (output : Fin (m + m) → R) :
    appendOutput (splitOutput output) = output := by
  exact Fin.append_castAdd_natAdd

/-- Splitting an output vector is a bijection. -/
theorem splitOutput_bijective {R : Type} {m : ℕ} :
    Function.Bijective (splitOutput : (Fin (m + m) → R) → Output R m) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨appendOutput, ?_, ?_⟩
  · exact appendOutput_splitOutput
  · exact splitOutput_appendOutput

/-- Split the columns of an `m + m`-sample LWE matrix into two `m`-column blocks. -/
def splitColumns {R : Type} {n m : ℕ}
    (matrix : Matrix (Fin n) (Fin (m + m)) R) : TwoBatchChallenge R n m :=
  (fun i j ↦ matrix i (Fin.castAdd m j),
    fun i j ↦ matrix i (Fin.natAdd m j))

/-- Concatenate two `m`-column matrices. -/
def appendColumns {R : Type} {n m : ℕ}
    (matrices : TwoBatchChallenge R n m) : Matrix (Fin n) (Fin (m + m)) R :=
  fun i ↦ Fin.append (matrices.1 i) (matrices.2 i)

@[simp]
theorem splitColumns_appendColumns {R : Type} {n m : ℕ}
    (matrices : TwoBatchChallenge R n m) :
    splitColumns (appendColumns matrices) = matrices := by
  rcases matrices with ⟨first, second⟩
  apply Prod.ext
  · funext i j
    exact Fin.append_left (first i) (second i) j
  · funext i j
    exact Fin.append_right (first i) (second i) j

@[simp]
theorem appendColumns_splitColumns {R : Type} {n m : ℕ}
    (matrix : Matrix (Fin n) (Fin (m + m)) R) :
    appendColumns (splitColumns matrix) = matrix := by
  funext i
  exact Fin.append_castAdd_natAdd

/-- Splitting matrix columns is a bijection. -/
theorem splitColumns_bijective {R : Type} {n m : ℕ} :
    Function.Bijective
      (splitColumns : Matrix (Fin n) (Fin (m + m)) R → TwoBatchChallenge R n m) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨appendColumns, ?_, ?_⟩
  · exact appendColumns_splitColumns
  · exact splitColumns_appendColumns

/-- Split an ordinary `m + m`-sample public transcript into two `m`-sample blocks. -/
def splitBatchTranscript {R : Type} {n m : ℕ}
    (transcript : Matrix (Fin n) (Fin (m + m)) R × (Fin (m + m) → R)) :
    TwoBatchTranscript R n m :=
  (splitColumns transcript.1, splitOutput transcript.2)

/-- Concatenate a two-block transcript into an ordinary `m + m`-sample transcript. -/
def appendBatchTranscript {R : Type} {n m : ℕ}
    (transcript : TwoBatchTranscript R n m) :
    Matrix (Fin n) (Fin (m + m)) R × (Fin (m + m) → R) :=
  (appendColumns transcript.1, appendOutput transcript.2)

@[simp]
theorem splitBatch_appendBatch {R : Type} {n m : ℕ}
    (transcript : TwoBatchTranscript R n m) :
    splitBatchTranscript (appendBatchTranscript transcript) = transcript := by
  rcases transcript with ⟨challenge, output⟩
  simp [splitBatchTranscript, appendBatchTranscript]

@[simp]
theorem appendBatch_splitBatch {R : Type} {n m : ℕ}
    (transcript : Matrix (Fin n) (Fin (m + m)) R × (Fin (m + m) → R)) :
    appendBatchTranscript (splitBatchTranscript transcript) = transcript := by
  rcases transcript with ⟨challenge, output⟩
  simp [splitBatchTranscript, appendBatchTranscript]

/-- Transcript splitting is a bijection. -/
theorem splitBatchTranscript_bijective {R : Type} {n m : ℕ} :
    Function.Bijective
      (splitBatchTranscript :
        (Matrix (Fin n) (Fin (m + m)) R × (Fin (m + m) → R)) →
          TwoBatchTranscript R n m) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨appendBatchTranscript, ?_, ?_⟩
  · exact appendBatch_splitBatch
  · exact splitBatch_appendBatch

/-- Splitting commutes with vector--matrix multiplication. -/
theorem splitOutput_vecMul {R : Type} [NonUnitalNonAssocSemiring R]
    {n m : ℕ} (secret : Fin n → R) (matrix : Matrix (Fin n) (Fin (m + m)) R) :
    splitOutput (vecMul secret matrix) =
      (vecMul secret (splitColumns matrix).1, vecMul secret (splitColumns matrix).2) := by
  ext <;> rfl

/-- Splitting commutes with coordinatewise addition. -/
theorem splitOutput_add {R : Type} [Add R] {m : ℕ}
    (first second : Fin (m + m) → R) :
    splitOutput (first + second) = splitOutput first + splitOutput second := by
  ext <;> rfl

/-- Output probabilities of an IID vector factor coordinatewise. -/
theorem probOutput_sampleIID {R : Type} [Finite R] (length : ℕ)
    (sampler : ProbComp R) (output : Fin length → R) :
    Pr[= output | ProbComp.sampleIID length sampler] =
      ∏ i, Pr[= output i | sampler] := by
  letI : Fintype R := Fintype.ofFinite R
  letI : DecidableEq R := Classical.decEq R
  unfold ProbComp.sampleIID
  induction length with
  | zero =>
      have output_eq : output = Fin.elim0 := funext fun i ↦ i.elim0
      subst output_eq
      simp [Fin.mOfFn, probOutput_pure]
  | succ length ih =>
      simp only [Fin.mOfFn]
      rw [probOutput_bind_eq_sum_fintype]
      have inner : ∀ head : R,
          Pr[= output | Fin.mOfFn length (fun _ ↦ sampler) >>= fun tail ↦
            pure (Fin.cons (α := fun _ ↦ R) head tail)] =
          if head = output 0 then
            Pr[= Fin.tail output | Fin.mOfFn length fun _ ↦ sampler] else 0 := by
        intro head
        rw [probOutput_bind_eq_sum_fintype]
        have output_eq_cons : ∀ tail : Fin length → R,
            (output = Fin.cons (α := fun _ ↦ R) head tail) ↔
              (head = output 0 ∧ tail = Fin.tail output) := by
          intro tail
          constructor
          · intro h
            refine ⟨by rw [h, Fin.cons_zero], funext fun i ↦ ?_⟩
            have hi := congrFun h i.succ
            rw [Fin.cons_succ] at hi
            exact hi.symm
          · rintro ⟨rfl, rfl⟩
            exact (Fin.cons_self_tail output).symm
        by_cases hHead : head = output 0
        · rw [if_pos hHead]
          subst hHead
          simp only [probOutput_pure, output_eq_cons, true_and]
          simp [mul_ite]
        · rw [if_neg hHead]
          refine Finset.sum_eq_zero fun tail _ ↦ ?_
          rw [probOutput_pure, if_neg (fun h ↦ hHead ((output_eq_cons tail).mp h).1), mul_zero]
      simp only [inner, mul_ite, mul_zero]
      rw [Finset.sum_ite_eq' Finset.univ (output 0)
        (fun head ↦ Pr[= head | sampler] *
          Pr[= Fin.tail output | Fin.mOfFn length fun _ ↦ sampler]),
        if_pos (Finset.mem_univ _), ih, Fin.prod_univ_succ]
      rfl

/-- Splitting a uniformly sampled combined matrix gives two independent uniform blocks. -/
theorem splitColumns_uniform_evalDist {R : Type} [Finite R] [SampleableType R]
    {n m : ℕ} :
    𝒟[splitColumns <$> ($ᵗ Matrix (Fin n) (Fin (m + m)) R)] =
      𝒟[$ᵗ (TwoBatchChallenge R n m)] :=
  evalDist_map_bijective_uniform_cross
    (α := Matrix (Fin n) (Fin (m + m)) R)
    (β := TwoBatchChallenge R n m)
    splitColumns splitColumns_bijective

/-- Splitting an IID error vector of length `m + m` gives two independent IID vectors of
length `m`. -/
theorem splitOutput_sampleIID_evalDist {R : Type} [Finite R]
    (m : ℕ) (sampler : ProbComp R) :
    𝒟[splitOutput <$> ProbComp.sampleIID (m + m) sampler] =
      𝒟[pairedErrorSampler m sampler] := by
  refine evalDist_ext fun output ↦ ?_
  calc
    Pr[= output | splitOutput <$> ProbComp.sampleIID (m + m) sampler] =
        Pr[= appendOutput output | ProbComp.sampleIID (m + m) sampler] := by
      simpa using
        (probOutput_map_injective (ProbComp.sampleIID (m + m) sampler)
          splitOutput_bijective.injective (appendOutput output))
    _ = ∏ i : Fin (m + m), Pr[= appendOutput output i | sampler] :=
      probOutput_sampleIID (m + m) sampler (appendOutput output)
    _ = (∏ i : Fin m, Pr[= output.1 i | sampler]) *
          ∏ i : Fin m, Pr[= output.2 i | sampler] := by
      rw [Fin.prod_univ_add]
      congr 1
      · apply Finset.prod_congr rfl
        intro i _
        rw [appendOutput, Fin.append_left]
      · apply Finset.prod_congr rfl
        intro i _
        rw [appendOutput, Fin.append_right]
    _ = Pr[= output | pairedErrorSampler m sampler] := by
      symm
      simp [pairedErrorSampler, probOutput_sampleIID]

/-- The uniform branch of ordinary matrix LWE is the canonical uniform transcript sampler. -/
theorem batch_uniformDistr_eq_uniformSample {R : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (n samples : ℕ) (secretSampler : ProbComp (Fin n → R))
    (errorSampler : ProbComp R) :
    LearningWithErrors.uniformDistr
        (FormalProof4FHE.LWE.batchProblem n samples secretSampler errorSampler) =
      ($ᵗ (Matrix (Fin n) (Fin samples) R × (Fin samples → R))) := by
  unfold LearningWithErrors.uniformDistr FormalProof4FHE.LWE.batchProblem
  have uniformProduct :
      ($ᵗ (Matrix (Fin n) (Fin samples) R × (Fin samples → R)) :
        ProbComp (Matrix (Fin n) (Fin samples) R × (Fin samples → R))) =
      Prod.mk <$> ($ᵗ Matrix (Fin n) (Fin samples) R) <*>
        ($ᵗ (Fin samples → R)) := rfl
  rw [uniformProduct]
  simp [monad_norm]

/-- Splitting maps the ordinary uniform branch to the two-block uniform branch. -/
theorem split_uniform_branch_evalDist {R : Type}
    [Semiring R] [Finite R] [DecidableEq R] [SampleableType R]
    (n m : ℕ) (secretSampler : ProbComp (Fin n → R))
    (errorSampler : ProbComp R) :
    𝒟[LearningWithErrors.uniformDistr
          (FormalProof4FHE.LWE.batchProblem n (m + m) secretSampler errorSampler) >>=
        fun transcript ↦ pure (splitBatchTranscript transcript)] =
      𝒟[LearningWithErrors.uniformDistr
        (twoBatchProblem n m secretSampler errorSampler)] := by
  rw [batch_uniformDistr_eq_uniformSample,
    twoBatch_uniformDistr_eq_uniformSample]
  rw [show (do
      let transcript ←
        ($ᵗ (Matrix (Fin n) (Fin (m + m)) R × (Fin (m + m) → R)))
      pure (splitBatchTranscript transcript)) =
      splitBatchTranscript <$>
        ($ᵗ (Matrix (Fin n) (Fin (m + m)) R × (Fin (m + m) → R)) :
          ProbComp (Matrix (Fin n) (Fin (m + m)) R × (Fin (m + m) → R))) by
    simp [monad_norm]]
  exact evalDist_map_bijective_uniform_cross
    (α := Matrix (Fin n) (Fin (m + m)) R × (Fin (m + m) → R))
    (β := TwoBatchTranscript R n m)
    splitBatchTranscript splitBatchTranscript_bijective

/-- Deterministically form a real two-block LWE transcript. -/
def twoBatchRealTranscript {R : Type} [Semiring R] {n m : ℕ}
    (challenge : TwoBatchChallenge R n m) (secret : Fin n → R)
    (errors : TwoBatchOutput R m) : TwoBatchTranscript R n m :=
  (challenge,
    (vecMul secret challenge.1 + errors.1,
      vecMul secret challenge.2 + errors.2))

/-- Splitting an ordinary real transcript splits both its signal and error coordinates. -/
theorem splitBatchTranscript_real {R : Type} [Semiring R] {n m : ℕ}
    (challenge : Matrix (Fin n) (Fin (m + m)) R)
    (secret : Fin n → R) (error : Fin (m + m) → R) :
    splitBatchTranscript (challenge, vecMul secret challenge + error) =
      twoBatchRealTranscript (splitColumns challenge) secret (splitOutput error) := by
  apply Prod.ext
  · rfl
  · simp only [splitBatchTranscript, twoBatchRealTranscript, splitOutput_add,
      splitOutput_vecMul]
    apply Prod.ext <;> rfl

/-- Splitting maps the ordinary real branch to the two-block real branch. -/
theorem split_real_branch_evalDist {R : Type}
    [Semiring R] [Finite R] [DecidableEq R] [SampleableType R]
    (n m : ℕ) (secretSampler : ProbComp (Fin n → R))
    (errorSampler : ProbComp R) :
    𝒟[LearningWithErrors.distr
          (FormalProof4FHE.LWE.batchProblem n (m + m) secretSampler errorSampler) >>=
        fun transcript ↦ pure (splitBatchTranscript transcript)] =
      𝒟[LearningWithErrors.distr
        (twoBatchProblem n m secretSampler errorSampler)] := by
  let ordinaryChallenge : ProbComp (Matrix (Fin n) (Fin (m + m)) R) :=
    $ᵗ Matrix (Fin n) (Fin (m + m)) R
  let mappedChallenge : ProbComp (TwoBatchChallenge R n m) :=
    splitColumns <$> ordinaryChallenge
  let targetChallenge : ProbComp (TwoBatchChallenge R n m) :=
    $ᵗ (TwoBatchChallenge R n m)
  let ordinaryErrors : ProbComp (Fin (m + m) → R) :=
    ProbComp.sampleIID (m + m) errorSampler
  let mappedErrors : ProbComp (TwoBatchOutput R m) :=
    splitOutput <$> ordinaryErrors
  let targetErrors : ProbComp (TwoBatchOutput R m) :=
    pairedErrorSampler m errorSampler
  have hChallenge : 𝒟[mappedChallenge] = 𝒟[targetChallenge] := by
    simpa only [mappedChallenge, ordinaryChallenge] using
      (splitColumns_uniform_evalDist (R := R) (n := n) (m := m))
  have hErrors : 𝒟[mappedErrors] = 𝒟[targetErrors] := by
    simpa only [mappedErrors, ordinaryErrors, targetErrors] using
      (splitOutput_sampleIID_evalDist m errorSampler)
  have left_eq :
      (LearningWithErrors.distr
          (FormalProof4FHE.LWE.batchProblem n (m + m) secretSampler errorSampler) >>=
        fun transcript ↦ pure (splitBatchTranscript transcript)) =
      (mappedChallenge >>= fun challenge ↦
        secretSampler >>= fun secret ↦
        mappedErrors >>= fun errors ↦
        pure (twoBatchRealTranscript challenge secret errors)) := by
    simp [LearningWithErrors.distr, FormalProof4FHE.LWE.batchProblem,
      mappedChallenge, ordinaryChallenge, mappedErrors, ordinaryErrors,
      splitBatchTranscript_real, bind_assoc, monad_norm]
  have right_eq :
      LearningWithErrors.distr (twoBatchProblem n m secretSampler errorSampler) =
      (targetChallenge >>= fun challenge ↦
        secretSampler >>= fun secret ↦
        targetErrors >>= fun errors ↦
        pure (twoBatchRealTranscript challenge secret errors)) := by
    simp [LearningWithErrors.distr, twoBatchProblem, targetChallenge, targetErrors,
      pairedErrorSampler, twoBatchRealTranscript, monad_norm]
  rw [left_eq, right_eq]
  calc
    _ = 𝒟[targetChallenge >>= fun challenge ↦
        secretSampler >>= fun secret ↦
        mappedErrors >>= fun errors ↦
        pure (twoBatchRealTranscript challenge secret errors)] :=
      evalDist_bind_eq_of_evalDist_eq hChallenge _
    _ = _ := by
      refine evalDist_bind_congr' targetChallenge fun challenge ↦ ?_
      refine evalDist_bind_congr' secretSampler fun secret ↦ ?_
      exact evalDist_bind_eq_of_evalDist_eq hErrors _

/-- Preprocess an ordinary `m + m`-sample transcript for a two-block distinguisher. -/
def ordinaryReduction {R : Type} [Semiring R] [DecidableEq R] [SampleableType R]
    {n m : ℕ}
    {secretSampler : ProbComp (Fin n → R)} {errorSampler : ProbComp R}
    (adversary : LearningWithErrors.Adversary
      (twoBatchProblem n m secretSampler errorSampler)) :
    LearningWithErrors.Adversary
      (FormalProof4FHE.LWE.batchProblem n (m + m) secretSampler errorSampler) :=
  fun transcript ↦ adversary (splitBatchTranscript transcript)

/-- The real game of a two-block distinguisher is the real ordinary-LWE game of its preprocessing
reduction. -/
theorem twoBatch_game0_evalDist_eq_batch {R : Type}
    [Semiring R] [Finite R] [DecidableEq R] [SampleableType R]
    (n m : ℕ) (secretSampler : ProbComp (Fin n → R))
    (errorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (twoBatchProblem n m secretSampler errorSampler)) :
    𝒟[LearningWithErrors.game0
        (twoBatchProblem n m secretSampler errorSampler) adversary] =
      𝒟[LearningWithErrors.game0
        (FormalProof4FHE.LWE.batchProblem n (m + m) secretSampler errorSampler)
        (ordinaryReduction (secretSampler := secretSampler)
          (errorSampler := errorSampler) adversary)] := by
  rw [LearningWithErrors.game0, LearningWithErrors.game0]
  simp only [ordinaryReduction]
  rw [show (LearningWithErrors.distr
        (FormalProof4FHE.LWE.batchProblem n (m + m) secretSampler errorSampler) >>=
      fun transcript ↦ adversary (splitBatchTranscript transcript)) =
      ((LearningWithErrors.distr
          (FormalProof4FHE.LWE.batchProblem n (m + m) secretSampler errorSampler) >>=
        fun transcript ↦ pure (splitBatchTranscript transcript)) >>= adversary) by
    simp [bind_assoc, monad_norm]]
  rw [evalDist_bind, evalDist_bind,
    split_real_branch_evalDist n m secretSampler errorSampler]

/-- Uniform-game counterpart of `twoBatch_game0_evalDist_eq_batch`. -/
theorem twoBatch_game1_evalDist_eq_batch {R : Type}
    [Semiring R] [Finite R] [DecidableEq R] [SampleableType R]
    (n m : ℕ) (secretSampler : ProbComp (Fin n → R))
    (errorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (twoBatchProblem n m secretSampler errorSampler)) :
    𝒟[LearningWithErrors.game1
        (twoBatchProblem n m secretSampler errorSampler) adversary] =
      𝒟[LearningWithErrors.game1
        (FormalProof4FHE.LWE.batchProblem n (m + m) secretSampler errorSampler)
        (ordinaryReduction (secretSampler := secretSampler)
          (errorSampler := errorSampler) adversary)] := by
  rw [LearningWithErrors.game1, LearningWithErrors.game1]
  simp only [ordinaryReduction]
  rw [show (LearningWithErrors.uniformDistr
        (FormalProof4FHE.LWE.batchProblem n (m + m) secretSampler errorSampler) >>=
      fun transcript ↦ adversary (splitBatchTranscript transcript)) =
      ((LearningWithErrors.uniformDistr
          (FormalProof4FHE.LWE.batchProblem n (m + m) secretSampler errorSampler) >>=
        fun transcript ↦ pure (splitBatchTranscript transcript)) >>= adversary) by
    simp [bind_assoc, monad_norm]]
  rw [evalDist_bind, evalDist_bind,
    split_uniform_branch_evalDist n m secretSampler errorSampler]

/-- A two-block LWE distinguisher and its ordinary `m + m`-sample preprocessing reduction have
exactly equal advantage. -/
theorem twoBatch_advantage_eq_batch {R : Type}
    [Semiring R] [Finite R] [DecidableEq R] [SampleableType R]
    (n m : ℕ) (secretSampler : ProbComp (Fin n → R))
    (errorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (twoBatchProblem n m secretSampler errorSampler)) :
    LearningWithErrors.advantage
        (twoBatchProblem n m secretSampler errorSampler) adversary =
      LearningWithErrors.advantage
        (FormalProof4FHE.LWE.batchProblem n (m + m) secretSampler errorSampler)
        (ordinaryReduction (secretSampler := secretSampler)
          (errorSampler := errorSampler) adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage,
    FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (twoBatch_game0_evalDist_eq_batch n m secretSampler errorSampler adversary) true,
    evalDist_ext_iff.mp
      (twoBatch_game1_evalDist_eq_batch n m secretSampler errorSampler adversary) true]

/-- The complete Theorem 6 reduction to ordinary LWE with `m + m` samples. -/
theorem advantage_eq_batch {R : Type}
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
        (FormalProof4FHE.LWE.batchProblem n (m + m)
          prefixSampler largeErrorSampler)
        (ordinaryReduction (secretSampler := prefixSampler)
          (errorSampler := largeErrorSampler)
          (reduction suffixSampler extraErrorSampler adversary)) := by
  calc
    _ = LearningWithErrors.advantage
        (twoBatchProblem n m prefixSampler largeErrorSampler)
        (reduction suffixSampler extraErrorSampler adversary) :=
      advantage_eq_twoBatch n k m prefixSampler suffixSampler
        smallErrorSampler largeErrorSampler extraErrorSampler
        hConvolution hSuffix hExtraError adversary
    _ = _ := twoBatch_advantage_eq_batch n m prefixSampler largeErrorSampler
      (reduction suffixSampler extraErrorSampler adversary)

/-- `ZMod q` specialization of the complete reduction to ordinary `m + m`-sample LWE. -/
theorem zmod_advantage_eq_batch {q : ℕ} [NeZero q]
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
        (FormalProof4FHE.LWE.zmodBatchProblem n (m + m) q largeErrorSampler)
        (ordinaryReduction
          (secretSampler := ($ᵗ (Fin n → ZMod q)))
          (errorSampler := largeErrorSampler)
          (reduction ($ᵗ (Fin k → ZMod q)) extraErrorSampler adversary)) := by
  simpa only [zmodProblem, FormalProof4FHE.LWE.zmodBatchProblem] using
    (advantage_eq_batch n k m
      ($ᵗ (Fin n → ZMod q)) ($ᵗ (Fin k → ZMod q))
      smallErrorSampler largeErrorSampler extraErrorSampler
      hConvolution (by simp) hExtraError adversary)

end FormalProof4FHE.SharedRandomness
