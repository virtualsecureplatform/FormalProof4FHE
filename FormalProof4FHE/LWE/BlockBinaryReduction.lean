/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.BlockBinary
import FormalProof4FHE.Probability.FiniteProduct
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-!
# Reduction for LWE with Block-Binary Secrets

This file gives a concrete, finite-game version of the weak-secret reduction used in
ePrint 2023/958.  It factors a structured public matrix as `C * B + Z`, extracts the compact
block key through `key ᵥ* C`, absorbs the correlated term `key ᵥ* Z` into the target error, and
then invokes ordinary LWE on `(B, (key ᵥ* C) ᵥ* B + error)`.

The sharp final bound separates three ingredients:

* one signed, randomized-row ordinary narrow-error LWE reduction for pseudorandomizing
  `C * B + Z`, retaining cancellation between masking sides and rows;
* ordinary wide-error LWE for the extracted secret;
* one exact joint statistical gap for noise absorption and extraction.

The noise-absorption distance is left explicit.  For the Gaussian parameters in the paper this
is the analytic statement controlled by the ratio of the narrow and wide errors; keeping it as a
finite `tvDist` makes the computational reduction independent of a particular Gaussian library.
A convenience corollary splits the joint gap using the tight finite leftover-hash term with
numerator `|R| ^ extractedDimension - 1`, and all flagship bounds are capped at one.
-/

open Matrix OracleComp

namespace FormalProof4FHE.BlockBinary

/-- Independent uniform sampling agrees with the uniform sampler on a product type, regardless of
which discoverable `SampleableType` instance supplies the latter. -/
theorem evalDist_independent_uniform_product {First Second : Type}
    [Fintype First] [SampleableType First]
    [Fintype Second] [SampleableType Second] :
    𝒟[do
      let first ← $ᵗ First
      let second ← $ᵗ Second
      return (first, second)] =
      𝒟[$ᵗ (First × Second)] := by
  rw [show (do
      let first ← $ᵗ First
      let second ← $ᵗ Second
      return (first, second)) =
      Prod.mk <$> ($ᵗ First) <*> ($ᵗ Second) by simp [monad_norm]]
  apply evalDist_ext
  intro output
  simp only [probOutput_seq_map_prod_mk_eq_mul, probOutput_uniformSample,
    Fintype.card_prod, Nat.cast_mul]
  rw [ENNReal.mul_inv] <;> simp

/-- A matrix of independent narrow errors, one vector for every output row. -/
def matrixErrorSampler {R : Type} (rowCount sampleCount : ℕ)
    (errorSampler : ProbComp R) :
    ProbComp (Matrix (Fin rowCount) (Fin sampleCount) R) :=
  Matrix.of <$> ProbComp.sampleIID rowCount
    (ProbComp.sampleIID sampleCount errorSampler)

/-- The matrix-LWE problem used to mask the structured challenge `C * B + Z`.

It is `rowCount` parallel ordinary-LWE secrets sharing the public matrix `B`.  A standard row
hybrid reduces this problem to ordinary LWE with a factor `rowCount`.  An intermediate theorem
keeps the problem explicit so both challenge-masking calls remain visible, and the final theorem
applies the row hybrid to each call. -/
def matrixMaskProblem {R : Type} [Semiring R] [DecidableEq R] [SampleableType R]
    (rowCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler : ProbComp R) :
    LearningWithErrors.Problem
      (Matrix (Fin extractedDimension) (Fin sampleCount) R)
      (Matrix (Fin rowCount) (Fin extractedDimension) R)
      (Matrix (Fin rowCount) (Fin sampleCount) R) where
  sampleChallenge :=
    $ᵗ Matrix (Fin extractedDimension) (Fin sampleCount) R
  sampleSecret :=
    $ᵗ Matrix (Fin rowCount) (Fin extractedDimension) R
  sampleError := matrixErrorSampler rowCount sampleCount narrowErrorSampler
  noiseless := fun left right ↦ left * right
  sampleUniform := $ᵗ Matrix (Fin rowCount) (Fin sampleCount) R

/-- Canonical structured real transcript.  The sampling order puts `(C, key)` first so the
leftover-hash step can be applied directly. -/
def structuredRealTranscript {R : Type} [Semiring R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R) :
    ProbComp
      (Matrix (Fin (blockCount * blockLength)) (Fin sampleCount) R ×
        (Fin sampleCount → R)) := do
  let extractor ←
    $ᵗ Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R
  let key ← $ᵗ (Key blockLength blockCount)
  let sourceMatrix ←
    $ᵗ Matrix (Fin extractedDimension) (Fin sampleCount) R
  let matrixError ← matrixErrorSampler (blockCount * blockLength)
    sampleCount narrowErrorSampler
  let wideError ← ProbComp.sampleIID sampleCount wideErrorSampler
  let challenge := extractor * sourceMatrix + matrixError
  return (challenge, vecMul (expand R key) challenge + wideError)

/-- Continue from an extractor seed/output pair to the public target transcript. -/
def extractorContinuation {R : Type} [Semiring R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (pair :
      Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R ×
        (Fin extractedDimension → R)) :
    ProbComp
      (Matrix (Fin (blockCount * blockLength)) (Fin sampleCount) R ×
        (Fin sampleCount → R)) := do
  let sourceMatrix ←
    $ᵗ Matrix (Fin extractedDimension) (Fin sampleCount) R
  let matrixError ← matrixErrorSampler (blockCount * blockLength)
    sampleCount narrowErrorSampler
  let wideError ← ProbComp.sampleIID sampleCount wideErrorSampler
  return (pair.1 * sourceMatrix + matrixError,
    vecMul pair.2 sourceMatrix + wideError)

/-- Structured transcript after the correlated narrow-noise term has been absorbed. -/
def noiseIdealTranscript {R : Type}
    [Ring R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R) :
    ProbComp
      (Matrix (Fin (blockCount * blockLength)) (Fin sampleCount) R ×
        (Fin sampleCount → R)) :=
  FormalProof4FHE.LeftoverHash.hashed
      (extractorHash (R := R) (blockLength := blockLength)
        (blockCount := blockCount) (extractedDimension := extractedDimension)) >>=
    extractorContinuation blockLength blockCount extractedDimension sampleCount
      narrowErrorSampler wideErrorSampler

/-- The same transcript with a genuinely uniform extracted secret. -/
def extractedTranscript {R : Type}
    [Ring R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R) :
    ProbComp
      (Matrix (Fin (blockCount * blockLength)) (Fin sampleCount) R ×
        (Fin sampleCount → R)) := do
  let extractor ←
    $ᵗ Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R
  let extractedSecret ← $ᵗ (Fin extractedDimension → R)
  extractorContinuation blockLength blockCount extractedDimension sampleCount
    narrowErrorSampler wideErrorSampler (extractor, extractedSecret)

/-- The structured challenge paired with an independent uniform right-hand side. -/
def structuredUniformTranscript {R : Type}
    [Semiring R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler : ProbComp R) :
    ProbComp
      (Matrix (Fin (blockCount * blockLength)) (Fin sampleCount) R ×
        (Fin sampleCount → R)) := do
  let extractor ←
    $ᵗ Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R
  let sourceMatrix ←
    $ᵗ Matrix (Fin extractedDimension) (Fin sampleCount) R
  let matrixError ← matrixErrorSampler (blockCount * blockLength)
    sampleCount narrowErrorSampler
  let uniform ← $ᵗ (Fin sampleCount → R)
  return (extractor * sourceMatrix + matrixError, uniform)

/-- Exact finite statistical cost of absorbing `expand(key) ᵥ* Z` into the wide error. -/
noncomputable def noiseAbsorptionGap {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R) : ℝ :=
  tvDist
    (structuredRealTranscript blockLength blockCount extractedDimension sampleCount
      narrowErrorSampler wideErrorSampler)
    (noiseIdealTranscript blockLength blockCount extractedDimension sampleCount
      narrowErrorSampler wideErrorSampler)

/-- Exact joint statistical cost of both noise absorption and block-key extraction.

Keeping this distance unsplit is at least as sharp as paying for the two transitions separately,
and can be strictly sharper when their signed deviations cancel. -/
noncomputable def jointStatisticalGap {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R) : ℝ :=
  tvDist
    (structuredRealTranscript blockLength blockCount extractedDimension sampleCount
      narrowErrorSampler wideErrorSampler)
    (extractedTranscript blockLength blockCount extractedDimension sampleCount
      narrowErrorSampler wideErrorSampler)

/-- The block-key leftover-hash distance survives arbitrary public postprocessing. -/
theorem tvDist_noiseIdeal_extracted_le {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R) :
    tvDist
        (noiseIdealTranscript blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler)
        (extractedTranscript blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler) ≤
      Real.sqrt
          ((Fintype.card R : ℝ) ^ extractedDimension /
            (blockLength + 1 : ℝ) ^ blockCount) /
        2 := by
  let continuation :=
    extractorContinuation (R := R) blockLength blockCount extractedDimension sampleCount
      narrowErrorSampler wideErrorSampler
  let independentIdeal : ProbComp
      (Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R ×
        (Fin extractedDimension → R)) := do
    let extractor ←
      $ᵗ Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R
    let extractedSecret ← $ᵗ (Fin extractedDimension → R)
    return (extractor, extractedSecret)
  have hbase : 𝒟[independentIdeal] =
      𝒟[(FormalProof4FHE.LeftoverHash.ideal : ProbComp
        (Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R ×
          (Fin extractedDimension → R)))] := by
    exact evalDist_independent_uniform_product
  have hright : 𝒟[independentIdeal >>= continuation] =
      𝒟[(FormalProof4FHE.LeftoverHash.ideal : ProbComp
          (Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R ×
            (Fin extractedDimension → R))) >>= continuation] := by
    simp only [evalDist_bind]
    rw [hbase]
  have hdata := tvDist_bind_right_le continuation
    (FormalProof4FHE.LeftoverHash.hashed
      (extractorHash (R := R) (blockLength := blockLength)
        (blockCount := blockCount) (extractedDimension := extractedDimension)))
    (FormalProof4FHE.LeftoverHash.ideal : ProbComp
      (Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R ×
        (Fin extractedDimension → R)))
  have hlhl := extractorHash_leftover (R := R)
    blockLength blockCount extractedDimension
  have hcanonical :
      tvDist
          (FormalProof4FHE.LeftoverHash.hashed
              (extractorHash (R := R) (blockLength := blockLength)
                (blockCount := blockCount) (extractedDimension := extractedDimension)) >>=
            continuation)
          (independentIdeal >>= continuation) ≤
        Real.sqrt
            ((Fintype.card R : ℝ) ^ extractedDimension /
              (blockLength + 1 : ℝ) ^ blockCount) /
          2 := by
    rw [show tvDist
        (FormalProof4FHE.LeftoverHash.hashed
            (extractorHash (R := R) (blockLength := blockLength)
              (blockCount := blockCount) (extractedDimension := extractedDimension)) >>=
          continuation)
        (independentIdeal >>= continuation) =
        tvDist
          (FormalProof4FHE.LeftoverHash.hashed
              (extractorHash (R := R) (blockLength := blockLength)
                (blockCount := blockCount) (extractedDimension := extractedDimension)) >>=
            continuation)
          ((FormalProof4FHE.LeftoverHash.ideal : ProbComp
              (Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R ×
                (Fin extractedDimension → R))) >>= continuation) by
      unfold tvDist
      rw [hright]]
    exact hdata.trans hlhl
  simpa [noiseIdealTranscript, extractedTranscript, continuation,
    independentIdeal, bind_assoc] using hcanonical

/-- Tight block-key leftover-hash distance after arbitrary public postprocessing. -/
theorem tvDist_noiseIdeal_extracted_le_tight {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R) :
    tvDist
        (noiseIdealTranscript blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler)
        (extractedTranscript blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler) ≤
      Real.sqrt
          (((Fintype.card R : ℝ) ^ extractedDimension - 1) /
            (blockLength + 1 : ℝ) ^ blockCount) /
        2 := by
  let continuation :=
    extractorContinuation (R := R) blockLength blockCount extractedDimension sampleCount
      narrowErrorSampler wideErrorSampler
  let independentIdeal : ProbComp
      (Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R ×
        (Fin extractedDimension → R)) := do
    let extractor ←
      $ᵗ Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R
    let extractedSecret ← $ᵗ (Fin extractedDimension → R)
    return (extractor, extractedSecret)
  have hbase : 𝒟[independentIdeal] =
      𝒟[(FormalProof4FHE.LeftoverHash.ideal : ProbComp
        (Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R ×
          (Fin extractedDimension → R)))] := by
    exact evalDist_independent_uniform_product
  have hright : 𝒟[independentIdeal >>= continuation] =
      𝒟[(FormalProof4FHE.LeftoverHash.ideal : ProbComp
          (Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R ×
            (Fin extractedDimension → R))) >>= continuation] := by
    simp only [evalDist_bind]
    rw [hbase]
  have hdata := tvDist_bind_right_le continuation
    (FormalProof4FHE.LeftoverHash.hashed
      (extractorHash (R := R) (blockLength := blockLength)
        (blockCount := blockCount) (extractedDimension := extractedDimension)))
    (FormalProof4FHE.LeftoverHash.ideal : ProbComp
      (Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R ×
        (Fin extractedDimension → R)))
  have hlhl := extractorHash_leftover_tight (R := R)
    blockLength blockCount extractedDimension
  have hcanonical :
      tvDist
          (FormalProof4FHE.LeftoverHash.hashed
              (extractorHash (R := R) (blockLength := blockLength)
                (blockCount := blockCount) (extractedDimension := extractedDimension)) >>=
            continuation)
          (independentIdeal >>= continuation) ≤
        Real.sqrt
            (((Fintype.card R : ℝ) ^ extractedDimension - 1) /
              (blockLength + 1 : ℝ) ^ blockCount) /
          2 := by
    rw [show tvDist
        (FormalProof4FHE.LeftoverHash.hashed
            (extractorHash (R := R) (blockLength := blockLength)
              (blockCount := blockCount) (extractedDimension := extractedDimension)) >>=
          continuation)
        (independentIdeal >>= continuation) =
        tvDist
          (FormalProof4FHE.LeftoverHash.hashed
              (extractorHash (R := R) (blockLength := blockLength)
                (blockCount := blockCount) (extractedDimension := extractedDimension)) >>=
            continuation)
          ((FormalProof4FHE.LeftoverHash.ideal : ProbComp
              (Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R ×
                (Fin extractedDimension → R))) >>= continuation) by
      unfold tvDist
      rw [hright]]
    exact hdata.trans hlhl
  simpa [noiseIdealTranscript, extractedTranscript, continuation,
    independentIdeal, bind_assoc] using hcanonical

set_option maxHeartbeats 400000 in
/-- The exact joint statistical gap is bounded by noise absorption plus the tight finite
leftover-hash term. -/
theorem jointStatisticalGap_le_noise_add_leftover_tight {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R) :
    jointStatisticalGap blockLength blockCount extractedDimension sampleCount
        narrowErrorSampler wideErrorSampler ≤
      noiseAbsorptionGap blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler +
        Real.sqrt
            (((Fintype.card R : ℝ) ^ extractedDimension - 1) /
              (blockLength + 1 : ℝ) ^ blockCount) /
          2 := by
  unfold jointStatisticalGap noiseAbsorptionGap
  apply le_trans (tvDist_triangle _
    (noiseIdealTranscript blockLength blockCount extractedDimension sampleCount
      narrowErrorSampler wideErrorSampler) _)
  apply add_le_add
  · exact le_rfl
  · exact tvDist_noiseIdeal_extracted_le_tight blockLength blockCount extractedDimension
      sampleCount narrowErrorSampler wideErrorSampler

/-- Reduction used for the real-side challenge-masking hop. -/
def realMaskReduction {R : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)) :
    LearningWithErrors.Adversary
      (matrixMaskProblem (R := R) (blockCount * blockLength)
        extractedDimension sampleCount narrowErrorSampler) :=
  fun sample ↦ do
    let key ← $ᵗ (Key blockLength blockCount)
    let wideError ← ProbComp.sampleIID sampleCount wideErrorSampler
    adversary (sample.2, vecMul (expand R key) sample.2 + wideError)

/-- Reduction used for the uniform-side challenge-masking hop. -/
def uniformMaskReduction {R : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem (R := R) blockLength blockCount sampleCount
        wideErrorSampler)) :
    LearningWithErrors.Adversary
      (matrixMaskProblem (R := R) (blockCount * blockLength)
        extractedDimension sampleCount narrowErrorSampler) :=
  fun sample ↦ do
    let uniform ← $ᵗ (Fin sampleCount → R)
    adversary (sample.2, uniform)

/-- Choose between a positive Boolean computation and the negation of a negative one.
Its acceptance probability is the signed average used to preserve cancellation between two
hybrid gaps. -/
def signedChoice (positive negative : ProbComp Bool) : ProbComp Bool := do
  let choosePositive ← $ᵗ Bool
  if choosePositive then positive else (! ·) <$> negative

/-- One matrix-mask distinguisher combining both masking hops with their correct signs. -/
def combinedMaskReduction {R : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)) :
    LearningWithErrors.Adversary
      (matrixMaskProblem (R := R) (blockCount * blockLength)
        extractedDimension sampleCount narrowErrorSampler) :=
  fun sample ↦ signedChoice
    (uniformMaskReduction blockLength blockCount extractedDimension sampleCount
      narrowErrorSampler wideErrorSampler adversary sample)
    (realMaskReduction blockLength blockCount extractedDimension sampleCount
      narrowErrorSampler wideErrorSampler adversary sample)

/-- Independent sampling commutes with the fair signed choice. -/
theorem evalDist_bind_signedChoice {Sample : Type}
    (samples : ProbComp Sample) (positive negative : Sample → ProbComp Bool) :
    𝒟[samples >>= fun sample ↦ signedChoice (positive sample) (negative sample)] =
      𝒟[signedChoice (samples >>= positive) (samples >>= negative)] := by
  let choices : ProbComp Bool := $ᵗ Bool
  unfold signedChoice
  change 𝒟[samples >>= fun sample ↦
      choices >>= fun choosePositive ↦
        if choosePositive then positive sample else (! ·) <$> negative sample] = _
  calc
    _ = 𝒟[choices >>= fun choosePositive ↦
        samples >>= fun sample ↦
          if choosePositive then positive sample else (! ·) <$> negative sample] :=
      OracleComp.DeferredSampling.evalDist_bind_comm samples choices _
    _ = _ := by
      apply evalDist_bind_congr' choices
      intro choosePositive
      cases choosePositive <;> simp

/-- Acceptance probability of a signed choice, in real-valued form. -/
theorem probOutput_true_signedChoice (positive negative : ProbComp Bool) :
    (Pr[= true | signedChoice positive negative]).toReal =
      ((Pr[= true | positive]).toReal + 1 - (Pr[= true | negative]).toReal) / 2 := by
  have hformula : Pr[= true | signedChoice positive negative] =
      (Pr[= true | positive] + Pr[= false | negative]) / 2 := by
    simp [signedChoice, probOutput_bind_uniformBool]
  have hfalse : Pr[= false | negative] = 1 - Pr[= true | negative] := by
    simp [probOutput_false_eq_sub]
  rw [hformula, hfalse, ENNReal.toReal_div,
    ENNReal.toReal_add probOutput_ne_top (ENNReal.sub_ne_top ENNReal.one_ne_top),
    ENNReal.toReal_sub_of_le probOutput_le_one ENNReal.one_ne_top]
  simp only [ENNReal.toReal_one, ENNReal.toReal_ofNat]
  ring

/-- Real-valued output probability of a finite uniform mixture. -/
theorem probOutput_bind_uniform_fintype_toReal {Index Output : Type}
    [Fintype Index] [Nonempty Index] [SampleableType Index]
    (continuation : Index → ProbComp Output) (output : Output) :
    (Pr[= output | do
      let index ← $ᵗ Index
      continuation index]).toReal =
      (∑ index, (Pr[= output | continuation index]).toReal) /
        (Fintype.card Index : ℝ) := by
  rw [probOutput_bind_eq_sum_fintype,
    ENNReal.toReal_sum (fun index _ ↦ ENNReal.mul_ne_top
      (by simp) (probOutput_ne_top (mx := continuation index) (x := output)))]
  simp_rw [probOutput_uniformSample, ENNReal.toReal_mul, ENNReal.toReal_inv,
    ENNReal.toReal_natCast]
  rw [← Finset.mul_sum]
  field_simp

/-- Ordinary-LWE reduction for the extracted-secret hop. -/
def extractedLWReduction {R : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)) :
    LearningWithErrors.Adversary
      (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
        ($ᵗ (Fin extractedDimension → R)) wideErrorSampler) :=
  fun sample ↦ do
    let extractor ←
      $ᵗ Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R
    let matrixError ← matrixErrorSampler (blockCount * blockLength)
      sampleCount narrowErrorSampler
    adversary (extractor * sample.1 + matrixError, sample.2)

/-! ## Exact branch laws for the three reductions -/

/-- On its real branch, the matrix-mask reduction produces the canonical structured real
transcript. -/
theorem evalDist_matrixMask_game0_real {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)) :
    𝒟[LearningWithErrors.game0
        (matrixMaskProblem (R := R) (blockCount * blockLength)
          extractedDimension sampleCount narrowErrorSampler)
        (realMaskReduction blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler adversary)] =
      𝒟[structuredRealTranscript blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler >>= adversary] := by
  let sourceMatrices :
      ProbComp (Matrix (Fin extractedDimension) (Fin sampleCount) R) :=
    $ᵗ Matrix (Fin extractedDimension) (Fin sampleCount) R
  let extractors :
      ProbComp
        (Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R) :=
    $ᵗ Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R
  let matrixErrors :
      ProbComp (Matrix (Fin (blockCount * blockLength)) (Fin sampleCount) R) :=
    matrixErrorSampler (blockCount * blockLength) sampleCount narrowErrorSampler
  let keys : ProbComp (Key blockLength blockCount) :=
    $ᵗ (Key blockLength blockCount)
  let wideErrors : ProbComp (Fin sampleCount → R) :=
    ProbComp.sampleIID sampleCount wideErrorSampler
  let finish
      (sourceMatrix : Matrix (Fin extractedDimension) (Fin sampleCount) R)
      (extractor :
        Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R)
      (matrixError :
        Matrix (Fin (blockCount * blockLength)) (Fin sampleCount) R)
      (key : Key blockLength blockCount) (wideError : Fin sampleCount → R) :
      ProbComp Bool :=
    let challenge := extractor * sourceMatrix + matrixError
    adversary (challenge, vecMul (expand R key) challenge + wideError)
  simp only [LearningWithErrors.game0, LearningWithErrors.distr,
    matrixMaskProblem, realMaskReduction, structuredRealTranscript, bind_assoc]
  change 𝒟[sourceMatrices >>= fun sourceMatrix ↦
      extractors >>= fun extractor ↦
      matrixErrors >>= fun matrixError ↦
      keys >>= fun key ↦
      wideErrors >>= fun wideError ↦
      finish sourceMatrix extractor matrixError key wideError] =
    𝒟[extractors >>= fun extractor ↦
      keys >>= fun key ↦
      sourceMatrices >>= fun sourceMatrix ↦
      matrixErrors >>= fun matrixError ↦
      wideErrors >>= fun wideError ↦
      finish sourceMatrix extractor matrixError key wideError]
  calc
    _ = 𝒟[extractors >>= fun extractor ↦
        sourceMatrices >>= fun sourceMatrix ↦
        matrixErrors >>= fun matrixError ↦
        keys >>= fun key ↦
        wideErrors >>= fun wideError ↦
        finish sourceMatrix extractor matrixError key wideError] :=
      OracleComp.DeferredSampling.evalDist_bind_comm sourceMatrices extractors _
    _ = 𝒟[extractors >>= fun extractor ↦
        sourceMatrices >>= fun sourceMatrix ↦
        keys >>= fun key ↦
        matrixErrors >>= fun matrixError ↦
        wideErrors >>= fun wideError ↦
        finish sourceMatrix extractor matrixError key wideError] := by
      apply evalDist_bind_congr' extractors
      intro extractor
      apply evalDist_bind_congr' sourceMatrices
      intro sourceMatrix
      exact OracleComp.DeferredSampling.evalDist_bind_comm matrixErrors keys _
    _ = _ := by
      apply evalDist_bind_congr' extractors
      intro extractor
      exact OracleComp.DeferredSampling.evalDist_bind_comm sourceMatrices keys _

/-- On its uniform branch, the real-side matrix-mask reduction is exactly the real block-binary
LWE game. -/
theorem evalDist_matrixMask_game1_real {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)) :
    𝒟[LearningWithErrors.game1
        (matrixMaskProblem (R := R) (blockCount * blockLength)
          extractedDimension sampleCount narrowErrorSampler)
        (realMaskReduction blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler adversary)] =
      𝒟[LearningWithErrors.game0
        (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)
        adversary] := by
  let sourceMatrices :
      ProbComp (Matrix (Fin extractedDimension) (Fin sampleCount) R) :=
    $ᵗ Matrix (Fin extractedDimension) (Fin sampleCount) R
  let targetReal : ProbComp Bool := do
    let challenge ←
      $ᵗ Matrix (Fin (blockCount * blockLength)) (Fin sampleCount) R
    let key ← $ᵗ (Key blockLength blockCount)
    let wideError ← ProbComp.sampleIID sampleCount wideErrorSampler
    adversary (challenge, vecMul (expand R key) challenge + wideError)
  simp only [LearningWithErrors.game0, LearningWithErrors.game1,
    LearningWithErrors.distr, LearningWithErrors.uniformDistr,
    matrixMaskProblem, realMaskReduction, problem, bind_assoc]
  change 𝒟[sourceMatrices >>= fun _ ↦ targetReal] = 𝒟[targetReal]
  exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
    sourceMatrices (by simp [sourceMatrices]) targetReal

/-- On its real branch, the uniform-side matrix-mask reduction produces a structured challenge
and an independent uniform right-hand side. -/
theorem evalDist_matrixMask_game0_uniform {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)) :
    𝒟[LearningWithErrors.game0
        (matrixMaskProblem (R := R) (blockCount * blockLength)
          extractedDimension sampleCount narrowErrorSampler)
        (uniformMaskReduction blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler adversary)] =
      𝒟[structuredUniformTranscript blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler >>= adversary] := by
  let sourceMatrices :
      ProbComp (Matrix (Fin extractedDimension) (Fin sampleCount) R) :=
    $ᵗ Matrix (Fin extractedDimension) (Fin sampleCount) R
  let extractors :
      ProbComp
        (Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R) :=
    $ᵗ Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R
  let matrixErrors :
      ProbComp (Matrix (Fin (blockCount * blockLength)) (Fin sampleCount) R) :=
    matrixErrorSampler (blockCount * blockLength) sampleCount narrowErrorSampler
  let uniforms : ProbComp (Fin sampleCount → R) :=
    $ᵗ (Fin sampleCount → R)
  let finish
      (sourceMatrix : Matrix (Fin extractedDimension) (Fin sampleCount) R)
      (extractor :
        Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R)
      (matrixError :
        Matrix (Fin (blockCount * blockLength)) (Fin sampleCount) R)
      (uniform : Fin sampleCount → R) : ProbComp Bool :=
    adversary (extractor * sourceMatrix + matrixError, uniform)
  simp only [LearningWithErrors.game0, LearningWithErrors.distr,
    matrixMaskProblem, uniformMaskReduction, structuredUniformTranscript, bind_assoc]
  change 𝒟[sourceMatrices >>= fun sourceMatrix ↦
      extractors >>= fun extractor ↦
      matrixErrors >>= fun matrixError ↦
      uniforms >>= fun uniform ↦
      finish sourceMatrix extractor matrixError uniform] =
    𝒟[extractors >>= fun extractor ↦
      sourceMatrices >>= fun sourceMatrix ↦
      matrixErrors >>= fun matrixError ↦
      uniforms >>= fun uniform ↦
      finish sourceMatrix extractor matrixError uniform]
  exact OracleComp.DeferredSampling.evalDist_bind_comm sourceMatrices extractors _

/-- On its uniform branch, the uniform-side matrix-mask reduction is exactly the uniform
block-binary LWE game. -/
theorem evalDist_matrixMask_game1_uniform {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)) :
    𝒟[LearningWithErrors.game1
        (matrixMaskProblem (R := R) (blockCount * blockLength)
          extractedDimension sampleCount narrowErrorSampler)
        (uniformMaskReduction blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler adversary)] =
      𝒟[LearningWithErrors.game1
        (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)
        adversary] := by
  let sourceMatrices :
      ProbComp (Matrix (Fin extractedDimension) (Fin sampleCount) R) :=
    $ᵗ Matrix (Fin extractedDimension) (Fin sampleCount) R
  let targetUniform : ProbComp Bool := do
    let challenge ←
      $ᵗ Matrix (Fin (blockCount * blockLength)) (Fin sampleCount) R
    let uniform ← $ᵗ (Fin sampleCount → R)
    adversary (challenge, uniform)
  simp only [LearningWithErrors.game1, LearningWithErrors.uniformDistr,
    matrixMaskProblem, uniformMaskReduction, problem, bind_assoc]
  change 𝒟[sourceMatrices >>= fun _ ↦ targetUniform] = 𝒟[targetUniform]
  exact OracleComp.DeferredSampling.evalDist_bind_const_neverFails
    sourceMatrices (by simp [sourceMatrices]) targetUniform

/-- The real matrix-mask branch of the combined distinguisher is the signed choice of the two
individual real branches. -/
theorem evalDist_matrixMask_game0_combined {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)) :
    𝒟[LearningWithErrors.game0
        (matrixMaskProblem (R := R) (blockCount * blockLength)
          extractedDimension sampleCount narrowErrorSampler)
        (combinedMaskReduction blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler adversary)] =
      𝒟[signedChoice
        (LearningWithErrors.game0
          (matrixMaskProblem (R := R) (blockCount * blockLength)
            extractedDimension sampleCount narrowErrorSampler)
          (uniformMaskReduction blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler adversary))
        (LearningWithErrors.game0
          (matrixMaskProblem (R := R) (blockCount * blockLength)
            extractedDimension sampleCount narrowErrorSampler)
          (realMaskReduction blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler adversary))] := by
  simpa [LearningWithErrors.game0, combinedMaskReduction] using
    (evalDist_bind_signedChoice
      (LearningWithErrors.distr
        (matrixMaskProblem (R := R) (blockCount * blockLength)
          extractedDimension sampleCount narrowErrorSampler))
      (uniformMaskReduction blockLength blockCount extractedDimension sampleCount
        narrowErrorSampler wideErrorSampler adversary)
      (realMaskReduction blockLength blockCount extractedDimension sampleCount
        narrowErrorSampler wideErrorSampler adversary))

/-- The uniform matrix-mask branch of the combined distinguisher is the signed choice of the two
individual uniform branches. -/
theorem evalDist_matrixMask_game1_combined {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)) :
    𝒟[LearningWithErrors.game1
        (matrixMaskProblem (R := R) (blockCount * blockLength)
          extractedDimension sampleCount narrowErrorSampler)
        (combinedMaskReduction blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler adversary)] =
      𝒟[signedChoice
        (LearningWithErrors.game1
          (matrixMaskProblem (R := R) (blockCount * blockLength)
            extractedDimension sampleCount narrowErrorSampler)
          (uniformMaskReduction blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler adversary))
        (LearningWithErrors.game1
          (matrixMaskProblem (R := R) (blockCount * blockLength)
            extractedDimension sampleCount narrowErrorSampler)
          (realMaskReduction blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler adversary))] := by
  simpa [LearningWithErrors.game1, combinedMaskReduction] using
    (evalDist_bind_signedChoice
      (LearningWithErrors.uniformDistr
        (matrixMaskProblem (R := R) (blockCount * blockLength)
          extractedDimension sampleCount narrowErrorSampler))
      (uniformMaskReduction blockLength blockCount extractedDimension sampleCount
        narrowErrorSampler wideErrorSampler adversary)
      (realMaskReduction blockLength blockCount extractedDimension sampleCount
        narrowErrorSampler wideErrorSampler adversary))

/-- The real ordinary-LWE branch maps to the transcript with a uniform extracted secret. -/
theorem evalDist_extractedLWE_game0 {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)) :
    𝒟[LearningWithErrors.game0
        (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
          ($ᵗ (Fin extractedDimension → R)) wideErrorSampler)
        (extractedLWReduction blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler adversary)] =
      𝒟[extractedTranscript blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler >>= adversary] := by
  let sourceMatrices :
      ProbComp (Matrix (Fin extractedDimension) (Fin sampleCount) R) :=
    $ᵗ Matrix (Fin extractedDimension) (Fin sampleCount) R
  let extractedSecrets : ProbComp (Fin extractedDimension → R) :=
    $ᵗ (Fin extractedDimension → R)
  let wideErrors : ProbComp (Fin sampleCount → R) :=
    ProbComp.sampleIID sampleCount wideErrorSampler
  let extractors :
      ProbComp
        (Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R) :=
    $ᵗ Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R
  let matrixErrors :
      ProbComp (Matrix (Fin (blockCount * blockLength)) (Fin sampleCount) R) :=
    matrixErrorSampler (blockCount * blockLength) sampleCount narrowErrorSampler
  let finish
      (sourceMatrix : Matrix (Fin extractedDimension) (Fin sampleCount) R)
      (extractedSecret : Fin extractedDimension → R)
      (wideError : Fin sampleCount → R)
      (extractor :
        Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R)
      (matrixError :
        Matrix (Fin (blockCount * blockLength)) (Fin sampleCount) R) :
      ProbComp Bool :=
    adversary (extractor * sourceMatrix + matrixError,
      vecMul extractedSecret sourceMatrix + wideError)
  simp only [LearningWithErrors.game0, LearningWithErrors.distr,
    FormalProof4FHE.LWE.batchProblem, extractedLWReduction,
    extractedTranscript, extractorContinuation,
    bind_assoc]
  change 𝒟[sourceMatrices >>= fun sourceMatrix ↦
      extractedSecrets >>= fun extractedSecret ↦
      wideErrors >>= fun wideError ↦
      extractors >>= fun extractor ↦
      matrixErrors >>= fun matrixError ↦
      finish sourceMatrix extractedSecret wideError extractor matrixError] =
    𝒟[extractors >>= fun extractor ↦
      extractedSecrets >>= fun extractedSecret ↦
      sourceMatrices >>= fun sourceMatrix ↦
      matrixErrors >>= fun matrixError ↦
      wideErrors >>= fun wideError ↦
      finish sourceMatrix extractedSecret wideError extractor matrixError]
  calc
    _ = 𝒟[sourceMatrices >>= fun sourceMatrix ↦
        extractedSecrets >>= fun extractedSecret ↦
        extractors >>= fun extractor ↦
        wideErrors >>= fun wideError ↦
        matrixErrors >>= fun matrixError ↦
        finish sourceMatrix extractedSecret wideError extractor matrixError] := by
      apply evalDist_bind_congr' sourceMatrices
      intro sourceMatrix
      apply evalDist_bind_congr' extractedSecrets
      intro extractedSecret
      exact OracleComp.DeferredSampling.evalDist_bind_comm wideErrors extractors _
    _ = 𝒟[sourceMatrices >>= fun sourceMatrix ↦
        extractors >>= fun extractor ↦
        extractedSecrets >>= fun extractedSecret ↦
        wideErrors >>= fun wideError ↦
        matrixErrors >>= fun matrixError ↦
        finish sourceMatrix extractedSecret wideError extractor matrixError] := by
      apply evalDist_bind_congr' sourceMatrices
      intro sourceMatrix
      exact OracleComp.DeferredSampling.evalDist_bind_comm extractedSecrets extractors _
    _ = 𝒟[extractors >>= fun extractor ↦
        sourceMatrices >>= fun sourceMatrix ↦
        extractedSecrets >>= fun extractedSecret ↦
        wideErrors >>= fun wideError ↦
        matrixErrors >>= fun matrixError ↦
        finish sourceMatrix extractedSecret wideError extractor matrixError] :=
      OracleComp.DeferredSampling.evalDist_bind_comm sourceMatrices extractors _
    _ = 𝒟[extractors >>= fun extractor ↦
        extractedSecrets >>= fun extractedSecret ↦
        sourceMatrices >>= fun sourceMatrix ↦
        wideErrors >>= fun wideError ↦
        matrixErrors >>= fun matrixError ↦
        finish sourceMatrix extractedSecret wideError extractor matrixError] := by
      apply evalDist_bind_congr' extractors
      intro extractor
      exact OracleComp.DeferredSampling.evalDist_bind_comm sourceMatrices extractedSecrets _
    _ = _ := by
      apply evalDist_bind_congr' extractors
      intro extractor
      apply evalDist_bind_congr' extractedSecrets
      intro extractedSecret
      apply evalDist_bind_congr' sourceMatrices
      intro sourceMatrix
      exact OracleComp.DeferredSampling.evalDist_bind_comm wideErrors matrixErrors _

/-- The uniform ordinary-LWE branch maps to the structured challenge with an independent uniform
right-hand side. -/
theorem evalDist_extractedLWE_game1 {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)) :
    𝒟[LearningWithErrors.game1
        (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
          ($ᵗ (Fin extractedDimension → R)) wideErrorSampler)
        (extractedLWReduction blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler adversary)] =
      𝒟[structuredUniformTranscript blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler >>= adversary] := by
  let sourceMatrices :
      ProbComp (Matrix (Fin extractedDimension) (Fin sampleCount) R) :=
    $ᵗ Matrix (Fin extractedDimension) (Fin sampleCount) R
  let uniforms : ProbComp (Fin sampleCount → R) :=
    $ᵗ (Fin sampleCount → R)
  let extractors :
      ProbComp
        (Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R) :=
    $ᵗ Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R
  let matrixErrors :
      ProbComp (Matrix (Fin (blockCount * blockLength)) (Fin sampleCount) R) :=
    matrixErrorSampler (blockCount * blockLength) sampleCount narrowErrorSampler
  let finish
      (sourceMatrix : Matrix (Fin extractedDimension) (Fin sampleCount) R)
      (uniform : Fin sampleCount → R)
      (extractor :
        Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R)
      (matrixError :
        Matrix (Fin (blockCount * blockLength)) (Fin sampleCount) R) :
      ProbComp Bool :=
    adversary (extractor * sourceMatrix + matrixError, uniform)
  simp only [LearningWithErrors.game1, LearningWithErrors.uniformDistr,
    FormalProof4FHE.LWE.batchProblem, extractedLWReduction,
    structuredUniformTranscript, bind_assoc]
  change 𝒟[sourceMatrices >>= fun sourceMatrix ↦
      uniforms >>= fun uniform ↦
      extractors >>= fun extractor ↦
      matrixErrors >>= fun matrixError ↦
      finish sourceMatrix uniform extractor matrixError] =
    𝒟[extractors >>= fun extractor ↦
      sourceMatrices >>= fun sourceMatrix ↦
      matrixErrors >>= fun matrixError ↦
      uniforms >>= fun uniform ↦
      finish sourceMatrix uniform extractor matrixError]
  calc
    _ = 𝒟[sourceMatrices >>= fun sourceMatrix ↦
        extractors >>= fun extractor ↦
        uniforms >>= fun uniform ↦
        matrixErrors >>= fun matrixError ↦
        finish sourceMatrix uniform extractor matrixError] := by
      apply evalDist_bind_congr' sourceMatrices
      intro sourceMatrix
      exact OracleComp.DeferredSampling.evalDist_bind_comm uniforms extractors _
    _ = 𝒟[extractors >>= fun extractor ↦
        sourceMatrices >>= fun sourceMatrix ↦
        uniforms >>= fun uniform ↦
        matrixErrors >>= fun matrixError ↦
        finish sourceMatrix uniform extractor matrixError] :=
      OracleComp.DeferredSampling.evalDist_bind_comm sourceMatrices extractors _
    _ = _ := by
      apply evalDist_bind_congr' extractors
      intro extractor
      apply evalDist_bind_congr' sourceMatrices
      intro sourceMatrix
      exact OracleComp.DeferredSampling.evalDist_bind_comm uniforms matrixErrors _

/-- The real-side matrix-mask advantage is exactly the first hybrid gap. -/
theorem realMask_advantage_eq {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)) :
    LearningWithErrors.advantage
        (matrixMaskProblem (R := R) (blockCount * blockLength)
          extractedDimension sampleCount narrowErrorSampler)
        (realMaskReduction blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler adversary) =
      |(Pr[= true |
          structuredRealTranscript blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler >>= adversary]).toReal -
        (Pr[= true | LearningWithErrors.game0
          (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)
          adversary]).toReal| := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage
  rw [probOutput_congr rfl
      (evalDist_matrixMask_game0_real blockLength blockCount extractedDimension sampleCount
        narrowErrorSampler wideErrorSampler adversary),
    probOutput_congr rfl
      (evalDist_matrixMask_game1_real blockLength blockCount extractedDimension sampleCount
        narrowErrorSampler wideErrorSampler adversary)]

/-- The uniform-side matrix-mask advantage is exactly the last hybrid gap. -/
theorem uniformMask_advantage_eq {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)) :
    LearningWithErrors.advantage
        (matrixMaskProblem (R := R) (blockCount * blockLength)
          extractedDimension sampleCount narrowErrorSampler)
        (uniformMaskReduction blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler adversary) =
      |(Pr[= true |
          structuredUniformTranscript blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler >>= adversary]).toReal -
        (Pr[= true | LearningWithErrors.game1
          (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)
          adversary]).toReal| := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage
  rw [probOutput_congr rfl
      (evalDist_matrixMask_game0_uniform blockLength blockCount extractedDimension sampleCount
        narrowErrorSampler wideErrorSampler adversary),
    probOutput_congr rfl
      (evalDist_matrixMask_game1_uniform blockLength blockCount extractedDimension sampleCount
        narrowErrorSampler wideErrorSampler adversary)]

/-- The combined matrix-mask advantage is exactly half the absolute *signed sum* of the two
masking gaps.  In contrast to bounding the two gaps separately, this identity preserves any
cancellation between them. -/
theorem combinedMask_advantage_eq {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)) :
    LearningWithErrors.advantage
        (matrixMaskProblem (R := R) (blockCount * blockLength)
          extractedDimension sampleCount narrowErrorSampler)
        (combinedMaskReduction blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler adversary) =
      |((Pr[= true | LearningWithErrors.game0
          (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)
          adversary]).toReal -
        (Pr[= true |
          structuredRealTranscript blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler >>= adversary]).toReal) +
        ((Pr[= true |
          structuredUniformTranscript blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler >>= adversary]).toReal -
        (Pr[= true | LearningWithErrors.game1
          (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)
          adversary]).toReal)| / 2 := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage
  rw [probOutput_congr rfl
      (evalDist_matrixMask_game0_combined blockLength blockCount extractedDimension sampleCount
        narrowErrorSampler wideErrorSampler adversary),
    probOutput_congr rfl
      (evalDist_matrixMask_game1_combined blockLength blockCount extractedDimension sampleCount
        narrowErrorSampler wideErrorSampler adversary),
    probOutput_true_signedChoice, probOutput_true_signedChoice,
    probOutput_congr rfl
      (evalDist_matrixMask_game0_uniform blockLength blockCount extractedDimension sampleCount
        narrowErrorSampler wideErrorSampler adversary),
    probOutput_congr rfl
      (evalDist_matrixMask_game0_real blockLength blockCount extractedDimension sampleCount
        narrowErrorSampler wideErrorSampler adversary),
    probOutput_congr rfl
      (evalDist_matrixMask_game1_uniform blockLength blockCount extractedDimension sampleCount
        narrowErrorSampler wideErrorSampler adversary),
    probOutput_congr rfl
      (evalDist_matrixMask_game1_real blockLength blockCount extractedDimension sampleCount
        narrowErrorSampler wideErrorSampler adversary)]
  rw [show
      (((Pr[= true |
          structuredUniformTranscript blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler >>= adversary]).toReal + 1 -
          (Pr[= true |
            structuredRealTranscript blockLength blockCount extractedDimension sampleCount
              narrowErrorSampler wideErrorSampler >>= adversary]).toReal) / 2 -
        ((Pr[= true | LearningWithErrors.game1
          (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)
          adversary]).toReal + 1 -
          (Pr[= true | LearningWithErrors.game0
            (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)
            adversary]).toReal) / 2) =
        (((Pr[= true | LearningWithErrors.game0
            (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)
            adversary]).toReal -
          (Pr[= true |
            structuredRealTranscript blockLength blockCount extractedDimension sampleCount
              narrowErrorSampler wideErrorSampler >>= adversary]).toReal) +
          ((Pr[= true |
            structuredUniformTranscript blockLength blockCount extractedDimension sampleCount
              narrowErrorSampler >>= adversary]).toReal -
          (Pr[= true | LearningWithErrors.game1
            (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)
            adversary]).toReal)) / 2 by ring,
    abs_div]
  norm_num

/-- The ordinary-LWE advantage is exactly the extracted-secret hybrid gap. -/
theorem extractedLWE_advantage_eq {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)) :
    LearningWithErrors.advantage
        (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
          ($ᵗ (Fin extractedDimension → R)) wideErrorSampler)
        (extractedLWReduction blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler adversary) =
      |(Pr[= true |
          extractedTranscript blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler >>= adversary]).toReal -
        (Pr[= true |
          structuredUniformTranscript blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler >>= adversary]).toReal| := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage
  rw [probOutput_congr rfl
      (evalDist_extractedLWE_game0 blockLength blockCount extractedDimension sampleCount
        narrowErrorSampler wideErrorSampler adversary),
    probOutput_congr rfl
      (evalDist_extractedLWE_game1 blockLength blockCount extractedDimension sampleCount
        narrowErrorSampler wideErrorSampler adversary)]

/-! ## Statistical gaps and the end-to-end concrete reduction -/

/-- Postprocessing the noise-absorption transcripts by an adversary costs at most their TV
distance. -/
theorem abs_prob_structuredReal_sub_noiseIdeal_le {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)) :
    |(Pr[= true |
        structuredRealTranscript blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler >>= adversary]).toReal -
      (Pr[= true |
        noiseIdealTranscript blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler >>= adversary]).toReal| ≤
      noiseAbsorptionGap blockLength blockCount extractedDimension sampleCount
        narrowErrorSampler wideErrorSampler := by
  calc
    _ ≤ tvDist
        (structuredRealTranscript blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler >>= adversary)
        (noiseIdealTranscript blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler >>= adversary) :=
      abs_probOutput_toReal_sub_le_tvDist _ _
    _ ≤ tvDist
        (structuredRealTranscript blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler)
        (noiseIdealTranscript blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler) :=
      tvDist_bind_right_le adversary _ _
    _ = _ := rfl

/-- Adversarial postprocessing pays only the exact joint statistical gap between the structured
real transcript and the extracted-secret transcript. -/
theorem abs_prob_structuredReal_sub_extracted_le_joint {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)) :
    |(Pr[= true |
        structuredRealTranscript blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler >>= adversary]).toReal -
      (Pr[= true |
        extractedTranscript blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler >>= adversary]).toReal| ≤
      jointStatisticalGap blockLength blockCount extractedDimension sampleCount
        narrowErrorSampler wideErrorSampler := by
  calc
    _ ≤ tvDist
        (structuredRealTranscript blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler >>= adversary)
        (extractedTranscript blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler >>= adversary) :=
      abs_probOutput_toReal_sub_le_tvDist _ _
    _ ≤ tvDist
        (structuredRealTranscript blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler)
        (extractedTranscript blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler) :=
      tvDist_bind_right_le adversary _ _
    _ = _ := rfl

/-- The concrete block-key leftover-hash bound after adversarial postprocessing. -/
theorem abs_prob_noiseIdeal_sub_extracted_le {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)) :
    |(Pr[= true |
        noiseIdealTranscript blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler >>= adversary]).toReal -
      (Pr[= true |
        extractedTranscript blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler >>= adversary]).toReal| ≤
      Real.sqrt
          ((Fintype.card R : ℝ) ^ extractedDimension /
            (blockLength + 1 : ℝ) ^ blockCount) /
        2 := by
  calc
    _ ≤ tvDist
        (noiseIdealTranscript blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler >>= adversary)
        (extractedTranscript blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler >>= adversary) :=
      abs_probOutput_toReal_sub_le_tvDist _ _
    _ ≤ tvDist
        (noiseIdealTranscript blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler)
        (extractedTranscript blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler) :=
      tvDist_bind_right_le adversary _ _
    _ ≤ _ := tvDist_noiseIdeal_extracted_le blockLength blockCount
      extractedDimension sampleCount narrowErrorSampler wideErrorSampler

/-- The tight finite block-key leftover-hash bound after adversarial postprocessing. -/
theorem abs_prob_noiseIdeal_sub_extracted_le_tight {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)) :
    |(Pr[= true |
        noiseIdealTranscript blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler >>= adversary]).toReal -
      (Pr[= true |
        extractedTranscript blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler >>= adversary]).toReal| ≤
      Real.sqrt
          (((Fintype.card R : ℝ) ^ extractedDimension - 1) /
            (blockLength + 1 : ℝ) ^ blockCount) /
        2 := by
  calc
    _ ≤ tvDist
        (noiseIdealTranscript blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler >>= adversary)
        (extractedTranscript blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler >>= adversary) :=
      abs_probOutput_toReal_sub_le_tvDist _ _
    _ ≤ tvDist
        (noiseIdealTranscript blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler)
        (extractedTranscript blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler) :=
      tvDist_bind_right_le adversary _ _
    _ ≤ _ := tvDist_noiseIdeal_extracted_le_tight blockLength blockCount
      extractedDimension sampleCount narrowErrorSampler wideErrorSampler

/-- End-to-end concrete block-binary key reduction.

The two matrix-mask terms account for replacing `C * B + Z` by a uniform public challenge on the
real and uniform sides.  The middle computational term is ordinary LWE in
`extractedDimension`.  The remaining terms are precisely noise absorption and extraction from a
key space of size `(blockLength + 1) ^ blockCount`. -/
theorem advantage_le_matrixMask_add_lwe_add_gaps {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)) :
    LearningWithErrors.advantage
        (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)
        adversary ≤
      LearningWithErrors.advantage
          (matrixMaskProblem (R := R) (blockCount * blockLength)
            extractedDimension sampleCount narrowErrorSampler)
          (realMaskReduction blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler adversary) +
        noiseAbsorptionGap blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler +
        Real.sqrt
            ((Fintype.card R : ℝ) ^ extractedDimension /
              (blockLength + 1 : ℝ) ^ blockCount) /
          2 +
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
            ($ᵗ (Fin extractedDimension → R)) wideErrorSampler)
          (extractedLWReduction blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler adversary) +
        LearningWithErrors.advantage
          (matrixMaskProblem (R := R) (blockCount * blockLength)
            extractedDimension sampleCount narrowErrorSampler)
          (uniformMaskReduction blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage
  let p0 : ℝ := (Pr[= true | LearningWithErrors.game0
    (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)
    adversary]).toReal
  let p1 : ℝ := (Pr[= true |
    structuredRealTranscript blockLength blockCount extractedDimension sampleCount
      narrowErrorSampler wideErrorSampler >>= adversary]).toReal
  let p2 : ℝ := (Pr[= true |
    noiseIdealTranscript blockLength blockCount extractedDimension sampleCount
      narrowErrorSampler wideErrorSampler >>= adversary]).toReal
  let p3 : ℝ := (Pr[= true |
    extractedTranscript blockLength blockCount extractedDimension sampleCount
      narrowErrorSampler wideErrorSampler >>= adversary]).toReal
  let p4 : ℝ := (Pr[= true |
    structuredUniformTranscript blockLength blockCount extractedDimension sampleCount
      narrowErrorSampler >>= adversary]).toReal
  let p5 : ℝ := (Pr[= true | LearningWithErrors.game1
    (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)
    adversary]).toReal
  change |p0 - p5| ≤ _
  have h01 : |p0 - p1| =
      LearningWithErrors.advantage
        (matrixMaskProblem (R := R) (blockCount * blockLength)
          extractedDimension sampleCount narrowErrorSampler)
        (realMaskReduction blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler adversary) := by
    rw [abs_sub_comm]
    exact (realMask_advantage_eq blockLength blockCount extractedDimension sampleCount
      narrowErrorSampler wideErrorSampler adversary).symm
  have h12 : |p1 - p2| ≤
      noiseAbsorptionGap blockLength blockCount extractedDimension sampleCount
        narrowErrorSampler wideErrorSampler :=
    abs_prob_structuredReal_sub_noiseIdeal_le blockLength blockCount
      extractedDimension sampleCount narrowErrorSampler wideErrorSampler adversary
  have h23 : |p2 - p3| ≤
      Real.sqrt
          ((Fintype.card R : ℝ) ^ extractedDimension /
            (blockLength + 1 : ℝ) ^ blockCount) /
        2 :=
    abs_prob_noiseIdeal_sub_extracted_le blockLength blockCount
      extractedDimension sampleCount narrowErrorSampler wideErrorSampler adversary
  have h34 : |p3 - p4| =
      LearningWithErrors.advantage
        (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
          ($ᵗ (Fin extractedDimension → R)) wideErrorSampler)
        (extractedLWReduction blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler adversary) :=
    (extractedLWE_advantage_eq blockLength blockCount extractedDimension sampleCount
      narrowErrorSampler wideErrorSampler adversary).symm
  have h45 : |p4 - p5| =
      LearningWithErrors.advantage
        (matrixMaskProblem (R := R) (blockCount * blockLength)
          extractedDimension sampleCount narrowErrorSampler)
        (uniformMaskReduction blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler adversary) :=
    (uniformMask_advantage_eq blockLength blockCount extractedDimension sampleCount
      narrowErrorSampler wideErrorSampler adversary).symm
  have htelescope :
      |p0 - p5| ≤
        |p0 - p1| + |p1 - p2| + |p2 - p3| + |p3 - p4| + |p4 - p5| := by
    have hid : p0 - p5 =
        (p0 - p1) + ((p1 - p2) + ((p2 - p3) + ((p3 - p4) + (p4 - p5)))) := by
      ring
    rw [hid]
    calc
      _ ≤ |p0 - p1| +
          |(p1 - p2) + ((p2 - p3) + ((p3 - p4) + (p4 - p5)))| :=
        abs_add_le _ _
      _ ≤ |p0 - p1| +
          (|p1 - p2| + |(p2 - p3) + ((p3 - p4) + (p4 - p5))|) := by
        gcongr
        exact abs_add_le _ _
      _ ≤ |p0 - p1| +
          (|p1 - p2| + (|p2 - p3| + |(p3 - p4) + (p4 - p5)|)) := by
        gcongr
        exact abs_add_le _ _
      _ ≤ |p0 - p1| +
          (|p1 - p2| + (|p2 - p3| + (|p3 - p4| + |p4 - p5|))) := by
        gcongr
        exact abs_add_le _ _
      _ = _ := by ring
  rw [h01, h34, h45] at htelescope
  calc
    |p0 - p5| ≤ _ := htelescope
    _ ≤ _ := by gcongr

/-- Sharper end-to-end reduction retaining the noise/extraction transition as one exact TV gap.

This avoids a triangle inequality internal to the statistical part of the reduction. -/
theorem advantage_le_matrixMask_add_lwe_add_jointGap {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)) :
    LearningWithErrors.advantage
        (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)
        adversary ≤
      LearningWithErrors.advantage
          (matrixMaskProblem (R := R) (blockCount * blockLength)
            extractedDimension sampleCount narrowErrorSampler)
          (realMaskReduction blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler adversary) +
        jointStatisticalGap blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler +
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
            ($ᵗ (Fin extractedDimension → R)) wideErrorSampler)
          (extractedLWReduction blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler adversary) +
        LearningWithErrors.advantage
          (matrixMaskProblem (R := R) (blockCount * blockLength)
            extractedDimension sampleCount narrowErrorSampler)
          (uniformMaskReduction blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage
  let p0 : ℝ := (Pr[= true | LearningWithErrors.game0
    (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)
    adversary]).toReal
  let p1 : ℝ := (Pr[= true |
    structuredRealTranscript blockLength blockCount extractedDimension sampleCount
      narrowErrorSampler wideErrorSampler >>= adversary]).toReal
  let p3 : ℝ := (Pr[= true |
    extractedTranscript blockLength blockCount extractedDimension sampleCount
      narrowErrorSampler wideErrorSampler >>= adversary]).toReal
  let p4 : ℝ := (Pr[= true |
    structuredUniformTranscript blockLength blockCount extractedDimension sampleCount
      narrowErrorSampler >>= adversary]).toReal
  let p5 : ℝ := (Pr[= true | LearningWithErrors.game1
    (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)
    adversary]).toReal
  change |p0 - p5| ≤ _
  have h01 : |p0 - p1| =
      LearningWithErrors.advantage
        (matrixMaskProblem (R := R) (blockCount * blockLength)
          extractedDimension sampleCount narrowErrorSampler)
        (realMaskReduction blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler adversary) := by
    rw [abs_sub_comm]
    exact (realMask_advantage_eq blockLength blockCount extractedDimension sampleCount
      narrowErrorSampler wideErrorSampler adversary).symm
  have h13 : |p1 - p3| ≤
      jointStatisticalGap blockLength blockCount extractedDimension sampleCount
        narrowErrorSampler wideErrorSampler :=
    abs_prob_structuredReal_sub_extracted_le_joint blockLength blockCount
      extractedDimension sampleCount narrowErrorSampler wideErrorSampler adversary
  have h34 : |p3 - p4| =
      LearningWithErrors.advantage
        (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
          ($ᵗ (Fin extractedDimension → R)) wideErrorSampler)
        (extractedLWReduction blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler adversary) :=
    (extractedLWE_advantage_eq blockLength blockCount extractedDimension sampleCount
      narrowErrorSampler wideErrorSampler adversary).symm
  have h45 : |p4 - p5| =
      LearningWithErrors.advantage
        (matrixMaskProblem (R := R) (blockCount * blockLength)
          extractedDimension sampleCount narrowErrorSampler)
        (uniformMaskReduction blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler adversary) :=
    (uniformMask_advantage_eq blockLength blockCount extractedDimension sampleCount
      narrowErrorSampler wideErrorSampler adversary).symm
  have htelescope :
      |p0 - p5| ≤ |p0 - p1| + |p1 - p3| + |p3 - p4| + |p4 - p5| := by
    have hid : p0 - p5 =
        (p0 - p1) + ((p1 - p3) + ((p3 - p4) + (p4 - p5))) := by
      ring
    rw [hid]
    calc
      _ ≤ |p0 - p1| + |(p1 - p3) + ((p3 - p4) + (p4 - p5))| :=
        abs_add_le _ _
      _ ≤ |p0 - p1| + (|p1 - p3| + |(p3 - p4) + (p4 - p5)|) := by
        gcongr
        exact abs_add_le _ _
      _ ≤ |p0 - p1| + (|p1 - p3| + (|p3 - p4| + |p4 - p5|)) := by
        gcongr
        exact abs_add_le _ _
      _ = _ := by ring
  rw [h01, h34, h45] at htelescope
  exact htelescope.trans (by gcongr)

/-- Tight computational grouping of the end-to-end reduction.

The two masking transitions are represented by one signed distinguisher, so their deviations may
cancel.  The factor two only converts the fair signed choice back to the original signed sum. -/
theorem advantage_le_two_combinedMask_add_lwe_add_jointGap {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)) :
    LearningWithErrors.advantage
        (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)
        adversary ≤
      2 * LearningWithErrors.advantage
          (matrixMaskProblem (R := R) (blockCount * blockLength)
            extractedDimension sampleCount narrowErrorSampler)
          (combinedMaskReduction blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler adversary) +
        jointStatisticalGap blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler +
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
            ($ᵗ (Fin extractedDimension → R)) wideErrorSampler)
          (extractedLWReduction blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage
  let p0 : ℝ := (Pr[= true | LearningWithErrors.game0
    (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)
    adversary]).toReal
  let p1 : ℝ := (Pr[= true |
    structuredRealTranscript blockLength blockCount extractedDimension sampleCount
      narrowErrorSampler wideErrorSampler >>= adversary]).toReal
  let p3 : ℝ := (Pr[= true |
    extractedTranscript blockLength blockCount extractedDimension sampleCount
      narrowErrorSampler wideErrorSampler >>= adversary]).toReal
  let p4 : ℝ := (Pr[= true |
    structuredUniformTranscript blockLength blockCount extractedDimension sampleCount
      narrowErrorSampler >>= adversary]).toReal
  let p5 : ℝ := (Pr[= true | LearningWithErrors.game1
    (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)
    adversary]).toReal
  change |p0 - p5| ≤ _
  have hcombined :
      LearningWithErrors.advantage
          (matrixMaskProblem (R := R) (blockCount * blockLength)
            extractedDimension sampleCount narrowErrorSampler)
          (combinedMaskReduction blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler adversary) =
        |(p0 - p1) + (p4 - p5)| / 2 := by
    simpa [p0, p1, p4, p5] using
      (combinedMask_advantage_eq blockLength blockCount extractedDimension sampleCount
        narrowErrorSampler wideErrorSampler adversary)
  have hmask :
      |(p0 - p1) + (p4 - p5)| =
        2 * LearningWithErrors.advantage
          (matrixMaskProblem (R := R) (blockCount * blockLength)
            extractedDimension sampleCount narrowErrorSampler)
          (combinedMaskReduction blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler adversary) := by
    rw [hcombined]
    ring
  have h13 : |p1 - p3| ≤
      jointStatisticalGap blockLength blockCount extractedDimension sampleCount
        narrowErrorSampler wideErrorSampler :=
    abs_prob_structuredReal_sub_extracted_le_joint blockLength blockCount
      extractedDimension sampleCount narrowErrorSampler wideErrorSampler adversary
  have h34 : |p3 - p4| =
      LearningWithErrors.advantage
        (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
          ($ᵗ (Fin extractedDimension → R)) wideErrorSampler)
        (extractedLWReduction blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler adversary) :=
    (extractedLWE_advantage_eq blockLength blockCount extractedDimension sampleCount
      narrowErrorSampler wideErrorSampler adversary).symm
  have hid : p0 - p5 =
      ((p0 - p1) + (p4 - p5)) + ((p1 - p3) + (p3 - p4)) := by
    ring
  rw [hid]
  calc
    _ ≤ |(p0 - p1) + (p4 - p5)| + |(p1 - p3) + (p3 - p4)| :=
      abs_add_le _ _
    _ ≤ |(p0 - p1) + (p4 - p5)| + (|p1 - p3| + |p3 - p4|) := by
      gcongr
      exact abs_add_le _ _
    _ ≤ |(p0 - p1) + (p4 - p5)| +
        (jointStatisticalGap blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler + |p3 - p4|) := by
      gcongr
    _ = _ := by rw [hmask, h34]; ring

/-! ## Row hybrid: matrix-mask LWE from ordinary LWE -/

/-- One real LWE row under a fixed public source matrix. -/
def realMaskRow {R : Type} [Semiring R] [SampleableType R]
    {extractedDimension sampleCount : ℕ}
    (sourceMatrix : Matrix (Fin extractedDimension) (Fin sampleCount) R)
    (narrowErrorSampler : ProbComp R) : ProbComp (Fin sampleCount → R) := do
  let secret ← $ᵗ (Fin extractedDimension → R)
  let error ← ProbComp.sampleIID sampleCount narrowErrorSampler
  return vecMul secret sourceMatrix + error

/-- Assemble independently sampled row vectors into a matrix. -/
def sampleRowMatrix {R : Type} (rowCount sampleCount : ℕ)
    (samplers : Fin rowCount → ProbComp (Fin sampleCount → R)) :
    ProbComp (Matrix (Fin rowCount) (Fin sampleCount) R) :=
  Matrix.of <$> Fin.mOfFn rowCount samplers

/-- Uniform independent rows give the uniform matrix distribution. -/
theorem evalDist_sampleRowMatrix_uniform {R : Type}
    [Fintype R] [SampleableType R] (rowCount sampleCount : ℕ) :
    𝒟[sampleRowMatrix rowCount sampleCount
        (fun _ => $ᵗ (Fin sampleCount → R))] =
      𝒟[$ᵗ Matrix (Fin rowCount) (Fin sampleCount) R] := by
  have hrows :=
    FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
      (alpha := Fin sampleCount → R) rowCount
  have hmapped := evalDist_map_eq_of_evalDist_eq hrows Matrix.of
  change 𝒟[Matrix.of <$> Fin.mOfFn rowCount
      (fun _ => $ᵗ (Fin sampleCount → R))] =
    𝒟[$ᵗ Matrix (Fin rowCount) (Fin sampleCount) R]
  calc
    _ = 𝒟[Matrix.of <$> ($ᵗ (Fin rowCount → Fin sampleCount → R))] :=
      hmapped
    _ = _ := evalDist_map_bijective_uniform_cross
      (α := Fin rowCount → Fin sampleCount → R)
      (β := Matrix (Fin rowCount) (Fin sampleCount) R)
      Matrix.of Matrix.of.bijective

/-- Row hybrid with its first `replaced` rows uniform and all remaining rows real. -/
def rowHybridRows {R : Type} [Semiring R] [SampleableType R]
    (rowCount extractedDimension sampleCount replaced : ℕ)
    (narrowErrorSampler : ProbComp R)
    (sourceMatrix : Matrix (Fin extractedDimension) (Fin sampleCount) R) :
    ProbComp (Matrix (Fin rowCount) (Fin sampleCount) R) :=
  sampleRowMatrix rowCount sampleCount fun index =>
    if index.val < replaced then
      $ᵗ (Fin sampleCount → R)
    else
      realMaskRow sourceMatrix narrowErrorSampler

/-- Boolean distinguishing game for a row hybrid. -/
def rowHybridGame {R : Type} [Semiring R] [SampleableType R]
    (rowCount extractedDimension sampleCount replaced : ℕ)
    (narrowErrorSampler : ProbComp R)
    (adversary :
      Matrix (Fin extractedDimension) (Fin sampleCount) R ×
        Matrix (Fin rowCount) (Fin sampleCount) R → ProbComp Bool) :
    ProbComp Bool := do
  let sourceMatrix ←
    $ᵗ Matrix (Fin extractedDimension) (Fin sampleCount) R
  let rows ← rowHybridRows rowCount extractedDimension sampleCount replaced
    narrowErrorSampler sourceMatrix
  adversary (sourceMatrix, rows)

/-- The ordinary-LWE reduction for one adjacent row-hybrid transition. -/
def rowHybridReduction {R : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (rowCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler : ProbComp R) (coordinate : Fin rowCount)
    (adversary : LearningWithErrors.Adversary
      (matrixMaskProblem (R := R) rowCount extractedDimension sampleCount
        narrowErrorSampler)) :
    LearningWithErrors.Adversary
      (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
        ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler) :=
  fun sample ↦ do
    let rows ← sampleRowMatrix rowCount sampleCount fun index =>
      if index = coordinate then
        pure sample.2
      else if index.val < coordinate.val then
        $ᵗ (Fin sampleCount → R)
      else
        realMaskRow sample.1 narrowErrorSampler
    adversary (sample.1, rows)

/-- A single ordinary-LWE distinguisher obtained by choosing the replaced row uniformly.

Unlike a sum of absolute adjacent hybrid gaps, this reduction retains cancellation across rows. -/
def randomRowHybridReduction {R : Type}
    [Semiring R] [DecidableEq R] [SampleableType R]
    (rowCount extractedDimension sampleCount : ℕ) [NeZero rowCount]
    (narrowErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (matrixMaskProblem (R := R) rowCount extractedDimension sampleCount
        narrowErrorSampler)) :
    LearningWithErrors.Adversary
      (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
        ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler) :=
  fun sample ↦ do
    let coordinate ← $ᵗ (Fin rowCount)
    rowHybridReduction rowCount extractedDimension sampleCount narrowErrorSampler
      coordinate adversary sample

/-- The real ordinary-LWE branch realizes hybrid `coordinate.val`. -/
theorem evalDist_rowHybridReduction_game0 {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (rowCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler : ProbComp R) (coordinate : Fin rowCount)
    (adversary : LearningWithErrors.Adversary
      (matrixMaskProblem (R := R) rowCount extractedDimension sampleCount
        narrowErrorSampler)) :
    𝒟[LearningWithErrors.game0
        (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
          ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler)
        (rowHybridReduction rowCount extractedDimension sampleCount
          narrowErrorSampler coordinate adversary)] =
      𝒟[rowHybridGame rowCount extractedDimension sampleCount coordinate.val
        narrowErrorSampler adversary] := by
  let sourceMatrices :
      ProbComp (Matrix (Fin extractedDimension) (Fin sampleCount) R) :=
    $ᵗ Matrix (Fin extractedDimension) (Fin sampleCount) R
  let samplers
      (sourceMatrix : Matrix (Fin extractedDimension) (Fin sampleCount) R) :
      Fin rowCount → ProbComp (Fin sampleCount → R) :=
    fun index => if index.val < coordinate.val then
      $ᵗ (Fin sampleCount → R)
    else realMaskRow sourceMatrix narrowErrorSampler
  let replacement
      (sourceMatrix : Matrix (Fin extractedDimension) (Fin sampleCount) R)
      (value : Fin sampleCount → R) :
      ProbComp (Matrix (Fin rowCount) (Fin sampleCount) R) :=
    sampleRowMatrix rowCount sampleCount fun index =>
      if index = coordinate then pure value else samplers sourceMatrix index
  simp only [LearningWithErrors.game0, LearningWithErrors.distr,
    FormalProof4FHE.LWE.batchProblem, rowHybridReduction,
    rowHybridGame, rowHybridRows, realMaskRow, bind_assoc, pure_bind]
  apply evalDist_bind_congr' sourceMatrices
  intro sourceMatrix
  have hpull := FormalProof4FHE.FiniteProduct.evalDist_pull_coordinate
    rowCount (samplers sourceMatrix) coordinate
  have hselected : samplers sourceMatrix coordinate =
      realMaskRow sourceMatrix narrowErrorSampler := by
    simp [samplers]
  rw [hselected] at hpull
  have hpullMatrix := evalDist_map_eq_of_evalDist_eq hpull Matrix.of
  let postprocess (rows : Matrix (Fin rowCount) (Fin sampleCount) R) : ProbComp Bool :=
    adversary (sourceMatrix, rows)
  have hbase :
      𝒟[realMaskRow sourceMatrix narrowErrorSampler >>= replacement sourceMatrix] =
        𝒟[sampleRowMatrix rowCount sampleCount (samplers sourceMatrix)] := by
    simpa [sampleRowMatrix, replacement, map_bind] using hpullMatrix
  have hpost :
      𝒟[(realMaskRow sourceMatrix narrowErrorSampler >>= replacement sourceMatrix) >>=
          postprocess] =
        𝒟[sampleRowMatrix rowCount sampleCount (samplers sourceMatrix) >>=
          postprocess] := by
    calc
      _ = 𝒟[realMaskRow sourceMatrix narrowErrorSampler >>= replacement sourceMatrix] >>=
            fun rows ↦ 𝒟[postprocess rows] :=
        evalDist_bind _ _
      _ = 𝒟[sampleRowMatrix rowCount sampleCount (samplers sourceMatrix)] >>=
            fun rows ↦ 𝒟[postprocess rows] := by rw [hbase]
      _ = _ := (evalDist_bind _ _).symm
  simpa [realMaskRow, replacement, postprocess, samplers, bind_assoc] using hpost

/-- The uniform ordinary-LWE branch realizes hybrid `coordinate.val + 1`. -/
theorem evalDist_rowHybridReduction_game1 {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (rowCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler : ProbComp R) (coordinate : Fin rowCount)
    (adversary : LearningWithErrors.Adversary
      (matrixMaskProblem (R := R) rowCount extractedDimension sampleCount
        narrowErrorSampler)) :
    𝒟[LearningWithErrors.game1
        (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
          ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler)
        (rowHybridReduction rowCount extractedDimension sampleCount
          narrowErrorSampler coordinate adversary)] =
      𝒟[rowHybridGame rowCount extractedDimension sampleCount (coordinate.val + 1)
        narrowErrorSampler adversary] := by
  let sourceMatrices :
      ProbComp (Matrix (Fin extractedDimension) (Fin sampleCount) R) :=
    $ᵗ Matrix (Fin extractedDimension) (Fin sampleCount) R
  let nextSamplers
      (sourceMatrix : Matrix (Fin extractedDimension) (Fin sampleCount) R) :
      Fin rowCount → ProbComp (Fin sampleCount → R) :=
    fun index => if index.val < coordinate.val + 1 then
      $ᵗ (Fin sampleCount → R)
    else realMaskRow sourceMatrix narrowErrorSampler
  let replacement
      (sourceMatrix : Matrix (Fin extractedDimension) (Fin sampleCount) R)
      (value : Fin sampleCount → R) :
      ProbComp (Matrix (Fin rowCount) (Fin sampleCount) R) :=
    sampleRowMatrix rowCount sampleCount fun index =>
      if index = coordinate then pure value
      else if index.val < coordinate.val then
        $ᵗ (Fin sampleCount → R)
      else realMaskRow sourceMatrix narrowErrorSampler
  simp only [LearningWithErrors.game1, LearningWithErrors.uniformDistr,
    FormalProof4FHE.LWE.batchProblem, rowHybridReduction,
    rowHybridGame, bind_assoc]
  change 𝒟[sourceMatrices >>= fun sourceMatrix ↦
      ($ᵗ (Fin sampleCount → R)) >>= fun value ↦
      replacement sourceMatrix value >>= fun rows ↦
      adversary (sourceMatrix, rows)] =
    𝒟[sourceMatrices >>= fun sourceMatrix ↦
      sampleRowMatrix rowCount sampleCount (nextSamplers sourceMatrix) >>= fun rows ↦
      adversary (sourceMatrix, rows)]
  apply evalDist_bind_congr' sourceMatrices
  intro sourceMatrix
  have hpull := FormalProof4FHE.FiniteProduct.evalDist_pull_coordinate
    rowCount (nextSamplers sourceMatrix) coordinate
  have hselected : nextSamplers sourceMatrix coordinate =
      ($ᵗ (Fin sampleCount → R)) := by
    simp [nextSamplers]
  rw [hselected] at hpull
  have hpullMatrix := evalDist_map_eq_of_evalDist_eq hpull Matrix.of
  have hreplacement : ∀ value,
      replacement sourceMatrix value =
        sampleRowMatrix rowCount sampleCount (fun index =>
          if index = coordinate then pure value else nextSamplers sourceMatrix index) := by
    intro value
    apply congrArg (sampleRowMatrix rowCount sampleCount)
    funext index
    by_cases hindex : index = coordinate
    · simp [hindex]
    · simp only [hindex, ↓reduceIte, nextSamplers]
      by_cases hlt : index.val < coordinate.val
      · have hnext : index.val < coordinate.val + 1 := by omega
        simp [hlt, hnext]
      · have hnotnext : ¬index.val < coordinate.val + 1 := by omega
        simp [hlt, hnotnext]
  let postprocess (rows : Matrix (Fin rowCount) (Fin sampleCount) R) : ProbComp Bool :=
    adversary (sourceMatrix, rows)
  have hbase :
      𝒟[(($ᵗ (Fin sampleCount → R)) >>= replacement sourceMatrix)] =
        𝒟[sampleRowMatrix rowCount sampleCount (nextSamplers sourceMatrix)] := by
    have hf : replacement sourceMatrix = fun value =>
        sampleRowMatrix rowCount sampleCount (fun index =>
          if index = coordinate then pure value else nextSamplers sourceMatrix index) :=
      funext hreplacement
    simpa [sampleRowMatrix, hf, map_bind] using hpullMatrix
  have hpost :
      𝒟[(($ᵗ (Fin sampleCount → R)) >>= replacement sourceMatrix) >>= postprocess] =
        𝒟[sampleRowMatrix rowCount sampleCount (nextSamplers sourceMatrix) >>=
          postprocess] := by
    calc
      _ = 𝒟[(($ᵗ (Fin sampleCount → R)) >>= replacement sourceMatrix)] >>=
            fun rows ↦ 𝒟[postprocess rows] :=
        evalDist_bind _ _
      _ = 𝒟[sampleRowMatrix rowCount sampleCount (nextSamplers sourceMatrix)] >>=
            fun rows ↦ 𝒟[postprocess rows] := by rw [hbase]
      _ = _ := (evalDist_bind _ _).symm
  simpa [replacement, postprocess, bind_assoc] using hpost

/-- The real branch of the randomized-row reduction is the uniform mixture of the lower row
hybrid endpoints. -/
theorem evalDist_randomRowHybridReduction_game0 {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (rowCount extractedDimension sampleCount : ℕ) [NeZero rowCount]
    (narrowErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (matrixMaskProblem (R := R) rowCount extractedDimension sampleCount
        narrowErrorSampler)) :
    𝒟[LearningWithErrors.game0
        (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
          ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler)
        (randomRowHybridReduction rowCount extractedDimension sampleCount
          narrowErrorSampler adversary)] =
      𝒟[do
        let coordinate ← $ᵗ (Fin rowCount)
        rowHybridGame rowCount extractedDimension sampleCount coordinate.val
          narrowErrorSampler adversary] := by
  let samples := LearningWithErrors.distr
    (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
      ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler)
  let coordinates : ProbComp (Fin rowCount) := $ᵗ (Fin rowCount)
  simp only [LearningWithErrors.game0, randomRowHybridReduction]
  change 𝒟[samples >>= fun sample ↦
      coordinates >>= fun coordinate ↦
        rowHybridReduction rowCount extractedDimension sampleCount narrowErrorSampler
          coordinate adversary sample] = _
  calc
    _ = 𝒟[coordinates >>= fun coordinate ↦
        samples >>= fun sample ↦
          rowHybridReduction rowCount extractedDimension sampleCount narrowErrorSampler
            coordinate adversary sample] :=
      OracleComp.DeferredSampling.evalDist_bind_comm samples coordinates _
    _ = _ := by
      apply evalDist_bind_congr' coordinates
      intro coordinate
      exact evalDist_rowHybridReduction_game0 rowCount extractedDimension sampleCount
        narrowErrorSampler coordinate adversary

/-- The uniform branch of the randomized-row reduction is the uniform mixture of the upper row
hybrid endpoints. -/
theorem evalDist_randomRowHybridReduction_game1 {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (rowCount extractedDimension sampleCount : ℕ) [NeZero rowCount]
    (narrowErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (matrixMaskProblem (R := R) rowCount extractedDimension sampleCount
        narrowErrorSampler)) :
    𝒟[LearningWithErrors.game1
        (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
          ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler)
        (randomRowHybridReduction rowCount extractedDimension sampleCount
          narrowErrorSampler adversary)] =
      𝒟[do
        let coordinate ← $ᵗ (Fin rowCount)
        rowHybridGame rowCount extractedDimension sampleCount (coordinate.val + 1)
          narrowErrorSampler adversary] := by
  let samples := LearningWithErrors.uniformDistr
    (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
      ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler)
  let coordinates : ProbComp (Fin rowCount) := $ᵗ (Fin rowCount)
  simp only [LearningWithErrors.game1, randomRowHybridReduction]
  change 𝒟[samples >>= fun sample ↦
      coordinates >>= fun coordinate ↦
        rowHybridReduction rowCount extractedDimension sampleCount narrowErrorSampler
          coordinate adversary sample] = _
  calc
    _ = 𝒟[coordinates >>= fun coordinate ↦
        samples >>= fun sample ↦
          rowHybridReduction rowCount extractedDimension sampleCount narrowErrorSampler
            coordinate adversary sample] :=
      OracleComp.DeferredSampling.evalDist_bind_comm samples coordinates _
    _ = _ := by
      apply evalDist_bind_congr' coordinates
      intro coordinate
      exact evalDist_rowHybridReduction_game1 rowCount extractedDimension sampleCount
        narrowErrorSampler coordinate adversary

/-- One adjacent row-hybrid gap is exactly the advantage of its ordinary-LWE reduction. -/
theorem rowHybridReduction_advantage_eq {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (rowCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler : ProbComp R) (coordinate : Fin rowCount)
    (adversary : LearningWithErrors.Adversary
      (matrixMaskProblem (R := R) rowCount extractedDimension sampleCount
        narrowErrorSampler)) :
    LearningWithErrors.advantage
        (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
          ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler)
        (rowHybridReduction rowCount extractedDimension sampleCount
          narrowErrorSampler coordinate adversary) =
      |(Pr[= true |
          rowHybridGame rowCount extractedDimension sampleCount coordinate.val
            narrowErrorSampler adversary]).toReal -
        (Pr[= true |
          rowHybridGame rowCount extractedDimension sampleCount (coordinate.val + 1)
            narrowErrorSampler adversary]).toReal| := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage
  rw [probOutput_congr rfl
      (evalDist_rowHybridReduction_game0 rowCount extractedDimension sampleCount
        narrowErrorSampler coordinate adversary),
    probOutput_congr rfl
      (evalDist_rowHybridReduction_game1 rowCount extractedDimension sampleCount
        narrowErrorSampler coordinate adversary)]

/-- Once every row has been replaced, the row sampler is the uniform matrix sampler. -/
theorem evalDist_rowHybridRows_all_uniform {R : Type}
    [Semiring R] [Fintype R] [SampleableType R]
    (rowCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler : ProbComp R)
    (sourceMatrix : Matrix (Fin extractedDimension) (Fin sampleCount) R) :
    𝒟[rowHybridRows rowCount extractedDimension sampleCount rowCount
        narrowErrorSampler sourceMatrix] =
      𝒟[$ᵗ Matrix (Fin rowCount) (Fin sampleCount) R] := by
  simpa [rowHybridRows, Fin.isLt] using
    (evalDist_sampleRowMatrix_uniform (R := R) rowCount sampleCount)

/-- The last row hybrid is exactly the uniform branch of the matrix-mask problem. -/
theorem evalDist_rowHybridGame_all_uniform {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (rowCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (matrixMaskProblem (R := R) rowCount extractedDimension sampleCount
        narrowErrorSampler)) :
    𝒟[rowHybridGame rowCount extractedDimension sampleCount rowCount
        narrowErrorSampler adversary] =
      𝒟[LearningWithErrors.game1
        (matrixMaskProblem (R := R) rowCount extractedDimension sampleCount
          narrowErrorSampler) adversary] := by
  let sourceMatrices :
      ProbComp (Matrix (Fin extractedDimension) (Fin sampleCount) R) :=
    $ᵗ Matrix (Fin extractedDimension) (Fin sampleCount) R
  simp only [rowHybridGame, LearningWithErrors.game1,
    LearningWithErrors.uniformDistr, matrixMaskProblem, bind_assoc, pure_bind]
  apply evalDist_bind_congr' sourceMatrices
  intro sourceMatrix
  rw [evalDist_bind, evalDist_bind,
    evalDist_rowHybridRows_all_uniform rowCount extractedDimension sampleCount
      narrowErrorSampler sourceMatrix]

/-- Matrix multiplication and addition are computed independently in each row. -/
theorem matrix_mul_add_of_rows {R : Type} [Semiring R]
    {rowCount extractedDimension sampleCount : ℕ}
    (secretRows : Fin rowCount → Fin extractedDimension → R)
    (errorRows : Fin rowCount → Fin sampleCount → R)
    (sourceMatrix : Matrix (Fin extractedDimension) (Fin sampleCount) R) :
    Matrix.of secretRows * sourceMatrix + Matrix.of errorRows =
      Matrix.of (fun index =>
        vecMul (secretRows index) sourceMatrix + errorRows index) := by
  ext index sample
  rfl

/-- Conditional on the shared public matrix, independently sampled matrix-LWE rows have exactly
the same distribution as the zero-th row hybrid. -/
theorem evalDist_matrixMask_real_rows {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (rowCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler : ProbComp R)
    (sourceMatrix : Matrix (Fin extractedDimension) (Fin sampleCount) R) :
    𝒟[do
      let secretMatrix ←
        $ᵗ Matrix (Fin rowCount) (Fin extractedDimension) R
      let errorMatrix ←
        matrixErrorSampler rowCount sampleCount narrowErrorSampler
      return secretMatrix * sourceMatrix + errorMatrix] =
      𝒟[rowHybridRows rowCount extractedDimension sampleCount 0
        narrowErrorSampler sourceMatrix] := by
  let secretVector : ProbComp (Fin extractedDimension → R) :=
    $ᵗ (Fin extractedDimension → R)
  let errorVector : ProbComp (Fin sampleCount → R) :=
    ProbComp.sampleIID sampleCount narrowErrorSampler
  let secretRows : ProbComp (Fin rowCount → Fin extractedDimension → R) :=
    Fin.mOfFn rowCount fun _ => secretVector
  let errorRows : ProbComp (Fin rowCount → Fin sampleCount → R) :=
    Fin.mOfFn rowCount fun _ => errorVector
  let separateRows :
      ProbComp ((Fin rowCount → Fin extractedDimension → R) ×
        (Fin rowCount → Fin sampleCount → R)) := do
    let secrets ← secretRows
    let errors ← errorRows
    return (secrets, errors)
  let zipRows :
      ((Fin rowCount → Fin extractedDimension → R) ×
          (Fin rowCount → Fin sampleCount → R)) →
        (Fin rowCount → (Fin extractedDimension → R) × (Fin sampleCount → R)) :=
    (Equiv.arrowProdEquivProdArrow (Fin rowCount)
      (fun _ => Fin extractedDimension → R)
      (fun _ => Fin sampleCount → R)).symm
  let pairSampler :
      ProbComp ((Fin extractedDimension → R) × (Fin sampleCount → R)) := do
    let secret ← secretVector
    let error ← errorVector
    return (secret, error)
  let pairedRows :
      ProbComp (Fin rowCount →
        (Fin extractedDimension → R) × (Fin sampleCount → R)) :=
    Fin.mOfFn rowCount fun _ => pairSampler
  let transform
      (pair : (Fin extractedDimension → R) × (Fin sampleCount → R)) :
      Fin sampleCount → R :=
    vecMul pair.1 sourceMatrix + pair.2
  let mapRows
      (pairs : Fin rowCount →
        (Fin extractedDimension → R) × (Fin sampleCount → R)) :
      Fin rowCount → Fin sampleCount → R :=
    fun index => transform (pairs index)
  let finish
      (pairs : Fin rowCount →
        (Fin extractedDimension → R) × (Fin sampleCount → R)) :
      Matrix (Fin rowCount) (Fin sampleCount) R :=
    Matrix.of (mapRows pairs)
  let independentSecrets :
      ProbComp (Matrix (Fin rowCount) (Fin extractedDimension) R) :=
    sampleRowMatrix rowCount extractedDimension fun _ => secretVector
  let continuation
      (secretMatrix : Matrix (Fin rowCount) (Fin extractedDimension) R) :
      ProbComp (Matrix (Fin rowCount) (Fin sampleCount) R) := do
    let errorMatrix ← matrixErrorSampler rowCount sampleCount narrowErrorSampler
    return secretMatrix * sourceMatrix + errorMatrix
  have hsecrets :
      𝒟[independentSecrets] =
        𝒟[$ᵗ Matrix (Fin rowCount) (Fin extractedDimension) R] := by
    simpa [independentSecrets, secretVector] using
      (evalDist_sampleRowMatrix_uniform (R := R) rowCount extractedDimension)
  have hreplace :
      𝒟[($ᵗ Matrix (Fin rowCount) (Fin extractedDimension) R) >>= continuation] =
        𝒟[independentSecrets >>= continuation] := by
    rw [evalDist_bind, evalDist_bind, ← hsecrets]
  have hzip :
      𝒟[zipRows <$> separateRows] = 𝒟[pairedRows] := by
    simpa [zipRows, separateRows, secretRows, errorRows, pairedRows,
      pairSampler, secretVector, errorVector] using
      (FormalProof4FHE.FiniteProduct.evalDist_fin_mOfFn_zip
        rowCount (fun _ => secretVector) (fun _ => errorVector))
  have hsource :
      (independentSecrets >>= continuation) =
        finish <$> (zipRows <$> separateRows) := by
    simp only [independentSecrets, continuation, sampleRowMatrix,
      matrixErrorSampler, ProbComp.sampleIID, secretRows, errorRows,
      separateRows, map_eq_bind_pure_comp, bind_assoc, pure_bind,
      Function.comp_apply]
    apply bind_congr
    intro secrets
    apply bind_congr
    intro errors
    congr 1
  have hrealRow : transform <$> pairSampler =
      realMaskRow sourceMatrix narrowErrorSampler := by
    simp [transform, pairSampler, secretVector, errorVector, realMaskRow,
      map_eq_bind_pure_comp, bind_assoc]
  have hmap := FormalProof4FHE.FiniteProduct.map_fin_mOfFn_const
    rowCount pairSampler transform
  have hfinish : finish <$> pairedRows =
      rowHybridRows rowCount extractedDimension sampleCount 0
        narrowErrorSampler sourceMatrix := by
    calc
      finish <$> pairedRows = Matrix.of <$> (mapRows <$> pairedRows) := by
        simp [finish, mapRows, Functor.map_map]
      _ = Matrix.of <$>
          Fin.mOfFn rowCount (fun _ => transform <$> pairSampler) := by
        rw [hmap]
      _ = _ := by
        simp [rowHybridRows, sampleRowMatrix, hrealRow]
  calc
    _ = 𝒟[independentSecrets >>= continuation] := by
      simpa [continuation] using hreplace
    _ = 𝒟[finish <$> (zipRows <$> separateRows)] :=
      congrArg evalDist hsource
    _ = 𝒟[finish <$> pairedRows] :=
      evalDist_map_eq_of_evalDist_eq hzip finish
    _ = _ := congrArg evalDist hfinish

/-- The zero-th row hybrid is exactly the real branch of the matrix-mask problem. -/
theorem evalDist_matrixMask_game0_rowHybrid {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (rowCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (matrixMaskProblem (R := R) rowCount extractedDimension sampleCount
        narrowErrorSampler)) :
    𝒟[LearningWithErrors.game0
        (matrixMaskProblem (R := R) rowCount extractedDimension sampleCount
          narrowErrorSampler) adversary] =
      𝒟[rowHybridGame rowCount extractedDimension sampleCount 0
        narrowErrorSampler adversary] := by
  let sourceMatrices :
      ProbComp (Matrix (Fin extractedDimension) (Fin sampleCount) R) :=
    $ᵗ Matrix (Fin extractedDimension) (Fin sampleCount) R
  let generatedRows
      (sourceMatrix : Matrix (Fin extractedDimension) (Fin sampleCount) R) :
      ProbComp (Matrix (Fin rowCount) (Fin sampleCount) R) := do
    let secretMatrix ←
      $ᵗ Matrix (Fin rowCount) (Fin extractedDimension) R
    let errorMatrix ← matrixErrorSampler rowCount sampleCount narrowErrorSampler
    return secretMatrix * sourceMatrix + errorMatrix
  let finish
      (sourceMatrix : Matrix (Fin extractedDimension) (Fin sampleCount) R)
      (rows : Matrix (Fin rowCount) (Fin sampleCount) R) : ProbComp Bool :=
    adversary (sourceMatrix, rows)
  simp only [LearningWithErrors.game0, LearningWithErrors.distr,
    matrixMaskProblem, rowHybridGame, bind_assoc, pure_bind]
  apply evalDist_bind_congr' sourceMatrices
  intro sourceMatrix
  have hpost :
      𝒟[generatedRows sourceMatrix >>= finish sourceMatrix] =
        𝒟[rowHybridRows rowCount extractedDimension sampleCount 0
          narrowErrorSampler sourceMatrix >>= finish sourceMatrix] := by
    have hrows := evalDist_matrixMask_real_rows
      rowCount extractedDimension sampleCount narrowErrorSampler sourceMatrix
    calc
      _ = 𝒟[generatedRows sourceMatrix] >>=
            fun rows ↦ 𝒟[finish sourceMatrix rows] :=
        evalDist_bind _ _
      _ = 𝒟[rowHybridRows rowCount extractedDimension sampleCount 0
              narrowErrorSampler sourceMatrix] >>=
            fun rows ↦ 𝒟[finish sourceMatrix rows] := by
        rw [show 𝒟[generatedRows sourceMatrix] =
            𝒟[rowHybridRows rowCount extractedDimension sampleCount 0
              narrowErrorSampler sourceMatrix] by
          simpa [generatedRows] using hrows]
      _ = _ := (evalDist_bind _ _).symm
  simpa [generatedRows, finish, bind_assoc] using hpost

/-- The absolute gap between two endpoints is at most the sum of its adjacent gaps. -/
theorem abs_sub_le_sum_adjacent (values : ℕ → ℝ) (count : ℕ) :
    |values 0 - values count| ≤
      ∑ index ∈ Finset.range count, |values index - values (index + 1)| := by
  rw [← Finset.sum_range_sub' values count]
  exact Finset.abs_sum_le_sum_abs
    (fun index => values index - values (index + 1)) (Finset.range count)

/-- Matrix-mask advantage is exactly the gap between the first and last row hybrids. -/
theorem matrixMask_advantage_eq_rowHybrid_endpoints {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (rowCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (matrixMaskProblem (R := R) rowCount extractedDimension sampleCount
        narrowErrorSampler)) :
    LearningWithErrors.advantage
        (matrixMaskProblem (R := R) rowCount extractedDimension sampleCount
          narrowErrorSampler) adversary =
      |(Pr[= true |
          rowHybridGame rowCount extractedDimension sampleCount 0
            narrowErrorSampler adversary]).toReal -
        (Pr[= true |
          rowHybridGame rowCount extractedDimension sampleCount rowCount
            narrowErrorSampler adversary]).toReal| := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage
  rw [probOutput_congr rfl
      (evalDist_matrixMask_game0_rowHybrid rowCount extractedDimension sampleCount
        narrowErrorSampler adversary),
    probOutput_congr rfl
      (evalDist_rowHybridGame_all_uniform rowCount extractedDimension sampleCount
        narrowErrorSampler adversary).symm]

/-- Exact randomized hybrid identity: matrix-mask advantage is `rowCount` times the advantage of
one ordinary-LWE reduction that chooses the transitioned row uniformly.

This retains cancellation among adjacent row gaps, unlike the usual sum-of-absolute-gaps bound. -/
theorem matrixMask_advantage_eq_card_mul_randomRowLWE {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (rowCount extractedDimension sampleCount : ℕ) [NeZero rowCount]
    (narrowErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (matrixMaskProblem (R := R) rowCount extractedDimension sampleCount
        narrowErrorSampler)) :
    LearningWithErrors.advantage
        (matrixMaskProblem (R := R) rowCount extractedDimension sampleCount
          narrowErrorSampler) adversary =
      (rowCount : ℝ) *
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
            ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler)
          (randomRowHybridReduction rowCount extractedDimension sampleCount
            narrowErrorSampler adversary) := by
  let values (replaced : ℕ) : ℝ :=
    (Pr[= true |
      rowHybridGame rowCount extractedDimension sampleCount replaced
        narrowErrorSampler adversary]).toReal
  rw [matrixMask_advantage_eq_rowHybrid_endpoints rowCount extractedDimension sampleCount
      narrowErrorSampler adversary,
    FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage
  rw [probOutput_congr rfl
      (evalDist_randomRowHybridReduction_game0 rowCount extractedDimension sampleCount
        narrowErrorSampler adversary),
    probOutput_congr rfl
      (evalDist_randomRowHybridReduction_game1 rowCount extractedDimension sampleCount
        narrowErrorSampler adversary),
    probOutput_bind_uniform_fintype_toReal,
    probOutput_bind_uniform_fintype_toReal]
  simp only [Fintype.card_fin]
  change |values 0 - values rowCount| =
    (rowCount : ℝ) *
      |(∑ coordinate : Fin rowCount, values coordinate.val) / (rowCount : ℝ) -
        (∑ coordinate : Fin rowCount, values (coordinate.val + 1)) / (rowCount : ℝ)|
  have htel :
      (∑ coordinate : Fin rowCount, values coordinate.val) -
          (∑ coordinate : Fin rowCount, values (coordinate.val + 1)) =
        values 0 - values rowCount := by
    have hlower :
        (∑ coordinate : Fin rowCount, values coordinate.val) =
          ∑ index ∈ Finset.range rowCount, values index := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro index hindex
      rw [dif_pos (Finset.mem_range.mp hindex)]
    have hupper :
        (∑ coordinate : Fin rowCount, values (coordinate.val + 1)) =
          ∑ index ∈ Finset.range rowCount, values (index + 1) := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro index hindex
      rw [dif_pos (Finset.mem_range.mp hindex)]
    rw [hlower, hupper, ← Finset.sum_sub_distrib, Finset.sum_range_sub']
  have hrowCount : (0 : ℝ) < rowCount := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne rowCount))
  rw [← sub_div, htel, abs_div, abs_of_pos hrowCount]
  field_simp

/-- A matrix-mask distinguisher reduces row by row to ordinary narrow-error LWE. -/
theorem matrixMask_advantage_le_sum_rowHybridLWE {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (rowCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (matrixMaskProblem (R := R) rowCount extractedDimension sampleCount
        narrowErrorSampler)) :
    LearningWithErrors.advantage
        (matrixMaskProblem (R := R) rowCount extractedDimension sampleCount
          narrowErrorSampler) adversary ≤
      ∑ coordinate : Fin rowCount,
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
            ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler)
          (rowHybridReduction rowCount extractedDimension sampleCount
            narrowErrorSampler coordinate adversary) := by
  let values (replaced : ℕ) : ℝ :=
    (Pr[= true |
      rowHybridGame rowCount extractedDimension sampleCount replaced
        narrowErrorSampler adversary]).toReal
  rw [matrixMask_advantage_eq_rowHybrid_endpoints
    rowCount extractedDimension sampleCount narrowErrorSampler adversary,
    Finset.sum_fin_eq_sum_range]
  change |values 0 - values rowCount| ≤ _
  calc
    _ ≤ ∑ index ∈ Finset.range rowCount,
        |values index - values (index + 1)| :=
      abs_sub_le_sum_adjacent values rowCount
    _ = _ := by
      apply Finset.sum_congr rfl
      intro index hindex
      have hlt : index < rowCount := Finset.mem_range.mp hindex
      rw [dif_pos hlt]
      let coordinate : Fin rowCount := ⟨index, hlt⟩
      symm
      simpa [values, coordinate] using
        (rowHybridReduction_advantage_eq rowCount extractedDimension sampleCount
          narrowErrorSampler coordinate adversary)

/-- Tight end-to-end ordinary-LWE reduction preserving both computational and statistical
cancellation.  Only one family of narrow-LWE row reductions is needed: it targets the combined
signed matrix distinguisher. -/
theorem advantage_le_combined_ordinaryLWE_add_jointGap {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)) :
    LearningWithErrors.advantage
        (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)
        adversary ≤
      2 * (∑ coordinate : Fin (blockCount * blockLength),
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
            ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler)
          (rowHybridReduction (blockCount * blockLength) extractedDimension sampleCount
            narrowErrorSampler coordinate
            (combinedMaskReduction blockLength blockCount extractedDimension sampleCount
              narrowErrorSampler wideErrorSampler adversary))) +
        jointStatisticalGap blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler +
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
            ($ᵗ (Fin extractedDimension → R)) wideErrorSampler)
          (extractedLWReduction blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler adversary) := by
  calc
    _ ≤ 2 * LearningWithErrors.advantage
          (matrixMaskProblem (R := R) (blockCount * blockLength)
            extractedDimension sampleCount narrowErrorSampler)
          (combinedMaskReduction blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler adversary) +
        jointStatisticalGap blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler +
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
            ($ᵗ (Fin extractedDimension → R)) wideErrorSampler)
          (extractedLWReduction blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler adversary) :=
      advantage_le_two_combinedMask_add_lwe_add_jointGap blockLength blockCount
        extractedDimension sampleCount narrowErrorSampler wideErrorSampler adversary
    _ ≤ _ := by
      gcongr
      exact matrixMask_advantage_le_sum_rowHybridLWE
        (blockCount * blockLength) extractedDimension sampleCount narrowErrorSampler
        (combinedMaskReduction blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler adversary)

/-- Sharpest reduction-specific ordinary-LWE bound in this development.

For a nonempty secret-coordinate set, both masking sides and every row transition are folded into
one randomized narrow-LWE adversary.  Thus no triangle inequality is used inside the computational
masking part. -/
theorem advantage_le_randomized_ordinaryLWE_add_jointGap {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    [NeZero (blockCount * blockLength)]
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)) :
    LearningWithErrors.advantage
        (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)
        adversary ≤
      2 * ((blockCount * blockLength : ℕ) : ℝ) *
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
            ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler)
          (randomRowHybridReduction (blockCount * blockLength) extractedDimension sampleCount
            narrowErrorSampler
            (combinedMaskReduction blockLength blockCount extractedDimension sampleCount
              narrowErrorSampler wideErrorSampler adversary)) +
        jointStatisticalGap blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler +
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
            ($ᵗ (Fin extractedDimension → R)) wideErrorSampler)
          (extractedLWReduction blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler adversary) := by
  calc
    _ ≤ 2 * LearningWithErrors.advantage
          (matrixMaskProblem (R := R) (blockCount * blockLength)
            extractedDimension sampleCount narrowErrorSampler)
          (combinedMaskReduction blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler adversary) +
        jointStatisticalGap blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler +
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
            ($ᵗ (Fin extractedDimension → R)) wideErrorSampler)
          (extractedLWReduction blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler adversary) :=
      advantage_le_two_combinedMask_add_lwe_add_jointGap blockLength blockCount
        extractedDimension sampleCount narrowErrorSampler wideErrorSampler adversary
    _ = _ := by
      rw [matrixMask_advantage_eq_card_mul_randomRowLWE
        (blockCount * blockLength) extractedDimension sampleCount narrowErrorSampler
        (combinedMaskReduction blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler adversary)]
      ring

/-- The sharp reduction-specific bound, capped at one. -/
theorem advantage_le_randomized_ordinaryLWE_add_jointGap_capped {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    [NeZero (blockCount * blockLength)]
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)) :
    LearningWithErrors.advantage
        (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)
        adversary ≤
      min 1
        (2 * ((blockCount * blockLength : ℕ) : ℝ) *
            LearningWithErrors.advantage
              (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
                ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler)
              (randomRowHybridReduction (blockCount * blockLength) extractedDimension sampleCount
                narrowErrorSampler
                (combinedMaskReduction blockLength blockCount extractedDimension sampleCount
                  narrowErrorSampler wideErrorSampler adversary)) +
          jointStatisticalGap blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler +
          LearningWithErrors.advantage
            (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
              ($ᵗ (Fin extractedDimension → R)) wideErrorSampler)
            (extractedLWReduction blockLength blockCount extractedDimension sampleCount
              narrowErrorSampler wideErrorSampler adversary)) := by
  apply le_min
  · exact FormalProof4FHE.LWE.advantage_le_one _ _
  · exact advantage_le_randomized_ordinaryLWE_add_jointGap blockLength blockCount
      extractedDimension sampleCount narrowErrorSampler wideErrorSampler adversary

/-- Sharp fully explicit reduction-specific bound using the exact finite leftover-hash constant. -/
theorem advantage_le_randomized_ordinaryLWE_add_gaps_tight {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    [NeZero (blockCount * blockLength)]
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)) :
    LearningWithErrors.advantage
        (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)
        adversary ≤
      min 1
        (2 * ((blockCount * blockLength : ℕ) : ℝ) *
            LearningWithErrors.advantage
              (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
                ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler)
              (randomRowHybridReduction (blockCount * blockLength) extractedDimension sampleCount
                narrowErrorSampler
                (combinedMaskReduction blockLength blockCount extractedDimension sampleCount
                  narrowErrorSampler wideErrorSampler adversary)) +
          noiseAbsorptionGap blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler +
          Real.sqrt
              (((Fintype.card R : ℝ) ^ extractedDimension - 1) /
                (blockLength + 1 : ℝ) ^ blockCount) /
            2 +
          LearningWithErrors.advantage
            (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
              ($ᵗ (Fin extractedDimension → R)) wideErrorSampler)
            (extractedLWReduction blockLength blockCount extractedDimension sampleCount
              narrowErrorSampler wideErrorSampler adversary)) := by
  apply le_min
  · exact FormalProof4FHE.LWE.advantage_le_one _ _
  · calc
      _ ≤ 2 * ((blockCount * blockLength : ℕ) : ℝ) *
            LearningWithErrors.advantage
              (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
                ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler)
              (randomRowHybridReduction (blockCount * blockLength) extractedDimension sampleCount
                narrowErrorSampler
                (combinedMaskReduction blockLength blockCount extractedDimension sampleCount
                  narrowErrorSampler wideErrorSampler adversary)) +
          jointStatisticalGap blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler +
          LearningWithErrors.advantage
            (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
              ($ᵗ (Fin extractedDimension → R)) wideErrorSampler)
            (extractedLWReduction blockLength blockCount extractedDimension sampleCount
              narrowErrorSampler wideErrorSampler adversary) :=
        advantage_le_randomized_ordinaryLWE_add_jointGap blockLength blockCount
          extractedDimension sampleCount narrowErrorSampler wideErrorSampler adversary
      _ ≤ _ := by
        have hgap := jointStatisticalGap_le_noise_add_leftover_tight blockLength blockCount
          extractedDimension sampleCount narrowErrorSampler wideErrorSampler
        linarith

/-- End-to-end reduction using only ordinary LWE, plus the two explicit statistical gaps.

There are two narrow-error row hybrids (one on each side of the main game sequence), while the
extracted-secret transition is one wide-error ordinary-LWE instance. -/
theorem advantage_le_ordinaryLWE_add_gaps {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)) :
    LearningWithErrors.advantage
        (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)
        adversary ≤
      (∑ coordinate : Fin (blockCount * blockLength),
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
            ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler)
          (rowHybridReduction (blockCount * blockLength) extractedDimension sampleCount
            narrowErrorSampler coordinate
            (realMaskReduction blockLength blockCount extractedDimension sampleCount
              narrowErrorSampler wideErrorSampler adversary))) +
        noiseAbsorptionGap blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler +
        Real.sqrt
            ((Fintype.card R : ℝ) ^ extractedDimension /
              (blockLength + 1 : ℝ) ^ blockCount) /
          2 +
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
            ($ᵗ (Fin extractedDimension → R)) wideErrorSampler)
          (extractedLWReduction blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler adversary) +
        (∑ coordinate : Fin (blockCount * blockLength),
          LearningWithErrors.advantage
            (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
              ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler)
            (rowHybridReduction (blockCount * blockLength) extractedDimension sampleCount
              narrowErrorSampler coordinate
              (uniformMaskReduction blockLength blockCount extractedDimension sampleCount
                narrowErrorSampler wideErrorSampler adversary))) := by
  calc
    _ ≤ LearningWithErrors.advantage
          (matrixMaskProblem (R := R) (blockCount * blockLength)
            extractedDimension sampleCount narrowErrorSampler)
          (realMaskReduction blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler adversary) +
        noiseAbsorptionGap blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler +
        Real.sqrt
            ((Fintype.card R : ℝ) ^ extractedDimension /
              (blockLength + 1 : ℝ) ^ blockCount) /
          2 +
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
            ($ᵗ (Fin extractedDimension → R)) wideErrorSampler)
          (extractedLWReduction blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler adversary) +
        LearningWithErrors.advantage
          (matrixMaskProblem (R := R) (blockCount * blockLength)
            extractedDimension sampleCount narrowErrorSampler)
          (uniformMaskReduction blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler adversary) :=
      advantage_le_matrixMask_add_lwe_add_gaps blockLength blockCount
        extractedDimension sampleCount narrowErrorSampler wideErrorSampler adversary
    _ ≤ _ := by
      gcongr
      · exact matrixMask_advantage_le_sum_rowHybridLWE
          (blockCount * blockLength) extractedDimension sampleCount narrowErrorSampler
          (realMaskReduction blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler adversary)
      · exact matrixMask_advantage_le_sum_rowHybridLWE
          (blockCount * blockLength) extractedDimension sampleCount narrowErrorSampler
          (uniformMaskReduction blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler adversary)

/-- Packaged concrete-security corollary.

Given concrete bounds for ordinary narrow- and wide-error LWE and for the analytic
noise-absorption distance, the block-binary loss is two row hybrids, one wide-error LWE call,
the noise bound, and the explicit leftover-hash term. -/
theorem advantage_le_of_ordinaryLWEBounds {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem (R := R) blockLength blockCount sampleCount wideErrorSampler))
    (narrowBound wideBound noiseBound : ℝ)
    (hNarrow : ∀ reduction : LearningWithErrors.Adversary
      (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
        ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler),
      LearningWithErrors.advantage
        (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
          ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler)
        reduction ≤ narrowBound)
    (hWide : ∀ reduction : LearningWithErrors.Adversary
      (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
        ($ᵗ (Fin extractedDimension → R)) wideErrorSampler),
      LearningWithErrors.advantage
        (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
          ($ᵗ (Fin extractedDimension → R)) wideErrorSampler)
        reduction ≤ wideBound)
    (hNoise :
      noiseAbsorptionGap blockLength blockCount extractedDimension sampleCount
        narrowErrorSampler wideErrorSampler ≤ noiseBound) :
    LearningWithErrors.advantage
        (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)
        adversary ≤
      2 * ((blockCount * blockLength : ℕ) : ℝ) * narrowBound +
        noiseBound +
        Real.sqrt
            ((Fintype.card R : ℝ) ^ extractedDimension /
              (blockLength + 1 : ℝ) ^ blockCount) /
          2 +
        wideBound := by
  have hreal :
      (∑ coordinate : Fin (blockCount * blockLength),
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
            ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler)
          (rowHybridReduction (blockCount * blockLength) extractedDimension sampleCount
            narrowErrorSampler coordinate
            (realMaskReduction blockLength blockCount extractedDimension sampleCount
              narrowErrorSampler wideErrorSampler adversary))) ≤
        ((blockCount * blockLength : ℕ) : ℝ) * narrowBound := by
    calc
      _ ≤ ∑ _coordinate : Fin (blockCount * blockLength), narrowBound := by
        apply Finset.sum_le_sum
        intro coordinate _
        exact hNarrow _
      _ = _ := by simp
  have huniform :
      (∑ coordinate : Fin (blockCount * blockLength),
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
            ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler)
          (rowHybridReduction (blockCount * blockLength) extractedDimension sampleCount
            narrowErrorSampler coordinate
            (uniformMaskReduction blockLength blockCount extractedDimension sampleCount
              narrowErrorSampler wideErrorSampler adversary))) ≤
        ((blockCount * blockLength : ℕ) : ℝ) * narrowBound := by
    calc
      _ ≤ ∑ _coordinate : Fin (blockCount * blockLength), narrowBound := by
        apply Finset.sum_le_sum
        intro coordinate _
        exact hNarrow _
      _ = _ := by simp
  have hwide :
      LearningWithErrors.advantage
          (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
            ($ᵗ (Fin extractedDimension → R)) wideErrorSampler)
          (extractedLWReduction blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler adversary) ≤ wideBound :=
    hWide _
  calc
    _ ≤ (∑ coordinate : Fin (blockCount * blockLength),
          LearningWithErrors.advantage
            (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
              ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler)
            (rowHybridReduction (blockCount * blockLength) extractedDimension sampleCount
              narrowErrorSampler coordinate
              (realMaskReduction blockLength blockCount extractedDimension sampleCount
                narrowErrorSampler wideErrorSampler adversary))) +
        noiseAbsorptionGap blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler +
        Real.sqrt
            ((Fintype.card R : ℝ) ^ extractedDimension /
              (blockLength + 1 : ℝ) ^ blockCount) /
          2 +
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
            ($ᵗ (Fin extractedDimension → R)) wideErrorSampler)
          (extractedLWReduction blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler adversary) +
        (∑ coordinate : Fin (blockCount * blockLength),
          LearningWithErrors.advantage
            (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
              ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler)
            (rowHybridReduction (blockCount * blockLength) extractedDimension sampleCount
              narrowErrorSampler coordinate
              (uniformMaskReduction blockLength blockCount extractedDimension sampleCount
                narrowErrorSampler wideErrorSampler adversary))) :=
      advantage_le_ordinaryLWE_add_gaps blockLength blockCount extractedDimension sampleCount
        narrowErrorSampler wideErrorSampler adversary
    _ ≤ ((blockCount * blockLength : ℕ) : ℝ) * narrowBound +
        noiseBound +
        Real.sqrt
            ((Fintype.card R : ℝ) ^ extractedDimension /
              (blockLength + 1 : ℝ) ^ blockCount) /
          2 +
        wideBound +
        ((blockCount * blockLength : ℕ) : ℝ) * narrowBound := by
      gcongr
    _ = _ := by ring

/-- Packaged bound using the cancellation-preserving computational reduction and an exact joint
statistical bound. -/
theorem advantage_le_of_ordinaryLWEBounds_joint {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem (R := R) blockLength blockCount sampleCount wideErrorSampler))
    (narrowBound wideBound jointBound : ℝ)
    (hNarrow : ∀ reduction : LearningWithErrors.Adversary
      (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
        ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler),
      LearningWithErrors.advantage
        (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
          ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler)
        reduction ≤ narrowBound)
    (hWide : ∀ reduction : LearningWithErrors.Adversary
      (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
        ($ᵗ (Fin extractedDimension → R)) wideErrorSampler),
      LearningWithErrors.advantage
        (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
          ($ᵗ (Fin extractedDimension → R)) wideErrorSampler)
        reduction ≤ wideBound)
    (hJoint :
      jointStatisticalGap blockLength blockCount extractedDimension sampleCount
        narrowErrorSampler wideErrorSampler ≤ jointBound) :
    LearningWithErrors.advantage
        (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)
        adversary ≤
      2 * ((blockCount * blockLength : ℕ) : ℝ) * narrowBound +
        jointBound + wideBound := by
  have hcombined :
      (∑ coordinate : Fin (blockCount * blockLength),
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
            ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler)
          (rowHybridReduction (blockCount * blockLength) extractedDimension sampleCount
            narrowErrorSampler coordinate
            (combinedMaskReduction blockLength blockCount extractedDimension sampleCount
              narrowErrorSampler wideErrorSampler adversary))) ≤
        ((blockCount * blockLength : ℕ) : ℝ) * narrowBound := by
    calc
      _ ≤ ∑ _coordinate : Fin (blockCount * blockLength), narrowBound := by
        apply Finset.sum_le_sum
        intro coordinate _
        exact hNarrow _
      _ = _ := by simp
  have hwide :
      LearningWithErrors.advantage
          (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
            ($ᵗ (Fin extractedDimension → R)) wideErrorSampler)
          (extractedLWReduction blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler adversary) ≤ wideBound :=
    hWide _
  calc
    _ ≤ 2 * (∑ coordinate : Fin (blockCount * blockLength),
          LearningWithErrors.advantage
            (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
              ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler)
            (rowHybridReduction (blockCount * blockLength) extractedDimension sampleCount
              narrowErrorSampler coordinate
              (combinedMaskReduction blockLength blockCount extractedDimension sampleCount
                narrowErrorSampler wideErrorSampler adversary))) +
        jointStatisticalGap blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler +
        LearningWithErrors.advantage
          (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
            ($ᵗ (Fin extractedDimension → R)) wideErrorSampler)
          (extractedLWReduction blockLength blockCount extractedDimension sampleCount
            narrowErrorSampler wideErrorSampler adversary) :=
      advantage_le_combined_ordinaryLWE_add_jointGap blockLength blockCount
        extractedDimension sampleCount narrowErrorSampler wideErrorSampler adversary
    _ ≤ 2 * (((blockCount * blockLength : ℕ) : ℝ) * narrowBound) +
        jointBound + wideBound := by gcongr
    _ = _ := by ring

/-- The joint bound, capped by the universal information-theoretic upper bound one. -/
theorem advantage_le_of_ordinaryLWEBounds_joint_capped {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem (R := R) blockLength blockCount sampleCount wideErrorSampler))
    (narrowBound wideBound jointBound : ℝ)
    (hNarrow : ∀ reduction : LearningWithErrors.Adversary
      (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
        ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler),
      LearningWithErrors.advantage
        (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
          ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler)
        reduction ≤ narrowBound)
    (hWide : ∀ reduction : LearningWithErrors.Adversary
      (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
        ($ᵗ (Fin extractedDimension → R)) wideErrorSampler),
      LearningWithErrors.advantage
        (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
          ($ᵗ (Fin extractedDimension → R)) wideErrorSampler)
        reduction ≤ wideBound)
    (hJoint :
      jointStatisticalGap blockLength blockCount extractedDimension sampleCount
        narrowErrorSampler wideErrorSampler ≤ jointBound) :
    LearningWithErrors.advantage
        (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)
        adversary ≤
      min 1 (2 * ((blockCount * blockLength : ℕ) : ℝ) * narrowBound +
        jointBound + wideBound) := by
  apply le_min
  · exact FormalProof4FHE.LWE.advantage_le_one _ _
  · exact advantage_le_of_ordinaryLWEBounds_joint blockLength blockCount
      extractedDimension sampleCount narrowErrorSampler wideErrorSampler adversary
      narrowBound wideBound jointBound hNarrow hWide hJoint

/-- Fully discharged sharp concrete bound.

Compared with the basic corollary, this uses the exact `(card R)^d - 1` finite leftover-hash
constant and caps the result at one.  Its ordinary-LWE loss remains `2 * blockCount * blockLength`
under a single uniform bound; the preceding reduction-specific theorem can be smaller because it
retains cancellation. -/
theorem advantage_le_of_ordinaryLWEBounds_tight {R : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount extractedDimension sampleCount : ℕ)
    (narrowErrorSampler wideErrorSampler : ProbComp R)
    (adversary : LearningWithErrors.Adversary
      (problem (R := R) blockLength blockCount sampleCount wideErrorSampler))
    (narrowBound wideBound noiseBound : ℝ)
    (hNarrow : ∀ reduction : LearningWithErrors.Adversary
      (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
        ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler),
      LearningWithErrors.advantage
        (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
          ($ᵗ (Fin extractedDimension → R)) narrowErrorSampler)
        reduction ≤ narrowBound)
    (hWide : ∀ reduction : LearningWithErrors.Adversary
      (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
        ($ᵗ (Fin extractedDimension → R)) wideErrorSampler),
      LearningWithErrors.advantage
        (FormalProof4FHE.LWE.batchProblem extractedDimension sampleCount
          ($ᵗ (Fin extractedDimension → R)) wideErrorSampler)
        reduction ≤ wideBound)
    (hNoise :
      noiseAbsorptionGap blockLength blockCount extractedDimension sampleCount
        narrowErrorSampler wideErrorSampler ≤ noiseBound) :
    LearningWithErrors.advantage
        (problem (R := R) blockLength blockCount sampleCount wideErrorSampler)
        adversary ≤
      min 1
        (2 * ((blockCount * blockLength : ℕ) : ℝ) * narrowBound +
          noiseBound +
          Real.sqrt
              (((Fintype.card R : ℝ) ^ extractedDimension - 1) /
                (blockLength + 1 : ℝ) ^ blockCount) /
            2 +
          wideBound) := by
  let leftoverBound : ℝ := Real.sqrt
    (((Fintype.card R : ℝ) ^ extractedDimension - 1) /
      (blockLength + 1 : ℝ) ^ blockCount) / 2
  have hSplit :
      jointStatisticalGap blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler ≤
        noiseAbsorptionGap blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler + leftoverBound := by
    simpa [leftoverBound] using
      (jointStatisticalGap_le_noise_add_leftover_tight blockLength blockCount
        extractedDimension sampleCount narrowErrorSampler wideErrorSampler)
  have hJoint :
      jointStatisticalGap blockLength blockCount extractedDimension sampleCount
          narrowErrorSampler wideErrorSampler ≤ noiseBound + leftoverBound :=
    hSplit.trans (add_le_add_left hNoise leftoverBound)
  simpa [leftoverBound, add_assoc] using
    (advantage_le_of_ordinaryLWEBounds_joint_capped blockLength blockCount
      extractedDimension sampleCount narrowErrorSampler wideErrorSampler adversary
      narrowBound wideBound (noiseBound + leftoverBound) hNarrow hWide hJoint)

end FormalProof4FHE.BlockBinary
