/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.ParallelBatch
import FormalProof4FHE.Probability.SquaredBias
import FormalProof4FHE.RLWE.Security
import FormalProof4FHE.SharedRandomness.Reduction

/-!
# Binary and Ternary Quadratic KDM Security from Interval-Masked RLWE

This module formalizes the interval-mask construction from `rlwecircular.md`.  A short secret `S`
and an independent interval mask `Z` determine the public hint `H = S - Z`.  The public affine map

`A = C - 2H`, `B = Y - H²`

sends a real hinted-RLWE sample `Y = C*S + E` exactly to

`B = A*S + S² + E - Z²`,

and sends the random hinted branch exactly to uniform.  A second ordinary-RLWE reduction proves
pseudorandomness of the zero-message distribution with the same error `E - Z²`.

The remaining hinted game is reduced to two ordinary RLWE blocks sharing one secret.  The reduction
samples a uniform hint code and uses the two-copy squared-bias test from
`FormalProof4FHE.Probability.SquaredBias`.  An injective interval encoding gives the concrete loss

`sqrt (2 * ((M + L - 1) / M)^n * Adv_RLWE)`,

where `L = 2` is binary and `L = 3` is ternary.  Thus `M ≥ n` gives a constant concrete loss;
the theorem does not claim the gadget-weighted extension, whose error contains `-g*Z²`.
-/

open Matrix OracleComp

namespace FormalProof4FHE.RLWE.IntervalMaskedQuadratic

noncomputable section

/-! ## Generic finite interval encoding -/

/-- Data needed by the finite reduction.  The hint code is public; `hintValue` is the ring element
used by the affine transformation.  Injectivity of `(hint, secret)` as a function of
`(secret, mask)` is the posterior-counting fact used in the quantitative reduction. -/
structure Encoding (R Secret Mask Hint : Type) [Sub R] where
  secretValue : Secret → R
  maskValue : Mask → R
  hint : Secret → Mask → Hint
  hintValue : Hint → R
  hintValue_hint : ∀ secret mask,
    hintValue (hint secret mask) = secretValue secret - maskValue mask
  hintSecret_injective : Function.Injective
    (fun value : Secret × Mask ↦ (hint value.1 value.2, value.1))

/-- A hinted ring-LWE transcript `(H,C,Y)`. -/
structure HintTranscript (Hint R : Type) where
  hint : Hint
  mask : R
  body : R

/-- A two-component ring-LWE transcript `(A,B)`. -/
abbrev Transcript (R : Type) := R × R

/-- A Boolean distinguisher for hinted transcripts. -/
abbrev HintDistinguisher (Hint R : Type) := HintTranscript Hint R → ProbComp Bool

/-- A Boolean distinguisher for ordinary two-component transcripts. -/
abbrev Distinguisher (R : Type) := Transcript R → ProbComp Bool

/-- One real ring-LWE block for a fixed secret. -/
def fixedSecretRealBlock
    {R Secret Mask Hint : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (encoding : Encoding R Secret Mask Hint) (errorSampler : ProbComp R)
    (secret : Secret) : ProbComp (Transcript R) := do
  let publicMask ← $ᵗ R
  let error ← errorSampler
  return (publicMask, publicMask * encoding.secretValue secret + error)

/-- One ideal uniform block. -/
def uniformBlock {R : Type} [SampleableType R] : ProbComp (Transcript R) :=
  $ᵗ (R × R)

/-- The real hinted distribution. -/
def hintRealView
    {R Secret Mask Hint : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    [SampleableType Secret] [SampleableType Mask]
    (encoding : Encoding R Secret Mask Hint) (errorSampler : ProbComp R) :
    ProbComp (HintTranscript Hint R) := do
  let secret ← $ᵗ Secret
  let intervalMask ← $ᵗ Mask
  let sample ← fixedSecretRealBlock encoding errorSampler secret
  return ⟨encoding.hint secret intervalMask, sample.1, sample.2⟩

/-- The hinted random distribution retains the genuine hint but replaces the ring-LWE body. -/
def hintRandomView
    {R Secret Mask Hint : Type}
    [Sub R] [SampleableType R] [SampleableType Secret] [SampleableType Mask]
    (encoding : Encoding R Secret Mask Hint) : ProbComp (HintTranscript Hint R) := do
  let secret ← $ᵗ Secret
  let intervalMask ← $ᵗ Mask
  let sample ← uniformBlock (R := R)
  return ⟨encoding.hint secret intervalMask, sample.1, sample.2⟩

/-- Hinted-RLWE distinguishing advantage. -/
def hintAdvantage
    {R Secret Mask Hint : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    [SampleableType Secret] [SampleableType Mask]
    (encoding : Encoding R Secret Mask Hint) (errorSampler : ProbComp R)
    (adversary : HintDistinguisher Hint R) : ℝ :=
  (hintRealView encoding errorSampler >>= adversary).boolDistAdvantage
    (hintRandomView encoding >>= adversary)

/-! ## Exact hinted-to-quadratic transformation -/

/-- Public affine transformation of a hinted transcript. -/
def quadraticTransform
    {R Secret Mask Hint : Type} [Ring R]
    (encoding : Encoding R Secret Mask Hint) (transcript : HintTranscript Hint R) :
    Transcript R :=
  (transcript.mask - 2 * encoding.hintValue transcript.hint,
    transcript.body - encoding.hintValue transcript.hint ^ 2)

/-- The real transformation identity. -/
theorem quadraticTransform_real
    {R Secret Mask Hint : Type} [CommRing R]
    (encoding : Encoding R Secret Mask Hint)
    (secret : Secret) (intervalMask : Mask) (publicMask error : R) :
    quadraticTransform encoding
        ⟨encoding.hint secret intervalMask,
          publicMask, publicMask * encoding.secretValue secret + error⟩ =
      (publicMask - 2 * (encoding.secretValue secret - encoding.maskValue intervalMask),
        (publicMask - 2 * (encoding.secretValue secret - encoding.maskValue intervalMask)) *
            encoding.secretValue secret + encoding.secretValue secret ^ 2 +
          (error - encoding.maskValue intervalMask ^ 2)) := by
  rw [quadraticTransform, encoding.hintValue_hint]
  apply Prod.ext
  · rfl
  · dsimp
    ring

/-- For a fixed hint, the random-branch transformation is bijective. -/
theorem quadraticTransform_pair_bijective
    {R Secret Mask Hint : Type} [Ring R]
    (encoding : Encoding R Secret Mask Hint) (hint : Hint) :
    Function.Bijective (fun sample : R × R ↦
      (sample.1 - 2 * encoding.hintValue hint,
        sample.2 - encoding.hintValue hint ^ 2)) := by
  let inverse : R × R → R × R := fun sample ↦
    (sample.1 + 2 * encoding.hintValue hint,
      sample.2 + encoding.hintValue hint ^ 2)
  refine Function.bijective_iff_has_inverse.mpr ⟨inverse, ?_, ?_⟩
  · intro sample
    apply Prod.ext <;> simp [inverse]
  · intro sample
    apply Prod.ext <;> simp [inverse]

/-- The target real quadratic distribution with exact secret law and error `E-Z²`. -/
def quadraticRealView
    {R Secret Mask Hint : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    [SampleableType Secret] [SampleableType Mask]
    (encoding : Encoding R Secret Mask Hint) (errorSampler : ProbComp R) :
    ProbComp (Transcript R) := do
  let secret ← $ᵗ Secret
  let intervalMask ← $ᵗ Mask
  let publicMask ← $ᵗ R
  let error ← errorSampler
  let targetMask := publicMask -
    2 * (encoding.secretValue secret - encoding.maskValue intervalMask)
  return (targetMask,
    targetMask * encoding.secretValue secret + encoding.secretValue secret ^ 2 +
      (error - encoding.maskValue intervalMask ^ 2))

/-- The target zero-message distribution with the same secret and error laws. -/
def zeroRealView
    {R Secret Mask Hint : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    [SampleableType Secret] [SampleableType Mask]
    (encoding : Encoding R Secret Mask Hint) (errorSampler : ProbComp R) :
    ProbComp (Transcript R) := do
  let secret ← $ᵗ Secret
  let intervalMask ← $ᵗ Mask
  let publicMask ← $ᵗ R
  let error ← errorSampler
  return (publicMask,
    publicMask * encoding.secretValue secret +
      (error - encoding.maskValue intervalMask ^ 2))

/-- The quadratic-versus-zero KDM advantage. -/
def kdmAdvantage
    {R Secret Mask Hint : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    [SampleableType Secret] [SampleableType Mask]
    (encoding : Encoding R Secret Mask Hint) (errorSampler : ProbComp R)
    (adversary : Distinguisher R) : ℝ :=
  (quadraticRealView encoding errorSampler >>= adversary).boolDistAdvantage
    (zeroRealView encoding errorSampler >>= adversary)

/-- Reduction from a quadratic KDM distinguisher to the hinted problem. -/
def quadraticReduction
    {R Secret Mask Hint : Type} [Ring R]
    (encoding : Encoding R Secret Mask Hint) (adversary : Distinguisher R) :
    HintDistinguisher Hint R :=
  fun transcript ↦ adversary (quadraticTransform encoding transcript)

theorem quadraticTransform_hintRealView_evalDist
    {R Secret Mask Hint : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Secret] [SampleableType Secret]
    [Fintype Mask] [SampleableType Mask]
    (encoding : Encoding R Secret Mask Hint) (errorSampler : ProbComp R) :
    evalDist (quadraticTransform encoding <$> hintRealView encoding errorSampler) =
      evalDist (quadraticRealView encoding errorSampler) := by
  simp only [hintRealView, fixedSecretRealBlock, quadraticRealView,
    map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  refine evalDist_bind_congr' ($ᵗ Secret) fun secret ↦ ?_
  refine evalDist_bind_congr' ($ᵗ Mask) fun intervalMask ↦ ?_
  refine evalDist_bind_congr' ($ᵗ R) fun publicMask ↦ ?_
  refine evalDist_bind_congr' errorSampler fun error ↦ ?_
  rw [quadraticTransform_real encoding secret intervalMask publicMask error]

theorem quadraticTransform_hintRandomView_evalDist
    {R Secret Mask Hint : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Secret] [SampleableType Secret]
    [Fintype Mask] [SampleableType Mask]
    (encoding : Encoding R Secret Mask Hint) :
    evalDist (quadraticTransform encoding <$> hintRandomView encoding) =
      evalDist (uniformBlock (R := R)) := by
  simp only [hintRandomView, uniformBlock, map_eq_bind_pure_comp,
    Function.comp_def, bind_assoc, pure_bind]
  calc
    evalDist (($ᵗ Secret) >>= fun secret ↦
        ($ᵗ Mask) >>= fun intervalMask ↦
          ($ᵗ (R × R)) >>= fun sample ↦
            pure (quadraticTransform encoding
              ⟨encoding.hint secret intervalMask, sample.1, sample.2⟩)) =
      evalDist (($ᵗ Secret) >>= fun _secret ↦
        ($ᵗ Mask) >>= fun _intervalMask ↦ $ᵗ (R × R)) := by
      refine evalDist_bind_congr' ($ᵗ Secret) fun secret ↦ ?_
      refine evalDist_bind_congr' ($ᵗ Mask) fun intervalMask ↦ ?_
      simpa only [quadraticTransform, map_eq_bind_pure_comp, Function.comp_def] using
        evalDist_map_bijective_uniform_cross
          (α := R × R) (β := R × R)
          (fun sample : R × R ↦
            (sample.1 - 2 * encoding.hintValue (encoding.hint secret intervalMask),
              sample.2 - encoding.hintValue (encoding.hint secret intervalMask) ^ 2))
          (quadraticTransform_pair_bijective encoding
            (encoding.hint secret intervalMask))
    _ = evalDist (($ᵗ Secret) >>= fun _secret ↦ $ᵗ (R × R)) := by
      refine evalDist_bind_congr' ($ᵗ Secret) fun _secret ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        ($ᵗ Mask) (by simp) _
    _ = evalDist ($ᵗ (R × R)) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        ($ᵗ Secret) (by simp) _

/-- The hinted real game of the public reduction is exactly the quadratic target game. -/
theorem quadraticReduction_real_evalDist
    {R Secret Mask Hint : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Secret] [SampleableType Secret]
    [Fintype Mask] [SampleableType Mask]
    (encoding : Encoding R Secret Mask Hint) (errorSampler : ProbComp R)
    (adversary : Distinguisher R) :
    evalDist (hintRealView encoding errorSampler >>=
        quadraticReduction encoding adversary) =
      evalDist (quadraticRealView encoding errorSampler >>= adversary) := by
  rw [show (hintRealView encoding errorSampler >>=
      quadraticReduction encoding adversary) =
      ((quadraticTransform encoding <$> hintRealView encoding errorSampler) >>=
        adversary) by
    have hReduction : quadraticReduction encoding adversary =
        fun transcript ↦ adversary (quadraticTransform encoding transcript) := rfl
    rw [hReduction]
    simp [map_eq_bind_pure_comp, bind_assoc]]
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (quadraticTransform_hintRealView_evalDist encoding errorSampler) adversary

/-- The hinted random game of the public reduction is exactly the uniform target game. -/
theorem quadraticReduction_random_evalDist
    {R Secret Mask Hint : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Secret] [SampleableType Secret]
    [Fintype Mask] [SampleableType Mask]
    (encoding : Encoding R Secret Mask Hint) (adversary : Distinguisher R) :
    evalDist (hintRandomView encoding >>= quadraticReduction encoding adversary) =
      evalDist (uniformBlock (R := R) >>= adversary) := by
  rw [show (hintRandomView encoding >>= quadraticReduction encoding adversary) =
      ((quadraticTransform encoding <$> hintRandomView encoding) >>= adversary) by
    have hReduction : quadraticReduction encoding adversary =
        fun transcript ↦ adversary (quadraticTransform encoding transcript) := rfl
    rw [hReduction]
    simp [map_eq_bind_pure_comp, bind_assoc]]
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (quadraticTransform_hintRandomView_evalDist encoding) adversary

/-- The quadratic real-versus-uniform advantage is exactly one hinted-RLWE advantage. -/
theorem quadratic_uniform_advantage_eq_hintAdvantage
    {R Secret Mask Hint : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Secret] [SampleableType Secret]
    [Fintype Mask] [SampleableType Mask]
    (encoding : Encoding R Secret Mask Hint) (errorSampler : ProbComp R)
    (adversary : Distinguisher R) :
    (quadraticRealView encoding errorSampler >>= adversary).boolDistAdvantage
        (uniformBlock (R := R) >>= adversary) =
      hintAdvantage encoding errorSampler (quadraticReduction encoding adversary) := by
  unfold hintAdvantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (quadraticReduction_real_evalDist encoding errorSampler adversary) true,
    evalDist_ext_iff.mp
      (quadraticReduction_random_evalDist encoding adversary) true]

/-! ## Ordinary RLWE reduction for the zero-message endpoint -/

/-- The scalar presentation of one ordinary ring-LWE sample with the selected secret law. -/
def oneSampleProblem
    {R Secret Mask Hint : Type}
    [CommRing R] [DecidableEq R] [SampleableType R] [SampleableType Secret]
    (encoding : Encoding R Secret Mask Hint) (errorSampler : ProbComp R) :
    LearningWithErrors.Problem R Secret R where
  sampleChallenge := $ᵗ R
  sampleSecret := $ᵗ Secret
  sampleError := errorSampler
  noiseless := fun secret publicMask ↦ publicMask * encoding.secretValue secret
  sampleUniform := $ᵗ R

/-- Subtract an independently sampled interval-mask square from an ordinary RLWE body. -/
def zeroReduction
    {R Secret Mask Hint : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    [SampleableType Secret] [SampleableType Mask]
    {errorSampler : ProbComp R}
    (encoding : Encoding R Secret Mask Hint) (adversary : Distinguisher R) :
    LearningWithErrors.Adversary (oneSampleProblem encoding errorSampler) :=
  fun transcript ↦ do
    let intervalMask ← $ᵗ Mask
    adversary (transcript.1,
      transcript.2 - encoding.maskValue intervalMask ^ 2)

theorem zeroReduction_real_evalDist
    {R Secret Mask Hint : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Secret] [SampleableType Secret]
    [Fintype Mask] [SampleableType Mask]
    (encoding : Encoding R Secret Mask Hint) (errorSampler : ProbComp R)
    (adversary : Distinguisher R) :
    evalDist (LearningWithErrors.game0 (oneSampleProblem encoding errorSampler)
        (zeroReduction encoding adversary)) =
      evalDist (zeroRealView encoding errorSampler >>= adversary) := by
  simp only [LearningWithErrors.game0, LearningWithErrors.distr, oneSampleProblem,
    zeroReduction, zeroRealView, bind_assoc, pure_bind]
  calc
    evalDist (($ᵗ R) >>= fun publicMask ↦
        ($ᵗ Secret) >>= fun secret ↦
          errorSampler >>= fun error ↦
            ($ᵗ Mask) >>= fun intervalMask ↦
              adversary (publicMask,
                publicMask * encoding.secretValue secret + error -
                  encoding.maskValue intervalMask ^ 2)) =
      evalDist (($ᵗ Secret) >>= fun secret ↦
        ($ᵗ R) >>= fun publicMask ↦
          errorSampler >>= fun error ↦
            ($ᵗ Mask) >>= fun intervalMask ↦
              adversary (publicMask,
                publicMask * encoding.secretValue secret + error -
                  encoding.maskValue intervalMask ^ 2)) :=
        evalDist_bind_bind_swap ($ᵗ R) ($ᵗ Secret) _
    _ = evalDist (($ᵗ Secret) >>= fun secret ↦
        ($ᵗ R) >>= fun publicMask ↦
          ($ᵗ Mask) >>= fun intervalMask ↦
            errorSampler >>= fun error ↦
              adversary (publicMask,
                publicMask * encoding.secretValue secret + error -
                  encoding.maskValue intervalMask ^ 2)) := by
      refine evalDist_bind_congr' ($ᵗ Secret) fun secret ↦ ?_
      refine evalDist_bind_congr' ($ᵗ R) fun publicMask ↦ ?_
      exact evalDist_bind_bind_swap errorSampler ($ᵗ Mask) _
    _ = evalDist (($ᵗ Secret) >>= fun secret ↦
        ($ᵗ Mask) >>= fun intervalMask ↦
          ($ᵗ R) >>= fun publicMask ↦
            errorSampler >>= fun error ↦
              adversary (publicMask,
                publicMask * encoding.secretValue secret +
                  (error - encoding.maskValue intervalMask ^ 2))) := by
      refine evalDist_bind_congr' ($ᵗ Secret) fun secret ↦ ?_
      calc
        _ = evalDist (($ᵗ Mask) >>= fun intervalMask ↦
            ($ᵗ R) >>= fun publicMask ↦
              errorSampler >>= fun error ↦
                adversary (publicMask,
                  publicMask * encoding.secretValue secret + error -
                    encoding.maskValue intervalMask ^ 2)) :=
          evalDist_bind_bind_swap ($ᵗ R) ($ᵗ Mask) _
        _ = _ := by
          refine evalDist_bind_congr' ($ᵗ Mask) fun intervalMask ↦ ?_
          refine evalDist_bind_congr' ($ᵗ R) fun publicMask ↦ ?_
          refine evalDist_bind_congr' errorSampler fun error ↦ ?_
          congr 2
          ring_nf

/-- For fixed `Z`, translating the second coordinate by `-Z²` preserves pair-uniformity. -/
theorem zeroShift_bijective
    {R : Type} [Ring R] (intervalMask : R) :
    Function.Bijective (fun transcript : R × R ↦
      (transcript.1, transcript.2 - intervalMask ^ 2)) := by
  let inverse : R × R → R × R := fun transcript ↦
    (transcript.1, transcript.2 + intervalMask ^ 2)
  refine Function.bijective_iff_has_inverse.mpr ⟨inverse, ?_, ?_⟩
  · intro transcript
    apply Prod.ext <;> simp [inverse]
  · intro transcript
    apply Prod.ext <;> simp [inverse]

theorem zeroReduction_random_evalDist
    {R Secret Mask Hint : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Secret] [SampleableType Secret]
    [Fintype Mask] [SampleableType Mask]
    (encoding : Encoding R Secret Mask Hint) (errorSampler : ProbComp R)
    (adversary : Distinguisher R) :
    evalDist (LearningWithErrors.game1 (oneSampleProblem encoding errorSampler)
        (zeroReduction encoding adversary)) =
      evalDist (uniformBlock (R := R) >>= adversary) := by
  simp only [LearningWithErrors.game1, LearningWithErrors.uniformDistr,
    oneSampleProblem, zeroReduction, uniformBlock, bind_assoc, pure_bind]
  calc
    evalDist (($ᵗ R) >>= fun publicMask ↦
        ($ᵗ R) >>= fun body ↦
          ($ᵗ Mask) >>= fun intervalMask ↦
            adversary (publicMask, body - encoding.maskValue intervalMask ^ 2)) =
      evalDist (($ᵗ Mask) >>= fun intervalMask ↦
        ($ᵗ (R × R)) >>= fun transcript ↦
          adversary (transcript.1,
            transcript.2 - encoding.maskValue intervalMask ^ 2)) := by
      calc
        _ = evalDist (($ᵗ R) >>= fun publicMask ↦
            ($ᵗ Mask) >>= fun intervalMask ↦
              ($ᵗ R) >>= fun body ↦
                adversary (publicMask,
                  body - encoding.maskValue intervalMask ^ 2)) := by
          refine evalDist_bind_congr' ($ᵗ R) fun publicMask ↦ ?_
          exact evalDist_bind_bind_swap ($ᵗ R) ($ᵗ Mask) _
        _ = evalDist (($ᵗ Mask) >>= fun intervalMask ↦
            ($ᵗ R) >>= fun publicMask ↦
              ($ᵗ R) >>= fun body ↦
                adversary (publicMask,
                  body - encoding.maskValue intervalMask ^ 2)) :=
          evalDist_bind_bind_swap ($ᵗ R) ($ᵗ Mask) _
        _ = _ := by
          refine evalDist_bind_congr' ($ᵗ Mask) fun intervalMask ↦ ?_
          have hProduct :=
            FormalProof4FHE.FiniteProduct.evalDist_independent_uniform_product
              (first := R) (second := R)
          simpa only [bind_assoc, pure_bind] using
            FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
              hProduct
              (fun transcript : R × R ↦
                adversary (transcript.1,
                  transcript.2 - encoding.maskValue intervalMask ^ 2))
    _ = evalDist (($ᵗ Mask) >>= fun _intervalMask ↦
        ($ᵗ (R × R)) >>= adversary) := by
      refine evalDist_bind_congr' ($ᵗ Mask) fun intervalMask ↦ ?_
      let transform : R × R → R × R := fun transcript ↦
        (transcript.1, transcript.2 - encoding.maskValue intervalMask ^ 2)
      have hUniform :
          evalDist (transform <$> ($ᵗ (R × R))) =
            evalDist ($ᵗ (R × R)) :=
        evalDist_map_bijective_uniform_cross
          (α := R × R) (β := R × R) transform
          (zeroShift_bijective (encoding.maskValue intervalMask))
      simpa only [transform, map_eq_bind_pure_comp, Function.comp_def, bind_assoc,
        pure_bind] using
          FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hUniform adversary
    _ = evalDist (($ᵗ (R × R)) >>= adversary) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        ($ᵗ Mask) (by simp) _

/-- The zero-message real-versus-uniform advantage is exactly ordinary one-sample RLWE. -/
theorem zero_uniform_advantage_eq_lwe
    {R Secret Mask Hint : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Secret] [SampleableType Secret]
    [Fintype Mask] [SampleableType Mask]
    (encoding : Encoding R Secret Mask Hint) (errorSampler : ProbComp R)
    (adversary : Distinguisher R) :
    (zeroRealView encoding errorSampler >>= adversary).boolDistAdvantage
        (uniformBlock (R := R) >>= adversary) =
      LearningWithErrors.advantage (oneSampleProblem encoding errorSampler)
        (zeroReduction encoding adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp (zeroReduction_real_evalDist encoding errorSampler adversary) true,
    evalDist_ext_iff.mp (zeroReduction_random_evalDist encoding errorSampler adversary) true]

/-! ## Cancellation-free hinted RLWE reduction -/

/-- The conditional real Boolean game for a public hint and its compatible secret. -/
def contextReal
    {R Secret Mask Hint : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (encoding : Encoding R Secret Mask Hint) (errorSampler : ProbComp R)
    (adversary : HintDistinguisher Hint R) (context : Hint × Secret) : ProbComp Bool := do
  let sample ← fixedSecretRealBlock encoding errorSampler context.2
  adversary ⟨context.1, sample.1, sample.2⟩

/-- The conditional ideal Boolean game for a public hint. -/
def contextIdeal
    {R Secret Mask Hint : Type}
    [Sub R] [SampleableType R]
    (_encoding : Encoding R Secret Mask Hint)
    (adversary : HintDistinguisher Hint R) (context : Hint × Secret) : ProbComp Bool := do
  let sample ← uniformBlock (R := R)
  adversary ⟨context.1, sample.1, sample.2⟩

/-- Conditional signed distinguishing gap. -/
def contextGap
    {R Secret Mask Hint : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (encoding : Encoding R Secret Mask Hint) (errorSampler : ProbComp R)
    (adversary : HintDistinguisher Hint R) (context : Hint × Secret) : ℝ :=
  SquaredBias.signedGap
    (contextReal encoding errorSampler adversary context)
    (contextIdeal encoding adversary context)

/-- The pair-indexed form of the real hinted game. -/
def pairHintRealGame
    {R Secret Mask Hint : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    [SampleableType Secret] [SampleableType Mask]
    (encoding : Encoding R Secret Mask Hint) (errorSampler : ProbComp R)
    (adversary : HintDistinguisher Hint R) : ProbComp Bool :=
  ($ᵗ (Secret × Mask)) >>= fun value ↦
    contextReal encoding errorSampler adversary
      (encoding.hint value.1 value.2, value.1)

/-- The pair-indexed form of the random hinted game. -/
def pairHintIdealGame
    {R Secret Mask Hint : Type}
    [Sub R] [SampleableType R]
    [SampleableType Secret] [SampleableType Mask]
    (encoding : Encoding R Secret Mask Hint)
    (adversary : HintDistinguisher Hint R) : ProbComp Bool :=
  ($ᵗ (Secret × Mask)) >>= fun value ↦
    contextIdeal encoding adversary
      (encoding.hint value.1 value.2, value.1)

theorem hintRealGame_evalDist_pair
    {R Secret Mask Hint : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Secret] [SampleableType Secret]
    [Fintype Mask] [SampleableType Mask]
    (encoding : Encoding R Secret Mask Hint) (errorSampler : ProbComp R)
    (adversary : HintDistinguisher Hint R) :
    evalDist (hintRealView encoding errorSampler >>= adversary) =
      evalDist (pairHintRealGame encoding errorSampler adversary) := by
  have hProduct :=
    FormalProof4FHE.FiniteProduct.evalDist_independent_uniform_product
      (first := Secret) (second := Mask)
  have hBind :=
    FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hProduct
      (fun value : Secret × Mask ↦
        contextReal encoding errorSampler adversary
          (encoding.hint value.1 value.2, value.1))
  simpa only [hintRealView, pairHintRealGame, contextReal, fixedSecretRealBlock,
    bind_assoc, pure_bind] using hBind

theorem hintRandomGame_evalDist_pair
    {R Secret Mask Hint : Type}
    [Sub R] [Fintype R] [SampleableType R]
    [Fintype Secret] [SampleableType Secret]
    [Fintype Mask] [SampleableType Mask]
    (encoding : Encoding R Secret Mask Hint)
    (adversary : HintDistinguisher Hint R) :
    evalDist (hintRandomView encoding >>= adversary) =
      evalDist (pairHintIdealGame encoding adversary) := by
  have hProduct :=
    FormalProof4FHE.FiniteProduct.evalDist_independent_uniform_product
      (first := Secret) (second := Mask)
  have hBind :=
    FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hProduct
      (fun value : Secret × Mask ↦
        contextIdeal encoding adversary
          (encoding.hint value.1 value.2, value.1))
  simpa only [hintRandomView, pairHintIdealGame, contextIdeal, uniformBlock,
    bind_assoc, pure_bind] using hBind

/-- The hinted signed gap is the mean conditional gap over genuine `(secret, mask)` pairs. -/
theorem signedGap_hintGames_eq_pairExpectation
    {R Secret Mask Hint : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Secret] [SampleableType Secret]
    [Fintype Mask] [SampleableType Mask]
    (encoding : Encoding R Secret Mask Hint) (errorSampler : ProbComp R)
    (adversary : HintDistinguisher Hint R) :
    SquaredBias.signedGap
        (hintRealView encoding errorSampler >>= adversary)
        (hintRandomView encoding >>= adversary) =
      BoundedMoment.expectation ($ᵗ (Secret × Mask))
        (fun value ↦ contextGap encoding errorSampler adversary
          (encoding.hint value.1 value.2, value.1)) := by
  have hMean := SquaredBias.signedGap_bind ($ᵗ (Secret × Mask))
    (fun value ↦ contextReal encoding errorSampler adversary
      (encoding.hint value.1 value.2, value.1))
    (fun value ↦ contextIdeal encoding adversary
      (encoding.hint value.1 value.2, value.1))
  unfold SquaredBias.signedGap
  rw [probOutput_congr rfl
      (hintRealGame_evalDist_pair encoding errorSampler adversary),
    probOutput_congr rfl (hintRandomGame_evalDist_pair encoding adversary)]
  exact hMean

/-- The two-copy real source game: sample a uniform public hint and secret, then square its
conditional ordinary-RLWE distinguishing gap. -/
def twoCopyRealGame
    {R Secret Mask Hint : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    [SampleableType Hint] [SampleableType Secret]
    (encoding : Encoding R Secret Mask Hint) (errorSampler : ProbComp R)
    (adversary : HintDistinguisher Hint R) : ProbComp Bool :=
  SquaredBias.contextualExperiment ($ᵗ (Hint × Secret))
    (contextReal encoding errorSampler adversary)
    (contextIdeal encoding adversary)

/-- The random source game replaces both same-secret RLWE blocks by uniform blocks. -/
def twoCopyRandomGame
    {R Secret Mask Hint : Type}
    [Sub R] [SampleableType R]
    [SampleableType Hint] [SampleableType Secret]
    (encoding : Encoding R Secret Mask Hint)
    (adversary : HintDistinguisher Hint R) : ProbComp Bool :=
  SquaredBias.contextualExperiment ($ᵗ (Hint × Secret))
    (contextIdeal encoding adversary)
    (contextIdeal encoding adversary)

/-- Exact two-copy, same-secret ordinary-RLWE advantage used by the reduction. -/
def twoCopyRLWEAdvantage
    {R Secret Mask Hint : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    [SampleableType Hint] [SampleableType Secret]
    (encoding : Encoding R Secret Mask Hint) (errorSampler : ProbComp R)
    (adversary : HintDistinguisher Hint R) : ℝ :=
  (twoCopyRealGame encoding errorSampler adversary).boolDistAdvantage
    (twoCopyRandomGame encoding adversary)

theorem probOutput_twoCopyRealGame_true
    {R Secret Mask Hint : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    [Fintype Hint] [SampleableType Hint]
    [Fintype Secret] [SampleableType Secret]
    (encoding : Encoding R Secret Mask Hint) (errorSampler : ProbComp R)
    (adversary : HintDistinguisher Hint R) :
    Pr[= true | twoCopyRealGame encoding errorSampler adversary].toReal =
      (1 + BoundedMoment.expectation ($ᵗ (Hint × Secret))
        (fun context ↦ contextGap encoding errorSampler adversary context ^ 2)) / 2 := by
  exact SquaredBias.probOutput_contextualExperiment_true
    ($ᵗ (Hint × Secret))
    (contextReal encoding errorSampler adversary)
    (contextIdeal encoding adversary)

theorem probOutput_twoCopyRandomGame_true
    {R Secret Mask Hint : Type}
    [Sub R] [SampleableType R]
    [Fintype Hint] [SampleableType Hint]
    [Fintype Secret] [SampleableType Secret]
    (encoding : Encoding R Secret Mask Hint)
    (adversary : HintDistinguisher Hint R) :
    Pr[= true | twoCopyRandomGame encoding adversary].toReal = 1 / 2 := by
  rw [show twoCopyRandomGame encoding adversary =
      SquaredBias.contextualExperiment ($ᵗ (Hint × Secret))
        (contextIdeal encoding adversary) (contextIdeal encoding adversary) by rfl,
    SquaredBias.probOutput_contextualExperiment_true]
  simp only [SquaredBias.signedGap, sub_self, OfNat.ofNat]
  rw [BoundedMoment.expectation_const]
  norm_num

/-- The source advantage is exactly half of the conditional squared-gap moment. -/
theorem twoCopyRLWEAdvantage_eq_half_secondMoment
    {R Secret Mask Hint : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    [Fintype Hint] [SampleableType Hint]
    [Fintype Secret] [SampleableType Secret]
    (encoding : Encoding R Secret Mask Hint) (errorSampler : ProbComp R)
    (adversary : HintDistinguisher Hint R) :
    twoCopyRLWEAdvantage encoding errorSampler adversary =
      BoundedMoment.expectation ($ᵗ (Hint × Secret))
        (fun context ↦ contextGap encoding errorSampler adversary context ^ 2) / 2 := by
  have hNonneg : 0 ≤ BoundedMoment.expectation ($ᵗ (Hint × Secret))
      (fun context ↦ contextGap encoding errorSampler adversary context ^ 2) := by
    exact BoundedMoment.secondMoment_nonneg ($ᵗ (Hint × Secret))
      (contextGap encoding errorSampler adversary)
  unfold twoCopyRLWEAdvantage ProbComp.boolDistAdvantage
  rw [probOutput_twoCopyRealGame_true encoding errorSampler adversary,
    probOutput_twoCopyRandomGame_true encoding adversary, abs_of_nonneg]
  · ring
  · linarith

/-- Quantitative interval-mask theorem.  Injectivity of `(hint,secret)` removes cancellation and
costs precisely the square root of the cardinality ratio. -/
theorem hintAdvantage_sq_le_two_mul_cardRatio_mul_twoCopy
    {R Secret Mask Hint : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Secret] [Nonempty Secret] [SampleableType Secret]
    [Fintype Mask] [Nonempty Mask] [SampleableType Mask]
    [Fintype Hint] [Nonempty Hint] [SampleableType Hint]
    (encoding : Encoding R Secret Mask Hint) (errorSampler : ProbComp R)
    (adversary : HintDistinguisher Hint R) :
    hintAdvantage encoding errorSampler adversary ^ 2 ≤
      2 * ((Fintype.card (Hint × Secret) : ℝ) /
        (Fintype.card (Secret × Mask) : ℝ)) *
          twoCopyRLWEAdvantage encoding errorSampler adversary := by
  have hCounting :=
    SquaredBias.sq_expectation_uniform_comp_le_card_ratio_secondMoment
      (fun value : Secret × Mask ↦
        (encoding.hint value.1 value.2, value.1))
      encoding.hintSecret_injective
      (contextGap encoding errorSampler adversary)
  unfold hintAdvantage ProbComp.boolDistAdvantage
  rw [show
      |Pr[= true | hintRealView encoding errorSampler >>= adversary].toReal -
        Pr[= true | hintRandomView encoding >>= adversary].toReal| ^ 2 =
        (SquaredBias.signedGap
          (hintRealView encoding errorSampler >>= adversary)
          (hintRandomView encoding >>= adversary)) ^ 2 by
      rw [sq_abs]
      rfl,
    signedGap_hintGames_eq_pairExpectation encoding errorSampler adversary]
  calc
    BoundedMoment.expectation ($ᵗ (Secret × Mask))
        (fun value ↦ contextGap encoding errorSampler adversary
          (encoding.hint value.1 value.2, value.1)) ^ 2 ≤
      ((Fintype.card (Hint × Secret) : ℝ) /
        (Fintype.card (Secret × Mask) : ℝ)) *
          BoundedMoment.expectation ($ᵗ (Hint × Secret))
            (fun context ↦ contextGap encoding errorSampler adversary context ^ 2) :=
      hCounting
    _ = 2 * ((Fintype.card (Hint × Secret) : ℝ) /
        (Fintype.card (Secret × Mask) : ℝ)) *
          twoCopyRLWEAdvantage encoding errorSampler adversary := by
      rw [twoCopyRLWEAdvantage_eq_half_secondMoment encoding errorSampler adversary]
      ring

theorem hintAdvantage_le_sqrt_two_mul_cardRatio_mul_twoCopy
    {R Secret Mask Hint : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Secret] [Nonempty Secret] [SampleableType Secret]
    [Fintype Mask] [Nonempty Mask] [SampleableType Mask]
    [Fintype Hint] [Nonempty Hint] [SampleableType Hint]
    (encoding : Encoding R Secret Mask Hint) (errorSampler : ProbComp R)
    (adversary : HintDistinguisher Hint R) :
    hintAdvantage encoding errorSampler adversary ≤
      Real.sqrt (2 * ((Fintype.card (Hint × Secret) : ℝ) /
        (Fintype.card (Secret × Mask) : ℝ)) *
          twoCopyRLWEAdvantage encoding errorSampler adversary) := by
  exact Real.le_sqrt_of_sq_le
    (hintAdvantage_sq_le_two_mul_cardRatio_mul_twoCopy
      encoding errorSampler adversary)

/-! ## Quadratic KDM conclusion -/

/-- Hybrid composition: quadratic KDM is hinted RLWE plus one ordinary zero-message RLWE hop. -/
theorem kdmAdvantage_le_hint_add_oneSampleRLWE
    {R Secret Mask Hint : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Secret] [SampleableType Secret]
    [Fintype Mask] [SampleableType Mask]
    (encoding : Encoding R Secret Mask Hint) (errorSampler : ProbComp R)
    (adversary : Distinguisher R) :
    kdmAdvantage encoding errorSampler adversary ≤
      hintAdvantage encoding errorSampler (quadraticReduction encoding adversary) +
        LearningWithErrors.advantage (oneSampleProblem encoding errorSampler)
          (zeroReduction encoding adversary) := by
  have hTriangle := ProbComp.boolDistAdvantage_triangle
    (quadraticRealView encoding errorSampler >>= adversary)
    (uniformBlock (R := R) >>= adversary)
    (zeroRealView encoding errorSampler >>= adversary)
  unfold kdmAdvantage
  rw [show (uniformBlock (R := R) >>= adversary).boolDistAdvantage
      (zeroRealView encoding errorSampler >>= adversary) =
      (zeroRealView encoding errorSampler >>= adversary).boolDistAdvantage
        (uniformBlock (R := R) >>= adversary) by
    unfold ProbComp.boolDistAdvantage
    rw [abs_sub_comm],
    quadratic_uniform_advantage_eq_hintAdvantage encoding errorSampler adversary,
    zero_uniform_advantage_eq_lwe encoding errorSampler adversary] at hTriangle
  exact hTriangle

/-- Main generic theorem for `RLWE_S(S²)`: two same-secret ordinary RLWE blocks and one
ordinary zero-message RLWE sample imply quadratic KDM security. -/
theorem kdmAdvantage_le_sqrt_twoCopy_add_oneSampleRLWE
    {R Secret Mask Hint : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Secret] [Nonempty Secret] [SampleableType Secret]
    [Fintype Mask] [Nonempty Mask] [SampleableType Mask]
    [Fintype Hint] [Nonempty Hint] [SampleableType Hint]
    (encoding : Encoding R Secret Mask Hint) (errorSampler : ProbComp R)
    (adversary : Distinguisher R) :
    kdmAdvantage encoding errorSampler adversary ≤
      Real.sqrt (2 * ((Fintype.card (Hint × Secret) : ℝ) /
        (Fintype.card (Secret × Mask) : ℝ)) *
          twoCopyRLWEAdvantage encoding errorSampler
            (quadraticReduction encoding adversary)) +
        LearningWithErrors.advantage (oneSampleProblem encoding errorSampler)
          (zeroReduction encoding adversary) := by
  exact (kdmAdvantage_le_hint_add_oneSampleRLWE
      encoding errorSampler adversary).trans
    (add_le_add
      (hintAdvantage_le_sqrt_two_mul_cardRatio_mul_twoCopy
        encoding errorSampler (quadraticReduction encoding adversary)) le_rfl)

/-! ## Concrete interval codes for binary and ternary polynomial secrets -/

/- Select one coherent algebra dictionary for the executable negacyclic carrier.  The carrier
also exposes its bundled operations directly; fixing these projections avoids an instance mismatch
at degree zero when the generic reduction asks for both `CommRing` and `Sub`. -/
local instance intervalRqCommRing (q degree : ℕ) : CommRing (Rq q degree) :=
  LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree

local instance intervalRqAddCommGroup (q degree : ℕ) : AddCommGroup (Rq q degree) :=
  (intervalRqCommRing q degree).toAddCommGroup

local instance intervalRqAdd (q degree : ℕ) : Add (Rq q degree) :=
  (intervalRqAddCommGroup q degree).toAdd

local instance intervalRqSub (q degree : ℕ) : Sub (Rq q degree) :=
  (intervalRqCommRing q degree).toAddGroupWithOne.toAddGroup.toSub

local instance intervalRqNeg (q degree : ℕ) : Neg (Rq q degree) :=
  (intervalRqAddCommGroup q degree).toNeg

local instance intervalRqZero (q degree : ℕ) : Zero (Rq q degree) :=
  (intervalRqAddCommGroup q degree).toZero

local instance intervalRqMul (q degree : ℕ) : Mul (Rq q degree) :=
  (intervalRqCommRing q degree).toMul

local instance intervalRqOne (q degree : ℕ) : One (Rq q degree) :=
  (intervalRqCommRing q degree).toAddGroupWithOne.toOne

theorem intervalRq_sub_eq_executable
    (q degree : ℕ) (left right : Rq q degree) :
    @Sub.sub (Rq q degree) (intervalRqSub q degree) left right =
      @Sub.sub (Rq q degree) (RLWE.negacyclicRing q degree).instSubPoly left right := by
  cases degree with
  | zero =>
      apply LatticeCrypto.Poly.ext_get_eq
      intro coefficient
      exact coefficient.elim0
  | succ degree => rfl

theorem intervalRq_sub_coefficient
    (q degree : ℕ) (left right : Rq q degree) (coefficient : Fin degree) :
    LatticeCrypto.Poly.toPi (left - right) coefficient =
      LatticeCrypto.Poly.toPi left coefficient -
        LatticeCrypto.Poly.toPi right coefficient := by
  change (RLWE.negacyclicRing q degree).backend.coeff
      (@Sub.sub (Rq q degree) (intervalRqSub q degree) left right) coefficient = _
  rw [intervalRq_sub_eq_executable]
  exact LatticeCrypto.NegacyclicRing.coeff_sub (RLWE.negacyclicRing q degree)
    left right coefficient

theorem executableRq_sub_get
    (q degree : ℕ) (left right : Rq q degree) (coefficient : Fin degree) :
    Vector.get
        (@Sub.sub (Rq q degree) (RLWE.negacyclicRing q degree).instSubPoly left right)
        coefficient =
      Vector.get left coefficient - Vector.get right coefficient := by
  exact LatticeCrypto.NegacyclicRing.coeff_sub (RLWE.negacyclicRing q degree)
    left right coefficient

local instance intervalHintSizeNeZero (L M : ℕ) [NeZero L] [NeZero M] :
    NeZero (M + L - 1) :=
  ⟨by
    have hL : 0 < L := Nat.pos_of_neZero L
    have hM : 0 < M := Nat.pos_of_neZero M
    omega⟩

/-- `degree` independent digits in `{0,…,L-1}`. -/
abbrev DigitSecret (L degree : ℕ) := Fin degree → Fin L

/-- `degree` independent interval-mask coefficients in `{0,…,M-1}`. -/
abbrev IntervalMask (M degree : ℕ) := Fin degree → Fin M

/-- The public coefficient code has exactly `M+L-1` possibilities per coordinate. -/
abbrev IntervalHint (L M degree : ℕ) := Fin degree → Fin (M + L - 1)

/-- Coefficientwise interval code `s + (M-1-z)`. -/
def intervalHintCode
    (L M degree : ℕ) [NeZero L] [NeZero M]
    (secret : DigitSecret L degree) (mask : IntervalMask M degree) :
    IntervalHint L M degree :=
  fun coefficient ↦
    ⟨(secret coefficient).val + (M - 1 - (mask coefficient).val), by
      have hL : 0 < L := Nat.pos_of_neZero L
      have hM : 0 < M := Nat.pos_of_neZero M
      have hs := (secret coefficient).isLt
      have hz := (mask coefficient).isLt
      omega⟩

/-- Revealing the interval code together with the secret uniquely identifies the sampled mask. -/
theorem intervalHintCode_secret_injective
    (L M degree : ℕ) [NeZero L] [NeZero M] :
    Function.Injective (fun value : DigitSecret L degree × IntervalMask M degree ↦
      (intervalHintCode L M degree value.1 value.2, value.1)) := by
  intro left right hEq
  have hSecret : left.1 = right.1 := congrArg Prod.snd hEq
  apply Prod.ext
  · exact hSecret
  · apply funext
    intro coefficient
    apply Fin.ext
    have hCode := congrFun (congrArg Prod.fst hEq) coefficient
    have hL : 0 < L := Nat.pos_of_neZero L
    have hM : 0 < M := Nat.pos_of_neZero M
    have hLeftMask := (left.2 coefficient).isLt
    have hRightMask := (right.2 coefficient).isLt
    have hLeftSecret := (left.1 coefficient).isLt
    have hRightSecret := (right.1 coefficient).isLt
    have hSecretCoefficient := congrFun hSecret coefficient
    simp only [intervalHintCode, Fin.mk.injEq] at hCode
    have hSecretVal : (left.1 coefficient).val = (right.1 coefficient).val :=
      congrArg Fin.val hSecretCoefficient
    omega

/-- Embed bounded natural coefficients into the executable negacyclic ring. -/
def natCoefficientPolynomial (q degree : ℕ) (values : Fin degree → ℕ) :
    Rq q degree :=
  LatticeCrypto.Poly.ofPi fun coefficient ↦ (values coefficient : ZMod q)

/-- Ring value of an `L`-ary secret, centered by the public natural offset. -/
def digitSecretPolynomial (q degree L offset : ℕ)
    (secret : DigitSecret L degree) : Rq q degree :=
  LatticeCrypto.Poly.ofPi fun coefficient ↦
    ((secret coefficient).val : ZMod q) - (offset : ZMod q)

/-- Ring value of an interval mask. -/
def intervalMaskPolynomial (q degree M : ℕ)
    (mask : IntervalMask M degree) : Rq q degree :=
  natCoefficientPolynomial q degree fun coefficient ↦ (mask coefficient).val

/-- Decode a public interval code as the ring element `H=S-Z`. -/
def intervalHintPolynomial (q degree L M offset : ℕ)
    (hint : IntervalHint L M degree) : Rq q degree :=
  LatticeCrypto.Poly.ofPi fun coefficient ↦
    ((hint coefficient).val : ZMod q) - (M - 1 : ℕ) - (offset : ZMod q)

theorem intervalHintPolynomial_code
    (q degree L M offset : ℕ) [NeZero L] [NeZero M]
    (secret : DigitSecret L degree) (mask : IntervalMask M degree) :
    intervalHintPolynomial q degree L M offset
        (intervalHintCode L M degree secret mask) =
      digitSecretPolynomial q degree L offset secret -
        intervalMaskPolynomial q degree M mask := by
  calc
    intervalHintPolynomial q degree L M offset
        (intervalHintCode L M degree secret mask) =
      @Sub.sub (Rq q degree) (RLWE.negacyclicRing q degree).instSubPoly
        (digitSecretPolynomial q degree L offset secret)
        (intervalMaskPolynomial q degree M mask) := by
      apply LatticeCrypto.Poly.ext_get_eq
      intro coefficient
      rw [executableRq_sub_get]
      simp only [intervalHintPolynomial, intervalHintCode, digitSecretPolynomial,
        intervalMaskPolynomial, natCoefficientPolynomial]
      simp [LatticeCrypto.Poly.ofPi, Vector.get]
      change
        ((secret coefficient).val : ZMod q) +
            ((M - 1 - (mask coefficient).val : ℕ) : ZMod q) -
            ((M - 1 : ℕ) : ZMod q) - (offset : ZMod q) =
          (((secret coefficient).val : ZMod q) - (offset : ZMod q)) -
            ((mask coefficient).val : ZMod q)
      have hM : 0 < M := Nat.pos_of_neZero M
      have hMask : (mask coefficient).val ≤ M - 1 := by omega
      rw [Nat.cast_sub hMask]
      ring
    _ = @Sub.sub (Rq q degree) (intervalRqSub q degree)
        (digitSecretPolynomial q degree L offset secret)
        (intervalMaskPolynomial q degree M mask) :=
      (intervalRq_sub_eq_executable q degree _ _).symm

/-- The complete generic polynomial interval encoding. -/
def intervalEncoding
    (q degree L M offset : ℕ) [NeZero L] [NeZero M] :
    Encoding (Rq q degree) (DigitSecret L degree)
      (IntervalMask M degree) (IntervalHint L M degree) where
  secretValue := digitSecretPolynomial q degree L offset
  maskValue := intervalMaskPolynomial q degree M
  hint := intervalHintCode L M degree
  hintValue := intervalHintPolynomial q degree L M offset
  hintValue_hint := intervalHintPolynomial_code q degree L M offset
  hintSecret_injective := intervalHintCode_secret_injective L M degree

/-- Exact cardinality ratio of the interval encoding. -/
theorem intervalEncoding_cardRatio
    (L M degree : ℕ) [NeZero L] [NeZero M] :
    (Fintype.card (IntervalHint L M degree × DigitSecret L degree) : ℝ) /
        (Fintype.card (DigitSecret L degree × IntervalMask M degree) : ℝ) =
      (((M + L - 1 : ℕ) : ℝ) / (M : ℝ)) ^ degree := by
  have hL : (L : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne L)
  have hM : (M : ℝ) ≠ 0 := by
    exact_mod_cast (NeZero.ne M)
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_mul, Nat.cast_pow]
  rw [div_pow]
  field_simp

/-- Binary polynomial secrets have coefficients in `{0,1}`. -/
abbrev BinarySecret (degree : ℕ) := DigitSecret 2 degree

/-- Ternary polynomial secrets have centered coefficients in `{-1,0,1}`. -/
abbrev TernarySecret (degree : ℕ) := DigitSecret 3 degree

/-- Binary interval encoding; the secret offset is zero. -/
def binaryEncoding (q degree M : ℕ) [NeZero M] :
    Encoding (Rq q degree) (BinarySecret degree)
      (IntervalMask M degree) (IntervalHint 2 M degree) :=
  intervalEncoding q degree 2 M 0

/-- Ternary interval encoding; digits `0,1,2` are centered to `-1,0,1`. -/
def ternaryEncoding (q degree M : ℕ) [NeZero M] :
    Encoding (Rq q degree) (TernarySecret degree)
      (IntervalMask M degree) (IntervalHint 3 M degree) :=
  intervalEncoding q degree 3 M 1

/-- Concrete binary `RLWE_S(S²)` theorem with interval loss `(1+1/M)^degree`. -/
theorem binary_kdmAdvantage_le
    (q degree M : ℕ) [NeZero q] [NeZero M]
    (errorSampler : ProbComp (Rq q degree))
    (adversary : Distinguisher (Rq q degree)) :
    kdmAdvantage (binaryEncoding q degree M) errorSampler adversary ≤
      Real.sqrt (2 * (((M : ℝ) + 1) / (M : ℝ)) ^ degree *
        twoCopyRLWEAdvantage (binaryEncoding q degree M) errorSampler
          (quadraticReduction (binaryEncoding q degree M) adversary)) +
      LearningWithErrors.advantage
        (oneSampleProblem (binaryEncoding q degree M) errorSampler)
        (zeroReduction (binaryEncoding q degree M) adversary) := by
  have h := kdmAdvantage_le_sqrt_twoCopy_add_oneSampleRLWE
    (binaryEncoding q degree M) errorSampler adversary
  rw [intervalEncoding_cardRatio 2 M degree] at h
  norm_num at h
  exact h

/-- Assumption-style binary security statement with explicit concrete source bounds. -/
theorem binary_kdmAdvantage_le_of_rlweBounds
    (q degree M : ℕ) [NeZero q] [NeZero M]
    (errorSampler : ProbComp (Rq q degree))
    (adversary : Distinguisher (Rq q degree))
    (twoCopyBound oneSampleBound : ℝ)
    (hTwoCopy :
      twoCopyRLWEAdvantage (binaryEncoding q degree M) errorSampler
        (quadraticReduction (binaryEncoding q degree M) adversary) ≤ twoCopyBound)
    (hOneSample :
      LearningWithErrors.advantage
        (oneSampleProblem (binaryEncoding q degree M) errorSampler)
        (zeroReduction (binaryEncoding q degree M) adversary) ≤ oneSampleBound) :
    kdmAdvantage (binaryEncoding q degree M) errorSampler adversary ≤
      Real.sqrt (2 * (((M : ℝ) + 1) / (M : ℝ)) ^ degree * twoCopyBound) +
        oneSampleBound := by
  have hFactor : 0 ≤ 2 * (((M : ℝ) + 1) / (M : ℝ)) ^ degree := by
    positivity
  exact (binary_kdmAdvantage_le q degree M errorSampler adversary).trans
    (add_le_add
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hTwoCopy hFactor)) hOneSample)

/-- Concrete ternary `RLWE_S(S²)` theorem with interval loss `(1+2/M)^degree`. -/
theorem ternary_kdmAdvantage_le
    (q degree M : ℕ) [NeZero q] [NeZero M]
    (errorSampler : ProbComp (Rq q degree))
    (adversary : Distinguisher (Rq q degree)) :
    kdmAdvantage (ternaryEncoding q degree M) errorSampler adversary ≤
      Real.sqrt (2 * (((M : ℝ) + 2) / (M : ℝ)) ^ degree *
        twoCopyRLWEAdvantage (ternaryEncoding q degree M) errorSampler
          (quadraticReduction (ternaryEncoding q degree M) adversary)) +
      LearningWithErrors.advantage
        (oneSampleProblem (ternaryEncoding q degree M) errorSampler)
        (zeroReduction (ternaryEncoding q degree M) adversary) := by
  have h := kdmAdvantage_le_sqrt_twoCopy_add_oneSampleRLWE
    (ternaryEncoding q degree M) errorSampler adversary
  rw [intervalEncoding_cardRatio 3 M degree] at h
  norm_num at h
  exact h

/-- Assumption-style ternary security statement with explicit concrete source bounds. -/
theorem ternary_kdmAdvantage_le_of_rlweBounds
    (q degree M : ℕ) [NeZero q] [NeZero M]
    (errorSampler : ProbComp (Rq q degree))
    (adversary : Distinguisher (Rq q degree))
    (twoCopyBound oneSampleBound : ℝ)
    (hTwoCopy :
      twoCopyRLWEAdvantage (ternaryEncoding q degree M) errorSampler
        (quadraticReduction (ternaryEncoding q degree M) adversary) ≤ twoCopyBound)
    (hOneSample :
      LearningWithErrors.advantage
        (oneSampleProblem (ternaryEncoding q degree M) errorSampler)
        (zeroReduction (ternaryEncoding q degree M) adversary) ≤ oneSampleBound) :
    kdmAdvantage (ternaryEncoding q degree M) errorSampler adversary ≤
      Real.sqrt (2 * (((M : ℝ) + 2) / (M : ℝ)) ^ degree * twoCopyBound) +
        oneSampleBound := by
  have hFactor : 0 ≤ 2 * (((M : ℝ) + 2) / (M : ℝ)) ^ degree := by
    positivity
  exact (ternary_kdmAdvantage_le q degree M errorSampler adversary).trans
    (add_le_add
      (Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hTwoCopy hFactor)) hOneSample)

end

end FormalProof4FHE.RLWE.IntervalMaskedQuadratic
