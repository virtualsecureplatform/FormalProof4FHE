/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.AffineCircular
import FormalProof4FHE.Probability.UniformInterval

/-!
# Public noise addition for ordinary LWE

Adding an independent error to each public output preserves the same secret and
the uniform branch. The real branch has the convolution error law exactly.
Replacing that convolution with a desired wide law loses at most one scalar TV
distance per sample. In particular, finite-budget interval flooding reduces
wide-error ordinary LWE to narrow-error ordinary LWE with an explicit loss.
These are batch reductions, not a bootstrap construction or a hardness claim
for any uninstantiated parameter family.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.LWE.NoiseFlooding

variable {R : Type} [CommRing R] [Finite R] [DecidableEq R] [SampleableType R]

def convolution (narrow extra : ProbComp R) : ProbComp R := do
  let small ← narrow
  let added ← extra
  pure (small + added)

/-- This public operation takes no secret input and keeps every challenge coefficient. -/
def flood {dimension samples : ℕ} (extra : ProbComp R)
    (transcript : BatchTranscript R dimension samples) :
    ProbComp (BatchTranscript R dimension samples) := do
  let added ← ProbComp.sampleIID samples extra
  pure (transcript.1, transcript.2 + added)

def reduction {dimension samples : ℕ} (extra : ProbComp R)
    (adversary : BatchTranscript R dimension samples → ProbComp Bool) :
    BatchTranscript R dimension samples → ProbComp Bool :=
  fun transcript ↦ flood extra transcript >>= adversary

theorem real_evalDist (dimension samples : ℕ)
    (secretSampler : ProbComp (Fin dimension → R)) (narrow extra : ProbComp R) :
    𝒟[LearningWithErrors.distr (batchProblem dimension samples secretSampler narrow) >>=
      flood extra] =
    𝒟[LearningWithErrors.distr
      (batchProblem dimension samples secretSampler (convolution narrow extra))] := by
  simp only [LearningWithErrors.distr, batchProblem, flood, bind_assoc, pure_bind]
  refine evalDist_bind_congr' _ fun challenge ↦ ?_
  refine evalDist_bind_congr' secretSampler fun secret ↦ ?_
  have h := evalDist_map_eq_of_evalDist_eq
    (FiniteProduct.evalDist_sampleIID_add_convolution samples narrow extra).symm
    (fun errors : Fin samples → R ↦ (challenge, vecMul secret challenge + errors))
  simpa only [convolution, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind, add_assoc, Pi.add_def] using h

omit [Finite R] [DecidableEq R] [SampleableType R] in
theorem translate_bijective {dimension samples : ℕ} (added : Fin samples → R) :
    Function.Bijective (fun transcript : BatchTranscript R dimension samples ↦
      (transcript.1, transcript.2 + added)) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨(fun transcript ↦ (transcript.1, transcript.2 - added)), ?_, ?_⟩
  · intro transcript
    simp
  · intro transcript
    simp

theorem uniform_evalDist (dimension samples : ℕ)
    (secretSampler : ProbComp (Fin dimension → R)) (narrow extra : ProbComp R)
    (hExtra : Pr[⊥ | extra] = 0) :
    𝒟[LearningWithErrors.uniformDistr (batchProblem dimension samples secretSampler narrow) >>=
      flood extra] =
    𝒟[LearningWithErrors.uniformDistr
      (batchProblem dimension samples secretSampler (convolution narrow extra))] := by
  have hu (errorSampler : ProbComp R) :
      LearningWithErrors.uniformDistr
        (batchProblem dimension samples secretSampler errorSampler) =
        ($ᵗ (BatchTranscript R dimension samples)) := by
    exact AffineCircular.ordinary_uniformDistr_eq_uniformSample
      dimension samples secretSampler id errorSampler
  rw [hu narrow, hu (convolution narrow extra)]
  unfold flood
  calc
    _ = 𝒟[ProbComp.sampleIID samples extra >>= fun added ↦
        ($ᵗ (BatchTranscript R dimension samples)) >>= fun transcript ↦
        pure (transcript.1, transcript.2 + added)] :=
      evalDist_bind_bind_swap _ _ _
    _ = 𝒟[ProbComp.sampleIID samples extra >>= fun _ ↦
        ($ᵗ (BatchTranscript R dimension samples))] := by
      refine evalDist_bind_congr' _ fun added ↦ ?_
      simpa only [map_eq_bind_pure_comp, Function.comp_def] using
        (evalDist_map_bijective_uniform_cross
          (α := BatchTranscript R dimension samples) (β := BatchTranscript R dimension samples)
          (fun transcript : BatchTranscript R dimension samples ↦
            (transcript.1, transcript.2 + added)) (translate_bijective added))
    _ = _ :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero _
        (FormalProof4FHE.SharedRandomness.probFailure_sampleIID_eq_zero samples extra hExtra) _

theorem advantage_convolution_eq (dimension samples : ℕ)
    (secretSampler : ProbComp (Fin dimension → R)) (narrow extra : ProbComp R)
    (hExtra : Pr[⊥ | extra] = 0)
    (adversary : BatchTranscript R dimension samples → ProbComp Bool) :
    LearningWithErrors.advantage
      (batchProblem dimension samples secretSampler (convolution narrow extra)) adversary =
    LearningWithErrors.advantage (batchProblem dimension samples secretSampler narrow)
      (reduction extra adversary) := by
  have hreal := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (real_evalDist dimension samples secretSampler narrow extra) adversary
  have huniform := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (uniform_evalDist dimension samples secretSampler narrow extra hExtra) adversary
  simp only [bind_assoc] at hreal huniform
  rw [advantage_eq_boolDistAdvantage, advantage_eq_boolDistAdvantage]
  unfold ProbComp.boolDistAdvantage LearningWithErrors.game0 LearningWithErrors.game1 reduction
  rw [probOutput_congr rfl hreal, probOutput_congr rfl huniform]

theorem real_tvDist_le (dimension samples : ℕ)
    (secretSampler : ProbComp (Fin dimension → R)) (left right : ProbComp R) :
    tvDist (LearningWithErrors.distr (batchProblem dimension samples secretSampler left))
      (LearningWithErrors.distr (batchProblem dimension samples secretSampler right)) ≤
        (samples : ℝ) * tvDist left right := by
  have hiid : tvDist (ProbComp.sampleIID samples left) (ProbComp.sampleIID samples right) ≤
      (samples : ℝ) * tvDist left right := by
    simpa [ProbComp.sampleIID] using
      (FiniteProduct.tvDist_fin_mOfFn_le_sum samples (fun _ ↦ left) (fun _ ↦ right))
  unfold LearningWithErrors.distr batchProblem
  apply tvDist_bind_left_le_const'
  intro challenge
  apply tvDist_bind_left_le_const'
  intro secret
  exact (tvDist_bind_right_le
    (fun errors ↦ pure (challenge, vecMul secret challenge + errors)) _ _).trans hiid

/-- All computational loss is an ordinary-LWE call with the original secret law. -/
theorem advantage_le_narrow (dimension samples : ℕ)
    (secretSampler : ProbComp (Fin dimension → R)) (narrow extra wide : ProbComp R)
    (hExtra : Pr[⊥ | extra] = 0)
    (adversary : BatchTranscript R dimension samples → ProbComp Bool) :
    LearningWithErrors.advantage (batchProblem dimension samples secretSampler wide) adversary ≤
      LearningWithErrors.advantage (batchProblem dimension samples secretSampler narrow)
        (reduction extra adversary) +
          (samples : ℝ) * tvDist (convolution narrow extra) wide := by
  let convProblem := batchProblem dimension samples secretSampler (convolution narrow extra)
  let wideProblem := batchProblem dimension samples secretSampler wide
  have hreal : (LearningWithErrors.game0 wideProblem adversary).boolDistAdvantage
      (LearningWithErrors.game0 convProblem adversary) ≤
        (samples : ℝ) * tvDist (convolution narrow extra) wide := by
    calc
      _ ≤ tvDist (LearningWithErrors.game0 wideProblem adversary)
          (LearningWithErrors.game0 convProblem adversary) :=
        abs_probOutput_toReal_sub_le_tvDist _ _
      _ ≤ tvDist (LearningWithErrors.distr wideProblem)
          (LearningWithErrors.distr convProblem) := tvDist_bind_right_le adversary _ _
      _ ≤ (samples : ℝ) * tvDist wide (convolution narrow extra) :=
        real_tvDist_le dimension samples secretSampler wide (convolution narrow extra)
      _ = _ := by rw [tvDist_comm]
  have huniform : LearningWithErrors.game1 wideProblem adversary =
      LearningWithErrors.game1 convProblem adversary := rfl
  rw [← advantage_convolution_eq dimension samples secretSampler narrow extra hExtra adversary,
    advantage_eq_boolDistAdvantage, advantage_eq_boolDistAdvantage]
  change (LearningWithErrors.game0 wideProblem adversary).boolDistAdvantage
      (LearningWithErrors.game1 wideProblem adversary) ≤ _
  rw [huniform]
  exact (ProbComp.boolDistAdvantage_triangle _ _ _).trans
    ((add_le_add hreal le_rfl).trans_eq (add_comm _ _))

/-- Uniform-secret modular LWE with interval errors needs only the narrow ordinary-LWE call. -/
theorem interval_advantage_le (dimension samples q radius rounds : ℕ) [NeZero q]
    (narrow : ProbComp (ZMod q)) (hNarrow : Pr[⊥ | narrow] = 0)
    (adversary : BatchTranscript (ZMod q) dimension samples → ProbComp Bool) :
    LearningWithErrors.advantage
      (zmodBatchProblem dimension samples q (UniformInterval.draw q radius)) adversary ≤
    LearningWithErrors.advantage (zmodBatchProblem dimension samples q narrow)
      (reduction (UniformInterval.sample q radius rounds) adversary) +
        (samples : ℝ) *
          (FormalProof4FHE.BlockBinary.scalarFirstMoment narrow
            (fun error ↦ ((LatticeCrypto.centeredRepr error).natAbs : ℝ)) /
              (2 * radius + 1 : ℝ) + (1 / 2 : ℝ) ^ rounds) := by
  have h := advantage_le_narrow dimension samples ($ᵗ (Fin dimension → ZMod q))
    narrow (UniformInterval.sample q radius rounds) (UniformInterval.draw q radius)
    (UniformInterval.sample_total q radius rounds) adversary
  apply h.trans
  apply add_le_add le_rfl
  apply mul_le_mul_of_nonneg_left _ (by positivity : 0 ≤ (samples : ℝ))
  exact UniformInterval.sampled_convolution_tvDist_le q radius rounds narrow hNarrow

end FormalProof4FHE.LWE.NoiseFlooding
