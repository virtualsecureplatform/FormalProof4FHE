/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.Security
import FormalProof4FHE.SharedRandomness.Reduction

/-!
# Semi-Adaptive Leaky LWE

This module formalizes the finite-game reduction underlying Lai--Swarnakar--Woo,
*Leaky LWE: Learning with Errors with Semi-Adaptive Secret- and Error-Leakage* (2025),
Definition 3 and Theorem 3.

The adversary first sees the public LWE challenge and then chooses an admissible leakage
description.  A statistical simulator samples additive secret/error corrections and a simulated
leakage.  If the corrected source hidden values and simulated leakage are within total variation
`delta` of the target hidden values and genuine noisy leakage, then the Leaky-LWE advantage is at
most the underlying LWE advantage plus `2 * delta`.  Instantiating

`delta = 2 * epsilon / (1 - epsilon)`

gives the paper's loss `4 * epsilon / (1 - epsilon)`.

The theorem is generic over finite `ProbComp` samplers and makes the statistical premise explicit.
It does not prove the paper's preceding multivariate discrete-Gaussian theorem that constructs the
simulator from covariance, smoothing, embedding, and leakage-operator-norm hypotheses.  Those
analytic objects are not currently available in Mathlib or this repository.  No axiom is introduced
for that missing layer.
-/

open Matrix OracleComp

namespace FormalProof4FHE.LWE.Leaky

noncomputable section

/-! ## Problems, adversaries, and games -/

/-- Public parameters for a semi-adaptive Leaky-LWE problem.

`source` is the ordinary LWE problem used by the reduction.  The target secret and error laws may
be wider.  The challenge, noiseless map, and uniform output law are shared with `source`.
`admissible` implements the assertion that the adversarially selected leakage belongs to the
allowed family. -/
structure Parameters (Sample Secret Output Leakage Choice : Type) where
  source : LearningWithErrors.Problem Sample Secret Output
  targetSecret : ProbComp Secret
  targetError : ProbComp Output
  leakageNoise : ProbComp Leakage
  leakage : Choice → Secret → Output → Leakage
  admissible : Choice → Bool

/-- A two-stage Leaky-LWE adversary.  Its first stage sees only the public challenge.  Any public
challenge-dependent auxiliary information can be included in `Sample`, and the first stage can
retain arbitrary finite state for the distinguishing stage. -/
structure Adversary (Sample Output Leakage Choice State : Type) where
  choose : Sample → ProbComp (Choice × State)
  distinguish : Output × Leakage × State → ProbComp Bool

/-- Target hidden values together with the noisy leakage exposed to the adversary. -/
structure HiddenView (Secret Output Leakage : Type) where
  secret : Secret
  error : Output
  leakage : Leakage

/-- Additive secret/error corrections and the leakage emitted by the source simulator. -/
structure Correction (Secret Output Leakage : Type) where
  secret : Secret
  error : Output
  leakage : Leakage

/-- A simulator selected after seeing the public challenge and the adversarial leakage choice. -/
structure Simulator (Sample Secret Output Leakage Choice : Type) where
  run : Sample → Choice → ProbComp (Correction Secret Output Leakage)

/-- Sample the target hidden values and their genuine noisy leakage. -/
def targetHiddenSampler
    {Sample Secret Output Leakage Choice : Type} [Add Leakage]
    (params : Parameters Sample Secret Output Leakage Choice) (choice : Choice) :
    ProbComp (HiddenView Secret Output Leakage) := do
  let secret ← params.targetSecret
  let error ← params.targetError
  let leakageNoise ← params.leakageNoise
  return ⟨secret, error, params.leakage choice secret error + leakageNoise⟩

/-- Sample source hidden values and add the simulator's correlated corrections. -/
def simulatedHiddenSampler
    {Sample Secret Output Leakage Choice : Type}
    [Add Secret] [Add Output]
    (params : Parameters Sample Secret Output Leakage Choice)
    (simulator : Simulator Sample Secret Output Leakage Choice)
    (sample : Sample) (choice : Choice) :
    ProbComp (HiddenView Secret Output Leakage) := do
  let sourceSecret ← params.source.sampleSecret
  let sourceError ← params.source.sampleError
  let correction ← simulator.run sample choice
  return ⟨sourceSecret + correction.secret,
    sourceError + correction.error, correction.leakage⟩

/-- The real semi-adaptive Leaky-LWE game. -/
def realGame
    {Sample Secret Output Leakage Choice State : Type}
    [Add Output] [Add Leakage]
    (params : Parameters Sample Secret Output Leakage Choice)
    (adversary : Adversary Sample Output Leakage Choice State) : ProbComp Bool := do
  let sample ← params.source.sampleChallenge
  let chosen ← adversary.choose sample
  if params.admissible chosen.1 = true then
    let hidden ← targetHiddenSampler params chosen.1
    adversary.distinguish
      (params.source.noiseless hidden.secret sample + hidden.error,
        hidden.leakage, chosen.2)
  else
    return false

/-- The random semi-adaptive Leaky-LWE game.  Secret, error, and leakage noise are still sampled,
so the leakage retains its real distribution while the LWE right-hand side is uniform. -/
def randomGame
    {Sample Secret Output Leakage Choice State : Type}
    [Add Leakage]
    (params : Parameters Sample Secret Output Leakage Choice)
    (adversary : Adversary Sample Output Leakage Choice State) : ProbComp Bool := do
  let sample ← params.source.sampleChallenge
  let chosen ← adversary.choose sample
  if params.admissible chosen.1 = true then
    let hidden ← targetHiddenSampler params chosen.1
    let uniform ← params.source.sampleUniform
    adversary.distinguish (uniform, hidden.leakage, chosen.2)
  else
    return false

/-- Absolute real-versus-random Leaky-LWE distinguishing advantage. -/
def advantage
    {Sample Secret Output Leakage Choice State : Type}
    [Add Output] [Add Leakage]
    (params : Parameters Sample Secret Output Leakage Choice)
    (adversary : Adversary Sample Output Leakage Choice State) : ℝ :=
  (realGame params adversary).boolDistAdvantage (randomGame params adversary)

/-! ## Statistical simulator certificate -/

/-- The noiseless LWE map is additive in its secret argument. -/
def NoiselessAdditive
    {Sample Secret Output : Type} [Add Secret] [Add Output]
    (problem : LearningWithErrors.Problem Sample Secret Output) : Prop :=
  ∀ sample left right,
    problem.noiseless (left + right) sample =
      problem.noiseless left sample + problem.noiseless right sample

/-- The source uniform law is invariant under every additive correction used by the simulator. -/
def UniformAddInvariant
    {Sample Secret Output : Type} [Add Output]
    (problem : LearningWithErrors.Problem Sample Secret Output) : Prop :=
  ∀ shift,
    evalDist (problem.sampleUniform >>= fun uniform ↦ pure (uniform + shift)) =
      evalDist problem.sampleUniform

/-- A statistical certificate is exactly the output needed from the paper's core Gaussian theorem:
for every admissible semi-adaptive leakage choice, corrected source hidden values and the simulated
leakage are close to the target hidden values and genuine noisy leakage. -/
def SimulationSound
    {Sample Secret Output Leakage Choice : Type}
    [Add Secret] [Add Output] [Add Leakage]
    (params : Parameters Sample Secret Output Leakage Choice)
    (simulator : Simulator Sample Secret Output Leakage Choice)
    (bound : ℝ) : Prop :=
  0 ≤ bound ∧
    ∀ sample choice, params.admissible choice = true →
      tvDist (simulatedHiddenSampler params simulator sample choice)
          (targetHiddenSampler params choice) ≤ bound

/-! ## Views induced by a simulator -/

/-- Assemble a real LWE output and leakage from hidden values. -/
def realView
    {Sample Secret Output Leakage : Type} [Add Output]
    (problem : LearningWithErrors.Problem Sample Secret Output)
    (sample : Sample) (hidden : HiddenView Secret Output Leakage) : Output × Leakage :=
  (problem.noiseless hidden.secret sample + hidden.error, hidden.leakage)

/-- Real view produced from corrected source hidden values. -/
def simulatedRealView
    {Sample Secret Output Leakage Choice : Type}
    [Add Secret] [Add Output]
    (params : Parameters Sample Secret Output Leakage Choice)
    (simulator : Simulator Sample Secret Output Leakage Choice)
    (sample : Sample) (choice : Choice) : ProbComp (Output × Leakage) :=
  realView params.source sample <$> simulatedHiddenSampler params simulator sample choice

/-- Genuine target real view. -/
def targetRealView
    {Sample Secret Output Leakage Choice : Type}
    [Add Output] [Add Leakage]
    (params : Parameters Sample Secret Output Leakage Choice)
    (sample : Sample) (choice : Choice) : ProbComp (Output × Leakage) :=
  realView params.source sample <$> targetHiddenSampler params choice

/-- Uniform output paired with the leakage marginal of corrected source hidden values. -/
def simulatedUniformView
    {Sample Secret Output Leakage Choice : Type}
    [Add Secret] [Add Output]
    (params : Parameters Sample Secret Output Leakage Choice)
    (simulator : Simulator Sample Secret Output Leakage Choice)
    (sample : Sample) (choice : Choice) : ProbComp (Output × Leakage) := do
  let hidden ← simulatedHiddenSampler params simulator sample choice
  let uniform ← params.source.sampleUniform
  return (uniform, hidden.leakage)

/-- Uniform output paired with the genuine target leakage marginal. -/
def targetUniformView
    {Sample Secret Output Leakage Choice : Type}
    [Add Leakage]
    (params : Parameters Sample Secret Output Leakage Choice)
    (choice : Choice) : ProbComp (Output × Leakage) := do
  let hidden ← targetHiddenSampler params choice
  let uniform ← params.source.sampleUniform
  return (uniform, hidden.leakage)

/-- Uniform output paired directly with the simulator's leakage. -/
def correctionUniformView
    {Sample Secret Output Leakage Choice : Type}
    (params : Parameters Sample Secret Output Leakage Choice)
    (simulator : Simulator Sample Secret Output Leakage Choice)
    (sample : Sample) (choice : Choice) : ProbComp (Output × Leakage) := do
  let correction ← simulator.run sample choice
  let uniform ← params.source.sampleUniform
  return (uniform, correction.leakage)

theorem simulatedRealView_tvDist_target_le
    {Sample Secret Output Leakage Choice : Type}
    [Add Secret] [Add Output] [Add Leakage]
    (params : Parameters Sample Secret Output Leakage Choice)
    (simulator : Simulator Sample Secret Output Leakage Choice)
    (bound : ℝ) (hSound : SimulationSound params simulator bound)
    (sample : Sample) (choice : Choice) (hChoice : params.admissible choice = true) :
    tvDist (simulatedRealView params simulator sample choice)
        (targetRealView params sample choice) ≤ bound := by
  exact (tvDist_map_le (realView params.source sample)
    (simulatedHiddenSampler params simulator sample choice)
    (targetHiddenSampler params choice)).trans (hSound.2 sample choice hChoice)

theorem simulatedUniformView_tvDist_target_le
    {Sample Secret Output Leakage Choice : Type}
    [Add Secret] [Add Output] [Add Leakage]
    (params : Parameters Sample Secret Output Leakage Choice)
    (simulator : Simulator Sample Secret Output Leakage Choice)
    (bound : ℝ) (hSound : SimulationSound params simulator bound)
    (sample : Sample) (choice : Choice) (hChoice : params.admissible choice = true) :
    tvDist (simulatedUniformView params simulator sample choice)
        (targetUniformView params choice) ≤ bound := by
  unfold simulatedUniformView targetUniformView
  exact (tvDist_bind_right_le (m := ProbComp)
    (α := HiddenView Secret Output Leakage) (β := Output × Leakage)
    (fun hidden : HiddenView Secret Output Leakage ↦ do
      let uniform ← params.source.sampleUniform
      return (uniform, hidden.leakage))
    (simulatedHiddenSampler params simulator sample choice)
    (targetHiddenSampler params choice)).trans (hSound.2 sample choice hChoice)

/-- The source secret and error draws in `simulatedUniformView` are ghosts: only the simulator's
leakage is retained. -/
theorem simulatedUniformView_evalDist_eq_correction
    {Sample Secret Output Leakage Choice : Type}
    [Add Secret] [Add Output]
    (params : Parameters Sample Secret Output Leakage Choice)
    (simulator : Simulator Sample Secret Output Leakage Choice)
    (sample : Sample) (choice : Choice) :
    evalDist (simulatedUniformView params simulator sample choice) =
      evalDist (correctionUniformView params simulator sample choice) := by
  simp only [simulatedUniformView, simulatedHiddenSampler, correctionUniformView,
    bind_assoc, pure_bind]
  calc
    evalDist (params.source.sampleSecret >>= fun _sourceSecret ↦
        params.source.sampleError >>= fun _sourceError ↦
          simulator.run sample choice >>= fun correction ↦
            params.source.sampleUniform >>= fun uniform ↦
              pure (uniform, correction.leakage)) =
      evalDist (params.source.sampleSecret >>= fun _sourceSecret ↦
        simulator.run sample choice >>= fun correction ↦
          params.source.sampleUniform >>= fun uniform ↦
            pure (uniform, correction.leakage)) := by
      refine evalDist_bind_congr' params.source.sampleSecret fun _sourceSecret ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        params.source.sampleError (by simp) _
    _ = evalDist (simulator.run sample choice >>= fun correction ↦
        params.source.sampleUniform >>= fun uniform ↦
          pure (uniform, correction.leakage)) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        params.source.sampleSecret (by simp) _

theorem correctionUniformView_tvDist_target_le
    {Sample Secret Output Leakage Choice : Type}
    [Add Secret] [Add Output] [Add Leakage]
    (params : Parameters Sample Secret Output Leakage Choice)
    (simulator : Simulator Sample Secret Output Leakage Choice)
    (bound : ℝ) (hSound : SimulationSound params simulator bound)
    (sample : Sample) (choice : Choice) (hChoice : params.admissible choice = true) :
    tvDist (correctionUniformView params simulator sample choice)
        (targetUniformView params choice) ≤ bound := by
  unfold tvDist
  rw [← simulatedUniformView_evalDist_eq_correction params simulator sample choice]
  exact simulatedUniformView_tvDist_target_le params simulator bound hSound
    sample choice hChoice

/-! ## Staged games and the ordinary-LWE reduction -/

/-- The simulator-based real game, ordered like the semi-adaptive target game. -/
def simulatedRealGame
    {Sample Secret Output Leakage Choice State : Type}
    [Add Secret] [Add Output]
    (params : Parameters Sample Secret Output Leakage Choice)
    (simulator : Simulator Sample Secret Output Leakage Choice)
    (adversary : Adversary Sample Output Leakage Choice State) : ProbComp Bool := do
  let sample ← params.source.sampleChallenge
  let chosen ← adversary.choose sample
  if params.admissible chosen.1 = true then
    let view ← simulatedRealView params simulator sample chosen.1
    adversary.distinguish (view.1, view.2, chosen.2)
  else
    return false

/-- The normalized simulator-based uniform game. -/
def simulatedRandomGame
    {Sample Secret Output Leakage Choice State : Type}
    (params : Parameters Sample Secret Output Leakage Choice)
    (simulator : Simulator Sample Secret Output Leakage Choice)
    (adversary : Adversary Sample Output Leakage Choice State) : ProbComp Bool := do
  let sample ← params.source.sampleChallenge
  let chosen ← adversary.choose sample
  if params.admissible chosen.1 = true then
    let view ← correctionUniformView params simulator sample chosen.1
    adversary.distinguish (view.1, view.2, chosen.2)
  else
    return false

/-- Public reduction from a Leaky-LWE adversary to an adversary for the source LWE problem. -/
def reduction
    {Sample Secret Output Leakage Choice State : Type}
    [Add Output]
    (params : Parameters Sample Secret Output Leakage Choice)
    (simulator : Simulator Sample Secret Output Leakage Choice)
    (adversary : Adversary Sample Output Leakage Choice State) :
    LearningWithErrors.Adversary params.source :=
  fun transcript ↦ do
    let chosen ← adversary.choose transcript.1
    if params.admissible chosen.1 = true then
      let correction ← simulator.run transcript.1 chosen.1
      adversary.distinguish
        (transcript.2 +
            (params.source.noiseless correction.secret transcript.1 + correction.error),
          correction.leakage, chosen.2)
    else
      return false

/-- The transformed source real output is the LWE output of the corrected hidden values. -/
theorem reduction_real_output
    {Sample Secret Output Leakage Choice State : Type}
    [AddCommGroup Secret] [AddCommGroup Output]
    (params : Parameters Sample Secret Output Leakage Choice)
    (hNoiseless : NoiselessAdditive params.source)
    (adversary : Adversary Sample Output Leakage Choice State)
    (sample : Sample) (sourceSecret : Secret) (sourceError : Output)
    (correction : Correction Secret Output Leakage) (state : State) :
    adversary.distinguish
        ((params.source.noiseless sourceSecret sample + sourceError) +
            (params.source.noiseless correction.secret sample + correction.error),
          correction.leakage, state) =
      adversary.distinguish
        (params.source.noiseless (sourceSecret + correction.secret) sample +
            (sourceError + correction.error),
          correction.leakage, state) := by
  congr 2
  rw [hNoiseless sample]
  abel

/-- The source LWE real game with the reduction has exactly the staged simulator distribution. -/
theorem reduction_realGame_evalDist
    {Sample Secret Output Leakage Choice State : Type}
    [AddCommGroup Secret] [AddCommGroup Output]
    (params : Parameters Sample Secret Output Leakage Choice)
    (simulator : Simulator Sample Secret Output Leakage Choice)
    (adversary : Adversary Sample Output Leakage Choice State)
    (hNoiseless : NoiselessAdditive params.source) :
    evalDist (LearningWithErrors.game0 params.source
        (reduction params simulator adversary)) =
      evalDist (simulatedRealGame params simulator adversary) := by
  simp only [LearningWithErrors.game0, LearningWithErrors.distr, reduction,
    simulatedRealGame, simulatedRealView, simulatedHiddenSampler, realView,
    map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  refine evalDist_bind_congr' params.source.sampleChallenge fun sample ↦ ?_
  calc
    evalDist (params.source.sampleSecret >>= fun sourceSecret ↦
        params.source.sampleError >>= fun sourceError ↦
          adversary.choose sample >>= fun chosen ↦
            if params.admissible chosen.1 = true then
              simulator.run sample chosen.1 >>= fun correction ↦
                adversary.distinguish
                  ((params.source.noiseless sourceSecret sample + sourceError) +
                      (params.source.noiseless correction.secret sample + correction.error),
                    correction.leakage, chosen.2)
            else pure false) =
      evalDist (adversary.choose sample >>= fun chosen ↦
        params.source.sampleSecret >>= fun sourceSecret ↦
          params.source.sampleError >>= fun sourceError ↦
            if params.admissible chosen.1 = true then
              simulator.run sample chosen.1 >>= fun correction ↦
                adversary.distinguish
                  ((params.source.noiseless sourceSecret sample + sourceError) +
                      (params.source.noiseless correction.secret sample + correction.error),
                    correction.leakage, chosen.2)
            else pure false) := by
      calc
        _ = evalDist (params.source.sampleSecret >>= fun sourceSecret ↦
            adversary.choose sample >>= fun chosen ↦
              params.source.sampleError >>= fun sourceError ↦
                if params.admissible chosen.1 = true then
                  simulator.run sample chosen.1 >>= fun correction ↦
                    adversary.distinguish
                      ((params.source.noiseless sourceSecret sample + sourceError) +
                          (params.source.noiseless correction.secret sample + correction.error),
                        correction.leakage, chosen.2)
                else pure false) := by
          refine evalDist_bind_congr' params.source.sampleSecret fun sourceSecret ↦ ?_
          exact evalDist_bind_bind_swap params.source.sampleError
            (adversary.choose sample) _
        _ = _ := evalDist_bind_bind_swap params.source.sampleSecret
          (adversary.choose sample) _
    _ = evalDist (adversary.choose sample >>= fun chosen ↦
        if params.admissible chosen.1 = true then
          params.source.sampleSecret >>= fun sourceSecret ↦
            params.source.sampleError >>= fun sourceError ↦
              simulator.run sample chosen.1 >>= fun correction ↦
                adversary.distinguish
                  (params.source.noiseless (sourceSecret + correction.secret) sample +
                      (sourceError + correction.error),
                    correction.leakage, chosen.2)
        else pure false) := by
      refine evalDist_bind_congr' (adversary.choose sample) fun chosen ↦ ?_
      by_cases hChoice : params.admissible chosen.1 = true
      · simp only [hChoice, if_true]
        refine evalDist_bind_congr' params.source.sampleSecret fun sourceSecret ↦ ?_
        refine evalDist_bind_congr' params.source.sampleError fun sourceError ↦ ?_
        refine evalDist_bind_congr' (simulator.run sample chosen.1) fun correction ↦ ?_
        rw [reduction_real_output params hNoiseless adversary sample sourceSecret
          sourceError correction chosen.2]
      · simp only [hChoice]
        calc
          evalDist (params.source.sampleSecret >>= fun _sourceSecret ↦
              params.source.sampleError >>= fun _sourceError ↦ pure false) =
              evalDist (params.source.sampleSecret >>= fun _sourceSecret ↦
                pure false) := by
            refine evalDist_bind_congr' params.source.sampleSecret fun _sourceSecret ↦ ?_
            exact
              FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
                params.source.sampleError (by simp) _
          _ = evalDist (pure false) :=
            FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
              params.source.sampleSecret (by simp) _
    _ = _ := by rfl

/-- For fixed simulator output, translating the source uniform value by the additive correction
does not change the subsequent adversarial view. -/
theorem fixed_uniform_correction_evalDist
    {Sample Secret Output Leakage Choice State : Type}
    [Add Output]
    (params : Parameters Sample Secret Output Leakage Choice)
    (adversary : Adversary Sample Output Leakage Choice State)
    (hUniform : UniformAddInvariant params.source)
    (sample : Sample) (correction : Correction Secret Output Leakage) (state : State) :
    evalDist (params.source.sampleUniform >>= fun uniform ↦
        adversary.distinguish
          (uniform +
              (params.source.noiseless correction.secret sample + correction.error),
            correction.leakage, state)) =
      evalDist (params.source.sampleUniform >>= fun uniform ↦
        adversary.distinguish (uniform, correction.leakage, state)) := by
  let shift := params.source.noiseless correction.secret sample + correction.error
  have hshift :
      evalDist (params.source.sampleUniform >>= fun uniform ↦ pure (uniform + shift)) =
        evalDist params.source.sampleUniform := hUniform shift
  simpa only [shift, bind_assoc, pure_bind] using
    FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hshift
      (fun uniform ↦ adversary.distinguish (uniform, correction.leakage, state))

/-- The source LWE random game with the reduction has exactly the normalized simulator
distribution. -/
theorem reduction_randomGame_evalDist
    {Sample Secret Output Leakage Choice State : Type}
    [Add Output]
    (params : Parameters Sample Secret Output Leakage Choice)
    (simulator : Simulator Sample Secret Output Leakage Choice)
    (adversary : Adversary Sample Output Leakage Choice State)
    (hUniform : UniformAddInvariant params.source) :
    evalDist (LearningWithErrors.game1 params.source
        (reduction params simulator adversary)) =
      evalDist (simulatedRandomGame params simulator adversary) := by
  simp only [LearningWithErrors.game1, LearningWithErrors.uniformDistr, reduction,
    simulatedRandomGame, correctionUniformView, bind_assoc, pure_bind]
  refine evalDist_bind_congr' params.source.sampleChallenge fun sample ↦ ?_
  calc
    evalDist (params.source.sampleUniform >>= fun uniform ↦
        adversary.choose sample >>= fun chosen ↦
          if params.admissible chosen.1 = true then
            simulator.run sample chosen.1 >>= fun correction ↦
              adversary.distinguish
                (uniform +
                    (params.source.noiseless correction.secret sample + correction.error),
                  correction.leakage, chosen.2)
          else pure false) =
      evalDist (adversary.choose sample >>= fun chosen ↦
        params.source.sampleUniform >>= fun uniform ↦
          if params.admissible chosen.1 = true then
            simulator.run sample chosen.1 >>= fun correction ↦
              adversary.distinguish
                (uniform +
                    (params.source.noiseless correction.secret sample + correction.error),
                  correction.leakage, chosen.2)
          else pure false) :=
      evalDist_bind_bind_swap params.source.sampleUniform (adversary.choose sample) _
    _ = evalDist (adversary.choose sample >>= fun chosen ↦
        if params.admissible chosen.1 = true then
          simulator.run sample chosen.1 >>= fun correction ↦
            params.source.sampleUniform >>= fun uniform ↦
              adversary.distinguish
                (uniform +
                    (params.source.noiseless correction.secret sample + correction.error),
                  correction.leakage, chosen.2)
        else pure false) := by
      refine evalDist_bind_congr' (adversary.choose sample) fun chosen ↦ ?_
      by_cases hChoice : params.admissible chosen.1 = true
      · simp only [hChoice, if_true]
        exact evalDist_bind_bind_swap params.source.sampleUniform
          (simulator.run sample chosen.1) _
      · simp only [hChoice]
        exact
          FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
            params.source.sampleUniform (by simp) _
    _ = evalDist (adversary.choose sample >>= fun chosen ↦
        if params.admissible chosen.1 = true then
          simulator.run sample chosen.1 >>= fun correction ↦
            params.source.sampleUniform >>= fun uniform ↦
              adversary.distinguish (uniform, correction.leakage, chosen.2)
        else pure false) := by
      refine evalDist_bind_congr' (adversary.choose sample) fun chosen ↦ ?_
      by_cases hChoice : params.admissible chosen.1 = true
      · simp only [hChoice, if_true]
        refine evalDist_bind_congr' (simulator.run sample chosen.1) fun correction ↦ ?_
        exact fixed_uniform_correction_evalDist params adversary hUniform sample
          correction chosen.2
      · simp [hChoice]
    _ = _ := by rfl

/-! ## Statistical game bounds -/

theorem simulatedRealGame_tvDist_realGame_le
    {Sample Secret Output Leakage Choice State : Type}
    [Add Secret] [Add Output] [Add Leakage]
    (params : Parameters Sample Secret Output Leakage Choice)
    (simulator : Simulator Sample Secret Output Leakage Choice)
    (adversary : Adversary Sample Output Leakage Choice State)
    (bound : ℝ) (hSound : SimulationSound params simulator bound) :
    tvDist (simulatedRealGame params simulator adversary)
        (realGame params adversary) ≤ bound := by
  unfold simulatedRealGame realGame
  refine tvDist_bind_left_le_const' params.source.sampleChallenge _ _ bound ?_
  intro sample
  refine tvDist_bind_left_le_const' (adversary.choose sample) _ _ bound ?_
  intro chosen
  by_cases hChoice : params.admissible chosen.1 = true
  · simp only [hChoice, if_true]
    simpa only [targetRealView, map_eq_bind_pure_comp, Function.comp_def,
      realView, bind_assoc, pure_bind] using (tvDist_bind_right_le
      (fun view : Output × Leakage ↦
        adversary.distinguish (view.1, view.2, chosen.2))
      (simulatedRealView params simulator sample chosen.1)
      (targetRealView params sample chosen.1)).trans
        (simulatedRealView_tvDist_target_le params simulator bound hSound
          sample chosen.1 hChoice)
  · simp [hChoice, hSound.1]

theorem simulatedRandomGame_tvDist_randomGame_le
    {Sample Secret Output Leakage Choice State : Type}
    [Add Secret] [Add Output] [Add Leakage]
    (params : Parameters Sample Secret Output Leakage Choice)
    (simulator : Simulator Sample Secret Output Leakage Choice)
    (adversary : Adversary Sample Output Leakage Choice State)
    (bound : ℝ) (hSound : SimulationSound params simulator bound) :
    tvDist (simulatedRandomGame params simulator adversary)
        (randomGame params adversary) ≤ bound := by
  unfold simulatedRandomGame randomGame
  refine tvDist_bind_left_le_const' params.source.sampleChallenge _ _ bound ?_
  intro sample
  refine tvDist_bind_left_le_const' (adversary.choose sample) _ _ bound ?_
  intro chosen
  by_cases hChoice : params.admissible chosen.1 = true
  · simp only [hChoice, if_true]
    simpa only [targetUniformView, bind_assoc, pure_bind] using (tvDist_bind_right_le
      (fun view : Output × Leakage ↦
        adversary.distinguish (view.1, view.2, chosen.2))
      (correctionUniformView params simulator sample chosen.1)
      (targetUniformView params chosen.1)).trans
        (correctionUniformView_tvDist_target_le params simulator bound hSound
          sample chosen.1 hChoice)
  · simp [hChoice, hSound.1]

theorem reduction_realGame_tvDist_le
    {Sample Secret Output Leakage Choice State : Type}
    [AddCommGroup Secret] [AddCommGroup Output] [Add Leakage]
    (params : Parameters Sample Secret Output Leakage Choice)
    (simulator : Simulator Sample Secret Output Leakage Choice)
    (adversary : Adversary Sample Output Leakage Choice State)
    (bound : ℝ) (hSound : SimulationSound params simulator bound)
    (hNoiseless : NoiselessAdditive params.source) :
    tvDist (LearningWithErrors.game0 params.source
        (reduction params simulator adversary))
      (realGame params adversary) ≤ bound := by
  unfold tvDist
  rw [reduction_realGame_evalDist params simulator adversary hNoiseless]
  exact simulatedRealGame_tvDist_realGame_le params simulator adversary bound hSound

theorem reduction_randomGame_tvDist_le
    {Sample Secret Output Leakage Choice State : Type}
    [Add Secret] [Add Output] [Add Leakage]
    (params : Parameters Sample Secret Output Leakage Choice)
    (simulator : Simulator Sample Secret Output Leakage Choice)
    (adversary : Adversary Sample Output Leakage Choice State)
    (bound : ℝ) (hSound : SimulationSound params simulator bound)
    (hUniform : UniformAddInvariant params.source) :
    tvDist (LearningWithErrors.game1 params.source
        (reduction params simulator adversary))
      (randomGame params adversary) ≤ bound := by
  unfold tvDist
  rw [reduction_randomGame_evalDist params simulator adversary hUniform]
  exact simulatedRandomGame_tvDist_randomGame_le params simulator adversary bound hSound

/-! ## Base Leaky-LWE theorem -/

/-- **Base semi-adaptive Leaky-LWE theorem.**  A `bound`-close hidden-value simulator incurs that
statistical loss once in each branch and otherwise reduces losslessly to the source LWE game. -/
theorem advantage_le_lwe_add_two_mul
    {Sample Secret Output Leakage Choice State : Type}
    [AddCommGroup Secret] [AddCommGroup Output] [Add Leakage]
    (params : Parameters Sample Secret Output Leakage Choice)
    (simulator : Simulator Sample Secret Output Leakage Choice)
    (adversary : Adversary Sample Output Leakage Choice State)
    (bound : ℝ) (hSound : SimulationSound params simulator bound)
    (hNoiseless : NoiselessAdditive params.source)
    (hUniform : UniformAddInvariant params.source) :
    advantage params adversary ≤
      LearningWithErrors.advantage params.source
        (reduction params simulator adversary) + 2 * bound := by
  let sourceReal := LearningWithErrors.game0 params.source
    (reduction params simulator adversary)
  let sourceRandom := LearningWithErrors.game1 params.source
    (reduction params simulator adversary)
  let targetReal := realGame params adversary
  let targetRandom := randomGame params adversary
  have hRealTV : tvDist sourceReal targetReal ≤ bound :=
    reduction_realGame_tvDist_le params simulator adversary bound hSound hNoiseless
  have hRandomTV : tvDist sourceRandom targetRandom ≤ bound :=
    reduction_randomGame_tvDist_le params simulator adversary bound hSound hUniform
  have hRealAdv : targetReal.boolDistAdvantage sourceReal ≤ bound := by
    exact (abs_probOutput_toReal_sub_le_tvDist targetReal sourceReal).trans
      ((tvDist_comm sourceReal targetReal ▸ hRealTV))
  have hRandomAdv : sourceRandom.boolDistAdvantage targetRandom ≤ bound :=
    (abs_probOutput_toReal_sub_le_tvDist sourceRandom targetRandom).trans hRandomTV
  have hFirst := ProbComp.boolDistAdvantage_triangle targetReal sourceReal targetRandom
  have hSecond := ProbComp.boolDistAdvantage_triangle sourceReal sourceRandom targetRandom
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage] 
  unfold advantage
  change targetReal.boolDistAdvantage targetRandom ≤
    sourceReal.boolDistAdvantage sourceRandom + 2 * bound
  linarith

/-- Equivalent lower-bound form, matching the direction displayed in Lai--Swarnakar--Woo
Theorem 3. -/
theorem leaky_sub_two_mul_le_lwe_advantage
    {Sample Secret Output Leakage Choice State : Type}
    [AddCommGroup Secret] [AddCommGroup Output] [Add Leakage]
    (params : Parameters Sample Secret Output Leakage Choice)
    (simulator : Simulator Sample Secret Output Leakage Choice)
    (adversary : Adversary Sample Output Leakage Choice State)
    (bound : ℝ) (hSound : SimulationSound params simulator bound)
    (hNoiseless : NoiselessAdditive params.source)
    (hUniform : UniformAddInvariant params.source) :
    advantage params adversary - 2 * bound ≤
      LearningWithErrors.advantage params.source
        (reduction params simulator adversary) := by
  linarith [advantage_le_lwe_add_two_mul params simulator adversary bound hSound
    hNoiseless hUniform]

/-- Per-branch statistical loss used in the paper. -/
def paperBranchLoss (epsilon : ℝ) : ℝ := 2 * epsilon / (1 - epsilon)

/-- Total loss in the statement of the paper's Theorem 3. -/
def paperLoss (epsilon : ℝ) : ℝ := 4 * epsilon / (1 - epsilon)

theorem two_mul_paperBranchLoss (epsilon : ℝ) :
    2 * paperBranchLoss epsilon = paperLoss epsilon := by
  unfold paperBranchLoss paperLoss
  ring

/-- The paper-normalized form of the base theorem.  The analytic Gaussian theorem supplies a
`SimulationSound` certificate with branch loss `2ε/(1-ε)`; the game reduction contributes the
displayed `4ε/(1-ε)` and nothing else. -/
theorem advantage_le_lwe_add_paperLoss
    {Sample Secret Output Leakage Choice State : Type}
    [AddCommGroup Secret] [AddCommGroup Output] [Add Leakage]
    (params : Parameters Sample Secret Output Leakage Choice)
    (simulator : Simulator Sample Secret Output Leakage Choice)
    (adversary : Adversary Sample Output Leakage Choice State)
    (epsilon : ℝ)
    (hSound : SimulationSound params simulator (paperBranchLoss epsilon))
    (hNoiseless : NoiselessAdditive params.source)
    (hUniform : UniformAddInvariant params.source) :
    advantage params adversary ≤
      LearningWithErrors.advantage params.source
        (reduction params simulator adversary) + paperLoss epsilon := by
  simpa only [two_mul_paperBranchLoss] using
    advantage_le_lwe_add_two_mul params simulator adversary
      (paperBranchLoss epsilon) hSound hNoiseless hUniform

/-- Lower-bound form exactly matching `Adv_LWE ≥ Adv_LLWE - 4ε/(1-ε)`. -/
theorem leaky_sub_paperLoss_le_lwe_advantage
    {Sample Secret Output Leakage Choice State : Type}
    [AddCommGroup Secret] [AddCommGroup Output] [Add Leakage]
    (params : Parameters Sample Secret Output Leakage Choice)
    (simulator : Simulator Sample Secret Output Leakage Choice)
    (adversary : Adversary Sample Output Leakage Choice State)
    (epsilon : ℝ)
    (hSound : SimulationSound params simulator (paperBranchLoss epsilon))
    (hNoiseless : NoiselessAdditive params.source)
    (hUniform : UniformAddInvariant params.source) :
    advantage params adversary - paperLoss epsilon ≤
      LearningWithErrors.advantage params.source
        (reduction params simulator adversary) := by
  linarith [advantage_le_lwe_add_paperLoss params simulator adversary epsilon hSound
    hNoiseless hUniform]

/-! ## Hardness transfer -/

/-- Concrete Leaky-LWE hardness against a selected class of two-stage adversaries. -/
def HardAgainst
    {Sample Secret Output Leakage Choice State : Type}
    [Add Output] [Add Leakage]
    (params : Parameters Sample Secret Output Leakage Choice)
    (allowed : Adversary Sample Output Leakage Choice State → Prop)
    (bound : ℝ) : Prop :=
  ∀ adversary, allowed adversary → advantage params adversary ≤ bound

theorem hardAgainst_of_lwe
    {Sample Secret Output Leakage Choice State : Type}
    [AddCommGroup Secret] [AddCommGroup Output] [Add Leakage]
    (params : Parameters Sample Secret Output Leakage Choice)
    (simulator : Simulator Sample Secret Output Leakage Choice)
    (leakyAllowed : Adversary Sample Output Leakage Choice State → Prop)
    (sourceAllowed : LearningWithErrors.Adversary params.source → Prop)
    (sourceBound statisticalBound : ℝ)
    (hSound : SimulationSound params simulator statisticalBound)
    (hNoiseless : NoiselessAdditive params.source)
    (hUniform : UniformAddInvariant params.source)
    (hClosed : ∀ adversary, leakyAllowed adversary →
      sourceAllowed (reduction params simulator adversary))
    (hSource : FormalProof4FHE.LWE.HardAgainst params.source sourceAllowed sourceBound) :
    HardAgainst params leakyAllowed (sourceBound + 2 * statisticalBound) := by
  intro adversary hAllowed
  exact (advantage_le_lwe_add_two_mul params simulator adversary statisticalBound
    hSound hNoiseless hUniform).trans
      (add_le_add (hSource _ (hClosed adversary hAllowed)) le_rfl)

/-! ## Error-only (Condition 2) specialization -/

/-- Simulator output needed in the error-only case; it never changes the source secret. -/
structure ErrorCorrection (Output Leakage : Type) where
  error : Output
  leakage : Leakage

/-- An error-only simulator. -/
structure ErrorSimulator (Sample Output Leakage Choice : Type) where
  run : Sample → Choice → ProbComp (ErrorCorrection Output Leakage)

/-- Promote an error-only simulator to the general additive simulator. -/
def Simulator.ofErrorOnly
    {Sample Secret Output Leakage Choice : Type} [Zero Secret]
    (simulator : ErrorSimulator Sample Output Leakage Choice) :
    Simulator Sample Secret Output Leakage Choice where
  run sample choice := do
    let correction ← simulator.run sample choice
    return ⟨0, correction.error, correction.leakage⟩

/-- Source error plus the error-only correction, paired with simulated leakage. -/
def simulatedErrorLeakageSampler
    {Sample Output Leakage Choice : Type} [Add Output]
    (sourceError : ProbComp Output)
    (simulator : ErrorSimulator Sample Output Leakage Choice)
    (sample : Sample) (choice : Choice) : ProbComp (Output × Leakage) := do
  let error ← sourceError
  let correction ← simulator.run sample choice
  return (error + correction.error, correction.leakage)

/-- Target error paired with genuine noisy error leakage. -/
def targetErrorLeakageSampler
    {Output Leakage Choice : Type} [Add Leakage]
    (targetError : ProbComp Output) (leakageNoise : ProbComp Leakage)
    (errorLeakage : Choice → Output → Leakage) (choice : Choice) :
    ProbComp (Output × Leakage) := do
  let error ← targetError
  let noise ← leakageNoise
  return (error, errorLeakage choice error + noise)

/-- Condition-2 statistical premise at the error/leakage level. -/
def ErrorSimulationSound
    {Sample Secret Output Leakage Choice : Type} [Add Output] [Add Leakage]
    (params : Parameters Sample Secret Output Leakage Choice)
    (simulator : ErrorSimulator Sample Output Leakage Choice)
    (errorLeakage : Choice → Output → Leakage) (bound : ℝ) : Prop :=
  0 ≤ bound ∧
    ∀ sample choice, params.admissible choice = true →
      tvDist
        (simulatedErrorLeakageSampler params.source.sampleError simulator sample choice)
        (targetErrorLeakageSampler params.targetError params.leakageNoise
          errorLeakage choice) ≤ bound

/-- An error-only statistical certificate lifts to the general hidden-value certificate when the
source and target secret laws agree and leakage is independent of the secret.  This is the exact
finite-game content of Condition 2's "identical and arbitrary" secret clause. -/
theorem simulationSound_of_errorOnly
    {Sample Secret Output Leakage Choice : Type}
    [AddCommGroup Secret] [Add Output] [Add Leakage]
    (params : Parameters Sample Secret Output Leakage Choice)
    (simulator : ErrorSimulator Sample Output Leakage Choice)
    (errorLeakage : Choice → Output → Leakage) (bound : ℝ)
    (hTargetSecret : params.targetSecret = params.source.sampleSecret)
    (hLeakage : ∀ choice secret error,
      params.leakage choice secret error = errorLeakage choice error)
    (hError : ErrorSimulationSound params simulator errorLeakage bound) :
    SimulationSound params (Simulator.ofErrorOnly simulator) bound := by
  refine ⟨hError.1, fun sample choice hChoice ↦ ?_⟩
  unfold simulatedHiddenSampler targetHiddenSampler Simulator.ofErrorOnly
  rw [hTargetSecret]
  simp only [bind_assoc, pure_bind, add_zero]
  refine tvDist_bind_left_le_const' params.source.sampleSecret _ _ bound ?_
  intro secret
  simpa only [simulatedErrorLeakageSampler, targetErrorLeakageSampler,
    map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
    hLeakage choice secret] using (tvDist_map_le
    (fun errorAndLeakage : Output × Leakage ↦
      (⟨secret, errorAndLeakage.1, errorAndLeakage.2⟩ : HiddenView Secret Output Leakage))
    (simulatedErrorLeakageSampler params.source.sampleError simulator sample choice)
    (targetErrorLeakageSampler params.targetError params.leakageNoise
      errorLeakage choice)).trans (hError.2 sample choice hChoice)

/-- Condition-2 form of the base theorem: the secret law is arbitrary but identical, and only the
error is leaked. -/
theorem errorOnly_advantage_le_lwe_add_two_mul
    {Sample Secret Output Leakage Choice State : Type}
    [AddCommGroup Secret] [AddCommGroup Output] [Add Leakage]
    (params : Parameters Sample Secret Output Leakage Choice)
    (simulator : ErrorSimulator Sample Output Leakage Choice)
    (errorLeakage : Choice → Output → Leakage)
    (adversary : Adversary Sample Output Leakage Choice State)
    (bound : ℝ)
    (hTargetSecret : params.targetSecret = params.source.sampleSecret)
    (hLeakage : ∀ choice secret error,
      params.leakage choice secret error = errorLeakage choice error)
    (hError : ErrorSimulationSound params simulator errorLeakage bound)
    (hNoiseless : NoiselessAdditive params.source)
    (hUniform : UniformAddInvariant params.source) :
    advantage params adversary ≤
      LearningWithErrors.advantage params.source
        (reduction params (Simulator.ofErrorOnly simulator) adversary) + 2 * bound :=
  advantage_le_lwe_add_two_mul params (Simulator.ofErrorOnly simulator) adversary bound
    (simulationSound_of_errorOnly params simulator errorLeakage bound
      hTargetSecret hLeakage hError) hNoiseless hUniform

/-- Paper-loss form of the error-only Condition-2 theorem. -/
theorem errorOnly_advantage_le_lwe_add_paperLoss
    {Sample Secret Output Leakage Choice State : Type}
    [AddCommGroup Secret] [AddCommGroup Output] [Add Leakage]
    (params : Parameters Sample Secret Output Leakage Choice)
    (simulator : ErrorSimulator Sample Output Leakage Choice)
    (errorLeakage : Choice → Output → Leakage)
    (adversary : Adversary Sample Output Leakage Choice State)
    (epsilon : ℝ)
    (hTargetSecret : params.targetSecret = params.source.sampleSecret)
    (hLeakage : ∀ choice secret error,
      params.leakage choice secret error = errorLeakage choice error)
    (hError : ErrorSimulationSound params simulator errorLeakage
      (paperBranchLoss epsilon))
    (hNoiseless : NoiselessAdditive params.source)
    (hUniform : UniformAddInvariant params.source) :
    advantage params adversary ≤
      LearningWithErrors.advantage params.source
        (reduction params (Simulator.ofErrorOnly simulator) adversary) + paperLoss epsilon := by
  simpa only [two_mul_paperBranchLoss] using
    errorOnly_advantage_le_lwe_add_two_mul params simulator errorLeakage adversary
      (paperBranchLoss epsilon) hTargetSecret hLeakage hError hNoiseless hUniform

/-! ## Standard matrix-LWE facts -/

/-- Vector--matrix multiplication is additive in the secret. -/
theorem batchProblem_noiselessAdditive
    {R : Type} [Semiring R] [DecidableEq R] [SampleableType R]
    (n m : ℕ) (secretSampler : ProbComp (Fin n → R)) (errorSampler : ProbComp R) :
    NoiselessAdditive (FormalProof4FHE.LWE.batchProblem n m secretSampler errorSampler) := by
  intro sample left right
  funext coordinate
  simp [FormalProof4FHE.LWE.batchProblem, Matrix.vecMul, dotProduct,
    Finset.sum_add_distrib, add_mul]

/-- The standard uniform output law of matrix LWE is invariant under additive corrections. -/
theorem batchProblem_uniformAddInvariant
    {R : Type} [CommRing R] [DecidableEq R] [SampleableType R]
    (n m : ℕ) (secretSampler : ProbComp (Fin n → R)) (errorSampler : ProbComp R) :
    UniformAddInvariant
      (FormalProof4FHE.LWE.batchProblem n m secretSampler errorSampler) := by
  intro shift
  change evalDist ((($ᵗ (Fin m → R)) >>= fun uniform ↦ pure (uniform + shift))) =
    evalDist ($ᵗ (Fin m → R))
  simpa only [map_eq_bind_pure_comp, Function.comp_def] using
    (evalDist_add_right_uniform (α := Fin m → R) shift)

/-! ## Matrix-form leakage -/

/-- A pair of secret- and error-leakage matrices as in Definition 3. -/
structure LeakageMatrices (R : Type) (n m columns : ℕ) where
  secret : Matrix (Fin n) (Fin columns) R
  error : Matrix (Fin m) (Fin columns) R

/-- Matrix-form leakage `(sᵀ,eᵀ)L`. -/
def matrixLeakage
    {R : Type} [Semiring R] {n m columns : ℕ}
    (matrices : LeakageMatrices R n m columns)
    (secret : Fin n → R) (error : Fin m → R) : Fin columns → R :=
  vecMul secret matrices.secret + vecMul error matrices.error

/-- Error-only matrix leakage used by Condition 2 and the circular-RLWE application. -/
def errorMatrixLeakage
    {R : Type} [Semiring R] {m columns : ℕ}
    (matrix : Matrix (Fin m) (Fin columns) R) (error : Fin m → R) : Fin columns → R :=
  vecMul error matrix

/-- Embedding an error-only matrix into the general matrix choice removes all secret dependence. -/
theorem matrixLeakage_errorOnly
    {R : Type} [Semiring R] {n m columns : ℕ}
    (matrix : Matrix (Fin m) (Fin columns) R)
    (secret : Fin n → R) (error : Fin m → R) :
    matrixLeakage (LeakageMatrices.mk 0 matrix) secret error =
      errorMatrixLeakage matrix error := by
  simp [matrixLeakage, errorMatrixLeakage]

end

end FormalProof4FHE.LWE.Leaky
