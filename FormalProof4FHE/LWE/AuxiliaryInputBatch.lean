/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.AuxiliaryInput
import FormalProof4FHE.Probability.FiniteProduct
import VCVio.OracleComp.QueryTracking.RandomOracle.DeferredSampling

/-!
# Finite Same-Secret Batching for Auxiliary-Input CircLWE

An auxiliary-input circular-LWE problem already gives its experiment-level continuation the
hidden secret.  This permits a sound standard hybrid over polynomially many challenges under one
fixed secret: one native challenge is embedded at a uniformly chosen coordinate, challenges
before it are uniform, and challenges after it are real.  The secret is used only by the
experiment to sample those correlated views.

This file proves the exact randomized-hybrid identity

`batch advantage = batch size * one-challenge randomized-hybrid advantage`.

Each batch coordinate receives a freshly sampled copy of the problem's auxiliary input.  Thus
the theorem preserves same-secret side information instead of silently replacing it by public or
independent data.  The reduction retains cancellation among adjacent signed hybrid gaps.
-/

open OracleComp

namespace FormalProof4FHE.LWE.AuxiliaryInput.Batch

variable {Secret Challenge Auxiliary : Type}

/-- One challenge together with the same-coordinate correlated auxiliary input. -/
abbrev View (Challenge Auxiliary : Type) := Challenge × Auxiliary

/-- One real same-secret view. -/
def realView (problem : Problem Secret Challenge Auxiliary) (secret : Secret) :
    ProbComp (View Challenge Auxiliary) := do
  let challenge ← problem.sampleReal secret
  let auxiliary ← problem.sampleAuxiliary secret
  return (challenge, auxiliary)

/-- One uniform challenge with a fresh same-secret auxiliary input. -/
def uniformView (problem : Problem Secret Challenge Auxiliary) (secret : Secret) :
    ProbComp (View Challenge Auxiliary) := do
  let challenge ← problem.sampleUniform
  let auxiliary ← problem.sampleAuxiliary secret
  return (challenge, auxiliary)

/-- A secret-aware continuation consuming a fixed-size vector of public views. -/
abbrev BatchContinuation (Secret Challenge Auxiliary : Type) (count : ℕ) :=
  Secret → (Fin count → View Challenge Auxiliary) → ProbComp Bool

/-- Hybrid with its first `replaced` challenges uniform and all remaining challenges real.  Every
coordinate retains an independently sampled auxiliary input under the common secret. -/
def hybridGame (problem : Problem Secret Challenge Auxiliary) (count replaced : ℕ)
    (continuation : BatchContinuation Secret Challenge Auxiliary count) : ProbComp Bool := do
  let secret ← problem.sampleSecret
  let views ← Fin.mOfFn count fun index ↦
    if index.val < replaced then uniformView problem secret else realView problem secret
  continuation secret views

/-- Real-versus-uniform advantage for a same-secret finite batch. -/
noncomputable def advantage (problem : Problem Secret Challenge Auxiliary) (count : ℕ)
    (continuation : BatchContinuation Secret Challenge Auxiliary count) : ℝ :=
  (hybridGame problem count 0 continuation).boolDistAdvantage
    (hybridGame problem count count continuation)

/-- Embed one supplied CircLWE challenge at `coordinate`, placing uniform challenges before it
and real challenges after it. -/
def coordinateContinuation (problem : Problem Secret Challenge Auxiliary) (count : ℕ)
    (coordinate : Fin count)
    (continuation : BatchContinuation Secret Challenge Auxiliary count) :
    Continuation Secret Challenge Auxiliary :=
  fun secret challenge auxiliary ↦ do
    let views ← Fin.mOfFn count fun index ↦
      if index = coordinate then
        pure (challenge, auxiliary)
      else if index.val < coordinate.val then
        uniformView problem secret
      else
        realView problem secret
    continuation secret views

/-- One native CircLWE continuation choosing the transitioned batch coordinate uniformly. -/
def randomHybridContinuation (problem : Problem Secret Challenge Auxiliary) (count : ℕ)
    [NeZero count]
    (continuation : BatchContinuation Secret Challenge Auxiliary count) :
    Continuation Secret Challenge Auxiliary :=
  fun secret challenge auxiliary ↦ do
    let coordinate ← $ᵗ (Fin count)
    coordinateContinuation problem count coordinate continuation
      secret challenge auxiliary

section CoordinateLaws

variable [Finite Challenge] [Finite Auxiliary]

/-- The real branch of one coordinate reduction realizes the lower adjacent hybrid. -/
theorem evalDist_realGame_coordinateContinuation
    (problem : Problem Secret Challenge Auxiliary) (count : ℕ)
    (coordinate : Fin count)
    (continuation : BatchContinuation Secret Challenge Auxiliary count) :
    𝒟[realGame problem
        (coordinateContinuation problem count coordinate continuation)] =
      𝒟[hybridGame problem count coordinate.val continuation] := by
  classical
  letI : Fintype (View Challenge Auxiliary) := Fintype.ofFinite _
  simp only [realGame, hybridGame, coordinateContinuation]
  apply evalDist_bind_congr' problem.sampleSecret
  intro secret
  let samplers : Fin count → ProbComp (View Challenge Auxiliary) :=
    fun index ↦ if index.val < coordinate.val then
      uniformView problem secret
    else
      realView problem secret
  let replacement (value : View Challenge Auxiliary) :
      ProbComp (Fin count → View Challenge Auxiliary) :=
    Fin.mOfFn count fun index ↦
      if index = coordinate then pure value else samplers index
  let postprocess (views : Fin count → View Challenge Auxiliary) : ProbComp Bool :=
    continuation secret views
  have hpull := FormalProof4FHE.FiniteProduct.evalDist_pull_coordinate
    count samplers coordinate
  have hselected : samplers coordinate = realView problem secret := by
    simp [samplers]
  rw [hselected] at hpull
  have hbase :
      𝒟[realView problem secret >>= replacement] =
        𝒟[Fin.mOfFn count samplers] := by
    simpa [replacement] using hpull
  have hpost :
      𝒟[(realView problem secret >>= replacement) >>= postprocess] =
        𝒟[Fin.mOfFn count samplers >>= postprocess] := by
    calc
      _ = 𝒟[realView problem secret >>= replacement] >>=
            fun views ↦ 𝒟[postprocess views] := evalDist_bind _ _
      _ = 𝒟[Fin.mOfFn count samplers] >>=
            fun views ↦ 𝒟[postprocess views] := by rw [hbase]
      _ = _ := (evalDist_bind _ _).symm
  simpa [realView, replacement, postprocess, samplers, bind_assoc] using hpost

/-- The uniform branch of one coordinate reduction realizes the upper adjacent hybrid. -/
theorem evalDist_uniformGame_coordinateContinuation
    (problem : Problem Secret Challenge Auxiliary) (count : ℕ)
    (coordinate : Fin count)
    (continuation : BatchContinuation Secret Challenge Auxiliary count) :
    𝒟[uniformGame problem
        (coordinateContinuation problem count coordinate continuation)] =
      𝒟[hybridGame problem count (coordinate.val + 1) continuation] := by
  classical
  letI : Fintype (View Challenge Auxiliary) := Fintype.ofFinite _
  simp only [uniformGame, hybridGame, coordinateContinuation]
  apply evalDist_bind_congr' problem.sampleSecret
  intro secret
  let nextSamplers : Fin count → ProbComp (View Challenge Auxiliary) :=
    fun index ↦ if index.val < coordinate.val + 1 then
      uniformView problem secret
    else
      realView problem secret
  let replacement (value : View Challenge Auxiliary) :
      ProbComp (Fin count → View Challenge Auxiliary) :=
    Fin.mOfFn count fun index ↦
      if index = coordinate then pure value
      else if index.val < coordinate.val then
        uniformView problem secret
      else
        realView problem secret
  let postprocess (views : Fin count → View Challenge Auxiliary) : ProbComp Bool :=
    continuation secret views
  have hpull := FormalProof4FHE.FiniteProduct.evalDist_pull_coordinate
    count nextSamplers coordinate
  have hselected : nextSamplers coordinate = uniformView problem secret := by
    simp [nextSamplers]
  rw [hselected] at hpull
  have hreplacement : ∀ value,
      replacement value =
        Fin.mOfFn count (fun index ↦
          if index = coordinate then pure value else nextSamplers index) := by
    intro value
    apply congrArg (Fin.mOfFn count)
    funext index
    by_cases hindex : index = coordinate
    · simp [hindex]
    · simp only [hindex, ↓reduceIte, nextSamplers]
      by_cases hlt : index.val < coordinate.val
      · have hnext : index.val < coordinate.val + 1 := by omega
        simp [hlt, hnext]
      · have hnotnext : ¬index.val < coordinate.val + 1 := by omega
        simp [hlt, hnotnext]
  have hbase :
      𝒟[uniformView problem secret >>= replacement] =
        𝒟[Fin.mOfFn count nextSamplers] := by
    have hf : replacement = fun value ↦
        Fin.mOfFn count (fun index ↦
          if index = coordinate then pure value else nextSamplers index) :=
      funext hreplacement
    simpa [hf] using hpull
  have hpost :
      𝒟[(uniformView problem secret >>= replacement) >>= postprocess] =
        𝒟[Fin.mOfFn count nextSamplers >>= postprocess] := by
    calc
      _ = 𝒟[uniformView problem secret >>= replacement] >>=
            fun views ↦ 𝒟[postprocess views] := evalDist_bind _ _
      _ = 𝒟[Fin.mOfFn count nextSamplers] >>=
            fun views ↦ 𝒟[postprocess views] := by rw [hbase]
      _ = _ := (evalDist_bind _ _).symm
  simpa [uniformView, replacement, postprocess, nextSamplers, bind_assoc] using hpost

end CoordinateLaws

section RandomizedLaws

variable [Finite Challenge] [Finite Auxiliary]

/-- The real branch of the randomized reduction is the uniform mixture of lower hybrid
endpoints. -/
theorem evalDist_realGame_randomHybridContinuation
    (problem : Problem Secret Challenge Auxiliary) (count : ℕ) [NeZero count]
    (continuation : BatchContinuation Secret Challenge Auxiliary count) :
    𝒟[realGame problem
        (randomHybridContinuation problem count continuation)] =
      𝒟[do
        let coordinate ← $ᵗ (Fin count)
        hybridGame problem count coordinate.val continuation] := by
  let samples : ProbComp (Secret × Challenge × Auxiliary) := do
    let secret ← problem.sampleSecret
    let challenge ← problem.sampleReal secret
    let auxiliary ← problem.sampleAuxiliary secret
    return (secret, challenge, auxiliary)
  let coordinates : ProbComp (Fin count) := $ᵗ (Fin count)
  let finish (sample : Secret × Challenge × Auxiliary) (coordinate : Fin count) :=
    coordinateContinuation problem count coordinate continuation
      sample.1 sample.2.1 sample.2.2
  calc
    𝒟[realGame problem
        (randomHybridContinuation problem count continuation)] =
      𝒟[samples >>= fun sample ↦ coordinates >>= finish sample] := by
        simp [realGame, randomHybridContinuation, samples, coordinates, finish,
          bind_assoc]
    _ = 𝒟[coordinates >>= fun coordinate ↦ samples >>= fun sample ↦
        finish sample coordinate] :=
      OracleComp.DeferredSampling.evalDist_bind_comm samples coordinates finish
    _ = _ := by
      apply evalDist_bind_congr' coordinates
      intro coordinate
      simpa [samples, finish, realGame, bind_assoc] using
        (evalDist_realGame_coordinateContinuation problem count coordinate continuation)

/-- The uniform branch of the randomized reduction is the uniform mixture of upper hybrid
endpoints. -/
theorem evalDist_uniformGame_randomHybridContinuation
    (problem : Problem Secret Challenge Auxiliary) (count : ℕ) [NeZero count]
    (continuation : BatchContinuation Secret Challenge Auxiliary count) :
    𝒟[uniformGame problem
        (randomHybridContinuation problem count continuation)] =
      𝒟[do
        let coordinate ← $ᵗ (Fin count)
        hybridGame problem count (coordinate.val + 1) continuation] := by
  let samples : ProbComp (Secret × Challenge × Auxiliary) := do
    let secret ← problem.sampleSecret
    let challenge ← problem.sampleUniform
    let auxiliary ← problem.sampleAuxiliary secret
    return (secret, challenge, auxiliary)
  let coordinates : ProbComp (Fin count) := $ᵗ (Fin count)
  let finish (sample : Secret × Challenge × Auxiliary) (coordinate : Fin count) :=
    coordinateContinuation problem count coordinate continuation
      sample.1 sample.2.1 sample.2.2
  calc
    𝒟[uniformGame problem
        (randomHybridContinuation problem count continuation)] =
      𝒟[samples >>= fun sample ↦ coordinates >>= finish sample] := by
        simp [uniformGame, randomHybridContinuation, samples, coordinates, finish,
          bind_assoc]
    _ = 𝒟[coordinates >>= fun coordinate ↦ samples >>= fun sample ↦
        finish sample coordinate] :=
      OracleComp.DeferredSampling.evalDist_bind_comm samples coordinates finish
    _ = _ := by
      apply evalDist_bind_congr' coordinates
      intro coordinate
      simpa [samples, finish, uniformGame, bind_assoc] using
        (evalDist_uniformGame_coordinateContinuation problem count coordinate continuation)

/-- Real-valued output probability of a finite uniform mixture. -/
theorem probOutput_bind_uniform_toReal {Index Output : Type}
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

/-- **Exact same-secret batching theorem.**  Replacing a batch of `count` real challenges by a
uniform batch costs exactly `count` times one native auxiliary-input CircLWE advantage.  The
single reduction chooses the adjacent transition uniformly and samples every other challenge
under the same hidden secret. -/
theorem advantage_eq_card_mul_randomHybrid
    (problem : Problem Secret Challenge Auxiliary) (count : ℕ) [NeZero count]
    (continuation : BatchContinuation Secret Challenge Auxiliary count) :
    advantage problem count continuation =
      (count : ℝ) *
        circularLweAdvantage problem
          (randomHybridContinuation problem count continuation) := by
  let values (replaced : ℕ) : ℝ :=
    (Pr[= true | hybridGame problem count replaced continuation]).toReal
  unfold advantage circularLweAdvantage ProbComp.boolDistAdvantage
  rw [probOutput_congr rfl
      (evalDist_realGame_randomHybridContinuation problem count continuation),
    probOutput_congr rfl
      (evalDist_uniformGame_randomHybridContinuation problem count continuation),
    probOutput_bind_uniform_toReal,
    probOutput_bind_uniform_toReal]
  simp only [Fintype.card_fin]
  change |values 0 - values count| =
    (count : ℝ) *
      |(∑ coordinate : Fin count, values coordinate.val) / (count : ℝ) -
        (∑ coordinate : Fin count, values (coordinate.val + 1)) / (count : ℝ)|
  have htel :
      (∑ coordinate : Fin count, values coordinate.val) -
          (∑ coordinate : Fin count, values (coordinate.val + 1)) =
        values 0 - values count := by
    have hlower :
        (∑ coordinate : Fin count, values coordinate.val) =
          ∑ index ∈ Finset.range count, values index := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro index hindex
      rw [dif_pos (Finset.mem_range.mp hindex)]
    have hupper :
        (∑ coordinate : Fin count, values (coordinate.val + 1)) =
          ∑ index ∈ Finset.range count, values (index + 1) := by
      rw [Finset.sum_fin_eq_sum_range]
      apply Finset.sum_congr rfl
      intro index hindex
      rw [dif_pos (Finset.mem_range.mp hindex)]
    rw [hlower, hupper, ← Finset.sum_sub_distrib, Finset.sum_range_sub']
  have hcount : (0 : ℝ) < count := by
    exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne count))
  rw [← sub_div, htel, abs_div, abs_of_pos hcount]
  field_simp

end RandomizedLaws

end FormalProof4FHE.LWE.AuxiliaryInput.Batch
