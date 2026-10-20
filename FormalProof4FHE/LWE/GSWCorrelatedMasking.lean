/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/
import FormalProof4FHE.LWE.GSWMasking
import FormalProof4FHE.LWE.Security

/-!
# GSW masking with arbitrary table-correlated public controls

Only the public table's marginal must be uniform. The context may be
arbitrarily correlated with that table, and need not have an efficiently
sampleable conditional distribution. Encryption selectors remain fresh and
independent of the public view. The usual whole-ciphertext leftover-hash
bound still holds for adaptive message choice.

This proves a statistical endpoint for a possible dual-mode reduction.
It does not prove joint mode hiding for any real self-key generator.
-/

open Matrix OracleComp
open scoped BigOperators ENNReal

namespace FormalProof4FHE.LWE.GSWCorrelatedMasking

open GSWMasking GSWGadget

/-- Arbitrary seed-correlated context adds no TV loss when conditional output
laws depend only on the seed. No conditional context sampler is assumed. -/
theorem context_joint_tvDist_eq_marginal
    {Seed Context Output : Type} [Fintype Seed] [Fintype Context] [Fintype Output]
    (view : ProbComp (Seed × Context)) (left right : Seed → ProbComp Output) :
    tvDist (SeededProductTV.joint view (fun pair ↦ left pair.1))
        (SeededProductTV.joint view (fun pair ↦ right pair.1)) =
      tvDist (SeededProductTV.joint (Prod.fst <$> view) left)
        (SeededProductTV.joint (Prod.fst <$> view) right) := by
  classical
  rw [SeededProductTV.tvDist_joint_eq_average, SeededProductTV.tvDist_joint_eq_average]
  simp only [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro seed _
  rw [← Finset.sum_mul, probOutput_fst_map_eq_sum,
    ENNReal.toReal_sum (fun _ _ ↦ probOutput_ne_top)]

variable {Q dimension samples : ℕ} [NeZero Q] (params : Parameters Q)
  {Context : Type}

/-- Retain the complete correlated view beside the encryption hash core. -/
theorem hashCore_context_masking [Fintype Context]
    (keySampler : ProbComp (Table Q dimension samples × Context))
    (hmarginal : 𝒟[Prod.fst <$> keySampler] = 𝒟[$ᵗ Table Q dimension samples]) :
    tvDist
        (SeededProductTV.joint keySampler fun view ↦
          hashCore view.1 <$> ($ᵗ Coins samples ((dimension + 1) * params.levels)))
        (SeededProductTV.joint keySampler fun _ ↦
          ($ᵗ Core Q dimension ((dimension + 1) * params.levels))) ≤
      ((dimension + 1) * params.levels) *
        (Real.sqrt ((Q : ℝ) ^ (dimension + 1) / (2 : ℝ) ^ samples) / 2) := by
  rw [context_joint_tvDist_eq_marginal keySampler
    (fun table ↦ hashCore table <$> ($ᵗ Coins samples ((dimension + 1) * params.levels)))
    (fun _ : Table Q dimension samples ↦ ($ᵗ Core Q dimension ((dimension + 1) * params.levels)))]
  have h := hashCore_joint_masking (Q := Q) (dimension := dimension) (samples := samples)
    (columns := (dimension + 1) * params.levels)
  have hleft : 𝒟[SeededProductTV.joint (Prod.fst <$> keySampler) (fun table ↦
      hashCore table <$> ($ᵗ Coins samples ((dimension + 1) * params.levels)))] =
      𝒟[SeededProductTV.joint ($ᵗ Table Q dimension samples) (fun table ↦
        hashCore table <$> ($ᵗ Coins samples ((dimension + 1) * params.levels)))] := by
    simp only [SeededProductTV.joint, evalDist_bind, hmarginal]
  have hright : 𝒟[SeededProductTV.joint (Prod.fst <$> keySampler) (fun _ ↦
      ($ᵗ Core Q dimension ((dimension + 1) * params.levels)))] =
      𝒟[SeededProductTV.joint ($ᵗ Table Q dimension samples) (fun _ ↦
        ($ᵗ Core Q dimension ((dimension + 1) * params.levels)))] := by
    simp only [SeededProductTV.joint, evalDist_bind, hmarginal]
  rw [tvDist, hleft, hright]
  simpa only [tvDist, SeededProductTV.joint, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind,
    Nat.cast_mul, Nat.cast_add, Nat.cast_one] using h

def correlatedHashGame
    (keySampler : ProbComp (Table Q dimension samples × Context))
    (adversary : Adversary (dimension := dimension) (samples := samples) params Context) : ProbComp Bool := do
  let view ← keySampler
  let coins ← $ᵗ Coins samples ((dimension + 1) * params.levels)
  maskingPostprocess params adversary view.2 (view.1, hashCore view.1 coins)

def correlatedIdealGame
    (keySampler : ProbComp (Table Q dimension samples × Context))
    (adversary : Adversary (dimension := dimension) (samples := samples) params Context) : ProbComp Bool := do
  let view ← keySampler
  let core ← $ᵗ Core Q dimension ((dimension + 1) * params.levels)
  maskingPostprocess params adversary view.2 (view.1, core)

/-- This is the actual stored-ciphertext encryption game, including adaptive
message choice after the table and its correlated controls are both visible. -/
theorem game_probOutput_eq_correlatedHashGame
    (keySampler : ProbComp (Table Q dimension samples × Context))
    (adversary : Adversary (dimension := dimension) (samples := samples) params Context) (result : Bool) :
    Pr[= result | game params keySampler adversary] =
      Pr[= result | correlatedHashGame params keySampler adversary] := by
  unfold game correlatedHashGame
  refine probOutput_bind_congr' keySampler result fun view ↦ ?_
  let preGame : ProbComp (Bool × (Bool × Bool × adversary.State)) := do
    let bit ← $ᵗ Bool
    let messages ← adversary.chooseMessages (storeTable view.1, view.2)
    pure (bit, messages)
  simpa [preGame, encrypt, maskingPostprocess, encryptStored_eq_ciphertextFromCore,
    monad_norm] using
    (probOutput_bind_bind_swap preGame
      ($ᵗ Coins samples ((dimension + 1) * params.levels))
      (fun pre coins ↦ do
        let guess ← adversary.distinguish pre.2.2.2
          (ciphertextFromCore params (hashCore view.1 coins)
            (if pre.1 then pre.2.1 else pre.2.2.1))
        pure (pre.1 == guess)) result)

theorem correlatedIdealGame_probOutput_true
    (keySampler : ProbComp (Table Q dimension samples × Context))
    (adversary : Adversary (dimension := dimension) (samples := samples) params Context) :
    Pr[= true | correlatedIdealGame params keySampler adversary] = 1 / 2 := by
  unfold correlatedIdealGame
  rw [probOutput_bind_eq_tsum]
  simp_rw [ideal_fixed_view_probOutput_true]
  rw [ENNReal.tsum_mul_right, tsum_probOutput_eq_one' (by simp), one_mul]

theorem correlatedHashGame_tvDist_idealGame_le [Fintype Context]
    (keySampler : ProbComp (Table Q dimension samples × Context))
    (hmarginal : 𝒟[Prod.fst <$> keySampler] = 𝒟[$ᵗ Table Q dimension samples])
    (adversary : Adversary (dimension := dimension) (samples := samples) params Context) :
    tvDist (correlatedHashGame params keySampler adversary)
        (correlatedIdealGame params keySampler adversary) ≤
      ((dimension + 1) * params.levels) *
        (Real.sqrt ((Q : ℝ) ^ (dimension + 1) / (2 : ℝ) ^ samples) / 2) := by
  let process := fun sample : (Table Q dimension samples × Context) ×
      Core Q dimension ((dimension + 1) * params.levels) ↦
    maskingPostprocess params adversary sample.1.2 (sample.1.1, sample.2)
  have h := tvDist_bind_right_le process
    (SeededProductTV.joint keySampler fun view ↦
      hashCore view.1 <$> ($ᵗ Coins samples ((dimension + 1) * params.levels)))
    (SeededProductTV.joint keySampler fun _ ↦
      ($ᵗ Core Q dimension ((dimension + 1) * params.levels)))
  simpa only [correlatedHashGame, correlatedIdealGame, SeededProductTV.joint,
    process, map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] using
      h.trans (hashCore_context_masking params keySampler hmarginal)

/-- Uniformity of the table MARGINAL suffices; the public context can be any
finite correlated object. This does not follow from computational table
pseudorandomness alone, and does not discharge the real joint-mode hop. -/
theorem game_abs_advantage_le_of_uniform_table_marginal [Fintype Context]
    (keySampler : ProbComp (Table Q dimension samples × Context))
    (hmarginal : 𝒟[Prod.fst <$> keySampler] = 𝒟[$ᵗ Table Q dimension samples])
    (adversary : Adversary (dimension := dimension) (samples := samples) params Context) :
    |Pr[= true | game params keySampler adversary].toReal - 1 / 2| ≤
      ((dimension + 1) * params.levels) *
        (Real.sqrt ((Q : ℝ) ^ (dimension + 1) / (2 : ℝ) ^ samples) / 2) := by
  rw [game_probOutput_eq_correlatedHashGame]
  have h := (abs_probOutput_toReal_sub_le_tvDist
    (correlatedHashGame params keySampler adversary)
    (correlatedIdealGame params keySampler adversary)).trans
      (correlatedHashGame_tvDist_idealGame_le params keySampler hmarginal adversary)
  simpa only [correlatedIdealGame_probOutput_true, ENNReal.toReal_div,
    ENNReal.toReal_one, ENNReal.toReal_ofNat] using h

/-- A candidate dual-mode comparison can retain any correlated context in
its uniform-table branch. Its real-to-ideal gap is still an explicit obligation. -/
theorem game_abs_advantage_le_joint_mode_gap [Fintype Context]
    (realSampler idealSampler : ProbComp (Table Q dimension samples × Context))
    (hmarginal : 𝒟[Prod.fst <$> idealSampler] = 𝒟[$ᵗ Table Q dimension samples])
    (adversary : Adversary (dimension := dimension) (samples := samples) params Context) :
    |Pr[= true | game params realSampler adversary].toReal - 1 / 2| ≤
      |Pr[= true | game params realSampler adversary].toReal -
        Pr[= true | game params idealSampler adversary].toReal| +
      ((dimension + 1) * params.levels) *
        (Real.sqrt ((Q : ℝ) ^ (dimension + 1) / (2 : ℝ) ^ samples) / 2) :=
  (abs_sub_le _ (Pr[= true | game params idealSampler adversary].toReal) (1 / 2 : ℝ)).trans
    (add_le_add le_rfl
      (game_abs_advantage_le_of_uniform_table_marginal params idealSampler hmarginal adversary))

/-- The complete actual IND-CPA continuation on one public view. -/
def observe (adversary : Adversary (dimension := dimension) (samples := samples) params Context)
    (view : Table Q dimension samples × Context) : ProbComp Bool := do
  let bit ← $ᵗ Bool
  let messages ← adversary.chooseMessages (storeTable view.1, view.2)
  let ciphertext ← encrypt params view.1 (if bit then messages.1 else messages.2.1)
  let guess ← adversary.distinguish messages.2.2 ciphertext
  pure (bit == guess)

noncomputable section

/-- A randomized, possibly nonlinear source simulator has a direct ordinary-LWE
game bound as soon as its uniform-source TABLE MARGINAL is uniform. There is
no invertibility or independence premise on its full control output. Matching
the real construction and proving efficiency/correctness remain obligations. -/
theorem ordinary_source_simulator_game_abs_advantage_le [Fintype Context]
    (sourceDimension sourceSamples : ℕ) (errorSampler : ProbComp (ZMod Q))
    (simulator : BatchTranscript (ZMod Q) sourceDimension sourceSamples →
      ProbComp (Table Q dimension samples × Context))
    (adversary : Adversary (dimension := dimension) (samples := samples) params Context)
    (hmarginal : 𝒟[Prod.fst <$> (LearningWithErrors.uniformDistr
        (zmodBatchProblem sourceDimension sourceSamples Q errorSampler) >>= simulator)] =
      𝒟[$ᵗ Table Q dimension samples]) :
    |Pr[= true | game params (LearningWithErrors.distr
          (zmodBatchProblem sourceDimension sourceSamples Q errorSampler) >>= simulator) adversary].toReal -
        1 / 2| ≤
      LearningWithErrors.advantage (zmodBatchProblem sourceDimension sourceSamples Q errorSampler)
        (fun raw ↦ simulator raw >>= observe params adversary) +
      ((dimension + 1) * params.levels) *
        (Real.sqrt ((Q : ℝ) ^ (dimension + 1) / (2 : ℝ) ^ samples) / 2) := by
  let problem := zmodBatchProblem sourceDimension sourceSamples Q errorSampler
  let reduction := fun raw ↦ simulator raw >>= observe params adversary
  have hreal : LearningWithErrors.game0 problem reduction =
      game params (LearningWithErrors.distr problem >>= simulator) adversary := by
    simp only [LearningWithErrors.game0, reduction, game, bind_assoc]
    rfl
  have huniform : LearningWithErrors.game1 problem reduction =
      game params (LearningWithErrors.uniformDistr problem >>= simulator) adversary := by
    simp only [LearningWithErrors.game1, reduction, game, bind_assoc]
    rfl
  have hsource := advantage_eq_boolDistAdvantage problem reduction
  rw [hreal, huniform] at hsource
  unfold ProbComp.boolDistAdvantage at hsource
  have h := game_abs_advantage_le_joint_mode_gap params
    (LearningWithErrors.distr problem >>= simulator)
    (LearningWithErrors.uniformDistr problem >>= simulator) hmarginal adversary
  simpa only [← hsource] using h

end

end FormalProof4FHE.LWE.GSWCorrelatedMasking
