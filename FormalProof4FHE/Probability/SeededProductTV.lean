/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.FiniteProduct
import FormalProof4FHE.Probability.LeftoverHash

/-!
# Independent outputs under one retained public seed

The seed is sampled once, not independently for every output. Retaining it makes
the joint TV distance exactly the average conditional distance. Consequently,
reusing a two-universal hash seed for independent inputs costs at most one
leftover-hash error per output. No computational assumption is involved.
-/

open OracleComp
open scoped BigOperators

namespace FormalProof4FHE.SeededProductTV

/-- Sample a seed once and retain it beside a conditional output. -/
def joint {Seed Output : Type} (seedSampler : ProbComp Seed)
    (outputSampler : Seed → ProbComp Output) : ProbComp (Seed × Output) := do
  let seed ← seedSampler
  let output ← outputSampler seed
  pure (seed, output)

/-- Keeping the seed prevents cancellation between different conditional laws. -/
theorem tvDist_joint_eq_average {Seed Output : Type} [Fintype Seed] [Fintype Output]
    (seedSampler : ProbComp Seed) (left right : Seed → ProbComp Output) :
    tvDist (joint seedSampler left) (joint seedSampler right) =
      ∑ seed, Pr[= seed | seedSampler].toReal * tvDist (left seed) (right seed) := by
  classical
  letI : DecidableEq Seed := Classical.decEq Seed
  letI : DecidableEq Output := Classical.decEq Output
  have hprob (sampler : Seed → ProbComp Output) (seed : Seed) (output : Output) :
      Pr[= (seed, output) | joint seedSampler sampler] =
        Pr[= seed | seedSampler] * Pr[= output | sampler seed] := by
    simp [joint, probOutput_bind_eq_sum_fintype]
  rw [LeftoverHash.tvDist_eq_half_sum_abs]
  simp_rw [Fintype.sum_prod_type, hprob, ENNReal.toReal_mul, ← mul_sub,
    abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
  simp_rw [← Finset.mul_sum]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro seed _
  rw [LeftoverHash.tvDist_eq_half_sum_abs]
  ring

/-- Conditional independent products share the original seed, with a linear loss. -/
theorem tvDist_joint_product_le {Seed Output : Type} [Fintype Seed] [Fintype Output]
    (seedSampler : ProbComp Seed) (left right : Seed → ProbComp Output) (count : ℕ) :
    tvDist
        (joint seedSampler fun seed ↦ Fin.mOfFn count fun _ ↦ left seed)
        (joint seedSampler fun seed ↦ Fin.mOfFn count fun _ ↦ right seed) ≤
      count * tvDist (joint seedSampler left) (joint seedSampler right) := by
  rw [tvDist_joint_eq_average, tvDist_joint_eq_average]
  calc
    _ ≤ ∑ seed, Pr[= seed | seedSampler].toReal *
        ((count : ℝ) * tvDist (left seed) (right seed)) := by
      apply Finset.sum_le_sum
      intro seed _
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      simpa using FiniteProduct.tvDist_fin_mOfFn_le_sum count
        (fun _ ↦ left seed) (fun _ ↦ right seed)
    _ = _ := by simp_rw [← mul_assoc, mul_comm _ (count : ℝ), mul_assoc]; rw [Finset.mul_sum]

/-- Several independent inputs hashed under one public seed. -/
def hashedColumns {Seed Input Output : Type}
    [SampleableType Seed] [SampleableType Input]
    (hash : Seed → Input → Output) (count : ℕ) : ProbComp (Seed × (Fin count → Output)) :=
  joint ($ᵗ Seed) fun seed ↦ Fin.mOfFn count fun _ ↦ hash seed <$> ($ᵗ Input)

/-- The matching ideal keeps that seed and makes all output coordinates independent uniform. -/
def idealColumns {Seed Output : Type}
    [SampleableType Seed] [SampleableType Output] (count : ℕ) :
    ProbComp (Seed × (Fin count → Output)) :=
  joint ($ᵗ Seed) fun _ ↦ Fin.mOfFn count fun _ ↦ ($ᵗ Output)

/-- The independent coordinate samplers equal one uniform input tape, hashed coordinatewise. -/
theorem evalDist_hashedColumns_eq_uniform_tape {Seed Input Output : Type}
    [Fintype Input] [SampleableType Seed] [SampleableType Input]
    (hash : Seed → Input → Output) (count : ℕ) :
    𝒟[hashedColumns hash count] =
      𝒟[do
        let seed ← $ᵗ Seed
        let inputs ← $ᵗ (Fin count → Input)
        pure (seed, fun column ↦ hash seed (inputs column))] := by
  unfold hashedColumns joint
  simp only [evalDist_bind]
  congr 1
  funext seed
  rw [← FiniteProduct.map_fin_mOfFn_const count ($ᵗ Input) (hash seed)]
  simp only [evalDist_map]
  rw [show 𝒟[Fin.mOfFn count fun _ ↦ ($ᵗ Input)] = 𝒟[$ᵗ (Fin count → Input)] from
    FiniteProduct.evalDist_sampleIID_uniform count]
  simp [monad_norm]

/-- All ideal output coordinates can be drawn as one uniform output tape. -/
theorem evalDist_idealColumns_eq_uniform_tape {Seed Output : Type}
    [Fintype Output] [SampleableType Seed] [SampleableType Output] (count : ℕ) :
    𝒟[idealColumns (Seed := Seed) (Output := Output) count] =
      𝒟[joint ($ᵗ Seed) fun _ ↦ ($ᵗ (Fin count → Output))] := by
  unfold idealColumns joint
  simp only [evalDist_bind]
  rw [show 𝒟[Fin.mOfFn count fun _ ↦ ($ᵗ Output)] = 𝒟[$ᵗ (Fin count → Output)] from
    FiniteProduct.evalDist_sampleIID_uniform count]

/-- Uniform seed/output pairs equal sequential independent sampling. -/
theorem evalDist_ideal_eq_joint {Seed Output : Type}
    [Fintype Seed] [Fintype Output] [SampleableType Seed] [SampleableType Output] :
    𝒟[LeftoverHash.ideal (Seed := Seed) (Output := Output)] =
      𝒟[joint ($ᵗ Seed) fun _ ↦ ($ᵗ Output)] := by
  exact (FiniteProduct.evalDist_independent_uniform_product
    (first := Seed) (second := Output)).symm

/-- Reusing one two-universal seed for independent inputs costs at most `count` errors. -/
theorem leftover_hash_columns {Seed Input Output : Type}
    [Fintype Seed] [Fintype Input] [Fintype Output]
    [SampleableType Seed] [SampleableType Input] [SampleableType Output]
    [DecidableEq Output] (hash : Seed → Input → Output)
    (huniversal : LeftoverHash.IsTwoUniversal Seed Input Output hash) (count : ℕ) :
    tvDist (hashedColumns hash count) (idealColumns (Seed := Seed) (Output := Output) count) ≤
      count * (Real.sqrt (Fintype.card Output / Fintype.card Input) / 2) := by
  have hsingle :
      tvDist (joint ($ᵗ Seed) fun seed ↦ hash seed <$> ($ᵗ Input))
          (joint ($ᵗ Seed) fun _ ↦ ($ᵗ Output)) ≤
        Real.sqrt (Fintype.card Output / Fintype.card Input) / 2 := by
    have h := LeftoverHash.leftover_hash_lemma hash huniversal
    have hideal := evalDist_ideal_eq_joint (Seed := Seed) (Output := Output)
    simpa only [tvDist, hideal, LeftoverHash.hashed, joint, map_eq_bind_pure_comp,
      Function.comp_def, bind_assoc, pure_bind] using h
  exact (tvDist_joint_product_le ($ᵗ Seed) (fun seed ↦ hash seed <$> ($ᵗ Input))
    (fun _ ↦ ($ᵗ Output)) count).trans
      (mul_le_mul_of_nonneg_left hsingle (Nat.cast_nonneg count))

/-- Joint laws can be processed after seeing their retained seed, without an extra loss. -/
theorem leftover_hash_columns_postprocess {Seed Input Output Result : Type}
    [Fintype Seed] [Fintype Input] [Fintype Output]
    [SampleableType Seed] [SampleableType Input] [SampleableType Output]
    [DecidableEq Output] (hash : Seed → Input → Output)
    (huniversal : LeftoverHash.IsTwoUniversal Seed Input Output hash) (count : ℕ)
    (process : Seed × (Fin count → Output) → ProbComp Result) :
    tvDist (hashedColumns hash count >>= process)
        (idealColumns (Seed := Seed) (Output := Output) count >>= process) ≤
      count * (Real.sqrt (Fintype.card Output / Fintype.card Input) / 2) :=
  (tvDist_bind_right_le process _ _).trans (leftover_hash_columns hash huniversal count)

end FormalProof4FHE.SeededProductTV
