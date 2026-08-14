/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.LeftoverHash
import FormalProof4FHE.RLWE.BFVStandardAssumptionCircularSecurity

/-!
# Corrected BFV circular security and its statistical boundary

This file formalizes the new statistical part of
`sketch/bfv_circular_security_corrected.tex`.  The exact adjacent normal form, HNF--knapsack
normalization, extension encoding, singular-tail loss, and corrected computational composition
are imported from `BFVStandardAssumptionCircularSecurity`.

The main new result is the high-collision-entropy alternative.  The fixed-HNF affine family is
proved two-universal over every finite field.  A collision-form strong leftover-hash theorem then
bounds each branch by uniform, and the triangle inequality bounds the real and zero branches.
The final support-cardinality theorem records why this statistical route does not cover stock
narrow-error BFV parameters.
-/

open OracleComp
open scoped BigOperators

namespace FormalProof4FHE.RLWE.BFVCircularSecurityCorrected

noncomputable section

/-! ## The fixed-HNF universal family -/

/-- The fixed-HNF affine hash used after adjacent differencing.  The repository's BFV convention
uses a positive mask coefficient; replacing the seed by its negative gives the manuscript's
`-a*x₀+x_E` convention exactly. -/
def hnfHash {F Row : Type} [Ring F]
    (mask : Row → F) (source : F × (Row → F)) : Row → F :=
  fun row ↦ mask row * source.1 + source.2 row

/-- Two different sources with the same first coordinate never collide under the HNF hash. -/
theorem hnfHash_ne_of_fst_eq
    {F Row : Type} [Field F]
    (left right : F × (Row → F)) (hDifferent : left ≠ right)
    (hFirst : left.1 = right.1) (mask : Row → F) :
    hnfHash mask left ≠ hnfHash mask right := by
  intro hHash
  apply hDifferent
  apply Prod.ext hFirst
  funext row
  have hCoordinate := congrFun hHash row
  simp only [hnfHash] at hCoordinate
  rw [hFirst] at hCoordinate
  exact add_left_cancel hCoordinate

/-- If the first source coordinates differ, at most one mask can make the hashes collide. -/
theorem hnfHash_collision_seed_unique
    {F Row : Type} [Field F]
    (left right : F × (Row → F)) (hFirst : left.1 ≠ right.1)
    {firstMask secondMask : Row → F}
    (hFirstMask : hnfHash firstMask left = hnfHash firstMask right)
    (hSecondMask : hnfHash secondMask left = hnfHash secondMask right) :
    firstMask = secondMask := by
  funext row
  have hOne := congrFun hFirstMask row
  have hTwo := congrFun hSecondMask row
  simp only [hnfHash] at hOne hTwo
  have hProduct :
      (firstMask row - secondMask row) * (left.1 - right.1) = 0 := by
    linear_combination hOne - hTwo
  rcases mul_eq_zero.mp hProduct with hMask | hSource
  · exact sub_eq_zero.mp hMask
  · exact (hFirst (sub_eq_zero.mp hSource)).elim

/-- The HNF affine family is two-universal.  If the distinguished source coordinate differs,
there is exactly at most one colliding seed; if it agrees, a collision is impossible. -/
theorem hnfHash_isTwoUniversal
    (F Row : Type) [Field F] [Fintype F] [Fintype Row]
    [DecidableEq F] [DecidableEq Row] :
    FormalProof4FHE.LeftoverHash.IsTwoUniversal
      (Row → F) (F × (Row → F)) (Row → F)
      (hnfHash (F := F) (Row := Row)) := by
  classical
  intro left right hDifferent
  by_cases hFirst : left.1 = right.1
  · have hEmpty :
        Finset.univ.filter (fun mask : Row → F ↦ hnfHash mask left = hnfHash mask right) =
          ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro mask _
      exact hnfHash_ne_of_fst_eq left right hDifferent hFirst mask
    rw [hEmpty]
    simp
  · have hAtMostOne :
        (Finset.univ.filter
          (fun mask : Row → F ↦ hnfHash mask left = hnfHash mask right)).card ≤ 1 :=
      Finset.card_le_one.mpr fun firstMask hFirstMem secondMask hSecondMem ↦ by
        exact hnfHash_collision_seed_unique left right hFirst
          (Finset.mem_filter.mp hFirstMem).2 (Finset.mem_filter.mp hSecondMem).2
    calc
      (Finset.univ.filter
          (fun mask : Row → F ↦ hnfHash mask left = hnfHash mask right)).card *
            Fintype.card (Row → F)
          ≤ 1 * Fintype.card (Row → F) :=
            Nat.mul_le_mul_right _ hAtMostOne
      _ = Fintype.card (Row → F) := one_mul _

/-! ## Collision-form strong leftover hashing -/

/-- Joint public seed and hash output for an arbitrary finite source distribution. -/
def hashedSource {Seed Input Output : Type} [SampleableType Seed]
    (source : ProbComp Input) (hash : Seed → Input → Output) :
    ProbComp (Seed × Output) := do
  let seed ← $ᵗ Seed
  let input ← source
  return (seed, hash seed input)

/-- Point mass of a public-seed hash applied to an arbitrary source. -/
theorem probOutput_hashedSource
    {Seed Input Output : Type}
    [Fintype Seed] [SampleableType Seed] [Fintype Input]
    [DecidableEq Seed] [DecidableEq Output]
    (source : ProbComp Input) (hash : Seed → Input → Output)
    (seed : Seed) (output : Output) :
    Pr[= (seed, output) | hashedSource source hash] =
      (Fintype.card Seed : ENNReal)⁻¹ *
        ∑ input, Pr[= input | source] *
          if hash seed input = output then 1 else 0 := by
  classical
  simp [hashedSource, probOutput_bind_eq_sum_fintype,
    probOutput_map_eq_sum_fintype_ite]
  rw [Finset.sum_eq_single seed]
  · simp [eq_comm]
  · intro other _ hOther
    simp [hOther.symm]
  · simp

/-- Real-valued form of `probOutput_hashedSource`. -/
theorem probOutput_hashedSource_toReal
    {Seed Input Output : Type}
    [Fintype Seed] [SampleableType Seed] [Fintype Input]
    [DecidableEq Seed] [DecidableEq Output]
    (source : ProbComp Input) (hash : Seed → Input → Output)
    (seed : Seed) (output : Output) :
    Pr[= (seed, output) | hashedSource source hash].toReal =
      (Fintype.card Seed : ℝ)⁻¹ *
        ∑ input, Pr[= input | source].toReal *
          if hash seed input = output then 1 else 0 := by
  rw [probOutput_hashedSource]
  rw [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    ENNReal.toReal_sum]
  · congr 1
    apply Finset.sum_congr rfl
    intro input _
    rw [ENNReal.toReal_mul]
    by_cases hOutput : hash seed input = output <;> simp [hOutput]
  · intro input _
    apply ENNReal.mul_ne_top probOutput_ne_top
    by_cases hOutput : hash seed input = output <;> simp [hOutput]

/-- Weighted hash-bucket squares count weighted pairs of colliding inputs. -/
theorem sum_weighted_hash_bucket_sq_eq
    {Seed Input Output : Type}
    [Fintype Seed] [Fintype Input] [Fintype Output]
    [DecidableEq Seed] [DecidableEq Output]
    (mass : Input → ℝ) (hash : Seed → Input → Output) :
    (∑ seed, ∑ output,
        (∑ input, mass input *
          if hash seed input = output then 1 else 0) ^ 2) =
      ∑ left, ∑ right,
        mass left * mass right *
          ((Finset.univ.filter fun seed : Seed ↦
            hash seed left = hash seed right).card : ℝ) := by
  classical
  have hSquare (seed : Seed) (output : Output) :
      (∑ input, mass input *
          if hash seed input = output then 1 else 0) ^ 2 =
        ∑ left, ∑ right,
          mass left * mass right *
            (if hash seed left = output ∧ hash seed right = output then 1 else 0) := by
    rw [pow_two, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro left _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro right _
    by_cases hLeft : hash seed left = output <;>
      by_cases hRight : hash seed right = output <;>
      simp [hLeft, hRight]
  simp_rw [hSquare]
  have hReorder :
      (∑ seed, ∑ output, ∑ left, ∑ right,
          mass left * mass right *
            (if hash seed left = output ∧ hash seed right = output then 1 else 0)) =
        ∑ left, ∑ right, ∑ seed, ∑ output,
          mass left * mass right *
            (if hash seed left = output ∧ hash seed right = output then 1 else 0) := by
    calc
      (∑ seed, ∑ output, ∑ left, ∑ right,
          mass left * mass right *
            (if hash seed left = output ∧ hash seed right = output then 1 else 0)) =
          ∑ seed, ∑ left, ∑ output, ∑ right,
            mass left * mass right *
              (if hash seed left = output ∧ hash seed right = output then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro seed _
            exact Finset.sum_comm
      _ = ∑ left, ∑ seed, ∑ output, ∑ right,
            mass left * mass right *
              (if hash seed left = output ∧ hash seed right = output then 1 else 0) :=
            Finset.sum_comm
      _ = ∑ left, ∑ seed, ∑ right, ∑ output,
            mass left * mass right *
              (if hash seed left = output ∧ hash seed right = output then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro left _
            apply Finset.sum_congr rfl
            intro seed _
            exact Finset.sum_comm
      _ = ∑ left, ∑ right, ∑ seed, ∑ output,
            mass left * mass right *
              (if hash seed left = output ∧ hash seed right = output then 1 else 0) := by
            apply Finset.sum_congr rfl
            intro left _
            exact Finset.sum_comm
  rw [hReorder]
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  calc
    (∑ seed, ∑ output,
        mass left * mass right *
          (if hash seed left = output ∧ hash seed right = output then (1 : ℝ) else 0)) =
        mass left * mass right *
          (∑ seed, ∑ output,
            if hash seed left = output ∧ hash seed right = output then (1 : ℝ) else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro seed _
          rw [Finset.mul_sum]
    _ = mass left * mass right *
        (∑ seed, if hash seed left = hash seed right then (1 : ℝ) else 0) := by
          congr 1
          apply Finset.sum_congr rfl
          intro seed _
          by_cases hCollision : hash seed left = hash seed right
          · rw [hCollision]
            simp
          · have hNoOutput : ∀ output,
                ¬ (hash seed left = output ∧ hash seed right = output) := by
              intro output hBoth
              exact hCollision (hBoth.1.trans hBoth.2.symm)
            simp [hCollision, hNoOutput]
    _ = mass left * mass right *
        ((Finset.univ.filter fun seed : Seed ↦
          hash seed left = hash seed right).card : ℝ) := by
          congr 1
          simp

/-- Two-universality as the real-valued pointwise collision-count bound used for weighted
sources.  The extra diagonal `S/O` is harmless and lets the complete double sum factor. -/
theorem collisionSeedCard_real_le_diagonal_add_uniform
    {Seed Input Output : Type}
    [Fintype Seed] [Fintype Output] [Nonempty Output]
    [DecidableEq Input] [DecidableEq Output]
    (hash : Seed → Input → Output)
    (hUniversal : FormalProof4FHE.LeftoverHash.IsTwoUniversal
      Seed Input Output hash)
    (left right : Input) :
    ((Finset.univ.filter fun seed : Seed ↦
        hash seed left = hash seed right).card : ℝ) ≤
      (if left = right then (Fintype.card Seed : ℝ) else 0) +
        (Fintype.card Seed : ℝ) / Fintype.card Output := by
  classical
  have hOutput : (0 : ℝ) < Fintype.card Output := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Output)
  by_cases hEqual : left = right
  · subst right
    simp only [eq_self, ↓reduceIte, Finset.filter_true, Finset.card_univ]
    have hNonnegative :
        0 ≤ (Fintype.card Seed : ℝ) / Fintype.card Output := by positivity
    exact le_add_of_nonneg_right (a := (Fintype.card Seed : ℝ)) hNonnegative
  · rw [if_neg hEqual, zero_add]
    apply (le_div_iff₀ hOutput).2
    have hNatural := hUniversal left right hEqual
    exact_mod_cast hNatural

/-- Weighted collision count of a two-universal family. -/
theorem weighted_collision_count_le
    {Seed Input Output : Type}
    [Fintype Seed] [Fintype Input] [Fintype Output]
    [Nonempty Output] [DecidableEq Input] [DecidableEq Output]
    (mass : Input → ℝ) (hMassNonnegative : ∀ input, 0 ≤ mass input)
    (hash : Seed → Input → Output)
    (hUniversal : FormalProof4FHE.LeftoverHash.IsTwoUniversal
      Seed Input Output hash) :
    (∑ left, ∑ right,
        mass left * mass right *
          ((Finset.univ.filter fun seed : Seed ↦
            hash seed left = hash seed right).card : ℝ)) ≤
      (Fintype.card Seed : ℝ) * ∑ input, mass input ^ 2 +
        ((Fintype.card Seed : ℝ) / Fintype.card Output) *
          (∑ input, mass input) ^ 2 := by
  classical
  calc
    (∑ left, ∑ right,
        mass left * mass right *
          ((Finset.univ.filter fun seed : Seed ↦
            hash seed left = hash seed right).card : ℝ)) ≤
        ∑ left, ∑ right,
          mass left * mass right *
            ((if left = right then (Fintype.card Seed : ℝ) else 0) +
              (Fintype.card Seed : ℝ) / Fintype.card Output) := by
          gcongr with left right
          · exact mul_nonneg (hMassNonnegative left) (hMassNonnegative right)
          · exact collisionSeedCard_real_le_diagonal_add_uniform
              hash hUniversal left right
    _ = (Fintype.card Seed : ℝ) * ∑ input, mass input ^ 2 +
        ((Fintype.card Seed : ℝ) / Fintype.card Output) *
          (∑ input, mass input) ^ 2 := by
      simp_rw [mul_add]
      rw [show
        (∑ left, ∑ right,
            (mass left * mass right *
                (if left = right then (Fintype.card Seed : ℝ) else 0) +
              mass left * mass right *
                ((Fintype.card Seed : ℝ) / Fintype.card Output))) =
          (∑ left, ∑ right,
              mass left * mass right *
                (if left = right then (Fintype.card Seed : ℝ) else 0)) +
            ∑ left, ∑ right,
              mass left * mass right *
                ((Fintype.card Seed : ℝ) / Fintype.card Output) by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro left _
          rw [Finset.sum_add_distrib]]
      congr 1
      · calc
          (∑ left, ∑ right,
              mass left * mass right *
                if left = right then (Fintype.card Seed : ℝ) else 0) =
              ∑ left, mass left ^ 2 * (Fintype.card Seed : ℝ) := by
                apply Finset.sum_congr rfl
                intro left _
                rw [Finset.sum_eq_single left]
                · simp [pow_two]
                · intro right _ hRight
                  simp [hRight.symm]
                · simp
          _ = (Fintype.card Seed : ℝ) * ∑ input, mass input ^ 2 := by
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro input _
                ring
      · calc
          (∑ left, ∑ right,
              mass left * mass right *
                ((Fintype.card Seed : ℝ) / Fintype.card Output)) =
              ((Fintype.card Seed : ℝ) / Fintype.card Output) *
                ∑ left, ∑ right, mass left * mass right := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro left _
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro right _
                  ring
          _ = ((Fintype.card Seed : ℝ) / Fintype.card Output) *
              (∑ input, mass input) ^ 2 := by
                congr 1
                rw [pow_two, Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro left _
                rw [Finset.mul_sum]

/-- Real point masses of a total finite computation sum to one. -/
theorem sum_probOutput_toReal_eq_one
    {Input : Type} [Fintype Input] (source : ProbComp Input) :
    ∑ input, Pr[= input | source].toReal = 1 := by
  rw [← ENNReal.toReal_sum (fun input _ ↦ probOutput_ne_top),
    sum_probOutput_eq_one (by simp), ENNReal.toReal_one]

/-- Collision probability of an arbitrary-source universal hash. -/
theorem collisionProbability_hashedSource_le
    {Seed Input Output : Type}
    [Fintype Seed] [Nonempty Seed] [SampleableType Seed]
    [Fintype Input] [Fintype Output] [Nonempty Output]
    [DecidableEq Seed] [DecidableEq Input] [DecidableEq Output]
    (source : ProbComp Input) (hash : Seed → Input → Output)
    (hUniversal : FormalProof4FHE.LeftoverHash.IsTwoUniversal
      Seed Input Output hash) :
    FormalProof4FHE.LeftoverHash.collisionProbability
        (hashedSource source hash) ≤
      FormalProof4FHE.LeftoverHash.collisionProbability source /
          Fintype.card Seed +
        1 / ((Fintype.card Seed : ℝ) * Fintype.card Output) := by
  classical
  let S : ℝ := Fintype.card Seed
  let O : ℝ := Fintype.card Output
  let mass : Input → ℝ := fun input ↦ Pr[= input | source].toReal
  have hS : 0 < S := by
    dsimp [S]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Seed)
  have hO : 0 < O := by
    dsimp [O]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Output)
  have hMassNonnegative : ∀ input, 0 ≤ mass input :=
    fun _ ↦ ENNReal.toReal_nonneg
  have hMassSum : ∑ input, mass input = 1 := by
    exact sum_probOutput_toReal_eq_one source
  have hJointCollision :
      FormalProof4FHE.LeftoverHash.collisionProbability
          (hashedSource source hash) =
        (S⁻¹) ^ 2 * ∑ left, ∑ right,
          mass left * mass right *
            ((Finset.univ.filter fun seed : Seed ↦
              hash seed left = hash seed right).card : ℝ) := by
    unfold FormalProof4FHE.LeftoverHash.collisionProbability
    rw [Fintype.sum_prod_type]
    simp_rw [probOutput_hashedSource_toReal]
    calc
      (∑ seed, ∑ output,
          ((Fintype.card Seed : ℝ)⁻¹ *
            ∑ input, mass input *
              if hash seed input = output then 1 else 0) ^ 2) =
          (S⁻¹) ^ 2 * ∑ seed, ∑ output,
            (∑ input, mass input *
              if hash seed input = output then 1 else 0) ^ 2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro seed _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro output _
            dsimp [S]
            ring
      _ = (S⁻¹) ^ 2 * ∑ left, ∑ right,
          mass left * mass right *
            ((Finset.univ.filter fun seed : Seed ↦
              hash seed left = hash seed right).card : ℝ) := by
            rw [sum_weighted_hash_bucket_sq_eq mass hash]
  have hWeighted := weighted_collision_count_le
    mass hMassNonnegative hash hUniversal
  rw [hJointCollision]
  calc
    (S⁻¹) ^ 2 * ∑ left, ∑ right,
        mass left * mass right *
          ((Finset.univ.filter fun seed : Seed ↦
            hash seed left = hash seed right).card : ℝ) ≤
        (S⁻¹) ^ 2 *
          (S * ∑ input, mass input ^ 2 +
            (S / O) * (∑ input, mass input) ^ 2) := by
              exact mul_le_mul_of_nonneg_left hWeighted (sq_nonneg S⁻¹)
    _ = FormalProof4FHE.LeftoverHash.collisionProbability source /
          Fintype.card Seed +
        1 / ((Fintype.card Seed : ℝ) * Fintype.card Output) := by
      rw [hMassSum]
      change
        (S⁻¹) ^ 2 *
            (S * FormalProof4FHE.LeftoverHash.collisionProbability source +
              S / O * 1 ^ 2) =
          FormalProof4FHE.LeftoverHash.collisionProbability source / S +
            1 / (S * O)
      field_simp

/-- Strong leftover-hash lemma for an arbitrary finite source, stated in terms of its exact
collision probability. -/
theorem strong_leftover_hash_lemma_collision
    {Seed Input Output : Type}
    [Fintype Seed] [Nonempty Seed] [SampleableType Seed]
    [Fintype Input]
    [Fintype Output] [Nonempty Output] [SampleableType Output]
    [DecidableEq Seed] [DecidableEq Input] [DecidableEq Output]
    (source : ProbComp Input) (hash : Seed → Input → Output)
    (hUniversal : FormalProof4FHE.LeftoverHash.IsTwoUniversal
      Seed Input Output hash) :
    tvDist (hashedSource source hash)
        (FormalProof4FHE.LeftoverHash.ideal (Seed := Seed) (Output := Output)) ≤
      Real.sqrt ((Fintype.card Output : ℝ) *
        FormalProof4FHE.LeftoverHash.collisionProbability source) / 2 := by
  let S : ℝ := Fintype.card Seed
  let O : ℝ := Fintype.card Output
  let C : ℝ := FormalProof4FHE.LeftoverHash.collisionProbability source
  have hS : 0 < S := by
    dsimp [S]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Seed)
  have hO : 0 < O := by
    dsimp [O]
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card Output)
  have hCollisionBase := collisionProbability_hashedSource_le
    source hash hUniversal
  have hCollision :
      FormalProof4FHE.LeftoverHash.collisionProbability
          (hashedSource source hash) ≤
        (1 + O * C) / Fintype.card (Seed × Output) := by
    calc
      FormalProof4FHE.LeftoverHash.collisionProbability
          (hashedSource source hash) ≤ C / S + 1 / (S * O) := by
            simpa [C, S, O] using hCollisionBase
      _ = (1 + O * C) / (S * O) := by
            field_simp
            ring
      _ = (1 + O * C) / Fintype.card (Seed × Output) := by
            simp [S, O, Fintype.card_prod]
  simpa [FormalProof4FHE.LeftoverHash.ideal, O, C] using
    (FormalProof4FHE.LeftoverHash.tvDist_uniform_le_of_collision
      (hashedSource source hash) (O * C) hCollision)

/-- Statistical fixed-HNF bound for an arbitrary correlated source. -/
theorem hnfHash_tvDist_uniform_le
    {F Row : Type} [Field F]
    [Fintype F] [DecidableEq F]
    [Fintype Row] [DecidableEq Row]
    [SampleableType (Row → F)]
    (source : ProbComp (F × (Row → F))) :
    tvDist
        (hashedSource source (hnfHash (F := F) (Row := Row)))
        (FormalProof4FHE.LeftoverHash.ideal
          (Seed := Row → F) (Output := Row → F)) ≤
      Real.sqrt ((Fintype.card (Row → F) : ℝ) *
        FormalProof4FHE.LeftoverHash.collisionProbability source) / 2 := by
  exact strong_leftover_hash_lemma_collision source hnfHash
    (hnfHash_isTwoUniversal F Row)

/-- A bijective reparameterization preserves collision probability exactly. -/
theorem collisionProbability_map_equiv
    {Input Output : Type} [Fintype Input] [Fintype Output]
    (equiv : Input ≃ Output) (source : ProbComp Input) :
    FormalProof4FHE.LeftoverHash.collisionProbability (equiv <$> source) =
      FormalProof4FHE.LeftoverHash.collisionProbability source := by
  classical
  unfold FormalProof4FHE.LeftoverHash.collisionProbability
  rw [← equiv.sum_comp]
  apply Finset.sum_congr rfl
  intro input _
  rw [probOutput_map_injective source equiv.injective]

/-- Independently sample a pair. -/
def independentPairSampler {First Second : Type}
    (first : ProbComp First) (second : ProbComp Second) :
    ProbComp (First × Second) := do
  let left ← first
  let right ← second
  return (left, right)

/-- Point mass of an independent pair factors. -/
theorem probOutput_independentPairSampler
    {First Second : Type} [Fintype First] [Fintype Second]
    [DecidableEq First] [DecidableEq Second]
    (first : ProbComp First) (second : ProbComp Second)
    (left : First) (right : Second) :
    Pr[= (left, right) | independentPairSampler first second] =
      Pr[= left | first] * Pr[= right | second] := by
  classical
  simp [independentPairSampler, probOutput_bind_eq_sum_fintype]

/-- Collision probability is multiplicative for independent finite sources. -/
theorem collisionProbability_independentPairSampler
    {First Second : Type} [Fintype First] [Fintype Second]
    [DecidableEq First] [DecidableEq Second]
    (first : ProbComp First) (second : ProbComp Second) :
    FormalProof4FHE.LeftoverHash.collisionProbability
        (independentPairSampler first second) =
      FormalProof4FHE.LeftoverHash.collisionProbability first *
        FormalProof4FHE.LeftoverHash.collisionProbability second := by
  unfold FormalProof4FHE.LeftoverHash.collisionProbability
  rw [Fintype.sum_prod_type, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro left _
  simp_rw [probOutput_independentPairSampler, ENNReal.toReal_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro right _
  ring

/-! ## Statistical BFV branches -/

namespace Standard

export FormalProof4FHE.RLWE.BFVStandardAssumptionCircularSecurity
  (gammaSourceEquiv gammaStockTranscript gammaHNFTranscript gammaCorrelatedError
    gammaCorrelatedError_zero gammaCorrelatedError_succ adjacent_gammaStockTranscript
    gammaStockTranscript_one gammaStockTranscript_zero)

end Standard

namespace BFV

export FormalProof4FHE.RLWE.BFVQuadraticCircularSecurity
  (Batch Transcript transcriptEquiv adjacentTransform adjacentEquiv uniformSampler
    stockSampler zeroSampler transcriptEquiv_uniform_evalDist)

end BFV

/-- The HNF output space has one field coordinate per gadget row. -/
@[simp]
theorem card_batch
    (F : Type) [Fintype F] (levels : ℕ) :
    Fintype.card (BFV.Batch F levels) = Fintype.card F ^ (levels + 1) := by
  simp [BFV.Batch, FormalProof4FHE.RLWE.SquareZeroQuadraticCircular.Vector]

/-- Original independent secret/error source, reparameterized as the correlated source of branch
`gamma`. -/
def gammaSourceSampler
    {F : Type} [CommRing F]
    (levels : ℕ) (radix gamma : F)
    (secretSampler : ProbComp F)
    (errorSampler : ProbComp (BFV.Batch F levels)) :
    ProbComp (F × BFV.Batch F levels) :=
  Standard.gammaSourceEquiv levels radix gamma <$>
    independentPairSampler secretSampler errorSampler

/-- The collision probability of either correlated branch is exactly that of the original
independent secret/error variables. -/
theorem collisionProbability_gammaSourceSampler
    {F : Type} [CommRing F] [Fintype F] [DecidableEq F]
    (levels : ℕ) (radix gamma : F)
    (secretSampler : ProbComp F)
    (errorSampler : ProbComp (BFV.Batch F levels)) :
    FormalProof4FHE.LeftoverHash.collisionProbability
        (gammaSourceSampler levels radix gamma secretSampler errorSampler) =
      FormalProof4FHE.LeftoverHash.collisionProbability secretSampler *
        FormalProof4FHE.LeftoverHash.collisionProbability errorSampler := by
  rw [gammaSourceSampler, collisionProbability_map_equiv,
    collisionProbability_independentPairSampler]

/-- HNF branch presented as public affine hashing of the exact correlated source. -/
def gammaHNFSampler
    {F : Type} [CommRing F] [Fintype F] [SampleableType F]
    (levels : ℕ) (radix gamma : F)
    (secretSampler : ProbComp F)
    (errorSampler : ProbComp (BFV.Batch F levels)) :
    ProbComp (BFV.Transcript F levels) :=
  hashedSource
    (gammaSourceSampler levels radix gamma secretSampler errorSampler)
    (hnfHash (F := F) (Row := Fin (levels + 1)))

/-- Stock BFV branch with a public scalar multiplying the quadratic gadget. -/
def gammaStockSampler
    {F : Type} [CommRing F] [Fintype F] [SampleableType F]
    (levels : ℕ) (radix gamma : F)
    (secretSampler : ProbComp F)
    (errorSampler : ProbComp (BFV.Batch F levels)) :
    ProbComp (BFV.Transcript F levels) := do
  let mask ← $ᵗ (BFV.Batch F levels)
  let secret ← secretSampler
  let error ← errorSampler
  return Standard.gammaStockTranscript levels radix gamma secret error mask

/-- The hash presentation is definitionally the direct correlated-HNF sampler after monad
normalization. -/
theorem gammaHNFSampler_evalDist_eq_direct
    {F : Type} [CommRing F] [Fintype F] [DecidableEq F] [SampleableType F]
    (levels : ℕ) (radix gamma : F)
    (secretSampler : ProbComp F)
    (errorSampler : ProbComp (BFV.Batch F levels)) :
    evalDist (gammaHNFSampler levels radix gamma secretSampler errorSampler) =
      evalDist (do
        let mask ← $ᵗ (BFV.Batch F levels)
        let secret ← secretSampler
        let error ← errorSampler
        return Standard.gammaHNFTranscript levels radix gamma secret error mask) := by
  have hPoint (mask : BFV.Batch F levels) (secret : F)
      (error : BFV.Batch F levels) :
      (mask, hnfHash mask
          (secret, Standard.gammaCorrelatedError levels radix gamma secret error)) =
        Standard.gammaHNFTranscript levels radix gamma secret error mask := by
    rfl
  simp [gammaHNFSampler, gammaSourceSampler, hashedSource,
    independentPairSampler, Standard.gammaSourceEquiv,
    map_eq_bind_pure_comp, bind_assoc, hPoint]

/-- Adjacent differencing maps every stock `gamma` branch exactly to its affine-hash branch. -/
theorem gammaStock_to_gammaHNF_evalDist
    {F : Type} [CommRing F] [Fintype F] [DecidableEq F] [SampleableType F]
    (levels : ℕ) (radix gamma : F)
    (secretSampler : ProbComp F)
    (errorSampler : ProbComp (BFV.Batch F levels)) :
    evalDist (BFV.transcriptEquiv levels radix <$>
        gammaStockSampler levels radix gamma secretSampler errorSampler) =
      evalDist (gammaHNFSampler levels radix gamma secretSampler errorSampler) := by
  have hMask :
      evalDist (BFV.adjacentTransform levels radix <$>
        ($ᵗ (BFV.Batch F levels))) =
        evalDist ($ᵗ (BFV.Batch F levels)) :=
    evalDist_map_bijective_uniform_cross
      (α := BFV.Batch F levels) (β := BFV.Batch F levels)
      (BFV.adjacentTransform levels radix)
      (BFV.adjacentEquiv levels radix).bijective
  have hBind := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq hMask
    (fun mask ↦ secretSampler >>= fun secret ↦
      errorSampler >>= fun error ↦
        pure (Standard.gammaHNFTranscript levels radix gamma secret error mask))
  calc
    evalDist (BFV.transcriptEquiv levels radix <$>
        gammaStockSampler levels radix gamma secretSampler errorSampler) =
      evalDist (do
        let mask ← $ᵗ (BFV.Batch F levels)
        let secret ← secretSampler
        let error ← errorSampler
        return Standard.gammaHNFTranscript levels radix gamma secret error mask) := by
          simpa only [gammaStockSampler, map_eq_bind_pure_comp, Function.comp_def,
            bind_assoc, pure_bind, Standard.adjacent_gammaStockTranscript] using hBind
    _ = evalDist (gammaHNFSampler levels radix gamma secretSampler errorSampler) :=
      (gammaHNFSampler_evalDist_eq_direct levels radix gamma
        secretSampler errorSampler).symm

/-- Total variation is invariant under a deterministic equivalence. -/
theorem tvDist_map_equiv_probComp
    {Input Output : Type} (equiv : Input ≃ Output)
    (left right : ProbComp Input) :
    tvDist (equiv <$> left) (equiv <$> right) = tvDist left right := by
  apply le_antisymm
  · exact tvDist_map_le (m := ProbComp) equiv left right
  · have hReverse := tvDist_map_le (m := ProbComp) equiv.symm
      (equiv <$> left) (equiv <$> right)
    simpa only [Functor.map_map, Equiv.symm_apply_apply, id_map'] using hReverse

/-- The original stock branch and its affine-HNF normal form have exactly the same distance from
uniform. -/
theorem gammaStock_tvDist_uniform_eq_gammaHNF
    {F : Type} [CommRing F] [Fintype F] [DecidableEq F] [SampleableType F]
    (levels : ℕ) (radix gamma : F)
    (secretSampler : ProbComp F)
    (errorSampler : ProbComp (BFV.Batch F levels)) :
    tvDist (gammaStockSampler levels radix gamma secretSampler errorSampler)
        (BFV.uniformSampler (R := F) levels) =
      tvDist (gammaHNFSampler levels radix gamma secretSampler errorSampler)
        (BFV.uniformSampler (R := F) levels) := by
  rw [← tvDist_map_equiv_probComp (BFV.transcriptEquiv levels radix)
    (gammaStockSampler levels radix gamma secretSampler errorSampler)
    (BFV.uniformSampler (R := F) levels)]
  unfold tvDist
  rw [gammaStock_to_gammaHNF_evalDist levels radix gamma secretSampler errorSampler,
    BFV.transcriptEquiv_uniform_evalDist]

/-- Exact collision-entropy statistical bound for either stock BFV branch. -/
theorem gammaStock_tvDist_uniform_le
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    (levels : ℕ) (radix gamma : F)
    (secretSampler : ProbComp F)
    (errorSampler : ProbComp (BFV.Batch F levels)) :
    tvDist (gammaStockSampler levels radix gamma secretSampler errorSampler)
        (BFV.uniformSampler (R := F) levels) ≤
      Real.sqrt ((Fintype.card (BFV.Batch F levels) : ℝ) *
        (FormalProof4FHE.LeftoverHash.collisionProbability secretSampler *
          FormalProof4FHE.LeftoverHash.collisionProbability errorSampler)) / 2 := by
  rw [gammaStock_tvDist_uniform_eq_gammaHNF]
  have hBound := hnfHash_tvDist_uniform_le
    (gammaSourceSampler levels radix gamma secretSampler errorSampler)
  rw [collisionProbability_gammaSourceSampler] at hBound
  simpa [gammaHNFSampler, FormalProof4FHE.LeftoverHash.ideal,
    BFV.uniformSampler] using hBound

/-- Assumption-free quadratic-circular statistical bound.  Both branches have identical source
collision probability because their source maps are bijections. -/
theorem gammaStock_one_zero_tvDist_le
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    (levels : ℕ) (radix : F)
    (secretSampler : ProbComp F)
    (errorSampler : ProbComp (BFV.Batch F levels)) :
    tvDist
        (gammaStockSampler levels radix 1 secretSampler errorSampler)
        (gammaStockSampler levels radix 0 secretSampler errorSampler) ≤
      Real.sqrt ((Fintype.card (BFV.Batch F levels) : ℝ) *
        (FormalProof4FHE.LeftoverHash.collisionProbability secretSampler *
          FormalProof4FHE.LeftoverHash.collisionProbability errorSampler)) := by
  let uniform := BFV.uniformSampler (R := F) levels
  calc
    tvDist
        (gammaStockSampler levels radix 1 secretSampler errorSampler)
        (gammaStockSampler levels radix 0 secretSampler errorSampler) ≤
      tvDist (gammaStockSampler levels radix 1 secretSampler errorSampler) uniform +
        tvDist uniform
          (gammaStockSampler levels radix 0 secretSampler errorSampler) :=
      tvDist_triangle _ uniform _
    _ ≤
      Real.sqrt ((Fintype.card (BFV.Batch F levels) : ℝ) *
        (FormalProof4FHE.LeftoverHash.collisionProbability secretSampler *
          FormalProof4FHE.LeftoverHash.collisionProbability errorSampler)) / 2 +
      Real.sqrt ((Fintype.card (BFV.Batch F levels) : ℝ) *
        (FormalProof4FHE.LeftoverHash.collisionProbability secretSampler *
          FormalProof4FHE.LeftoverHash.collisionProbability errorSampler)) / 2 := by
        apply add_le_add
        · exact gammaStock_tvDist_uniform_le levels radix 1
            secretSampler errorSampler
        · rw [tvDist_comm]
          exact gammaStock_tvDist_uniform_le levels radix 0
            secretSampler errorSampler
    _ = Real.sqrt ((Fintype.card (BFV.Batch F levels) : ℝ) *
        (FormalProof4FHE.LeftoverHash.collisionProbability secretSampler *
          FormalProof4FHE.LeftoverHash.collisionProbability errorSampler)) := by ring

/-- The `gamma=1` sampler is exactly the repository's stock BFV sampler. -/
theorem gammaStockSampler_one_evalDist
    {F : Type} [CommRing F] [Fintype F] [DecidableEq F] [SampleableType F]
    (levels : ℕ) (radix : F)
    (secretSampler : ProbComp F)
    (errorSampler : ProbComp (BFV.Batch F levels)) :
    evalDist (gammaStockSampler levels radix 1 secretSampler errorSampler) =
      evalDist (BFV.stockSampler levels radix secretSampler errorSampler) := by
  simp [gammaStockSampler, BFV.stockSampler, Standard.gammaStockTranscript_one]

/-- The `gamma=0` sampler is exactly the matching ordinary encryption-of-zero sampler. -/
theorem gammaStockSampler_zero_evalDist
    {F : Type} [CommRing F] [Fintype F] [DecidableEq F] [SampleableType F]
    (levels : ℕ) (radix : F)
    (secretSampler : ProbComp F)
    (errorSampler : ProbComp (BFV.Batch F levels)) :
    evalDist (gammaStockSampler levels radix 0 secretSampler errorSampler) =
      evalDist (BFV.zeroSampler levels secretSampler errorSampler) := by
  simp [gammaStockSampler, BFV.zeroSampler, Standard.gammaStockTranscript_zero]

/-- Statistical circular-security theorem for the actual stock/zero BFV samplers. -/
theorem stock_zero_tvDist_le_sqrt_collision
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    (levels : ℕ) (radix : F)
    (secretSampler : ProbComp F)
    (errorSampler : ProbComp (BFV.Batch F levels)) :
    tvDist
        (BFV.stockSampler levels radix secretSampler errorSampler)
        (BFV.zeroSampler levels secretSampler errorSampler) ≤
      Real.sqrt ((Fintype.card (BFV.Batch F levels) : ℝ) *
        (FormalProof4FHE.LeftoverHash.collisionProbability secretSampler *
          FormalProof4FHE.LeftoverHash.collisionProbability errorSampler)) := by
  have hBound := gammaStock_one_zero_tvDist_le
    levels radix secretSampler errorSampler
  unfold tvDist at hBound ⊢
  rwa [gammaStockSampler_one_evalDist,
    gammaStockSampler_zero_evalDist] at hBound

/-- Collision-probability form of the manuscript's entropy criterion.  Taking
`target = 2^(-lambda)` is exactly the exponentiated statement, without formalizing logarithms. -/
theorem stock_zero_tvDist_le_of_collisionBudget
    {F : Type} [Field F] [Fintype F] [DecidableEq F] [SampleableType F]
    (levels : ℕ) (radix : F)
    (secretSampler : ProbComp F)
    (errorSampler : ProbComp (BFV.Batch F levels))
    (target : ℝ) (hTarget : 0 ≤ target)
    (hCollision :
      (Fintype.card (BFV.Batch F levels) : ℝ) *
          (FormalProof4FHE.LeftoverHash.collisionProbability secretSampler *
            FormalProof4FHE.LeftoverHash.collisionProbability errorSampler) ≤
        target ^ 2) :
    tvDist
        (BFV.stockSampler levels radix secretSampler errorSampler)
        (BFV.zeroSampler levels secretSampler errorSampler) ≤ target := by
  exact (stock_zero_tvDist_le_sqrt_collision
    levels radix secretSampler errorSampler).trans (by
      rw [Real.sqrt_le_iff]
      exact ⟨hTarget, hCollision⟩)

/-! ## Coefficient-growth interface -/

/-- First correlated coordinate in the real branch.  Instantiating `size` with the coefficient
sup norm and `mulFactor` with the ring degree gives `E+n*S²`. -/
theorem gammaCorrelatedError_one_zero_size_le
    {R : Type} [CommRing R]
    (levels : ℕ) (radix secret : R) (error : BFV.Batch R levels)
    (size : R → ℝ) (secretBound errorBound mulFactor : ℝ)
    (hAdd : ∀ left right, size (left + right) ≤ size left + size right)
    (hMul : ∀ left right, size (left * right) ≤
      mulFactor * size left * size right)
    (hSizeNonnegative : ∀ value, 0 ≤ size value)
    (hSecret : size secret ≤ secretBound)
    (hError : size (error 0) ≤ errorBound)
    (hMulFactorNonnegative : 0 ≤ mulFactor)
    (hSecretBoundNonnegative : 0 ≤ secretBound) :
    size (Standard.gammaCorrelatedError levels radix 1 secret error 0) ≤
      errorBound + mulFactor * secretBound ^ 2 := by
  rw [Standard.gammaCorrelatedError_zero]
  simp only [one_mul]
  have hSquare : size secret ^ 2 ≤ secretBound ^ 2 :=
    (sq_le_sq₀ (hSizeNonnegative secret) hSecretBoundNonnegative).2 hSecret
  calc
    size (secret ^ 2 + error 0) ≤
        size (secret ^ 2) + size (error 0) := hAdd _ _
    _ ≤ mulFactor * size secret * size secret + errorBound := by
      exact add_le_add (by simpa [pow_two] using hMul secret secret) hError
    _ = mulFactor * size secret ^ 2 + errorBound := by ring
    _ ≤ mulFactor * secretBound ^ 2 + errorBound := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left hSquare hMulFactorNonnegative) le_rfl
    _ = errorBound + mulFactor * secretBound ^ 2 := by ring

/-- Every later correlated coordinate has the checked `(B+1)E` form once multiplication by the
public radix is bounded by `B`. -/
theorem gammaCorrelatedError_succ_size_le
    {R : Type} [CommRing R]
    (levels : ℕ) (radix gamma secret : R) (error : BFV.Batch R levels)
    (previous : Fin levels)
    (size : R → ℝ) (radixBound errorBound : ℝ)
    (hSub : ∀ left right, size (left - right) ≤ size left + size right)
    (hRadixMul : ∀ value, size (radix * value) ≤ radixBound * size value)
    (hCurrent : size (error previous.succ) ≤ errorBound)
    (hPrevious : size (error previous.castSucc) ≤ errorBound)
    (hRadixBoundNonnegative : 0 ≤ radixBound) :
    size (Standard.gammaCorrelatedError levels radix gamma secret error previous.succ) ≤
      (radixBound + 1) * errorBound := by
  rw [Standard.gammaCorrelatedError_succ]
  calc
    size (error previous.succ - radix * error previous.castSucc) ≤
        size (error previous.succ) + size (radix * error previous.castSucc) := hSub _ _
    _ ≤ errorBound + radixBound * size (error previous.castSucc) :=
      add_le_add hCurrent (hRadixMul _)
    _ ≤ errorBound + radixBound * errorBound := by gcongr
    _ = (radixBound + 1) * errorBound := by ring

/-! ## Support-size obstruction -/

/-- Every probability distribution on a finite type has collision probability at least the
reciprocal of the ambient cardinality.  Applying this theorem to the exact support subtype gives
the usual support-cardinality version. -/
theorem one_le_card_mul_collisionProbability
    {Input : Type} [Fintype Input]
    (source : ProbComp Input) :
    1 ≤ (Fintype.card Input : ℝ) *
      FormalProof4FHE.LeftoverHash.collisionProbability source := by
  classical
  let mass : Input → ℝ := fun input ↦ Pr[= input | source].toReal
  have hCauchy := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ : Finset Input) (fun _ : Input ↦ (1 : ℝ)) mass
  have hMass : ∑ input, mass input = 1 := sum_probOutput_toReal_eq_one source
  simpa [mass, hMass, FormalProof4FHE.LeftoverHash.collisionProbability] using hCauchy

/-- Any collision budget sufficient for leftover hashing forces a corresponding source-cardinality
budget. -/
theorem outputCard_le_sourceCard_mul_collisionBudget
    {Input : Type} [Fintype Input]
    (source : ProbComp Input) (outputCard collisionBudget : ℝ)
    (hOutputNonnegative : 0 ≤ outputCard)
    (hBudget : outputCard *
        FormalProof4FHE.LeftoverHash.collisionProbability source ≤ collisionBudget) :
    outputCard ≤ (Fintype.card Input : ℝ) * collisionBudget := by
  have hLower := one_le_card_mul_collisionProbability source
  have hInputNonnegative : (0 : ℝ) ≤ Fintype.card Input := by positivity
  calc
    outputCard ≤ outputCard *
        ((Fintype.card Input : ℝ) *
          FormalProof4FHE.LeftoverHash.collisionProbability source) := by
            nlinarith
    _ = (Fintype.card Input : ℝ) *
        (outputCard *
          FormalProof4FHE.LeftoverHash.collisionProbability source) := by ring
    _ ≤ (Fintype.card Input : ℝ) * collisionBudget :=
      mul_le_mul_of_nonneg_left hBudget hInputNonnegative

/-- Coefficient-alphabet form of the narrow-BFV support obstruction.  `SecretSymbol` and
`ErrorSymbol` are the coefficient alphabets, `degree` is the ring degree, and `digits` is the
number of error polynomials.  This is the exponentiated, log-free form of the manuscript's
necessary entropy inequality. -/
theorem coefficientAlphabet_support_obstruction
    (SecretSymbol ErrorSymbol : Type)
    [Fintype SecretSymbol] [Fintype ErrorSymbol]
    (degree digits : ℕ)
    (source : ProbComp
      ((Fin degree → SecretSymbol) ×
        (Fin digits → Fin degree → ErrorSymbol)))
    (outputCard collisionBudget : ℝ)
    (hOutputNonnegative : 0 ≤ outputCard)
    (hBudget : outputCard *
        FormalProof4FHE.LeftoverHash.collisionProbability source ≤ collisionBudget) :
    outputCard ≤
      ((Fintype.card SecretSymbol : ℝ) ^ degree *
        (Fintype.card ErrorSymbol : ℝ) ^ (digits * degree)) * collisionBudget := by
  have hNecessary := outputCard_le_sourceCard_mul_collisionBudget
    source outputCard collisionBudget hOutputNonnegative hBudget
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin,
    Nat.cast_mul, Nat.cast_pow] at hNecessary
  have hErrorPower :
      ((Fintype.card ErrorSymbol : ℝ) ^ degree) ^ digits =
        (Fintype.card ErrorSymbol : ℝ) ^ (digits * degree) := by
    rw [← pow_mul, Nat.mul_comm]
  rwa [hErrorPower] at hNecessary

end

end FormalProof4FHE.RLWE.BFVCircularSecurityCorrected
