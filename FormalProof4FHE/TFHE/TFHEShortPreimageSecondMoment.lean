/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.JointSubsetKeyBRKDelayedProjection
import FormalProof4FHE.TFHE.RingSquarePowerOfTwoLiftingSelector
import Mathlib.Algebra.Order.Star.Real
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Ternary short-preimage second moments and the SIS boundary

This module formalizes the finite second-moment core of the short-preimage argument. A family of
candidate rows is partitioned into correlated clusters. A single candidate hits a fixed target
with mass `1 / M`; distinct candidates in different clusters have joint mass `1 / M^2`; and a
distinct pair in one cluster has joint mass `C / M^2`. The exact second moment then gives

`failure <= (M - 1) / N + (C - 1) H / N^2`,

where `N` is the candidate count and `H` is the number of ordered distinct within-cluster pairs.
For canonical ternary rows over a power-of-two modulus, clusters are supports and `C = 2^d`.

The remaining sections prove exact disjoint-support Gram control, record the independent
computational boundary that two related geometric-gadget preimages give a nonzero homogeneous SIS
relation, and formalize the odd-minor/parity/`±2` algebra behind the canonical pair classes. None
of these results asserts an efficient preimage algorithm.
-/

open scoped BigOperators ENNReal

namespace FormalProof4FHE.TFHE.TFHEShortPreimageSecondMoment

noncomputable section

/-! ## Generic clustered second moment -/

namespace ClusteredMoment

variable {Seed Candidate : Type} [Fintype Seed] [Fintype Candidate]

/-- Real indicator of a candidate hitting on one public seed. -/
def hitIndicator (hit : Seed → Candidate → Prop) [DecidableRel hit]
    (seed : Seed) (candidate : Candidate) : ℝ :=
  if hit seed candidate then 1 else 0

/-- Number of candidates hitting on one seed, represented in `ℝ` for moment calculations. -/
def hitCount (hit : Seed → Candidate → Prop) [DecidableRel hit]
    (seed : Seed) : ℝ :=
  ∑ candidate, hitIndicator hit seed candidate

/-- Number of seeds on which no candidate hits. -/
def zeroHitSeedCount (hit : Seed → Candidate → Prop) [DecidableRel hit] : ℕ :=
  (Finset.univ.filter fun seed ↦ hitCount hit seed = 0).card

/-- Ordered distinct pairs belonging to the same correlation cluster. -/
def clusteredOrderedPairCount
    (sameCluster : Candidate → Candidate → Prop) [DecidableEq Candidate]
    [DecidableRel sameCluster] : ℕ :=
  (Finset.univ.filter fun pair : Candidate × Candidate ↦
    pair.1 ≠ pair.2 ∧ sameCluster pair.1 pair.2).card

theorem cast_clusteredOrderedPairCount
    (sameCluster : Candidate → Candidate → Prop) [DecidableEq Candidate]
    [DecidableRel sameCluster] :
    (clusteredOrderedPairCount sameCluster : ℝ) =
      ∑ left, ∑ right,
        if left ≠ right ∧ sameCluster left right then 1 else 0 := by
  classical
  unfold clusteredOrderedPairCount
  rw [show ((Finset.univ.filter fun pair : Candidate × Candidate ↦
      pair.1 ≠ pair.2 ∧ sameCluster pair.1 pair.2).card : ℝ) =
      ∑ pair : Candidate × Candidate,
        if pair.1 ≠ pair.2 ∧ sameCluster pair.1 pair.2 then 1 else 0 by
    simp]
  rw [Fintype.sum_prod_type]

omit [Fintype Seed] [Fintype Candidate] in
theorem hitIndicator_sq
    (hit : Seed → Candidate → Prop) [DecidableRel hit]
    (seed : Seed) (candidate : Candidate) :
    hitIndicator hit seed candidate ^ 2 = hitIndicator hit seed candidate := by
  by_cases h : hit seed candidate <;> simp [hitIndicator, h]

/-- Summing the hit count first over seeds or first over candidates gives the same first moment. -/
theorem sum_hitCount_eq_sum_singleMass
    (hit : Seed → Candidate → Prop) [DecidableRel hit] :
    (∑ seed, hitCount hit seed) =
      ∑ candidate, ∑ seed, hitIndicator hit seed candidate := by
  simp only [hitCount]
  exact Finset.sum_comm

/-- Expanding the square of the hit count gives the complete ordered-pair moment. -/
theorem sum_hitCount_sq_eq_sum_pairMass
    (hit : Seed → Candidate → Prop) [DecidableRel hit] :
    (∑ seed, hitCount hit seed ^ 2) =
      ∑ left, ∑ right, ∑ seed,
        hitIndicator hit seed left * hitIndicator hit seed right := by
  classical
  calc
    (∑ seed, hitCount hit seed ^ 2) =
        ∑ seed, ∑ left, ∑ right,
          hitIndicator hit seed left * hitIndicator hit seed right := by
      apply Finset.sum_congr rfl
      intro seed _
      simp only [hitCount, pow_two, Finset.sum_mul_sum]
    _ = ∑ left, ∑ seed, ∑ right,
          hitIndicator hit seed left * hitIndicator hit seed right := by
      rw [Finset.sum_comm]
    _ = ∑ left, ∑ right, ∑ seed,
          hitIndicator hit seed left * hitIndicator hit seed right := by
      apply Finset.sum_congr rfl
      intro left _
      exact Finset.sum_comm

/-- Exact first moment from a uniform singleton hit mass. -/
theorem sum_hitCount_eq
    (hit : Seed → Candidate → Prop) [DecidableRel hit]
    (M : ℝ) (singleMass : ∀ candidate,
      (∑ seed, hitIndicator hit seed candidate) = Fintype.card Seed / M) :
    (∑ seed, hitCount hit seed) =
      Fintype.card Seed * Fintype.card Candidate / M := by
  rw [sum_hitCount_eq_sum_singleMass]
  simp_rw [singleMass]
  simp
  ring

/-- Exact second moment for a family whose only excess pair mass occurs inside `sameCluster`. -/
theorem sum_hitCount_sq_eq
    (hit : Seed → Candidate → Prop) [DecidableRel hit]
    (sameCluster : Candidate → Candidate → Prop) [DecidableEq Candidate]
    [DecidableRel sameCluster]
    (M clusterFactor : ℝ)
    (pairMass : ∀ left right,
      (∑ seed,
          hitIndicator hit seed left * hitIndicator hit seed right) =
        if left = right then Fintype.card Seed / M
        else if sameCluster left right then
          clusterFactor * Fintype.card Seed / M ^ 2
        else Fintype.card Seed / M ^ 2) :
    (∑ seed, hitCount hit seed ^ 2) =
      Fintype.card Seed *
        (Fintype.card Candidate / M +
          ((Fintype.card Candidate : ℝ) ^ 2 - Fintype.card Candidate) / M ^ 2 +
          (clusterFactor - 1) * clusteredOrderedPairCount sameCluster / M ^ 2) := by
  classical
  rw [sum_hitCount_sq_eq_sum_pairMass]
  simp_rw [pairMass]
  let S : ℝ := Fintype.card Seed
  let N : ℝ := Fintype.card Candidate
  let H : ℝ := clusteredOrderedPairCount sameCluster
  have hpoint (left right : Candidate) :
      (if left = right then S / M
        else if sameCluster left right then clusterFactor * S / M ^ 2
        else S / M ^ 2) =
      S / M ^ 2 +
        (if left = right then S / M - S / M ^ 2 else 0) +
        (if left ≠ right ∧ sameCluster left right then
          (clusterFactor - 1) * S / M ^ 2 else 0) := by
    by_cases heq : left = right
    · subst right
      simp
    · by_cases hcluster : sameCluster left right
      · simp [heq, hcluster]
        ring
      · simp [heq, hcluster]
  change
    (∑ left : Candidate, ∑ right : Candidate,
      if left = right then S / M
      else if sameCluster left right then clusterFactor * S / M ^ 2
      else S / M ^ 2) =
      S * (N / M + (N ^ 2 - N) / M ^ 2 +
        (clusterFactor - 1) * H / M ^ 2)
  simp_rw [hpoint]
  have hclusterSum :
      (∑ left : Candidate, ∑ right : Candidate,
        if left ≠ right ∧ sameCluster left right then
          (clusterFactor - 1) * S / M ^ 2 else 0) =
        H * ((clusterFactor - 1) * S / M ^ 2) := by
    let K := (clusterFactor - 1) * S / M ^ 2
    calc
      (∑ left : Candidate, ∑ right : Candidate,
          if left ≠ right ∧ sameCluster left right then K else 0) =
          ∑ left : Candidate,
            (∑ right : Candidate,
              if left ≠ right ∧ sameCluster left right then 1 else 0) * K := by
        apply Finset.sum_congr rfl
        intro left _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro right _
        by_cases h : left ≠ right ∧ sameCluster left right <;> simp [h]
      _ = (∑ left : Candidate, ∑ right : Candidate,
              if left ≠ right ∧ sameCluster left right then 1 else 0) * K := by
        rw [Finset.sum_mul]
      _ = H * K := by
        rw [← cast_clusteredOrderedPairCount sameCluster]
  have hdiagonalSum :
      (∑ left : Candidate, ∑ right : Candidate,
        if left = right then S / M - S / M ^ 2 else 0) =
        N * (S / M - S / M ^ 2) := by
    calc
      (∑ left : Candidate, ∑ right : Candidate,
          if left = right then S / M - S / M ^ 2 else 0) =
          ∑ _left : Candidate, (S / M - S / M ^ 2) := by
        apply Finset.sum_congr rfl
        intro left _
        simp
      _ = N * (S / M - S / M ^ 2) := by
        simp [N]
        ring
  simp_rw [Finset.sum_add_distrib]
  rw [hdiagonalSum, hclusterSum]
  simp only [Finset.sum_const, nsmul_eq_mul]
  simp only [Finset.card_univ]
  simp only [S, N, H]
  ring

/-- A zero-hit seed contributes the complete squared mean to the centered second moment. -/
theorem zeroHitSeedCount_mul_mean_sq_le
    (hit : Seed → Candidate → Prop) [DecidableRel hit]
    (mean : ℝ) :
    (zeroHitSeedCount hit : ℝ) * mean ^ 2 ≤
      ∑ seed, (hitCount hit seed - mean) ^ 2 := by
  classical
  calc
    (zeroHitSeedCount hit : ℝ) * mean ^ 2 =
        ∑ seed, if hitCount hit seed = 0 then mean ^ 2 else 0 := by
      unfold zeroHitSeedCount
      rw [show ((Finset.univ.filter fun seed ↦ hitCount hit seed = 0).card : ℝ) =
          ∑ seed, if hitCount hit seed = 0 then 1 else 0 by simp]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro seed _
      by_cases hzero : hitCount hit seed = 0 <;> simp [hzero]
    _ ≤ ∑ seed, (hitCount hit seed - mean) ^ 2 := by
      apply Finset.sum_le_sum
      intro seed _
      by_cases hzero : hitCount hit seed = 0
      · simp [hzero]
      · simp [hzero]
        positivity

/-- The clustered second-moment failure bound.  This is the exact abstract form used by the
canonical-ternary calculation: `M` is the target-space cardinality, `clusterFactor` is the
same-support joint-hit factor, and `clusteredOrderedPairCount` is an ordered count. -/
theorem zeroHitSeedRatio_le
    [Nonempty Seed] [Nonempty Candidate]
    (hit : Seed → Candidate → Prop) [DecidableRel hit]
    (sameCluster : Candidate → Candidate → Prop) [DecidableEq Candidate]
    [DecidableRel sameCluster]
    (M clusterFactor : ℝ) (hM : 0 < M)
    (singleMass : ∀ candidate,
      (∑ seed, hitIndicator hit seed candidate) = Fintype.card Seed / M)
    (pairMass : ∀ left right,
      (∑ seed,
          hitIndicator hit seed left * hitIndicator hit seed right) =
        if left = right then Fintype.card Seed / M
        else if sameCluster left right then
          clusterFactor * Fintype.card Seed / M ^ 2
        else Fintype.card Seed / M ^ 2) :
    (zeroHitSeedCount hit : ℝ) / Fintype.card Seed ≤
      (M - 1) / Fintype.card Candidate +
        (clusterFactor - 1) * clusteredOrderedPairCount sameCluster /
          (Fintype.card Candidate : ℝ) ^ 2 := by
  let S : ℝ := Fintype.card Seed
  let N : ℝ := Fintype.card Candidate
  let H : ℝ := clusteredOrderedPairCount sameCluster
  have hS : 0 < S := by
    dsimp [S]
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hN : 0 < N := by
    dsimp [N]
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hfirst :
      (∑ seed, hitCount hit seed) = S * N / M := by
    simpa [S, N] using sum_hitCount_eq hit M singleMass
  have hsecond :
      (∑ seed, hitCount hit seed ^ 2) =
        S * (N / M + (N ^ 2 - N) / M ^ 2 +
          (clusterFactor - 1) * H / M ^ 2) := by
    simpa [S, N, H] using
      sum_hitCount_sq_eq hit sameCluster M clusterFactor pairMass
  have hlinear :
      (∑ seed, 2 * hitCount hit seed * (N / M)) =
        2 * (N / M) * (∑ seed, hitCount hit seed) := by
    calc
      (∑ seed, 2 * hitCount hit seed * (N / M)) =
          ∑ seed, (2 * (N / M)) * hitCount hit seed := by
        apply Finset.sum_congr rfl
        intro seed _
        ring
      _ = 2 * (N / M) * (∑ seed, hitCount hit seed) := by
        rw [Finset.mul_sum]
  have hconstant :
      (∑ _seed : Seed, (N / M) ^ 2) = S * (N / M) ^ 2 := by
    simp [S]
  have hcentered :
      (∑ seed, (hitCount hit seed - N / M) ^ 2) =
        S * (((M - 1) * N + (clusterFactor - 1) * H) / M ^ 2) := by
    calc
      (∑ seed, (hitCount hit seed - N / M) ^ 2) =
          (∑ seed, hitCount hit seed ^ 2) -
            2 * (N / M) * (∑ seed, hitCount hit seed) +
              S * (N / M) ^ 2 := by
        simp_rw [sub_sq]
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
        rw [hlinear, hconstant]
      _ = S * (((M - 1) * N + (clusterFactor - 1) * H) / M ^ 2) := by
        rw [hfirst, hsecond]
        field_simp [ne_of_gt hM]
        ring
  have hzero := zeroHitSeedCount_mul_mean_sq_le hit (N / M)
  rw [hcentered] at hzero
  have hcross :
      (zeroHitSeedCount hit : ℝ) * N ^ 2 ≤
        S * ((M - 1) * N + (clusterFactor - 1) * H) := by
    field_simp [ne_of_gt hM] at hzero
    nlinarith
  change (zeroHitSeedCount hit : ℝ) / S ≤
    (M - 1) / N + (clusterFactor - 1) * H / N ^ 2
  rw [show (M - 1) / N + (clusterFactor - 1) * H / N ^ 2 =
      ((M - 1) * N + (clusterFactor - 1) * H) / N ^ 2 by
    field_simp [ne_of_gt hN]]
  rw [div_le_div_iff₀ hS (sq_pos_of_pos hN)]
  nlinarith

/-- Number of public seeds on which at least one prescribed target has no candidate preimage. -/
def someTargetZeroSeedCount {Target : Type} [Fintype Target]
    (hit : Seed → Target → Candidate → Prop)
    [decidableHit : ∀ seed target candidate, Decidable (hit seed target candidate)] : ℕ :=
  (Finset.univ.filter fun seed ↦
    ∃ target, hitCount (fun publicSeed candidate ↦
      hit publicSeed target candidate) seed = 0).card

/-- Finite target-family union bound.  Applying `zeroHitSeedRatio_le` to each target and then this
theorem charges the target multiplicity exactly once. -/
theorem someTargetZeroSeedRatio_le {Target : Type} [Fintype Target]
    [DecidableEq Seed] [DecidableEq Target]
    (hit : Seed → Target → Candidate → Prop) (failure : ℝ)
    [decidableHit : ∀ seed target candidate, Decidable (hit seed target candidate)]
    (pointwise : ∀ target,
      (zeroHitSeedCount (fun seed candidate ↦ hit seed target candidate) : ℝ) /
          Fintype.card Seed ≤ failure) :
    (someTargetZeroSeedCount hit : ℝ) / Fintype.card Seed ≤
      Fintype.card Target * failure := by
  classical
  have hsubset :
      (Finset.univ.filter fun seed : Seed ↦
        ∃ target, hitCount (fun publicSeed candidate ↦
          hit publicSeed target candidate) seed = 0) ⊆
        Finset.univ.biUnion fun target : Target ↦
          Finset.univ.filter fun seed : Seed ↦
            hitCount (fun publicSeed candidate ↦
              hit publicSeed target candidate) seed = 0 := by
    intro seed hseed
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hseed
    obtain ⟨target, hzero⟩ := hseed
    simp only [Finset.mem_biUnion]
    refine ⟨target, Finset.mem_univ target, ?_⟩
    simp [hzero]
  have hcountNat :
      someTargetZeroSeedCount hit ≤
        ∑ target : Target,
          zeroHitSeedCount (fun seed candidate ↦ hit seed target candidate) := by
    unfold someTargetZeroSeedCount zeroHitSeedCount
    calc
      (Finset.univ.filter fun seed : Seed ↦
          ∃ target, hitCount (fun publicSeed candidate ↦
            hit publicSeed target candidate) seed = 0).card ≤
          (Finset.univ.biUnion fun target : Target ↦
            Finset.univ.filter fun seed : Seed ↦
              hitCount (fun publicSeed candidate ↦
                hit publicSeed target candidate) seed = 0).card :=
        Finset.card_le_card hsubset
      _ ≤ ∑ target : Target,
          (Finset.univ.filter fun seed : Seed ↦
            hitCount (fun publicSeed candidate ↦
              hit publicSeed target candidate) seed = 0).card :=
        Finset.card_biUnion_le
  have hcountReal :
      (someTargetZeroSeedCount hit : ℝ) ≤
        ∑ target : Target,
          (zeroHitSeedCount
            (fun seed candidate ↦ hit seed target candidate) : ℝ) := by
    exact_mod_cast hcountNat
  calc
    (someTargetZeroSeedCount hit : ℝ) / Fintype.card Seed ≤
        (∑ target : Target,
          (zeroHitSeedCount
            (fun seed candidate ↦ hit seed target candidate) : ℝ)) /
              Fintype.card Seed :=
      div_le_div_of_nonneg_right hcountReal (by positivity)
    _ = ∑ target : Target,
          (zeroHitSeedCount
            (fun seed candidate ↦ hit seed target candidate) : ℝ) /
              Fintype.card Seed := by
      rw [Finset.sum_div]
    _ ≤ ∑ _target : Target, failure := by
      apply Finset.sum_le_sum
      intro target _
      exact pointwise target
    _ = Fintype.card Target * failure := by simp

end ClusteredMoment

/-! ## Disjoint supports give exact joint Gram control -/

namespace DisjointGram

variable {Output Source : Type} [Fintype Output] [DecidableEq Output]
  [Fintype Source]

/-- Squared Euclidean norm of one selected preimage row. -/
def rowEnergy (postprocess : Matrix Output Source ℝ) (output : Output) : ℝ :=
  ∑ source, postprocess output source ^ 2

/-- Different output rows use disjoint source coordinates. -/
def PairwiseDisjointRows (postprocess : Matrix Output Source ℝ) : Prop :=
  ∀ first second, first ≠ second → ∀ source,
    postprocess first source = 0 ∨ postprocess second source = 0

omit [Fintype Output] [DecidableEq Output] in
theorem crossGram_eq_zero (postprocess : Matrix Output Source ℝ)
    (hdisjoint : PairwiseDisjointRows postprocess)
    (first second : Output) (hne : first ≠ second) :
    ∑ source, postprocess first source * postprocess second source = 0 := by
  apply Finset.sum_eq_zero
  intro source _
  rcases hdisjoint first second hne source with hfirst | hsecond
  · simp [hfirst]
  · simp [hsecond]

omit [Fintype Output] in
/-- The complete row Gram matrix is exactly diagonal; this is stronger than bounding rows one at
a time and retains every off-diagonal covariance entry. -/
theorem mul_transpose_eq_diagonal (postprocess : Matrix Output Source ℝ)
    (hdisjoint : PairwiseDisjointRows postprocess) :
    postprocess * postprocess.transpose =
      Matrix.diagonal (rowEnergy postprocess) := by
  classical
  ext first second
  by_cases heq : first = second
  · subst second
    simp [Matrix.mul_apply, Matrix.diagonal, rowEnergy, pow_two]
  · rw [Matrix.mul_apply]
    change (∑ source,
      postprocess first source * postprocess second source) = _
    rw [crossGram_eq_zero postprocess hdisjoint first second heq]
    simp [Matrix.diagonal, heq]

omit [Fintype Output] in
/-- If every disjoint row has energy at most `bound`, then the simultaneous matrix inequality is
positive semidefinite: `postprocess * postprocessᵀ ⪯ bound I`. -/
theorem gram_psd_le (postprocess : Matrix Output Source ℝ)
    (hdisjoint : PairwiseDisjointRows postprocess) (bound : ℝ)
    (henergy : ∀ output, rowEnergy postprocess output ≤ bound) :
    (bound • (1 : Matrix Output Output ℝ) -
      postprocess * postprocess.transpose).PosSemidef := by
  classical
  rw [mul_transpose_eq_diagonal postprocess hdisjoint]
  have hmatrix :
      bound • (1 : Matrix Output Output ℝ) -
          Matrix.diagonal (rowEnergy postprocess) =
        Matrix.diagonal fun output ↦ bound - rowEnergy postprocess output := by
    ext first second
    by_cases heq : first = second <;> simp [Matrix.diagonal, heq]
  rw [hmatrix]
  apply Matrix.PosSemidef.diagonal
  intro output
  exact sub_nonneg.mpr (henergy output)

end DisjointGram

/-! ## Two related preimages imply an SIS relation -/

namespace SISBoundary

variable {Row Coordinate : Type} [Fintype Row]

/-- Integer coefficients applied to a public matrix, reduced modulo `modulus`. -/
def integerRowCombination (modulus : ℕ) (coefficient : Row → ℤ)
    (matrix : Row → Coordinate → ZMod modulus) : Coordinate → ZMod modulus :=
  fun coordinate ↦
    ∑ row, (coefficient row : ZMod modulus) * matrix row coordinate

/-- Pointwise integer scaling, kept explicit to avoid confusing integer multiplication with
modular scalar multiplication. -/
def integerScale (scale : ℤ) (coefficient : Row → ℤ) : Row → ℤ :=
  fun row ↦ scale * coefficient row

theorem integerRowCombination_sub (modulus : ℕ) (left right : Row → ℤ)
    (matrix : Row → Coordinate → ZMod modulus) :
    integerRowCombination modulus (left - right) matrix =
      integerRowCombination modulus left matrix -
        integerRowCombination modulus right matrix := by
  funext coordinate
  simp [integerRowCombination, sub_mul, Finset.sum_sub_distrib]

theorem integerRowCombination_integerScale (modulus : ℕ) (scale : ℤ)
    (coefficient : Row → ℤ) (matrix : Row → Coordinate → ZMod modulus) :
    integerRowCombination modulus (integerScale scale coefficient) matrix =
      fun coordinate ↦
        (scale : ZMod modulus) *
          integerRowCombination modulus coefficient matrix coordinate := by
  funext coordinate
  unfold integerRowCombination integerScale
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro row _
  push_cast
  ring

/-- The coefficient-wise alphabet condition used by the short-preimage argument. -/
def IsTernary (coefficient : Row → ℤ) : Prop :=
  ∀ row, coefficient row = -1 ∨ coefficient row = 0 ∨ coefficient row = 1

omit [Fintype Row] in
theorem IsTernary.abs_le_one {coefficient : Row → ℤ}
    (hternary : IsTernary coefficient) (row : Row) :
    |coefficient row| ≤ 1 := by
  rcases hternary row with hnegative | hzero | hpositive
  · simp [hnegative]
  · simp [hzero]
  · simp [hpositive]

theorem IsTernary.exists_nonzero_coordinate {coefficient : Row → ℤ}
    (hternary : IsTernary coefficient) (hne : coefficient ≠ 0) :
    ∃ row, coefficient row = -1 ∨ coefficient row = 1 := by
  classical
  by_contra hexists
  push Not at hexists
  apply hne
  funext row
  rcases hternary row with hnegative | hzero | hpositive
  · exact False.elim ((hexists row).1 hnegative)
  · exact hzero
  · exact False.elim ((hexists row).2 hpositive)

/-- The homogeneous relation obtained by subtracting a base-scaled preimage from the next
geometric-gadget preimage. -/
def geometricRelation (base : ℤ) (left right : Row → ℤ) : Row → ℤ :=
  integerScale base left - right

theorem geometricRelation_ne_zero (base : ℤ) (left right : Row → ℤ)
    (hbase : 2 ≤ base) (hleftTernary : IsTernary left)
    (hrightTernary : IsTernary right) (hleftNe : left ≠ 0) :
    geometricRelation base left right ≠ 0 := by
  obtain ⟨pivot, hpivot⟩ :=
    hleftTernary.exists_nonzero_coordinate hleftNe
  have hrightLower : -1 ≤ right pivot := by
    rcases hrightTernary pivot with hnegative | hzero | hpositive <;> omega
  have hrightUpper : right pivot ≤ 1 := by
    rcases hrightTernary pivot with hnegative | hzero | hpositive <;> omega
  intro hzero
  have hpivotZero := congrFun hzero pivot
  change base * left pivot - right pivot = 0 at hpivotZero
  rcases hpivot with hnegative | hpositive
  · rw [hnegative] at hpivotZero
    norm_num at hpivotZero
    omega
  · rw [hpositive] at hpivotZero
    norm_num at hpivotZero
    omega

omit [Fintype Row] in
theorem abs_geometricRelation_apply_le (base : ℤ) (left right : Row → ℤ)
    (hleftTernary : IsTernary left) (hrightTernary : IsTernary right)
    (row : Row) :
    |geometricRelation base left right row| ≤ |base| + 1 := by
  calc
    |geometricRelation base left right row| =
        |base * left row - right row| := by
      rfl
    _ ≤ |base * left row| + |right row| := abs_sub _ _
    _ = |base| * |left row| + |right row| := by rw [abs_mul]
    _ ≤ |base| * 1 + 1 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hleftTernary.abs_le_one row) (abs_nonneg base))
        (hrightTernary.abs_le_one row)
    _ = |base| + 1 := by ring

/-- Two ternary preimages of the related targets `target` and `base * target`, under the same
public matrix, yield a nonzero homogeneous SIS vector with coefficient bound `|base| + 1`.
This is the precise computational boundary left after the information-theoretic existence proof. -/
theorem geometricPreimages_give_sis (modulus : ℕ) (base : ℤ)
    (matrix : Row → Coordinate → ZMod modulus)
    (target : Coordinate → ZMod modulus) (left right : Row → ℤ)
    (hbase : 2 ≤ base) (hleftTernary : IsTernary left)
    (hrightTernary : IsTernary right) (hleftNe : left ≠ 0)
    (hleft : integerRowCombination modulus left matrix = target)
    (hright : integerRowCombination modulus right matrix =
      fun coordinate ↦ (base : ZMod modulus) * target coordinate) :
    ∃ relation : Row → ℤ,
      relation ≠ 0 ∧
      integerRowCombination modulus relation matrix = 0 ∧
      ∀ row, |relation row| ≤ |base| + 1 := by
  refine ⟨geometricRelation base left right,
    geometricRelation_ne_zero base left right hbase hleftTernary hrightTernary hleftNe,
    ?_, abs_geometricRelation_apply_le base left right hleftTernary hrightTernary⟩
  rw [geometricRelation, integerRowCombination_sub,
    integerRowCombination_integerScale, hleft, hright]
  funext coordinate
  simp

end SISBoundary

/-! ## Algebra behind the canonical-ternary pair classification -/

namespace PairClassification

variable {Row R : Type} [Fintype Row] [DecidableEq Row]

/-- The two simultaneous scalar row combinations made by one public column. -/
def pairCombination [CommRing R] (left right : Row → R) :
    (Row → R) →+ R × R where
  toFun vector :=
    (∑ row, left row * vector row, ∑ row, right row * vector row)
  map_zero' := by simp
  map_add' := by
    intro first second
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib, Prod.mk_add_mk]

/-- A selected two-by-two minor of the two coefficient rows. -/
def pairMinor [CommRing R] (left right : Row → R) (first second : Row) : R :=
  left first * right second - left second * right first

/-- A unit two-by-two minor makes the simultaneous pair-combination map surjective. -/
theorem pairCombination_surjective_of_unit_minor
    [CommRing R] [Nontrivial R] (left right : Row → R) (first second : Row)
    (hminor : IsUnit (pairMinor left right first second)) :
    Function.Surjective (pairCombination left right) := by
  classical
  have hne : first ≠ second := by
    intro heq
    subst second
    simp [pairMinor] at hminor
  let determinantUnit : Rˣ := hminor.unit
  let inverse : R := ↑determinantUnit⁻¹
  have hunitSpec : (determinantUnit : R) =
      pairMinor left right first second := hminor.unit_spec
  have hinverse : inverse * pairMinor left right first second = 1 := by
    rw [← hunitSpec]
    exact Units.inv_mul determinantUnit
  intro target
  let firstValue : R := inverse *
    (right second * target.1 - left second * target.2)
  let secondValue : R := inverse *
    (-right first * target.1 + left first * target.2)
  let preimage : Row → R :=
    Pi.single first firstValue + Pi.single second secondValue
  have sum_mul_single (coefficient : Row → R) (index : Row) (value : R) :
      (∑ row, coefficient row * (Pi.single index value : Row → R) row) =
        coefficient index * value := by
    rw [Finset.sum_eq_single index]
    · simp
    · intro row _ hrow
      simp [hrow]
    · simp
  refine ⟨preimage, ?_⟩
  apply Prod.ext
  · change (∑ row, left row * preimage row) = target.1
    have hsum :
        (∑ row, left row * preimage row) =
          left first * firstValue + left second * secondValue := by
      simp only [preimage, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      rw [sum_mul_single, sum_mul_single]
    rw [hsum]
    change
      left first * (inverse *
          (right second * target.1 - left second * target.2)) +
        left second * (inverse *
          (-right first * target.1 + left first * target.2)) = target.1
    calc
      _ = (inverse * pairMinor left right first second) * target.1 := by
        simp only [pairMinor]
        ring
      _ = target.1 := by rw [hinverse, one_mul]
  · change (∑ row, right row * preimage row) = target.2
    have hsum :
        (∑ row, right row * preimage row) =
          right first * firstValue + right second * secondValue := by
      simp only [preimage, Pi.add_apply, mul_add, Finset.sum_add_distrib]
      rw [sum_mul_single, sum_mul_single]
    rw [hsum]
    change
      right first * (inverse *
          (right second * target.1 - left second * target.2)) +
        right second * (inverse *
          (-right first * target.1 + left first * target.2)) = target.2
    calc
      _ = (inverse * pairMinor left right first second) * target.2 := by
        simp only [pairMinor]
        ring
      _ = target.2 := by rw [hinverse, one_mul]

/-- Reduction of an integer coefficient row into the public modular ring. -/
def reduceCoefficient (modulus : ℕ) (coefficient : Row → ℤ) :
    Row → ZMod modulus :=
  fun row ↦ coefficient row

/-- Equality of supports, stated without committing to a particular finite-set encoding. -/
def SameSupport (left right : Row → ℤ) : Prop :=
  ∀ row, left row = 0 ↔ right row = 0

omit [DecidableEq Row] in
theorem exists_nonzero_coordinate {coefficient : Row → ℤ}
    (hne : coefficient ≠ 0) : ∃ row, coefficient row ≠ 0 := by
  classical
  by_contra hexists
  push Not at hexists
  apply hne
  funext row
  exact hexists row

/-- Distinct supports of nonzero ternary rows expose an odd (`±1`) minor.  Consequently the
two-output map is surjective over every modular ring. -/
theorem pairCombination_surjective_of_different_ternary_support
    (exponent : ℕ) (left right : Row → ℤ)
    (hleftTernary : SISBoundary.IsTernary left)
    (hrightTernary : SISBoundary.IsTernary right)
    (hleftNe : left ≠ 0) (hrightNe : right ≠ 0)
    (hdifferent : ¬SameSupport left right) :
    Function.Surjective
      (pairCombination (reduceCoefficient (2 ^ (exponent + 1)) left)
        (reduceCoefficient (2 ^ (exponent + 1)) right)) := by
  classical
  letI : Fact (1 < 2 ^ (exponent + 1)) :=
    ⟨one_lt_pow' (by omega : 1 < 2) (by omega)⟩
  rw [SameSupport] at hdifferent
  push Not at hdifferent
  obtain ⟨first, hfirst⟩ := hdifferent
  by_cases hleftFirst : left first = 0
  · have hrightFirst : right first ≠ 0 := by
      rcases hfirst with hcase | hcase
      · exact hcase.2
      · exact (hcase.1 hleftFirst).elim
    obtain ⟨second, hleftSecond⟩ := exists_nonzero_coordinate hleftNe
    apply pairCombination_surjective_of_unit_minor
      (first := first) (second := second)
    rcases hrightTernary first with hrightNegative | hrightZero | hrightPositive
    · rcases hleftTernary second with hleftNegative | hleftZero | hleftPositive
      · simp [pairMinor, reduceCoefficient, hleftFirst, hrightNegative,
          hleftNegative]
      · exact (hleftSecond hleftZero).elim
      · simp [pairMinor, reduceCoefficient, hleftFirst, hrightNegative,
          hleftPositive]
    · exact (hrightFirst hrightZero).elim
    · rcases hleftTernary second with hleftNegative | hleftZero | hleftPositive
      · simp [pairMinor, reduceCoefficient, hleftFirst, hrightPositive,
          hleftNegative]
      · exact (hleftSecond hleftZero).elim
      · simp [pairMinor, reduceCoefficient, hleftFirst, hrightPositive,
          hleftPositive]
  · have hrightFirst : right first = 0 := by
      rcases hfirst with hcase | hcase
      · exact (hleftFirst hcase.1).elim
      · exact hcase.2
    obtain ⟨second, hrightSecond⟩ := exists_nonzero_coordinate hrightNe
    apply pairCombination_surjective_of_unit_minor
      (first := first) (second := second)
    rcases hleftTernary first with hleftNegative | hleftZero | hleftPositive
    · rcases hrightTernary second with hrightNegative | hrightZero | hrightPositive
      · simp [pairMinor, reduceCoefficient, hrightFirst, hleftNegative,
          hrightNegative]
      · exact (hrightSecond hrightZero).elim
      · simp [pairMinor, reduceCoefficient, hrightFirst, hleftNegative,
          hrightPositive]
    · exact (hleftFirst hleftZero).elim
    · rcases hrightTernary second with hrightNegative | hrightZero | hrightPositive
      · simp [pairMinor, reduceCoefficient, hrightFirst, hleftPositive,
          hrightNegative]
      · exact (hrightSecond hrightZero).elim
      · simp [pairMinor, reduceCoefficient, hrightFirst, hleftPositive,
          hrightPositive]

omit [Fintype Row] [DecidableEq Row] in
/-- Equal-support canonical rows that are distinct expose a minor equal to `+2` or `-2`.
The `commonPositive` premise is exactly what the first-nonzero-positive convention supplies. -/
theorem exists_unit_two_minor_of_same_support
    (modulus : ℕ) (left right : Row → ℤ)
    (hleftTernary : SISBoundary.IsTernary left)
    (hrightTernary : SISBoundary.IsTernary right)
    (hsupport : SameSupport left right) (hne : left ≠ right)
    (commonPositive : ∃ first, left first = 1 ∧ right first = 1) :
    ∃ first second,
      pairMinor (reduceCoefficient modulus left)
          (reduceCoefficient modulus right) first second = 2 ∨
        pairMinor (reduceCoefficient modulus left)
          (reduceCoefficient modulus right) first second = -2 := by
  classical
  obtain ⟨first, hleftFirst, hrightFirst⟩ := commonPositive
  obtain ⟨second, hsecond⟩ := Function.ne_iff.mp hne
  have hleftSecond : left second ≠ 0 := by
    intro hzero
    have hrightZero := (hsupport second).mp hzero
    exact hsecond (hzero.trans hrightZero.symm)
  have hrightSecond : right second ≠ 0 := by
    intro hzero
    have hleftZero := (hsupport second).mpr hzero
    exact hsecond (hleftZero.trans hzero.symm)
  refine ⟨first, second, ?_⟩
  rcases hleftTernary second with hleftNegative | hleftZero | hleftPositive
  · rcases hrightTernary second with hrightNegative | hrightZero | hrightPositive
    · exact (hsecond (hleftNegative.trans hrightNegative.symm)).elim
    · exact (hrightSecond hrightZero).elim
    · left
      simp [pairMinor, reduceCoefficient, hleftFirst, hrightFirst,
        hleftNegative, hrightPositive]
      ring
  · exact (hleftSecond hleftZero).elim
  · rcases hrightTernary second with hrightNegative | hrightZero | hrightPositive
    · right
      simp [pairMinor, reduceCoefficient, hleftFirst, hrightFirst,
        hleftPositive, hrightNegative]
      ring
    · exact (hrightSecond hrightZero).elim
    · exact (hsecond (hleftPositive.trans hrightPositive.symm)).elim

omit [Fintype Row] [DecidableEq Row] in
/-- Equal ternary supports have identical coefficient parity at every coordinate. -/
theorem scalarParity_reduceCoefficient_eq_of_same_support
    (exponent : ℕ) (left right : Row → ℤ)
    (hleftTernary : SISBoundary.IsTernary left)
    (hrightTernary : SISBoundary.IsTernary right)
    (hsupport : SameSupport left right) (row : Row) :
    TGSW.RingSquare.PreimageCompiler.PowerOfTwoLifting.scalarParity exponent
        (reduceCoefficient (2 ^ (exponent + 1)) left row) =
      TGSW.RingSquare.PreimageCompiler.PowerOfTwoLifting.scalarParity exponent
        (reduceCoefficient (2 ^ (exponent + 1)) right row) := by
  rcases hleftTernary row with hleftNegative | hleftZero | hleftPositive
  · rcases hrightTernary row with hrightNegative | hrightZero | hrightPositive
    · simp [reduceCoefficient, hleftNegative, hrightNegative,
        TGSW.RingSquare.PreimageCompiler.PowerOfTwoLifting.scalarParity]
    · have hleftZero := (hsupport row).mpr hrightZero
      omega
    · simp [reduceCoefficient, hleftNegative, hrightPositive,
        TGSW.RingSquare.PreimageCompiler.PowerOfTwoLifting.scalarParity]
  · have hrightZero := (hsupport row).mp hleftZero
    simp [reduceCoefficient, hleftZero, hrightZero]
  · rcases hrightTernary row with hrightNegative | hrightZero | hrightPositive
    · simp [reduceCoefficient, hleftPositive, hrightNegative,
        TGSW.RingSquare.PreimageCompiler.PowerOfTwoLifting.scalarParity]
    · have hleftZero := (hsupport row).mpr hrightZero
      omega
    · simp [reduceCoefficient, hleftPositive, hrightPositive,
        TGSW.RingSquare.PreimageCompiler.PowerOfTwoLifting.scalarParity]

end PairClassification

end

end FormalProof4FHE.TFHE.TFHEShortPreimageSecondMoment
