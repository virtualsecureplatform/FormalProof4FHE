/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import Mathlib.Analysis.Real.Sqrt
import VCVio.EvalDist.TVDist
import VCVio.OracleComp.Constructions.SampleableType

/-!
# A Finite Leftover Hash Lemma

This file develops the finite, information-theoretic form of the leftover hash lemma used by
Regev encryption.  The statement is phrased directly for VCVio `ProbComp` computations and
two-universal hash families over finite types.
-/

open BigOperators OracleComp

namespace FormalProof4FHE.LeftoverHash

/-- Collision probability of a finite probabilistic computation. -/
noncomputable def collisionProbability {α : Type} [Fintype α] (p : ProbComp α) : ℝ :=
  ∑ x, Pr[= x | p].toReal ^ 2

/-- A family is two-universal when distinct inputs collide for at most a uniform fraction of
the seeds.  This cardinal formulation avoids any choice of probability representation. -/
def IsTwoUniversal (Seed Input Output : Type)
    [Fintype Seed] [Fintype Output] [DecidableEq Output]
    (hash : Seed → Input → Output) : Prop :=
  ∀ x y, x ≠ y →
    (Finset.univ.filter fun seed : Seed => hash seed x = hash seed y).card *
        Fintype.card Output ≤ Fintype.card Seed

/-- Joint distribution of a public hash seed and the hash of a uniform input. -/
def hashed {Seed Input Output : Type}
    [SampleableType Seed] [SampleableType Input]
    (hash : Seed → Input → Output) : ProbComp (Seed × Output) := do
  let seed ← $ᵗ Seed
  let input ← $ᵗ Input
  return (seed, hash seed input)

/-- The ideal joint distribution consists of an independent uniform seed and output. -/
def ideal {Seed Output : Type}
    [SampleableType Seed] [SampleableType Output] : ProbComp (Seed × Output) :=
  $ᵗ (Seed × Output)

/-- For finite, non-failing computations, VCVio total-variation distance is the usual half of
the sum of pointwise absolute probability differences. -/
theorem tvDist_eq_half_sum_abs {α : Type} [Fintype α]
    (p q : ProbComp α) :
    tvDist p q =
      (1 / 2 : ℝ) * ∑ x, |Pr[= x | p].toReal - Pr[= x | q].toReal| := by
  classical
  rw [tvDist, SPMF.tvDist, PMF.tvDist, PMF.etvDist]
  rw [tsum_option _ ENNReal.summable]
  have hp : (𝒟[p]).toPMF none = 0 := probFailure_eq_zero (mx := p)
  have hq : (𝒟[q]).toPMF none = 0 := probFailure_eq_zero (mx := q)
  rw [hp, hq, ENNReal.absDiff_self, zero_add, tsum_fintype, ENNReal.toReal_div]
  rw [ENNReal.toReal_sum (fun x _ ↦ by
    exact ne_top_of_le_ne_top
      (ENNReal.add_ne_top.mpr ⟨PMF.apply_ne_top _ _, PMF.apply_ne_top _ _⟩)
      (ENNReal.absDiff_le_add _ _))]
  simp only [ENNReal.toReal_ofNat]
  simp_rw [ENNReal.absDiff_toReal (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)]
  simp only [← SPMF.apply_eq_toPMF_some, ← probOutput_def]
  ring

/-- Collision probability controls distance from uniform.  This is the analytic core of the
leftover hash lemma. -/
theorem tvDist_uniform_le_of_collision {α : Type}
    [Fintype α] [Nonempty α] [SampleableType α]
    (p : ProbComp α) (ε : ℝ)
    (hcollision : collisionProbability p ≤
      (1 + ε) / Fintype.card α) :
    tvDist p ($ᵗ α) ≤ Real.sqrt ε / 2 := by
  classical
  let N : ℝ := Fintype.card α
  have hN : 0 < N := by
    have hcard : 0 < Fintype.card α := Fintype.card_pos
    change (0 : ℝ) < (Fintype.card α : ℝ)
    exact_mod_cast hcard
  have hmass : (∑ x, Pr[= x | p].toReal) = 1 := by
    rw [← ENNReal.toReal_sum (fun x _ ↦
      ne_top_of_le_ne_top ENNReal.one_ne_top (probOutput_le_one (mx := p) (x := x))),
      sum_probOutput_eq_one (by simp), ENNReal.toReal_one]
  have huniform : ∀ x : α, Pr[= x | ($ᵗ α : ProbComp α)].toReal = N⁻¹ := by
    intro x
    simp [N, ENNReal.toReal_inv]
  have hdeviation :
      (∑ x, (Pr[= x | p].toReal - N⁻¹) ^ 2) =
        collisionProbability p - N⁻¹ := by
    simp only [sub_sq, collisionProbability, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Finset.sum_mul, ← Finset.mul_sum, hmass]
    change (∑ x, Pr[= x | p].toReal ^ 2) - 2 * 1 * N⁻¹ + N * N⁻¹ ^ 2 =
      (∑ x, Pr[= x | p].toReal ^ 2) - N⁻¹
    field_simp
    ring
  have hdeviation_le :
      (∑ x, (Pr[= x | p].toReal - N⁻¹) ^ 2) ≤ ε / N := by
    rw [hdeviation]
    have hc : collisionProbability p ≤ (1 + ε) / N := by simpa [N] using hcollision
    apply (sub_le_iff_le_add).2
    calc
      collisionProbability p ≤ (1 + ε) / N := hc
      _ = ε / N + N⁻¹ := by field_simp; ring
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : α ↦ (1 : ℝ))
    (fun x ↦ |Pr[= x | p].toReal - N⁻¹|)
  have hsquare :
      (∑ x, |Pr[= x | p].toReal - N⁻¹|) ^ 2 ≤ ε := by
    calc
      (∑ x, |Pr[= x | p].toReal - N⁻¹|) ^ 2
          ≤ N * ∑ x, (Pr[= x | p].toReal - N⁻¹) ^ 2 := by
            simpa [N, sq_abs] using hcauchy
      _ ≤ N * (ε / N) := mul_le_mul_of_nonneg_left hdeviation_le hN.le
      _ = ε := by field_simp
  have hsum : (∑ x, |Pr[= x | p].toReal - N⁻¹|) ≤ Real.sqrt ε :=
    Real.le_sqrt_of_sq_le hsquare
  rw [tvDist_eq_half_sum_abs]
  simp_rw [huniform]
  nlinarith

/-- Point probability of the joint hashed distribution, expressed by the size of a hash fiber. -/
theorem probOutput_hashed {Seed Input Output : Type}
    [Fintype Seed] [SampleableType Seed]
    [Fintype Input] [SampleableType Input]
    [DecidableEq Output]
    (hash : Seed → Input → Output) (seed : Seed) (output : Output) :
    Pr[= (seed, output) | hashed hash] =
      (Fintype.card Seed : ENNReal)⁻¹ * (Fintype.card Input : ENNReal)⁻¹ *
        ((Finset.univ.filter fun input : Input => hash seed input = output).card : ENNReal) := by
  classical
  simp [hashed, probOutput_bind_eq_sum_fintype, probOutput_map_eq_sum_fintype_ite,
    mul_assoc]
  rw [Finset.sum_eq_single seed]
  · simp [eq_comm]
    ring
  · intro other _ hne
    simp [hne.symm]
  · simp

/-- Squared hash-fiber sizes count ordered pairs of inputs that collide. -/
theorem sum_fiber_card_sq_eq {Input Output : Type}
    [Fintype Input] [Fintype Output] [DecidableEq Output]
    (hash : Input → Output) :
    (∑ output, ((Finset.univ.filter fun input : Input => hash input = output).card : ℝ) ^ 2) =
      ∑ x, ∑ y, if hash x = hash y then (1 : ℝ) else 0 := by
  classical
  simp_rw [show ∀ output,
      ((Finset.univ.filter fun input : Input => hash input = output).card : ℝ) =
        ∑ input, if hash input = output then (1 : ℝ) else 0 by
    intro output
    simp]
  simp_rw [pow_two, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy : hash x = hash y
  · simp [hxy]
  · simp [hxy]

/-- The second-moment counting bound supplied by two-universality. -/
theorem sum_fiber_card_sq_le {Seed Input Output : Type}
    [Fintype Seed] [Fintype Input]
    [Fintype Output] [Nonempty Output] [DecidableEq Output]
    (hash : Seed → Input → Output)
    (huniversal : IsTwoUniversal Seed Input Output hash) :
    (∑ seed, ∑ output,
        ((Finset.univ.filter fun input : Input => hash seed input = output).card : ℝ) ^ 2) ≤
      (Fintype.card Seed : ℝ) * Fintype.card Input +
        (Fintype.card Seed : ℝ) * (Fintype.card Input : ℝ) ^ 2 /
          Fintype.card Output := by
  classical
  let S : ℝ := Fintype.card Seed
  let I : ℝ := Fintype.card Input
  let O : ℝ := Fintype.card Output
  have hO : 0 < O := by
    have hcard : 0 < Fintype.card Output := Fintype.card_pos
    change (0 : ℝ) < (Fintype.card Output : ℝ)
    exact_mod_cast hcard
  have hreorder :
      (∑ seed, ∑ output,
          ((Finset.univ.filter fun input : Input => hash seed input = output).card : ℝ) ^ 2) =
        ∑ x, ∑ y,
          ((Finset.univ.filter fun seed : Seed => hash seed x = hash seed y).card : ℝ) := by
    simp_rw [sum_fiber_card_sq_eq]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro y _
    simp
  rw [hreorder]
  calc
    (∑ x, ∑ y,
        ((Finset.univ.filter fun seed : Seed => hash seed x = hash seed y).card : ℝ))
        ≤ ∑ x, ∑ y, if x = y then S else S / O := by
          gcongr with x y
          by_cases hxy : x = y
          · subst y
            simp [S]
          · rw [if_neg hxy]
            apply (le_div_iff₀ hO).2
            have hnat := huniversal x y hxy
            change
              ((Finset.univ.filter fun seed : Seed => hash seed x = hash seed y).card : ℝ) *
                  (Fintype.card Output : ℝ) ≤ (Fintype.card Seed : ℝ)
            exact_mod_cast hnat
    _ ≤ ∑ x, (S + I * (S / O)) := by
          gcongr with x
          calc
            (∑ y, if x = y then S else S / O)
                ≤ ∑ y, ((if x = y then S else 0) + S / O) := by
                  gcongr with y
                  by_cases hxy : x = y
                  · simp [hxy, div_nonneg (by positivity : 0 ≤ S) hO.le]
                  · simp [hxy]
            _ = S + I * (S / O) := by
                  rw [Finset.sum_add_distrib, Fintype.sum_ite_eq, Finset.sum_const]
                  simp [I]
    _ = S * I + S * I ^ 2 / O := by
          simp [I]
          ring
    _ = (Fintype.card Seed : ℝ) * Fintype.card Input +
          (Fintype.card Seed : ℝ) * (Fintype.card Input : ℝ) ^ 2 /
            Fintype.card Output := by rfl

/-- Finite leftover hash lemma.  A two-universal family extracting from a uniform finite input
has joint seed/output distance at most `sqrt (|Output| / |Input|) / 2` from uniform. -/
theorem leftover_hash_lemma {Seed Input Output : Type}
    [Fintype Seed] [Nonempty Seed] [SampleableType Seed]
    [Fintype Input] [Nonempty Input] [SampleableType Input]
    [Fintype Output] [Nonempty Output] [DecidableEq Output] [SampleableType Output]
    (hash : Seed → Input → Output)
    (huniversal : IsTwoUniversal Seed Input Output hash) :
    tvDist (hashed hash) (ideal (Seed := Seed) (Output := Output)) ≤
      Real.sqrt (Fintype.card Output / Fintype.card Input) / 2 := by
  classical
  let S : ℝ := Fintype.card Seed
  let I : ℝ := Fintype.card Input
  let O : ℝ := Fintype.card Output
  have hcollision_eq :
      collisionProbability (hashed hash) =
        (S⁻¹ * I⁻¹) ^ 2 *
          ∑ seed, ∑ output,
            ((Finset.univ.filter fun input : Input => hash seed input = output).card : ℝ) ^ 2 := by
    unfold collisionProbability
    rw [Fintype.sum_prod_type]
    simp_rw [probOutput_hashed hash, ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_natCast]
    dsimp [S, I]
    simp_rw [mul_pow]
    simp_rw [← Finset.mul_sum]
  have hS : 0 < S := by
    have hcard : 0 < Fintype.card Seed := Fintype.card_pos
    change (0 : ℝ) < (Fintype.card Seed : ℝ)
    exact_mod_cast hcard
  have hI : 0 < I := by
    have hcard : 0 < Fintype.card Input := Fintype.card_pos
    change (0 : ℝ) < (Fintype.card Input : ℝ)
    exact_mod_cast hcard
  have hO : 0 < O := by
    have hcard : 0 < Fintype.card Output := Fintype.card_pos
    change (0 : ℝ) < (Fintype.card Output : ℝ)
    exact_mod_cast hcard
  have hsecond := sum_fiber_card_sq_le hash huniversal
  have hcollision :
      collisionProbability (hashed hash) ≤
        (1 + O / I) / Fintype.card (Seed × Output) := by
    rw [hcollision_eq]
    calc
      (S⁻¹ * I⁻¹) ^ 2 *
          ∑ seed, ∑ output,
            ((Finset.univ.filter fun input : Input => hash seed input = output).card : ℝ) ^ 2
          ≤ (S⁻¹ * I⁻¹) ^ 2 * (S * I + S * I ^ 2 / O) :=
            mul_le_mul_of_nonneg_left hsecond (sq_nonneg _)
      _ = (1 + O / I) / (S * O) := by field_simp; ring
      _ = (1 + O / I) / Fintype.card (Seed × Output) := by
            simp [S, O, Fintype.card_prod]
  simpa [ideal, O, I] using
    (tvDist_uniform_le_of_collision (hashed hash) (O / I) hcollision)

/-! ## Binary subset-sum hashing -/

/-- Hash a bit vector by summing the selected entries of a public table. -/
def binarySubsetSum {D G : Type} [Fintype D] [DecidableEq D] [AddCommMonoid G]
    (table : D → G) (bits : D → Bool) : G :=
  ∑ i, if bits i then table i else 0

/-- Split a function table into one distinguished coordinate and all remaining coordinates. -/
def tableEquivAt {D G : Type} [DecidableEq D] (i : D) :
    (D → G) ≃ G × ({j : D // j ≠ i} → G) where
  toFun table := (table i, fun j ↦ table j)
  invFun pair := fun j ↦ if h : j = i then pair.1 else pair.2 ⟨j, h⟩
  left_inv table := by
    funext j
    by_cases h : j = i
    · subst j
      simp
    · simp [h]
  right_inv pair := by
    apply Prod.ext
    · simp
    · funext j
      simp [j.property]

/-- Isolate one coordinate in a binary subset sum. -/
theorem binarySubsetSum_eq_head_add {D G : Type}
    [Fintype D] [DecidableEq D] [AddCommMonoid G]
    (table : D → G) (bits : D → Bool) (i : D) :
    binarySubsetSum table bits =
      (if bits i then table i else 0) +
        ∑ j ∈ Finset.univ.erase i, if bits j then table j else 0 := by
  exact (Finset.add_sum_erase Finset.univ
    (fun j ↦ if bits j then table j else 0) (Finset.mem_univ i)).symm

/-- The contribution of all coordinates except `i` to the difference of two subset sums. -/
def binaryRestDifference {D G : Type}
    [Fintype D] [DecidableEq D] [AddCommGroup G]
    (i : D) (rest : {j : D // j ≠ i} → G) (x y : D → Bool) : G :=
  let table := (tableEquivAt (G := G) i).symm (0, rest)
  (∑ j ∈ Finset.univ.erase i, if x j then table j else 0) -
    ∑ j ∈ Finset.univ.erase i, if y j then table j else 0

/-- The unique value of coordinate `i` that makes the two subset sums collide. -/
def binaryCollisionCoordinate {D G : Type}
    [Fintype D] [DecidableEq D] [AddCommGroup G]
    (i : D) (rest : {j : D // j ≠ i} → G) (x y : D → Bool) : G :=
  if x i then -binaryRestDifference i rest x y else binaryRestDifference i rest x y

/-- Once two bit vectors differ at `i`, their subset sums collide for exactly one value of the
table entry at `i`. -/
theorem binarySubsetSum_collision_iff {D G : Type}
    [Fintype D] [DecidableEq D] [AddCommGroup G]
    (i : D) (x y : D → Bool) (hdiff : x i ≠ y i)
    (u : G) (rest : {j : D // j ≠ i} → G) :
    binarySubsetSum ((tableEquivAt (G := G) i).symm (u, rest)) x =
        binarySubsetSum ((tableEquivAt (G := G) i).symm (u, rest)) y ↔
      u = binaryCollisionCoordinate i rest x y := by
  rw [binarySubsetSum_eq_head_add, binarySubsetSum_eq_head_add]
  have hi : ((tableEquivAt (G := G) i).symm (u, rest)) i = u := by simp [tableEquivAt]
  rw [hi]
  unfold binaryCollisionCoordinate binaryRestDifference
  have hrest (bits : D → Bool) :
      (∑ j ∈ Finset.univ.erase i,
          if bits j then ((tableEquivAt (G := G) i).symm (u, rest)) j else 0) =
        ∑ j ∈ Finset.univ.erase i,
          if bits j then ((tableEquivAt (G := G) i).symm (0, rest)) j else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp [tableEquivAt, hji]
  rw [hrest x, hrest y]
  cases hx : x i <;> cases hy : y i
  · simp [hx, hy] at hdiff
  · simp only [Bool.false_eq_true, ↓reduceIte, zero_add]
    constructor
    · intro h
      exact eq_sub_iff_add_eq.mpr h.symm
    · intro h
      exact (eq_sub_iff_add_eq.mp h).symm
  · simp only [Bool.false_eq_true, zero_add, ↓reduceIte, neg_sub]
    constructor
    · intro h
      exact eq_sub_iff_add_eq.mpr h
    · intro h
      exact eq_sub_iff_add_eq.mp h
  · simp [hx, hy] at hdiff

/-- The colliding tables for two distinct bit vectors are in bijection with the table entries away
from any coordinate on which the vectors differ. -/
noncomputable def binaryCollisionEquivRest {D G : Type}
    [Fintype D] [DecidableEq D] [AddCommGroup G]
    (i : D) (x y : D → Bool) (hdiff : x i ≠ y i) :
    {table : D → G // binarySubsetSum table x = binarySubsetSum table y} ≃
      ({j : D // j ≠ i} → G) where
  toFun table := ((tableEquivAt (G := G) i) table).2
  invFun rest :=
    ⟨(tableEquivAt (G := G) i).symm
        (binaryCollisionCoordinate i rest x y, rest),
      (binarySubsetSum_collision_iff i x y hdiff _ _).2 rfl⟩
  left_inv table := by
    apply Subtype.ext
    apply (tableEquivAt (G := G) i).injective
    simp only [Equiv.apply_symm_apply]
    apply Prod.ext
    · change binaryCollisionCoordinate i
          ((tableEquivAt (G := G) i) table).2 x y = table.val i
      have hcollision :
          binarySubsetSum
              ((tableEquivAt (G := G) i).symm
                (((tableEquivAt (G := G) i) table).1,
                  ((tableEquivAt (G := G) i) table).2)) x =
            binarySubsetSum
              ((tableEquivAt (G := G) i).symm
                (((tableEquivAt (G := G) i) table).1,
                  ((tableEquivAt (G := G) i) table).2)) y := by
        simpa using table.property
      exact ((binarySubsetSum_collision_iff i x y hdiff _ _).1 hcollision).symm
    · rfl
  right_inv rest := by
    change ((tableEquivAt (G := G) i)
      ((tableEquivAt (G := G) i).symm
        (binaryCollisionCoordinate i rest x y, rest))).2 = rest
    simp

/-- The random-table binary subset-sum family is two-universal over every finite additive
commutative group. -/
theorem binarySubsetSum_isTwoUniversal {D G : Type}
    [Fintype D] [DecidableEq D]
    [Fintype G] [DecidableEq G] [AddCommGroup G] :
    IsTwoUniversal (D → G) (D → Bool) G binarySubsetSum := by
  intro x y hxy
  have hexists : ∃ i, x i ≠ y i := by
    by_contra h
    apply hxy
    funext i
    by_contra hi
    exact h ⟨i, hi⟩
  obtain ⟨i, hdiff⟩ := hexists
  have hcollisionCard :
      (Finset.univ.filter fun table : D → G =>
          binarySubsetSum table x = binarySubsetSum table y).card =
        Fintype.card ({j : D // j ≠ i} → G) := by
    rw [← Fintype.card_subtype]
    exact Fintype.card_congr (binaryCollisionEquivRest i x y hdiff)
  apply Nat.le_of_eq
  calc
    (Finset.univ.filter fun table : D → G =>
        binarySubsetSum table x = binarySubsetSum table y).card * Fintype.card G
        = Fintype.card ({j : D // j ≠ i} → G) * Fintype.card G := by
          rw [hcollisionCard]
    _ = Fintype.card G * Fintype.card ({j : D // j ≠ i} → G) := Nat.mul_comm _ _
    _ = Fintype.card (G × ({j : D // j ≠ i} → G)) := by simp
    _ = Fintype.card (D → G) :=
      (Fintype.card_congr (tableEquivAt (G := G) i)).symm

end FormalProof4FHE.LeftoverHash
