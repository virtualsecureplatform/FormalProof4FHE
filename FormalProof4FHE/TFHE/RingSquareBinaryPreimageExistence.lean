/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.LeftoverHash
import FormalProof4FHE.TFHE.BootstrappingCorrectness
import FormalProof4FHE.TFHE.RingSquareUnitMaskObstruction

/-!
# Binary Short-Preimage Existence for the Ring-Square Compiler

The counting obstruction for the `RGSW_S(-S)` compiler is nearly tight at the level of
information-theoretic existence.  Reserve one source mask with coefficient one and use binary
weights for all remaining masks.  The reserved mask is a uniform additive offset, while binary
subset sum on the remaining masks is a two-universal hash family.

A finite second-moment argument proves that a fixed target has a binary preimage for at least an
`I / (I + O)` fraction of mask tables, where `I` is the number of binary choices and `O` is the
ring cardinality.  Thus `m` extra masks give failure at most approximately `|R| / 2^m`.

This is an existence theorem, not an efficient algorithm for finding the subset.  Efficient
inhomogeneous subset-sum/Ring-SIS search remains the computational gap in the circular-security
reduction.
-/

open OracleComp
open scoped BigOperators ENNReal

namespace FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.BinaryPreimageExistence

noncomputable section

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing

/-! ## A generic anchored two-universal family -/

/-- Add a uniform offset to an arbitrary finite hash family. -/
def anchoredHash {Seed Input Output : Type} [Add Output]
    (hash : Seed → Input → Output) (seed : Output × Seed) (input : Input) : Output :=
  seed.1 + hash seed.2 input

/-- Size of the fiber above one fixed target for an anchored seed. -/
def anchoredFiberCard {Seed Input Output : Type}
    [Fintype Input] [DecidableEq Output] [Add Output]
    (hash : Seed → Input → Output) (target : Output) (seed : Output × Seed) : ℕ :=
  (Finset.univ.filter fun input : Input ↦ anchoredHash hash seed input = target).card

/-- Ordinary fiber size of the unanchored family. -/
def fiberCard {Seed Input Output : Type}
    [Fintype Input] [DecidableEq Output]
    (hash : Seed → Input → Output) (seed : Seed) (output : Output) : ℕ :=
  (Finset.univ.filter fun input : Input ↦ hash seed input = output).card

/-- The anchored target fiber is the ordinary fiber above `target - offset`. -/
theorem anchoredFiberCard_eq_fiberCard_target_sub
    {Seed Input Output : Type}
    [Fintype Input] [DecidableEq Output] [AddCommGroup Output]
    (hash : Seed → Input → Output) (target offset : Output) (seed : Seed) :
    anchoredFiberCard hash target (offset, seed) =
      fiberCard hash seed (target - offset) := by
  classical
  unfold anchoredFiberCard fiberCard anchoredHash
  apply congrArg Finset.card
  ext input
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    exact (eq_sub_iff_add_eq.mpr (by simpa [add_comm] using h))
  · intro h
    have := eq_sub_iff_add_eq.mp h
    simpa [add_comm] using this

/-- Summing a fixed anchored fiber over every offset is just summing all ordinary fibers. -/
theorem sum_offset_anchoredFiberCard_sq_eq_sum_fiberCard_sq
    {Seed Input Output : Type}
    [Fintype Input] [DecidableEq Output] [Fintype Output] [AddCommGroup Output]
    (hash : Seed → Input → Output) (target : Output) (seed : Seed) :
    (∑ offset : Output, (anchoredFiberCard hash target (offset, seed) : ℝ) ^ 2) =
      ∑ output : Output, (fiberCard hash seed output : ℝ) ^ 2 := by
  simp_rw [anchoredFiberCard_eq_fiberCard_target_sub]
  exact Fintype.sum_equiv (Equiv.subLeft target) _ _ fun _ ↦ rfl

/-- Exact first moment of one fixed anchored target fiber. -/
theorem sum_anchoredFiberCard_eq
    {Seed Input Output : Type}
    [Fintype Seed] [Fintype Input] [DecidableEq Output]
    [Fintype Output] [AddCommGroup Output]
    (hash : Seed → Input → Output) (target : Output) :
    (∑ seed : Output × Seed, (anchoredFiberCard hash target seed : ℝ)) =
      (Fintype.card Seed : ℝ) * Fintype.card Input := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  calc
    (∑ seed : Seed, ∑ offset : Output,
        (anchoredFiberCard hash target (offset, seed) : ℝ)) =
        ∑ _seed : Seed, (Fintype.card Input : ℝ) := by
      apply Finset.sum_congr rfl
      intro seed _
      simp_rw [anchoredFiberCard_eq_fiberCard_target_sub]
      rw [Fintype.sum_equiv (Equiv.subLeft target)
        (fun offset ↦ (fiberCard hash seed (target - offset) : ℝ))
        (fun output ↦ (fiberCard hash seed output : ℝ)) (fun _ ↦ rfl)]
      unfold fiberCard
      simp_rw [show ∀ output,
          ((Finset.univ.filter fun input : Input ↦ hash seed input = output).card : ℝ) =
            ∑ input : Input, if hash seed input = output then (1 : ℝ) else 0 by
        intro output
        simp]
      rw [Finset.sum_comm]
      simp
    _ = (Fintype.card Seed : ℝ) * Fintype.card Input := by simp

/-- The fixed-target anchored second moment is exactly the all-output unanchored second moment. -/
theorem sum_anchoredFiberCard_sq_eq
    {Seed Input Output : Type}
    [Fintype Seed] [Fintype Input] [DecidableEq Output]
    [Fintype Output] [AddCommGroup Output]
    (hash : Seed → Input → Output) (target : Output) :
    (∑ seed : Output × Seed, (anchoredFiberCard hash target seed : ℝ) ^ 2) =
      ∑ seed : Seed, ∑ output : Output, (fiberCard hash seed output : ℝ) ^ 2 := by
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro seed _
  exact sum_offset_anchoredFiberCard_sq_eq_sum_fiberCard_sq hash target seed

/-- Number of anchored seeds whose fixed-target fiber is nonempty. -/
def nonemptyAnchoredFiberCount
    {Seed Input Output : Type}
    [Fintype Seed] [Fintype Input] [DecidableEq Output]
    [Fintype Output] [Add Output]
    (hash : Seed → Input → Output) (target : Output) : ℕ :=
  (Finset.univ.filter fun seed : Output × Seed ↦
    anchoredFiberCard hash target seed ≠ 0).card

theorem anchoredFiberCard_ne_zero_iff_exists
    {Seed Input Output : Type}
    [Fintype Input] [DecidableEq Output] [Add Output]
    (hash : Seed → Input → Output) (target : Output) (seed : Output × Seed) :
    anchoredFiberCard hash target seed ≠ 0 ↔
      ∃ input, anchoredHash hash seed input = target := by
  classical
  unfold anchoredFiberCard
  rw [Finset.card_ne_zero, Finset.nonempty_iff_ne_empty]
  simp

/-- Cauchy--Schwarz lower-bounds the number of nonempty anchored fibers by their first and
second moments. -/
theorem sum_anchoredFiberCard_sq_le_nonempty_mul_secondMoment
    {Seed Input Output : Type}
    [Fintype Seed] [Fintype Input] [DecidableEq Output]
    [Fintype Output] [Add Output]
    (hash : Seed → Input → Output) (target : Output) :
    (∑ seed : Output × Seed, (anchoredFiberCard hash target seed : ℝ)) ^ 2 ≤
      (nonemptyAnchoredFiberCount hash target : ℝ) *
        ∑ seed : Output × Seed, (anchoredFiberCard hash target seed : ℝ) ^ 2 := by
  classical
  let indicator : Output × Seed → ℝ := fun seed ↦
    if anchoredFiberCard hash target seed = 0 then 0 else 1
  let value : Output × Seed → ℝ := fun seed ↦ anchoredFiberCard hash target seed
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ indicator value
  have hleft : (∑ seed : Output × Seed, indicator seed * value seed) =
      ∑ seed : Output × Seed, (anchoredFiberCard hash target seed : ℝ) := by
    apply Finset.sum_congr rfl
    intro seed _
    by_cases hzero : anchoredFiberCard hash target seed = 0
    · simp [indicator, value, hzero]
    · simp [indicator, value, hzero]
  have hindicator : (∑ seed : Output × Seed, indicator seed ^ 2) =
      (nonemptyAnchoredFiberCount hash target : ℝ) := by
    unfold nonemptyAnchoredFiberCount
    calc
      (∑ seed : Output × Seed, indicator seed ^ 2) =
          ∑ seed : Output × Seed,
            if anchoredFiberCard hash target seed ≠ 0 then (1 : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro seed _
        by_cases hzero : anchoredFiberCard hash target seed = 0
        · simp [indicator, hzero]
        · simp [indicator, hzero]
      _ = ((Finset.univ.filter fun seed : Output × Seed ↦
          anchoredFiberCard hash target seed ≠ 0).card : ℝ) := by
        simpa using
          (Finset.sum_boole (R := ℝ)
            (fun seed : Output × Seed ↦ anchoredFiberCard hash target seed ≠ 0)
            (Finset.univ : Finset (Output × Seed)))
  have hvalue : (∑ seed : Output × Seed, value seed ^ 2) =
      ∑ seed : Output × Seed, (anchoredFiberCard hash target seed : ℝ) ^ 2 := by
    rfl
  rwa [hleft, hindicator, hvalue] at hcauchy

/-- Cross-multiplied second-moment existence bound for any anchored two-universal family. -/
theorem card_seed_mul_card_input_le_nonempty_mul_add
    {Seed Input Output : Type}
    [Fintype Seed] [Nonempty Seed]
    [Fintype Input] [Nonempty Input]
    [Fintype Output] [Nonempty Output] [DecidableEq Output]
    [AddCommGroup Output]
    (hash : Seed → Input → Output)
    (huniversal : LeftoverHash.IsTwoUniversal Seed Input Output hash)
    (target : Output) :
    (Fintype.card (Output × Seed) : ℝ) * Fintype.card Input ≤
      (nonemptyAnchoredFiberCount hash target : ℝ) *
        ((Fintype.card Output : ℝ) + Fintype.card Input) := by
  let R : ℝ := Fintype.card Seed
  let I : ℝ := Fintype.card Input
  let O : ℝ := Fintype.card Output
  let C : ℝ := nonemptyAnchoredFiberCount hash target
  have hR : 0 < R := by
    dsimp [R]
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hI : 0 < I := by
    dsimp [I]
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hO : 0 < O := by
    dsimp [O]
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hmoment := sum_anchoredFiberCard_sq_le_nonempty_mul_secondMoment hash target
  rw [sum_anchoredFiberCard_eq hash target,
    sum_anchoredFiberCard_sq_eq hash target] at hmoment
  have hsecond := LeftoverHash.sum_fiber_card_sq_le hash huniversal
  change
    (∑ seed : Seed, ∑ output : Output,
      (fiberCard hash seed output : ℝ) ^ 2) ≤ R * I + R * I ^ 2 / O at hsecond
  have hcombined : (R * I) ^ 2 ≤ C * (R * I + R * I ^ 2 / O) :=
    hmoment.trans (mul_le_mul_of_nonneg_left hsecond (by positivity))
  have hscaled := mul_le_mul_of_nonneg_left hcombined hO.le
  have hfactorLeft : O * (R * I) ^ 2 = (R * I) * (O * R * I) := by ring
  have hfactorRight :
      O * (C * (R * I + R * I ^ 2 / O)) =
        (R * I) * (C * (O + I)) := by
    field_simp
  rw [hfactorLeft, hfactorRight] at hscaled
  have hRI : 0 < R * I := mul_pos hR hI
  have hcross : O * R * I ≤ C * (O + I) :=
    le_of_mul_le_mul_left hscaled hRI
  simpa [R, I, O, C, Fintype.card_prod, mul_assoc, mul_left_comm, mul_comm,
    add_comm] using hcross

/-- Probability form: at least an `I/(I+O)` fraction of anchored seeds hit any fixed target. -/
theorem card_input_div_add_le_probEvent_exists_anchoredPreimage_toReal
    {Seed Input Output : Type}
    [Fintype Seed] [Nonempty Seed]
    [Fintype Input] [Nonempty Input]
    [Fintype Output] [Nonempty Output] [DecidableEq Output]
    [AddCommGroup Output] [SampleableType (Output × Seed)]
    (hash : Seed → Input → Output)
    (huniversal : LeftoverHash.IsTwoUniversal Seed Input Output hash)
    (target : Output) :
    (Fintype.card Input : ℝ) /
        ((Fintype.card Input : ℝ) + Fintype.card Output) ≤
      (Pr[(fun seed : Output × Seed ↦
          ∃ input, anchoredHash hash seed input = target) |
        ($ᵗ (Output × Seed))]).toReal := by
  classical
  let I : ℝ := Fintype.card Input
  let O : ℝ := Fintype.card Output
  let S : ℝ := Fintype.card (Output × Seed)
  let C : ℝ := nonemptyAnchoredFiberCount hash target
  have hI : 0 < I := by
    dsimp [I]
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hO : 0 < O := by
    dsimp [O]
    exact_mod_cast Fintype.card_pos_iff.mpr inferInstance
  have hS : 0 < S := by
    dsimp [S]
    exact_mod_cast Fintype.card_pos
  have hcross := card_seed_mul_card_input_le_nonempty_mul_add
    hash huniversal target
  change S * I ≤ C * (O + I) at hcross
  have hratio : I / (I + O) ≤ C / S := by
    apply (div_le_div_iff₀ (add_pos hI hO) hS).2
    simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using hcross
  have hprobability :
      (Pr[(fun seed : Output × Seed ↦
          ∃ input, anchoredHash hash seed input = target) |
        ($ᵗ (Output × Seed))]).toReal = C / S := by
    rw [probEvent_uniformSample, ENNReal.toReal_div]
    simp only [ENNReal.toReal_natCast]
    have hfilter :
        (Finset.univ.filter fun seed : Output × Seed ↦
          ∃ input, anchoredHash hash seed input = target) =
        Finset.univ.filter fun seed : Output × Seed ↦
          anchoredFiberCard hash target seed ≠ 0 := by
      ext seed
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact (anchoredFiberCard_ne_zero_iff_exists hash target seed).symm
    rw [hfilter]
    rfl
  rw [hprobability]
  exact hratio

/-- Binary subset sums instantiate the generic anchored-preimage bound over every finite additive
commutative group. -/
theorem binarySubsetSum_card_input_div_add_le_exists_toReal
    {D G : Type}
    [Fintype D] [DecidableEq D]
    [Fintype G] [Nonempty G] [DecidableEq G] [AddCommGroup G]
    [SampleableType (G × (D → G))]
    (target : G) :
    (Fintype.card (D → Bool) : ℝ) /
        ((Fintype.card (D → Bool) : ℝ) + Fintype.card G) ≤
      (Pr[(fun seed : G × (D → G) ↦
          ∃ bits : D → Bool,
            anchoredHash LeftoverHash.binarySubsetSum seed bits = target) |
        ($ᵗ (G × (D → G)))]).toReal :=
  card_input_div_add_le_probEvent_exists_anchoredPreimage_toReal
    LeftoverHash.binarySubsetSum LeftoverHash.binarySubsetSum_isTwoUniversal target

/-! ## The actual level-zero mask equation -/

/-- Regard an offset and `m` subset-sum entries as the `m + 1` public source masks of the
ring-square compiler. -/
def anchoredMasks {R : Type} {extraCount : ℕ}
    (seed : R × (Fin extraCount → R)) :
    MultiSourceCounting.Vectors R (extraCount + 1) :=
  Fin.cons seed.1 seed.2

/-- Splitting off the reserved mask is a bijection between anchored seeds and complete source-mask
vectors. -/
theorem anchoredMasks_bijective {R : Type} (extraCount : ℕ) :
    Function.Bijective
      (anchoredMasks :
        (R × (Fin extraCount → R)) →
          MultiSourceCounting.Vectors R (extraCount + 1)) := by
  constructor
  · intro left right heq
    apply Prod.ext
    · simpa [anchoredMasks] using congrFun heq 0
    · funext index
      simpa [anchoredMasks] using congrFun heq index.succ
  · intro masks
    refine ⟨(masks 0, fun index ↦ masks index.succ), ?_⟩
    funext index
    refine Fin.cases ?_ (fun tail ↦ ?_) index <;> simp [anchoredMasks]

/-- Uniform anchored seeds and uniform complete mask vectors give the same probability for every
event. -/
theorem probEvent_uniform_masks_eq_anchored
    {R : Type} (extraCount : ℕ)
    [SampleableType (R × (Fin extraCount → R))]
    [SampleableType (MultiSourceCounting.Vectors R (extraCount + 1))]
    (event : MultiSourceCounting.Vectors R (extraCount + 1) → Prop) :
    Pr[event |
        ($ᵗ MultiSourceCounting.Vectors R (extraCount + 1))] =
      Pr[(fun seed : R × (Fin extraCount → R) ↦
          event (anchoredMasks seed)) |
        ($ᵗ (R × (Fin extraCount → R)))] := by
  have hmap :
      evalDist
          ((anchoredMasks :
              (R × (Fin extraCount → R)) →
                MultiSourceCounting.Vectors R (extraCount + 1)) <$>
            ($ᵗ (R × (Fin extraCount → R)))) =
        evalDist ($ᵗ MultiSourceCounting.Vectors R (extraCount + 1)) :=
    evalDist_map_bijective_uniform_cross
      (α := R × (Fin extraCount → R))
      (β := MultiSourceCounting.Vectors R (extraCount + 1))
      (anchoredMasks :
        (R × (Fin extraCount → R)) →
          MultiSourceCounting.Vectors R (extraCount + 1))
      (anchoredMasks_bijective extraCount)
  calc
    Pr[event | ($ᵗ MultiSourceCounting.Vectors R (extraCount + 1))] =
        Pr[event |
          anchoredMasks <$> ($ᵗ (R × (Fin extraCount → R)))] := by
      unfold probEvent
      rw [hmap]
    _ = _ := by
      simpa only [Function.comp_def] using
        (probEvent_map
          (mx := ($ᵗ (R × (Fin extraCount → R))))
          (f := anchoredMasks) event)

/-- The reserved mask receives coefficient one; every remaining coefficient is a bit. -/
def anchoredBinaryWeight {R : Type} [CommRing R] {extraCount : ℕ}
    (bits : Fin extraCount → Bool) :
    MultiSourceCounting.Vectors R (extraCount + 1) :=
  Fin.cons 1 fun index ↦ if bits index then 1 else 0

/-- The compiler's mask equation with anchored binary weights is exactly anchored binary
subset sum. -/
theorem maskCombination_anchoredBinaryWeight_eq
    {R : Type} [CommRing R] {extraCount : ℕ}
    (seed : R × (Fin extraCount → R)) (bits : Fin extraCount → Bool) :
    MultiSourceCounting.maskCombination (anchoredBinaryWeight bits) (anchoredMasks seed) =
      anchoredHash LeftoverHash.binarySubsetSum seed bits := by
  classical
  simp [MultiSourceCounting.maskCombination, anchoredBinaryWeight, anchoredMasks,
    anchoredHash, LeftoverHash.binarySubsetSum, Fin.sum_univ_succ]

/-- Direct mask-equation form of the binary-preimage probability bound. -/
theorem binaryMaskCombination_card_input_div_add_le_exists_toReal
    {R : Type} (extraCount : ℕ)
    [Fintype R] [Nonempty R] [DecidableEq R] [CommRing R]
    [SampleableType (R × (Fin extraCount → R))]
    (target : R) :
    (Fintype.card (Fin extraCount → Bool) : ℝ) /
        ((Fintype.card (Fin extraCount → Bool) : ℝ) + Fintype.card R) ≤
      (Pr[(fun seed : R × (Fin extraCount → R) ↦
          ∃ bits : Fin extraCount → Bool,
            MultiSourceCounting.maskCombination
                (anchoredBinaryWeight bits) (anchoredMasks seed) = target) |
        ($ᵗ (R × (Fin extraCount → R)))]).toReal := by
  simpa only [maskCombination_anchoredBinaryWeight_eq] using
    (binarySubsetSum_card_input_div_add_le_exists_toReal
      (D := Fin extraCount) (G := R) target)

/-! ## Production power-of-two negacyclic ring -/

/-- Every coefficient of an anchored binary weight has centered norm at most one in an arbitrary
positive-degree executable ring. -/
theorem cInfNorm_anchoredBinaryWeight_le_one
    {q degree extraCount : ℕ} [NeZero q]
    (bits : Fin extraCount → Bool) (index : Fin (extraCount + 1)) :
    LatticeCrypto.cInfNorm
        (anchoredBinaryWeight
          (R := RLWE.Rq q (degree + 1)) bits index) ≤ 1 := by
  refine Fin.cases ?_ (fun tail ↦ ?_) index
  · simpa [anchoredBinaryWeight] using
      (BootstrappingCorrectness.cInfNorm_one_le (q := q) (degree := degree))
  · cases hbit : bits tail <;>
      simp [anchoredBinaryWeight, hbit,
        BootstrappingCorrectness.cInfNorm_one_le]

/-- Positive-degree form whose degree need not be syntactically written as a successor. -/
theorem cInfNorm_anchoredBinaryWeight_le_one_of_degree_pos
    {q ringDegree extraCount : ℕ} [NeZero q]
    (ringDegree_positive : 0 < ringDegree)
    (bits : Fin extraCount → Bool) (index : Fin (extraCount + 1)) :
    LatticeCrypto.cInfNorm
        (anchoredBinaryWeight
          (R := RLWE.Rq q ringDegree) bits index) ≤ 1 := by
  obtain ⟨degree, rfl⟩ := Nat.exists_eq_succ_of_ne_zero
    (Nat.ne_of_gt ringDegree_positive)
  exact cInfNorm_anchoredBinaryWeight_le_one bits index

/-- The same norm-one certificate for the production degree `N = 2^d`. -/
theorem production_cInfNorm_anchoredBinaryWeight_le_one
    (modulusExponent degreeExponent extraCount : ℕ)
    (bits : Fin extraCount → Bool) (index : Fin (extraCount + 1)) :
    LatticeCrypto.cInfNorm
        (anchoredBinaryWeight
          (R := SingleSourceInverse.PowerOfTwo.Ring
            modulusExponent degreeExponent) bits index) ≤ 1 := by
  exact cInfNorm_anchoredBinaryWeight_le_one_of_degree_pos
    (q := 2 ^ modulusExponent)
    (ringDegree := 2 ^ degreeExponent) (pow_pos (by omega) degreeExponent)
    bits index

/-- In the production ring, `m` binary coordinates hit every fixed target for at least the
explicit fraction `2^m / (2^m + q^N)` of anchored public mask families. -/
theorem production_binaryMaskCombination_twoPow_div_add_le_existsTarget_toReal
    (modulusExponent degreeExponent extraCount : ℕ)
    (target : SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent)
    [SampleableType
      (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent ×
        (Fin extraCount →
          SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent))] :
    (((2 ^ extraCount : ℕ) : ℝ) /
        (((2 ^ extraCount : ℕ) : ℝ) +
          (((2 ^ modulusExponent) ^ (2 ^ degreeExponent) : ℕ) : ℝ))) ≤
      (Pr[(fun seed :
          SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent ×
            (Fin extraCount →
              SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent) ↦
          ∃ bits : Fin extraCount → Bool,
            MultiSourceCounting.maskCombination
                (anchoredBinaryWeight bits) (anchoredMasks seed) = target) |
        ($ᵗ (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent ×
          (Fin extraCount →
            SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent))) ]).toReal := by
  simpa only [Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
    RLWE.RingRegev.card_rq] using
    (binaryMaskCombination_card_input_div_add_le_exists_toReal
      (R := SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent)
      extraCount target)

/-- Level-zero target-one specialization of the preceding all-target theorem. -/
theorem production_binaryMaskCombination_twoPow_div_add_le_exists_toReal
    (modulusExponent degreeExponent extraCount : ℕ)
    [SampleableType
      (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent ×
        (Fin extraCount →
          SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent))] :
    (((2 ^ extraCount : ℕ) : ℝ) /
        (((2 ^ extraCount : ℕ) : ℝ) +
          (((2 ^ modulusExponent) ^ (2 ^ degreeExponent) : ℕ) : ℝ))) ≤
      (Pr[(fun seed :
          SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent ×
            (Fin extraCount →
              SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent) ↦
          ∃ bits : Fin extraCount → Bool,
            MultiSourceCounting.maskCombination
                (anchoredBinaryWeight bits) (anchoredMasks seed) = 1) |
        ($ᵗ (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent ×
          (Fin extraCount →
            SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent))) ]).toReal :=
  production_binaryMaskCombination_twoPow_div_add_le_existsTarget_toReal
    modulusExponent degreeExponent extraCount 1

/-- Fully coefficient-bounded all-target form: the same fraction of mask families has an actual
radius-one preimage in the compiler's production `BoundedWeights` type. -/
theorem production_binaryBoundedPreimage_twoPow_div_add_le_existsTarget_toReal
    (modulusExponent degreeExponent extraCount : ℕ)
    (target : SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent)
    [SampleableType
      (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent ×
        (Fin extraCount →
          SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent))] :
    (((2 ^ extraCount : ℕ) : ℝ) /
        (((2 ^ extraCount : ℕ) : ℝ) +
          (((2 ^ modulusExponent) ^ (2 ^ degreeExponent) : ℕ) : ℝ))) ≤
      (Pr[(fun seed :
          SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent ×
            (Fin extraCount →
              SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent) ↦
          ∃ weight : SingleSourceInverse.PowerOfTwo.BoundedWeights
              modulusExponent degreeExponent (extraCount + 1) 1,
            MultiSourceCounting.maskCombination weight.1 (anchoredMasks seed) = target) |
        ($ᵗ (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent ×
          (Fin extraCount →
            SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent))) ]).toReal := by
  calc
    _ ≤ (Pr[(fun seed :
          SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent ×
            (Fin extraCount →
              SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent) ↦
        ∃ bits : Fin extraCount → Bool,
          MultiSourceCounting.maskCombination
              (anchoredBinaryWeight bits) (anchoredMasks seed) = target) |
      ($ᵗ (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent ×
        (Fin extraCount →
          SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent))) ]).toReal :=
      production_binaryMaskCombination_twoPow_div_add_le_existsTarget_toReal
        modulusExponent degreeExponent extraCount target
    _ ≤ _ := by
      apply ENNReal.toReal_mono probEvent_ne_top
      apply probEvent_mono
      intro seed _ hbinary
      obtain ⟨bits, hcombination⟩ := hbinary
      exact ⟨⟨anchoredBinaryWeight bits,
        production_cInfNorm_anchoredBinaryWeight_le_one
          modulusExponent degreeExponent extraCount bits⟩, hcombination⟩

/-- Level-zero target-one specialization in the concrete bounded-weight type. -/
theorem production_binaryBoundedPreimage_twoPow_div_add_le_exists_toReal
    (modulusExponent degreeExponent extraCount : ℕ)
    [SampleableType
      (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent ×
        (Fin extraCount →
          SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent))] :
    (((2 ^ extraCount : ℕ) : ℝ) /
        (((2 ^ extraCount : ℕ) : ℝ) +
          (((2 ^ modulusExponent) ^ (2 ^ degreeExponent) : ℕ) : ℝ))) ≤
      (Pr[(fun seed :
          SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent ×
            (Fin extraCount →
              SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent) ↦
          ∃ weight : SingleSourceInverse.PowerOfTwo.BoundedWeights
              modulusExponent degreeExponent (extraCount + 1) 1,
            MultiSourceCounting.maskCombination weight.1 (anchoredMasks seed) = 1) |
        ($ᵗ (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent ×
          (Fin extraCount →
            SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent))) ]).toReal :=
  production_binaryBoundedPreimage_twoPow_div_add_le_existsTarget_toReal
    modulusExponent degreeExponent extraCount 1

/-! ## Explicit efficient-selector boundary -/

/-- A candidate algorithm returns the `m` binary coefficients; the reserved first coefficient is
inserted by `anchoredBinaryWeight`.  No complexity claim is built into this function type. -/
abbrev BitSelector (R : Type) (extraCount : ℕ) :=
  MultiSourceCounting.Vectors R (extraCount + 1) → Fin extraCount → Bool

/-- Turn a bit-selection algorithm into the exact public-weight selector consumed by the
ring-square compiler. -/
def binarySelectorWeights {R : Type} [CommRing R] {extraCount : ℕ}
    (selector : BitSelector R extraCount) : Selector R (extraCount + 1) :=
  fun masks ↦ anchoredBinaryWeight (selector masks)

/-- Pointwise completeness means that whenever a binary preimage exists, the algorithm actually
returns one.  An asymptotic security theorem must additionally establish that the algorithm is
polynomial time; this predicate deliberately does not assert that. -/
def IsCompleteBinarySelector {R : Type} [CommRing R] {extraCount : ℕ}
    (target : R) (selector : BitSelector R extraCount) : Prop :=
  ∀ masks,
    (∃ bits : Fin extraCount → Bool,
      MultiSourceCounting.maskCombination
          (anchoredBinaryWeight bits) masks = target) →
    MultiSourceCounting.maskCombination
        (binarySelectorWeights selector masks) masks = target

/-- Classical exhaustive choice of a binary preimage whenever one exists.  This witnesses that
the completeness interface is logically inhabited, but deliberately carries no efficiency claim. -/
noncomputable def exhaustiveCompleteBitSelector
    {R : Type} [CommRing R] [DecidableEq R] {extraCount : ℕ}
    (target : R) : BitSelector R extraCount :=
  fun masks ↦
    if h : ∃ bits : Fin extraCount → Bool,
        MultiSourceCounting.maskCombination
          (anchoredBinaryWeight bits) masks = target then
      Classical.choose h
    else
      fun _index ↦ false

/-- Exhaustive choice is pointwise complete.  This theorem is information-theoretic only: its
selector is noncomputable and must not be used to assert PPT reduction closure. -/
theorem exhaustiveCompleteBitSelector_isComplete
    {R : Type} [CommRing R] [DecidableEq R] {extraCount : ℕ}
    (target : R) :
    IsCompleteBinarySelector target
      (exhaustiveCompleteBitSelector (extraCount := extraCount) target) := by
  intro masks hexists
  unfold binarySelectorWeights exhaustiveCompleteBitSelector
  rw [dif_pos hexists]
  exact Classical.choose_spec hexists

/-- A complete binary selector inherits the second-moment success probability.  This is the
precise interface at which a future polynomial-time subset-sum algorithm can enter. -/
theorem production_completeBinarySelector_twoPow_div_add_le_success_toReal
    (modulusExponent degreeExponent extraCount : ℕ)
    (target : SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent)
    [SampleableType
      (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent ×
        (Fin extraCount →
          SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent))]
    (selector : BitSelector
      (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent) extraCount)
    (hcomplete : IsCompleteBinarySelector target selector) :
    (((2 ^ extraCount : ℕ) : ℝ) /
        (((2 ^ extraCount : ℕ) : ℝ) +
          (((2 ^ modulusExponent) ^ (2 ^ degreeExponent) : ℕ) : ℝ))) ≤
      (Pr[(fun seed :
          SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent ×
            (Fin extraCount →
              SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent) ↦
          MultiSourceCounting.maskCombination
              (binarySelectorWeights selector (anchoredMasks seed))
              (anchoredMasks seed) = target) |
        ($ᵗ (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent ×
          (Fin extraCount →
            SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent))) ]).toReal := by
  calc
    _ ≤ (Pr[(fun seed :
          SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent ×
            (Fin extraCount →
              SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent) ↦
        ∃ bits : Fin extraCount → Bool,
          MultiSourceCounting.maskCombination
              (anchoredBinaryWeight bits) (anchoredMasks seed) = target) |
      ($ᵗ (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent ×
        (Fin extraCount →
          SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent))) ]).toReal :=
      production_binaryMaskCombination_twoPow_div_add_le_existsTarget_toReal
        modulusExponent degreeExponent extraCount target
    _ ≤ _ := by
      apply ENNReal.toReal_mono probEvent_ne_top
      apply probEvent_mono
      intro seed _ hexists
      exact hcomplete (anchoredMasks seed) hexists

/-- Complementary form: a complete selector fails on at most
`q^N / (2^m + q^N)` of anchored mask tables. -/
theorem production_completeBinarySelector_failure_toReal_le_card_div_add
    (modulusExponent degreeExponent extraCount : ℕ)
    (target : SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent)
    [SampleableType
      (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent ×
        (Fin extraCount →
          SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent))]
    (selector : BitSelector
      (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent) extraCount)
    (hcomplete : IsCompleteBinarySelector target selector) :
    (Pr[(fun seed :
        SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent ×
          (Fin extraCount →
            SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent) ↦
        ¬ MultiSourceCounting.maskCombination
            (binarySelectorWeights selector (anchoredMasks seed))
            (anchoredMasks seed) = target) |
      ($ᵗ (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent ×
        (Fin extraCount →
          SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent))) ]).toReal ≤
      (((2 ^ modulusExponent) ^ (2 ^ degreeExponent) : ℕ) : ℝ) /
        (((2 ^ extraCount : ℕ) : ℝ) +
          (((2 ^ modulusExponent) ^ (2 ^ degreeExponent) : ℕ) : ℝ)) := by
  let R := SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent
  let Seed := R × (Fin extraCount → R)
  let succeeds : Seed → Prop := fun seed ↦
    MultiSourceCounting.maskCombination
        (binarySelectorWeights selector (anchoredMasks seed))
        (anchoredMasks seed) = target
  let I : ℝ := (2 ^ extraCount : ℕ)
  let O : ℝ := ((2 ^ modulusExponent) ^ (2 ^ degreeExponent) : ℕ)
  have hI : 0 < I := by positivity
  have hO : 0 < O := by positivity
  have hsuccess : I / (I + O) ≤
      (Pr[succeeds | ($ᵗ Seed)]).toReal := by
    simpa [R, Seed, succeeds, I, O] using
      (production_completeBinarySelector_twoPow_div_add_le_success_toReal
        modulusExponent degreeExponent extraCount target selector hcomplete)
  have hcomplement := probEvent_compl ($ᵗ Seed) succeeds
  rw [probFailure_eq_zero, tsub_zero] at hcomplement
  have hreal := congrArg ENNReal.toReal hcomplement
  rw [ENNReal.toReal_add probEvent_ne_top probEvent_ne_top, ENNReal.toReal_one] at hreal
  change (Pr[fun seed : Seed ↦ ¬ succeeds seed | ($ᵗ Seed)]).toReal ≤ O / (I + O)
  calc
    (Pr[fun seed : Seed ↦ ¬ succeeds seed | ($ᵗ Seed)]).toReal =
        1 - (Pr[succeeds | ($ᵗ Seed)]).toReal := by linarith
    _ ≤ 1 - I / (I + O) := sub_le_sub_left hsuccess 1
    _ = O / (I + O) := by field_simp; ring

/-- The same explicit failure bound for the compiler's native uniform source-mask-vector law. -/
theorem production_completeBinarySelector_uniformMasks_failure_toReal_le_card_div_add
    (modulusExponent degreeExponent extraCount : ℕ)
    (target : SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent)
    [SampleableType
      (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent ×
        (Fin extraCount →
          SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent))]
    [SampleableType
      (MultiSourceCounting.Vectors
        (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent)
        (extraCount + 1))]
    (selector : BitSelector
      (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent) extraCount)
    (hcomplete : IsCompleteBinarySelector target selector) :
    (Pr[(fun masks : MultiSourceCounting.Vectors
          (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent)
          (extraCount + 1) ↦
        ¬ MultiSourceCounting.maskCombination
            (binarySelectorWeights selector masks) masks = target) |
      ($ᵗ MultiSourceCounting.Vectors
        (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent)
        (extraCount + 1))]).toReal ≤
      (((2 ^ modulusExponent) ^ (2 ^ degreeExponent) : ℕ) : ℝ) /
        (((2 ^ extraCount : ℕ) : ℝ) +
          (((2 ^ modulusExponent) ^ (2 ^ degreeExponent) : ℕ) : ℝ)) := by
  rw [probEvent_uniform_masks_eq_anchored]
  exact production_completeBinarySelector_failure_toReal_le_card_div_add
    modulusExponent degreeExponent extraCount target selector hcomplete

/-- Every output of the binary selector interface has coefficient norm at most one, independently
of whether it succeeds. -/
theorem production_cInfNorm_binarySelectorWeights_le_one
    (modulusExponent degreeExponent extraCount : ℕ)
    (selector : BitSelector
      (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent) extraCount)
    (masks : MultiSourceCounting.Vectors
      (SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent) (extraCount + 1))
    (index : Fin (extraCount + 1)) :
    LatticeCrypto.cInfNorm
        (binarySelectorWeights
          (R := SingleSourceInverse.PowerOfTwo.Ring modulusExponent degreeExponent)
          selector masks index) ≤ 1 :=
  production_cInfNorm_anchoredBinaryWeight_le_one
    modulusExponent degreeExponent extraCount (selector masks) index

/-- A selected mask-combination equality is definitionally the compiler's one-row success
predicate. -/
theorem selectorSucceeds_of_binarySelectorWeights_combination_eq
    {R : Type} [CommRing R] {extraCount : ℕ}
    (target : R) (selector : BitSelector R extraCount)
    (sourceRows : SourceRows R (extraCount + 1))
    (hselected : MultiSourceCounting.maskCombination
      (binarySelectorWeights selector (sourceMasks sourceRows))
      (sourceMasks sourceRows) = target) :
    SelectorSucceeds target (binarySelectorWeights selector) sourceRows := by
  classical
  unfold SelectorSucceeds HasGadgetPreimage preimageCombination
  simpa [binarySelectorWeights, MultiSourceCounting.maskCombination,
    TLWE.linearCombination, sourceMasks] using hselected

/-- Pointwise completeness is exactly enough to discharge the compiler's gadget-preimage
predicate on every source family possessing a binary preimage. -/
theorem selectorSucceeds_of_completeBinarySelector
    {R : Type} [CommRing R] {extraCount : ℕ}
    (target : R) (selector : BitSelector R extraCount)
    (hcomplete : IsCompleteBinarySelector target selector)
    (sourceRows : SourceRows R (extraCount + 1))
    (hexists : ∃ bits : Fin extraCount → Bool,
      MultiSourceCounting.maskCombination
          (anchoredBinaryWeight bits) (sourceMasks sourceRows) = target) :
    SelectorSucceeds target (binarySelectorWeights selector) sourceRows := by
  have hselected := hcomplete (sourceMasks sourceRows) hexists
  exact selectorSucceeds_of_binarySelectorWeights_combination_eq
    target selector sourceRows hselected

end

end FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.BinaryPreimageExistence
