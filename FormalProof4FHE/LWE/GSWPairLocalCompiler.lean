/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/
import FormalProof4FHE.LWE.KDMStarConversion
import Mathlib.Combinatorics.SetFamily.Shatter

/-!
# Candidate-key bound for public pair-local corrections

The coefficients may depend arbitrarily on a public transcript. Once fixed,
an affine correction supported on the two target coordinates excludes one
of their four assignments whenever four times the residual bound is smaller
than the centered quadratic weight. If every coordinate pair is covered,
Sauer--Shelah bounds the number of compatible binary keys by n + 1.

This is a pointwise candidate-count theorem, not a formal computational LWE
reduction. It does not apply to dense corrections using other coordinates,
private coefficients, or an arbitrary different evaluation invariant.
-/

open scoped BigOperators

namespace FormalProof4FHE.LWE.GSWPairLocalCompiler

def residual {R : Type} [CommRing R] (c x y w : R) (a b : Bool) : R :=
  c + x * KDMStarGSW.anchor a + y * KDMStarGSW.anchor b +
    w * KDMStarGSW.anchor a * KDMStarGSW.anchor b

def cornerConstant {R : Type} [CommRing R] (w : R) : Bool → Bool → R
  | false, false => w
  | _, _ => 0

def cornerFirst {R : Type} [CommRing R] (w : R) : Bool → Bool → R
  | _, false => -w
  | _, true => 0

def cornerSecond {R : Type} [CommRing R] (w : R) : Bool → Bool → R
  | false, _ => -w
  | true, _ => 0

/-- Explicit public affine coefficients fit exactly three corners. -/
theorem three_corner_residual {R : Type} [CommRing R] (w : R)
    (excludedA excludedB a b : Bool) :
    residual (cornerConstant w excludedA excludedB)
      (cornerFirst w excludedA excludedB) (cornerSecond w excludedA excludedB) w a b =
      if a = excludedA ∧ b = excludedB then
        (if excludedA = excludedB then w else -w) else 0 := by
  cases excludedA <;> cases excludedB <;> cases a <;> cases b <;>
    simp [residual, cornerConstant, cornerFirst, cornerSecond, KDMStarGSW.anchor]

theorem four_corner_identity {R : Type} [CommRing R] (c x y w : R) :
    residual c x y w true true - residual c x y w true false -
      residual c x y w false true + residual c x y w false false = w := by
  simp [residual, KDMStarGSW.anchor]
  ring

theorem exists_bad_pair {q : ℕ} [NeZero q] (c x y w : ZMod q) (bound : ℕ)
    (hw : 4 * bound < KDMStarConversion.magnitude w) :
    ∃ a b, bound < KDMStarConversion.magnitude (residual c x y w a b) := by
  by_contra h
  push Not at h
  have hb := KDMStarConversion.magnitude_difference2_le
    (fun s ↦ c + x * s 0 + y * s 1 + w * s 0 * s 1) bound
    (by simpa [KDMStarConversion.corner, residual] using h)
  have heq : KDMStarConversion.difference2
      (fun s ↦ c + x * s 0 + y * s 1 + w * s 0 * s 1) = w := by
    simpa [KDMStarConversion.difference2, KDMStarConversion.corner, residual]
      using four_corner_identity c x y w
  rw [heq] at hb
  omega

theorem not_shatters_pair {α : Type} [DecidableEq α] {q : ℕ} [NeZero q]
    (family : Finset (Finset α)) (i j : α) (hij : i ≠ j)
    (c x y w : ZMod q) (bound : ℕ)
    (hw : 4 * bound < KDMStarConversion.magnitude w)
    (hgood : ∀ s ∈ family, KDMStarConversion.magnitude
      (residual c x y w (decide (i ∈ s)) (decide (j ∈ s))) ≤ bound) :
    ¬ family.Shatters {i, j} := by
  intro hs
  obtain ⟨a, b, hab⟩ := exists_bad_pair c x y w bound hw
  let t : Finset α := (if a then {i} else ∅) ∪ (if b then {j} else ∅)
  have ht : t ⊆ {i, j} := by
    cases a <;> cases b <;> simp [t]
  obtain ⟨s, hsf, heq⟩ := hs ht
  have hi : decide (i ∈ s) = a := by
    have hm := Finset.ext_iff.mp heq i
    cases a <;> cases b <;> simp [t, hij] at hm <;> simp [hm]
  have hj : decide (j ∈ s) = b := by
    have hm := Finset.ext_iff.mp heq j
    cases a <;> cases b <;> simp [t, Ne.symm hij] at hm <;> simp [hm]
  have hb := hgood s hsf
  rw [hi, hj] at hb
  omega

/-- A purely combinatorial bound; no probability or hardness assumption. -/
theorem card_le_of_no_shattered_pair {α : Type} [DecidableEq α] [Fintype α]
    (family : Finset (Finset α))
    (hpair : ∀ i j, i ≠ j → ¬ family.Shatters {i, j}) :
    family.card ≤ Fintype.card α + 1 := by
  have hvc : family.vcDim ≤ 1 := by
    apply Finset.sup_le
    intro s hs
    apply Finset.card_le_one.mpr
    intro i hi j hj
    by_contra hij
    exact hpair i j hij ((Finset.mem_shatterer.mp hs).mono_right
      (by simpa using (Finset.insert_subset_iff.mpr ⟨hi, Finset.singleton_subset_iff.mpr hj⟩)))
  calc
    family.card ≤ family.shatterer.card := Finset.card_le_card_shatterer family
    _ ≤ ∑ k ∈ Finset.Iic family.vcDim, (Fintype.card α).choose k :=
      Finset.card_shatterer_le_sum_vcDim
    _ ≤ ∑ k ∈ Finset.Iic 1, (Fintype.card α).choose k := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.Iic_subset_Iic.mpr hvc
      · intro k _ _
        exact Nat.zero_le _
    _ = Fintype.card α + 1 := by
      have hi : Finset.Iic (1 : ℕ) = {0, 1} := by
        ext k
        simp only [Finset.mem_Iic, Finset.mem_insert, Finset.mem_singleton]
        omega
      simp [hi, Nat.add_comm]

/-- Coefficients and weights can be different for each pair, and can be
chosen from the entire public transcript before this theorem is applied. -/
theorem candidate_key_bound {α : Type} [DecidableEq α] [Fintype α]
    {q : ℕ} [NeZero q] (family : Finset (Finset α))
    (c x y w : α → α → ZMod q) (bound : ℕ)
    (hw : ∀ i j, i ≠ j → 4 * bound < KDMStarConversion.magnitude (w i j))
    (hgood : ∀ s ∈ family, ∀ i j, i ≠ j → KDMStarConversion.magnitude
      (residual (c i j) (x i j) (y i j) (w i j)
        (decide (i ∈ s)) (decide (j ∈ s))) ≤ bound) :
    family.card ≤ Fintype.card α + 1 := by
  apply card_le_of_no_shattered_pair
  intro i j hij
  exact not_shatters_pair family i j hij (c i j) (x i j) (y i j) (w i j)
    bound (hw i j hij) (fun s hs ↦ hgood s hs i j hij)

end FormalProof4FHE.LWE.GSWPairLocalCompiler
