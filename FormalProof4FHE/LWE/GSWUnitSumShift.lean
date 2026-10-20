/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.FiniteProduct
import FormalProof4FHE.LWE.GSWQuadraticPreimage

/-!
# Unit-sum masks absorb one common hint by one secret shift

For masks with coordinate sum one, a scalar key-dependent hint is absorbed
by adding that scalar to every secret coordinate. Different row hints yield
different shifted secrets. A single fixed shifted secret works for every
unit-sum mask in a whole batch exactly when its row hints agree.

This audits the row identity used in ePrint 2015/466, not its entire scheme.
The conditional two-coordinate example has exactly uniform row marginals
and an explicitly correlated joint view. It refutes an inference from row
marginals to joint uniformity, not the paper's asymptotic security claim.
-/

open Matrix OracleComp
open scoped BigOperators ENNReal

namespace FormalProof4FHE.LWE.GSWUnitSumShift

def shifted {R : Type} [Add R] {n : ℕ} (secret : Fin n → R) (hint : R) : Fin n → R :=
  fun row ↦ secret row + hint

theorem row_identity {R : Type} [CommRing R] {n : ℕ}
    (mask secret : Fin n → R) (hint error : R) (hsum : ∑ row, mask row = 1) :
    dotProduct mask secret + error + hint = dotProduct mask (shifted secret hint) + error := by
  simp only [dotProduct, shifted, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hsum, one_mul]
  ring

theorem shifted_eq_iff {R : Type} [AddGroup R] {n : ℕ}
    (secret : Fin (n + 1) → R) (first second : R) :
    shifted secret first = shifted secret second ↔ first = second := by
  constructor
  · intro h
    exact add_left_cancel (congrFun h 0)
  · rintro rfl
    rfl

/-- Unit coordinate masks are included among all unit-sum masks. -/
theorem all_unitSum_masks_force_shift {R : Type} [CommRing R] {n : ℕ}
    (secret target : Fin n → R) (hint : R)
    (h : ∀ mask : Fin n → R, (∑ row, mask row) = 1 →
      dotProduct mask target = dotProduct mask secret + hint) :
    target = shifted secret hint := by
  funext row
  have hh := h (fun other ↦ if other = row then 1 else 0) (by simp)
  simpa [dotProduct, shifted, ite_mul] using hh

/-- The exact common-secret interface that a batch reduction would need. -/
theorem common_shift_iff {R : Type} [CommRing R] {n k : ℕ}
    (secret target : Fin (n + 1) → R) (hints : Fin k → R) :
    (∀ column (mask : Fin (n + 1) → R), (∑ row, mask row) = 1 →
      dotProduct mask target = dotProduct mask secret + hints column) ↔
      ∀ column, target = shifted secret (hints column) := by
  constructor
  · intro h column
    exact all_unitSum_masks_force_shift secret target (hints column) (h column)
  · intro h column mask hsum
    rw [h column]
    simpa using (row_identity mask secret (hints column) 0 hsum).symm

theorem common_shift_requires_equal_hints {R : Type} [CommRing R] {n k : ℕ}
    (secret target : Fin (n + 1) → R) (hints : Fin k → R)
    (h : ∀ column (mask : Fin (n + 1) → R), (∑ row, mask row) = 1 →
      dotProduct mask target = dotProduct mask secret + hints column)
    (first second : Fin k) : hints first = hints second := by
  have hh := (common_shift_iff secret target hints).mp h
  exact (shifted_eq_iff secret _ _).mp ((hh first).symm.trans (hh second))

def twoMask {R : Type} [Ring R] (first : R) : Fin 2 → R :=
  ![first, 1 - first]

theorem twoMask_sum {R : Type} [CommRing R] (first : R) :
    ∑ row, twoMask first row = 1 := by
  simp [twoMask, Fin.sum_univ_two]

/-- Two valid unit-sum rows with distinct affine key hints. Their bodies
coincide at these fixed masks for every key, before adding independent noise. -/
theorem conditional_bodies_eq {R : Type} [CommRing R] (secret : Fin 2 → R) :
    dotProduct (twoMask (0 : R)) secret + secret 0 =
      dotProduct (twoMask (1 : R)) secret + secret 1 := by
  simp [twoMask, dotProduct, Fin.sum_univ_two, add_comm]

def sumEquiv {R : Type} [AddGroup R] : (R × R) ≃ (R × R) where
  toFun pair := (pair.1 + pair.2, pair.2)
  invFun pair := (pair.1 - pair.2, pair.2)
  left_inv pair := by simp
  right_inv pair := by simp

noncomputable section

def conditionalJoint (q : ℕ) [NeZero q] : ProbComp (ZMod q × ZMod q) :=
  (fun key : ZMod q × ZMod q ↦ (key.1 + key.2, key.1 + key.2)) <$> ($ᵗ (ZMod q × ZMod q))

theorem conditionalJoint_eq_unitSum_rows (q : ℕ) [NeZero q] :
    conditionalJoint q =
      (fun key : ZMod q × ZMod q ↦
        (dotProduct (twoMask (0 : ZMod q)) ![key.1, key.2] + key.1,
          dotProduct (twoMask (1 : ZMod q)) ![key.1, key.2] + key.2)) <$>
          ($ᵗ (ZMod q × ZMod q)) := by
  unfold conditionalJoint
  congr 1
  funext key
  simp [twoMask, dotProduct, Fin.sum_univ_two, add_comm]

theorem sum_uniform (q : ℕ) [NeZero q] :
    𝒟[(fun key : ZMod q × ZMod q ↦ key.1 + key.2) <$> ($ᵗ (ZMod q × ZMod q))] =
      𝒟[$ᵗ ZMod q] := by
  have hh := evalDist_map_bijective_uniform_cross (ZMod q × ZMod q) (sumEquiv (R := ZMod q))
    (sumEquiv (R := ZMod q)).bijective
  have hf := evalDist_map_eq_of_evalDist_eq hh Prod.fst
  rw [evalDist_map_fst_uniformSample_prod, Functor.map_map] at hf
  exact hf

theorem conditionalJoint_fst_uniform (q : ℕ) [NeZero q] :
    𝒟[Prod.fst <$> conditionalJoint q] = 𝒟[$ᵗ ZMod q] := by
  simpa [conditionalJoint, map_map, Function.comp_def] using sum_uniform q

theorem conditionalJoint_snd_uniform (q : ℕ) [NeZero q] :
    𝒟[Prod.snd <$> conditionalJoint q] = 𝒟[$ᵗ ZMod q] := by
  simpa [conditionalJoint, map_map, Function.comp_def] using sum_uniform q

theorem conditionalJoint_equal_probability (q : ℕ) [NeZero q] :
    Pr[fun bodies ↦ bodies.1 = bodies.2 | conditionalJoint q] = 1 := by
  have hq : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast NeZero.ne q
  have ht : (q : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  simp [conditionalJoint, probEvent_map, ENNReal.div_self (mul_ne_zero hq hq) (ENNReal.mul_ne_top ht ht)]

theorem uniform_equal_probability (q : ℕ) [NeZero q] :
    Pr[fun bodies : ZMod q × ZMod q ↦ bodies.1 = bodies.2 | $ᵗ (ZMod q × ZMod q)] =
      (q : ℝ≥0∞)⁻¹ := by
  rw [probEvent_uniformSample]
  have hc : Fintype.card {bodies : ZMod q × ZMod q // bodies.1 = bodies.2} = q := by
    let eqv : {bodies : ZMod q × ZMod q // bodies.1 = bodies.2} ≃ ZMod q :=
      { toFun := fun bodies ↦ bodies.1.1
        invFun := fun value ↦ ⟨(value, value), rfl⟩
        left_inv := by
          intro bodies
          apply Subtype.ext
          exact Prod.ext rfl bodies.2
        right_inv := fun _ ↦ rfl }
    rw [Fintype.card_congr eqv, ZMod.card]
  rw [← Fintype.card_subtype, hc, Fintype.card_prod, ZMod.card, Nat.cast_mul]
  have hq : (q : ℝ≥0∞) ≠ 0 := by exact_mod_cast NeZero.ne q
  have ht : (q : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inr ht) (Or.inl ht), ← mul_assoc,
    ENNReal.mul_inv_cancel hq ht, one_mul]

end

end FormalProof4FHE.LWE.GSWUnitSumShift
