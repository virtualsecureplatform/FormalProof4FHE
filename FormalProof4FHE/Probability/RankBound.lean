/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.SubspaceLWE.Basic
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-!
# Rank of a Uniform Finite-Field Matrix

This file proves the finite-field rank estimate used in the Subspace-LWE reduction.  It first
counts full-column-rank matrices exactly, then derives the convenient bound

`Pr[rank M < d] ≤ 2 / |F|^(δ + 1)`

for a uniform `(d + δ) × d` matrix over a finite field `F`.
-/

open Matrix OracleComp
open scoped ENNReal

namespace FormalProof4FHE.FiniteFieldRank

/-- A real-valued union bound for the complement of a finite product. -/
theorem one_sub_prod_one_sub_le_sum {ι : Type} [Fintype ι] [LinearOrder ι]
    (f : ι → ℝ) (hf0 : ∀ i, 0 ≤ f i) (hf1 : ∀ i, f i ≤ 1) :
    1 - ∏ i, (1 - f i) ≤ ∑ i, f i := by
  rw [Finset.prod_one_sub_ordered]
  simp only [sub_sub_cancel]
  apply Finset.sum_le_sum
  intro i _
  have hfactor0 : ∀ j ∈ Finset.univ.filter (· < i), 0 ≤ 1 - f j := by
    intro j _
    linarith [hf1 j]
  have hfactor1 : ∀ j ∈ Finset.univ.filter (· < i), 1 - f j ≤ 1 := by
    intro j _
    linarith [hf0 j]
  have hprod0 : 0 ≤ ∏ j ∈ Finset.univ with j < i, (1 - f j) :=
    Finset.prod_nonneg hfactor0
  have hprod1 : ∏ j ∈ Finset.univ with j < i, (1 - f j) ≤ 1 :=
    Finset.prod_le_one hfactor0 hfactor1
  nlinarith [hf0 i]

/-- A matrix has full column rank exactly when its column family is linearly independent. -/
theorem rank_eq_width_iff_linearIndependent {F : Type} [Field F] [Fintype F]
    (rows cols : ℕ) (matrix : Matrix (Fin rows) (Fin cols) F) :
    matrix.rank = cols ↔ LinearIndependent F matrix.col := by
  rw [linearIndependent_iff_card_eq_finrank_span]
  simp [Set.finrank, Matrix.rank_eq_finrank_span_cols, eq_comm]

/-- Full-column-rank matrices correspond to linearly independent ordered column families. -/
noncomputable def fullRankEquiv {F : Type} [Field F] [Fintype F] (rows cols : ℕ) :
    {matrix : Matrix (Fin rows) (Fin cols) F // matrix.rank = cols} ≃
      {columns : Fin cols → (Fin rows → F) // LinearIndependent F columns} :=
  Equiv.subtypeEquiv (Matrix.transposeAddEquiv (Fin rows) (Fin cols) F).toEquiv
    (fun matrix ↦ rank_eq_width_iff_linearIndependent rows cols matrix)

/-- Exact count of full-column-rank rectangular matrices over a finite field. -/
theorem card_fullRank {F : Type} [Field F] [Fintype F]
    (rows cols : ℕ) (h : cols ≤ rows) :
    Nat.card {matrix : Matrix (Fin rows) (Fin cols) F // matrix.rank = cols} =
      ∏ i : Fin cols, (Fintype.card F ^ rows - Fintype.card F ^ i.val) := by
  rw [Nat.card_congr (fullRankEquiv rows cols)]
  have h' : cols ≤ Module.finrank F (Fin rows → F) := by
    simpa using h
  simpa using card_linearIndependent (K := F) (V := Fin rows → F) h'

/-- Exact failure probability for a uniform rectangular matrix. -/
theorem rankFailure_exact {F : Type} [Field F] [Fintype F]
    [SampleableType F] (rows cols : ℕ) (h : cols ≤ rows) :
    Pr[(fun matrix : Matrix (Fin rows) (Fin cols) F ↦ matrix.rank < cols) |
      ($ᵗ Matrix (Fin rows) (Fin cols) F)] =
      ((Fintype.card F ^ (rows * cols) -
        ∏ i : Fin cols, (Fintype.card F ^ rows - Fintype.card F ^ i.val) : ℕ) :
          ℝ≥0∞) /
        (Fintype.card F ^ (rows * cols) : ℕ) := by
  classical
  rw [probEvent_uniformSample]
  congr 1
  · rw [show (Finset.univ.filter
        (fun matrix : Matrix (Fin rows) (Fin cols) F ↦ matrix.rank < cols)).card =
        Fintype.card {matrix : Matrix (Fin rows) (Fin cols) F //
          matrix.rank < cols} by
          rw [Fintype.card_subtype]]
    let badEquiv :
        {matrix : Matrix (Fin rows) (Fin cols) F // matrix.rank < cols} ≃
          {matrix : Matrix (Fin rows) (Fin cols) F // ¬matrix.rank = cols} :=
      Equiv.subtypeEquiv (Equiv.refl _) (fun matrix ↦ by
        change matrix.rank < cols ↔ ¬matrix.rank = cols
        have hle := Matrix.rank_le_width matrix
        omega)
    rw [Fintype.card_congr badEquiv, Fintype.card_subtype_compl,
      show Fintype.card (Matrix (Fin rows) (Fin cols) F) =
        Fintype.card F ^ (rows * cols) by
          change Fintype.card (Fin rows → Fin cols → F) = _
          rw [Fintype.card_fun, Fintype.card_fun]
          simp only [Fintype.card_fin]
          rw [mul_comm, pow_mul]]
    norm_cast
    exact congrArg (fun n ↦ Fintype.card F ^ (rows * cols) - n)
      (by simpa [Nat.card_eq_fintype_card] using card_fullRank (F := F) rows cols h)
  · norm_cast
    change Fintype.card (Fin rows → Fin cols → F) = _
    rw [Fintype.card_fun, Fintype.card_fun]
    simp only [Fintype.card_fin]
    rw [mul_comm, pow_mul]

/-- The exact rank-failure probability, normalized as a real-valued product. -/
theorem rankFailure_toReal_eq {F : Type} [Field F] [Fintype F]
    [SampleableType F] (rows cols : ℕ) (h : cols ≤ rows) :
    (Pr[(fun matrix : Matrix (Fin rows) (Fin cols) F ↦ matrix.rank < cols) |
      ($ᵗ Matrix (Fin rows) (Fin cols) F)]).toReal =
      1 - ∏ i : Fin cols,
        (1 - (Fintype.card F : ℝ) ^ i.val / (Fintype.card F : ℝ) ^ rows) := by
  rw [rankFailure_exact rows cols h, ENNReal.toReal_div]
  simp only [ENNReal.toReal_natCast]
  let q := Fintype.card F
  change
    ((q ^ (rows * cols) -
        ∏ i : Fin cols, (q ^ rows - q ^ i.val) : ℕ) : ℝ) /
      (q ^ (rows * cols) : ℕ) =
        1 - ∏ i : Fin cols,
          (1 - (q : ℝ) ^ i.val / (q : ℝ) ^ rows)
  have hq : 0 < q := Fintype.card_pos
  have hpow (i : Fin cols) : q ^ i.val ≤ q ^ rows :=
    Nat.pow_le_pow_right hq (le_trans i.isLt.le h)
  have hprod : (∏ i : Fin cols, (q ^ rows - q ^ i.val)) ≤ q ^ (rows * cols) := by
    calc
      (∏ i : Fin cols, (q ^ rows - q ^ i.val)) ≤ ∏ _i : Fin cols, q ^ rows := by
        apply Finset.prod_le_prod
        · intro i _
          exact Nat.zero_le _
        · intro i _
          exact Nat.sub_le _ _
      _ = (q ^ rows) ^ cols := by simp
      _ = q ^ (rows * cols) := by rw [pow_mul]
  have hcastProd :
      ((∏ i : Fin cols, (q ^ rows - q ^ i.val) : ℕ) : ℝ) =
        ∏ i : Fin cols, ((q : ℝ) ^ rows - (q : ℝ) ^ i.val) := by
    rw [Nat.cast_prod]
    apply Finset.prod_congr rfl
    intro i _
    rw [Nat.cast_sub (hpow i)]
    norm_cast
  have hqReal : (q : ℝ) ^ rows ≠ 0 := by positivity
  have hnormalize :
      (∏ i : Fin cols, (1 - (q : ℝ) ^ i.val / (q : ℝ) ^ rows)) =
        (∏ i : Fin cols, ((q : ℝ) ^ rows - (q : ℝ) ^ i.val)) /
          ((q : ℝ) ^ rows) ^ cols := by
    calc
      (∏ i : Fin cols, (1 - (q : ℝ) ^ i.val / (q : ℝ) ^ rows)) =
          ∏ i : Fin cols,
            (((q : ℝ) ^ rows - (q : ℝ) ^ i.val) / (q : ℝ) ^ rows) := by
        apply Finset.prod_congr rfl
        intro i _
        field_simp
      _ = _ := by
        rw [Finset.prod_div_distrib]
        simp
  rw [Nat.cast_sub hprod, hcastProd]
  simp only [Nat.cast_pow]
  rw [pow_mul, hnormalize]
  field_simp

/-- Union-bound form of the finite-field rank-failure estimate. -/
theorem rankFailure_toReal_le_sum {F : Type} [Field F] [Fintype F]
    [SampleableType F] (rows cols : ℕ) (h : cols ≤ rows) :
    (Pr[(fun matrix : Matrix (Fin rows) (Fin cols) F ↦ matrix.rank < cols) |
      ($ᵗ Matrix (Fin rows) (Fin cols) F)]).toReal ≤
      ∑ i : Fin cols,
        (Fintype.card F : ℝ) ^ i.val / (Fintype.card F : ℝ) ^ rows := by
  rw [rankFailure_toReal_eq rows cols h]
  apply one_sub_prod_one_sub_le_sum
  · intro i
    positivity
  · intro i
    have hcardReal : (0 : ℝ) < Fintype.card F := by
      exact_mod_cast Fintype.card_pos
    apply (div_le_one (pow_pos hcardReal rows)).2
    exact_mod_cast Nat.pow_le_pow_right Fintype.card_pos (le_trans i.isLt.le h)

/-- Bound the normalized geometric sum occurring in the rank estimate. -/
theorem geometric_ratio_sum_le (q : ℝ) (hq : 2 ≤ q) (dimension slack : ℕ) :
    (∑ i : Fin dimension, q ^ i.val / q ^ (dimension + slack)) ≤
      2 / q ^ (slack + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun i ↦ q ^ i / q ^ (dimension + slack)) dimension,
    ← Finset.sum_div]
  rw [pow_add, pow_succ]
  have hq0 : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hd : 0 < q ^ dimension := pow_pos hq0 dimension
  have hs : 0 < q ^ slack := pow_pos hq0 slack
  apply (div_le_div_iff₀ (mul_pos hd hs) (mul_pos hs hq0)).2
  have hsum0 : 0 ≤ ∑ i ∈ Finset.range dimension, q ^ i :=
    Finset.sum_nonneg fun i _ ↦ pow_nonneg hq0.le i
  have hgeom := geom_sum_mul q dimension
  have hcore : (∑ i ∈ Finset.range dimension, q ^ i) * q ≤
      2 * q ^ dimension := by
    nlinarith [pow_nonneg hq0.le dimension]
  calc
    (∑ i ∈ Finset.range dimension, q ^ i) * (q ^ slack * q) =
        ((∑ i ∈ Finset.range dimension, q ^ i) * q) * q ^ slack := by ring
    _ ≤ (2 * q ^ dimension) * q ^ slack :=
      mul_le_mul_of_nonneg_right hcore hs.le
    _ = 2 * (q ^ dimension * q ^ slack) := by ring

/-- A uniform `(dimension + slack) × dimension` matrix over a finite field fails to have full
column rank with probability at most `2 / |F|^(slack + 1)`. -/
theorem rankFailure_le {F : Type} [Field F] [Fintype F]
    [SampleableType F] (dimension slack : ℕ) :
    Pr[(fun matrix : Matrix (Fin (dimension + slack)) (Fin dimension) F ↦
      matrix.rank < dimension) |
      ($ᵗ Matrix (Fin (dimension + slack)) (Fin dimension) F)] ≤
      2 / (Fintype.card F : ℝ≥0∞) ^ (slack + 1) := by
  apply (ENNReal.toReal_le_toReal probEvent_ne_top
    (ENNReal.div_ne_top (by simp)
      (pow_ne_zero _ (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)))).mp
  simp only [ENNReal.toReal_div, ENNReal.toReal_ofNat, ENNReal.toReal_pow,
    ENNReal.toReal_natCast]
  exact
    (rankFailure_toReal_le_sum (dimension + slack) dimension (by omega)).trans
      (geometric_ratio_sum_le (Fintype.card F : ℝ)
        (by exact_mod_cast (Fintype.one_lt_card : 1 < Fintype.card F))
        dimension slack)

end FormalProof4FHE.FiniteFieldRank
