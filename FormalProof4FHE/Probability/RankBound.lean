/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.SubspaceLWE.Basic
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Projection

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

/-! ## Reducing a fixed high-rank left factor to a rectangular matrix

The lemmas in this section close the linear-algebra bridge used by Pietrzak's Subspace-LWE
reduction.  If a fixed square matrix `X` has rank at least `d + δ`, then multiplying a uniform
ambient-by-`d` matrix by `X` loses column rank no more often than a fresh uniform
`(d + δ)`-by-`d` matrix does. -/

/-- Left multiplication by an invertible square matrix permutes rectangular matrices. -/
theorem mulLeftRect_bijective {F : Type} [Field F]
    {rows cols : Type} [Fintype rows] [DecidableEq rows]
    (unit : Matrix rows rows F) (hunit : IsUnit unit) :
    Function.Bijective (fun matrix : Matrix rows cols F ↦ unit * matrix) := by
  let inverse : Matrix rows rows F := (hunit.unit⁻¹ : (Matrix rows rows F)ˣ)
  have hleft : inverse * unit = 1 := by
    rw [← hunit.unit_spec]
    exact Units.inv_mul _
  have hright : unit * inverse = 1 := by
    rw [← hunit.unit_spec]
    exact Units.mul_inv _
  constructor
  · intro first second heq
    have h := congrArg (fun matrix ↦ inverse * matrix) heq
    simpa [← Matrix.mul_assoc, hleft] using h
  · intro matrix
    refine ⟨inverse * matrix, ?_⟩
    simp [← Matrix.mul_assoc, hright]

/-- Embed the rows of a smaller full-rank block into the rank block of a normal form. -/
private def rowEmbedding {ambient rank lower : ℕ} {rest : Type} (h : lower ≤ rank)
    (equiv : Fin ambient ≃ Fin rank ⊕ rest) : Fin lower → Fin ambient :=
  fun index ↦ equiv.symm (Sum.inl (Fin.castLE h index))

private theorem rowEmbedding_injective {ambient rank lower : ℕ} {rest : Type}
    (h : lower ≤ rank) (equiv : Fin ambient ≃ Fin rank ⊕ rest) :
    Function.Injective (rowEmbedding h equiv) :=
  equiv.symm.injective.comp (Sum.inl_injective.comp (Fin.castLE_injective h))

/-- The leading rows of the rank normal form act as the identity. -/
private theorem rankNormalForm_mul_restrict {F : Type} [Field F]
    {ambient rank lower cols : ℕ} {rest : Type} [Fintype rest] (h : lower ≤ rank)
    (equiv : Fin ambient ≃ Fin rank ⊕ rest)
    (matrix : Matrix (Fin ambient) (Fin cols) F) :
    (((fromBlocks 1 0 0 0).submatrix equiv equiv) * matrix).submatrix
        (rowEmbedding h equiv) (Equiv.refl (Fin cols)) =
      matrix.submatrix (rowEmbedding h equiv) (Equiv.refl (Fin cols)) := by
  ext i j
  simp only [Matrix.submatrix_apply, Equiv.refl_apply, Matrix.mul_apply, rowEmbedding,
    Equiv.apply_symm_apply]
  calc
    (∑ x, fromBlocks 1 0 0 0 (Sum.inl (Fin.castLE h i)) (equiv x) * matrix x j) =
        ∑ y : Fin rank ⊕ rest,
          fromBlocks 1 0 0 0 (Sum.inl (Fin.castLE h i)) y * matrix (equiv.symm y) j := by
      rw [← equiv.sum_comp]
      simp only [Equiv.symm_apply_apply]
      rfl
    _ = matrix (equiv.symm (Sum.inl (Fin.castLE h i))) j := by
      simp [Matrix.one_apply]

/-- A high-rank square matrix can be normalized so that a row restriction witnesses every
column-rank failure after multiplication. -/
private theorem exists_unit_and_restriction_of_rank_ge {F : Type} [Field F]
    (ambient lower cols : ℕ) (left : Matrix (Fin ambient) (Fin ambient) F)
    (hleft : lower ≤ left.rank) :
    ∃ (unit : Matrix (Fin ambient) (Fin ambient) F) (row : Fin lower → Fin ambient),
      IsUnit unit ∧ Function.Injective row ∧
        ∀ matrix : Matrix (Fin ambient) (Fin cols) F,
          (left * (unit * matrix)).rank < cols →
            (matrix.submatrix row (Equiv.refl (Fin cols))).rank < cols := by
  classical
  obtain ⟨rowUnit, columnUnit, equiv, hrowUnit, hcolumnUnit, hnormal⟩ :=
    Matrix.exists_rank_normal_form left
  refine ⟨columnUnit, rowEmbedding hleft equiv, hcolumnUnit,
    rowEmbedding_injective hleft equiv, ?_⟩
  intro matrix hbad
  have hdet : IsUnit rowUnit.det := (Matrix.isUnit_iff_isUnit_det rowUnit).1 hrowUnit
  have hbad' : (rowUnit * (left * (columnUnit * matrix))).rank < cols := by
    rw [Matrix.rank_mul_eq_right_of_isUnit_det rowUnit (left * (columnUnit * matrix)) hdet]
    exact hbad
  have hproduct : rowUnit * (left * (columnUnit * matrix)) =
      ((fromBlocks 1 0 0 0).submatrix equiv equiv) * matrix := by
    calc
      rowUnit * (left * (columnUnit * matrix)) =
          (rowUnit * left * columnUnit) * matrix := by simp [Matrix.mul_assoc]
      _ = ((fromBlocks 1 0 0 0).submatrix equiv equiv) * matrix := by rw [hnormal]
  rw [hproduct] at hbad'
  apply lt_of_le_of_lt _ hbad'
  rw [← rankNormalForm_mul_restrict hleft equiv matrix]
  exact Matrix.rank_submatrix_le _ _ _

/-- Restricting independent uniform matrix rows along an injection remains uniform. -/
theorem evalDist_restrictRows_uniform {F : Type} [Fintype F] [SampleableType F]
    (ambient lower cols : ℕ) (row : Fin lower → Fin ambient)
    (hrow : Function.Injective row) :
    evalDist (do
      let matrix ← $ᵗ Matrix (Fin ambient) (Fin cols) F
      return matrix.submatrix row (Equiv.refl (Fin cols))) =
      evalDist ($ᵗ Matrix (Fin lower) (Fin cols) F) := by
  let inputEquiv : Matrix (Fin ambient) (Fin cols) F ≃
      (Fin ambient → Fin cols → F) := Matrix.of.symm
  let outputEquiv : (Fin lower → Fin cols → F) ≃
      Matrix (Fin lower) (Fin cols) F := Matrix.of
  let restrict : (Fin ambient → Fin cols → F) → (Fin lower → Fin cols → F) :=
    fun matrix ↦ matrix ∘ row
  have hgame :
      (do
        let matrix ← $ᵗ Matrix (Fin ambient) (Fin cols) F
        return matrix.submatrix row (Equiv.refl (Fin cols))) =
        outputEquiv <$> (restrict <$> (inputEquiv <$>
          ($ᵗ Matrix (Fin ambient) (Fin cols) F))) := by
    simp only [bind_pure_comp, Functor.map_map]
    congr 1
  rw [hgame]
  have hinput :
      evalDist (inputEquiv <$> ($ᵗ Matrix (Fin ambient) (Fin cols) F)) =
        evalDist ($ᵗ (Fin ambient → Fin cols → F)) :=
    evalDist_map_bijective_uniform_cross
      (α := Matrix (Fin ambient) (Fin cols) F)
      (β := Fin ambient → Fin cols → F) inputEquiv inputEquiv.bijective
  have hrestrict :
      evalDist (restrict <$> ($ᵗ (Fin ambient → Fin cols → F))) =
        evalDist ($ᵗ (Fin lower → Fin cols → F)) := by
    simpa [restrict, bind_pure_comp] using
      (evalDist_uniformSample_map_comp_injective
        (A := Fin lower) (B := Fin ambient) (R := Fin cols → F) hrow)
  have hinput' := hinput
  rw [evalDist_map] at hinput'
  have hrestrict' := hrestrict
  rw [evalDist_map] at hrestrict'
  calc
    evalDist (outputEquiv <$> (restrict <$> (inputEquiv <$>
        ($ᵗ Matrix (Fin ambient) (Fin cols) F)))) =
        evalDist (outputEquiv <$> (restrict <$> ($ᵗ (Fin ambient → Fin cols → F)))) := by
      simp only [evalDist_map]
      rw [hinput']
    _ = evalDist (outputEquiv <$> ($ᵗ (Fin lower → Fin cols → F))) := by
      simp only [evalDist_map]
      rw [hrestrict']
    _ = evalDist ($ᵗ Matrix (Fin lower) (Fin cols) F) :=
      evalDist_map_bijective_uniform_cross
        (α := Fin lower → Fin cols → F)
        (β := Matrix (Fin lower) (Fin cols) F) outputEquiv outputEquiv.bijective

/-- A fixed high-rank left factor has no larger rank-failure probability than the exposed
uniform rectangular submatrix. -/
theorem rankMulFailure_le_rectangular {F : Type} [Field F] [Fintype F]
    [SampleableType F] (ambient dimension slack : ℕ)
    (left : Matrix (Fin ambient) (Fin ambient) F)
    (hleft : dimension + slack ≤ left.rank) :
    Pr[(fun matrix : Matrix (Fin ambient) (Fin dimension) F ↦
      (left * matrix).rank < dimension) |
      ($ᵗ Matrix (Fin ambient) (Fin dimension) F)] ≤
    Pr[(fun matrix : Matrix (Fin (dimension + slack)) (Fin dimension) F ↦
      matrix.rank < dimension) |
      ($ᵗ Matrix (Fin (dimension + slack)) (Fin dimension) F)] := by
  classical
  obtain ⟨unit, row, hunit, hrow, himp⟩ :=
    exists_unit_and_restriction_of_rank_ge ambient (dimension + slack) dimension left hleft
  let transform := fun matrix : Matrix (Fin ambient) (Fin dimension) F ↦ unit * matrix
  let restrict := fun matrix : Matrix (Fin ambient) (Fin dimension) F ↦
    matrix.submatrix row (Equiv.refl (Fin dimension))
  have htransform : Function.Bijective transform := mulLeftRect_bijective unit hunit
  have htransformDist :
      evalDist (transform <$> ($ᵗ Matrix (Fin ambient) (Fin dimension) F)) =
        evalDist ($ᵗ Matrix (Fin ambient) (Fin dimension) F) :=
    evalDist_map_bijective_uniform_cross
      (α := Matrix (Fin ambient) (Fin dimension) F)
      (β := Matrix (Fin ambient) (Fin dimension) F) transform htransform
  have hrestrictDist :
      evalDist (restrict <$> ($ᵗ Matrix (Fin ambient) (Fin dimension) F)) =
        evalDist ($ᵗ Matrix (Fin (dimension + slack)) (Fin dimension) F) := by
    rw [show restrict <$> ($ᵗ Matrix (Fin ambient) (Fin dimension) F) =
        (do
          let matrix ← $ᵗ Matrix (Fin ambient) (Fin dimension) F
          return matrix.submatrix row (Equiv.refl (Fin dimension))) by
      simp only [restrict, bind_pure_comp]]
    exact evalDist_restrictRows_uniform ambient (dimension + slack) dimension row hrow
  calc
    Pr[(fun matrix : Matrix (Fin ambient) (Fin dimension) F ↦
        (left * matrix).rank < dimension) |
        ($ᵗ Matrix (Fin ambient) (Fin dimension) F)] =
      Pr[(fun matrix : Matrix (Fin ambient) (Fin dimension) F ↦
        (left * matrix).rank < dimension) |
        transform <$> ($ᵗ Matrix (Fin ambient) (Fin dimension) F)] :=
      probEvent_congr' (fun _ _ ↦ Iff.rfl) htransformDist.symm
    _ = Pr[(fun matrix : Matrix (Fin ambient) (Fin dimension) F ↦
        (left * transform matrix).rank < dimension) |
        ($ᵗ Matrix (Fin ambient) (Fin dimension) F)] := by
      rw [probEvent_map]
      rfl
    _ ≤ Pr[(fun matrix : Matrix (Fin ambient) (Fin dimension) F ↦
        (restrict matrix).rank < dimension) |
        ($ᵗ Matrix (Fin ambient) (Fin dimension) F)] := by
      apply probEvent_mono
      intro matrix _ hbad
      exact himp matrix hbad
    _ = Pr[(fun matrix : Matrix (Fin (dimension + slack)) (Fin dimension) F ↦
        matrix.rank < dimension) |
        restrict <$> ($ᵗ Matrix (Fin ambient) (Fin dimension) F)] := by
      rw [probEvent_map]
      rfl
    _ = Pr[(fun matrix : Matrix (Fin (dimension + slack)) (Fin dimension) F ↦
        matrix.rank < dimension) |
        ($ᵗ Matrix (Fin (dimension + slack)) (Fin dimension) F)] :=
      probEvent_congr' (fun _ _ ↦ Iff.rfl) hrestrictDist

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
