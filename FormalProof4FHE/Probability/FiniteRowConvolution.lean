/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Fourier Factorization of Finite Row Convolutions

Let every row choose an element from an arbitrary finite, possibly row-dependent type, and let
that choice contribute an element of a finite abelian group.  The number of complete row families
whose contributions sum to zero is a convolution fiber.  Character orthogonality gives an exact
formula for this fiber, while exchanging the finite sums factors every Fourier coefficient into
independent row-local sums.

The centered form separates the trivial character exactly.  Its triangle-inequality corollary
keeps both the target-group cardinality and the actual product of row-choice cardinalities, which
is the denominator-sensitive form needed for retained-fiber collision estimates.
-/

open scoped BigOperators

namespace FormalProof4FHE.FiniteRowConvolution

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Number of dependent row families whose contributions sum to zero. -/
def rowSumZeroFiberCard
    {Row Target : Type*} [Fintype Row] [DecidableEq Row]
    [AddCommGroup Target] [Fintype Target]
    (Choice : Row → Type*) [(row : Row) → Fintype (Choice row)]
    (contribution : (row : Row) → Choice row → Target) : ℕ :=
  Nat.card
    {rows : (row : Row) → Choice row //
      (∑ row : Row, contribution row (rows row)) = 0}

/-- A finite additive character maps a finite additive sum to a multiplicative product. -/
theorem addChar_apply_finset_sum
    {Index Target : Type*} [DecidableEq Index] [AddCommMonoid Target]
    (character : AddChar Target ℂ) (indices : Finset Index) (value : Index → Target) :
    character (∑ index ∈ indices, value index) =
      ∏ index ∈ indices, character (value index) := by
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices hindex ih =>
      rw [Finset.sum_insert hindex, Finset.prod_insert hindex,
        AddChar.map_add_eq_mul, ih]

/-- The zero convolution fiber is counted by its indicator sum. -/
theorem rowSumZeroFiberCard_eq_sum_indicator
    {Row Target : Type*} [Fintype Row] [DecidableEq Row]
    [AddCommGroup Target] [Fintype Target]
    (Choice : Row → Type*) [(row : Row) → Fintype (Choice row)]
    (contribution : (row : Row) → Choice row → Target) :
    rowSumZeroFiberCard Choice contribution =
      ∑ rows : (row : Row) → Choice row,
        if (∑ row : Row, contribution row (rows row)) = 0 then 1 else 0 := by
  classical
  unfold rowSumZeroFiberCard
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.card_subtype]
  symm
  simp

/-- **Exact finite row-convolution Fourier identity.**  Multiplying the zero-fiber cardinality by
the target-group cardinality gives a sum over target characters, and the coefficient of each
character is a product of independent row-local character sums. -/
theorem card_mul_rowSumZeroFiberCard_eq_sum_prod_rowCharacterSum
    {Row Target : Type*} [Fintype Row] [DecidableEq Row]
    [AddCommGroup Target] [Fintype Target]
    (Choice : Row → Type*) [(row : Row) → Fintype (Choice row)]
    (contribution : (row : Row) → Choice row → Target) :
    (Fintype.card Target : ℂ) * (rowSumZeroFiberCard Choice contribution : ℂ) =
      ∑ character : AddChar Target ℂ,
        ∏ row : Row,
          ∑ choice : Choice row, character (contribution row choice) := by
  classical
  calc
    (Fintype.card Target : ℂ) * (rowSumZeroFiberCard Choice contribution : ℂ) =
        ∑ rows : (row : Row) → Choice row,
          if (∑ row : Row, contribution row (rows row)) = 0 then
            (Fintype.card Target : ℂ)
          else 0 := by
      rw [rowSumZeroFiberCard_eq_sum_indicator]
      push_cast
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro rows _
      by_cases hzero : (∑ row : Row, contribution row (rows row)) = 0 <;>
        simp [hzero]
    _ = ∑ rows : (row : Row) → Choice row,
        ∑ character : AddChar Target ℂ,
          character (∑ row : Row, contribution row (rows row)) := by
      apply Finset.sum_congr rfl
      intro rows _
      rw [AddChar.sum_apply_eq_ite]
    _ = ∑ rows : (row : Row) → Choice row,
        ∑ character : AddChar Target ℂ,
          ∏ row : Row, character (contribution row (rows row)) := by
      apply Finset.sum_congr rfl
      intro rows _
      apply Finset.sum_congr rfl
      intro character _
      exact addChar_apply_finset_sum character Finset.univ
        (fun row ↦ contribution row (rows row))
    _ = ∑ character : AddChar Target ℂ,
        ∑ rows : (row : Row) → Choice row,
          ∏ row : Row, character (contribution row (rows row)) := by
      rw [Finset.sum_comm]
    _ = ∑ character : AddChar Target ℂ,
        ∏ row : Row,
          ∑ choice : Choice row, character (contribution row choice) := by
      apply Finset.sum_congr rfl
      intro character _
      exact (Fintype.prod_sum
        (fun row choice ↦ character (contribution row choice))).symm

/-- The product of the actual dependent row-choice cardinalities. -/
def rowChoiceCardProduct
    {Row : Type*} [Fintype Row]
    (Choice : Row → Type*) [(row : Row) → Fintype (Choice row)] : ℕ :=
  ∏ row : Row, Fintype.card (Choice row)

/-- **Centered exact Fourier identity.**  The trivial character contributes precisely the full
product of row-choice cardinalities; only nontrivial characters control deviation of the zero
fiber from the uniform target-group baseline. -/
theorem card_mul_rowSumZeroFiberCard_sub_rowChoiceCardProduct_eq_nontrivialFourierSum
    {Row Target : Type*} [Fintype Row] [DecidableEq Row]
    [AddCommGroup Target] [Fintype Target]
    (Choice : Row → Type*) [(row : Row) → Fintype (Choice row)]
    (contribution : (row : Row) → Choice row → Target) :
    (Fintype.card Target : ℂ) * (rowSumZeroFiberCard Choice contribution : ℂ) -
        (rowChoiceCardProduct Choice : ℂ) =
      ∑ character ∈ (Finset.univ.erase (0 : AddChar Target ℂ)),
        ∏ row : Row,
          ∑ choice : Choice row, character (contribution row choice) := by
  classical
  rw [card_mul_rowSumZeroFiberCard_eq_sum_prod_rowCharacterSum]
  have hzero :
      (∏ row : Row,
          ∑ choice : Choice row,
            (0 : AddChar Target ℂ) (contribution row choice)) =
        (rowChoiceCardProduct Choice : ℂ) := by
    simp [rowChoiceCardProduct]
  rw [← hzero]
  exact (Finset.sum_erase_eq_sub (Finset.mem_univ (0 : AddChar Target ℂ))).symm

/-- Denominator-sensitive deviation bound obtained from the centered identity.  No ambient
replacement is made: the baseline uses the actual product of row-choice cardinalities, and the
left side retains the exact target-group cardinality. -/
theorem norm_card_mul_rowSumZeroFiberCard_sub_rowChoiceCardProduct_le
    {Row Target : Type*} [Fintype Row] [DecidableEq Row]
    [AddCommGroup Target] [Fintype Target]
    (Choice : Row → Type*) [(row : Row) → Fintype (Choice row)]
    (contribution : (row : Row) → Choice row → Target) :
    ‖(Fintype.card Target : ℂ) * (rowSumZeroFiberCard Choice contribution : ℂ) -
        (rowChoiceCardProduct Choice : ℂ)‖ ≤
      ∑ character ∈ (Finset.univ.erase (0 : AddChar Target ℂ)),
        ∏ row : Row,
          ‖∑ choice : Choice row, character (contribution row choice)‖ := by
  classical
  rw [card_mul_rowSumZeroFiberCard_sub_rowChoiceCardProduct_eq_nontrivialFourierSum]
  refine (norm_sum_le _ _).trans_eq ?_
  apply Finset.sum_congr rfl
  intro character _
  rw [norm_prod]

/-- Total nontrivial row-Fourier mass in the centered convolution formula. -/
def nontrivialRowFourierNormSum
    {Row Target : Type*} [Fintype Row] [DecidableEq Row]
    [AddCommGroup Target] [Fintype Target]
    (Choice : Row → Type*) [(row : Row) → Fintype (Choice row)]
    (contribution : (row : Row) → Choice row → Target) : ℝ :=
  ∑ character ∈ (Finset.univ.erase (0 : AddChar Target ℂ)),
    ∏ row : Row,
      ‖∑ choice : Choice row, character (contribution row choice)‖

/-- Normalized upper bound for the zero-convolution fiber.  The numerator contains the exact
row-choice product plus only the nontrivial Fourier mass; the exact target cardinality remains in
the denominator. -/
theorem rowSumZeroFiberCard_le_add_nontrivialRowFourierNormSum_div_card
    {Row Target : Type*} [Fintype Row] [DecidableEq Row]
    [AddCommGroup Target] [Fintype Target]
    (Choice : Row → Type*) [(row : Row) → Fintype (Choice row)]
    (contribution : (row : Row) → Choice row → Target) :
    (rowSumZeroFiberCard Choice contribution : ℝ) ≤
      ((rowChoiceCardProduct Choice : ℝ) +
          nontrivialRowFourierNormSum Choice contribution) /
        Fintype.card Target := by
  classical
  have hnorm :=
    norm_card_mul_rowSumZeroFiberCard_sub_rowChoiceCardProduct_le Choice contribution
  have hcast :
      (Fintype.card Target : ℂ) * (rowSumZeroFiberCard Choice contribution : ℂ) -
          (rowChoiceCardProduct Choice : ℂ) =
        (((Fintype.card Target : ℝ) *
            (rowSumZeroFiberCard Choice contribution : ℝ) -
          (rowChoiceCardProduct Choice : ℝ) : ℝ) : ℂ) := by
    norm_num
  have habs :
      |(Fintype.card Target : ℝ) * (rowSumZeroFiberCard Choice contribution : ℝ) -
          (rowChoiceCardProduct Choice : ℝ)| ≤
        nontrivialRowFourierNormSum Choice contribution := by
    rw [hcast, Complex.norm_real] at hnorm
    simpa only [nontrivialRowFourierNormSum, Real.norm_eq_abs] using hnorm
  have hlinear :
      (Fintype.card Target : ℝ) * (rowSumZeroFiberCard Choice contribution : ℝ) -
          (rowChoiceCardProduct Choice : ℝ) ≤
        nontrivialRowFourierNormSum Choice contribution :=
    (le_abs_self _).trans habs
  have hcard : (0 : ℝ) < Fintype.card Target := by positivity
  apply (le_div_iff₀ hcard).2
  nlinarith

end

end FormalProof4FHE.FiniteRowConvolution
