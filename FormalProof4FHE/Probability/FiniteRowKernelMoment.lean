/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Exact Moments of Finite Row-Constrained Fibers

A matrix assembled from independently chosen rows has a kernel whose cardinality is a coupled
quantity.  Its moments nevertheless admit an exact row-factorized counting form.  Expanding the
`moment`-th power selects `moment` candidate kernel vectors; exchanging the finite sums then makes
every row choice independent.

This elementary identity is the finite counting core behind row-wise rank and Fourier estimates.
It does not assume that the row choices are uniform over an ambient space: each row may range over
an arbitrary finite, dependent validity subtype.
-/

open scoped BigOperators

namespace FormalProof4FHE.FiniteRowKernelMoment

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Number of values satisfying all constraints selected by a dependent family of rows. -/
def constrainedFiberCard
    {Row Value : Type} [Fintype Row] [DecidableEq Row] [Fintype Value]
    (Choice : Row → Type) [(row : Row) → Fintype (Choice row)]
    (accepts : (row : Row) → Choice row → Value → Prop)
    (rows : (row : Row) → Choice row) : ℕ :=
  Fintype.card {value : Value // ∀ row, accepts row (rows row) value}

/-- Number of choices for one row that simultaneously accept a finite tuple of values. -/
def simultaneousRowChoiceCard
    {Row Value : Type} [Fintype Row] [DecidableEq Row] [Fintype Value]
    (Choice : Row → Type) [(row : Row) → Fintype (Choice row)]
    (accepts : (row : Row) → Choice row → Value → Prop)
    (moment : ℕ) (row : Row) (values : Fin moment → Value) : ℕ :=
  Fintype.card {choice : Choice row // ∀ index, accepts row choice (values index)}

/-- A finite predicate subtype is counted by its indicator sum. -/
theorem constrainedFiberCard_eq_sum_indicator
    {Row Value : Type} [Fintype Row] [DecidableEq Row] [Fintype Value]
    (Choice : Row → Type) [(row : Row) → Fintype (Choice row)]
    (accepts : (row : Row) → Choice row → Value → Prop)
    (rows : (row : Row) → Choice row) :
    constrainedFiberCard Choice accepts rows =
      ∑ value : Value, if ∀ row, accepts row (rows row) value then 1 else 0 := by
  classical
  unfold constrainedFiberCard
  rw [Fintype.card_subtype]
  symm
  simp

/-- **Exact row-factorized kernel-moment identity.**  The sum of the `moment`-th powers of
complete constrained-fiber cardinalities equals a sum over `moment` value vectors of a product
of simultaneous one-row acceptance counts. -/
theorem sum_constrainedFiberCard_pow_eq_sum_prod_simultaneousRowChoiceCard
    {Row Value : Type} [Fintype Row] [DecidableEq Row] [Fintype Value]
    (Choice : Row → Type) [(row : Row) → Fintype (Choice row)]
    (accepts : (row : Row) → Choice row → Value → Prop)
    (moment : ℕ) :
    (∑ rows : (row : Row) → Choice row,
        constrainedFiberCard Choice accepts rows ^ moment) =
      ∑ values : Fin moment → Value,
        ∏ row : Row,
          simultaneousRowChoiceCard Choice accepts moment row values := by
  classical
  simp_rw [constrainedFiberCard_eq_sum_indicator Choice accepts, Fintype.sum_pow]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro values _
  have indicatorProduct_swap
      (rows : (row : Row) → Choice row) :
      (∏ index : Fin moment,
          if ∀ row, accepts row (rows row) (values index) then 1 else 0) =
        ∏ row : Row,
          if ∀ index, accepts row (rows row) (values index) then 1 else 0 := by
    calc
      (∏ index : Fin moment,
          if ∀ row, accepts row (rows row) (values index) then 1 else 0) =
          if ∀ index, ∀ row, accepts row (rows row) (values index) then 1 else 0 := by
            simpa using (Finset.prod_boole
              (p := fun index : Fin moment =>
                ∀ row, accepts row (rows row) (values index))
              (s := Finset.univ) :
              (∏ index : Fin moment,
                if ∀ row, accepts row (rows row) (values index) then (1 : ℕ) else 0) = _)
      _ = if ∀ row, ∀ index, accepts row (rows row) (values index) then 1 else 0 := by
        by_cases hall : ∀ index, ∀ row, accepts row (rows row) (values index)
        · have hall' : ∀ row, ∀ index, accepts row (rows row) (values index) :=
            fun row index => hall index row
          simp [hall]
        · have hall' : ¬ ∀ row, ∀ index, accepts row (rows row) (values index) := by
            intro swapped
            exact hall (fun index row => swapped row index)
          simp [hall, hall']
      _ = ∏ row : Row,
          if ∀ index, accepts row (rows row) (values index) then 1 else 0 := by
            symm
            simpa using (Finset.prod_boole
              (p := fun row : Row =>
                ∀ index, accepts row (rows row) (values index))
              (s := Finset.univ) :
              (∏ row : Row,
                if ∀ index, accepts row (rows row) (values index) then (1 : ℕ) else 0) = _)
  simp_rw [indicatorProduct_swap]
  calc
    (∑ rows : (row : Row) → Choice row,
        ∏ row : Row,
          if ∀ index, accepts row (rows row) (values index) then 1 else 0) =
        ∏ row : Row,
          ∑ choice : Choice row,
            if ∀ index, accepts row choice (values index) then 1 else 0 :=
      (Fintype.prod_sum (fun row choice =>
        if ∀ index, accepts row choice (values index) then (1 : ℕ) else 0)).symm
    _ = ∏ row : Row,
        simultaneousRowChoiceCard Choice accepts moment row values := by
      apply Finset.prod_congr rfl
      intro row _
      unfold simultaneousRowChoiceCard
      rw [Fintype.card_subtype]
      symm
      simp

end

end FormalProof4FHE.FiniteRowKernelMoment
