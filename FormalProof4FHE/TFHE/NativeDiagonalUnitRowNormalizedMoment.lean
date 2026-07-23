/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.FiniteNormalizedRowMoment
import FormalProof4FHE.TFHE.NativeDiagonalUnitTwoColumnMoment

/-!
# Denominator-Preserving Native TFHE Row Moments

The retained transformed-error fiber is a product of row-local valid-digit fibers.  Its kernel
moment numerator is a sum of products of row-local simultaneous acceptance counts.  This module
keeps the exact fiber denominator and distributes it row-by-row, rather than replacing every
nonempty fiber cardinality by one.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm

noncomputable section

open FormalProof4FHE.TFHE

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing
attribute [local instance] Classical.propDecidable

/-! ## Row-local target fibers -/

/-- A transformed-error vector constant at one supplied ring value.  Row-local definitions only
inspect its value at the active row. -/
def constantTransformedError
    {q degree ringRank levels : ℕ}
    (target : RLWE.Rq q (degree + 1)) :
    Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1) :=
  fun _row ↦ target

/-- Valid omitted digit rows over one explicitly supplied transformed-error coordinate. -/
abbrev CompletableOmittedDigitRowAt
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank levels))
    (target : RLWE.Rq q (degree + 1)) :=
  CompletableOmittedDigitRow (base := base) candidate sourceError
    (constantTransformedError target) selected hunit row

/-- Replacing all inactive transformed-error coordinates by the active coordinate does not
change the valid row subtype. -/
def completableOmittedDigitRowAtEquiv
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank levels)) :
    CompletableOmittedDigitRowAt (base := base) candidate sourceError selected hunit row
        (transformedError row) ≃
      CompletableOmittedDigitRow (base := base) candidate sourceError transformedError selected
        hunit row :=
  Equiv.subtypeEquiv (Equiv.refl _) (by
    intro omitted
    rfl)

/-- Cardinality of one valid row fiber at an explicit transformed-error coordinate. -/
noncomputable def reconstructedRowFiberCardAt
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank levels))
    (target : RLWE.Rq q (degree + 1)) : ℕ :=
  Fintype.card
    (CompletableOmittedDigitRowAt (base := base) candidate sourceError selected hunit row target)

/-- Number of valid rows at an explicit target coordinate that annihilate an entire proposed
tuple. -/
noncomputable def reconstructedSimultaneousRowChoiceCardAt
    {q base degree ringRank levels moment : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank levels))
    (target : RLWE.Rq q (degree + 1))
    (values : Fin moment →
      (Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))) : ℕ :=
  Fintype.card
    {choice : CompletableOmittedDigitRowAt (base := base) candidate sourceError selected hunit
        row target //
      ∀ index, ReconstructedRowAccepts candidate sourceError
        (constantTransformedError target) selected hunit row choice (values index)}

/-- The explicit-coordinate valid-row count agrees with the original vector-indexed count. -/
theorem reconstructedRowFiberCardAt_eq
    {q base degree ringRank levels : ℕ} [NeZero q]
    (candidate : Bool)
    (sourceError transformedError :
      Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1))
    (selected : DifferenceDigitColumn ringRank levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank levels)) :
    reconstructedRowFiberCardAt (base := base) candidate sourceError selected hunit row
        (transformedError row) =
      Fintype.card
        (CompletableOmittedDigitRow (base := base) candidate sourceError transformedError selected
          hunit row) := by
  exact Fintype.card_congr
    (completableOmittedDigitRowAtEquiv candidate sourceError transformedError selected hunit row)

/-- The explicit-coordinate simultaneous acceptance count agrees with the original count. -/
theorem reconstructedSimultaneousRowChoiceCardAt_eq
    {q degree ringRank moment : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank params.levels))
    (values : Fin moment →
      (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1))) :
    reconstructedSimultaneousRowChoiceCardAt (base := params.base) candidate sourceError selected
        hunit row (transformedError row) values =
      reconstructedSimultaneousRowChoiceCard params candidate sourceError transformedError
        selected hunit moment row values := by
  classical
  unfold reconstructedSimultaneousRowChoiceCardAt reconstructedSimultaneousRowChoiceCard
    FormalProof4FHE.FiniteRowKernelMoment.simultaneousRowChoiceCard
  let equivalence :
      {choice : CompletableOmittedDigitRowAt (base := params.base) candidate sourceError selected
          hunit row (transformedError row) //
        ∀ index, ReconstructedRowAccepts candidate sourceError
          (constantTransformedError (transformedError row)) selected hunit row choice
            (values index)} ≃
      {choice : CompletableOmittedDigitRow (base := params.base) candidate sourceError
          transformedError selected hunit row //
        ∀ index, ReconstructedRowAccepts candidate sourceError transformedError selected hunit
          row choice (values index)} :=
    Equiv.subtypeEquiv
      (completableOmittedDigitRowAtEquiv candidate sourceError transformedError selected hunit row)
      (by
        intro choice
        rfl)
  exact Fintype.card_congr equivalence

/-! ## Exact normalized factorization -/

/-- The native retained-fiber cardinality is the product of explicit-coordinate row-fiber
cardinalities. -/
theorem fixedErrorDifferenceFiberCard_eq_prod_reconstructedRowFiberCardAt
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    fixedErrorDifferenceFiberCard params candidate sourceError transformedError =
      ∏ row : Fin (TGSW.rowCount ringRank params.levels),
        reconstructedRowFiberCardAt (base := params.base) candidate sourceError selected hunit row
          (transformedError row) := by
  rw [fixedErrorDifferenceFiberCard_eq_prod_completableRows params hcapacity hbase candidate
    sourceError transformedError selected hunit]
  apply Finset.prod_congr rfl
  intro row _
  exact (reconstructedRowFiberCardAt_eq candidate sourceError transformedError selected hunit
    row).symm

/-- The complete row-factorized moment numerator in one retained transformed-error fiber. -/
noncomputable def fixedErrorDifferenceRowMomentNumerator
    {q degree ringRank : ℕ} [NeZero q]
    (moment : ℕ) (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) : ℕ :=
  ∑ values : Fin moment →
      (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1)),
    ∏ row : Fin (TGSW.rowCount ringRank params.levels),
      reconstructedSimultaneousRowChoiceCard params candidate sourceError transformedError
        selected hunit moment row values

/-- Sum over all transformed-error fibers of their totalized normalized row-kernel moment.  This
is the quantity before removing the zero-tuple baseline and before the outer ciphertext-space
normalization. -/
noncomputable def fixedErrorDifferenceNormalizedRowMomentSum
    {q degree ringRank : ℕ} [NeZero q]
    (moment : ℕ) (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) : ℝ :=
  ∑ transformedError : DiagonalErrorVector q degree ringRank params.levels,
    FormalProof4FHE.FiniteNormalizedRowMoment.normalizedRatio
      (fixedErrorDifferenceFiberCard params candidate sourceError transformedError)
      (fixedErrorDifferenceRowMomentNumerator moment params candidate sourceError transformedError
        selected hunit)

/-- One row's sum, over its transformed-error coordinate, of simultaneous-acceptance density
inside the valid row fiber. -/
noncomputable def reconstructedRowNormalizedMomentSumAt
    {q degree ringRank moment : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank params.levels))
    (values : Fin moment →
      (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1))) : ℝ :=
  ∑ target : RLWE.Rq q (degree + 1),
    FormalProof4FHE.FiniteNormalizedRowMoment.normalizedRatio
      (reconstructedRowFiberCardAt (base := params.base) candidate sourceError selected hunit row
        target)
      (reconstructedSimultaneousRowChoiceCardAt (base := params.base) candidate sourceError
        selected hunit row target values)

/-- **Exact denominator-preserving TFHE row-moment normal form.**  The sum of normalized moments
over complete transformed-error vectors is a sum over proposed tuples of a product of row-local
normalized acceptance sums.  No retained-fiber denominator is discarded. -/
theorem fixedErrorDifferenceNormalizedRowMomentSum_eq_sum_prod_rows
    {q degree ringRank moment : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    fixedErrorDifferenceNormalizedRowMomentSum moment params candidate sourceError selected hunit =
      ∑ values : Fin moment →
          (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1)),
        ∏ row : Fin (TGSW.rowCount ringRank params.levels),
          reconstructedRowNormalizedMomentSumAt params candidate sourceError selected hunit row
            values := by
  classical
  unfold fixedErrorDifferenceNormalizedRowMomentSum
    fixedErrorDifferenceRowMomentNumerator reconstructedRowNormalizedMomentSumAt
  calc
    (∑ transformedError : DiagonalErrorVector q degree ringRank params.levels,
      FormalProof4FHE.FiniteNormalizedRowMoment.normalizedRatio
        (fixedErrorDifferenceFiberCard params candidate sourceError transformedError)
        (∑ values : Fin moment →
            (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1)),
          ∏ row : Fin (TGSW.rowCount ringRank params.levels),
            reconstructedSimultaneousRowChoiceCard params candidate sourceError transformedError
              selected hunit moment row values)) =
      ∑ transformedError : DiagonalErrorVector q degree ringRank params.levels,
        FormalProof4FHE.FiniteNormalizedRowMoment.normalizedRatio
          (∏ row : Fin (TGSW.rowCount ringRank params.levels),
            reconstructedRowFiberCardAt (base := params.base) candidate sourceError selected hunit
              row (transformedError row))
          (∑ values : Fin moment →
              (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1)),
            ∏ row : Fin (TGSW.rowCount ringRank params.levels),
              reconstructedSimultaneousRowChoiceCardAt (base := params.base) candidate sourceError
                selected hunit row (transformedError row) values) := by
      apply Finset.sum_congr rfl
      intro transformedError _
      congr 1
      exact fixedErrorDifferenceFiberCard_eq_prod_reconstructedRowFiberCardAt params hcapacity
        hbase candidate sourceError transformedError selected hunit
    _ = ∑ transformedError : DiagonalErrorVector q degree ringRank params.levels,
        ∑ values : Fin moment →
            (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1)),
          FormalProof4FHE.FiniteNormalizedRowMoment.normalizedProduct
            (fun row : Fin (TGSW.rowCount ringRank params.levels) ↦
              reconstructedRowFiberCardAt (base := params.base) candidate sourceError selected
                hunit row (transformedError row))
            (fun row : Fin (TGSW.rowCount ringRank params.levels) ↦
              reconstructedSimultaneousRowChoiceCardAt (base := params.base) candidate sourceError
                selected hunit row (transformedError row) values) := by
      apply Finset.sum_congr rfl
      intro transformedError _
      rw [FormalProof4FHE.FiniteNormalizedRowMoment.normalizedRatio_sum_prod_eq_sum_normalizedProduct]
    _ = ∑ values : Fin moment →
          (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1)),
        ∏ row : Fin (TGSW.rowCount ringRank params.levels),
          ∑ target : RLWE.Rq q (degree + 1),
            FormalProof4FHE.FiniteNormalizedRowMoment.normalizedRatio
              (reconstructedRowFiberCardAt (base := params.base) candidate sourceError selected
                hunit row target)
              (reconstructedSimultaneousRowChoiceCardAt (base := params.base) candidate sourceError
                selected hunit row target values) := by
      exact FormalProof4FHE.FiniteNormalizedRowMoment.sum_normalizedProduct_eq_sum_prod_rowNormalizedSums_constFiber
        (fun _row : Fin (TGSW.rowCount ringRank params.levels) ↦ RLWE.Rq q (degree + 1))
        (fun row target ↦ reconstructedRowFiberCardAt (base := params.base) candidate sourceError
          selected hunit row target)
        (fun row target values ↦ reconstructedSimultaneousRowChoiceCardAt (base := params.base)
          candidate sourceError selected hunit row target values)

/-! ## Exact return to the native self-collision slice -/

/-- **Denominator-preserving native self-slice identity.**  After the zero tuple removes one
baseline contribution on each nonempty transformed-error fiber, the complete equal-difference
collision loss is the remaining normalized row moment divided by the full difference-ciphertext
space.  This is an equality, not a relaxation by the smallest possible fiber size. -/
theorem fixedErrorDiagonalNormalizedSelfPairCollisionExcess_eq_normalizedRowMoment_sub_nonempty
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    fixedErrorDiagonalNormalizedSelfPairCollisionExcess params candidate sourceError =
      (fixedErrorDifferenceNormalizedRowMomentSum ringRank params candidate sourceError selected
          hunit -
        (fixedErrorDifferenceNonemptyFiberCount params candidate sourceError : ℝ)) /
      (Fintype.card
        (RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ) := by
  rw [fixedErrorDiagonalNormalizedSelfPairCollisionExcess_eq_kernelFiberAverage]
  unfold fixedErrorDifferenceNormalizedRowMomentSum fixedErrorDifferenceRowMomentNumerator
  have hDifferenceCard :
      (0 : ℝ) < Fintype.card
        (RingGSWCiphertext q (degree + 1) ringRank params.levels) := by
    exact_mod_cast Fintype.card_pos
  calc
    (∑ transformedError : DiagonalErrorVector q degree ringRank params.levels,
      if fixedErrorDifferenceFiberCard params candidate sourceError transformedError = 0 then
        0
      else
        (∑ difference : RingGSWCiphertext q (degree + 1) ringRank params.levels,
            if fixedErrorDifferenceSide params candidate sourceError difference =
                transformedError then
              differenceSelfKernelFactor params candidate difference
            else 0) /
          ((Fintype.card
              (RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ) *
            (fixedErrorDifferenceFiberCard params candidate sourceError
              transformedError : ℝ))) =
        ∑ transformedError : DiagonalErrorVector q degree ringRank params.levels,
          (if fixedErrorDifferenceFiberCard params candidate sourceError transformedError = 0 then
            0
          else
            (((∑ values : Fin ringRank →
                  (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1)),
                ∏ row : Fin (TGSW.rowCount ringRank params.levels),
                  reconstructedSimultaneousRowChoiceCard params candidate sourceError
                    transformedError selected hunit ringRank row values : ℕ) : ℝ) -
              (fixedErrorDifferenceFiberCard params candidate sourceError
                transformedError : ℝ)) /
              (fixedErrorDifferenceFiberCard params candidate sourceError
                transformedError : ℝ)) /
            (Fintype.card
              (RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ) := by
      apply Finset.sum_congr rfl
      intro transformedError _
      by_cases hfiber :
          fixedErrorDifferenceFiberCard params candidate sourceError transformedError = 0
      · simp [hfiber]
      · simp only [hfiber, if_false]
        rw [fixedErrorDifferenceKernelSum_eq_simultaneousRowMoment_sub_card params hcapacity
          hbase candidate sourceError transformedError selected hunit]
        rw [← fixedErrorDifferenceFiberCard_eq_prod_completableRows params hcapacity hbase
          candidate sourceError transformedError selected hunit]
        have hFiberCard : (0 : ℝ) <
            fixedErrorDifferenceFiberCard params candidate sourceError transformedError := by
          exact_mod_cast Nat.pos_of_ne_zero hfiber
        field_simp [hDifferenceCard.ne', hFiberCard.ne']
    _ =
        (∑ transformedError : DiagonalErrorVector q degree ringRank params.levels,
          if fixedErrorDifferenceFiberCard params candidate sourceError transformedError = 0 then
            0
          else
            (((∑ values : Fin ringRank →
                  (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1)),
                ∏ row : Fin (TGSW.rowCount ringRank params.levels),
                  reconstructedSimultaneousRowChoiceCard params candidate sourceError
                    transformedError selected hunit ringRank row values : ℕ) : ℝ) -
              (fixedErrorDifferenceFiberCard params candidate sourceError
                transformedError : ℝ)) /
              (fixedErrorDifferenceFiberCard params candidate sourceError
                transformedError : ℝ)) /
          (Fintype.card
            (RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ) := by
      rw [Finset.sum_div]
    _ =
        ((∑ transformedError : DiagonalErrorVector q degree ringRank params.levels,
            FormalProof4FHE.FiniteNormalizedRowMoment.normalizedRatio
              (fixedErrorDifferenceFiberCard params candidate sourceError transformedError)
              (∑ values : Fin ringRank →
                  (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1)),
                ∏ row : Fin (TGSW.rowCount ringRank params.levels),
                  reconstructedSimultaneousRowChoiceCard params candidate sourceError
                    transformedError selected hunit ringRank row values)) -
          (∑ transformedError : DiagonalErrorVector q degree ringRank params.levels,
            if fixedErrorDifferenceFiberCard params candidate sourceError transformedError = 0
            then (0 : ℝ) else 1)) /
        (Fintype.card
          (RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ) := by
      congr 1
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro transformedError _
      exact
        FormalProof4FHE.FiniteNormalizedRowMoment.normalizedDifferenceRatio_eq_sub_nonemptyIndicator
          (fixedErrorDifferenceFiberCard params candidate sourceError transformedError)
          (∑ values : Fin ringRank →
              (Fin (TGSW.rowCount ringRank params.levels) → RLWE.Rq q (degree + 1)),
            ∏ row : Fin (TGSW.rowCount ringRank params.levels),
              reconstructedSimultaneousRowChoiceCard params candidate sourceError transformedError
                selected hunit ringRank row values)
    _ = _ := by
      rw [FormalProof4FHE.FiniteNormalizedRowMoment.sum_nonemptyIndicator_eq_card_filter]
      rfl

end

end FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm
