/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.FiniteRowConvolution
import FormalProof4FHE.Probability.FinitePiAddCharDual
import FormalProof4FHE.TFHE.NativeDiagonalRetainedFiberCharacterMoment
import FormalProof4FHE.TFHE.NativeDiagonalUnitTwoColumnSlice

/-!
# Row-Sum Normal Form for the Native Retained-Fiber Character Moment

At exact gadget capacity and after selecting a unit source-error coordinate, a retained native
difference is an independent family of valid reconstructed digit rows.  This module identifies
the character-annihilation condition on that difference with one zero-sum constraint in the dual
of the native row space: every reconstructed output row contributes a pulled-back character, and
their sum is the character composed with the complete row operator.

Consequently the acceptance cardinality in the distinct-pair character factorial moment is
exactly a finite row-convolution zero fiber.  This preserves the actual retained-fiber product
cardinality and exposes the row-local distributions needed by a quantitative Fourier estimate.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm

noncomputable section

open FormalProof4FHE.TFHE

attribute [local instance] Classical.propDecidable
attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing

variable {q degree ringRank : ℕ}

/-- Tuples of native row-space characters used by the exact distinct-pair moment. -/
abbrev NativeDiagonalRowCharacterTuple (q degree ringRank levels : ℕ) :=
  Fin ringRank → AddChar (NativeDiagonalRow q degree ringRank levels) ℂ

/-- Explicit test values parametrizing the dual of a native row-character tuple. -/
abbrev NativeDiagonalRowCharacterTupleTestValues (q degree ringRank levels : ℕ) :=
  Fin ringRank → NativeDiagonalRow q degree ringRank levels

/-- In ring rank one, summing evaluation over all character tuples is ordinary finite-character
orthogonality on the native row space. -/
theorem sum_rankOneCharacterTuple_apply_eq_ite
    {levels : ℕ} [NeZero q]
    (value : NativeDiagonalRow q degree 1 levels) :
    (∑ characters : NativeDiagonalRowCharacterTuple q degree 1 levels,
        characters 0 value) =
      if value = 0 then (Fintype.card (NativeDiagonalRow q degree 1 levels) : ℂ) else 0 := by
  classical
  let equivalence := Equiv.funUnique (Fin 1)
    (AddChar (NativeDiagonalRow q degree 1 levels) ℂ)
  calc
    (∑ characters : NativeDiagonalRowCharacterTuple q degree 1 levels,
        characters 0 value) =
        ∑ character : AddChar (NativeDiagonalRow q degree 1 levels) ℂ,
          character value := by
      exact Fintype.sum_equiv equivalence _ _ (fun _ => rfl)
    _ = if value = 0 then
          (Fintype.card (NativeDiagonalRow q degree 1 levels) : ℂ) else 0 :=
      AddChar.sum_apply_eq_ite value

/-- Removing the trivial rank-one character tuple subtracts exactly one from the orthogonality
sum. -/
theorem sum_nontrivial_rankOneCharacterTuple_apply_eq_ite
    {levels : ℕ} [NeZero q]
    (value : NativeDiagonalRow q degree 1 levels) :
    (∑ characters ∈ (Finset.univ.erase
        (0 : NativeDiagonalRowCharacterTuple q degree 1 levels)),
      characters 0 value) =
      if value = 0 then
        (Fintype.card (NativeDiagonalRow q degree 1 levels) : ℂ) - 1
      else -1 := by
  classical
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ
    (0 : NativeDiagonalRowCharacterTuple q degree 1 levels))]
  rw [sum_rankOneCharacterTuple_apply_eq_ite]
  by_cases hzero : value = 0 <;> simp [hzero]

/-- Exact rank-one `L²` orthogonality for the source-mode factor `1 + character(value)`. -/
theorem sum_rankOneCharacterTuple_norm_one_add_apply_sq_eq_ite
    {levels : ℕ} [NeZero q]
    (value : NativeDiagonalRow q degree 1 levels) :
    (∑ characters : NativeDiagonalRowCharacterTuple q degree 1 levels,
      ‖1 + characters 0 value‖ ^ 2) =
      if value = 0 then
        4 * (Fintype.card (NativeDiagonalRow q degree 1 levels) : ℝ)
      else
        2 * (Fintype.card (NativeDiagonalRow q degree 1 levels) : ℝ) := by
  classical
  have hpoint (characters : NativeDiagonalRowCharacterTuple q degree 1 levels) :
      ‖1 + characters 0 value‖ ^ 2 =
        2 + 2 * ((characters 0) (-value)).re := by
    rw [Complex.sq_norm, Complex.normSq_add, (characters 0).map_neg_eq_conj]
    simp [Complex.normSq_eq_norm_sq, (characters 0).norm_apply]
    norm_num
  have hcard :
      Fintype.card (NativeDiagonalRowCharacterTuple q degree 1 levels) =
        Fintype.card (NativeDiagonalRow q degree 1 levels) := by
    calc
      Fintype.card (NativeDiagonalRowCharacterTuple q degree 1 levels) =
          Fintype.card (AddChar (NativeDiagonalRow q degree 1 levels) ℂ) :=
        Fintype.card_congr
          (Equiv.funUnique (Fin 1)
            (AddChar (NativeDiagonalRow q degree 1 levels) ℂ))
      _ = Fintype.card (NativeDiagonalRow q degree 1 levels) := AddChar.card_eq
  calc
    (∑ characters : NativeDiagonalRowCharacterTuple q degree 1 levels,
      ‖1 + characters 0 value‖ ^ 2) =
        ∑ characters : NativeDiagonalRowCharacterTuple q degree 1 levels,
          (2 + 2 * ((characters 0) (-value)).re) := by
      apply Finset.sum_congr rfl
      intro characters _
      exact hpoint characters
    _ = 2 * (Fintype.card (NativeDiagonalRowCharacterTuple q degree 1 levels) : ℝ) +
        2 * (∑ characters : NativeDiagonalRowCharacterTuple q degree 1 levels,
          (characters 0) (-value)).re := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp [mul_comm]
    _ = 2 * (Fintype.card (NativeDiagonalRow q degree 1 levels) : ℝ) +
        2 * (∑ characters : NativeDiagonalRowCharacterTuple q degree 1 levels,
          (characters 0) (-value)).re := by rw [hcard]
    _ = if value = 0 then
          4 * (Fintype.card (NativeDiagonalRow q degree 1 levels) : ℝ)
        else
          2 * (Fintype.card (NativeDiagonalRow q degree 1 levels) : ℝ) := by
      rw [sum_rankOneCharacterTuple_apply_eq_ite]
      by_cases hzero : value = 0
      · rw [if_pos hzero, if_pos (by simp [hzero]), Complex.natCast_re]
        ring
      · rw [if_neg hzero, if_neg (by simpa using hzero)]
        simp

/-- Deleting the trivial character removes its squared contribution `4` from the rank-one
source-mode `L²` identity. -/
theorem sum_nontrivial_rankOneCharacterTuple_norm_one_add_apply_sq_eq_ite
    {levels : ℕ} [NeZero q]
    (value : NativeDiagonalRow q degree 1 levels) :
    (∑ characters ∈ (Finset.univ.erase
        (0 : NativeDiagonalRowCharacterTuple q degree 1 levels)),
      ‖1 + characters 0 value‖ ^ 2) =
      if value = 0 then
        4 * (Fintype.card (NativeDiagonalRow q degree 1 levels) : ℝ) - 4
      else
        2 * (Fintype.card (NativeDiagonalRow q degree 1 levels) : ℝ) - 4 := by
  classical
  rw [Finset.sum_erase_eq_sub (Finset.mem_univ
    (0 : NativeDiagonalRowCharacterTuple q degree 1 levels))]
  rw [sum_rankOneCharacterTuple_norm_one_add_apply_sq_eq_ite]
  by_cases hzero : value = 0 <;> simp [hzero] <;> norm_num

/-- Squared triangle inequality in the form used by the phase-aware Fourier estimate. -/
theorem complex_norm_add_sq_le_two_mul
    (left right : ℂ) :
    ‖left + right‖ ^ 2 ≤ 2 * ‖left‖ ^ 2 + 2 * ‖right‖ ^ 2 := by
  have htriangle := norm_add_le left right
  have hleft := norm_nonneg left
  have hright := norm_nonneg right
  have hadd := norm_nonneg (left + right)
  nlinarith [sq_nonneg (‖left‖ - ‖right‖)]

noncomputable local instance nativeDiagonalRowDecidableEq
    (q degree ringRank levels : ℕ) :
    DecidableEq (NativeDiagonalRow q degree ringRank levels) :=
  Classical.decEq _

@[simp]
theorem reconstructedRowOperatorEntry_zero
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank params.levels))
    (omitted : CompletableOmittedDigitRow (base := params.base)
      candidate sourceError transformedError selected hunit row) :
    reconstructedRowOperatorEntry candidate sourceError transformedError selected hunit row
        omitted 0 = 0 := by
  unfold reconstructedRowOperatorEntry
  cases candidate <;> simp [signedValue]

/-- One reconstructed row-operator entry is additive in its native input row. -/
theorem reconstructedRowOperatorEntry_add
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank params.levels))
    (omitted : CompletableOmittedDigitRow (base := params.base)
      candidate sourceError transformedError selected hunit row)
    (left right : NativeDiagonalRow q degree ringRank params.levels) :
    reconstructedRowOperatorEntry candidate sourceError transformedError selected hunit row
        omitted (left + right) =
      reconstructedRowOperatorEntry candidate sourceError transformedError selected hunit row
          omitted left +
        reconstructedRowOperatorEntry candidate sourceError transformedError selected hunit row
          omitted right := by
  unfold reconstructedRowOperatorEntry
  cases candidate <;>
    simp only [Pi.add_apply, signedValue_false, signedValue_true, neg_add_rev, mul_add,
      Finset.sum_add_distrib] <;> ring

/-- An additive character sends a finite additive sum to the corresponding multiplicative
product. -/
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

/-- Additive map containing one reconstructed operator entry in one output row and zero in all
other output rows. -/
noncomputable def reconstructedSingleRowOperatorAddHom
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (row : Fin (TGSW.rowCount ringRank params.levels))
    (omitted : CompletableOmittedDigitRow (base := params.base)
      candidate sourceError transformedError selected hunit row) :
    NativeDiagonalRow q degree ringRank params.levels →+
      NativeDiagonalRow q degree ringRank params.levels where
  toFun value := Pi.single row
    (reconstructedRowOperatorEntry candidate sourceError transformedError selected hunit row
      omitted value)
  map_zero' := by
    simp
  map_add' left right := by
    rw [reconstructedRowOperatorEntry_add params candidate sourceError transformedError
      selected hunit row omitted, Pi.single_add]

/-- Pull one complete-output character back along one reconstructed row contribution. -/
noncomputable def reconstructedRowPulledCharacter
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (character : AddChar (NativeDiagonalRow q degree ringRank params.levels) ℂ)
    (row : Fin (TGSW.rowCount ringRank params.levels))
    (omitted : CompletableOmittedDigitRow (base := params.base)
      candidate sourceError transformedError selected hunit row) :
    AddChar (NativeDiagonalRow q degree ringRank params.levels) ℂ :=
  character.compAddMonoidHom
    (reconstructedSingleRowOperatorAddHom params candidate sourceError transformedError
      selected hunit row omitted)

/-- Coordinatewise pulled-back contribution of one reconstructed row to a tuple of native
characters. -/
noncomputable def reconstructedRowPulledCharacterTuple
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (characters : NativeDiagonalRowCharacterTuple
      q degree ringRank params.levels)
    (row : Fin (TGSW.rowCount ringRank params.levels))
    (omitted : CompletableOmittedDigitRow (base := params.base)
      candidate sourceError transformedError selected hunit row) :
    NativeDiagonalRowCharacterTuple q degree ringRank params.levels :=
  fun coordinate ↦ reconstructedRowPulledCharacter params candidate sourceError
    transformedError selected hunit (characters coordinate) row omitted

/-- The sum of the single-row reconstructed operators is the complete native row operator of
the reconstructed retained difference. -/
theorem sum_reconstructedSingleRowOperator_eq_rowOperator_reconstruct
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (rows : ∀ row : Fin (TGSW.rowCount ringRank params.levels),
      CompletableOmittedDigitRow (base := params.base)
        candidate sourceError transformedError selected hunit row)
    (value : NativeDiagonalRow q degree ringRank params.levels) :
    (∑ row : Fin (TGSW.rowCount ringRank params.levels),
        reconstructedSingleRowOperatorAddHom params candidate sourceError transformedError
          selected hunit row (rows row) value) =
      rowOperator candidate
        (differenceEntryDigits params
          (reconstructFixedErrorDifferenceFromRows params hcapacity hbase candidate sourceError
            transformedError selected hunit rows)) value := by
  change
    (∑ row : Fin (TGSW.rowCount ringRank params.levels),
      Pi.single row
        (reconstructedRowOperatorEntry candidate sourceError transformedError selected hunit row
          (rows row) value)) = _
  rw [Finset.univ_sum_single]
  funext outputRow
  unfold reconstructedRowOperatorEntry rowOperator
  simp only [differenceEntryDigits_reconstructFixedErrorDifferenceFromRows]

/-- Evaluation of the sum of row-local pulled characters is evaluation of the original
character on the complete reconstructed row operator. -/
theorem sum_reconstructedRowPulledCharacter_apply
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (character : AddChar (NativeDiagonalRow q degree ringRank params.levels) ℂ)
    (rows : ∀ row : Fin (TGSW.rowCount ringRank params.levels),
      CompletableOmittedDigitRow (base := params.base)
        candidate sourceError transformedError selected hunit row)
    (value : NativeDiagonalRow q degree ringRank params.levels) :
    (∑ row : Fin (TGSW.rowCount ringRank params.levels),
        reconstructedRowPulledCharacter params candidate sourceError transformedError selected
          hunit character row (rows row)) value =
      character
        (rowOperator candidate
          (differenceEntryDigits params
            (reconstructFixedErrorDifferenceFromRows params hcapacity hbase candidate sourceError
              transformedError selected hunit rows)) value) := by
  rw [← sum_reconstructedSingleRowOperator_eq_rowOperator_reconstruct params hcapacity hbase
    candidate sourceError transformedError selected hunit rows value]
  rw [AddChar.sum_apply]
  simp only [reconstructedRowPulledCharacter, AddChar.compAddMonoidHom_apply]
  exact (addChar_apply_finset_sum character Finset.univ fun row ↦
    reconstructedSingleRowOperatorAddHom params candidate sourceError transformedError selected
      hunit row (rows row) value).symm

/-- One character annihilates the reconstructed complete operator iff its row-local pulled-back
characters sum to the trivial character. -/
theorem rowCharacterAnnihilates_reconstruct_iff_rowPulledSum_eq_zero
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (character : AddChar (NativeDiagonalRow q degree ringRank params.levels) ℂ)
    (rows : ∀ row : Fin (TGSW.rowCount ringRank params.levels),
      CompletableOmittedDigitRow (base := params.base)
        candidate sourceError transformedError selected hunit row) :
    rowCharacterAnnihilatesDifference params candidate character
        (reconstructFixedErrorDifferenceFromRows params hcapacity hbase candidate sourceError
          transformedError selected hunit rows) ↔
      (∑ row : Fin (TGSW.rowCount ringRank params.levels),
        reconstructedRowPulledCharacter params candidate sourceError transformedError selected
          hunit character row (rows row)) = 0 := by
  rw [AddChar.eq_zero_iff]
  constructor <;> intro hvalue value
  · rw [sum_reconstructedRowPulledCharacter_apply params hcapacity hbase candidate sourceError
      transformedError selected hunit character rows value]
    exact hvalue value
  · rw [← sum_reconstructedRowPulledCharacter_apply params hcapacity hbase candidate sourceError
      transformedError selected hunit character rows value]
    exact hvalue value

/-- A tuple accepts the reconstructed difference iff the tuple-valued row contributions sum to
zero. -/
theorem rowCharacterTupleAccepts_reconstruct_iff_rowPulledTupleSum_eq_zero
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (characters : NativeDiagonalRowCharacterTuple q degree ringRank params.levels)
    (rows : ∀ row : Fin (TGSW.rowCount ringRank params.levels),
      CompletableOmittedDigitRow (base := params.base)
        candidate sourceError transformedError selected hunit row) :
    rowCharacterTupleAcceptsDifference params candidate characters
        (reconstructFixedErrorDifferenceFromRows params hcapacity hbase candidate sourceError
          transformedError selected hunit rows) ↔
      (∑ row : Fin (TGSW.rowCount ringRank params.levels),
        reconstructedRowPulledCharacterTuple params candidate sourceError transformedError
          selected hunit characters row (rows row)) = 0 := by
  constructor
  · intro haccepts
    funext coordinate
    simp only [Finset.sum_apply, Pi.zero_apply, reconstructedRowPulledCharacterTuple]
    exact
      (rowCharacterAnnihilates_reconstruct_iff_rowPulledSum_eq_zero params hcapacity hbase
        candidate sourceError transformedError selected hunit (characters coordinate) rows).1
        (haccepts coordinate)
  · intro hsum coordinate
    apply
      (rowCharacterAnnihilates_reconstruct_iff_rowPulledSum_eq_zero params hcapacity hbase
        candidate sourceError transformedError selected hunit (characters coordinate) rows).2
    have hcoordinate := congrFun hsum coordinate
    simpa only [Finset.sum_apply, Pi.zero_apply, reconstructedRowPulledCharacterTuple] using
      hcoordinate

/-- The independent family of valid reconstructed rows is equivalent to the native retained
difference fiber. -/
noncomputable def fixedErrorDifferenceRowsEquivFiber
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    (∀ row : Fin (TGSW.rowCount ringRank params.levels),
      CompletableOmittedDigitRow (base := params.base)
        candidate sourceError transformedError selected hunit row) ≃
      FixedErrorDifferenceFiber params candidate sourceError transformedError :=
  (completableOmittedDigitTensorEquivRows (base := params.base) candidate sourceError
    transformedError selected hunit).symm.trans
      (fixedErrorDifferenceFiberEquivCompletableOmitted params hcapacity hbase candidate
        sourceError transformedError selected hunit).symm

@[simp]
theorem fixedErrorDifferenceRowsEquivFiber_apply_coe
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (rows : ∀ row : Fin (TGSW.rowCount ringRank params.levels),
      CompletableOmittedDigitRow (base := params.base)
        candidate sourceError transformedError selected hunit row) :
    (fixedErrorDifferenceRowsEquivFiber params hcapacity hbase candidate sourceError
      transformedError selected hunit rows).1 =
      reconstructFixedErrorDifferenceFromRows params hcapacity hbase candidate sourceError
        transformedError selected hunit rows := rfl

/-- Exact row-convolution zero-fiber cardinality for one tuple of native characters. -/
noncomputable def reconstructedCharacterTupleRowSumZeroCard
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (characters : NativeDiagonalRowCharacterTuple q degree ringRank params.levels) : ℕ :=
  Nat.card
    {rows : ∀ row : Fin (TGSW.rowCount ringRank params.levels),
        CompletableOmittedDigitRow (base := params.base)
          candidate sourceError transformedError selected hunit row //
      (∑ row : Fin (TGSW.rowCount ringRank params.levels),
        reconstructedRowPulledCharacterTuple params candidate sourceError transformedError
          selected hunit characters row (rows row)) = 0}

/-- **Exact retained character-count row-sum normal form.**  The number of retained native
differences accepted by a character tuple is the zero fiber of the sum of its independent
row-local pulled-character contributions. -/
theorem fixedErrorDifferenceCharacterTupleAcceptanceCard_eq_rowSumZeroCard
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (characters : NativeDiagonalRowCharacterTuple q degree ringRank params.levels) :
    fixedErrorDifferenceCharacterTupleAcceptanceCard params candidate sourceError
        transformedError characters =
      reconstructedCharacterTupleRowSumZeroCard params candidate sourceError transformedError
        selected hunit characters := by
  unfold fixedErrorDifferenceCharacterTupleAcceptanceCard
    reconstructedCharacterTupleRowSumZeroCard
  apply Nat.card_congr
  let rowEquiv := fixedErrorDifferenceRowsEquivFiber params hcapacity hbase candidate sourceError
    transformedError selected hunit
  exact
    (Equiv.subtypeEquiv rowEquiv (fun rows ↦ by
      change
        (∑ row : Fin (TGSW.rowCount ringRank params.levels),
          reconstructedRowPulledCharacterTuple params candidate sourceError transformedError
            selected hunit characters row (rows row)) = 0 ↔
          rowCharacterTupleAcceptsDifference params candidate characters
            (reconstructFixedErrorDifferenceFromRows params hcapacity hbase candidate sourceError
              transformedError selected hunit rows)
      exact
        (rowCharacterTupleAccepts_reconstruct_iff_rowPulledTupleSum_eq_zero params hcapacity
          hbase candidate sourceError transformedError selected hunit characters rows).symm)).symm

/-- Row-local Fourier coefficient of the reconstructed zero-sum convolution for a fixed tuple of
native operator characters. -/
noncomputable def reconstructedCharacterTupleRowFourierCoefficient
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (characters : NativeDiagonalRowCharacterTuple q degree ringRank params.levels)
    (dualCharacter : AddChar
      (NativeDiagonalRowCharacterTuple q degree ringRank params.levels) ℂ)
    (row : Fin (TGSW.rowCount ringRank params.levels)) : ℂ :=
  ∑ omitted : CompletableOmittedDigitRow (base := params.base)
      candidate sourceError transformedError selected hunit row,
    dualCharacter
      (reconstructedRowPulledCharacterTuple params candidate sourceError transformedError
        selected hunit characters row omitted)

/-- Concrete form of a row-Fourier coefficient after parametrizing the second dual by explicit
native test rows. -/
noncomputable def reconstructedCharacterTupleRowTestFourierCoefficient
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (characters : NativeDiagonalRowCharacterTuple q degree ringRank params.levels)
    (testValues : NativeDiagonalRowCharacterTupleTestValues
      q degree ringRank params.levels)
    (row : Fin (TGSW.rowCount ringRank params.levels)) : ℂ :=
  ∑ omitted : CompletableOmittedDigitRow (base := params.base)
      candidate sourceError transformedError selected hunit row,
    ∏ coordinate : Fin ringRank,
      characters coordinate
        (reconstructedSingleRowOperatorAddHom params candidate sourceError transformedError
          selected hunit row omitted (testValues coordinate))

/-- Evaluating an abstract second-dual character at its explicit test-row representative gives
the concrete product of original character evaluations. -/
@[simp]
theorem reconstructedCharacterTupleRowFourierCoefficient_evaluationEquiv
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (characters : NativeDiagonalRowCharacterTuple q degree ringRank params.levels)
    (testValues : NativeDiagonalRowCharacterTupleTestValues
      q degree ringRank params.levels)
    (row : Fin (TGSW.rowCount ringRank params.levels)) :
    reconstructedCharacterTupleRowFourierCoefficient params candidate sourceError
        transformedError selected hunit characters
          (FormalProof4FHE.FinitePiAddCharDual.evaluationEquiv testValues) row =
      reconstructedCharacterTupleRowTestFourierCoefficient params candidate sourceError
        transformedError selected hunit characters testValues row := by
  unfold reconstructedCharacterTupleRowFourierCoefficient
    reconstructedCharacterTupleRowTestFourierCoefficient
  apply Finset.sum_congr rfl
  intro omitted _
  rw [FormalProof4FHE.FinitePiAddCharDual.evaluationEquiv_apply_character]
  apply Finset.prod_congr rfl
  intro coordinate _
  rfl

/-- In the canonical rank-one setting the concrete row coefficient is a single original native
character evaluated on one reconstructed output-row contribution. -/
theorem reconstructedCharacterTupleRowTestFourierCoefficient_ringRank_one
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree 1 params.levels)
    (selected : DifferenceDigitColumn 1 params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (characters : NativeDiagonalRowCharacterTuple q degree 1 params.levels)
    (testValues : NativeDiagonalRowCharacterTupleTestValues q degree 1 params.levels)
    (row : Fin (TGSW.rowCount 1 params.levels)) :
    reconstructedCharacterTupleRowTestFourierCoefficient params candidate sourceError
        transformedError selected hunit characters testValues row =
      ∑ omitted : CompletableOmittedDigitRow (base := params.base)
          candidate sourceError transformedError selected hunit row,
        characters 0
          (Pi.single row
            (reconstructedRowOperatorEntry candidate sourceError transformedError selected hunit
              row omitted (testValues 0))) := by
  unfold reconstructedCharacterTupleRowTestFourierCoefficient
    reconstructedSingleRowOperatorAddHom
  simp

/-- In ring rank one, eliminating the forced selected digit exposes the exact minor-weighted
phase inside every term of the row-local character sum. -/
theorem reconstructedCharacterTupleRowTestFourierCoefficient_ringRank_one_eq_minorPhase
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree 1 params.levels)
    (selected : DifferenceDigitColumn 1 params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (characters : NativeDiagonalRowCharacterTuple q degree 1 params.levels)
    (testValues : NativeDiagonalRowCharacterTupleTestValues q degree 1 params.levels)
    (row : Fin (TGSW.rowCount 1 params.levels)) :
    reconstructedCharacterTupleRowTestFourierCoefficient params candidate sourceError
        transformedError selected hunit characters testValues row =
      ∑ omitted : CompletableOmittedDigitRow (base := params.base)
          candidate sourceError transformedError selected hunit row,
        characters 0
          (Pi.single row
            (reconstructedRowRetainedOffsetMinorPhase candidate sourceError transformedError
              selected hunit row omitted (testValues 0))) := by
  rw [reconstructedCharacterTupleRowTestFourierCoefficient_ringRank_one]
  apply Finset.sum_congr rfl
  intro omitted _
  rw [reconstructedRowOperatorEntry_eq_retainedOffsetMinorPhase]

/-- The fixed retained offset factors completely out of the rank-one character sum. -/
theorem reconstructedCharacterTupleRowTestFourierCoefficient_ringRank_one_eq_offset_mul_minorSum
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree 1 params.levels)
    (selected : DifferenceDigitColumn 1 params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (characters : NativeDiagonalRowCharacterTuple q degree 1 params.levels)
    (testValues : NativeDiagonalRowCharacterTupleTestValues q degree 1 params.levels)
    (row : Fin (TGSW.rowCount 1 params.levels)) :
    reconstructedCharacterTupleRowTestFourierCoefficient params candidate sourceError
        transformedError selected hunit characters testValues row =
      characters 0
          (Pi.single row
            (reconstructedRowRetainedOffset candidate sourceError transformedError selected
              hunit row (testValues 0))) *
        ∑ omitted : CompletableOmittedDigitRow (base := params.base)
            candidate sourceError transformedError selected hunit row,
          characters 0
            (Pi.single row
              (reconstructedRowMinorPhase candidate sourceError transformedError selected hunit
                row omitted (testValues 0))) := by
  rw [reconstructedCharacterTupleRowTestFourierCoefficient_ringRank_one_eq_minorPhase,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro omitted _
  rw [reconstructedRowRetainedOffsetMinorPhase_eq]
  simp only [Pi.single_add, AddChar.map_add_eq_mul]

/-- The digit-independent offset has unit character norm, so the size of the concrete rank-one
Fourier coefficient is exactly the size of the pure minor-phase character sum. -/
theorem norm_reconstructedCharacterTupleRowTestFourierCoefficient_ringRank_one_eq_minorSum
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree 1 params.levels)
    (selected : DifferenceDigitColumn 1 params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (characters : NativeDiagonalRowCharacterTuple q degree 1 params.levels)
    (testValues : NativeDiagonalRowCharacterTupleTestValues q degree 1 params.levels)
    (row : Fin (TGSW.rowCount 1 params.levels)) :
    ‖reconstructedCharacterTupleRowTestFourierCoefficient params candidate sourceError
        transformedError selected hunit characters testValues row‖ =
      ‖∑ omitted : CompletableOmittedDigitRow (base := params.base)
          candidate sourceError transformedError selected hunit row,
        characters 0
          (Pi.single row
            (reconstructedRowMinorPhase candidate sourceError transformedError selected hunit row
              omitted (testValues 0)))‖ := by
  rw [reconstructedCharacterTupleRowTestFourierCoefficient_ringRank_one_eq_offset_mul_minorSum,
    norm_mul, (characters 0).norm_apply, one_mul]

/-- The concrete rank-one test tuple obtained from the retained source-error row is nonzero as
soon as the selected source-error coordinate is a unit. -/
theorem rankOneSourceErrorTestValues_ne_zero
    [NeZero q] [Nontrivial (RLWE.Rq q (degree + 1))]
    (params : Gadget.Base.Parameters q)
    (sourceError : DiagonalErrorVector q degree 1 params.levels)
    (selected : DifferenceDigitColumn 1 params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    (fun _ : Fin 1 => sourceError :
      NativeDiagonalRowCharacterTupleTestValues q degree 1 params.levels) ≠ 0 := by
  intro hzero
  have hcoordinate := congrFun (congrFun hzero 0) (finProdFinEquiv selected)
  exact hunit.ne_zero (by simpa using hcoordinate)

/-- The source-error Fourier coefficient has an exact phase: its magnitude is the valid-row
cardinality and its phase is the outer character evaluated on the retained transformed-error
coordinate. -/
theorem reconstructedCharacterTupleRowTestFourierCoefficient_sourceError_eq_card_mul_character
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree 1 params.levels)
    (selected : DifferenceDigitColumn 1 params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (characters : NativeDiagonalRowCharacterTuple q degree 1 params.levels)
    (row : Fin (TGSW.rowCount 1 params.levels)) :
    reconstructedCharacterTupleRowTestFourierCoefficient params candidate sourceError
        transformedError selected hunit characters (fun _ : Fin 1 => sourceError) row =
      (Fintype.card (CompletableOmittedDigitRow (base := params.base)
          candidate sourceError transformedError selected hunit row) : ℂ) *
        characters 0 (Pi.single row (transformedError row)) := by
  rw [reconstructedCharacterTupleRowTestFourierCoefficient_ringRank_one]
  simp only [reconstructedRowOperatorEntry_sourceError]
  simp

/-- The nonzero source-error test tuple is an unavoidable full-size Fourier spike: all of its
two-column minors vanish, so the row coefficient has norm equal to the complete valid-row
cardinality. -/
theorem norm_reconstructedCharacterTupleRowTestFourierCoefficient_sourceError_eq_card
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree 1 params.levels)
    (selected : DifferenceDigitColumn 1 params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (characters : NativeDiagonalRowCharacterTuple q degree 1 params.levels)
    (row : Fin (TGSW.rowCount 1 params.levels)) :
    ‖reconstructedCharacterTupleRowTestFourierCoefficient params candidate sourceError
        transformedError selected hunit characters (fun _ : Fin 1 => sourceError) row‖ =
      Fintype.card (CompletableOmittedDigitRow (base := params.base)
        candidate sourceError transformedError selected hunit row) := by
  rw [norm_reconstructedCharacterTupleRowTestFourierCoefficient_ringRank_one_eq_minorSum]
  simp

/-- Every abstract dual character occurring in the row convolution has a unique explicit native
test-row representative. -/
theorem existsUnique_testValues_representing_nativeCharacterTupleDual
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (dualCharacter : AddChar
      (NativeDiagonalRowCharacterTuple q degree ringRank params.levels) ℂ) :
    ∃! testValues : NativeDiagonalRowCharacterTupleTestValues
        q degree ringRank params.levels,
      FormalProof4FHE.FinitePiAddCharDual.evaluationEquiv testValues = dualCharacter := by
  let equivalence := FormalProof4FHE.FinitePiAddCharDual.evaluationEquiv
    (Index := Fin ringRank)
    (Value := NativeDiagonalRow q degree ringRank params.levels)
  refine ⟨equivalence.symm dualCharacter, equivalence.apply_symm_apply dualCharacter, ?_⟩
  intro testValues htestValues
  exact equivalence.injective
    (htestValues.trans (equivalence.apply_symm_apply dualCharacter).symm)

/-- Product of the actual valid reconstructed-row choice cardinalities in one retained fiber. -/
noncomputable def reconstructedValidRowChoiceCardProduct
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) : ℕ :=
  ∏ row : Fin (TGSW.rowCount ringRank params.levels),
    Fintype.card
      (CompletableOmittedDigitRow (base := params.base)
        candidate sourceError transformedError selected hunit row)

/-- Across all reconstructed rows, the structured source-error Fourier mode is exactly the
complete valid-fiber product times one outer-character phase on the transformed-error vector. -/
theorem prod_reconstructedCharacterTupleRowTestFourierCoefficient_sourceError_eq
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree 1 params.levels)
    (selected : DifferenceDigitColumn 1 params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (characters : NativeDiagonalRowCharacterTuple q degree 1 params.levels) :
    (∏ row : Fin (TGSW.rowCount 1 params.levels),
        reconstructedCharacterTupleRowTestFourierCoefficient params candidate sourceError
          transformedError selected hunit characters (fun _ : Fin 1 => sourceError) row) =
      (reconstructedValidRowChoiceCardProduct params candidate sourceError transformedError
          selected hunit : ℂ) * characters 0 transformedError := by
  simp_rw [reconstructedCharacterTupleRowTestFourierCoefficient_sourceError_eq_card_mul_character]
  rw [Finset.prod_mul_distrib]
  have hcard :
      (∏ row : Fin (TGSW.rowCount 1 params.levels),
          (Fintype.card (CompletableOmittedDigitRow (base := params.base)
            candidate sourceError transformedError selected hunit row) : ℂ)) =
        (reconstructedValidRowChoiceCardProduct params candidate sourceError transformedError
          selected hunit : ℂ) := by
    unfold reconstructedValidRowChoiceCardProduct
    rw [Nat.cast_prod]
  rw [hcard]
  apply congrArg (fun phase : ℂ =>
    (reconstructedValidRowChoiceCardProduct params candidate sourceError transformedError
      selected hunit : ℂ) * phase)
  calc
    (∏ row : Fin (TGSW.rowCount 1 params.levels),
        characters 0 (Pi.single row (transformedError row))) =
        characters 0
          (∑ row : Fin (TGSW.rowCount 1 params.levels),
            Pi.single row (transformedError row)) :=
      (addChar_apply_finset_sum (characters 0) Finset.univ
        (fun row => Pi.single row (transformedError row))).symm
    _ = characters 0 transformedError := by rw [Finset.univ_sum_single]

/-- The TFHE-specific zero-sum count is definitionally the generic dependent-row convolution
fiber, up to the instance-independent presentation of finite cardinality. -/
theorem reconstructedCharacterTupleRowSumZeroCard_eq_finiteRowConvolution
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (characters : NativeDiagonalRowCharacterTuple q degree ringRank params.levels) :
    reconstructedCharacterTupleRowSumZeroCard params candidate sourceError transformedError
        selected hunit characters =
      FormalProof4FHE.FiniteRowConvolution.rowSumZeroFiberCard
        (fun row : Fin (TGSW.rowCount ringRank params.levels) ↦
          CompletableOmittedDigitRow (base := params.base)
            candidate sourceError transformedError selected hunit row)
        (fun row omitted ↦
          reconstructedRowPulledCharacterTuple params candidate sourceError transformedError
            selected hunit characters row omitted) := by
  unfold reconstructedCharacterTupleRowSumZeroCard
    FormalProof4FHE.FiniteRowConvolution.rowSumZeroFiberCard
  rfl

/-- **Exact native retained-fiber row Fourier factorization.**  For every character tuple from
the cokernel moment, its acceptance cardinality is controlled by a second character transform
whose coefficients factor over independently reconstructed valid rows. -/
theorem card_mul_reconstructedCharacterTupleRowSumZeroCard_eq_sum_prod_rowFourierCoefficient
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (characters : NativeDiagonalRowCharacterTuple q degree ringRank params.levels) :
    (Fintype.card
        (NativeDiagonalRowCharacterTuple q degree ringRank params.levels) : ℂ) *
        (reconstructedCharacterTupleRowSumZeroCard params candidate sourceError transformedError
          selected hunit characters : ℂ) =
      ∑ dualCharacter : AddChar
          (NativeDiagonalRowCharacterTuple q degree ringRank params.levels) ℂ,
        ∏ row : Fin (TGSW.rowCount ringRank params.levels),
          reconstructedCharacterTupleRowFourierCoefficient params candidate sourceError
            transformedError selected hunit characters dualCharacter row := by
  rw [reconstructedCharacterTupleRowSumZeroCard_eq_finiteRowConvolution]
  simpa only [reconstructedCharacterTupleRowFourierCoefficient] using
    (FormalProof4FHE.FiniteRowConvolution.card_mul_rowSumZeroFiberCard_eq_sum_prod_rowCharacterSum
        (Choice := fun row : Fin (TGSW.rowCount ringRank params.levels) ↦
          CompletableOmittedDigitRow (base := params.base)
            candidate sourceError transformedError selected hunit row)
        (contribution := fun row omitted ↦
          reconstructedRowPulledCharacterTuple params candidate sourceError transformedError
            selected hunit characters row omitted))

/-- Centered exact native factorization.  The trivial dual character contributes the precise
valid-row product, leaving only nontrivial Fourier coefficients. -/
theorem card_mul_reconstructedCharacterTupleRowSumZeroCard_sub_validRowProduct_eq_nontrivial
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (characters : NativeDiagonalRowCharacterTuple q degree ringRank params.levels) :
    (Fintype.card
        (NativeDiagonalRowCharacterTuple q degree ringRank params.levels) : ℂ) *
        (reconstructedCharacterTupleRowSumZeroCard params candidate sourceError transformedError
          selected hunit characters : ℂ) -
        (reconstructedValidRowChoiceCardProduct params candidate sourceError transformedError
          selected hunit : ℂ) =
      ∑ dualCharacter ∈ (Finset.univ.erase
          (0 : AddChar
            (NativeDiagonalRowCharacterTuple q degree ringRank params.levels) ℂ)),
        ∏ row : Fin (TGSW.rowCount ringRank params.levels),
          reconstructedCharacterTupleRowFourierCoefficient params candidate sourceError
            transformedError selected hunit characters dualCharacter row := by
  rw [reconstructedCharacterTupleRowSumZeroCard_eq_finiteRowConvolution]
  simpa only [reconstructedCharacterTupleRowFourierCoefficient,
    reconstructedValidRowChoiceCardProduct,
    FormalProof4FHE.FiniteRowConvolution.rowChoiceCardProduct] using
      (FormalProof4FHE.FiniteRowConvolution.card_mul_rowSumZeroFiberCard_sub_rowChoiceCardProduct_eq_nontrivialFourierSum
          (Choice := fun row : Fin (TGSW.rowCount ringRank params.levels) ↦
            CompletableOmittedDigitRow (base := params.base)
              candidate sourceError transformedError selected hunit row)
          (contribution := fun row omitted ↦
            reconstructedRowPulledCharacterTuple params candidate sourceError transformedError
              selected hunit characters row omitted))

/-- Reindex the exact centered factorization itself, without taking norms, by concrete nonzero
test-value tuples. -/
theorem card_mul_reconstructedCharacterTupleRowSumZeroCard_sub_validRowProduct_eq_testValues
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (characters : NativeDiagonalRowCharacterTuple q degree ringRank params.levels) :
    (Fintype.card
        (NativeDiagonalRowCharacterTuple q degree ringRank params.levels) : ℂ) *
        (reconstructedCharacterTupleRowSumZeroCard params candidate sourceError transformedError
          selected hunit characters : ℂ) -
        (reconstructedValidRowChoiceCardProduct params candidate sourceError transformedError
          selected hunit : ℂ) =
      ∑ testValues ∈ (Finset.univ.erase
          (0 : NativeDiagonalRowCharacterTupleTestValues
            q degree ringRank params.levels)),
        ∏ row : Fin (TGSW.rowCount ringRank params.levels),
          reconstructedCharacterTupleRowTestFourierCoefficient params candidate sourceError
            transformedError selected hunit characters testValues row := by
  rw [card_mul_reconstructedCharacterTupleRowSumZeroCard_sub_validRowProduct_eq_nontrivial]
  simpa only [reconstructedCharacterTupleRowFourierCoefficient_evaluationEquiv] using
    (FormalProof4FHE.FinitePiAddCharDual.sum_ne_zero_evaluationEquiv
      (Index := Fin ringRank)
      (Value := NativeDiagonalRow q degree ringRank params.levels)
      (summand := fun dualCharacter ↦
        ∏ row : Fin (TGSW.rowCount ringRank params.levels),
          reconstructedCharacterTupleRowFourierCoefficient params candidate sourceError
            transformedError selected hunit characters dualCharacter row))

/-- Phase-aware rank-one split of the centered transform.  The unavoidable source-error mode is
kept exactly as `fiberCard * character(transformedError)`; only the remaining nonzero test tuples
are left for cancellation estimates. -/
theorem card_mul_reconstructedCharacterTupleRowSumZeroCard_sub_validRowProduct_eq_sourceMode_add
    [NeZero q] [Nontrivial (RLWE.Rq q (degree + 1))]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree 1 params.levels)
    (selected : DifferenceDigitColumn 1 params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (characters : NativeDiagonalRowCharacterTuple q degree 1 params.levels) :
    (Fintype.card (NativeDiagonalRowCharacterTuple q degree 1 params.levels) : ℂ) *
        (reconstructedCharacterTupleRowSumZeroCard params candidate sourceError transformedError
          selected hunit characters : ℂ) -
        (reconstructedValidRowChoiceCardProduct params candidate sourceError transformedError
          selected hunit : ℂ) =
      (reconstructedValidRowChoiceCardProduct params candidate sourceError transformedError
          selected hunit : ℂ) * characters 0 transformedError +
        ∑ testValues ∈ ((Finset.univ.erase
            (0 : NativeDiagonalRowCharacterTupleTestValues q degree 1 params.levels)).erase
              (fun _ : Fin 1 => sourceError)),
          ∏ row : Fin (TGSW.rowCount 1 params.levels),
            reconstructedCharacterTupleRowTestFourierCoefficient params candidate sourceError
              transformedError selected hunit characters testValues row := by
  rw [card_mul_reconstructedCharacterTupleRowSumZeroCard_sub_validRowProduct_eq_testValues]
  let sourceTest : NativeDiagonalRowCharacterTupleTestValues q degree 1 params.levels :=
    fun _ => sourceError
  let testSet := Finset.univ.erase
    (0 : NativeDiagonalRowCharacterTupleTestValues q degree 1 params.levels)
  let term := fun testValues :
      NativeDiagonalRowCharacterTupleTestValues q degree 1 params.levels =>
    ∏ row : Fin (TGSW.rowCount 1 params.levels),
      reconstructedCharacterTupleRowTestFourierCoefficient params candidate sourceError
        transformedError selected hunit characters testValues row
  have hsourceTest : sourceTest ≠ 0 :=
    rankOneSourceErrorTestValues_ne_zero params sourceError selected hunit
  have hmem : sourceTest ∈ testSet := by simp [testSet, hsourceTest]
  change (∑ testValues ∈ testSet, term testValues) = _
  calc
    (∑ testValues ∈ testSet, term testValues) =
        (∑ testValues ∈ testSet.erase sourceTest, term testValues) + term sourceTest :=
      (Finset.sum_erase_add testSet term hmem).symm
    _ = term sourceTest +
        ∑ testValues ∈ testSet.erase sourceTest, term testValues := by ac_rfl
    _ = (reconstructedValidRowChoiceCardProduct params candidate sourceError transformedError
          selected hunit : ℂ) * characters 0 transformedError +
        ∑ testValues ∈ testSet.erase sourceTest, term testValues := by
      rw [show term sourceTest =
          (reconstructedValidRowChoiceCardProduct params candidate sourceError transformedError
            selected hunit : ℂ) * characters 0 transformedError by
        exact prod_reconstructedCharacterTupleRowTestFourierCoefficient_sourceError_eq
          params candidate sourceError transformedError selected hunit characters]
    _ = _ := rfl

/-- The second-dual remainder after deleting both the trivial test tuple and the structured
source-error test tuple. -/
noncomputable def reconstructedCharacterTupleRowFourierNonSourceRemainder
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree 1 params.levels)
    (selected : DifferenceDigitColumn 1 params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (characters : NativeDiagonalRowCharacterTuple q degree 1 params.levels) : ℂ :=
  ∑ testValues ∈ ((Finset.univ.erase
      (0 : NativeDiagonalRowCharacterTupleTestValues q degree 1 params.levels)).erase
        (fun _ : Fin 1 => sourceError)),
    ∏ row : Fin (TGSW.rowCount 1 params.levels),
      reconstructedCharacterTupleRowTestFourierCoefficient params candidate sourceError
        transformedError selected hunit characters testValues row

/-- Exact outer-character `L²` factor of the structured rank-one source mode. -/
noncomputable def rankOneSourceModeSquareFactor
    {levels : ℕ} [NeZero q]
    (transformedError : NativeDiagonalRow q degree 1 levels) : ℝ :=
  if transformedError = 0 then
    4 * (Fintype.card (NativeDiagonalRow q degree 1 levels) : ℝ) - 4
  else
    2 * (Fintype.card (NativeDiagonalRow q degree 1 levels) : ℝ) - 4

/-- Squared `L²` mass, over nontrivial outer characters, of the non-source second-dual
remainder. -/
noncomputable def reconstructedCharacterTupleRowFourierNonSourceSquareMass
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree 1 params.levels)
    (selected : DifferenceDigitColumn 1 params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) : ℝ :=
  ∑ characters ∈ (Finset.univ.erase
      (0 : NativeDiagonalRowCharacterTuple q degree 1 params.levels)),
    ‖reconstructedCharacterTupleRowFourierNonSourceRemainder params candidate sourceError
      transformedError selected hunit characters‖ ^ 2

theorem sum_nontrivial_rankOneCharacterTuple_norm_one_add_apply_sq_eq_sourceFactor
    {levels : ℕ} [NeZero q]
    (value : NativeDiagonalRow q degree 1 levels) :
    (∑ characters ∈ (Finset.univ.erase
        (0 : NativeDiagonalRowCharacterTuple q degree 1 levels)),
      ‖1 + characters 0 value‖ ^ 2) =
      rankOneSourceModeSquareFactor value := by
  rw [sum_nontrivial_rankOneCharacterTuple_norm_one_add_apply_sq_eq_ite]
  by_cases hzero : value = 0 <;>
    simp only [rankOneSourceModeSquareFactor, hzero, if_pos]

/-- Named phase-aware centered identity with only the non-source remainder left opaque. -/
theorem card_mul_reconstructedCharacterTupleRowSumZeroCard_sub_validRowProduct_eq_sourceMode_add_remainder
    [NeZero q] [Nontrivial (RLWE.Rq q (degree + 1))]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree 1 params.levels)
    (selected : DifferenceDigitColumn 1 params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (characters : NativeDiagonalRowCharacterTuple q degree 1 params.levels) :
    (Fintype.card (NativeDiagonalRowCharacterTuple q degree 1 params.levels) : ℂ) *
        (reconstructedCharacterTupleRowSumZeroCard params candidate sourceError transformedError
          selected hunit characters : ℂ) -
        (reconstructedValidRowChoiceCardProduct params candidate sourceError transformedError
          selected hunit : ℂ) =
      (reconstructedValidRowChoiceCardProduct params candidate sourceError transformedError
          selected hunit : ℂ) * characters 0 transformedError +
        reconstructedCharacterTupleRowFourierNonSourceRemainder params candidate sourceError
          transformedError selected hunit characters := by
  simpa only [reconstructedCharacterTupleRowFourierNonSourceRemainder] using
    (card_mul_reconstructedCharacterTupleRowSumZeroCard_sub_validRowProduct_eq_sourceMode_add
      params candidate sourceError transformedError selected hunit characters)

/-- Pointwise phase-aware square bound.  It retains the structured factor
`1 + character(transformedError)` and charges the non-source second-dual remainder separately. -/
theorem reconstructedCharacterTupleRowSumZeroCard_sq_le_phaseAware
    [NeZero q] [Nontrivial (RLWE.Rq q (degree + 1))]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree 1 params.levels)
    (selected : DifferenceDigitColumn 1 params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (characters : NativeDiagonalRowCharacterTuple q degree 1 params.levels) :
    (reconstructedCharacterTupleRowSumZeroCard params candidate sourceError transformedError
        selected hunit characters : ℝ) ^ 2 ≤
      (2 *
            (reconstructedValidRowChoiceCardProduct params candidate sourceError transformedError
              selected hunit : ℝ) ^ 2 *
            ‖1 + characters 0 transformedError‖ ^ 2 +
          2 * ‖reconstructedCharacterTupleRowFourierNonSourceRemainder params candidate
            sourceError transformedError selected hunit characters‖ ^ 2) /
        (Fintype.card (NativeDiagonalRowCharacterTuple q degree 1 params.levels) : ℝ) ^ 2 := by
  let targetCard := Fintype.card
    (NativeDiagonalRowCharacterTuple q degree 1 params.levels)
  let fiberCard := reconstructedValidRowChoiceCardProduct params candidate sourceError
    transformedError selected hunit
  let acceptanceCard := reconstructedCharacterTupleRowSumZeroCard params candidate sourceError
    transformedError selected hunit characters
  let remainder := reconstructedCharacterTupleRowFourierNonSourceRemainder params candidate
    sourceError transformedError selected hunit characters
  have hcenter :=
    card_mul_reconstructedCharacterTupleRowSumZeroCard_sub_validRowProduct_eq_sourceMode_add_remainder
      params candidate sourceError transformedError selected hunit characters
  have hscaled :
      (targetCard : ℂ) * (acceptanceCard : ℂ) =
        (fiberCard : ℂ) * (1 + characters 0 transformedError) + remainder := by
    dsimp only [targetCard, fiberCard, acceptanceCard, remainder]
    linear_combination hcenter
  have hnorm := complex_norm_add_sq_le_two_mul
    ((fiberCard : ℂ) * (1 + characters 0 transformedError)) remainder
  rw [← hscaled] at hnorm
  simp only [norm_mul, Complex.norm_natCast] at hnorm
  have htargetPos : 0 < (targetCard : ℝ) := by positivity
  change (acceptanceCard : ℝ) ^ 2 ≤ _
  rw [le_div_iff₀ (sq_pos_of_pos htargetPos)]
  change
    (acceptanceCard : ℝ) ^ 2 * (targetCard : ℝ) ^ 2 ≤
      2 * (fiberCard : ℝ) ^ 2 * ‖1 + characters 0 transformedError‖ ^ 2 +
        2 * ‖remainder‖ ^ 2
  nlinarith

/-- Summed phase-aware square bound.  Exact outer-character orthogonality evaluates the complete
structured source mode; the only unevaluated term is the `L²` mass of the non-source remainder. -/
theorem sum_nontrivial_reconstructedCharacterTupleRowSumZeroCard_sq_le_phaseAware
    [NeZero q] [Nontrivial (RLWE.Rq q (degree + 1))]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree 1 params.levels)
    (selected : DifferenceDigitColumn 1 params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    (∑ characters ∈ (Finset.univ.erase
        (0 : NativeDiagonalRowCharacterTuple q degree 1 params.levels)),
      (reconstructedCharacterTupleRowSumZeroCard params candidate sourceError transformedError
        selected hunit characters : ℝ) ^ 2) ≤
      (2 *
            (reconstructedValidRowChoiceCardProduct params candidate sourceError transformedError
              selected hunit : ℝ) ^ 2 *
            rankOneSourceModeSquareFactor transformedError +
          2 * reconstructedCharacterTupleRowFourierNonSourceSquareMass params candidate
            sourceError transformedError selected hunit) /
        (Fintype.card (NativeDiagonalRowCharacterTuple q degree 1 params.levels) : ℝ) ^ 2 := by
  calc
    (∑ characters ∈ (Finset.univ.erase
        (0 : NativeDiagonalRowCharacterTuple q degree 1 params.levels)),
      (reconstructedCharacterTupleRowSumZeroCard params candidate sourceError transformedError
        selected hunit characters : ℝ) ^ 2) ≤
        ∑ characters ∈ (Finset.univ.erase
            (0 : NativeDiagonalRowCharacterTuple q degree 1 params.levels)),
          (2 *
                (reconstructedValidRowChoiceCardProduct params candidate sourceError
                  transformedError selected hunit : ℝ) ^ 2 *
                ‖1 + characters 0 transformedError‖ ^ 2 +
              2 * ‖reconstructedCharacterTupleRowFourierNonSourceRemainder params candidate
                sourceError transformedError selected hunit characters‖ ^ 2) /
            (Fintype.card
              (NativeDiagonalRowCharacterTuple q degree 1 params.levels) : ℝ) ^ 2 := by
      apply Finset.sum_le_sum
      intro characters _
      exact reconstructedCharacterTupleRowSumZeroCard_sq_le_phaseAware params candidate
        sourceError transformedError selected hunit characters
    _ = (2 *
              (reconstructedValidRowChoiceCardProduct params candidate sourceError
                transformedError selected hunit : ℝ) ^ 2 *
              (∑ characters ∈ (Finset.univ.erase
                  (0 : NativeDiagonalRowCharacterTuple q degree 1 params.levels)),
                ‖1 + characters 0 transformedError‖ ^ 2) +
            2 * reconstructedCharacterTupleRowFourierNonSourceSquareMass params candidate
              sourceError transformedError selected hunit) /
          (Fintype.card
            (NativeDiagonalRowCharacterTuple q degree 1 params.levels) : ℝ) ^ 2 := by
      rw [← Finset.sum_div, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      rfl
    _ = _ := by
      rw [sum_nontrivial_rankOneCharacterTuple_norm_one_add_apply_sq_eq_sourceFactor]

/-- Summing the structured source mode over every nontrivial outer character gives exact
orthogonality: a large zero-error term and the negative fiber cardinality otherwise. -/
theorem sum_nontrivial_rankOneSourceMode_eq_ite
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree 1 params.levels)
    (selected : DifferenceDigitColumn 1 params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    (∑ characters ∈ (Finset.univ.erase
        (0 : NativeDiagonalRowCharacterTuple q degree 1 params.levels)),
      (reconstructedValidRowChoiceCardProduct params candidate sourceError transformedError
          selected hunit : ℂ) * characters 0 transformedError) =
      if transformedError = 0 then
        (reconstructedValidRowChoiceCardProduct params candidate sourceError transformedError
            selected hunit : ℂ) *
          ((Fintype.card (NativeDiagonalRow q degree 1 params.levels) : ℂ) - 1)
      else
        -(reconstructedValidRowChoiceCardProduct params candidate sourceError transformedError
          selected hunit : ℂ) := by
  rw [← Finset.mul_sum, sum_nontrivial_rankOneCharacterTuple_apply_eq_ite]
  by_cases hzero : transformedError = 0 <;> simp [hzero]

/-- Exact outer-character aggregate of the phase-aware centered transform.  All source-mode
cancellation is evaluated; only the sum of non-source remainders remains. -/
theorem sum_nontrivial_centeredRowFourier_eq_sourceOrthogonality_add_remainder
    [NeZero q] [Nontrivial (RLWE.Rq q (degree + 1))]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree 1 params.levels)
    (selected : DifferenceDigitColumn 1 params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    (∑ characters ∈ (Finset.univ.erase
        (0 : NativeDiagonalRowCharacterTuple q degree 1 params.levels)),
      ((Fintype.card (NativeDiagonalRowCharacterTuple q degree 1 params.levels) : ℂ) *
          (reconstructedCharacterTupleRowSumZeroCard params candidate sourceError
            transformedError selected hunit characters : ℂ) -
        (reconstructedValidRowChoiceCardProduct params candidate sourceError transformedError
          selected hunit : ℂ))) =
      (if transformedError = 0 then
        (reconstructedValidRowChoiceCardProduct params candidate sourceError transformedError
            selected hunit : ℂ) *
          ((Fintype.card (NativeDiagonalRow q degree 1 params.levels) : ℂ) - 1)
      else
        -(reconstructedValidRowChoiceCardProduct params candidate sourceError transformedError
          selected hunit : ℂ)) +
        ∑ characters ∈ (Finset.univ.erase
            (0 : NativeDiagonalRowCharacterTuple q degree 1 params.levels)),
          reconstructedCharacterTupleRowFourierNonSourceRemainder params candidate sourceError
            transformedError selected hunit characters := by
  calc
    (∑ characters ∈ (Finset.univ.erase
        (0 : NativeDiagonalRowCharacterTuple q degree 1 params.levels)),
      ((Fintype.card (NativeDiagonalRowCharacterTuple q degree 1 params.levels) : ℂ) *
          (reconstructedCharacterTupleRowSumZeroCard params candidate sourceError
            transformedError selected hunit characters : ℂ) -
        (reconstructedValidRowChoiceCardProduct params candidate sourceError transformedError
          selected hunit : ℂ))) =
        ∑ characters ∈ (Finset.univ.erase
            (0 : NativeDiagonalRowCharacterTuple q degree 1 params.levels)),
          ((reconstructedValidRowChoiceCardProduct params candidate sourceError transformedError
              selected hunit : ℂ) * characters 0 transformedError +
            reconstructedCharacterTupleRowFourierNonSourceRemainder params candidate sourceError
              transformedError selected hunit characters) := by
      let characterSet : Finset
          (NativeDiagonalRowCharacterTuple q degree 1 params.levels) :=
        Finset.univ.erase 0
      change characterSet.sum (fun characters =>
          (Fintype.card (NativeDiagonalRowCharacterTuple q degree 1 params.levels) : ℂ) *
              (reconstructedCharacterTupleRowSumZeroCard params candidate sourceError
                transformedError selected hunit characters : ℂ) -
            (reconstructedValidRowChoiceCardProduct params candidate sourceError transformedError
              selected hunit : ℂ)) = characterSet.sum (fun characters =>
          ((reconstructedValidRowChoiceCardProduct params candidate sourceError transformedError
              selected hunit : ℂ) * characters 0 transformedError +
            reconstructedCharacterTupleRowFourierNonSourceRemainder params candidate sourceError
              transformedError selected hunit characters))
      apply congrArg (fun summand :
        NativeDiagonalRowCharacterTuple q degree 1 params.levels → ℂ =>
          characterSet.sum summand)
      funext characters
      exact
        card_mul_reconstructedCharacterTupleRowSumZeroCard_sub_validRowProduct_eq_sourceMode_add_remainder
          params candidate sourceError transformedError selected hunit characters
    _ = (∑ characters ∈ (Finset.univ.erase
          (0 : NativeDiagonalRowCharacterTuple q degree 1 params.levels)),
        (reconstructedValidRowChoiceCardProduct params candidate sourceError transformedError
            selected hunit : ℂ) * characters 0 transformedError) +
        ∑ characters ∈ (Finset.univ.erase
            (0 : NativeDiagonalRowCharacterTuple q degree 1 params.levels)),
          reconstructedCharacterTupleRowFourierNonSourceRemainder params candidate sourceError
            transformedError selected hunit characters := by
      rw [Finset.sum_add_distrib]
    _ = _ := by
      rw [sum_nontrivial_rankOneSourceMode_eq_ite]

/-- Native denominator-sensitive Fourier bound.  It preserves both the full dual target
cardinality and the actual valid-row product of the retained fiber. -/
theorem norm_card_mul_reconstructedCharacterTupleRowSumZeroCard_sub_validRowProduct_le
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (characters : NativeDiagonalRowCharacterTuple q degree ringRank params.levels) :
    ‖(Fintype.card
        (NativeDiagonalRowCharacterTuple q degree ringRank params.levels) : ℂ) *
        (reconstructedCharacterTupleRowSumZeroCard params candidate sourceError transformedError
          selected hunit characters : ℂ) -
        (reconstructedValidRowChoiceCardProduct params candidate sourceError transformedError
          selected hunit : ℂ)‖ ≤
      ∑ dualCharacter ∈ (Finset.univ.erase
          (0 : AddChar
            (NativeDiagonalRowCharacterTuple q degree ringRank params.levels) ℂ)),
        ∏ row : Fin (TGSW.rowCount ringRank params.levels),
          ‖reconstructedCharacterTupleRowFourierCoefficient params candidate sourceError
            transformedError selected hunit characters dualCharacter row‖ := by
  rw [reconstructedCharacterTupleRowSumZeroCard_eq_finiteRowConvolution]
  simpa only [reconstructedCharacterTupleRowFourierCoefficient,
    reconstructedValidRowChoiceCardProduct,
    FormalProof4FHE.FiniteRowConvolution.rowChoiceCardProduct] using
      (FormalProof4FHE.FiniteRowConvolution.norm_card_mul_rowSumZeroFiberCard_sub_rowChoiceCardProduct_le
          (Choice := fun row : Fin (TGSW.rowCount ringRank params.levels) ↦
            CompletableOmittedDigitRow (base := params.base)
              candidate sourceError transformedError selected hunit row)
          (contribution := fun row omitted ↦
            reconstructedRowPulledCharacterTuple params candidate sourceError transformedError
              selected hunit characters row omitted))

/-- Total nontrivial row-local Fourier mass for one accepting native character tuple. -/
noncomputable def reconstructedCharacterTupleRowFourierDeviation
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (characters : NativeDiagonalRowCharacterTuple q degree ringRank params.levels) : ℝ :=
  ∑ dualCharacter ∈ (Finset.univ.erase
      (0 : AddChar
        (NativeDiagonalRowCharacterTuple q degree ringRank params.levels) ℂ)),
    ∏ row : Fin (TGSW.rowCount ringRank params.levels),
      ‖reconstructedCharacterTupleRowFourierCoefficient params candidate sourceError
        transformedError selected hunit characters dualCharacter row‖

/-- The complete nontrivial second-dual mass can be reindexed exactly by nonzero tuples of
explicit native test rows. -/
theorem reconstructedCharacterTupleRowFourierDeviation_eq_testValues
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (characters : NativeDiagonalRowCharacterTuple q degree ringRank params.levels) :
    reconstructedCharacterTupleRowFourierDeviation params candidate sourceError transformedError
        selected hunit characters =
      ∑ testValues ∈ (Finset.univ.erase
          (0 : NativeDiagonalRowCharacterTupleTestValues
            q degree ringRank params.levels)),
        ∏ row : Fin (TGSW.rowCount ringRank params.levels),
          ‖reconstructedCharacterTupleRowTestFourierCoefficient params candidate sourceError
            transformedError selected hunit characters testValues row‖ := by
  unfold reconstructedCharacterTupleRowFourierDeviation
  simpa only [reconstructedCharacterTupleRowFourierCoefficient_evaluationEquiv] using
    (FormalProof4FHE.FinitePiAddCharDual.sum_ne_zero_evaluationEquiv
      (Index := Fin ringRank)
      (Value := NativeDiagonalRow q degree ringRank params.levels)
      (summand := fun dualCharacter ↦
        ∏ row : Fin (TGSW.rowCount ringRank params.levels),
          ‖reconstructedCharacterTupleRowFourierCoefficient params candidate sourceError
            transformedError selected hunit characters dualCharacter row‖))

/-- In rank one, the explicit nonzero source-error mode contributes the complete valid-row
product to the nontrivial Fourier mass.  Consequently a quantitative proof must separate this
proportional mode rather than postulating cancellation for every nonzero test tuple. -/
theorem reconstructedValidRowChoiceCardProduct_le_rowFourierDeviation_sourceErrorMode
    [NeZero q] [Nontrivial (RLWE.Rq q (degree + 1))]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree 1 params.levels)
    (selected : DifferenceDigitColumn 1 params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (characters : NativeDiagonalRowCharacterTuple q degree 1 params.levels) :
    (reconstructedValidRowChoiceCardProduct params candidate sourceError transformedError
        selected hunit : ℝ) ≤
      reconstructedCharacterTupleRowFourierDeviation params candidate sourceError
        transformedError selected hunit characters := by
  rw [reconstructedCharacterTupleRowFourierDeviation_eq_testValues]
  let sourceTest : NativeDiagonalRowCharacterTupleTestValues q degree 1 params.levels :=
    fun _ => sourceError
  have hsourceTest : sourceTest ≠ 0 := by
    exact rankOneSourceErrorTestValues_ne_zero params sourceError selected hunit
  have hmem : sourceTest ∈ (Finset.univ.erase
      (0 : NativeDiagonalRowCharacterTupleTestValues q degree 1 params.levels)) := by
    simp [hsourceTest]
  have hterm :
      (reconstructedValidRowChoiceCardProduct params candidate sourceError transformedError
          selected hunit : ℝ) =
        ∏ row : Fin (TGSW.rowCount 1 params.levels),
          ‖reconstructedCharacterTupleRowTestFourierCoefficient params candidate sourceError
            transformedError selected hunit characters sourceTest row‖ := by
    unfold reconstructedValidRowChoiceCardProduct
    push_cast
    apply Finset.prod_congr rfl
    intro row _
    exact
      (norm_reconstructedCharacterTupleRowTestFourierCoefficient_sourceError_eq_card
        params candidate sourceError transformedError selected hunit characters row).symm
  rw [hterm]
  exact Finset.single_le_sum
    (f := fun testValues :
        NativeDiagonalRowCharacterTupleTestValues q degree 1 params.levels =>
      ∏ row : Fin (TGSW.rowCount 1 params.levels),
        ‖reconstructedCharacterTupleRowTestFourierCoefficient params candidate sourceError
          transformedError selected hunit characters testValues row‖)
    (fun testValues _ => by positivity) hmem

/-- Fourier upper envelope for one retained-fiber acceptance cardinality. -/
noncomputable def reconstructedCharacterTupleRowFourierAcceptanceUpperBound
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (characters : NativeDiagonalRowCharacterTuple q degree ringRank params.levels) : ℝ :=
  ((reconstructedValidRowChoiceCardProduct params candidate sourceError transformedError
        selected hunit : ℝ) +
      reconstructedCharacterTupleRowFourierDeviation params candidate sourceError
        transformedError selected hunit characters) /
    Fintype.card (NativeDiagonalRowCharacterTuple q degree ringRank params.levels)

theorem reconstructedCharacterTupleRowFourierDeviation_nonneg
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (characters : NativeDiagonalRowCharacterTuple q degree ringRank params.levels) :
    0 ≤ reconstructedCharacterTupleRowFourierDeviation params candidate sourceError
      transformedError selected hunit characters := by
  unfold reconstructedCharacterTupleRowFourierDeviation
  positivity

theorem reconstructedCharacterTupleRowFourierAcceptanceUpperBound_nonneg
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (characters : NativeDiagonalRowCharacterTuple q degree ringRank params.levels) :
    0 ≤ reconstructedCharacterTupleRowFourierAcceptanceUpperBound params candidate sourceError
      transformedError selected hunit characters := by
  unfold reconstructedCharacterTupleRowFourierAcceptanceUpperBound
  apply div_nonneg
  · exact add_nonneg (by positivity)
      (reconstructedCharacterTupleRowFourierDeviation_nonneg params candidate sourceError
        transformedError selected hunit characters)
  · positivity

/-- The exact retained acceptance count is bounded by its denominator-preserving row-Fourier
envelope. -/
theorem reconstructedCharacterTupleRowSumZeroCard_le_rowFourierAcceptanceUpperBound
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (characters : NativeDiagonalRowCharacterTuple q degree ringRank params.levels) :
    (reconstructedCharacterTupleRowSumZeroCard params candidate sourceError transformedError
        selected hunit characters : ℝ) ≤
      reconstructedCharacterTupleRowFourierAcceptanceUpperBound params candidate sourceError
        transformedError selected hunit characters := by
  rw [reconstructedCharacterTupleRowSumZeroCard_eq_finiteRowConvolution]
  simpa only [reconstructedCharacterTupleRowFourierAcceptanceUpperBound,
    reconstructedCharacterTupleRowFourierDeviation,
    reconstructedCharacterTupleRowFourierCoefficient,
    reconstructedValidRowChoiceCardProduct,
    FormalProof4FHE.FiniteRowConvolution.nontrivialRowFourierNormSum,
    FormalProof4FHE.FiniteRowConvolution.rowChoiceCardProduct] using
      (FormalProof4FHE.FiniteRowConvolution.rowSumZeroFiberCard_le_add_nontrivialRowFourierNormSum_div_card
          (Choice := fun row : Fin (TGSW.rowCount ringRank params.levels) ↦
            CompletableOmittedDigitRow (base := params.base)
              candidate sourceError transformedError selected hunit row)
          (contribution := fun row omitted ↦
            reconstructedRowPulledCharacterTuple params candidate sourceError transformedError
              selected hunit characters row omitted))

/-- The native distinct-pair character factorial moment is exactly the factorial second moment
of the row-convolution zero-fiber cardinalities. -/
theorem fixedErrorDifferenceCharacterFactorialMoment_eq_rowSumZeroMoment
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    fixedErrorDifferenceCharacterFactorialMoment params candidate sourceError
        transformedError =
      ∑ characters : NativeDiagonalRowCharacterTuple q degree ringRank params.levels,
        if characters ≠ 0 then
          (reconstructedCharacterTupleRowSumZeroCard params candidate sourceError
              transformedError selected hunit characters : ℝ) *
            ((reconstructedCharacterTupleRowSumZeroCard params candidate sourceError
                transformedError selected hunit characters : ℝ) - 1)
        else 0 := by
  unfold fixedErrorDifferenceCharacterFactorialMoment
  apply Finset.sum_congr rfl
  intro characters _
  by_cases hcharacters : characters ≠ 0
  · rw [if_pos hcharacters, if_pos hcharacters]
    rw [fixedErrorDifferenceCharacterTupleAcceptanceCard_eq_rowSumZeroCard params hcapacity
      hbase candidate sourceError transformedError selected hunit characters]
  · simp [hcharacters]

/-- Reindex an indicator sum over nonzero finite elements as a sum over `univ.erase 0`. -/
private theorem sum_ite_ne_zero_eq_sum_erase
    {Index Value : Type*} [Fintype Index] [DecidableEq Index] [Zero Index]
    [AddCommMonoid Value]
    (weight : Index → Value) :
    (∑ index : Index, if index ≠ 0 then weight index else 0) =
      ∑ index ∈ (Finset.univ.erase (0 : Index)), weight index := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext index
    simp
  · intro index _
    rfl

/-- Explicit rank-one phase-aware square moment.  Exact outer-character orthogonality has
already evaluated the structured source-error mode; the only opaque quantity is the squared
mass of the non-source second-dual remainder. -/
noncomputable def fixedErrorDifferenceCharacterRankOnePhaseAwareSquareMoment
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree 1 params.levels)
    (selected : DifferenceDigitColumn 1 params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) : ℝ :=
  (2 *
          (reconstructedValidRowChoiceCardProduct params candidate sourceError transformedError
            selected hunit : ℝ) ^ 2 *
          rankOneSourceModeSquareFactor transformedError +
        2 * reconstructedCharacterTupleRowFourierNonSourceSquareMass params candidate
          sourceError transformedError selected hunit) /
      (Fintype.card (NativeDiagonalRowCharacterTuple q degree 1 params.levels) : ℝ) ^ 2

theorem fixedErrorDifferenceCharacterRankOnePhaseAwareSquareMoment_nonneg
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree 1 params.levels)
    (selected : DifferenceDigitColumn 1 params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    0 ≤ fixedErrorDifferenceCharacterRankOnePhaseAwareSquareMoment params candidate sourceError
      transformedError selected hunit := by
  unfold fixedErrorDifferenceCharacterRankOnePhaseAwareSquareMoment
  rw [← sum_nontrivial_rankOneCharacterTuple_norm_one_add_apply_sq_eq_sourceFactor]
  unfold reconstructedCharacterTupleRowFourierNonSourceSquareMass
  positivity

/-- The exact native rank-one character factorial moment is bounded by the phase-aware square
moment.  Unlike the norm-only Fourier envelope, this retains and then exactly averages the
structured circular source-error phase. -/
theorem fixedErrorDifferenceCharacterFactorialMoment_le_rankOnePhaseAwareSquareMoment
    [NeZero q] [Nontrivial (RLWE.Rq q (degree + 1))]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree 1 params.levels)
    (selected : DifferenceDigitColumn 1 params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    fixedErrorDifferenceCharacterFactorialMoment params candidate sourceError transformedError ≤
      fixedErrorDifferenceCharacterRankOnePhaseAwareSquareMoment params candidate sourceError
        transformedError selected hunit := by
  rw [fixedErrorDifferenceCharacterFactorialMoment_eq_rowSumZeroMoment params hcapacity hbase
    candidate sourceError transformedError selected hunit]
  calc
    (∑ characters : NativeDiagonalRowCharacterTuple q degree 1 params.levels,
      if characters ≠ 0 then
        (reconstructedCharacterTupleRowSumZeroCard params candidate sourceError transformedError
            selected hunit characters : ℝ) *
          ((reconstructedCharacterTupleRowSumZeroCard params candidate sourceError
              transformedError selected hunit characters : ℝ) - 1)
      else 0) ≤
        ∑ characters : NativeDiagonalRowCharacterTuple q degree 1 params.levels,
          if characters ≠ 0 then
            (reconstructedCharacterTupleRowSumZeroCard params candidate sourceError
              transformedError selected hunit characters : ℝ) ^ 2
          else 0 := by
      apply Finset.sum_le_sum
      intro characters _
      by_cases hcharacters : characters ≠ 0
      · rw [if_pos hcharacters, if_pos hcharacters]
        have hcardNonneg :
            0 ≤ (reconstructedCharacterTupleRowSumZeroCard params candidate sourceError
              transformedError selected hunit characters : ℝ) := by positivity
        nlinarith
      · simp [hcharacters]
    _ = ∑ characters ∈ (Finset.univ.erase
          (0 : NativeDiagonalRowCharacterTuple q degree 1 params.levels)),
        (reconstructedCharacterTupleRowSumZeroCard params candidate sourceError transformedError
          selected hunit characters : ℝ) ^ 2 := by
      exact sum_ite_ne_zero_eq_sum_erase _
    _ ≤ fixedErrorDifferenceCharacterRankOnePhaseAwareSquareMoment params candidate sourceError
        transformedError selected hunit := by
      exact sum_nontrivial_reconstructedCharacterTupleRowSumZeroCard_sq_le_phaseAware params
        candidate sourceError transformedError selected hunit

/-- Pointwise phase-aware rank-one square-moment certificate inside one selected unit
source-error slice. -/
def fixedErrorDifferenceFiberRankOnePhaseAwareSquareMomentAverageBoundAt
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree 1 params.levels)
    (selected : DifferenceDigitColumn 1 params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (collisionAverageBound : ℝ) : Prop :=
  ∀ transformedError : DiagonalErrorVector q degree 1 params.levels,
    fixedErrorDifferenceCharacterRankOnePhaseAwareSquareMoment params candidate sourceError
        transformedError selected hunit ≤
      (fixedErrorDifferenceFiberCard params candidate sourceError transformedError : ℝ) *
        collisionAverageBound

/-- A phase-aware rank-one square-moment estimate supplies the exact character factorial-moment
certificate consumed by the retained-cokernel security bridge. -/
theorem fixedErrorDifferenceFiberCharacterFactorialMomentAverageBound_of_rankOnePhaseAwareSquareMomentAt
    [NeZero q] [Nontrivial (RLWE.Rq q (degree + 1))]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree 1 params.levels)
    (selected : DifferenceDigitColumn 1 params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (collisionAverageBound : ℝ)
    (hPhaseAware : fixedErrorDifferenceFiberRankOnePhaseAwareSquareMomentAverageBoundAt params
      candidate sourceError selected hunit collisionAverageBound) :
    fixedErrorDifferenceFiberCharacterFactorialMomentAverageBound params candidate sourceError
      collisionAverageBound := by
  intro transformedError
  exact
    (fixedErrorDifferenceCharacterFactorialMoment_le_rankOnePhaseAwareSquareMoment params
      hcapacity hbase candidate sourceError transformedError selected hunit).trans
        (hPhaseAware transformedError)

/-- Direct phase-aware rank-one bridge to the denominator-preserving distinct-collision
certificate. -/
theorem fixedErrorDifferenceFiberDistinctCollisionAverageBound_of_rankOnePhaseAwareSquareMomentAt
    [NeZero q] [Nontrivial (RLWE.Rq q (degree + 1))]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree 1 params.levels)
    (selected : DifferenceDigitColumn 1 params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (collisionAverageBound : ℝ)
    (hPhaseAware : fixedErrorDifferenceFiberRankOnePhaseAwareSquareMomentAverageBoundAt params
      candidate sourceError selected hunit collisionAverageBound) :
    fixedErrorDifferenceFiberDistinctCollisionAverageBound params candidate sourceError
      collisionAverageBound :=
  fixedErrorDifferenceFiberDistinctCollisionAverageBound_of_characterFactorialMoment params
    candidate sourceError collisionAverageBound
      (fixedErrorDifferenceFiberCharacterFactorialMomentAverageBound_of_rankOnePhaseAwareSquareMomentAt
        params hcapacity hbase candidate sourceError selected hunit collisionAverageBound
          hPhaseAware)

/-- Sum of the squared row-Fourier acceptance envelopes over nontrivial native character tuples. -/
noncomputable def fixedErrorDifferenceCharacterRowFourierSquareMoment
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) : ℝ :=
  ∑ characters : NativeDiagonalRowCharacterTuple q degree ringRank params.levels,
    if characters ≠ 0 then
      (reconstructedCharacterTupleRowFourierAcceptanceUpperBound params candidate sourceError
        transformedError selected hunit characters) ^ 2
    else 0

theorem fixedErrorDifferenceCharacterRowFourierSquareMoment_nonneg
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    0 ≤ fixedErrorDifferenceCharacterRowFourierSquareMoment params candidate sourceError
      transformedError selected hunit := by
  unfold fixedErrorDifferenceCharacterRowFourierSquareMoment
  positivity

/-- The exact nontrivial character factorial moment is bounded by the explicit square moment of
the denominator-preserving row-Fourier envelopes. -/
theorem fixedErrorDifferenceCharacterFactorialMoment_le_rowFourierSquareMoment
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected))) :
    fixedErrorDifferenceCharacterFactorialMoment params candidate sourceError transformedError ≤
      fixedErrorDifferenceCharacterRowFourierSquareMoment params candidate sourceError
        transformedError selected hunit := by
  rw [fixedErrorDifferenceCharacterFactorialMoment_eq_rowSumZeroMoment params hcapacity hbase
    candidate sourceError transformedError selected hunit]
  unfold fixedErrorDifferenceCharacterRowFourierSquareMoment
  apply Finset.sum_le_sum
  intro characters _
  by_cases hcharacters : characters ≠ 0
  · rw [if_pos hcharacters, if_pos hcharacters]
    have hcardNonneg :
        0 ≤ (reconstructedCharacterTupleRowSumZeroCard params candidate sourceError
          transformedError selected hunit characters : ℝ) := by positivity
    have hcardLe :=
      reconstructedCharacterTupleRowSumZeroCard_le_rowFourierAcceptanceUpperBound
        params candidate sourceError transformedError selected hunit characters
    calc
      (reconstructedCharacterTupleRowSumZeroCard params candidate sourceError transformedError
          selected hunit characters : ℝ) *
          ((reconstructedCharacterTupleRowSumZeroCard params candidate sourceError
              transformedError selected hunit characters : ℝ) - 1) ≤
        (reconstructedCharacterTupleRowSumZeroCard params candidate sourceError transformedError
          selected hunit characters : ℝ) *
          (reconstructedCharacterTupleRowSumZeroCard params candidate sourceError
            transformedError selected hunit characters : ℝ) := by
              nlinarith
      _ ≤ reconstructedCharacterTupleRowFourierAcceptanceUpperBound params candidate sourceError
          transformedError selected hunit characters *
        reconstructedCharacterTupleRowFourierAcceptanceUpperBound params candidate sourceError
          transformedError selected hunit characters :=
            mul_self_le_mul_self hcardNonneg hcardLe
      _ = (reconstructedCharacterTupleRowFourierAcceptanceUpperBound params candidate sourceError
          transformedError selected hunit characters) ^ 2 := by ring
  · simp [hcharacters]

/-- Pointwise row-Fourier square-moment certificate inside one selected unit source-error slice. -/
def fixedErrorDifferenceFiberRowFourierSquareMomentAverageBoundAt
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (collisionAverageBound : ℝ) : Prop :=
  ∀ transformedError : DiagonalErrorVector q degree ringRank params.levels,
    fixedErrorDifferenceCharacterRowFourierSquareMoment params candidate sourceError
        transformedError selected hunit ≤
      (fixedErrorDifferenceFiberCard params candidate sourceError transformedError : ℝ) *
        collisionAverageBound

/-- A row-Fourier square-moment estimate supplies the exact character factorial-moment
certificate consumed by the retained-cokernel security bridge. -/
theorem fixedErrorDifferenceFiberCharacterFactorialMomentAverageBound_of_rowFourierSquareMomentAt
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (collisionAverageBound : ℝ)
    (hFourier : fixedErrorDifferenceFiberRowFourierSquareMomentAverageBoundAt params candidate
      sourceError selected hunit collisionAverageBound) :
    fixedErrorDifferenceFiberCharacterFactorialMomentAverageBound params candidate sourceError
      collisionAverageBound := by
  intro transformedError
  exact
    (fixedErrorDifferenceCharacterFactorialMoment_le_rowFourierSquareMoment params hcapacity
      hbase candidate sourceError transformedError selected hunit).trans
        (hFourier transformedError)

/-- Direct row-Fourier bridge to the denominator-preserving distinct-collision certificate. -/
theorem fixedErrorDifferenceFiberDistinctCollisionAverageBound_of_rowFourierSquareMomentAt
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hcapacity : q = params.base ^ params.levels)
    (hbase : params.base ≤ q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (selected : DifferenceDigitColumn ringRank params.levels)
    (hunit : IsUnit (sourceError (finProdFinEquiv selected)))
    (collisionAverageBound : ℝ)
    (hFourier : fixedErrorDifferenceFiberRowFourierSquareMomentAverageBoundAt params candidate
      sourceError selected hunit collisionAverageBound) :
    fixedErrorDifferenceFiberDistinctCollisionAverageBound params candidate sourceError
      collisionAverageBound :=
  fixedErrorDifferenceFiberDistinctCollisionAverageBound_of_characterFactorialMoment params
    candidate sourceError collisionAverageBound
      (fixedErrorDifferenceFiberCharacterFactorialMomentAverageBound_of_rowFourierSquareMomentAt
        params hcapacity hbase candidate sourceError selected hunit collisionAverageBound hFourier)

end

end FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm
