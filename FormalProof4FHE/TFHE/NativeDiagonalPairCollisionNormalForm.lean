/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeDiagonalJointCollision

/-!
# Paired-Collision Normal Form for the Native TFHE Diagonal

The retained-side collision theorem compares two independent copies of the complete hidden
difference/challenge randomness.  For a fixed pair of differences, equality of the two
transformed challenges is the zero fiber of one rectangular additive operator

`(leftChallenge, rightChallenge) ↦ A_left leftChallenge - A_right rightChallenge`.

This file exposes that operator.  Surjectivity of its row-level version lifts to the complete
challenge matrix and makes the challenge-pair collision count exactly uniform.  Unlike the
obstructed square determinant route, the row operator here has twice as many input columns as
output rows.  The exact conditional Pearson divergence is reduced to normalized paired excesses,
then bounded by one source-error-independent total over all difference pairs.  A future concrete
rank estimate can therefore exploit genuine entropy slack without a retained-fiber worst case.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm

noncomputable section

open FormalProof4FHE.TFHE

variable {q degree ringRank : ℕ}

/-- Difference of two fixed-digit row operators, viewed as one rectangular operator on a pair
of row vectors. -/
def pairedRowDifferenceOperator {R : Type} [CommRing R] {dimension levels : ℕ}
    (candidate : Bool)
    (leftDigits rightDigits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (values :
      (Fin (TGSW.rowCount dimension levels) → R) ×
        (Fin (TGSW.rowCount dimension levels) → R)) :
    Fin (TGSW.rowCount dimension levels) → R :=
  rowOperator candidate leftDigits values.1 -
    rowOperator candidate rightDigits values.2

theorem pairedRowDifferenceOperator_zero {R : Type} [CommRing R]
    {dimension levels : ℕ} (candidate : Bool)
    (leftDigits rightDigits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R) :
    pairedRowDifferenceOperator candidate leftDigits rightDigits 0 = 0 := by
  funext row
  cases candidate <;> simp [pairedRowDifferenceOperator, rowOperator]

theorem pairedRowDifferenceOperator_add {R : Type} [CommRing R]
    {dimension levels : ℕ} (candidate : Bool)
    (leftDigits rightDigits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (left right :
      (Fin (TGSW.rowCount dimension levels) → R) ×
        (Fin (TGSW.rowCount dimension levels) → R)) :
    pairedRowDifferenceOperator candidate leftDigits rightDigits (left + right) =
      pairedRowDifferenceOperator candidate leftDigits rightDigits left +
        pairedRowDifferenceOperator candidate leftDigits rightDigits right := by
  unfold pairedRowDifferenceOperator
  change
    rowOperator candidate leftDigits (left.1 + right.1) -
        rowOperator candidate rightDigits (left.2 + right.2) = _
  rw [rowOperator_add, rowOperator_add]
  abel

/-- Additive-homomorphism packaging of the paired rectangular row operator. -/
def pairedRowDifferenceAddHom {R : Type} [CommRing R] {dimension levels : ℕ}
    (candidate : Bool)
    (leftDigits rightDigits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R) :
    ((Fin (TGSW.rowCount dimension levels) → R) ×
      (Fin (TGSW.rowCount dimension levels) → R)) →+
        (Fin (TGSW.rowCount dimension levels) → R) where
  toFun := pairedRowDifferenceOperator candidate leftDigits rightDigits
  map_zero' := pairedRowDifferenceOperator_zero candidate leftDigits rightDigits
  map_add' := pairedRowDifferenceOperator_add candidate leftDigits rightDigits

/-- Complete paired operator on the two public challenge matrices. -/
def pairedChallengeDifferenceOperator {R : Type} [CommRing R]
    {dimension levels : ℕ} (candidate : Bool)
    (leftDigits rightDigits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (challenges :
      Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R ×
        Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R) :
    Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R :=
  challengeOperator candidate leftDigits challenges.1 -
    challengeOperator candidate rightDigits challenges.2

theorem pairedChallengeDifferenceOperator_zero {R : Type} [CommRing R]
    {dimension levels : ℕ} (candidate : Bool)
    (leftDigits rightDigits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R) :
    pairedChallengeDifferenceOperator candidate leftDigits rightDigits 0 = 0 := by
  funext coordinate
  exact pairedRowDifferenceOperator_zero candidate leftDigits rightDigits

theorem pairedChallengeDifferenceOperator_add {R : Type} [CommRing R]
    {dimension levels : ℕ} (candidate : Bool)
    (leftDigits rightDigits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (left right :
      Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R ×
        Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R) :
    pairedChallengeDifferenceOperator candidate leftDigits rightDigits (left + right) =
      pairedChallengeDifferenceOperator candidate leftDigits rightDigits left +
        pairedChallengeDifferenceOperator candidate leftDigits rightDigits right := by
  funext coordinate
  exact pairedRowDifferenceOperator_add candidate leftDigits rightDigits
    (left.1 coordinate, left.2 coordinate)
    (right.1 coordinate, right.2 coordinate)

/-- Additive-homomorphism packaging of the paired complete-challenge operator. -/
def pairedChallengeDifferenceAddHom {R : Type} [CommRing R]
    {dimension levels : ℕ} (candidate : Bool)
    (leftDigits rightDigits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R) :
    (Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R ×
      Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R) →+
        Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R where
  toFun := pairedChallengeDifferenceOperator candidate leftDigits rightDigits
  map_zero' := pairedChallengeDifferenceOperator_zero candidate leftDigits rightDigits
  map_add' := pairedChallengeDifferenceOperator_add candidate leftDigits rightDigits

/-- Row-level surjectivity lifts coordinatewise to the complete public challenge matrix. -/
theorem pairedChallengeDifferenceOperator_surjective_of_row
    {R : Type} [CommRing R] {dimension levels : ℕ} (candidate : Bool)
    (leftDigits rightDigits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (hrow : Function.Surjective
      (pairedRowDifferenceOperator candidate leftDigits rightDigits)) :
    Function.Surjective
      (pairedChallengeDifferenceOperator candidate leftDigits rightDigits) := by
  intro target
  choose preimage hpreimage using fun coordinate : Fin dimension => hrow (target coordinate)
  refine ⟨(fun coordinate => (preimage coordinate).1,
    fun coordinate => (preimage coordinate).2), ?_⟩
  funext coordinate
  exact hpreimage coordinate

/-- Equivalence between the zero fiber of the complete paired challenge operator and one
row-level zero-fiber witness for every public challenge coordinate. -/
def pairedChallengeZeroFiberEquiv
    {R : Type} [CommRing R] {dimension levels : ℕ} (candidate : Bool)
    (leftDigits rightDigits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R) :
    {challenges :
        Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R ×
          Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R //
      pairedChallengeDifferenceOperator candidate leftDigits rightDigits challenges = 0} ≃
      (Fin dimension →
        {values :
            (Fin (TGSW.rowCount dimension levels) → R) ×
              (Fin (TGSW.rowCount dimension levels) → R) //
          pairedRowDifferenceOperator candidate leftDigits rightDigits values = 0}) where
  toFun := fun challenges coordinate =>
    ⟨(challenges.1.1 coordinate, challenges.1.2 coordinate), by
      change rowOperator candidate leftDigits (challenges.1.1 coordinate) -
          rowOperator candidate rightDigits (challenges.1.2 coordinate) = 0
      have h := congrFun challenges.2 coordinate
      change rowOperator candidate leftDigits (challenges.1.1 coordinate) -
          rowOperator candidate rightDigits (challenges.1.2 coordinate) = 0 at h
      exact h⟩
  invFun := fun rows =>
    ⟨(fun coordinate => (rows coordinate).1.1,
      fun coordinate => (rows coordinate).1.2), by
        funext coordinate
        change rowOperator candidate leftDigits (rows coordinate).1.1 -
            rowOperator candidate rightDigits (rows coordinate).1.2 = 0
        exact (rows coordinate).2⟩
  left_inv := by
    intro challenges
    apply Subtype.ext
    apply Prod.ext <;> funext coordinate <;> rfl
  right_inv := by
    intro rows
    funext coordinate
    apply Subtype.ext
    rfl

/-- Cardinality of the zero fiber of the paired row operator. -/
def pairedRowZeroFiberCard
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    {dimension levels : ℕ} (candidate : Bool)
    (leftDigits rightDigits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R) : ℕ :=
  (Finset.univ.filter fun values :
      (Fin (TGSW.rowCount dimension levels) → R) ×
        (Fin (TGSW.rowCount dimension levels) → R) =>
    pairedRowDifferenceOperator candidate leftDigits rightDigits values = 0).card

/-- Ordered challenge-pair collision count for two fixed digit matrices. -/
noncomputable def pairedChallengeCollisionCount
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    {dimension levels : ℕ} (candidate : Bool)
    (leftDigits rightDigits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R) : ℝ :=
  ∑ leftChallenge : Matrix (Fin dimension)
      (Fin (TGSW.rowCount dimension levels)) R,
    ∑ rightChallenge : Matrix (Fin dimension)
        (Fin (TGSW.rowCount dimension levels)) R,
      if challengeOperator candidate leftDigits leftChallenge =
          challengeOperator candidate rightDigits rightChallenge then
        1
      else 0

theorem pairedChallengeCollisionCount_eq_zeroFiber
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    {dimension levels : ℕ} (candidate : Bool)
    (leftDigits rightDigits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R) :
    pairedChallengeCollisionCount candidate leftDigits rightDigits =
      ∑ challenges :
          Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R ×
            Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R,
        if pairedChallengeDifferenceOperator candidate leftDigits rightDigits challenges = 0
        then 1 else 0 := by
  rw [Fintype.sum_prod_type]
  unfold pairedChallengeCollisionCount pairedChallengeDifferenceOperator
  apply Finset.sum_congr rfl
  intro leftChallenge _
  apply Finset.sum_congr rfl
  intro rightChallenge _
  simp only [sub_eq_zero]

/-- The complete challenge-pair collision count is the row-level zero-fiber cardinality raised
to the number of independent public challenge coordinates. -/
theorem pairedChallengeCollisionCount_eq_rowZeroFiberCard_pow
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    {dimension levels : ℕ} (candidate : Bool)
    (leftDigits rightDigits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R) :
    pairedChallengeCollisionCount candidate leftDigits rightDigits =
      (pairedRowZeroFiberCard candidate leftDigits rightDigits : ℝ) ^ dimension := by
  rw [pairedChallengeCollisionCount_eq_zeroFiber]
  rw [FormalProof4FHE.ConditionalCollision.indicatorSum_eq_card_subtype]
  have hchallengeCard := Fintype.card_congr
    (pairedChallengeZeroFiberEquiv candidate leftDigits rightDigits)
  rw [hchallengeCard, Fintype.card_pi]
  have hrowCard :
      Fintype.card
          {values :
              (Fin (TGSW.rowCount dimension levels) → R) ×
                (Fin (TGSW.rowCount dimension levels) → R) //
            pairedRowDifferenceOperator candidate leftDigits rightDigits values = 0} =
        pairedRowZeroFiberCard candidate leftDigits rightDigits := by
    unfold pairedRowZeroFiberCard
    apply Fintype.card_of_subtype
    intro values
    simp
  simp only [hrowCard, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Nat.cast_pow]

/-- A surjective paired row operator gives exactly the uniform challenge-pair collision
baseline. -/
theorem pairedChallengeCollisionCount_eq_card_of_surjective
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    {dimension levels : ℕ} (candidate : Bool)
    (leftDigits rightDigits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R)
    (hrow : Function.Surjective
      (pairedRowDifferenceOperator candidate leftDigits rightDigits)) :
    pairedChallengeCollisionCount candidate leftDigits rightDigits =
      Fintype.card
        (Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R) := by
  rw [pairedChallengeCollisionCount_eq_zeroFiber]
  have hzero :=
    FormalProof4FHE.ConditionalCollision.zeroFiberCount_addHom_eq_card_div
      (pairedChallengeDifferenceAddHom candidate leftDigits rightDigits)
      (pairedChallengeDifferenceOperator_surjective_of_row
        candidate leftDigits rightDigits hrow)
  change
    (∑ challenges,
      if pairedChallengeDifferenceOperator candidate leftDigits rightDigits challenges = 0
      then (1 : ℝ) else 0) = _ at hzero
  rw [show
    (∑ challenges,
      if pairedChallengeDifferenceOperator candidate leftDigits rightDigits challenges = 0
      then (1 : ℝ) else 0) =
        (Fintype.card
            (Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R ×
              Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R) : ℝ) /
          (Fintype.card
            (Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R) : ℝ) by
      exact hzero]
  rw [Fintype.card_prod]
  have hcard :
      (Fintype.card
        (Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R) : ℝ) ≠ 0 := by
    exact_mod_cast
      (Fintype.card_ne_zero :
        Fintype.card
          (Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R) ≠ 0)
  field_simp [hcard]
  norm_num [Nat.cast_mul, pow_two]

/-- Every paired additive challenge operator has at least the uniform collision baseline; rank
deficiency can only increase its zero fiber. -/
theorem card_le_pairedChallengeCollisionCount
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R]
    {dimension levels : ℕ} (candidate : Bool)
    (leftDigits rightDigits : Fin (TGSW.rowCount dimension levels) →
      Fin (dimension + 1) → Fin levels → R) :
    (Fintype.card
        (Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R) : ℝ) ≤
      pairedChallengeCollisionCount candidate leftDigits rightDigits := by
  rw [pairedChallengeCollisionCount_eq_zeroFiber]
  have hzero := FormalProof4FHE.ConditionalCollision.card_div_le_zeroFiberCount_addHom
    (pairedChallengeDifferenceAddHom candidate leftDigits rightDigits)
  change
    (Fintype.card
        (Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R ×
          Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R) : ℝ) /
      (Fintype.card
        (Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R) : ℝ) ≤
    (∑ challenges,
      if pairedChallengeDifferenceOperator candidate leftDigits rightDigits challenges = 0
      then (1 : ℝ) else 0) at hzero
  rw [Fintype.card_prod] at hzero
  have hcard :
      (Fintype.card
        (Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R) : ℝ) ≠ 0 := by
    exact_mod_cast
      (Fintype.card_ne_zero :
        Fintype.card
          (Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R) ≠ 0)
  convert hzero using 1
  field_simp [hcard]
  norm_num [Nat.cast_mul, pow_two]

/-- Challenge-pair collision count for two concrete native difference ciphertexts. -/
noncomputable def differencePairChallengeCollisionCount [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ :=
  pairedChallengeCollisionCount candidate
    (differenceEntryDigits params leftDifference)
    (differenceEntryDigits params rightDifference)

/-- Retained transformed error as a function of the difference ciphertext alone. -/
def fixedErrorDifferenceSide [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    DiagonalErrorVector q degree ringRank params.levels :=
  rowOperator candidate (differenceEntryDigits params difference) sourceError

/-- Number of difference ciphertexts producing one retained transformed-error value. -/
def fixedErrorDifferenceFiberCard [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels) : ℕ :=
  FormalProof4FHE.ConditionalCollision.sideFiberCard
    (fixedErrorDifferenceSide params candidate sourceError) transformedError

/-- Excess of one fixed difference pair's challenge-collision count above the uniform
challenge baseline. -/
noncomputable def differencePairChallengeCollisionExcess [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ :=
  differencePairChallengeCollisionCount params candidate
      leftDifference rightDifference -
    Fintype.card (DiagonalChallenge q degree ringRank params.levels)

theorem differencePairChallengeCollisionExcess_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    0 ≤ differencePairChallengeCollisionExcess params candidate
      leftDifference rightDifference := by
  unfold differencePairChallengeCollisionExcess differencePairChallengeCollisionCount
  linarith [card_le_pairedChallengeCollisionCount candidate
    (differenceEntryDigits params leftDifference)
    (differenceEntryDigits params rightDifference)]

/-- Total rectangular challenge-collision excess over every ordered pair of native difference
ciphertexts.  This quantity no longer depends on a retained error fiber. -/
noncomputable def totalDifferencePairChallengeCollisionExcess [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool) : ℝ :=
  ∑ leftDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels,
    ∑ rightDifference :
        RingGSWCiphertext q (degree + 1) ringRank params.levels,
      differencePairChallengeCollisionExcess params candidate
        leftDifference rightDifference

theorem totalDifferencePairChallengeCollisionExcess_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool) :
    0 ≤ totalDifferencePairChallengeCollisionExcess
      (degree := degree) (ringRank := ringRank) params candidate := by
  unfold totalDifferencePairChallengeCollisionExcess
  apply Finset.sum_nonneg
  intro leftDifference _
  apply Finset.sum_nonneg
  intro rightDifference _
  exact differencePairChallengeCollisionExcess_nonneg
    params candidate leftDifference rightDifference

/-- Total paired-challenge collision excess among difference pairs in one retained side fiber. -/
noncomputable def fixedErrorDiagonalPairCollisionExcess [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels) : ℝ :=
  ∑ leftDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels,
    ∑ rightDifference :
        RingGSWCiphertext q (degree + 1) ringRank params.levels,
      if fixedErrorDifferenceSide params candidate sourceError leftDifference =
            transformedError ∧
          fixedErrorDifferenceSide params candidate sourceError rightDifference =
            transformedError then
        differencePairChallengeCollisionExcess params candidate
          leftDifference rightDifference
      else 0

theorem fixedErrorDiagonalPairCollisionExcess_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels) :
    0 ≤ fixedErrorDiagonalPairCollisionExcess params candidate
      sourceError transformedError := by
  unfold fixedErrorDiagonalPairCollisionExcess
  apply Finset.sum_nonneg
  intro leftDifference _
  apply Finset.sum_nonneg
  intro rightDifference _
  split_ifs
  · exact differencePairChallengeCollisionExcess_nonneg
      params candidate leftDifference rightDifference
  · exact le_rfl

/-- Summing the retained-side excesses is bounded by the total excess over all difference pairs.
Pairs from different retained fibers are simply dropped from the left-hand side. -/
theorem sum_fixedErrorDiagonalPairCollisionExcess_le_total [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) :
    (∑ transformedError : DiagonalErrorVector q degree ringRank params.levels,
      fixedErrorDiagonalPairCollisionExcess params candidate
        sourceError transformedError) ≤
      totalDifferencePairChallengeCollisionExcess
        (degree := degree) (ringRank := ringRank) params candidate := by
  unfold fixedErrorDiagonalPairCollisionExcess
  unfold totalDifferencePairChallengeCollisionExcess
  exact FormalProof4FHE.ConditionalCollision.sum_sameSidePairWeight_le_total
    (fixedErrorDifferenceSide params candidate sourceError)
    (differencePairChallengeCollisionExcess params candidate)
    (differencePairChallengeCollisionExcess_nonneg params candidate)

/-- Global normalized paired-collision excess for one fixed source-error vector.  Unlike the
pointwise fiber certificate, this retains the exact probability weight of each side fiber. -/
noncomputable def fixedErrorDiagonalNormalizedPairCollisionExcess [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) : ℝ :=
  ∑ transformedError : DiagonalErrorVector q degree ringRank params.levels,
    if fixedErrorDifferenceFiberCard params candidate sourceError transformedError = 0 then
      0
    else
      fixedErrorDiagonalPairCollisionExcess params candidate
          sourceError transformedError /
        ((Fintype.card
              (RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ) *
          (Fintype.card
              (DiagonalChallenge q degree ringRank params.levels) : ℝ) *
          (fixedErrorDifferenceFiberCard params candidate sourceError
            transformedError : ℝ))

theorem fixedErrorDiagonalNormalizedPairCollisionExcess_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) :
    0 ≤ fixedErrorDiagonalNormalizedPairCollisionExcess
      params candidate sourceError := by
  unfold fixedErrorDiagonalNormalizedPairCollisionExcess
  apply Finset.sum_nonneg
  intro transformedError _
  split_ifs
  · exact le_rfl
  · exact div_nonneg
      (fixedErrorDiagonalPairCollisionExcess_nonneg
        params candidate sourceError transformedError) (by positivity)

/-- A source-error-independent budget obtained by discarding the retained-side restriction and
using only that every nonempty difference fiber has cardinality at least one. -/
noncomputable def globalDifferencePairCollisionBudget [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool) : ℝ :=
  totalDifferencePairChallengeCollisionExcess
      (degree := degree) (ringRank := ringRank) params candidate /
    ((Fintype.card
        (RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ) *
      (Fintype.card
        (DiagonalChallenge q degree ringRank params.levels) : ℝ))

theorem globalDifferencePairCollisionBudget_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool) :
    0 ≤ globalDifferencePairCollisionBudget
      (degree := degree) (ringRank := ringRank) params candidate := by
  unfold globalDifferencePairCollisionBudget
  exact div_nonneg
    (totalDifferencePairChallengeCollisionExcess_nonneg
      (degree := degree) (ringRank := ringRank) params candidate) (by positivity)

/-- The exact fixed-error normalized excess is bounded by a single unconditional sum over
rectangular difference pairs.  In particular, the right-hand side is independent of the source
error distribution. -/
theorem fixedErrorDiagonalNormalizedPairCollisionExcess_le_globalBudget [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) :
    fixedErrorDiagonalNormalizedPairCollisionExcess
        params candidate sourceError ≤
      globalDifferencePairCollisionBudget
        (degree := degree) (ringRank := ringRank) params candidate := by
  unfold fixedErrorDiagonalNormalizedPairCollisionExcess
  unfold fixedErrorDiagonalPairCollisionExcess fixedErrorDifferenceFiberCard
  unfold globalDifferencePairCollisionBudget
  unfold totalDifferencePairChallengeCollisionExcess
  have hdifferenceCard :
      (0 : ℝ) < Fintype.card
        (RingGSWCiphertext q (degree + 1) ringRank params.levels) := by
    exact_mod_cast Fintype.card_pos
  have hchallengeCard :
      (0 : ℝ) < Fintype.card
        (DiagonalChallenge q degree ringRank params.levels) := by
    exact_mod_cast Fintype.card_pos
  exact
    FormalProof4FHE.ConditionalCollision.sum_sameSidePairWeight_div_scaledFiberCard_le_total_div
        (fixedErrorDifferenceSide params candidate sourceError)
        (differencePairChallengeCollisionExcess params candidate)
        (differencePairChallengeCollisionExcess_nonneg params candidate)
        ((Fintype.card
            (RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ) *
          (Fintype.card
            (DiagonalChallenge q degree ringRank params.levels) : ℝ))
        (mul_pos hdifferenceCard hchallengeCard)

/-- Surjectivity of the concrete paired row operator makes a difference pair contribute exactly
one uniform challenge-space unit to the conditional collision count. -/
theorem differencePairChallengeCollisionCount_eq_card_of_surjective [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels)
    (hrow : Function.Surjective
      (pairedRowDifferenceOperator candidate
        (differenceEntryDigits params leftDifference)
        (differenceEntryDigits params rightDifference))) :
    differencePairChallengeCollisionCount params candidate
        leftDifference rightDifference =
      Fintype.card (DiagonalChallenge q degree ringRank params.levels) := by
  exact pairedChallengeCollisionCount_eq_card_of_surjective candidate
    (differenceEntryDigits params leftDifference)
    (differenceEntryDigits params rightDifference) hrow

theorem differencePairChallengeCollisionExcess_eq_zero_of_surjective [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels)
    (hrow : Function.Surjective
      (pairedRowDifferenceOperator candidate
        (differenceEntryDigits params leftDifference)
        (differenceEntryDigits params rightDifference))) :
    differencePairChallengeCollisionExcess params candidate
      leftDifference rightDifference = 0 := by
  unfold differencePairChallengeCollisionExcess
  rw [differencePairChallengeCollisionCount_eq_card_of_surjective
    params candidate leftDifference rightDifference hrow]
  ring

/-- The complete joint-input side fiber is the difference-only side fiber times the entire
independent challenge space. -/
theorem fixedErrorDiagonalSideFiberCard_eq_challenge_mul_differenceFiber [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels) :
    FormalProof4FHE.ConditionalCollision.sideFiberCard
        (fixedErrorDiagonalSide params candidate sourceError) transformedError =
      Fintype.card (DiagonalChallenge q degree ringRank params.levels) *
        fixedErrorDifferenceFiberCard params candidate sourceError transformedError := by
  unfold fixedErrorDiagonalSide fixedErrorDifferenceFiberCard fixedErrorDifferenceSide
  exact FormalProof4FHE.ConditionalCollision.sideFiberCard_prod_fst
    (Coin := DiagonalChallenge q degree ringRank params.levels)
    (side := fun difference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels =>
        rowOperator candidate (differenceEntryDigits params difference) sourceError)
    transformedError

/-- The native conditional pair count is exactly a sum over two difference ciphertexts.  A
difference pair is retained only when both row operators produce the requested side value; its
weight is the collision count of the corresponding rectangular paired challenge operator. -/
theorem fixedErrorDiagonalCollisionPairCount_eq_differencePairs [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (transformedError : DiagonalErrorVector q degree ringRank params.levels) :
    FormalProof4FHE.ConditionalCollision.conditionalFiberCollisionPairCount
        (fixedErrorDiagonalSide params candidate sourceError)
        (fixedErrorDiagonalOutput params candidate) transformedError =
      ∑ leftDifference :
          RingGSWCiphertext q (degree + 1) ringRank params.levels,
        ∑ rightDifference :
            RingGSWCiphertext q (degree + 1) ringRank params.levels,
          if rowOperator candidate (differenceEntryDigits params leftDifference)
                sourceError = transformedError ∧
              rowOperator candidate (differenceEntryDigits params rightDifference)
                sourceError = transformedError then
            differencePairChallengeCollisionCount params candidate
              leftDifference rightDifference
          else 0 := by
  unfold fixedErrorDiagonalSide fixedErrorDiagonalOutput
  simpa only [differencePairChallengeCollisionCount, pairedChallengeCollisionCount] using
    (FormalProof4FHE.ConditionalCollision.conditionalFiberCollisionPairCount_prod
      (Seed := RingGSWCiphertext q (degree + 1) ringRank params.levels)
      (Coin := DiagonalChallenge q degree ringRank params.levels)
      (side := fun difference =>
        rowOperator candidate (differenceEntryDigits params difference) sourceError)
      (output := fun difference challenge =>
        challengeOperator candidate (differenceEntryDigits params difference) challenge)
      transformedError)

/-- Exact baseline-plus-excess form of the native conditional collision-pair count.  The
baseline is what a uniform challenge would contribute for every ordered pair of differences;
all remaining work is isolated in `fixedErrorDiagonalPairCollisionExcess`. -/
theorem fixedErrorDiagonalCollisionPairCount_eq_baseline_add_excess [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels) :
    FormalProof4FHE.ConditionalCollision.conditionalFiberCollisionPairCount
        (fixedErrorDiagonalSide params candidate sourceError)
        (fixedErrorDiagonalOutput params candidate) transformedError =
      (Fintype.card (DiagonalChallenge q degree ringRank params.levels) : ℝ) *
          (fixedErrorDifferenceFiberCard params candidate sourceError
            transformedError : ℝ) ^ 2 +
        fixedErrorDiagonalPairCollisionExcess params candidate
          sourceError transformedError := by
  rw [fixedErrorDiagonalCollisionPairCount_eq_differencePairs]
  let side := fixedErrorDifferenceSide params candidate sourceError
  let C : ℝ := Fintype.card (DiagonalChallenge q degree ringRank params.levels)
  have hdecompose (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) :
      (if side leftDifference = transformedError ∧
          side rightDifference = transformedError then
        differencePairChallengeCollisionCount params candidate
          leftDifference rightDifference
      else 0) =
        (if side leftDifference = transformedError ∧
            side rightDifference = transformedError then C else 0) +
          (if side leftDifference = transformedError ∧
              side rightDifference = transformedError then
            differencePairChallengeCollisionExcess params candidate
              leftDifference rightDifference
          else 0) := by
    by_cases hside : side leftDifference = transformedError ∧
      side rightDifference = transformedError
    · simp only [hside]
      unfold differencePairChallengeCollisionExcess
      dsimp [C]
      ring
    · simp [hside]
  change
    (∑ leftDifference,
      ∑ rightDifference,
        if side leftDifference = transformedError ∧
            side rightDifference = transformedError then
          differencePairChallengeCollisionCount params candidate
            leftDifference rightDifference
        else 0) = _
  simp_rw [hdecompose, Finset.sum_add_distrib]
  rw [FormalProof4FHE.ConditionalCollision.sideFiberPairWeightedCount_eq]
  unfold fixedErrorDiagonalPairCollisionExcess fixedErrorDifferenceFiberCard
  change
    C *
          (FormalProof4FHE.ConditionalCollision.sideFiberCard side transformedError : ℝ) ^ 2 +
        (∑ leftDifference,
          ∑ rightDifference,
            if side leftDifference = transformedError ∧
                side rightDifference = transformedError then
              differencePairChallengeCollisionExcess params candidate
                leftDifference rightDifference
            else 0) = _
  rfl

/-- Exact global normal form: the fixed-error conditional Pearson divergence is precisely the
normalized sum of paired rectangular collision excesses.  No worst-case side-fiber bound is
introduced. -/
theorem fixedErrorDiagonalChiSquare_eq_normalizedPairCollisionExcess [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) :
    fixedErrorDiagonalChiSquare params candidate sourceError =
      fixedErrorDiagonalNormalizedPairCollisionExcess
        params candidate sourceError := by
  unfold fixedErrorDiagonalChiSquare
  rw [FormalProof4FHE.ConditionalCollision.conditionalFiberChiSquare_eq_secondMoment,
    FormalProof4FHE.ConditionalCollision.conditionalFiberSecondMoment_eq_collisionPairCount]
  rw [Fintype.card_prod]
  simp only [Nat.cast_mul]
  simp_rw [fixedErrorDiagonalCollisionPairCount_eq_baseline_add_excess,
    fixedErrorDiagonalSideFiberCard_eq_challenge_mul_differenceFiber]
  let D : ℝ := Fintype.card
    (RingGSWCiphertext q (degree + 1) ringRank params.levels)
  let C : ℝ := Fintype.card (DiagonalChallenge q degree ringRank params.levels)
  let K := fun transformedError :
      DiagonalErrorVector q degree ringRank params.levels =>
    fixedErrorDifferenceFiberCard params candidate sourceError transformedError
  let E := fun transformedError :
      DiagonalErrorVector q degree ringRank params.levels =>
    fixedErrorDiagonalPairCollisionExcess params candidate sourceError transformedError
  have hD : D ≠ 0 := by
    dsimp [D]
    exact_mod_cast
      (Fintype.card_ne_zero :
        Fintype.card
          (RingGSWCiphertext q (degree + 1) ringRank params.levels) ≠ 0)
  have hC : C ≠ 0 := by
    dsimp [C]
    exact_mod_cast
      (Fintype.card_ne_zero :
        Fintype.card (DiagonalChallenge q degree ringRank params.levels) ≠ 0)
  have hsummand (transformedError :
      DiagonalErrorVector q degree ringRank params.levels) :
      (if Fintype.card (DiagonalChallenge q degree ringRank params.levels) *
            K transformedError = 0 then
        0
      else
        (C * (K transformedError : ℝ) ^ 2 + E transformedError) /
          (C * (K transformedError : ℝ))) =
        (K transformedError : ℝ) +
          (if K transformedError = 0 then 0
          else E transformedError / (C * (K transformedError : ℝ))) := by
    by_cases hK : K transformedError = 0
    · simp [hK]
    · have hKReal : (K transformedError : ℝ) ≠ 0 := by exact_mod_cast hK
      have hcardChallenge :
          Fintype.card (DiagonalChallenge q degree ringRank params.levels) ≠ 0 :=
        Fintype.card_ne_zero
      simp only [hK, hcardChallenge, Nat.mul_eq_zero, false_or, if_false]
      field_simp [hC, hKReal]
  simp only [Nat.cast_mul]
  change
    C / (D * C) *
          (∑ transformedError,
            if Fintype.card (DiagonalChallenge q degree ringRank params.levels) *
                  K transformedError = 0 then
              0
            else
              (C * (K transformedError : ℝ) ^ 2 + E transformedError) /
                (C * (K transformedError : ℝ))) - 1 = _
  simp_rw [hsummand]
  have hfiberSum :
      (∑ transformedError : DiagonalErrorVector q degree ringRank params.levels,
          (K transformedError : ℝ)) = D := by
    dsimp [K, D, fixedErrorDifferenceFiberCard]
    exact_mod_cast FormalProof4FHE.ConditionalCollision.sum_sideFiberCard
      (fixedErrorDifferenceSide params candidate sourceError)
  rw [Finset.sum_add_distrib, hfiberSum]
  unfold fixedErrorDiagonalNormalizedPairCollisionExcess
  change
    C / (D * C) *
          (D + ∑ transformedError,
            if K transformedError = 0 then 0
            else E transformedError / (C * (K transformedError : ℝ))) - 1 =
      ∑ transformedError,
        if K transformedError = 0 then 0
        else E transformedError /
          (D * C * (K transformedError : ℝ))
  have hterm (transformedError :
      DiagonalErrorVector q degree ringRank params.levels) :
      (if K transformedError = 0 then 0
      else E transformedError / (D * C * (K transformedError : ℝ))) =
        (1 / D) *
          (if K transformedError = 0 then 0
          else E transformedError / (C * (K transformedError : ℝ))) := by
    by_cases hK : K transformedError = 0
    · simp [hK]
    · have hKReal : (K transformedError : ℝ) ≠ 0 := by exact_mod_cast hK
      simp only [hK, if_false]
      field_simp [hD, hC, hKReal]
  simp_rw [hterm]
  rw [← Finset.mul_sum]
  field_simp [hD, hC]
  ring

/-- A bound on the exact global normalized pair excess controls the fixed-error chi-square
statistical loss without a pointwise side-fiber hypothesis. -/
theorem fixedErrorDiagonalChiSquareLoss_le_of_normalizedPairCollisionExcess [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (ε : ℝ)
    (hexcess : fixedErrorDiagonalNormalizedPairCollisionExcess
      params candidate sourceError ≤ ε) :
    fixedErrorDiagonalChiSquareLoss params candidate sourceError ≤
      Real.sqrt ε / 2 := by
  unfold fixedErrorDiagonalChiSquareLoss
  rw [fixedErrorDiagonalChiSquare_eq_normalizedPairCollisionExcess]
  gcongr

/-- The fixed-source-error Pearson divergence is controlled by the source-independent global
difference-pair budget. -/
theorem fixedErrorDiagonalChiSquare_le_globalDifferencePairCollisionBudget [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) :
    fixedErrorDiagonalChiSquare params candidate sourceError ≤
      globalDifferencePairCollisionBudget
        (degree := degree) (ringRank := ringRank) params candidate := by
  rw [fixedErrorDiagonalChiSquare_eq_normalizedPairCollisionExcess]
  exact fixedErrorDiagonalNormalizedPairCollisionExcess_le_globalBudget
    params candidate sourceError

/-- Source-independent statistical loss obtained from the global rectangular-pair budget. -/
theorem fixedErrorDiagonalChiSquareLoss_le_globalDifferencePairCollisionBudget [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) :
    fixedErrorDiagonalChiSquareLoss params candidate sourceError ≤
      Real.sqrt
          (globalDifferencePairCollisionBudget
            (degree := degree) (ringRank := ringRank) params candidate) /
        2 := by
  apply fixedErrorDiagonalChiSquareLoss_le_of_normalizedPairCollisionExcess
  exact fixedErrorDiagonalNormalizedPairCollisionExcess_le_globalBudget
    params candidate sourceError

/-- A support-wise estimate of the global normalized pair excess bounds the complete source-error
average used by the native diagonal hybrid. -/
theorem averagedSourceErrorDiagonalChiSquareLoss_le_of_normalizedPairCollisionExcess [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) (ε : ℝ)
    (hexcess : ∀ sourceError ∈ support
      (ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
        sourceErrorSampler),
      fixedErrorDiagonalNormalizedPairCollisionExcess
        params candidate sourceError ≤ ε) :
    averagedSourceErrorDiagonalChiSquareLoss (ringRank := ringRank)
        params sourceErrorSampler candidate ≤
      Real.sqrt ε / 2 := by
  let ErrorVector := DiagonalErrorVector q degree ringRank params.levels
  let Errors : ProbComp ErrorVector :=
    ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) sourceErrorSampler
  letI : Fintype ErrorVector := Fintype.ofFinite ErrorVector
  have hmass : (∑ sourceError : ErrorVector,
      Pr[= sourceError | Errors].toReal) = 1 := by
    rw [← ENNReal.toReal_sum (fun _ _ => probOutput_ne_top),
      sum_probOutput_eq_one (by simp), ENNReal.toReal_one]
  unfold averagedSourceErrorDiagonalChiSquareLoss
  rw [tsum_fintype]
  calc
    ∑ sourceError : ErrorVector,
        Pr[= sourceError | Errors].toReal *
          fixedErrorDiagonalChiSquareLoss params candidate sourceError ≤
      ∑ sourceError : ErrorVector,
        Pr[= sourceError | Errors].toReal * (Real.sqrt ε / 2) := by
          apply Finset.sum_le_sum
          intro sourceError _
          by_cases hsource : sourceError ∈ support Errors
          · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
            apply fixedErrorDiagonalChiSquareLoss_le_of_normalizedPairCollisionExcess
            exact hexcess sourceError (by simpa [Errors, ErrorVector] using hsource)
          · have hzero : Pr[= sourceError | Errors] = 0 :=
              probOutput_eq_zero_of_not_mem_support hsource
            simp [hzero]
    _ = (∑ sourceError : ErrorVector,
        Pr[= sourceError | Errors].toReal) * (Real.sqrt ε / 2) := by
          rw [Finset.sum_mul]
    _ = Real.sqrt ε / 2 := by rw [hmass, one_mul]

/-- The complete source-error average obeys the same global pair-collision budget, with no
support-wise premise on the source-error sampler. -/
theorem averagedSourceErrorDiagonalChiSquareLoss_le_globalDifferencePairCollisionBudget
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) :
    averagedSourceErrorDiagonalChiSquareLoss (ringRank := ringRank)
        params sourceErrorSampler candidate ≤
      Real.sqrt
          (globalDifferencePairCollisionBudget
            (degree := degree) (ringRank := ringRank) params candidate) /
        2 := by
  apply averagedSourceErrorDiagonalChiSquareLoss_le_of_normalizedPairCollisionExcess
  intro sourceError _
  exact fixedErrorDiagonalNormalizedPairCollisionExcess_le_globalBudget
    params candidate sourceError

/-- Selected-diagonal replacement from the global normalized paired excess and the mixed-error
marginal estimate. -/
theorem tvDist_operatorDiagonalExperiment_target_le_of_normalizedPairCollisionExcess [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (ε mixedErrorBound : ℝ)
    (hexcess : ∀ sourceError ∈ support
      (ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
        sourceErrorSampler),
      fixedErrorDiagonalNormalizedPairCollisionExcess
        params candidate sourceError ≤ ε)
    (hmixed : mixedDiagonalErrorDistance (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler candidate ≤ mixedErrorBound) :
    tvDist
        (operatorDiagonalExperiment params sourceErrorSampler candidate ringSecret)
        (TGSW.encrypt ringRank params.levels targetErrorSampler
          (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) candidate)) ≤
      Real.sqrt ε / 2 + mixedErrorBound := by
  exact (tvDist_operatorDiagonalExperiment_target_le_jointChiSquare
    params sourceErrorSampler targetErrorSampler candidate ringSecret).trans
      (add_le_add
        (averagedSourceErrorDiagonalChiSquareLoss_le_of_normalizedPairCollisionExcess
          params sourceErrorSampler candidate ε hexcess)
        hmixed)

/-- Selected-diagonal replacement controlled by the source-independent global difference-pair
budget and the remaining mixed-error marginal estimate. -/
theorem tvDist_operatorDiagonalExperiment_target_le_globalDifferencePairCollisionBudget
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (mixedErrorBound : ℝ)
    (hmixed : mixedDiagonalErrorDistance (ringRank := ringRank) params
      sourceErrorSampler targetErrorSampler candidate ≤ mixedErrorBound) :
    tvDist
        (operatorDiagonalExperiment params sourceErrorSampler candidate ringSecret)
        (TGSW.encrypt ringRank params.levels targetErrorSampler
          (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) candidate)) ≤
      Real.sqrt
          (globalDifferencePairCollisionBudget
            (degree := degree) (ringRank := ringRank) params candidate) /
        2 + mixedErrorBound := by
  exact tvDist_operatorDiagonalExperiment_target_le_of_normalizedPairCollisionExcess
    params sourceErrorSampler targetErrorSampler candidate ringSecret
    (globalDifferencePairCollisionBudget
      (degree := degree) (ringRank := ringRank) params candidate)
    mixedErrorBound
    (fun sourceError _ =>
      fixedErrorDiagonalNormalizedPairCollisionExcess_le_globalBudget
        params candidate sourceError)
    hmixed

/-- The global normalized paired excess bounds the actual self-correlated selected entry,
uniformly over the hidden bit when supplied for both candidates. -/
theorem tvDist_diagonalExperiment_directEntry_le_of_normalizedPairCollisionExcess [NeZero q]
    {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension)
    (ε mixedErrorBound : ℝ)
    (hexcess : ∀ candidate sourceError,
      sourceError ∈ support
        (ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
          sourceErrorSampler) →
      fixedErrorDiagonalNormalizedPairCollisionExcess
        params candidate sourceError ≤ ε)
    (hmixed : ∀ candidate,
      mixedDiagonalErrorDistance (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler candidate ≤ mixedErrorBound) :
    tvDist
        (OffDiagonalNormalForm.diagonalExperiment params sourceErrorSampler
          hidden ringSecret coordinate)
        (OffDiagonalNormalForm.directEntrySampler params targetErrorSampler
          hidden ringSecret coordinate) ≤
      Real.sqrt ε / 2 + mixedErrorBound := by
  have h := tvDist_operatorDiagonalExperiment_target_le_of_normalizedPairCollisionExcess
    params sourceErrorSampler targetErrorSampler (hidden coordinate) ringSecret
    ε mixedErrorBound (fun sourceError hsource =>
      hexcess (hidden coordinate) sourceError hsource) (hmixed (hidden coordinate))
  unfold tvDist at h ⊢
  rw [diagonalExperiment_evalDist_eq_operator
    params sourceErrorSampler hidden ringSecret coordinate]
  unfold OffDiagonalNormalForm.directEntrySampler
  rw [← TGSW.encrypt_evalDist_eq_directEncrypt ringRank params.levels
    targetErrorSampler (embedRingSecret q ringSecret)
    (Gadget.Base.ringGadget params)
    (embedConstantBit q (degree + 1) (hidden coordinate))]
  exact h

/-- Source-error-independent form for the actual self-correlated diagonal entry.  It suffices to
bound the two candidate-specific global pair budgets by one numerical parameter. -/
theorem tvDist_diagonalExperiment_directEntry_le_globalDifferencePairCollisionBudget
    [NeZero q]
    {lweDimension : ℕ}
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler targetErrorSampler :
      ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension)
    (ε mixedErrorBound : ℝ)
    (hbudget : ∀ candidate,
      globalDifferencePairCollisionBudget
        (degree := degree) (ringRank := ringRank) params candidate ≤ ε)
    (hmixed : ∀ candidate,
      mixedDiagonalErrorDistance (ringRank := ringRank) params
        sourceErrorSampler targetErrorSampler candidate ≤ mixedErrorBound) :
    tvDist
        (OffDiagonalNormalForm.diagonalExperiment params sourceErrorSampler
          hidden ringSecret coordinate)
        (OffDiagonalNormalForm.directEntrySampler params targetErrorSampler
          hidden ringSecret coordinate) ≤
      Real.sqrt ε / 2 + mixedErrorBound := by
  apply tvDist_diagonalExperiment_directEntry_le_of_normalizedPairCollisionExcess
  · intro candidate sourceError _
    exact (fixedErrorDiagonalNormalizedPairCollisionExcess_le_globalBudget
      params candidate sourceError).trans (hbudget candidate)
  · exact hmixed

/-- A relative bound on the summed rectangular-pair collision excess discharges the native
pointwise pair-collision certificate.  The normalization is exactly the number of ordered
difference pairs in the retained side fiber times one challenge baseline. -/
theorem fixedErrorDiagonalPairCollisionBound_of_excess [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (ε : ℝ)
    (hexcess : ∀ transformedError :
      DiagonalErrorVector q degree ringRank params.levels,
      fixedErrorDiagonalPairCollisionExcess params candidate
          sourceError transformedError ≤
        ε * (Fintype.card
          (DiagonalChallenge q degree ringRank params.levels) : ℝ) *
          (fixedErrorDifferenceFiberCard params candidate sourceError
            transformedError : ℝ) ^ 2) :
    fixedErrorDiagonalPairCollisionBound params candidate sourceError ε := by
  intro transformedError
  rw [fixedErrorDiagonalCollisionPairCount_eq_baseline_add_excess,
    fixedErrorDiagonalSideFiberCard_eq_challenge_mul_differenceFiber]
  simp only [Nat.cast_mul]
  let C : ℝ := Fintype.card (DiagonalChallenge q degree ringRank params.levels)
  let K : ℝ := fixedErrorDifferenceFiberCard params candidate sourceError transformedError
  let E : ℝ := fixedErrorDiagonalPairCollisionExcess params candidate
    sourceError transformedError
  change C * (C * K ^ 2 + E) ≤ (1 + ε) * (C * K) ^ 2
  have hE : E ≤ ε * C * K ^ 2 := by
    simpa only [C, K, E] using hexcess transformedError
  calc
    C * (C * K ^ 2 + E) ≤ C * (C * K ^ 2 + ε * C * K ^ 2) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = (1 + ε) * (C * K) ^ 2 := by ring

end

end FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm
