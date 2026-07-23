/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.FiniteAdditiveCokernel
import FormalProof4FHE.Probability.FiniteDistinctPairWitnessMoment
import FormalProof4FHE.TFHE.NativeDiagonalUnitRowWeightedNormalForm

/-!
# Additive-Character Moment for the Retained Native TFHE Cokernel

The exact native cokernel factor is converted into a finite additive-character count.  A character
annihilates the paired row image exactly when it annihilates both constituent row operators.
Consequently, powers of the paired cokernel factor count tuples of common annihilating characters.

This is the denominator-preserving starting point for the distinct retained-fiber estimate: after
summing over unequal retained pairs, the trivial character tuple cancels the uniform baseline and
only nontrivial character factorial moments remain.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm

noncomputable section

open FormalProof4FHE.TFHE

attribute [local instance] Classical.propDecidable
attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing

set_option maxHeartbeats 2000000

variable {q degree ringRank : ℕ}

/-- The native row space on which one selected-diagonal row operator acts. -/
abbrev NativeDiagonalRow (q degree ringRank levels : ℕ) :=
  Fin (TGSW.rowCount ringRank levels) → RLWE.Rq q (degree + 1)

/-- One complex additive character annihilates a fixed native difference row operator. -/
def rowCharacterAnnihilatesDifference [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (character : AddChar
      (NativeDiagonalRow q degree ringRank params.levels) ℂ)
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) : Prop :=
  ∀ value : NativeDiagonalRow q degree ringRank params.levels,
    character (rowOperator candidate
      (differenceEntryDigits params difference) value) = 1

/-- Characters that annihilate the complete paired row image. -/
abbrev DifferencePairRowAnnihilator [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) :=
  FormalProof4FHE.FiniteAdditiveCokernel.Annihilator
    (pairedRowDifferenceAddHom candidate
      (differenceEntryDigits params leftDifference)
      (differenceEntryDigits params rightDifference)).range

/-- A character annihilates the paired image iff it annihilates the left and right row maps
separately. -/
theorem pairRangeAnnihilator_iff
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels)
    (character : AddChar
      (NativeDiagonalRow q degree ringRank params.levels) ℂ) :
    (∀ value : (pairedRowDifferenceAddHom candidate
        (differenceEntryDigits params leftDifference)
        (differenceEntryDigits params rightDifference)).range,
      character value.1 = 1) ↔
      rowCharacterAnnihilatesDifference params candidate character leftDifference ∧
        rowCharacterAnnihilatesDifference params candidate character rightDifference := by
  constructor
  · intro hannihilates
    constructor
    · intro value
      let pairedValue :
          (NativeDiagonalRow q degree ringRank params.levels) ×
            (NativeDiagonalRow q degree ringRank params.levels) := (value, 0)
      have h := hannihilates
        ⟨pairedRowDifferenceAddHom candidate
            (differenceEntryDigits params leftDifference)
            (differenceEntryDigits params rightDifference) pairedValue,
          ⟨pairedValue, rfl⟩⟩
      change character
        (rowOperator candidate (differenceEntryDigits params leftDifference) value -
          rowOperator candidate (differenceEntryDigits params rightDifference) 0) = 1 at h
      rw [show rowOperator candidate
          (differenceEntryDigits params rightDifference) 0 = 0 from
        (rowOperatorAddHom candidate
          (differenceEntryDigits params rightDifference)).map_zero, sub_zero] at h
      exact h
    · intro value
      let pairedValue :
          (NativeDiagonalRow q degree ringRank params.levels) ×
            (NativeDiagonalRow q degree ringRank params.levels) := (0, value)
      have h := hannihilates
        ⟨pairedRowDifferenceAddHom candidate
            (differenceEntryDigits params leftDifference)
            (differenceEntryDigits params rightDifference) pairedValue,
          ⟨pairedValue, rfl⟩⟩
      change character
        (rowOperator candidate (differenceEntryDigits params leftDifference) 0 -
          rowOperator candidate (differenceEntryDigits params rightDifference) value) = 1 at h
      rw [show rowOperator candidate
          (differenceEntryDigits params leftDifference) 0 = 0 from
        (rowOperatorAddHom candidate
          (differenceEntryDigits params leftDifference)).map_zero,
        zero_sub, AddChar.map_neg_eq_inv] at h
      exact inv_eq_one.mp h
  · rintro ⟨hleft, hright⟩ value
    obtain ⟨pairedValue, hpairedValue⟩ := value.2
    rw [← hpairedValue]
    change character
      (rowOperator candidate (differenceEntryDigits params leftDifference) pairedValue.1 -
        rowOperator candidate (differenceEntryDigits params rightDifference) pairedValue.2) = 1
    rw [AddChar.map_sub_eq_div, hleft, hright, div_one]

/-- The paired-row annihilator is the subtype of characters common to the two constituent row
operators. -/
noncomputable def differencePairRowAnnihilatorEquivCommon
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    DifferencePairRowAnnihilator params candidate leftDifference rightDifference ≃
      {character : AddChar
          (NativeDiagonalRow q degree ringRank params.levels) ℂ //
        rowCharacterAnnihilatesDifference params candidate character leftDifference ∧
          rowCharacterAnnihilatesDifference params candidate character rightDifference} :=
  Equiv.subtypeEquiv (Equiv.refl _) (fun character ↦
    pairRangeAnnihilator_iff params candidate leftDifference rightDifference character)

/-- **Exact native character-cokernel identity.**  The real-valued row cokernel factor is the
cardinality of the common additive-character annihilator. -/
theorem differencePairRowCokernelFactor_eq_card_commonAnnihilator
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    differencePairRowCokernelFactor params candidate leftDifference rightDifference =
      (Nat.card
        {character : AddChar
            (NativeDiagonalRow q degree ringRank params.levels) ℂ //
          rowCharacterAnnihilatesDifference params candidate character leftDifference ∧
            rowCharacterAnnihilatesDifference params candidate character rightDifference} : ℝ) := by
  unfold differencePairRowCokernelFactor differencePairRowImageCard
  calc
    (Fintype.card
        (Fin (TGSW.rowCount ringRank params.levels) →
          RLWE.Rq q (degree + 1)) : ℝ) /
        Fintype.card (pairedRowDifferenceAddHom candidate
          (differenceEntryDigits params leftDifference)
          (differenceEntryDigits params rightDifference)).range =
      (Nat.card
          (Fin (TGSW.rowCount ringRank params.levels) →
            RLWE.Rq q (degree + 1)) : ℝ) /
        Nat.card (pairedRowDifferenceAddHom candidate
          (differenceEntryDigits params leftDifference)
          (differenceEntryDigits params rightDifference)).range := by
      congr 1 <;> exact_mod_cast (Nat.card_eq_fintype_card :
        Nat.card _ = Fintype.card _).symm
    _ =
      Nat.card
        (FormalProof4FHE.FiniteAdditiveCokernel.Annihilator
          (pairedRowDifferenceAddHom candidate
            (differenceEntryDigits params leftDifference)
            (differenceEntryDigits params rightDifference)).range) := by
      exact FormalProof4FHE.FiniteAdditiveCokernel.natCard_div_natCard_range_eq_natCard_annihilator
        (pairedRowDifferenceAddHom candidate
          (differenceEntryDigits params leftDifference)
          (differenceEntryDigits params rightDifference))
    _ = Nat.card
        {character : AddChar
            (NativeDiagonalRow q degree ringRank params.levels) ℂ //
          rowCharacterAnnihilatesDifference params candidate character leftDifference ∧
            rowCharacterAnnihilatesDifference params candidate character rightDifference} := by
      exact_mod_cast Nat.card_congr
        (differencePairRowAnnihilatorEquivCommon params candidate leftDifference rightDifference)

/-- A tuple of row characters annihilates one fixed native difference when every coordinate
character does. -/
def rowCharacterTupleAcceptsDifference [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (characters : Fin ringRank →
      AddChar (NativeDiagonalRow q degree ringRank params.levels) ℂ)
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) : Prop :=
  ∀ coordinate,
    rowCharacterAnnihilatesDifference params candidate (characters coordinate) difference

/-- The trivial character tuple annihilates every native row operator. -/
theorem rowCharacterTupleAcceptsDifference_zero
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (difference : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    rowCharacterTupleAcceptsDifference params candidate 0 difference := by
  intro coordinate value
  exact AddChar.zero_apply _

/-- Coordinatewise equivalence between tuples of common annihilator elements and character
tuples that accept both fixed differences. -/
noncomputable def commonAnnihilatorTupleEquiv
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    (Fin ringRank →
      {character : AddChar
          (NativeDiagonalRow q degree ringRank params.levels) ℂ //
        rowCharacterAnnihilatesDifference params candidate character leftDifference ∧
          rowCharacterAnnihilatesDifference params candidate character rightDifference}) ≃
      {characters : Fin ringRank →
          AddChar (NativeDiagonalRow q degree ringRank params.levels) ℂ //
        rowCharacterTupleAcceptsDifference params candidate characters leftDifference ∧
          rowCharacterTupleAcceptsDifference params candidate characters rightDifference} where
  toFun characters :=
    ⟨fun coordinate ↦ (characters coordinate).1,
      ⟨fun coordinate ↦ (characters coordinate).2.1,
        fun coordinate ↦ (characters coordinate).2.2⟩⟩
  invFun characters := fun coordinate ↦
    ⟨characters.1 coordinate,
      ⟨characters.2.1 coordinate, characters.2.2 coordinate⟩⟩
  left_inv characters := by
    funext coordinate
    exact Subtype.ext rfl
  right_inv characters := by
    exact Subtype.ext rfl

/-- Raising the exact row-cokernel factor to `ringRank` counts tuples of characters that
annihilate both fixed row operators. -/
theorem differencePairRowCokernelFactor_pow_eq_card_commonCharacterTuples
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (leftDifference rightDifference :
      RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    (differencePairRowCokernelFactor params candidate
        leftDifference rightDifference) ^ ringRank =
      (Nat.card
        {characters : Fin ringRank →
            AddChar (NativeDiagonalRow q degree ringRank params.levels) ℂ //
          rowCharacterTupleAcceptsDifference params candidate characters leftDifference ∧
            rowCharacterTupleAcceptsDifference params candidate characters rightDifference} : ℝ) := by
  rw [differencePairRowCokernelFactor_eq_card_commonAnnihilator]
  let Common :=
    {character : AddChar
        (NativeDiagonalRow q degree ringRank params.levels) ℂ //
      rowCharacterAnnihilatesDifference params candidate character leftDifference ∧
        rowCharacterAnnihilatesDifference params candidate character rightDifference}
  calc
    (Nat.card Common : ℝ) ^ ringRank =
        (Nat.card (Fin ringRank → Common) : ℝ) := by
      rw [Nat.card_fun, Nat.card_fin]
      norm_cast
    _ = (Nat.card
        {characters : Fin ringRank →
            AddChar (NativeDiagonalRow q degree ringRank params.levels) ℂ //
          rowCharacterTupleAcceptsDifference params candidate characters leftDifference ∧
            rowCharacterTupleAcceptsDifference params candidate characters rightDifference} : ℝ) := by
      exact_mod_cast Nat.card_congr
        (commonAnnihilatorTupleEquiv params candidate leftDifference rightDifference)

/-- **Exact denominator-preserving distinct-pair character moment.**  Inside one retained
transformed-error fiber, the native cokernel excess is exactly the factorial second moment of
nontrivial common annihilating character tuples.  The trivial tuple cancels the `-1` uniform
baseline; no binary-rank or whole-ring corank envelope is used. -/
theorem fixedErrorDiagonalDistinctPairCokernelExcess_eq_nontrivialCharacterMoment
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels) :
    fixedErrorDiagonalDistinctPairCokernelExcess
        params candidate sourceError transformedError =
      ∑ characters : Fin ringRank →
          AddChar (NativeDiagonalRow q degree ringRank params.levels) ℂ,
        if characters ≠ 0 then
          ∑ leftDifference :
              FixedErrorDifferenceFiber params candidate sourceError transformedError,
            ∑ rightDifference :
                FixedErrorDifferenceFiber params candidate sourceError transformedError,
              if leftDifference ≠ rightDifference ∧
                  rowCharacterTupleAcceptsDifference params candidate characters
                    leftDifference.1 ∧
                  rowCharacterTupleAcceptsDifference params candidate characters
                    rightDifference.1 then
                (1 : ℝ)
              else 0
        else 0 := by
  rw [fixedErrorDiagonalDistinctPairCokernelExcess_eq_fiberPairSum]
  simp only [Subtype.coe_injective.ne_iff]
  simp_rw [differencePairRowCokernelFactor_pow_eq_card_commonCharacterTuples]
  let Fiber := FixedErrorDifferenceFiber params candidate sourceError transformedError
  let CharacterTuple := Fin ringRank →
    AddChar (NativeDiagonalRow q degree ringRank params.levels) ℂ
  let accepts : CharacterTuple → Fiber → Prop := fun characters difference ↦
    rowCharacterTupleAcceptsDifference params candidate characters difference.1
  have hmoment :=
    FormalProof4FHE.FiniteDistinctPairWitnessMoment.sum_distinct_card_common_sub_one_eq_nonzeroWitnessMoment
      (Input := Fiber) (Witness := CharacterTuple) accepts (0 : CharacterTuple)
      (fun difference ↦
        rowCharacterTupleAcceptsDifference_zero params candidate difference.1)
  convert hmoment using 1
  · apply Finset.sum_congr rfl
    intro leftDifference _
    apply Finset.sum_congr rfl
    intro rightDifference _
    by_cases hdistinct : leftDifference ≠ rightDifference <;>
      simp [hdistinct, accepts, Fiber, CharacterTuple]
  · apply Finset.sum_congr rfl
    intro characters _
    by_cases hcharacters : characters ≠ 0
    · rw [if_pos hcharacters, if_pos hcharacters]
      apply Finset.sum_congr rfl
      intro leftDifference _
      apply Finset.sum_congr rfl
      intro rightDifference _
      by_cases haccepts : leftDifference ≠ rightDifference ∧
          rowCharacterTupleAcceptsDifference params candidate characters leftDifference.1 ∧
          rowCharacterTupleAcceptsDifference params candidate characters rightDifference.1 <;>
        simp [haccepts, accepts, Fiber, CharacterTuple]
    · simp [hcharacters]

/-- Number of retained differences accepted by one tuple of native row characters. -/
noncomputable def fixedErrorDifferenceCharacterTupleAcceptanceCard
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels)
    (characters : Fin ringRank →
      AddChar (NativeDiagonalRow q degree ringRank params.levels) ℂ) : ℕ :=
  Nat.card
    {difference : FixedErrorDifferenceFiber params candidate sourceError transformedError //
      rowCharacterTupleAcceptsDifference params candidate characters difference.1}

/-- Nontrivial-character factorial moment in one retained transformed-error fiber. -/
noncomputable def fixedErrorDifferenceCharacterFactorialMoment
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels) : ℝ :=
  ∑ characters : Fin ringRank →
      AddChar (NativeDiagonalRow q degree ringRank params.levels) ℂ,
    if characters ≠ 0 then
      (fixedErrorDifferenceCharacterTupleAcceptanceCard params candidate sourceError
          transformedError characters : ℝ) *
        ((fixedErrorDifferenceCharacterTupleAcceptanceCard params candidate sourceError
            transformedError characters : ℝ) - 1)
    else 0

/-- Compact factorial-moment form of the exact retained distinct cokernel excess. -/
theorem fixedErrorDiagonalDistinctPairCokernelExcess_eq_characterFactorialMoment
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels) :
    fixedErrorDiagonalDistinctPairCokernelExcess
        params candidate sourceError transformedError =
      ∑ characters : Fin ringRank →
          AddChar (NativeDiagonalRow q degree ringRank params.levels) ℂ,
        if characters ≠ 0 then
          (fixedErrorDifferenceCharacterTupleAcceptanceCard params candidate sourceError
              transformedError characters : ℝ) *
            ((fixedErrorDifferenceCharacterTupleAcceptanceCard params candidate sourceError
                transformedError characters : ℝ) - 1)
        else 0 := by
  rw [fixedErrorDiagonalDistinctPairCokernelExcess_eq_nontrivialCharacterMoment]
  apply Finset.sum_congr rfl
  intro characters _
  by_cases hcharacters : characters ≠ 0
  · rw [if_pos hcharacters, if_pos hcharacters]
    unfold fixedErrorDifferenceCharacterTupleAcceptanceCard
    have hfactorial :=
      FormalProof4FHE.FiniteDistinctPairWitnessMoment.sum_distinct_acceptance_indicator_eq_factorialCard
        (fun difference :
            FixedErrorDifferenceFiber params candidate sourceError transformedError ↦
          rowCharacterTupleAcceptsDifference params candidate characters difference.1)
    convert hfactorial using 1
    apply Finset.sum_congr rfl
    intro leftDifference _
    apply Finset.sum_congr rfl
    intro rightDifference _
    by_cases haccepts : leftDifference ≠ rightDifference ∧
        rowCharacterTupleAcceptsDifference params candidate characters leftDifference.1 ∧
        rowCharacterTupleAcceptsDifference params candidate characters rightDifference.1 <;>
      simp [haccepts]
  · simp [hcharacters]

/-- Named exact identity between the native cokernel excess and its character factorial moment. -/
theorem fixedErrorDiagonalDistinctPairCokernelExcess_eq_characterFactorialMoment'
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels) :
    fixedErrorDiagonalDistinctPairCokernelExcess
        params candidate sourceError transformedError =
      fixedErrorDifferenceCharacterFactorialMoment
        params candidate sourceError transformedError := by
  simpa only [fixedErrorDifferenceCharacterFactorialMoment] using
    (fixedErrorDiagonalDistinctPairCokernelExcess_eq_characterFactorialMoment
      params candidate sourceError transformedError)

/-- The character factorial moment is nonnegative. -/
theorem fixedErrorDifferenceCharacterFactorialMoment_nonneg
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError transformedError :
      DiagonalErrorVector q degree ringRank params.levels) :
    0 ≤ fixedErrorDifferenceCharacterFactorialMoment
      params candidate sourceError transformedError := by
  rw [← fixedErrorDiagonalDistinctPairCokernelExcess_eq_characterFactorialMoment']
  exact fixedErrorDiagonalDistinctPairCokernelExcess_nonneg
    params candidate sourceError transformedError

/-- Exact normalized distinct-pair loss with every retained-fiber denominator preserved.  The
challenge cardinality cancels, leaving the character factorial moment divided only by the full
difference space and the actual fiber cardinality. -/
theorem fixedErrorDiagonalNormalizedDistinctPairCollisionExcess_eq_characterFactorialFiberAverage
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels) :
    fixedErrorDiagonalNormalizedDistinctPairCollisionExcess
        params candidate sourceError =
      ∑ transformedError : DiagonalErrorVector q degree ringRank params.levels,
        if fixedErrorDifferenceFiberCard params candidate sourceError transformedError = 0 then
          0
        else
          fixedErrorDifferenceCharacterFactorialMoment
              params candidate sourceError transformedError /
            ((Fintype.card
                (RingGSWCiphertext q (degree + 1) ringRank params.levels) : ℝ) *
              (fixedErrorDifferenceFiberCard params candidate sourceError
                transformedError : ℝ)) := by
  unfold fixedErrorDiagonalNormalizedDistinctPairCollisionExcess
  apply Finset.sum_congr rfl
  intro transformedError _
  by_cases hfiber :
      fixedErrorDifferenceFiberCard params candidate sourceError transformedError = 0
  · simp [hfiber]
  · simp only [hfiber, if_false]
    rw [fixedErrorDiagonalDistinctPairCollisionExcess_eq_challengeCard_mul_cokernelExcess,
      fixedErrorDiagonalDistinctPairCokernelExcess_eq_characterFactorialMoment']
    have hDifference : (0 : ℝ) < Fintype.card
        (RingGSWCiphertext q (degree + 1) ringRank params.levels) := by
      exact_mod_cast Fintype.card_pos
    have hChallenge : (0 : ℝ) < Fintype.card
        (DiagonalChallenge q degree ringRank params.levels) := by
      exact_mod_cast Fintype.card_pos
    have hFiber : (0 : ℝ) <
        fixedErrorDifferenceFiberCard params candidate sourceError transformedError := by
      exact_mod_cast Nat.pos_of_ne_zero hfiber
    field_simp [hDifference.ne', hChallenge.ne', hFiber.ne']

/-- Denominator-preserving analytic certificate for the distinct character moment. -/
def fixedErrorDifferenceFiberCharacterFactorialMomentAverageBound
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (collisionAverageBound : ℝ) : Prop :=
  ∀ transformedError : DiagonalErrorVector q degree ringRank params.levels,
    fixedErrorDifferenceCharacterFactorialMoment
        params candidate sourceError transformedError ≤
      (fixedErrorDifferenceFiberCard
          params candidate sourceError transformedError : ℝ) *
        collisionAverageBound

/-- The character-moment certificate is exactly equivalent to the retained native cokernel
certificate consumed by the security reduction. -/
theorem fixedErrorDifferenceFiberDistinctCokernelAverageBound_iff_characterFactorialMoment
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (collisionAverageBound : ℝ) :
    fixedErrorDifferenceFiberDistinctCokernelAverageBound
        params candidate sourceError collisionAverageBound ↔
      fixedErrorDifferenceFiberCharacterFactorialMomentAverageBound
        params candidate sourceError collisionAverageBound := by
  constructor
  · intro hbound transformedError
    rw [← fixedErrorDiagonalDistinctPairCokernelExcess_eq_characterFactorialMoment']
    exact hbound transformedError
  · intro hbound transformedError
    rw [fixedErrorDiagonalDistinctPairCokernelExcess_eq_characterFactorialMoment']
    exact hbound transformedError

/-- A denominator-preserving character factorial-moment estimate directly supplies the retained
distinct-collision certificate consumed by the native Pearson-loss security reduction. -/
theorem fixedErrorDifferenceFiberDistinctCollisionAverageBound_of_characterFactorialMoment
    [NeZero q]
    (params : Gadget.Base.Parameters q) (candidate : Bool)
    (sourceError : DiagonalErrorVector q degree ringRank params.levels)
    (collisionAverageBound : ℝ)
    (hCharacter : fixedErrorDifferenceFiberCharacterFactorialMomentAverageBound
      params candidate sourceError collisionAverageBound) :
    fixedErrorDifferenceFiberDistinctCollisionAverageBound
      params candidate sourceError collisionAverageBound := by
  apply fixedErrorDifferenceFiberDistinctCollisionAverageBound_of_cokernel
  exact
    (fixedErrorDifferenceFiberDistinctCokernelAverageBound_iff_characterFactorialMoment
      params candidate sourceError collisionAverageBound).2 hCharacter

end

end FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm
