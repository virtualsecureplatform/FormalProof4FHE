/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-!
# Explicit Dual of a Finite Product of Additive-Character Groups

For a finite index type and finite abelian group `Value`, a tuple of values evaluates a tuple of
characters coordinatewise and multiplies the results.  This gives every complex additive
character of the product `Index → AddChar Value ℂ` exactly once.

The equivalence is the concrete product form of finite Pontryagin duality.  It is useful when a
second Fourier transform has introduced abstract characters of a character-tuple group: those
characters can instead be summed over explicit tuples of test values.
-/

open scoped BigOperators

namespace FormalProof4FHE.FinitePiAddCharDual

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Coordinatewise evaluation of a tuple of additive characters at a tuple of values. -/
def evaluationCharacter
    {Index Value : Type*} [Fintype Index] [DecidableEq Index]
    [AddCommGroup Value] [Fintype Value]
    (values : Index → Value) : AddChar (Index → AddChar Value ℂ) ℂ where
  toFun characters := ∏ index : Index, characters index (values index)
  map_zero_eq_one' := by simp
  map_add_eq_mul' left right := by
    simp only [Pi.add_apply, AddChar.add_apply]
    exact Finset.prod_mul_distrib

@[simp]
theorem evaluationCharacter_apply
    {Index Value : Type*} [Fintype Index] [DecidableEq Index]
    [AddCommGroup Value] [Fintype Value]
    (values : Index → Value) (characters : Index → AddChar Value ℂ) :
    evaluationCharacter values characters =
      ∏ index : Index, characters index (values index) := rfl

@[simp]
theorem evaluationCharacter_zero
    {Index Value : Type*} [Fintype Index] [DecidableEq Index]
    [AddCommGroup Value] [Fintype Value] :
    evaluationCharacter (0 : Index → Value) =
      (0 : AddChar (Index → AddChar Value ℂ) ℂ) := by
  apply AddChar.ext
  intro characters
  simp [evaluationCharacter]

/-- Evaluation tuples are separated by the full product character group. -/
theorem evaluationCharacter_injective
    {Index Value : Type*} [Fintype Index] [DecidableEq Index]
    [AddCommGroup Value] [Fintype Value] :
    Function.Injective
      (evaluationCharacter : (Index → Value) → AddChar (Index → AddChar Value ℂ) ℂ) := by
  intro left right hequal
  funext index
  apply AddChar.doubleDualEmb_injective
  apply AddChar.ext
  intro character
  have happly := DFunLike.congr_fun hequal (Pi.single index character)
  change character (left index) = character (right index)
  change
    (∏ coordinate : Index,
      ((Pi.single index character : Index → AddChar Value ℂ) coordinate) (left coordinate)) =
    (∏ coordinate : Index,
      ((Pi.single index character : Index → AddChar Value ℂ) coordinate) (right coordinate)) at happly
  have hprod (values : Index → Value) :
      (∏ coordinate : Index,
          ((Pi.single index character : Index → AddChar Value ℂ) coordinate)
            (values coordinate)) =
        character (values index) := by
    calc
      (∏ coordinate : Index,
          ((Pi.single index character : Index → AddChar Value ℂ) coordinate)
            (values coordinate)) =
          ((Pi.single index character : Index → AddChar Value ℂ) index)
            (values index) := by
        apply Fintype.prod_eq_single index
        intro coordinate hcoordinate
        simp [hcoordinate]
      _ = character (values index) := by simp
  rw [hprod left, hprod right] at happly
  exact happly

/-- Every character of a finite product of character groups is coordinatewise evaluation at a
unique tuple of values. -/
def evaluationEquiv
    {Index Value : Type*} [Fintype Index] [DecidableEq Index]
    [AddCommGroup Value] [Fintype Value] :
    (Index → Value) ≃ AddChar (Index → AddChar Value ℂ) ℂ := by
  apply Equiv.ofBijective evaluationCharacter
  rw [Fintype.bijective_iff_injective_and_card]
  constructor
  · exact evaluationCharacter_injective
  · rw [AddChar.card_eq]
    simp only [Fintype.card_pi]
    simp

@[simp]
theorem evaluationEquiv_apply
    {Index Value : Type*} [Fintype Index] [DecidableEq Index]
    [AddCommGroup Value] [Fintype Value]
    (values : Index → Value) :
    evaluationEquiv values = evaluationCharacter values := rfl

@[simp]
theorem evaluationEquiv_apply_character
    {Index Value : Type*} [Fintype Index] [DecidableEq Index]
    [AddCommGroup Value] [Fintype Value]
    (values : Index → Value) (characters : Index → AddChar Value ℂ) :
    evaluationEquiv values characters =
      ∏ index : Index, characters index (values index) := rfl

@[simp]
theorem evaluationEquiv_eq_zero
    {Index Value : Type*} [Fintype Index] [DecidableEq Index]
    [AddCommGroup Value] [Fintype Value]
    (values : Index → Value) :
    evaluationEquiv values = 0 ↔ values = 0 := by
  constructor
  · intro hequal
    apply evaluationEquiv.injective
    simpa using hequal
  · rintro rfl
    simpa only [evaluationEquiv_apply] using
      (evaluationCharacter_zero (Index := Index) (Value := Value))

/-- Reindex a sum over nonzero second-dual characters by their unique nonzero explicit test-value
tuples. -/
theorem sum_ne_zero_evaluationEquiv
    {Index Value Sum : Type*} [Fintype Index] [DecidableEq Index]
    [AddCommGroup Value] [Fintype Value] [AddCommMonoid Sum]
    (summand : AddChar (Index → AddChar Value ℂ) ℂ → Sum) :
    (∑ character ∈
        (Finset.univ.erase (0 : AddChar (Index → AddChar Value ℂ) ℂ)),
      summand character) =
      ∑ values ∈ (Finset.univ.erase (0 : Index → Value)),
        summand (evaluationEquiv values) := by
  classical
  let equivalence := evaluationEquiv (Index := Index) (Value := Value)
  let nonzeroEquivalence :
      {values : Index → Value // values ≠ 0} ≃
        {character : AddChar (Index → AddChar Value ℂ) ℂ // character ≠ 0} :=
    Equiv.subtypeEquiv equivalence (fun values ↦ by
      change values ≠ 0 ↔ evaluationEquiv values ≠ 0
      exact (evaluationEquiv_eq_zero values).not.symm)
  calc
    (∑ character ∈
        (Finset.univ.erase (0 : AddChar (Index → AddChar Value ℂ) ℂ)),
      summand character) =
        ∑ character :
            {character : AddChar (Index → AddChar Value ℂ) ℂ // character ≠ 0},
          summand character.1 :=
      Finset.sum_subtype _ (by simp) _
    _ = ∑ values : {values : Index → Value // values ≠ 0},
        summand (equivalence values.1) := by
      exact (Fintype.sum_equiv nonzeroEquivalence _ _ (fun _ ↦ rfl)).symm
    _ = ∑ values ∈ (Finset.univ.erase (0 : Index → Value)),
        summand (evaluationEquiv values) := by
      dsimp only [equivalence]
      exact
        (Finset.sum_subtype
          (p := fun values : Index → Value ↦ values ≠ 0)
          (Finset.univ.erase (0 : Index → Value))
          (by intro values; simp)
          (fun values ↦ summand (evaluationEquiv values))).symm

end

end FormalProof4FHE.FinitePiAddCharDual
