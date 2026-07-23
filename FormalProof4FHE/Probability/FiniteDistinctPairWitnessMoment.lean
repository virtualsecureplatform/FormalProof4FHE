/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import Mathlib

/-!
# Finite Distinct-Pair Witness Moments

If one distinguished witness accepts every input, subtracting one from the number of witnesses
common to a pair removes exactly that witness.  Summing over unequal input pairs and exchanging
the finite sums leaves a factorial second moment over the nontrivial witnesses.
-/

namespace FormalProof4FHE.FiniteDistinctPairWitnessMoment

noncomputable section

open scoped BigOperators

attribute [local instance] Classical.propDecidable

variable {Input Witness : Type*} [Fintype Input] [Fintype Witness]

/-- A satisfying witness is either the distinguished witness or a non-distinguished satisfying
witness. -/
noncomputable def satisfyingEquivOptionNonzero
    (predicate : Witness → Prop) (distinguished : Witness)
    (hdistinguished : predicate distinguished) :
    {witness : Witness // predicate witness} ≃
      Option {witness : Witness // witness ≠ distinguished ∧ predicate witness} where
  toFun witness :=
    if hwitness : witness.1 = distinguished then none
    else some ⟨witness.1, hwitness, witness.2⟩
  invFun witness := match witness with
    | none => ⟨distinguished, hdistinguished⟩
    | some nonzero => ⟨nonzero.1, nonzero.2.2⟩
  left_inv witness := by
    by_cases hwitness : witness.1 = distinguished
    · apply Subtype.ext
      simp [hwitness]
    · apply Subtype.ext
      simp [hwitness]
  right_inv witness := by
    cases witness with
    | none => simp
    | some nonzero => simp [nonzero.2.1]

/-- Removing the universally accepting distinguished witness subtracts exactly one from the
satisfying-witness cardinality. -/
theorem card_satisfying_sub_one_eq_card_nonzeroSatisfying
    (predicate : Witness → Prop) (distinguished : Witness)
    (hdistinguished : predicate distinguished) :
    Nat.card {witness : Witness // predicate witness} - 1 =
      Nat.card
        {witness : Witness // witness ≠ distinguished ∧ predicate witness} := by
  have hcard := Nat.card_congr
    (satisfyingEquivOptionNonzero predicate distinguished hdistinguished)
  have hoption :
      Nat.card (Option
        {witness : Witness // witness ≠ distinguished ∧ predicate witness}) =
        Nat.card
          {witness : Witness // witness ≠ distinguished ∧ predicate witness} + 1 := by
    letI : Fintype
        {witness : Witness // witness ≠ distinguished ∧ predicate witness} :=
      Fintype.ofFinite _
    simp [Nat.card_eq_fintype_card]
  rw [hoption] at hcard
  omega

/-- Real-valued form of removing the distinguished witness. -/
theorem cast_card_satisfying_sub_one_eq_card_nonzeroSatisfying
    (predicate : Witness → Prop) (distinguished : Witness)
    (hdistinguished : predicate distinguished) :
    (Nat.card {witness : Witness // predicate witness} : ℝ) - 1 =
      Nat.card
        {witness : Witness // witness ≠ distinguished ∧ predicate witness} := by
  have hcard := Nat.card_congr
    (satisfyingEquivOptionNonzero predicate distinguished hdistinguished)
  have hoption :
      Nat.card (Option
        {witness : Witness // witness ≠ distinguished ∧ predicate witness}) =
        Nat.card
          {witness : Witness // witness ≠ distinguished ∧ predicate witness} + 1 := by
    letI : Fintype
        {witness : Witness // witness ≠ distinguished ∧ predicate witness} :=
      Fintype.ofFinite _
    simp [Nat.card_eq_fintype_card]
  rw [hoption] at hcard
  have hcardReal :
      (Nat.card {witness : Witness // predicate witness} : ℝ) =
        (Nat.card
          {witness : Witness // witness ≠ distinguished ∧ predicate witness} : ℝ) + 1 := by
    exact_mod_cast hcard
  linarith

/-- A subtype cardinality is the sum of its membership indicators. -/
theorem cast_card_subtype_eq_sum_indicator
    (predicate : Witness → Prop) :
    (Nat.card {witness : Witness // predicate witness} : ℝ) =
      ∑ witness : Witness, if predicate witness then 1 else 0 := by
  letI : Fintype {witness : Witness // predicate witness} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
  push_cast
  simp

/-- The number of ordered unequal pairs accepted by one predicate is its factorial second
moment `n (n - 1)`. -/
theorem sum_distinct_acceptance_indicator_eq_factorialCard
    (accepts : Input → Prop) :
    (∑ left : Input, ∑ right : Input,
      if left ≠ right ∧ accepts left ∧ accepts right then (1 : ℝ) else 0) =
      (Nat.card {input : Input // accepts input} : ℝ) *
        ((Nat.card {input : Input // accepts input} : ℝ) - 1) := by
  classical
  let accepted : Finset Input := Finset.univ.filter accepts
  have haccepted : accepted.card = Nat.card {input : Input // accepts input} := by
    letI : Fintype {input : Input // accepts input} := Fintype.ofFinite _
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hoffDiag :
      accepted.offDiag =
        Finset.univ.filter (fun pair : Input × Input ↦
          pair.1 ≠ pair.2 ∧ accepts pair.1 ∧ accepts pair.2) := by
    ext pair
    simp only [Finset.mem_offDiag, accepted, Finset.mem_filter, Finset.mem_univ, true_and]
    aesop
  calc
    (∑ left : Input, ∑ right : Input,
      if left ≠ right ∧ accepts left ∧ accepts right then (1 : ℝ) else 0) =
        ∑ pair : Input × Input,
          if pair.1 ≠ pair.2 ∧ accepts pair.1 ∧ accepts pair.2 then (1 : ℝ) else 0 := by
      rw [Fintype.sum_prod_type]
    _ = (accepted.offDiag.card : ℝ) := by
      rw [hoffDiag, Finset.card_filter]
      push_cast
      simp
    _ = (Nat.card {input : Input // accepts input} : ℝ) *
        ((Nat.card {input : Input // accepts input} : ℝ) - 1) := by
      rw [Finset.offDiag_card, haccepted]
      let count := Nat.card {input : Input // accepts input}
      change ((count * count - count : ℕ) : ℝ) =
        (count : ℝ) * ((count : ℝ) - 1)
      by_cases hcount : count = 0
      · simp [hcount]
      · have hone : 1 ≤ count := Nat.one_le_iff_ne_zero.mpr hcount
        rw [show count * count - count = count * (count - 1) by
          simpa using (Nat.mul_sub_left_distrib count count 1).symm]
        push_cast [Nat.cast_sub hone]
        ring

/-- **Distinct-pair witness-moment identity.**  The universal distinguished witness cancels the
subtracted baseline, and every remaining witness contributes the number of ordered unequal input
pairs that it accepts twice. -/
theorem sum_distinct_card_common_sub_one_eq_nonzeroWitnessMoment
    (accepts : Witness → Input → Prop)
    (distinguished : Witness)
    (hdistinguished : ∀ input, accepts distinguished input) :
    (∑ left : Input, ∑ right : Input,
      if left ≠ right then
        (Nat.card
          {witness : Witness // accepts witness left ∧ accepts witness right} : ℝ) - 1
      else 0) =
      ∑ witness : Witness,
        if witness ≠ distinguished then
          ∑ left : Input, ∑ right : Input,
            if left ≠ right ∧ accepts witness left ∧ accepts witness right then
              (1 : ℝ)
            else 0
        else 0 := by
  classical
  calc
    (∑ left : Input, ∑ right : Input,
      if left ≠ right then
        (Nat.card
          {witness : Witness // accepts witness left ∧ accepts witness right} : ℝ) - 1
      else 0) =
      ∑ left : Input, ∑ right : Input,
        if left ≠ right then
          ∑ witness : Witness,
            if witness ≠ distinguished ∧ accepts witness left ∧ accepts witness right then
              (1 : ℝ)
            else 0
        else 0 := by
      apply Finset.sum_congr rfl
      intro left _
      apply Finset.sum_congr rfl
      intro right _
      by_cases hdistinct : left ≠ right
      · rw [if_pos hdistinct, if_pos hdistinct]
        calc
          (Nat.card
              {witness : Witness // accepts witness left ∧ accepts witness right} : ℝ) - 1 =
              Nat.card
                {witness : Witness // witness ≠ distinguished ∧
                  (accepts witness left ∧ accepts witness right)} :=
            cast_card_satisfying_sub_one_eq_card_nonzeroSatisfying
              (fun witness ↦ accepts witness left ∧ accepts witness right)
              distinguished ⟨hdistinguished left, hdistinguished right⟩
          _ = ∑ witness : Witness,
              if witness ≠ distinguished ∧ accepts witness left ∧ accepts witness right
              then (1 : ℝ) else 0 :=
            by
              convert cast_card_subtype_eq_sum_indicator
                (fun witness ↦ witness ≠ distinguished ∧
                  accepts witness left ∧ accepts witness right) using 1
              apply Finset.sum_congr rfl
              intro witness _
              by_cases hwitness : witness ≠ distinguished ∧
                  accepts witness left ∧ accepts witness right <;>
                simp [hwitness]
      · simp [hdistinct]
    _ = ∑ left : Input, ∑ right : Input, ∑ witness : Witness,
          if witness ≠ distinguished then
            if left ≠ right ∧ accepts witness left ∧ accepts witness right then
              (1 : ℝ)
            else 0
          else 0 := by
      apply Finset.sum_congr rfl
      intro left _
      apply Finset.sum_congr rfl
      intro right _
      by_cases hdistinct : left ≠ right
      · rw [if_pos hdistinct]
        apply Finset.sum_congr rfl
        intro witness _
        by_cases hwitness : witness ≠ distinguished <;>
          simp [hdistinct, hwitness]
      · simp [hdistinct]
    _ = ∑ left : Input, ∑ witness : Witness, ∑ right : Input,
          if witness ≠ distinguished then
            if left ≠ right ∧ accepts witness left ∧ accepts witness right then
              (1 : ℝ)
            else 0
          else 0 := by
      apply Finset.sum_congr rfl
      intro left _
      exact Finset.sum_comm
    _ = ∑ witness : Witness, ∑ left : Input, ∑ right : Input,
          if witness ≠ distinguished then
            if left ≠ right ∧ accepts witness left ∧ accepts witness right then
              (1 : ℝ)
            else 0
          else 0 := Finset.sum_comm
    _ = ∑ witness : Witness,
        if witness ≠ distinguished then
          ∑ left : Input, ∑ right : Input,
            if left ≠ right ∧ accepts witness left ∧ accepts witness right then
              (1 : ℝ)
            else 0
        else 0 := by
      apply Finset.sum_congr rfl
      intro witness _
      by_cases hwitness : witness ≠ distinguished <;> simp [hwitness]

end

end FormalProof4FHE.FiniteDistinctPairWitnessMoment
