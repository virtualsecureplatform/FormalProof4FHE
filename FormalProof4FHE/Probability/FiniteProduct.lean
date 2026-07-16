/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import VCVio.OracleComp.Constructions.SampleableType

/-!
# Finite Independent Products

Reusable distribution lemmas for `Fin.mOfFn`.  These isolate the coordinatewise calculations used
by both batch-LWE compilation and parallel-secret hybrid arguments.
-/

open OracleComp

namespace FormalProof4FHE.FiniteProduct

/-- Output probabilities of a finite independent product multiply coordinatewise. -/
theorem probOutput_fin_mOfFn {alpha : Type} [Finite alpha] (count : ℕ)
    (samplers : Fin count → ProbComp alpha) (values : Fin count → alpha) :
    Pr[= values | Fin.mOfFn count samplers] =
      ∏ index, Pr[= values index | samplers index] := by
  letI : Fintype alpha := Fintype.ofFinite alpha
  letI : DecidableEq alpha := Classical.decEq alpha
  induction count with
  | zero =>
      have hvalues : values = Fin.elim0 := funext fun index => index.elim0
      subst hvalues
      simp [Fin.mOfFn, probOutput_pure]
  | succ count ih =>
      simp only [Fin.mOfFn]
      rw [probOutput_bind_eq_sum_fintype]
      have hinner : ∀ value : alpha,
          Pr[= values | Fin.mOfFn count (fun index => samplers index.succ) >>=
              fun rest => pure (Fin.cons value rest)] =
            if value = values 0 then
              Pr[= Fin.tail values |
                Fin.mOfFn count fun index => samplers index.succ]
            else 0 := by
        intro value
        rw [probOutput_bind_eq_sum_fintype]
        have hiff : ∀ rest : Fin count → alpha,
            values = Fin.cons value rest ↔
              value = values 0 ∧ rest = Fin.tail values := by
          intro rest
          constructor
          · intro heq
            refine ⟨by rw [heq, Fin.cons_zero], funext fun index => ?_⟩
            have hcomponent := congrFun heq index.succ
            rw [Fin.cons_succ] at hcomponent
            exact hcomponent.symm
          · rintro ⟨rfl, rfl⟩
            exact (Fin.cons_self_tail values).symm
        by_cases hvalue : value = values 0
        · rw [if_pos hvalue]
          subst value
          simp only [probOutput_pure, hiff, true_and]
          simp [mul_ite]
        · rw [if_neg hvalue]
          refine Finset.sum_eq_zero fun rest _ => ?_
          rw [probOutput_pure,
            if_neg (fun heq => hvalue ((hiff rest).mp heq).1), mul_zero]
      simp only [hinner, mul_ite, mul_zero]
      rw [Finset.sum_ite_eq' Finset.univ (values 0)
        (fun value => Pr[= value | samplers 0] *
          Pr[= Fin.tail values |
            Fin.mOfFn count fun index => samplers index.succ]),
        if_pos (Finset.mem_univ _), ih, Fin.prod_univ_succ]
      rfl

/-- Independent uniform coordinates are uniform on the finite function space. -/
theorem evalDist_sampleIID_uniform {alpha : Type} [Fintype alpha]
    [SampleableType alpha] (count : ℕ) :
    evalDist (ProbComp.sampleIID count ($ᵗ alpha)) =
      evalDist ($ᵗ (Fin count → alpha)) := by
  apply evalDist_ext
  intro values
  simp only [ProbComp.sampleIID, probOutput_fin_mOfFn,
    probOutput_uniformSample]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fintype.card_fun, Nat.cast_pow]
  exact ENNReal.inv_pow.symm

/-- Sampling two finite products separately and zipping them agrees with sampling coordinate
pairs independently. -/
theorem evalDist_fin_mOfFn_zip {left right : Type}
    [Finite left] [Finite right] (count : ℕ)
    (leftSampler : Fin count → ProbComp left)
    (rightSampler : Fin count → ProbComp right) :
    evalDist
      ((Equiv.arrowProdEquivProdArrow (Fin count) (fun _ => left)
          (fun _ => right)).symm <$>
        (do
          let leftValues ← Fin.mOfFn count leftSampler
          let rightValues ← Fin.mOfFn count rightSampler
          pure (leftValues, rightValues))) =
      evalDist (Fin.mOfFn count fun index => do
        let leftValue ← leftSampler index
        let rightValue ← rightSampler index
        pure (leftValue, rightValue)) := by
  classical
  apply evalDist_ext
  intro values
  rw [probOutput_map_equiv]
  simp only [probOutput_fin_mOfFn]
  simp [Finset.prod_mul_distrib]
  rw [probOutput_fin_mOfFn, probOutput_fin_mOfFn]

/-- Pull one coordinate sampler in front of an independent finite product. -/
theorem evalDist_pull_coordinate {alpha : Type} [Fintype alpha] [DecidableEq alpha]
    (count : ℕ) (samplers : Fin count → ProbComp alpha) (coordinate : Fin count) :
    𝒟[samplers coordinate >>= fun value =>
      Fin.mOfFn count
        (fun index => if index = coordinate then pure value else samplers index)] =
      𝒟[Fin.mOfFn count samplers] := by
  apply evalDist_ext
  intro values
  rw [probOutput_bind_eq_sum_fintype]
  simp_rw [probOutput_fin_mOfFn]
  let rest : ENNReal := ∏ index ∈ (Finset.univ.erase coordinate),
    Pr[= values index | samplers index]
  have hproduct (value : alpha) :
      (∏ index,
          Pr[= values index |
            if index = coordinate then pure value else samplers index]) =
        if value = values coordinate then rest else 0 := by
    rw [← Finset.prod_erase_mul Finset.univ
      (fun index => Pr[= values index |
        if index = coordinate then pure value else samplers index])
      (Finset.mem_univ coordinate)]
    have hrest :
        (∏ index ∈ Finset.univ.erase coordinate,
          Pr[= values index |
            if index = coordinate then pure value else samplers index]) = rest := by
      apply Finset.prod_congr rfl
      intro index hindex
      rw [if_neg (Finset.ne_of_mem_erase hindex)]
    rw [hrest]
    simp [rest, eq_comm]
  simp_rw [hproduct]
  simp only [mul_ite, mul_zero]
  rw [Finset.sum_ite_eq' Finset.univ (values coordinate)
    (fun value => Pr[= value | samplers coordinate] * rest),
    if_pos (Finset.mem_univ _)]
  rw [← Finset.mul_prod_erase Finset.univ
    (fun index => Pr[= values index | samplers index])
    (Finset.mem_univ coordinate)]

/-- Coordinatewise mapping commutes with an IID finite product. -/
theorem map_fin_mOfFn_const {alpha beta : Type} (count : ℕ)
    (sampler : ProbComp alpha) (transform : alpha → beta) :
    (fun values index => transform (values index)) <$>
        Fin.mOfFn count (fun _ => sampler) =
      Fin.mOfFn count (fun _ => transform <$> sampler) := by
  induction count with
  | zero =>
      simp only [Fin.mOfFn, map_pure]
      congr 1
      funext index
      exact index.elim0
  | succ count ih =>
      simp only [Fin.mOfFn, map_eq_bind_pure_comp, bind_assoc, pure_bind]
      apply bind_congr
      intro head
      simp only [Function.comp_apply, pure_bind]
      let tailTransform : (Fin count → alpha) → (Fin count → beta) :=
        fun rest index => transform (rest index)
      let addHead : (Fin count → beta) → (Fin (count + 1) → beta) :=
        fun rest => @Fin.cons count (fun _ : Fin (count + 1) => beta)
          (transform head) rest
      have hcons (rest : Fin count → alpha) :
          (fun index => transform
            (@Fin.cons count (fun _ : Fin (count + 1) => alpha) head rest index)) =
            addHead (tailTransform rest) := by
        funext index
        refine Fin.cases ?_ (fun tailIndex => ?_) index
        · simp [addHead]
        · simp [addHead, tailTransform]
      calc
        (do
          let rest ← Fin.mOfFn count (fun _ => sampler)
          pure (fun index => transform
            (@Fin.cons count (fun _ : Fin (count + 1) => alpha)
              head rest index))) =
            (do
              let rest ← Fin.mOfFn count (fun _ => sampler)
              pure (addHead (tailTransform rest))) := by
                apply bind_congr
                intro rest
                rw [hcons]
        _ = addHead <$> (tailTransform <$>
              Fin.mOfFn count (fun _ => sampler)) := by
            simp [map_eq_bind_pure_comp, bind_assoc]
        _ = addHead <$>
              Fin.mOfFn count (fun _ => transform <$> sampler) := by
            rw [ih]
        _ = (do
              let rest ← Fin.mOfFn count
                (fun _ => sampler >>= pure ∘ transform)
              pure (Fin.cons (transform head) rest)) := by
            simp [addHead, map_eq_bind_pure_comp]

end FormalProof4FHE.FiniteProduct
