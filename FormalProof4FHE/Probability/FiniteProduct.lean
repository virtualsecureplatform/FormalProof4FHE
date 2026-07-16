/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import VCVio.OracleComp.Constructions.SampleableType
import VCVio.EvalDist.TVDist

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

/-- Every coordinate of a uniformly sampled finite function is itself uniform. -/
theorem evalDist_map_apply_uniformSample_fun {domain codomain : Type}
    [Finite domain] [DecidableEq domain]
    [Finite codomain] [Nonempty codomain]
    [SampleableType codomain] [SampleableType (domain → codomain)]
    (coordinate : domain) :
    𝒟[(fun table => table coordinate) <$> ($ᵗ (domain → codomain))] =
      𝒟[$ᵗ codomain] := by
  letI : Fintype domain := Fintype.ofFinite domain
  letI : Fintype codomain := Fintype.ofFinite codomain
  let overwritten : ProbComp (domain → codomain) := do
    let value ← $ᵗ codomain
    let table ← $ᵗ (domain → codomain)
    pure (Function.update table coordinate value)
  have hoverwrite : 𝒟[overwritten] = 𝒟[$ᵗ (domain → codomain)] := by
    exact evalDist_uniformSample_bind_update coordinate
  have hmapped :
      𝒟[(fun table => table coordinate) <$> overwritten] =
        𝒟[(fun table => table coordinate) <$> ($ᵗ (domain → codomain))] := by
    simpa only [evalDist_map] using
      congrArg (fun distribution =>
        (fun table => table coordinate) <$> distribution) hoverwrite
  have hdiscard :
      𝒟[(fun table => table coordinate) <$> overwritten] = 𝒟[$ᵗ codomain] := by
    classical
    apply evalDist_ext
    intro value
    simp [overwritten, probOutput_bind_eq_sum_fintype]
  exact hmapped.symm.trans hdiscard

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

/-- The expectation of a nonnegative functional of one product coordinate is exactly its
expectation under that coordinate's sampler. -/
theorem tsum_probOutput_fin_mOfFn_apply_mul {alpha : Type} (count : ℕ)
    (samplers : Fin count → ProbComp alpha) (coordinate : Fin count)
    (cost : alpha → ENNReal) :
    (∑' values,
      Pr[= values | Fin.mOfFn count samplers] * cost (values coordinate)) =
      ∑' value, Pr[= value | samplers coordinate] * cost value := by
  induction count with
  | zero => exact coordinate.elim0
  | succ count ih =>
      refine Fin.cases ?_ (fun tailCoordinate => ?_) coordinate
      · simp only [Fin.mOfFn, tsum_probOutput_bind_mul,
          tsum_probOutput_pure_mul, Fin.cons_zero]
        simp_rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]
      · simp only [Fin.mOfFn, tsum_probOutput_bind_mul,
          tsum_probOutput_pure_mul, Fin.cons_succ]
        rw [ih (fun index => samplers index.succ) tailCoordinate]
        rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]

/-- Expectation of a constant under a total probabilistic computation is that constant. -/
theorem tsum_probOutput_mul_const {alpha : Type} (sampler : ProbComp alpha)
    (constant : ENNReal) :
    (∑' value, Pr[= value | sampler] * constant) = constant := by
  rw [ENNReal.tsum_mul_right, tsum_probOutput_of_liftM_PMF, one_mul]

/-- Nonnegative expectation commutes with a finite sum of costs. -/
theorem tsum_probOutput_mul_finset_sum {alpha index : Type}
    [DecidableEq index] (sampler : ProbComp alpha) (indices : Finset index)
    (cost : index → alpha → ENNReal) :
    (∑' value,
      Pr[= value | sampler] * ∑ index ∈ indices, cost index value) =
      ∑ index ∈ indices,
        ∑' value, Pr[= value | sampler] * cost index value := by
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices hindex ih =>
      simp only [Finset.sum_insert hindex, mul_add, ENNReal.tsum_add, ih]

/-- Mapping each coordinate by its own deterministic function commutes with a finite
independent product. -/
theorem map_fin_mOfFn {alpha beta : Type} (count : ℕ)
    (samplers : Fin count → ProbComp alpha)
    (transform : Fin count → alpha → beta) :
    (fun values index => transform index (values index)) <$> Fin.mOfFn count samplers =
      Fin.mOfFn count (fun index => transform index <$> samplers index) := by
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
        fun rest index => transform index.succ (rest index)
      let addHead : (Fin count → beta) → (Fin (count + 1) → beta) :=
        fun rest => @Fin.cons count (fun _ : Fin (count + 1) => beta)
          (transform 0 head) rest
      have hcons (rest : Fin count → alpha) :
          (fun index => transform index
            (@Fin.cons count (fun _ : Fin (count + 1) => alpha) head rest index)) =
            addHead (tailTransform rest) := by
        funext index
        refine Fin.cases ?_ (fun tailIndex => ?_) index
        · simp [addHead]
        · simp [addHead, tailTransform]
      calc
        (do
          let rest ← Fin.mOfFn count (fun index => samplers index.succ)
          pure (fun index => transform index
            (@Fin.cons count (fun _ : Fin (count + 1) => alpha)
              head rest index))) =
            (do
              let rest ← Fin.mOfFn count (fun index => samplers index.succ)
              pure (addHead (tailTransform rest))) := by
                apply bind_congr
                intro rest
                rw [hcons]
        _ = addHead <$> (tailTransform <$>
              Fin.mOfFn count (fun index => samplers index.succ)) := by
            simp [map_eq_bind_pure_comp, bind_assoc]
        _ = addHead <$>
              Fin.mOfFn count (fun index =>
                transform index.succ <$> samplers index.succ) := by
            rw [ih (fun index => samplers index.succ)
              (fun index => transform index.succ)]
        _ = (do
              let rest ← Fin.mOfFn count
                (fun index => samplers index.succ >>=
                  pure ∘ transform index.succ)
              pure (Fin.cons (transform 0 head) rest)) := by
            simp [addHead, map_eq_bind_pure_comp]

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

/-- Total variation between two finite independent products is at most the sum of the
coordinatewise distances.  This is the finite-product (hybrid) inequality, stated for
possibly non-identical coordinate samplers. -/
theorem tvDist_fin_mOfFn_le_sum {alpha : Type} [Finite alpha] (count : ℕ)
    (left right : Fin count → ProbComp alpha) :
    tvDist (Fin.mOfFn count left) (Fin.mOfFn count right) ≤
      ∑ index, tvDist (left index) (right index) := by
  classical
  induction count with
  | zero =>
      simp [Fin.mOfFn, tvDist_self]
  | succ count ih =>
      let leftTail : ProbComp (Fin count → alpha) :=
        Fin.mOfFn count fun index => left index.succ
      let rightTail : ProbComp (Fin count → alpha) :=
        Fin.mOfFn count fun index => right index.succ
      let middle : ProbComp (Fin (count + 1) → alpha) := do
        let head ← left 0
        let tail ← rightTail
        pure (Fin.cons head tail)
      have htail : tvDist leftTail rightTail ≤
          ∑ index : Fin count, tvDist (left index.succ) (right index.succ) := by
        exact ih (fun index => left index.succ) (fun index => right index.succ)
      have hsameHead :
          tvDist
              (do
                let head ← left 0
                let tail ← leftTail
                pure (Fin.cons head tail))
              middle ≤
            ∑ index : Fin count,
              tvDist (left index.succ) (right index.succ) := by
        unfold middle
        simpa only [map_eq_bind_pure_comp, Function.comp_def] using
          (tvDist_bind_left_le_const' (m := ProbComp) (α := alpha)
            (β := Fin (count + 1) → alpha) (left 0)
            (fun head =>
              (fun tail : Fin count → alpha => Fin.cons head tail) <$> leftTail)
            (fun head =>
              (fun tail : Fin count → alpha => Fin.cons head tail) <$> rightTail)
            (∑ index : Fin count,
              tvDist (left index.succ) (right index.succ))
            (fun head =>
              (tvDist_map_le (m := ProbComp) (α := Fin count → alpha)
                (β := Fin (count + 1) → alpha)
                (fun tail : Fin count → alpha => Fin.cons head tail)
                leftTail rightTail).trans htail))
      have hsameTail :
          tvDist middle
              (do
                let head ← right 0
                let tail ← rightTail
                pure (Fin.cons head tail)) ≤
              tvDist (left 0) (right 0) := by
        unfold middle
        simpa only [map_eq_bind_pure_comp, Function.comp_def] using
          (tvDist_bind_right_le (m := ProbComp) (α := alpha)
            (β := Fin (count + 1) → alpha)
            (fun head =>
              (fun tail : Fin count → alpha => Fin.cons head tail) <$> rightTail)
            (left 0) (right 0))
      have hsum :
          (∑ index : Fin (count + 1), tvDist (left index) (right index)) =
            (∑ index : Fin count,
                tvDist (left index.succ) (right index.succ)) +
              tvDist (left 0) (right 0) := by
        rw [Fin.sum_univ_succ, add_comm]
      simp only [Fin.mOfFn]
      rw [hsum]
      exact (tvDist_triangle _ middle _).trans
        (add_le_add hsameHead hsameTail)

/-- ENNReal-valued convexity for a shared bind, retaining the exact average of the conditional
TV distances. -/
theorem ofReal_tvDist_bind_left_le_expectation {alpha beta : Type}
    (sampler : ProbComp alpha) (left right : alpha → ProbComp beta) :
    ENNReal.ofReal (tvDist (sampler >>= left) (sampler >>= right)) ≤
      ∑' value,
        Pr[= value | sampler] * ENNReal.ofReal (tvDist (left value) (right value)) := by
  have hprob_ne_top : ∀ value : alpha, Pr[= value | sampler] ≠ ⊤ := fun _ =>
    ne_top_of_le_ne_top ENNReal.one_ne_top probOutput_le_one
  have hprob_summable : Summable (fun value : alpha => Pr[= value | sampler].toReal) :=
    ENNReal.summable_toReal (by
      rw [tsum_probOutput_of_liftM_PMF]
      exact ENNReal.one_ne_top)
  have hsummand_nonneg : ∀ value : alpha,
      0 ≤ Pr[= value | sampler].toReal * tvDist (left value) (right value) :=
    fun _ => mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _)
  have hsummand_summable : Summable
      (fun value : alpha =>
        Pr[= value | sampler].toReal * tvDist (left value) (right value)) :=
    Summable.of_nonneg_of_le hsummand_nonneg
      (fun _ => mul_le_of_le_one_right ENNReal.toReal_nonneg (tvDist_le_one _ _))
      hprob_summable
  have hofRealSum :
      ENNReal.ofReal
          (∑' value : alpha,
            Pr[= value | sampler].toReal * tvDist (left value) (right value)) =
        ∑' value : alpha,
          Pr[= value | sampler] *
            ENNReal.ofReal (tvDist (left value) (right value)) := by
    rw [ENNReal.ofReal_tsum_of_nonneg hsummand_nonneg hsummand_summable]
    apply tsum_congr
    intro value
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (hprob_ne_top value)]
  exact (ENNReal.ofReal_le_ofReal (tvDist_bind_left_le sampler left right)).trans_eq
    hofRealSum

/-- TV cost of translating a sampler by a fixed additive shift. -/
noncomputable def addShiftDistance {R : Type} [Add R]
    (sampler : ProbComp R) (shift : R) : ℝ :=
  tvDist ((fun value => shift + value) <$> sampler) sampler

@[simp]
theorem addShiftDistance_zero {R : Type} [AddGroup R]
    (sampler : ProbComp R) : addShiftDistance sampler 0 = 0 := by
  simp [addShiftDistance, tvDist_self]

/-- Translation costs are subadditive.  The proof is the TV triangle inequality together
with data processing under a further translation; it does not require a norm or a tail bound. -/
theorem addShiftDistance_add_le {R : Type} [AddCommGroup R]
    (sampler : ProbComp R) (first second : R) :
    addShiftDistance sampler (first + second) ≤
      addShiftDistance sampler first + addShiftDistance sampler second := by
  let firstShifted : ProbComp R := (fun value => first + value) <$> sampler
  have htranslate :
      tvDist
          ((fun value => first + second + value) <$> sampler)
          firstShifted ≤ addShiftDistance sampler second := by
    have hdata := tvDist_map_le (m := ProbComp) (α := R) (β := R)
      (fun value => first + value)
      ((fun value => second + value) <$> sampler) sampler
    simpa only [Functor.map_map, Function.comp_apply, add_assoc,
      firstShifted, addShiftDistance] using hdata
  calc
    tvDist ((fun value => first + second + value) <$> sampler) sampler ≤
        tvDist ((fun value => first + second + value) <$> sampler) firstShifted +
          tvDist firstShifted sampler := tvDist_triangle _ firstShifted _
    _ ≤ addShiftDistance sampler second + addShiftDistance sampler first :=
      add_le_add htranslate le_rfl
    _ = addShiftDistance sampler first + addShiftDistance sampler second :=
      add_comm _ _

/-- A finite sum of shifts costs at most the sum of the individual translation costs. -/
theorem addShiftDistance_sum_le_sum {index R : Type}
    [DecidableEq index] [AddCommGroup R] (sampler : ProbComp R)
    (indices : Finset index) (shift : index → R) :
    addShiftDistance sampler (∑ index ∈ indices, shift index) ≤
      ∑ index ∈ indices, addShiftDistance sampler (shift index) := by
  induction indices using Finset.induction_on with
  | empty => simp
  | @insert index indices hindex ih =>
      simp only [Finset.sum_insert hindex]
      exact (addShiftDistance_add_le sampler (shift index)
        (∑ item ∈ indices, shift item)).trans (add_le_add le_rfl ih)

/-- Translating an independent vector costs at most the sum of its scalar translation costs. -/
theorem tvDist_add_fin_mOfFn_le_sum {R : Type} [Finite R] [Add R]
    (count : ℕ) (sampler : ProbComp R) (shift : Fin count → R) :
    tvDist
        ((fun values index => shift index + values index) <$>
          Fin.mOfFn count (fun _ => sampler))
        (Fin.mOfFn count fun _ => sampler) ≤
      ∑ index, addShiftDistance sampler (shift index) := by
  rw [map_fin_mOfFn count (fun _ => sampler)
    (fun index value => shift index + value)]
  exact tvDist_fin_mOfFn_le_sum count
    (fun index => (fun value => shift index + value) <$> sampler)
    (fun _ => sampler)

end FormalProof4FHE.FiniteProduct
