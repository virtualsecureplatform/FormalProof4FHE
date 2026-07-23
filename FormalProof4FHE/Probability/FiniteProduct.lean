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

/-- Sampling two finite types independently agrees with the canonical uniform sampler on their
product.  Stating this at the level of evaluation distributions makes the result independent of
which discoverable `SampleableType` instance supplies the product sampler. -/
theorem evalDist_independent_uniform_product {first second : Type}
    [Fintype first] [SampleableType first]
    [Fintype second] [SampleableType second] :
    𝒟[do
      let left ← $ᵗ first
      let right ← $ᵗ second
      return (left, right)] =
      𝒟[$ᵗ (first × second)] := by
  rw [show (do
      let left ← $ᵗ first
      let right ← $ᵗ second
      return (left, right)) =
      Prod.mk <$> ($ᵗ first) <*> ($ᵗ second) by simp [monad_norm]]
  apply evalDist_ext
  intro output
  simp only [probOutput_seq_map_prod_mk_eq_mul, probOutput_uniformSample,
    Fintype.card_prod, Nat.cast_mul]
  rw [ENNReal.mul_inv] <;> simp

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

/-- Coordinatewise distributional equality lifts to an independently sampled finite product. -/
theorem evalDist_fin_mOfFn_congr {alpha : Type} [Finite alpha] (count : ℕ)
    (left right : Fin count → ProbComp alpha)
    (h : ∀ index, evalDist (left index) = evalDist (right index)) :
    evalDist (Fin.mOfFn count left) = evalDist (Fin.mOfFn count right) := by
  apply evalDist_ext
  intro values
  simp only [probOutput_fin_mOfFn]
  apply Finset.prod_congr rfl
  intro index _hindex
  exact evalDist_ext_iff.mp (h index) (values index)

/-- Sampling a finite input tape first and then independently processing every coordinate has
the same output law as sampling and processing each coordinate consecutively.  This is the
finite-product deferred-sampling rule used to turn repeated oracle access into an explicit
finite challenge. -/
theorem evalDist_presample_fin_mOfFn {alpha beta : Type} [Finite alpha] [Finite beta]
    (count : ℕ)
    (source : Fin count → ProbComp alpha)
    (process : Fin count → alpha → ProbComp beta) :
    evalDist (do
      let inputs ← Fin.mOfFn count source
      Fin.mOfFn count fun index => process index (inputs index)) =
      evalDist (Fin.mOfFn count fun index => do
        let input ← source index
        process index input) := by
  classical
  letI : Fintype alpha := Fintype.ofFinite alpha
  letI : Fintype beta := Fintype.ofFinite beta
  apply evalDist_ext
  intro outputs
  simp only [probOutput_bind_eq_tsum, probOutput_fin_mOfFn, tsum_fintype]
  rw [Fintype.prod_sum]
  simp only [Finset.prod_mul_distrib]

/-- A finite product of deterministic coordinate samplers is the deterministic function formed
from those coordinates. -/
theorem evalDist_fin_mOfFn_pure {alpha : Type} [Finite alpha]
    (count : ℕ) (values : Fin count → alpha) :
    evalDist
        (Fin.mOfFn count
          (fun index ↦ pure (values index) : Fin count → ProbComp alpha)) =
      evalDist (pure values : ProbComp (Fin count → alpha)) := by
  classical
  letI : DecidableEq alpha := Classical.decEq alpha
  apply evalDist_ext
  intro output
  rw [probOutput_fin_mOfFn]
  simp only [probOutput_pure]
  by_cases h : output = values
  · subst output
    simp
  · rw [if_neg h]
    obtain ⟨index, hindex⟩ := Function.ne_iff.mp h
    rw [Finset.prod_eq_zero (Finset.mem_univ index)]
    simp [hindex]

/-- Sampling scalar sums independently in every coordinate is equivalent to sampling the two
complete independent vectors first and adding them coordinatewise. -/
theorem evalDist_sampleIID_add_convolution
    {alpha : Type} [Finite alpha] [Add alpha]
    (count : ℕ) (left right : ProbComp alpha) :
    evalDist
        (ProbComp.sampleIID count (do
          let leftValue ← left
          let rightValue ← right
          return leftValue + rightValue)) =
      evalDist (do
        let leftValues ← ProbComp.sampleIID count left
        let rightValues ← ProbComp.sampleIID count right
        return fun index ↦ leftValues index + rightValues index) := by
  unfold ProbComp.sampleIID
  let process : Fin count → alpha → ProbComp alpha := fun _index leftValue ↦ do
    let rightValue ← right
    return leftValue + rightValue
  have hLeft := evalDist_presample_fin_mOfFn
    count (fun _index : Fin count ↦ left) process
  have hRight (leftValues : Fin count → alpha) :=
    evalDist_presample_fin_mOfFn
      count (fun _index : Fin count ↦ right)
      (fun index rightValue ↦
        (pure (leftValues index + rightValue) : ProbComp alpha))
  symm
  calc
    evalDist (do
        let leftValues ← Fin.mOfFn count (fun _index : Fin count ↦ left)
        let rightValues ← Fin.mOfFn count (fun _index : Fin count ↦ right)
        return fun index ↦ leftValues index + rightValues index) =
      evalDist (do
        let leftValues ← Fin.mOfFn count (fun _index : Fin count ↦ left)
        Fin.mOfFn count (fun index ↦ do
          let rightValue ← right
          return leftValues index + rightValue)) := by
      apply evalDist_bind_congr'
      intro leftValues
      rw [← hRight leftValues]
      apply evalDist_bind_congr'
      intro rightValues
      exact (evalDist_fin_mOfFn_pure count
        (fun index ↦ leftValues index + rightValues index)).symm
    _ = evalDist (Fin.mOfFn count (fun index ↦ do
          let leftValue ← left
          process index leftValue)) := hLeft
    _ = evalDist (Fin.mOfFn count (fun _index ↦ do
          let leftValue ← left
          let rightValue ← right
          return leftValue + rightValue)) := by
      rfl

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

/-- Coordinatewise support membership for an independent finite product. -/
theorem mem_support_fin_mOfFn_apply {alpha : Type} (count : ℕ)
    (samplers : Fin count → ProbComp alpha) (values : Fin count → alpha)
    (hvalues : values ∈ support (Fin.mOfFn count samplers)) (coordinate : Fin count) :
    values coordinate ∈ support (samplers coordinate) := by
  induction count with
  | zero => exact coordinate.elim0
  | succ count ih =>
      rw [Fin.mOfFn, mem_support_bind_iff] at hvalues
      obtain ⟨head, hhead, hvalues⟩ := hvalues
      rw [mem_support_bind_iff] at hvalues
      obtain ⟨tail, htail, hvalues⟩ := hvalues
      simp only [support_pure, Set.mem_singleton_iff] at hvalues
      subst values
      refine Fin.cases ?_ (fun index => ?_) coordinate
      · simpa using hhead
      · rw [Fin.cons_succ]
        exact ih (fun index => samplers index.succ) tail htail index

/-- A finite independent product of never-failing coordinate samplers never fails. -/
theorem probFailure_fin_mOfFn_eq_zero {alpha : Type} (count : ℕ)
    (samplers : Fin count → ProbComp alpha)
    (hSamplers : ∀ index, Pr[⊥ | samplers index] = 0) :
    Pr[⊥ | Fin.mOfFn count samplers] = 0 := by
  induction count with
  | zero => simp [Fin.mOfFn]
  | succ count ih =>
      simp only [Fin.mOfFn]
      letI : NeverFail (samplers 0) :=
        NeverFail.of_probFailure_eq_zero _ (hSamplers 0)
      have hTail : Pr[⊥ | Fin.mOfFn count (fun index => samplers index.succ)] = 0 :=
        ih (fun index => samplers index.succ) (fun index => hSamplers index.succ)
      letI : NeverFail (Fin.mOfFn count (fun index => samplers index.succ)) :=
        NeverFail.of_probFailure_eq_zero _ hTail
      have hAll : NeverFail (do
          let head ← samplers 0
          let tail ← Fin.mOfFn count (fun index => samplers index.succ)
          pure (Fin.cons (α := fun _ => alpha) head tail)) := by
        apply NeverFail.bind_of_forall
      exact hAll.probFailure_eq_zero

/-- Two distinct coordinates of a never-failing finite independent product may be sampled
explicitly and independently before any continuation that uses only those coordinates. -/
theorem evalDist_bind_fin_mOfFn_two_coordinates
    {alpha beta : Type} [Fintype alpha] [DecidableEq alpha]
    (count : ℕ) (samplers : Fin count → ProbComp alpha)
    (first second : Fin count) (hne : first ≠ second)
    (hSamplers : ∀ index, Pr[⊥ | samplers index] = 0)
    (finish : alpha → alpha → ProbComp beta) :
    evalDist (Fin.mOfFn count samplers >>= fun values =>
        finish (values first) (values second)) =
      evalDist (samplers first >>= fun firstValue =>
        samplers second >>= fun secondValue =>
          finish firstValue secondValue) := by
  let firstFixed := fun (firstValue : alpha) (index : Fin count) =>
    if index = first then pure firstValue else samplers index
  let bothFixed := fun (firstValue secondValue : alpha) (index : Fin count) =>
    if index = second then pure secondValue else firstFixed firstValue index
  let continuation := fun (values : Fin count → alpha) =>
    finish (values first) (values second)
  have hFirstPull :
      evalDist (samplers first >>= fun firstValue =>
          Fin.mOfFn count (firstFixed firstValue)) =
        evalDist (Fin.mOfFn count samplers) := by
    simpa only [firstFixed] using evalDist_pull_coordinate count samplers first
  calc
    _ = evalDist ((samplers first >>= fun firstValue =>
          Fin.mOfFn count (firstFixed firstValue)) >>= continuation) := by
      rw [evalDist_bind, evalDist_bind, hFirstPull]
    _ = evalDist (samplers first >>= fun firstValue =>
          Fin.mOfFn count (firstFixed firstValue) >>= continuation) := by
      simp only [bind_assoc]
    _ = evalDist (samplers first >>= fun firstValue =>
          samplers second >>= fun secondValue =>
            Fin.mOfFn count (bothFixed firstValue secondValue) >>= continuation) := by
      refine evalDist_bind_congr' (samplers first) fun firstValue => ?_
      have hSecondPull :
          evalDist (samplers second >>= fun secondValue =>
              Fin.mOfFn count (bothFixed firstValue secondValue)) =
            evalDist (Fin.mOfFn count (firstFixed firstValue)) := by
        simpa only [firstFixed, bothFixed, if_neg (Ne.symm hne)] using
          evalDist_pull_coordinate count (firstFixed firstValue) second
      calc
        _ = evalDist ((samplers second >>= fun secondValue =>
            Fin.mOfFn count (bothFixed firstValue secondValue)) >>= continuation) := by
          rw [evalDist_bind, evalDist_bind, hSecondPull]
        _ = _ := by simp only [bind_assoc]
    _ = _ := by
      refine evalDist_bind_congr' (samplers first) fun firstValue => ?_
      refine evalDist_bind_congr' (samplers second) fun secondValue => ?_
      let remaining := Fin.mOfFn count (bothFixed firstValue secondValue)
      have hContinuation :
          remaining >>= continuation = remaining >>= fun _ => finish firstValue secondValue := by
        apply OracleComp.bind_congr_of_forall_mem_support
        intro values hvalues
        have hFirstSupport := mem_support_fin_mOfFn_apply count
          (bothFixed firstValue secondValue) values hvalues first
        have hSecondSupport := mem_support_fin_mOfFn_apply count
          (bothFixed firstValue secondValue) values hvalues second
        have hFirst : values first = firstValue := by
          rw [show bothFixed firstValue secondValue first = pure firstValue by
            simp [bothFixed, firstFixed, hne]] at hFirstSupport
          simpa only [support_pure, Set.mem_singleton_iff] using hFirstSupport
        have hSecond : values second = secondValue := by
          rw [show bothFixed firstValue secondValue second = pure secondValue by
            simp [bothFixed]] at hSecondSupport
          simpa only [support_pure, Set.mem_singleton_iff] using hSecondSupport
        simp only [continuation, hFirst, hSecond]
      rw [hContinuation]
      apply evalDist_ext
      intro output
      rw [probOutput_bind_const]
      have hRemaining : Pr[⊥ | remaining] = 0 := by
        apply probFailure_fin_mOfFn_eq_zero
        intro index
        by_cases hSecond : index = second
        · simp [bothFixed, hSecond]
        · by_cases hFirst : index = first
          · simp [bothFixed, firstFixed, hFirst]
          · rw [show bothFixed firstValue secondValue index = samplers index by
              simp [bothFixed, firstFixed, hSecond, hFirst]]
            exact hSamplers index
      rw [hRemaining]
      simp

/-- Pull one coordinate in front of a finite product while retaining the complete table.  A
continuation may use both the explicit pulled value and all remaining coordinates; the fixed
coordinate in the retained table is proved equal to that value support-wise. -/
theorem evalDist_bind_fin_mOfFn_pull_coordinate
    {alpha beta : Type} [Fintype alpha] [DecidableEq alpha]
    (count : ℕ) (samplers : Fin count → ProbComp alpha)
    (coordinate : Fin count)
    (finish : alpha → (Fin count → alpha) → ProbComp beta) :
    evalDist (Fin.mOfFn count samplers >>= fun values =>
        finish (values coordinate) values) =
      evalDist (samplers coordinate >>= fun value =>
        Fin.mOfFn count
          (fun index => if index = coordinate then pure value else samplers index) >>= fun values =>
            finish value values) := by
  let fixed := fun (value : alpha) (index : Fin count) =>
    if index = coordinate then pure value else samplers index
  let continuation := fun (values : Fin count → alpha) =>
    finish (values coordinate) values
  have hPull :
      evalDist (samplers coordinate >>= fun value => Fin.mOfFn count (fixed value)) =
        evalDist (Fin.mOfFn count samplers) := by
    simpa only [fixed] using evalDist_pull_coordinate count samplers coordinate
  calc
    _ = evalDist ((samplers coordinate >>= fun value =>
          Fin.mOfFn count (fixed value)) >>= continuation) := by
      rw [evalDist_bind, evalDist_bind, hPull]
    _ = evalDist (samplers coordinate >>= fun value =>
          Fin.mOfFn count (fixed value) >>= continuation) := by
      simp only [bind_assoc]
    _ = evalDist (samplers coordinate >>= fun value =>
          Fin.mOfFn count (fixed value) >>= fun values => finish value values) := by
      refine evalDist_bind_congr' (samplers coordinate) fun value => ?_
      apply congrArg evalDist
      apply OracleComp.bind_congr_of_forall_mem_support
      intro values hvalues
      have hCoordinateSupport := mem_support_fin_mOfFn_apply count
        (fixed value) values hvalues coordinate
      have hCoordinate : values coordinate = value := by
        rw [show fixed value coordinate = pure value by simp [fixed]] at hCoordinateSupport
        simpa only [support_pure, Set.mem_singleton_iff] using hCoordinateSupport
      simp only [continuation, hCoordinate]
    _ = _ := by rfl

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

/-- An event depending on one coordinate of an independent finite product has exactly the
probability of the corresponding event under that coordinate's sampler. -/
theorem probEvent_fin_mOfFn_apply {alpha : Type} (count : ℕ)
    (samplers : Fin count → ProbComp alpha) (coordinate : Fin count)
    (event : alpha → Prop) :
    Pr[(fun values => event (values coordinate)) | Fin.mOfFn count samplers] =
      Pr[event | samplers coordinate] := by
  classical
  rw [probEvent_eq_tsum_ite, probEvent_eq_tsum_ite]
  calc
    (∑' values, if event (values coordinate) then
        Pr[= values | Fin.mOfFn count samplers] else 0) =
        ∑' values, Pr[= values | Fin.mOfFn count samplers] *
          (if event (values coordinate) then 1 else 0) := by
            refine tsum_congr fun values => ?_
            by_cases hevent : event (values coordinate) <;> simp [hevent]
    _ = ∑' value, Pr[= value | samplers coordinate] *
          (if event value then 1 else 0) :=
      tsum_probOutput_fin_mOfFn_apply_mul count samplers coordinate
        (fun value => if event value then 1 else 0)
    _ = ∑' value, if event value then Pr[= value | samplers coordinate] else 0 := by
      refine tsum_congr fun value => ?_
      by_cases hevent : event value <;> simp [hevent]

/-- An event requiring every coordinate of an independent finite product to satisfy its own
predicate has probability equal to the product of the coordinate probabilities. -/
theorem probEvent_fin_mOfFn_forall {alpha : Type} [Finite alpha] (count : ℕ)
    (samplers : Fin count → ProbComp alpha)
    (events : Fin count → alpha → Prop) :
    Pr[(fun values => ∀ coordinate, events coordinate (values coordinate)) |
        Fin.mOfFn count samplers] =
      ∏ coordinate, Pr[events coordinate | samplers coordinate] := by
  classical
  letI : Fintype alpha := Fintype.ofFinite alpha
  rw [probEvent_eq_tsum_ite, tsum_fintype]
  simp only [probOutput_fin_mOfFn]
  simp_rw [probEvent_eq_tsum_ite, tsum_fintype]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro values _
  by_cases hall : ∀ coordinate, events coordinate (values coordinate)
  · simp [hall]
  · simp only [hall, if_false]
    symm
    rw [Finset.prod_eq_zero_iff]
    obtain ⟨coordinate, hcoordinate⟩ := not_forall.mp hall
    exact ⟨coordinate, Finset.mem_univ _, by simp [hcoordinate]⟩

/-- Mapping a finite independent product through a function of one coordinate has the same
distribution as mapping that coordinate's sampler directly. -/
theorem evalDist_map_fin_mOfFn_apply {alpha beta : Type} (count : ℕ)
    (samplers : Fin count → ProbComp alpha) (coordinate : Fin count)
    (transform : alpha → beta) :
    evalDist ((fun values => transform (values coordinate)) <$> Fin.mOfFn count samplers) =
      evalDist (transform <$> samplers coordinate) := by
  apply evalDist_ext
  intro value
  simp only [probOutput_map]
  exact probEvent_fin_mOfFn_apply count samplers coordinate
    (fun input => transform input = value)

/-- Real-valued expectation obeys the usual map law for nonnegative costs.  The underlying
`ProbComp` identity is stated for `ENNReal`; this wrapper performs the finite-valued `toReal`
conversion once so statistical-distance developments can remain on the real scale. -/
theorem tsum_probOutput_map_toReal_mul {alpha beta : Type}
    (sampler : ProbComp alpha) (transform : alpha → beta) (cost : beta → ℝ)
    (hcost : ∀ value, 0 ≤ cost value) :
    (∑' value, Pr[= value | transform <$> sampler].toReal * cost value) =
      ∑' input, Pr[= input | sampler].toReal * cost (transform input) := by
  have hleftTop : ∀ value : beta,
      Pr[= value | transform <$> sampler] * ENNReal.ofReal (cost value) ≠ ⊤ := by
    intro value
    exact ENNReal.mul_ne_top probOutput_ne_top ENNReal.ofReal_ne_top
  have hrightTop : ∀ input : alpha,
      Pr[= input | sampler] * ENNReal.ofReal (cost (transform input)) ≠ ⊤ := by
    intro input
    exact ENNReal.mul_ne_top probOutput_ne_top ENNReal.ofReal_ne_top
  calc
    _ = (∑' value,
        Pr[= value | transform <$> sampler] * ENNReal.ofReal (cost value)).toReal := by
      rw [ENNReal.tsum_toReal_eq hleftTop]
      exact tsum_congr fun value ↦ by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hcost value)]
    _ = (∑' input,
        Pr[= input | sampler] * ENNReal.ofReal (cost (transform input))).toReal := by
      rw [tsum_probOutput_map_mul]
    _ = _ := by
      rw [ENNReal.tsum_toReal_eq hrightTop]
      exact tsum_congr fun input ↦ by
        rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hcost (transform input))]

/-- Equal evaluation distributions give equal real-valued expectations of the same cost. -/
theorem tsum_probOutput_toReal_mul_congr {alpha : Type}
    {left right : ProbComp alpha} (hdist : evalDist left = evalDist right)
    (cost : alpha → ℝ) :
    (∑' value, Pr[= value | left].toReal * cost value) =
      ∑' value, Pr[= value | right].toReal * cost value := by
  exact tsum_congr fun value ↦ by
    rw [probOutput_congr rfl hdist]

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

/-- Applying an independent deterministic map to every coordinate of a uniform finite function
space costs at most the sum of its one-coordinate uniform distances. -/
theorem tvDist_map_uniform_fun_le_sum {alpha : Type}
    [SampleableType alpha] (count : ℕ)
    (transform : Fin count → alpha → alpha) :
    tvDist
        ((fun values index => transform index (values index)) <$>
          ($ᵗ (Fin count → alpha)))
        ($ᵗ (Fin count → alpha)) ≤
      ∑ index, tvDist (transform index <$> ($ᵗ alpha)) ($ᵗ alpha) := by
  letI : Fintype alpha := Fintype.ofFinite alpha
  let product : ProbComp (Fin count → alpha) :=
    Fin.mOfFn count fun _ => $ᵗ alpha
  let pointwise : (Fin count → alpha) → Fin count → alpha :=
    fun values index => transform index (values index)
  have huniform : evalDist product = evalDist ($ᵗ (Fin count → alpha)) := by
    simpa only [ProbComp.sampleIID, product] using
      (evalDist_sampleIID_uniform (alpha := alpha) count)
  have hmapped : evalDist (pointwise <$> product) =
      evalDist (pointwise <$> ($ᵗ (Fin count → alpha))) :=
    evalDist_map_eq_of_evalDist_eq huniform pointwise
  unfold tvDist
  rw [← hmapped, ← huniform]
  change tvDist (pointwise <$> product) product ≤ _
  rw [show pointwise <$> product =
      Fin.mOfFn count (fun index => transform index <$> ($ᵗ alpha)) by
    simpa only [pointwise, product] using
      (map_fin_mOfFn count (fun _ => ($ᵗ alpha : ProbComp alpha)) transform)]
  exact tvDist_fin_mOfFn_le_sum count
    (fun index => transform index <$> ($ᵗ alpha)) (fun _ => $ᵗ alpha)

/-! ### Multiplicative total-variation bounds

The usual hybrid inequality above is linear and can exceed one.  The following overlap
formulation retains the exact probability-scale saturation of independent products.  It is the
sharp universal product bound when only the coordinatewise TV distances are known.
-/

/-- Common probability mass of two computations.  For total computations this is exactly one
minus their total-variation distance. -/
noncomputable def overlapENN {alpha : Type} (left right : ProbComp alpha) : ENNReal :=
  ∑' value, min Pr[= value | left] Pr[= value | right]

/-- Common mass and total variation are complementary for `ProbComp` computations. -/
theorem overlapENN_add_ofReal_tvDist_eq_one {alpha : Type}
    (left right : ProbComp alpha) :
    overlapENN left right + ENNReal.ofReal (tvDist left right) = 1 := by
  let P : alpha → ENNReal := fun value => Pr[= value | left]
  let Q : alpha → ENNReal := fun value => Pr[= value | right]
  let S : ENNReal := ∑' value, min (P value) (Q value)
  have hP_sum : ∑' value, P value = 1 := by
    exact tsum_probOutput_of_liftM_PMF left
  have hQ_sum : ∑' value, Q value = 1 := by
    exact tsum_probOutput_of_liftM_PMF right
  have hS_le : S ≤ 1 := hP_sum ▸ ENNReal.tsum_le_tsum fun value => min_le_left _ _
  have hS_ne_top : S ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hS_le
  have hleft : S + ∑' value, (P value - Q value) = 1 := by
    rw [← ENNReal.tsum_add, ← hP_sum]
    exact tsum_congr fun value => by
      rw [add_comm, tsub_add_min]
  have hright : S + ∑' value, (Q value - P value) = 1 := by
    rw [← ENNReal.tsum_add, ← hQ_sum]
    exact tsum_congr fun value => by
      rw [min_comm]
      rw [add_comm, tsub_add_min]
  have hleftSub : ∑' value, (P value - Q value) = 1 - S :=
    ENNReal.eq_sub_of_add_eq hS_ne_top (by rwa [add_comm] at hleft)
  have hrightSub : ∑' value, (Q value - P value) = 1 - S :=
    ENNReal.eq_sub_of_add_eq hS_ne_top (by rwa [add_comm] at hright)
  have habsDiff :
      (∑' value, ENNReal.absDiff (P value) (Q value)) = 2 * (1 - S) := by
    simp only [ENNReal.absDiff, ENNReal.tsum_add, hleftSub, hrightSub, two_mul]
  have htv : ENNReal.ofReal (tvDist left right) =
      (∑' value, ENNReal.absDiff (P value) (Q value)) / 2 := by
    rw [tvDist, SPMF.tvDist, PMF.tvDist,
      ENNReal.ofReal_toReal (PMF.etvDist_ne_top _ _), PMF.etvDist,
      tsum_option _ ENNReal.summable]
    have hfailLeft : (evalDist left).toPMF none = 0 := probFailure_eq_zero (mx := left)
    have hfailRight : (evalDist right).toPMF none = 0 := probFailure_eq_zero (mx := right)
    rw [hfailLeft, hfailRight, ENNReal.absDiff_self, zero_add]
    congr 1
  change S + ENNReal.ofReal (tvDist left right) = 1
  rw [htv, habsDiff, mul_comm,
    ENNReal.mul_div_cancel_right (by norm_num) (by simp)]
  exact add_tsub_cancel_of_le hS_le

/-- The product of the coordinate overlaps is no larger than the overlap of the independent
product distributions. -/
theorem prod_overlapENN_le_overlapENN_fin_mOfFn {alpha : Type} [Finite alpha]
    (count : ℕ) (left right : Fin count → ProbComp alpha) :
    ∏ index, overlapENN (left index) (right index) ≤
      overlapENN (Fin.mOfFn count left) (Fin.mOfFn count right) := by
  classical
  letI : Fintype alpha := Fintype.ofFinite alpha
  simp only [overlapENN, tsum_fintype, probOutput_fin_mOfFn]
  rw [Fintype.prod_sum]
  apply Finset.sum_le_sum
  intro values _
  exact Finset.prod_min_le

/-- Multiplicative finite-product TV bound.  Unlike the additive hybrid bound, this expression
never loses the independent-product saturation:
`TV(⊗ Pᵢ, ⊗ Qᵢ) ≤ 1 - ∏ᵢ (1 - TV(Pᵢ,Qᵢ))`. -/
theorem ofReal_tvDist_fin_mOfFn_le_one_sub_prod {alpha : Type} [Finite alpha]
    (count : ℕ) (left right : Fin count → ProbComp alpha) :
    ENNReal.ofReal (tvDist (Fin.mOfFn count left) (Fin.mOfFn count right)) ≤
      1 - ∏ index,
        (1 - ENNReal.ofReal (tvDist (left index) (right index))) := by
  let totalOverlap := overlapENN (Fin.mOfFn count left) (Fin.mOfFn count right)
  have htotalAdd := overlapENN_add_ofReal_tvDist_eq_one
    (Fin.mOfFn count left) (Fin.mOfFn count right)
  have htotalFinite : totalOverlap ≠ ⊤ := by
    exact ne_top_of_le_ne_top ENNReal.one_ne_top
      (calc
        totalOverlap ≤ totalOverlap +
            ENNReal.ofReal
              (tvDist (Fin.mOfFn count left) (Fin.mOfFn count right)) :=
          le_add_right le_rfl
        _ = 1 := htotalAdd)
  have htotal :
      ENNReal.ofReal (tvDist (Fin.mOfFn count left) (Fin.mOfFn count right)) =
        1 - totalOverlap := by
    exact ENNReal.eq_sub_of_add_eq htotalFinite (by rwa [add_comm] at htotalAdd)
  have hcoordinate : ∀ index : Fin count,
      overlapENN (left index) (right index) =
        1 - ENNReal.ofReal (tvDist (left index) (right index)) := by
    intro index
    have hadd := overlapENN_add_ofReal_tvDist_eq_one (left index) (right index)
    exact ENNReal.eq_sub_of_add_eq
      (show ENNReal.ofReal (tvDist (left index) (right index)) ≠ ⊤ by simp)
      hadd
  rw [htotal]
  calc
    1 - totalOverlap ≤
        1 - ∏ index, overlapENN (left index) (right index) :=
      tsub_le_tsub_left
        (prod_overlapENN_le_overlapENN_fin_mOfFn count left right) 1
    _ = 1 - ∏ index,
        (1 - ENNReal.ofReal (tvDist (left index) (right index))) := by
      simp_rw [hcoordinate]

/-- Union bound for the complement of a finite product, in real arithmetic. -/
theorem one_sub_prod_one_sub_le_sum_real {index : Type} [Fintype index]
    (cost : index → ℝ) (hnonneg : ∀ index, 0 ≤ cost index)
    (hle : ∀ index, cost index ≤ 1) :
    1 - ∏ index, (1 - cost index) ≤ ∑ index, cost index := by
  classical
  letI : DecidableEq index := Classical.decEq index
  have hgeneral : ∀ indices : Finset index,
      1 - ∏ index ∈ indices, (1 - cost index) ≤
        ∑ index ∈ indices, cost index := by
    intro indices
    induction indices using Finset.induction_on with
    | empty => simp
    | @insert index indices hindex ih =>
        rw [Finset.prod_insert hindex, Finset.sum_insert hindex]
        have hproduct_le_one :
            ∏ item ∈ indices, (1 - cost item) ≤ 1 :=
          Finset.prod_le_one
            (fun item hitem => sub_nonneg.mpr (hle item))
            (fun item hitem => sub_le_self 1 (hnonneg item))
        calc
          1 - (1 - cost index) * ∏ item ∈ indices, (1 - cost item) =
              (1 - ∏ item ∈ indices, (1 - cost item)) +
                cost index * ∏ item ∈ indices, (1 - cost item) := by ring
          _ ≤ (∑ item ∈ indices, cost item) + cost index := by
            exact add_le_add ih
              (mul_le_of_le_one_right (hnonneg index) hproduct_le_one)
          _ = cost index + ∑ item ∈ indices, cost item := add_comm _ _
  exact hgeneral Finset.univ

/-- Probability-scale union bound `1 - ∏ᵢ(1-dᵢ) ≤ ∑ᵢ dᵢ` for `ENNReal` costs. -/
theorem one_sub_prod_one_sub_le_sum {index : Type} [Fintype index]
    (cost : index → ENNReal) (hle : ∀ index, cost index ≤ 1) :
    1 - ∏ index, (1 - cost index) ≤ ∑ index, cost index := by
  classical
  have hcostFinite : ∀ index, cost index ≠ ⊤ := fun index =>
    ne_top_of_le_ne_top ENNReal.one_ne_top (hle index)
  have hfactorFinite : ∀ index, 1 - cost index ≠ ⊤ := fun _ => by simp
  have hproduct_le_one : ∏ index, (1 - cost index) ≤ 1 :=
    Finset.prod_le_one (fun _ _ => bot_le) (fun index _ => tsub_le_self)
  have hlhsFinite : 1 - ∏ index, (1 - cost index) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top tsub_le_self
  have hrhsFinite : ∑ index, cost index ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun index _ => hcostFinite index
  apply (ENNReal.toReal_le_toReal hlhsFinite hrhsFinite).mp
  rw [ENNReal.toReal_sub_of_le hproduct_le_one ENNReal.one_ne_top,
    ENNReal.toReal_one, ENNReal.toReal_prod, ENNReal.toReal_sum]
  · simp_rw [ENNReal.toReal_sub_of_le (hle _) ENNReal.one_ne_top,
      ENNReal.toReal_one]
    exact one_sub_prod_one_sub_le_sum_real
      (fun index => (cost index).toReal)
      (fun _ => ENNReal.toReal_nonneg)
      (fun index => ENNReal.toReal_mono ENNReal.one_ne_top (hle index))
  · exact fun index _ => hcostFinite index

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

/-- Real-valued convexity for a shared bind, retaining the exact average of the conditional
TV distances. -/
theorem tvDist_bind_left_le_expectation {alpha beta : Type}
    (sampler : ProbComp alpha) (left right : alpha → ProbComp beta) :
    tvDist (sampler >>= left) (sampler >>= right) ≤
      ∑' value,
        Pr[= value | sampler].toReal * tvDist (left value) (right value) := by
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
  have h := ofReal_tvDist_bind_left_le_expectation sampler left right
  rw [← hofRealSum] at h
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top h
  simpa only [ENNReal.toReal_ofReal (tvDist_nonneg _ _),
    ENNReal.toReal_ofReal (tsum_nonneg hsummand_nonneg)] using hreal

/-- Averaging conditional TV bounds expressed by bad events gives the bad probability of the
combined run.  This form is useful when the good conditional maps are exact permutations and
rank failure is allowed on a small random set of public contexts. -/
theorem tvDist_bind_left_le_probEvent_cont {prefixType outputType badOutput : Type}
    (prefixSampler : ProbComp prefixType)
    (left right : prefixType → ProbComp outputType)
    (badRun : prefixType → ProbComp badOutput) (badEvent : badOutput → Prop)
    (hpoint : ∀ prefixValue,
      tvDist (left prefixValue) (right prefixValue) ≤
        Pr[badEvent | badRun prefixValue].toReal) :
    tvDist (prefixSampler >>= left) (prefixSampler >>= right) ≤
      Pr[badEvent | prefixSampler >>= badRun].toReal := by
  have hprobSummable : Summable
      (fun value : prefixType => Pr[= value | prefixSampler].toReal) :=
    ENNReal.summable_toReal
      (ne_top_of_le_ne_top ENNReal.one_ne_top tsum_probOutput_le_one)
  have hlhsSummable : Summable (fun value : prefixType =>
      Pr[= value | prefixSampler].toReal *
        tvDist (left value) (right value)) :=
    hprobSummable.of_nonneg_of_le
      (fun _ => mul_nonneg ENNReal.toReal_nonneg (tvDist_nonneg _ _))
      (fun _ => mul_le_of_le_one_right ENNReal.toReal_nonneg
        (tvDist_le_one _ _))
  have hrhsSummable : Summable (fun value : prefixType =>
      Pr[= value | prefixSampler].toReal * Pr[badEvent | badRun value].toReal) :=
    hprobSummable.of_nonneg_of_le
      (fun _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
      (fun _ => mul_le_of_le_one_right ENNReal.toReal_nonneg
        (ENNReal.toReal_mono ENNReal.one_ne_top probEvent_le_one))
  calc
    tvDist (prefixSampler >>= left) (prefixSampler >>= right) ≤
        ∑' value, Pr[= value | prefixSampler].toReal *
          tvDist (left value) (right value) :=
      tvDist_bind_left_le_expectation prefixSampler left right
    _ ≤ ∑' value, Pr[= value | prefixSampler].toReal *
          Pr[badEvent | badRun value].toReal :=
      Summable.tsum_le_tsum
        (fun value => mul_le_mul_of_nonneg_left (hpoint value)
          ENNReal.toReal_nonneg) hlhsSummable hrhsSummable
    _ = Pr[badEvent | prefixSampler >>= badRun].toReal := by
      rw [probEvent_bind_eq_tsum, ENNReal.tsum_toReal_eq]
      · exact tsum_congr fun value => ENNReal.toReal_mul.symm
      · intro value
        exact ENNReal.mul_ne_top
          (ne_top_of_le_ne_top ENNReal.one_ne_top probOutput_le_one)
          probEvent_ne_top

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

/-- A never-failing sampler on a finite additive group that is close to each of its translates
is close to uniform.  This is the averaging converse to translation invariance: average all
translates over a uniform shift.  The translated mixture is exactly uniform, while the
untranslated mixture is the original sampler. -/
theorem tvDist_uniform_le_of_addShiftDistance_le
    {R : Type} [AddCommGroup R] [Fintype R] [SampleableType R]
    (sampler : ProbComp R) (hsampler : Pr[⊥ | sampler] = 0)
    (bound : ℝ)
    (hshift : ∀ shift : R, addShiftDistance sampler shift ≤ bound) :
    tvDist sampler ($ᵗ R) ≤ bound := by
  let uniform : ProbComp R := $ᵗ R
  let shiftedMixture : ProbComp R := uniform >>= fun shift ↦
    (fun value ↦ shift + value) <$> sampler
  let constantMixture : ProbComp R := uniform >>= fun _shift ↦ sampler
  have hmixture : tvDist shiftedMixture constantMixture ≤ bound := by
    refine tvDist_bind_left_le_const' (m := ProbComp)
      uniform (fun shift ↦ (fun value ↦ shift + value) <$> sampler)
      (fun _shift ↦ sampler) bound ?_
    exact hshift
  have hconstant : evalDist constantMixture = evalDist sampler := by
    unfold constantMixture
    refine evalDist_ext fun output ↦ ?_
    rw [probOutput_bind_const]
    simp [uniform]
  have hshifted : evalDist shiftedMixture = evalDist uniform := by
    calc
      evalDist shiftedMixture =
          evalDist (sampler >>= fun value ↦
            uniform >>= fun shift ↦ pure (shift + value)) := by
        simpa only [shiftedMixture, Functor.map, bind_pure_comp] using
          (evalDist_bind_bind_swap uniform sampler
            (fun shift value ↦ pure (shift + value)))
      _ = evalDist (sampler >>= fun _value ↦ uniform) := by
        refine evalDist_bind_congr' sampler fun value ↦ ?_
        let translation : R ≃ R :=
          { toFun := fun shift ↦ shift + value
            invFun := fun output ↦ output - value
            left_inv := by intro shift; simp
            right_inv := by intro output; simp }
        simpa only [uniform, Functor.map, bind_pure_comp] using
          (evalDist_map_bijective_uniform_cross
            (α := R) (β := R) (fun shift ↦ shift + value) translation.bijective)
      _ = evalDist uniform := by
        refine evalDist_ext fun output ↦ ?_
        rw [probOutput_bind_const, hsampler]
        simp
  have hmixtureEq :
      tvDist shiftedMixture constantMixture = tvDist uniform sampler := by
    unfold tvDist
    rw [hshifted, hconstant]
  rw [hmixtureEq] at hmixture
  simpa only [tvDist_comm, uniform] using hmixture

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

/-- Multiplicative counterpart of `tvDist_add_fin_mOfFn_le_sum`.  It keeps the exact
probability-scale saturation across independent vector coordinates. -/
theorem ofReal_tvDist_add_fin_mOfFn_le_one_sub_prod {R : Type} [Finite R] [Add R]
    (count : ℕ) (sampler : ProbComp R) (shift : Fin count → R) :
    ENNReal.ofReal
        (tvDist
          ((fun values index => shift index + values index) <$>
            Fin.mOfFn count (fun _ => sampler))
          (Fin.mOfFn count fun _ => sampler)) ≤
      1 - ∏ index,
        (1 - ENNReal.ofReal (addShiftDistance sampler (shift index))) := by
  rw [map_fin_mOfFn count (fun _ => sampler)
    (fun index value => shift index + value)]
  exact ofReal_tvDist_fin_mOfFn_le_one_sub_prod count
    (fun index => (fun value => shift index + value) <$> sampler)
    (fun _ => sampler)

end FormalProof4FHE.FiniteProduct
