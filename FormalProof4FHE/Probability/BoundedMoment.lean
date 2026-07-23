/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.FiniteProduct
import FormalProof4FHE.Probability.LeftoverHash

/-!
# Bounded Moments as Total-Variation Tests

This file packages a finite, elementary obstruction used by the small-noise
`RGSW_S(-S)` analysis.  A bounded real observable is a statistical test: the
difference of its expectations under two finite distributions is at most twice
its bound times total variation.  Applying this to a clipped square turns a
second-moment increase caused by an independent hidden residual into an
explicit lower bound on total variation.

The factor two is deliberate.  It follows directly from the `L¹/2` definition
of total variation and avoids imposing a global centering convention on the
observable.  It is immaterial for asymptotic non-negligibility arguments.
-/

open OracleComp
open scoped BigOperators

namespace FormalProof4FHE.BoundedMoment

noncomputable section

/-- Real expectation of an observable on a finite `ProbComp` output type. -/
def expectation {A : Type} [Fintype A]
    (sampler : ProbComp A) (observable : A → ℝ) : ℝ :=
  ∑ value, Pr[= value | sampler].toReal * observable value

/-- Evaluation-distribution equality preserves every finite real expectation. -/
theorem expectation_congr_evalDist {A : Type} [Fintype A]
    {left right : ProbComp A} (hDist : evalDist left = evalDist right)
    (observable : A → ℝ) :
    expectation left observable = expectation right observable := by
  classical
  unfold expectation
  apply Finset.sum_congr rfl
  intro value _
  rw [probOutput_congr rfl hDist]

/-- Expectations are linear in the observable. -/
theorem expectation_add {A : Type} [Fintype A]
    (sampler : ProbComp A) (left right : A → ℝ) :
    expectation sampler (fun value ↦ left value + right value) =
      expectation sampler left + expectation sampler right := by
  classical
  simp only [expectation, mul_add, Finset.sum_add_distrib]

/-- Pull a real scalar through a finite expectation. -/
theorem expectation_const_mul {A : Type} [Fintype A]
    (sampler : ProbComp A) (constant : ℝ) (observable : A → ℝ) :
    expectation sampler (fun value ↦ constant * observable value) =
      constant * expectation sampler observable := by
  classical
  unfold expectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro value _
  ring

/-- A total probabilistic computation has expectation one for the constant-one
observable. -/
theorem expectation_one {A : Type} [Fintype A]
    (sampler : ProbComp A) :
    expectation sampler (fun _ ↦ (1 : ℝ)) = 1 := by
  classical
  unfold expectation
  simp only [mul_one]
  rw [← ENNReal.toReal_sum (fun value _ ↦ probOutput_ne_top),
    sum_probOutput_eq_one (by simp), ENNReal.toReal_one]

/-- Expectation under `pure` evaluates the observable at the returned value. -/
theorem expectation_pure {A : Type} [Fintype A]
    (value : A) (observable : A → ℝ) :
    expectation (pure value : ProbComp A) observable = observable value := by
  classical
  letI : DecidableEq A := Classical.decEq A
  unfold expectation
  rw [Finset.sum_eq_single value]
  · simp only [probOutput_pure_self, ENNReal.toReal_one, one_mul]
  · intro other _ hOther
    rw [probOutput_pure, if_neg hOther, ENNReal.toReal_zero, zero_mul]
  · intro hValue
    exact (hValue (Finset.mem_univ value)).elim

/-- Finite real-valued expectation obeys the bind law. -/
theorem expectation_bind {A B : Type} [Fintype A] [Fintype B]
    (sampler : ProbComp A) (continuation : A → ProbComp B)
    (observable : B → ℝ) :
    expectation (sampler >>= continuation) observable =
      ∑ value, Pr[= value | sampler].toReal *
        expectation (continuation value) observable := by
  classical
  unfold expectation
  simp_rw [probOutput_bind_eq_sum_fintype]
  simp_rw [ENNReal.toReal_sum (fun _ _ ↦
    ENNReal.mul_ne_top probOutput_ne_top probOutput_ne_top)]
  simp_rw [ENNReal.toReal_mul]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro value _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro output _
  ring

/-- Mapping a finite sampler composes its observable inside the expectation. -/
theorem expectation_map {A B : Type} [Fintype A] [Fintype B]
    (sampler : ProbComp A) (transform : A → B) (observable : B → ℝ) :
    expectation (transform <$> sampler) observable =
      expectation sampler (fun value ↦ observable (transform value)) := by
  rw [map_eq_bind_pure_comp, expectation_bind]
  apply Finset.sum_congr rfl
  intro value _
  simp only [Function.comp_apply, expectation_pure]

/-- Observables that agree on the sampler support have the same expectation. -/
theorem expectation_congr_on_support {A : Type} [Fintype A]
    (sampler : ProbComp A) (left right : A → ℝ)
    (hEq : ∀ value, value ∈ support sampler → left value = right value) :
    expectation sampler left = expectation sampler right := by
  classical
  unfold expectation
  apply Finset.sum_congr rfl
  intro value _
  by_cases hValue : value ∈ support sampler
  · rw [hEq value hValue]
  · rw [probOutput_eq_zero_of_not_mem_support hValue,
      ENNReal.toReal_zero, zero_mul, zero_mul]

/-- Expectation of a constant under a total computation. -/
theorem expectation_const {A : Type} [Fintype A]
    (sampler : ProbComp A) (constant : ℝ) :
    expectation sampler (fun _ ↦ constant) = constant := by
  calc
    expectation sampler (fun _ ↦ constant) =
        expectation sampler (fun _ ↦ constant * (1 : ℝ)) := by
      apply congrArg (expectation sampler)
      funext value
      ring
    _ = constant * expectation sampler (fun _ ↦ (1 : ℝ)) :=
      expectation_const_mul sampler constant (fun _ ↦ (1 : ℝ))
    _ = constant := by rw [expectation_one, mul_one]

/-- The first real moment of a finite sampler. -/
def mean {A : Type} [Fintype A]
    (sampler : ProbComp A) (lift : A → ℝ) : ℝ :=
  expectation sampler lift

/-- The second real moment of a finite sampler. -/
def secondMoment {A : Type} [Fintype A]
    (sampler : ProbComp A) (lift : A → ℝ) : ℝ :=
  expectation sampler (fun value ↦ (lift value) ^ 2)

/-- Evaluation-distribution equality preserves the first moment. -/
theorem mean_congr_evalDist {A : Type} [Fintype A]
    {left right : ProbComp A} (hDist : evalDist left = evalDist right)
    (lift : A → ℝ) :
    mean left lift = mean right lift :=
  expectation_congr_evalDist hDist lift

/-- Mean of a mapped sampler. -/
theorem mean_map {A B : Type} [Fintype A] [Fintype B]
    (sampler : ProbComp A) (transform : A → B) (lift : B → ℝ) :
    mean (transform <$> sampler) lift =
      expectation sampler (fun value ↦ lift (transform value)) := by
  exact expectation_map sampler transform lift

/-- Evaluation-distribution equality preserves the second moment. -/
theorem secondMoment_congr_evalDist {A : Type} [Fintype A]
    {left right : ProbComp A} (hDist : evalDist left = evalDist right)
    (lift : A → ℝ) :
    secondMoment left lift = secondMoment right lift :=
  expectation_congr_evalDist hDist (fun value ↦ (lift value) ^ 2)

/-- Second moment of a mapped sampler. -/
theorem secondMoment_map {A B : Type} [Fintype A] [Fintype B]
    (sampler : ProbComp A) (transform : A → B) (lift : B → ℝ) :
    secondMoment (transform <$> sampler) lift =
      expectation sampler (fun value ↦ (lift (transform value)) ^ 2) := by
  exact expectation_map sampler transform (fun value ↦ (lift value) ^ 2)

/-- A finite second moment is nonnegative. -/
theorem secondMoment_nonneg {A : Type} [Fintype A]
    (sampler : ProbComp A) (lift : A → ℝ) :
    0 ≤ secondMoment sampler lift := by
  classical
  unfold secondMoment expectation
  apply Finset.sum_nonneg
  intro value _
  exact mul_nonneg ENNReal.toReal_nonneg (sq_nonneg (lift value))

/-- One supported output with nonzero real lift makes the second moment
strictly positive. -/
theorem secondMoment_pos_of_mem_support_of_ne_zero
    {A : Type} [Fintype A]
    (sampler : ProbComp A) (lift : A → ℝ) (value : A)
    (hValue : value ∈ support sampler) (hLift : lift value ≠ 0) :
    0 < secondMoment sampler lift := by
  classical
  have hProbabilityNe : Pr[= value | sampler] ≠ 0 :=
    (mem_support_iff sampler value).mp hValue
  have hProbabilityPos : 0 < Pr[= value | sampler].toReal :=
    ENNReal.toReal_pos hProbabilityNe probOutput_ne_top
  have hTermPos :
      0 < Pr[= value | sampler].toReal * (lift value) ^ 2 :=
    mul_pos hProbabilityPos (sq_pos_of_ne_zero hLift)
  have hTermLe :
      Pr[= value | sampler].toReal * (lift value) ^ 2 ≤
        ∑ candidate,
          Pr[= candidate | sampler].toReal * (lift candidate) ^ 2 := by
    exact Finset.single_le_sum
      (s := Finset.univ)
      (f := fun candidate ↦
        Pr[= candidate | sampler].toReal * (lift candidate) ^ 2)
      (fun candidate _ ↦
        mul_nonneg ENNReal.toReal_nonneg (sq_nonneg (lift candidate)))
      (Finset.mem_univ value)
  exact hTermPos.trans_le hTermLe

/-- Expectation of a quadratic polynomial in one observable. -/
theorem expectation_quadratic {A : Type} [Fintype A]
    (sampler : ProbComp A) (lift : A → ℝ) (linear constant : ℝ) :
    expectation sampler
        (fun value ↦ (lift value) ^ 2 + linear * lift value + constant) =
      secondMoment sampler lift + linear * mean sampler lift + constant := by
  calc
    expectation sampler
        (fun value ↦ (lift value) ^ 2 + linear * lift value + constant) =
      expectation sampler (fun value ↦ (lift value) ^ 2) +
        expectation sampler (fun value ↦ linear * lift value) +
          expectation sampler (fun _ ↦ constant) := by
      rw [show (fun value ↦ (lift value) ^ 2 + linear * lift value + constant) =
          (fun value ↦ ((lift value) ^ 2 + linear * lift value) + constant) by rfl]
      rw [expectation_add, expectation_add]
    _ = secondMoment sampler lift + linear * mean sampler lift + constant := by
      rw [expectation_const_mul, expectation_const]
      rfl

/-- Add two independent samples. -/
def independentAdd {A : Type} [Add A]
    (left right : ProbComp A) : ProbComp A := do
  let leftValue ← left
  let rightValue ← right
  return leftValue + rightValue

/-- Nested-expectation normal form for an independent sum. -/
theorem expectation_independentAdd {A : Type} [Fintype A] [Add A]
    (left right : ProbComp A) (observable : A → ℝ) :
    expectation (independentAdd left right) observable =
      expectation left (fun leftValue ↦
        expectation right (fun rightValue ↦
          observable (leftValue + rightValue))) := by
  classical
  unfold independentAdd
  rw [expectation_bind]
  apply Finset.sum_congr rfl
  intro leftValue _
  congr 1
  rw [expectation_bind]
  apply Finset.sum_congr rfl
  intro rightValue _
  rw [expectation_pure]

/-- Independent additive samples have additive means whenever the chosen real lift respects
addition on their joint support. -/
theorem mean_independentAdd_eq_add
    {A : Type} [Fintype A] [Add A]
    (left right : ProbComp A) (lift : A → ℝ)
    (hAdd : ∀ leftValue, leftValue ∈ support left →
      ∀ rightValue, rightValue ∈ support right →
        lift (leftValue + rightValue) =
          lift leftValue + lift rightValue) :
    mean (independentAdd left right) lift =
      mean left lift + mean right lift := by
  rw [mean, expectation_independentAdd]
  calc
    expectation left (fun leftValue ↦
        expectation right (fun rightValue ↦
          lift (leftValue + rightValue))) =
      expectation left (fun leftValue ↦
        expectation right (fun rightValue ↦
          lift leftValue + lift rightValue)) := by
      apply expectation_congr_on_support
      intro leftValue hLeft
      apply expectation_congr_on_support
      intro rightValue hRight
      exact hAdd leftValue hLeft rightValue hRight
    _ = expectation left (fun leftValue ↦
        lift leftValue + mean right lift) := by
      apply congrArg (expectation left)
      funext leftValue
      rw [expectation_add, expectation_const]
      rfl
    _ = mean left lift + mean right lift := by
      rw [expectation_add, expectation_const]
      rfl

/-- Independent centered additive samples have additive second moments whenever
the chosen real lift respects addition on their joint support. -/
theorem secondMoment_independentAdd_eq_add
    {A : Type} [Fintype A] [Add A]
    (left right : ProbComp A) (lift : A → ℝ)
    (hAdd : ∀ leftValue, leftValue ∈ support left →
      ∀ rightValue, rightValue ∈ support right →
        lift (leftValue + rightValue) =
          lift leftValue + lift rightValue)
    (hLeftCentered : mean left lift = 0)
    (hRightCentered : mean right lift = 0) :
    secondMoment (independentAdd left right) lift =
      secondMoment left lift + secondMoment right lift := by
  rw [secondMoment, expectation_independentAdd]
  calc
    expectation left (fun leftValue ↦
        expectation right (fun rightValue ↦
          (lift (leftValue + rightValue)) ^ 2)) =
      expectation left (fun leftValue ↦
        expectation right (fun rightValue ↦
          (lift leftValue + lift rightValue) ^ 2)) := by
      apply expectation_congr_on_support
      intro leftValue hLeft
      apply expectation_congr_on_support
      intro rightValue hRight
      rw [hAdd leftValue hLeft rightValue hRight]
    _ = expectation left (fun leftValue ↦
        (lift leftValue) ^ 2 +
          2 * lift leftValue * mean right lift +
          secondMoment right lift) := by
      apply congrArg (expectation left)
      funext leftValue
      have hQuadratic := expectation_quadratic right lift
        (2 * lift leftValue) ((lift leftValue) ^ 2)
      calc
        expectation right (fun rightValue ↦
            (lift leftValue + lift rightValue) ^ 2) =
          expectation right (fun rightValue ↦
            (lift rightValue) ^ 2 +
              (2 * lift leftValue) * lift rightValue +
              (lift leftValue) ^ 2) := by
            apply congrArg (expectation right)
            funext rightValue
            ring
        _ = secondMoment right lift +
            (2 * lift leftValue) * mean right lift +
              (lift leftValue) ^ 2 := hQuadratic
        _ = (lift leftValue) ^ 2 +
            2 * lift leftValue * mean right lift +
              secondMoment right lift := by ring
    _ = secondMoment left lift + secondMoment right lift := by
      have hQuadratic := expectation_quadratic left lift
        (2 * mean right lift) (secondMoment right lift)
      calc
        expectation left (fun leftValue ↦
            (lift leftValue) ^ 2 +
              2 * lift leftValue * mean right lift +
              secondMoment right lift) =
          expectation left (fun leftValue ↦
            (lift leftValue) ^ 2 +
              (2 * mean right lift) * lift leftValue +
              secondMoment right lift) := by
            apply congrArg (expectation left)
            funext leftValue
            ring
        _ = secondMoment left lift +
            (2 * mean right lift) * mean left lift +
              secondMoment right lift := hQuadratic
        _ = secondMoment left lift + secondMoment right lift := by
          rw [hLeftCentered, hRightCentered]
          ring

/-! ## Weighted independent sums -/

/-- Real weighted sum of a finite vector after applying one scalar lift. -/
def weightedSum {A : Type} {count : ℕ}
    (weights : Fin count → ℝ) (lift : A → ℝ)
    (values : Fin count → A) : ℝ :=
  ∑ index, weights index * lift (values index)

/-- Head/tail decomposition of a weighted sum. -/
theorem weightedSum_cons {A : Type} {count : ℕ}
    (weights : Fin (count + 1) → ℝ) (lift : A → ℝ)
    (head : A) (tail : Fin count → A) :
    weightedSum weights lift (Fin.cons head tail) =
      weights 0 * lift head +
        weightedSum (fun index ↦ weights index.succ) lift tail := by
  unfold weightedSum
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- A weighted sum of IID centered finite samples is centered. -/
theorem mean_sampleIID_weightedSum_eq_zero
    {A : Type} [Fintype A]
    (sampler : ProbComp A) (lift : A → ℝ)
    (hCentered : mean sampler lift = 0) :
    ∀ (count : ℕ) (weights : Fin count → ℝ),
      mean (ProbComp.sampleIID count sampler) (weightedSum weights lift) = 0 := by
  intro count
  induction count with
  | zero =>
      intro weights
      simp [ProbComp.sampleIID, Fin.mOfFn, mean, weightedSum,
        expectation_pure]
  | succ count inductionHypothesis =>
      intro weights
      rw [mean]
      unfold ProbComp.sampleIID
      simp only [Fin.mOfFn]
      rw [expectation_bind]
      let tailWeights : Fin count → ℝ := fun index ↦ weights index.succ
      have hInner (head : A) :
          expectation
              (Fin.mOfFn count (fun _ ↦ sampler) >>=
                fun tail ↦ pure (Fin.cons head tail))
              (weightedSum weights lift) = weights 0 * lift head := by
        calc
          expectation
              (Fin.mOfFn count (fun _ ↦ sampler) >>=
                fun tail ↦ pure (Fin.cons head tail))
              (weightedSum weights lift) =
            expectation (Fin.mOfFn count fun _ ↦ sampler)
              (fun tail ↦ weightedSum weights lift (Fin.cons head tail)) := by
                rw [expectation_bind]
                apply Finset.sum_congr rfl
                intro tail _
                rw [expectation_pure]
          _ = expectation (Fin.mOfFn count fun _ ↦ sampler)
              (fun tail ↦
                weights 0 * lift head + weightedSum tailWeights lift tail) := by
                  apply congrArg (expectation (Fin.mOfFn count fun _ ↦ sampler))
                  funext tail
                  exact weightedSum_cons weights lift head tail
          _ = expectation (Fin.mOfFn count fun _ ↦ sampler)
                (fun _ ↦ weights 0 * lift head) +
              expectation (Fin.mOfFn count fun _ ↦ sampler)
                (weightedSum tailWeights lift) :=
                  expectation_add _ _ _
          _ = weights 0 * lift head := by
            rw [expectation_const]
            change weights 0 * lift head +
                mean (ProbComp.sampleIID count sampler)
                  (weightedSum tailWeights lift) = _
            rw [inductionHypothesis tailWeights, add_zero]
      calc
        (∑ head,
            Pr[= head | sampler].toReal *
              expectation
                (Fin.mOfFn count (fun _ ↦ sampler) >>=
                  fun tail ↦ pure (Fin.cons head tail))
                (weightedSum weights lift)) =
          ∑ head,
            Pr[= head | sampler].toReal * (weights 0 * lift head) := by
              apply Finset.sum_congr rfl
              intro head _
              rw [hInner]
        _ = expectation sampler (fun head ↦ weights 0 * lift head) := rfl
        _ = weights 0 * mean sampler lift :=
          expectation_const_mul sampler (weights 0) lift
        _ = 0 := by rw [hCentered, mul_zero]

/-- Exact second moment of a weighted sum of IID centered finite samples. -/
theorem secondMoment_sampleIID_weightedSum_eq
    {A : Type} [Fintype A]
    (sampler : ProbComp A) (lift : A → ℝ)
    (hCentered : mean sampler lift = 0) :
    ∀ (count : ℕ) (weights : Fin count → ℝ),
      secondMoment (ProbComp.sampleIID count sampler)
          (weightedSum weights lift) =
        secondMoment sampler lift * ∑ index, weights index ^ 2 := by
  intro count
  induction count with
  | zero =>
      intro weights
      simp [ProbComp.sampleIID, Fin.mOfFn, secondMoment, weightedSum,
        expectation_pure]
  | succ count inductionHypothesis =>
      intro weights
      rw [secondMoment]
      unfold ProbComp.sampleIID
      simp only [Fin.mOfFn]
      rw [expectation_bind]
      let tailWeights : Fin count → ℝ := fun index ↦ weights index.succ
      have hTailCentered :
          mean (ProbComp.sampleIID count sampler)
              (weightedSum tailWeights lift) = 0 :=
        mean_sampleIID_weightedSum_eq_zero sampler lift hCentered
          count tailWeights
      have hInner (head : A) :
          expectation
              (Fin.mOfFn count (fun _ ↦ sampler) >>=
                fun tail ↦ pure (Fin.cons head tail))
              (fun values ↦ weightedSum weights lift values ^ 2) =
            secondMoment sampler lift *
                ∑ index : Fin count, tailWeights index ^ 2 +
              (weights 0 * lift head) ^ 2 := by
        let headTerm := weights 0 * lift head
        calc
          expectation
              (Fin.mOfFn count (fun _ ↦ sampler) >>=
                fun tail ↦ pure (Fin.cons head tail))
              (fun values ↦ weightedSum weights lift values ^ 2) =
            expectation (Fin.mOfFn count fun _ ↦ sampler)
              (fun tail ↦ weightedSum weights lift (Fin.cons head tail) ^ 2) := by
                rw [expectation_bind]
                apply Finset.sum_congr rfl
                intro tail _
                rw [expectation_pure]
          _ = expectation (Fin.mOfFn count fun _ ↦ sampler)
              (fun tail ↦
                weightedSum tailWeights lift tail ^ 2 +
                  (2 * headTerm) * weightedSum tailWeights lift tail +
                    headTerm ^ 2) := by
                  apply congrArg (expectation (Fin.mOfFn count fun _ ↦ sampler))
                  funext tail
                  rw [weightedSum_cons]
                  change (headTerm + weightedSum tailWeights lift tail) ^ 2 = _
                  ring
          _ = secondMoment
                (ProbComp.sampleIID count sampler)
                (weightedSum tailWeights lift) +
              (2 * headTerm) *
                mean (ProbComp.sampleIID count sampler)
                  (weightedSum tailWeights lift) +
              headTerm ^ 2 :=
                expectation_quadratic _ (weightedSum tailWeights lift)
                  (2 * headTerm) (headTerm ^ 2)
          _ = secondMoment sampler lift *
                ∑ index : Fin count, tailWeights index ^ 2 +
              (weights 0 * lift head) ^ 2 := by
            rw [inductionHypothesis tailWeights, hTailCentered]
            simp only [mul_zero, add_zero, headTerm]
      calc
        (∑ head,
            Pr[= head | sampler].toReal *
              expectation
                (Fin.mOfFn count (fun _ ↦ sampler) >>=
                  fun tail ↦ pure (Fin.cons head tail))
                (fun values ↦ weightedSum weights lift values ^ 2)) =
          ∑ head,
            Pr[= head | sampler].toReal *
              (secondMoment sampler lift *
                  ∑ index : Fin count, tailWeights index ^ 2 +
                (weights 0 * lift head) ^ 2) := by
              apply Finset.sum_congr rfl
              intro head _
              rw [hInner]
        _ = expectation sampler
            (fun head ↦
              secondMoment sampler lift *
                  ∑ index : Fin count, tailWeights index ^ 2 +
                (weights 0 * lift head) ^ 2) := rfl
        _ = expectation sampler
              (fun _ ↦ secondMoment sampler lift *
                ∑ index : Fin count, tailWeights index ^ 2) +
            expectation sampler (fun head ↦ (weights 0 * lift head) ^ 2) :=
              expectation_add _ _ _
        _ = secondMoment sampler lift *
                ∑ index : Fin count, tailWeights index ^ 2 +
            expectation sampler
              (fun head ↦ weights 0 ^ 2 * lift head ^ 2) := by
                rw [expectation_const]
                apply congrArg (fun value ↦
                  secondMoment sampler lift *
                      ∑ index : Fin count, tailWeights index ^ 2 + value)
                apply congrArg (expectation sampler)
                funext head
                ring
        _ = secondMoment sampler lift *
                ∑ index : Fin count, tailWeights index ^ 2 +
            weights 0 ^ 2 * secondMoment sampler lift := by
              rw [expectation_const_mul]
              rfl
        _ = secondMoment sampler lift *
            ∑ index : Fin (count + 1), weights index ^ 2 := by
              rw [Fin.sum_univ_succ]
              change secondMoment sampler lift *
                    ∑ index : Fin count, weights index.succ ^ 2 +
                  weights 0 ^ 2 * secondMoment sampler lift =
                secondMoment sampler lift *
                  (weights 0 ^ 2 +
                    ∑ index : Fin count, weights index.succ ^ 2)
              ring

/-- A uniformly bounded observable cannot separate two finite distributions by
more than twice its bound times total variation. -/
theorem abs_expectation_sub_le_two_mul_bound_mul_tvDist
    {A : Type} [Fintype A]
    (left right : ProbComp A) (observable : A → ℝ) (bound : ℝ)
    (hBound : ∀ value, |observable value| ≤ bound) :
    |expectation left observable - expectation right observable| ≤
      2 * bound * tvDist left right := by
  classical
  unfold expectation
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ value,
        (Pr[= value | left].toReal * observable value -
          Pr[= value | right].toReal * observable value)| =
        |∑ value,
          (Pr[= value | left].toReal -
            Pr[= value | right].toReal) * observable value| := by
      apply congrArg abs
      apply Finset.sum_congr rfl
      intro value _
      ring
    _ ≤ ∑ value,
        |(Pr[= value | left].toReal -
          Pr[= value | right].toReal) * observable value| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ value,
        |Pr[= value | left].toReal -
          Pr[= value | right].toReal| * bound := by
      apply Finset.sum_le_sum
      intro value _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hBound value) (abs_nonneg _)
    _ = 2 * bound * tvDist left right := by
      rw [FormalProof4FHE.LeftoverHash.tvDist_eq_half_sum_abs]
      rw [← Finset.sum_mul]
      ring

/-- The square observable, clipped to zero outside the centered interval
`[-bound, bound]`. -/
def clippedSquare {A : Type} (bound : ℝ) (lift : A → ℝ) (value : A) : ℝ :=
  if |lift value| ≤ bound then (lift value) ^ 2 else 0

/-- A clipped square is globally bounded by `bound²`. -/
theorem abs_clippedSquare_le_sq {A : Type}
    (bound : ℝ) (lift : A → ℝ) (hBoundNonneg : 0 ≤ bound) (value : A) :
    |clippedSquare bound lift value| ≤ bound ^ 2 := by
  classical
  by_cases h : |lift value| ≤ bound
  · rw [clippedSquare, if_pos h, abs_sq]
    rw [← sq_abs]
    exact (sq_le_sq₀ (abs_nonneg _) hBoundNonneg).2 h
  · simp [clippedSquare, h, pow_two_nonneg bound]

/-- On a bounded point, clipping does not change the square observable. -/
theorem clippedSquare_eq_sq_of_abs_le {A : Type}
    (bound : ℝ) (lift : A → ℝ) (value : A)
    (h : |lift value| ≤ bound) :
    clippedSquare bound lift value = (lift value) ^ 2 := by
  simp [clippedSquare, h]

/-- If every supported output is inside the clipping interval, the clipped
second moment is the ordinary second moment. -/
theorem expectation_clippedSquare_eq_secondMoment_of_support
    {A : Type} [Fintype A]
    (sampler : ProbComp A) (bound : ℝ) (lift : A → ℝ)
    (hSupport : ∀ value, value ∈ support sampler →
      |lift value| ≤ bound) :
    expectation sampler (clippedSquare bound lift) =
      secondMoment sampler lift := by
  apply expectation_congr_on_support
  intro value hValue
  exact clippedSquare_eq_sq_of_abs_le bound lift value
    (hSupport value hValue)

/-- A bounded second-moment gap is at most `2 * bound² * TV`. -/
theorem abs_clippedSecondMoment_sub_le
    {A : Type} [Fintype A]
    (left right : ProbComp A) (bound : ℝ) (lift : A → ℝ)
    (hBoundNonneg : 0 ≤ bound) :
    |expectation left (clippedSquare bound lift) -
        expectation right (clippedSquare bound lift)| ≤
      2 * bound ^ 2 * tvDist left right := by
  exact abs_expectation_sub_le_two_mul_bound_mul_tvDist
    left right (clippedSquare bound lift) (bound ^ 2)
      (abs_clippedSquare_le_sq bound lift hBoundNonneg)

/-- Core bounded-no-wrap obstruction.  If an independent centered residual is
added to centered noise, the residual's complete second moment is visible to a
bounded square test.  Hence it is at most `2 * bound²` times the total-variation
distance between shifted and unshifted noise.

The two support hypotheses are exactly the no-wrap/correctness regime: both the
original noise and the final shifted noise must admit the same centered real
lift inside `[-bound, bound]`. -/
theorem secondMoment_le_two_mul_sq_mul_tvDist_independentAdd
    {A : Type} [Fintype A] [Add A]
    (residual noise : ProbComp A) (bound : ℝ) (lift : A → ℝ)
    (hBoundNonneg : 0 ≤ bound)
    (hAdd : ∀ residualValue, residualValue ∈ support residual →
      ∀ noiseValue, noiseValue ∈ support noise →
        lift (residualValue + noiseValue) =
          lift residualValue + lift noiseValue)
    (hResidualCentered : mean residual lift = 0)
    (hNoiseCentered : mean noise lift = 0)
    (hNoiseSupport : ∀ value, value ∈ support noise →
      |lift value| ≤ bound)
    (hShiftedSupport : ∀ value,
      value ∈ support (independentAdd residual noise) →
        |lift value| ≤ bound) :
    secondMoment residual lift ≤
      2 * bound ^ 2 * tvDist (independentAdd residual noise) noise := by
  have hMoment := secondMoment_independentAdd_eq_add
    residual noise lift hAdd hResidualCentered hNoiseCentered
  have hShiftedClip :=
    expectation_clippedSquare_eq_secondMoment_of_support
      (independentAdd residual noise) bound lift hShiftedSupport
  have hNoiseClip :=
    expectation_clippedSquare_eq_secondMoment_of_support
      noise bound lift hNoiseSupport
  have hTV := abs_clippedSecondMoment_sub_le
    (independentAdd residual noise) noise bound lift hBoundNonneg
  calc
    secondMoment residual lift =
        |expectation (independentAdd residual noise)
            (clippedSquare bound lift) -
          expectation noise (clippedSquare bound lift)| := by
      rw [hShiftedClip, hNoiseClip, hMoment]
      rw [show secondMoment residual lift + secondMoment noise lift -
          secondMoment noise lift = secondMoment residual lift by ring]
      exact (abs_of_nonneg (secondMoment_nonneg residual lift)).symm
    _ ≤ 2 * bound ^ 2 *
        tvDist (independentAdd residual noise) noise := hTV

/-- Ratio form of the bounded-no-wrap obstruction. -/
theorem secondMoment_div_two_mul_sq_le_tvDist_independentAdd
    {A : Type} [Fintype A] [Add A]
    (residual noise : ProbComp A) (bound : ℝ) (lift : A → ℝ)
    (hBoundPos : 0 < bound)
    (hAdd : ∀ residualValue, residualValue ∈ support residual →
      ∀ noiseValue, noiseValue ∈ support noise →
        lift (residualValue + noiseValue) =
          lift residualValue + lift noiseValue)
    (hResidualCentered : mean residual lift = 0)
    (hNoiseCentered : mean noise lift = 0)
    (hNoiseSupport : ∀ value, value ∈ support noise →
      |lift value| ≤ bound)
    (hShiftedSupport : ∀ value,
      value ∈ support (independentAdd residual noise) →
        |lift value| ≤ bound) :
    secondMoment residual lift / (2 * bound ^ 2) ≤
      tvDist (independentAdd residual noise) noise := by
  have hDenominator : 0 < (2 * bound ^ 2 : ℝ) := by positivity
  rw [div_le_iff₀ hDenominator]
  have hBase := secondMoment_le_two_mul_sq_mul_tvDist_independentAdd
    residual noise bound lift hBoundPos.le hAdd hResidualCentered
      hNoiseCentered hNoiseSupport hShiftedSupport
  nlinarith [hBase]

end

end FormalProof4FHE.BoundedMoment
