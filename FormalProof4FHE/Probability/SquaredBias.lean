/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.BoundedMoment

/-!
# Squaring a Boolean Distinguishing Bias

This module packages the elementary two-copy reduction used for posterior-secret and
interval-masked LWE.  Given two Boolean computations, it runs two independent copies of each and
turns the product of their signed output differences into a Boolean probability.  The resulting
probability is exactly one half plus one half of the squared signed gap, so cancellation between
different hidden contexts is eliminated.
-/

open OracleComp

namespace FormalProof4FHE.SquaredBias

noncomputable section

/-- Embed a Boolean output into `ℝ` as zero or one. -/
def bitReal (value : Bool) : ℝ := if value then 1 else 0

/-- The signed true-output gap. -/
def signedGap (real ideal : ProbComp Bool) : ℝ :=
  Pr[= true | real].toReal - Pr[= true | ideal].toReal

/-- Convert the product of two sample-level signed differences into a Boolean probability.

If either paired difference is zero, a fair bit is returned.  Otherwise the result is true exactly
when the two differences have the same sign. -/
def combine (real₁ ideal₁ real₂ ideal₂ : Bool) : ProbComp Bool :=
  if real₁ = ideal₁ ∨ real₂ = ideal₂ then
    $ᵗ Bool
  else
    pure (real₁ = real₂)

theorem probOutput_combine_true (real₁ ideal₁ real₂ ideal₂ : Bool) :
    Pr[= true | combine real₁ ideal₁ real₂ ideal₂].toReal =
      (1 + (bitReal real₁ - bitReal ideal₁) *
        (bitReal real₂ - bitReal ideal₂)) / 2 := by
  cases real₁ <;> cases ideal₁ <;> cases real₂ <;> cases ideal₂ <;>
    norm_num [combine, bitReal, probOutput_uniformSample]

theorem expectation_bitReal (sampler : ProbComp Bool) :
    BoundedMoment.expectation sampler bitReal = Pr[= true | sampler].toReal := by
  simp [BoundedMoment.expectation, bitReal]

theorem expectation_bind_nested
    {A B : Type} [Fintype A] [Fintype B]
    (sampler : ProbComp A) (continuation : A → ProbComp B)
    (observable : B → ℝ) :
    BoundedMoment.expectation (sampler >>= continuation) observable =
      BoundedMoment.expectation sampler fun value ↦
        BoundedMoment.expectation (continuation value) observable := by
  rw [BoundedMoment.expectation_bind]
  rfl

theorem expectation_affine
    {A : Type} [Fintype A] (sampler : ProbComp A)
    (constant slope : ℝ) (observable : A → ℝ) :
    BoundedMoment.expectation sampler
        (fun value ↦ constant + slope * observable value) =
      constant + slope * BoundedMoment.expectation sampler observable := by
  rw [BoundedMoment.expectation_add, BoundedMoment.expectation_const,
    BoundedMoment.expectation_const_mul]

/-- Expectations commute with pointwise subtraction. -/
theorem expectation_sub
    {A : Type} [Fintype A] (sampler : ProbComp A) (left right : A → ℝ) :
    BoundedMoment.expectation sampler (fun value ↦ left value - right value) =
      BoundedMoment.expectation sampler left -
        BoundedMoment.expectation sampler right := by
  calc
    BoundedMoment.expectation sampler (fun value ↦ left value - right value) =
        BoundedMoment.expectation sampler
          (fun value ↦ left value + (-1) * right value) := by
      apply congrArg (BoundedMoment.expectation sampler)
      funext value
      ring
    _ = BoundedMoment.expectation sampler left +
          BoundedMoment.expectation sampler (fun value ↦ (-1) * right value) :=
      BoundedMoment.expectation_add sampler left (fun value ↦ (-1) * right value)
    _ = BoundedMoment.expectation sampler left +
          (-1) * BoundedMoment.expectation sampler right := by
      rw [BoundedMoment.expectation_const_mul]
    _ = BoundedMoment.expectation sampler left -
          BoundedMoment.expectation sampler right := by ring

/-- The signed gap after sampling the same hidden context is the mean of the conditional gaps. -/
theorem signedGap_bind
    {Context : Type} [Fintype Context]
    (contexts : ProbComp Context) (real ideal : Context → ProbComp Bool) :
    signedGap (contexts >>= real) (contexts >>= ideal) =
      BoundedMoment.expectation contexts
        (fun context ↦ signedGap (real context) (ideal context)) := by
  unfold signedGap
  rw [← expectation_bitReal, ← expectation_bitReal,
    expectation_bind_nested, expectation_bind_nested, ← expectation_sub]
  apply congrArg (BoundedMoment.expectation contexts)
  funext context
  rw [expectation_bitReal, expectation_bitReal]

/-- One paired real/ideal output. -/
def paired (real ideal : ProbComp Bool) : ProbComp (Bool × Bool) := do
  let realOutput ← real
  let idealOutput ← ideal
  return (realOutput, idealOutput)

/-- The signed sample-level difference of one paired output. -/
def difference (outputs : Bool × Bool) : ℝ :=
  bitReal outputs.1 - bitReal outputs.2

theorem expectation_difference_paired (real ideal : ProbComp Bool) :
    BoundedMoment.expectation (paired real ideal) difference = signedGap real ideal := by
  unfold paired
  rw [expectation_bind_nested]
  apply Eq.trans _ (show
      BoundedMoment.expectation real bitReal -
          BoundedMoment.expectation ideal bitReal = signedGap real ideal by
        rw [expectation_bitReal, expectation_bitReal]
        rfl)
  rw [show (fun realOutput ↦
      BoundedMoment.expectation
        (ideal >>= fun idealOutput ↦ pure (realOutput, idealOutput)) difference) =
      (fun realOutput ↦ bitReal realOutput -
        BoundedMoment.expectation ideal bitReal) by
      funext realOutput
      rw [expectation_bind_nested]
      simp only [BoundedMoment.expectation_pure, difference]
      have h := expectation_affine ideal (bitReal realOutput) (-1) bitReal
      calc
        BoundedMoment.expectation ideal
            (fun idealOutput ↦ bitReal realOutput - bitReal idealOutput) =
          BoundedMoment.expectation ideal
            (fun idealOutput ↦ bitReal realOutput + (-1) * bitReal idealOutput) := by
              apply congrArg (BoundedMoment.expectation ideal)
              funext idealOutput
              ring
        _ = bitReal realOutput + (-1) *
            BoundedMoment.expectation ideal bitReal := h
        _ = bitReal realOutput - BoundedMoment.expectation ideal bitReal := by ring]
  have h := expectation_affine real
    (-BoundedMoment.expectation ideal bitReal) 1 bitReal
  calc
    BoundedMoment.expectation real
        (fun realOutput ↦ bitReal realOutput -
          BoundedMoment.expectation ideal bitReal) =
      BoundedMoment.expectation real
        (fun realOutput ↦ -BoundedMoment.expectation ideal bitReal +
          1 * bitReal realOutput) := by
        apply congrArg (BoundedMoment.expectation real)
        funext realOutput
        ring
    _ = -BoundedMoment.expectation ideal bitReal +
        1 * BoundedMoment.expectation real bitReal := h
    _ = BoundedMoment.expectation real bitReal -
        BoundedMoment.expectation ideal bitReal := by ring

/-- Two independent copies of the real/ideal comparison with the sample-level product test. -/
def experiment (real ideal : ProbComp Bool) : ProbComp Bool := do
  let first ← paired real ideal
  let second ← paired real ideal
  combine first.1 first.2 second.1 second.2

/-- The polarized two-copy experiment.  Its two real/ideal pairs may use different samplers. -/
def crossExperiment (real₁ ideal₁ real₂ ideal₂ : ProbComp Bool) : ProbComp Bool := do
  let first ← paired real₁ ideal₁
  let second ← paired real₂ ideal₂
  combine first.1 first.2 second.1 second.2

/-- The polarized experiment realizes the product of the two signed gaps. -/
theorem probOutput_crossExperiment_true
    (real₁ ideal₁ real₂ ideal₂ : ProbComp Bool) :
    Pr[= true | crossExperiment real₁ ideal₁ real₂ ideal₂].toReal =
      (1 + signedGap real₁ ideal₁ * signedGap real₂ ideal₂) / 2 := by
  rw [← expectation_bitReal]
  unfold crossExperiment
  rw [expectation_bind_nested]
  have hInner (first : Bool × Bool) :
      BoundedMoment.expectation
          (paired real₂ ideal₂ >>= fun second ↦
            combine first.1 first.2 second.1 second.2) bitReal =
        (1 + difference first * signedGap real₂ ideal₂) / 2 := by
    rw [expectation_bind_nested]
    simp_rw [expectation_bitReal, probOutput_combine_true]
    have h := expectation_affine (paired real₂ ideal₂) (1 / 2)
      (difference first / 2) difference
    rw [expectation_difference_paired] at h
    calc
      BoundedMoment.expectation (paired real₂ ideal₂)
          (fun second ↦
            (1 + (bitReal first.1 - bitReal first.2) *
              (bitReal second.1 - bitReal second.2)) / 2) =
        BoundedMoment.expectation (paired real₂ ideal₂)
          (fun second ↦ 1 / 2 + (difference first / 2) * difference second) := by
            apply congrArg (BoundedMoment.expectation (paired real₂ ideal₂))
            funext second
            simp only [difference]
            ring
      _ = 1 / 2 + (difference first / 2) * signedGap real₂ ideal₂ := h
      _ = (1 + difference first * signedGap real₂ ideal₂) / 2 := by ring
  simp_rw [hInner]
  have hOuter := expectation_affine (paired real₁ ideal₁) (1 / 2)
    (signedGap real₂ ideal₂ / 2) difference
  rw [expectation_difference_paired] at hOuter
  calc
    BoundedMoment.expectation (paired real₁ ideal₁)
        (fun value ↦ (1 + difference value * signedGap real₂ ideal₂) / 2) =
      BoundedMoment.expectation (paired real₁ ideal₁)
        (fun value ↦ 1 / 2 +
          (signedGap real₂ ideal₂ / 2) * difference value) := by
        apply congrArg (BoundedMoment.expectation (paired real₁ ideal₁))
        funext value
        ring
    _ = 1 / 2 + (signedGap real₂ ideal₂ / 2) *
        signedGap real₁ ideal₁ := hOuter
    _ = (1 + signedGap real₁ ideal₁ * signedGap real₂ ideal₂) / 2 := by
      ring

/-- The two-copy experiment squares the signed Boolean gap exactly. -/
theorem probOutput_experiment_true (real ideal : ProbComp Bool) :
    Pr[= true | experiment real ideal].toReal =
      (1 + signedGap real ideal ^ 2) / 2 := by
  rw [← expectation_bitReal]
  unfold experiment
  rw [expectation_bind_nested]
  have hInner (first : Bool × Bool) :
      BoundedMoment.expectation
          (paired real ideal >>= fun second ↦
            combine first.1 first.2 second.1 second.2) bitReal =
        (1 + difference first * signedGap real ideal) / 2 := by
    rw [expectation_bind_nested]
    simp_rw [expectation_bitReal, probOutput_combine_true]
    have h := expectation_affine (paired real ideal) (1 / 2)
      (difference first / 2) difference
    rw [expectation_difference_paired] at h
    calc
      BoundedMoment.expectation (paired real ideal)
          (fun second ↦
            (1 + (bitReal first.1 - bitReal first.2) *
              (bitReal second.1 - bitReal second.2)) / 2) =
        BoundedMoment.expectation (paired real ideal)
          (fun second ↦ 1 / 2 + (difference first / 2) * difference second) := by
            apply congrArg (BoundedMoment.expectation (paired real ideal))
            funext second
            simp only [difference]
            ring
      _ = 1 / 2 + (difference first / 2) * signedGap real ideal := h
      _ = (1 + difference first * signedGap real ideal) / 2 := by ring
  simp_rw [hInner]
  have hOuter := expectation_affine (paired real ideal) (1 / 2)
    (signedGap real ideal / 2) difference
  rw [expectation_difference_paired] at hOuter
  calc
    BoundedMoment.expectation (paired real ideal)
        (fun value ↦ (1 + difference value * signedGap real ideal) / 2) =
      BoundedMoment.expectation (paired real ideal)
        (fun value ↦ 1 / 2 +
          (signedGap real ideal / 2) * difference value) := by
        apply congrArg (BoundedMoment.expectation (paired real ideal))
        funext value
        ring
    _ = 1 / 2 + (signedGap real ideal / 2) * signedGap real ideal := hOuter
    _ = (1 + signedGap real ideal ^ 2) / 2 := by ring

/-- With identical inputs the squared-bias experiment is an exact fair coin. -/
theorem probOutput_experiment_self_true (sampler : ProbComp Bool) :
    Pr[= true | experiment sampler sampler].toReal = 1 / 2 := by
  rw [probOutput_experiment_true]
  simp [signedGap]

/-- Square the signed gap after sampling a hidden public context. -/
def contextualExperiment {Context : Type} (contexts : ProbComp Context)
    (real ideal : Context → ProbComp Bool) : ProbComp Bool := do
  let context ← contexts
  experiment (real context) (ideal context)

theorem probOutput_contextualExperiment_true
    {Context : Type} [Fintype Context]
    (contexts : ProbComp Context) (real ideal : Context → ProbComp Bool) :
    Pr[= true | contextualExperiment contexts real ideal].toReal =
      (1 + BoundedMoment.expectation contexts
        (fun context ↦ signedGap (real context) (ideal context) ^ 2)) / 2 := by
  rw [← expectation_bitReal]
  unfold contextualExperiment
  rw [expectation_bind_nested]
  simp_rw [expectation_bitReal, probOutput_experiment_true]
  have h := expectation_affine contexts (1 / 2) (1 / 2)
    (fun context ↦ signedGap (real context) (ideal context) ^ 2)
  calc
    BoundedMoment.expectation contexts
        (fun context ↦ (1 + signedGap (real context) (ideal context) ^ 2) / 2) =
      BoundedMoment.expectation contexts
        (fun context ↦ 1 / 2 +
          (1 / 2) * signedGap (real context) (ideal context) ^ 2) := by
        apply congrArg (BoundedMoment.expectation contexts)
        funext context
        ring
    _ = 1 / 2 + (1 / 2) * BoundedMoment.expectation contexts
        (fun context ↦ signedGap (real context) (ideal context) ^ 2) := h
    _ = (1 + BoundedMoment.expectation contexts
        (fun context ↦ signedGap (real context) (ideal context) ^ 2)) / 2 := by ring

/-- A finite uniform expectation is the corresponding arithmetic mean. -/
theorem expectation_uniform_eq_sum_div
    {A : Type} [Fintype A] [Nonempty A] [SampleableType A]
    (observable : A → ℝ) :
    BoundedMoment.expectation ($ᵗ A) observable =
      (∑ value, observable value) / (Fintype.card A : ℝ) := by
  unfold BoundedMoment.expectation
  simp_rw [probOutput_uniformSample, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [← Finset.mul_sum]
  field_simp

/-- An injective image of a uniform source has squared mean bounded by the ambient uniform second
moment, with the exact cardinality ratio. -/
theorem sq_expectation_uniform_comp_le_card_ratio_secondMoment
    {A B : Type}
    [Fintype A] [Nonempty A] [SampleableType A]
    [Fintype B] [Nonempty B] [SampleableType B]
    (transform : A → B) (hTransform : Function.Injective transform)
    (observable : B → ℝ) :
    BoundedMoment.expectation ($ᵗ A) (fun value ↦ observable (transform value)) ^ 2 ≤
      ((Fintype.card B : ℝ) / (Fintype.card A : ℝ)) *
        BoundedMoment.expectation ($ᵗ B) (fun value ↦ observable value ^ 2) := by
  classical
  letI : DecidableEq B := Classical.decEq B
  rw [expectation_uniform_eq_sum_div, expectation_uniform_eq_sum_div]
  let sumA : ℝ := ∑ value : A, observable (transform value)
  let squareA : ℝ := ∑ value : A, observable (transform value) ^ 2
  let squareB : ℝ := ∑ value : B, observable value ^ 2
  have hCardA : (0 : ℝ) < Fintype.card A := by exact_mod_cast Fintype.card_pos
  have hCardB : (0 : ℝ) < Fintype.card B := by exact_mod_cast Fintype.card_pos
  have hCauchy : sumA ^ 2 ≤ (Fintype.card A : ℝ) * squareA := by
    have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
      (fun _ : A ↦ (1 : ℝ)) (fun value ↦ observable (transform value))
    simpa [sumA, squareA] using h
  have hSquares : squareA ≤ squareB := by
    have hImage :
        (∑ value ∈ Finset.univ.image transform, observable value ^ 2) =
          ∑ value : A, observable (transform value) ^ 2 :=
      Finset.sum_image (f := fun value ↦ observable value ^ 2)
        (fun left _ right _ hEq ↦ hTransform hEq)
    rw [show squareA = ∑ value ∈ Finset.univ.image transform,
        observable value ^ 2 by exact hImage.symm]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ ↦ sq_nonneg _)
  dsimp only [sumA] at hCauchy
  dsimp only [squareA] at hCauchy hSquares
  dsimp only [squareB] at hSquares
  calc
    ((∑ value : A, observable (transform value)) /
        (Fintype.card A : ℝ)) ^ 2 =
      (∑ value : A, observable (transform value)) ^ 2 /
        (Fintype.card A : ℝ) ^ 2 := by ring
    _ ≤ ((Fintype.card A : ℝ) *
        ∑ value : A, observable (transform value) ^ 2) /
          (Fintype.card A : ℝ) ^ 2 := by
      exact div_le_div_of_nonneg_right hCauchy (sq_nonneg _)
    _ ≤ ((Fintype.card A : ℝ) *
        ∑ value : B, observable value ^ 2) /
          (Fintype.card A : ℝ) ^ 2 := by
      gcongr
    _ = ((Fintype.card B : ℝ) / (Fintype.card A : ℝ)) *
        ((∑ value : B, observable value ^ 2) /
          (Fintype.card B : ℝ)) := by
      field_simp

end

end FormalProof4FHE.SquaredBias
