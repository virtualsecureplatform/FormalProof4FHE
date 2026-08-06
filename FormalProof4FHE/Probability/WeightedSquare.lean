/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.BoundedMoment

/-!
# Weighted Squared-Mean Comparison for Finite Samplers

This file proves the finite change-of-measure inequality used by randomized-hint reductions.
For two finite laws `P` and `Q`, with `Q` covering the support of `P`, it defines the exact
second density moment

`C₂(P ∥ Q) = ∑ x, P(x)² / Q(x)`

and proves

`(E_P f)² ≤ C₂(P ∥ Q) * E_Q[f²]`.

Unlike the uniform injective counting lemma, this statement preserves the actual probabilities
of a nonuniform sampler such as centered binomial noise.  The constant is a finite sum and can
therefore be evaluated for concrete finite parameters before any analytic relaxation is chosen.
-/

open OracleComp
open scoped BigOperators

namespace FormalProof4FHE.WeightedSquare

noncomputable section

/-- Real probability mass of a finite computation at one output. -/
def probabilityMass {A : Type} (sampler : ProbComp A) (value : A) : ℝ :=
  Pr[= value | sampler].toReal

theorem probabilityMass_nonneg {A : Type} (sampler : ProbComp A) (value : A) :
    0 ≤ probabilityMass sampler value :=
  ENNReal.toReal_nonneg

/-- The real masses of a finite total computation sum to one. -/
theorem sum_probabilityMass_eq_one {A : Type} [Fintype A] (sampler : ProbComp A) :
    ∑ value, probabilityMass sampler value = 1 := by
  classical
  unfold probabilityMass
  rw [← ENNReal.toReal_sum (fun value _ ↦ probOutput_ne_top),
    sum_probOutput_eq_one (by simp), ENNReal.toReal_one]

/-- Exact second moment of the density `dP/dQ` under `Q`.  Terms outside the support of `Q`
use Lean's total division; the comparison theorem separately requires support coverage. -/
def densitySecondMoment {A : Type} [Fintype A]
    (actual reference : ProbComp A) : ℝ :=
  ∑ value, probabilityMass actual value ^ 2 / probabilityMass reference value

theorem densitySecondMoment_nonneg {A : Type} [Fintype A]
    (actual reference : ProbComp A) :
    0 ≤ densitySecondMoment actual reference := by
  classical
  unfold densitySecondMoment
  exact Finset.sum_nonneg fun value _ ↦
    div_nonneg (sq_nonneg _) (probabilityMass_nonneg reference value)

/-- Finite weighted Cauchy--Schwarz in change-of-measure form. -/
theorem sq_sum_mul_le_density_mul_square
    {A : Type} [Fintype A]
    (p q observable : A → ℝ)
    (hq : ∀ value, 0 ≤ q value)
    (hcover : ∀ value, p value ≠ 0 → q value ≠ 0) :
    (∑ value, p value * observable value) ^ 2 ≤
      (∑ value, p value ^ 2 / q value) *
        ∑ value, q value * observable value ^ 2 := by
  classical
  have hCauchy := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (Finset.univ : Finset A)
    (r := fun value ↦ p value * observable value)
    (f := fun value ↦ p value ^ 2 / q value)
    (g := fun value ↦ q value * observable value ^ 2)
    (fun value _ ↦ div_nonneg (sq_nonneg _) (hq value))
    (fun value _ ↦ mul_nonneg (hq value) (sq_nonneg _))
    (fun value _ ↦ by
      by_cases hpzero : p value = 0
      · simp [hpzero]
      · have hqzero := hcover value hpzero
        field_simp
        ring_nf
        exact le_rfl)
  simpa [mul_comm] using hCauchy

/-- **Finite weighted squared-mean theorem.**  If the reference sampler covers every output
with positive actual mass, the actual squared mean is controlled by the exact second density
moment times the reference second moment. -/
theorem sq_expectation_le_densitySecondMoment_mul_secondMoment
    {A : Type} [Fintype A]
    (actual reference : ProbComp A) (observable : A → ℝ)
    (hcover : ∀ value, probabilityMass actual value ≠ 0 →
      probabilityMass reference value ≠ 0) :
    BoundedMoment.expectation actual observable ^ 2 ≤
      densitySecondMoment actual reference *
        BoundedMoment.expectation reference (fun value ↦ observable value ^ 2) := by
  classical
  exact sq_sum_mul_le_density_mul_square
    (fun value ↦ probabilityMass actual value)
    (fun value ↦ probabilityMass reference value)
    observable
    (probabilityMass_nonneg reference)
    hcover

/-! ## Independent-product factorization -/

/-- The real point mass of an IID finite product is the product of the coordinate masses. -/
theorem probabilityMass_sampleIID
    {A : Type} [Finite A] (count : ℕ) (sampler : ProbComp A)
    (values : Fin count → A) :
    probabilityMass (ProbComp.sampleIID count sampler) values =
      ∏ coordinate, probabilityMass sampler (values coordinate) := by
  letI : Fintype A := Fintype.ofFinite A
  unfold probabilityMass ProbComp.sampleIID
  rw [FormalProof4FHE.FiniteProduct.probOutput_fin_mOfFn,
    ENNReal.toReal_prod]

/-- The exact second density moment tensorizes under IID products. -/
theorem densitySecondMoment_sampleIID
    {A : Type} [Fintype A]
    (count : ℕ) (actual reference : ProbComp A) :
    densitySecondMoment
        (ProbComp.sampleIID count actual)
        (ProbComp.sampleIID count reference) =
      densitySecondMoment actual reference ^ count := by
  classical
  unfold densitySecondMoment
  simp_rw [probabilityMass_sampleIID]
  calc
    (∑ values : Fin count → A,
        (∏ coordinate, probabilityMass actual (values coordinate)) ^ 2 /
          ∏ coordinate, probabilityMass reference (values coordinate)) =
      ∑ values : Fin count → A,
        ∏ coordinate,
          probabilityMass actual (values coordinate) ^ 2 /
            probabilityMass reference (values coordinate) := by
      apply Finset.sum_congr rfl
      intro values _
      rw [Finset.prod_div_distrib, Finset.prod_pow]
    _ = ∏ _coordinate : Fin count,
        ∑ value : A,
          probabilityMass actual value ^ 2 /
            probabilityMass reference value := by
      exact (Fintype.prod_sum
        (fun _coordinate : Fin count ↦ fun value : A ↦
          probabilityMass actual value ^ 2 /
            probabilityMass reference value)).symm
    _ = (∑ value : A,
          probabilityMass actual value ^ 2 /
            probabilityMass reference value) ^ count := by
      rw [Fin.prod_const]

/-- Elementary exponential relaxation used after product factorization. -/
theorem one_add_pow_le_exp_nat_mul (count : ℕ) (cost : ℝ) (hcost : 0 ≤ cost) :
    (1 + cost) ^ count ≤ Real.exp ((count : ℝ) * cost) := by
  calc
    (1 + cost) ^ count ≤ Real.exp cost ^ count := by
      exact pow_le_pow_left₀ (by positivity) (by simpa [add_comm] using Real.add_one_le_exp cost) _
    _ = Real.exp ((count : ℝ) * cost) := by
      rw [← Real.exp_nat_mul]

end

end FormalProof4FHE.WeightedSquare
