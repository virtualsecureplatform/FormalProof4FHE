/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.RingSquareCenteredBinomialAnchorMoment

/-!
# Centered-Binomial Moment of an Independent Negacyclic Product

This file proves the exact coefficient second moment for the clean two-mask residual `Z₁ Z₂`.
Both masks have IID centered-binomial coefficients of width `eta`.  A fixed negacyclic output
coefficient is a signed dot product after a coordinate permutation, so independence gives

`E[((Z₁ Z₂)_k)^2] = N * (eta / 2)^2`.

The result is stated for the real centered-coefficient convolution.  Thus its only modular
hypothesis is the scalar no-wrap condition used to identify each executable `ZMod q` coefficient
with its signed CBD value; no ring-product no-wrap assumption is hidden in the statement.  A
finite second-moment (Chebyshev/Markov) tail bound is also supplied.
-/

open OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.RingProductCenteredBinomialMoment

noncomputable section

open FormalProof4FHE.BoundedMoment
open FormalProof4FHE.RLWE.CenteredBinomial
open FormalProof4FHE.TFHE.TGSW.RingSquare.PreimageCompiler.CenteredBinomialAnchorMoment

/-- Expectation commutes with a finite sum of observables. -/
theorem expectation_sum {A I : Type} [Fintype A] [Fintype I]
    (sampler : ProbComp A) (observable : I → A → ℝ) :
    expectation sampler (fun value ↦ ∑ index, observable index value) =
      ∑ index, expectation sampler (observable index) := by
  classical
  unfold expectation
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro index _
  rw [Finset.mul_sum]

/-- Elementary finite second-moment tail inequality, before division by the threshold. -/
theorem probEvent_sq_ge_toReal_mul_le_secondMoment
    {A : Type} [Fintype A] (sampler : ProbComp A) (lift : A → ℝ)
    (threshold : ℝ) :
    Pr[(fun value ↦ threshold ^ 2 ≤ lift value ^ 2) | sampler].toReal *
        threshold ^ 2 ≤ secondMoment sampler lift := by
  classical
  rw [probEvent_eq_sum_fintype_ite, ENNReal.toReal_sum]
  · simp only [apply_ite, ENNReal.toReal_zero]
    unfold secondMoment expectation
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro value _
    by_cases hvalue : threshold ^ 2 ≤ lift value ^ 2
    · rw [if_pos hvalue]
      exact mul_le_mul_of_nonneg_left hvalue ENNReal.toReal_nonneg
    · rw [if_neg hvalue, zero_mul]
      exact mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  · intro value _
    by_cases hvalue : threshold ^ 2 ≤ lift value ^ 2
    · simp [hvalue, probOutput_ne_top]
    · simp [hvalue]

/-- Finite second-moment tail inequality in inverse-square form. -/
theorem probEvent_sq_ge_toReal_le
    {A : Type} [Fintype A] (sampler : ProbComp A) (lift : A → ℝ)
    (threshold : ℝ) (hthreshold : 0 < threshold) :
    Pr[(fun value ↦ threshold ^ 2 ≤ lift value ^ 2) | sampler].toReal ≤
      secondMoment sampler lift / threshold ^ 2 := by
  apply (le_div_iff₀ (sq_pos_of_pos hthreshold)).2
  exact probEvent_sq_ge_toReal_mul_le_secondMoment sampler lift threshold

/-- Expected squared Euclidean norm of an IID CBD coefficient vector. -/
theorem expectation_sampleIID_sum_sq
    (q eta count : ℕ) [NeZero q] (hNoWrap : 2 * eta < q) :
    expectation (ProbComp.sampleIID count (coefficientSampler q eta))
        (fun values ↦ ∑ index, centeredCoefficientLift q (values index) ^ 2) =
      (count : ℝ) * ((eta : ℝ) / 2) := by
  rw [expectation_sum]
  have hcoordinate (index : Fin count) :
      expectation (ProbComp.sampleIID count (coefficientSampler q eta))
          (fun values ↦ centeredCoefficientLift q (values index) ^ 2) =
        (eta : ℝ) / 2 := by
    calc
      _ = secondMoment
          ((fun values : Fin count → ZMod q ↦ values index) <$>
            ProbComp.sampleIID count (coefficientSampler q eta))
          (centeredCoefficientLift q) := by
            rw [secondMoment_map]
      _ = secondMoment (coefficientSampler q eta) (centeredCoefficientLift q) := by
            apply secondMoment_congr_evalDist
            simpa [ProbComp.sampleIID] using
              (FormalProof4FHE.FiniteProduct.evalDist_map_fin_mOfFn_apply
                count (fun _ : Fin count ↦ coefficientSampler q eta) index id)
      _ = (eta : ℝ) / 2 :=
        secondMoment_coefficientSampler_centeredCoefficientLift q eta hNoWrap
  simp_rw [hcoordinate]
  simp

/-- Signed left coefficient in one fixed negacyclic convolution row. -/
def signedLeftWeight {q degree : ℕ} [NeZero q]
    (output : Fin (degree + 1)) (left : Fin (degree + 1) → ZMod q)
    (input : Fin (degree + 1)) : ℝ :=
  if input.val ≤ output.val then centeredCoefficientLift q (left input)
  else -centeredCoefficientLift q (left input)

@[simp]
theorem signedLeftWeight_sq {q degree : ℕ} [NeZero q]
    (output : Fin (degree + 1)) (left : Fin (degree + 1) → ZMod q)
    (input : Fin (degree + 1)) :
    signedLeftWeight output left input ^ 2 =
      centeredCoefficientLift q (left input) ^ 2 := by
  unfold signedLeftWeight
  split <;> ring

/-- Real centered coefficient of the negacyclic product of two modular coefficient vectors. -/
def realNegacyclicProductCoefficient {q degree : ℕ} [NeZero q]
    (output : Fin (degree + 1))
    (pair : (Fin (degree + 1) → ZMod q) × (Fin (degree + 1) → ZMod q)) : ℝ :=
  weightedSum (signedLeftWeight output pair.1) (centeredCoefficientLift q)
    (sourceIndexTableEquiv (ZMod q) output pair.2)

/-- Two independent IID CBD coefficient vectors. -/
def independentCoefficientPairSampler (q degree eta : ℕ) [NeZero q] :
    ProbComp ((Fin (degree + 1) → ZMod q) × (Fin (degree + 1) → ZMod q)) := do
  let left ← ProbComp.sampleIID (degree + 1) (coefficientSampler q eta)
  let right ← ProbComp.sampleIID (degree + 1) (coefficientSampler q eta)
  return (left, right)

/-- **Exact independent-CBD negacyclic product moment.** -/
theorem secondMoment_realNegacyclicProductCoefficient
    (q degree eta : ℕ) [NeZero q] (output : Fin (degree + 1))
    (hNoWrap : 2 * eta < q) :
    secondMoment (independentCoefficientPairSampler q degree eta)
        (realNegacyclicProductCoefficient output) =
      ((degree + 1 : ℕ) : ℝ) * ((eta : ℝ) / 2) ^ 2 := by
  unfold secondMoment independentCoefficientPairSampler
  rw [expectation_bind]
  have hinner (left : Fin (degree + 1) → ZMod q) :
      expectation
          (ProbComp.sampleIID (degree + 1) (coefficientSampler q eta) >>=
            fun right ↦ pure (left, right))
          (fun pair ↦ realNegacyclicProductCoefficient output pair ^ 2) =
        ((eta : ℝ) / 2) *
          ∑ input, centeredCoefficientLift q (left input) ^ 2 := by
    calc
      _ = secondMoment
          (sourceIndexTableEquiv (ZMod q) output <$>
            ProbComp.sampleIID (degree + 1) (coefficientSampler q eta))
          (weightedSum (signedLeftWeight output left)
            (centeredCoefficientLift q)) := by
              rw [secondMoment_map, expectation_bind]
              apply Finset.sum_congr rfl
              intro right _
              rw [expectation_pure]
              rfl
      _ = secondMoment
          (ProbComp.sampleIID (degree + 1) (coefficientSampler q eta))
          (weightedSum (signedLeftWeight output left)
            (centeredCoefficientLift q)) := by
              apply secondMoment_congr_evalDist
              exact sourceIndexTableEquiv_sampleIID_evalDist
                (coefficientSampler q eta) output
      _ = ((eta : ℝ) / 2) * ∑ input,
          signedLeftWeight output left input ^ 2 :=
            secondMoment_sampleIID_coefficientSampler_weightedSum
              q eta (degree + 1) (signedLeftWeight output left) hNoWrap
      _ = ((eta : ℝ) / 2) *
          ∑ input, centeredCoefficientLift q (left input) ^ 2 := by
            congr 1
            apply Finset.sum_congr rfl
            intro input _
            exact signedLeftWeight_sq output left input
  simp_rw [hinner]
  rw [← expectation, expectation_const_mul]
  rw [expectation_sampleIID_sum_sq q eta (degree + 1) hNoWrap]
  ring

/-- Inverse-square tail bound obtained from the exact independent-product moment. -/
theorem realNegacyclicProductCoefficient_tail
    (q degree eta : ℕ) [NeZero q] (output : Fin (degree + 1))
    (hNoWrap : 2 * eta < q) (threshold : ℝ) (hthreshold : 0 < threshold) :
    Pr[(fun pair ↦ threshold ^ 2 ≤
          realNegacyclicProductCoefficient output pair ^ 2) |
        independentCoefficientPairSampler q degree eta].toReal ≤
      (((degree + 1 : ℕ) : ℝ) * ((eta : ℝ) / 2) ^ 2) /
        threshold ^ 2 := by
  rw [← secondMoment_realNegacyclicProductCoefficient q degree eta output hNoWrap]
  exact probEvent_sq_ge_toReal_le _ _ threshold hthreshold

/-- Simultaneous maximum-coefficient tail obtained by a finite union bound.  This deliberately
keeps the elementary inverse-square estimate; stronger subexponential tails can replace it
without changing the exact moment theorem above. -/
theorem realNegacyclicProduct_allCoefficients_tail
    (q degree eta : ℕ) [NeZero q]
    (hNoWrap : 2 * eta < q) (threshold : ℝ) (hthreshold : 0 < threshold) :
    Pr[(fun pair ↦ ∃ output : Fin (degree + 1),
          threshold ^ 2 ≤ realNegacyclicProductCoefficient output pair ^ 2) |
        independentCoefficientPairSampler q degree eta].toReal ≤
      (((degree + 1 : ℕ) : ℝ) ^ 2 * ((eta : ℝ) / 2) ^ 2) /
        threshold ^ 2 := by
  let sampler := independentCoefficientPairSampler q degree eta
  let event : Fin (degree + 1) →
      ((Fin (degree + 1) → ZMod q) × (Fin (degree + 1) → ZMod q)) → Prop :=
    fun output pair ↦
      threshold ^ 2 ≤ realNegacyclicProductCoefficient output pair ^ 2
  have hunion :
      Pr[(fun pair ↦ ∃ output : Fin (degree + 1), event output pair) | sampler] ≤
        ∑ output : Fin (degree + 1), Pr[event output | sampler] := by
    simpa only [Finset.mem_univ, true_and] using
      (probEvent_exists_finset_le_sum
        (Finset.univ : Finset (Fin (degree + 1))) sampler event)
  have hsumNeTop :
      (∑ output : Fin (degree + 1), Pr[event output | sampler]) ≠ ⊤ := by
    exact ENNReal.sum_ne_top.mpr (fun output _ ↦ probEvent_ne_top)
  have hreal := ENNReal.toReal_mono hsumNeTop hunion
  have htoRealSum :
      (∑ output : Fin (degree + 1), Pr[event output | sampler]).toReal =
        ∑ output : Fin (degree + 1), Pr[event output | sampler].toReal := by
    rw [ENNReal.toReal_sum]
    intro output _
    exact probEvent_ne_top
  rw [htoRealSum] at hreal
  calc
    _ ≤ ∑ _output : Fin (degree + 1),
        (((degree + 1 : ℕ) : ℝ) * ((eta : ℝ) / 2) ^ 2) /
          threshold ^ 2 := by
      refine hreal.trans (Finset.sum_le_sum ?_)
      intro output _
      exact realNegacyclicProductCoefficient_tail
        q degree eta output hNoWrap threshold hthreshold
    _ = _ := by
      simp
      ring

end

end FormalProof4FHE.TFHE.RingProductCenteredBinomialMoment
