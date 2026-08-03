/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeTRGSWConcreteBRKRecovery

/-!
# Aggregate native-TRGSW security and complexity leveraging

The information-theoretic posterior-spectral route is incompatible with the native KSK recovery
theorems.  This module replaces its exponentially large absolute tail by one signed aggregate
high-pass experiment.  The experiment is defined by the Jordan decomposition of the canonical
Walsh high-pass measure.  Its gap is exactly the signed high-degree diagonal Fourier sum, divided
by a finite normalization factor.

The second part instantiates the existing two-copy squared-bias theorem with the *complete key* as
the guessed leakage.  This is the match-and-square reduction from the note: an optimized
square-root tilted fake-key law incurs exactly the order-`1/2` Renyi concentration of the full key.
The final theorem composes the low-degree joint-affine premise, aggregate reduction, construction
defect, and independent-message endpoint.  Constructibility of the complete native aggregate view
from zero-row RLWE remains an explicit premise, rather than being hidden in the finite algebra.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.NativeTRGSWAggregateSecurityAndComplexityLeveraging

noncomputable section

open NativeTRGSWBarrierAndSpectralBoundary
open RGSWCoefficientCircularSecurity

/-! ## The canonical finite Walsh high-pass measure -/

/-- Frequencies of degree at most `degree`, including the zero frequency. -/
def boundedFrequencies (Index : Type) [Fintype Index] [DecidableEq Index]
    (degree : ℕ) : Finset (BitVector Index) :=
  insert zeroFrequency (lowFrequencies Index degree)

@[simp]
theorem zeroFrequency_mem_boundedFrequencies
    (Index : Type) [Fintype Index] [DecidableEq Index] (degree : ℕ) :
    (zeroFrequency : BitVector Index) ∈ boundedFrequencies Index degree := by
  simp [boundedFrequencies]

theorem zeroFrequency_not_mem_lowFrequencies
    (Index : Type) [Fintype Index] [DecidableEq Index] (degree : ℕ) :
    (zeroFrequency : BitVector Index) ∉ lowFrequencies Index degree := by
  simp [lowFrequencies, nonzeroFrequencies]

theorem card_boundedFrequencies
    (Index : Type) [Fintype Index] [DecidableEq Index] (degree : ℕ) :
    (boundedFrequencies Index degree).card = lowFrequencyCount Index degree + 1 := by
  simp [boundedFrequencies, zeroFrequency_not_mem_lowFrequencies,
    lowFrequencyCount]

/-- Point mass at the zero xor mask. -/
def zeroPointWeight {Index : Type} [Fintype Index] [DecidableEq Index]
    (mask : BitVector Index) : ℝ :=
  if mask = zeroFrequency then 1 else 0

/-- The bounded-degree Walsh kernel `sum_(|S| <= d) chi_S(mask)`. -/
def lowPassKernel (Index : Type) [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (mask : BitVector Index) : ℝ :=
  ∑ frequency ∈ boundedFrequencies Index degree, walsh frequency mask

/-- Canonical signed high-pass weight `delta_0 - K_{<=d}/2^t`. -/
def highPassWeight (Index : Type) [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (mask : BitVector Index) : ℝ :=
  zeroPointWeight mask - lowPassKernel Index degree mask / cubeSize Index

/-- Unnormalized Walsh transform of a real weight table. -/
def walshTransform {Index : Type} [Fintype Index] [DecidableEq Index]
    (weight : BitVector Index → ℝ) (frequency : BitVector Index) : ℝ :=
  ∑ mask, weight mask * walsh frequency mask

theorem sum_zeroPointWeight_mul_walsh
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (frequency : BitVector Index) :
    (∑ mask : BitVector Index, zeroPointWeight mask * walsh frequency mask) = 1 := by
  classical
  simp [zeroPointWeight, walsh, zeroFrequency, bitSign]

theorem sum_lowPassKernel_mul_walsh
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (frequency : BitVector Index) :
    (∑ mask : BitVector Index,
        lowPassKernel Index degree mask * walsh frequency mask) =
      if frequency ∈ boundedFrequencies Index degree then cubeSize Index else 0 := by
  classical
  unfold lowPassKernel
  calc
    (∑ mask : BitVector Index,
        (∑ candidate ∈ boundedFrequencies Index degree,
          walsh candidate mask) * walsh frequency mask) =
        ∑ mask : BitVector Index,
          ∑ candidate ∈ boundedFrequencies Index degree,
            walsh candidate mask * walsh frequency mask := by
      apply Finset.sum_congr rfl
      intro mask _
      rw [Finset.sum_mul]
    _ = ∑ candidate ∈ boundedFrequencies Index degree,
          ∑ mask : BitVector Index,
            walsh candidate mask * walsh frequency mask := by
      rw [Finset.sum_comm]
    _ = ∑ candidate ∈ boundedFrequencies Index degree,
          if candidate = frequency then cubeSize Index else 0 := by
      apply Finset.sum_congr rfl
      intro candidate _
      exact walsh_orthogonality candidate frequency
    _ = if frequency ∈ boundedFrequencies Index degree then cubeSize Index else 0 := by
      by_cases hfrequency : frequency ∈ boundedFrequencies Index degree
      · simp [hfrequency]
      · simp [hfrequency]

/-- Exact transform of the high-pass signed measure: it kills bounded degrees and is one on every
higher frequency. -/
theorem walshTransform_highPassWeight
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (frequency : BitVector Index) :
    walshTransform (highPassWeight Index degree) frequency =
      if frequency ∈ boundedFrequencies Index degree then 0 else 1 := by
  classical
  unfold walshTransform highPassWeight
  calc
    (∑ mask : BitVector Index,
        (zeroPointWeight mask - lowPassKernel Index degree mask / cubeSize Index) *
          walsh frequency mask) =
        (∑ mask : BitVector Index,
          zeroPointWeight mask * walsh frequency mask) -
        (∑ mask : BitVector Index,
          lowPassKernel Index degree mask * walsh frequency mask) / cubeSize Index := by
      calc
        _ = ∑ mask : BitVector Index,
            (zeroPointWeight mask * walsh frequency mask -
              (lowPassKernel Index degree mask * walsh frequency mask) /
                cubeSize Index) := by
          apply Finset.sum_congr rfl
          intro mask _
          ring
        _ = (∑ mask : BitVector Index,
              zeroPointWeight mask * walsh frequency mask) -
            ∑ mask : BitVector Index,
              (lowPassKernel Index degree mask * walsh frequency mask) /
                cubeSize Index := by
          simp only [Finset.sum_sub_distrib]
        _ = _ := by
          congr 1
          simp only [div_eq_mul_inv]
          rw [← Finset.sum_mul]
    _ = 1 -
        (if frequency ∈ boundedFrequencies Index degree then cubeSize Index else 0) /
          cubeSize Index := by
      rw [sum_zeroPointWeight_mul_walsh,
        sum_lowPassKernel_mul_walsh]
    _ = if frequency ∈ boundedFrequencies Index degree then 0 else 1 := by
      by_cases hfrequency : frequency ∈ boundedFrequencies Index degree <;>
        simp [hfrequency, cubeSize_ne_zero Index]

/-- The high-pass signed table has total mass zero. -/
theorem sum_highPassWeight_eq_zero
    (Index : Type) [Fintype Index] [DecidableEq Index] (degree : ℕ) :
    ∑ mask : BitVector Index, highPassWeight Index degree mask = 0 := by
  have htransform := walshTransform_highPassWeight
    (Index := Index) degree (zeroFrequency : BitVector Index)
  rw [if_pos (zeroFrequency_mem_boundedFrequencies Index degree)] at htransform
  simpa [walshTransform, walsh_zeroFrequency] using htransform

/-! ## Jordan decomposition and normalized aggregate masks -/

/-- Positive Jordan part, written without order-lattice notation. -/
def positiveHighPassWeight (Index : Type) [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (mask : BitVector Index) : ℝ :=
  (|highPassWeight Index degree mask| + highPassWeight Index degree mask) / 2

/-- Negative Jordan part. -/
def negativeHighPassWeight (Index : Type) [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (mask : BitVector Index) : ℝ :=
  (|highPassWeight Index degree mask| - highPassWeight Index degree mask) / 2

theorem positiveHighPassWeight_nonneg
    (Index : Type) [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (mask : BitVector Index) :
    0 ≤ positiveHighPassWeight Index degree mask := by
  unfold positiveHighPassWeight
  linarith [neg_le_abs (highPassWeight Index degree mask)]

theorem negativeHighPassWeight_nonneg
    (Index : Type) [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (mask : BitVector Index) :
    0 ≤ negativeHighPassWeight Index degree mask := by
  unfold negativeHighPassWeight
  linarith [le_abs_self (highPassWeight Index degree mask)]

theorem positive_sub_negativeHighPassWeight
    (Index : Type) [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (mask : BitVector Index) :
    positiveHighPassWeight Index degree mask -
        negativeHighPassWeight Index degree mask =
      highPassWeight Index degree mask := by
  unfold positiveHighPassWeight negativeHighPassWeight
  ring

/-- Common positive/negative Jordan mass `lambda_d`. -/
def aggregateNormalization (Index : Type) [Fintype Index] [DecidableEq Index]
    (degree : ℕ) : ℝ :=
  ∑ mask : BitVector Index, positiveHighPassWeight Index degree mask

theorem sum_negativeHighPassWeight_eq_aggregateNormalization
    (Index : Type) [Fintype Index] [DecidableEq Index] (degree : ℕ) :
    (∑ mask : BitVector Index, negativeHighPassWeight Index degree mask) =
      aggregateNormalization Index degree := by
  have hzero := sum_highPassWeight_eq_zero Index degree
  have hdiff :
      (∑ mask : BitVector Index,
        (positiveHighPassWeight Index degree mask -
          negativeHighPassWeight Index degree mask)) = 0 := by
    simpa only [positive_sub_negativeHighPassWeight] using hzero
  rw [Finset.sum_sub_distrib] at hdiff
  unfold aggregateNormalization
  linarith

/-- Full-support frequency used to prove positivity when the cutoff is below the dimension. -/
def fullFrequency (Index : Type) : BitVector Index := fun _ ↦ true

@[simp]
theorem supportSize_fullFrequency
    (Index : Type) [Fintype Index] [DecidableEq Index] :
    supportSize (fullFrequency Index) = Fintype.card Index := by
  simp [supportSize, frequencySupport, fullFrequency]

theorem fullFrequency_not_mem_boundedFrequencies
    (Index : Type) [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree < Fintype.card Index) :
    fullFrequency Index ∉ boundedFrequencies Index degree := by
  simp only [boundedFrequencies, Finset.mem_insert]
  push Not
  constructor
  · intro hequal
    have hcardpos : 0 < Fintype.card Index := by omega
    let coordinate : Index := Classical.choice (Fintype.card_pos_iff.mp hcardpos)
    have hvalue := congrFun hequal coordinate
    simp [fullFrequency, zeroFrequency] at hvalue
  · simp [lowFrequencies, supportSize_fullFrequency, hdegree]

theorem boundedFrequencies_ssubset_univ
    (Index : Type) [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree < Fintype.card Index) :
    boundedFrequencies Index degree ⊂ (Finset.univ : Finset (BitVector Index)) := by
  rw [Finset.ssubset_iff_subset_ne]
  refine ⟨Finset.subset_univ _, ?_⟩
  intro hequal
  have hmember : fullFrequency Index ∈ boundedFrequencies Index degree := by
    rw [hequal]
    simp
  exact fullFrequency_not_mem_boundedFrequencies Index degree hdegree hmember

theorem card_boundedFrequencies_lt_cubeSize
    (Index : Type) [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree < Fintype.card Index) :
    ((boundedFrequencies Index degree).card : ℝ) < cubeSize Index := by
  have hcardNat :
      (boundedFrequencies Index degree).card < Fintype.card (BitVector Index) :=
    Finset.card_lt_card
      (boundedFrequencies_ssubset_univ Index degree hdegree)
  have hcardReal :
      ((boundedFrequencies Index degree).card : ℝ) <
        (Fintype.card (BitVector Index) : ℝ) := by
    exact_mod_cast hcardNat
  simpa [cubeSize] using hcardReal

@[simp]
theorem walsh_zeroWord
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (frequency : BitVector Index) :
    walsh frequency (zeroFrequency : BitVector Index) = 1 := by
  rw [walsh_comm, walsh_zeroFrequency]

theorem lowPassKernel_zeroFrequency
    (Index : Type) [Fintype Index] [DecidableEq Index] (degree : ℕ) :
    lowPassKernel Index degree (zeroFrequency : BitVector Index) =
      (boundedFrequencies Index degree).card := by
  simp [lowPassKernel]

theorem highPassWeight_zeroFrequency_pos
    (Index : Type) [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree < Fintype.card Index) :
    0 < highPassWeight Index degree (zeroFrequency : BitVector Index) := by
  rw [highPassWeight, lowPassKernel_zeroFrequency]
  simp only [zeroPointWeight]
  have hcube := cubeSize_pos Index
  have hcard := card_boundedFrequencies_lt_cubeSize Index degree hdegree
  apply sub_pos.mpr
  exact (div_lt_one hcube).mpr hcard

theorem aggregateNormalization_pos
    (Index : Type) [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree < Fintype.card Index) :
    0 < aggregateNormalization Index degree := by
  let zero : BitVector Index := zeroFrequency
  have hweight : 0 < highPassWeight Index degree zero :=
    highPassWeight_zeroFrequency_pos Index degree hdegree
  have hpositivePart :
      positiveHighPassWeight Index degree zero = highPassWeight Index degree zero := by
    unfold positiveHighPassWeight
    rw [abs_of_pos hweight]
    ring
  have hsingle :
      positiveHighPassWeight Index degree zero ≤
        aggregateNormalization Index degree := by
    unfold aggregateNormalization
    exact Finset.single_le_sum
      (fun mask _ ↦ positiveHighPassWeight_nonneg Index degree mask)
      (Finset.mem_univ zero)
  rw [hpositivePart] at hsingle
  exact hweight.trans_le hsingle

/-- Positive aggregate mask law. -/
def aggregatePositiveWeight (Index : Type) [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (mask : BitVector Index) : ℝ :=
  positiveHighPassWeight Index degree mask / aggregateNormalization Index degree

/-- Negative aggregate mask law. -/
def aggregateNegativeWeight (Index : Type) [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (mask : BitVector Index) : ℝ :=
  negativeHighPassWeight Index degree mask / aggregateNormalization Index degree

theorem aggregatePositiveWeight_nonneg
    (Index : Type) [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (mask : BitVector Index) :
    0 ≤ aggregatePositiveWeight Index degree mask := by
  exact div_nonneg (positiveHighPassWeight_nonneg Index degree mask)
    (Finset.sum_nonneg fun candidate _ ↦
      positiveHighPassWeight_nonneg Index degree candidate)

theorem aggregateNegativeWeight_nonneg
    (Index : Type) [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (mask : BitVector Index) :
    0 ≤ aggregateNegativeWeight Index degree mask := by
  exact div_nonneg (negativeHighPassWeight_nonneg Index degree mask)
    (Finset.sum_nonneg fun candidate _ ↦
      positiveHighPassWeight_nonneg Index degree candidate)

theorem sum_aggregatePositiveWeight_eq_one
    (Index : Type) [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree < Fintype.card Index) :
    ∑ mask : BitVector Index, aggregatePositiveWeight Index degree mask = 1 := by
  unfold aggregatePositiveWeight aggregateNormalization
  rw [← Finset.sum_div, div_self]
  exact ne_of_gt (aggregateNormalization_pos Index degree hdegree)

theorem sum_aggregateNegativeWeight_eq_one
    (Index : Type) [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree < Fintype.card Index) :
    ∑ mask : BitVector Index, aggregateNegativeWeight Index degree mask = 1 := by
  unfold aggregateNegativeWeight
  rw [← Finset.sum_div, sum_negativeHighPassWeight_eq_aggregateNormalization,
    div_self]
  exact ne_of_gt (aggregateNormalization_pos Index degree hdegree)

theorem aggregateWeight_walsh_gap
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (frequency : BitVector Index) :
    (∑ mask : BitVector Index,
        aggregatePositiveWeight Index degree mask * walsh frequency mask) -
      (∑ mask : BitVector Index,
        aggregateNegativeWeight Index degree mask * walsh frequency mask) =
      (if frequency ∈ boundedFrequencies Index degree then 0 else 1) /
        aggregateNormalization Index degree := by
  rw [← Finset.sum_sub_distrib]
  calc
    (∑ mask : BitVector Index,
        (aggregatePositiveWeight Index degree mask * walsh frequency mask -
          aggregateNegativeWeight Index degree mask * walsh frequency mask)) =
      (∑ mask : BitVector Index,
        highPassWeight Index degree mask * walsh frequency mask) /
          aggregateNormalization Index degree := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro mask _
        unfold aggregatePositiveWeight aggregateNegativeWeight
        rw [← positive_sub_negativeHighPassWeight Index degree mask]
        ring
    _ = _ := by rw [← walshTransform, walshTransform_highPassWeight]

/-! ### Normalization bounds -/

/-- The common Jordan mass is one half of the `L¹` mass of the signed high-pass table. -/
theorem two_mul_aggregateNormalization_eq_sum_abs
    (Index : Type) [Fintype Index] [DecidableEq Index] (degree : ℕ) :
    2 * aggregateNormalization Index degree =
      ∑ mask : BitVector Index, |highPassWeight Index degree mask| := by
  have hzero := sum_highPassWeight_eq_zero Index degree
  unfold aggregateNormalization positiveHighPassWeight
  calc
    2 * ∑ mask : BitVector Index,
        (|highPassWeight Index degree mask| + highPassWeight Index degree mask) / 2 =
      (∑ mask : BitVector Index, |highPassWeight Index degree mask|) +
        ∑ mask : BitVector Index, highPassWeight Index degree mask := by
      rw [Finset.mul_sum]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro mask _
      ring
    _ = _ := by rw [hzero, add_zero]

/-- Exact low-pass second moment from Walsh orthogonality. -/
theorem sum_lowPassKernel_sq
    (Index : Type) [Fintype Index] [DecidableEq Index] (degree : ℕ) :
    (∑ mask : BitVector Index, lowPassKernel Index degree mask ^ 2) =
      cubeSize Index * (boundedFrequencies Index degree).card := by
  classical
  unfold lowPassKernel
  calc
    (∑ mask : BitVector Index,
        (∑ first ∈ boundedFrequencies Index degree, walsh first mask) ^ 2) =
      ∑ mask : BitVector Index,
        ∑ first ∈ boundedFrequencies Index degree,
          ∑ second ∈ boundedFrequencies Index degree,
            walsh first mask * walsh second mask := by
      apply Finset.sum_congr rfl
      intro mask _
      rw [pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro first _
      rw [Finset.mul_sum]
    _ = ∑ first ∈ boundedFrequencies Index degree,
        ∑ second ∈ boundedFrequencies Index degree,
          ∑ mask : BitVector Index,
            walsh first mask * walsh second mask := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro first _
      rw [Finset.sum_comm]
    _ = ∑ first ∈ boundedFrequencies Index degree,
        ∑ second ∈ boundedFrequencies Index degree,
          if first = second then cubeSize Index else 0 := by
      apply Finset.sum_congr rfl
      intro first _
      apply Finset.sum_congr rfl
      intro second _
      exact walsh_orthogonality first second
    _ = cubeSize Index * (boundedFrequencies Index degree).card := by
      simp [mul_comm]

/-- Cauchy--Schwarz gives the sharp mean-absolute low-pass bound. -/
theorem sum_abs_lowPassKernel_div_cubeSize_le_sqrt_card
    (Index : Type) [Fintype Index] [DecidableEq Index] (degree : ℕ) :
    (∑ mask : BitVector Index, |lowPassKernel Index degree mask|) /
        cubeSize Index ≤
      Real.sqrt (boundedFrequencies Index degree).card := by
  classical
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _mask : BitVector Index ↦ (1 : ℝ))
    (fun mask ↦ |lowPassKernel Index degree mask|)
  have hcubeCard :
      (Fintype.card (BitVector Index) : ℝ) = cubeSize Index := by
    simp [cubeSize]
  have hsquare :
      (∑ mask : BitVector Index, |lowPassKernel Index degree mask|) ^ 2 ≤
        cubeSize Index ^ 2 * (boundedFrequencies Index degree).card := by
    calc
      _ ≤ (Fintype.card (BitVector Index) : ℝ) * 1 *
          ∑ mask : BitVector Index, lowPassKernel Index degree mask ^ 2 := by
        simpa only [one_mul, one_pow, Finset.sum_const, Finset.card_univ,
          nsmul_eq_mul, sq_abs] using hcauchy
      _ = (Fintype.card (BitVector Index) : ℝ) *
          ∑ mask : BitVector Index, lowPassKernel Index degree mask ^ 2 := by ring
      _ = _ := by
        rw [hcubeCard, sum_lowPassKernel_sq]
        ring
  have hnormalizedSquare :
      ((∑ mask : BitVector Index, |lowPassKernel Index degree mask|) /
          cubeSize Index) ^ 2 ≤
        ((boundedFrequencies Index degree).card : ℝ) := by
    have hcubeSq : 0 < cubeSize Index ^ 2 := sq_pos_of_pos (cubeSize_pos Index)
    calc
      _ = (∑ mask : BitVector Index, |lowPassKernel Index degree mask|) ^ 2 /
          cubeSize Index ^ 2 := by ring
      _ ≤ (cubeSize Index ^ 2 * (boundedFrequencies Index degree).card) /
          cubeSize Index ^ 2 :=
        div_le_div_of_nonneg_right hsquare hcubeSq.le
      _ = _ := by field_simp [ne_of_gt (cubeSize_pos Index)]
  exact Real.le_sqrt_of_sq_le hnormalizedSquare

/-- Positive mass at zero gives the lower normalization bound from the note. -/
theorem one_sub_card_div_cubeSize_le_aggregateNormalization
    (Index : Type) [Fintype Index] [DecidableEq Index] (degree : ℕ) :
    1 - (boundedFrequencies Index degree).card / cubeSize Index ≤
      aggregateNormalization Index degree := by
  let zero : BitVector Index := zeroFrequency
  have hpart :
      highPassWeight Index degree zero ≤
        positiveHighPassWeight Index degree zero := by
    unfold positiveHighPassWeight
    linarith [le_abs_self (highPassWeight Index degree zero)]
  have hsingle :
      positiveHighPassWeight Index degree zero ≤
        aggregateNormalization Index degree := by
    unfold aggregateNormalization
    exact Finset.single_le_sum
      (fun mask _ ↦ positiveHighPassWeight_nonneg Index degree mask)
      (Finset.mem_univ zero)
  calc
    1 - (boundedFrequencies Index degree).card / cubeSize Index =
        highPassWeight Index degree zero := by
      simp [zero, highPassWeight, lowPassKernel_zeroFrequency, zeroPointWeight]
    _ ≤ positiveHighPassWeight Index degree zero := hpart
    _ ≤ aggregateNormalization Index degree := hsingle

/-- Sharp polynomial normalization bound `lambda_d <= (1 + sqrt N_{<=d}) / 2`. -/
theorem aggregateNormalization_le_one_add_sqrt_card_div_two
    (Index : Type) [Fintype Index] [DecidableEq Index] (degree : ℕ) :
    aggregateNormalization Index degree ≤
      (1 + Real.sqrt (boundedFrequencies Index degree).card) / 2 := by
  have habs :
      (∑ mask : BitVector Index, |highPassWeight Index degree mask|) ≤
        1 + (∑ mask : BitVector Index, |lowPassKernel Index degree mask|) /
          cubeSize Index := by
    calc
      _ ≤ ∑ mask : BitVector Index,
          (|zeroPointWeight mask| +
            |lowPassKernel Index degree mask / cubeSize Index|) := by
        apply Finset.sum_le_sum
        intro mask _
        exact abs_sub _ _
      _ = (∑ mask : BitVector Index, |zeroPointWeight mask|) +
          ∑ mask : BitVector Index,
            |lowPassKernel Index degree mask / cubeSize Index| := by
        rw [Finset.sum_add_distrib]
      _ = 1 + (∑ mask : BitVector Index, |lowPassKernel Index degree mask|) /
          cubeSize Index := by
        congr 1
        · calc
            (∑ mask : BitVector Index, |zeroPointWeight mask|) =
              ∑ mask : BitVector Index, zeroPointWeight mask := by
                apply Finset.sum_congr rfl
                intro mask _
                unfold zeroPointWeight
                split <;> simp
            _ = ∑ mask : BitVector Index,
                zeroPointWeight mask *
                  walsh (zeroFrequency : BitVector Index) mask := by
                apply Finset.sum_congr rfl
                intro mask _
                rw [walsh_zeroFrequency, mul_one]
            _ = 1 := sum_zeroPointWeight_mul_walsh zeroFrequency
        · calc
            (∑ mask : BitVector Index,
                |lowPassKernel Index degree mask / cubeSize Index|) =
              ∑ mask : BitVector Index,
                |lowPassKernel Index degree mask| / cubeSize Index := by
                apply Finset.sum_congr rfl
                intro mask _
                rw [abs_div, abs_of_pos (cubeSize_pos Index)]
            _ = _ := by
              simp only [div_eq_mul_inv]
              rw [← Finset.sum_mul]
  have hmean := sum_abs_lowPassKernel_div_cubeSize_le_sqrt_card Index degree
  have htwo := two_mul_aggregateNormalization_eq_sum_abs Index degree
  nlinarith

/-- The same bounds with `N_{<=d} = 1 + N_d` exposed through the existing low-frequency count. -/
theorem aggregateNormalization_bounds
    (Index : Type) [Fintype Index] [DecidableEq Index] (degree : ℕ) :
    1 - (lowFrequencyCount Index degree + 1) / cubeSize Index ≤
        aggregateNormalization Index degree ∧
      aggregateNormalization Index degree ≤
        (1 + Real.sqrt (lowFrequencyCount Index degree + 1)) / 2 := by
  have hcard :
      ((boundedFrequencies Index degree).card : ℝ) =
        (lowFrequencyCount Index degree : ℝ) + 1 := by
    exact_mod_cast card_boundedFrequencies Index degree
  rw [← hcard]
  exact ⟨one_sub_card_div_cubeSize_le_aggregateNormalization Index degree,
    aggregateNormalization_le_one_add_sqrt_card_div_two Index degree⟩

/-! ## Exact aggregate-tail identity -/

/-- Mean response after xoring the secret with a mask drawn from an arbitrary real weight table.
The secret is uniform; a table summing to one is an ordinary mask law. -/
def weightedOrbitMean
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (weight : BitVector Index → ℝ)
    (response : BitVector Index → BitVector Index → ℝ) : ℝ :=
  (∑ secret : BitVector Index, ∑ mask : BitVector Index,
      weight mask * response secret (xorEquiv secret mask)) / cubeSize Index

theorem weightedOrbitMean_zero
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (response : BitVector Index → BitVector Index → ℝ) :
    weightedOrbitMean (fun _ ↦ 0) response = 0 := by
  simp [weightedOrbitMean]

theorem weightedOrbitMean_add
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (left right : BitVector Index → ℝ)
    (response : BitVector Index → BitVector Index → ℝ) :
    weightedOrbitMean (fun mask ↦ left mask + right mask) response =
      weightedOrbitMean left response + weightedOrbitMean right response := by
  unfold weightedOrbitMean
  simp only [add_mul, Finset.sum_add_distrib]
  ring

theorem weightedOrbitMean_sub
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (left right : BitVector Index → ℝ)
    (response : BitVector Index → BitVector Index → ℝ) :
    weightedOrbitMean (fun mask ↦ left mask - right mask) response =
      weightedOrbitMean left response - weightedOrbitMean right response := by
  unfold weightedOrbitMean
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

theorem weightedOrbitMean_div
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (weight : BitVector Index → ℝ) (divisor : ℝ)
    (response : BitVector Index → BitVector Index → ℝ) :
    weightedOrbitMean (fun mask ↦ weight mask / divisor) response =
      weightedOrbitMean weight response / divisor := by
  unfold weightedOrbitMean
  simp only [div_eq_mul_inv]
  calc
    (∑ secret : BitVector Index, ∑ mask : BitVector Index,
        weight mask * divisor⁻¹ * response secret (xorEquiv secret mask)) /
          cubeSize Index =
      ((∑ secret : BitVector Index, ∑ mask : BitVector Index,
          weight mask * response secret (xorEquiv secret mask)) * divisor⁻¹) /
        cubeSize Index := by
      congr 1
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro secret _
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro mask _
      ring
    _ = _ := by ring

theorem weightedOrbitMean_finset_sum
    {Index Frequency : Type} [Fintype Index] [DecidableEq Index]
    (frequencies : Finset Frequency) (weight : Frequency → BitVector Index → ℝ)
    (response : BitVector Index → BitVector Index → ℝ) :
    weightedOrbitMean
        (fun mask ↦ ∑ frequency ∈ frequencies, weight frequency mask) response =
      ∑ frequency ∈ frequencies, weightedOrbitMean (weight frequency) response := by
  classical
  induction frequencies using Finset.induction_on with
  | empty => simp [weightedOrbitMean_zero]
  | @insert frequency frequencies hfrequency ih =>
      simp only [Finset.sum_insert hfrequency]
      rw [weightedOrbitMean_add, ih]

/-- A single Walsh-weighted orbit mean is the corresponding diagonal Fourier coefficient times
the cube size. -/
theorem weightedOrbitMean_walsh
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (response : BitVector Index → BitVector Index → ℝ)
    (frequency : BitVector Index) :
    weightedOrbitMean (walsh frequency) response =
      cubeSize Index * fourierCoefficient response frequency frequency := by
  have horbit := orbitFilteredCorrelation_eq_fourierCoefficient response frequency
  unfold weightedOrbitMean orbitFilteredCorrelation at *
  rw [← horbit]
  field_simp [cubeSize_ne_zero Index]

/-- Dividing the character weight by the cube size gives exactly one diagonal coefficient. -/
theorem weightedOrbitMean_walsh_div_cube
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (response : BitVector Index → BitVector Index → ℝ)
    (frequency : BitVector Index) :
    weightedOrbitMean (fun mask ↦ walsh frequency mask / cubeSize Index) response =
      fourierCoefficient response frequency frequency := by
  rw [weightedOrbitMean_div, weightedOrbitMean_walsh]
  field_simp [cubeSize_ne_zero Index]

@[simp]
theorem xorEquiv_zeroFrequency
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (secret : BitVector Index) :
    xorEquiv secret (zeroFrequency : BitVector Index) = secret := by
  funext coordinate
  simp [xorEquiv, zeroFrequency, LWE.MultiKeyAffine.maskedBit]

/-- The zero point mass produces the diagonal mean. -/
theorem weightedOrbitMean_zeroPointWeight
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (response : BitVector Index → BitVector Index → ℝ) :
    weightedOrbitMean zeroPointWeight response = diagonalMean response := by
  classical
  unfold weightedOrbitMean diagonalMean zeroPointWeight
  congr 1
  apply Finset.sum_congr rfl
  intro secret _
  simp

/-- The normalized low-pass kernel extracts the complete bounded-frequency diagonal sum. -/
theorem weightedOrbitMean_lowPassKernel_div_cube
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (response : BitVector Index → BitVector Index → ℝ) (degree : ℕ) :
    weightedOrbitMean
        (fun mask ↦ lowPassKernel Index degree mask / cubeSize Index) response =
      ∑ frequency ∈ boundedFrequencies Index degree,
        fourierCoefficient response frequency frequency := by
  calc
    weightedOrbitMean
        (fun mask ↦ lowPassKernel Index degree mask / cubeSize Index) response =
      weightedOrbitMean
        (fun mask ↦ ∑ frequency ∈ boundedFrequencies Index degree,
          walsh frequency mask / cubeSize Index) response := by
        congr 2
        funext mask
        unfold lowPassKernel
        rw [Finset.sum_div]
    _ = ∑ frequency ∈ boundedFrequencies Index degree,
        weightedOrbitMean
          (fun mask ↦ walsh frequency mask / cubeSize Index) response :=
      weightedOrbitMean_finset_sum _ _ _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro frequency _
      exact weightedOrbitMean_walsh_div_cube response frequency

/-- Signed high-degree diagonal Fourier sum.  Unlike the rejected statistical tail, this does not
sum the absolute values of exponentially many coefficients. -/
def signedHighDegreeSum
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (response : BitVector Index → BitVector Index → ℝ) (degree : ℕ) : ℝ :=
  ∑ frequency ∈ highFrequencies Index degree,
    fourierCoefficient response frequency frequency

/-- The unnormalized high-pass orbit experiment is exactly the signed high-degree diagonal sum. -/
theorem weightedOrbitMean_highPassWeight
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (response : BitVector Index → BitVector Index → ℝ) (degree : ℕ) :
    weightedOrbitMean (highPassWeight Index degree) response =
      signedHighDegreeSum response degree := by
  rw [show highPassWeight Index degree =
      fun mask ↦ zeroPointWeight mask -
        lowPassKernel Index degree mask / cubeSize Index by rfl]
  rw [weightedOrbitMean_sub, weightedOrbitMean_zeroPointWeight,
    weightedOrbitMean_lowPassKernel_div_cube]
  unfold boundedFrequencies
  rw [Finset.sum_insert (zeroFrequency_not_mem_lowFrequencies Index degree),
    fourierCoefficient_zero_zero]
  have hdiagonal := diagonalFourierIdentity response
  rw [show (Finset.univ.erase (zeroFrequency : BitVector Index)) =
      nonzeroFrequencies Index by rfl] at hdiagonal
  have hpartition := sum_nonzero_eq_sum_low_add_sum_high degree
    (fun frequency ↦ fourierCoefficient response frequency frequency)
  calc
    diagonalMean response -
        (independentMean response +
          ∑ frequency ∈ lowFrequencies Index degree,
            fourierCoefficient response frequency frequency) =
      (diagonalMean response - independentMean response) -
        ∑ frequency ∈ lowFrequencies Index degree,
          fourierCoefficient response frequency frequency := by ring
    _ = (∑ frequency ∈ nonzeroFrequencies Index,
          fourierCoefficient response frequency frequency) -
        ∑ frequency ∈ lowFrequencies Index degree,
          fourierCoefficient response frequency frequency := by rw [hdiagonal]
    _ = _ := by
      rw [hpartition]
      unfold signedHighDegreeSum
      ring

/-- Acceptance in one of the two aggregate games, represented directly by its exact finite mask
law. -/
def aggregateAcceptance
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (positive : Bool)
    (response : BitVector Index → BitVector Index → ℝ) (degree : ℕ) : ℝ :=
  weightedOrbitMean
    (if positive then aggregatePositiveWeight Index degree
      else aggregateNegativeWeight Index degree)
    response

/-- Exact aggregate-tail identity from the note. -/
theorem aggregateAcceptance_true_sub_false
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (response : BitVector Index → BitVector Index → ℝ) (degree : ℕ) :
    aggregateAcceptance true response degree -
        aggregateAcceptance false response degree =
      signedHighDegreeSum response degree /
        aggregateNormalization Index degree := by
  change
    weightedOrbitMean (aggregatePositiveWeight Index degree) response -
        weightedOrbitMean (aggregateNegativeWeight Index degree) response = _
  rw [← weightedOrbitMean_sub]
  calc
    weightedOrbitMean
        (fun mask ↦ aggregatePositiveWeight Index degree mask -
          aggregateNegativeWeight Index degree mask) response =
      weightedOrbitMean
        (fun mask ↦ highPassWeight Index degree mask /
          aggregateNormalization Index degree) response := by
        congr 2
        funext mask
        unfold aggregatePositiveWeight aggregateNegativeWeight
        rw [← positive_sub_negativeHighPassWeight Index degree mask]
        ring
    _ = weightedOrbitMean (highPassWeight Index degree) response /
        aggregateNormalization Index degree :=
      weightedOrbitMean_div _ _ _
    _ = _ := by rw [weightedOrbitMean_highPassWeight]

/-- Multiplicative form of the aggregate identity. -/
theorem signedHighDegreeSum_eq_aggregateNormalization_mul_gap
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (response : BitVector Index → BitVector Index → ℝ)
    (degree : ℕ) (hdegree : degree < Fintype.card Index) :
    signedHighDegreeSum response degree =
      aggregateNormalization Index degree *
        (aggregateAcceptance true response degree -
          aggregateAcceptance false response degree) := by
  rw [aggregateAcceptance_true_sub_false]
  field_simp [ne_of_gt (aggregateNormalization_pos Index degree hdegree)]

/-- Low/high bridge using one aggregate game instead of an absolute posterior spectral tail. -/
theorem diagonalGap_le_lowCount_mul_add_aggregate
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (response : BitVector Index → BitVector Index → ℝ)
    (degree : ℕ) (hdegree : degree < Fintype.card Index) (lowBound : ℝ)
    (hlow : ∀ frequency ∈ lowFrequencies Index degree,
      |fourierCoefficient response frequency frequency| ≤ lowBound) :
    |diagonalMean response - independentMean response| ≤
      lowFrequencyCount Index degree * lowBound +
        aggregateNormalization Index degree *
          |aggregateAcceptance true response degree -
            aggregateAcceptance false response degree| := by
  rw [diagonalFourierIdentity]
  rw [show (Finset.univ.erase (zeroFrequency : BitVector Index)) =
      nonzeroFrequencies Index by rfl]
  rw [sum_nonzero_eq_sum_low_add_sum_high]
  calc
    |(∑ frequency ∈ lowFrequencies Index degree,
          fourierCoefficient response frequency frequency) +
        ∑ frequency ∈ highFrequencies Index degree,
          fourierCoefficient response frequency frequency| ≤
      |(∑ frequency ∈ lowFrequencies Index degree,
          fourierCoefficient response frequency frequency)| +
        |signedHighDegreeSum response degree| := by
      exact abs_add_le _ _
    _ ≤ lowFrequencyCount Index degree * lowBound +
        |signedHighDegreeSum response degree| := by
      gcongr
      exact abs_sum_low_le_count_mul degree _ lowBound hlow
    _ = _ := by
      have hnormalization : 0 ≤ aggregateNormalization Index degree :=
        Finset.sum_nonneg fun mask _ ↦
          positiveHighPassWeight_nonneg Index degree mask
      rw [signedHighDegreeSum_eq_aggregateNormalization_mul_gap
        response degree hdegree, abs_mul, abs_of_nonneg hnormalization]

/-- Add the independent-message/zero-message endpoint to the aggregate bridge. -/
theorem diagonalGap_add_endpoint_le
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (response : BitVector Index → BitVector Index → ℝ)
    (degree : ℕ) (hdegree : degree < Fintype.card Index)
    (lowBound aggregateBound endpoint endpointBound : ℝ)
    (hlow : ∀ frequency ∈ lowFrequencies Index degree,
      |fourierCoefficient response frequency frequency| ≤ lowBound)
    (haggregate :
      |aggregateAcceptance true response degree -
        aggregateAcceptance false response degree| ≤ aggregateBound)
    (hendpoint : endpoint ≤ endpointBound) :
    |diagonalMean response - independentMean response| + endpoint ≤
      lowFrequencyCount Index degree * lowBound +
        aggregateNormalization Index degree * aggregateBound + endpointBound := by
  have hgap := diagonalGap_le_lowCount_mul_add_aggregate
    response degree hdegree lowBound hlow
  have hnormalization : 0 ≤ aggregateNormalization Index degree :=
    Finset.sum_nonneg fun mask _ ↦ positiveHighPassWeight_nonneg Index degree mask
  nlinarith [mul_le_mul_of_nonneg_left haggregate hnormalization]

/-! ## Aggregate containment and the point-oracle separation -/

/-- Algebra of the sign-guess reduction: a fair choice between the positive experiment and the
complement of the negative experiment has exactly half their distinguishing gap from any common
sign-independent reference.  Native xor normalization supplies the cryptographic implementation
of this calculation. -/
theorem signGuessReduction_gap
    (positiveAcceptance negativeAcceptance commonAcceptance : ℝ) :
    |(positiveAcceptance + (1 - negativeAcceptance)) / 2 -
        (commonAcceptance + (1 - commonAcceptance)) / 2| =
      |positiveAcceptance - negativeAcceptance| / 2 := by
  rw [show
      (positiveAcceptance + (1 - negativeAcceptance)) / 2 -
          (commonAcceptance + (1 - commonAcceptance)) / 2 =
        (positiveAcceptance - negativeAcceptance) / 2 by ring,
    abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- Zero-query response of the point-oracle counterexample.  Its hidden point is `secret xor
message`, so querying zero accepts exactly on the diagonal. -/
def pointOracleZeroResponse
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (secret message : BitVector Index) : ℝ :=
  if message = secret then 1 else 0

@[simp]
theorem xorEquiv_eq_self_iff
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (secret mask : BitVector Index) :
    xorEquiv secret mask = secret ↔ mask = zeroFrequency := by
  constructor
  · intro hequal
    apply (xorEquiv secret).injective
    rw [xorEquiv_zeroFrequency]
    exact hequal
  · rintro rfl
    exact xorEquiv_zeroFrequency secret

/-- Against the point-oracle zero query, an arbitrary mask law is observed only through its mass
at zero. -/
theorem weightedOrbitMean_pointOracleZeroResponse
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (weight : BitVector Index → ℝ) :
    weightedOrbitMean weight pointOracleZeroResponse =
      weight (zeroFrequency : BitVector Index) := by
  classical
  unfold weightedOrbitMean pointOracleZeroResponse
  have hinner : ∀ secret : BitVector Index,
      (∑ mask : BitVector Index,
        weight mask * if xorEquiv secret mask = secret then 1 else 0) =
        weight (zeroFrequency : BitVector Index) := by
    intro secret
    simp only [xorEquiv_eq_self_iff]
    simp
  simp_rw [hinner]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hcard : (Fintype.card (BitVector Index) : ℝ) = cubeSize Index := by
    simp [cubeSize]
  rw [hcard]
  field_simp [cubeSize_ne_zero Index]

/-- The point-oracle aggregate gap is the positive high-pass mass at zero divided by `lambda_d`;
the negative law gives zero mass there. -/
theorem pointOracle_aggregateGap_eq
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree < Fintype.card Index) :
    aggregateAcceptance true
        (pointOracleZeroResponse (Index := Index)) degree -
      aggregateAcceptance false
        (pointOracleZeroResponse (Index := Index)) degree =
      (1 - (boundedFrequencies Index degree).card / cubeSize Index) /
        aggregateNormalization Index degree := by
  change
    weightedOrbitMean (aggregatePositiveWeight Index degree)
        pointOracleZeroResponse -
      weightedOrbitMean (aggregateNegativeWeight Index degree)
        pointOracleZeroResponse = _
  rw [weightedOrbitMean_pointOracleZeroResponse,
    weightedOrbitMean_pointOracleZeroResponse]
  have hweight := highPassWeight_zeroFrequency_pos Index degree hdegree
  have hpositive :
      positiveHighPassWeight Index degree (zeroFrequency : BitVector Index) =
        highPassWeight Index degree zeroFrequency := by
    unfold positiveHighPassWeight
    rw [abs_of_pos hweight]
    ring
  have hnegative :
      negativeHighPassWeight Index degree (zeroFrequency : BitVector Index) = 0 := by
    unfold negativeHighPassWeight
    rw [abs_of_pos hweight]
    ring
  unfold aggregatePositiveWeight aggregateNegativeWeight
  rw [hpositive, hnegative, zero_div, sub_zero]
  congr 1
  simp [highPassWeight, lowPassKernel_zeroFrequency, zeroPointWeight]

/-- In particular the aggregate games have a strictly positive one-query gap in the point-oracle
model.  This is the finite algebraic core of the sketch's black-box separation. -/
theorem pointOracle_aggregateGap_pos
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree < Fintype.card Index) :
    0 < aggregateAcceptance true
        (pointOracleZeroResponse (Index := Index)) degree -
      aggregateAcceptance false
        (pointOracleZeroResponse (Index := Index)) degree := by
  rw [pointOracle_aggregateGap_eq degree hdegree]
  apply div_pos
  · exact sub_pos.mpr ((div_lt_one (cubeSize_pos Index)).mpr
      (card_boundedFrequencies_lt_cubeSize Index degree hdegree))
  · exact aggregateNormalization_pos Index degree hdegree

/-! ## Full-key match-and-square complexity leveraging -/

/-- The diagonal plus/minus advantage when the fake key supplied to the constructor is the actual
complete key. -/
def fullKeyAggregateAdvantage
    {Key : Type} (keySampler : ProbComp Key)
    (plus minus : Key → Key → ProbComp Bool) : ℝ :=
  leakedAdvantage keySampler id plus minus

/-- The doubled-source match-and-square advantage with an independently sampled fake key. -/
def fullKeyMatchSquareAdvantage
    {Key : Type} (keySampler fakeKeySampler : ProbComp Key)
    (plus minus : Key → Key → ProbComp Bool) : ℝ :=
  leakageRemovalAdvantage keySampler fakeKeySampler plus minus

/-- Order-`1/2` concentration of the complete key law. -/
def fullKeyConcentration
    {Key : Type} [Fintype Key] (keySampler : ProbComp Key) : ℝ :=
  halfRenyiConcentration (leakageLaw keySampler id)

theorem fullKeyConcentration_nonneg
    {Key : Type} [Fintype Key] (keySampler : ProbComp Key) :
    0 ≤ fullKeyConcentration keySampler := by
  exact sq_nonneg _

/-- The square-root tilted fake-key law is optimal for the match-and-square proof: every covering
fake-key distribution has `Gamma` at least the full-key Renyi-half concentration. -/
theorem fullKeyConcentration_le_leakageGamma
    {Key : Type} [Fintype Key]
    (keySampler fakeKeySampler : ProbComp Key)
    (hcover : ∀ key, probabilityMass keySampler key ≠ 0 →
      probabilityMass fakeKeySampler key ≠ 0) :
    fullKeyConcentration keySampler ≤
      leakageGamma keySampler fakeKeySampler id := by
  classical
  let p : Key → ℝ := fun key ↦
    probabilityMass (leakageLaw keySampler id) key
  let q : Key → ℝ := fun key ↦ probabilityMass fakeKeySampler key
  have hp (key : Key) : 0 ≤ p key := probabilityMass_nonneg _ _
  have hq (key : Key) : 0 ≤ q key := probabilityMass_nonneg _ _
  have hkeyMass (key : Key) :
      probabilityMass keySampler key = p key := by
    simp [p, probabilityMass, leakageLaw]
  have hproduct (key : Key) :
      Real.sqrt (p key / q key) * Real.sqrt (q key) = Real.sqrt (p key) := by
    by_cases hpzero : p key = 0
    · simp [hpzero]
    · have hqzero : q key ≠ 0 := by
        apply hcover key
        rw [hkeyMass]
        exact hpzero
      rw [Real.sqrt_div (hp key)]
      field_simp [(Real.sqrt_ne_zero (hq key)).2 hqzero]
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun key : Key ↦ Real.sqrt (p key / q key))
    (fun key ↦ Real.sqrt (q key))
  have hleft :
      (∑ key : Key, Real.sqrt (p key / q key) * Real.sqrt (q key)) =
        ∑ key : Key, Real.sqrt (p key) := by
    apply Finset.sum_congr rfl
    intro key _
    exact hproduct key
  have hfirst :
      (∑ key : Key, Real.sqrt (p key / q key) ^ 2) =
        ∑ key : Key, p key / q key := by
    apply Finset.sum_congr rfl
    intro key _
    rw [Real.sq_sqrt (div_nonneg (hp key) (hq key))]
  have hsecond :
      (∑ key : Key, Real.sqrt (q key) ^ 2) = 1 := by
    simp_rw [Real.sq_sqrt (hq _)]
    exact sum_probabilityMass_eq_one fakeKeySampler
  have hbound :
      (∑ key : Key, Real.sqrt (p key)) ^ 2 ≤
        ∑ key : Key, p key / q key := by
    simpa only [hleft, hfirst, hsecond, mul_one] using hcauchy
  unfold fullKeyConcentration halfRenyiConcentration
  rw [leakageGamma_eq_sum_ratio]
  exact hbound

/-- Match-and-square theorem.  The optimized fake-key law is proportional to the square root of
the complete key mass; existence and efficient sampling of that law are explicit premises. -/
theorem fullKeyAggregateAdvantage_le_sqrt_matchSquare
    {Key : Type} [Fintype Key]
    (keySampler fakeKeySampler : ProbComp Key)
    (plus minus : Key → Key → ProbComp Bool)
    (hcover : ∀ key, probabilityMass keySampler key ≠ 0 →
      probabilityMass fakeKeySampler key ≠ 0)
    (hoptimized : ∀ key,
      probabilityMass fakeKeySampler key =
        Real.sqrt (probabilityMass (leakageLaw keySampler id) key) /
          halfRenyiNormalizer keySampler id) :
    fullKeyAggregateAdvantage keySampler plus minus ≤
      Real.sqrt (2 * fullKeyConcentration keySampler *
        fullKeyMatchSquareAdvantage keySampler fakeKeySampler plus minus) := by
  unfold fullKeyAggregateAdvantage fullKeyConcentration
    fullKeyMatchSquareAdvantage
  rw [← leakageGamma_eq_halfRenyiConcentration_of_optimizedLaw
    keySampler fakeKeySampler id hoptimized]
  exact leakedAdvantage_le_sqrt_two_mul_gamma_mul_removal
    keySampler fakeKeySampler id plus minus hcover

/-- Approximate diagonal construction plus a zero-row source bound.  This is the corollary with
defects `sigmaPlus + sigmaMinus` from the note. -/
theorem nativeAggregateGap_le_defects_add_sqrt
    {Key : Type} [Fintype Key]
    (keySampler fakeKeySampler : ProbComp Key)
    (plus minus : Key → Key → ProbComp Bool)
    (nativeAggregateGap sigmaPlus sigmaMinus sourceBound : ℝ)
    (hdiagonal : nativeAggregateGap ≤ sigmaPlus + sigmaMinus +
      fullKeyAggregateAdvantage keySampler plus minus)
    (hsource : fullKeyMatchSquareAdvantage
      keySampler fakeKeySampler plus minus ≤ sourceBound)
    (hcover : ∀ key, probabilityMass keySampler key ≠ 0 →
      probabilityMass fakeKeySampler key ≠ 0)
    (hoptimized : ∀ key,
      probabilityMass fakeKeySampler key =
        Real.sqrt (probabilityMass (leakageLaw keySampler id) key) /
          halfRenyiNormalizer keySampler id) :
    nativeAggregateGap ≤ sigmaPlus + sigmaMinus +
      Real.sqrt (2 * fullKeyConcentration keySampler * sourceBound) := by
  have hmatch := fullKeyAggregateAdvantage_le_sqrt_matchSquare
    keySampler fakeKeySampler plus minus hcover hoptimized
  have hconcentration := fullKeyConcentration_nonneg keySampler
  have hradicand :
      2 * fullKeyConcentration keySampler *
          fullKeyMatchSquareAdvantage keySampler fakeKeySampler plus minus ≤
        2 * fullKeyConcentration keySampler * sourceBound := by
    exact mul_le_mul_of_nonneg_left hsource
      (mul_nonneg (by norm_num) hconcentration)
  calc
    nativeAggregateGap ≤ sigmaPlus + sigmaMinus +
        fullKeyAggregateAdvantage keySampler plus minus := hdiagonal
    _ ≤ sigmaPlus + sigmaMinus +
        Real.sqrt (2 * fullKeyConcentration keySampler *
          fullKeyMatchSquareAdvantage keySampler fakeKeySampler plus minus) := by
      gcongr
    _ ≤ sigmaPlus + sigmaMinus +
        Real.sqrt (2 * fullKeyConcentration keySampler * sourceBound) := by
      gcongr

/-- Final native complexity-leveraged composition theorem.  `hlow` is supplied by the doubled
complete heterogeneous affine-source reduction; `hdiagonal` is the complete-view aggregate
constructor; and `hsource` is its doubled zero-row RLWE security bound. -/
theorem nativeCircularSecurity_with_complexityLeveraging
    {Index Key : Type} [Fintype Index] [DecidableEq Index] [Fintype Key]
    (response : BitVector Index → BitVector Index → ℝ)
    (degree : ℕ) (hdegree : degree < Fintype.card Index)
    (affineBound endpoint endpointBound sigmaPlus sigmaMinus sourceBound : ℝ)
    (keySampler fakeKeySampler : ProbComp Key)
    (plus minus : Key → Key → ProbComp Bool)
    (hlow : ∀ frequency ∈ lowFrequencies Index degree,
      |fourierCoefficient response frequency frequency| ≤
        Real.sqrt ((2 : ℝ) ^ (degree + 1) * affineBound))
    (hdiagonal :
      |aggregateAcceptance true response degree -
          aggregateAcceptance false response degree| ≤
        sigmaPlus + sigmaMinus +
          fullKeyAggregateAdvantage keySampler plus minus)
    (hsource : fullKeyMatchSquareAdvantage
      keySampler fakeKeySampler plus minus ≤ sourceBound)
    (hendpoint : endpoint ≤ endpointBound)
    (hcover : ∀ key, probabilityMass keySampler key ≠ 0 →
      probabilityMass fakeKeySampler key ≠ 0)
    (hoptimized : ∀ key,
      probabilityMass fakeKeySampler key =
        Real.sqrt (probabilityMass (leakageLaw keySampler id) key) /
          halfRenyiNormalizer keySampler id) :
    |diagonalMean response - independentMean response| + endpoint ≤
      lowFrequencyCount Index degree *
          Real.sqrt ((2 : ℝ) ^ (degree + 1) * affineBound) +
        aggregateNormalization Index degree *
          (sigmaPlus + sigmaMinus +
            Real.sqrt (2 * fullKeyConcentration keySampler * sourceBound)) +
        endpointBound := by
  have haggregate := nativeAggregateGap_le_defects_add_sqrt
    keySampler fakeKeySampler plus minus
    |aggregateAcceptance true response degree -
      aggregateAcceptance false response degree|
    sigmaPlus sigmaMinus sourceBound hdiagonal hsource hcover hoptimized
  exact diagonalGap_add_endpoint_le response degree hdegree
    (Real.sqrt ((2 : ℝ) ^ (degree + 1) * affineBound))
    (sigmaPlus + sigmaMinus +
      Real.sqrt (2 * fullKeyConcentration keySampler * sourceBound))
    endpoint endpointBound hlow haggregate hendpoint

/-! ### Concrete full-key concentration factors -/

theorem probabilityMass_leakageLaw_id
    {Key : Type} [Fintype Key] (keySampler : ProbComp Key) (key : Key) :
    probabilityMass (leakageLaw keySampler id) key =
      probabilityMass keySampler key := by
  simp [probabilityMass, leakageLaw]

theorem fullKeyConcentration_eq_halfRenyiConcentration
    {Key : Type} [Fintype Key] (keySampler : ProbComp Key) :
    fullKeyConcentration keySampler = halfRenyiConcentration keySampler := by
  unfold fullKeyConcentration halfRenyiConcentration
  congr 2
  funext key
  rw [probabilityMass_leakageLaw_id]

/-- Uniform independent binary-prefix/ternary-suffix keys have the exponential factor
`2^prefixCount * 3^suffixCount`. -/
theorem fullKeyConcentration_uniform_binary_ternary
    (prefixCount suffixCount : ℕ) :
    fullKeyConcentration
        ($ᵗ ((Fin prefixCount → Bool) × (Fin suffixCount → Fin 3))) =
      2 ^ prefixCount * 3 ^ suffixCount := by
  rw [fullKeyConcentration_eq_halfRenyiConcentration,
    halfRenyiConcentration_uniform]
  simp [Fintype.card_prod]

end

end FormalProof4FHE.TFHE.NativeTRGSWAggregateSecurityAndComplexityLeveraging
