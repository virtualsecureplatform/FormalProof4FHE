/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeTRGSWAggregateProjectedLeakage

/-!
# Support-sensitive aggregate accounting and robust projected leakage

This module records two quantitative refinements of the native-TRGSW aggregate argument.

First, the low-frequency bridge retains an individual bound for every Walsh support instead of
replacing all of them by one maximum.  Bounds depending only on support size are then grouped by
the exact binomial multiplicity.

Second, the exact translation-stabilizer obstruction is strengthened to an `L¹` separation
theorem.  Whenever a translation flips one retained high-pass Walsh character, the two normalized
Jordan laws cannot both be approximately invariant.  This is the analytic input needed for a
robust approximate-leakage recovery theorem.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.NativeTRGSWAggregateRobustLeakage

noncomputable section

open NativeTRGSWBarrierAndSpectralBoundary
open NativeTRGSWCompleteChannel
open NativeTRGSWAggregateSecurityAndComplexityLeveraging
open NativeTRGSWAggregateConcreteChannel
open NativeTRGSWAggregateProjectedLeakage

/-! ## Support-sensitive low-frequency accounting -/

/-- The low-frequency triangle bound with a separate nonnegative budget for every frequency. -/
theorem abs_sum_low_le_sum_bounds
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (coefficient bound : BitVector Index → ℝ)
    (hbound : ∀ frequency ∈ lowFrequencies Index degree,
      |coefficient frequency| ≤ bound frequency) :
    |∑ frequency ∈ lowFrequencies Index degree, coefficient frequency| ≤
      ∑ frequency ∈ lowFrequencies Index degree, bound frequency := by
  calc
    |∑ frequency ∈ lowFrequencies Index degree, coefficient frequency| ≤
        ∑ frequency ∈ lowFrequencies Index degree, |coefficient frequency| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := Finset.sum_le_sum fun frequency hfrequency ↦
      hbound frequency hfrequency

/-- Low/high aggregate bridge without replacing the individual low-frequency bounds by their
maximum. -/
theorem diagonalGap_le_sum_lowBounds_add_aggregate
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (response : BitVector Index → BitVector Index → ℝ)
    (degree : ℕ) (hdegree : degree < Fintype.card Index)
    (lowBound : BitVector Index → ℝ)
    (hlow : ∀ frequency ∈ lowFrequencies Index degree,
      |fourierCoefficient response frequency frequency| ≤ lowBound frequency) :
    |diagonalMean response - independentMean response| ≤
      (∑ frequency ∈ lowFrequencies Index degree, lowBound frequency) +
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
        |signedHighDegreeSum response degree| := abs_add_le _ _
    _ ≤ (∑ frequency ∈ lowFrequencies Index degree, lowBound frequency) +
        |signedHighDegreeSum response degree| := by
      gcongr
      exact abs_sum_low_le_sum_bounds degree _ lowBound hlow
    _ = _ := by
      have hnormalization : 0 ≤ aggregateNormalization Index degree :=
        Finset.sum_nonneg fun mask _ ↦
          positiveHighPassWeight_nonneg Index degree mask
      rw [signedHighDegreeSum_eq_aggregateNormalization_mul_gap
        response degree hdegree, abs_mul, abs_of_nonneg hnormalization]

/-- Support-size specialization of the individual low-frequency bridge. -/
theorem diagonalGap_le_supportSizeBounds_add_aggregate
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (response : BitVector Index → BitVector Index → ℝ)
    (degree : ℕ) (hdegree : degree < Fintype.card Index)
    (supportBound : ℕ → ℝ)
    (hlow : ∀ frequency ∈ lowFrequencies Index degree,
      |fourierCoefficient response frequency frequency| ≤
        supportBound (supportSize frequency)) :
    |diagonalMean response - independentMean response| ≤
      (∑ frequency ∈ lowFrequencies Index degree,
        supportBound (supportSize frequency)) +
        aggregateNormalization Index degree *
          |aggregateAcceptance true response degree -
            aggregateAcceptance false response degree| := by
  exact diagonalGap_le_sum_lowBounds_add_aggregate
    response degree hdegree (fun frequency ↦ supportBound (supportSize frequency)) hlow

/-- Reindex a support-size-dependent sum from indicator words to their nonempty finite
supports. -/
theorem sum_lowFrequencies_supportBound_eq_lowSubsetFamily
    (Index : Type) [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (supportBound : ℕ → ℝ) :
    (∑ frequency ∈ lowFrequencies Index degree,
        supportBound (supportSize frequency)) =
      ∑ support ∈ lowSubsetFamily Index degree,
        supportBound support.card := by
  classical
  apply Finset.sum_bij
      (fun frequency _ ↦ frequencySupport frequency)
  · intro frequency hfrequency
    rcases Finset.mem_filter.mp hfrequency with ⟨hnonzero, hsize⟩
    have hfrequency_ne : frequency ≠ (zeroFrequency : BitVector Index) :=
      (Finset.mem_erase.mp hnonzero).1
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_, ?_⟩
    · exact Finset.nonempty_iff_ne_empty.mpr fun hempty ↦
        hfrequency_ne ((frequencySupport_eq_empty_iff frequency).mp hempty)
    · exact hsize
  · intro first _ second _ hequal
    exact (frequencyFinsetEquiv Index).injective hequal
  · intro support hsupport
    rcases Finset.mem_filter.mp hsupport with ⟨_, hnonempty, hcard⟩
    let frequency := (frequencyFinsetEquiv Index).symm support
    have hfrequencySupport : frequencySupport frequency = support :=
      (frequencyFinsetEquiv Index).apply_symm_apply support
    have hfrequency_ne : frequency ≠ (zeroFrequency : BitVector Index) := by
      intro hzero
      rw [hzero, frequencySupport_zeroFrequency] at hfrequencySupport
      exact hnonempty.ne_empty hfrequencySupport.symm
    refine ⟨frequency, ?_, hfrequencySupport⟩
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_erase.mpr ⟨hfrequency_ne, Finset.mem_univ _⟩, ?_⟩
    unfold supportSize
    rw [hfrequencySupport]
    exact hcard
  · intro frequency _
    rfl

/-- Exact binomial grouping of a bound depending only on Walsh support size. -/
theorem sum_lowSubsetFamily_supportBound_eq_binomial
    (Index : Type) [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (supportBound : ℕ → ℝ) :
    (∑ support ∈ lowSubsetFamily Index degree,
        supportBound support.card) =
      ∑ cardinality ∈ Finset.Icc 1 degree,
        (Nat.choose (Fintype.card Index) cardinality : ℝ) *
          supportBound cardinality := by
  classical
  have hmaps :
      ((lowSubsetFamily Index degree : Finset (Finset Index)) : Set (Finset Index)).MapsTo
        Finset.card (Finset.Icc 1 degree) := by
    intro support hsupport
    rcases Finset.mem_filter.mp hsupport with ⟨_, hnonempty, hcard⟩
    exact Finset.mem_Icc.mpr ⟨Finset.card_pos.mpr hnonempty, hcard⟩
  calc
    (∑ support ∈ lowSubsetFamily Index degree, supportBound support.card) =
        ∑ cardinality ∈ Finset.Icc 1 degree,
          ∑ support ∈ lowSubsetFamily Index degree with support.card = cardinality,
            supportBound support.card :=
      (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro cardinality hcardinality
      have hfiber :
          (lowSubsetFamily Index degree).filter
              (fun support ↦ support.card = cardinality) =
            (Finset.univ : Finset Index).powersetCard cardinality := by
        ext support
        rcases Finset.mem_Icc.mp hcardinality with ⟨hpositive, hdegree⟩
        simp only [lowSubsetFamily, Finset.mem_filter, Finset.mem_univ, true_and,
          Finset.mem_powersetCard, Finset.subset_univ]
        constructor
        · rintro ⟨_, hequal⟩
          exact hequal
        · intro hequal
          have hsupportPositive : 0 < support.card := by omega
          exact ⟨⟨Finset.card_pos.mp hsupportPositive, by omega⟩, hequal⟩
      rw [show (∑ support ∈ lowSubsetFamily Index degree with
          support.card = cardinality, supportBound support.card) =
          ∑ support ∈ (lowSubsetFamily Index degree).filter
            (fun support ↦ support.card = cardinality),
              supportBound support.card by rfl]
      rw [hfiber]
      calc
        (∑ support ∈ (Finset.univ : Finset Index).powersetCard cardinality,
            supportBound support.card) =
          ∑ _support ∈ (Finset.univ : Finset Index).powersetCard cardinality,
            supportBound cardinality := by
              apply Finset.sum_congr rfl
              intro support hsupport
              rw [(Finset.mem_powersetCard.mp hsupport).2]
        _ = _ := by simp

/-- Fully grouped support-sensitive aggregate bridge. -/
theorem diagonalGap_le_binomialSupportBounds_add_aggregate
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (response : BitVector Index → BitVector Index → ℝ)
    (degree : ℕ) (hdegree : degree < Fintype.card Index)
    (supportBound : ℕ → ℝ)
    (hlow : ∀ frequency ∈ lowFrequencies Index degree,
      |fourierCoefficient response frequency frequency| ≤
        supportBound (supportSize frequency)) :
    |diagonalMean response - independentMean response| ≤
      (∑ cardinality ∈ Finset.Icc 1 degree,
        (Nat.choose (Fintype.card Index) cardinality : ℝ) *
          supportBound cardinality) +
        aggregateNormalization Index degree *
          |aggregateAcceptance true response degree -
            aggregateAcceptance false response degree| := by
  rw [← sum_lowSubsetFamily_supportBound_eq_binomial Index degree supportBound,
    ← sum_lowFrequencies_supportBound_eq_lowSubsetFamily Index degree supportBound]
  exact diagonalGap_le_supportSizeBounds_add_aggregate
    response degree hdegree supportBound hlow

/-- The existing affine-source certificate already contains a sharper bound than its uniform
`degree` wrapper: leakage removal pays the actual support size of each frequency. -/
theorem supportSizeLowFrequencyBound_of_certificate
    {Index View : Type} [Fintype Index] [DecidableEq Index]
    [SampleableType (BitVector Index)] [Fintype View]
    {channel : CompleteChannel Index View} {response : View → ℝ}
    {degree : ℕ} {delta : ℝ}
    (certificate : LowDegreeAffineSourceCertificate channel response degree delta)
    (frequency : BitVector Index) (hfrequency : frequency ∈ lowFrequencies Index degree) :
    |fourierCoefficient (completeChannelResponse channel response) frequency frequency| ≤
      Real.sqrt ((2 : ℝ) ^ (supportSize frequency + 1) * delta) := by
  exact (certificate.coefficient_le frequency hfrequency).trans
    (supportLeakageRemoval_binaryBound frequency (supportSize frequency)
      (certificate.real frequency) (certificate.ideal frequency) delta (le_refl _)
      (certificate.removal_le frequency hfrequency))

/-- Install an affine-source certificate directly into the support-sensitive aggregate bridge. -/
theorem diagonalGap_le_affineCertificateSupportBounds_add_aggregate
    {Index View : Type} [Fintype Index] [DecidableEq Index]
    [SampleableType (BitVector Index)] [Fintype View]
    (channel : CompleteChannel Index View) (response : View → ℝ)
    (degree : ℕ) (hdegree : degree < Fintype.card Index) (delta : ℝ)
    (certificate : LowDegreeAffineSourceCertificate channel response degree delta) :
    |diagonalMean (completeChannelResponse channel response) -
        independentMean (completeChannelResponse channel response)| ≤
      (∑ cardinality ∈ Finset.Icc 1 degree,
        (Nat.choose (Fintype.card Index) cardinality : ℝ) *
          Real.sqrt ((2 : ℝ) ^ (cardinality + 1) * delta)) +
        aggregateNormalization Index degree *
          |aggregateAcceptance true (completeChannelResponse channel response) degree -
            aggregateAcceptance false (completeChannelResponse channel response) degree| := by
  exact diagonalGap_le_binomialSupportBounds_add_aggregate
    (completeChannelResponse channel response) degree hdegree
    (fun cardinality ↦ Real.sqrt ((2 : ℝ) ^ (cardinality + 1) * delta))
    (supportSizeLowFrequencyBound_of_certificate certificate)

/-- Support-sensitive bridge for executable aggregate experiments approximating the two ideal
Jordan laws. -/
theorem diagonalGap_le_binomialSupportBounds_add_approximateAggregate
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (response : BitVector Index → BitVector Index → ℝ)
    (degree : ℕ) (hdegree : degree < Fintype.card Index)
    (supportBound : ℕ → ℝ)
    (actualPositive actualNegative positiveDefect negativeDefect : ℝ)
    (hlow : ∀ frequency ∈ lowFrequencies Index degree,
      |fourierCoefficient response frequency frequency| ≤
        supportBound (supportSize frequency))
    (hpositive : |actualPositive - aggregateAcceptance true response degree| ≤
      positiveDefect)
    (hnegative : |actualNegative - aggregateAcceptance false response degree| ≤
      negativeDefect) :
    |diagonalMean response - independentMean response| ≤
      (∑ cardinality ∈ Finset.Icc 1 degree,
        (Nat.choose (Fintype.card Index) cardinality : ℝ) *
          supportBound cardinality) +
        aggregateNormalization Index degree *
          (|actualPositive - actualNegative| + positiveDefect + negativeDefect) := by
  have hbase := diagonalGap_le_binomialSupportBounds_add_aggregate
    response degree hdegree supportBound hlow
  have hgap := abs_ideal_gap_le_actual_gap_add_defects
    (aggregateAcceptance true response degree)
    (aggregateAcceptance false response degree)
    actualPositive actualNegative positiveDefect negativeDefect hpositive hnegative
  have hnormalization : 0 ≤ aggregateNormalization Index degree :=
    Finset.sum_nonneg fun mask _ ↦
      positiveHighPassWeight_nonneg Index degree mask
  exact hbase.trans
    (add_le_add_right (mul_le_mul_of_nonneg_left hgap hnormalization) _)

/-- Add an independently bounded endpoint without collapsing the support-dependent budgets. -/
theorem diagonalGap_add_endpoint_le_binomialSupportBounds
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (response : BitVector Index → BitVector Index → ℝ)
    (degree : ℕ) (hdegree : degree < Fintype.card Index)
    (supportBound : ℕ → ℝ)
    (aggregateBound endpoint endpointBound : ℝ)
    (hlow : ∀ frequency ∈ lowFrequencies Index degree,
      |fourierCoefficient response frequency frequency| ≤
        supportBound (supportSize frequency))
    (haggregate :
      |aggregateAcceptance true response degree -
        aggregateAcceptance false response degree| ≤ aggregateBound)
    (hendpoint : endpoint ≤ endpointBound) :
    |diagonalMean response - independentMean response| + endpoint ≤
      (∑ cardinality ∈ Finset.Icc 1 degree,
        (Nat.choose (Fintype.card Index) cardinality : ℝ) *
          supportBound cardinality) +
        aggregateNormalization Index degree * aggregateBound + endpointBound := by
  have hgap := diagonalGap_le_binomialSupportBounds_add_aggregate
    response degree hdegree supportBound hlow
  have hnormalization : 0 ≤ aggregateNormalization Index degree :=
    Finset.sum_nonneg fun mask _ ↦
      positiveHighPassWeight_nonneg Index degree mask
  nlinarith [mul_le_mul_of_nonneg_left haggregate hnormalization]

/-! ## Quantitative translation separation -/

/-- `L¹` distance between two finite real tables.  Unlike `tvDist`, this definition also applies
to signed tables such as the canonical high-pass measure. -/
def tableL1Distance
    {A : Type} [Fintype A] (left right : A → ℝ) : ℝ :=
  ∑ value, |left value - right value|

theorem tableL1Distance_nonneg
    {A : Type} [Fintype A] (left right : A → ℝ) :
    0 ≤ tableL1Distance left right := by
  exact Finset.sum_nonneg fun value _ ↦ abs_nonneg _

theorem tableL1Distance_triangle
    {A : Type} [Fintype A] (left middle right : A → ℝ) :
    tableL1Distance left right ≤
      tableL1Distance left middle + tableL1Distance middle right := by
  unfold tableL1Distance
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun value _ ↦
    abs_sub_le (left value) (middle value) (right value)

theorem tableL1Distance_comm
    {A : Type} [Fintype A] (left right : A → ℝ) :
    tableL1Distance left right = tableL1Distance right left := by
  unfold tableL1Distance
  apply Finset.sum_congr rfl
  intro value _
  exact abs_sub_comm (left value) (right value)

/-- Translate a real table on the binary cube. -/
def translateTable
    {Index : Type} (shift : BitVector Index)
    (weight : BitVector Index → ℝ) : BitVector Index → ℝ :=
  fun word ↦ weight (xorEquiv shift word)

/-- `L¹` failure of translation invariance. -/
def translationL1Defect
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (weight : BitVector Index → ℝ) (shift : BitVector Index) : ℝ :=
  tableL1Distance (translateTable shift weight) weight

/-- Walsh transform of a translated table. -/
theorem walshTransform_translateTable
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (weight : BitVector Index → ℝ) (shift frequency : BitVector Index) :
    walshTransform (translateTable shift weight) frequency =
      walsh frequency shift * walshTransform weight frequency := by
  classical
  unfold walshTransform translateTable
  calc
    (∑ word : BitVector Index,
        weight (xorEquiv shift word) * walsh frequency word) =
      ∑ word : BitVector Index,
        weight (xorEquiv shift (xorEquiv shift word)) *
          walsh frequency (xorEquiv shift word) :=
      ((xorEquiv shift).sum_comp
        (fun word ↦ weight (xorEquiv shift word) * walsh frequency word)).symm
    _ = ∑ word : BitVector Index,
        weight word * (walsh frequency shift * walsh frequency word) := by
      apply Finset.sum_congr rfl
      intro word _
      rw [← xorEquiv_assoc, xorEquiv_self, xorEquiv_zero_left]
      rw [show walsh frequency (xorEquiv shift word) =
          walsh frequency shift * walsh frequency word by
        simpa [xorEquiv] using walsh_maskedBit frequency shift word]
    _ = walsh frequency shift *
        ∑ word : BitVector Index, weight word * walsh frequency word := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro word _
      ring

/-- A bounded Walsh character turns transform difference into a lower bound on table `L¹`
distance. -/
theorem abs_walshTransform_sub_le_tableL1Distance
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (left right : BitVector Index → ℝ) (frequency : BitVector Index) :
    |walshTransform left frequency - walshTransform right frequency| ≤
      tableL1Distance left right := by
  unfold walshTransform tableL1Distance
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ word : BitVector Index,
        (left word * walsh frequency word -
          right word * walsh frequency word)| ≤
      ∑ word : BitVector Index,
        |left word * walsh frequency word -
          right word * walsh frequency word| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ word : BitVector Index, |left word - right word| := by
      apply Finset.sum_congr rfl
      intro word _
      rw [← sub_mul, abs_mul, abs_walsh, mul_one]

/-- Flipping one retained high-pass character forces `L¹` translation defect at least two for
the unnormalized signed high-pass table. -/
theorem two_le_translationL1Defect_highPassWeight
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (shift frequency : BitVector Index)
    (hfrequency : frequency ∉ boundedFrequencies Index degree)
    (hflip : walsh frequency shift = -1) :
    (2 : ℝ) ≤ translationL1Defect (highPassWeight Index degree) shift := by
  have hbound := abs_walshTransform_sub_le_tableL1Distance
    (translateTable shift (highPassWeight Index degree))
    (highPassWeight Index degree) frequency
  rw [walshTransform_translateTable,
    walshTransform_highPassWeight, if_neg hfrequency, hflip] at hbound
  norm_num [translationL1Defect] at hbound ⊢
  exact hbound

/-- The signed high-pass table is the common Jordan normalization times the difference of its
two normalized probability tables. -/
theorem highPassWeight_eq_normalization_mul_aggregateDifference
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree < Fintype.card Index)
    (word : BitVector Index) :
    highPassWeight Index degree word =
      aggregateNormalization Index degree *
        (aggregatePositiveWeight Index degree word -
          aggregateNegativeWeight Index degree word) := by
  have hnormalization : aggregateNormalization Index degree ≠ 0 :=
    ne_of_gt (aggregateNormalization_pos Index degree hdegree)
  unfold aggregatePositiveWeight aggregateNegativeWeight
  rw [← positive_sub_negativeHighPassWeight]
  field_simp

/-- Translating the signed table costs at most the common normalization times the sum of the two
normalized Jordan translation defects. -/
theorem translationL1Defect_highPassWeight_le_normalization_mul
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree < Fintype.card Index)
    (shift : BitVector Index) :
    translationL1Defect (highPassWeight Index degree) shift ≤
      aggregateNormalization Index degree *
        (translationL1Defect (aggregatePositiveWeight Index degree) shift +
          translationL1Defect (aggregateNegativeWeight Index degree) shift) := by
  have hnormalization : 0 ≤ aggregateNormalization Index degree :=
    le_of_lt (aggregateNormalization_pos Index degree hdegree)
  unfold translationL1Defect tableL1Distance translateTable
  calc
    (∑ word : BitVector Index,
        |highPassWeight Index degree (xorEquiv shift word) -
          highPassWeight Index degree word|) =
      ∑ word : BitVector Index,
        |aggregateNormalization Index degree *
          ((aggregatePositiveWeight Index degree (xorEquiv shift word) -
              aggregatePositiveWeight Index degree word) -
            (aggregateNegativeWeight Index degree (xorEquiv shift word) -
              aggregateNegativeWeight Index degree word))| := by
        apply Finset.sum_congr rfl
        intro word _
        rw [highPassWeight_eq_normalization_mul_aggregateDifference degree hdegree,
          highPassWeight_eq_normalization_mul_aggregateDifference degree hdegree]
        congr 1
        ring
    _ ≤ ∑ word : BitVector Index,
        aggregateNormalization Index degree *
          (|aggregatePositiveWeight Index degree (xorEquiv shift word) -
              aggregatePositiveWeight Index degree word| +
            |aggregateNegativeWeight Index degree (xorEquiv shift word) -
              aggregateNegativeWeight Index degree word|) := by
        apply Finset.sum_le_sum
        intro word _
        rw [abs_mul, abs_of_nonneg hnormalization]
        apply mul_le_mul_of_nonneg_left _ hnormalization
        let positiveDifference :=
          aggregatePositiveWeight Index degree (xorEquiv shift word) -
            aggregatePositiveWeight Index degree word
        let negativeDifference :=
          aggregateNegativeWeight Index degree (xorEquiv shift word) -
            aggregateNegativeWeight Index degree word
        change |positiveDifference - negativeDifference| ≤
          |positiveDifference| + |negativeDifference|
        calc
          |positiveDifference - negativeDifference| =
              |positiveDifference + (-negativeDifference)| := by
                rw [sub_eq_add_neg]
          _ ≤ |positiveDifference| + |-negativeDifference| := abs_add_le _ _
          _ = _ := by rw [abs_neg]
    _ = aggregateNormalization Index degree *
        ((∑ word : BitVector Index,
            |aggregatePositiveWeight Index degree (xorEquiv shift word) -
              aggregatePositiveWeight Index degree word|) +
          ∑ word : BitVector Index,
            |aggregateNegativeWeight Index degree (xorEquiv shift word) -
              aggregateNegativeWeight Index degree word|) := by
        calc
          (∑ word : BitVector Index,
              aggregateNormalization Index degree *
                (|aggregatePositiveWeight Index degree (xorEquiv shift word) -
                    aggregatePositiveWeight Index degree word| +
                  |aggregateNegativeWeight Index degree (xorEquiv shift word) -
                    aggregateNegativeWeight Index degree word|)) =
            (∑ word : BitVector Index,
                aggregateNormalization Index degree *
                  |aggregatePositiveWeight Index degree (xorEquiv shift word) -
                    aggregatePositiveWeight Index degree word|) +
              ∑ word : BitVector Index,
                aggregateNormalization Index degree *
                  |aggregateNegativeWeight Index degree (xorEquiv shift word) -
                    aggregateNegativeWeight Index degree word| := by
              simp only [mul_add, Finset.sum_add_distrib]
          _ = aggregateNormalization Index degree *
                (∑ word : BitVector Index,
                  |aggregatePositiveWeight Index degree (xorEquiv shift word) -
                    aggregatePositiveWeight Index degree word|) +
              aggregateNormalization Index degree *
                (∑ word : BitVector Index,
                  |aggregateNegativeWeight Index degree (xorEquiv shift word) -
                    aggregateNegativeWeight Index degree word|) := by
              rw [Finset.mul_sum, Finset.mul_sum]
          _ = _ := by ring

/-- Quantitative robust stabilizer theorem.  If a shift flips any retained high-pass Walsh
character, the sum of the positive and negative normalized translation defects cannot be small. -/
theorem two_le_normalization_mul_sum_translationL1Defects
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree < Fintype.card Index)
    (shift frequency : BitVector Index)
    (hfrequency : frequency ∉ boundedFrequencies Index degree)
    (hflip : walsh frequency shift = -1) :
    (2 : ℝ) ≤ aggregateNormalization Index degree *
      (translationL1Defect (aggregatePositiveWeight Index degree) shift +
        translationL1Defect (aggregateNegativeWeight Index degree) shift) := by
  exact (two_le_translationL1Defect_highPassWeight
    degree shift frequency hfrequency hflip).trans
      (translationL1Defect_highPassWeight_le_normalization_mul
        degree hdegree shift)

/-! ## Robust phase-oblivious leakage collision bound -/

/-- The target plaintext law obtained by translating one of the canonical aggregate mask laws by
a binary prefix. -/
def aggregatePlaintextTarget
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (positive : Bool) (degree : ℕ) (prefixKey : BitVector Index) :
    BitVector Index → ℝ :=
  fun message ↦ aggregateMaskWeight positive Index degree
    (xorEquiv prefixKey message)

/-- Complete-table `L¹` defect at a specified leakage value.  Keeping the value explicit also
covers randomized leakage kernels. -/
def phaseObliviousPlaintextL1DefectAt
    {Index Key Leakage : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (prefixValue : Key → BitVector Index)
    (plaintextLaw : Bool → Leakage → BitVector Index → ℝ)
    (positive : Bool) (key : Key) (leakageValue : Leakage) : ℝ :=
  tableL1Distance (plaintextLaw positive leakageValue)
    (aggregatePlaintextTarget positive degree (prefixValue key))

/-- Pointwise complete-table `L¹` defect for deterministic leakage. -/
def phaseObliviousPlaintextL1Defect
    {Index Key Leakage : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (prefixValue : Key → BitVector Index) (leakage : Key → Leakage)
    (plaintextLaw : Bool → Leakage → BitVector Index → ℝ)
    (positive : Bool) (key : Key) : ℝ :=
  phaseObliviousPlaintextL1DefectAt
    degree prefixValue plaintextLaw positive key (leakage key)

theorem phaseObliviousPlaintextL1DefectAt_nonneg
    {Index Key Leakage : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (prefixValue : Key → BitVector Index)
    (plaintextLaw : Bool → Leakage → BitVector Index → ℝ)
    (positive : Bool) (key : Key) (leakageValue : Leakage) :
    0 ≤ phaseObliviousPlaintextL1DefectAt
      degree prefixValue plaintextLaw positive key leakageValue := by
  exact tableL1Distance_nonneg _ _

/-- Reindexing two translated plaintext targets exposes precisely the translation defect of the
underlying mask table. -/
theorem tableL1Distance_xorTargets_eq_translationL1Defect
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (weight : BitVector Index → ℝ) (firstPrefix secondPrefix : BitVector Index) :
    tableL1Distance
        (fun message ↦ weight (xorEquiv secondPrefix message))
        (fun message ↦ weight (xorEquiv firstPrefix message)) =
      translationL1Defect weight (xorEquiv firstPrefix secondPrefix) := by
  classical
  unfold tableL1Distance translationL1Defect translateTable
  calc
    (∑ message : BitVector Index,
        |weight (xorEquiv secondPrefix message) -
          weight (xorEquiv firstPrefix message)|) =
      ∑ word : BitVector Index,
        |weight (xorEquiv secondPrefix (xorEquiv firstPrefix word)) -
          weight (xorEquiv firstPrefix (xorEquiv firstPrefix word))| :=
      ((xorEquiv firstPrefix).sum_comp
        (fun message ↦
          |weight (xorEquiv secondPrefix message) -
            weight (xorEquiv firstPrefix message)|)).symm
    _ = ∑ word : BitVector Index,
        |weight (xorEquiv (xorEquiv firstPrefix secondPrefix) word) -
          weight word| := by
      apply Finset.sum_congr rfl
      intro word _
      have hsecond :
          xorEquiv secondPrefix (xorEquiv firstPrefix word) =
            xorEquiv (xorEquiv firstPrefix secondPrefix) word := by
        calc
          xorEquiv secondPrefix (xorEquiv firstPrefix word) =
              xorEquiv (xorEquiv secondPrefix firstPrefix) word := by
            rw [xorEquiv_assoc]
          _ = xorEquiv (xorEquiv firstPrefix secondPrefix) word := by
            rw [xorEquiv_comm secondPrefix firstPrefix]
      have hfirst :
          xorEquiv firstPrefix (xorEquiv firstPrefix word) = word := by
        rw [← xorEquiv_assoc, xorEquiv_self, xorEquiv_zero_left]
      rw [hsecond, hfirst]

/-- Same translation-defect triangle bound at an explicitly shared leakage value. -/
theorem translationL1Defect_aggregateMaskWeight_le_phaseDefectsAt
    {Index Key Leakage : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (prefixValue : Key → BitVector Index)
    (plaintextLaw : Bool → Leakage → BitVector Index → ℝ)
    (positive : Bool) (first second : Key) (leakageValue : Leakage) :
    translationL1Defect (aggregateMaskWeight positive Index degree)
        (xorEquiv (prefixValue first) (prefixValue second)) ≤
      phaseObliviousPlaintextL1DefectAt
          degree prefixValue plaintextLaw positive first leakageValue +
        phaseObliviousPlaintextL1DefectAt
          degree prefixValue plaintextLaw positive second leakageValue := by
  let commonLaw := plaintextLaw positive leakageValue
  let firstTarget := aggregatePlaintextTarget positive degree (prefixValue first)
  let secondTarget := aggregatePlaintextTarget positive degree (prefixValue second)
  have horbit :
      tableL1Distance secondTarget firstTarget =
        translationL1Defect (aggregateMaskWeight positive Index degree)
          (xorEquiv (prefixValue first) (prefixValue second)) := by
    exact tableL1Distance_xorTargets_eq_translationL1Defect
      (aggregateMaskWeight positive Index degree)
      (prefixValue first) (prefixValue second)
  rw [← horbit]
  have htriangle := tableL1Distance_triangle secondTarget commonLaw firstTarget
  calc
    tableL1Distance secondTarget firstTarget ≤
        tableL1Distance secondTarget commonLaw +
          tableL1Distance commonLaw firstTarget := htriangle
    _ = phaseObliviousPlaintextL1DefectAt
          degree prefixValue plaintextLaw positive first leakageValue +
        phaseObliviousPlaintextL1DefectAt
          degree prefixValue plaintextLaw positive second leakageValue := by
      unfold phaseObliviousPlaintextL1DefectAt
      change tableL1Distance secondTarget commonLaw +
          tableL1Distance commonLaw firstTarget =
        tableL1Distance commonLaw firstTarget +
          tableL1Distance commonLaw secondTarget
      rw [tableL1Distance_comm secondTarget commonLaw]
      ring

/-- If two keys have the same leakage, the translation defect for either aggregate sign is at
most the sum of their two plaintext-construction defects. -/
theorem translationL1Defect_aggregateMaskWeight_le_phaseDefects_of_equalLeakage
    {Index Key Leakage : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (prefixValue : Key → BitVector Index) (leakage : Key → Leakage)
    (plaintextLaw : Bool → Leakage → BitVector Index → ℝ)
    (positive : Bool) (first second : Key)
    (hleakage : leakage first = leakage second) :
    translationL1Defect (aggregateMaskWeight positive Index degree)
        (xorEquiv (prefixValue first) (prefixValue second)) ≤
      phaseObliviousPlaintextL1Defect
          degree prefixValue leakage plaintextLaw positive first +
        phaseObliviousPlaintextL1Defect
          degree prefixValue leakage plaintextLaw positive second := by
  let commonLaw := plaintextLaw positive (leakage first)
  let firstTarget := aggregatePlaintextTarget positive degree (prefixValue first)
  let secondTarget := aggregatePlaintextTarget positive degree (prefixValue second)
  have hcommonSecond :
      plaintextLaw positive (leakage second) = commonLaw := by
    unfold commonLaw
    rw [← hleakage]
  have horbit :
      tableL1Distance secondTarget firstTarget =
        translationL1Defect (aggregateMaskWeight positive Index degree)
          (xorEquiv (prefixValue first) (prefixValue second)) := by
    exact tableL1Distance_xorTargets_eq_translationL1Defect
      (aggregateMaskWeight positive Index degree)
      (prefixValue first) (prefixValue second)
  rw [← horbit]
  have htriangle := tableL1Distance_triangle secondTarget commonLaw firstTarget
  calc
    tableL1Distance secondTarget firstTarget ≤
        tableL1Distance secondTarget commonLaw +
          tableL1Distance commonLaw firstTarget := htriangle
    _ = phaseObliviousPlaintextL1Defect
          degree prefixValue leakage plaintextLaw positive first +
        phaseObliviousPlaintextL1Defect
          degree prefixValue leakage plaintextLaw positive second := by
      unfold phaseObliviousPlaintextL1Defect
      change tableL1Distance secondTarget commonLaw +
          tableL1Distance commonLaw firstTarget =
        tableL1Distance commonLaw firstTarget +
          tableL1Distance (plaintextLaw positive (leakage second)) secondTarget
      rw [tableL1Distance_comm secondTarget commonLaw, hcommonSecond]
      ring

/-- Any nonzero shift below the usual cutoff flips at least one retained high-pass character. -/
theorem exists_highFrequency_walsh_eq_neg_one_of_ne_zero
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree + 2 ≤ Fintype.card Index)
    (shift : BitVector Index) (hshift : shift ≠ zeroFrequency) :
    ∃ frequency, frequency ∉ boundedFrequencies Index degree ∧
      walsh frequency shift = -1 := by
  classical
  have hdegreeLt : degree < Fintype.card Index := by omega
  have hnotInvariant : ¬ CommonAggregateTranslationInvariant Index degree shift := by
    intro hinvariant
    have hzero :=
      (commonAggregateTranslationInvariant_iff_eq_zero_of_degree_add_two_le
        degree hdegree shift).mp hinvariant
    exact hshift hzero
  have hcharactersFail :
      ¬ ∀ frequency, frequency ∉ boundedFrequencies Index degree →
        walsh frequency shift = 1 := by
    intro hcharacters
    exact hnotInvariant
      ((commonAggregateTranslationInvariant_iff_walsh_eq_one
        degree hdegreeLt shift).mpr hcharacters)
  push Not at hcharactersFail
  rcases hcharactersFail with ⟨frequency, hfrequency, hnotOne⟩
  refine ⟨frequency, hfrequency, ?_⟩
  rcases walsh_eq_one_or_neg_one frequency shift with hone | hnegative
  · exact False.elim (hnotOne hone)
  · exact hnegative

/-- Robust collision separation at one explicitly shared leakage value.  This is the form used
for stochastic leakage kernels. -/
theorem two_le_normalization_mul_four_phaseDefectsAt_of_prefix_collision
    {Index Key Leakage : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree + 2 ≤ Fintype.card Index)
    (prefixValue : Key → BitVector Index)
    (plaintextLaw : Bool → Leakage → BitVector Index → ℝ)
    (first second : Key) (leakageValue : Leakage)
    (hprefix : prefixValue first ≠ prefixValue second) :
    (2 : ℝ) ≤ aggregateNormalization Index degree *
      (phaseObliviousPlaintextL1DefectAt
          degree prefixValue plaintextLaw true first leakageValue +
        phaseObliviousPlaintextL1DefectAt
          degree prefixValue plaintextLaw true second leakageValue +
        phaseObliviousPlaintextL1DefectAt
          degree prefixValue plaintextLaw false first leakageValue +
        phaseObliviousPlaintextL1DefectAt
          degree prefixValue plaintextLaw false second leakageValue) := by
  let shift := xorEquiv (prefixValue first) (prefixValue second)
  have hshiftNe : shift ≠ zeroFrequency := by
    intro hzero
    exact hprefix (xorEquiv_left_cancel_zero hzero)
  rcases exists_highFrequency_walsh_eq_neg_one_of_ne_zero
    degree hdegree shift hshiftNe with ⟨frequency, hfrequency, hflip⟩
  have hdegreeLt : degree < Fintype.card Index := by omega
  have hseparation := two_le_normalization_mul_sum_translationL1Defects
    degree hdegreeLt shift frequency hfrequency hflip
  have hpositive := translationL1Defect_aggregateMaskWeight_le_phaseDefectsAt
    degree prefixValue plaintextLaw true first second leakageValue
  have hnegative := translationL1Defect_aggregateMaskWeight_le_phaseDefectsAt
    degree prefixValue plaintextLaw false first second leakageValue
  have hnormalization : 0 ≤ aggregateNormalization Index degree :=
    le_of_lt (aggregateNormalization_pos Index degree hdegreeLt)
  have hsum :
      translationL1Defect (aggregatePositiveWeight Index degree) shift +
          translationL1Defect (aggregateNegativeWeight Index degree) shift ≤
        phaseObliviousPlaintextL1DefectAt
            degree prefixValue plaintextLaw true first leakageValue +
          phaseObliviousPlaintextL1DefectAt
            degree prefixValue plaintextLaw true second leakageValue +
          phaseObliviousPlaintextL1DefectAt
            degree prefixValue plaintextLaw false first leakageValue +
          phaseObliviousPlaintextL1DefectAt
            degree prefixValue plaintextLaw false second leakageValue := by
    change
      translationL1Defect (aggregateMaskWeight true Index degree) shift +
          translationL1Defect (aggregateMaskWeight false Index degree) shift ≤ _
    dsimp [shift]
    linarith
  exact hseparation.trans (mul_le_mul_of_nonneg_left hsum hnormalization)

/-- A nontrivial prefix collision below the usual cutoff forces a constant aggregate amount of
plaintext-construction error across the two signs and two colliding keys. -/
theorem two_le_normalization_mul_four_phaseDefects_of_prefix_collision
    {Index Key Leakage : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree + 2 ≤ Fintype.card Index)
    (prefixValue : Key → BitVector Index) (leakage : Key → Leakage)
    (plaintextLaw : Bool → Leakage → BitVector Index → ℝ)
    (first second : Key) (hleakage : leakage first = leakage second)
    (hprefix : prefixValue first ≠ prefixValue second) :
    (2 : ℝ) ≤ aggregateNormalization Index degree *
      (phaseObliviousPlaintextL1Defect
          degree prefixValue leakage plaintextLaw true first +
        phaseObliviousPlaintextL1Defect
          degree prefixValue leakage plaintextLaw true second +
        phaseObliviousPlaintextL1Defect
          degree prefixValue leakage plaintextLaw false first +
        phaseObliviousPlaintextL1Defect
          degree prefixValue leakage plaintextLaw false second) := by
  classical
  let shift := xorEquiv (prefixValue first) (prefixValue second)
  have hdegreeLt : degree < Fintype.card Index := by omega
  have hshiftNe : shift ≠ zeroFrequency := by
    intro hzero
    exact hprefix (xorEquiv_left_cancel_zero hzero)
  have hnotInvariant : ¬ CommonAggregateTranslationInvariant Index degree shift := by
    intro hinvariant
    have hzero :=
      (commonAggregateTranslationInvariant_iff_eq_zero_of_degree_add_two_le
        degree hdegree shift).mp hinvariant
    exact hshiftNe hzero
  have hcharactersFail :
      ¬ ∀ frequency, frequency ∉ boundedFrequencies Index degree →
        walsh frequency shift = 1 := by
    intro hcharacters
    exact hnotInvariant
      ((commonAggregateTranslationInvariant_iff_walsh_eq_one
        degree hdegreeLt shift).mpr hcharacters)
  push Not at hcharactersFail
  rcases hcharactersFail with ⟨frequency, hfrequency, hnotOne⟩
  have hflip : walsh frequency shift = -1 := by
    rcases walsh_eq_one_or_neg_one frequency shift with hone | hnegative
    · exact False.elim (hnotOne hone)
    · exact hnegative
  have hseparation := two_le_normalization_mul_sum_translationL1Defects
    degree hdegreeLt shift frequency hfrequency hflip
  have hpositive :=
    translationL1Defect_aggregateMaskWeight_le_phaseDefects_of_equalLeakage
      degree prefixValue leakage plaintextLaw true first second hleakage
  have hnegative :=
    translationL1Defect_aggregateMaskWeight_le_phaseDefects_of_equalLeakage
      degree prefixValue leakage plaintextLaw false first second hleakage
  have hnormalization : 0 ≤ aggregateNormalization Index degree :=
    le_of_lt (aggregateNormalization_pos Index degree hdegreeLt)
  have hsum :
      translationL1Defect (aggregatePositiveWeight Index degree) shift +
          translationL1Defect (aggregateNegativeWeight Index degree) shift ≤
        phaseObliviousPlaintextL1Defect
            degree prefixValue leakage plaintextLaw true first +
          phaseObliviousPlaintextL1Defect
            degree prefixValue leakage plaintextLaw true second +
          phaseObliviousPlaintextL1Defect
            degree prefixValue leakage plaintextLaw false first +
          phaseObliviousPlaintextL1Defect
            degree prefixValue leakage plaintextLaw false second := by
    change
      translationL1Defect (aggregateMaskWeight true Index degree) shift +
          translationL1Defect (aggregateMaskWeight false Index degree) shift ≤ _
    dsimp [shift]
    linarith
  exact hseparation.trans (mul_le_mul_of_nonneg_left hsum hnormalization)

/-- Uniform per-key defect form of the robust collision obstruction. -/
theorem two_le_four_mul_normalization_mul_defect_of_prefix_collision
    {Index Key Leakage : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree + 2 ≤ Fintype.card Index)
    (prefixValue : Key → BitVector Index) (leakage : Key → Leakage)
    (plaintextLaw : Bool → Leakage → BitVector Index → ℝ)
    (defect : ℝ)
    (hdefect : ∀ positive key,
      phaseObliviousPlaintextL1Defect
        degree prefixValue leakage plaintextLaw positive key ≤ defect)
    (first second : Key) (hleakage : leakage first = leakage second)
    (hprefix : prefixValue first ≠ prefixValue second) :
    (2 : ℝ) ≤ 4 * aggregateNormalization Index degree * defect := by
  have hcollision :=
    two_le_normalization_mul_four_phaseDefects_of_prefix_collision
      degree hdegree prefixValue leakage plaintextLaw first second hleakage hprefix
  have hnormalization : 0 ≤ aggregateNormalization Index degree :=
    le_of_lt (aggregateNormalization_pos Index degree (by omega))
  have hsum :
      phaseObliviousPlaintextL1Defect
          degree prefixValue leakage plaintextLaw true first +
        phaseObliviousPlaintextL1Defect
          degree prefixValue leakage plaintextLaw true second +
        phaseObliviousPlaintextL1Defect
          degree prefixValue leakage plaintextLaw false first +
        phaseObliviousPlaintextL1Defect
          degree prefixValue leakage plaintextLaw false second ≤
      4 * defect := by
    linarith [hdefect true first, hdefect true second,
      hdefect false first, hdefect false second]
  calc
    (2 : ℝ) ≤ aggregateNormalization Index degree *
        (phaseObliviousPlaintextL1Defect
            degree prefixValue leakage plaintextLaw true first +
          phaseObliviousPlaintextL1Defect
            degree prefixValue leakage plaintextLaw true second +
          phaseObliviousPlaintextL1Defect
            degree prefixValue leakage plaintextLaw false first +
          phaseObliviousPlaintextL1Defect
            degree prefixValue leakage plaintextLaw false second) := hcollision
    _ ≤ aggregateNormalization Index degree * (4 * defect) :=
      mul_le_mul_of_nonneg_left hsum hnormalization
    _ = 4 * aggregateNormalization Index degree * defect := by ring

/-- If the uniform pointwise defect lies strictly below the robust Walsh threshold, equal leakage
still forces exact prefix recovery. -/
theorem prefix_eq_of_equal_leakage_of_four_mul_normalization_mul_defect_lt_two
    {Index Key Leakage : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree + 2 ≤ Fintype.card Index)
    (prefixValue : Key → BitVector Index) (leakage : Key → Leakage)
    (plaintextLaw : Bool → Leakage → BitVector Index → ℝ)
    (defect : ℝ)
    (hdefect : ∀ positive key,
      phaseObliviousPlaintextL1Defect
        degree prefixValue leakage plaintextLaw positive key ≤ defect)
    (hsmall : 4 * aggregateNormalization Index degree * defect < 2)
    (first second : Key) (hleakage : leakage first = leakage second) :
    prefixValue first = prefixValue second := by
  by_contra hprefix
  have hlower := two_le_four_mul_normalization_mul_defect_of_prefix_collision
    degree hdegree prefixValue leakage plaintextLaw defect hdefect
    first second hleakage hprefix
  linarith

/-- Randomized-leakage support separation.  Below the robust threshold, one leakage value cannot
have positive mass under two keys with different prefixes. -/
theorem prefix_eq_of_shared_stochasticLeakageValue_of_small_pointwise_defect
    {Index Key Leakage : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree + 2 ≤ Fintype.card Index)
    (prefixValue : Key → BitVector Index)
    (leakageMass : Key → Leakage → ℝ)
    (plaintextLaw : Bool → Leakage → BitVector Index → ℝ)
    (defect : ℝ)
    (hdefect : ∀ positive key leakageValue,
      0 < leakageMass key leakageValue →
        phaseObliviousPlaintextL1DefectAt
          degree prefixValue plaintextLaw positive key leakageValue ≤ defect)
    (hsmall : 4 * aggregateNormalization Index degree * defect < 2)
    (first second : Key) (leakageValue : Leakage)
    (hfirst : 0 < leakageMass first leakageValue)
    (hsecond : 0 < leakageMass second leakageValue) :
    prefixValue first = prefixValue second := by
  by_contra hprefix
  have hlower :=
    two_le_normalization_mul_four_phaseDefectsAt_of_prefix_collision
      degree hdegree prefixValue plaintextLaw first second leakageValue hprefix
  have hnormalization : 0 ≤ aggregateNormalization Index degree :=
    le_of_lt (aggregateNormalization_pos Index degree (by omega))
  have hsum :
      phaseObliviousPlaintextL1DefectAt
          degree prefixValue plaintextLaw true first leakageValue +
        phaseObliviousPlaintextL1DefectAt
          degree prefixValue plaintextLaw true second leakageValue +
        phaseObliviousPlaintextL1DefectAt
          degree prefixValue plaintextLaw false first leakageValue +
        phaseObliviousPlaintextL1DefectAt
          degree prefixValue plaintextLaw false second leakageValue ≤
      4 * defect := by
    linarith [hdefect true first leakageValue hfirst,
      hdefect true second leakageValue hsecond,
      hdefect false first leakageValue hfirst,
      hdefect false second leakageValue hsecond]
  have hupper := mul_le_mul_of_nonneg_left hsum hnormalization
  have : (2 : ℝ) ≤ 4 * aggregateNormalization Index degree * defect := by
    calc
      (2 : ℝ) ≤ aggregateNormalization Index degree *
          (phaseObliviousPlaintextL1DefectAt
              degree prefixValue plaintextLaw true first leakageValue +
            phaseObliviousPlaintextL1DefectAt
              degree prefixValue plaintextLaw true second leakageValue +
            phaseObliviousPlaintextL1DefectAt
              degree prefixValue plaintextLaw false first leakageValue +
            phaseObliviousPlaintextL1DefectAt
              degree prefixValue plaintextLaw false second leakageValue) := hlower
      _ ≤ aggregateNormalization Index degree * (4 * defect) := hupper
      _ = 4 * aggregateNormalization Index degree * defect := by ring
  linarith

/-- Pairwise overlap mass of two finite stochastic leakage kernels. -/
def stochasticLeakageOverlap
    {Key Leakage : Type} [Fintype Leakage]
    (leakageMass : Key → Leakage → ℝ) (first second : Key) : ℝ :=
  ∑ leakageValue, min (leakageMass first leakageValue)
    (leakageMass second leakageValue)

/-- Average plaintext-table defect under one stochastic leakage kernel. -/
def averagePhaseObliviousPlaintextL1Defect
    {Index Key Leakage : Type}
    [Fintype Index] [DecidableEq Index] [Fintype Leakage]
    (degree : ℕ) (prefixValue : Key → BitVector Index)
    (leakageMass : Key → Leakage → ℝ)
    (plaintextLaw : Bool → Leakage → BitVector Index → ℝ)
    (positive : Bool) (key : Key) : ℝ :=
  ∑ leakageValue, leakageMass key leakageValue *
    phaseObliviousPlaintextL1DefectAt
      degree prefixValue plaintextLaw positive key leakageValue

/-- Average-defect version of randomized-leakage separation.  Distinct prefixes can share only
proportionally small leakage overlap. -/
theorem two_mul_stochasticLeakageOverlap_le_normalization_mul_averageDefects
    {Index Key Leakage : Type}
    [Fintype Index] [DecidableEq Index] [Fintype Leakage]
    (degree : ℕ) (hdegree : degree + 2 ≤ Fintype.card Index)
    (prefixValue : Key → BitVector Index)
    (leakageMass : Key → Leakage → ℝ)
    (hmass : ∀ key leakageValue, 0 ≤ leakageMass key leakageValue)
    (plaintextLaw : Bool → Leakage → BitVector Index → ℝ)
    (first second : Key) (hprefix : prefixValue first ≠ prefixValue second) :
    2 * stochasticLeakageOverlap leakageMass first second ≤
      aggregateNormalization Index degree *
        (averagePhaseObliviousPlaintextL1Defect
            degree prefixValue leakageMass plaintextLaw true first +
          averagePhaseObliviousPlaintextL1Defect
            degree prefixValue leakageMass plaintextLaw false first +
          averagePhaseObliviousPlaintextL1Defect
            degree prefixValue leakageMass plaintextLaw true second +
          averagePhaseObliviousPlaintextL1Defect
            degree prefixValue leakageMass plaintextLaw false second) := by
  let normalization := aggregateNormalization Index degree
  let overlapWeight : Leakage → ℝ := fun leakageValue ↦
    min (leakageMass first leakageValue) (leakageMass second leakageValue)
  let firstError : Leakage → ℝ := fun leakageValue ↦
    phaseObliviousPlaintextL1DefectAt
        degree prefixValue plaintextLaw true first leakageValue +
      phaseObliviousPlaintextL1DefectAt
        degree prefixValue plaintextLaw false first leakageValue
  let secondError : Leakage → ℝ := fun leakageValue ↦
    phaseObliviousPlaintextL1DefectAt
        degree prefixValue plaintextLaw true second leakageValue +
      phaseObliviousPlaintextL1DefectAt
        degree prefixValue plaintextLaw false second leakageValue
  have hnormalization : 0 ≤ normalization :=
    le_of_lt (aggregateNormalization_pos Index degree (by omega))
  have hoverlapNonneg (leakageValue : Leakage) :
      0 ≤ overlapWeight leakageValue := by
    exact le_min (hmass first leakageValue) (hmass second leakageValue)
  have hfirstErrorNonneg (leakageValue : Leakage) : 0 ≤ firstError leakageValue := by
    exact add_nonneg
      (phaseObliviousPlaintextL1DefectAt_nonneg
        degree prefixValue plaintextLaw true first leakageValue)
      (phaseObliviousPlaintextL1DefectAt_nonneg
        degree prefixValue plaintextLaw false first leakageValue)
  have hsecondErrorNonneg (leakageValue : Leakage) : 0 ≤ secondError leakageValue := by
    exact add_nonneg
      (phaseObliviousPlaintextL1DefectAt_nonneg
        degree prefixValue plaintextLaw true second leakageValue)
      (phaseObliviousPlaintextL1DefectAt_nonneg
        degree prefixValue plaintextLaw false second leakageValue)
  have hpointwise (leakageValue : Leakage) :
      2 * overlapWeight leakageValue ≤
        normalization * overlapWeight leakageValue *
          (firstError leakageValue + secondError leakageValue) := by
    have hseparation :=
      two_le_normalization_mul_four_phaseDefectsAt_of_prefix_collision
        degree hdegree prefixValue plaintextLaw first second leakageValue hprefix
    have hrewritten :
        (2 : ℝ) ≤ normalization *
          (firstError leakageValue + secondError leakageValue) := by
      simpa [normalization, firstError, secondError, add_assoc, add_left_comm,
        add_comm] using hseparation
    have hmul := mul_le_mul_of_nonneg_left hrewritten
      (hoverlapNonneg leakageValue)
    nlinarith
  have hsumPointwise :
      (∑ leakageValue : Leakage, 2 * overlapWeight leakageValue) ≤
        ∑ leakageValue : Leakage,
          normalization * overlapWeight leakageValue *
            (firstError leakageValue + secondError leakageValue) :=
    Finset.sum_le_sum fun leakageValue _ ↦ hpointwise leakageValue
  have hweighted (leakageValue : Leakage) :
      overlapWeight leakageValue *
          (firstError leakageValue + secondError leakageValue) ≤
        leakageMass first leakageValue * firstError leakageValue +
          leakageMass second leakageValue * secondError leakageValue := by
    have hfirstWeight : overlapWeight leakageValue ≤ leakageMass first leakageValue :=
      min_le_left _ _
    have hsecondWeight : overlapWeight leakageValue ≤ leakageMass second leakageValue :=
      min_le_right _ _
    rw [mul_add]
    exact add_le_add
      (mul_le_mul_of_nonneg_right hfirstWeight (hfirstErrorNonneg leakageValue))
      (mul_le_mul_of_nonneg_right hsecondWeight (hsecondErrorNonneg leakageValue))
  have hweightedSum :
      (∑ leakageValue : Leakage,
          normalization * overlapWeight leakageValue *
            (firstError leakageValue + secondError leakageValue)) ≤
        normalization *
          ∑ leakageValue : Leakage,
            (leakageMass first leakageValue * firstError leakageValue +
              leakageMass second leakageValue * secondError leakageValue) := by
    calc
      (∑ leakageValue : Leakage,
          normalization * overlapWeight leakageValue *
            (firstError leakageValue + secondError leakageValue)) =
        normalization *
          ∑ leakageValue : Leakage,
            overlapWeight leakageValue *
              (firstError leakageValue + secondError leakageValue) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro leakageValue _
          ring
      _ ≤ normalization *
          ∑ leakageValue : Leakage,
            (leakageMass first leakageValue * firstError leakageValue +
              leakageMass second leakageValue * secondError leakageValue) := by
        apply mul_le_mul_of_nonneg_left _ hnormalization
        exact Finset.sum_le_sum fun leakageValue _ ↦ hweighted leakageValue
  calc
    2 * stochasticLeakageOverlap leakageMass first second =
        ∑ leakageValue : Leakage, 2 * overlapWeight leakageValue := by
      simp [stochasticLeakageOverlap, overlapWeight, Finset.mul_sum]
    _ ≤ ∑ leakageValue : Leakage,
        normalization * overlapWeight leakageValue *
          (firstError leakageValue + secondError leakageValue) := hsumPointwise
    _ ≤ normalization *
        ∑ leakageValue : Leakage,
          (leakageMass first leakageValue * firstError leakageValue +
            leakageMass second leakageValue * secondError leakageValue) := hweightedSum
    _ = aggregateNormalization Index degree *
        (averagePhaseObliviousPlaintextL1Defect
            degree prefixValue leakageMass plaintextLaw true first +
          averagePhaseObliviousPlaintextL1Defect
            degree prefixValue leakageMass plaintextLaw false first +
          averagePhaseObliviousPlaintextL1Defect
            degree prefixValue leakageMass plaintextLaw true second +
          averagePhaseObliviousPlaintextL1Defect
            degree prefixValue leakageMass plaintextLaw false second) := by
      unfold normalization firstError secondError
      unfold averagePhaseObliviousPlaintextL1Defect
      simp_rw [mul_add]
      simp only [Finset.sum_add_distrib]
      ring

end

end FormalProof4FHE.TFHE.NativeTRGSWAggregateRobustLeakage
