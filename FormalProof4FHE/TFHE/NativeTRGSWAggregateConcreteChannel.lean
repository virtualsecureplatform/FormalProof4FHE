/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeTRGSWAggregateSecurityAndComplexityLeveraging
import FormalProof4FHE.Probability.FinitePMFCompilerApproximation
import FormalProof4FHE.Probability.ModularGaussian

/-!
# Concrete native aggregate TRGSW channel

This module realizes the abstract high-pass orbit experiment as an actual native complete-cloud
sampler.  A binary prefix key is sampled uniformly, an independent mask is sampled from a caller
supplied finite computation, and the complete native BRK/KSK channel is generated with message
`prefix xor mask`.  The suffix and the KSK remain inside the existing complete native kernel, so
all of their correlation is retained.

The first half is exact: the acceptance probability of this sampler is precisely the weighted
orbit mean whose weight is the mask sampler's point-mass function.  Consequently, any samplers
realizing the two normalized Jordan laws instantiate the abstract aggregate games with zero
construction defect.  The second half packages the corresponding complete-cloud bridge, leaving
only the cryptographic source bound and mask-sampler realization separate.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.NativeTRGSWAggregateConcreteChannel

noncomputable section

open NativeTRGSWBarrierAndSpectralBoundary
open NativeTRGSWCompleteChannel
open NativeTRGSWAggregateSecurityAndComplexityLeveraging
open RGSWCoefficientCircularSecurity
open Native.SharedRandomnessOneCycle

/-! ## Generic sampler realization of an orbit mean -/

/-- Select the positive or negative normalized Jordan table. -/
def aggregateMaskWeight
    (positive : Bool) (Index : Type) [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (mask : BitVector Index) : ℝ :=
  if positive then aggregatePositiveWeight Index degree mask
  else aggregateNegativeWeight Index degree mask

theorem aggregateMaskWeight_nonneg
    (positive : Bool) (Index : Type) [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (mask : BitVector Index) :
    0 ≤ aggregateMaskWeight positive Index degree mask := by
  cases positive <;>
    simp [aggregateMaskWeight, aggregatePositiveWeight_nonneg,
      aggregateNegativeWeight_nonneg]

theorem sum_aggregateMaskWeight_eq_one
    (positive : Bool) (Index : Type) [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree < Fintype.card Index) :
    ∑ mask : BitVector Index, aggregateMaskWeight positive Index degree mask = 1 := by
  cases positive <;>
    simp [aggregateMaskWeight,
      sum_aggregatePositiveWeight_eq_one Index degree hdegree,
      sum_aggregateNegativeWeight_eq_one Index degree hdegree]

@[simp]
theorem aggregateAcceptance_eq_weightedOrbitMean_aggregateMaskWeight
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (positive : Bool) (response : BitVector Index → BitVector Index → ℝ) (degree : ℕ) :
    aggregateAcceptance positive response degree =
      weightedOrbitMean (aggregateMaskWeight positive Index degree) response := by
  cases positive <;> rfl

/-! ### Mathematical and executable mask laws -/

/-- Mathematical PMF denoted by one normalized Jordan mask law. -/
noncomputable def aggregateMaskPMF
    (positive : Bool) (Index : Type) [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree < Fintype.card Index) :
    PMF (BitVector Index) :=
  PMF.ofFintype
    (fun mask ↦ ENNReal.ofReal (aggregateMaskWeight positive Index degree mask))
    (by
      calc
        (∑ mask : BitVector Index,
            ENNReal.ofReal (aggregateMaskWeight positive Index degree mask)) =
            ENNReal.ofReal
              (∑ mask : BitVector Index,
                aggregateMaskWeight positive Index degree mask) := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          intro mask _
          exact aggregateMaskWeight_nonneg positive Index degree mask
        _ = 1 := by
          rw [sum_aggregateMaskWeight_eq_one positive Index degree hdegree]
          exact ENNReal.ofReal_one)

@[simp]
theorem aggregateMaskPMF_apply_toReal
    (positive : Bool) (Index : Type) [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree < Fintype.card Index)
    (mask : BitVector Index) :
    (aggregateMaskPMF positive Index degree hdegree mask).toReal =
      aggregateMaskWeight positive Index degree mask := by
  rw [aggregateMaskPMF, PMF.ofFintype_apply, ENNReal.toReal_ofReal]
  exact aggregateMaskWeight_nonneg positive Index degree mask

/-- A canonical proof-carrying executable approximation to either aggregate mask law.  The
denominator is explicit and its finite total-variation error is stored in the certificate. -/
noncomputable def roundedAggregateMaskCertificate
    (positive : Bool) (Index : Type) [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree < Fintype.card Index)
    (denominator : ℕ) (hdenominator : 0 < denominator) :
    FinitePMFCompiler.TicketTable.Certificate
      (aggregateMaskPMF positive Index degree hdegree) :=
  FinitePMFCompiler.TicketTable.roundedCertificate
    (aggregateMaskPMF positive Index degree hdegree)
    (zeroFrequency : BitVector Index) denominator hdenominator

/-- Real `L¹` point-mass error of a proof-carrying ticket table is at most twice its certified
total-variation bound. -/
theorem certificate_sum_abs_probabilityMass_sub_target_le
    {Output : Type} [Fintype Output] [DecidableEq Output]
    {target : PMF Output}
    (certificate : FinitePMFCompiler.TicketTable.Certificate target) :
    (∑ value : Output,
        |probabilityMass certificate.table.sampler value -
          (target value).toReal|) ≤
      2 * certificate.bound.toReal := by
  have hmass (value : Output) :
      probabilityMass certificate.table.sampler value =
        (certificate.table.outputPMF value).toReal := by
    unfold probabilityMass
    rw [FinitePMFCompiler.TicketTable.probOutput_sampler,
      FinitePMFCompiler.TicketTable.outputPMF_apply]
  have htv := certificate.tvDist_le
  rw [FormalProof4FHE.ModularGaussian.tvDist_eq_half_tsum_abs_toReal,
    tsum_fintype] at htv
  simp_rw [hmass]
  linarith

/-- Elementary stability of an orbit mean under `L¹` perturbation of its mask weights. -/
theorem abs_weightedOrbitMean_sub_le_sum_abs
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (left right : BitVector Index → ℝ)
    (response : BitVector Index → BitVector Index → ℝ)
    (hresponse : ∀ secret message, |response secret message| ≤ 1) :
    |weightedOrbitMean left response - weightedOrbitMean right response| ≤
      ∑ mask : BitVector Index, |left mask - right mask| := by
  classical
  rw [← weightedOrbitMean_sub]
  unfold weightedOrbitMean
  have hcube : 0 < cubeSize Index := cubeSize_pos Index
  rw [abs_div, abs_of_pos hcube]
  apply (div_le_iff₀ hcube).2
  calc
    |∑ secret : BitVector Index, ∑ mask : BitVector Index,
        (left mask - right mask) * response secret (xorEquiv secret mask)| ≤
        ∑ secret : BitVector Index,
          |∑ mask : BitVector Index,
            (left mask - right mask) * response secret (xorEquiv secret mask)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _secret : BitVector Index,
          ∑ mask : BitVector Index, |left mask - right mask| := by
      apply Finset.sum_le_sum
      intro secret _
      calc
        |∑ mask : BitVector Index,
            (left mask - right mask) * response secret (xorEquiv secret mask)| ≤
            ∑ mask : BitVector Index,
              |(left mask - right mask) *
                response secret (xorEquiv secret mask)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ mask : BitVector Index, |left mask - right mask| := by
          apply Finset.sum_le_sum
          intro mask _
          rw [abs_mul]
          simpa only [mul_one] using
            mul_le_mul_of_nonneg_left
              (hresponse secret (xorEquiv secret mask)) (abs_nonneg _)
    _ = (∑ mask : BitVector Index, |left mask - right mask|) *
          cubeSize Index := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      simp [cubeSize]
      ring

/-- A real expectation of an observable bounded by one is itself bounded by one. -/
theorem abs_expectation_le_one
    {Output : Type} [Fintype Output]
    (sampler : ProbComp Output) (observable : Output → ℝ)
    (hobservable : ∀ value, |observable value| ≤ 1) :
    |FormalProof4FHE.BoundedMoment.expectation sampler observable| ≤ 1 := by
  classical
  unfold FormalProof4FHE.BoundedMoment.expectation
  calc
    |∑ value : Output, Pr[= value | sampler].toReal * observable value| ≤
        ∑ value : Output,
          |Pr[= value | sampler].toReal * observable value| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ value : Output, probabilityMass sampler value := by
      apply Finset.sum_le_sum
      intro value _
      rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      simpa [probabilityMass] using
        mul_le_mul_of_nonneg_left (hobservable value) ENNReal.toReal_nonneg
    _ = 1 := sum_probabilityMass_eq_one sampler

/-- Sample a uniform binary secret, then a private mask, and feed `secret xor mask` to a complete
sampler kernel.  The mask is not part of the public output. -/
noncomputable def aggregateOrbitExperiment
    {Index View : Type} [Fintype Index] [SampleableType (BitVector Index)]
    (sampler : BitVector Index → BitVector Index → ProbComp View)
    (maskSampler : ProbComp (BitVector Index)) : ProbComp View := do
  let secret ← ($ᵗ (BitVector Index))
  let mask ← maskSampler
  sampler secret (xorEquiv secret mask)

/-- The concrete orbit experiment has exactly the weighted-orbit expectation induced by the mask
sampler's real point masses. -/
theorem aggregateOrbitExperiment_expectation_eq_weightedOrbitMean
    {Index View : Type} [Fintype Index] [DecidableEq Index]
    [SampleableType (BitVector Index)] [Fintype View]
    (sampler : BitVector Index → BitVector Index → ProbComp View)
    (maskSampler : ProbComp (BitVector Index)) (response : View → ℝ) :
    FormalProof4FHE.BoundedMoment.expectation
        (aggregateOrbitExperiment sampler maskSampler) response =
      weightedOrbitMean (probabilityMass maskSampler)
        (completeChannelResponse (channelOfSampler sampler) response) := by
  classical
  unfold aggregateOrbitExperiment
  rw [FormalProof4FHE.BoundedMoment.expectation_bind]
  simp_rw [FormalProof4FHE.BoundedMoment.expectation_bind]
  simp_rw [← completeChannelResponse_channelOfSampler_eq_expectation]
  unfold weightedOrbitMean probabilityMass
  simp_rw [probOutput_uniformSample, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have hcard : (Fintype.card (BitVector Index) : ℝ) = cubeSize Index := by
    simp [cubeSize]
  rw [← Finset.mul_sum, hcard]
  field_simp [cubeSize_ne_zero Index]

/-- Randomized-adversary form of the exact orbit-experiment identity. -/
theorem aggregateOrbitExperiment_acceptance_eq_weightedOrbitMean
    {Index View : Type} [Fintype Index] [DecidableEq Index]
    [SampleableType (BitVector Index)] [Fintype View]
    (sampler : BitVector Index → BitVector Index → ProbComp View)
    (maskSampler : ProbComp (BitVector Index))
    (adversary : View → ProbComp Bool) :
    Pr[= true | aggregateOrbitExperiment sampler maskSampler >>= adversary].toReal =
      weightedOrbitMean (probabilityMass maskSampler)
        (completeChannelResponse (channelOfSampler sampler)
          (adversaryResponse adversary)) := by
  rw [← expectation_adversaryResponse_eq_probOutput]
  exact aggregateOrbitExperiment_expectation_eq_weightedOrbitMean
    sampler maskSampler (adversaryResponse adversary)

/-! ## Concrete native aggregate cloud-key games -/

/-- Actual native aggregate cloud-key sampler.  It retains the complete BRK, suffix KSK, and all
shared-key correlation generated by `fixedPrefixMessageView`. -/
noncomputable def nativeAggregateView
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (maskSampler : ProbComp (BinarySecret prefixDimension)) :
    ProbComp (CloudKey
      q prefixDimension suffixDimension tgswLevels keySwitchLevels) :=
  aggregateOrbitExperiment
    (fixedPrefixMessageView q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    maskSampler

/-- Acceptance in the concrete native aggregate game is exactly the weighted response of the
existing complete native channel. -/
theorem nativeAggregateView_acceptance_eq_weightedOrbitMean
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (maskSampler : ProbComp (BinarySecret prefixDimension))
    (adversary : CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels →
      ProbComp Bool) :
    Pr[= true | nativeAggregateView q prefixDimension suffixDimension tgswLevels
        keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        maskSampler >>= adversary].toReal =
      weightedOrbitMean (probabilityMass maskSampler)
        (completeChannelResponse
          (nativeCompleteChannel q prefixDimension suffixDimension tgswLevels keySwitchLevels
            ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
          (adversaryResponse adversary)) := by
  exact aggregateOrbitExperiment_acceptance_eq_weightedOrbitMean
    (fixedPrefixMessageView q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    maskSampler adversary

/-- Every conditional native complete-channel response induced by a Boolean adversary is bounded
by one. -/
theorem nativeCompleteChannel_adversaryResponse_abs_le_one
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels →
      ProbComp Bool)
    (prefixKey message : BinarySecret prefixDimension) :
    |completeChannelResponse
        (nativeCompleteChannel q prefixDimension suffixDimension tgswLevels keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        (adversaryResponse adversary) prefixKey message| ≤ 1 := by
  unfold nativeCompleteChannel
  rw [completeChannelResponse_channelOfSampler_eq_expectation]
  exact abs_expectation_le_one _ _ (adversaryResponse_abs_le_one adversary)

/-- A sampler whose point masses are one normalized Jordan table realizes the corresponding
native aggregate game exactly. -/
theorem nativeAggregateView_acceptance_eq_aggregateAcceptance_of_probabilityMass
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (positive : Bool) (degree : ℕ)
    (maskSampler : ProbComp (BinarySecret prefixDimension))
    (hmass : ∀ mask,
      probabilityMass maskSampler mask =
        aggregateMaskWeight positive (Fin prefixDimension) degree mask)
    (adversary : CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels →
      ProbComp Bool) :
    Pr[= true | nativeAggregateView q prefixDimension suffixDimension tgswLevels
        keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        maskSampler >>= adversary].toReal =
      aggregateAcceptance positive
        (completeChannelResponse
          (nativeCompleteChannel q prefixDimension suffixDimension tgswLevels keySwitchLevels
            ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
          (adversaryResponse adversary)) degree := by
  rw [nativeAggregateView_acceptance_eq_weightedOrbitMean]
  have hweight :
      probabilityMass maskSampler =
        if positive then aggregatePositiveWeight (Fin prefixDimension) degree
        else aggregateNegativeWeight (Fin prefixDimension) degree := by
    funext mask
    cases positive <;> simpa [aggregateMaskWeight] using hmass mask
  rw [hweight]
  rfl

/-- An executable ticket-table approximation realizes the ideal native aggregate acceptance up
to twice its certified total-variation error.  This is the explicit construction defect consumed
by the final security theorem. -/
theorem nativeAggregateView_acceptance_sub_aggregateAcceptance_le_certificate
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (positive : Bool) (degree : ℕ)
    (hdegree : degree < Fintype.card (Fin prefixDimension))
    (certificate : FinitePMFCompiler.TicketTable.Certificate
      (aggregateMaskPMF positive (Fin prefixDimension) degree hdegree))
    (adversary : CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels →
      ProbComp Bool) :
    |Pr[= true | nativeAggregateView q prefixDimension suffixDimension tgswLevels
          keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
          certificate.table.sampler >>= adversary].toReal -
        aggregateAcceptance positive
          (completeChannelResponse
            (nativeCompleteChannel q prefixDimension suffixDimension tgswLevels keySwitchLevels
              ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
            (adversaryResponse adversary)) degree| ≤
      2 * certificate.bound.toReal := by
  rw [nativeAggregateView_acceptance_eq_weightedOrbitMean]
  rw [aggregateAcceptance_eq_weightedOrbitMean_aggregateMaskWeight]
  have hresponse : ∀ prefixKey message : BinarySecret prefixDimension,
      |completeChannelResponse
        (nativeCompleteChannel q prefixDimension suffixDimension tgswLevels keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        (adversaryResponse adversary) prefixKey message| ≤ 1 :=
    nativeCompleteChannel_adversaryResponse_abs_le_one q prefixDimension suffixDimension
      tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget
      keySwitchGadget adversary
  refine (abs_weightedOrbitMean_sub_le_sum_abs
    (probabilityMass certificate.table.sampler)
    (aggregateMaskWeight positive (Fin prefixDimension) degree)
    (completeChannelResponse
      (nativeCompleteChannel q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
      (adversaryResponse adversary)) hresponse).trans ?_
  simpa only [aggregateMaskPMF_apply_toReal] using
    certificate_sum_abs_probabilityMass_sub_target_le certificate

/-- Three-point triangle inequality in the form used to replace the two ideal aggregate
acceptances by their executable approximations. -/
theorem abs_ideal_gap_le_actual_gap_add_defects
    (idealPositive idealNegative actualPositive actualNegative
      positiveDefect negativeDefect : ℝ)
    (hpositive : |actualPositive - idealPositive| ≤ positiveDefect)
    (hnegative : |actualNegative - idealNegative| ≤ negativeDefect) :
    |idealPositive - idealNegative| ≤
      |actualPositive - actualNegative| + positiveDefect + negativeDefect := by
  calc
    |idealPositive - idealNegative| ≤
        |idealPositive - actualPositive| +
          |actualPositive - idealNegative| :=
      abs_sub_le idealPositive actualPositive idealNegative
    _ ≤ |idealPositive - actualPositive| +
          (|actualPositive - actualNegative| +
            |actualNegative - idealNegative|) := by
      gcongr
      exact abs_sub_le actualPositive actualNegative idealNegative
    _ ≤ positiveDefect +
          (|actualPositive - actualNegative| + negativeDefect) := by
      gcongr
      simpa [abs_sub_comm] using hpositive
    _ = |actualPositive - actualNegative| + positiveDefect + negativeDefect := by ring

/-- The aggregate low/high bridge remains valid for executable aggregate experiments that
approximate the two ideal Jordan laws, with their two construction defects added once. -/
theorem diagonalGap_le_low_add_approximateAggregate
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (response : BitVector Index → BitVector Index → ℝ)
    (degree : ℕ) (hdegree : degree < Fintype.card Index) (lowBound : ℝ)
    (actualPositive actualNegative positiveDefect negativeDefect : ℝ)
    (hlow : ∀ frequency ∈ lowFrequencies Index degree,
      |fourierCoefficient response frequency frequency| ≤ lowBound)
    (hpositive : |actualPositive - aggregateAcceptance true response degree| ≤
      positiveDefect)
    (hnegative : |actualNegative - aggregateAcceptance false response degree| ≤
      negativeDefect) :
    |diagonalMean response - independentMean response| ≤
      lowFrequencyCount Index degree * lowBound +
        aggregateNormalization Index degree *
          (|actualPositive - actualNegative| + positiveDefect + negativeDefect) := by
  have hbase := diagonalGap_le_lowCount_mul_add_aggregate
    response degree hdegree lowBound hlow
  have hgap := abs_ideal_gap_le_actual_gap_add_defects
    (aggregateAcceptance true response degree)
    (aggregateAcceptance false response degree)
    actualPositive actualNegative positiveDefect negativeDefect hpositive hnegative
  have hnormalization : 0 ≤ aggregateNormalization Index degree :=
    Finset.sum_nonneg fun mask _ ↦
      positiveHighPassWeight_nonneg Index degree mask
  exact hbase.trans (by
    simpa [add_comm] using
      (add_le_add_left
        (mul_le_mul_of_nonneg_left hgap hnormalization)
        (lowFrequencyCount Index degree * lowBound)))

/-- Exact positive-minus-negative identity for two concrete native mask samplers realizing the
Jordan laws. -/
theorem nativeAggregateView_acceptance_gap_eq
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (degree : ℕ)
    (positiveMaskSampler negativeMaskSampler : ProbComp (BinarySecret prefixDimension))
    (hpositive : ∀ mask,
      probabilityMass positiveMaskSampler mask =
        aggregatePositiveWeight (Fin prefixDimension) degree mask)
    (hnegative : ∀ mask,
      probabilityMass negativeMaskSampler mask =
        aggregateNegativeWeight (Fin prefixDimension) degree mask)
    (adversary : CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels →
      ProbComp Bool) :
    Pr[= true | nativeAggregateView q prefixDimension suffixDimension tgswLevels
        keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        positiveMaskSampler >>= adversary].toReal -
      Pr[= true | nativeAggregateView q prefixDimension suffixDimension tgswLevels
        keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        negativeMaskSampler >>= adversary].toReal =
      aggregateAcceptance true
          (completeChannelResponse
            (nativeCompleteChannel q prefixDimension suffixDimension tgswLevels keySwitchLevels
              ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
            (adversaryResponse adversary)) degree -
        aggregateAcceptance false
          (completeChannelResponse
            (nativeCompleteChannel q prefixDimension suffixDimension tgswLevels keySwitchLevels
              ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
          (adversaryResponse adversary)) degree := by
  have hplus :=
    nativeAggregateView_acceptance_eq_aggregateAcceptance_of_probabilityMass
      q prefixDimension suffixDimension tgswLevels keySwitchLevels ringErrorSampler
      keySwitchErrorSampler tgswGadget keySwitchGadget true degree positiveMaskSampler
      (fun mask ↦ by simpa [aggregateMaskWeight] using hpositive mask) adversary
  have hminus :=
    nativeAggregateView_acceptance_eq_aggregateAcceptance_of_probabilityMass
      q prefixDimension suffixDimension tgswLevels keySwitchLevels ringErrorSampler
      keySwitchErrorSampler tgswGadget keySwitchGadget false degree negativeMaskSampler
      (fun mask ↦ by simpa [aggregateMaskWeight] using hnegative mask) adversary
  rw [hplus, hminus]

/-- Fully concrete low/high bridge for the actual native real cloud-key view and actual native
aggregate cloud-key samplers.  No statistical spectral-decay premise occurs. -/
theorem realCloudKey_gap_le_low_add_nativeAggregate
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels →
      ProbComp Bool)
    (degree : ℕ) (hdegree : degree < prefixDimension) (lowBound : ℝ)
    (positiveMaskSampler negativeMaskSampler : ProbComp (BinarySecret prefixDimension))
    (hpositive : ∀ mask,
      probabilityMass positiveMaskSampler mask =
        aggregatePositiveWeight (Fin prefixDimension) degree mask)
    (hnegative : ∀ mask,
      probabilityMass negativeMaskSampler mask =
        aggregateNegativeWeight (Fin prefixDimension) degree mask)
    (hlow : ∀ frequency ∈ lowFrequencies (Fin prefixDimension) degree,
      |fourierCoefficient
        (completeChannelResponse
          (nativeCompleteChannel q prefixDimension suffixDimension tgswLevels keySwitchLevels
            ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
          (adversaryResponse adversary)) frequency frequency| ≤ lowBound) :
    |Pr[= true | Native.SharedRandomnessOneCycle.realCloudKeyView q prefixDimension
        suffixDimension tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget >>= adversary].toReal -
      Pr[= true | independentMessageNativeView q prefixDimension suffixDimension tgswLevels
        keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget >>=
          adversary].toReal| ≤
      lowFrequencyCount (Fin prefixDimension) degree * lowBound +
        aggregateNormalization (Fin prefixDimension) degree *
          |Pr[= true | nativeAggregateView q prefixDimension suffixDimension tgswLevels
              keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
              positiveMaskSampler >>= adversary].toReal -
            Pr[= true | nativeAggregateView q prefixDimension suffixDimension tgswLevels
              keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
              negativeMaskSampler >>= adversary].toReal| := by
  rw [realCloudKeyAcceptance_eq_diagonalMean q prefixDimension suffixDimension
    tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler
    tgswGadget keySwitchGadget adversary]
  rw [independentMessageNativeAcceptance_eq_independentMean q prefixDimension suffixDimension
    tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler
    tgswGadget keySwitchGadget adversary]
  rw [nativeAggregateView_acceptance_gap_eq q prefixDimension suffixDimension tgswLevels
    keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget degree
    positiveMaskSampler negativeMaskSampler hpositive hnegative adversary]
  exact diagonalGap_le_lowCount_mul_add_aggregate
    (completeChannelResponse
      (nativeCompleteChannel q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
      (adversaryResponse adversary)) degree (by simpa using hdegree) lowBound hlow

/-- Executable version of the concrete native aggregate bridge.  Each ideal Jordan mask law is
represented by a proof-carrying ticket table; the two certified sampler errors appear once each
inside the aggregate normalization factor. -/
theorem realCloudKey_gap_le_low_add_certifiedNativeAggregate
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels →
      ProbComp Bool)
    (degree : ℕ) (hdegree : degree < Fintype.card (Fin prefixDimension))
    (lowBound : ℝ)
    (positiveCertificate : FinitePMFCompiler.TicketTable.Certificate
      (aggregateMaskPMF true (Fin prefixDimension) degree hdegree))
    (negativeCertificate : FinitePMFCompiler.TicketTable.Certificate
      (aggregateMaskPMF false (Fin prefixDimension) degree hdegree))
    (hlow : ∀ frequency ∈ lowFrequencies (Fin prefixDimension) degree,
      |fourierCoefficient
        (completeChannelResponse
          (nativeCompleteChannel q prefixDimension suffixDimension tgswLevels keySwitchLevels
            ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
          (adversaryResponse adversary)) frequency frequency| ≤ lowBound) :
    |Pr[= true | Native.SharedRandomnessOneCycle.realCloudKeyView q prefixDimension
        suffixDimension tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget >>= adversary].toReal -
      Pr[= true | independentMessageNativeView q prefixDimension suffixDimension tgswLevels
        keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget >>=
          adversary].toReal| ≤
      lowFrequencyCount (Fin prefixDimension) degree * lowBound +
        aggregateNormalization (Fin prefixDimension) degree *
          (|Pr[= true | nativeAggregateView q prefixDimension suffixDimension tgswLevels
                keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
                positiveCertificate.table.sampler >>= adversary].toReal -
              Pr[= true | nativeAggregateView q prefixDimension suffixDimension tgswLevels
                keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
                negativeCertificate.table.sampler >>= adversary].toReal| +
            2 * positiveCertificate.bound.toReal +
            2 * negativeCertificate.bound.toReal) := by
  rw [realCloudKeyAcceptance_eq_diagonalMean q prefixDimension suffixDimension
    tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler
    tgswGadget keySwitchGadget adversary]
  rw [independentMessageNativeAcceptance_eq_independentMean q prefixDimension suffixDimension
    tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler
    tgswGadget keySwitchGadget adversary]
  exact diagonalGap_le_low_add_approximateAggregate
    (completeChannelResponse
      (nativeCompleteChannel q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
      (adversaryResponse adversary)) degree hdegree lowBound
    Pr[= true | nativeAggregateView q prefixDimension suffixDimension tgswLevels
      keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
      positiveCertificate.table.sampler >>= adversary].toReal
    Pr[= true | nativeAggregateView q prefixDimension suffixDimension tgswLevels
      keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
      negativeCertificate.table.sampler >>= adversary].toReal
    (2 * positiveCertificate.bound.toReal)
    (2 * negativeCertificate.bound.toReal) hlow
    (nativeAggregateView_acceptance_sub_aggregateAcceptance_le_certificate
      q prefixDimension suffixDimension tgswLevels keySwitchLevels ringErrorSampler
      keySwitchErrorSampler tgswGadget keySwitchGadget true degree hdegree
      positiveCertificate adversary)
    (nativeAggregateView_acceptance_sub_aggregateAcceptance_le_certificate
      q prefixDimension suffixDimension tgswLevels keySwitchLevels ringErrorSampler
      keySwitchErrorSampler tgswGadget keySwitchGadget false degree hdegree
      negativeCertificate adversary)

/-- Final concrete native aggregate theorem before the genuinely cryptographic source step.  The
low-degree affine certificate, executable aggregate-game advantage, and endpoint are the only
security premises; Fourier algebra, native channel plumbing, and sampler defects are discharged
internally. -/
theorem realCloudKey_conditionalCertifiedAggregateSecurity
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels →
      ProbComp Bool)
    (degree : ℕ) (hdegree : degree < Fintype.card (Fin prefixDimension))
    (delta aggregateBound endpoint endpointBound : ℝ)
    (lowCertificate : LowDegreeAffineSourceCertificate
      (nativeCompleteChannel q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
      (adversaryResponse adversary) degree delta)
    (positiveCertificate : FinitePMFCompiler.TicketTable.Certificate
      (aggregateMaskPMF true (Fin prefixDimension) degree hdegree))
    (negativeCertificate : FinitePMFCompiler.TicketTable.Certificate
      (aggregateMaskPMF false (Fin prefixDimension) degree hdegree))
    (haggregate :
      |Pr[= true | nativeAggregateView q prefixDimension suffixDimension tgswLevels
            keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
            positiveCertificate.table.sampler >>= adversary].toReal -
        Pr[= true | nativeAggregateView q prefixDimension suffixDimension tgswLevels
          keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
          negativeCertificate.table.sampler >>= adversary].toReal| ≤ aggregateBound)
    (hendpoint : endpoint ≤ endpointBound) :
    |Pr[= true | Native.SharedRandomnessOneCycle.realCloudKeyView q prefixDimension
        suffixDimension tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget >>= adversary].toReal -
      Pr[= true | independentMessageNativeView q prefixDimension suffixDimension tgswLevels
        keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget >>=
          adversary].toReal| + endpoint ≤
      lowFrequencyCount (Fin prefixDimension) degree *
          Real.sqrt ((2 : ℝ) ^ (degree + 1) * delta) +
        aggregateNormalization (Fin prefixDimension) degree *
          (aggregateBound + 2 * positiveCertificate.bound.toReal +
            2 * negativeCertificate.bound.toReal) +
        endpointBound := by
  have hgap := realCloudKey_gap_le_low_add_certifiedNativeAggregate
    q prefixDimension suffixDimension tgswLevels keySwitchLevels ringErrorSampler
    keySwitchErrorSampler tgswGadget keySwitchGadget adversary degree hdegree
    (Real.sqrt ((2 : ℝ) ^ (degree + 1) * delta))
    positiveCertificate negativeCertificate lowCertificate.lowFrequencyBound
  have hnormalization : 0 ≤ aggregateNormalization (Fin prefixDimension) degree :=
    Finset.sum_nonneg fun mask _ ↦
      positiveHighPassWeight_nonneg (Fin prefixDimension) degree mask
  calc
    |Pr[= true | Native.SharedRandomnessOneCycle.realCloudKeyView q prefixDimension
          suffixDimension tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget >>= adversary].toReal -
        Pr[= true | independentMessageNativeView q prefixDimension suffixDimension tgswLevels
          keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget >>=
            adversary].toReal| + endpoint ≤
        (lowFrequencyCount (Fin prefixDimension) degree *
            Real.sqrt ((2 : ℝ) ^ (degree + 1) * delta) +
          aggregateNormalization (Fin prefixDimension) degree *
            (|Pr[= true | nativeAggregateView q prefixDimension suffixDimension tgswLevels
                  keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget
                  keySwitchGadget positiveCertificate.table.sampler >>= adversary].toReal -
                Pr[= true | nativeAggregateView q prefixDimension suffixDimension tgswLevels
                  keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget
                  keySwitchGadget negativeCertificate.table.sampler >>= adversary].toReal| +
              2 * positiveCertificate.bound.toReal +
              2 * negativeCertificate.bound.toReal)) + endpoint :=
      by simpa [add_comm] using add_le_add_right hgap endpoint
    _ ≤ lowFrequencyCount (Fin prefixDimension) degree *
          Real.sqrt ((2 : ℝ) ^ (degree + 1) * delta) +
        aggregateNormalization (Fin prefixDimension) degree *
          (aggregateBound + 2 * positiveCertificate.bound.toReal +
            2 * negativeCertificate.bound.toReal) +
        endpointBound := by
      gcongr

end

end FormalProof4FHE.TFHE.NativeTRGSWAggregateConcreteChannel
