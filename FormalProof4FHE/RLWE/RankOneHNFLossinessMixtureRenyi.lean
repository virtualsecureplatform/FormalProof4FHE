/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.RankOneHNFLossinessRenyi
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Optimized Mixture-Reference Renyi Bounds

This module formalizes the finite and algebraic content of
`sketch/mahalanobisimprove.md`.  Instead of comparing every shifted channel component with one
fixed zero-centred Gaussian, it optimizes the reference over the complete mixture.

The finite theory is native:

* the arbitrary-reference guessing bound;
* the exact optimized overlap functional and its minimizing Renyi centre;
* the actual-output-marginal and posterior-moment identities;
* finite mixture references and local log-sum-exp/relative-entropy bounds;
* cancellation for a uniform finite support and the resulting exponential criterion; and
* averaging over the complete descriptor/leakage value.

The only continuous analytic boundary is packaged by
`EqualCovarianceGaussianMixtureCertificate`: its fields are precisely the equal-covariance
Gaussian likelihood-ratio integral and the standard-Gaussian linear MGF.  The cluster-overlap
theorem and every subsequent entropy/distance calculation are proved from those fields.  No
axiom is introduced.
-/

open OracleComp
open scoped ENNReal BigOperators InnerProductSpace

namespace FormalProof4FHE.RLWE.RankOneHNFLossinessMixtureRenyi

open RankOneHNFLossinessRLWENTRU
open RankOneHNFLossinessRefined
open RankOneHNFLossinessSupportAware
open RankOneHNFLossinessRenyi

noncomputable section

/-! ## The exact optimized finite overlap functional -/

/-- The joint real mass `pi(s) W_s(y)`. -/
def jointPointMass {Secret Output : Type}
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (secret : Secret) (output : Output) : ℝ :=
  realPointMass prior secret * realPointMass (channel secret) output

theorem jointPointMass_nonneg
    {Secret Output : Type} [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (secret : Secret) (output : Output) :
    0 ≤ jointPointMass prior channel secret output :=
  mul_nonneg (realPointMass_nonneg prior secret)
    (realPointMass_nonneg (channel secret) output)

/-- The pointwise order-`alpha` joint-mass sum
`A(y) = sum_s (pi(s) W_s(y))^alpha`. -/
def renyiAmplitude
    {Secret Output : Type} [Fintype Secret]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (alpha : ℝ) (output : Output) : ℝ :=
  ∑ secret, jointPointMass prior channel secret output ^ alpha

theorem renyiAmplitude_nonneg
    {Secret Output : Type} [Fintype Secret]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (alpha : ℝ) (output : Output) :
    0 ≤ renyiAmplitude prior channel alpha output :=
  Finset.sum_nonneg fun secret _ ↦
    Real.rpow_nonneg (jointPointMass_nonneg prior channel secret output) alpha

/-- The optimized finite overlap functional from equation (3):
`sum_y A(y)^(1/alpha)`. -/
def optimizedRenyiOverlap
    {Secret Output : Type} [Fintype Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (alpha : ℝ) : ℝ :=
  ∑ output, renyiAmplitude prior channel alpha output ^ (1 / alpha)

theorem optimizedRenyiOverlap_nonneg
    {Secret Output : Type} [Fintype Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (alpha : ℝ) :
    0 ≤ optimizedRenyiOverlap prior channel alpha :=
  Finset.sum_nonneg fun output _ ↦
    Real.rpow_nonneg (renyiAmplitude_nonneg prior channel alpha output) (1 / alpha)

/-- **Optimized finite Renyi guessing theorem (equation (3)).**  This statement needs no
reference distribution and remains valid when some output points are unreachable. -/
theorem conditionalGuessingProbability_le_optimizedRenyiOverlap
    {Secret Output : Type}
    [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (alpha : ℝ) (halpha : 1 < alpha) :
    (conditionalGuessingProbability
      (conditionalChannelJoint prior channel)).toReal ≤
      optimizedRenyiOverlap prior channel alpha := by
  let joint := conditionalChannelJoint prior channel
  rw [conditionalGuessingProbability_toReal_eq_realFiniteGuessingMass]
  unfold realFiniteGuessingMass optimizedRenyiOverlap
  apply Finset.sum_le_sum
  intro output _
  rw [probOutput_conditionalChannelJoint, ENNReal.toReal_mul]
  change jointPointMass prior channel (maximizingSecret joint output) output ≤
    renyiAmplitude prior channel alpha output ^ (1 / alpha)
  exact le_rpow_sum_rpow
    (fun secret ↦ jointPointMass prior channel secret output)
    (fun secret ↦ jointPointMass_nonneg prior channel secret output)
    alpha (lt_trans zero_lt_one halpha) (maximizingSecret joint output)

/-- The arbitrary-reference functional `J_alpha(Q)` from equation (1). -/
def referenceRenyiFunctional
    {Secret Output : Type} [Fintype Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (reference : PositiveProbabilityTable Output) (alpha : ℝ) : ℝ :=
  ∑ secret,
    realPointMass prior secret ^ alpha *
      finiteRenyiMoment alpha
        (fun output ↦ realPointMass (channel secret) output) reference.mass

/-- **Arbitrary-reference theorem (equation (1)).** -/
theorem arbitraryReferenceRenyiGuessingBound
    {Secret Output : Type}
    [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (reference : PositiveProbabilityTable Output)
    (alpha : ℝ) (halpha : 1 < alpha) :
    (conditionalGuessingProbability
      (conditionalChannelJoint prior channel)).toReal ≤
      (referenceRenyiFunctional prior channel reference alpha) ^ (1 / alpha) := by
  simpa only [referenceRenyiFunctional] using
    conditionalRenyiGuessingBound prior channel reference alpha halpha

/-- Rearrange `J_alpha(Q)` output by output. -/
theorem referenceRenyiFunctional_eq_weightedAmplitude
    {Secret Output : Type} [Fintype Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (reference : PositiveProbabilityTable Output) (alpha : ℝ) :
    referenceRenyiFunctional prior channel reference alpha =
      ∑ output, reference.mass output *
        (renyiAmplitude prior channel alpha output /
          reference.mass output ^ alpha) := by
  unfold referenceRenyiFunctional finiteRenyiMoment renyiAmplitude jointPointMass
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro output _
  rw [Finset.sum_div, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro secret _
  rw [Real.mul_rpow (realPointMass_nonneg prior secret)
    (realPointMass_nonneg (channel secret) output)]
  rw [reference_mul_div_rpow _ _ _ (reference.positive output)]
  ring

/-- Every reference-root is at least the optimized overlap.  This is the finite Renyi-centre
variational inequality. -/
theorem optimizedRenyiOverlap_le_referenceRoot
    {Secret Output : Type} [Fintype Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (reference : PositiveProbabilityTable Output)
    (alpha : ℝ) (halpha : 1 < alpha) :
    optimizedRenyiOverlap prior channel alpha ≤
      (referenceRenyiFunctional prior channel reference alpha) ^ (1 / alpha) := by
  let normalized : Output → ℝ := fun output ↦
    renyiAmplitude prior channel alpha output / reference.mass output ^ alpha
  have hnormalized : ∀ output, 0 ≤ normalized output := by
    intro output
    exact div_nonneg (renyiAmplitude_nonneg prior channel alpha output)
      (Real.rpow_nonneg (reference.nonneg output) alpha)
  calc
    optimizedRenyiOverlap prior channel alpha =
        ∑ output, reference.mass output * normalized output ^ (1 / alpha) := by
      unfold optimizedRenyiOverlap normalized
      apply Finset.sum_congr rfl
      intro output _
      exact rpow_eq_mul_div_rpow _ _ _
        (renyiAmplitude_nonneg prior channel alpha output)
        (reference.positive output) (lt_trans zero_lt_one halpha)
    _ ≤ (∑ output, reference.mass output * normalized output) ^ (1 / alpha) :=
      sum_mul_rpow_le_rpow_sum_mul reference.mass normalized reference.nonneg
        reference.sum_mass hnormalized alpha halpha
    _ = (referenceRenyiFunctional prior channel reference alpha) ^ (1 / alpha) := by
      rw [referenceRenyiFunctional_eq_weightedAmplitude]

/-! ## The exact finite Renyi centre -/

/-- The normalized order-`alpha` Renyi centre from equation (2). -/
def renyiCenter
    {Secret Output : Type} [Fintype Secret] [Fintype Output]
    [Nonempty Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (alpha : ℝ) (_halpha : 1 < alpha)
    (hamplitude : ∀ output, 0 < renyiAmplitude prior channel alpha output) :
    PositiveProbabilityTable Output where
  mass output :=
    renyiAmplitude prior channel alpha output ^ (1 / alpha) /
      optimizedRenyiOverlap prior channel alpha
  positive output := by
    apply div_pos
    · exact Real.rpow_pos_of_pos (hamplitude output) _
    · unfold optimizedRenyiOverlap
      exact Finset.sum_pos
        (fun candidate _ ↦ Real.rpow_pos_of_pos (hamplitude candidate) _)
        Finset.univ_nonempty
  sum_mass := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt <| Finset.sum_pos
      (fun output _ ↦ Real.rpow_pos_of_pos (hamplitude output) _)
      Finset.univ_nonempty)

@[simp]
theorem renyiCenter_mass
    {Secret Output : Type} [Fintype Secret] [Fintype Output]
    [Nonempty Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (alpha : ℝ) (halpha : 1 < alpha)
    (hamplitude : ∀ output, 0 < renyiAmplitude prior channel alpha output)
    (output : Output) :
    (renyiCenter prior channel alpha halpha hamplitude).mass output =
      renyiAmplitude prior channel alpha output ^ (1 / alpha) /
        optimizedRenyiOverlap prior channel alpha := rfl

theorem renyiAmplitude_div_center_rpow
    {Secret Output : Type} [Fintype Secret] [Fintype Output]
    [Nonempty Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (alpha : ℝ) (halpha : 1 < alpha)
    (hamplitude : ∀ output, 0 < renyiAmplitude prior channel alpha output)
    (output : Output) :
    renyiAmplitude prior channel alpha output /
        (renyiCenter prior channel alpha halpha hamplitude).mass output ^ alpha =
      optimizedRenyiOverlap prior channel alpha ^ alpha := by
  let amplitude := renyiAmplitude prior channel alpha output
  let normalization := optimizedRenyiOverlap prior channel alpha
  have halphaPos : 0 < alpha := lt_trans zero_lt_one halpha
  have hampPos : 0 < amplitude := hamplitude output
  have hnormPos : 0 < normalization := by
    unfold normalization optimizedRenyiOverlap
    exact Finset.sum_pos
      (fun candidate _ ↦ Real.rpow_pos_of_pos (hamplitude candidate) _)
      Finset.univ_nonempty
  have hampRoot : (amplitude ^ (1 / alpha)) ^ alpha = amplitude := by
    rw [← Real.rpow_mul hampPos.le]
    field_simp
    simp
  rw [renyiCenter_mass]
  change amplitude / (amplitude ^ (1 / alpha) / normalization) ^ alpha =
    normalization ^ alpha
  rw [Real.div_rpow (Real.rpow_nonneg hampPos.le _) hnormPos.le, hampRoot]
  field_simp [ne_of_gt hampPos, ne_of_gt (Real.rpow_pos_of_pos hnormPos alpha)]

/-- Substitution of the Renyi centre gives exactly the optimized objective. -/
theorem referenceRenyiFunctional_renyiCenter
    {Secret Output : Type} [Fintype Secret] [Fintype Output]
    [Nonempty Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (alpha : ℝ) (halpha : 1 < alpha)
    (hamplitude : ∀ output, 0 < renyiAmplitude prior channel alpha output) :
    referenceRenyiFunctional prior channel
        (renyiCenter prior channel alpha halpha hamplitude) alpha =
      optimizedRenyiOverlap prior channel alpha ^ alpha := by
  rw [referenceRenyiFunctional_eq_weightedAmplitude]
  simp_rw [renyiAmplitude_div_center_rpow prior channel alpha halpha hamplitude]
  rw [← Finset.sum_mul]
  rw [(renyiCenter prior channel alpha halpha hamplitude).sum_mass, one_mul]

/-- Equation (2) really is optimal: its objective root equals the overlap functional and is no
larger than the root obtained from any positive reference. -/
theorem renyiCenter_root_eq_and_le
    {Secret Output : Type} [Fintype Secret] [Fintype Output]
    [Nonempty Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (reference : PositiveProbabilityTable Output)
    (alpha : ℝ) (halpha : 1 < alpha)
    (hamplitude : ∀ output, 0 < renyiAmplitude prior channel alpha output) :
    (referenceRenyiFunctional prior channel
        (renyiCenter prior channel alpha halpha hamplitude) alpha) ^ (1 / alpha) =
        optimizedRenyiOverlap prior channel alpha ∧
      (referenceRenyiFunctional prior channel
        (renyiCenter prior channel alpha halpha hamplitude) alpha) ^ (1 / alpha) ≤
        (referenceRenyiFunctional prior channel reference alpha) ^ (1 / alpha) := by
  have hnormalization : 0 ≤ optimizedRenyiOverlap prior channel alpha :=
    optimizedRenyiOverlap_nonneg prior channel alpha
  have hroot :
      (referenceRenyiFunctional prior channel
        (renyiCenter prior channel alpha halpha hamplitude) alpha) ^ (1 / alpha) =
          optimizedRenyiOverlap prior channel alpha := by
    rw [referenceRenyiFunctional_renyiCenter]
    rw [← Real.rpow_mul hnormalization]
    field_simp [ne_of_gt (lt_trans zero_lt_one halpha)]
    simp
  exact ⟨hroot, hroot.trans_le
    (optimizedRenyiOverlap_le_referenceRoot prior channel reference alpha halpha)⟩

/-! ## The actual output marginal and posterior moments -/

/-- The real output-marginal mass `P_Y(y) = sum_s pi(s) W_s(y)`. -/
def outputMarginalMass
    {Secret Output : Type} [Fintype Secret]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (output : Output) : ℝ :=
  ∑ secret, jointPointMass prior channel secret output

theorem outputMarginalMass_nonneg
    {Secret Output : Type} [Fintype Secret]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (output : Output) :
    0 ≤ outputMarginalMass prior channel output :=
  Finset.sum_nonneg fun secret _ ↦ jointPointMass_nonneg prior channel secret output

theorem sum_outputMarginalMass
    {Secret Output : Type} [Fintype Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output) :
    ∑ output, outputMarginalMass prior channel output = 1 := by
  unfold outputMarginalMass jointPointMass
  rw [Finset.sum_comm]
  calc
    (∑ secret, ∑ output,
        realPointMass prior secret * realPointMass (channel secret) output) =
        ∑ secret, realPointMass prior secret *
          ∑ output, realPointMass (channel secret) output := by
      apply Finset.sum_congr rfl
      intro secret _
      rw [Finset.mul_sum]
    _ = ∑ secret, realPointMass prior secret := by
      apply Finset.sum_congr rfl
      intro secret _
      have hchannel : ∑ output, realPointMass (channel secret) output = 1 := by
        simpa only [realPointMass] using sum_probOutput_toReal_eq_one (channel secret)
      rw [hchannel, mul_one]
    _ = 1 := by
      simpa only [realPointMass] using sum_probOutput_toReal_eq_one prior

/-- Package a full-support output marginal as the positive reference used in equation (5). -/
def outputMarginalReference
    {Secret Output : Type} [Fintype Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (hpositive : ∀ output, 0 < outputMarginalMass prior channel output) :
    PositiveProbabilityTable Output where
  mass := outputMarginalMass prior channel
  positive := hpositive
  sum_mass := sum_outputMarginalMass prior channel

@[simp]
theorem outputMarginalReference_mass
    {Secret Output : Type} [Fintype Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (hpositive : ∀ output, 0 < outputMarginalMass prior channel output)
    (output : Output) :
    (outputMarginalReference prior channel hpositive).mass output =
      outputMarginalMass prior channel output := rfl

/-- The finite posterior `pi(s | y)`. -/
def posteriorMass
    {Secret Output : Type} [Fintype Secret]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (output : Output) (secret : Secret) : ℝ :=
  jointPointMass prior channel secret output /
    outputMarginalMass prior channel output

theorem posteriorMass_nonneg
    {Secret Output : Type} [Fintype Secret]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (hpositive : ∀ output, 0 < outputMarginalMass prior channel output)
    (output : Output) (secret : Secret) :
    0 ≤ posteriorMass prior channel output secret :=
  div_nonneg (jointPointMass_nonneg prior channel secret output)
    (hpositive output).le

theorem sum_posteriorMass
    {Secret Output : Type} [Fintype Secret]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (hpositive : ∀ output, 0 < outputMarginalMass prior channel output)
    (output : Output) :
    ∑ secret, posteriorMass prior channel output secret = 1 := by
  unfold posteriorMass outputMarginalMass
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (hpositive output))

/-- The posterior order-`alpha` power sum. -/
def posteriorAlphaMoment
    {Secret Output : Type} [Fintype Secret]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (alpha : ℝ) (output : Output) : ℝ :=
  ∑ secret, posteriorMass prior channel output secret ^ alpha

theorem posteriorAlphaMoment_nonneg
    {Secret Output : Type} [Fintype Secret]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (hpositive : ∀ output, 0 < outputMarginalMass prior channel output)
    (alpha : ℝ) (output : Output) :
    0 ≤ posteriorAlphaMoment prior channel alpha output :=
  Finset.sum_nonneg fun secret _ ↦
    Real.rpow_nonneg (posteriorMass_nonneg prior channel hpositive output secret) alpha

/-- Bayes normalization identifies the posterior power sum with `A(y) / P_Y(y)^alpha`. -/
theorem posteriorAlphaMoment_eq_amplitude_div
    {Secret Output : Type} [Fintype Secret]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (_hpositive : ∀ output, 0 < outputMarginalMass prior channel output)
    (alpha : ℝ) (output : Output) :
    posteriorAlphaMoment prior channel alpha output =
      renyiAmplitude prior channel alpha output /
        outputMarginalMass prior channel output ^ alpha := by
  unfold posteriorAlphaMoment posteriorMass renyiAmplitude
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro secret _
  exact Real.div_rpow
    (jointPointMass_nonneg prior channel secret output)
    (outputMarginalMass_nonneg prior channel output) alpha

/-- **Expected posterior `L^alpha` norm (equation (4)).**  The optimized overlap is exactly the
output-marginal expectation of the posterior norm. -/
theorem optimizedRenyiOverlap_eq_expectedPosteriorNorm
    {Secret Output : Type} [Fintype Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (hpositive : ∀ output, 0 < outputMarginalMass prior channel output)
    (alpha : ℝ) (halpha : 0 < alpha) :
    optimizedRenyiOverlap prior channel alpha =
      ∑ output, outputMarginalMass prior channel output *
        posteriorAlphaMoment prior channel alpha output ^ (1 / alpha) := by
  unfold optimizedRenyiOverlap
  apply Finset.sum_congr rfl
  intro output _
  rw [posteriorAlphaMoment_eq_amplitude_div prior channel hpositive]
  exact rpow_eq_mul_div_rpow _ _ _
    (renyiAmplitude_nonneg prior channel alpha output)
    (hpositive output) halpha

theorem conditionalGuessingProbability_le_expectedPosteriorNorm
    {Secret Output : Type}
    [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (hpositive : ∀ output, 0 < outputMarginalMass prior channel output)
    (alpha : ℝ) (halpha : 1 < alpha) :
    (conditionalGuessingProbability
      (conditionalChannelJoint prior channel)).toReal ≤
      ∑ output, outputMarginalMass prior channel output *
        posteriorAlphaMoment prior channel alpha output ^ (1 / alpha) := by
  rw [← optimizedRenyiOverlap_eq_expectedPosteriorNorm prior channel hpositive alpha
    (lt_trans zero_lt_one halpha)]
  exact conditionalGuessingProbability_le_optimizedRenyiOverlap prior channel alpha halpha

/-- The actual-marginal reference functional is the expected posterior power sum. -/
theorem referenceRenyiFunctional_outputMarginal
    {Secret Output : Type} [Fintype Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (hpositive : ∀ output, 0 < outputMarginalMass prior channel output)
    (alpha : ℝ) :
    referenceRenyiFunctional prior channel
        (outputMarginalReference prior channel hpositive) alpha =
      ∑ output, outputMarginalMass prior channel output *
        posteriorAlphaMoment prior channel alpha output := by
  rw [referenceRenyiFunctional_eq_weightedAmplitude]
  apply Finset.sum_congr rfl
  intro output _
  rw [outputMarginalReference_mass]
  rw [posteriorAlphaMoment_eq_amplitude_div prior channel hpositive]

/-- **Actual-output-marginal theorem (equation (5)).** -/
theorem conditionalGuessingProbability_le_posteriorMomentRoot
    {Secret Output : Type}
    [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (hpositive : ∀ output, 0 < outputMarginalMass prior channel output)
    (alpha : ℝ) (halpha : 1 < alpha) :
    (conditionalGuessingProbability
      (conditionalChannelJoint prior channel)).toReal ≤
      (∑ output, outputMarginalMass prior channel output *
        posteriorAlphaMoment prior channel alpha output) ^ (1 / alpha) := by
  rw [← referenceRenyiFunctional_outputMarginal prior channel hpositive]
  exact arbitraryReferenceRenyiGuessingBound prior channel
    (outputMarginalReference prior channel hpositive) alpha halpha

/-- **Posterior collision bound (equation (6)).** -/
theorem conditionalGuessingProbability_le_sqrt_posteriorCollision
    {Secret Output : Type}
    [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (hpositive : ∀ output, 0 < outputMarginalMass prior channel output) :
    (conditionalGuessingProbability
      (conditionalChannelJoint prior channel)).toReal ≤
      Real.sqrt (∑ output, outputMarginalMass prior channel output *
        posteriorAlphaMoment prior channel 2 output) := by
  simpa only [Real.sqrt_eq_rpow, one_div] using
    conditionalGuessingProbability_le_posteriorMomentRoot
      prior channel hpositive 2 (by norm_num)

/-- Posterior power sums, and hence the marginal-reference objective, never exceed one.  Thus the
mixture reference has the correct trivial endpoint in the disjoint-component regime. -/
theorem expectedPosteriorAlphaMoment_le_one
    {Secret Output : Type}
    [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (hpositive : ∀ output, 0 < outputMarginalMass prior channel output)
    (alpha : ℝ) (halpha : 1 ≤ alpha) :
    (∑ output, outputMarginalMass prior channel output *
      posteriorAlphaMoment prior channel alpha output) ≤ 1 := by
  have hposteriorLe : ∀ output secret,
      posteriorMass prior channel output secret ≤ 1 := by
    intro output secret
    have hsingle : posteriorMass prior channel output secret ≤
        ∑ candidate, posteriorMass prior channel output candidate :=
      Finset.single_le_sum
        (fun candidate _ ↦ posteriorMass_nonneg prior channel hpositive output candidate)
        (Finset.mem_univ secret)
    simpa [sum_posteriorMass prior channel hpositive output] using hsingle
  calc
    (∑ output, outputMarginalMass prior channel output *
        posteriorAlphaMoment prior channel alpha output) ≤
        ∑ output, outputMarginalMass prior channel output * 1 := by
      apply Finset.sum_le_sum
      intro output _
      apply mul_le_mul_of_nonneg_left _
        (outputMarginalMass_nonneg prior channel output)
      unfold posteriorAlphaMoment
      calc
        (∑ secret, posteriorMass prior channel output secret ^ alpha) ≤
            ∑ secret, posteriorMass prior channel output secret := by
          apply Finset.sum_le_sum
          intro secret _
          exact Real.rpow_le_self_of_le_one
            (posteriorMass_nonneg prior channel hpositive output secret)
            (hposteriorLe output secret) halpha
        _ = 1 := sum_posteriorMass prior channel hpositive output
    _ = 1 := by simpa using sum_outputMarginalMass prior channel

/-- In the fully overlapping benchmark the posterior is the prior, so equation (4) reduces to
the prior `L^alpha` norm. -/
theorem expectedPosteriorNorm_eq_priorNorm_of_posterior_eq
    {Secret Output : Type}
    [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (alpha : ℝ)
    (posterior_eq : ∀ output secret,
      posteriorMass prior channel output secret = realPointMass prior secret) :
    (∑ output, outputMarginalMass prior channel output *
      posteriorAlphaMoment prior channel alpha output ^ (1 / alpha)) =
      (∑ secret, realPointMass prior secret ^ alpha) ^ (1 / alpha) := by
  have hmoment : ∀ output,
      posteriorAlphaMoment prior channel alpha output =
        ∑ secret, realPointMass prior secret ^ alpha := by
    intro output
    unfold posteriorAlphaMoment
    apply Finset.sum_congr rfl
    intro secret _
    rw [posterior_eq]
  simp_rw [hmoment]
  rw [← Finset.sum_mul, sum_outputMarginalMass, one_mul]

/-- In the disjoint-component benchmark every posterior is a point mass, so the
actual-marginal objective in equation (5) is exactly one. -/
theorem expectedPosteriorAlphaMoment_eq_one_of_pointMass
    {Secret Output : Type}
    [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (alpha : ℝ) (halpha : 0 < alpha) (selected : Output → Secret)
    (posterior_eq : ∀ output secret,
      posteriorMass prior channel output secret =
        if secret = selected output then 1 else 0) :
    (∑ output, outputMarginalMass prior channel output *
      posteriorAlphaMoment prior channel alpha output) = 1 := by
  have hmoment : ∀ output,
      posteriorAlphaMoment prior channel alpha output = 1 := by
    intro output
    unfold posteriorAlphaMoment
    simp_rw [posterior_eq]
    simp [Real.zero_rpow (ne_of_gt halpha)]
  simp_rw [hmoment, mul_one]
  exact sum_outputMarginalMass prior channel

/-! ## Finite mixtures and local kernels -/

/-- A positive mixture of positive finite probability tables. -/
def positiveProbabilityMixture
    {Index Output : Type} [Fintype Index] [Nonempty Index] [Fintype Output]
    (weight : PositiveProbabilityTable Index)
    (component : Index → PositiveProbabilityTable Output) :
    PositiveProbabilityTable Output where
  mass output := ∑ index, weight.mass index * (component index).mass output
  positive output :=
    Finset.sum_pos
      (fun index _ ↦ mul_pos (weight.positive index) ((component index).positive output))
      Finset.univ_nonempty
  sum_mass := by
    rw [Finset.sum_comm]
    calc
      (∑ index, ∑ output, weight.mass index * (component index).mass output) =
          ∑ index, weight.mass index * ∑ output, (component index).mass output := by
        apply Finset.sum_congr rfl
        intro index _
        rw [Finset.mul_sum]
      _ = ∑ index, weight.mass index := by
        apply Finset.sum_congr rfl
        intro index _
        rw [(component index).sum_mass, mul_one]
      _ = 1 := weight.sum_mass

@[simp]
theorem positiveProbabilityMixture_mass
    {Index Output : Type} [Fintype Index] [Nonempty Index] [Fintype Output]
    (weight : PositiveProbabilityTable Index)
    (component : Index → PositiveProbabilityTable Output) (output : Output) :
    (positiveProbabilityMixture weight component).mass output =
      ∑ index, weight.mass index * (component index).mass output := rfl

/-- A local cloud around every secret.  `neighbor` is injective so its weighted mixture is a
subsum of the global codeword mixture.  A separate finite `Neighbor` type permits genuine local
support without assigning artificial positive mass to every global secret. -/
structure LocalKernel (Secret Neighbor : Type) [Fintype Neighbor] where
  neighbor : Secret → Neighbor → Secret
  neighbor_injective : ∀ secret, Function.Injective (neighbor secret)
  distribution : Secret → PositiveProbabilityTable Neighbor

/-- Relative entropy of the local cloud with respect to the global mixture weights. -/
def LocalKernel.relativeEntropy
    {Secret Neighbor : Type} [Fintype Secret] [Fintype Neighbor]
    (kernel : LocalKernel Secret Neighbor)
    (reference : PositiveProbabilityTable Secret) (secret : Secret) : ℝ :=
  ∑ neighbor,
    (kernel.distribution secret).mass neighbor *
      Real.log ((kernel.distribution secret).mass neighbor /
        reference.mass (kernel.neighbor secret neighbor))

/-- Shannon entropy in nats of one local cloud. -/
def LocalKernel.entropy
    {Secret Neighbor : Type} [Fintype Neighbor]
    (kernel : LocalKernel Secret Neighbor) (secret : Secret) : ℝ :=
  -∑ neighbor,
    (kernel.distribution secret).mass neighbor *
      Real.log ((kernel.distribution secret).mass neighbor)

/-- Average pairwise squared whitened distance in a local cloud. -/
def LocalKernel.averageSquaredDistance
    {Secret Neighbor Vector : Type} [Fintype Neighbor]
    [SeminormedAddCommGroup Vector]
    (kernel : LocalKernel Secret Neighbor)
    (difference : Secret → Secret → Vector) (secret : Secret) : ℝ :=
  ∑ neighbor,
    (kernel.distribution secret).mass neighbor *
      ‖difference (kernel.neighbor secret neighbor) secret‖ ^ 2

theorem LocalKernel.averageSquaredDistance_nonneg
    {Secret Neighbor Vector : Type} [Fintype Neighbor]
    [SeminormedAddCommGroup Vector]
    (kernel : LocalKernel Secret Neighbor)
    (difference : Secret → Secret → Vector) (secret : Secret) :
    0 ≤ kernel.averageSquaredDistance difference secret :=
  Finset.sum_nonneg fun neighbor _ ↦
    mul_nonneg ((kernel.distribution secret).nonneg neighbor) (sq_nonneg _)

/-- Whitened displacement of the local-cloud barycentre. -/
def LocalKernel.barycenter
    {Secret Neighbor Vector : Type} [Fintype Neighbor]
    [SeminormedAddCommGroup Vector] [NormedSpace ℝ Vector]
    (kernel : LocalKernel Secret Neighbor)
    (difference : Secret → Secret → Vector) (secret : Secret) : Vector :=
  ∑ neighbor,
    (kernel.distribution secret).mass neighbor •
      difference (kernel.neighbor secret neighbor) secret

/-- A finite sum over an injectively embedded local type is bounded by the complete nonnegative
sum over the global type. -/
theorem sum_comp_le_sum_of_injective
    {Local Global : Type} [Fintype Local] [Fintype Global] [DecidableEq Global]
    (embed : Local → Global) (hinjective : Function.Injective embed)
    (value : Global → ℝ) (value_nonneg : ∀ global, 0 ≤ value global) :
    (∑ index, value (embed index)) ≤ ∑ global, value global := by
  calc
    (∑ index, value (embed index)) =
        ∑ global ∈ (Finset.univ : Finset Local).image embed, value global := by
      symm
      rw [Finset.sum_image]
      intro left _ right _ heq
      exact hinjective heq
    _ ≤ ∑ global ∈ (Finset.univ : Finset Global), value global :=
      Finset.sum_le_sum_of_subset_of_nonneg (by simp)
        (fun global _ _ ↦ value_nonneg global)
    _ = ∑ global, value global := rfl

/-- Finite weighted log-sum-exp variational inequality.  This is weighted AM--GM in the exact
form used by the local-overlap proof. -/
theorem exp_neg_relativeEntropy_add_expectation_le_mixture
    {Local Global : Type}
    [Fintype Local] [Fintype Global] [DecidableEq Global]
    (weight : PositiveProbabilityTable Local)
    (reference : PositiveProbabilityTable Global)
    (embed : Local → Global) (hinjective : Function.Injective embed)
    (score : Global → ℝ) :
    Real.exp
        (-(∑ index, weight.mass index *
            Real.log (weight.mass index / reference.mass (embed index))) +
          ∑ index, weight.mass index * score (embed index)) ≤
      ∑ global, reference.mass global * Real.exp (score global) := by
  let tilted : Local → ℝ := fun index ↦
    Real.log (reference.mass (embed index) / weight.mass index) +
      score (embed index)
  have hjensen := convexOn_exp.map_sum_le
    (t := Finset.univ) (w := weight.mass) (p := tilted)
    (fun index _ ↦ weight.nonneg index) weight.sum_mass
    (fun index _ ↦ Set.mem_univ (tilted index))
  have hexponent :
      (∑ index, weight.mass index * tilted index) =
        -(∑ index, weight.mass index *
            Real.log (weight.mass index / reference.mass (embed index))) +
          ∑ index, weight.mass index * score (embed index) := by
    unfold tilted
    have hlog : ∀ index,
        Real.log (reference.mass (embed index) / weight.mass index) =
          -Real.log (weight.mass index / reference.mass (embed index)) := by
      intro index
      rw [Real.log_div (ne_of_gt (reference.positive (embed index)))
          (ne_of_gt (weight.positive index)),
        Real.log_div (ne_of_gt (weight.positive index))
          (ne_of_gt (reference.positive (embed index)))]
      ring
    simp_rw [hlog, mul_add, mul_neg, Finset.sum_add_distrib]
    rw [Finset.sum_neg_distrib]
  have hterm : ∀ index,
      weight.mass index * Real.exp (tilted index) =
        reference.mass (embed index) * Real.exp (score (embed index)) := by
    intro index
    unfold tilted
    rw [Real.exp_add,
      Real.exp_log (div_pos (reference.positive (embed index)) (weight.positive index))]
    field_simp [ne_of_gt (weight.positive index),
      ne_of_gt (reference.positive (embed index))]
  calc
    Real.exp
        (-(∑ index, weight.mass index *
            Real.log (weight.mass index / reference.mass (embed index))) +
          ∑ index, weight.mass index * score (embed index)) =
        Real.exp (∑ index, weight.mass index * tilted index) := by rw [hexponent]
    _ ≤ ∑ index, weight.mass index * Real.exp (tilted index) := by
      simpa only [smul_eq_mul] using hjensen
    _ = ∑ index,
        reference.mass (embed index) * Real.exp (score (embed index)) := by
      apply Finset.sum_congr rfl
      intro index _
      exact hterm index
    _ ≤ ∑ global, reference.mass global * Real.exp (score global) :=
      sum_comp_le_sum_of_injective embed hinjective
        (fun global ↦ reference.mass global * Real.exp (score global))
        (fun global ↦ mul_nonneg (reference.nonneg global) (Real.exp_nonneg _))

/-! ## Equal-covariance Gaussian mixture boundary and cluster theorem -/

/-- The small amount of expectation structure used by the Gaussian cluster proof.  Both finite
expectations and measure integrals satisfy these two laws. -/
structure PositiveExpectation (Sample : Type) where
  expect : (Sample → ℝ) → ℝ
  monotone : ∀ {left right : Sample → ℝ},
    (∀ sample, left sample ≤ right sample) → expect left ≤ expect right
  const_mul : ∀ (constant : ℝ) (value : Sample → ℝ),
    expect (fun sample ↦ constant * value sample) = constant * expect value

theorem PositiveExpectation.congr
    {Sample : Type} (expectation : PositiveExpectation Sample)
    {left right : Sample → ℝ} (heq : ∀ sample, left sample = right sample) :
    expectation.expect left = expectation.expect right :=
  le_antisymm
    (expectation.monotone fun sample ↦ (heq sample).le)
    (expectation.monotone fun sample ↦ (heq sample).ge)

/-- Standard-Gaussian linear MGF, isolated as the continuous analytic boundary. -/
structure StandardGaussianExpectationCertificate (Vector : Type)
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector] where
  expectation : PositiveExpectation Vector
  mgf_eq : ∀ (theta : ℝ) (vector : Vector),
    expectation.expect
        (fun noise ↦ Real.exp (theta * ⟪vector, noise⟫_ℝ)) =
      Real.exp (theta ^ 2 * ‖vector‖ ^ 2 / 2)

/-- The equal-covariance Gaussian log-likelihood ratio
`<d(t,s),z> - ‖d(t,s)‖²/2`. -/
def gaussianLikelihoodScore
    {Secret Vector : Type} [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (difference : Secret → Secret → Vector)
    (candidate secret : Secret) (noise : Vector) : ℝ :=
  ⟪difference candidate secret, noise⟫_ℝ -
    ‖difference candidate secret‖ ^ 2 / 2

/-- Averaging Gaussian likelihood scores produces exactly the barycentre linear term minus half
the average squared distance. -/
theorem LocalKernel.average_gaussianLikelihoodScore
    {Secret Neighbor Vector : Type} [Fintype Neighbor]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (kernel : LocalKernel Secret Neighbor)
    (difference : Secret → Secret → Vector) (secret : Secret) (noise : Vector) :
    (∑ neighbor,
        (kernel.distribution secret).mass neighbor *
          gaussianLikelihoodScore difference
            (kernel.neighbor secret neighbor) secret noise) =
      ⟪kernel.barycenter difference secret, noise⟫_ℝ -
        kernel.averageSquaredDistance difference secret / 2 := by
  unfold gaussianLikelihoodScore LocalKernel.barycenter
    LocalKernel.averageSquaredDistance
  rw [sum_inner]
  simp_rw [real_inner_smul_left, mul_sub]
  rw [Finset.sum_sub_distrib]
  congr 1
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro neighbor _
  ring

/-- Proof-carrying version of the exact Gaussian-mixture overlap formula (7).  `overlap_eq`
contains the equal-covariance density calculation; `gaussian.mgf_eq` contains the standard
Gaussian integral.  Everything else in the local-cluster theorem is native Lean algebra. -/
structure EqualCovarianceGaussianMixtureCertificate
    (Secret Output Vector : Type)
    [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (component : Secret → PositiveProbabilityTable Output)
    (mixtureWeight : PositiveProbabilityTable Secret) (alpha : ℝ) where
  difference : Secret → Secret → Vector
  gaussian : StandardGaussianExpectationCertificate Vector
  overlap_eq : ∀ secret,
    finiteRenyiMoment alpha (component secret).mass
        (positiveProbabilityMixture mixtureWeight component).mass =
      gaussian.expectation.expect (fun noise ↦
        (∑ candidate, mixtureWeight.mass candidate *
          Real.exp (gaussianLikelihoodScore difference candidate secret noise)) ^
            (1 - alpha))

/-- **Gaussian cluster-overlap theorem (equation (9)).** -/
theorem EqualCovarianceGaussianMixtureCertificate.moment_le_localCluster
    {Secret Neighbor Output Vector : Type}
    [Fintype Secret] [Nonempty Secret] [DecidableEq Secret]
    [Fintype Neighbor] [Fintype Output]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    {component : Secret → PositiveProbabilityTable Output}
    {mixtureWeight : PositiveProbabilityTable Secret} {alpha : ℝ}
    (certificate : EqualCovarianceGaussianMixtureCertificate
      Secret Output Vector component mixtureWeight alpha)
    (kernel : LocalKernel Secret Neighbor)
    (halpha : 1 < alpha) (secret : Secret) :
    finiteRenyiMoment alpha (component secret).mass
        (positiveProbabilityMixture mixtureWeight component).mass ≤
      Real.exp
        ((alpha - 1) * kernel.relativeEntropy mixtureWeight secret +
          (alpha - 1) / 2 *
            kernel.averageSquaredDistance certificate.difference secret +
          (alpha - 1) ^ 2 / 2 *
            ‖kernel.barycenter certificate.difference secret‖ ^ 2) := by
  let r : ℝ := alpha - 1
  let divergence := kernel.relativeEntropy mixtureWeight secret
  let averageDistance :=
    kernel.averageSquaredDistance certificate.difference secret
  let barycentre := kernel.barycenter certificate.difference secret
  have hr : 0 < r := sub_pos.mpr halpha
  have hlower : ∀ noise,
      Real.exp (-divergence + ⟪barycentre, noise⟫_ℝ - averageDistance / 2) ≤
        ∑ candidate, mixtureWeight.mass candidate *
          Real.exp (gaussianLikelihoodScore certificate.difference
            candidate secret noise) := by
    intro noise
    calc
      Real.exp (-divergence + ⟪barycentre, noise⟫_ℝ - averageDistance / 2) =
          Real.exp
            (-kernel.relativeEntropy mixtureWeight secret +
              ∑ neighbor, (kernel.distribution secret).mass neighbor *
                gaussianLikelihoodScore certificate.difference
                  (kernel.neighbor secret neighbor) secret noise) := by
            rw [kernel.average_gaussianLikelihoodScore]
            dsimp [divergence, averageDistance, barycentre]
            ring_nf
      _ ≤ ∑ candidate, mixtureWeight.mass candidate *
          Real.exp (gaussianLikelihoodScore certificate.difference
            candidate secret noise) :=
        exp_neg_relativeEntropy_add_expectation_le_mixture
          (kernel.distribution secret) mixtureWeight (kernel.neighbor secret)
          (kernel.neighbor_injective secret)
          (fun candidate ↦ gaussianLikelihoodScore certificate.difference
            candidate secret noise)
  have hpoint : ∀ noise,
      (∑ candidate, mixtureWeight.mass candidate *
          Real.exp (gaussianLikelihoodScore certificate.difference
            candidate secret noise)) ^ (1 - alpha) ≤
        Real.exp (r * divergence + r / 2 * averageDistance) *
          Real.exp (-r * ⟪barycentre, noise⟫_ℝ) := by
    intro noise
    have hnegative : 1 - alpha ≤ 0 := by linarith
    calc
      (∑ candidate, mixtureWeight.mass candidate *
          Real.exp (gaussianLikelihoodScore certificate.difference
            candidate secret noise)) ^ (1 - alpha) ≤
          Real.exp (-divergence + ⟪barycentre, noise⟫_ℝ - averageDistance / 2) ^
            (1 - alpha) :=
        Real.rpow_le_rpow_of_nonpos (Real.exp_pos _) (hlower noise) hnegative
      _ = Real.exp
          ((-divergence + ⟪barycentre, noise⟫_ℝ - averageDistance / 2) *
            (1 - alpha)) := by rw [Real.exp_mul]
      _ = Real.exp (r * divergence + r / 2 * averageDistance) *
          Real.exp (-r * ⟪barycentre, noise⟫_ℝ) := by
        rw [← Real.exp_add]
        dsimp [r]
        ring_nf
  rw [certificate.overlap_eq]
  calc
    certificate.gaussian.expectation.expect (fun noise ↦
        (∑ candidate, mixtureWeight.mass candidate *
          Real.exp (gaussianLikelihoodScore certificate.difference
            candidate secret noise)) ^ (1 - alpha)) ≤
        certificate.gaussian.expectation.expect (fun noise ↦
          Real.exp (r * divergence + r / 2 * averageDistance) *
            Real.exp (-r * ⟪barycentre, noise⟫_ℝ)) :=
      certificate.gaussian.expectation.monotone hpoint
    _ = Real.exp (r * divergence + r / 2 * averageDistance) *
        certificate.gaussian.expectation.expect
          (fun noise ↦ Real.exp (-r * ⟪barycentre, noise⟫_ℝ)) :=
      certificate.gaussian.expectation.const_mul _ _
    _ = Real.exp (r * divergence + r / 2 * averageDistance) *
        Real.exp ((-r) ^ 2 * ‖barycentre‖ ^ 2 / 2) := by
      rw [certificate.gaussian.mgf_eq]
    _ = Real.exp
        ((alpha - 1) * kernel.relativeEntropy mixtureWeight secret +
          (alpha - 1) / 2 *
            kernel.averageSquaredDistance certificate.difference secret +
          (alpha - 1) ^ 2 / 2 *
            ‖kernel.barycenter certificate.difference secret‖ ^ 2) := by
      rw [← Real.exp_add]
      dsimp [r, divergence, averageDistance, barycentre]
      ring_nf

/-- **Conditional local-cluster guessing theorem (equations (10) and (25)).** -/
theorem conditionalGaussianMixtureClusterGuessingBound
    {Secret Neighbor Output Vector : Type}
    [Fintype Secret] [Nonempty Secret] [DecidableEq Secret]
    [Fintype Neighbor] [Fintype Output] [DecidableEq Output]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (component : Secret → PositiveProbabilityTable Output)
    (mixtureWeight : PositiveProbabilityTable Secret)
    (alpha : ℝ) (halpha : 1 < alpha)
    (certificate : EqualCovarianceGaussianMixtureCertificate
      Secret Output Vector component mixtureWeight alpha)
    (kernel : LocalKernel Secret Neighbor)
    (channel_mass : ∀ secret output,
      realPointMass (channel secret) output = (component secret).mass output) :
    (conditionalGuessingProbability
      (conditionalChannelJoint prior channel)).toReal ≤
      (∑ secret, realPointMass prior secret ^ alpha *
        Real.exp
          ((alpha - 1) * kernel.relativeEntropy mixtureWeight secret +
            (alpha - 1) / 2 *
              kernel.averageSquaredDistance certificate.difference secret +
            (alpha - 1) ^ 2 / 2 *
              ‖kernel.barycenter certificate.difference secret‖ ^ 2)) ^
        (1 / alpha) := by
  let reference := positiveProbabilityMixture mixtureWeight component
  have hfunctional :
      referenceRenyiFunctional prior channel reference alpha =
        ∑ secret, realPointMass prior secret ^ alpha *
          finiteRenyiMoment alpha (component secret).mass reference.mass := by
    unfold referenceRenyiFunctional
    apply Finset.sum_congr rfl
    intro secret _
    congr 1
    apply Finset.sum_congr rfl
    intro output _
    change realPointMass (channel secret) output ^ alpha *
      reference.mass output ^ (1 - alpha) =
        (component secret).mass output ^ alpha *
          reference.mass output ^ (1 - alpha)
    rw [channel_mass]
  have hsourceNonneg :
      0 ≤ ∑ secret, realPointMass prior secret ^ alpha *
        finiteRenyiMoment alpha (component secret).mass reference.mass := by
    apply Finset.sum_nonneg
    intro secret _
    apply mul_nonneg (Real.rpow_nonneg (realPointMass_nonneg prior secret) alpha)
    unfold finiteRenyiMoment
    exact Finset.sum_nonneg fun output _ ↦ mul_nonneg
      (Real.rpow_nonneg ((component secret).nonneg output) alpha)
      (Real.rpow_nonneg (reference.nonneg output) (1 - alpha))
  calc
    (conditionalGuessingProbability
      (conditionalChannelJoint prior channel)).toReal ≤
        (referenceRenyiFunctional prior channel reference alpha) ^ (1 / alpha) :=
      arbitraryReferenceRenyiGuessingBound prior channel reference alpha halpha
    _ = (∑ secret, realPointMass prior secret ^ alpha *
          finiteRenyiMoment alpha (component secret).mass reference.mass) ^
            (1 / alpha) := by rw [hfunctional]
    _ ≤ (∑ secret, realPointMass prior secret ^ alpha *
        Real.exp
          ((alpha - 1) * kernel.relativeEntropy mixtureWeight secret +
            (alpha - 1) / 2 *
              kernel.averageSquaredDistance certificate.difference secret +
            (alpha - 1) ^ 2 / 2 *
              ‖kernel.barycenter certificate.difference secret‖ ^ 2)) ^
          (1 / alpha) := by
      apply Real.rpow_le_rpow hsourceNonneg
      · apply Finset.sum_le_sum
        intro secret _
        exact mul_le_mul_of_nonneg_left
          (certificate.moment_le_localCluster kernel halpha secret)
          (Real.rpow_nonneg (realPointMass_nonneg prior secret) alpha)
      · positivity

/-! ## Uniform supports and local-neighborhood mass -/

/-- For a uniform global mixture, local relative entropy is `log |S| - H(lambda_s)`. -/
theorem LocalKernel.relativeEntropy_eq_log_card_sub_entropy
    {Secret Neighbor : Type}
    [Fintype Secret] [Nonempty Secret] [Fintype Neighbor]
    (kernel : LocalKernel Secret Neighbor)
    (reference : PositiveProbabilityTable Secret)
    (uniform : ∀ secret,
      reference.mass secret = 1 / (Fintype.card Secret : ℝ))
    (secret : Secret) :
    kernel.relativeEntropy reference secret =
      Real.log (Fintype.card Secret : ℝ) - kernel.entropy secret := by
  let cardinality : ℝ := Fintype.card Secret
  have hcardinality : 0 < cardinality := by
    dsimp [cardinality]
    exact_mod_cast Fintype.card_pos
  have hlog : ∀ neighbor,
      Real.log ((kernel.distribution secret).mass neighbor /
          reference.mass (kernel.neighbor secret neighbor)) =
        Real.log ((kernel.distribution secret).mass neighbor) +
          Real.log cardinality := by
    intro neighbor
    rw [uniform]
    rw [Real.log_div
        (ne_of_gt ((kernel.distribution secret).positive neighbor))
        (ne_of_gt (div_pos zero_lt_one hcardinality)),
      Real.log_div one_ne_zero (ne_of_gt hcardinality), Real.log_one]
    ring
  unfold LocalKernel.relativeEntropy LocalKernel.entropy
  simp_rw [hlog, mul_add, Finset.sum_add_distrib]
  rw [← Finset.sum_mul, (kernel.distribution secret).sum_mass, one_mul]
  dsimp [cardinality]
  ring

/-- A posterior neighborhood obtained by conditioning the mixture weights on mass `b` has
relative entropy exactly `-log b`, the identity used in equation (23). -/
theorem LocalKernel.relativeEntropy_eq_neg_log_normalizer
    {Secret Neighbor : Type}
    [Fintype Secret] [Fintype Neighbor]
    (kernel : LocalKernel Secret Neighbor)
    (reference : PositiveProbabilityTable Secret)
    (normalizer : ℝ) (hnormalizer : 0 < normalizer)
    (conditioned : ∀ secret neighbor,
      (kernel.distribution secret).mass neighbor =
        reference.mass (kernel.neighbor secret neighbor) / normalizer)
    (secret : Secret) :
    kernel.relativeEntropy reference secret = -Real.log normalizer := by
  have hratio : ∀ neighbor,
      (kernel.distribution secret).mass neighbor /
          reference.mass (kernel.neighbor secret neighbor) =
        1 / normalizer := by
    intro neighbor
    rw [conditioned]
    field_simp [ne_of_gt (reference.positive (kernel.neighbor secret neighbor)),
      ne_of_gt hnormalizer]
  unfold LocalKernel.relativeEntropy
  simp_rw [hratio]
  rw [← Finset.sum_mul, (kernel.distribution secret).sum_mass, one_mul]
  rw [Real.log_div one_ne_zero (ne_of_gt hnormalizer), Real.log_one]
  ring

/-- Algebraic cancellation of the total support size in equation (11). -/
theorem uniformRenyiWeight_cancel
    (cardinality alpha localPenalty : ℝ) (hcardinality : 0 < cardinality) :
    (1 / cardinality) ^ alpha *
        Real.exp ((alpha - 1) * Real.log cardinality + localPenalty) =
      (1 / cardinality) * Real.exp localPenalty := by
  have hinverse : 0 < (1 / cardinality : ℝ) := div_pos zero_lt_one hcardinality
  have hlogInverse : Real.log (1 / cardinality) = -Real.log cardinality := by
    rw [Real.log_div one_ne_zero (ne_of_gt hcardinality), Real.log_one]
    ring
  calc
    (1 / cardinality) ^ alpha *
        Real.exp ((alpha - 1) * Real.log cardinality + localPenalty) =
        Real.exp
          (Real.log (1 / cardinality) * alpha +
            ((alpha - 1) * Real.log cardinality + localPenalty)) := by
      rw [Real.rpow_def_of_pos hinverse, ← Real.exp_add]
    _ = Real.exp (Real.log (1 / cardinality) + localPenalty) := by
      rw [hlogInverse]
      congr 1
      ring
    _ = (1 / cardinality) * Real.exp localPenalty := by
      rw [Real.exp_add, Real.exp_log hinverse]

/-- **Uniform-support local-cloud theorem (equation (11)).** -/
theorem uniformGaussianMixtureClusterGuessingBound
    {Secret Neighbor Output Vector : Type}
    [Fintype Secret] [Nonempty Secret] [DecidableEq Secret]
    [Fintype Neighbor] [Fintype Output] [DecidableEq Output]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (component : Secret → PositiveProbabilityTable Output)
    (mixtureWeight : PositiveProbabilityTable Secret)
    (alpha : ℝ) (halpha : 1 < alpha)
    (certificate : EqualCovarianceGaussianMixtureCertificate
      Secret Output Vector component mixtureWeight alpha)
    (kernel : LocalKernel Secret Neighbor)
    (channel_mass : ∀ secret output,
      realPointMass (channel secret) output = (component secret).mass output)
    (prior_uniform : ∀ secret,
      realPointMass prior secret = 1 / (Fintype.card Secret : ℝ))
    (mixture_uniform : ∀ secret,
      mixtureWeight.mass secret = 1 / (Fintype.card Secret : ℝ)) :
    (conditionalGuessingProbability
      (conditionalChannelJoint prior channel)).toReal ≤
      ((1 / (Fintype.card Secret : ℝ)) *
        ∑ secret, Real.exp
          (-(alpha - 1) * kernel.entropy secret +
            (alpha - 1) / 2 *
              kernel.averageSquaredDistance certificate.difference secret +
            (alpha - 1) ^ 2 / 2 *
              ‖kernel.barycenter certificate.difference secret‖ ^ 2)) ^
        (1 / alpha) := by
  have hgeneral := conditionalGaussianMixtureClusterGuessingBound
    prior channel component mixtureWeight alpha halpha certificate kernel channel_mass
  refine hgeneral.trans_eq ?_
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro secret _
  rw [prior_uniform,
    kernel.relativeEntropy_eq_log_card_sub_entropy mixtureWeight mixture_uniform]
  let localPenalty : ℝ :=
    -(alpha - 1) * kernel.entropy secret +
      (alpha - 1) / 2 *
        kernel.averageSquaredDistance certificate.difference secret +
      (alpha - 1) ^ 2 / 2 *
        ‖kernel.barycenter certificate.difference secret‖ ^ 2
  have hcardinality : 0 < (Fintype.card Secret : ℝ) := by
    exact_mod_cast Fintype.card_pos
  convert uniformRenyiWeight_cancel
    (Fintype.card Secret : ℝ) alpha localPenalty hcardinality using 1
  all_goals dsimp [localPenalty]
  all_goals ring_nf

/-- **Uniform exponential lossiness criterion (equations (12)--(13) and (26)).** -/
theorem uniformGaussianMixtureClusterExponentialBound
    {Secret Neighbor Output Vector : Type}
    [Fintype Secret] [Nonempty Secret] [DecidableEq Secret]
    [Fintype Neighbor] [Fintype Output] [DecidableEq Output]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (component : Secret → PositiveProbabilityTable Output)
    (mixtureWeight : PositiveProbabilityTable Secret)
    (alpha : ℝ) (halpha : 1 < alpha)
    (certificate : EqualCovarianceGaussianMixtureCertificate
      Secret Output Vector component mixtureWeight alpha)
    (kernel : LocalKernel Secret Neighbor)
    (channel_mass : ∀ secret output,
      realPointMass (channel secret) output = (component secret).mass output)
    (prior_uniform : ∀ secret,
      realPointMass prior secret = 1 / (Fintype.card Secret : ℝ))
    (mixture_uniform : ∀ secret,
      mixtureWeight.mass secret = 1 / (Fintype.card Secret : ℝ))
    (dimension : ℕ) (kappa averageBound barycenterBound : ℝ)
    (entropy_lower : ∀ secret,
      kappa * dimension ≤ kernel.entropy secret)
    (distance_upper : ∀ secret,
      kernel.averageSquaredDistance certificate.difference secret ≤
        averageBound * dimension)
    (barycenter_upper : ∀ secret,
      ‖kernel.barycenter certificate.difference secret‖ ^ 2 ≤
        barycenterBound * dimension) :
    (conditionalGuessingProbability
      (conditionalChannelJoint prior channel)).toReal ≤
      Real.exp
        (-(alpha - 1) / alpha *
          (kappa - averageBound / 2 -
            (alpha - 1) / 2 * barycenterBound) * dimension) := by
  let r : ℝ := alpha - 1
  let localPenalty : Secret → ℝ := fun secret ↦
    -r * kernel.entropy secret +
      r / 2 * kernel.averageSquaredDistance certificate.difference secret +
      r ^ 2 / 2 * ‖kernel.barycenter certificate.difference secret‖ ^ 2
  let exponent : ℝ :=
    -r * (kappa - averageBound / 2 - r / 2 * barycenterBound) * dimension
  have hr : 0 < r := sub_pos.mpr halpha
  have hpenalty : ∀ secret, localPenalty secret ≤ exponent := by
    intro secret
    have hentropy := mul_le_mul_of_nonpos_left (entropy_lower secret) (by linarith : -r ≤ 0)
    have hdistance := mul_le_mul_of_nonneg_left (distance_upper secret)
      (by positivity : 0 ≤ r / 2)
    have hbarycenter := mul_le_mul_of_nonneg_left (barycenter_upper secret)
      (by positivity : 0 ≤ r ^ 2 / 2)
    calc
      localPenalty secret ≤
          -r * (kappa * dimension) +
            (r / 2) * (averageBound * dimension) +
            (r ^ 2 / 2) * (barycenterBound * dimension) := by
        dsimp [localPenalty]
        exact add_le_add (add_le_add hentropy hdistance) hbarycenter
      _ = exponent := by
        dsimp [exponent]
        ring
  have haverage :
      (1 / (Fintype.card Secret : ℝ)) *
          ∑ secret, Real.exp (localPenalty secret) ≤ Real.exp exponent := by
    have hsum : (∑ secret, Real.exp (localPenalty secret)) ≤
        ∑ _secret : Secret, Real.exp exponent :=
      Finset.sum_le_sum fun secret _ ↦ Real.exp_le_exp.mpr (hpenalty secret)
    have hcardinality : 0 < (Fintype.card Secret : ℝ) := by
      exact_mod_cast Fintype.card_pos
    calc
      (1 / (Fintype.card Secret : ℝ)) *
          ∑ secret, Real.exp (localPenalty secret) ≤
          (1 / (Fintype.card Secret : ℝ)) *
            ∑ _secret : Secret, Real.exp exponent :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = Real.exp exponent := by
        simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
        field_simp [ne_of_gt hcardinality]
  have hpoint := uniformGaussianMixtureClusterGuessingBound
    prior channel component mixtureWeight alpha halpha certificate kernel
      channel_mass prior_uniform mixture_uniform
  calc
    (conditionalGuessingProbability
      (conditionalChannelJoint prior channel)).toReal ≤
        ((1 / (Fintype.card Secret : ℝ)) *
          ∑ secret, Real.exp (localPenalty secret)) ^ (1 / alpha) := by
      simpa only [r, localPenalty] using hpoint
    _ ≤ Real.exp exponent ^ (1 / alpha) := by
      apply Real.rpow_le_rpow
      · exact mul_nonneg (by positivity)
          (Finset.sum_nonneg fun secret _ ↦ (Real.exp_nonneg _))
      · exact haverage
      · positivity
    _ = Real.exp
        (-(alpha - 1) / alpha *
          (kappa - averageBound / 2 -
            (alpha - 1) / 2 * barycenterBound) * dimension) := by
      rw [← Real.exp_mul]
      dsimp [exponent, r]
      field_simp [ne_of_gt (lt_trans zero_lt_one halpha)]

/-! ## Descriptor/leakage averaging -/

/-- Pointwise local-cloud bounds average with the actual descriptor/leakage law, rather than a
worst-case or constant-probability typical descriptor (equation (20)). -/
theorem descriptorAveragedGaussianMixtureClusterGuessingBound
    {Descriptor Secret Neighbor Output Vector : Type}
    [Fintype Descriptor] [DecidableEq Descriptor]
    [Fintype Secret] [Nonempty Secret] [DecidableEq Secret]
    [Fintype Neighbor] [Fintype Output] [DecidableEq Output]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (descriptorSampler : ProbComp Descriptor)
    (prior : Descriptor → ProbComp Secret)
    (channel : Descriptor → Secret → ProbComp Output)
    (component : Descriptor → Secret → PositiveProbabilityTable Output)
    (mixtureWeight : Descriptor → PositiveProbabilityTable Secret)
    (alpha : ℝ) (halpha : 1 < alpha)
    (certificate : ∀ descriptor,
      EqualCovarianceGaussianMixtureCertificate Secret Output Vector
        (component descriptor) (mixtureWeight descriptor) alpha)
    (kernel : Descriptor → LocalKernel Secret Neighbor)
    (channel_mass : ∀ descriptor secret output,
      realPointMass (channel descriptor secret) output =
        (component descriptor secret).mass output) :
    (conditionalGuessingProbability
      (contextualChannelJoint descriptorSampler prior channel)).toReal ≤
      ∑ descriptor, realPointMass descriptorSampler descriptor *
        (∑ secret, realPointMass (prior descriptor) secret ^ alpha *
          Real.exp
            ((alpha - 1) *
                (kernel descriptor).relativeEntropy
                  (mixtureWeight descriptor) secret +
              (alpha - 1) / 2 *
                (kernel descriptor).averageSquaredDistance
                  (certificate descriptor).difference secret +
              (alpha - 1) ^ 2 / 2 *
                ‖(kernel descriptor).barycenter
                  (certificate descriptor).difference secret‖ ^ 2)) ^
          (1 / alpha) := by
  apply descriptorAveragedGuessingBound descriptorSampler prior channel
  intro descriptor
  exact conditionalGaussianMixtureClusterGuessingBound
    (prior descriptor) (channel descriptor) (component descriptor)
    (mixtureWeight descriptor) alpha halpha (certificate descriptor)
    (kernel descriptor) (channel_mass descriptor)

/-! ## Finite normalized-weight benchmark -/

/-- Normalize any strictly positive finite weight.  This is the finite model of a discrete
Gaussian lattice law. -/
def normalizedPositiveWeight
    {Secret : Type} [Fintype Secret] [Nonempty Secret]
    (weight : Secret → ℝ) (weight_pos : ∀ secret, 0 < weight secret) :
    PositiveProbabilityTable Secret where
  mass secret := weight secret / ∑ candidate, weight candidate
  positive secret := div_pos (weight_pos secret)
    (Finset.sum_pos (fun candidate _ ↦ weight_pos candidate) Finset.univ_nonempty)
  sum_mass := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt <|
      Finset.sum_pos (fun candidate _ ↦ weight_pos candidate) Finset.univ_nonempty)

@[simp]
theorem normalizedPositiveWeight_mass
    {Secret : Type} [Fintype Secret] [Nonempty Secret]
    (weight : Secret → ℝ) (weight_pos : ∀ secret, 0 < weight secret)
    (secret : Secret) :
    (normalizedPositiveWeight weight weight_pos).mass secret =
      weight secret / ∑ candidate, weight candidate := rfl

/-- Exact normalized-weight power-sum identity.  For discrete-Gaussian weights, the numerator is
the finite theta mass at width `sigma / sqrt alpha`, giving equation (24). -/
theorem normalizedPositiveWeight_alphaMoment
    {Secret : Type} [Fintype Secret] [Nonempty Secret]
    (weight : Secret → ℝ) (weight_pos : ∀ secret, 0 < weight secret)
    (alpha : ℝ) :
    (∑ secret, (normalizedPositiveWeight weight weight_pos).mass secret ^ alpha) =
      (∑ secret, weight secret ^ alpha) /
        (∑ secret, weight secret) ^ alpha := by
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro secret _
  exact Real.div_rpow (weight_pos secret).le
    (Finset.sum_nonneg fun candidate _ ↦ (weight_pos candidate).le) alpha

/-! ## Quadratic-codeword link -/

/-- The local theorem uses only pairwise differences.  For the quadratic product-cancellation
codebook this difference is the already exact factorization from equation (16). -/
theorem quadraticMixtureCodeword_sub_factor
    {R : Type} [CommRing R] (z fg left right : R) :
    quadraticCodewordRow z fg right - quadraticCodewordRow z fg left =
      (right - left) * (z + fg * (right + left)) :=
  quadraticCodewordRow_sub_factor z fg left right

end

end FormalProof4FHE.RLWE.RankOneHNFLossinessMixtureRenyi
