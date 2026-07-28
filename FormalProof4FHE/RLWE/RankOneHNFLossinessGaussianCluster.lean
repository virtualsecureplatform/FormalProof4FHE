/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.RankOneHNFLossinessMixtureRenyi

/-!
# Gibbs-Optimized Gaussian Cluster Certificates

This module formalizes the finite optimization and certificate layer of
`sketch/gaussiancluster.md`.  It strengthens the mixture-reference Renyi theorem by choosing the
local cloud through an explicit Gibbs law and by exposing the exact barycenter-aware primal--dual
gap.

The following parts are native Lean algebra over finite probability tables:

* the barycenter-free Gibbs optimizer and soft-overlap mass;
* the barycenter-aware tilted Gibbs law and exact primal--dual gap;
* certified strong duality from a self-consistent Gibbs fixed point;
* full and restricted soft-overlap Gaussian-mixture bounds;
* effective-codebook and bad-set exponential bounds; and
* the general finite non-Gaussian likelihood-ratio cluster inequality.

The equal-covariance continuous Gaussian likelihood-ratio integral remains exactly the explicit
`EqualCovarianceGaussianMixtureCertificate` boundary inherited from
`RankOneHNFLossinessMixtureRenyi`.  A numerical optimizer may supply a fixed point or an
approximate primal--dual pair; neither is introduced as an axiom.
-/

open OracleComp
open scoped ENNReal BigOperators InnerProductSpace

namespace FormalProof4FHE.RLWE.RankOneHNFLossinessGaussianCluster

open RankOneHNFLossinessRLWENTRU
open RankOneHNFLossinessRefined
open RankOneHNFLossinessSupportAware
open RankOneHNFLossinessRenyi
open RankOneHNFLossinessMixtureRenyi

noncomputable section

/-! ## Finite weighted geometry -/

/-- Relative entropy between two strictly positive finite probability tables. -/
def finiteRelativeEntropy
    {Index : Type} [Fintype Index]
    (left right : PositiveProbabilityTable Index) : ℝ :=
  ∑ index, left.mass index * Real.log (left.mass index / right.mass index)

theorem positiveProbabilityTable_ext
    {Index : Type} [Fintype Index]
    (left right : PositiveProbabilityTable Index)
    (hmass : ∀ index, left.mass index = right.mass index) :
    left = right := by
  cases left with
  | mk leftMass leftPositive leftSum =>
    cases right with
    | mk rightMass rightPositive rightSum =>
      dsimp at hmass
      have heq : leftMass = rightMass := funext hmass
      subst rightMass
      rfl

/-- Average squared displacement under a finite probability table. -/
def averageSquaredDisplacement
    {Index Vector : Type} [Fintype Index] [SeminormedAddCommGroup Vector]
    (weight : PositiveProbabilityTable Index) (displacement : Index → Vector) : ℝ :=
  ∑ index, weight.mass index * ‖displacement index‖ ^ 2

/-- Weighted displacement barycenter. -/
def displacementBarycenter
    {Index Vector : Type} [Fintype Index]
    [SeminormedAddCommGroup Vector] [NormedSpace ℝ Vector]
    (weight : PositiveProbabilityTable Index) (displacement : Index → Vector) : Vector :=
  ∑ index, weight.mass index • displacement index

theorem averageSquaredDisplacement_nonneg
    {Index Vector : Type} [Fintype Index] [SeminormedAddCommGroup Vector]
    (weight : PositiveProbabilityTable Index) (displacement : Index → Vector) :
    0 ≤ averageSquaredDisplacement weight displacement :=
  Finset.sum_nonneg fun index _ ↦
    mul_nonneg (weight.nonneg index) (sq_nonneg _)

theorem finiteRelativeEntropy_self
    {Index : Type} [Fintype Index]
    (weight : PositiveProbabilityTable Index) :
    finiteRelativeEntropy weight weight = 0 := by
  unfold finiteRelativeEntropy
  apply Finset.sum_eq_zero
  intro index _
  rw [div_self (ne_of_gt (weight.positive index)), Real.log_one, mul_zero]

/-- Gibbs' inequality for the finite, strictly positive tables used by the optimizer. -/
theorem finiteRelativeEntropy_nonneg
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (left right : PositiveProbabilityTable Index) :
    0 ≤ finiteRelativeEntropy left right := by
  have h := exp_neg_relativeEntropy_add_expectation_le_mixture
    left right (fun index ↦ index) Function.injective_id (fun _ ↦ (0 : ℝ))
  have hexp : Real.exp (-finiteRelativeEntropy left right) ≤ Real.exp 0 := by
    simpa only [finiteRelativeEntropy, mul_zero, Finset.sum_const_zero, add_zero,
      Real.exp_zero, Real.exp_zero, mul_one, right.sum_mass] using h
  have := Real.exp_le_exp.mp hexp
  linarith

theorem sum_mass_mul_inner_eq_inner_barycenter
    {Index Vector : Type} [Fintype Index]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (weight : PositiveProbabilityTable Index) (displacement : Index → Vector)
    (vector : Vector) :
    (∑ index, weight.mass index * ⟪vector, displacement index⟫_ℝ) =
      ⟪vector, displacementBarycenter weight displacement⟫_ℝ := by
  unfold displacementBarycenter
  rw [inner_sum]
  apply Finset.sum_congr rfl
  intro index _
  rw [real_inner_smul_right]

/-- The complete barycenter-aware cluster objective from equation (3). -/
def clusterObjective
    {Index Vector : Type} [Fintype Index]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (r : ℝ) (weight reference : PositiveProbabilityTable Index)
    (displacement : Index → Vector) : ℝ :=
  finiteRelativeEntropy weight reference +
    averageSquaredDisplacement weight displacement / 2 +
    r / 2 * ‖displacementBarycenter weight displacement‖ ^ 2

/-! ## The barycenter-free Gibbs optimizer -/

/-- The Gaussian-kernel overlap mass `Z = sum_t beta(t) exp (-||d_t||^2/2)`. -/
def softOverlapMass
    {Index Vector : Type} [Fintype Index] [SeminormedAddCommGroup Vector]
    (reference : PositiveProbabilityTable Index) (displacement : Index → Vector) : ℝ :=
  ∑ index, reference.mass index * Real.exp (-‖displacement index‖ ^ 2 / 2)

theorem softOverlapMass_pos
    {Index Vector : Type} [Fintype Index] [Nonempty Index]
    [SeminormedAddCommGroup Vector]
    (reference : PositiveProbabilityTable Index) (displacement : Index → Vector) :
    0 < softOverlapMass reference displacement := by
  unfold softOverlapMass
  exact Finset.sum_pos
    (fun index _ ↦ mul_pos (reference.positive index) (Real.exp_pos _))
    Finset.univ_nonempty

/-- Equation (6): the normalized barycenter-free soft-overlap distribution. -/
def softOverlapDistribution
    {Index Vector : Type} [Fintype Index] [Nonempty Index]
    [SeminormedAddCommGroup Vector]
    (reference : PositiveProbabilityTable Index) (displacement : Index → Vector) :
    PositiveProbabilityTable Index where
  mass index :=
    reference.mass index * Real.exp (-‖displacement index‖ ^ 2 / 2) /
      softOverlapMass reference displacement
  positive index := div_pos
    (mul_pos (reference.positive index) (Real.exp_pos _))
    (softOverlapMass_pos reference displacement)
  sum_mass := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (softOverlapMass_pos reference displacement))

@[simp]
theorem softOverlapDistribution_mass
    {Index Vector : Type} [Fintype Index] [Nonempty Index]
    [SeminormedAddCommGroup Vector]
    (reference : PositiveProbabilityTable Index) (displacement : Index → Vector)
    (index : Index) :
    (softOverlapDistribution reference displacement).mass index =
      reference.mass index * Real.exp (-‖displacement index‖ ^ 2 / 2) /
        softOverlapMass reference displacement := rfl

/-- The logarithmic Gibbs-density identity behind equations (6)--(7). -/
theorem softOverlapDistribution_log_ratio
    {Index Vector : Type} [Fintype Index] [Nonempty Index]
    [SeminormedAddCommGroup Vector]
    (reference : PositiveProbabilityTable Index) (displacement : Index → Vector)
    (index : Index) :
    Real.log ((softOverlapDistribution reference displacement).mass index /
        reference.mass index) =
      -‖displacement index‖ ^ 2 / 2 -
        Real.log (softOverlapMass reference displacement) := by
  have hratio :
      (softOverlapDistribution reference displacement).mass index /
          reference.mass index =
        Real.exp (-‖displacement index‖ ^ 2 / 2) /
          softOverlapMass reference displacement := by
    rw [softOverlapDistribution_mass]
    field_simp [ne_of_gt (reference.positive index),
      ne_of_gt (softOverlapMass_pos reference displacement)]
  rw [hratio, Real.log_div (ne_of_gt (Real.exp_pos _))
    (ne_of_gt (softOverlapMass_pos reference displacement)), Real.log_exp]

/-- Rewrite an arbitrary density relative to the soft Gibbs density. -/
theorem log_ratio_softOverlapDistribution
    {Index Vector : Type} [Fintype Index] [Nonempty Index]
    [SeminormedAddCommGroup Vector]
    (weight reference : PositiveProbabilityTable Index)
    (displacement : Index → Vector) (index : Index) :
    Real.log (weight.mass index /
        (softOverlapDistribution reference displacement).mass index) =
      Real.log (weight.mass index / reference.mass index) +
        ‖displacement index‖ ^ 2 / 2 +
        Real.log (softOverlapMass reference displacement) := by
  rw [Real.log_div (ne_of_gt (weight.positive index))
      (ne_of_gt ((softOverlapDistribution reference displacement).positive index)),
    Real.log_div (ne_of_gt (weight.positive index))
      (ne_of_gt (reference.positive index))]
  have hsoft := softOverlapDistribution_log_ratio reference displacement index
  rw [Real.log_div
      (ne_of_gt ((softOverlapDistribution reference displacement).positive index))
      (ne_of_gt (reference.positive index))] at hsoft
  linarith

/-- Exact Gibbs decomposition.  Nonnegativity of its first term proves equation (7). -/
theorem finiteRelativeEntropy_add_average_eq_soft
    {Index Vector : Type} [Fintype Index] [Nonempty Index]
    [SeminormedAddCommGroup Vector]
    (weight reference : PositiveProbabilityTable Index)
    (displacement : Index → Vector) :
    finiteRelativeEntropy weight reference +
        averageSquaredDisplacement weight displacement / 2 =
      finiteRelativeEntropy weight (softOverlapDistribution reference displacement) -
        Real.log (softOverlapMass reference displacement) := by
  unfold finiteRelativeEntropy averageSquaredDisplacement
  simp_rw [log_ratio_softOverlapDistribution weight reference displacement]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hdistance :
      (∑ index, weight.mass index * (‖displacement index‖ ^ 2 / 2)) =
        (∑ index, weight.mass index * ‖displacement index‖ ^ 2) / 2 := by
    calc
      (∑ index, weight.mass index * (‖displacement index‖ ^ 2 / 2)) =
          ∑ index, (weight.mass index * ‖displacement index‖ ^ 2) / 2 := by
        apply Finset.sum_congr rfl
        intro index _
        ring
      _ = (∑ index, weight.mass index * ‖displacement index‖ ^ 2) / 2 := by
        rw [Finset.sum_div]
  rw [hdistance]
  rw [← Finset.sum_mul]
  rw [weight.sum_mass, one_mul]
  ring

theorem softOverlapDistribution_objective_without_barycenter
    {Index Vector : Type} [Fintype Index] [Nonempty Index] [DecidableEq Index]
    [SeminormedAddCommGroup Vector]
    (reference : PositiveProbabilityTable Index) (displacement : Index → Vector) :
    finiteRelativeEntropy (softOverlapDistribution reference displacement) reference +
        averageSquaredDisplacement (softOverlapDistribution reference displacement)
          displacement / 2 =
      -Real.log (softOverlapMass reference displacement) := by
  rw [finiteRelativeEntropy_add_average_eq_soft]
  rw [finiteRelativeEntropy_self]
  ring

/-- Equation (7): the soft Gibbs law minimizes the barycenter-free objective. -/
theorem neg_log_softOverlapMass_le_objective_without_barycenter
    {Index Vector : Type} [Fintype Index] [Nonempty Index] [DecidableEq Index]
    [SeminormedAddCommGroup Vector]
    (weight reference : PositiveProbabilityTable Index)
    (displacement : Index → Vector) :
    -Real.log (softOverlapMass reference displacement) ≤
      finiteRelativeEntropy weight reference +
        averageSquaredDisplacement weight displacement / 2 := by
  rw [finiteRelativeEntropy_add_average_eq_soft]
  have hnonneg := finiteRelativeEntropy_nonneg weight
    (softOverlapDistribution reference displacement)
  linarith

/-- Equation (8): the barycenter of the soft Gibbs law. -/
def softBarycenter
    {Index Vector : Type} [Fintype Index] [Nonempty Index]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (reference : PositiveProbabilityTable Index) (displacement : Index → Vector) : Vector :=
  displacementBarycenter (softOverlapDistribution reference displacement) displacement

/-! ## Exact barycenter-aware primal--dual gap -/

/-- The tilted overlap partition function `Z(u)` from equation (10). -/
def tiltedOverlapMass
    {Index Vector : Type} [Fintype Index]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (r : ℝ) (reference : PositiveProbabilityTable Index)
    (displacement : Index → Vector) (dual : Vector) : ℝ :=
  ∑ index, reference.mass index *
    Real.exp (-‖displacement index‖ ^ 2 / 2 -
      r * ⟪dual, displacement index⟫_ℝ)

theorem tiltedOverlapMass_pos
    {Index Vector : Type} [Fintype Index] [Nonempty Index]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (r : ℝ) (reference : PositiveProbabilityTable Index)
    (displacement : Index → Vector) (dual : Vector) :
    0 < tiltedOverlapMass r reference displacement dual := by
  unfold tiltedOverlapMass
  exact Finset.sum_pos
    (fun index _ ↦ mul_pos (reference.positive index) (Real.exp_pos _))
    Finset.univ_nonempty

/-- Equation (13): the barycenter-tilted Gibbs distribution. -/
def tiltedOverlapDistribution
    {Index Vector : Type} [Fintype Index] [Nonempty Index]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (r : ℝ) (reference : PositiveProbabilityTable Index)
    (displacement : Index → Vector) (dual : Vector) :
    PositiveProbabilityTable Index where
  mass index := reference.mass index *
    Real.exp (-‖displacement index‖ ^ 2 / 2 -
      r * ⟪dual, displacement index⟫_ℝ) /
        tiltedOverlapMass r reference displacement dual
  positive index := div_pos
    (mul_pos (reference.positive index) (Real.exp_pos _))
    (tiltedOverlapMass_pos r reference displacement dual)
  sum_mass := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt (tiltedOverlapMass_pos r reference displacement dual))

@[simp]
theorem tiltedOverlapDistribution_mass
    {Index Vector : Type} [Fintype Index] [Nonempty Index]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (r : ℝ) (reference : PositiveProbabilityTable Index)
    (displacement : Index → Vector) (dual : Vector) (index : Index) :
    (tiltedOverlapDistribution r reference displacement dual).mass index =
      reference.mass index *
        Real.exp (-‖displacement index‖ ^ 2 / 2 -
          r * ⟪dual, displacement index⟫_ℝ) /
            tiltedOverlapMass r reference displacement dual := rfl

/-- The dual objective `phi(u)` from equation (11). -/
def clusterDualPotential
    {Index Vector : Type} [Fintype Index]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (r : ℝ) (reference : PositiveProbabilityTable Index)
    (displacement : Index → Vector) (dual : Vector) : ℝ :=
  -Real.log (tiltedOverlapMass r reference displacement dual) -
    r / 2 * ‖dual‖ ^ 2

theorem tiltedOverlapDistribution_log_ratio
    {Index Vector : Type} [Fintype Index] [Nonempty Index]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (r : ℝ) (reference : PositiveProbabilityTable Index)
    (displacement : Index → Vector) (dual : Vector) (index : Index) :
    Real.log ((tiltedOverlapDistribution r reference displacement dual).mass index /
        reference.mass index) =
      -‖displacement index‖ ^ 2 / 2 -
        r * ⟪dual, displacement index⟫_ℝ -
        Real.log (tiltedOverlapMass r reference displacement dual) := by
  have hratio :
      (tiltedOverlapDistribution r reference displacement dual).mass index /
          reference.mass index =
        Real.exp (-‖displacement index‖ ^ 2 / 2 -
            r * ⟪dual, displacement index⟫_ℝ) /
          tiltedOverlapMass r reference displacement dual := by
    rw [tiltedOverlapDistribution_mass]
    field_simp [ne_of_gt (reference.positive index),
      ne_of_gt (tiltedOverlapMass_pos r reference displacement dual)]
  rw [hratio, Real.log_div (ne_of_gt (Real.exp_pos _))
    (ne_of_gt (tiltedOverlapMass_pos r reference displacement dual)), Real.log_exp]

theorem log_ratio_tiltedOverlapDistribution
    {Index Vector : Type} [Fintype Index] [Nonempty Index]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (r : ℝ) (weight reference : PositiveProbabilityTable Index)
    (displacement : Index → Vector) (dual : Vector) (index : Index) :
    Real.log (weight.mass index /
        (tiltedOverlapDistribution r reference displacement dual).mass index) =
      Real.log (weight.mass index / reference.mass index) +
        ‖displacement index‖ ^ 2 / 2 +
        r * ⟪dual, displacement index⟫_ℝ +
        Real.log (tiltedOverlapMass r reference displacement dual) := by
  rw [Real.log_div (ne_of_gt (weight.positive index))
      (ne_of_gt ((tiltedOverlapDistribution r reference displacement dual).positive index)),
    Real.log_div (ne_of_gt (weight.positive index))
      (ne_of_gt (reference.positive index))]
  have htilted := tiltedOverlapDistribution_log_ratio
    r reference displacement dual index
  rw [Real.log_div
      (ne_of_gt ((tiltedOverlapDistribution r reference displacement dual).positive index))
      (ne_of_gt (reference.positive index))] at htilted
  linarith

theorem finiteRelativeEntropy_tiltedOverlapDistribution
    {Index Vector : Type} [Fintype Index] [Nonempty Index]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (r : ℝ) (weight reference : PositiveProbabilityTable Index)
    (displacement : Index → Vector) (dual : Vector) :
    finiteRelativeEntropy weight
        (tiltedOverlapDistribution r reference displacement dual) =
      finiteRelativeEntropy weight reference +
        averageSquaredDisplacement weight displacement / 2 +
        r * ⟪dual, displacementBarycenter weight displacement⟫_ℝ +
        Real.log (tiltedOverlapMass r reference displacement dual) := by
  unfold finiteRelativeEntropy averageSquaredDisplacement
  simp_rw [log_ratio_tiltedOverlapDistribution r weight reference displacement dual]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hdistance :
      (∑ index, weight.mass index * (‖displacement index‖ ^ 2 / 2)) =
        (∑ index, weight.mass index * ‖displacement index‖ ^ 2) / 2 := by
    calc
      (∑ index, weight.mass index * (‖displacement index‖ ^ 2 / 2)) =
          ∑ index, (weight.mass index * ‖displacement index‖ ^ 2) / 2 := by
        apply Finset.sum_congr rfl
        intro index _
        ring
      _ = (∑ index, weight.mass index * ‖displacement index‖ ^ 2) / 2 := by
        rw [Finset.sum_div]
  have hinner := sum_mass_mul_inner_eq_inner_barycenter
    weight displacement dual
  have hscaledInner :
      (∑ index, weight.mass index *
        (r * ⟪dual, displacement index⟫_ℝ)) =
        r * ⟪dual, displacementBarycenter weight displacement⟫_ℝ := by
    calc
      (∑ index, weight.mass index *
          (r * ⟪dual, displacement index⟫_ℝ)) =
          ∑ index, r *
            (weight.mass index * ⟪dual, displacement index⟫_ℝ) := by
        apply Finset.sum_congr rfl
        intro index _
        ring
      _ = r * ∑ index,
          weight.mass index * ⟪dual, displacement index⟫_ℝ := by
        rw [Finset.mul_sum]
      _ = r * ⟪dual, displacementBarycenter weight displacement⟫_ℝ := by
        rw [hinner]
  rw [hdistance, hscaledInner]
  rw [← Finset.sum_mul, weight.sum_mass, one_mul]

/-- Equation (14): exact primal--dual gap identity. -/
theorem clusterObjective_sub_dual_eq_gap
    {Index Vector : Type} [Fintype Index] [Nonempty Index]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (r : ℝ) (weight reference : PositiveProbabilityTable Index)
    (displacement : Index → Vector) (dual : Vector) :
    clusterObjective r weight reference displacement -
        clusterDualPotential r reference displacement dual =
      finiteRelativeEntropy weight
          (tiltedOverlapDistribution r reference displacement dual) +
        r / 2 * ‖displacementBarycenter weight displacement - dual‖ ^ 2 := by
  rw [finiteRelativeEntropy_tiltedOverlapDistribution]
  rw [norm_sub_sq_real]
  rw [real_inner_comm dual (displacementBarycenter weight displacement)]
  unfold clusterObjective clusterDualPotential
  ring

/-- Weak duality follows immediately from the exact gap. -/
theorem clusterDualPotential_le_objective
    {Index Vector : Type} [Fintype Index] [Nonempty Index] [DecidableEq Index]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (r : ℝ) (hr : 0 ≤ r) (weight reference : PositiveProbabilityTable Index)
    (displacement : Index → Vector) (dual : Vector) :
    clusterDualPotential r reference displacement dual ≤
      clusterObjective r weight reference displacement := by
  have hkl := finiteRelativeEntropy_nonneg weight
    (tiltedOverlapDistribution r reference displacement dual)
  have hsquare : 0 ≤ r / 2 *
      ‖displacementBarycenter weight displacement - dual‖ ^ 2 :=
    mul_nonneg (div_nonneg hr (by norm_num)) (sq_nonneg _)
  rw [← sub_nonneg]
  rw [clusterObjective_sub_dual_eq_gap]
  exact add_nonneg hkl hsquare

/-- A proof-carrying self-consistent solution of the finite Gibbs fixed-point equation (15)--(16).
It is directly checkable for a numerical optimizer and is sufficient for exact strong duality. -/
structure ClusterOptimalityCertificate
    (Index Vector : Type) [Fintype Index] [Nonempty Index]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (r : ℝ) (reference : PositiveProbabilityTable Index)
    (displacement : Index → Vector) where
  dual : Vector
  fixedPoint :
    displacementBarycenter
      (tiltedOverlapDistribution r reference displacement dual) displacement = dual

/-- A self-consistent tilted Gibbs law has zero primal--dual gap. -/
theorem ClusterOptimalityCertificate.objective_eq_dual
    {Index Vector : Type} [Fintype Index] [Nonempty Index]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    {r : ℝ} {reference : PositiveProbabilityTable Index}
    {displacement : Index → Vector}
    (certificate : ClusterOptimalityCertificate Index Vector r reference displacement) :
    clusterObjective r
        (tiltedOverlapDistribution r reference displacement certificate.dual)
        reference displacement =
      clusterDualPotential r reference displacement certificate.dual := by
  have hgap := clusterObjective_sub_dual_eq_gap r
    (tiltedOverlapDistribution r reference displacement certificate.dual)
    reference displacement certificate.dual
  rw [finiteRelativeEntropy_self, certificate.fixedPoint, sub_self, norm_zero, pow_two,
    zero_mul, mul_zero, add_zero] at hgap
  linarith

/-- Certified primal optimality, the finite proof-carrying form of the minimum in equation (12). -/
theorem ClusterOptimalityCertificate.objective_le
    {Index Vector : Type} [Fintype Index] [Nonempty Index] [DecidableEq Index]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    {r : ℝ} (hr : 0 ≤ r) {reference : PositiveProbabilityTable Index}
    {displacement : Index → Vector}
    (certificate : ClusterOptimalityCertificate Index Vector r reference displacement)
    (weight : PositiveProbabilityTable Index) :
    clusterObjective r
        (tiltedOverlapDistribution r reference displacement certificate.dual)
        reference displacement ≤
      clusterObjective r weight reference displacement := by
  rw [certificate.objective_eq_dual]
  exact clusterDualPotential_le_objective r hr weight reference displacement certificate.dual

/-- Certified dual optimality, completing the exact primal--dual statement. -/
theorem ClusterOptimalityCertificate.dual_le
    {Index Vector : Type} [Fintype Index] [Nonempty Index] [DecidableEq Index]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    {r : ℝ} (hr : 0 ≤ r) {reference : PositiveProbabilityTable Index}
    {displacement : Index → Vector}
    (certificate : ClusterOptimalityCertificate Index Vector r reference displacement)
    (dual : Vector) :
    clusterDualPotential r reference displacement dual ≤
      clusterDualPotential r reference displacement certificate.dual := by
  calc
    clusterDualPotential r reference displacement dual ≤
        clusterObjective r
          (tiltedOverlapDistribution r reference displacement certificate.dual)
          reference displacement :=
      clusterDualPotential_le_objective r hr _ reference displacement dual
    _ = clusterDualPotential r reference displacement certificate.dual :=
      certificate.objective_eq_dual

theorem tiltedOverlapMass_zero
    {Index Vector : Type} [Fintype Index]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (r : ℝ) (reference : PositiveProbabilityTable Index)
    (displacement : Index → Vector) :
    tiltedOverlapMass r reference displacement 0 =
      softOverlapMass reference displacement := by
  unfold tiltedOverlapMass softOverlapMass
  simp

theorem tiltedOverlapDistribution_zero
    {Index Vector : Type} [Fintype Index] [Nonempty Index]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (r : ℝ) (reference : PositiveProbabilityTable Index)
    (displacement : Index → Vector) :
    tiltedOverlapDistribution r reference displacement 0 =
      softOverlapDistribution reference displacement := by
  apply positiveProbabilityTable_ext
  intro index
  simp [tiltedOverlapDistribution_mass, softOverlapDistribution_mass,
    tiltedOverlapMass_zero]

theorem clusterDualPotential_zero
    {Index Vector : Type} [Fintype Index]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (r : ℝ) (reference : PositiveProbabilityTable Index)
    (displacement : Index → Vector) :
    clusterDualPotential r reference displacement 0 =
      -Real.log (softOverlapMass reference displacement) := by
  simp [clusterDualPotential, tiltedOverlapMass_zero]

/-- Equation (18): the barycenter-free approximation has exactly the displayed primal--dual
gap at the zero dual vector. -/
theorem softOverlap_objective_sub_dual_zero
    {Index Vector : Type} [Fintype Index] [Nonempty Index] [DecidableEq Index]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (r : ℝ) (reference : PositiveProbabilityTable Index)
    (displacement : Index → Vector) :
    clusterObjective r (softOverlapDistribution reference displacement)
        reference displacement -
      clusterDualPotential r reference displacement 0 =
        r / 2 * ‖softBarycenter reference displacement‖ ^ 2 := by
  rw [clusterObjective_sub_dual_eq_gap]
  rw [tiltedOverlapDistribution_zero, finiteRelativeEntropy_self]
  simp only [softBarycenter, sub_zero, zero_add]

/-- Equations (19)--(20), conditional only on the checkable fixed-point witness needed to name
the exact optimizer. -/
theorem ClusterOptimalityCertificate.softOverlap_bracket
    {Index Vector : Type} [Fintype Index] [Nonempty Index] [DecidableEq Index]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    {r : ℝ} (hr : 0 ≤ r) {reference : PositiveProbabilityTable Index}
    {displacement : Index → Vector}
    (certificate : ClusterOptimalityCertificate Index Vector r reference displacement) :
    -Real.log (softOverlapMass reference displacement) ≤
        clusterObjective r
          (tiltedOverlapDistribution r reference displacement certificate.dual)
          reference displacement ∧
      clusterObjective r
          (tiltedOverlapDistribution r reference displacement certificate.dual)
          reference displacement ≤
        -Real.log (softOverlapMass reference displacement) +
          r / 2 * ‖softBarycenter reference displacement‖ ^ 2 := by
  constructor
  · rw [← clusterDualPotential_zero]
    exact clusterDualPotential_le_objective r hr _ reference displacement 0
  · have hle := certificate.objective_le hr
      (softOverlapDistribution reference displacement)
    have hgap := softOverlap_objective_sub_dual_zero r reference displacement
    rw [clusterDualPotential_zero] at hgap
    linarith

/-! ## Explicit Gaussian soft-overlap bounds -/

/-- Turn a family of full-support distributions into identity-embedded local kernels. -/
def identityLocalKernel
    {Secret : Type} [Fintype Secret]
    (distribution : Secret → PositiveProbabilityTable Secret) :
    LocalKernel Secret Secret where
  neighbor := fun _ candidate ↦ candidate
  neighbor_injective := fun _ ↦ Function.injective_id
  distribution := distribution

@[simp]
theorem identityLocalKernel_relativeEntropy
    {Secret : Type} [Fintype Secret]
    (distribution : Secret → PositiveProbabilityTable Secret)
    (reference : PositiveProbabilityTable Secret) (secret : Secret) :
    (identityLocalKernel distribution).relativeEntropy reference secret =
      finiteRelativeEntropy (distribution secret) reference := rfl

@[simp]
theorem identityLocalKernel_averageSquaredDistance
    {Secret Vector : Type} [Fintype Secret]
    [SeminormedAddCommGroup Vector]
    (distribution : Secret → PositiveProbabilityTable Secret)
    (difference : Secret → Secret → Vector) (secret : Secret) :
    (identityLocalKernel distribution).averageSquaredDistance difference secret =
      averageSquaredDisplacement (distribution secret) (fun candidate ↦
        difference candidate secret) := rfl

@[simp]
theorem identityLocalKernel_barycenter
    {Secret Vector : Type} [Fintype Secret]
    [SeminormedAddCommGroup Vector] [NormedSpace ℝ Vector]
    (distribution : Secret → PositiveProbabilityTable Secret)
    (difference : Secret → Secret → Vector) (secret : Secret) :
    (identityLocalKernel distribution).barycenter difference secret =
      displacementBarycenter (distribution secret) (fun candidate ↦
        difference candidate secret) := rfl

/-- The full-support Gibbs kernel from equations (5)--(8). -/
def softOverlapKernel
    {Secret Vector : Type} [Fintype Secret] [Nonempty Secret]
    [SeminormedAddCommGroup Vector]
    (reference : PositiveProbabilityTable Secret)
    (difference : Secret → Secret → Vector) : LocalKernel Secret Secret :=
  identityLocalKernel fun secret ↦
    softOverlapDistribution reference (fun candidate ↦ difference candidate secret)

theorem softOverlapKernel_relativeEntropy_add_distance
    {Secret Vector : Type}
    [Fintype Secret] [Nonempty Secret] [DecidableEq Secret]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (reference : PositiveProbabilityTable Secret)
    (difference : Secret → Secret → Vector) (secret : Secret) :
    (softOverlapKernel reference difference).relativeEntropy reference secret +
        (softOverlapKernel reference difference).averageSquaredDistance
          difference secret / 2 =
      -Real.log (softOverlapMass reference
        (fun candidate ↦ difference candidate secret)) := by
  exact softOverlapDistribution_objective_without_barycenter reference
    (fun candidate ↦ difference candidate secret)

@[simp]
theorem softOverlapKernel_barycenter
    {Secret Vector : Type} [Fintype Secret] [Nonempty Secret]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (reference : PositiveProbabilityTable Secret)
    (difference : Secret → Secret → Vector) (secret : Secret) :
    (softOverlapKernel reference difference).barycenter difference secret =
      softBarycenter reference (fun candidate ↦ difference candidate secret) := rfl

/-- Equation (9), in exponential form.  This is the security-relevant Gibbs specialization and
does not require an optimizer fixed-point certificate. -/
theorem EqualCovarianceGaussianMixtureCertificate.moment_le_softOverlapExp
    {Secret Output Vector : Type}
    [Fintype Secret] [Nonempty Secret] [DecidableEq Secret]
    [Fintype Output]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    {component : Secret → PositiveProbabilityTable Output}
    {mixtureWeight : PositiveProbabilityTable Secret} {alpha : ℝ}
    (certificate : EqualCovarianceGaussianMixtureCertificate
      Secret Output Vector component mixtureWeight alpha)
    (halpha : 1 < alpha) (secret : Secret) :
    finiteRenyiMoment alpha (component secret).mass
        (positiveProbabilityMixture mixtureWeight component).mass ≤
      Real.exp
        (-(alpha - 1) * Real.log
            (softOverlapMass mixtureWeight (fun candidate ↦
              certificate.difference candidate secret)) +
          (alpha - 1) ^ 2 / 2 *
            ‖softBarycenter mixtureWeight (fun candidate ↦
              certificate.difference candidate secret)‖ ^ 2) := by
  let kernel := softOverlapKernel mixtureWeight certificate.difference
  have hcluster := certificate.moment_le_localCluster kernel halpha secret
  have hsoft := softOverlapKernel_relativeEntropy_add_distance
    mixtureWeight certificate.difference secret
  let r : ℝ := alpha - 1
  have hfirst :
      r * kernel.relativeEntropy mixtureWeight secret +
          r / 2 * kernel.averageSquaredDistance certificate.difference secret =
        -r * Real.log
          (softOverlapMass mixtureWeight (fun candidate ↦
            certificate.difference candidate secret)) := by
    calc
      r * kernel.relativeEntropy mixtureWeight secret +
          r / 2 * kernel.averageSquaredDistance certificate.difference secret =
          r * (kernel.relativeEntropy mixtureWeight secret +
            kernel.averageSquaredDistance certificate.difference secret / 2) := by ring
      _ = r * (-Real.log
          (softOverlapMass mixtureWeight (fun candidate ↦
            certificate.difference candidate secret))) := by rw [hsoft]
      _ = -r * Real.log
          (softOverlapMass mixtureWeight (fun candidate ↦
            certificate.difference candidate secret)) := by ring
  calc
    finiteRenyiMoment alpha (component secret).mass
        (positiveProbabilityMixture mixtureWeight component).mass ≤
        Real.exp
          (r * kernel.relativeEntropy mixtureWeight secret +
            r / 2 * kernel.averageSquaredDistance certificate.difference secret +
            r ^ 2 / 2 *
              ‖kernel.barycenter certificate.difference secret‖ ^ 2) := by
      simpa only [kernel, r] using hcluster
    _ = Real.exp
        (-(alpha - 1) * Real.log
            (softOverlapMass mixtureWeight (fun candidate ↦
              certificate.difference candidate secret)) +
          (alpha - 1) ^ 2 / 2 *
            ‖softBarycenter mixtureWeight (fun candidate ↦
              certificate.difference candidate secret)‖ ^ 2) := by
      rw [hfirst]
      simp only [kernel, softOverlapKernel_barycenter]
      rfl

/-- Equation (9), factored as `Z^{-r}` times the barycenter penalty. -/
theorem EqualCovarianceGaussianMixtureCertificate.moment_le_softOverlap
    {Secret Output Vector : Type}
    [Fintype Secret] [Nonempty Secret] [DecidableEq Secret]
    [Fintype Output]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    {component : Secret → PositiveProbabilityTable Output}
    {mixtureWeight : PositiveProbabilityTable Secret} {alpha : ℝ}
    (certificate : EqualCovarianceGaussianMixtureCertificate
      Secret Output Vector component mixtureWeight alpha)
    (halpha : 1 < alpha) (secret : Secret) :
    finiteRenyiMoment alpha (component secret).mass
        (positiveProbabilityMixture mixtureWeight component).mass ≤
      softOverlapMass mixtureWeight (fun candidate ↦
          certificate.difference candidate secret) ^ (-(alpha - 1)) *
        Real.exp
          ((alpha - 1) ^ 2 / 2 *
            ‖softBarycenter mixtureWeight (fun candidate ↦
              certificate.difference candidate secret)‖ ^ 2) := by
  let z := softOverlapMass mixtureWeight (fun candidate ↦
    certificate.difference candidate secret)
  let penalty := (alpha - 1) ^ 2 / 2 *
    ‖softBarycenter mixtureWeight (fun candidate ↦
      certificate.difference candidate secret)‖ ^ 2
  have hz : 0 < z := softOverlapMass_pos mixtureWeight _
  have h := moment_le_softOverlapExp certificate halpha secret
  calc
    finiteRenyiMoment alpha (component secret).mass
        (positiveProbabilityMixture mixtureWeight component).mass ≤
        Real.exp (-(alpha - 1) * Real.log z + penalty) := by
      simpa only [z, penalty] using h
    _ = z ^ (-(alpha - 1)) * Real.exp penalty := by
      rw [Real.rpow_def_of_pos hz, ← Real.exp_add]
      congr 1
      ring

/-- The conditional guessing theorem obtained by inserting the explicit Gibbs bound into the
arbitrary-reference theorem. -/
theorem conditionalGaussianMixtureSoftOverlapGuessingBound
    {Secret Output Vector : Type}
    [Fintype Secret] [Nonempty Secret] [DecidableEq Secret]
    [Fintype Output] [DecidableEq Output]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (component : Secret → PositiveProbabilityTable Output)
    (mixtureWeight : PositiveProbabilityTable Secret)
    (alpha : ℝ) (halpha : 1 < alpha)
    (certificate : EqualCovarianceGaussianMixtureCertificate
      Secret Output Vector component mixtureWeight alpha)
    (channel_mass : ∀ secret output,
      realPointMass (channel secret) output = (component secret).mass output) :
    (conditionalGuessingProbability
      (conditionalChannelJoint prior channel)).toReal ≤
      (∑ secret, realPointMass prior secret ^ alpha *
        Real.exp
          (-(alpha - 1) * Real.log
              (softOverlapMass mixtureWeight (fun candidate ↦
                certificate.difference candidate secret)) +
            (alpha - 1) ^ 2 / 2 *
              ‖softBarycenter mixtureWeight (fun candidate ↦
                certificate.difference candidate secret)‖ ^ 2)) ^
        (1 / alpha) := by
  let kernel := softOverlapKernel mixtureWeight certificate.difference
  have hgeneral := conditionalGaussianMixtureClusterGuessingBound
    prior channel component mixtureWeight alpha halpha certificate kernel channel_mass
  refine hgeneral.trans_eq ?_
  congr 1
  apply Finset.sum_congr rfl
  intro secret _
  congr 1
  have hsoft := softOverlapKernel_relativeEntropy_add_distance
    mixtureWeight certificate.difference secret
  have hfirst :
      (alpha - 1) * kernel.relativeEntropy mixtureWeight secret +
          (alpha - 1) / 2 *
            kernel.averageSquaredDistance certificate.difference secret =
        -(alpha - 1) * Real.log
          (softOverlapMass mixtureWeight (fun candidate ↦
            certificate.difference candidate secret)) := by
    calc
      (alpha - 1) * kernel.relativeEntropy mixtureWeight secret +
          (alpha - 1) / 2 *
            kernel.averageSquaredDistance certificate.difference secret =
          (alpha - 1) * (kernel.relativeEntropy mixtureWeight secret +
            kernel.averageSquaredDistance certificate.difference secret / 2) := by ring
      _ = (alpha - 1) * (-Real.log
          (softOverlapMass mixtureWeight (fun candidate ↦
            certificate.difference candidate secret))) := by rw [hsoft]
      _ = -(alpha - 1) * Real.log
          (softOverlapMass mixtureWeight (fun candidate ↦
            certificate.difference candidate secret)) := by ring
  rw [hfirst]
  simp only [kernel, softOverlapKernel_barycenter]

/-! ## Restricted soft-overlap neighborhoods -/

/-- Soft overlap mass on an injectively embedded local candidate type. -/
def restrictedSoftOverlapMass
    {Local Global Vector : Type} [Fintype Local] [Fintype Global]
    [SeminormedAddCommGroup Vector]
    (reference : PositiveProbabilityTable Global) (embed : Local → Global)
    (displacement : Local → Vector) : ℝ :=
  ∑ index, reference.mass (embed index) *
    Real.exp (-‖displacement index‖ ^ 2 / 2)

theorem restrictedSoftOverlapMass_pos
    {Local Global Vector : Type} [Fintype Local] [Nonempty Local] [Fintype Global]
    [SeminormedAddCommGroup Vector]
    (reference : PositiveProbabilityTable Global) (embed : Local → Global)
    (displacement : Local → Vector) :
    0 < restrictedSoftOverlapMass reference embed displacement := by
  unfold restrictedSoftOverlapMass
  exact Finset.sum_pos
    (fun index _ ↦ mul_pos (reference.positive (embed index)) (Real.exp_pos _))
    Finset.univ_nonempty

/-- Gibbs law normalized only over a manageable local candidate set. -/
def restrictedSoftOverlapDistribution
    {Local Global Vector : Type} [Fintype Local] [Nonempty Local] [Fintype Global]
    [SeminormedAddCommGroup Vector]
    (reference : PositiveProbabilityTable Global) (embed : Local → Global)
    (displacement : Local → Vector) : PositiveProbabilityTable Local where
  mass index := reference.mass (embed index) *
    Real.exp (-‖displacement index‖ ^ 2 / 2) /
      restrictedSoftOverlapMass reference embed displacement
  positive index := div_pos
    (mul_pos (reference.positive (embed index)) (Real.exp_pos _))
    (restrictedSoftOverlapMass_pos reference embed displacement)
  sum_mass := by
    rw [← Finset.sum_div]
    exact div_self (ne_of_gt
      (restrictedSoftOverlapMass_pos reference embed displacement))

theorem restrictedSoftOverlapDistribution_log_ratio
    {Local Global Vector : Type} [Fintype Local] [Nonempty Local] [Fintype Global]
    [SeminormedAddCommGroup Vector]
    (reference : PositiveProbabilityTable Global) (embed : Local → Global)
    (displacement : Local → Vector) (index : Local) :
    Real.log
        ((restrictedSoftOverlapDistribution reference embed displacement).mass index /
          reference.mass (embed index)) =
      -‖displacement index‖ ^ 2 / 2 -
        Real.log (restrictedSoftOverlapMass reference embed displacement) := by
  have hratio :
      (restrictedSoftOverlapDistribution reference embed displacement).mass index /
          reference.mass (embed index) =
        Real.exp (-‖displacement index‖ ^ 2 / 2) /
          restrictedSoftOverlapMass reference embed displacement := by
    change
      (reference.mass (embed index) * Real.exp (-‖displacement index‖ ^ 2 / 2) /
          restrictedSoftOverlapMass reference embed displacement) /
          reference.mass (embed index) = _
    field_simp [ne_of_gt (reference.positive (embed index)),
      ne_of_gt (restrictedSoftOverlapMass_pos reference embed displacement)]
  rw [hratio, Real.log_div (ne_of_gt (Real.exp_pos _))
    (ne_of_gt (restrictedSoftOverlapMass_pos reference embed displacement)), Real.log_exp]

/-- Restricted analogue of equation (7). -/
theorem restrictedSoftOverlap_objective_eq
    {Local Global Vector : Type} [Fintype Local] [Nonempty Local] [Fintype Global]
    [SeminormedAddCommGroup Vector]
    (reference : PositiveProbabilityTable Global) (embed : Local → Global)
    (displacement : Local → Vector) :
    (∑ index,
        (restrictedSoftOverlapDistribution reference embed displacement).mass index *
          Real.log
            ((restrictedSoftOverlapDistribution reference embed displacement).mass index /
              reference.mass (embed index))) +
        averageSquaredDisplacement
          (restrictedSoftOverlapDistribution reference embed displacement) displacement / 2 =
      -Real.log (restrictedSoftOverlapMass reference embed displacement) := by
  unfold averageSquaredDisplacement
  simp_rw [restrictedSoftOverlapDistribution_log_ratio reference embed displacement]
  simp_rw [mul_sub]
  rw [Finset.sum_sub_distrib]
  have hdistance :
      (∑ index,
        (restrictedSoftOverlapDistribution reference embed displacement).mass index *
          (‖displacement index‖ ^ 2 / 2)) =
        (∑ index,
          (restrictedSoftOverlapDistribution reference embed displacement).mass index *
            ‖displacement index‖ ^ 2) / 2 := by
    calc
      _ = ∑ index,
          ((restrictedSoftOverlapDistribution reference embed displacement).mass index *
            ‖displacement index‖ ^ 2) / 2 := by
        apply Finset.sum_congr rfl
        intro index _
        ring
      _ = _ := by rw [Finset.sum_div]
  have hnegativeDistance :
      (∑ index,
        (restrictedSoftOverlapDistribution reference embed displacement).mass index *
          (-‖displacement index‖ ^ 2 / 2)) =
        -((∑ index,
          (restrictedSoftOverlapDistribution reference embed displacement).mass index *
            ‖displacement index‖ ^ 2) / 2) := by
    calc
      _ = ∑ index,
          -((restrictedSoftOverlapDistribution reference embed displacement).mass index *
            (‖displacement index‖ ^ 2 / 2)) := by
        apply Finset.sum_congr rfl
        intro index _
        ring
      _ = -(∑ index,
          (restrictedSoftOverlapDistribution reference embed displacement).mass index *
            (‖displacement index‖ ^ 2 / 2)) := by
        rw [Finset.sum_neg_distrib]
      _ = _ := by rw [hdistance]
  rw [hnegativeDistance]
  rw [← Finset.sum_mul,
    (restrictedSoftOverlapDistribution reference embed displacement).sum_mass, one_mul]
  ring

/-- Center-dependent restricted Gibbs local kernel. -/
def restrictedSoftOverlapKernel
    {Secret Local Vector : Type} [Fintype Secret] [Fintype Local] [Nonempty Local]
    [SeminormedAddCommGroup Vector]
    (reference : PositiveProbabilityTable Secret)
    (embed : Secret → Local → Secret)
    (embed_injective : ∀ secret, Function.Injective (embed secret))
    (difference : Secret → Secret → Vector) : LocalKernel Secret Local where
  neighbor := embed
  neighbor_injective := embed_injective
  distribution := fun secret ↦
    restrictedSoftOverlapDistribution reference (embed secret)
      (fun index ↦ difference (embed secret index) secret)

/-- Equation (29), in exponential form, for any injectively represented local candidate set. -/
theorem EqualCovarianceGaussianMixtureCertificate.moment_le_restrictedSoftOverlapExp
    {Secret Local Output Vector : Type}
    [Fintype Secret] [Nonempty Secret] [DecidableEq Secret]
    [Fintype Local] [Nonempty Local] [Fintype Output]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    {component : Secret → PositiveProbabilityTable Output}
    {mixtureWeight : PositiveProbabilityTable Secret} {alpha : ℝ}
    (certificate : EqualCovarianceGaussianMixtureCertificate
      Secret Output Vector component mixtureWeight alpha)
    (embed : Secret → Local → Secret)
    (embed_injective : ∀ secret, Function.Injective (embed secret))
    (halpha : 1 < alpha) (secret : Secret) :
    finiteRenyiMoment alpha (component secret).mass
        (positiveProbabilityMixture mixtureWeight component).mass ≤
      Real.exp
        (-(alpha - 1) * Real.log
            (restrictedSoftOverlapMass mixtureWeight (embed secret)
              (fun index ↦ certificate.difference (embed secret index) secret)) +
          (alpha - 1) ^ 2 / 2 *
            ‖displacementBarycenter
              (restrictedSoftOverlapDistribution mixtureWeight (embed secret)
                (fun index ↦ certificate.difference (embed secret index) secret))
              (fun index ↦ certificate.difference (embed secret index) secret)‖ ^ 2) := by
  let kernel := restrictedSoftOverlapKernel mixtureWeight embed embed_injective
    certificate.difference
  have hcluster := certificate.moment_le_localCluster kernel halpha secret
  have hsoft := restrictedSoftOverlap_objective_eq mixtureWeight (embed secret)
    (fun index ↦ certificate.difference (embed secret index) secret)
  let r : ℝ := alpha - 1
  have hfirst :
      r * kernel.relativeEntropy mixtureWeight secret +
          r / 2 * kernel.averageSquaredDistance certificate.difference secret =
        -r * Real.log
          (restrictedSoftOverlapMass mixtureWeight (embed secret)
            (fun index ↦ certificate.difference (embed secret index) secret)) := by
    change r *
        (∑ index,
          (restrictedSoftOverlapDistribution mixtureWeight (embed secret)
            (fun index ↦ certificate.difference (embed secret index) secret)).mass index *
              Real.log
                ((restrictedSoftOverlapDistribution mixtureWeight (embed secret)
                  (fun index ↦ certificate.difference (embed secret index) secret)).mass index /
                  mixtureWeight.mass (embed secret index))) +
        r / 2 * averageSquaredDisplacement
          (restrictedSoftOverlapDistribution mixtureWeight (embed secret)
            (fun index ↦ certificate.difference (embed secret index) secret))
          (fun index ↦ certificate.difference (embed secret index) secret) = _
    calc
      _ = r * ((∑ index,
          (restrictedSoftOverlapDistribution mixtureWeight (embed secret)
            (fun index ↦ certificate.difference (embed secret index) secret)).mass index *
              Real.log
                ((restrictedSoftOverlapDistribution mixtureWeight (embed secret)
                  (fun index ↦ certificate.difference (embed secret index) secret)).mass index /
                  mixtureWeight.mass (embed secret index))) +
        averageSquaredDisplacement
          (restrictedSoftOverlapDistribution mixtureWeight (embed secret)
            (fun index ↦ certificate.difference (embed secret index) secret))
          (fun index ↦ certificate.difference (embed secret index) secret) / 2) := by ring
      _ = r * (-Real.log
          (restrictedSoftOverlapMass mixtureWeight (embed secret)
            (fun index ↦ certificate.difference (embed secret index) secret))) := by rw [hsoft]
      _ = _ := by ring
  calc
    finiteRenyiMoment alpha (component secret).mass
        (positiveProbabilityMixture mixtureWeight component).mass ≤
        Real.exp
          (r * kernel.relativeEntropy mixtureWeight secret +
            r / 2 * kernel.averageSquaredDistance certificate.difference secret +
            r ^ 2 / 2 * ‖kernel.barycenter certificate.difference secret‖ ^ 2) := by
      simpa only [kernel, r] using hcluster
    _ = _ := by
      rw [hfirst]
      rfl

/-! ## Effective local codebook size -/

/-- A single mixture component always gives the trivial bound
`Xi_alpha(s) <= beta(s)^(1-alpha)`.  This is the rigorous source of the `K >= 1` floor and does
not require a point mass to inhabit the strictly-positive optimizer type. -/
theorem finiteRenyiMoment_component_mixture_le_weight
    {Secret Output : Type}
    [Fintype Secret] [Nonempty Secret] [DecidableEq Secret] [Fintype Output]
    (component : Secret → PositiveProbabilityTable Output)
    (weight : PositiveProbabilityTable Secret)
    (alpha : ℝ) (halpha : 1 < alpha) (secret : Secret) :
    finiteRenyiMoment alpha (component secret).mass
        (positiveProbabilityMixture weight component).mass ≤
      weight.mass secret ^ (1 - alpha) := by
  unfold finiteRenyiMoment
  calc
    (∑ output, (component secret).mass output ^ alpha *
        (positiveProbabilityMixture weight component).mass output ^ (1 - alpha)) ≤
        ∑ output, (component secret).mass output *
          weight.mass secret ^ (1 - alpha) := by
      apply Finset.sum_le_sum
      intro output _
      have hmixture :
          weight.mass secret * (component secret).mass output ≤
            (positiveProbabilityMixture weight component).mass output := by
        change weight.mass secret * (component secret).mass output ≤
          ∑ candidate, weight.mass candidate * (component candidate).mass output
        exact Finset.single_le_sum
          (fun candidate _ ↦ mul_nonneg (weight.nonneg candidate)
            ((component candidate).nonneg output))
          (Finset.mem_univ secret)
      have hnegative : 1 - alpha ≤ 0 := by linarith
      have hrpow :
          (positiveProbabilityMixture weight component).mass output ^ (1 - alpha) ≤
            (weight.mass secret * (component secret).mass output) ^ (1 - alpha) :=
        Real.rpow_le_rpow_of_nonpos
          (mul_pos (weight.positive secret) ((component secret).positive output))
          hmixture hnegative
      calc
        (component secret).mass output ^ alpha *
            (positiveProbabilityMixture weight component).mass output ^ (1 - alpha) ≤
            (component secret).mass output ^ alpha *
              (weight.mass secret * (component secret).mass output) ^ (1 - alpha) :=
          mul_le_mul_of_nonneg_left hrpow
            (Real.rpow_nonneg ((component secret).nonneg output) alpha)
        _ = (component secret).mass output *
            weight.mass secret ^ (1 - alpha) := by
          rw [Real.mul_rpow (weight.nonneg secret) ((component secret).nonneg output)]
          have hcombine :
              (component secret).mass output ^ alpha *
                  (component secret).mass output ^ (1 - alpha) =
                (component secret).mass output := by
            rw [← Real.rpow_add ((component secret).positive output)]
            norm_num
          calc
            (component secret).mass output ^ alpha *
                (weight.mass secret ^ (1 - alpha) *
                  (component secret).mass output ^ (1 - alpha)) =
                weight.mass secret ^ (1 - alpha) *
                  ((component secret).mass output ^ alpha *
                    (component secret).mass output ^ (1 - alpha)) := by ring
            _ = weight.mass secret ^ (1 - alpha) *
                (component secret).mass output := by rw [hcombine]
            _ = _ := by ring
    _ = weight.mass secret ^ (1 - alpha) := by
      rw [← Finset.sum_mul, (component secret).sum_mass, one_mul]

/-- The directly computable effective local codebook size from equations (23)--(24), before
taking the maximum with the universal floor one. -/
def softEffectiveOverlap
    {Index Vector : Type} [Fintype Index] [Nonempty Index]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (r : ℝ) (reference : PositiveProbabilityTable Index)
    (displacement : Index → Vector) (center : Index) : ℝ :=
  (softOverlapMass reference displacement / reference.mass center) *
    Real.exp (-r / 2 * ‖softBarycenter reference displacement‖ ^ 2)

theorem softEffectiveOverlap_pos
    {Index Vector : Type} [Fintype Index] [Nonempty Index]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (r : ℝ) (reference : PositiveProbabilityTable Index)
    (displacement : Index → Vector) (center : Index) :
    0 < softEffectiveOverlap r reference displacement center :=
  mul_pos
    (div_pos (softOverlapMass_pos reference displacement) (reference.positive center))
    (Real.exp_pos _)

/-- The certified effective size, floored at one by the exact one-component mixture bound. -/
def certifiedSoftEffectiveOverlap
    {Index Vector : Type} [Fintype Index] [Nonempty Index]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (r : ℝ) (reference : PositiveProbabilityTable Index)
    (displacement : Index → Vector) (center : Index) : ℝ :=
  max 1 (softEffectiveOverlap r reference displacement center)

theorem certifiedSoftEffectiveOverlap_one_le
    {Index Vector : Type} [Fintype Index] [Nonempty Index]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (r : ℝ) (reference : PositiveProbabilityTable Index)
    (displacement : Index → Vector) (center : Index) :
    1 ≤ certifiedSoftEffectiveOverlap r reference displacement center :=
  le_max_left _ _

theorem softMomentBound_eq_weight_mul_effective
    {Index Vector : Type} [Fintype Index] [Nonempty Index]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (r : ℝ) (reference : PositiveProbabilityTable Index)
    (displacement : Index → Vector) (center : Index) :
    softOverlapMass reference displacement ^ (-r) *
        Real.exp (r ^ 2 / 2 * ‖softBarycenter reference displacement‖ ^ 2) =
      reference.mass center ^ (-r) *
        softEffectiveOverlap r reference displacement center ^ (-r) := by
  let z := softOverlapMass reference displacement
  let b := reference.mass center
  let barycenterSq := ‖softBarycenter reference displacement‖ ^ 2
  have hz : 0 < z := softOverlapMass_pos reference displacement
  have hb : 0 < b := reference.positive center
  have he : 0 < Real.exp (-r / 2 * barycenterSq) := Real.exp_pos _
  have hk : 0 < softEffectiveOverlap r reference displacement center :=
    softEffectiveOverlap_pos r reference displacement center
  rw [Real.rpow_def_of_pos hz, Real.rpow_def_of_pos hb,
    Real.rpow_def_of_pos hk, ← Real.exp_add, ← Real.exp_add]
  congr 1
  have hlog :
      Real.log (softEffectiveOverlap r reference displacement center) =
        Real.log z - Real.log b - r / 2 * barycenterSq := by
    unfold softEffectiveOverlap
    dsimp [z, b, barycenterSq]
    rw [Real.log_mul (ne_of_gt (div_pos hz hb)) (ne_of_gt he),
      Real.log_div (ne_of_gt hz) (ne_of_gt hb), Real.log_exp]
    change Real.log z - Real.log b + -r / 2 * barycenterSq =
      Real.log z - Real.log b - r / 2 * barycenterSq
    ring
  rw [hlog]
  dsimp [z, b, barycenterSq]
  ring

/-- Equations (23)--(24): the soft Gaussian moment is controlled by the certified effective
codebook size, with the exact one-component bound supplying the floor at one. -/
theorem EqualCovarianceGaussianMixtureCertificate.moment_le_certifiedEffectiveOverlap
    {Secret Output Vector : Type}
    [Fintype Secret] [Nonempty Secret] [DecidableEq Secret]
    [Fintype Output]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    {component : Secret → PositiveProbabilityTable Output}
    {mixtureWeight : PositiveProbabilityTable Secret} {r : ℝ}
    (certificate : EqualCovarianceGaussianMixtureCertificate
      Secret Output Vector component mixtureWeight (1 + r))
    (hr : 0 < r) (secret : Secret) :
    finiteRenyiMoment (1 + r) (component secret).mass
        (positiveProbabilityMixture mixtureWeight component).mass ≤
      mixtureWeight.mass secret ^ (-r) *
        certifiedSoftEffectiveOverlap r mixtureWeight
          (fun candidate ↦ certificate.difference candidate secret) secret ^ (-r) := by
  let displacement : Secret → Vector := fun candidate ↦
    certificate.difference candidate secret
  by_cases hsmall : softEffectiveOverlap r mixtureWeight displacement secret ≤ 1
  · have htrivial := finiteRenyiMoment_component_mixture_le_weight
      component mixtureWeight (1 + r) (by linarith) secret
    have hexponent : 1 - (1 + r) = -r := by ring
    rw [hexponent] at htrivial
    have hmax : certifiedSoftEffectiveOverlap r mixtureWeight displacement secret = 1 :=
      max_eq_left hsmall
    simpa only [displacement, hmax, Real.one_rpow, mul_one] using htrivial
  · have hlarge : 1 ≤ softEffectiveOverlap r mixtureWeight displacement secret :=
      le_of_not_ge hsmall
    have hsoft := moment_le_softOverlap certificate (by linarith) secret
    have hmax : certifiedSoftEffectiveOverlap r mixtureWeight displacement secret =
        softEffectiveOverlap r mixtureWeight displacement secret := max_eq_right hlarge
    rw [hmax]
    rw [← softMomentBound_eq_weight_mul_effective r mixtureWeight displacement secret]
    simpa only [displacement, add_sub_cancel_left] using hsoft

/-- Equations (25)--(26): with the actual positive prior as mixture weight, the guessing bound is
the prior expectation of the certified effective codebook size to power `-r`. -/
theorem conditionalGaussianMixtureEffectiveOverlapGuessingBound
    {Secret Output Vector : Type}
    [Fintype Secret] [Nonempty Secret] [DecidableEq Secret]
    [Fintype Output] [DecidableEq Output]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (component : Secret → PositiveProbabilityTable Output)
    (mixtureWeight : PositiveProbabilityTable Secret)
    (r : ℝ) (hr : 0 < r)
    (certificate : EqualCovarianceGaussianMixtureCertificate
      Secret Output Vector component mixtureWeight (1 + r))
    (prior_mass : ∀ secret, realPointMass prior secret = mixtureWeight.mass secret)
    (channel_mass : ∀ secret output,
      realPointMass (channel secret) output = (component secret).mass output) :
    (conditionalGuessingProbability
      (conditionalChannelJoint prior channel)).toReal ≤
      (∑ secret, mixtureWeight.mass secret *
        certifiedSoftEffectiveOverlap r mixtureWeight
          (fun candidate ↦ certificate.difference candidate secret) secret ^ (-r)) ^
        (1 / (1 + r)) := by
  let reference := positiveProbabilityMixture mixtureWeight component
  have hfunctional :
      referenceRenyiFunctional prior channel reference (1 + r) =
        ∑ secret, mixtureWeight.mass secret ^ (1 + r) *
          finiteRenyiMoment (1 + r) (component secret).mass reference.mass := by
    unfold referenceRenyiFunctional
    apply Finset.sum_congr rfl
    intro secret _
    rw [prior_mass]
    congr 1
    unfold finiteRenyiMoment
    apply Finset.sum_congr rfl
    intro output _
    change realPointMass (channel secret) output ^ (1 + r) *
      reference.mass output ^ (1 - (1 + r)) = _
    rw [channel_mass]
  have hsourceNonneg :
      0 ≤ ∑ secret, mixtureWeight.mass secret ^ (1 + r) *
        finiteRenyiMoment (1 + r) (component secret).mass reference.mass := by
    apply Finset.sum_nonneg
    intro secret _
    apply mul_nonneg (Real.rpow_nonneg (mixtureWeight.nonneg secret) (1 + r))
    unfold finiteRenyiMoment
    exact Finset.sum_nonneg fun output _ ↦ mul_nonneg
      (Real.rpow_nonneg ((component secret).nonneg output) (1 + r))
      (Real.rpow_nonneg (reference.nonneg output) (1 - (1 + r)))
  have hsum :
      (∑ secret, mixtureWeight.mass secret ^ (1 + r) *
        finiteRenyiMoment (1 + r) (component secret).mass reference.mass) ≤
        ∑ secret, mixtureWeight.mass secret *
          certifiedSoftEffectiveOverlap r mixtureWeight
            (fun candidate ↦ certificate.difference candidate secret) secret ^ (-r) := by
    apply Finset.sum_le_sum
    intro secret _
    have hmoment :=
      EqualCovarianceGaussianMixtureCertificate.moment_le_certifiedEffectiveOverlap
        certificate hr secret
    have hmassCombine :
        mixtureWeight.mass secret ^ (1 + r) *
          mixtureWeight.mass secret ^ (-r) = mixtureWeight.mass secret := by
      rw [← Real.rpow_add (mixtureWeight.positive secret),
        show (1 + r) + -r = 1 by ring, Real.rpow_one]
    calc
      mixtureWeight.mass secret ^ (1 + r) *
          finiteRenyiMoment (1 + r) (component secret).mass reference.mass ≤
          mixtureWeight.mass secret ^ (1 + r) *
            (mixtureWeight.mass secret ^ (-r) *
              certifiedSoftEffectiveOverlap r mixtureWeight
                (fun candidate ↦ certificate.difference candidate secret) secret ^ (-r)) :=
        mul_le_mul_of_nonneg_left hmoment
          (Real.rpow_nonneg (mixtureWeight.nonneg secret) (1 + r))
      _ = mixtureWeight.mass secret *
          certifiedSoftEffectiveOverlap r mixtureWeight
            (fun candidate ↦ certificate.difference candidate secret) secret ^ (-r) := by
        rw [← mul_assoc, hmassCombine]
  calc
    (conditionalGuessingProbability
      (conditionalChannelJoint prior channel)).toReal ≤
        (referenceRenyiFunctional prior channel reference (1 + r)) ^
          (1 / (1 + r)) :=
      arbitraryReferenceRenyiGuessingBound prior channel reference (1 + r) (by linarith)
    _ = (∑ secret, mixtureWeight.mass secret ^ (1 + r) *
          finiteRenyiMoment (1 + r) (component secret).mass reference.mass) ^
            (1 / (1 + r)) := by rw [hfunctional]
    _ ≤ (∑ secret, mixtureWeight.mass secret *
        certifiedSoftEffectiveOverlap r mixtureWeight
          (fun candidate ↦ certificate.difference candidate secret) secret ^ (-r)) ^
          (1 / (1 + r)) := by
      exact Real.rpow_le_rpow hsourceNonneg hsum (by positivity)

/-- The effective-overlap moment appearing in equations (25)--(27). -/
def effectiveOverlapMoment
    {Index : Type} [Fintype Index]
    (weight : PositiveProbabilityTable Index) (effectiveSize : Index → ℝ)
    (r : ℝ) : ℝ :=
  ∑ index, weight.mass index * effectiveSize index ^ (-r)

theorem effectiveOverlapMoment_nonneg
    {Index : Type} [Fintype Index]
    (weight : PositiveProbabilityTable Index) (effectiveSize : Index → ℝ)
    (r : ℝ) (effective_nonneg : ∀ index, 0 ≤ effectiveSize index) :
    0 ≤ effectiveOverlapMoment weight effectiveSize r :=
  Finset.sum_nonneg fun index _ ↦ mul_nonneg (weight.nonneg index)
    (Real.rpow_nonneg (effective_nonneg index) (-r))

/-- Equation (27): a high effective size off a bad set gives the exact bad-mass plus exponential
moment bound. -/
theorem effectiveOverlapMoment_le_bad_add_exp
    {Index : Type} [Fintype Index]
    (weight : PositiveProbabilityTable Index) (effectiveSize : Index → ℝ)
    (r threshold epsilon : ℝ) (hr : 0 ≤ r) (hthreshold : 0 ≤ threshold)
    (_hepsilonNonneg : 0 ≤ epsilon) (_hepsilonLe : epsilon ≤ 1)
    (bad : Index → Prop) [DecidablePred bad]
    (effective_one_le : ∀ index, 1 ≤ effectiveSize index)
    (bad_mass :
      (∑ index ∈ (Finset.univ : Finset Index).filter bad,
        weight.mass index) ≤ epsilon)
    (good_effective : ∀ index, ¬bad index →
      Real.exp threshold ≤ effectiveSize index) :
    effectiveOverlapMoment weight effectiveSize r ≤
      epsilon + (1 - epsilon) * Real.exp (-r * threshold) := by
  let badWeight : ℝ :=
    ∑ index ∈ (Finset.univ : Finset Index).filter bad, weight.mass index
  let decay : ℝ := Real.exp (-r * threshold)
  have hdecayNonneg : 0 ≤ decay := (Real.exp_pos _).le
  have hdecayLe : decay ≤ 1 := by
    dsimp [decay]
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.mpr (by nlinarith)
  have hbadTerm :
      (∑ index ∈ (Finset.univ : Finset Index).filter bad,
          weight.mass index * effectiveSize index ^ (-r)) ≤ badWeight := by
    dsimp [badWeight]
    apply Finset.sum_le_sum
    intro index _
    exact mul_le_of_le_one_right (weight.nonneg index)
      (Real.rpow_le_one_of_one_le_of_nonpos (effective_one_le index) (by linarith))
  have hgoodTerm :
      (∑ index ∈ (Finset.univ : Finset Index).filter (fun index ↦ ¬bad index),
          weight.mass index * effectiveSize index ^ (-r)) ≤
        (1 - badWeight) * decay := by
    have hpoint : ∀ index, ¬bad index → effectiveSize index ^ (-r) ≤ decay := by
      intro index hgood
      have hpow := Real.rpow_le_rpow_of_nonpos
        (Real.exp_pos threshold) (good_effective index hgood) (by linarith : -r ≤ 0)
      calc
        effectiveSize index ^ (-r) ≤ Real.exp threshold ^ (-r) := hpow
        _ = decay := by
          rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
          dsimp [decay]
          congr 1
          ring
    calc
      (∑ index ∈ (Finset.univ : Finset Index).filter (fun index ↦ ¬bad index),
          weight.mass index * effectiveSize index ^ (-r)) ≤
          ∑ index ∈ (Finset.univ : Finset Index).filter (fun index ↦ ¬bad index),
            weight.mass index * decay := by
        apply Finset.sum_le_sum
        intro index hmem
        exact mul_le_mul_of_nonneg_left
          (hpoint index (by simpa using (Finset.mem_filter.mp hmem).2))
          (weight.nonneg index)
      _ = (1 - badWeight) * decay := by
        rw [← Finset.sum_mul]
        have hsplit := Finset.sum_filter_add_sum_filter_not
          (Finset.univ : Finset Index) bad weight.mass
        have htotal : ∑ index, weight.mass index = 1 := weight.sum_mass
        have hgoodMass :
            (∑ index ∈ (Finset.univ : Finset Index).filter (fun index ↦ ¬bad index),
              weight.mass index) = 1 - badWeight := by
          have hsplit' :
              (∑ index ∈ (Finset.univ : Finset Index).filter bad,
                  weight.mass index) +
                ∑ index ∈ (Finset.univ : Finset Index).filter (fun index ↦ ¬bad index),
                  weight.mass index = 1 := by
            simpa only [htotal] using hsplit
          dsimp [badWeight]
          linarith
        rw [hgoodMass]
  calc
    effectiveOverlapMoment weight effectiveSize r =
        (∑ index ∈ (Finset.univ : Finset Index).filter bad,
          weight.mass index * effectiveSize index ^ (-r)) +
        ∑ index ∈ (Finset.univ : Finset Index).filter (fun index ↦ ¬bad index),
          weight.mass index * effectiveSize index ^ (-r) := by
      unfold effectiveOverlapMoment
      exact (Finset.sum_filter_add_sum_filter_not Finset.univ bad
        (fun index ↦ weight.mass index * effectiveSize index ^ (-r))).symm
    _ ≤ badWeight + (1 - badWeight) * decay := add_le_add hbadTerm hgoodTerm
    _ = decay + (1 - decay) * badWeight := by ring
    _ ≤ decay + (1 - decay) * epsilon := by
      exact (add_le_add_iff_left decay).2
        (mul_le_mul_of_nonneg_left bad_mass (sub_nonneg.mpr hdecayLe))
    _ = epsilon + (1 - epsilon) * Real.exp (-r * threshold) := by
      dsimp [decay]
      ring

/-- Concrete effective-size bad-set theorem obtained by combining equations (26) and (27). -/
theorem conditionalGaussianMixtureEffectiveOverlapBadSetBound
    {Secret Output Vector : Type}
    [Fintype Secret] [Nonempty Secret] [DecidableEq Secret]
    [Fintype Output] [DecidableEq Output]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (component : Secret → PositiveProbabilityTable Output)
    (mixtureWeight : PositiveProbabilityTable Secret)
    (r threshold epsilon : ℝ) (hr : 0 < r) (hthreshold : 0 ≤ threshold)
    (hepsilonNonneg : 0 ≤ epsilon) (hepsilonLe : epsilon ≤ 1)
    (certificate : EqualCovarianceGaussianMixtureCertificate
      Secret Output Vector component mixtureWeight (1 + r))
    (prior_mass : ∀ secret, realPointMass prior secret = mixtureWeight.mass secret)
    (channel_mass : ∀ secret output,
      realPointMass (channel secret) output = (component secret).mass output)
    (bad : Secret → Prop) [DecidablePred bad]
    (bad_mass :
      (∑ secret ∈ (Finset.univ : Finset Secret).filter bad,
        mixtureWeight.mass secret) ≤ epsilon)
    (good_effective : ∀ secret, ¬bad secret →
      Real.exp threshold ≤
        certifiedSoftEffectiveOverlap r mixtureWeight
          (fun candidate ↦ certificate.difference candidate secret) secret) :
    (conditionalGuessingProbability
      (conditionalChannelJoint prior channel)).toReal ≤
      (epsilon + (1 - epsilon) * Real.exp (-r * threshold)) ^
        (1 / (1 + r)) := by
  let effectiveSize : Secret → ℝ := fun secret ↦
    certifiedSoftEffectiveOverlap r mixtureWeight
      (fun candidate ↦ certificate.difference candidate secret) secret
  have hguess := conditionalGaussianMixtureEffectiveOverlapGuessingBound
    prior channel component mixtureWeight r hr certificate prior_mass channel_mass
  have hmoment := effectiveOverlapMoment_le_bad_add_exp
    mixtureWeight effectiveSize r threshold epsilon hr.le hthreshold
      hepsilonNonneg hepsilonLe bad
      (fun secret ↦ certifiedSoftEffectiveOverlap_one_le r mixtureWeight _ secret)
      bad_mass good_effective
  have hsource : 0 ≤ effectiveOverlapMoment mixtureWeight effectiveSize r :=
    effectiveOverlapMoment_nonneg mixtureWeight effectiveSize r fun secret ↦
      (zero_le_one.trans
        (certifiedSoftEffectiveOverlap_one_le r mixtureWeight _ secret))
  calc
    (conditionalGuessingProbability
      (conditionalChannelJoint prior channel)).toReal ≤
        effectiveOverlapMoment mixtureWeight effectiveSize r ^ (1 / (1 + r)) := by
      simpa only [effectiveOverlapMoment, effectiveSize] using hguess
    _ ≤ (epsilon + (1 - epsilon) * Real.exp (-r * threshold)) ^
        (1 / (1 + r)) := by
      exact Real.rpow_le_rpow hsource hmoment (by positivity)

/-! ## General finite non-Gaussian channels -/

/-- The cluster average of the log-likelihood ratio `log (W_t(y) / W_s(y))`.  Strictly
positive finite tables are the counting-measure version of densities with a common dominating
measure. -/
def averagedLogLikelihoodRatio
    {Secret Output : Type} [Fintype Secret] [Fintype Output]
    (cluster : PositiveProbabilityTable Secret)
    (component : Secret → PositiveProbabilityTable Output)
    (secret : Secret) (output : Output) : ℝ :=
  ∑ candidate, cluster.mass candidate *
    Real.log ((component candidate).mass output / (component secret).mass output)

/-- The logarithmic-moment term in equation (31), before applying `log`. -/
def finiteLikelihoodRatioClusterMoment
    {Secret Output : Type} [Fintype Secret] [Fintype Output]
    (cluster : PositiveProbabilityTable Secret)
    (component : Secret → PositiveProbabilityTable Output)
    (r : ℝ) (secret : Secret) : ℝ :=
  ∑ output, (component secret).mass output *
    Real.exp (-r * averagedLogLikelihoodRatio cluster component secret output)

theorem finiteLikelihoodRatioClusterMoment_pos
    {Secret Output : Type} [Fintype Secret] [Fintype Output] [Nonempty Output]
    (cluster : PositiveProbabilityTable Secret)
    (component : Secret → PositiveProbabilityTable Output)
    (r : ℝ) (secret : Secret) :
    0 < finiteLikelihoodRatioClusterMoment cluster component r secret := by
  unfold finiteLikelihoodRatioClusterMoment
  exact Finset.sum_pos
    (fun output _ ↦ mul_pos ((component secret).positive output) (Real.exp_pos _))
    Finset.univ_nonempty

/-- Weighted AM--GM lower-bounds the global mixture likelihood ratio by a selected cluster.
This is the pointwise engine of equation (31). -/
theorem exp_neg_entropy_add_average_logLikelihood_le_mixtureRatio
    {Secret Output : Type}
    [Fintype Secret] [Nonempty Secret] [DecidableEq Secret] [Fintype Output]
    (cluster mixtureWeight : PositiveProbabilityTable Secret)
    (component : Secret → PositiveProbabilityTable Output)
    (secret : Secret) (output : Output) :
    Real.exp
        (-finiteRelativeEntropy cluster mixtureWeight +
          averagedLogLikelihoodRatio cluster component secret output) ≤
      (positiveProbabilityMixture mixtureWeight component).mass output /
        (component secret).mass output := by
  have hamgm := exp_neg_relativeEntropy_add_expectation_le_mixture
    cluster mixtureWeight (fun candidate ↦ candidate) Function.injective_id
      (fun candidate ↦
        Real.log ((component candidate).mass output / (component secret).mass output))
  have hright :
      (∑ candidate, mixtureWeight.mass candidate *
          Real.exp
            (Real.log ((component candidate).mass output /
              (component secret).mass output))) =
        (positiveProbabilityMixture mixtureWeight component).mass output /
          (component secret).mass output := by
    simp_rw [Real.exp_log
      (div_pos ((component _).positive output) ((component secret).positive output))]
    rw [positiveProbabilityMixture_mass, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro candidate _
    ring
  simpa only [finiteRelativeEntropy, averagedLogLikelihoodRatio, Function.id_def,
    hright] using hamgm

/-- A positive order-`1+r` Renyi integrand is an expectation of the mixture likelihood ratio to
power `-r`. -/
theorem renyiIntegrand_eq_likelihoodRatio
    (likelihood reference r : ℝ) (hlikelihood : 0 < likelihood)
    (hreference : 0 < reference) :
    likelihood ^ (1 + r) * reference ^ (1 - (1 + r)) =
      likelihood * (reference / likelihood) ^ (-r) := by
  rw [Real.rpow_def_of_pos hlikelihood, Real.rpow_def_of_pos hreference,
    Real.rpow_def_of_pos (div_pos hreference hlikelihood)]
  calc
    Real.exp (Real.log likelihood * (1 + r)) *
          Real.exp (Real.log reference * (1 - (1 + r))) =
        Real.exp
          (Real.log likelihood * (1 + r) +
            Real.log reference * (1 - (1 + r))) := (Real.exp_add _ _).symm
    _ = Real.exp
        (Real.log likelihood + (Real.log reference - Real.log likelihood) * (-r)) := by
      congr 1
      ring
    _ = Real.exp (Real.log likelihood) *
        Real.exp (Real.log (reference / likelihood) * (-r)) := by
      rw [Real.log_div hreference.ne' hlikelihood.ne', Real.exp_add]
    _ = likelihood * Real.exp (Real.log (reference / likelihood) * (-r)) := by
      rw [Real.exp_log hlikelihood]

/-- Exponentiated equation (31), proved entirely for finite positive likelihood tables. -/
theorem finiteRenyiMoment_le_nonGaussianCluster
    {Secret Output : Type}
    [Fintype Secret] [Nonempty Secret] [DecidableEq Secret]
    [Fintype Output]
    (component : Secret → PositiveProbabilityTable Output)
    (mixtureWeight cluster : PositiveProbabilityTable Secret)
    (r : ℝ) (hr : 0 ≤ r) (secret : Secret) :
    finiteRenyiMoment (1 + r) (component secret).mass
        (positiveProbabilityMixture mixtureWeight component).mass ≤
      Real.exp (r * finiteRelativeEntropy cluster mixtureWeight) *
        finiteLikelihoodRatioClusterMoment cluster component r secret := by
  let reference := positiveProbabilityMixture mixtureWeight component
  have hpoint : ∀ output,
      (reference.mass output / (component secret).mass output) ^ (-r) ≤
        Real.exp (r * finiteRelativeEntropy cluster mixtureWeight) *
          Real.exp (-r * averagedLogLikelihoodRatio cluster component secret output) := by
    intro output
    have hlower := exp_neg_entropy_add_average_logLikelihood_le_mixtureRatio
      cluster mixtureWeight component secret output
    have hpow := Real.rpow_le_rpow_of_nonpos
      (Real.exp_pos _) hlower (by linarith : -r ≤ 0)
    calc
      (reference.mass output / (component secret).mass output) ^ (-r) ≤
          Real.exp
            (-finiteRelativeEntropy cluster mixtureWeight +
              averagedLogLikelihoodRatio cluster component secret output) ^ (-r) := hpow
      _ = Real.exp (r * finiteRelativeEntropy cluster mixtureWeight) *
          Real.exp (-r * averagedLogLikelihoodRatio cluster component secret output) := by
        rw [← Real.exp_mul, ← Real.exp_add]
        congr 1
        ring
  calc
    finiteRenyiMoment (1 + r) (component secret).mass reference.mass =
        ∑ output, (component secret).mass output *
          (reference.mass output / (component secret).mass output) ^ (-r) := by
      unfold finiteRenyiMoment
      apply Finset.sum_congr rfl
      intro output _
      exact renyiIntegrand_eq_likelihoodRatio _ _ r
        ((component secret).positive output) (reference.positive output)
    _ ≤ ∑ output, (component secret).mass output *
        (Real.exp (r * finiteRelativeEntropy cluster mixtureWeight) *
          Real.exp (-r * averagedLogLikelihoodRatio cluster component secret output)) := by
      apply Finset.sum_le_sum
      intro output _
      exact mul_le_mul_of_nonneg_left (hpoint output) ((component secret).nonneg output)
    _ = Real.exp (r * finiteRelativeEntropy cluster mixtureWeight) *
        finiteLikelihoodRatioClusterMoment cluster component r secret := by
      unfold finiteLikelihoodRatioClusterMoment
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro output _
      ring

/-- Equation (31) in the sketch: the logarithm of the mixture-reference Renyi moment is at most
relative entropy plus the log moment-generating term. -/
theorem log_finiteRenyiMoment_le_nonGaussianCluster
    {Secret Output : Type}
    [Fintype Secret] [Nonempty Secret] [DecidableEq Secret]
    [Fintype Output] [Nonempty Output]
    (component : Secret → PositiveProbabilityTable Output)
    (mixtureWeight cluster : PositiveProbabilityTable Secret)
    (r : ℝ) (hr : 0 ≤ r) (secret : Secret) :
    Real.log
        (finiteRenyiMoment (1 + r) (component secret).mass
          (positiveProbabilityMixture mixtureWeight component).mass) ≤
      r * finiteRelativeEntropy cluster mixtureWeight +
        Real.log (finiteLikelihoodRatioClusterMoment cluster component r secret) := by
  let reference := positiveProbabilityMixture mixtureWeight component
  have hleftPos :
      0 < finiteRenyiMoment (1 + r) (component secret).mass reference.mass := by
    unfold finiteRenyiMoment
    exact Finset.sum_pos
      (fun output _ ↦ mul_pos
        (Real.rpow_pos_of_pos ((component secret).positive output) (1 + r))
        (Real.rpow_pos_of_pos (reference.positive output) (1 - (1 + r))))
      Finset.univ_nonempty
  have hmomentPos := finiteLikelihoodRatioClusterMoment_pos cluster component r secret
  apply log_le_of_pos_of_le_exp _ _ hleftPos
  calc
    finiteRenyiMoment (1 + r) (component secret).mass reference.mass ≤
        Real.exp (r * finiteRelativeEntropy cluster mixtureWeight) *
          finiteLikelihoodRatioClusterMoment cluster component r secret :=
      finiteRenyiMoment_le_nonGaussianCluster component mixtureWeight cluster r hr secret
    _ = Real.exp
        (r * finiteRelativeEntropy cluster mixtureWeight +
          Real.log (finiteLikelihoodRatioClusterMoment cluster component r secret)) := by
      rw [Real.exp_add, Real.exp_log hmomentPos]

/-! ## Finite truncation of an original secret law -/

/-- Forget whether a sample came from the truncation set or its tail. -/
def forgetTruncationContextKernel {Output : Type} : Bool × Output → ProbComp Output :=
  fun side ↦ pure side.2

/-- Sample either the normalized good-set prior or the tail prior, run its conditional channel,
then hide the good/tail flag.  This is the finite probability law underlying equation (32). -/
def truncationMixtureJoint
    {Secret Output : Type}
    (contextSampler : ProbComp Bool)
    (prior : Bool → ProbComp Secret)
    (channel : Bool → Secret → ProbComp Output) :
    ProbComp (Secret × Output) :=
  postprocessJoint (contextualChannelJoint contextSampler prior channel)
    forgetTruncationContextKernel

/-- Revealing the good/tail flag gives the elementary truncation bound: the tail contributes at
most its mass, while the normalized good law contributes its own guessing bound. -/
theorem binaryContextTruncationGuessingBound
    {Secret Output : Type}
    [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (contextSampler : ProbComp Bool)
    (prior : Bool → ProbComp Secret)
    (channel : Bool → Secret → ProbComp Output)
    (tailMass goodBound : ℝ)
    (tail_mass : realPointMass contextSampler true = tailMass)
    (good_mass : realPointMass contextSampler false = 1 - tailMass)
    (good_guess :
      (conditionalGuessingProbability
        (conditionalChannelJoint (prior false) (channel false))).toReal ≤ goodBound) :
    (conditionalGuessingProbability
      (contextualChannelJoint contextSampler prior channel)).toReal ≤
      tailMass + (1 - tailMass) * goodBound := by
  have haverage := descriptorAveragedGuessingBound contextSampler prior channel
    (fun isTail ↦ if isTail then 1 else goodBound) (by
      intro isTail
      cases isTail with
      | false => simpa using good_guess
      | true =>
          simp only [ite_true]
          exact ENNReal.toReal_mono ENNReal.one_ne_top
            (conditionalGuessingProbability_le_one _))
  have tail_mass' : Pr[= true | contextSampler].toReal = tailMass := by
    simpa only [realPointMass] using tail_mass
  have good_mass' : Pr[= false | contextSampler].toReal = 1 - tailMass := by
    simpa only [realPointMass] using good_mass
  simpa [Finset.sum_boole, good_mass', tail_mass', add_comm] using haverage

/-- Equation (32): hiding the truncation flag cannot increase guessing probability, so the same
tail-plus-good bound applies to the original mixture law. -/
theorem truncationMixtureGuessingBound
    {Secret Output : Type}
    [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (contextSampler : ProbComp Bool)
    (prior : Bool → ProbComp Secret)
    (channel : Bool → Secret → ProbComp Output)
    (tailMass goodBound : ℝ)
    (tail_mass : realPointMass contextSampler true = tailMass)
    (good_mass : realPointMass contextSampler false = 1 - tailMass)
    (good_guess :
      (conditionalGuessingProbability
        (conditionalChannelJoint (prior false) (channel false))).toReal ≤ goodBound) :
    (conditionalGuessingProbability
      (truncationMixtureJoint contextSampler prior channel)).toReal ≤
      tailMass + (1 - tailMass) * goodBound := by
  have hforget := conditionalGuessingProbability_postprocessJoint_le
    (contextualChannelJoint contextSampler prior channel) forgetTruncationContextKernel
  have hcontextFinite :
      conditionalGuessingProbability
          (contextualChannelJoint contextSampler prior channel) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (conditionalGuessingProbability_le_one _)
  have hforgetReal :
      (conditionalGuessingProbability
        (truncationMixtureJoint contextSampler prior channel)).toReal ≤
      (conditionalGuessingProbability
        (contextualChannelJoint contextSampler prior channel)).toReal := by
    exact ENNReal.toReal_mono hcontextFinite hforget
  exact hforgetReal.trans
    (binaryContextTruncationGuessingBound contextSampler prior channel
      tailMass goodBound tail_mass good_mass good_guess)

/-- Gaussian/effective-codebook specialization of equation (32).  The `false` branch is the
normalized finite truncation set; the `true` branch is arbitrary and costs only its tail mass. -/
theorem truncatedGaussianMixtureEffectiveOverlapGuessingBound
    {Secret Output Vector : Type}
    [Fintype Secret] [Nonempty Secret] [DecidableEq Secret]
    [Fintype Output] [DecidableEq Output]
    [NormedAddCommGroup Vector] [InnerProductSpace ℝ Vector]
    (contextSampler : ProbComp Bool)
    (prior : Bool → ProbComp Secret)
    (channel : Bool → Secret → ProbComp Output)
    (component : Secret → PositiveProbabilityTable Output)
    (mixtureWeight : PositiveProbabilityTable Secret)
    (r tailMass : ℝ) (hr : 0 < r)
    (certificate : EqualCovarianceGaussianMixtureCertificate
      Secret Output Vector component mixtureWeight (1 + r))
    (tail_mass : realPointMass contextSampler true = tailMass)
    (good_mass : realPointMass contextSampler false = 1 - tailMass)
    (prior_mass : ∀ secret,
      realPointMass (prior false) secret = mixtureWeight.mass secret)
    (channel_mass : ∀ secret output,
      realPointMass (channel false secret) output = (component secret).mass output) :
    (conditionalGuessingProbability
      (truncationMixtureJoint contextSampler prior channel)).toReal ≤
      tailMass + (1 - tailMass) *
        (∑ secret, mixtureWeight.mass secret *
          certifiedSoftEffectiveOverlap r mixtureWeight
            (fun candidate ↦ certificate.difference candidate secret) secret ^ (-r)) ^
          (1 / (1 + r)) := by
  apply truncationMixtureGuessingBound contextSampler prior channel tailMass
    ((∑ secret, mixtureWeight.mass secret *
      certifiedSoftEffectiveOverlap r mixtureWeight
        (fun candidate ↦ certificate.difference candidate secret) secret ^ (-r)) ^
      (1 / (1 + r))) tail_mass good_mass
  exact conditionalGaussianMixtureEffectiveOverlapGuessingBound
    (prior false) (channel false) component mixtureWeight r hr certificate
      prior_mass channel_mass

/-! ## Quadratic product-cancellation codebook -/

/-- A common translation disappears from every pairwise codeword difference. -/
theorem commonTranslation_sub_cancel
    {Value : Type} [AddCommGroup Value] (translation left right : Value) :
    (translation + right) - (translation + left) = right - left := by
  abel

/-- Equation (33), restated at the Gaussian-cluster layer. -/
theorem quadraticGaussianClusterCodeword_sub_factor
    {R : Type} [CommRing R] (z fg left right : R) :
    quadraticCodewordRow z fg right - quadraticCodewordRow z fg left =
      (right - left) * (z + fg * (right + left)) :=
  quadraticCodewordRow_sub_factor z fg left right

/-- Squared whitened distance of the complete embedded quadratic codeword.  Every embedding
coordinate contains every row; this is the coherent row energy rather than a maximum-row
surrogate. -/
def embeddedQuadraticDifferenceEnergy
    {Embedding Row R : Type} [Fintype Embedding] [Fintype Row] [CommRing R]
    (noiseWidth : ℝ) (embedding : Embedding → R →+* ℝ)
    (z fg : Row → R) (left right : R) : ℝ :=
  (1 / noiseWidth ^ 2) *
    ∑ coordinate, ∑ row,
      |embedding coordinate
        (quadraticCodewordRow (z row) (fg row) right -
          quadraticCodewordRow (z row) (fg row) left)| ^ 2

/-- The factorized expression on the right side of equation (34). -/
def factorizedQuadraticDifferenceEnergy
    {Embedding Row R : Type} [Fintype Embedding] [Fintype Row] [CommRing R]
    (noiseWidth : ℝ) (embedding : Embedding → R →+* ℝ)
    (z fg : Row → R) (left right : R) : ℝ :=
  (1 / noiseWidth ^ 2) *
    ∑ coordinate,
      |embedding coordinate (right - left)| ^ 2 *
        ∑ row,
          |embedding coordinate (z row) +
            embedding coordinate (fg row) * embedding coordinate (right + left)| ^ 2

/-- Equation (34): after canonical embedding, the exact quadratic difference energy separates
into the secret-difference factor and the complete per-coordinate row energy. -/
theorem embeddedQuadraticDifferenceEnergy_eq_factorized
    {Embedding Row R : Type} [Fintype Embedding] [Fintype Row] [CommRing R]
    (noiseWidth : ℝ) (embedding : Embedding → R →+* ℝ)
    (z fg : Row → R) (left right : R) :
    embeddedQuadraticDifferenceEnergy noiseWidth embedding z fg left right =
      factorizedQuadraticDifferenceEnergy noiseWidth embedding z fg left right := by
  unfold embeddedQuadraticDifferenceEnergy factorizedQuadraticDifferenceEnergy
  congr 1
  apply Finset.sum_congr rfl
  intro coordinate _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro row _
  rw [quadraticCodewordRow_sub_factor, map_mul, map_sub, map_add, map_add,
    map_mul, abs_mul, mul_pow]
  rw [map_add]

end

end FormalProof4FHE.RLWE.RankOneHNFLossinessGaussianCluster
