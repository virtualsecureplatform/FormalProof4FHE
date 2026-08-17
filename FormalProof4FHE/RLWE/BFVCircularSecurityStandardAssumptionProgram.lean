/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.BFVFoldFreeCircularSecurityFramework
import FormalProof4FHE.TFHE.BlockCategoricalHashCMUXSelfCircular
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# BFV circular security: finite core of the large-modulus standard-assumption program

This file formalizes the sound finite algebra in
`sketch/bfv_circular_security_standard_assumption_program.tex`:

* the exact three-sample random-quadratic-coefficient compiler and its uniform fresh-pair map;
* the unit-target normalization-to-SIS relation, generalized to a target multiplier `P`;
* scalar-box unit differences and exact universal-hash pair collisions;
* fixed-gadget public linear combination at the auxiliary modulus;
* the exact algebraic divisibility identity behind coefficientwise modulus-down; and
* quotient--remainder uniformity for scalar and coefficient-product carriers.

The lattice implementation, interval-flooding calculation, end-to-end computational games, and
concrete RLWE/correctness parameter family remain explicit external obligations.  In particular,
this module does not assert the manuscript's final conjecture.
-/

open OracleComp
open scoped BigOperators ENNReal

namespace FormalProof4FHE.RLWE.BFVCircularSecurityStandardAssumptionProgram

noncomputable section

open FormalProof4FHE.RLWE.BFVFoldFreeCircularSecurityFramework

/-! ## Exact three-sample compiler -/

/-- One ordinary negative-sign RLWE row. -/
structure Row (R : Type) where
  mask : R
  body : R

/-- An ordinary row `b=-a*s+e`. -/
def ordinaryRow {R : Type} [Ring R] (secret error mask : R) : Row R :=
  ⟨mask, -mask * secret + error⟩

/-- Random public coefficient of the quadratic term. -/
def threeSampleCoefficient {R : Type} [Mul R] (first second : Row R) : R :=
  first.mask * second.mask

/-- Public mask produced from three ordinary rows. -/
def threeSampleMask {R : Type} [Ring R]
    (first second third : Row R) : R :=
  third.mask - first.mask * second.body - second.mask * first.body

/-- Public body produced from three ordinary rows. -/
def threeSampleBody {R : Type} [Ring R]
    (first second third : Row R) : R :=
  third.body - first.body * second.body

/-- Error left by the three-sample compiler. -/
def threeSampleError {R : Type} [Ring R]
    (firstError secondError thirdError : R) : R :=
  thirdError - firstError * secondError

/-- The manuscript's exact identity
`C=-A*s+G*s²+(e₃-e₁e₂)`. -/
theorem threeSample_identity
    {R : Type} [CommRing R]
    (secret firstError secondError thirdError firstMask secondMask thirdMask : R) :
    let first := ordinaryRow secret firstError firstMask
    let second := ordinaryRow secret secondError secondMask
    let third := ordinaryRow secret thirdError thirdMask
    threeSampleBody first second third =
      -threeSampleMask first second third * secret +
        threeSampleCoefficient first second * secret ^ 2 +
          threeSampleError firstError secondError thirdError := by
  dsimp [ordinaryRow, threeSampleBody, threeSampleMask,
    threeSampleCoefficient, threeSampleError]
  ring

/-- For fixed first and second public rows, the fresh third mask/body map is a pair of
translations. -/
def threeSampleFreshEquiv
    {R : Type} [AddCommGroup R] [Mul R]
    (firstMask secondMask firstBody secondBody : R) :
    (R × R) ≃ (R × R) where
  toFun fresh :=
    (fresh.1 - firstMask * secondBody - secondMask * firstBody,
      fresh.2 - firstBody * secondBody)
  invFun output :=
    (output.1 + firstMask * secondBody + secondMask * firstBody,
      output.2 + firstBody * secondBody)
  left_inv fresh := by
    apply Prod.ext
    · dsimp
      abel
    · simp
  right_inv output := by
    apply Prod.ext
    · dsimp
      abel
    · simp

/-- Conditioned on the first two rows, uniform fresh third mask and body give an exactly uniform
compiled mask/body pair. -/
theorem threeSampleFresh_uniform_evalDist
    {R : Type} [AddCommGroup R] [Mul R]
    [Fintype R] [DecidableEq R] [SampleableType R]
    (firstMask secondMask firstBody secondBody : R) :
    evalDist (threeSampleFreshEquiv firstMask secondMask firstBody secondBody <$>
        ($ᵗ (R × R))) =
      evalDist ($ᵗ (R × R)) :=
  evalDist_map_bijective_uniform_cross
    (α := R × R) (β := R × R)
    (threeSampleFreshEquiv firstMask secondMask firstBody secondBody)
    (threeSampleFreshEquiv firstMask secondMask firstBody secondBody).bijective

/-- The random quadratic coefficient can be retained as arbitrary side information while the
compiled mask/body pair remains exactly uniform. -/
theorem threeSampleFresh_withCoefficient_uniform_evalDist
    {R : Type} [AddCommGroup R] [Mul R]
    [Fintype R] [DecidableEq R] [SampleableType R]
    (coefficient firstMask secondMask firstBody secondBody : R) :
    evalDist ((fun fresh ↦
        (coefficient,
          threeSampleFreshEquiv firstMask secondMask firstBody secondBody fresh)) <$>
      ($ᵗ (R × R))) =
      evalDist ((fun output : R × R ↦ (coefficient, output)) <$> ($ᵗ (R × R))) := by
  have hFresh := threeSampleFresh_uniform_evalDist
    firstMask secondMask firstBody secondBody
  let attach := fun output : R × R ↦
    (pure (coefficient, output) : ProbComp (R × (R × R)))
  calc
    evalDist ((fun fresh ↦
        (coefficient,
          threeSampleFreshEquiv firstMask secondMask firstBody secondBody fresh)) <$>
      ($ᵗ (R × R))) =
      evalDist ((threeSampleFreshEquiv firstMask secondMask firstBody secondBody <$>
        ($ᵗ (R × R))) >>= attach) := by
          simp [attach, map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist (($ᵗ (R × R)) >>= attach) := by
      rw [evalDist_bind, hFresh, ← evalDist_bind]
    _ = evalDist ((fun output : R × R ↦ (coefficient, output)) <$>
        ($ᵗ (R × R))) := by
      simp [attach, map_eq_bind_pure_comp]

/-! ### Complete unit-conditioned uniform branch -/

/-- Five uniform ring coins left after conditioning the first mask to a fixed public unit. -/
@[ext]
structure FiveCoins (R : Type) where
  secondMask : R
  firstBody : R
  secondBody : R
  thirdMask : R
  thirdBody : R
  deriving Fintype, DecidableEq, Nonempty

noncomputable instance fiveCoinsSampleableType
    {R : Type} [Fintype R] [Nonempty R] : SampleableType (FiveCoins R) :=
  SampleableType.ofFintype _

/-- Output triple `(G,A,C)` of the unit-conditioned uniform compiler. -/
def conditionedUniformTriple
    {R : Type} [CommRing R] (firstMask : Rˣ) (coins : FiveCoins R) : R × R × R :=
  ((firstMask : R) * coins.secondMask,
    coins.thirdMask - (firstMask : R) * coins.secondBody -
      coins.secondMask * coins.firstBody,
    coins.thirdBody - coins.firstBody * coins.secondBody)

/-- The complete compiler is an equivalence after retaining the two unused bodies. -/
def conditionedUniformCompilerEquiv
    {R : Type} [CommRing R] (firstMask : Rˣ) :
    FiveCoins R ≃ (R × R × R) × (R × R) where
  toFun coins :=
    (conditionedUniformTriple firstMask coins,
      (coins.firstBody, coins.secondBody))
  invFun output :=
    let secondMask := ((firstMask⁻¹ : Rˣ) : R) * output.1.1
    { secondMask := secondMask
      firstBody := output.2.1
      secondBody := output.2.2
      thirdMask := output.1.2.1 + (firstMask : R) * output.2.2 +
        secondMask * output.2.1
      thirdBody := output.1.2.2 + output.2.1 * output.2.2 }
  left_inv coins := by
    apply FiveCoins.ext
    · simp [conditionedUniformTriple]
    · simp
    · simp
    · simp [conditionedUniformTriple]
      ring
    · simp [conditionedUniformTriple]
  right_inv output := by
    rcases output with ⟨⟨coefficient, mask, body⟩, ⟨firstBody, secondBody⟩⟩
    apply Prod.ext
    · apply Prod.ext
      · simp [conditionedUniformTriple]
      · apply Prod.ext
        · simp [conditionedUniformTriple]
          ring
        · simp [conditionedUniformTriple]
    · simp

/-- For every fixed unit first mask, the complete uniform three-sample compiler outputs an exactly
uniform and independent random coefficient, mask, and body. -/
theorem conditionedUniformTriple_uniform_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (firstMask : Rˣ) :
    evalDist (conditionedUniformTriple firstMask <$> ($ᵗ FiveCoins R)) =
      evalDist ($ᵗ (R × R × R)) := by
  let compiler := conditionedUniformCompilerEquiv firstMask
  have hCompiler :
      evalDist (compiler <$> ($ᵗ FiveCoins R)) =
        evalDist ($ᵗ ((R × R × R) × (R × R))) :=
    evalDist_map_bijective_uniform_cross
      (α := FiveCoins R) (β := (R × R × R) × (R × R))
      compiler compiler.bijective
  calc
    evalDist (conditionedUniformTriple firstMask <$> ($ᵗ FiveCoins R)) =
      evalDist (Prod.fst <$> (compiler <$> ($ᵗ FiveCoins R))) := by
        rw [Functor.map_map]
        rfl
    _ = evalDist (Prod.fst <$> ($ᵗ ((R × R × R) × (R × R)))) := by
      simpa only [evalDist_map] using congrArg
        (fun distribution ↦ Prod.fst <$> distribution) hCompiler
    _ = evalDist ($ᵗ (R × R × R)) :=
      evalDist_map_fst_uniformSample_prod

/-- Averaging over an arbitrary public unit sampler preserves the same uniform output law. -/
theorem conditionedUniformTriple_unitSampler_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (unitSampler : ProbComp Rˣ) :
    evalDist (unitSampler >>= fun firstMask ↦
        conditionedUniformTriple firstMask <$> ($ᵗ FiveCoins R)) =
      evalDist ($ᵗ (R × R × R)) := by
  calc
    evalDist (unitSampler >>= fun firstMask ↦
        conditionedUniformTriple firstMask <$> ($ᵗ FiveCoins R)) =
      evalDist (unitSampler >>= fun _firstMask ↦
        ($ᵗ (R × R × R))) := by
          apply evalDist_bind_congr'
          intro firstMask
          exact conditionedUniformTriple_uniform_evalDist firstMask
    _ = evalDist ($ᵗ (R × R × R)) := by
      apply evalDist_ext
      intro output
      rw [probOutput_bind_const]
      simp

/-- Complete three-row source view after publicly conditioning the first mask to be a unit. -/
abbrev UnitConditionedThreeRowView (R : Type) [Monoid R] := Rˣ × FiveCoins R

/-- Public compiler from the complete unit-conditioned source view. -/
def compileUnitConditionedView
    {R : Type} [CommRing R]
    (view : UnitConditionedThreeRowView R) : R × R × R :=
  conditionedUniformTriple view.1 view.2

/-- Canonical uniform source view with an arbitrary public unit sampler. -/
def unitConditionedUniformViewSampler
    {R : Type} [CommRing R] [Fintype R] [SampleableType R]
    (unitSampler : ProbComp Rˣ) : ProbComp (UnitConditionedThreeRowView R) := do
  let firstMask ← unitSampler
  let coins ← $ᵗ FiveCoins R
  return (firstMask, coins)

/-- Compiling the complete unit-conditioned uniform source view gives the canonical uniform
triple exactly. -/
theorem compileUnitConditionedUniformView_evalDist
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (unitSampler : ProbComp Rˣ) :
    evalDist (compileUnitConditionedView <$>
        unitConditionedUniformViewSampler unitSampler) =
      evalDist ($ᵗ (R × R × R)) := by
  rw [show compileUnitConditionedView <$>
      unitConditionedUniformViewSampler unitSampler =
        (unitSampler >>= fun firstMask ↦
          conditionedUniformTriple firstMask <$> ($ᵗ FiveCoins R)) by
    simp [unitConditionedUniformViewSampler, compileUnitConditionedView,
      map_eq_bind_pure_comp, bind_assoc]]
  exact conditionedUniformTriple_unitSampler_evalDist unitSampler

/-- Exact finite computational reduction: any bound distinguishing a real unit-conditioned
three-row source view from its uniform source view also bounds the compiled random-coefficient
quadratic triple against uniform. -/
theorem compiledTriple_tvDist_uniform_le_source
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (unitSampler : ProbComp Rˣ)
    (realSource : ProbComp (UnitConditionedThreeRowView R)) :
    tvDist (compileUnitConditionedView <$> realSource) ($ᵗ (R × R × R)) ≤
      tvDist realSource (unitConditionedUniformViewSampler unitSampler) := by
  have hUniform := compileUnitConditionedUniformView_evalDist unitSampler
  calc
    tvDist (compileUnitConditionedView <$> realSource) ($ᵗ (R × R × R)) =
      tvDist (compileUnitConditionedView <$> realSource)
        (compileUnitConditionedView <$>
          unitConditionedUniformViewSampler unitSampler) := by
            unfold tvDist
            rw [hUniform]
    _ ≤ tvDist realSource (unitConditionedUniformViewSampler unitSampler) :=
      tvDist_map_le compileUnitConditionedView _ _

/-- Concrete real source view built from one secret, three errors, a unit first mask, and two
ordinary public masks. -/
def unitConditionedRealView
    {R : Type} [CommRing R]
    (secret firstError secondError thirdError : R)
    (firstMask : Rˣ) (secondMask thirdMask : R) :
    UnitConditionedThreeRowView R :=
  (firstMask,
    { secondMask := secondMask
      firstBody := -(firstMask : R) * secret + firstError
      secondBody := -secondMask * secret + secondError
      thirdMask := thirdMask
      thirdBody := -thirdMask * secret + thirdError })

/-- The complete source-view compiler agrees exactly with the three-sample identity in the real
branch. -/
theorem compileUnitConditionedRealView
    {R : Type} [CommRing R]
    (secret firstError secondError thirdError : R)
    (firstMask : Rˣ) (secondMask thirdMask : R) :
    let view := unitConditionedRealView secret firstError secondError thirdError
      firstMask secondMask thirdMask
    (compileUnitConditionedView view).2.2 =
      -(compileUnitConditionedView view).2.1 * secret +
        (compileUnitConditionedView view).1 * secret ^ 2 +
          threeSampleError firstError secondError thirdError := by
  dsimp [unitConditionedRealView, compileUnitConditionedView,
    conditionedUniformTriple, threeSampleError]
  ring

/-- Proof-carrying interface for implementing public unit rejection from ordinary uniform-mask
RLWE samples.  Only this algorithmic conditioning layer is needed to connect the exact source
reduction above to an unconditioned standard RLWE game. -/
structure UnitRejectionReduction where
  conditionedSourceBound : ℝ
  ordinaryRLWEBound : ℝ
  rejectionFailure : ℝ
  conditioned_nonneg : 0 ≤ conditionedSourceBound
  ordinary_nonneg : 0 ≤ ordinaryRLWEBound
  rejectionFailure_nonneg : 0 ≤ rejectionFailure
  reduces : conditionedSourceBound ≤ ordinaryRLWEBound + rejectionFailure

/-- Arithmetic composition of public unit rejection with the exact three-sample compiler. -/
theorem compiledTriple_tvDist_le_ordinary_add_rejection
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (unitSampler : ProbComp Rˣ)
    (realSource : ProbComp (UnitConditionedThreeRowView R))
    (certificate : UnitRejectionReduction)
    (hSource :
      tvDist realSource (unitConditionedUniformViewSampler unitSampler) ≤
        certificate.conditionedSourceBound) :
    tvDist (compileUnitConditionedView <$> realSource) ($ᵗ (R × R × R)) ≤
      certificate.ordinaryRLWEBound + certificate.rejectionFailure := by
  exact (compiledTriple_tvDist_uniform_le_source unitSampler realSource).trans
    (hSource.trans certificate.reduces)

/-! ## Normalization-to-SIS algebra -/

/-- Uniform coefficients programmed from a Ring-SIS instance with a unit scaling target and unit
last coordinate. -/
def programmedNormalizerCoefficient
    {R : Type} [CommRing R]
    (target last : Rˣ) (coefficient : R) : R :=
  -(target : R) * coefficient * ((last⁻¹ : Rˣ) : R)

/-- Factoring a public linear combination of programmed coefficients. -/
theorem sum_programmedNormalizerCoefficient
    {R Index : Type} [CommRing R] [Fintype Index]
    (target last : Rˣ) (coefficients normalizer : Index → R) :
    (∑ index, normalizer index *
        programmedNormalizerCoefficient target last (coefficients index)) =
      -(target : R) * (∑ index, normalizer index * coefficients index) *
        ((last⁻¹ : Rˣ) : R) := by
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro index _
  simp [programmedNormalizerCoefficient]
  ring

/-- General normalization relation.  Normalizing the programmed uniform coefficients to
`multiplier * target` yields a homogeneous relation whose final coefficient is `multiplier`.
For a unit target (`multiplier=1`) this is the short `(z,1)` Ring-SIS relation.  For the proposed
nonunit target it is `(z,P)`, so the final coefficient is deliberately large. -/
theorem normalization_yields_relation
    {R Index : Type} [CommRing R] [Fintype Index]
    (target last : Rˣ) (multiplier : R)
    (coefficients normalizer : Index → R)
    (hNormalize :
      (∑ index, normalizer index *
          programmedNormalizerCoefficient target last (coefficients index)) =
        multiplier * (target : R)) :
    (∑ index, normalizer index * coefficients index) + multiplier * (last : R) = 0 := by
  let combined := ∑ index, normalizer index * coefficients index
  have hFactored :
      -(target : R) * combined * ((last⁻¹ : Rˣ) : R) =
        multiplier * (target : R) := by
    rw [← sum_programmedNormalizerCoefficient target last coefficients normalizer]
    exact hNormalize
  have hCancelTarget :
      -combined * ((last⁻¹ : Rˣ) : R) = multiplier := by
    apply target.isUnit.mul_left_cancel
    change (target : R) * (-combined * ((last⁻¹ : Rˣ) : R)) =
      (target : R) * multiplier
    calc
      (target : R) * (-combined * ((last⁻¹ : Rˣ) : R)) =
          -(target : R) * combined * ((last⁻¹ : Rˣ) : R) := by ring
      _ = multiplier * (target : R) := hFactored
      _ = (target : R) * multiplier := mul_comm _ _
  have hMultiplyLast := congrArg (fun value : R ↦ value * (last : R)) hCancelTarget
  change combined + multiplier * (last : R) = 0
  have hNegCombined : -combined = multiplier * (last : R) := by
    calc
      -combined =
          (-combined * ((last⁻¹ : Rˣ) : R)) * (last : R) := by simp
      _ = multiplier * (last : R) := hMultiplyLast
  rw [← hNegCombined]
  exact add_neg_cancel combined

/-- Unit-target specialization giving the exact `(normalizer,1)` homogeneous relation. -/
theorem unitNormalization_yields_relation
    {R Index : Type} [CommRing R] [Fintype Index]
    (target last : Rˣ) (coefficients normalizer : Index → R)
    (hNormalize :
      (∑ index, normalizer index *
          programmedNormalizerCoefficient target last (coefficients index)) =
        (target : R)) :
    (∑ index, normalizer index * coefficients index) + (last : R) = 0 := by
  simpa using normalization_yields_relation target last (1 : R)
    coefficients normalizer (by simpa using hNormalize)

/-! ## Universal scalar-box hashing -/

/-- Encode one scalar box point in an algebra over `ZMod modulus`. -/
def scalarBoxSource
    {R : Type} (modulus width dimension : ℕ)
    [CommRing R] [Algebra (ZMod modulus) R]
    (point : Fin dimension → Fin width) : Fin dimension → R :=
  fun index ↦ algebraMap (ZMod modulus) R (point index).val

/-- Two different box points have a coordinate whose scalar difference is a unit whenever the box
width is below the least prime factor of the modulus.  The manuscript's `2W < minFac(M)` premise
is stronger than the `W < minFac(M)` premise used here. -/
theorem exists_scalarBoxSource_sub_isUnit
    {R : Type} (modulus width dimension : ℕ)
    [CommRing R] [Algebra (ZMod modulus) R]
    (hWidth : width < modulus.minFac)
    {left right : Fin dimension → Fin width} (hDifferent : left ≠ right) :
    ∃ selected : Fin dimension,
      IsUnit (scalarBoxSource (R := R) modulus width dimension left selected -
        scalarBoxSource (R := R) modulus width dimension right selected) := by
  have hExists : ∃ selected, left selected ≠ right selected := by
    by_contra hNo
    apply hDifferent
    funext selected
    exact not_ne_iff.mp (not_exists.mp hNo selected)
  obtain ⟨selected, hCoordinate⟩ := hExists
  refine ⟨selected, ?_⟩
  by_cases hOrder : (left selected).val < (right selected).val
  · let difference := (right selected).val - (left selected).val
    have hDifferencePos : difference ≠ 0 := by
      dsimp [difference]
      omega
    have hDifferenceLt : difference < modulus.minFac := by
      dsimp [difference]
      omega
    have hCoprime : difference.Coprime modulus :=
      (Nat.coprime_of_lt_minFac hDifferencePos hDifferenceLt).symm
    have hUnitZMod : IsUnit (difference : ZMod modulus) :=
      (ZMod.isUnit_iff_coprime difference modulus).2 hCoprime
    have hDifferenceIdentity :
        ((left selected).val : ZMod modulus) - (right selected).val =
          -(difference : ZMod modulus) := by
      calc
        ((left selected).val : ZMod modulus) - (right selected).val =
            -(((right selected).val : ZMod modulus) - (left selected).val) := by ring
        _ = -(difference : ZMod modulus) := by
          rw [Nat.cast_sub hOrder.le]
    have hMapped := hUnitZMod.neg.map (algebraMap (ZMod modulus) R)
    change IsUnit
      (algebraMap (ZMod modulus) R ((left selected).val : ZMod modulus) -
        algebraMap (ZMod modulus) R ((right selected).val : ZMod modulus))
    rw [← map_sub, hDifferenceIdentity]
    exact hMapped
  · have hReverse : (right selected).val < (left selected).val := by
      omega
    let difference := (left selected).val - (right selected).val
    have hDifferencePos : difference ≠ 0 := by
      dsimp [difference]
      omega
    have hDifferenceLt : difference < modulus.minFac := by
      dsimp [difference]
      omega
    have hCoprime : difference.Coprime modulus :=
      (Nat.coprime_of_lt_minFac hDifferencePos hDifferenceLt).symm
    have hUnitZMod : IsUnit (difference : ZMod modulus) :=
      (ZMod.isUnit_iff_coprime difference modulus).2 hCoprime
    have hMapped := hUnitZMod.map (algebraMap (ZMod modulus) R)
    change IsUnit
      (algebraMap (ZMod modulus) R ((left selected).val : ZMod modulus) -
        algebraMap (ZMod modulus) R ((right selected).val : ZMod modulus))
    rw [← map_sub, show
      ((left selected).val : ZMod modulus) - (right selected).val =
        (difference : ZMod modulus) by
          rw [Nat.cast_sub hReverse.le]]
    exact hMapped

/-- Scalar-box public hash. -/
def scalarBoxHash
    {R : Type} [CommRing R]
    {dimension width : ℕ}
    (coefficients : Fin dimension → R)
    (point : Fin dimension → Fin width) : R :=
  ∑ index, (point index).val * coefficients index

/-- The difference of two fixed scalar-box hashes as an additive map of the public coefficients. -/
def scalarBoxDifferenceAddHom
    {R : Type} [CommRing R]
    {dimension width : ℕ}
    (left right : Fin dimension → Fin width) :
    (Fin dimension → R) →+ R where
  toFun coefficients :=
    ∑ index, (((left index).val : R) * coefficients index -
      ((right index).val : R) * coefficients index)
  map_zero' := by simp
  map_add' first second := by
    simp [mul_add, Finset.sum_add_distrib]
    ring

/-- The scalar-box difference map is surjective once one scalar difference is a unit. -/
theorem scalarBoxDifferenceAddHom_surjective_of_isUnit
    {R : Type} [CommRing R]
    {dimension width : ℕ}
    (left right : Fin dimension → Fin width) (selected : Fin dimension)
    (hUnit : IsUnit (((left selected).val : R) - (right selected).val)) :
    Function.Surjective (scalarBoxDifferenceAddHom (R := R) left right) := by
  intro output
  let unit : Rˣ := hUnit.unit
  let coefficients : Fin dimension → R := fun index ↦
    if index = selected then ((unit⁻¹ : Rˣ) : R) * output else 0
  refine ⟨coefficients, ?_⟩
  change (∑ index, (((left index).val : R) * coefficients index -
    ((right index).val : R) * coefficients index)) = output
  rw [Finset.sum_eq_single selected]
  · dsimp [coefficients]
    rw [if_pos rfl]
    have hUnitSpec : (unit : R) =
        ((left selected).val : R) - (right selected).val := hUnit.unit_spec
    calc
      ((left selected).val : R) * (((unit⁻¹ : Rˣ) : R) * output) -
          ((right selected).val : R) * (((unit⁻¹ : Rˣ) : R) * output) =
        (((left selected).val : R) - (right selected).val) *
          (((unit⁻¹ : Rˣ) : R) * output) := by ring
      _ = (unit : R) * (((unit⁻¹ : Rˣ) : R) * output) := by rw [hUnitSpec]
      _ = output := by rw [← mul_assoc]; simp
  · intro index _ hIndex
    simp [coefficients, hIndex]
  · simp

/-- Exact universality of the scalar-box hash from one unit coordinate difference. -/
theorem scalarBoxHash_pairCollision_probability_of_isUnit
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    {dimension width : ℕ}
    (left right : Fin dimension → Fin width) (selected : Fin dimension)
    (hUnit : IsUnit (((left selected).val : R) - (right selected).val)) :
    Pr[(fun coefficients : Fin dimension → R ↦
        scalarBoxHash coefficients left = scalarBoxHash coefficients right) |
      ($ᵗ (Fin dimension → R))] =
      (Fintype.card R : ℝ≥0∞)⁻¹ := by
  have hUniform :
      evalDist (scalarBoxDifferenceAddHom (R := R) left right <$>
          ($ᵗ (Fin dimension → R))) = evalDist ($ᵗ R) :=
    evalDist_map_surjective_addHom_uniform
      (scalarBoxDifferenceAddHom (R := R) left right)
      (scalarBoxDifferenceAddHom_surjective_of_isUnit left right selected hUnit)
  calc
    Pr[(fun coefficients : Fin dimension → R ↦
        scalarBoxHash coefficients left = scalarBoxHash coefficients right) |
      ($ᵗ (Fin dimension → R))] =
      Pr[= (0 : R) | scalarBoxDifferenceAddHom (R := R) left right <$>
        ($ᵗ (Fin dimension → R))] := by
          rw [probOutput_map]
          apply probEvent_congr'
          · intro coefficients _
            change (∑ index, ((left index).val : R) * coefficients index) =
                (∑ index, ((right index).val : R) * coefficients index) ↔
              (∑ index, (((left index).val : R) * coefficients index -
                ((right index).val : R) * coefficients index)) = 0
            rw [Finset.sum_sub_distrib]
            exact sub_eq_zero.symm
          · rfl
    _ = Pr[= (0 : R) | ($ᵗ R)] := evalDist_ext_iff.mp hUniform 0
    _ = (Fintype.card R : ℝ≥0∞)⁻¹ := probOutput_uniformSample _ _

/-- Manuscript form of scalar-box universality. -/
theorem scalarBoxHash_pairCollision_probability
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (modulus dimension width : ℕ) [Algebra (ZMod modulus) R]
    (hWidth : width < modulus.minFac)
    (left right : Fin dimension → Fin width) (hDifferent : left ≠ right) :
    Pr[(fun coefficients : Fin dimension → R ↦
        scalarBoxHash coefficients left = scalarBoxHash coefficients right) |
      ($ᵗ (Fin dimension → R))] =
      (Fintype.card R : ℝ≥0∞)⁻¹ := by
  obtain ⟨selected, hUnit⟩ := exists_scalarBoxSource_sub_isUnit
    (R := R) modulus width dimension hWidth hDifferent
  have hUnit' :
      IsUnit (((left selected).val : R) - (right selected).val) := by
    simpa [scalarBoxSource] using hUnit
  exact scalarBoxHash_pairCollision_probability_of_isUnit
    left right selected hUnit'

/-- Cardinal two-universality form of the scalar-box collision theorem. -/
theorem scalarBoxHash_isTwoUniversal
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (modulus dimension width : ℕ) [Algebra (ZMod modulus) R]
    (hWidth : width < modulus.minFac) :
    FormalProof4FHE.LeftoverHash.IsTwoUniversal
      (Fin dimension → R) (Fin dimension → Fin width) R scalarBoxHash := by
  classical
  intro left right hDifferent
  obtain ⟨selected, hUnitSource⟩ := exists_scalarBoxSource_sub_isUnit
    (R := R) modulus width dimension hWidth hDifferent
  have hUnit :
      IsUnit (((left selected).val : R) - (right selected).val) := by
    simpa [scalarBoxSource] using hUnitSource
  let transform := scalarBoxDifferenceAddHom (R := R) left right
  have hSurjective : Function.Surjective transform :=
    scalarBoxDifferenceAddHom_surjective_of_isUnit left right selected hUnit
  have hFilter :
      (Finset.univ.filter fun coefficients : Fin dimension → R ↦
          scalarBoxHash coefficients left = scalarBoxHash coefficients right) =
        Finset.univ.filter fun coefficients : Fin dimension → R ↦
          transform coefficients = 0 := by
    ext coefficients
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change scalarBoxHash coefficients left = scalarBoxHash coefficients right ↔
      (∑ index, (((left index).val : R) * coefficients index -
        ((right index).val : R) * coefficients index)) = 0
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.symm
  rw [hFilter]
  exact le_of_eq
    (FormalProof4FHE.FiniteSurjectiveFiber.zeroFiberCard_mul_card_eq_card_of_surjective
      transform hSurjective)

/-! ### Conditional-average form of leftover hashing -/

/-- Joint public-seed distance is exactly the average, over public seeds, of the conditional
image distance. -/
theorem tvDist_hashed_eq_average
    {Seed Input Output : Type}
    [Fintype Seed] [Nonempty Seed] [SampleableType Seed]
    [Fintype Input] [Nonempty Input] [SampleableType Input]
    [Fintype Output] [Nonempty Output] [DecidableEq Output] [SampleableType Output]
    (hash : Seed → Input → Output) :
    tvDist (FormalProof4FHE.LeftoverHash.hashed hash)
        (FormalProof4FHE.LeftoverHash.ideal (Seed := Seed) (Output := Output)) =
      (∑ seed, tvDist (hash seed <$> ($ᵗ Input)) ($ᵗ Output)) /
        Fintype.card Seed := by
  classical
  let seedCard : ℝ := Fintype.card Seed
  have hSeedCard : 0 < seedCard := by
    dsimp [seedCard]
    exact_mod_cast Fintype.card_pos
  have hHashed (seed : Seed) (output : Output) :
      Pr[= (seed, output) | FormalProof4FHE.LeftoverHash.hashed hash].toReal =
        seedCard⁻¹ * Pr[= output | hash seed <$> ($ᵗ Input)].toReal := by
    rw [FormalProof4FHE.LeftoverHash.probOutput_hashed,
      FormalProof4FHE.LeftoverHash.probOutput_map_uniform_eq_fiberCard]
    simp only [ENNReal.toReal_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
    dsimp [seedCard]
    ring
  have hIdeal (seed : Seed) (output : Output) :
      Pr[= (seed, output) |
          FormalProof4FHE.LeftoverHash.ideal (Seed := Seed) (Output := Output)].toReal =
        seedCard⁻¹ * Pr[= output | ($ᵗ Output)].toReal := by
    simp [FormalProof4FHE.LeftoverHash.ideal, seedCard,
      probOutput_uniformSample, Fintype.card_prod,
      ENNReal.toReal_inv, ENNReal.toReal_natCast]
    field_simp
  rw [FormalProof4FHE.LeftoverHash.tvDist_eq_half_sum_abs,
    Fintype.sum_prod_type]
  simp_rw [hHashed, hIdeal,
    FormalProof4FHE.LeftoverHash.tvDist_eq_half_sum_abs]
  have hSeedInverse : 0 ≤ seedCard⁻¹ := by positivity
  simp_rw [← mul_sub, abs_mul, abs_of_nonneg hSeedInverse]
  rw [Finset.mul_sum, Finset.sum_div]
  dsimp [seedCard]
  apply Finset.sum_congr rfl
  intro seed _
  rw [← Finset.mul_sum]
  ring

/-- Two-universality gives the manuscript's average conditional leftover-hash estimate. -/
theorem average_hash_tvDist_le
    {Seed Input Output : Type}
    [Fintype Seed] [Nonempty Seed] [SampleableType Seed]
    [Fintype Input] [Nonempty Input] [SampleableType Input]
    [Fintype Output] [Nonempty Output] [DecidableEq Output] [SampleableType Output]
    (hash : Seed → Input → Output)
    (hUniversal : FormalProof4FHE.LeftoverHash.IsTwoUniversal
      Seed Input Output hash) :
    (∑ seed, tvDist (hash seed <$> ($ᵗ Input)) ($ᵗ Output)) /
        Fintype.card Seed ≤
      Real.sqrt (Fintype.card Output / Fintype.card Input) / 2 := by
  rw [← tvDist_hashed_eq_average hash]
  exact FormalProof4FHE.LeftoverHash.leftover_hash_lemma hash hUniversal

/-- Scalar-box specialization of the exact average leftover-hash bound. -/
theorem scalarBoxHash_average_tvDist_le
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (modulus dimension width : ℕ) [NeZero width] [Algebra (ZMod modulus) R]
    (hWidth : width < modulus.minFac) :
    (∑ coefficients : Fin dimension → R,
        tvDist (scalarBoxHash coefficients <$> ($ᵗ (Fin dimension → Fin width)))
          ($ᵗ R)) /
        Fintype.card (Fin dimension → R) ≤
      Real.sqrt ((Fintype.card R : ℝ) / width ^ dimension) / 2 := by
  simpa using average_hash_tvDist_le
    (scalarBoxHash (R := R) (dimension := dimension) (width := width))
    (scalarBoxHash_isTwoUniversal modulus dimension width hWidth)

/-! ### Fixed-target missing-image interface -/

/-- A target is absent from one deterministic hash image. -/
def targetMissing
    {Seed Input Output : Type}
    (hash : Seed → Input → Output) (target : Output) (seed : Seed) : Prop :=
  ∀ input, hash seed input ≠ target

/-- Finite set of seeds whose image misses the target. -/
noncomputable def missingSeeds
    {Seed Input Output : Type} [Fintype Seed]
    (hash : Seed → Input → Output) (target : Output) : Finset Seed := by
  classical
  exact Finset.univ.filter (targetMissing hash target)

/-- If a fixed target is absent from a deterministic image of a uniform input, that image is at
least one uniform point mass away from uniform in total variation. -/
theorem inv_card_le_tvDist_of_targetMissing
    {Input Output : Type}
    [Fintype Input] [SampleableType Input]
    [Fintype Output] [DecidableEq Output] [Nonempty Output] [SampleableType Output]
    (transform : Input → Output) (target : Output)
    (hMissing : ∀ input, transform input ≠ target) :
    (Fintype.card Output : ℝ)⁻¹ ≤
      tvDist (transform <$> ($ᵗ Input)) ($ᵗ Output) := by
  let indicator : Output → Bool := fun output ↦ decide (output = target)
  have hMappedZero :
      Pr[= true | indicator <$> (transform <$> ($ᵗ Input))] = 0 := by
    rw [show indicator <$> (transform <$> ($ᵗ Input)) =
        (indicator ∘ transform) <$> ($ᵗ Input) by
          simp [Functor.map_map, Function.comp_def]]
    rw [probOutput_map_eq_sum_fintype_ite]
    simp [indicator, hMissing]
  have hUniformTrue :
      (Pr[= true | indicator <$> ($ᵗ Output)]).toReal =
        (Fintype.card Output : ℝ)⁻¹ := by
    rw [probOutput_map]
    simp only [indicator, decide_eq_true_eq, probEvent_eq_eq_probOutput,
      probOutput_uniformSample, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  have hBoolean := abs_probOutput_toReal_sub_le_tvDist
    (indicator <$> (transform <$> ($ᵗ Input))) (indicator <$> ($ᵗ Output))
  have hDataProcessing := tvDist_map_le indicator
    (transform <$> ($ᵗ Input)) ($ᵗ Output)
  rw [hMappedZero, ENNReal.toReal_zero, zero_sub, abs_neg, hUniformTrue] at hBoolean
  have hInverseNonneg : 0 ≤ (Fintype.card Output : ℝ)⁻¹ := by positivity
  have hBoolean' :
      (Fintype.card Output : ℝ)⁻¹ ≤
        tvDist (indicator <$> (transform <$> ($ᵗ Input)))
          (indicator <$> ($ᵗ Output)) := by
    simpa [abs_of_nonneg hInverseNonneg] using hBoolean
  exact hBoolean'.trans hDataProcessing

/-- Finite Markov form of the manuscript's missing-target argument.  It turns any average
conditional distance estimate into a bound on the fraction of seeds whose image misses a fixed
target. -/
theorem missingTarget_fraction_le_card_mul_average
    {Seed Input Output : Type}
    [Fintype Seed] [DecidableEq Seed] [Nonempty Seed]
    [Fintype Input] [SampleableType Input]
    [Fintype Output] [DecidableEq Output] [Nonempty Output] [SampleableType Output]
    (hash : Seed → Input → Output) (target : Output) :
    (((missingSeeds hash target).card : ℝ) /
        Fintype.card Seed) ≤
      (Fintype.card Output : ℝ) *
        ((∑ seed, tvDist (hash seed <$> ($ᵗ Input)) ($ᵗ Output)) /
          Fintype.card Seed) := by
  classical
  let badSeeds := missingSeeds hash target
  let outputCard : ℝ := Fintype.card Output
  let seedCard : ℝ := Fintype.card Seed
  have hOutputCard : 0 < outputCard := by
    dsimp [outputCard]
    exact_mod_cast Fintype.card_pos
  have hSeedCard : 0 < seedCard := by
    dsimp [seedCard]
    exact_mod_cast Fintype.card_pos
  have hBadLower :
      (badSeeds.card : ℝ) * outputCard⁻¹ ≤
        ∑ seed ∈ badSeeds,
          tvDist (hash seed <$> ($ᵗ Input)) ($ᵗ Output) := by
    calc
      (badSeeds.card : ℝ) * outputCard⁻¹ =
          ∑ _seed ∈ badSeeds, outputCard⁻¹ := by simp
      _ ≤ ∑ seed ∈ badSeeds,
          tvDist (hash seed <$> ($ᵗ Input)) ($ᵗ Output) := by
        apply Finset.sum_le_sum
        intro seed hSeed
        have hSeedMissing : targetMissing hash target seed := by
          simpa [badSeeds, missingSeeds] using hSeed
        exact inv_card_le_tvDist_of_targetMissing (hash seed) target
          (fun input ↦ hSeedMissing input)
  have hBadToAll :
      (∑ seed ∈ badSeeds,
          tvDist (hash seed <$> ($ᵗ Input)) ($ᵗ Output)) ≤
        ∑ seed, tvDist (hash seed <$> ($ᵗ Input)) ($ᵗ Output) := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro seed _ _
    exact tvDist_nonneg _ _
  change (badSeeds.card : ℝ) / seedCard ≤
    outputCard * ((∑ seed, tvDist (hash seed <$> ($ᵗ Input)) ($ᵗ Output)) / seedCard)
  have hCore := hBadLower.trans hBadToAll
  have hDiv :
      (badSeeds.card : ℝ) / outputCard ≤
        ∑ seed, tvDist (hash seed <$> ($ᵗ Input)) ($ᵗ Output) := by
    simpa [div_eq_mul_inv] using hCore
  have hMul :
      (badSeeds.card : ℝ) ≤
        (∑ seed, tvDist (hash seed <$> ($ᵗ Input)) ($ᵗ Output)) * outputCard :=
    (div_le_iff₀ hOutputCard).mp hDiv
  apply (div_le_iff₀ hSeedCard).2
  calc
    (badSeeds.card : ℝ) ≤
        outputCard * (∑ seed, tvDist (hash seed <$> ($ᵗ Input)) ($ᵗ Output)) := by
      simpa [mul_comm] using hMul
    _ = outputCard *
        ((∑ seed, tvDist (hash seed <$> ($ᵗ Input)) ($ᵗ Output)) / seedCard) *
          seedCard := by
      field_simp

/-- Convenience form after supplying a leftover-hash average-distance estimate. -/
theorem missingTarget_fraction_le
    {Seed Input Output : Type}
    [Fintype Seed] [DecidableEq Seed] [Nonempty Seed]
    [Fintype Input] [SampleableType Input]
    [Fintype Output] [DecidableEq Output] [Nonempty Output] [SampleableType Output]
    (hash : Seed → Input → Output) (target : Output) (averageBound : ℝ)
    (hAverage :
      (∑ seed, tvDist (hash seed <$> ($ᵗ Input)) ($ᵗ Output)) /
          Fintype.card Seed ≤ averageBound) :
    (((missingSeeds hash target).card : ℝ) /
        Fintype.card Seed) ≤
      (Fintype.card Output : ℝ) * averageBound := by
  exact (missingTarget_fraction_le_card_mul_average hash target).trans
    (mul_le_mul_of_nonneg_left hAverage (by positivity))

/-- Seeds missing at least one target in a finite target family. -/
noncomputable def someTargetMissingSeeds
    {Seed Input Output : Type} [Fintype Seed]
    (hash : Seed → Input → Output) (targets : Finset Output) : Finset Seed := by
  classical
  exact Finset.univ.filter fun seed ↦
    ∃ target ∈ targets, targetMissing hash target seed

/-- Finite weighted union bound used for simultaneous target coverage. -/
theorem finiteWeightedUnionBound
    {Index Context : Type} [Fintype Context] [DecidableEq Context] [DecidableEq Index]
    (indices : Finset Index) (event : Index → Context → Prop)
    [∀ index context, Decidable (event index context)]
    (mass : Context → ℝ) (hMass : ∀ context, 0 ≤ mass context) :
    (∑ context ∈ Finset.univ.filter
        (fun context ↦ ∃ index ∈ indices, event index context), mass context) ≤
      ∑ index ∈ indices,
        ∑ context ∈ Finset.univ.filter (event index), mass context := by
  classical
  calc
    (∑ context ∈ Finset.univ.filter
        (fun context ↦ ∃ index ∈ indices, event index context), mass context) =
      ∑ context, if ∃ index ∈ indices, event index context then mass context else 0 := by
        rw [← Finset.sum_filter]
    _ ≤ ∑ context, ∑ index ∈ indices,
        if event index context then mass context else 0 := by
      apply Finset.sum_le_sum
      intro context _
      by_cases hUnion : ∃ index ∈ indices, event index context
      · simp only [if_pos hUnion]
        obtain ⟨index, hIndex, hEvent⟩ := hUnion
        have hSingle :
            (if event index context then mass context else 0) ≤
              ∑ other ∈ indices,
                if event other context then mass context else 0 := by
          apply Finset.single_le_sum
            (s := indices)
            (f := fun other ↦ if event other context then mass context else 0)
          · intro other _
            by_cases hOther : event other context
            · simp [hOther, hMass context]
            · simp [hOther]
          · exact hIndex
        simpa [hEvent] using hSingle
      · simp only [if_neg hUnion]
        exact Finset.sum_nonneg fun index _ ↦ by
          by_cases hIndex : event index context
          · simp [hIndex, hMass context]
          · simp [hIndex]
    _ = ∑ index ∈ indices,
        ∑ context, if event index context then mass context else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ index ∈ indices,
        ∑ context ∈ Finset.univ.filter (event index), mass context := by
      apply Finset.sum_congr rfl
      intro index _
      rw [← Finset.sum_filter]

/-- Union-bound form for simultaneously covering a finite target family. -/
theorem simultaneousMissingTargets_fraction_le
    {Seed Input Output : Type}
    [Fintype Seed] [DecidableEq Seed] [Nonempty Seed]
    [Fintype Input] [SampleableType Input]
    [Fintype Output] [DecidableEq Output] [Nonempty Output] [SampleableType Output]
    (hash : Seed → Input → Output) (targets : Finset Output) (averageBound : ℝ)
    (hAverage :
      (∑ seed, tvDist (hash seed <$> ($ᵗ Input)) ($ᵗ Output)) /
          Fintype.card Seed ≤ averageBound) :
    (((someTargetMissingSeeds hash targets).card : ℝ) /
        Fintype.card Seed) ≤
      targets.card * ((Fintype.card Output : ℝ) * averageBound) := by
  classical
  let seedCard : ℝ := Fintype.card Seed
  have hSeedCard : 0 < seedCard := by
    dsimp [seedCard]
    exact_mod_cast Fintype.card_pos
  have hUnion :=
    finiteWeightedUnionBound
      targets (fun target seed ↦ targetMissing hash target seed)
      (fun _seed : Seed ↦ seedCard⁻¹) (fun _seed ↦ by positivity)
  have hIndividual (target : Output) :
      (((missingSeeds hash target).card : ℝ) / Fintype.card Seed) ≤
        (Fintype.card Output : ℝ) * averageBound :=
    missingTarget_fraction_le hash target averageBound hAverage
  calc
    (((someTargetMissingSeeds hash targets).card : ℝ) /
        Fintype.card Seed) =
      ∑ seed ∈ Finset.univ.filter
          (fun seed ↦ ∃ target ∈ targets, targetMissing hash target seed),
        seedCard⁻¹ := by
          rw [Finset.sum_const]
          simp [someTargetMissingSeeds, seedCard, div_eq_mul_inv]
    _ ≤ ∑ target ∈ targets,
        ∑ seed ∈ Finset.univ.filter (targetMissing hash target), seedCard⁻¹ := hUnion
    _ = ∑ target ∈ targets,
        (((missingSeeds hash target).card : ℝ) / Fintype.card Seed) := by
      apply Finset.sum_congr rfl
      intro target _
      rw [Finset.sum_const]
      simp [missingSeeds, seedCard, div_eq_mul_inv]
    _ ≤ ∑ _target ∈ targets,
        ((Fintype.card Output : ℝ) * averageBound) := by
      apply Finset.sum_le_sum
      intro target _
      exact hIndividual target
    _ = targets.card * ((Fintype.card Output : ℝ) * averageBound) := by simp

/-- Simultaneous missing-target bound for the concrete scalar-box family. -/
theorem scalarBoxHash_simultaneousMissing_fraction_le
    {R : Type} [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (modulus dimension width : ℕ) [NeZero width] [Algebra (ZMod modulus) R]
    (hWidth : width < modulus.minFac) (targets : Finset R) :
    (((someTargetMissingSeeds
        (scalarBoxHash (R := R) (dimension := dimension) (width := width))
        targets).card : ℝ) /
        Fintype.card (Fin dimension → R)) ≤
      targets.card * ((Fintype.card R : ℝ) *
        (Real.sqrt ((Fintype.card R : ℝ) / width ^ dimension) / 2)) := by
  exact simultaneousMissingTargets_fraction_le
    (scalarBoxHash (R := R) (dimension := dimension) (width := width))
    targets (Real.sqrt ((Fintype.card R : ℝ) / width ^ dimension) / 2)
    (scalarBoxHash_average_tvDist_le modulus dimension width hWidth)

/-! ## Proof-carrying approximate-CVP interface -/

/-- Euclidean norm of an integer coefficient vector. -/
def integerL2Norm {dimension : ℕ} (vector : Fin dimension → ℤ) : ℝ :=
  Real.sqrt (∑ index, (vector index : ℝ) ^ 2)

/-- Complete finite interface needed from the HNF/SNF and approximate-CVP implementation.  The
certificate explicitly distinguishes the exact coset/kernel obligations from the approximation
inequalities; it does not postulate that LLL/Babai constructs such a certificate. -/
structure ApproximateCVPPreimageCertificate
    (dimension : ℕ) (Target : Type) [AddCommGroup Target] where
  publicMap : (Fin dimension → ℤ) →+ Target
  target : Target
  baseSolution : Fin dimension → ℤ
  latticeCorrection : Fin dimension → ℤ
  boxWitness : Fin dimension → ℤ
  approximationFactor : ℝ
  distanceToLattice : ℝ
  boxWidth : ℝ
  baseSolution_valid : publicMap baseSolution = target
  latticeCorrection_mem_kernel : publicMap latticeCorrection = 0
  boxWitness_valid : publicMap boxWitness = target
  approximationFactor_nonneg : 0 ≤ approximationFactor
  output_norm_le_approximation :
    integerL2Norm (baseSolution - latticeCorrection) ≤
      approximationFactor * distanceToLattice
  distance_le_boxWitness : distanceToLattice ≤ integerL2Norm boxWitness
  boxWitness_norm_le :
    integerL2Norm boxWitness ≤ boxWidth * Real.sqrt dimension

/-- The approximate-CVP interface returns an exact modular preimage. -/
theorem approximateCVP_output_valid
    {dimension : ℕ} {Target : Type} [AddCommGroup Target]
    (certificate : ApproximateCVPPreimageCertificate dimension Target) :
    certificate.publicMap
        (certificate.baseSolution - certificate.latticeCorrection) =
      certificate.target := by
  rw [map_sub, certificate.baseSolution_valid,
    certificate.latticeCorrection_mem_kernel, sub_zero]

/-- The manuscript's bound `‖z‖₂ ≤ rho_m W sqrt(m)` follows exactly from the certified CVP
interface. -/
theorem approximateCVP_output_norm_le
    {dimension : ℕ} {Target : Type} [AddCommGroup Target]
    (certificate : ApproximateCVPPreimageCertificate dimension Target) :
    integerL2Norm
        (certificate.baseSolution - certificate.latticeCorrection) ≤
      certificate.approximationFactor * certificate.boxWidth *
        Real.sqrt dimension := by
  calc
    integerL2Norm
        (certificate.baseSolution - certificate.latticeCorrection) ≤
      certificate.approximationFactor * certificate.distanceToLattice :=
        certificate.output_norm_le_approximation
    _ ≤ certificate.approximationFactor * integerL2Norm certificate.boxWitness :=
      mul_le_mul_of_nonneg_left certificate.distance_le_boxWitness
        certificate.approximationFactor_nonneg
    _ ≤ certificate.approximationFactor *
        (certificate.boxWidth * Real.sqrt dimension) :=
      mul_le_mul_of_nonneg_left certificate.boxWitness_norm_le
        certificate.approximationFactor_nonneg
    _ = certificate.approximationFactor * certificate.boxWidth *
        Real.sqrt dimension := by ring

/-! ## Fixed-gadget linear combination -/

/-- Public scalar linear combination. -/
def linearCombination
    {R Index : Type} [CommRing R] [Fintype Index]
    (coefficients values : Index → R) : R :=
  ∑ index, coefficients index * values index

/-- Combining random-coefficient quadratic rows with one independent zero row produces the
prescribed fixed quadratic coefficient exactly. -/
theorem fixedGadgetCombination
    {R Index : Type} [CommRing R] [Fintype Index]
    (secret multiplier gadget zeroMask zeroBody zeroError : R)
    (normalizer masks bodies quadraticCoefficients errors : Index → R)
    (hRows : ∀ index,
      bodies index + masks index * secret =
        quadraticCoefficients index * secret ^ 2 + errors index)
    (hTarget :
      linearCombination normalizer quadraticCoefficients = multiplier * gadget)
    (hZero : zeroBody + zeroMask * secret = zeroError) :
    (zeroBody + linearCombination normalizer bodies) +
        (zeroMask + linearCombination normalizer masks) * secret =
      multiplier * gadget * secret ^ 2 +
        (zeroError + linearCombination normalizer errors) := by
  have hAdd (left right : Index → R) :
      linearCombination normalizer (fun index ↦ left index + right index) =
        linearCombination normalizer left + linearCombination normalizer right := by
    simp [linearCombination, mul_add, Finset.sum_add_distrib]
  have hScale (values : Index → R) (scale : R) :
      linearCombination normalizer (fun index ↦ values index * scale) =
        linearCombination normalizer values * scale := by
    simp [linearCombination, Finset.sum_mul, mul_assoc]
  have hRowsCombined :
      linearCombination normalizer
          (fun index ↦ bodies index + masks index * secret) =
        linearCombination normalizer
          (fun index ↦ quadraticCoefficients index * secret ^ 2 + errors index) := by
    apply Finset.sum_congr rfl
    intro index _
    dsimp [linearCombination]
    rw [hRows index]
  calc
    (zeroBody + linearCombination normalizer bodies) +
        (zeroMask + linearCombination normalizer masks) * secret =
      (zeroBody + zeroMask * secret) +
        linearCombination normalizer
          (fun index ↦ bodies index + masks index * secret) := by
        rw [hAdd, hScale]
        ring
    _ = zeroError + linearCombination normalizer
          (fun index ↦ quadraticCoefficients index * secret ^ 2 + errors index) := by
        rw [hZero, hRowsCombined]
    _ = zeroError +
        linearCombination normalizer quadraticCoefficients * secret ^ 2 +
          linearCombination normalizer errors := by
        rw [hAdd, hScale]
        ring
    _ = multiplier * gadget * secret ^ 2 +
        (zeroError + linearCombination normalizer errors) := by
      rw [hTarget]
      ring

/-! ## Algebraic modulus-down identity -/

/-- Residual after dividing the public representatives by a factor `P`.  `quotientWitness`
records the multiple of the remaining modulus `Q` in the original congruence. -/
def modulusDownResidual
    {R : Type} [CommRing R]
    (remainingModulus quotientBody quotientMask gadget secret quotientWitness : R) : R :=
  quotientBody + quotientMask * secret - gadget * secret ^ 2 -
    remainingModulus * quotientWitness

/-- Exact factorization underlying coefficientwise modulus-down.  No division or integral-domain
assumption is hidden: the theorem explicitly proves that the numerator is a multiple of `P`. -/
theorem modulusDown_factorization
    {R : Type} [CommRing R]
    (divisor remainingModulus body mask quotientBody quotientMask
      bodyRemainder maskRemainder gadget secret error quotientWitness : R)
    (hBody : body = divisor * quotientBody + bodyRemainder)
    (hMask : mask = divisor * quotientMask + maskRemainder)
    (hAuxiliaryRelation :
      body + mask * secret =
        divisor * (gadget * secret ^ 2) + error +
          (divisor * remainingModulus) * quotientWitness) :
    divisor *
        modulusDownResidual remainingModulus quotientBody quotientMask
          gadget secret quotientWitness =
      error - bodyRemainder - maskRemainder * secret := by
  rw [hBody, hMask] at hAuxiliaryRelation
  dsimp [modulusDownResidual]
  linear_combination hAuxiliaryRelation

/-- The quotient representatives satisfy the desired fixed-gadget relation modulo the remaining
modulus, with `modulusDownResidual` as error. -/
theorem modulusDown_relation
    {R : Type} [CommRing R]
    (remainingModulus quotientBody quotientMask gadget secret quotientWitness : R) :
    quotientBody + quotientMask * secret =
      gadget * secret ^ 2 +
        modulusDownResidual remainingModulus quotientBody quotientMask
          gadget secret quotientWitness +
        remainingModulus * quotientWitness := by
  simp [modulusDownResidual]
  ring

/-- Combined form: the displayed residual gives both the quotient relation and the exact
coefficientwise divisibility identity. -/
theorem modulusDown_identity
    {R : Type} [CommRing R]
    (divisor remainingModulus body mask quotientBody quotientMask
      bodyRemainder maskRemainder gadget secret error quotientWitness : R)
    (hBody : body = divisor * quotientBody + bodyRemainder)
    (hMask : mask = divisor * quotientMask + maskRemainder)
    (hAuxiliaryRelation :
      body + mask * secret =
        divisor * (gadget * secret ^ 2) + error +
          (divisor * remainingModulus) * quotientWitness) :
    quotientBody + quotientMask * secret =
        gadget * secret ^ 2 +
          modulusDownResidual remainingModulus quotientBody quotientMask
            gadget secret quotientWitness +
          remainingModulus * quotientWitness ∧
      divisor *
          modulusDownResidual remainingModulus quotientBody quotientMask
            gadget secret quotientWitness =
        error - bodyRemainder - maskRemainder * secret := by
  exact ⟨modulusDown_relation remainingModulus quotientBody quotientMask
    gadget secret quotientWitness,
    modulusDown_factorization divisor remainingModulus body mask quotientBody
      quotientMask bodyRemainder maskRemainder gadget secret error quotientWitness
      hBody hMask hAuxiliaryRelation⟩

/-- Rank-`degree` negacyclic convolution has the standard linear coefficient-infinity bound. -/
theorem rq_cInfNorm_mul_le_degree
    {modulus degree : ℕ} [NeZero modulus] (hDegree : 0 < degree)
    (left right : FormalProof4FHE.RLWE.Rq modulus degree) :
    LatticeCrypto.cInfNorm (left * right) ≤
      degree * (LatticeCrypto.cInfNorm left * LatticeCrypto.cInfNorm right) := by
  cases degree with
  | zero => omega
  | succ reducedDegree =>
      exact FormalProof4FHE.TFHE.SharpRotationNoise.cInfNorm_mul_le_linear
        left right

/-- Concrete remainder-times-secret specialization used in the modulus-down error estimate. -/
theorem remainder_mul_secret_cInfNorm_le
    {modulus degree remainderBound secretBound : ℕ} [NeZero modulus]
    (hDegree : 0 < degree)
    (remainder secret : FormalProof4FHE.RLWE.Rq modulus degree)
    (hRemainder : LatticeCrypto.cInfNorm remainder ≤ remainderBound)
    (hSecret : LatticeCrypto.cInfNorm secret ≤ secretBound) :
    LatticeCrypto.cInfNorm (remainder * secret) ≤
      degree * (remainderBound * secretBound) := by
  exact (rq_cInfNorm_mul_le_degree hDegree remainder secret).trans
    (Nat.mul_le_mul_left degree (Nat.mul_le_mul hRemainder hSecret))

/-! ## Exact quotient--remainder uniformity -/

/-- Euclidean quotient/remainder equivalence for one canonical coefficient.  Its first component
is division by `divisor`; its second component is reduction modulo `divisor`. -/
def quotientRemainderEquiv (divisor quotientCardinality : ℕ) :
    Fin (divisor * quotientCardinality) ≃
      Fin quotientCardinality × Fin divisor :=
  (finCongr (Nat.mul_comm divisor quotientCardinality)).trans
    finProdFinEquiv.symm

@[simp]
theorem quotientRemainderEquiv_fst_val
    (divisor quotientCardinality : ℕ)
    (value : Fin (divisor * quotientCardinality)) :
    ((quotientRemainderEquiv divisor quotientCardinality value).1).val =
      value.val / divisor := by
  rfl

@[simp]
theorem quotientRemainderEquiv_snd_val
    (divisor quotientCardinality : ℕ)
    (value : Fin (divisor * quotientCardinality)) :
    ((quotientRemainderEquiv divisor quotientCardinality value).2).val =
      value.val % divisor := by
  rfl

/-- Scalar quotient and remainder of a uniform canonical representative are jointly uniform. -/
theorem quotientRemainder_uniform_evalDist
    (divisor quotientCardinality : ℕ)
    [NeZero divisor] [NeZero quotientCardinality] :
    evalDist (quotientRemainderEquiv divisor quotientCardinality <$>
        ($ᵗ Fin (divisor * quotientCardinality))) =
      evalDist ($ᵗ (Fin quotientCardinality × Fin divisor)) :=
  evalDist_map_bijective_uniform_cross
    (α := Fin (divisor * quotientCardinality))
    (β := Fin quotientCardinality × Fin divisor)
    (quotientRemainderEquiv divisor quotientCardinality)
    (quotientRemainderEquiv divisor quotientCardinality).bijective

/-- Apply quotient/remainder splitting independently to every coefficient. -/
def coefficientQuotientRemainderEquiv
    (rank divisor quotientCardinality : ℕ) :
    (Fin rank → Fin (divisor * quotientCardinality)) ≃
      (Fin rank → Fin quotientCardinality) × (Fin rank → Fin divisor) where
  toFun value :=
    ((fun coordinate ↦
      (quotientRemainderEquiv divisor quotientCardinality (value coordinate)).1),
      fun coordinate ↦
        (quotientRemainderEquiv divisor quotientCardinality (value coordinate)).2)
  invFun value coordinate :=
    (quotientRemainderEquiv divisor quotientCardinality).symm
      (value.1 coordinate, value.2 coordinate)
  left_inv value := by
    funext coordinate
    exact (quotientRemainderEquiv divisor quotientCardinality).symm_apply_apply
      (value coordinate)
  right_inv value := by
    apply Prod.ext <;> funext coordinate
    · exact congrArg Prod.fst
        ((quotientRemainderEquiv divisor quotientCardinality).apply_symm_apply
          (value.1 coordinate, value.2 coordinate))
    · exact congrArg Prod.snd
        ((quotientRemainderEquiv divisor quotientCardinality).apply_symm_apply
          (value.1 coordinate, value.2 coordinate))

/-- The complete coefficientwise quotient and remainder are independent canonical uniforms. -/
theorem coefficientQuotientRemainder_uniform_evalDist
    (rank divisor quotientCardinality : ℕ)
    [NeZero divisor] [NeZero quotientCardinality] :
    evalDist (coefficientQuotientRemainderEquiv rank divisor quotientCardinality <$>
        ($ᵗ (Fin rank → Fin (divisor * quotientCardinality)))) =
      evalDist ($ᵗ ((Fin rank → Fin quotientCardinality) ×
        (Fin rank → Fin divisor))) :=
  evalDist_map_bijective_uniform_cross
    (α := Fin rank → Fin (divisor * quotientCardinality))
    (β := (Fin rank → Fin quotientCardinality) × (Fin rank → Fin divisor))
    (coefficientQuotientRemainderEquiv rank divisor quotientCardinality)
    (coefficientQuotientRemainderEquiv rank divisor quotientCardinality).bijective

/-- In particular, discarding the remainder leaves an exactly uniform coefficientwise quotient. -/
theorem coefficientQuotient_uniform_evalDist
    (rank divisor quotientCardinality : ℕ)
    [NeZero divisor] [NeZero quotientCardinality] :
    evalDist ((fun value ↦
        (coefficientQuotientRemainderEquiv rank divisor quotientCardinality value).1) <$>
      ($ᵗ (Fin rank → Fin (divisor * quotientCardinality)))) =
      evalDist ($ᵗ (Fin rank → Fin quotientCardinality)) := by
  have hSplit := coefficientQuotientRemainder_uniform_evalDist
    rank divisor quotientCardinality
  calc
    evalDist ((fun value ↦
        (coefficientQuotientRemainderEquiv rank divisor quotientCardinality value).1) <$>
      ($ᵗ (Fin rank → Fin (divisor * quotientCardinality)))) =
      evalDist (Prod.fst <$>
        (coefficientQuotientRemainderEquiv rank divisor quotientCardinality <$>
          ($ᵗ (Fin rank → Fin (divisor * quotientCardinality))))) := by
            simp [Functor.map_map]
    _ = evalDist (Prod.fst <$> ($ᵗ ((Fin rank → Fin quotientCardinality) ×
          (Fin rank → Fin divisor)))) := by
      simpa only [evalDist_map] using congrArg
        (fun distribution ↦ Prod.fst <$> distribution) hSplit
    _ = evalDist ($ᵗ (Fin rank → Fin quotientCardinality)) :=
      evalDist_map_fst_uniformSample_prod

/-! ### Executable negacyclic-ring quotient/remainder law -/

/-- The executable `Rq` carrier as canonical finite coefficient representatives. -/
def rqFinCoefficientEquiv
    (modulus degree : ℕ) [NeZero modulus] :
    FormalProof4FHE.RLWE.Rq modulus degree ≃ (Fin degree → Fin modulus) :=
  (FormalProof4FHE.FiniteCenteredSupport.polynomialEquivPi (ZMod modulus) degree).trans
    (Equiv.arrowCongr (Equiv.refl (Fin degree))
      (ZMod.finEquiv modulus).toEquiv.symm)

/-- Coefficientwise quotient/remainder equivalence on the literal executable negacyclic rings. -/
def rqQuotientRemainderEquiv
    (degree divisor quotientCardinality : ℕ)
    [NeZero divisor] [NeZero quotientCardinality] :
    FormalProof4FHE.RLWE.Rq (divisor * quotientCardinality) degree ≃
      FormalProof4FHE.RLWE.Rq quotientCardinality degree ×
        FormalProof4FHE.RLWE.Rq divisor degree :=
  (rqFinCoefficientEquiv (divisor * quotientCardinality) degree).trans
    ((coefficientQuotientRemainderEquiv degree divisor quotientCardinality).trans
      (Equiv.prodCongr
        (rqFinCoefficientEquiv quotientCardinality degree).symm
        (rqFinCoefficientEquiv divisor degree).symm))

/-- A uniform executable auxiliary-modulus ring element splits into independent uniform quotient
and remainder ring elements. -/
theorem rqQuotientRemainder_uniform_evalDist
    (degree divisor quotientCardinality : ℕ)
    [NeZero divisor] [NeZero quotientCardinality] :
    evalDist (rqQuotientRemainderEquiv degree divisor quotientCardinality <$>
        ($ᵗ FormalProof4FHE.RLWE.Rq (divisor * quotientCardinality) degree)) =
      evalDist ($ᵗ (FormalProof4FHE.RLWE.Rq quotientCardinality degree ×
        FormalProof4FHE.RLWE.Rq divisor degree)) :=
  evalDist_map_bijective_uniform_cross
    (α := FormalProof4FHE.RLWE.Rq (divisor * quotientCardinality) degree)
    (β := FormalProof4FHE.RLWE.Rq quotientCardinality degree ×
      FormalProof4FHE.RLWE.Rq divisor degree)
    (rqQuotientRemainderEquiv degree divisor quotientCardinality)
    (rqQuotientRemainderEquiv degree divisor quotientCardinality).bijective

/-- Discarding the executable remainder leaves an exactly uniform `Rq Q degree` quotient. -/
theorem rqQuotient_uniform_evalDist
    (degree divisor quotientCardinality : ℕ)
    [NeZero divisor] [NeZero quotientCardinality] :
    evalDist ((fun value ↦
        (rqQuotientRemainderEquiv degree divisor quotientCardinality value).1) <$>
      ($ᵗ FormalProof4FHE.RLWE.Rq (divisor * quotientCardinality) degree)) =
      evalDist ($ᵗ FormalProof4FHE.RLWE.Rq quotientCardinality degree) := by
  have hSplit := rqQuotientRemainder_uniform_evalDist
    degree divisor quotientCardinality
  calc
    evalDist ((fun value ↦
        (rqQuotientRemainderEquiv degree divisor quotientCardinality value).1) <$>
      ($ᵗ FormalProof4FHE.RLWE.Rq (divisor * quotientCardinality) degree)) =
      evalDist (Prod.fst <$>
        (rqQuotientRemainderEquiv degree divisor quotientCardinality <$>
          ($ᵗ FormalProof4FHE.RLWE.Rq
            (divisor * quotientCardinality) degree))) := by
              simp [Functor.map_map]
    _ = evalDist (Prod.fst <$> ($ᵗ
        (FormalProof4FHE.RLWE.Rq quotientCardinality degree ×
          FormalProof4FHE.RLWE.Rq divisor degree))) := by
      simpa only [evalDist_map] using congrArg
        (fun distribution ↦ Prod.fst <$> distribution) hSplit
    _ = evalDist ($ᵗ FormalProof4FHE.RLWE.Rq quotientCardinality degree) :=
      evalDist_map_fst_uniformSample_prod

/-- Split quotient and remainder simultaneously for a public mask/body pair. -/
def rqPairQuotientRemainderEquiv
    (degree divisor quotientCardinality : ℕ)
    [NeZero divisor] [NeZero quotientCardinality] :
    (FormalProof4FHE.RLWE.Rq (divisor * quotientCardinality) degree ×
      FormalProof4FHE.RLWE.Rq (divisor * quotientCardinality) degree) ≃
      ((FormalProof4FHE.RLWE.Rq quotientCardinality degree ×
        FormalProof4FHE.RLWE.Rq quotientCardinality degree) ×
       (FormalProof4FHE.RLWE.Rq divisor degree ×
        FormalProof4FHE.RLWE.Rq divisor degree)) where
  toFun pair :=
    let left := rqQuotientRemainderEquiv degree divisor quotientCardinality pair.1
    let right := rqQuotientRemainderEquiv degree divisor quotientCardinality pair.2
    ((left.1, right.1), (left.2, right.2))
  invFun output :=
    ((rqQuotientRemainderEquiv degree divisor quotientCardinality).symm
      (output.1.1, output.2.1),
     (rqQuotientRemainderEquiv degree divisor quotientCardinality).symm
      (output.1.2, output.2.2))
  left_inv pair := by
    apply Prod.ext
    · exact (rqQuotientRemainderEquiv degree divisor quotientCardinality).symm_apply_apply
        pair.1
    · exact (rqQuotientRemainderEquiv degree divisor quotientCardinality).symm_apply_apply
        pair.2
  right_inv output := by
    rcases output with ⟨⟨leftQuotient, rightQuotient⟩,
      ⟨leftRemainder, rightRemainder⟩⟩
    simp

/-- Coefficientwise quotient of an independent uniform auxiliary-modulus mask/body pair is an
exactly uniform final-modulus pair. -/
theorem rqPairQuotient_uniform_evalDist
    (degree divisor quotientCardinality : ℕ)
    [NeZero divisor] [NeZero quotientCardinality] :
    evalDist ((fun pair ↦
        (rqPairQuotientRemainderEquiv degree divisor quotientCardinality pair).1) <$>
      ($ᵗ (FormalProof4FHE.RLWE.Rq (divisor * quotientCardinality) degree ×
        FormalProof4FHE.RLWE.Rq (divisor * quotientCardinality) degree))) =
      evalDist ($ᵗ (FormalProof4FHE.RLWE.Rq quotientCardinality degree ×
        FormalProof4FHE.RLWE.Rq quotientCardinality degree)) := by
  let split := rqPairQuotientRemainderEquiv degree divisor quotientCardinality
  have hSplit :
      evalDist (split <$> ($ᵗ
        (FormalProof4FHE.RLWE.Rq (divisor * quotientCardinality) degree ×
          FormalProof4FHE.RLWE.Rq (divisor * quotientCardinality) degree))) =
        evalDist ($ᵗ
          ((FormalProof4FHE.RLWE.Rq quotientCardinality degree ×
            FormalProof4FHE.RLWE.Rq quotientCardinality degree) ×
           (FormalProof4FHE.RLWE.Rq divisor degree ×
            FormalProof4FHE.RLWE.Rq divisor degree))) :=
    evalDist_map_bijective_uniform_cross
      (α := FormalProof4FHE.RLWE.Rq (divisor * quotientCardinality) degree ×
        FormalProof4FHE.RLWE.Rq (divisor * quotientCardinality) degree)
      (β := (FormalProof4FHE.RLWE.Rq quotientCardinality degree ×
        FormalProof4FHE.RLWE.Rq quotientCardinality degree) ×
       (FormalProof4FHE.RLWE.Rq divisor degree ×
        FormalProof4FHE.RLWE.Rq divisor degree))
      split split.bijective
  calc
    evalDist ((fun pair ↦
        (rqPairQuotientRemainderEquiv degree divisor quotientCardinality pair).1) <$>
      ($ᵗ (FormalProof4FHE.RLWE.Rq (divisor * quotientCardinality) degree ×
        FormalProof4FHE.RLWE.Rq (divisor * quotientCardinality) degree))) =
      evalDist (Prod.fst <$> (split <$> ($ᵗ
        (FormalProof4FHE.RLWE.Rq (divisor * quotientCardinality) degree ×
          FormalProof4FHE.RLWE.Rq (divisor * quotientCardinality) degree)))) := by
            simp [split, Functor.map_map]
    _ = evalDist (Prod.fst <$> ($ᵗ
          ((FormalProof4FHE.RLWE.Rq quotientCardinality degree ×
            FormalProof4FHE.RLWE.Rq quotientCardinality degree) ×
           (FormalProof4FHE.RLWE.Rq divisor degree ×
            FormalProof4FHE.RLWE.Rq divisor degree)))) := by
      simpa only [evalDist_map] using congrArg
        (fun distribution ↦ Prod.fst <$> distribution) hSplit
    _ = evalDist ($ᵗ (FormalProof4FHE.RLWE.Rq quotientCardinality degree ×
        FormalProof4FHE.RLWE.Rq quotientCardinality degree)) :=
      evalDist_map_fst_uniformSample_prod

/-- Every executable auxiliary-modulus coefficient is exactly `divisor * quotient + remainder`
in canonical natural representatives. -/
theorem rqQuotientRemainder_coefficient_decomposition
    (degree divisor quotientCardinality : ℕ)
    [NeZero divisor] [NeZero quotientCardinality]
    (value : FormalProof4FHE.RLWE.Rq
      (divisor * quotientCardinality) degree)
    (coordinate : Fin degree) :
    let coefficients :=
      rqFinCoefficientEquiv (divisor * quotientCardinality) degree value
    let split :=
      coefficientQuotientRemainderEquiv degree divisor quotientCardinality coefficients
    (coefficients coordinate).val =
      divisor * (split.1 coordinate).val + (split.2 coordinate).val := by
  change ((rqFinCoefficientEquiv (divisor * quotientCardinality) degree value)
      coordinate).val =
    divisor *
      ((quotientRemainderEquiv divisor quotientCardinality
        ((rqFinCoefficientEquiv (divisor * quotientCardinality) degree value)
          coordinate)).1).val +
      ((quotientRemainderEquiv divisor quotientCardinality
        ((rqFinCoefficientEquiv (divisor * quotientCardinality) degree value)
          coordinate)).2).val
  rw [quotientRemainderEquiv_fst_val, quotientRemainderEquiv_snd_val]
  exact (Nat.div_add_mod _ _).symm

/-! ## Exact modular centered-interval flooding -/

namespace ModularFlooding

namespace Box

export FormalProof4FHE.TFHE.Native.BlockCategoricalHashCMUXSelfCircular
  (centeredIntegerInterval shiftedCenteredIntegerInterval
    card_centeredIntegerInterval card_shiftedCenteredIntegerInterval
    card_centeredIntegerInterval_inter_shifted centeredIntervalCoordinateLoss
    centeredIntervalCoordinateLoss_le_absRatio one_sub_centeredIntervalOverlap_eq_loss
    tvDist_uniformFinset_sameCard)

end Box

namespace UniformSubset

export FormalProof4FHE.TFHE.SourceAlignedBRKKSKJointLaw.NativeCompiler
  (uniformFinset)

end UniformSubset

/-- Integer casting modulo `modulus` is injective on any interval of width strictly below the
modulus. -/
theorem intCast_injectiveOn_Icc
    (modulus : ℕ) [NeZero modulus]
    (lower upper : ℤ) (hWidth : upper - lower < modulus) :
    Set.InjOn (fun value : ℤ ↦ (value : ZMod modulus)) (Set.Icc lower upper) := by
  intro left hLeft right hRight hCast
  have hDivides : (modulus : ℤ) ∣ left - right := by
    change (left : ZMod modulus) = right at hCast
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, hCast, sub_self]
  have hAbs : |left - right| < (modulus : ℤ) := by
    rw [abs_lt]
    constructor <;> linarith [hLeft.1, hLeft.2, hRight.1, hRight.2]
  have hZero := Int.eq_zero_of_abs_lt_dvd hDivides hAbs
  exact sub_eq_zero.mp hZero

/-- Centered integer support embedded coefficientwise modulo `modulus`. -/
def modularCenteredInterval (modulus radius : ℕ) : Finset (ZMod modulus) :=
  (Box.centeredIntegerInterval radius).image fun value : ℤ ↦ (value : ZMod modulus)

/-- Shifted centered integer support embedded modulo `modulus`. -/
def modularShiftedCenteredInterval
    (modulus radius : ℕ) (shift : ℤ) : Finset (ZMod modulus) :=
  (Box.shiftedCenteredIntegerInterval radius shift).image
    fun value : ℤ ↦ (value : ZMod modulus)

/-- Both integer supports lie in one common no-wrap interval. -/
theorem centered_union_subset_noWrapInterval
    (radius bound : ℕ) (shift : ℤ) (hBound : shift.natAbs ≤ bound) :
    ↑(Box.centeredIntegerInterval radius ∪
        Box.shiftedCenteredIntegerInterval radius shift) ⊆
      Set.Icc (-((radius + bound : ℕ) : ℤ)) ((radius + bound : ℕ) : ℤ) := by
  have hAbs : |shift| ≤ (bound : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hBound
  have hShiftLower : -(bound : ℤ) ≤ shift :=
    (neg_le_neg hAbs).trans (neg_abs_le shift)
  have hShiftUpper : shift ≤ (bound : ℤ) :=
    (le_abs_self shift).trans hAbs
  intro value hValue
  simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe,
    Box.centeredIntegerInterval, Box.shiftedCenteredIntegerInterval,
    Finset.mem_Icc, Set.mem_Icc] at hValue ⊢
  rcases hValue with hCentered | hShifted <;> omega

/-- Integer casting is injective on the union of the centered and shifted supports under the
no-wrap inequality `2*(radius+bound) < modulus`. -/
theorem intCast_injectiveOn_centered_union
    (modulus radius bound : ℕ) [NeZero modulus]
    (shift : ℤ) (hBound : shift.natAbs ≤ bound)
    (hNoWrap : 2 * (radius + bound) < modulus) :
    Set.InjOn (fun value : ℤ ↦ (value : ZMod modulus))
      ↑(Box.centeredIntegerInterval radius ∪
        Box.shiftedCenteredIntegerInterval radius shift) := by
  apply (intCast_injectiveOn_Icc modulus
    (-((radius + bound : ℕ) : ℤ)) ((radius + bound : ℕ) : ℤ) ?_).mono
  · exact centered_union_subset_noWrapInterval radius bound shift hBound
  · have hNoWrapInt :
        ((2 * (radius + bound) : ℕ) : ℤ) < (modulus : ℤ) := by
      exact_mod_cast hNoWrap
    push_cast at hNoWrapInt ⊢
    omega

/-- The modular centered support retains the exact integer-interval cardinality. -/
theorem card_modularCenteredInterval
    (modulus radius bound : ℕ) [NeZero modulus]
    (shift : ℤ) (hBound : shift.natAbs ≤ bound)
    (hNoWrap : 2 * (radius + bound) < modulus) :
    (modularCenteredInterval modulus radius).card = 2 * radius + 1 := by
  let integerSupport := Box.centeredIntegerInterval radius
  have hInjective := intCast_injectiveOn_centered_union
    modulus radius bound shift hBound hNoWrap
  have hOnSupport : Set.InjOn (fun value : ℤ ↦ (value : ZMod modulus))
      ↑integerSupport := by
    apply hInjective.mono
    intro value hValue
    exact Finset.mem_union_left _ hValue
  rw [modularCenteredInterval, Finset.card_image_of_injOn hOnSupport,
    Box.card_centeredIntegerInterval]

/-- The shifted modular support has the same exact cardinality. -/
theorem card_modularShiftedCenteredInterval
    (modulus radius bound : ℕ) [NeZero modulus]
    (shift : ℤ) (hBound : shift.natAbs ≤ bound)
    (hNoWrap : 2 * (radius + bound) < modulus) :
    (modularShiftedCenteredInterval modulus radius shift).card = 2 * radius + 1 := by
  let integerSupport := Box.shiftedCenteredIntegerInterval radius shift
  have hInjective := intCast_injectiveOn_centered_union
    modulus radius bound shift hBound hNoWrap
  have hOnSupport : Set.InjOn (fun value : ℤ ↦ (value : ZMod modulus))
      ↑integerSupport := by
    apply hInjective.mono
    intro value hValue
    exact Finset.mem_union_right _ hValue
  rw [modularShiftedCenteredInterval, Finset.card_image_of_injOn hOnSupport,
    Box.card_shiftedCenteredIntegerInterval]

/-- The modular supports retain the exact no-wrap overlap count. -/
theorem card_modularCenteredInterval_inter_shifted
    (modulus radius bound : ℕ) [NeZero modulus]
    (shift : ℤ) (hBound : shift.natAbs ≤ bound)
    (hNoWrap : 2 * (radius + bound) < modulus) :
    (modularCenteredInterval modulus radius ∩
        modularShiftedCenteredInterval modulus radius shift).card =
      (2 * radius + 1) - shift.natAbs := by
  let left := Box.centeredIntegerInterval radius
  let right := Box.shiftedCenteredIntegerInterval radius shift
  have hInjective := intCast_injectiveOn_centered_union
    modulus radius bound shift hBound hNoWrap
  have hIntersection :
      (left ∩ right).image (fun value : ℤ ↦ (value : ZMod modulus)) =
        left.image (fun value : ℤ ↦ (value : ZMod modulus)) ∩
          right.image (fun value : ℤ ↦ (value : ZMod modulus)) :=
    Finset.image_inter_of_injOn left right (by
      simpa [left, right] using hInjective)
  rw [modularCenteredInterval, modularShiftedCenteredInterval,
    ← hIntersection]
  rw [Finset.card_image_of_injOn]
  · exact Box.card_centeredIntegerInterval_inter_shifted radius shift
  · exact hInjective.mono Finset.inter_subset_union

/-- Uniform sampler on the modular centered support. -/
def centeredSampler
    (modulus radius : ℕ) [NeZero modulus] : ProbComp (ZMod modulus) := by
  let support := modularCenteredInterval modulus radius
  have hNonempty : support.Nonempty := by
    refine ⟨0, ?_⟩
    rw [show support = modularCenteredInterval modulus radius by rfl,
      modularCenteredInterval]
    simp only [Finset.mem_image]
    refine ⟨0, ?_, by simp⟩
    simp [Box.centeredIntegerInterval]
  letI : Nonempty support := hNonempty.to_subtype
  exact UniformSubset.uniformFinset support

/-- Uniform sampler on the modular shifted support. -/
def shiftedSampler
    (modulus radius : ℕ) [NeZero modulus] (shift : ℤ) : ProbComp (ZMod modulus) := by
  let support := modularShiftedCenteredInterval modulus radius shift
  have hNonempty : support.Nonempty := by
    refine ⟨(shift : ZMod modulus), ?_⟩
    rw [show support = modularShiftedCenteredInterval modulus radius shift by rfl,
      modularShiftedCenteredInterval]
    simp only [Finset.mem_image]
    refine ⟨shift, ?_, rfl⟩
    simp [Box.shiftedCenteredIntegerInterval]
  letI : Nonempty support := hNonempty.to_subtype
  exact UniformSubset.uniformFinset support

/-- Exact modular one-coordinate flooding distance.  The loss is clipped automatically when the
two intervals separate; under the manuscript's small-shift premise it reduces to
`|shift|/(2*radius+1)`. -/
theorem tvDist_centered_shifted_eq_coordinateLoss
    (modulus radius bound : ℕ) [NeZero modulus]
    (shift : ℤ) (hBound : shift.natAbs ≤ bound)
    (hNoWrap : 2 * (radius + bound) < modulus) :
    tvDist (centeredSampler modulus radius)
        (shiftedSampler modulus radius shift) =
      Box.centeredIntervalCoordinateLoss radius shift := by
  let left := modularCenteredInterval modulus radius
  let right := modularShiftedCenteredInterval modulus radius shift
  have hLeftNonempty : left.Nonempty := by
    refine ⟨0, ?_⟩
    rw [show left = modularCenteredInterval modulus radius by rfl,
      modularCenteredInterval]
    simp only [Finset.mem_image]
    refine ⟨0, ?_, by simp⟩
    simp [Box.centeredIntegerInterval]
  have hRightNonempty : right.Nonempty := by
    refine ⟨(shift : ZMod modulus), ?_⟩
    rw [show right = modularShiftedCenteredInterval modulus radius shift by rfl,
      modularShiftedCenteredInterval]
    simp only [Finset.mem_image]
    refine ⟨shift, ?_, rfl⟩
    simp [Box.shiftedCenteredIntegerInterval]
  letI : Nonempty left := hLeftNonempty.to_subtype
  letI : Nonempty right := hRightNonempty.to_subtype
  change tvDist (UniformSubset.uniformFinset left)
      (UniformSubset.uniformFinset right) = _
  rw [Box.tvDist_uniformFinset_sameCard left right]
  · rw [card_modularCenteredInterval_inter_shifted modulus radius bound shift
      hBound hNoWrap,
      card_modularCenteredInterval modulus radius bound shift hBound hNoWrap]
    simpa only [Box.card_centeredIntegerInterval_inter_shifted,
      Box.card_centeredIntegerInterval] using
        Box.one_sub_centeredIntervalOverlap_eq_loss radius shift
  · rw [card_modularCenteredInterval modulus radius bound shift hBound hNoWrap,
      card_modularShiftedCenteredInterval modulus radius bound shift hBound hNoWrap]

/-- Familiar exact ratio when the shift is smaller than the interval cardinality. -/
theorem tvDist_centered_shifted_eq_absRatio
    (modulus radius bound : ℕ) [NeZero modulus]
    (shift : ℤ) (hBound : shift.natAbs ≤ bound)
    (hNoWrap : 2 * (radius + bound) < modulus)
    (hSmallShift : shift.natAbs ≤ 2 * radius + 1) :
    tvDist (centeredSampler modulus radius)
        (shiftedSampler modulus radius shift) =
      (shift.natAbs : ℝ) / (2 * radius + 1) := by
  rw [tvDist_centered_shifted_eq_coordinateLoss modulus radius bound shift hBound hNoWrap]
  unfold Box.centeredIntervalCoordinateLoss
  rw [min_eq_right]
  exact_mod_cast hSmallShift

/-- Concrete joint flooding bound for arbitrary correlated public context.  This is the
manuscript's `coordinateCount * bound / (2*radius+1)` estimate, with modular no-wrap checked once
uniformly for every context-dependent shift. -/
theorem conditioned_modularCenteredFlooding_le
    {Context : Type}
    (contextSampler : ProbComp Context)
    (modulus radius bound coordinateCount : ℕ) [NeZero modulus]
    (shift : Context → Fin coordinateCount → ℤ)
    (hBound : ∀ context coordinate, (shift context coordinate).natAbs ≤ bound)
    (hNoWrap : 2 * (radius + bound) < modulus) :
    tvDist
        (contextSampler >>= fun context ↦
          Fin.mOfFn coordinateCount fun coordinate ↦
            shiftedSampler modulus radius (shift context coordinate))
        (contextSampler >>= fun _context ↦
          Fin.mOfFn coordinateCount fun _coordinate ↦
            centeredSampler modulus radius) ≤
      coordinateCount * (bound : ℝ) / (2 * radius + 1) := by
  apply tvDist_bind_left_le_const'
  intro context
  calc
    tvDist
        (Fin.mOfFn coordinateCount fun coordinate ↦
          shiftedSampler modulus radius (shift context coordinate))
        (Fin.mOfFn coordinateCount fun _coordinate ↦
          centeredSampler modulus radius) ≤
      ∑ coordinate, tvDist
        (shiftedSampler modulus radius (shift context coordinate))
        (centeredSampler modulus radius) :=
      FormalProof4FHE.FiniteProduct.tvDist_fin_mOfFn_le_sum
        coordinateCount _ _
    _ = ∑ coordinate,
        Box.centeredIntervalCoordinateLoss radius (shift context coordinate) := by
      apply Finset.sum_congr rfl
      intro coordinate _
      rw [tvDist_comm,
        tvDist_centered_shifted_eq_coordinateLoss modulus radius bound
          (shift context coordinate) (hBound context coordinate) hNoWrap]
    _ ≤ ∑ _coordinate : Fin coordinateCount,
        (bound : ℝ) / (2 * radius + 1) := by
      apply Finset.sum_le_sum
      intro coordinate _
      calc
        Box.centeredIntervalCoordinateLoss radius (shift context coordinate) ≤
            ((shift context coordinate).natAbs : ℝ) / (2 * radius + 1) :=
          Box.centeredIntervalCoordinateLoss_le_absRatio radius
            (shift context coordinate)
        _ ≤ (bound : ℝ) / (2 * radius + 1) := by
          gcongr
          exact_mod_cast hBound context coordinate
    _ = coordinateCount * (bound : ℝ) / (2 * radius + 1) := by
      simp
      ring

/-- Joint version retaining the complete correlated context in the output. -/
theorem conditioned_modularCenteredFlooding_joint_le
    {Context : Type}
    (contextSampler : ProbComp Context)
    (modulus radius bound coordinateCount : ℕ) [NeZero modulus]
    (shift : Context → Fin coordinateCount → ℤ)
    (hBound : ∀ context coordinate, (shift context coordinate).natAbs ≤ bound)
    (hNoWrap : 2 * (radius + bound) < modulus) :
    tvDist
        (contextSampler >>= fun context ↦
          (fun values ↦ (context, values)) <$>
            Fin.mOfFn coordinateCount (fun coordinate ↦
              shiftedSampler modulus radius (shift context coordinate)))
        (contextSampler >>= fun context ↦
          (fun values ↦ (context, values)) <$>
            Fin.mOfFn coordinateCount (fun _coordinate ↦
              centeredSampler modulus radius)) ≤
      coordinateCount * (bound : ℝ) / (2 * radius + 1) := by
  apply tvDist_bind_left_le_const'
  intro context
  calc
    tvDist
        ((fun values ↦ (context, values)) <$>
          Fin.mOfFn coordinateCount (fun coordinate ↦
            shiftedSampler modulus radius (shift context coordinate)))
        ((fun values ↦ (context, values)) <$>
          Fin.mOfFn coordinateCount (fun _coordinate ↦
            centeredSampler modulus radius)) ≤
      tvDist
        (Fin.mOfFn coordinateCount (fun coordinate ↦
          shiftedSampler modulus radius (shift context coordinate)))
        (Fin.mOfFn coordinateCount (fun _coordinate ↦
          centeredSampler modulus radius)) :=
      tvDist_map_le (fun values ↦ (context, values)) _ _
    _ ≤ coordinateCount * (bound : ℝ) / (2 * radius + 1) := by
      calc
        tvDist
            (Fin.mOfFn coordinateCount (fun coordinate ↦
              shiftedSampler modulus radius (shift context coordinate)))
            (Fin.mOfFn coordinateCount (fun _coordinate ↦
              centeredSampler modulus radius)) ≤
          ∑ coordinate, tvDist
            (shiftedSampler modulus radius (shift context coordinate))
            (centeredSampler modulus radius) :=
          FormalProof4FHE.FiniteProduct.tvDist_fin_mOfFn_le_sum
            coordinateCount _ _
        _ = ∑ coordinate,
            Box.centeredIntervalCoordinateLoss radius (shift context coordinate) := by
          apply Finset.sum_congr rfl
          intro coordinate _
          rw [tvDist_comm,
            tvDist_centered_shifted_eq_coordinateLoss modulus radius bound
              (shift context coordinate) (hBound context coordinate) hNoWrap]
        _ ≤ ∑ _coordinate : Fin coordinateCount,
            (bound : ℝ) / (2 * radius + 1) := by
          apply Finset.sum_le_sum
          intro coordinate _
          exact (Box.centeredIntervalCoordinateLoss_le_absRatio radius
            (shift context coordinate)).trans (by
              gcongr
              exact_mod_cast hBound context coordinate)
        _ = coordinateCount * (bound : ℝ) / (2 * radius + 1) := by
          simp
          ring

/-- Any deterministic BFV/public-view assembly applied after the joint flooding comparison obeys
the same bound. -/
theorem conditioned_modularCenteredFlooding_postprocess_le
    {Context Output : Type}
    (contextSampler : ProbComp Context)
    (modulus radius bound coordinateCount : ℕ) [NeZero modulus]
    (shift : Context → Fin coordinateCount → ℤ)
    (assemble : Context → (Fin coordinateCount → ZMod modulus) → Output)
    (hBound : ∀ context coordinate, (shift context coordinate).natAbs ≤ bound)
    (hNoWrap : 2 * (radius + bound) < modulus) :
    tvDist
        (contextSampler >>= fun context ↦
          assemble context <$>
            Fin.mOfFn coordinateCount (fun coordinate ↦
              shiftedSampler modulus radius (shift context coordinate)))
        (contextSampler >>= fun context ↦
          assemble context <$>
            Fin.mOfFn coordinateCount (fun _coordinate ↦
              centeredSampler modulus radius)) ≤
      coordinateCount * (bound : ℝ) / (2 * radius + 1) := by
  apply tvDist_bind_left_le_const'
  intro context
  calc
    tvDist
        (assemble context <$>
          Fin.mOfFn coordinateCount (fun coordinate ↦
            shiftedSampler modulus radius (shift context coordinate)))
        (assemble context <$>
          Fin.mOfFn coordinateCount (fun _coordinate ↦
            centeredSampler modulus radius)) ≤
      tvDist
        (Fin.mOfFn coordinateCount (fun coordinate ↦
          shiftedSampler modulus radius (shift context coordinate)))
        (Fin.mOfFn coordinateCount (fun _coordinate ↦
          centeredSampler modulus radius)) :=
      tvDist_map_le (assemble context) _ _
    _ ≤ coordinateCount * (bound : ℝ) / (2 * radius + 1) := by
      calc
        tvDist
            (Fin.mOfFn coordinateCount (fun coordinate ↦
              shiftedSampler modulus radius (shift context coordinate)))
            (Fin.mOfFn coordinateCount (fun _coordinate ↦
              centeredSampler modulus radius)) ≤
          ∑ coordinate, tvDist
            (shiftedSampler modulus radius (shift context coordinate))
            (centeredSampler modulus radius) :=
          FormalProof4FHE.FiniteProduct.tvDist_fin_mOfFn_le_sum
            coordinateCount _ _
        _ = ∑ coordinate,
            Box.centeredIntervalCoordinateLoss radius (shift context coordinate) := by
          apply Finset.sum_congr rfl
          intro coordinate _
          rw [tvDist_comm,
            tvDist_centered_shifted_eq_coordinateLoss modulus radius bound
              (shift context coordinate) (hBound context coordinate) hNoWrap]
        _ ≤ ∑ _coordinate : Fin coordinateCount,
            (bound : ℝ) / (2 * radius + 1) := by
          apply Finset.sum_le_sum
          intro coordinate _
          exact (Box.centeredIntervalCoordinateLoss_le_absRatio radius
            (shift context coordinate)).trans (by
              gcongr
              exact_mod_cast hBound context coordinate)
        _ = coordinateCount * (bound : ℝ) / (2 * radius + 1) := by
          simp
          ring

/-- Public affine row view assembled from retained public information, a fixed phase, and the
flooding error. -/
def floodedAffineView
    {Context Public : Type} (modulus coordinateCount : ℕ)
    (publicView : Context → Public)
    (phase : Context → Fin coordinateCount → ZMod modulus)
    (context : Context) (noise : Fin coordinateCount → ZMod modulus) :
    Public × (Fin coordinateCount → ZMod modulus) :=
  (publicView context, fun coordinate ↦ phase context coordinate + noise coordinate)

/-- Corrected zero-branch simulation.  The quotient/remainder rounding residual is treated as a
context-dependent bounded shift and hidden by flooding; no false equality with ordinary RLWE at
the smaller modulus is used. -/
theorem correctedZeroBranchFlooding_le
    {Context Public : Type}
    (contextSampler : ProbComp Context)
    (modulus radius bound coordinateCount : ℕ) [NeZero modulus]
    (publicView : Context → Public)
    (phase : Context → Fin coordinateCount → ZMod modulus)
    (roundingResidual : Context → Fin coordinateCount → ℤ)
    (hBound : ∀ context coordinate,
      (roundingResidual context coordinate).natAbs ≤ bound)
    (hNoWrap : 2 * (radius + bound) < modulus) :
    tvDist
        (contextSampler >>= fun context ↦
          floodedAffineView modulus coordinateCount publicView phase context <$>
            Fin.mOfFn coordinateCount (fun coordinate ↦
              shiftedSampler modulus radius (roundingResidual context coordinate)))
        (contextSampler >>= fun context ↦
          floodedAffineView modulus coordinateCount publicView phase context <$>
            Fin.mOfFn coordinateCount (fun _coordinate ↦
              centeredSampler modulus radius)) ≤
      coordinateCount * (bound : ℝ) / (2 * radius + 1) := by
  exact conditioned_modularCenteredFlooding_postprocess_le
    contextSampler modulus radius bound coordinateCount roundingResidual
    (floodedAffineView modulus coordinateCount publicView phase) hBound hNoWrap

end ModularFlooding

/-! ## Joint flooding composition with correlated side information -/

/-- A uniform scalar translation bound lifts to a complete independent vector and remains valid
after conditioning on arbitrary correlated public state.  This proves the joint-composition part
of the manuscript's flooding lemma; the concrete interval overlap bound must be supplied as
`hScalar`. -/
theorem conditioned_product_shift_tvDist_le
    {Context R : Type} [Finite R] [Add R]
    (contextSampler : ProbComp Context) (count : ℕ)
    (sampler : ProbComp R) (shift : Context → Fin count → R)
    (scalarBound : ℝ)
    (hScalar : ∀ context index,
      FormalProof4FHE.FiniteProduct.addShiftDistance sampler (shift context index) ≤
        scalarBound) :
    tvDist
        (contextSampler >>= fun context ↦
          (fun values index ↦ shift context index + values index) <$>
            Fin.mOfFn count (fun _ ↦ sampler))
        (contextSampler >>= fun _context ↦
          Fin.mOfFn count (fun _ ↦ sampler)) ≤
      count * scalarBound := by
  apply tvDist_bind_left_le_const'
  intro context
  calc
    tvDist
        ((fun values index ↦ shift context index + values index) <$>
          Fin.mOfFn count (fun _ ↦ sampler))
        (Fin.mOfFn count (fun _ ↦ sampler)) ≤
      ∑ index, FormalProof4FHE.FiniteProduct.addShiftDistance
        sampler (shift context index) :=
      FormalProof4FHE.FiniteProduct.tvDist_add_fin_mOfFn_le_sum
        count sampler (shift context)
    _ ≤ ∑ _index : Fin count, scalarBound := by
      apply Finset.sum_le_sum
      intro index _
      exact hScalar context index
    _ = count * scalarBound := by simp

/-! ## Final proof-only security and correctness compositions -/

/-- Triangle composition of the proposed real and corrected zero branches through one uniform
endpoint.  Every reduction and statistical loss remains visible. -/
theorem largeModulus_circular_tvDist_le
    {Output : Type}
    (realBranch zeroBranch uniformBranch : ProbComp Output)
    (realRLWEBound unitRejectionLoss preimageLoss algorithmLoss realFloodingLoss
      zeroRLWEBound zeroFloodingLoss : ℝ)
    (hReal : tvDist realBranch uniformBranch ≤
      realRLWEBound + unitRejectionLoss + preimageLoss + algorithmLoss +
        realFloodingLoss)
    (hZero : tvDist zeroBranch uniformBranch ≤
      zeroRLWEBound + zeroFloodingLoss) :
    tvDist realBranch zeroBranch ≤
      realRLWEBound + unitRejectionLoss + preimageLoss + algorithmLoss +
        realFloodingLoss + zeroRLWEBound + zeroFloodingLoss := by
  calc
    tvDist realBranch zeroBranch ≤
        tvDist realBranch uniformBranch + tvDist uniformBranch zeroBranch :=
      tvDist_triangle _ _ _
    _ = tvDist realBranch uniformBranch + tvDist zeroBranch uniformBranch := by
      rw [tvDist_comm uniformBranch zeroBranch]
    _ ≤ (realRLWEBound + unitRejectionLoss + preimageLoss + algorithmLoss +
          realFloodingLoss) + (zeroRLWEBound + zeroFloodingLoss) :=
      add_le_add hReal hZero
    _ = realRLWEBound + unitRejectionLoss + preimageLoss + algorithmLoss +
        realFloodingLoss + zeroRLWEBound + zeroFloodingLoss := by ring

/-- Proof-carrying complete BFV noise budget for the proposed flooded evaluation key.  The exact
relinearization phase is already checked by the BFV modules; the numerical terms come from the
chosen BFV arithmetic/circuit theorem. -/
structure BFVCorrectnessBudget where
  freshCiphertextNoise : ℕ
  multiplicationNoise : ℕ
  relinearizationNoise : ℕ
  plaintextScalingNoise : ℕ
  decryptionMargin : ℕ
  fits :
    freshCiphertextNoise + multiplicationNoise + relinearizationNoise +
      plaintextScalingNoise < decryptionMargin

/-- The complete named noise sum lies below the certified decryption margin. -/
theorem BFVCorrectnessBudget.total_lt_margin
    (budget : BFVCorrectnessBudget) :
    budget.freshCiphertextNoise + budget.multiplicationNoise +
        budget.relinearizationNoise + budget.plaintextScalingNoise <
      budget.decryptionMargin :=
  budget.fits

end

end FormalProof4FHE.RLWE.BFVCircularSecurityStandardAssumptionProgram
