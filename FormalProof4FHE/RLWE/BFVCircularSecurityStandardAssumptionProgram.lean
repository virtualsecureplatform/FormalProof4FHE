/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.BFVFoldFreeCircularSecurityFramework
import Mathlib.Data.Nat.Prime.Basic
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

end

end FormalProof4FHE.RLWE.BFVCircularSecurityStandardAssumptionProgram
