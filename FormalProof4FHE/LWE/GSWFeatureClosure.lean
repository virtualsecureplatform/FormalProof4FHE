/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.GSWSelfKey
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# A boundary for affine-only GSW secret-feature lifting

A decryption vector formed from features of a binary secret contains a constant
coordinate. Encrypting each original secret bit as a GSW control produces mask
phases equal to that bit times each decryption feature. If all these products
belong to the same linear feature span, that span is the entire Boolean function
space. Consequently it needs at least `2^dimension` generators, including the
constant coordinate. This rules out this particular polynomial-size affine-only
lifting. It is not an impossibility theorem for FHE or for computational KDM
reductions on the unchanged masked quadratic view.
-/

open scoped BigOperators

namespace FormalProof4FHE.LWE.GSWFeatureClosure

abbrev Secret (dimension : ℕ) := Fin dimension → Bool

variable {R : Type} [CommRing R] {dimension : ℕ}

/-- The original binary secret coordinates, viewed as scalar-valued functions. -/
def coordinate (index : Fin dimension) : Secret dimension → R :=
  fun secret ↦ if secret index then 1 else 0

/-- Indicator that a secret agrees with a selected point on the named coordinates. -/
def partialIndicator (point : Secret dimension) (indices : Finset (Fin dimension)) :
    Secret dimension → R :=
  fun secret ↦ ∏ index ∈ indices, if secret index = point index then 1 else 0

/-- Closure under coordinate multiplication and linear subtraction constructs every partial indicator. -/
theorem partialIndicator_mem (space : Submodule R (Secret dimension → R))
    (hone : (1 : Secret dimension → R) ∈ space)
    (hclosed : ∀ index function, function ∈ space → coordinate index * function ∈ space)
    (point : Secret dimension) (indices : Finset (Fin dimension)) :
    partialIndicator point indices ∈ space := by
  classical
  induction indices using Finset.induction_on with
  | empty =>
    have hempty : partialIndicator (R := R) point ∅ = 1 := by
      funext secret
      simp [partialIndicator]
    rw [hempty]
    exact hone
  | @insert index indices hindex ih =>
    have hmul := hclosed index (partialIndicator point indices) ih
    cases hpoint : point index with
    | false =>
      have hsub := space.sub_mem ih hmul
      convert hsub using 1
      funext secret
      cases hsecret : secret index <;>
        simp [partialIndicator, Finset.prod_insert hindex, coordinate, hpoint, hsecret]
    | true =>
      convert hmul using 1
      funext secret
      cases hsecret : secret index <;>
        simp [partialIndicator, Finset.prod_insert hindex, coordinate, hpoint, hsecret]

/-- A full indicator is exactly one at its point and zero everywhere else. -/
theorem partialIndicator_univ (point secret : Secret dimension) :
    partialIndicator (R := R) point Finset.univ secret = if secret = point then 1 else 0 := by
  classical
  by_cases h : secret = point
  · subst secret
    simp [partialIndicator]
  · rw [if_neg h]
    obtain ⟨index, hindex⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ index) (by simp [hindex])

/-- A feature span containing the constant and closed under every original secret bit is already full. -/
theorem eq_top_of_coordinate_closed (space : Submodule R (Secret dimension → R))
    (hone : (1 : Secret dimension → R) ∈ space)
    (hclosed : ∀ index function, function ∈ space → coordinate index * function ∈ space) :
    space = ⊤ := by
  classical
  apply top_unique
  intro function _
  have hexpand : function = ∑ point : Secret dimension,
      function point • partialIndicator point Finset.univ := by
    funext secret
    simp [partialIndicator_univ]
  rw [hexpand]
  exact space.sum_mem fun point _ ↦
    space.smul_mem (function point) (partialIndicator_mem space hone hclosed point Finset.univ)

/-- It suffices to check closure on feature generators: multiplication is linear on their span. -/
theorem span_coordinate_closed {Columns : Type} (feature : Columns → Secret dimension → R)
    (hproduct : ∀ index column,
      coordinate index * feature column ∈ Submodule.span R (Set.range feature)) :
    ∀ index function, function ∈ Submodule.span R (Set.range feature) →
      coordinate index * function ∈ Submodule.span R (Set.range feature) := by
  intro index function hfunction
  induction hfunction using Submodule.span_induction with
  | mem function hfunction =>
    obtain ⟨column, rfl⟩ := hfunction
    exact hproduct index column
  | zero => simp
  | add left right _ _ hleft hright =>
    simpa [mul_add] using (Submodule.span R (Set.range feature)).add_mem hleft hright
  | smul scalar function _ ih =>
    convert (Submodule.span R (Set.range feature)).smul_mem scalar ih using 1
    funext secret
    simp only [Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- An affine-only control layout over a fixed feature vector needs exponentially many features.
The count includes the constant component of the GSW decryption vector. -/
theorem feature_count_ge [Nontrivial R] {features : ℕ}
    (feature : Fin features → Secret dimension → R)
    (hone : (1 : Secret dimension → R) ∈ Submodule.span R (Set.range feature))
    (hproduct : ∀ index column,
      coordinate index * feature column ∈ Submodule.span R (Set.range feature)) :
    2 ^ dimension ≤ features := by
  have htop := eq_top_of_coordinate_closed (Submodule.span R (Set.range feature)) hone
    (span_coordinate_closed feature hproduct)
  have h := finrank_le_of_span_eq_top htop
  simpa [Module.finrank_pi, Secret, Fintype.card_fun] using h

/-- Adjoin the compulsory constant decryption coordinate to any proposed feature vector. -/
def augmentedFeature {features : ℕ} (feature : Fin features → Secret dimension → R) :
    Option (Fin features) → Secret dimension → R
  | none => 1
  | some column => feature column

/-- Affine messages in a feature vector are exactly the span of that vector with the constant. -/
def affineFeatureSpan {features : ℕ} (feature : Fin features → Secret dimension → R) :
    Submodule R (Secret dimension → R) :=
  Submodule.span R (Set.range (augmentedFeature feature))

/-- The original GSW body and mask phases cannot all be affine in fewer than `2^n-1`
nonconstant decryption features. The body premise accounts for the leading constant coordinate. -/
theorem affine_feature_count_ge [Nontrivial R] {features : ℕ}
    (feature : Fin features → Secret dimension → R)
    (hbody : ∀ index, coordinate index ∈ affineFeatureSpan feature)
    (hmask : ∀ index column, coordinate index * feature column ∈ affineFeatureSpan feature) :
    2 ^ dimension ≤ features + 1 := by
  have hone : (1 : Secret dimension → R) ∈ affineFeatureSpan feature :=
    Submodule.subset_span ⟨none, rfl⟩
  have hproduct : ∀ index column,
      coordinate index * augmentedFeature feature column ∈ affineFeatureSpan feature := by
    intro index column
    cases column with
    | none => simpa [augmentedFeature] using hbody index
    | some column => simpa [augmentedFeature] using hmask index column
  have htop := eq_top_of_coordinate_closed (affineFeatureSpan feature) hone
    (span_coordinate_closed (augmentedFeature feature) hproduct)
  have h := finrank_le_of_span_eq_top htop
  simpa [Module.finrank_pi, Secret, Fintype.card_fun] using h

/-- If body phases are affine but the feature vector is smaller, at least one real mask product
escapes its affine span. Negating that product does not change this obstruction. -/
theorem exists_nonaffine_mask_product [Nontrivial R] {features : ℕ}
    (feature : Fin features → Secret dimension → R) (hsmall : features + 1 < 2 ^ dimension)
    (hbody : ∀ index, coordinate index ∈ affineFeatureSpan feature) :
    ∃ index column, coordinate index * feature column ∉ affineFeatureSpan feature := by
  classical
  by_contra hnone
  have hmask : ∀ index column, coordinate index * feature column ∈ affineFeatureSpan feature := by
    simpa only [not_exists, not_not] using hnone
  exact (not_lt_of_ge (affine_feature_count_ge feature hbody hmask)) hsmall

/-- Actual normalized GSW message for encrypting one original bit under the feature key,
restricted to the gadget column of weight one. `none` is the body; `some column` is a mask. -/
def controlPhase {features : ℕ} (feature : Fin features → Secret dimension → R)
    (index : Fin dimension) (position : Option (Fin features)) : Secret dimension → R :=
  fun secret ↦ GSWSelfKey.phaseMessage
    ({ coordinate := fun _ : Fin 1 ↦ position, weight := fun _ ↦ 1 } :
      GSWSelfKey.Layout R features 1)
    (fun column ↦ feature column secret) (fun _ ↦ coordinate index secret) 0

/-- The weight-one GSW body message is the original secret bit. -/
theorem controlPhase_body {features : ℕ} (feature : Fin features → Secret dimension → R)
    (index : Fin dimension) : controlPhase feature index none = coordinate index := by
  funext secret
  simp [controlPhase, GSWSelfKey.phaseMessage]

/-- The weight-one GSW mask message is the negative bit/feature product. -/
theorem controlPhase_mask {features : ℕ} (feature : Fin features → Secret dimension → R)
    (index : Fin dimension) (column : Fin features) :
    controlPhase feature index (some column) = -(coordinate index * feature column) := by
  funext secret
  simp [controlPhase, GSWSelfKey.phaseMessage, mul_comm]

/-- Apply the capacity bound to the actual GSW phase-message definition.
All control phases affine in one feature key force that key's exponential dimension. -/
theorem control_phase_feature_count_ge [Nontrivial R] {features : ℕ}
    (feature : Fin features → Secret dimension → R)
    (hphase : ∀ index position, controlPhase feature index position ∈ affineFeatureSpan feature) :
    2 ^ dimension ≤ features + 1 := by
  apply affine_feature_count_ge feature
  · intro index
    simpa only [controlPhase_body] using hphase index none
  · intro index column
    have h := hphase index (some column)
    rw [controlPhase_mask] at h
    exact (affineFeatureSpan feature).neg_mem_iff.mp h

end FormalProof4FHE.LWE.GSWFeatureClosure
