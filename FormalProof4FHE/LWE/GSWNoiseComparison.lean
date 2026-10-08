/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.GSWGaussianCorrectness
import FormalProof4FHE.Probability.FiniteProductTV

/-!
# Gaussian replacement in the complete one-key GSW generation view

Only the original IID scalar noise law changes. The one secret, all public and
control masks, their materialization, and subsequent processing are shared.
The comparison retains even the client's secret as part of the joint model;
this is a statistical implementation/reference comparison, not a security game
that reveals the secret to an adversary. No circular/KDM hardness is assumed.
-/

open OracleComp
open scoped BigOperators ENNReal

namespace FormalProof4FHE.LWE.GSWNoiseComparison

open GSWGadget GSWSampling GSWPublicKey

variable {View : Type}

/-- Mathematical reference for the full original key draws. The scalar reference may be an
ideal PMF; all masks and the single binary secret use the exact existing finite seed law. -/
noncomputable def referenceDraws {Q : ℕ} [NeZero Q] (params : Parameters Q)
    (dimension samples : ℕ) (errorDistribution : PMF (ZMod Q)) : PMF (KeyDraws params dimension samples) := do
  let errors ← Fin.mOfFn (errorCount params dimension samples) (fun _ ↦ errorDistribution)
  let seed ← (liftM ($ᵗ (KeySeed params dimension samples)) : PMF (KeySeed params dimension samples))
  pure ⟨errors, seed⟩

/-- Reference materialization produces both public tables under that same sampled secret. -/
noncomputable def referenceKeys {Q : ℕ} [NeZero Q] (params : Parameters Q)
    (dimension samples : ℕ) (errorDistribution : PMF (ZMod Q)) : PMF (KeyMaterial params dimension samples) :=
  materialFromDraws params <$> referenceDraws params dimension samples errorDistribution

/-- The implementation's complete draw law is exactly the reference model at its actual scalar PMF. -/
theorem liftM_sampleKeyDraws {Q : ℕ} [NeZero Q] (params : Parameters Q)
    (dimension samples : ℕ) (errorSampler : ProbComp (ZMod Q)) :
    (liftM (sampleKeyDraws params dimension samples errorSampler) : PMF (KeyDraws params dimension samples)) =
      referenceDraws params dimension samples (liftM errorSampler) := by
  simp only [sampleKeyDraws, referenceDraws, liftM_bind, liftM_pure, FiniteProductTV.liftM_sampleIID]

/-- Exact model equality preserves the entire operational key material. -/
theorem liftM_generateKeys {Q : ℕ} [NeZero Q] (params : Parameters Q)
    (dimension samples : ℕ) (errorSampler : ProbComp (ZMod Q)) :
    (liftM (generateKeys params dimension samples errorSampler) : PMF (KeyMaterial params dimension samples)) =
      referenceKeys params dimension samples (liftM errorSampler) := by
  simp only [generateKeys, referenceKeys, liftM_map, liftM_sampleKeyDraws]

/-- The complete draw vector loses at most one scalar TV error per originally sampled coordinate. -/
theorem referenceDraws_etvDist_le {Q : ℕ} [NeZero Q] (params : Parameters Q)
    (dimension samples : ℕ) (left right : PMF (ZMod Q)) :
    (referenceDraws params dimension samples left).etvDist (referenceDraws params dimension samples right) ≤
      errorCount params dimension samples * left.etvDist right := by
  unfold referenceDraws
  exact (PMF.etvDist_bind_right_le _ _ _).trans (FiniteProductTV.etvDist_iid_le _ _ _)

/-- The shared materialization preserves all public-key/control correlations. -/
theorem referenceKeys_etvDist_le {Q : ℕ} [NeZero Q] (params : Parameters Q)
    (dimension samples : ℕ) (left right : PMF (ZMod Q)) :
    (referenceKeys params dimension samples left).etvDist (referenceKeys params dimension samples right) ≤
      errorCount params dimension samples * left.etvDist right := by
  unfold referenceKeys
  exact (PMF.etvDist_map_le _ _ _).trans (referenceDraws_etvDist_le params dimension samples left right)

/-- Actual finite key generation against any ideal scalar reference, with its full joint material. -/
theorem generateKeys_etvDist_reference_le {Q : ℕ} [NeZero Q] (params : Parameters Q)
    (dimension samples : ℕ) (errorSampler : ProbComp (ZMod Q)) (reference : PMF (ZMod Q)) :
    (liftM (generateKeys params dimension samples errorSampler) : PMF (KeyMaterial params dimension samples)).etvDist
      (referenceKeys params dimension samples reference) ≤
        errorCount params dimension samples * (liftM errorSampler : PMF (ZMod Q)).etvDist reference := by
  rw [liftM_generateKeys]
  exact referenceKeys_etvDist_le params dimension samples _ _

/-- Arbitrary shared randomized processing adds no loss, even when it reuses the public key
and controls or chooses subsequent computations based on their joint view. -/
theorem observation_etvDist_reference_le {Q : ℕ} [NeZero Q] (params : Parameters Q)
    (dimension samples : ℕ) (errorSampler : ProbComp (ZMod Q)) (reference : PMF (ZMod Q))
    (observe : KeyMaterial params dimension samples → PMF View) :
    ((liftM (generateKeys params dimension samples errorSampler) : PMF (KeyMaterial params dimension samples)).bind
      observe).etvDist ((referenceKeys params dimension samples reference).bind observe) ≤
        errorCount params dimension samples * (liftM errorSampler : PMF (ZMod Q)).etvDist reference := by
  exact (PMF.etvDist_bind_right_le observe _ _).trans
    (generateKeys_etvDist_reference_le params dimension samples errorSampler reference)

/-- The exact public portion of one operational key material, exposing neither a second key nor the client secret. -/
def publicView {Q dimension samples : ℕ} (params : Parameters Q) (keys : KeyMaterial params dimension samples) :=
  (keys.publicKey, keys.controls)

/-- In particular, the ordinary public key and complete same-key bootstrap tape are compared jointly. -/
theorem publicView_etvDist_reference_le {Q : ℕ} [NeZero Q] (params : Parameters Q)
    (dimension samples : ℕ) (errorSampler : ProbComp (ZMod Q)) (reference : PMF (ZMod Q)) :
    (publicView params <$> (liftM (generateKeys params dimension samples errorSampler) : PMF (KeyMaterial params dimension samples))).etvDist
      (publicView params <$> referenceKeys params dimension samples reference) ≤
        errorCount params dimension samples * (liftM errorSampler : PMF (ZMod Q)).etvDist reference := by
  exact (PMF.etvDist_map_le _ _ _).trans
    (generateKeys_etvDist_reference_le params dimension samples errorSampler reference)

/-- Gaussian reference for the concrete family. This is a mathematical PMF, not an alternative implementation. -/
noncomputable def familyReferenceKeys (dimension : ℕ) :
    PMF (KeyMaterial (GSWBootstrapParameters.params dimension) dimension (sampleCount dimension)) :=
  referenceKeys (GSWBootstrapParameters.params dimension) dimension (sampleCount dimension)
    (GSWGaussianCorrectness.idealScalar dimension)

/-- Explicit complete-key replacement envelope, independent of later inputs and circuit depth. -/
noncomputable def familyComparisonBound (dimension : ℕ) : ℝ≥0∞ :=
  (272 * (dimension + 1) ^ 2 : ℕ) * (GSWGaussianCorrectness.generatedScalarCertificate dimension).bound

set_option backward.isDefEq.respectTransparency false in
/-- The actual generated finite family and its Gaussian reference are close as complete one-key material. -/
theorem family_keys_etvDist_le (dimension : ℕ) :
    (liftM (generateKeys (GSWBootstrapParameters.params dimension) dimension (sampleCount dimension)
      (GaussianIntegerWeights.modularTable (GSWBootstrapParameters.coefficientModulus dimension)
        (dimension + 1) (GaussianIntegerWeights.familyPrecision dimension)).sampler) :
        PMF (KeyMaterial (GSWBootstrapParameters.params dimension) dimension (sampleCount dimension))).etvDist
      (familyReferenceKeys dimension) ≤ familyComparisonBound dimension := by
  have h := generateKeys_etvDist_reference_le (GSWBootstrapParameters.params dimension) dimension (sampleCount dimension)
    (GaussianIntegerWeights.modularTable (GSWBootstrapParameters.coefficientModulus dimension)
      (dimension + 1) (GaussianIntegerWeights.familyPrecision dimension)).sampler
    (GSWGaussianCorrectness.idealScalar dimension)
  have hcount : (errorCount (GSWBootstrapParameters.params dimension) dimension (sampleCount dimension) : ℝ≥0∞) ≤
      (272 * (dimension + 1) ^ 2 : ℕ) := by exact_mod_cast errorCount_le dimension
  have hscalar : (liftM (GaussianIntegerWeights.modularTable (GSWBootstrapParameters.coefficientModulus dimension)
      (dimension + 1) (GaussianIntegerWeights.familyPrecision dimension)).sampler :
        PMF (ZMod (GSWBootstrapParameters.coefficientModulus dimension))).etvDist
          (GSWGaussianCorrectness.idealScalar dimension) ≤
            (GSWGaussianCorrectness.generatedScalarCertificate dimension).bound :=
    (GSWGaussianCorrectness.generatedScalarCertificate dimension).etvDist_le
  exact h.trans (mul_le_mul' hcount hscalar)

/-- All original key-noise draws together still have negligible replacement error. -/
theorem familyComparisonBound_negligible : negligible familyComparisonBound := by
  have h := negligible_polynomial_mul GSWGaussianCorrectness.generatedScalarCertificate_bound_negligible
    ((272 * (Polynomial.X + 1) ^ 2) : Polynomial ℕ)
  convert h using 1
  funext dimension
  simp [familyComparisonBound, Nat.cast_mul, Nat.cast_pow, Nat.cast_add]

/-- No scalar or joint-view approximation premise remains in the concrete statistical comparison. -/
theorem family_keys_etvDist_negligible :
    negligible (fun dimension ↦
      (liftM (generateKeys (GSWBootstrapParameters.params dimension) dimension (sampleCount dimension)
        (GaussianIntegerWeights.modularTable (GSWBootstrapParameters.coefficientModulus dimension)
          (dimension + 1) (GaussianIntegerWeights.familyPrecision dimension)).sampler) :
            PMF (KeyMaterial (GSWBootstrapParameters.params dimension) dimension (sampleCount dimension))).etvDist
        (familyReferenceKeys dimension)) :=
  negligible_of_le family_keys_etvDist_le familyComparisonBound_negligible

/-- Shared randomized observations retain a negligible bound, without query/gate-count multiplication. -/
theorem family_observation_etvDist_negligible (Views : ℕ → Type)
    (observe : ∀ dimension, KeyMaterial (GSWBootstrapParameters.params dimension) dimension (sampleCount dimension) → PMF (Views dimension)) :
    negligible (fun dimension ↦
      ((liftM (generateKeys (GSWBootstrapParameters.params dimension) dimension (sampleCount dimension)
        (GaussianIntegerWeights.modularTable (GSWBootstrapParameters.coefficientModulus dimension)
          (dimension + 1) (GaussianIntegerWeights.familyPrecision dimension)).sampler) :
            PMF (KeyMaterial (GSWBootstrapParameters.params dimension) dimension (sampleCount dimension))).bind
        (observe dimension)).etvDist ((familyReferenceKeys dimension).bind (observe dimension))) := by
  apply negligible_of_le (g := familyComparisonBound)
  · intro dimension
    exact (PMF.etvDist_bind_right_le (observe dimension) _ _).trans (family_keys_etvDist_le dimension)
  · exact familyComparisonBound_negligible

/-- Complete implementation key law for the concrete generated integer-weight sampler. -/
noncomputable def familyGeneratedKeys (dimension : ℕ) :
    PMF (KeyMaterial (GSWBootstrapParameters.params dimension) dimension (sampleCount dimension)) :=
  liftM (generateKeys (GSWBootstrapParameters.params dimension) dimension (sampleCount dimension)
    (GaussianIntegerWeights.modularTable (GSWBootstrapParameters.coefficientModulus dimension)
      (dimension + 1) (GaussianIntegerWeights.familyPrecision dimension)).sampler)

/-- The sampler change in both branches adds only twice the complete-key comparison envelope.
The reference-game advantage is retained; this is not an ordinary-LWE hardness claim. -/
theorem family_advantage_le_reference (dimension : ℕ)
    (observe : Bool → KeyMaterial (GSWBootstrapParameters.params dimension) dimension (sampleCount dimension) → PMF Bool) :
    FiniteProductTV.booleanAdvantage
      ((familyGeneratedKeys dimension).bind (observe false))
      ((familyGeneratedKeys dimension).bind (observe true)) ≤
        2 * familyComparisonBound dimension +
          FiniteProductTV.booleanAdvantage
            ((familyReferenceKeys dimension).bind (observe false))
            ((familyReferenceKeys dimension).bind (observe true)) := by
  have h := FiniteProductTV.booleanAdvantage_bind_le_reference
    (familyGeneratedKeys dimension) (familyReferenceKeys dimension) observe
  exact h.trans (add_le_add (mul_le_mul' le_rfl (family_keys_etvDist_le dimension)) le_rfl)

/-- An independently proved negligible reference-game advantage transfers to the implementation.
Discharging the reference-game hypothesis from ordinary LWE remains required. -/
theorem family_advantage_negligible_of_reference
    (observe : ∀ dimension, Bool → KeyMaterial (GSWBootstrapParameters.params dimension) dimension (sampleCount dimension) → PMF Bool)
    (hreference : negligible (fun dimension ↦
      FiniteProductTV.booleanAdvantage
        ((familyReferenceKeys dimension).bind (observe dimension false))
        ((familyReferenceKeys dimension).bind (observe dimension true)))) :
    negligible (fun dimension ↦
      FiniteProductTV.booleanAdvantage
        ((familyGeneratedKeys dimension).bind (observe dimension false))
        ((familyGeneratedKeys dimension).bind (observe dimension true))) := by
  apply negligible_of_le (fun dimension ↦ family_advantage_le_reference dimension (observe dimension))
  exact negligible_add (negligible_const_mul familyComparisonBound_negligible (by simp)) hreference

end FormalProof4FHE.LWE.GSWNoiseComparison
