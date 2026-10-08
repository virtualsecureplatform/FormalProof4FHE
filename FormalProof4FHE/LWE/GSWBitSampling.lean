/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.GSWNoiseComparison
import FormalProof4FHE.Probability.WeightedBitSampler

/-!
# One-key GSW with fair-bit noise sampling

Bounded rejection replaces the abstract uniform ticket oracle in the scalar
noise implementation. The complete one-secret key law remains negligibly close
to the existing Gaussian reference, including every public/control correlation.
Positive-dimensional circuit correctness is exact. Uniform mask sampling and
arithmetic/evaluator bit costs remain separate implementation obligations.
There is no ordinary-LWE security reduction for the full bootstrap tape here.
-/

open OracleComp
open scoped ENNReal

namespace FormalProof4FHE.LWE.GSWBitSampling

open GSWBootstrapParameters GSWPublicKey GSWSampling

/-- Computable scalar implementation: compressed weights and bounded fair bits. -/
def errorSampler (dimension : ℕ) : ProbComp (ZMod (coefficientModulus dimension)) :=
  WeightedBitSampler.familySampler (coefficientModulus dimension) dimension

/-- Operational key generation using the new noise implementation. The single
secret and the public/control mask samplers are those of `GSWSampling`. -/
def generate (dimension : ℕ) : ProbComp (KeyMaterial (params dimension) dimension (sampleCount dimension)) :=
  generateKeys (params dimension) dimension (sampleCount dimension) (errorSampler dimension)

theorem coinBound_errorSampler (dimension : ℕ) :
    BoundedUniform.CoinBound (errorSampler dimension)
      ((dimension + 1) ^ 2 * (3 * (dimension + 1) ^ 2 + 1)) :=
  WeightedBitSampler.coinBound_familySampler _ _

theorem scalar_tail_eq_zero (dimension : ℕ) :
    Pr[(fun value => keyBound dimension < (LatticeCrypto.centeredRepr value).natAbs) |
      errorSampler dimension] = 0 := by
  apply WeightedSampler.Table.probEvent_bitSampler_eq_zero_of_entries
  intro entry hentry
  exact not_lt_of_ge (GaussianIntegerWeights.modularTable_entries_bounded _ _ _ entry hentry)

set_option backward.isDefEq.respectTransparency false in
theorem correctness_failure_eq_zero (dimension : ℕ) (hdimension : 0 < dimension)
    {inputs wires : ℕ} (messages : Vector Bool inputs)
    (program : GSWCircuit.Program inputs wires) (output : Fin wires) :
    Pr[= false | correctnessExperiment (dimension := dimension) (samples := sampleCount dimension)
      (params dimension) (level dimension) (oneCode dimension)
      (errorSampler dimension) messages program output] = 0 := by
  have h := correctness_failure_le_dimension_bound hdimension (errorSampler dimension)
    messages program output
  have htail := scalar_tail_eq_zero dimension
  simp only [coefficientModulus] at htail
  rw [htail, mul_zero] at h
  exact le_antisymm h zero_le

/-- Correctness for the entire family, including its finite dimension-zero case. -/
theorem correctness_failure_negligible (inputs wires : ℕ → ℕ)
    (messages : ∀ dimension, Vector Bool (inputs dimension))
    (programs : ∀ dimension, GSWCircuit.Program (inputs dimension) (wires dimension))
    (outputs : ∀ dimension, Fin (wires dimension)) :
    negligible (fun dimension =>
      Pr[= false | correctnessExperiment (dimension := dimension) (samples := sampleCount dimension)
        (params dimension) (level dimension) (oneCode dimension)
        (errorSampler dimension) (messages dimension) (programs dimension) (outputs dimension)]) := by
  apply negligible_of_le (g := fun dimension => ENNReal.ofReal ((1 / 2 : ℝ) ^ dimension))
  · intro dimension
    by_cases hdimension : 0 < dimension
    · rw [correctness_failure_eq_zero dimension hdimension]
      exact zero_le
    · have hzero : dimension = 0 := Nat.eq_zero_of_not_pos hdimension
      subst dimension
      simpa only [pow_zero, ENNReal.ofReal_one] using
        (probOutput_le_one (mx := correctnessExperiment (dimension := 0) (samples := sampleCount 0)
          (params 0) (level 0) (oneCode 0) (errorSampler 0) (messages 0) (programs 0) (outputs 0))
          (x := false))
  · exact DiscreteGaussianTail.half_pow_negligible

/-- Full-key implementation/reference loss: old Gaussian approximation plus all
bounded-ticket draws, with the original secret and all masks retained. -/
noncomputable def comparisonBound (dimension : ℕ) : ℝ≥0∞ :=
  (272 * (dimension + 1) ^ 2 : ℕ) * ENNReal.ofReal ((1 / 2 : ℝ) ^ dimension) +
    GSWNoiseComparison.familyComparisonBound dimension

set_option backward.isDefEq.respectTransparency false in
theorem generate_etvDist_le (dimension : ℕ) :
    (liftM (generate dimension) : PMF (KeyMaterial (params dimension) dimension (sampleCount dimension))).etvDist
      (GSWNoiseComparison.familyReferenceKeys dimension) ≤ comparisonBound dimension := by
  let table := GaussianIntegerWeights.modularTable (coefficientModulus dimension)
    (dimension + 1) (GaussianIntegerWeights.familyPrecision dimension)
  let previous : PMF (KeyMaterial (params dimension) dimension (sampleCount dimension)) :=
    liftM (generateKeys (params dimension) dimension (sampleCount dimension) table.sampler)
  have hscalar : (liftM (errorSampler dimension) : PMF (ZMod (coefficientModulus dimension))).etvDist
      (liftM table.sampler) ≤ ENNReal.ofReal ((1 / 2 : ℝ) ^ dimension) := by
    rw [WeightedBitSampler.etvDist_liftM_eq_ofReal_tvDist table.fallback]
    exact ENNReal.ofReal_le_ofReal (WeightedBitSampler.family_tvDist_le _ _)
  have hcount : (errorCount (params dimension) dimension (sampleCount dimension) : ℝ≥0∞) ≤
      (272 * (dimension + 1) ^ 2 : ℕ) := by exact_mod_cast errorCount_le dimension
  have hreplace : (liftM (generate dimension) : PMF _).etvDist previous ≤
      (272 * (dimension + 1) ^ 2 : ℕ) * ENNReal.ofReal ((1 / 2 : ℝ) ^ dimension) := by
    dsimp only [generate, previous]
    rw [GSWNoiseComparison.liftM_generateKeys,
      GSWNoiseComparison.liftM_generateKeys]
    exact (GSWNoiseComparison.referenceKeys_etvDist_le _ _ _ _ _).trans
      (mul_le_mul' hcount hscalar)
  exact (PMF.etvDist_triangle _ previous _).trans
    (add_le_add hreplace (GSWNoiseComparison.family_keys_etvDist_le dimension))

theorem comparisonBound_negligible : negligible comparisonBound := by
  have hbits := negligible_polynomial_mul DiscreteGaussianTail.half_pow_negligible
    (Polynomial.C 272 * (Polynomial.X + 1) ^ 2 : Polynomial ℕ)
  apply negligible_add _ GSWNoiseComparison.familyComparisonBound_negligible
  simpa using hbits

theorem generate_etvDist_negligible :
    negligible (fun dimension =>
      (liftM (generate dimension) : PMF (KeyMaterial (params dimension) dimension (sampleCount dimension))).etvDist
        (GSWNoiseComparison.familyReferenceKeys dimension)) :=
  negligible_of_le generate_etvDist_le comparisonBound_negligible

end FormalProof4FHE.LWE.GSWBitSampling
