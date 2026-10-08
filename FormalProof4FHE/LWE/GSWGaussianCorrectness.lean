/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.GSWSampling
import FormalProof4FHE.Probability.DiscreteGaussianTail
import FormalProof4FHE.Probability.WeightedSampler
import FormalProof4FHE.Probability.GaussianIntegerWeights
import FormalProof4FHE.Probability.GaussianSamplerTV

/-!
# Gaussian correctness accounting for the one-key GSW construction

The ideal scalar Gaussian has integer standard deviation `n+1`. A checked finite
sampler approximation gives whole-circuit failure at most
`272*(n+1)^2 * (4*exp (-(n+1)^2/2) + approximationError)`.
The ideal term is proved negligible. A negligible scalar approximation error
remains negligible after the polynomial factor. The generated scalar family now has a proved negligible Gaussian TV certificate;
its arithmetic/random-bit cost and security of the same-key public view remain open.
-/

open scoped ENNReal

namespace FormalProof4FHE.LWE.GSWGaussianCorrectness

open GSWSampling GSWPublicKey GSWBootstrapParameters DiscreteGaussianTail

/-- Exact mathematical noise target; the Gaussian width is an integer `n+1`. -/
noncomputable def idealScalar (dimension : ℕ) : PMF (ZMod (coefficientModulus dimension)) :=
  ModularGaussian.distribution (coefficientModulus dimension) (dimension + 1 : ℕ)
    (by positivity)

/-- Data plus a checked approximation proof; no efficient family is asserted by this alias. -/
abbrev ScalarCertificate (dimension : ℕ) :=
  FinitePMFCompiler.TicketTable.Certificate (idealScalar dimension)

/-- Explicit correctness-loss envelope, including the actual scalar approximation error. -/
noncomputable def failureBound (dimension : ℕ) (approximationError : ℝ≥0∞) : ℝ≥0∞ :=
  (272 * (dimension + 1) ^ 2 : ℕ) *
    (ENNReal.ofReal (4 * Real.exp (-((dimension + 1 : ℕ) : ℝ) ^ 2 / 2)) + approximationError)

set_option backward.isDefEq.respectTransparency false in
/-- Whole-circuit correctness for the executable sampler carried by a checked Gaussian table. -/
theorem correctness_failure_le_gaussian {dimension inputs wires : ℕ} (hdimension : 0 < dimension)
    (certificate : ScalarCertificate dimension) (messages : Vector Bool inputs)
    (program : GSWCircuit.Program inputs wires) (output : Fin wires) :
    Pr[= false | correctnessExperiment (dimension := dimension) (samples := sampleCount dimension)
      (params dimension) (level dimension) (oneCode dimension)
      certificate.table.sampler messages program output] ≤ failureBound dimension certificate.bound := by
  apply (correctness_failure_le_dimension_bound hdimension certificate.table.sampler
    messages program output).trans
  apply mul_le_mul_of_nonneg_left _ zero_le
  simpa only [keyBound, coefficientModulus, idealScalar] using probEvent_ticket_tail_le (coefficientModulus dimension)
    (dimension + 1) (Nat.succ_pos dimension) certificate

/-- Quadratically many original errors preserve negligibility of the Gaussian and sampler terms. -/
theorem failureBound_negligible {approximationError : ℕ → ℝ≥0∞}
    (happroximation : negligible approximationError) :
    negligible (fun dimension ↦ failureBound dimension (approximationError dimension)) := by
  have hscalar := negligible_add gaussian_tail_bound_negligible happroximation
  have h := negligible_polynomial_mul hscalar
    (Polynomial.C 272 * (Polynomial.X + 1) ^ 2 : Polynomial ℕ)
  simpa [failureBound] using h

/-- The ideal-noise part of the concrete failure envelope is unconditionally negligible. -/
theorem ideal_failureBound_negligible :
    negligible (fun dimension ↦ failureBound dimension 0) :=
  failureBound_negligible negligible_zero

set_option backward.isDefEq.respectTransparency false in
/-- The dimension-zero envelope exceeds one; this handles the finite initial parameter
without altering the actual experiment in the asymptotic theorem. -/
theorem failureBound_zero_ge_one (approximationError : ℝ≥0∞) :
    1 ≤ failureBound 0 approximationError := by
  have hreal : (1 : ℝ) ≤ 4 * Real.exp (-(1 : ℝ) ^ 2 / 2) := by
    norm_num only [one_pow]
    nlinarith [Real.add_one_le_exp (-(1 : ℝ) / 2)]
  have hscalar : (1 : ℝ≥0∞) ≤ ENNReal.ofReal (4 * Real.exp (-(1 : ℝ) ^ 2 / 2)) := by
    simpa only [ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hreal
  unfold failureBound
  simpa only [zero_add, one_pow, mul_one, Nat.cast_one, Nat.cast_ofNat] using
    mul_le_mul' (by norm_num : (1 : ℝ≥0∞) ≤ 272)
      (hscalar.trans (le_add_of_nonneg_right (show 0 ≤ approximationError from zero_le)))

/-- The same explicit bound covers every natural parameter, including its finite zero case. -/
theorem correctness_failure_le_gaussian_all {inputs wires : ℕ} (dimension : ℕ)
    (certificate : ScalarCertificate dimension) (messages : Vector Bool inputs)
    (program : GSWCircuit.Program inputs wires) (output : Fin wires) :
    Pr[= false | correctnessExperiment (dimension := dimension) (samples := sampleCount dimension)
      (params dimension) (level dimension) (oneCode dimension)
      certificate.table.sampler messages program output] ≤ failureBound dimension certificate.bound := by
  by_cases hdimension : 0 < dimension
  · exact correctness_failure_le_gaussian hdimension certificate messages program output
  · have hzero : dimension = 0 := Nat.eq_zero_of_not_pos hdimension
    subst dimension
    exact probOutput_le_one.trans (failureBound_zero_ge_one certificate.bound)

/-- Actual whole-circuit failure is negligible for any checked finite Gaussian sampler family
whose scalar approximation error is negligible. Circuit sizes and input counts may vary freely;
this is a correctness theorem, not a sampler-generation or evaluator cost theorem. -/
theorem correctness_failure_negligible (inputs wires : ℕ → ℕ)
    (certificates : ∀ dimension, ScalarCertificate dimension)
    (messages : ∀ dimension, Vector Bool (inputs dimension))
    (programs : ∀ dimension, GSWCircuit.Program (inputs dimension) (wires dimension))
    (outputs : ∀ dimension, Fin (wires dimension))
    (happroximation : negligible (fun dimension ↦ (certificates dimension).bound)) :
    negligible (fun dimension ↦
      Pr[= false | correctnessExperiment (dimension := dimension) (samples := sampleCount dimension)
        (params dimension) (level dimension) (oneCode dimension)
        (certificates dimension).table.sampler (messages dimension) (programs dimension) (outputs dimension)]) := by
  apply negligible_of_le (g := fun dimension ↦ failureBound dimension (certificates dimension).bound)
  · intro dimension
    exact correctness_failure_le_gaussian_all dimension (certificates dimension)
      (messages dimension) (programs dimension) (outputs dimension)
  · exact failureBound_negligible happroximation

/-- Gaussian approximation certificate carrying compressed integer weights as operational data. -/
abbrev CompressedScalarCertificate (dimension : ℕ) :=
  WeightedSampler.Table.Certificate (idealScalar dimension)

/-- Gaussian whole-circuit bound for the compressed executable sampler; the semantic expansion
is used only by the proof, and introduces no additional approximation loss. -/
theorem correctness_failure_le_compressed_gaussian {inputs wires : ℕ} (dimension : ℕ)
    (certificate : CompressedScalarCertificate dimension) (messages : Vector Bool inputs)
    (program : GSWCircuit.Program inputs wires) (output : Fin wires) :
    Pr[= false | correctnessExperiment (dimension := dimension) (samples := sampleCount dimension)
      (params dimension) (level dimension) (oneCode dimension)
      certificate.table.sampler messages program output] ≤ failureBound dimension certificate.bound := by
  rw [WeightedSampler.Table.Certificate.sampler_eq_toExpanded certificate]
  exact correctness_failure_le_gaussian_all dimension certificate.toExpanded messages program output

/-- Actual failure is negligible for compressed Gaussian certificates with negligible scalar error. -/
theorem correctness_failure_compressed_negligible (inputs wires : ℕ → ℕ)
    (certificates : ∀ dimension, CompressedScalarCertificate dimension)
    (messages : ∀ dimension, Vector Bool (inputs dimension))
    (programs : ∀ dimension, GSWCircuit.Program (inputs dimension) (wires dimension))
    (outputs : ∀ dimension, Fin (wires dimension))
    (happroximation : negligible (fun dimension ↦ (certificates dimension).bound)) :
    negligible (fun dimension ↦
      Pr[= false | correctnessExperiment (dimension := dimension) (samples := sampleCount dimension)
        (params dimension) (level dimension) (oneCode dimension)
        (certificates dimension).table.sampler (messages dimension) (programs dimension) (outputs dimension)]) := by
  apply negligible_of_le (g := fun dimension ↦ failureBound dimension (certificates dimension).bound)
  · intro dimension
    exact correctness_failure_le_compressed_gaussian dimension (certificates dimension)
      (messages dimension) (programs dimension) (outputs dimension)
  · exact failureBound_negligible happroximation

set_option backward.isDefEq.respectTransparency false in
/-- A compressed sampler whose stored errors fit the key budget gives exact whole-circuit
correctness. Its eventual security still needs a checked ordinary-LWE-compatible approximation. -/
theorem correctness_failure_eq_zero_compressed_bounded {dimension inputs wires : ℕ}
    (hdimension : 0 < dimension)
    (table : WeightedSampler.Table (ZMod (coefficientModulus dimension)))
    (hentries : ∀ entry ∈ table.entries,
      (LatticeCrypto.centeredRepr entry.1).natAbs ≤ keyBound dimension)
    (messages : Vector Bool inputs) (program : GSWCircuit.Program inputs wires) (output : Fin wires) :
    Pr[= false | correctnessExperiment (dimension := dimension) (samples := sampleCount dimension)
      (params dimension) (level dimension) (oneCode dimension) table.sampler messages program output] = 0 := by
  have htail : Pr[(fun error ↦ keyBound dimension < (LatticeCrypto.centeredRepr error).natAbs) |
      table.sampler] = 0 := by
    apply table.probEvent_eq_zero_of_entries
    intro entry hentry
    exact not_lt_of_ge (hentries entry hentry)
  have h := correctness_failure_le_dimension_bound hdimension table.sampler messages program output
  simp only [coefficientModulus] at htail
  rw [htail, mul_zero] at h
  exact le_antisymm h zero_le

set_option backward.isDefEq.respectTransparency false in
/-- The computably generated Gaussian-weight table has exact whole-circuit correctness
at every positive secret dimension, without a scalar approximation premise. This is
correctness only: ordinary-LWE joint-view security remains a separate obligation. -/
theorem correctness_failure_eq_zero_generated_weights (dimension : ℕ) (hdimension : 0 < dimension)
    (precision : ℕ) {inputs wires : ℕ} (messages : Vector Bool inputs)
    (program : GSWCircuit.Program inputs wires) (output : Fin wires) :
    Pr[= false | correctnessExperiment (dimension := dimension) (samples := sampleCount dimension)
      (params dimension) (level dimension) (oneCode dimension)
      (GaussianIntegerWeights.modularTable (coefficientModulus dimension)
        (dimension + 1) precision).sampler messages program output] = 0 := by
  apply correctness_failure_eq_zero_compressed_bounded hdimension
  intro entry hentry
  simpa only [keyBound] using GaussianIntegerWeights.modularTable_entries_bounded
    (coefficientModulus dimension) (dimension + 1) precision entry hentry

/-- A concrete certificate family with generated table data and fully proved Gaussian TV error. -/
noncomputable def generatedScalarCertificate (dimension : ℕ) : CompressedScalarCertificate dimension :=
  GaussianSamplerTV.modularCertificate (coefficientModulus dimension) (dimension + 1)
    (GaussianIntegerWeights.familyPrecision dimension) (by omega)

/-- The proved certificate contains the actual computable scalar table. -/
theorem generatedScalarCertificate_table (dimension : ℕ) :
    (generatedScalarCertificate dimension).table =
      GaussianIntegerWeights.modularTable (coefficientModulus dimension) (dimension + 1)
        (GaussianIntegerWeights.familyPrecision dimension) := rfl

theorem generatedScalarCertificate_bound_negligible :
    negligible (fun dimension ↦ (generatedScalarCertificate dimension).bound) := by
  simpa only [generatedScalarCertificate, GaussianSamplerTV.modularCertificate_bound] using
    GaussianSamplerTV.approximationBound_family_negligible

/-- Actual scalar TV to the ideal ordinary-LWE noise model is negligible, without a certificate premise. -/
theorem generated_scalar_etvDist_negligible :
    negligible (fun dimension ↦
      (GaussianIntegerWeights.modularTable (coefficientModulus dimension) (dimension + 1)
        (GaussianIntegerWeights.familyPrecision dimension)).outputPMF.etvDist (idealScalar dimension)) := by
  apply negligible_of_le (g := fun dimension ↦ (generatedScalarCertificate dimension).bound)
  · intro dimension
    exact (generatedScalarCertificate dimension).etvDist_le
  · exact generatedScalarCertificate_bound_negligible

/-- Whole-circuit correctness for the generated finite family, retaining dimension zero and
varying input counts and circuit programs. No tail or approximation certificate is assumed. -/
theorem correctness_failure_generated_negligible (inputs wires : ℕ → ℕ)
    (messages : ∀ dimension, Vector Bool (inputs dimension))
    (programs : ∀ dimension, GSWCircuit.Program (inputs dimension) (wires dimension))
    (outputs : ∀ dimension, Fin (wires dimension)) :
    negligible (fun dimension ↦
      Pr[= false | correctnessExperiment (dimension := dimension) (samples := sampleCount dimension)
        (params dimension) (level dimension) (oneCode dimension)
        (GaussianIntegerWeights.modularTable (coefficientModulus dimension) (dimension + 1)
          (GaussianIntegerWeights.familyPrecision dimension)).sampler
        (messages dimension) (programs dimension) (outputs dimension)]) := by
  simpa only [generatedScalarCertificate_table] using
    correctness_failure_compressed_negligible inputs wires generatedScalarCertificate messages programs outputs
      generatedScalarCertificate_bound_negligible

end FormalProof4FHE.LWE.GSWGaussianCorrectness
