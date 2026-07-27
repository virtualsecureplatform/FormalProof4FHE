/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.RLWE.RankOneHNFLossinessSupportAware
import Mathlib.Analysis.Convex.SpecificFunctions.Pow
import Mathlib.Analysis.Convex.Jensen

/-!
# Conditional Renyi Bounds for Rank-One HNF Lossiness

This module formalizes the finite and algebraic content of `sketch/spanningtree.md`.
It replaces the additive spanning-tree estimate by a prior-sensitive finite-order Renyi
bound.  The central theorem is proved directly for finite `ProbComp` channels, and a second
theorem proves exact tensorization over independent rows while keeping every coherent CRT/RNS
row as one output block.

The subgaussian-to-exponential arithmetic, fixed-weight conditioning loss, descriptor averaging,
and quadratic-codebook energy identities are also native.  Continuous Gaussian and Laplace
density integrals, lattice theta masses, and bounded-differences concentration are represented by
proof-carrying certificates because those measure-theoretic distributions are outside the finite
`ProbComp` model.  No axiom is introduced.
-/

open OracleComp
open scoped ENNReal BigOperators

namespace FormalProof4FHE.RLWE.RankOneHNFLossinessRenyi

open RankOneHNFLossinessRLWENTRU
open RankOneHNFLossinessRefined
open RankOneHNFLossinessSupportAware

noncomputable section

/-! ## Finite Renyi moments -/

/-- The real point mass of a finite probabilistic computation. -/
def realPointMass {Output : Type} [DecidableEq Output]
    (sampler : ProbComp Output) (output : Output) : ℝ :=
  Pr[= output | sampler].toReal

theorem realPointMass_nonneg {Output : Type} [DecidableEq Output]
    (sampler : ProbComp Output) (output : Output) :
    0 ≤ realPointMass sampler output :=
  ENNReal.toReal_nonneg

/-- Finite real Renyi moment
`sum_y P(y)^alpha Q(y)^(1-alpha)`.  Reference masses are required to be positive in the
guessing theorem, so this real-valued definition agrees with the usual extended-real moment. -/
def finiteRenyiMoment {Output : Type} [Fintype Output]
    (alpha : ℝ) (likelihood reference : Output → ℝ) : ℝ :=
  ∑ output, likelihood output ^ alpha * reference output ^ (1 - alpha)

/-- A finite reference probability table with full support. -/
structure PositiveProbabilityTable (Output : Type) [Fintype Output] where
  mass : Output → ℝ
  positive : ∀ output, 0 < mass output
  sum_mass : ∑ output, mass output = 1

theorem PositiveProbabilityTable.nonneg
    {Output : Type} [Fintype Output]
    (reference : PositiveProbabilityTable Output) (output : Output) :
    0 ≤ reference.mass output :=
  (reference.positive output).le

/-- A nonnegative number is bounded by the `L^alpha` norm of any finite family containing it. -/
theorem le_rpow_sum_rpow
    {Index : Type} [Fintype Index] [Nonempty Index]
    (value : Index → ℝ) (nonneg : ∀ index, 0 ≤ value index)
    (alpha : ℝ) (halpha : 0 < alpha) (index : Index) :
    value index ≤ (∑ candidate, value candidate ^ alpha) ^ (1 / alpha) := by
  have hpow : value index ^ alpha ≤ ∑ candidate, value candidate ^ alpha := by
    exact Finset.single_le_sum (fun candidate _ ↦ Real.rpow_nonneg (nonneg candidate) alpha)
      (Finset.mem_univ index)
  have hsum : 0 ≤ ∑ candidate, value candidate ^ alpha :=
    Finset.sum_nonneg fun candidate _ ↦ Real.rpow_nonneg (nonneg candidate) alpha
  have hrpow := Real.rpow_le_rpow
    (Real.rpow_nonneg (nonneg index) alpha) hpow (by positivity : 0 ≤ 1 / alpha)
  calc
    value index = (value index ^ alpha) ^ (1 / alpha) := by
      rw [← Real.rpow_mul (nonneg index)]
      field_simp
      simp
    _ ≤ (∑ candidate, value candidate ^ alpha) ^ (1 / alpha) := hrpow

/-- Weighted finite Jensen inequality for the concave map `x |-> x^(1/alpha)`. -/
theorem sum_mul_rpow_le_rpow_sum_mul
    {Index : Type} [Fintype Index]
    (weight value : Index → ℝ)
    (weight_nonneg : ∀ index, 0 ≤ weight index)
    (weight_sum : ∑ index, weight index = 1)
    (value_nonneg : ∀ index, 0 ≤ value index)
    (alpha : ℝ) (halpha : 1 < alpha) :
    (∑ index, weight index * value index ^ (1 / alpha)) ≤
      (∑ index, weight index * value index) ^ (1 / alpha) := by
  have hexp_pos : 0 ≤ 1 / alpha := by positivity
  have hexp_le : 1 / alpha ≤ 1 := by
    have ha0 : 0 < alpha := lt_trans zero_lt_one halpha
    exact (div_le_one ha0).2 (le_of_lt halpha)
  simpa only [smul_eq_mul, Function.comp_apply] using
    (Real.concaveOn_rpow hexp_pos hexp_le).le_map_sum
      (t := Finset.univ) (w := weight) (p := value)
      (fun index _ ↦ weight_nonneg index) weight_sum
      (fun index _ ↦ Set.mem_Ici.mpr (value_nonneg index))

/-- Pull a positive reference mass out of an `L^alpha` root. -/
theorem rpow_eq_mul_div_rpow
    (total reference alpha : ℝ) (total_nonneg : 0 ≤ total)
    (reference_pos : 0 < reference) (alpha_pos : 0 < alpha) :
    total ^ (1 / alpha) =
      reference * (total / reference ^ alpha) ^ (1 / alpha) := by
  have hrefpow : 0 < reference ^ alpha := Real.rpow_pos_of_pos reference_pos alpha
  calc
    total ^ (1 / alpha) =
        (reference ^ alpha * (total / reference ^ alpha)) ^ (1 / alpha) := by
      rw [mul_div_cancel₀ total hrefpow.ne']
    _ = (reference ^ alpha) ^ (1 / alpha) *
        (total / reference ^ alpha) ^ (1 / alpha) := by
      rw [Real.mul_rpow (Real.rpow_nonneg reference_pos.le alpha)
        (div_nonneg total_nonneg hrefpow.le)]
    _ = reference * (total / reference ^ alpha) ^ (1 / alpha) := by
      congr 1
      rw [← Real.rpow_mul reference_pos.le]
      field_simp
      simp

/-- The weighted Jensen integrand is exactly the usual Renyi factor. -/
theorem reference_mul_div_rpow
    (total reference alpha : ℝ) (reference_pos : 0 < reference) :
    reference * (total / reference ^ alpha) =
      total * reference ^ (1 - alpha) := by
  rw [Real.rpow_sub reference_pos 1 alpha, Real.rpow_one]
  field_simp [ne_of_gt (Real.rpow_pos_of_pos reference_pos alpha)]

/-! ## Conditional finite-order Renyi guessing theorem -/

/-- **Conditional finite Renyi theorem.**  For every full-support finite reference law `Q`,
the optimal guessing probability is bounded by

`(sum_s pi(s)^alpha * sum_y W_s(y)^alpha Q(y)^(1-alpha))^(1/alpha)`.

This is Theorem 1 of `sketch/spanningtree.md` before using row independence. -/
theorem conditionalRenyiGuessingBound
    {Secret Output : Type}
    [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (reference : PositiveProbabilityTable Output)
    (alpha : ℝ) (halpha : 1 < alpha) :
    (conditionalGuessingProbability
      (conditionalChannelJoint prior channel)).toReal ≤
      (∑ secret,
          realPointMass prior secret ^ alpha *
            finiteRenyiMoment alpha
              (fun output ↦ realPointMass (channel secret) output)
              reference.mass) ^ (1 / alpha) := by
  let joint := conditionalChannelJoint prior channel
  let jointMass : Secret → Output → ℝ := fun secret output ↦
    realPointMass prior secret * realPointMass (channel secret) output
  let alphaMass : Output → ℝ := fun output ↦
    ∑ secret, jointMass secret output ^ alpha
  let normalizedMass : Output → ℝ := fun output ↦
    alphaMass output / reference.mass output ^ alpha
  have halphaPos : 0 < alpha := lt_trans zero_lt_one halpha
  have hjointNonneg : ∀ secret output, 0 ≤ jointMass secret output := by
    intro secret output
    exact mul_nonneg (realPointMass_nonneg prior secret)
      (realPointMass_nonneg (channel secret) output)
  have halphaMassNonneg : ∀ output, 0 ≤ alphaMass output := by
    intro output
    exact Finset.sum_nonneg fun secret _ ↦
      Real.rpow_nonneg (hjointNonneg secret output) alpha
  have hnormalizedNonneg : ∀ output, 0 ≤ normalizedMass output := by
    intro output
    exact div_nonneg (halphaMassNonneg output)
      (Real.rpow_nonneg (reference.nonneg output) alpha)
  have hpoint : ∀ output,
      Pr[= (maximizingSecret joint output, output) | joint].toReal ≤
        alphaMass output ^ (1 / alpha) := by
    intro output
    rw [probOutput_conditionalChannelJoint, ENNReal.toReal_mul]
    exact le_rpow_sum_rpow (fun secret ↦ jointMass secret output)
      (fun secret ↦ hjointNonneg secret output) alpha halphaPos
      (maximizingSecret joint output)
  calc
    (conditionalGuessingProbability joint).toReal =
        ∑ output, Pr[= (maximizingSecret joint output, output) | joint].toReal :=
      conditionalGuessingProbability_toReal_eq_realFiniteGuessingMass joint
    _ ≤ ∑ output, alphaMass output ^ (1 / alpha) := by
      exact Finset.sum_le_sum fun output _ ↦ hpoint output
    _ = ∑ output,
        reference.mass output * normalizedMass output ^ (1 / alpha) := by
      apply Finset.sum_congr rfl
      intro output _
      exact rpow_eq_mul_div_rpow _ _ _ (halphaMassNonneg output)
        (reference.positive output) halphaPos
    _ ≤ (∑ output, reference.mass output * normalizedMass output) ^ (1 / alpha) :=
      sum_mul_rpow_le_rpow_sum_mul reference.mass normalizedMass reference.nonneg
        reference.sum_mass hnormalizedNonneg alpha halpha
    _ = (∑ secret,
          realPointMass prior secret ^ alpha *
            finiteRenyiMoment alpha
              (fun output ↦ realPointMass (channel secret) output)
              reference.mass) ^ (1 / alpha) := by
      congr 1
      calc
        (∑ output, reference.mass output * normalizedMass output) =
            ∑ output, ∑ secret,
              reference.mass output *
                (jointMass secret output ^ alpha /
                  reference.mass output ^ alpha) := by
          apply Finset.sum_congr rfl
          intro output _
          unfold normalizedMass alphaMass
          rw [Finset.sum_div, Finset.mul_sum]
        _ = ∑ secret, ∑ output,
              reference.mass output *
                (jointMass secret output ^ alpha /
                  reference.mass output ^ alpha) := by
          rw [Finset.sum_comm]
        _ = ∑ secret,
            realPointMass prior secret ^ alpha *
              finiteRenyiMoment alpha
                (fun output ↦ realPointMass (channel secret) output)
                reference.mass := by
          apply Finset.sum_congr rfl
          intro secret _
          unfold finiteRenyiMoment jointMass
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro output _
          rw [reference_mul_div_rpow _ _ _ (reference.positive output)]
          rw [Real.mul_rpow (realPointMass_nonneg prior secret)
            (realPointMass_nonneg (channel secret) output)]
          ring

/-! ## Exact tensorization over independent rows -/

/-- Product of homogeneous finite row likelihood tables.  An `Output` value may itself be the
complete coherent CRT/RNS observation of one row. -/
def productLikelihood {Row Output Secret : Type} [Fintype Row]
    (rowLikelihood : Row → Secret → Output → ℝ)
    (secret : Secret) (output : Row → Output) : ℝ :=
  ∏ row, rowLikelihood row secret (output row)

/-- Product of row reference tables. -/
def productReferenceMass {Row Output : Type} [Fintype Row]
    (rowReference : Row → Output → ℝ) (output : Row → Output) : ℝ :=
  ∏ row, rowReference row (output row)

/-- Independent products of positive finite probability tables again form a positive probability
table. -/
def PositiveProbabilityTable.pi
    {Row Output : Type} [Fintype Row] [DecidableEq Row] [Fintype Output]
    (rowReference : Row → PositiveProbabilityTable Output) :
    PositiveProbabilityTable (Row → Output) where
  mass := productReferenceMass fun row ↦ (rowReference row).mass
  positive := by
    intro output
    exact Finset.prod_pos fun row _ ↦ (rowReference row).positive (output row)
  sum_mass := by
    unfold productReferenceMass
    rw [← Fintype.prod_sum]
    have hrow : ∀ row, ∑ output, (rowReference row).mass output = 1 :=
      fun row ↦ (rowReference row).sum_mass
    simp_rw [hrow]
    simp

/-- Exact product factorization of finite Renyi moments. -/
theorem finiteRenyiMoment_product
    {Row Output Secret : Type}
    [Fintype Row] [DecidableEq Row] [Fintype Output]
    (rowLikelihood : Row → Secret → Output → ℝ)
    (likelihood_nonneg : ∀ row secret output,
      0 ≤ rowLikelihood row secret output)
    (rowReference : Row → PositiveProbabilityTable Output)
    (alpha : ℝ) (secret : Secret) :
    finiteRenyiMoment alpha
        (productLikelihood rowLikelihood secret)
        (productReferenceMass fun row ↦ (rowReference row).mass) =
      ∏ row,
        finiteRenyiMoment alpha (rowLikelihood row secret)
          (rowReference row).mass := by
  unfold finiteRenyiMoment productLikelihood productReferenceMass
  symm
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro output _
  rw [Finset.prod_mul_distrib]
  rw [Real.finsetProd_rpow Finset.univ
      (fun row ↦ rowLikelihood row secret (output row))
      (fun row _ ↦ likelihood_nonneg row secret (output row)) alpha]
  rw [Real.finsetProd_rpow Finset.univ
      (fun row ↦ (rowReference row).mass (output row))
      (fun row _ ↦ (rowReference row).nonneg (output row)) (1 - alpha)]

/-- **Conditional Renyi product theorem.**  If the complete row vector has the product
likelihood of its independent row channels, its guessing probability is bounded by the product
of the row Renyi moments inside the prior-sensitive partition function.  No factorization is made
inside the per-row `Output` type. -/
theorem conditionalRenyiProductGuessingBound
    {Row Secret Output : Type}
    [Fintype Row] [DecidableEq Row]
    [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret)
    (rowChannel : Row → Secret → ProbComp Output)
    (completeChannel : Secret → ProbComp (Row → Output))
    (product_law : ∀ secret output,
      realPointMass (completeChannel secret) output =
        productLikelihood
          (fun row secret output ↦ realPointMass (rowChannel row secret) output)
          secret output)
    (rowReference : Row → PositiveProbabilityTable Output)
    (alpha : ℝ) (halpha : 1 < alpha) :
    (conditionalGuessingProbability
      (conditionalChannelJoint prior completeChannel)).toReal ≤
      (∑ secret,
          realPointMass prior secret ^ alpha *
            ∏ row,
              finiteRenyiMoment alpha
                (fun output ↦ realPointMass (rowChannel row secret) output)
                (rowReference row).mass) ^ (1 / alpha) := by
  let reference := PositiveProbabilityTable.pi rowReference
  refine (conditionalRenyiGuessingBound prior completeChannel reference alpha halpha).trans_eq ?_
  congr 2
  funext secret
  congr 1
  rw [show (fun output ↦ realPointMass (completeChannel secret) output) =
      productLikelihood
        (fun row secret output ↦ realPointMass (rowChannel row secret) output)
        secret from funext (product_law secret)]
  exact finiteRenyiMoment_product
    (fun row secret output ↦ realPointMass (rowChannel row secret) output)
    (fun row secret output ↦ realPointMass_nonneg (rowChannel row secret) output)
    rowReference alpha secret

/-! ## Energy and entropy reduction -/

/-- Expectation with respect to the real point masses of a finite probabilistic computation. -/
def finiteExpectation {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (prior : ProbComp Secret) (value : Secret → ℝ) : ℝ :=
  ∑ secret, realPointMass prior secret * value secret

@[simp]
theorem finiteExpectation_one
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (prior : ProbComp Secret) :
    finiteExpectation prior (fun _ ↦ (1 : ℝ)) = 1 := by
  unfold finiteExpectation realPointMass
  simpa using sum_probOutput_toReal_eq_one prior

/-- The centered exponential moment used in the subgaussian hypothesis. -/
def centeredExponentialMoment
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (prior : ProbComp Secret) (energy : Secret → ℝ) (mean t : ℝ) : ℝ :=
  finiteExpectation prior (fun secret ↦ Real.exp (t * (energy secret - mean)))

/-- A rowwise proof object connecting a concrete likelihood/reference pair to a nonnegative
energy.  Equal-covariance Gaussian integration supplies this interface with coefficient
`alpha * (alpha - 1) / 2`; finite implementations may prove it directly from their tables. -/
structure RenyiRowEnergyCertificate
    (Row Secret Output : Type) [Fintype Output]
    (rowLikelihood : Row → Secret → Output → ℝ)
    (rowReference : Row → PositiveProbabilityTable Output)
    (alpha coefficient : ℝ) where
  likelihood_nonneg : ∀ row secret output, 0 ≤ rowLikelihood row secret output
  energy : Row → Secret → ℝ
  energy_nonneg : ∀ row secret, 0 ≤ energy row secret
  moment_le : ∀ row secret,
    finiteRenyiMoment alpha (rowLikelihood row secret)
        (rowReference row).mass ≤
      Real.exp (coefficient * energy row secret)

/-- Total descriptor-conditioned whitened energy across all independent rows. -/
def RenyiRowEnergyCertificate.totalEnergy
    {Row Secret Output : Type} [Fintype Row] [Fintype Output]
    {rowLikelihood : Row → Secret → Output → ℝ}
    {rowReference : Row → PositiveProbabilityTable Output}
    {alpha coefficient : ℝ}
    (certificate : RenyiRowEnergyCertificate Row Secret Output
      rowLikelihood rowReference alpha coefficient)
    (secret : Secret) : ℝ :=
  ∑ row, certificate.energy row secret

theorem RenyiRowEnergyCertificate.totalEnergy_nonneg
    {Row Secret Output : Type} [Fintype Row] [Fintype Output]
    {rowLikelihood : Row → Secret → Output → ℝ}
    {rowReference : Row → PositiveProbabilityTable Output}
    {alpha coefficient : ℝ}
    (certificate : RenyiRowEnergyCertificate Row Secret Output
      rowLikelihood rowReference alpha coefficient)
    (secret : Secret) :
    0 ≤ certificate.totalEnergy secret :=
  Finset.sum_nonneg fun row _ ↦ certificate.energy_nonneg row secret

/-- Replace the exact tensorized row moments by a certified exponential energy cost. -/
theorem productRenyiMoment_le_exp_totalEnergy
    {Row Secret Output : Type}
    [Fintype Row] [Fintype Output]
    (rowLikelihood : Row → Secret → Output → ℝ)
    (rowReference : Row → PositiveProbabilityTable Output)
    (alpha coefficient : ℝ)
    (certificate : RenyiRowEnergyCertificate Row Secret Output
      rowLikelihood rowReference alpha coefficient)
    (secret : Secret) :
    (∏ row,
        finiteRenyiMoment alpha (rowLikelihood row secret)
          (rowReference row).mass) ≤
      Real.exp (coefficient * certificate.totalEnergy secret) := by
  calc
    (∏ row,
        finiteRenyiMoment alpha (rowLikelihood row secret)
          (rowReference row).mass) ≤
        ∏ row, Real.exp (coefficient * certificate.energy row secret) := by
      apply Finset.prod_le_prod
      · intro row _
        exact Finset.sum_nonneg fun output _ ↦
          mul_nonneg
            (Real.rpow_nonneg (certificate.likelihood_nonneg row secret output) alpha)
            (Real.rpow_nonneg ((rowReference row).nonneg output) (1 - alpha))
      · intro row _
        exact certificate.moment_le row secret
    _ = Real.exp (coefficient * certificate.totalEnergy secret) := by
      rw [← Real.exp_sum]
      congr 1
      unfold RenyiRowEnergyCertificate.totalEnergy
      rw [Finset.mul_sum]

/-- Product theorem after a rowwise energy certificate.  In the Gaussian specialization the
coefficient is `alpha * (alpha - 1) / 2`. -/
theorem conditionalRenyiProductEnergyBound
    {Row Secret Output : Type}
    [Fintype Row] [DecidableEq Row]
    [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret)
    (rowChannel : Row → Secret → ProbComp Output)
    (completeChannel : Secret → ProbComp (Row → Output))
    (product_law : ∀ secret output,
      realPointMass (completeChannel secret) output =
        productLikelihood
          (fun row secret output ↦ realPointMass (rowChannel row secret) output)
          secret output)
    (rowReference : Row → PositiveProbabilityTable Output)
    (alpha coefficient : ℝ) (halpha : 1 < alpha)
    (certificate : RenyiRowEnergyCertificate Row Secret Output
      (fun row secret output ↦ realPointMass (rowChannel row secret) output)
      rowReference alpha coefficient) :
    (conditionalGuessingProbability
      (conditionalChannelJoint prior completeChannel)).toReal ≤
      (∑ secret,
          realPointMass prior secret ^ alpha *
            Real.exp (coefficient * certificate.totalEnergy secret)) ^ (1 / alpha) := by
  refine (conditionalRenyiProductGuessingBound prior rowChannel completeChannel
    product_law rowReference alpha halpha).trans ?_
  apply Real.rpow_le_rpow
  · exact Finset.sum_nonneg fun secret _ ↦ mul_nonneg
      (Real.rpow_nonneg (realPointMass_nonneg prior secret) alpha)
      (Finset.prod_nonneg fun row _ ↦ Finset.sum_nonneg fun output _ ↦
        mul_nonneg (Real.rpow_nonneg (realPointMass_nonneg _ _) alpha)
          (Real.rpow_nonneg ((rowReference row).nonneg output) (1 - alpha)))
  · apply Finset.sum_le_sum
    intro secret _
    exact mul_le_mul_of_nonneg_left
      (productRenyiMoment_le_exp_totalEnergy
        (fun row secret output ↦ realPointMass (rowChannel row secret) output)
        rowReference alpha coefficient certificate secret)
      (Real.rpow_nonneg (realPointMass_nonneg prior secret) alpha)
  · positivity

/-- A max-mass/conditional-min-entropy bound converts `pi(s)^alpha` to a single prior factor. -/
theorem pointMass_rpow_le_entropyFactor_mul
    (mass entropy alpha : ℝ) (mass_nonneg : 0 ≤ mass)
    (mass_le : mass ≤ Real.exp (-entropy)) (halpha : 1 < alpha) :
    mass ^ alpha ≤ Real.exp (-(alpha - 1) * entropy) * mass := by
  by_cases hmass : mass = 0
  · rw [hmass, Real.zero_rpow (ne_of_gt (lt_trans zero_lt_one halpha)), mul_zero]
  · have hmassPos : 0 < mass := lt_of_le_of_ne mass_nonneg (Ne.symm hmass)
    have hexpPos : 0 < Real.exp (-entropy) := Real.exp_pos _
    calc
      mass ^ alpha = mass ^ ((alpha - 1) + 1) := by
        congr 1
        ring
      _ = mass ^ (alpha - 1) * mass ^ (1 : ℝ) :=
        Real.rpow_add hmassPos _ _
      _ = mass ^ (alpha - 1) * mass := by rw [Real.rpow_one]
      _ ≤ (Real.exp (-entropy)) ^ (alpha - 1) * mass := by
        exact mul_le_mul_of_nonneg_right
          (Real.rpow_le_rpow mass_nonneg mass_le (by linarith)) mass_nonneg
      _ = Real.exp (-(alpha - 1) * entropy) * mass := by
        rw [← Real.exp_mul]
        congr 2
        ring

/-- Finite expectation of `exp(coefficient * energy)`. -/
def exponentialEnergyMoment
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (prior : ProbComp Secret) (energy : Secret → ℝ) (coefficient : ℝ) : ℝ :=
  finiteExpectation prior (fun secret ↦ Real.exp (coefficient * energy secret))

/-- Equation (4), stated without logarithms so that zero guessing mass causes no endpoint
convention. -/
theorem conditionalRenyiEnergyEntropyBound
    {Secret Output : Type}
    [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret) (channel : Secret → ProbComp Output)
    (reference : PositiveProbabilityTable Output)
    (energy : Secret → ℝ) (alpha coefficient entropy : ℝ)
    (halpha : 1 < alpha)
    (moment_le : ∀ secret,
      finiteRenyiMoment alpha
          (fun output ↦ realPointMass (channel secret) output)
          reference.mass ≤
        Real.exp (coefficient * energy secret))
    (prior_max : ∀ secret,
      realPointMass prior secret ≤ Real.exp (-entropy)) :
    (conditionalGuessingProbability
      (conditionalChannelJoint prior channel)).toReal ≤
      Real.exp (-((alpha - 1) / alpha) * entropy) *
        exponentialEnergyMoment prior energy coefficient ^ (1 / alpha) := by
  have halphaPos : 0 < alpha := lt_trans zero_lt_one halpha
  have hpartitionNonneg :
      0 ≤ ∑ secret,
        realPointMass prior secret ^ alpha *
          finiteRenyiMoment alpha
            (fun output ↦ realPointMass (channel secret) output)
            reference.mass := by
    exact Finset.sum_nonneg fun secret _ ↦ mul_nonneg
      (Real.rpow_nonneg (realPointMass_nonneg prior secret) alpha)
      (Finset.sum_nonneg fun output _ ↦ mul_nonneg
        (Real.rpow_nonneg (realPointMass_nonneg (channel secret) output) alpha)
        (Real.rpow_nonneg (reference.nonneg output) (1 - alpha)))
  have hpartition :
      (∑ secret,
          realPointMass prior secret ^ alpha *
            finiteRenyiMoment alpha
              (fun output ↦ realPointMass (channel secret) output)
              reference.mass) ≤
        Real.exp (-(alpha - 1) * entropy) *
          exponentialEnergyMoment prior energy coefficient := by
    unfold exponentialEnergyMoment finiteExpectation
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro secret _
    calc
      realPointMass prior secret ^ alpha *
          finiteRenyiMoment alpha
            (fun output ↦ realPointMass (channel secret) output)
            reference.mass ≤
          realPointMass prior secret ^ alpha *
            Real.exp (coefficient * energy secret) := by
        exact mul_le_mul_of_nonneg_left (moment_le secret)
          (Real.rpow_nonneg (realPointMass_nonneg prior secret) alpha)
      _ ≤ (Real.exp (-(alpha - 1) * entropy) *
          realPointMass prior secret) *
            Real.exp (coefficient * energy secret) :=
        mul_le_mul_of_nonneg_right
          (pointMass_rpow_le_entropyFactor_mul _ _ _
            (realPointMass_nonneg prior secret) (prior_max secret) halpha)
          (Real.exp_nonneg _)
      _ = Real.exp (-(alpha - 1) * entropy) *
          (realPointMass prior secret *
            Real.exp (coefficient * energy secret)) := by ring
  have hexpMomentNonneg :
      0 ≤ exponentialEnergyMoment prior energy coefficient := by
    unfold exponentialEnergyMoment finiteExpectation
    exact Finset.sum_nonneg fun secret _ ↦
      mul_nonneg (realPointMass_nonneg prior secret) (Real.exp_nonneg _)
  calc
    (conditionalGuessingProbability
      (conditionalChannelJoint prior channel)).toReal ≤
        (∑ secret,
          realPointMass prior secret ^ alpha *
            finiteRenyiMoment alpha
              (fun output ↦ realPointMass (channel secret) output)
              reference.mass) ^ (1 / alpha) :=
      conditionalRenyiGuessingBound prior channel reference alpha halpha
    _ ≤ (Real.exp (-(alpha - 1) * entropy) *
        exponentialEnergyMoment prior energy coefficient) ^ (1 / alpha) := by
      exact Real.rpow_le_rpow hpartitionNonneg hpartition (by positivity)
    _ = Real.exp (-((alpha - 1) / alpha) * entropy) *
        exponentialEnergyMoment prior energy coefficient ^ (1 / alpha) := by
      rw [Real.mul_rpow (Real.exp_nonneg _) hexpMomentNonneg]
      congr 1
      rw [← Real.exp_mul]
      congr 1
      field_simp

/-- Centering is an exact finite identity, independent of any concentration hypothesis. -/
theorem exponentialEnergyMoment_eq_exp_mul_centered
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (prior : ProbComp Secret) (energy : Secret → ℝ) (mean t : ℝ) :
    exponentialEnergyMoment prior energy t =
      Real.exp (t * mean) * centeredExponentialMoment prior energy mean t := by
  unfold exponentialEnergyMoment centeredExponentialMoment finiteExpectation
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro secret _
  calc
    realPointMass prior secret * Real.exp (t * energy secret) =
        realPointMass prior secret *
          Real.exp (t * mean + t * (energy secret - mean)) := by
      congr 2
      ring
    _ = Real.exp (t * mean) *
        (realPointMass prior secret *
          Real.exp (t * (energy secret - mean))) := by
      rw [Real.exp_add]
      ring

/-- The analytic input of Theorem 2.  A bounded-differences or direct finite computation can
construct this object; all use of the resulting MGF estimate is checked below. -/
structure SubgaussianEnergyCertificate
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (prior : ProbComp Secret) (energy : Secret → ℝ) where
  mean : ℝ
  varianceProxy : ℝ
  varianceProxy_nonneg : 0 ≤ varianceProxy
  mean_eq_expectation : mean = finiteExpectation prior energy
  centered_mgf_le : ∀ t, 0 ≤ t →
    centeredExponentialMoment prior energy mean t ≤
      Real.exp (t ^ 2 * varianceProxy / 8)

/-- The centered subgaussian certificate bounds the uncentered exponential energy moment. -/
theorem SubgaussianEnergyCertificate.exponentialEnergyMoment_le
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    {prior : ProbComp Secret} {energy : Secret → ℝ}
    (certificate : SubgaussianEnergyCertificate prior energy)
    (t : ℝ) (ht : 0 ≤ t) :
    exponentialEnergyMoment prior energy t ≤
      Real.exp (t * certificate.mean +
        t ^ 2 * certificate.varianceProxy / 8) := by
  rw [exponentialEnergyMoment_eq_exp_mul_centered
    prior energy certificate.mean t]
  calc
    Real.exp (t * certificate.mean) *
        centeredExponentialMoment prior energy certificate.mean t ≤
      Real.exp (t * certificate.mean) *
        Real.exp (t ^ 2 * certificate.varianceProxy / 8) :=
      mul_le_mul_of_nonneg_left (certificate.centered_mgf_le t ht)
        (Real.exp_nonneg _)
    _ = Real.exp (t * certificate.mean +
        t ^ 2 * certificate.varianceProxy / 8) := (Real.exp_add _ _).symm

/-- Product/energy/entropy form of equation (4).  It exposes the complete independent-row
channel while treating each row output as one coherent block. -/
theorem conditionalRenyiProductEnergyEntropyBound
    {Row Secret Output : Type}
    [Fintype Row] [DecidableEq Row]
    [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret)
    (rowChannel : Row → Secret → ProbComp Output)
    (completeChannel : Secret → ProbComp (Row → Output))
    (product_law : ∀ secret output,
      realPointMass (completeChannel secret) output =
        productLikelihood
          (fun row secret output ↦ realPointMass (rowChannel row secret) output)
          secret output)
    (rowReference : Row → PositiveProbabilityTable Output)
    (alpha coefficient entropy : ℝ) (halpha : 1 < alpha)
    (certificate : RenyiRowEnergyCertificate Row Secret Output
      (fun row secret output ↦ realPointMass (rowChannel row secret) output)
      rowReference alpha coefficient)
    (prior_max : ∀ secret,
      realPointMass prior secret ≤ Real.exp (-entropy)) :
    (conditionalGuessingProbability
      (conditionalChannelJoint prior completeChannel)).toReal ≤
      Real.exp (-((alpha - 1) / alpha) * entropy) *
        exponentialEnergyMoment prior certificate.totalEnergy coefficient ^
          (1 / alpha) := by
  let reference := PositiveProbabilityTable.pi rowReference
  apply conditionalRenyiEnergyEntropyBound prior completeChannel reference
    certificate.totalEnergy alpha coefficient entropy halpha
  · intro secret
    rw [show (fun output ↦ realPointMass (completeChannel secret) output) =
        productLikelihood
          (fun row secret output ↦ realPointMass (rowChannel row secret) output)
          secret from funext (product_law secret)]
    change finiteRenyiMoment alpha
      (productLikelihood
        (fun row secret output ↦ realPointMass (rowChannel row secret) output)
        secret)
      (productReferenceMass fun row ↦ (rowReference row).mass) ≤ _
    rw [finiteRenyiMoment_product
      (fun row secret output ↦ realPointMass (rowChannel row secret) output)
      (fun row secret output ↦ realPointMass_nonneg (rowChannel row secret) output)
      rowReference alpha secret]
    exact productRenyiMoment_le_exp_totalEnergy
      (fun row secret output ↦ realPointMass (rowChannel row secret) output)
      rowReference alpha coefficient certificate secret
  · exact prior_max

/-- **Subgaussian conditional Renyi theorem (equation (6)).**  The conclusion is stated as an
exponential probability bound, which is equivalent to the logarithmic statement whenever the
guessing probability is positive and remains meaningful at zero. -/
theorem conditionalRenyiProductSubgaussianBound
    {Row Secret Output : Type}
    [Fintype Row] [DecidableEq Row]
    [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret)
    (rowChannel : Row → Secret → ProbComp Output)
    (completeChannel : Secret → ProbComp (Row → Output))
    (product_law : ∀ secret output,
      realPointMass (completeChannel secret) output =
        productLikelihood
          (fun row secret output ↦ realPointMass (rowChannel row secret) output)
          secret output)
    (rowReference : Row → PositiveProbabilityTable Output)
    (entropy r : ℝ) (hr : 0 < r)
    (rowEnergy : RenyiRowEnergyCertificate Row Secret Output
      (fun row secret output ↦ realPointMass (rowChannel row secret) output)
      rowReference (1 + r) ((1 + r) * r / 2))
    (concentration : SubgaussianEnergyCertificate prior rowEnergy.totalEnergy)
    (prior_max : ∀ secret,
      realPointMass prior secret ≤ Real.exp (-entropy)) :
    (conditionalGuessingProbability
      (conditionalChannelJoint prior completeChannel)).toReal ≤
      Real.exp
        (-r / (1 + r) * entropy +
          r / 2 * concentration.mean +
          (1 + r) * r ^ 2 / 32 * concentration.varianceProxy) := by
  let alpha : ℝ := 1 + r
  let kappa : ℝ := (1 + r) * r / 2
  have halpha : 1 < alpha := by unfold alpha; linarith
  have halphaPos : 0 < alpha := lt_trans zero_lt_one halpha
  have hkappa : 0 ≤ kappa := by
    unfold kappa
    positivity
  have hmoment := concentration.exponentialEnergyMoment_le kappa hkappa
  have hmomentNonneg :
      0 ≤ exponentialEnergyMoment prior rowEnergy.totalEnergy kappa := by
    unfold exponentialEnergyMoment finiteExpectation
    exact Finset.sum_nonneg fun secret _ ↦
      mul_nonneg (realPointMass_nonneg prior secret) (Real.exp_nonneg _)
  calc
    (conditionalGuessingProbability
      (conditionalChannelJoint prior completeChannel)).toReal ≤
        Real.exp (-((alpha - 1) / alpha) * entropy) *
          exponentialEnergyMoment prior rowEnergy.totalEnergy kappa ^
            (1 / alpha) := by
      exact conditionalRenyiProductEnergyEntropyBound prior rowChannel completeChannel
        product_law rowReference alpha kappa entropy halpha rowEnergy prior_max
    _ ≤ Real.exp (-((alpha - 1) / alpha) * entropy) *
        Real.exp (kappa * concentration.mean +
          kappa ^ 2 * concentration.varianceProxy / 8) ^ (1 / alpha) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hmomentNonneg hmoment (by positivity))
        (Real.exp_nonneg _)
    _ = Real.exp
        (-r / (1 + r) * entropy +
          r / 2 * concentration.mean +
          (1 + r) * r ^ 2 / 32 * concentration.varianceProxy) := by
      rw [← Real.exp_mul, ← Real.exp_add]
      congr 1
      unfold alpha kappa
      field_simp [ne_of_gt (by linarith : 0 < 1 + r)]
      ring

/-! ## Explicit exponential margin -/

/-- The normalized exponent calculation behind equations (7)--(9).  The hypothesis `rChoice`
is exactly the useful property of the displayed minimum in equation (8). -/
theorem normalizedSubgaussianExponent_le
    (h u v delta r : ℝ)
    (hh : 0 ≤ h) (hv : 0 ≤ v)
    (hr : 0 < r) (hr_le_one : r ≤ 1)
    (delta_eq : delta = h - u / 2)
    (rChoice : r * (h + v / 16) ≤ delta / 2) :
    -r / (1 + r) * h + r / 2 * u +
        (1 + r) * r ^ 2 / 32 * v ≤
      -r * delta / 2 := by
  have hden : 0 < 1 + r := by linarith
  have hentropy :
      -r / (1 + r) * h ≤ -r * h + r ^ 2 * h := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hden).2
    have hcube : 0 ≤ r ^ 3 * h :=
      mul_nonneg (pow_nonneg hr.le 3) hh
    nlinarith
  have hvariance :
      (1 + r) * r ^ 2 / 32 * v ≤ r ^ 2 / 16 * v := by
    have hnonneg : 0 ≤ r ^ 2 * v * (1 - r) := by positivity
    nlinarith
  have hchoiceMul := mul_le_mul_of_nonneg_left rChoice hr.le
  calc
    -r / (1 + r) * h + r / 2 * u +
        (1 + r) * r ^ 2 / 32 * v ≤
      (-r * h + r ^ 2 * h) + r / 2 * u + r ^ 2 / 16 * v := by
        linarith
    _ = -r * delta + r ^ 2 * (h + v / 16) := by
      rw [delta_eq]
      ring
    _ ≤ -r * delta + r * (delta / 2) := by
      nlinarith
    _ = -r * delta / 2 := by ring

/-- The displayed parameter choice in equation (8). -/
noncomputable def renyiSlack (delta h v : ℝ) : ℝ :=
  min 1 (delta / (2 * (h + v / 16)))

theorem renyiSlack_pos
    (delta h v : ℝ) (hdelta : 0 < delta) (hden : 0 < h + v / 16) :
    0 < renyiSlack delta h v := by
  unfold renyiSlack
  exact lt_min zero_lt_one (div_pos hdelta (by positivity))

theorem renyiSlack_le_one (delta h v : ℝ) :
    renyiSlack delta h v ≤ 1 :=
  min_le_left _ _

theorem renyiSlack_mul_le_half
    (delta h v : ℝ) (hden : 0 < h + v / 16) :
    renyiSlack delta h v * (h + v / 16) ≤ delta / 2 := by
  have hmin : renyiSlack delta h v ≤ delta / (2 * (h + v / 16)) :=
    min_le_right _ _
  calc
    renyiSlack delta h v * (h + v / 16) ≤
        (delta / (2 * (h + v / 16))) * (h + v / 16) :=
      mul_le_mul_of_nonneg_right hmin hden.le
    _ = delta / 2 := by
      have hlinear : h * 16 + v ≠ 0 := by nlinarith
      field_simp [hlinear]

/-- Convert an exponential probability bound to the paper's logarithmic notation whenever the
probability is positive. -/
theorem log_le_of_pos_of_le_exp (probability exponent : ℝ)
    (positive : 0 < probability) (bound : probability ≤ Real.exp exponent) :
    Real.log probability ≤ exponent :=
  (Real.log_le_iff_le_exp positive).2 bound

/-- A uniform finite prior has min-entropy equal to the logarithm of its support cardinality. -/
theorem uniformPrior_pointMass_eq_exp_neg_logCard
    {Secret : Type} [Fintype Secret] [Nonempty Secret] [DecidableEq Secret]
    (prior : ProbComp Secret)
    (uniform : ∀ secret,
      realPointMass prior secret = 1 / (Fintype.card Secret : ℝ))
    (secret : Secret) :
    realPointMass prior secret =
      Real.exp (-Real.log (Fintype.card Secret : ℝ)) := by
  have hcard : (0 : ℝ) < Fintype.card Secret := by
    exact_mod_cast Fintype.card_pos
  rw [uniform, Real.exp_neg, Real.exp_log hcard]
  simp [one_div]

/-- Scale the normalized margin by the dimension and by descriptor-conditioned entropy, mean,
and variance bounds. -/
theorem subgaussianExponent_le_explicit
    (n h u v delta r entropy mean varianceProxy : ℝ)
    (hn : 0 ≤ n) (hh : 0 ≤ h) (hv : 0 ≤ v)
    (hr : 0 < r) (hr_le_one : r ≤ 1)
    (delta_eq : delta = h - u / 2)
    (rChoice : r * (h + v / 16) ≤ delta / 2)
    (entropy_lower : n * h ≤ entropy)
    (mean_upper : mean ≤ n * u)
    (variance_upper : varianceProxy ≤ n * v) :
    -r / (1 + r) * entropy + r / 2 * mean +
        (1 + r) * r ^ 2 / 32 * varianceProxy ≤
      -n * r * delta / 2 := by
  have hden : 0 < 1 + r := by linarith
  have hentropyCoeff : -r / (1 + r) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hr.le) hden.le
  have hmeanCoeff : 0 ≤ r / 2 := by positivity
  have hvarianceCoeff : 0 ≤ (1 + r) * r ^ 2 / 32 := by positivity
  have hentropyTerm :=
    mul_le_mul_of_nonpos_left entropy_lower hentropyCoeff
  have hmeanTerm := mul_le_mul_of_nonneg_left mean_upper hmeanCoeff
  have hvarianceTerm :=
    mul_le_mul_of_nonneg_left variance_upper hvarianceCoeff
  have hnormalized := normalizedSubgaussianExponent_le
    h u v delta r hh hv hr hr_le_one delta_eq rChoice
  calc
    -r / (1 + r) * entropy + r / 2 * mean +
        (1 + r) * r ^ 2 / 32 * varianceProxy ≤
      n * (-r / (1 + r) * h + r / 2 * u +
        (1 + r) * r ^ 2 / 32 * v) := by
      linarith
    _ ≤ n * (-r * delta / 2) :=
      mul_le_mul_of_nonneg_left hnormalized hn
    _ = -n * r * delta / 2 := by ring

/-- **Explicit exponential theorem (equation (9)).** -/
theorem conditionalRenyiProductExplicitBound
    {Row Secret Output : Type}
    [Fintype Row] [DecidableEq Row]
    [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret)
    (rowChannel : Row → Secret → ProbComp Output)
    (completeChannel : Secret → ProbComp (Row → Output))
    (product_law : ∀ secret output,
      realPointMass (completeChannel secret) output =
        productLikelihood
          (fun row secret output ↦ realPointMass (rowChannel row secret) output)
          secret output)
    (rowReference : Row → PositiveProbabilityTable Output)
    (entropy n h u v delta r : ℝ)
    (rowEnergy : RenyiRowEnergyCertificate Row Secret Output
      (fun row secret output ↦ realPointMass (rowChannel row secret) output)
      rowReference (1 + r) ((1 + r) * r / 2))
    (concentration : SubgaussianEnergyCertificate prior rowEnergy.totalEnergy)
    (prior_max : ∀ secret,
      realPointMass prior secret ≤ Real.exp (-entropy))
    (hn : 0 ≤ n) (hh : 0 ≤ h) (hv : 0 ≤ v)
    (hr : 0 < r) (hr_le_one : r ≤ 1)
    (delta_eq : delta = h - u / 2)
    (rChoice : r * (h + v / 16) ≤ delta / 2)
    (entropy_lower : n * h ≤ entropy)
    (mean_upper : concentration.mean ≤ n * u)
    (variance_upper : concentration.varianceProxy ≤ n * v) :
    (conditionalGuessingProbability
      (conditionalChannelJoint prior completeChannel)).toReal ≤
      Real.exp (-n * r * delta / 2) := by
  refine (conditionalRenyiProductSubgaussianBound prior rowChannel completeChannel
    product_law rowReference entropy r hr rowEnergy concentration prior_max).trans ?_
  exact Real.exp_le_exp.mpr
    (subgaussianExponent_le_explicit n h u v delta r entropy
      concentration.mean concentration.varianceProxy hn hh hv hr hr_le_one
      delta_eq rChoice entropy_lower mean_upper variance_upper)

/-- Equation (9) with `r` instantiated by the displayed minimum in equation (8). -/
theorem conditionalRenyiProductExplicitBound_renyiSlack
    {Row Secret Output : Type}
    [Fintype Row] [DecidableEq Row]
    [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret)
    (rowChannel : Row → Secret → ProbComp Output)
    (completeChannel : Secret → ProbComp (Row → Output))
    (product_law : ∀ secret output,
      realPointMass (completeChannel secret) output =
        productLikelihood
          (fun row secret output ↦ realPointMass (rowChannel row secret) output)
          secret output)
    (rowReference : Row → PositiveProbabilityTable Output)
    (entropy n h u v delta : ℝ)
    (rowEnergy : RenyiRowEnergyCertificate Row Secret Output
      (fun row secret output ↦ realPointMass (rowChannel row secret) output)
      rowReference (1 + renyiSlack delta h v)
        ((1 + renyiSlack delta h v) * renyiSlack delta h v / 2))
    (concentration : SubgaussianEnergyCertificate prior rowEnergy.totalEnergy)
    (prior_max : ∀ secret,
      realPointMass prior secret ≤ Real.exp (-entropy))
    (hn : 0 ≤ n) (hh : 0 ≤ h) (hv : 0 ≤ v)
    (hdelta : 0 < delta) (hden : 0 < h + v / 16)
    (delta_eq : delta = h - u / 2)
    (entropy_lower : n * h ≤ entropy)
    (mean_upper : concentration.mean ≤ n * u)
    (variance_upper : concentration.varianceProxy ≤ n * v) :
    (conditionalGuessingProbability
      (conditionalChannelJoint prior completeChannel)).toReal ≤
      Real.exp (-n * renyiSlack delta h v * delta / 2) := by
  exact conditionalRenyiProductExplicitBound prior rowChannel completeChannel
    product_law rowReference entropy n h u v delta (renyiSlack delta h v)
    rowEnergy concentration prior_max hn hh hv
    (renyiSlack_pos delta h v hdelta hden)
    (renyiSlack_le_one delta h v) delta_eq
    (renyiSlack_mul_le_half delta h v hden)
    entropy_lower mean_upper variance_upper

/-! ## Fixed-weight conditioning -/

/-- A finite conditioning certificate records the only point-mass fact used in equation (14).
For the fixed-weight ternary law, `eventMass` is the binomial point probability `p_w`. -/
structure ConditioningMassCertificate
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (conditioned independent : ProbComp Secret) where
  eventMass : ℝ
  eventMass_pos : 0 < eventMass
  pointMass_le : ∀ secret,
    realPointMass conditioned secret ≤
      realPointMass independent secret / eventMass

/-- Equation (14) for every nonnegative function. -/
theorem ConditioningMassCertificate.finiteExpectation_le
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    {conditioned independent : ProbComp Secret}
    (certificate : ConditioningMassCertificate conditioned independent)
    (value : Secret → ℝ) (value_nonneg : ∀ secret, 0 ≤ value secret) :
    finiteExpectation conditioned value ≤
      certificate.eventMass⁻¹ * finiteExpectation independent value := by
  unfold finiteExpectation
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro secret _
  calc
    realPointMass conditioned secret * value secret ≤
        (realPointMass independent secret / certificate.eventMass) * value secret :=
      mul_le_mul_of_nonneg_right (certificate.pointMass_le secret)
        (value_nonneg secret)
    _ = certificate.eventMass⁻¹ *
        (realPointMass independent secret * value secret) := by
      rw [div_eq_mul_inv]
      ring

/-- Conditioning costs exactly one inverse event mass in the exponential energy moment. -/
theorem ConditioningMassCertificate.exponentialEnergyMoment_le
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    {conditioned independent : ProbComp Secret}
    (certificate : ConditioningMassCertificate conditioned independent)
    (energy : Secret → ℝ) (t : ℝ) :
    exponentialEnergyMoment conditioned energy t ≤
      certificate.eventMass⁻¹ *
        exponentialEnergyMoment independent energy t :=
  certificate.finiteExpectation_le _ fun _ ↦ Real.exp_nonneg _

/-- **Fixed-weight ternary conditioning theorem (equation (15)).**  A concentration certificate
for the independent comparison law transfers to the conditioned law with the exact
`log(1 / p_w) / (1+r)` penalty. -/
theorem conditionalRenyiProductConditionedSubgaussianBound
    {Row Secret Output : Type}
    [Fintype Row] [DecidableEq Row]
    [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (conditionedPrior independentPrior : ProbComp Secret)
    (rowChannel : Row → Secret → ProbComp Output)
    (completeChannel : Secret → ProbComp (Row → Output))
    (product_law : ∀ secret output,
      realPointMass (completeChannel secret) output =
        productLikelihood
          (fun row secret output ↦ realPointMass (rowChannel row secret) output)
          secret output)
    (rowReference : Row → PositiveProbabilityTable Output)
    (entropy r : ℝ) (hr : 0 < r)
    (rowEnergy : RenyiRowEnergyCertificate Row Secret Output
      (fun row secret output ↦ realPointMass (rowChannel row secret) output)
      rowReference (1 + r) ((1 + r) * r / 2))
    (conditioning : ConditioningMassCertificate conditionedPrior independentPrior)
    (concentration : SubgaussianEnergyCertificate
      independentPrior rowEnergy.totalEnergy)
    (prior_max : ∀ secret,
      realPointMass conditionedPrior secret ≤ Real.exp (-entropy)) :
    (conditionalGuessingProbability
      (conditionalChannelJoint conditionedPrior completeChannel)).toReal ≤
      Real.exp
        (-r / (1 + r) * entropy +
          r / 2 * concentration.mean +
          (1 + r) * r ^ 2 / 32 * concentration.varianceProxy +
          1 / (1 + r) * Real.log (1 / conditioning.eventMass)) := by
  let alpha : ℝ := 1 + r
  let kappa : ℝ := (1 + r) * r / 2
  have halpha : 1 < alpha := by unfold alpha; linarith
  have halphaPos : 0 < alpha := lt_trans zero_lt_one halpha
  have hkappa : 0 ≤ kappa := by unfold kappa; positivity
  have hindependent := concentration.exponentialEnergyMoment_le kappa hkappa
  have hconditioned := conditioning.exponentialEnergyMoment_le
    rowEnergy.totalEnergy kappa
  have hmoment :
      exponentialEnergyMoment conditionedPrior rowEnergy.totalEnergy kappa ≤
        conditioning.eventMass⁻¹ *
          Real.exp (kappa * concentration.mean +
            kappa ^ 2 * concentration.varianceProxy / 8) :=
    hconditioned.trans
      (mul_le_mul_of_nonneg_left hindependent
        (inv_nonneg.mpr conditioning.eventMass_pos.le))
  have hmomentNonneg :
      0 ≤ exponentialEnergyMoment conditionedPrior rowEnergy.totalEnergy kappa := by
    unfold exponentialEnergyMoment finiteExpectation
    exact Finset.sum_nonneg fun secret _ ↦
      mul_nonneg (realPointMass_nonneg conditionedPrior secret) (Real.exp_nonneg _)
  calc
    (conditionalGuessingProbability
      (conditionalChannelJoint conditionedPrior completeChannel)).toReal ≤
        Real.exp (-((alpha - 1) / alpha) * entropy) *
          exponentialEnergyMoment conditionedPrior rowEnergy.totalEnergy kappa ^
            (1 / alpha) := by
      exact conditionalRenyiProductEnergyEntropyBound conditionedPrior rowChannel
        completeChannel product_law rowReference alpha kappa entropy halpha
        rowEnergy prior_max
    _ ≤ Real.exp (-((alpha - 1) / alpha) * entropy) *
        (conditioning.eventMass⁻¹ *
          Real.exp (kappa * concentration.mean +
            kappa ^ 2 * concentration.varianceProxy / 8)) ^ (1 / alpha) := by
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow hmomentNonneg hmoment (by positivity))
        (Real.exp_nonneg _)
    _ = Real.exp
        (-r / (1 + r) * entropy +
          r / 2 * concentration.mean +
          (1 + r) * r ^ 2 / 32 * concentration.varianceProxy +
          1 / (1 + r) * Real.log (1 / conditioning.eventMass)) := by
      have hinvPos : 0 < conditioning.eventMass⁻¹ :=
        inv_pos.mpr conditioning.eventMass_pos
      rw [Real.mul_rpow hinvPos.le (Real.exp_nonneg _)]
      rw [Real.rpow_def_of_pos hinvPos]
      rw [show conditioning.eventMass⁻¹ = 1 / conditioning.eventMass by
        rw [one_div]]
      rw [← Real.exp_mul, ← Real.exp_add, ← Real.exp_add]
      congr 1
      unfold alpha kappa
      field_simp [ne_of_gt (by linarith : 0 < 1 + r)]
      ring

/-! ## Finite coordinate oscillations and quadratic codebook algebra -/

/-- Exact finite coordinate oscillation from equation (11).  Invalid pairs contribute zero;
valid pairs include the diagonal, so this is precisely the maximum over valid pairs and is a
finite target for exact or interval certification. -/
def coordinateOscillation
    {Coordinate Alphabet : Type}
    [Fintype Coordinate] [DecidableEq Coordinate]
    [Fintype Alphabet] [Nonempty Alphabet] [DecidableEq Alphabet]
    (energy : (Coordinate → Alphabet) → ℝ) (changed : Coordinate) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun left ↦
    Finset.univ.sup' Finset.univ_nonempty fun right ↦
      if ∀ coordinate, coordinate ≠ changed → left coordinate = right coordinate
      then |energy left - energy right|
      else 0

/-- Every one-coordinate change is bounded by the computed oscillation. -/
theorem abs_energy_sub_le_coordinateOscillation
    {Coordinate Alphabet : Type}
    [Fintype Coordinate] [DecidableEq Coordinate]
    [Fintype Alphabet] [Nonempty Alphabet] [DecidableEq Alphabet]
    (energy : (Coordinate → Alphabet) → ℝ) (changed : Coordinate)
    (left right : Coordinate → Alphabet)
    (agree : ∀ coordinate, coordinate ≠ changed →
      left coordinate = right coordinate) :
    |energy left - energy right| ≤ coordinateOscillation energy changed := by
  classical
  unfold coordinateOscillation
  calc
    |energy left - energy right| =
        (if ∀ coordinate, coordinate ≠ changed →
            left coordinate = right coordinate
          then |energy left - energy right| else 0) := (if_pos agree).symm
    _ ≤ Finset.univ.sup' Finset.univ_nonempty (fun candidate ↦
        if ∀ coordinate, coordinate ≠ changed →
            left coordinate = candidate coordinate
          then |energy left - energy candidate| else 0) :=
      Finset.le_sup'
        (fun candidate : Coordinate → Alphabet ↦
          if ∀ coordinate, coordinate ≠ changed →
              left coordinate = candidate coordinate
            then |energy left - energy candidate| else 0)
        (Finset.mem_univ right)
    _ ≤ Finset.univ.sup' Finset.univ_nonempty (fun candidate ↦
        Finset.univ.sup' Finset.univ_nonempty (fun other ↦
          if ∀ coordinate, coordinate ≠ changed →
              candidate coordinate = other coordinate
            then |energy candidate - energy other| else 0)) :=
      Finset.le_sup'
        (fun candidate : Coordinate → Alphabet ↦
          Finset.univ.sup' Finset.univ_nonempty (fun other ↦
            if ∀ coordinate, coordinate ≠ changed →
                candidate coordinate = other coordinate
              then |energy candidate - energy other| else 0))
        (Finset.mem_univ left)

theorem coordinateOscillation_nonneg
    {Coordinate Alphabet : Type}
    [Fintype Coordinate] [DecidableEq Coordinate]
    [Fintype Alphabet] [Nonempty Alphabet] [DecidableEq Alphabet]
    (energy : (Coordinate → Alphabet) → ℝ) (changed : Coordinate) :
    0 ≤ coordinateOscillation energy changed := by
  let secret : Coordinate → Alphabet := fun _ ↦ Classical.choice inferInstance
  have hbound := abs_energy_sub_le_coordinateOscillation
    energy changed secret secret (fun _ _ ↦ rfl)
  simpa [secret] using hbound

/-- The variance proxy `sum_i Delta_i^2` from equation (12). -/
def coordinateOscillationVariance
    {Coordinate Alphabet : Type}
    [Fintype Coordinate] [DecidableEq Coordinate]
    [Fintype Alphabet] [Nonempty Alphabet] [DecidableEq Alphabet]
    (energy : (Coordinate → Alphabet) → ℝ) : ℝ :=
  ∑ coordinate, coordinateOscillation energy coordinate ^ 2

theorem coordinateOscillationVariance_nonneg
    {Coordinate Alphabet : Type}
    [Fintype Coordinate] [DecidableEq Coordinate]
    [Fintype Alphabet] [Nonempty Alphabet] [DecidableEq Alphabet]
    (energy : (Coordinate → Alphabet) → ℝ) :
    0 ≤ coordinateOscillationVariance energy := by
  exact Finset.sum_nonneg fun coordinate _ ↦ sq_nonneg _

/-- Proof-carrying boundary for the Hoeffding/Doob iteration in equation (12).  Coordinate
oscillations and their squared sum are native finite maxima; this field records the analytic
martingale MGF argument for the selected independent-coordinate sampler. -/
structure BoundedDifferencesMGFCertificate
    {Coordinate Alphabet : Type}
    [Fintype Coordinate] [DecidableEq Coordinate]
    [Fintype Alphabet] [Nonempty Alphabet] [DecidableEq Alphabet]
    (prior : ProbComp (Coordinate → Alphabet))
    (energy : (Coordinate → Alphabet) → ℝ) where
  centered_mgf_le : ∀ t, 0 ≤ t →
    centeredExponentialMoment prior energy (finiteExpectation prior energy) t ≤
      Real.exp (t ^ 2 * coordinateOscillationVariance energy / 8)

/-- A bounded-differences certificate instantiates the generic subgaussian interface with the
exact finite sum of squared coordinate oscillations. -/
def BoundedDifferencesMGFCertificate.toSubgaussian
    {Coordinate Alphabet : Type}
    [Fintype Coordinate] [DecidableEq Coordinate]
    [Fintype Alphabet] [Nonempty Alphabet] [DecidableEq Alphabet]
    {prior : ProbComp (Coordinate → Alphabet)}
    {energy : (Coordinate → Alphabet) → ℝ}
    (certificate : BoundedDifferencesMGFCertificate prior energy) :
    SubgaussianEnergyCertificate prior energy where
  mean := finiteExpectation prior energy
  varianceProxy := coordinateOscillationVariance energy
  varianceProxy_nonneg := coordinateOscillationVariance_nonneg energy
  mean_eq_expectation := rfl
  centered_mgf_le := certificate.centered_mgf_le

/-- Equation (20) in any commutative ring. -/
theorem quadraticSquare_update
    {R : Type} [CommRing R] (secret delta basis : R) :
    (secret + delta * basis) ^ 2 - secret ^ 2 =
      2 * delta * basis * secret + delta ^ 2 * basis ^ 2 := by
  ring

/-- The normalized quadratic codebook energy in equation (16).  `linearPart` and
`quadraticPart` represent `M_w s` and `M_g Q(s)` respectively. -/
def quadraticCodebookEnergy
    {Row Secret E : Type} [Fintype Row] [NormedAddCommGroup E]
    (sigma : ℝ) (linearPart quadraticPart : Row → Secret → E)
    (center : Row → E) (secret : Secret) : ℝ :=
  (1 / sigma ^ 2) *
    ∑ row, ‖linearPart row secret + quadraticPart row secret - center row‖ ^ 2

theorem quadraticCodebookEnergy_nonneg
    {Row Secret E : Type} [Fintype Row] [NormedAddCommGroup E]
    (sigma : ℝ) (linearPart quadraticPart : Row → Secret → E)
    (center : Row → E) (secret : Secret) :
    0 ≤ quadraticCodebookEnergy sigma linearPart quadraticPart center secret := by
  unfold quadraticCodebookEnergy
  exact mul_nonneg (div_nonneg zero_le_one (sq_nonneg sigma))
    (Finset.sum_nonneg fun row _ ↦ sq_nonneg _)

/-- Hilbert-space form of the sensitivity inequality in equation (21). -/
theorem abs_norm_add_sq_sub_norm_sq_le
    {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (value increment : E) :
    |‖value + increment‖ ^ 2 - ‖value‖ ^ 2| ≤
      2 * ‖value‖ * ‖increment‖ + ‖increment‖ ^ 2 := by
  rw [norm_add_sq_real]
  have hinner := abs_real_inner_le_norm value increment
  calc
    |‖value‖ ^ 2 + 2 * inner ℝ value increment + ‖increment‖ ^ 2 -
        ‖value‖ ^ 2| =
      |2 * inner ℝ value increment + ‖increment‖ ^ 2| := by ring_nf
    _ ≤ |2 * inner ℝ value increment| + |‖increment‖ ^ 2| :=
      abs_add_le _ _
    _ = 2 * |inner ℝ value increment| + ‖increment‖ ^ 2 := by
      rw [abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (sq_nonneg ‖increment‖)]
    _ ≤ 2 * (‖value‖ * ‖increment‖) + ‖increment‖ ^ 2 := by
      gcongr
    _ = 2 * ‖value‖ * ‖increment‖ + ‖increment‖ ^ 2 := by ring

/-- If `D` is the exact change of the normalized stacked codeword `L`, its energy change obeys
the right side of equation (21). -/
theorem codebookEnergy_change_le
    {Secret E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (codeword : Secret → E) (left right : Secret) (increment : E)
    (update : codeword right = codeword left + increment) :
    |‖codeword right‖ ^ 2 - ‖codeword left‖ ^ 2| ≤
      2 * ‖codeword left‖ * ‖increment‖ + ‖increment‖ ^ 2 := by
  rw [update]
  exact abs_norm_add_sq_sub_norm_sq_le _ _

/-! ## Descriptor/leakage averaging and coherent RNS rows -/

/-- Equation (23): integrate the descriptor-conditioned exponential bounds against the actual
descriptor/leakage law. -/
theorem descriptorAveragedExponentialGuessingBound
    {Descriptor Secret Output : Type}
    [Fintype Descriptor] [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Descriptor] [DecidableEq Secret] [DecidableEq Output]
    (descriptorSampler : ProbComp Descriptor)
    (prior : Descriptor → ProbComp Secret)
    (channel : Descriptor → Secret → ProbComp Output)
    (n : ℝ) (beta : Descriptor → ℝ)
    (pointwise : ∀ descriptor,
      (conditionalGuessingProbability
        (conditionalChannelJoint (prior descriptor) (channel descriptor))).toReal ≤
          Real.exp (-n * beta descriptor)) :
    (conditionalGuessingProbability
      (contextualChannelJoint descriptorSampler prior channel)).toReal ≤
      ∑ descriptor, realPointMass descriptorSampler descriptor *
        Real.exp (-n * beta descriptor) := by
  exact descriptorAveragedGuessingBound descriptorSampler prior channel
    (fun descriptor ↦ Real.exp (-n * beta descriptor)) pointwise

/-- Equation (24): bad descriptors are charged by their actual mass and good descriptors by one
common exponent.  No worst-case replacement is made before this split. -/
theorem descriptorBadSetExponentialGuessingBound
    {Descriptor Secret Output : Type}
    [Fintype Descriptor] [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Descriptor] [DecidableEq Secret] [DecidableEq Output]
    (descriptorSampler : ProbComp Descriptor)
    (prior : Descriptor → ProbComp Secret)
    (channel : Descriptor → Secret → ProbComp Output)
    (bad : Descriptor → Prop) [DecidablePred bad]
    (n epsilon beta0 : ℝ) (beta : Descriptor → ℝ)
    (hn : 0 ≤ n)
    (badMass :
      (∑ descriptor ∈ Finset.univ.filter bad,
        realPointMass descriptorSampler descriptor) ≤ epsilon)
    (goodBeta : ∀ descriptor, ¬bad descriptor → beta0 ≤ beta descriptor)
    (pointwise : ∀ descriptor,
      (conditionalGuessingProbability
        (conditionalChannelJoint (prior descriptor) (channel descriptor))).toReal ≤
          Real.exp (-n * beta descriptor)) :
    (conditionalGuessingProbability
      (contextualChannelJoint descriptorSampler prior channel)).toReal ≤
      epsilon + Real.exp (-n * beta0) := by
  rw [contextualGuessingProbability_toReal_eq_average]
  have hcellMass : ∀ _index : Unit,
      (∑ descriptor ∈ Finset.univ.filter
        (fun descriptor ↦ ¬bad descriptor ∧ () = _index),
          realPointMass descriptorSampler descriptor) ≤ 1 := by
    intro index
    calc
      (∑ descriptor ∈ Finset.univ.filter
          (fun descriptor ↦ ¬bad descriptor ∧ () = index),
          realPointMass descriptorSampler descriptor) ≤
        ∑ descriptor, realPointMass descriptorSampler descriptor := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · exact Finset.filter_subset _ _
          · exact fun descriptor _ _ ↦ realPointMass_nonneg descriptorSampler descriptor
      _ = 1 := by
        unfold realPointMass
        exact sum_probOutput_toReal_eq_one descriptorSampler
  have h := finiteIntervalExpectationBound
    (weight := fun descriptor ↦ realPointMass descriptorSampler descriptor)
    (pointwise := fun descriptor ↦
      (conditionalGuessingProbability
        (conditionalChannelJoint (prior descriptor) (channel descriptor))).toReal)
    (bad := bad) (cell := fun _ ↦ ()) (beta := epsilon)
    (cellMassUpper := fun _ : Unit ↦ 1)
    (cellBound := fun _ : Unit ↦ Real.exp (-n * beta0))
    (fun descriptor ↦ realPointMass_nonneg descriptorSampler descriptor)
    (fun descriptor ↦ ENNReal.toReal_mono ENNReal.one_ne_top
      (conditionalGuessingProbability_le_one _))
    (fun _ ↦ Real.exp_nonneg _)
    badMass hcellMass
    (fun descriptor hgood ↦ pointwise descriptor |>.trans
      (Real.exp_le_exp.mpr (by
        have := goodBeta descriptor hgood
        nlinarith)))
  simpa [realPointMass] using h

/-- The independent product is over evaluation-key rows.  Specializing each row output to a
complete coherent CRT pair makes explicit that no independence between the two components (or
between any limbs encoded in `Rest`) is assumed. -/
theorem conditionalRenyiProductGuessingBound_coherentRows
    {Row Secret Star Rest : Type}
    [Fintype Row] [DecidableEq Row]
    [Fintype Secret] [Nonempty Secret] [Fintype Star] [Fintype Rest]
    [DecidableEq Secret] [DecidableEq Star] [DecidableEq Rest]
    (prior : ProbComp Secret)
    (rowChannel : Row → Secret → ProbComp (CoherentObservation Star Rest))
    (completeChannel : Secret →
      ProbComp (Row → CoherentObservation Star Rest))
    (product_law : ∀ secret output,
      realPointMass (completeChannel secret) output =
        productLikelihood
          (fun row secret output ↦ realPointMass (rowChannel row secret) output)
          secret output)
    (rowReference : Row →
      PositiveProbabilityTable (CoherentObservation Star Rest))
    (alpha : ℝ) (halpha : 1 < alpha) :
    (conditionalGuessingProbability
      (conditionalChannelJoint prior completeChannel)).toReal ≤
      (∑ secret,
          realPointMass prior secret ^ alpha *
            ∏ row,
              finiteRenyiMoment alpha
                (fun output ↦ realPointMass (rowChannel row secret) output)
                (rowReference row).mass) ^ (1 / alpha) :=
  conditionalRenyiProductGuessingBound prior rowChannel completeChannel
    product_law rowReference alpha halpha

/-! ## Continuous Gaussian and product-Laplace reference certificates -/

/-- Proof-carrying boundary for the equal-covariance Gaussian Renyi identity.  Mathlib's finite
`ProbComp` does not model continuous densities, so an implementation supplies the integrated
moment equality; its conversion to the row-energy theorem is native. -/
structure EqualCovarianceGaussianRowCertificate
    (Row Secret Output : Type) [Fintype Output]
    (rowLikelihood : Row → Secret → Output → ℝ)
    (rowReference : Row → PositiveProbabilityTable Output)
    (alpha : ℝ) where
  likelihood_nonneg : ∀ row secret output, 0 ≤ rowLikelihood row secret output
  mahalanobisEnergy : Row → Secret → ℝ
  mahalanobisEnergy_nonneg : ∀ row secret, 0 ≤ mahalanobisEnergy row secret
  moment_eq : ∀ row secret,
    finiteRenyiMoment alpha (rowLikelihood row secret) (rowReference row).mass =
      Real.exp
        (alpha * (alpha - 1) / 2 * mahalanobisEnergy row secret)

/-- Install the equal-covariance identity as the row energy certificate used by Theorem 2. -/
def EqualCovarianceGaussianRowCertificate.toRenyiRowEnergy
    {Row Secret Output : Type} [Fintype Output]
    {rowLikelihood : Row → Secret → Output → ℝ}
    {rowReference : Row → PositiveProbabilityTable Output}
    {alpha : ℝ}
    (certificate : EqualCovarianceGaussianRowCertificate Row Secret Output
      rowLikelihood rowReference alpha) :
    RenyiRowEnergyCertificate Row Secret Output rowLikelihood rowReference alpha
      (alpha * (alpha - 1) / 2) where
  likelihood_nonneg := certificate.likelihood_nonneg
  energy := certificate.mahalanobisEnergy
  energy_nonneg := certificate.mahalanobisEnergy_nonneg
  moment_le := fun row secret ↦ (certificate.moment_eq row secret).le

/-- The explicit constant in equations (25)--(26). -/
noncomputable def laplaceRenyiConstant
    (alpha scale : ℝ) (dimension : ℕ) : ℝ :=
  ((2 * Real.pi) ^ (-alpha / 2) *
      (scale / 2) ^ (1 - alpha) *
      (2 * Real.sqrt (2 * Real.pi / alpha)) *
      Real.exp ((alpha - 1) ^ 2 * scale ^ 2 / (2 * alpha))) ^ dimension

/-- Proof-carrying version of the Gaussian-versus-product-Laplace integral in Lemma 3.  `growth`
is `a_j * ‖m_j(s)‖₁`; the exact closed-form constants can be supplied by
`laplaceRenyiConstant`. -/
structure ProductLaplaceRowCertificate
    (Row Secret Output : Type) [Fintype Output]
    (rowLikelihood : Row → Secret → Output → ℝ)
    (rowReference : Row → PositiveProbabilityTable Output)
    (alpha : ℝ) where
  likelihood_nonneg : ∀ row secret output, 0 ≤ rowLikelihood row secret output
  constant : Row → ℝ
  constant_nonneg : ∀ row, 0 ≤ constant row
  growth : Row → Secret → ℝ
  moment_le : ∀ row secret,
    finiteRenyiMoment alpha (rowLikelihood row secret) (rowReference row).mass ≤
      constant row * Real.exp ((alpha - 1) * growth row secret)

def ProductLaplaceRowCertificate.constantProduct
    {Row Secret Output : Type} [Fintype Row] [Fintype Output]
    {rowLikelihood : Row → Secret → Output → ℝ}
    {rowReference : Row → PositiveProbabilityTable Output}
    {alpha : ℝ}
    (certificate : ProductLaplaceRowCertificate Row Secret Output
      rowLikelihood rowReference alpha) : ℝ :=
  ∏ row, certificate.constant row

def ProductLaplaceRowCertificate.totalGrowth
    {Row Secret Output : Type} [Fintype Row] [Fintype Output]
    {rowLikelihood : Row → Secret → Output → ℝ}
    {rowReference : Row → PositiveProbabilityTable Output}
    {alpha : ℝ}
    (certificate : ProductLaplaceRowCertificate Row Secret Output
      rowLikelihood rowReference alpha) (secret : Secret) : ℝ :=
  ∑ row, certificate.growth row secret

theorem ProductLaplaceRowCertificate.constantProduct_nonneg
    {Row Secret Output : Type} [Fintype Row] [Fintype Output]
    {rowLikelihood : Row → Secret → Output → ℝ}
    {rowReference : Row → PositiveProbabilityTable Output}
    {alpha : ℝ}
    (certificate : ProductLaplaceRowCertificate Row Secret Output
      rowLikelihood rowReference alpha) :
    0 ≤ certificate.constantProduct :=
  Finset.prod_nonneg fun row _ ↦ certificate.constant_nonneg row

theorem ProductLaplaceRowCertificate.productMoment_le
    {Row Secret Output : Type} [Fintype Row] [Fintype Output]
    {rowLikelihood : Row → Secret → Output → ℝ}
    {rowReference : Row → PositiveProbabilityTable Output}
    {alpha : ℝ}
    (certificate : ProductLaplaceRowCertificate Row Secret Output
      rowLikelihood rowReference alpha) (secret : Secret) :
    (∏ row, finiteRenyiMoment alpha (rowLikelihood row secret)
        (rowReference row).mass) ≤
      certificate.constantProduct *
        Real.exp ((alpha - 1) * certificate.totalGrowth secret) := by
  calc
    (∏ row, finiteRenyiMoment alpha (rowLikelihood row secret)
        (rowReference row).mass) ≤
      ∏ row, certificate.constant row *
        Real.exp ((alpha - 1) * certificate.growth row secret) := by
      apply Finset.prod_le_prod
      · intro row _
        exact Finset.sum_nonneg fun output _ ↦ mul_nonneg
          (Real.rpow_nonneg (certificate.likelihood_nonneg row secret output) alpha)
          (Real.rpow_nonneg ((rowReference row).nonneg output) (1 - alpha))
      · intro row _
        exact certificate.moment_le row secret
    _ = certificate.constantProduct *
        Real.exp ((alpha - 1) * certificate.totalGrowth secret) := by
      rw [Finset.prod_mul_distrib, ← Real.exp_sum]
      congr 2
      unfold ProductLaplaceRowCertificate.totalGrowth
      rw [Finset.mul_sum]

/-- Conditional product theorem after the product-Laplace row bound. -/
theorem conditionalRenyiProductLaplaceBound
    {Row Secret Output : Type}
    [Fintype Row] [DecidableEq Row]
    [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret)
    (rowChannel : Row → Secret → ProbComp Output)
    (completeChannel : Secret → ProbComp (Row → Output))
    (product_law : ∀ secret output,
      realPointMass (completeChannel secret) output =
        productLikelihood
          (fun row secret output ↦ realPointMass (rowChannel row secret) output)
          secret output)
    (rowReference : Row → PositiveProbabilityTable Output)
    (alpha : ℝ) (halpha : 1 < alpha)
    (certificate : ProductLaplaceRowCertificate Row Secret Output
      (fun row secret output ↦ realPointMass (rowChannel row secret) output)
      rowReference alpha) :
    (conditionalGuessingProbability
      (conditionalChannelJoint prior completeChannel)).toReal ≤
      (certificate.constantProduct *
        ∑ secret, realPointMass prior secret ^ alpha *
          Real.exp ((alpha - 1) * certificate.totalGrowth secret)) ^
            (1 / alpha) := by
  refine (conditionalRenyiProductGuessingBound prior rowChannel completeChannel
    product_law rowReference alpha halpha).trans ?_
  apply Real.rpow_le_rpow
  · exact Finset.sum_nonneg fun secret _ ↦ mul_nonneg
      (Real.rpow_nonneg (realPointMass_nonneg prior secret) alpha)
      (Finset.prod_nonneg fun row _ ↦ Finset.sum_nonneg fun output _ ↦
        mul_nonneg (Real.rpow_nonneg (realPointMass_nonneg _ _) alpha)
          (Real.rpow_nonneg ((rowReference row).nonneg output) (1 - alpha)))
  · rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro secret _
    calc
      realPointMass prior secret ^ alpha *
          ∏ row, finiteRenyiMoment alpha
            (fun output ↦ realPointMass (rowChannel row secret) output)
            (rowReference row).mass ≤
        realPointMass prior secret ^ alpha *
          (certificate.constantProduct *
            Real.exp ((alpha - 1) * certificate.totalGrowth secret)) := by
        exact mul_le_mul_of_nonneg_left (certificate.productMoment_le secret)
          (Real.rpow_nonneg (realPointMass_nonneg prior secret) alpha)
      _ = certificate.constantProduct *
          (realPointMass prior secret ^ alpha *
            Real.exp ((alpha - 1) * certificate.totalGrowth secret)) := by ring
  · positivity

/-- Finite proof-carrying theta-mass endpoint.  For an actual infinite discrete Gaussian lattice,
constructing `partition_le` is the analytic/lattice-summation obligation corresponding to
equations (27)--(28). -/
structure ThetaMassPartitionCertificate
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (prior : ProbComp Secret) (growth : Secret → ℝ) (alpha : ℝ) where
  rhoSecret : ℝ
  thetaMass : ℝ
  gamma : ℝ
  epsilon : ℝ
  sigmaEffective : ℝ
  constantTerm : ℝ
  linearTerm : ℝ
  rhoSecret_pos : 0 < rhoSecret
  thetaMass_nonneg : 0 ≤ thetaMass
  epsilon_pos : 0 < epsilon
  epsilon_lt_gamma : epsilon < gamma
  sigmaEffective_eq : sigmaEffective = Real.sqrt (Real.pi / (gamma - epsilon))
  partition_le :
    (∑ secret, realPointMass prior secret ^ alpha *
      Real.exp ((alpha - 1) * growth secret)) ≤
      thetaMass / rhoSecret ^ alpha *
        Real.exp ((alpha - 1) * constantTerm +
          (alpha - 1) ^ 2 * linearTerm ^ 2 / (4 * epsilon))

/-- **Discrete-Gaussian/product-Laplace endpoint (equation (29)).**  The row tensorization and
all root/exponent arithmetic are native; only the continuous integral and theta partition
estimate reside in the two explicit certificates. -/
theorem conditionalRenyiProductLaplaceThetaBound
    {Row Secret Output : Type}
    [Fintype Row] [DecidableEq Row]
    [Fintype Secret] [Nonempty Secret] [Fintype Output]
    [DecidableEq Secret] [DecidableEq Output]
    (prior : ProbComp Secret)
    (rowChannel : Row → Secret → ProbComp Output)
    (completeChannel : Secret → ProbComp (Row → Output))
    (product_law : ∀ secret output,
      realPointMass (completeChannel secret) output =
        productLikelihood
          (fun row secret output ↦ realPointMass (rowChannel row secret) output)
          secret output)
    (rowReference : Row → PositiveProbabilityTable Output)
    (alpha : ℝ) (halpha : 1 < alpha)
    (laplace : ProductLaplaceRowCertificate Row Secret Output
      (fun row secret output ↦ realPointMass (rowChannel row secret) output)
      rowReference alpha)
    (theta : ThetaMassPartitionCertificate prior laplace.totalGrowth alpha) :
    (conditionalGuessingProbability
      (conditionalChannelJoint prior completeChannel)).toReal ≤
      laplace.constantProduct ^ (1 / alpha) *
        theta.thetaMass ^ (1 / alpha) / theta.rhoSecret *
          Real.exp
            ((alpha - 1) * theta.constantTerm / alpha +
              (alpha - 1) ^ 2 * theta.linearTerm ^ 2 /
                (4 * alpha * theta.epsilon)) := by
  have halphaPos : 0 < alpha := lt_trans zero_lt_one halpha
  let partition : ℝ :=
    ∑ secret, realPointMass prior secret ^ alpha *
      Real.exp ((alpha - 1) * laplace.totalGrowth secret)
  have hpartitionNonneg : 0 ≤ partition := by
    unfold partition
    exact Finset.sum_nonneg fun secret _ ↦ mul_nonneg
      (Real.rpow_nonneg (realPointMass_nonneg prior secret) alpha)
      (Real.exp_nonneg _)
  let exponent : ℝ :=
    (alpha - 1) * theta.constantTerm +
      (alpha - 1) ^ 2 * theta.linearTerm ^ 2 / (4 * theta.epsilon)
  have hupperNonneg :
      0 ≤ theta.thetaMass / theta.rhoSecret ^ alpha * Real.exp exponent := by
    exact mul_nonneg
      (div_nonneg theta.thetaMass_nonneg
        (Real.rpow_nonneg theta.rhoSecret_pos.le alpha))
      (Real.exp_nonneg _)
  have hpartitionUpper : partition ≤
      theta.thetaMass / theta.rhoSecret ^ alpha * Real.exp exponent := by
    simpa [partition, exponent] using theta.partition_le
  calc
    (conditionalGuessingProbability
      (conditionalChannelJoint prior completeChannel)).toReal ≤
        (laplace.constantProduct * partition) ^ (1 / alpha) := by
      exact conditionalRenyiProductLaplaceBound prior rowChannel completeChannel
        product_law rowReference alpha halpha laplace
    _ ≤ (laplace.constantProduct *
        (theta.thetaMass / theta.rhoSecret ^ alpha * Real.exp exponent)) ^
          (1 / alpha) := by
      exact Real.rpow_le_rpow
        (mul_nonneg laplace.constantProduct_nonneg hpartitionNonneg)
        (mul_le_mul_of_nonneg_left hpartitionUpper laplace.constantProduct_nonneg)
        (by positivity)
    _ = laplace.constantProduct ^ (1 / alpha) *
        theta.thetaMass ^ (1 / alpha) / theta.rhoSecret *
          Real.exp
            ((alpha - 1) * theta.constantTerm / alpha +
              (alpha - 1) ^ 2 * theta.linearTerm ^ 2 /
                (4 * alpha * theta.epsilon)) := by
      have hrhoPowNonneg : 0 ≤ theta.rhoSecret ^ alpha :=
        Real.rpow_nonneg theta.rhoSecret_pos.le alpha
      rw [Real.mul_rpow laplace.constantProduct_nonneg hupperNonneg]
      rw [Real.mul_rpow
        (div_nonneg theta.thetaMass_nonneg hrhoPowNonneg) (Real.exp_nonneg _)]
      rw [Real.div_rpow theta.thetaMass_nonneg hrhoPowNonneg]
      have hrhoRoot :
          (theta.rhoSecret ^ alpha) ^ (1 / alpha) = theta.rhoSecret := by
        rw [← Real.rpow_mul theta.rhoSecret_pos.le]
        field_simp
        simp
      rw [hrhoRoot, ← Real.exp_mul]
      have hexponent : exponent * (1 / alpha) =
          (alpha - 1) * theta.constantTerm / alpha +
            (alpha - 1) ^ 2 * theta.linearTerm ^ 2 /
              (4 * alpha * theta.epsilon) := by
        unfold exponent
        field_simp [ne_of_gt halphaPos, ne_of_gt theta.epsilon_pos]
      rw [hexponent]
      ring

end

end FormalProof4FHE.RLWE.RankOneHNFLossinessRenyi
