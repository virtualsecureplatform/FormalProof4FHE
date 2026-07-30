/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.ConditionalCollision
import FormalProof4FHE.Probability.SquaredBias
import FormalProof4FHE.RLWE.RankOneHNFLossinessSupportAware
import FormalProof4FHE.TFHE.JointSubsetKeyBRKRefined
import Mathlib.Analysis.Complex.Exponential

/-!
# Centered-mixture and covariance-matched joint KSK bounds

This module sharpens the first-order Mahalanobis mixture estimate in
`JointSubsetKeyBRKRefined`.  The Gaussian density calculation is exposed as one explicit
certificate field, while the following steps are proved natively:

* centering cancels the linear term in the Gaussian pair-kernel identity;
* on the unit interaction range, Pearson chi-square is bounded by the independent-pair second
  moment, and hence total variation is bounded by its square root divided by two;
* IID centered ternary secrets give the exact second-order Frobenius expression;
* a canonical exact-Hamming-weight signed-ternary sampler has isotropic variance `weight / n`;
* residual covariance may be subtracted from the simulator's correction covariance, so the
  complete approximate-factorization error has the prescribed covariance.

The certificate boundary is necessary because the finite `ProbComp` API does not supply the
continuous/wrapped/rounded multivariate Gaussian density identity.  No cancellation, finite
moment, matrix, or security-loss calculation is left in that boundary.
-/

open Matrix OracleComp
open scoped ENNReal BigOperators

namespace FormalProof4FHE.TFHE.JointSubsetKeyBRKCenteredMixture

open FormalProof4FHE.BoundedMoment
open FormalProof4FHE.ConditionalCollision
open FormalProof4FHE.FiniteProduct

/-! ## Finite independent-pair expectations -/

/-- Expectation of a kernel on two independent draws from the same finite sampler. -/
noncomputable def pairExpectation {Secret : Type} [Fintype Secret]
    (sampler : ProbComp Secret) (kernel : Secret → Secret → ℝ) : ℝ :=
  expectation sampler (fun left ↦ expectation sampler (kernel left))

theorem expectation_mono_of_pointwise
    {Value : Type} [Fintype Value] (sampler : ProbComp Value)
    {left right : Value → ℝ} (hle : ∀ value, left value ≤ right value) :
    expectation sampler left ≤ expectation sampler right := by
  classical
  unfold expectation
  apply Finset.sum_le_sum
  intro value _
  exact mul_le_mul_of_nonneg_left (hle value) ENNReal.toReal_nonneg

theorem expectation_sum
    {Value Index : Type} [Fintype Value] [Fintype Index]
    (sampler : ProbComp Value) (term : Index → Value → ℝ) :
    expectation sampler (fun value ↦ ∑ index, term index value) =
      ∑ index, expectation sampler (term index) := by
  classical
  unfold expectation
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]

theorem pairExpectation_congr
    {Secret : Type} [Fintype Secret] (sampler : ProbComp Secret)
    {left right : Secret → Secret → ℝ}
    (heq : ∀ first second, left first second = right first second) :
    pairExpectation sampler left = pairExpectation sampler right := by
  unfold pairExpectation
  apply congrArg (expectation sampler)
  funext first
  apply congrArg (expectation sampler)
  funext second
  exact heq first second

theorem pairExpectation_add
    {Secret : Type} [Fintype Secret] (sampler : ProbComp Secret)
    (left right : Secret → Secret → ℝ) :
    pairExpectation sampler (fun first second ↦
        left first second + right first second) =
      pairExpectation sampler left + pairExpectation sampler right := by
  unfold pairExpectation
  simp_rw [expectation_add]

theorem pairExpectation_const
    {Secret : Type} [Fintype Secret] (sampler : ProbComp Secret) (constant : ℝ) :
    pairExpectation sampler (fun _ _ ↦ constant) = constant := by
  unfold pairExpectation
  simp_rw [expectation_const]

theorem pairExpectation_mono_of_pointwise
    {Secret : Type} [Fintype Secret] (sampler : ProbComp Secret)
    {left right : Secret → Secret → ℝ}
    (hle : ∀ first second, left first second ≤ right first second) :
    pairExpectation sampler left ≤ pairExpectation sampler right := by
  unfold pairExpectation
  apply expectation_mono_of_pointwise
  intro first
  apply expectation_mono_of_pointwise
  exact hle first

theorem pairExpectation_sq_nonneg
    {Secret : Type} [Fintype Secret] (sampler : ProbComp Secret)
    (interaction : Secret → Secret → ℝ) :
    0 ≤ pairExpectation sampler (fun left right ↦ interaction left right ^ 2) := by
  unfold pairExpectation expectation
  positivity

/-! ## Centered Gaussian-mixture cancellation -/

/-- Proof-carrying analytic boundary for the Gaussian pair-kernel identity.

For equal-covariance Gaussian shifts, `interaction left right` is
`mu(left)ᵀ Σ⁻¹ mu(right)`.  The displayed Pearson identity follows by integrating the two
density ratios against the reference Gaussian.  Wrapped or rounded implementations may instead
provide an approximate or finite analogue in a later instantiation. -/
structure CenteredMixtureChiSquareCertificate
    {Secret Output : Type} [Fintype Secret] [Fintype Output]
    (secretSampler : ProbComp Secret) (real ideal : ProbComp Output)
    (interaction : Secret → Secret → ℝ) where
  absolutelyContinuous : ∀ output,
    Pr[= output | ideal].toReal = 0 → Pr[= output | real].toReal = 0
  pairKernelIdentity :
    pearsonChiSquare real ideal =
      pairExpectation secretSampler
        (fun left right ↦ Real.exp (interaction left right)) - 1
  centeredInteraction : pairExpectation secretSampler interaction = 0

/-- Centering removes the entire linear term from the exponential pair kernel. -/
theorem CenteredMixtureChiSquareCertificate.pearsonChiSquare_eq_remainder
    {Secret Output : Type} [Fintype Secret] [Fintype Output]
    {secretSampler : ProbComp Secret} {real ideal : ProbComp Output}
    {interaction : Secret → Secret → ℝ}
    (certificate : CenteredMixtureChiSquareCertificate
      secretSampler real ideal interaction) :
    pearsonChiSquare real ideal =
      pairExpectation secretSampler
        (fun left right ↦
          Real.exp (interaction left right) - 1 - interaction left right) := by
  rw [certificate.pairKernelIdentity]
  have hdecompose :
      pairExpectation secretSampler
          (fun left right ↦ Real.exp (interaction left right)) =
        pairExpectation secretSampler
            (fun left right ↦
              (Real.exp (interaction left right) - 1 - interaction left right) +
                (1 + interaction left right)) := by
      apply pairExpectation_congr
      intro left right
      ring
  rw [hdecompose, pairExpectation_add]
  have honeInteraction :
      pairExpectation secretSampler
          (fun left right ↦ 1 + interaction left right) = 1 := by
    rw [pairExpectation_add, pairExpectation_const,
      certificate.centeredInteraction, add_zero]
  rw [honeInteraction]
  ring

/-- On `|interaction| ≤ 1`, centered Gaussian-mixture Pearson divergence is controlled by the
independent-pair interaction second moment.  This is the cancellation absent from the
first-order pointwise-shift argument. -/
theorem CenteredMixtureChiSquareCertificate.pearsonChiSquare_le_pairSecondMoment
    {Secret Output : Type} [Fintype Secret] [Fintype Output]
    {secretSampler : ProbComp Secret} {real ideal : ProbComp Output}
    {interaction : Secret → Secret → ℝ}
    (certificate : CenteredMixtureChiSquareCertificate
      secretSampler real ideal interaction)
    (interaction_small : ∀ left right, |interaction left right| ≤ 1) :
    pearsonChiSquare real ideal ≤
      pairExpectation secretSampler
        (fun left right ↦ interaction left right ^ 2) := by
  rw [certificate.pearsonChiSquare_eq_remainder]
  apply pairExpectation_mono_of_pointwise
  intro left right
  exact (le_abs_self _).trans
    (Real.abs_exp_sub_one_sub_id_le (interaction_small left right))

/-- Second-order centered-mixture total-variation bound. -/
theorem CenteredMixtureChiSquareCertificate.tvDist_le_pairSecondMoment
    {Secret Output : Type} [Fintype Secret] [Fintype Output]
    {secretSampler : ProbComp Secret} {real ideal : ProbComp Output}
    {interaction : Secret → Secret → ℝ}
    (certificate : CenteredMixtureChiSquareCertificate
      secretSampler real ideal interaction)
    (interaction_small : ∀ left right, |interaction left right| ≤ 1) :
    tvDist real ideal ≤
      Real.sqrt
        (pairExpectation secretSampler
          (fun left right ↦ interaction left right ^ 2)) / 2 := by
  calc
    tvDist real ideal ≤ Real.sqrt (pearsonChiSquare real ideal) / 2 :=
      tvDist_le_sqrt_pearsonChiSquare_div_two real ideal
        certificate.absolutelyContinuous
    _ ≤ Real.sqrt
          (pairExpectation secretSampler
            (fun left right ↦ interaction left right ^ 2)) / 2 := by
      gcongr
      exact certificate.pearsonChiSquare_le_pairSecondMoment interaction_small

/-! ### Constructor-level consequence -/

open JointSubsetKeyBRK
open DirectSubsetKeyBRK

/-- Substituting a centered-mixture second-order estimate in the complete two-real-branch joint
bound charges one square root of the pair second moment. -/
theorem targetAdvantage_le_centeredMixture
    {Sample Secret Output Prefix View : Type} [Add Output]
    {problem : LearningWithErrors.Problem Sample Secret Output}
    {prefixSampler : ProbComp Prefix} {targetView : Bool → ProbComp View}
    {constructor : PublicViewConstructor problem prefixSampler targetView}
    (certificate : DefectCertificate constructor)
    (pairSecondMoment : ℝ)
    (noise_le : certificate.noiseError ≤ Real.sqrt pairSecondMoment / 2)
    (distinguisher : Distinguisher View) :
    targetAdvantage targetView distinguisher ≤
      2 * LearningWithErrors.advantage problem (constructor.reduction distinguisher) +
        2 * certificate.factorizationError + Real.sqrt pairSecondMoment +
        certificate.uniformError + certificate.auxiliaryError := by
  have hbase := certificate.targetAdvantage_le_two_source_add_joint_errors distinguisher
  linarith

/-! ## Exact IID centered-ternary pair moment -/

/-- Bilinear interaction `zᵀ B z'` in a column-oriented weighted-sum normal form. -/
def ternaryBilinearInteraction {dimension : ℕ}
    (gram : Matrix (Fin dimension) (Fin dimension) ℝ)
    (left right : Fin dimension → Fin 3) : ℝ :=
  weightedSum
    (fun column ↦
      weightedSum (fun row ↦ gram row column)
        JointSubsetKeyBRKRefined.centeredTernaryDigit left)
    JointSubsetKeyBRKRefined.centeredTernaryDigit right

/-- The independent-pair IID ternary interaction is exactly centered. -/
theorem pairExpectation_iidTernaryBilinearInteraction_eq_zero
    (dimension : ℕ) (gram : Matrix (Fin dimension) (Fin dimension) ℝ) :
    pairExpectation (ProbComp.sampleIID dimension ($ᵗ (Fin 3)))
      (ternaryBilinearInteraction gram) = 0 := by
  unfold pairExpectation
  have hinner (left : Fin dimension → Fin 3) :
      expectation (ProbComp.sampleIID dimension ($ᵗ (Fin 3)))
          (ternaryBilinearInteraction gram left) = 0 := by
    exact mean_sampleIID_weightedSum_eq_zero
      ($ᵗ (Fin 3)) JointSubsetKeyBRKRefined.centeredTernaryDigit
      JointSubsetKeyBRKRefined.mean_uniform_centeredTernaryDigit_eq_zero
      dimension _
  simp_rw [hinner]
  exact expectation_const _ 0

/-- Exact second independent-pair moment

`E[(Zᵀ B Z')²] = (2/3)² * ∑ᵢ,ⱼ Bᵢⱼ²`

for independent IID uniform centered-ternary vectors. -/
theorem pairExpectation_sq_iidTernaryBilinearInteraction_eq
    (dimension : ℕ) (gram : Matrix (Fin dimension) (Fin dimension) ℝ) :
    pairExpectation (ProbComp.sampleIID dimension ($ᵗ (Fin 3)))
        (fun left right ↦ ternaryBilinearInteraction gram left right ^ 2) =
      (2 / 3 : ℝ) ^ 2 * ∑ row, ∑ column, gram row column ^ 2 := by
  let sampler := ProbComp.sampleIID dimension ($ᵗ (Fin 3))
  let digit := JointSubsetKeyBRKRefined.centeredTernaryDigit
  have hcentered : mean ($ᵗ (Fin 3)) digit = 0 :=
    JointSubsetKeyBRKRefined.mean_uniform_centeredTernaryDigit_eq_zero
  have hsecond : secondMoment ($ᵗ (Fin 3)) digit = 2 / 3 :=
    JointSubsetKeyBRKRefined.secondMoment_uniform_centeredTernaryDigit_eq_two_thirds
  have hinner (left : Fin dimension → Fin 3) :
      expectation sampler
          (fun right ↦ ternaryBilinearInteraction gram left right ^ 2) =
        (2 / 3 : ℝ) * ∑ column,
          (weightedSum (fun row ↦ gram row column) digit left) ^ 2 := by
    change secondMoment sampler
        (weightedSum
          (fun column ↦ weightedSum (fun row ↦ gram row column) digit left)
          digit) = _
    rw [secondMoment_sampleIID_weightedSum_eq ($ᵗ (Fin 3)) digit hcentered,
      hsecond]
  change expectation sampler
      (fun left ↦ expectation sampler
        (fun right ↦ ternaryBilinearInteraction gram left right ^ 2)) = _
  rw [show
    (fun left ↦ expectation sampler
      (fun right ↦ ternaryBilinearInteraction gram left right ^ 2)) =
      (fun left ↦ (2 / 3 : ℝ) * ∑ column,
        weightedSum (fun row ↦ gram row column) digit left ^ 2) by
    funext left
    exact hinner left]
  rw [expectation_const_mul, expectation_sum]
  have houter (column : Fin dimension) :
      expectation sampler
          (fun left ↦ weightedSum (fun row ↦ gram row column) digit left ^ 2) =
        (2 / 3 : ℝ) * ∑ row, gram row column ^ 2 := by
    change secondMoment sampler
        (weightedSum (fun row ↦ gram row column) digit) = _
    rw [secondMoment_sampleIID_weightedSum_eq ($ᵗ (Fin 3)) digit hcentered,
      hsecond]
  simp_rw [houter]
  rw [← Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

/-! ## Exact fixed-Hamming-weight signed-ternary moments -/

/-- Supports of exact cardinality `weight`. -/
abbrev FixedWeightSupport (dimension weight : ℕ) :=
  ↥((Finset.univ : Finset (Fin dimension)).powersetCard weight)

/-- The repository's canonical support-plus-sign representation. -/
abbrev FixedWeightTernarySecret (dimension weight : ℕ) :=
  FormalProof4FHE.RLWE.RankOneHNFLossinessSupportAware.FixedWeightTernarySecret
    dimension weight

/-- Redundant sampling seed: signs outside the selected support are ignored.  Keeping a full
IID sign vector makes the finite moment proof transparent; mapping this seed below produces the
canonical support-plus-sign secret. -/
abbrev FixedWeightTernarySeed (dimension weight : ℕ) :=
  FixedWeightSupport dimension weight × (Fin dimension → Fin 2)

theorem fixedWeightSupport_nonempty
    (dimension weight : ℕ) (weight_le : weight ≤ dimension) :
    Nonempty (FixedWeightSupport dimension weight) := by
  rcases (Finset.powersetCard_nonempty.mpr (by simpa using weight_le) :
    ((Finset.univ : Finset (Fin dimension)).powersetCard weight).Nonempty) with
    ⟨support, support_mem⟩
  exact ⟨⟨support, support_mem⟩⟩

@[reducible]
noncomputable def fixedWeightSupportSampleable
    (dimension weight : ℕ) (weight_le : weight ≤ dimension) :
    SampleableType (FixedWeightSupport dimension weight) :=
  letI : Nonempty (FixedWeightSupport dimension weight) :=
    fixedWeightSupport_nonempty dimension weight weight_le
  SampleableType.ofFintype _

/-- Uniform sampler on exact-cardinality supports. -/
noncomputable def fixedWeightSupportSampler
    (dimension weight : ℕ) (weight_le : weight ≤ dimension) :
    ProbComp (FixedWeightSupport dimension weight) :=
  @uniformSample (FixedWeightSupport dimension weight)
    (fixedWeightSupportSampleable dimension weight weight_le)

theorem expectation_fixedWeightSupportSampler_eq_sum_div
    (dimension weight : ℕ) (weight_le : weight ≤ dimension)
    (observable : FixedWeightSupport dimension weight → ℝ) :
    expectation (fixedWeightSupportSampler dimension weight weight_le) observable =
      (∑ support, observable support) / (Nat.choose dimension weight : ℝ) := by
  letI : Nonempty (FixedWeightSupport dimension weight) :=
    fixedWeightSupport_nonempty dimension weight weight_le
  letI : SampleableType (FixedWeightSupport dimension weight) :=
    fixedWeightSupportSampleable dimension weight weight_le
  change expectation ($ᵗ (FixedWeightSupport dimension weight)) observable = _
  rw [FormalProof4FHE.SquaredBias.expectation_uniform_eq_sum_div]
  simp [FixedWeightSupport]

/-- Double counting: every coordinate belongs to exactly
`choose (dimension - 1) (weight - 1)` supports of positive weight. -/
theorem sum_fixedWeightSupports_sum
    (dimension weight : ℕ) (weight_pos : 0 < weight)
    (observable : Fin dimension → ℝ) :
    (∑ support : FixedWeightSupport dimension weight,
        ∑ index ∈ support.1, observable index) =
      (Nat.choose (dimension - 1) (weight - 1) : ℝ) *
        ∑ index, observable index := by
  classical
  let supports := (Finset.univ : Finset (Fin dimension)).powersetCard weight
  have support_count (index : Fin dimension) :
      ((Finset.univ.filter fun support : ↥supports ↦
          index ∈ support.1).card) =
        Nat.choose (dimension - 1) (weight - 1) := by
    have raw_count :
        (supports.filter fun support ↦ index ∈ support).card =
          Nat.choose (dimension - 1) (weight - 1) := by
      have hcount := Finset.card_filter_powersetCard_subset
        ({index} : Finset (Fin dimension)) (Finset.univ : Finset (Fin dimension))
        weight (by simp) (by rw [Finset.card_singleton]; omega)
      simpa [supports] using hcount
    rw [Finset.univ_eq_attach supports, Finset.filter_attach']
    simp only [Finset.card_map, Finset.card_attach]
    convert raw_count using 1
    change
      (supports.filter fun support ↦
          ∃ _ : support ∈ supports, index ∈ support).card =
        (supports.filter fun support ↦ index ∈ support).card
    congr 1
    apply Finset.filter_congr
    intro support support_mem
    simp [support_mem]
  change (∑ support : ↥supports,
    ∑ index ∈ support.1, observable index) = _
  calc
    (∑ support : ↥supports, ∑ index ∈ support.1, observable index) =
        ∑ support : ↥supports, ∑ index,
          if index ∈ support.1 then observable index else 0 := by
      apply Finset.sum_congr rfl
      intro support _
      rw [← Finset.sum_filter]
      simp
    _ = ∑ index, ∑ support : ↥supports,
          if index ∈ support.1 then observable index else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ index,
          ((Finset.univ.filter fun support : ↥supports ↦
            index ∈ support.1).card : ℝ) * observable index := by
      apply Finset.sum_congr rfl
      intro index _
      rw [← Finset.sum_filter]
      simp
    _ = ∑ index,
          (Nat.choose (dimension - 1) (weight - 1) : ℝ) * observable index := by
      apply Finset.sum_congr rfl
      intro index _
      rw [support_count index]
    _ = _ := by rw [Finset.mul_sum]

/-- The exact inclusion probability of one coordinate in a uniform fixed-weight support. -/
theorem choose_pred_ratio_eq_weight_div_dimension
    (dimension weight : ℕ) (weight_pos : 0 < weight)
    (weight_le : weight ≤ dimension) :
    (Nat.choose (dimension - 1) (weight - 1) : ℝ) /
        Nat.choose dimension weight =
      (weight : ℝ) / dimension := by
  have dimension_pos : 0 < dimension := weight_pos.trans_le weight_le
  have choose_pos : 0 < Nat.choose dimension weight := Nat.choose_pos weight_le
  have choose_identity := Nat.add_one_mul_choose_eq (dimension - 1) (weight - 1)
  rw [Nat.sub_add_cancel dimension_pos, Nat.sub_add_cancel weight_pos] at choose_identity
  field_simp
  have choose_identity_real :
      (dimension : ℝ) * Nat.choose (dimension - 1) (weight - 1) =
        Nat.choose dimension weight * weight := by
    exact_mod_cast choose_identity
  simpa [mul_comm] using choose_identity_real

/-- Uniform exact-weight supports have isotropic inclusion moment `weight / dimension`. -/
theorem expectation_fixedWeightSupport_sum
    (dimension weight : ℕ) (weight_le : weight ≤ dimension)
    (observable : Fin dimension → ℝ) :
    expectation (fixedWeightSupportSampler dimension weight weight_le)
        (fun support ↦ ∑ index ∈ support.1, observable index) =
      (weight : ℝ) / dimension * ∑ index, observable index := by
  rw [expectation_fixedWeightSupportSampler_eq_sum_div]
  by_cases weight_zero : weight = 0
  · subst weight
    have support_sum_zero :
        (∑ support : FixedWeightSupport dimension 0,
            ∑ index ∈ support.1, observable index) = 0 := by
      apply Finset.sum_eq_zero
      intro support _
      have support_card := (Finset.mem_powersetCard.mp support.property).2
      have support_empty : support.1 = ∅ := Finset.card_eq_zero.mp support_card
      simp [support_empty]
    rw [support_sum_zero]
    simp
  · have weight_pos : 0 < weight := Nat.pos_of_ne_zero weight_zero
    rw [sum_fixedWeightSupports_sum dimension weight weight_pos observable]
    rw [show
      ((Nat.choose (dimension - 1) (weight - 1) : ℝ) *
          ∑ index, observable index) / Nat.choose dimension weight =
        ((Nat.choose (dimension - 1) (weight - 1) : ℝ) /
          Nat.choose dimension weight) * ∑ index, observable index by ring]
    rw [choose_pred_ratio_eq_weight_div_dimension
      dimension weight weight_pos weight_le]

/-- Symmetric sign embedding used on the selected support. -/
def centeredSignBit (sign : Fin 2) : ℝ := if sign = 0 then -1 else 1

theorem mean_uniform_centeredSignBit_eq_zero :
    mean ($ᵗ (Fin 2)) centeredSignBit = 0 := by
  simp [mean, expectation, Fin.sum_univ_two, centeredSignBit,
    probOutput_uniformSample, ENNReal.toReal_inv]

theorem secondMoment_uniform_centeredSignBit_eq_one :
    secondMoment ($ᵗ (Fin 2)) centeredSignBit = 1 := by
  simp [secondMoment, expectation, centeredSignBit,
    probOutput_uniformSample, ENNReal.toReal_inv]

theorem centeredSignBit_ne_zero (sign : Fin 2) : centeredSignBit sign ≠ 0 := by
  fin_cases sign <;> norm_num [centeredSignBit]

/-- Sample a uniform support and an independent full sign vector. -/
noncomputable def fixedWeightTernarySeedSampler
    (dimension weight : ℕ) (weight_le : weight ≤ dimension) :
    ProbComp (FixedWeightTernarySeed dimension weight) :=
  fixedWeightSupportSampler dimension weight weight_le >>= fun support ↦
    (fun signs ↦ (support, signs)) <$>
      ProbComp.sampleIID dimension ($ᵗ (Fin 2))

/-- Restrict the redundant full sign vector to its sampled support. -/
def fixedWeightTernarySecretOfSeed
    {dimension weight : ℕ} (seed : FixedWeightTernarySeed dimension weight) :
    FixedWeightTernarySecret dimension weight :=
  ⟨seed.1, fun index ↦ seed.2 index.1⟩

/-- Canonical exact-Hamming-weight signed-ternary sampler. -/
noncomputable def fixedWeightTernarySampler
    (dimension weight : ℕ) (weight_le : weight ≤ dimension) :
    ProbComp (FixedWeightTernarySecret dimension weight) :=
  fixedWeightTernarySecretOfSeed <$>
    fixedWeightTernarySeedSampler dimension weight weight_le

/-- Real coefficient represented by a canonical fixed-weight secret. -/
def fixedWeightTernaryValue
    {dimension weight : ℕ} (secret : FixedWeightTernarySecret dimension weight)
    (index : Fin dimension) : ℝ :=
  if index_mem : index ∈ secret.1.1 then
    centeredSignBit (secret.2 ⟨index, index_mem⟩)
  else 0

theorem fixedWeightTernaryValue_ne_zero_iff
    {dimension weight : ℕ} (secret : FixedWeightTernarySecret dimension weight)
    (index : Fin dimension) :
    fixedWeightTernaryValue secret index ≠ 0 ↔ index ∈ secret.1.1 := by
  by_cases index_mem : index ∈ secret.1.1
  · simp only [fixedWeightTernaryValue, dif_pos index_mem]
    constructor
    · exact fun _ ↦ index_mem
    · intro _
      exact centeredSignBit_ne_zero _
  · simp [fixedWeightTernaryValue, index_mem]

/-- The decoded secret has exact Hamming weight, not merely the desired second moment. -/
theorem card_support_fixedWeightTernaryValue
    {dimension weight : ℕ} (secret : FixedWeightTernarySecret dimension weight) :
    (Finset.univ.filter fun index ↦
      fixedWeightTernaryValue secret index ≠ 0).card = weight := by
  have support_eq :
      (Finset.univ.filter fun index ↦
        fixedWeightTernaryValue secret index ≠ 0) = secret.1.1 := by
    ext index
    simp [fixedWeightTernaryValue_ne_zero_iff]
  rw [support_eq]
  exact (Finset.mem_powersetCard.mp secret.1.property).2

def fixedWeightSeedWeightedSum
    {dimension weight : ℕ} (weights : Fin dimension → ℝ)
    (seed : FixedWeightTernarySeed dimension weight) : ℝ :=
  ∑ index, weights index *
    if index ∈ seed.1.1 then centeredSignBit (seed.2 index) else 0

theorem fixedWeightSeedWeightedSum_eq
    {dimension weight : ℕ} (weights : Fin dimension → ℝ)
    (seed : FixedWeightTernarySeed dimension weight) :
    fixedWeightSeedWeightedSum weights seed =
      weightedSum (fun index ↦ if index ∈ seed.1.1 then weights index else 0)
        centeredSignBit seed.2 := by
  classical
  unfold fixedWeightSeedWeightedSum weightedSum
  apply Finset.sum_congr rfl
  intro index _
  by_cases index_mem : index ∈ seed.1.1 <;> simp [index_mem]

theorem mean_fixedWeightSeedWeightedSum_eq_zero
    (dimension weight : ℕ) (weight_le : weight ≤ dimension)
    (weights : Fin dimension → ℝ) :
    mean (fixedWeightTernarySeedSampler dimension weight weight_le)
      (fixedWeightSeedWeightedSum weights) = 0 := by
  rw [mean, fixedWeightTernarySeedSampler, expectation_bind]
  have inner_mean (support : FixedWeightSupport dimension weight) :
      expectation
          ((fun signs ↦ (support, signs)) <$>
            ProbComp.sampleIID dimension ($ᵗ (Fin 2)))
          (fixedWeightSeedWeightedSum weights) = 0 := by
    rw [expectation_map]
    rw [show
      (fun signs ↦ fixedWeightSeedWeightedSum weights (support, signs)) =
        weightedSum
          (fun index ↦ if index ∈ support.1 then weights index else 0)
          centeredSignBit by
      funext signs
      exact fixedWeightSeedWeightedSum_eq weights (support, signs)]
    change mean (ProbComp.sampleIID dimension ($ᵗ (Fin 2)))
      (weightedSum
        (fun index ↦ if index ∈ support.1 then weights index else 0)
        centeredSignBit) = 0
    exact mean_sampleIID_weightedSum_eq_zero
      ($ᵗ (Fin 2)) centeredSignBit mean_uniform_centeredSignBit_eq_zero dimension _
  simp_rw [inner_mean, mul_zero]
  simp

theorem secondMoment_fixedWeightSeedWeightedSum_eq
    (dimension weight : ℕ) (weight_le : weight ≤ dimension)
    (weights : Fin dimension → ℝ) :
    secondMoment (fixedWeightTernarySeedSampler dimension weight weight_le)
        (fixedWeightSeedWeightedSum weights) =
      (weight : ℝ) / dimension * ∑ index, weights index ^ 2 := by
  rw [secondMoment, fixedWeightTernarySeedSampler, expectation_bind]
  have inner_secondMoment (support : FixedWeightSupport dimension weight) :
      expectation
          ((fun signs ↦ (support, signs)) <$>
            ProbComp.sampleIID dimension ($ᵗ (Fin 2)))
          (fun seed ↦ fixedWeightSeedWeightedSum weights seed ^ 2) =
        ∑ index ∈ support.1, weights index ^ 2 := by
    rw [expectation_map]
    rw [show
      (fun signs ↦ fixedWeightSeedWeightedSum weights (support, signs) ^ 2) =
        (fun signs ↦
          weightedSum
            (fun index ↦ if index ∈ support.1 then weights index else 0)
            centeredSignBit signs ^ 2) by
      funext signs
      rw [fixedWeightSeedWeightedSum_eq]]
    change secondMoment (ProbComp.sampleIID dimension ($ᵗ (Fin 2)))
      (weightedSum
        (fun index ↦ if index ∈ support.1 then weights index else 0)
        centeredSignBit) = _
    rw [secondMoment_sampleIID_weightedSum_eq
      ($ᵗ (Fin 2)) centeredSignBit mean_uniform_centeredSignBit_eq_zero,
      secondMoment_uniform_centeredSignBit_eq_one, one_mul]
    calc
      (∑ index, (if index ∈ support.1 then weights index else 0) ^ 2) =
          ∑ index, if index ∈ support.1 then weights index ^ 2 else 0 := by
        apply Finset.sum_congr rfl
        intro index _
        by_cases index_mem : index ∈ support.1 <;> simp [index_mem]
      _ = ∑ index ∈ support.1, weights index ^ 2 := by
        rw [← Finset.sum_filter]
        simp
  simp_rw [inner_secondMoment]
  change expectation (fixedWeightSupportSampler dimension weight weight_le)
      (fun support ↦ ∑ index ∈ support.1, weights index ^ 2) = _
  exact expectation_fixedWeightSupport_sum dimension weight weight_le
    (fun index ↦ weights index ^ 2)

/-- Weighted sum on the canonical support-plus-sign secret. -/
def fixedWeightTernaryWeightedSum
    {dimension weight : ℕ} (weights : Fin dimension → ℝ)
    (secret : FixedWeightTernarySecret dimension weight) : ℝ :=
  ∑ index, weights index * fixedWeightTernaryValue secret index

theorem fixedWeightTernaryWeightedSum_ofSeed
    {dimension weight : ℕ} (weights : Fin dimension → ℝ)
    (seed : FixedWeightTernarySeed dimension weight) :
    fixedWeightTernaryWeightedSum weights (fixedWeightTernarySecretOfSeed seed) =
      fixedWeightSeedWeightedSum weights seed := by
  classical
  unfold fixedWeightTernaryWeightedSum fixedWeightSeedWeightedSum
  apply Finset.sum_congr rfl
  intro index _
  by_cases index_mem : index ∈ seed.1.1
  · simp [fixedWeightTernaryValue, fixedWeightTernarySecretOfSeed, index_mem]
  · simp [fixedWeightTernaryValue, fixedWeightTernarySecretOfSeed, index_mem]

/-- Every weighted fixed-weight ternary linear form is exactly centered. -/
theorem mean_fixedWeightTernaryWeightedSum_eq_zero
    (dimension weight : ℕ) (weight_le : weight ≤ dimension)
    (weights : Fin dimension → ℝ) :
    mean (fixedWeightTernarySampler dimension weight weight_le)
      (fixedWeightTernaryWeightedSum weights) = 0 := by
  rw [mean, fixedWeightTernarySampler, expectation_map]
  rw [show
    (fun seed ↦ fixedWeightTernaryWeightedSum weights
      (fixedWeightTernarySecretOfSeed seed)) =
        fixedWeightSeedWeightedSum weights by
    funext seed
    exact fixedWeightTernaryWeightedSum_ofSeed weights seed]
  exact mean_fixedWeightSeedWeightedSum_eq_zero dimension weight weight_le weights

/-- Exact isotropic second moment for the canonical fixed-weight signed-ternary sampler. -/
theorem secondMoment_fixedWeightTernaryWeightedSum_eq
    (dimension weight : ℕ) (weight_le : weight ≤ dimension)
    (weights : Fin dimension → ℝ) :
    secondMoment (fixedWeightTernarySampler dimension weight weight_le)
        (fixedWeightTernaryWeightedSum weights) =
      (weight : ℝ) / dimension * ∑ index, weights index ^ 2 := by
  rw [secondMoment, fixedWeightTernarySampler, expectation_map]
  rw [show
    (fun seed ↦ fixedWeightTernaryWeightedSum weights
        (fixedWeightTernarySecretOfSeed seed) ^ 2) =
      (fun seed ↦ fixedWeightSeedWeightedSum weights seed ^ 2) by
    funext seed
    rw [fixedWeightTernaryWeightedSum_ofSeed]]
  exact secondMoment_fixedWeightSeedWeightedSum_eq dimension weight weight_le weights

/-- Bilinear interaction `zᵀ B z'` for canonical fixed-weight secrets. -/
def fixedWeightTernaryBilinearInteraction
    {dimension weight : ℕ} (gram : Matrix (Fin dimension) (Fin dimension) ℝ)
    (left right : FixedWeightTernarySecret dimension weight) : ℝ :=
  fixedWeightTernaryWeightedSum
    (fun column ↦
      fixedWeightTernaryWeightedSum (fun row ↦ gram row column) left)
    right

theorem pairExpectation_fixedWeightTernaryBilinearInteraction_eq_zero
    (dimension weight : ℕ) (weight_le : weight ≤ dimension)
    (gram : Matrix (Fin dimension) (Fin dimension) ℝ) :
    pairExpectation (fixedWeightTernarySampler dimension weight weight_le)
      (fixedWeightTernaryBilinearInteraction gram) = 0 := by
  unfold pairExpectation
  have inner_mean (left : FixedWeightTernarySecret dimension weight) :
      expectation (fixedWeightTernarySampler dimension weight weight_le)
          (fixedWeightTernaryBilinearInteraction gram left) = 0 := by
    exact mean_fixedWeightTernaryWeightedSum_eq_zero dimension weight weight_le _
  simp_rw [inner_mean]
  exact expectation_const _ 0

/-- Exact independent-pair fixed-weight interaction moment

`E[(Zᵀ B Z')²] = (weight / dimension)² * ∑ᵢ,ⱼ Bᵢⱼ²`.
-/
theorem pairExpectation_sq_fixedWeightTernaryBilinearInteraction_eq
    (dimension weight : ℕ) (weight_le : weight ≤ dimension)
    (gram : Matrix (Fin dimension) (Fin dimension) ℝ) :
    pairExpectation (fixedWeightTernarySampler dimension weight weight_le)
        (fun left right ↦
          fixedWeightTernaryBilinearInteraction gram left right ^ 2) =
      ((weight : ℝ) / dimension) ^ 2 *
        ∑ row, ∑ column, gram row column ^ 2 := by
  let sampler := fixedWeightTernarySampler dimension weight weight_le
  let variance := (weight : ℝ) / dimension
  have inner_secondMoment (left : FixedWeightTernarySecret dimension weight) :
      expectation sampler
          (fun right ↦ fixedWeightTernaryBilinearInteraction gram left right ^ 2) =
        variance * ∑ column,
          fixedWeightTernaryWeightedSum (fun row ↦ gram row column) left ^ 2 := by
    change secondMoment sampler
      (fixedWeightTernaryWeightedSum
        (fun column ↦
          fixedWeightTernaryWeightedSum (fun row ↦ gram row column) left)) = _
    exact secondMoment_fixedWeightTernaryWeightedSum_eq
      dimension weight weight_le _
  change expectation sampler
      (fun left ↦ expectation sampler
        (fun right ↦ fixedWeightTernaryBilinearInteraction gram left right ^ 2)) = _
  rw [show
    (fun left ↦ expectation sampler
      (fun right ↦ fixedWeightTernaryBilinearInteraction gram left right ^ 2)) =
      (fun left ↦ variance * ∑ column,
        fixedWeightTernaryWeightedSum (fun row ↦ gram row column) left ^ 2) by
    funext left
    exact inner_secondMoment left]
  rw [expectation_const_mul, expectation_sum]
  have outer_secondMoment (column : Fin dimension) :
      expectation sampler
          (fun left ↦
            fixedWeightTernaryWeightedSum (fun row ↦ gram row column) left ^ 2) =
        variance * ∑ row, gram row column ^ 2 := by
    change secondMoment sampler
      (fixedWeightTernaryWeightedSum (fun row ↦ gram row column)) = _
    exact secondMoment_fixedWeightTernaryWeightedSum_eq
      dimension weight weight_le _
  simp_rw [outer_secondMoment]
  rw [← Finset.mul_sum]
  rw [Finset.sum_comm]
  ring

/-! ### Ready-to-use centered-mixture bounds -/

/-- The Gram matrix `Rᵀ M R` governing Mahalanobis interaction between two residual shifts. -/
def mahalanobisGram
    {OutputCoordinate SecretCoordinate : Type}
    [Fintype OutputCoordinate] [Fintype SecretCoordinate]
    (precision : Matrix OutputCoordinate OutputCoordinate ℝ)
    (residual : Matrix OutputCoordinate SecretCoordinate ℝ) :
    Matrix SecretCoordinate SecretCoordinate ℝ :=
  residual.transpose * precision * residual

/-- IID ternary specialization of the centered-mixture TV theorem. -/
theorem CenteredMixtureChiSquareCertificate.tvDist_iidTernary_le
    {Output : Type} [Fintype Output]
    (dimension : ℕ) (gram : Matrix (Fin dimension) (Fin dimension) ℝ)
    (real ideal : ProbComp Output)
    (certificate : CenteredMixtureChiSquareCertificate
      (ProbComp.sampleIID dimension ($ᵗ (Fin 3))) real ideal
      (ternaryBilinearInteraction gram))
    (interaction_small : ∀ left right : Fin dimension → Fin 3,
      |ternaryBilinearInteraction gram left right| ≤ 1) :
    tvDist real ideal ≤
      Real.sqrt ((2 / 3 : ℝ) ^ 2 *
        ∑ row, ∑ column, gram row column ^ 2) / 2 := by
  rw [← pairExpectation_sq_iidTernaryBilinearInteraction_eq dimension gram]
  exact certificate.tvDist_le_pairSecondMoment interaction_small

/-- Exact-Hamming-weight signed-ternary specialization of the centered-mixture TV theorem. -/
theorem CenteredMixtureChiSquareCertificate.tvDist_fixedWeightTernary_le
    {Output : Type} [Fintype Output]
    (dimension weight : ℕ) (weight_le : weight ≤ dimension)
    (gram : Matrix (Fin dimension) (Fin dimension) ℝ)
    (real ideal : ProbComp Output)
    (certificate : CenteredMixtureChiSquareCertificate
      (fixedWeightTernarySampler dimension weight weight_le) real ideal
      (fixedWeightTernaryBilinearInteraction gram))
    (interaction_small : ∀ left right : FixedWeightTernarySecret dimension weight,
      |fixedWeightTernaryBilinearInteraction gram left right| ≤ 1) :
    tvDist real ideal ≤
      Real.sqrt (((weight : ℝ) / dimension) ^ 2 *
        ∑ row, ∑ column, gram row column ^ 2) / 2 := by
  rw [← pairExpectation_sq_fixedWeightTernaryBilinearInteraction_eq
    dimension weight weight_le gram]
  exact certificate.tvDist_le_pairSecondMoment interaction_small

/-! ## Residual covariance matching -/

section ResidualCovariance

variable {SourceCoordinate SecretCoordinate TargetCoordinate : Type}
  [Fintype SourceCoordinate] [Fintype SecretCoordinate]

/-- Covariance contributed by the centered residual-secret term `R Z`. -/
def residualCovariance
    (residual : Matrix TargetCoordinate SecretCoordinate ℝ)
    (secretCovariance : Matrix SecretCoordinate SecretCoordinate ℝ) :
    Matrix TargetCoordinate TargetCoordinate ℝ :=
  residual * secretCovariance * residual.transpose

/-- Linear transport preserves positive semidefiniteness of the secret covariance. -/
theorem residualCovariance_posSemidef
    [Fintype TargetCoordinate]
    (residual : Matrix TargetCoordinate SecretCoordinate ℝ)
    (secretCovariance : Matrix SecretCoordinate SecretCoordinate ℝ)
    (secret_psd : secretCovariance.PosSemidef) :
    (residualCovariance residual secretCovariance).PosSemidef := by
  simpa [residualCovariance] using
    secret_psd.mul_mul_conjTranspose_same residual

/-- Gaussian covariance reserved for the corrected base before adding the centered residual. -/
def covarianceMatchedBase
    (residual : Matrix TargetCoordinate SecretCoordinate ℝ)
    (secretCovariance : Matrix SecretCoordinate SecretCoordinate ℝ)
    (targetCovariance : Matrix TargetCoordinate TargetCoordinate ℝ) :
    Matrix TargetCoordinate TargetCoordinate ℝ :=
  targetCovariance - residualCovariance residual secretCovariance

/-- Correction covariance after reserving covariance for both `L E` and `R Z`. -/
def covarianceMatchedCorrection
    (postprocess : Matrix TargetCoordinate SourceCoordinate ℝ)
    (sourceCovariance : Matrix SourceCoordinate SourceCoordinate ℝ)
    (residual : Matrix TargetCoordinate SecretCoordinate ℝ)
    (secretCovariance : Matrix SecretCoordinate SecretCoordinate ℝ)
    (targetCovariance : Matrix TargetCoordinate TargetCoordinate ℝ) :
    Matrix TargetCoordinate TargetCoordinate ℝ :=
  targetCovariance -
    postprocess * sourceCovariance * postprocess.transpose -
      residualCovariance residual secretCovariance

/-- The transformed source error plus correction has the covariance reserved for the Gaussian
base of the centered residual mixture. -/
theorem transformed_add_matchedCorrection
    (postprocess : Matrix TargetCoordinate SourceCoordinate ℝ)
    (sourceCovariance : Matrix SourceCoordinate SourceCoordinate ℝ)
    (residual : Matrix TargetCoordinate SecretCoordinate ℝ)
    (secretCovariance : Matrix SecretCoordinate SecretCoordinate ℝ)
    (targetCovariance : Matrix TargetCoordinate TargetCoordinate ℝ) :
    postprocess * sourceCovariance * postprocess.transpose +
        covarianceMatchedCorrection postprocess sourceCovariance residual
          secretCovariance targetCovariance =
      covarianceMatchedBase residual secretCovariance targetCovariance := by
  unfold covarianceMatchedCorrection covarianceMatchedBase
  abel

/-- Exact covariance bookkeeping for the covariance-matched construction. -/
theorem transformed_add_matchedCorrection_add_residualCovariance
    (postprocess : Matrix TargetCoordinate SourceCoordinate ℝ)
    (sourceCovariance : Matrix SourceCoordinate SourceCoordinate ℝ)
    (residual : Matrix TargetCoordinate SecretCoordinate ℝ)
    (secretCovariance : Matrix SecretCoordinate SecretCoordinate ℝ)
    (targetCovariance : Matrix TargetCoordinate TargetCoordinate ℝ) :
    postprocess * sourceCovariance * postprocess.transpose +
          covarianceMatchedCorrection postprocess sourceCovariance residual
            secretCovariance targetCovariance +
        residualCovariance residual secretCovariance =
      targetCovariance := by
  unfold covarianceMatchedCorrection
  abel

/-- Checkable algebraic part of covariance matching.  `exactBaseCorrection` remains the
sampler-level Gaussian convolution statement for the selected continuous/wrapped/discrete model;
the centered-mixture certificate then controls the remaining non-Gaussian residual. -/
structure ResidualCovarianceMatchingCertificate
    {State Error : Type} [Add Error]
    (stateSampler : ProbComp State) (derived : State → Error)
    (basePrescribed : ProbComp Error)
    (postprocess : Matrix TargetCoordinate SourceCoordinate ℝ)
    (sourceCovariance : Matrix SourceCoordinate SourceCoordinate ℝ)
    (residual : Matrix TargetCoordinate SecretCoordinate ℝ)
    (secretCovariance : Matrix SecretCoordinate SecretCoordinate ℝ)
    (targetCovariance : Matrix TargetCoordinate TargetCoordinate ℝ) where
  correctionPSD :
    (covarianceMatchedCorrection postprocess sourceCovariance residual
      secretCovariance targetCovariance).PosSemidef
  exactBaseCorrection :
    JointSubsetKeyBRKRefined.ExactCorrectionNoiseCertificate
      stateSampler derived basePrescribed

theorem ResidualCovarianceMatchingCertificate.covariance_eq
    {State Error : Type} [Add Error]
    {stateSampler : ProbComp State} {derived : State → Error}
    {basePrescribed : ProbComp Error}
    {postprocess : Matrix TargetCoordinate SourceCoordinate ℝ}
    {sourceCovariance : Matrix SourceCoordinate SourceCoordinate ℝ}
    {residual : Matrix TargetCoordinate SecretCoordinate ℝ}
    {secretCovariance : Matrix SecretCoordinate SecretCoordinate ℝ}
    {targetCovariance : Matrix TargetCoordinate TargetCoordinate ℝ}
    (_certificate : ResidualCovarianceMatchingCertificate
      stateSampler derived basePrescribed postprocess sourceCovariance residual
        secretCovariance targetCovariance) :
    postprocess * sourceCovariance * postprocess.transpose +
          covarianceMatchedCorrection postprocess sourceCovariance residual
            secretCovariance targetCovariance +
        residualCovariance residual secretCovariance =
      targetCovariance :=
  transformed_add_matchedCorrection_add_residualCovariance
    postprocess sourceCovariance residual secretCovariance targetCovariance

/-- Complete proof boundary for the covariance-matched centered-mixture route.  The matrix and
full-joint correction obligations are carried by `covariance`; the sole analytic density
obligation and its centering fact are carried by `mixture`. -/
structure CovarianceMatchedCenteredMixtureCertificate
    {State Error Secret Output : Type} [Add Error]
    [Fintype Secret] [Fintype Output]
    (stateSampler : ProbComp State) (derived : State → Error)
    (basePrescribed : ProbComp Error)
    (postprocess : Matrix TargetCoordinate SourceCoordinate ℝ)
    (sourceCovariance : Matrix SourceCoordinate SourceCoordinate ℝ)
    (residual : Matrix TargetCoordinate SecretCoordinate ℝ)
    (secretCovariance : Matrix SecretCoordinate SecretCoordinate ℝ)
    (targetCovariance : Matrix TargetCoordinate TargetCoordinate ℝ)
    (secretSampler : ProbComp Secret) (real ideal : ProbComp Output)
    (interaction : Secret → Secret → ℝ) where
  covariance : ResidualCovarianceMatchingCertificate
    stateSampler derived basePrescribed postprocess sourceCovariance residual
      secretCovariance targetCovariance
  mixture : CenteredMixtureChiSquareCertificate
    secretSampler real ideal interaction
  interaction_small : ∀ left right, |interaction left right| ≤ 1

theorem CovarianceMatchedCenteredMixtureCertificate.tvDist_le
    {State Error Secret Output : Type} [Add Error]
    [Fintype Secret] [Fintype Output]
    {stateSampler : ProbComp State} {derived : State → Error}
    {basePrescribed : ProbComp Error}
    {postprocess : Matrix TargetCoordinate SourceCoordinate ℝ}
    {sourceCovariance : Matrix SourceCoordinate SourceCoordinate ℝ}
    {residual : Matrix TargetCoordinate SecretCoordinate ℝ}
    {secretCovariance : Matrix SecretCoordinate SecretCoordinate ℝ}
    {targetCovariance : Matrix TargetCoordinate TargetCoordinate ℝ}
    {secretSampler : ProbComp Secret} {real ideal : ProbComp Output}
    {interaction : Secret → Secret → ℝ}
    (certificate : CovarianceMatchedCenteredMixtureCertificate
      stateSampler derived basePrescribed postprocess sourceCovariance residual
        secretCovariance targetCovariance secretSampler real ideal interaction) :
    tvDist real ideal ≤
      Real.sqrt (pairExpectation secretSampler
        (fun left right ↦ interaction left right ^ 2)) / 2 :=
  certificate.mixture.tvDist_le_pairSecondMoment certificate.interaction_small

theorem CovarianceMatchedCenteredMixtureCertificate.covariance_eq
    {State Error Secret Output : Type} [Add Error]
    [Fintype Secret] [Fintype Output]
    {stateSampler : ProbComp State} {derived : State → Error}
    {basePrescribed : ProbComp Error}
    {postprocess : Matrix TargetCoordinate SourceCoordinate ℝ}
    {sourceCovariance : Matrix SourceCoordinate SourceCoordinate ℝ}
    {residual : Matrix TargetCoordinate SecretCoordinate ℝ}
    {secretCovariance : Matrix SecretCoordinate SecretCoordinate ℝ}
    {targetCovariance : Matrix TargetCoordinate TargetCoordinate ℝ}
    {secretSampler : ProbComp Secret} {real ideal : ProbComp Output}
    {interaction : Secret → Secret → ℝ}
    (certificate : CovarianceMatchedCenteredMixtureCertificate
      stateSampler derived basePrescribed postprocess sourceCovariance residual
        secretCovariance targetCovariance secretSampler real ideal interaction) :
    postprocess * sourceCovariance * postprocess.transpose +
          covarianceMatchedCorrection postprocess sourceCovariance residual
            secretCovariance targetCovariance +
        residualCovariance residual secretCovariance =
      targetCovariance :=
  certificate.covariance.covariance_eq

end ResidualCovariance

end FormalProof4FHE.TFHE.JointSubsetKeyBRKCenteredMixture
