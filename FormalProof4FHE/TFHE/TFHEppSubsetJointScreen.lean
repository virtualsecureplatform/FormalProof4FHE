/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.JointSubsetKeyBRKCenteredMixture

/-!
# TFHEpp subset-key joint-simulation screen

This file instantiates necessary conditions from the centered-mixture joint BRK/KSK theorem at
the standard TFHEpp subset-key dimensions.  It does not assert insecurity of TFHEpp.  It checks
whether the current covariance-matched constrained-factorization route can certify the
implementation.

For equal spherical source and target error variance, positive-semidefinite correction covariance
forces every row `l` of the postprocessing matrix to satisfy `sum l_i^2 <= 1`.  If centered lifts
of its coefficients are integral and the row is nonzero, the row is therefore one signed
selector and its residual row is zero.  This turns covariance compatibility into an exact
short-factorization event.

At the implementation parameters, the hidden ternary suffix has dimension `1024 - 630 = 394`.
For a uniform matrix over `ZMod (2^16)`, all signed selectors from at most `2^127` source rows
represent one fixed target row with probability at most `2^-6176`.  Conversely, setting a top
gadget row of the postprocessor to zero leaves a residual of magnitude `2^14`; its IID ternary
variance alone exceeds the nominal level-zero error variance, so the covariance correction is
not positive semidefinite.

The actual C++ error sampler uses `std::normal_distribution<double>` followed by `dtot16`.
Consequently its exact finite law is not identified here with a mathematical Gaussian law; an
exact finite-law model or an approximation-distance charge is still required for the
pair-kernel certificate.  The covariance obstruction below occurs before that analytic boundary.
-/

open Matrix OracleComp
open scoped ENNReal BigOperators

namespace FormalProof4FHE.TFHE.TFHEppSubsetJointScreen

open JointSubsetKeyBRKCenteredMixture
open JointSubsetKeyBRKRefined

/-! ## Necessary covariance budget -/

/-- A diagonal consequence of positive-semidefinite covariance correction. -/
theorem covarianceBudget
    {Source Target Secret : Type}
    [Fintype Source] [Fintype Target] [Fintype Secret]
    [DecidableEq Source] [DecidableEq Target] [DecidableEq Secret]
    (postprocess : Matrix Target Source ℝ)
    (residual : Matrix Target Secret ℝ)
    (sourceVariance secretVariance targetVariance : ℝ)
    (row : Target)
    (hpsd :
      (covarianceMatchedCorrection
        postprocess (sourceVariance • (1 : Matrix Source Source ℝ))
        residual (secretVariance • (1 : Matrix Secret Secret ℝ))
        (targetVariance • (1 : Matrix Target Target ℝ))).PosSemidef) :
    sourceVariance * ∑ column, postprocess row column ^ 2 +
        secretVariance * ∑ coordinate, residual row coordinate ^ 2 ≤
      targetVariance := by
  have hdiag : 0 ≤
      (covarianceMatchedCorrection
        postprocess (sourceVariance • (1 : Matrix Source Source ℝ))
        residual (secretVariance • (1 : Matrix Secret Secret ℝ))
        (targetVariance • (1 : Matrix Target Target ℝ))) row row := by
    simpa using hpsd.2 (Finsupp.single row 1)
  simp only [covarianceMatchedCorrection, residualCovariance,
    Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply,
    Matrix.one_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] at hdiag
  rw [Finset.mul_sum, Finset.mul_sum]
  have hnormalized :
      ∑ coordinate, secretVariance * residual row coordinate ^ 2 ≤
        targetVariance -
          ∑ column, sourceVariance * postprocess row column ^ 2 := by
    simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using hdiag
  linarith

/-- With equal positive source and target variances, each postprocessing row has squared
Euclidean energy at most one. -/
theorem covarianceRowEnergy_le_one
    {Source Target Secret : Type}
    [Fintype Source] [Fintype Target] [Fintype Secret]
    [DecidableEq Source] [DecidableEq Target] [DecidableEq Secret]
    (postprocess : Matrix Target Source ℝ)
    (residual : Matrix Target Secret ℝ)
    (noiseVariance secretVariance : ℝ)
    (noiseVariance_pos : 0 < noiseVariance)
    (secretVariance_nonneg : 0 ≤ secretVariance)
    (row : Target)
    (hpsd :
      (covarianceMatchedCorrection
        postprocess (noiseVariance • (1 : Matrix Source Source ℝ))
        residual (secretVariance • (1 : Matrix Secret Secret ℝ))
        (noiseVariance • (1 : Matrix Target Target ℝ))).PosSemidef) :
    ∑ column, postprocess row column ^ 2 ≤ 1 := by
  have budget := show
      noiseVariance * ∑ column, postprocess row column ^ 2 +
          secretVariance * ∑ coordinate, residual row coordinate ^ 2 ≤
        noiseVariance from by
    exact covarianceBudget postprocess residual noiseVariance secretVariance
      noiseVariance row hpsd
  have hresidual : 0 ≤ ∑ coordinate, residual row coordinate ^ 2 := by
    positivity
  nlinarith

/-! ## Integral energy-one rows are signed selectors -/

/-- A nonzero integral vector has squared Euclidean energy at least one. -/
theorem integralRowEnergy_ge_one
    {Source : Type} [Fintype Source]
    (values : Source → ℝ)
    (integral : ∀ index, ∃ value : ℤ, values index = value)
    (nonzero : ∃ index, values index ≠ 0) :
    1 ≤ ∑ index, values index ^ 2 := by
  obtain ⟨index, hindex⟩ := nonzero
  obtain ⟨value, hvalue⟩ := integral index
  have value_ne_zero : value ≠ 0 := by
    intro hzero
    apply hindex
    simp [hvalue, hzero]
  have hsquareInteger : (1 : ℤ) ≤ value ^ 2 :=
    (one_le_sq_iff_one_le_abs value).2 (Int.one_le_abs value_ne_zero)
  have hsquare : (1 : ℝ) ≤ values index ^ 2 := by
    rw [hvalue]
    exact_mod_cast hsquareInteger
  exact hsquare.trans
    (Finset.single_le_sum
      (fun coordinate (_ : coordinate ∈ (Finset.univ : Finset Source)) ↦
        sq_nonneg (values coordinate))
      (Finset.mem_univ index))

/-- The only nonzero integral vectors with energy at most one are signed coordinate selectors. -/
theorem integralRowEnergy_le_one_eq_signedSingle
    {Source : Type} [Fintype Source] [DecidableEq Source]
    (values : Source → ℝ)
    (integral : ∀ index, ∃ value : ℤ, values index = value)
    (nonzero : ∃ index, values index ≠ 0)
    (energy_le : ∑ index, values index ^ 2 ≤ 1) :
    ∃ pivot,
      values = Pi.single pivot 1 ∨
        values = Pi.single pivot (-1) := by
  classical
  obtain ⟨pivot, hpivot⟩ := nonzero
  have energy_ge : 1 ≤ ∑ index, values index ^ 2 :=
    integralRowEnergy_ge_one values integral ⟨pivot, hpivot⟩
  have energy_eq : ∑ index, values index ^ 2 = 1 :=
    le_antisymm energy_le energy_ge
  obtain ⟨value, hvalue⟩ := integral pivot
  have value_ne_zero : value ≠ 0 := by
    intro hzero
    apply hpivot
    simp [hvalue, hzero]
  have hsquareInteger : (1 : ℤ) ≤ value ^ 2 :=
    (one_le_sq_iff_one_le_abs value).2 (Int.one_le_abs value_ne_zero)
  have hsquare_ge : (1 : ℝ) ≤ values pivot ^ 2 := by
    rw [hvalue]
    exact_mod_cast hsquareInteger
  have hsquare_le : values pivot ^ 2 ≤ ∑ index, values index ^ 2 :=
    Finset.single_le_sum
      (fun index (_ : index ∈ (Finset.univ : Finset Source)) ↦
        sq_nonneg (values index))
      (Finset.mem_univ pivot)
  have hpivot_square : values pivot ^ 2 = 1 := by
    nlinarith
  have hrest :
      ∑ index ∈ (Finset.univ : Finset Source).erase pivot,
          values index ^ 2 = 0 := by
    have hdecompose := Finset.sum_erase_add Finset.univ
      (fun index ↦ values index ^ 2) (Finset.mem_univ pivot)
    rw [energy_eq, hpivot_square] at hdecompose
    linarith
  have hoffPivot (index : Source) (hne : index ≠ pivot) :
      values index = 0 := by
    have hmem : index ∈ (Finset.univ : Finset Source).erase pivot := by
      simp [hne]
    have hsquare_zero :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun coordinate
            (_ : coordinate ∈ (Finset.univ : Finset Source).erase pivot) ↦
          sq_nonneg (values coordinate))).mp hrest index hmem
    nlinarith
  refine ⟨pivot, ?_⟩
  rcases sq_eq_one_iff.mp hpivot_square with hpivot_one | hpivot_neg_one
  · left
    funext index
    by_cases hindex : index = pivot
    · subst index
      simp [hpivot_one]
    · simp [hindex, hoffPivot index hindex]
  · right
    funext index
    by_cases hindex : index = pivot
    · subst index
      simp [hpivot_neg_one]
    · simp [hindex, hoffPivot index hindex]

/-- Once a row spends the full equal-noise covariance budget, positive secret variance forces
the corresponding residual row to vanish. -/
theorem covarianceResidualRow_eq_zero_of_energy_eq_one
    {Source Target Secret : Type}
    [Fintype Source] [Fintype Target] [Fintype Secret]
    [DecidableEq Source] [DecidableEq Target] [DecidableEq Secret]
    (postprocess : Matrix Target Source ℝ)
    (residual : Matrix Target Secret ℝ)
    (noiseVariance secretVariance : ℝ)
    (noiseVariance_pos : 0 < noiseVariance)
    (secretVariance_pos : 0 < secretVariance)
    (row : Target)
    (hpsd :
      (covarianceMatchedCorrection
        postprocess (noiseVariance • (1 : Matrix Source Source ℝ))
        residual (secretVariance • (1 : Matrix Secret Secret ℝ))
        (noiseVariance • (1 : Matrix Target Target ℝ))).PosSemidef)
    (rowEnergy : ∑ column, postprocess row column ^ 2 = 1) :
    ∀ coordinate, residual row coordinate = 0 := by
  have budget := covarianceBudget postprocess residual
    noiseVariance secretVariance noiseVariance row hpsd
  have hresidual_nonneg :
      0 ≤ ∑ coordinate, residual row coordinate ^ 2 := by
    positivity
  have hresidual_zero :
      ∑ coordinate, residual row coordinate ^ 2 = 0 := by
    nlinarith
  intro coordinate
  have hsquare :=
    (Finset.sum_eq_zero_iff_of_nonneg
      (fun index (_ : index ∈ (Finset.univ : Finset Secret)) ↦
        sq_nonneg (residual row index))).mp hresidual_zero
      coordinate (Finset.mem_univ coordinate)
  nlinarith

/-- Every nonzero integral postprocessing row compatible with the equal-noise covariance is a
signed selector. -/
theorem covarianceCompatibility_forces_signedSelectors
    {Source Target Secret : Type}
    [Fintype Source] [Fintype Target] [Fintype Secret]
    [DecidableEq Source] [DecidableEq Target] [DecidableEq Secret]
    (postprocess : Matrix Target Source ℝ)
    (residual : Matrix Target Secret ℝ)
    (noiseVariance secretVariance : ℝ)
    (noiseVariance_pos : 0 < noiseVariance)
    (secretVariance_nonneg : 0 ≤ secretVariance)
    (integral : ∀ row column, ∃ value : ℤ,
      postprocess row column = value)
    (nonzero : ∀ row, ∃ column, postprocess row column ≠ 0)
    (hpsd :
      (covarianceMatchedCorrection
        postprocess (noiseVariance • (1 : Matrix Source Source ℝ))
        residual (secretVariance • (1 : Matrix Secret Secret ℝ))
        (noiseVariance • (1 : Matrix Target Target ℝ))).PosSemidef) :
    ∀ row, ∃ pivot,
      postprocess row = Pi.single pivot 1 ∨
        postprocess row = Pi.single pivot (-1) := by
  intro row
  apply integralRowEnergy_le_one_eq_signedSingle
    (postprocess row) (integral row) (nonzero row)
  exact covarianceRowEnergy_le_one postprocess residual
    noiseVariance secretVariance noiseVariance_pos secretVariance_nonneg row hpsd

/-- If every integral postprocessing row is nonzero, covariance compatibility also forces the
complete approximate-factorization residual to be zero. -/
theorem covarianceCompatibility_forces_zeroResidual
    {Source Target Secret : Type}
    [Fintype Source] [Fintype Target] [Fintype Secret]
    [DecidableEq Source] [DecidableEq Target] [DecidableEq Secret]
    (postprocess : Matrix Target Source ℝ)
    (residual : Matrix Target Secret ℝ)
    (noiseVariance secretVariance : ℝ)
    (noiseVariance_pos : 0 < noiseVariance)
    (secretVariance_pos : 0 < secretVariance)
    (integral : ∀ row column, ∃ value : ℤ,
      postprocess row column = value)
    (nonzero : ∀ row, ∃ column, postprocess row column ≠ 0)
    (hpsd :
      (covarianceMatchedCorrection
        postprocess (noiseVariance • (1 : Matrix Source Source ℝ))
        residual (secretVariance • (1 : Matrix Secret Secret ℝ))
        (noiseVariance • (1 : Matrix Target Target ℝ))).PosSemidef) :
    residual = 0 := by
  ext row coordinate
  have energy_le : ∑ column, postprocess row column ^ 2 ≤ 1 :=
    covarianceRowEnergy_le_one postprocess residual noiseVariance secretVariance
      noiseVariance_pos secretVariance_pos.le row hpsd
  have energy_ge : 1 ≤ ∑ column, postprocess row column ^ 2 :=
    integralRowEnergy_ge_one (postprocess row) (integral row) (nonzero row)
  have energy_eq : ∑ column, postprocess row column ^ 2 = 1 :=
    le_antisymm energy_le energy_ge
  exact covarianceResidualRow_eq_zero_of_energy_eq_one
    postprocess residual noiseVariance secretVariance noiseVariance_pos
    secretVariance_pos row hpsd energy_eq coordinate

/-! ## The zero-row alternative fails the covariance test -/

/-- A zero postprocessing row cannot be repaired if one residual coordinate already contributes
more variance than the entire target budget. -/
theorem covarianceMatchedCorrection_not_posSemidef_of_zeroRow_largeResidual
    {Source Target Secret : Type}
    [Fintype Source] [Fintype Target] [Fintype Secret]
    [DecidableEq Source] [DecidableEq Target] [DecidableEq Secret]
    (postprocess : Matrix Target Source ℝ)
    (residual : Matrix Target Secret ℝ)
    (sourceVariance secretVariance targetVariance : ℝ)
    (secretVariance_nonneg : 0 ≤ secretVariance)
    (row : Target) (coordinate : Secret)
    (postprocess_zero : ∀ column, postprocess row column = 0)
    (too_large : targetVariance <
      secretVariance * residual row coordinate ^ 2) :
    ¬ (covarianceMatchedCorrection
      postprocess (sourceVariance • (1 : Matrix Source Source ℝ))
      residual (secretVariance • (1 : Matrix Secret Secret ℝ))
      (targetVariance • (1 : Matrix Target Target ℝ))).PosSemidef := by
  intro hpsd
  have budget := covarianceBudget postprocess residual sourceVariance
    secretVariance targetVariance row hpsd
  have sourceEnergy_zero :
      ∑ column, postprocess row column ^ 2 = 0 := by
    simp [postprocess_zero]
  have residualCoordinate_le :
      residual row coordinate ^ 2 ≤
        ∑ index, residual row index ^ 2 :=
    Finset.single_le_sum
      (fun index (_ : index ∈ (Finset.univ : Finset Secret)) ↦
        sq_nonneg (residual row index))
      (Finset.mem_univ coordinate)
  rw [sourceEnergy_zero, mul_zero, zero_add] at budget
  nlinarith

/-! ## Implementation parameter arithmetic -/

namespace Parameters

set_option exponentiation.threshold 1024

def lvl0Dimension : ℕ := 630
def lvl1Dimension : ℕ := 1024
def lvl10Levels : ℕ := 7
def lvl10Basebit : ℕ := 2
def lvl10DigitCount : ℕ := 2
def suffixDimension : ℕ := lvl1Dimension - lvl0Dimension
def lvl10KSKRows : ℕ := suffixDimension * lvl10Levels * lvl10DigitCount

/-- Exact decimal source literal in `include/params/128bit.hpp`, interpreted as a real. -/
noncomputable def lvl0Alpha : ℝ := 925119974676756 / 10 ^ 19

/-- Nominal variance in integer torus coordinates before implementation rounding effects. -/
noncomputable def lvl0IntendedVariance : ℝ := (lvl0Alpha * 2 ^ 16) ^ 2

/-- The `j = 0` level-one-to-level-zero key-switch gadget scalar. -/
def lvl10TopGadget : ℝ := 2 ^ 14

theorem suffixDimension_eq : suffixDimension = 394 := by
  norm_num [suffixDimension, lvl1Dimension, lvl0Dimension]

theorem lvl10DigitCount_eq :
    lvl10DigitCount = 2 ^ (lvl10Basebit - 1) := by
  norm_num [lvl10DigitCount, lvl10Basebit]

theorem lvl10KSKRows_eq : lvl10KSKRows = 5516 := by
  norm_num [lvl10KSKRows, suffixDimension, lvl1Dimension, lvl0Dimension,
    lvl10Levels, lvl10DigitCount]

theorem lvl10TopGadget_eq : lvl10TopGadget = 2 ^ (16 - lvl10Basebit) := by
  norm_num [lvl10TopGadget, lvl10Basebit]

theorem lvl0IntendedVariance_lt_37 : lvl0IntendedVariance < 37 := by
  norm_num [lvl0IntendedVariance, lvl0Alpha]

theorem topResidualTernaryVariance_gt_37 :
    37 < (2 / 3 : ℝ) * (-lvl10TopGadget) ^ 2 := by
  norm_num [lvl10TopGadget]

theorem signedSelectorExponent_eq : 16 * 394 - 128 = 6176 := by
  norm_num

/-- At the TFHEpp dimensions, a zero top-gadget postprocessing row leaves too much ternary
residual variance for a positive-semidefinite correction. -/
theorem topRow_zeroPostprocess_rejects_covariance
    {Source Target : Type}
    [Fintype Source] [Fintype Target]
    [DecidableEq Source] [DecidableEq Target]
    (postprocess : Matrix Target Source ℝ)
    (residual : Matrix Target (Fin 394) ℝ)
    (row : Target) (coordinate : Fin 394)
    (postprocess_zero : ∀ column, postprocess row column = 0)
    (top_residual : residual row coordinate = -lvl10TopGadget) :
    ¬ (covarianceMatchedCorrection
      postprocess (lvl0IntendedVariance • (1 : Matrix Source Source ℝ))
      residual ((2 / 3 : ℝ) • (1 : Matrix (Fin 394) (Fin 394) ℝ))
      (lvl0IntendedVariance • (1 : Matrix Target Target ℝ))).PosSemidef := by
  apply covarianceMatchedCorrection_not_posSemidef_of_zeroRow_largeResidual
    postprocess residual lvl0IntendedVariance (2 / 3) lvl0IntendedVariance
    (by norm_num) row coordinate postprocess_zero
  rw [top_residual]
  exact lvl0IntendedVariance_lt_37.trans topResidualTernaryVariance_gt_37

end Parameters

/-! ## Interaction check on the only covariance-compatible nonzero branch -/

theorem mahalanobisGram_zero_residual
    {Output Secret : Type} [Fintype Output] [Fintype Secret]
    (precision : Matrix Output Output ℝ) :
    mahalanobisGram precision (0 : Matrix Output Secret ℝ) = 0 := by
  simp [mahalanobisGram]

/-- A zero residual gives exactly zero IID-ternary pair interaction. -/
theorem iidTernaryInteraction_eq_zero_of_zero_residual
    {Output : Type} [Fintype Output]
    (dimension : ℕ) (precision : Matrix Output Output ℝ)
    (residual : Matrix Output (Fin dimension) ℝ)
    (residual_zero : residual = 0)
    (left right : Fin dimension → Fin 3) :
    ternaryBilinearInteraction
      (mahalanobisGram precision residual) left right = 0 := by
  subst residual
  rw [mahalanobisGram_zero_residual]
  simp [ternaryBilinearInteraction, FormalProof4FHE.BoundedMoment.weightedSum]

/-- When covariance compatibility has forced the residual to zero, the centered-mixture
interaction is exactly zero and the required `|interaction| <= 1` premise is automatic. -/
theorem iidTernaryInteraction_small_of_zero_residual
    {Output : Type} [Fintype Output]
    (dimension : ℕ) (precision : Matrix Output Output ℝ)
    (residual : Matrix Output (Fin dimension) ℝ)
    (residual_zero : residual = 0) :
    ∀ left right : Fin dimension → Fin 3,
      |ternaryBilinearInteraction
        (mahalanobisGram precision residual) left right| ≤ 1 := by
  intro left right
  rw [iidTernaryInteraction_eq_zero_of_zero_residual
    dimension precision residual residual_zero left right]
  norm_num

/-! ## Signed-selector factorization probability -/

set_option exponentiation.threshold 1024

noncomputable section

/-- A signed coordinate selector over any coefficient type. -/
def signedSelector
    {R Row : Type} [Zero R] [One R] [Neg R] [DecidableEq Row]
    (pivot : Row) (negative : Bool) : Row → R :=
  Pi.single pivot (if negative then -1 else 1)

/-- Every signed selector available from a finite family of source rows. -/
def signedSelectorCandidates
    (R Row : Type) [Zero R] [One R] [Neg R] [DecidableEq R]
    [Fintype Row] [DecidableEq Row] : Finset (Row → R) :=
  (Finset.univ : Finset (Row × Bool)).image
    (fun choice ↦ signedSelector choice.1 choice.2)

theorem signedSelectorCandidates_card_le
    (R Row : Type) [Zero R] [One R] [Neg R] [DecidableEq R]
    [Fintype Row] [DecidableEq Row] :
    (signedSelectorCandidates R Row).card ≤ 2 * Fintype.card Row := by
  calc
    (signedSelectorCandidates R Row).card ≤
        (Finset.univ : Finset (Row × Bool)).card := by
      exact Finset.card_image_le
    _ = 2 * Fintype.card Row := by simp [Nat.mul_comm]

theorem signedSelectorCandidates_primitive
    {Row : Type} [Fintype Row] [DecidableEq Row]
    (coefficient : Row → ZMod (2 ^ 16))
    (member : coefficient ∈ signedSelectorCandidates (ZMod (2 ^ 16)) Row) :
    HasUnitCoordinate coefficient := by
  rw [signedSelectorCandidates, Finset.mem_image] at member
  obtain ⟨⟨pivot, negative⟩, _, rfl⟩ := member
  refine ⟨pivot, ?_⟩
  cases negative <;> simp [signedSelector]

noncomputable local instance coordinateSampleable :
    SampleableType (Fin 394 → ZMod (2 ^ 16)) :=
  instSampleableTypePiFintype

noncomputable local instance matrixSampleable
    {Row : Type} [Fintype Row] [DecidableEq Row] :
    SampleableType (Matrix Row (Fin 394) (ZMod (2 ^ 16))) :=
  JointSubsetKeyBRKRefined.matrixSampleable

/-- For no more than `2^127` source rows, the probability that any covariance-compatible signed
selector represents one fixed suffix-gadget row is at most `2^-6176`.  Success of the complete
factorization is contained in this one-row event. -/
theorem signedSelectorFactorizationSuccess_le
    {Row : Type} [Fintype Row] [DecidableEq Row]
    (rowBound : Fintype.card Row ≤ 2 ^ 127)
    (target : Fin 394 → ZMod (2 ^ 16)) :
    Pr[(fun matrix : Matrix Row (Fin 394) (ZMod (2 ^ 16)) ↦
          ∃ coefficient ∈ signedSelectorCandidates (ZMod (2 ^ 16)) Row,
            rowCombination coefficient matrix = target) |
        ($ᵗ Matrix Row (Fin 394) (ZMod (2 ^ 16)))] ≤
      ((2 : ENNReal) ^ 6176)⁻¹ := by
  apply (shortFactorizationSuccess_le_card_pow
    (signedSelectorCandidates (ZMod (2 ^ 16)) Row)
    (fun coefficient member ↦
      signedSelectorCandidates_primitive coefficient member)
    target).trans
  calc
    ((signedSelectorCandidates (ZMod (2 ^ 16)) Row).card : ENNReal) *
          ((Fintype.card (ZMod (2 ^ 16)) : ENNReal) ^
            Fintype.card (Fin 394))⁻¹ ≤
        (2 ^ 128 : ENNReal) * ((2 ^ 16 : ENNReal) ^ 394)⁻¹ := by
      simp only [ZMod.card, Fintype.card_fin]
      gcongr
      exact_mod_cast
        (signedSelectorCandidates_card_le (ZMod (2 ^ 16)) Row).trans
          (calc
            2 * Fintype.card Row ≤ 2 * 2 ^ 127 :=
              Nat.mul_le_mul_left 2 rowBound
            _ = 2 ^ 128 := by norm_num [pow_succ])
      norm_num
    _ = ((2 : ENNReal) ^ 6176)⁻¹ := by
      rw [← pow_mul]
      rw [show 16 * 394 = 6304 by norm_num,
        show 6304 = 128 + 6176 by norm_num, pow_add]
      rw [ENNReal.mul_inv (by simp) (by simp), ← mul_assoc,
        ENNReal.mul_inv_cancel (by simp) (by simp), one_mul]

end

end FormalProof4FHE.TFHE.TFHEppSubsetJointScreen
