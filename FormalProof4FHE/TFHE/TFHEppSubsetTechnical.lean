/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.JointSubsetKeyBRKDelayedProjectionSolver
import FormalProof4FHE.TFHE.TFHEppSubsetJointScreen

/-!
# Technical TFHEpp subset-key parameter consequences

This module records the implementation-independent algebra and the exact parameter arithmetic
that remain after the delayed-projection solver theorem.

The invertible-minor construction solves the target-ring equation and then lifts its coefficients
by the complete `2^16` modulus scale.  Projection therefore leaves an integral target-ring linear
combination of the level-one errors.  At the current TFHEpp widths the level-one integer variance
is already greater than the complete level-zero target variance.  Consequently every nonzero
integral derived-error row violates positive-semidefinite covariance completion.  This is a
rejection of this particular solver instantiation, not of every high-modulus short-preimage
solver: a solution of `L A = 2^16 G` may use the surplus-row kernel and need not have `2^16 ∣ L`.

For such a genuinely short high-modulus row, the exact continuous covariance budget permits
Euclidean radius `3104` and rejects integer radius `3105`.  The existence and efficient recovery
of a row in this ball are deliberately not asserted here.

The second section gives the full-secret KSK representation.  A native subset-KSK row with prefix
mask `a`, suffix gadget coefficient `g`, and selected suffix coordinate `i` is the inner product
of the complete secret `(x,z)` with the public combined row `(a, g e_i)`.  Thus a future
full-secret factorization can retain all secret coordinates instead of reducing the source
problem to the suffix alone.
-/

open Matrix
open scoped BigOperators

namespace FormalProof4FHE.TFHE.TFHEppSubsetTechnical

open JointSubsetKeyBRKCenteredMixture
open TFHEppSubsetJointScreen

/-! ## A general narrow-target obstruction -/

/-- If the source variance already exceeds the target variance, a nonzero integral
postprocessing row cannot admit positive-semidefinite covariance correction.  Any nonnegative
residual covariance only strengthens the obstruction. -/
theorem covarianceCorrection_not_posSemidef_of_narrowerTarget_integralRow
    {Source Target Secret : Type}
    [Fintype Source] [Fintype Target] [Fintype Secret]
    [DecidableEq Source] [DecidableEq Target] [DecidableEq Secret]
    (postprocess : Matrix Target Source ℝ)
    (residual : Matrix Target Secret ℝ)
    (sourceVariance secretVariance targetVariance : ℝ)
    (sourceVariance_nonneg : 0 ≤ sourceVariance)
    (secretVariance_nonneg : 0 ≤ secretVariance)
    (target_lt_source : targetVariance < sourceVariance)
    (row : Target)
    (integral : ∀ column, ∃ value : ℤ, postprocess row column = value)
    (nonzero : ∃ column, postprocess row column ≠ 0) :
    ¬ (covarianceMatchedCorrection
      postprocess (sourceVariance • (1 : Matrix Source Source ℝ))
      residual (secretVariance • (1 : Matrix Secret Secret ℝ))
      (targetVariance • (1 : Matrix Target Target ℝ))).PosSemidef := by
  intro hpsd
  have budget := covarianceBudget postprocess residual sourceVariance
    secretVariance targetVariance row hpsd
  have energy_ge : 1 ≤ ∑ column, postprocess row column ^ 2 :=
    integralRowEnergy_ge_one (postprocess row) integral nonzero
  have source_le :
      sourceVariance ≤
        sourceVariance * ∑ column, postprocess row column ^ 2 := by
    nlinarith
  have residual_nonneg :
      0 ≤ secretVariance * ∑ coordinate, residual row coordinate ^ 2 := by
    positivity
  linarith

/-! ## Exact current-parameter arithmetic -/

namespace Parameters

open TFHEppSubsetJointScreen.Parameters

set_option exponentiation.threshold 1024

/-- The level-one normalized width is `2^-25` on a 32-bit torus. -/
noncomputable def lvl1IntendedVariance : ℝ := (2 ^ (32 - 25) : ℝ) ^ 2

/-- Large-to-small word scale used by the delayed `32 -> 16` projection. -/
def wordScale : ℕ := 2 ^ (32 - 16)

theorem lvl1IntendedVariance_eq : lvl1IntendedVariance = 16384 := by
  norm_num [lvl1IntendedVariance]

theorem wordScale_eq : wordScale = 65536 := by
  norm_num [wordScale]

theorem lvl0IntendedVariance_lt_lvl1IntendedVariance :
    lvl0IntendedVariance < lvl1IntendedVariance := by
  rw [lvl1IntendedVariance_eq]
  exact lvl0IntendedVariance_lt_37.trans (by norm_num)

/-- The current target variance is large enough for every high-modulus row of Euclidean norm at
most `3104`, after the one final division by `2^16`. -/
theorem highModulusRadius_3104_fits :
    lvl1IntendedVariance * (3104 : ℝ) ^ 2 ≤
      (wordScale : ℝ) ^ 2 * lvl0IntendedVariance := by
  norm_num [lvl1IntendedVariance, wordScale, lvl0IntendedVariance,
    lvl0Alpha]

/-- Integer radius `3105` already exceeds the exact nominal covariance budget. -/
theorem highModulusRadius_3105_fails :
    (wordScale : ℝ) ^ 2 * lvl0IntendedVariance <
      lvl1IntendedVariance * (3105 : ℝ) ^ 2 := by
  norm_num [lvl1IntendedVariance, wordScale, lvl0IntendedVariance,
    lvl0Alpha]

/-- The exact lifted-minor derived-error row cannot match the current target covariance once it
contains a nonzero integral coefficient. -/
theorem liftedMinorRow_rejects_currentCovariance
    {Source Target Secret : Type}
    [Fintype Source] [Fintype Target] [Fintype Secret]
    [DecidableEq Source] [DecidableEq Target] [DecidableEq Secret]
    (postprocess : Matrix Target Source ℝ)
    (residual : Matrix Target Secret ℝ)
    (secretVariance : ℝ) (secretVariance_nonneg : 0 ≤ secretVariance)
    (row : Target)
    (integral : ∀ column, ∃ value : ℤ, postprocess row column = value)
    (nonzero : ∃ column, postprocess row column ≠ 0) :
    ¬ (covarianceMatchedCorrection
      postprocess (lvl1IntendedVariance • (1 : Matrix Source Source ℝ))
      residual (secretVariance • (1 : Matrix Secret Secret ℝ))
      (lvl0IntendedVariance • (1 : Matrix Target Target ℝ))).PosSemidef := by
  exact covarianceCorrection_not_posSemidef_of_narrowerTarget_integralRow
    postprocess residual lvl1IntendedVariance secretVariance lvl0IntendedVariance
    (by rw [lvl1IntendedVariance_eq]; norm_num) secretVariance_nonneg
    lvl0IntendedVariance_lt_lvl1IntendedVariance row integral nonzero

/-- Entrywise centered lift specialized to the current target word. -/
def centeredLift16
    {Source Target : Type}
    (matrix : Matrix Target Source (ZMod (2 ^ 16))) :
    Matrix Target Source ℝ :=
  fun row column ↦ (matrix row column).valMinAbs

/-- A nonzero modular row remains nonzero after taking centered integer representatives. -/
theorem centeredLift_row_nonzero
    {Source Target : Type} [Fintype Source]
    (matrix : Matrix Target Source (ZMod (2 ^ 16))) (row : Target)
    (nonzero : ∃ column, matrix row column ≠ 0) :
    ∃ column, centeredLift16 matrix row column ≠ 0 := by
  obtain ⟨column, hcolumn⟩ := nonzero
  refine ⟨column, ?_⟩
  intro hlift
  change ((matrix row column).valMinAbs : ℝ) = 0 at hlift
  have hval : (matrix row column).valMinAbs = 0 := by
    exact_mod_cast hlift
  exact hcolumn ((ZMod.valMinAbs_eq_zero _).mp hval)

/-- Every centered lift is integral, as required by the narrow-target obstruction. -/
theorem centeredLift_integral
    {Source Target : Type}
    (matrix : Matrix Target Source (ZMod (2 ^ 16))) :
    ∀ row column, ∃ value : ℤ,
      centeredLift16 matrix row column = value := by
  intro row column
  exact ⟨(matrix row column).valMinAbs, rfl⟩

/-- A nonzero row of any exact target-ring postprocessor, including the invertible-minor
postprocessor, fails the current level-one-to-level-zero covariance test after centered lift. -/
theorem centeredTargetRingRow_rejects_currentCovariance
    {Source Target Secret : Type}
    [Fintype Source] [Fintype Target] [Fintype Secret]
    [DecidableEq Source] [DecidableEq Target] [DecidableEq Secret]
    (postprocess : Matrix Target Source (ZMod (2 ^ 16)))
    (residual : Matrix Target Secret ℝ)
    (secretVariance : ℝ) (secretVariance_nonneg : 0 ≤ secretVariance)
    (row : Target) (nonzero : ∃ column, postprocess row column ≠ 0) :
    ¬ (covarianceMatchedCorrection
      (centeredLift16 postprocess)
      (lvl1IntendedVariance • (1 : Matrix Source Source ℝ))
      residual (secretVariance • (1 : Matrix Secret Secret ℝ))
      (lvl0IntendedVariance • (1 : Matrix Target Target ℝ))).PosSemidef := by
  apply liftedMinorRow_rejects_currentCovariance
    (centeredLift16 postprocess)
    residual secretVariance secretVariance_nonneg row
  · exact centeredLift_integral postprocess row
  · exact centeredLift_row_nonzero postprocess row nonzero

/-- An exact product with a nonzero gadget row forces the corresponding postprocessing row to be
nonzero. -/
theorem row_nonzero_of_product_row_nonzero
    {R SourceRow Coordinate Output : Type} [CommSemiring R]
    [Fintype SourceRow] [Fintype Coordinate]
    (postprocess : Matrix Output SourceRow R)
    (source : Matrix SourceRow Coordinate R)
    (gadget : Matrix Output Coordinate R)
    (product_eq : postprocess * source = gadget)
    (row : Output) (gadget_nonzero : ∃ coordinate, gadget row coordinate ≠ 0) :
    ∃ sourceRow, postprocess row sourceRow ≠ 0 := by
  by_contra hzero
  simp only [not_exists, not_not] at hzero
  obtain ⟨coordinate, hcoordinate⟩ := gadget_nonzero
  apply hcoordinate
  rw [← product_eq]
  simp [Matrix.mul_apply, hzero]

/-- Concrete exact-factorization form of the current lifted-minor no-go theorem. -/
theorem exactTargetRingFactorization_rejects_currentCovariance
    {SourceRow Coordinate Output Secret : Type}
    [Fintype SourceRow] [Fintype Coordinate] [Fintype Output] [Fintype Secret]
    [DecidableEq SourceRow] [DecidableEq Coordinate]
    [DecidableEq Output] [DecidableEq Secret]
    (postprocess : Matrix Output SourceRow (ZMod (2 ^ 16)))
    (source : Matrix SourceRow Coordinate (ZMod (2 ^ 16)))
    (gadget : Matrix Output Coordinate (ZMod (2 ^ 16)))
    (product_eq : postprocess * source = gadget)
    (residual : Matrix Output Secret ℝ)
    (secretVariance : ℝ) (secretVariance_nonneg : 0 ≤ secretVariance)
    (row : Output) (gadget_nonzero : ∃ coordinate, gadget row coordinate ≠ 0) :
    ¬ (covarianceMatchedCorrection
      (centeredLift16 postprocess)
      (lvl1IntendedVariance • (1 : Matrix SourceRow SourceRow ℝ))
      residual (secretVariance • (1 : Matrix Secret Secret ℝ))
      (lvl0IntendedVariance • (1 : Matrix Output Output ℝ))).PosSemidef := by
  apply centeredTargetRingRow_rejects_currentCovariance
    postprocess residual secretVariance secretVariance_nonneg row
  exact row_nonzero_of_product_row_nonzero
    postprocess source gadget product_eq row gadget_nonzero

end Parameters

/-! ## Full-secret KSK row representation -/

namespace FullSecretKSK

variable {R Prefix Suffix : Type}

/-- Concatenate independently represented prefix and suffix secrets. -/
def combinedSecret (prefixSecret : Prefix → R) (suffixSecret : Suffix → R) :
    Prefix ⊕ Suffix → R :=
  Sum.elim prefixSecret suffixSecret

/-- Public complete-secret coefficient row for one subset KSK ciphertext.  The prefix block is
the ordinary public mask; the suffix block contains one gadget coefficient. -/
def combinedTargetRow [Zero R] [DecidableEq Suffix]
    (mask : Prefix → R) (gadget : R) (coordinate : Suffix) :
    Prefix ⊕ Suffix → R :=
  Sum.elim mask (Pi.single coordinate gadget)

/-- The complete-secret inner product is exactly the native subset-KSK phase: the prefix mask
inner product plus the selected suffix gadget message. -/
theorem dotProduct_combinedTargetRow_combinedSecret
    [CommSemiring R] [Fintype Prefix] [Fintype Suffix]
    [DecidableEq Suffix]
    (mask : Prefix → R) (gadget : R) (coordinate : Suffix)
    (prefixSecret : Prefix → R) (suffixSecret : Suffix → R) :
    dotProduct (combinedTargetRow mask gadget coordinate)
        (combinedSecret prefixSecret suffixSecret) =
      dotProduct mask prefixSecret + gadget * suffixSecret coordinate := by
  classical
  simp [dotProduct, combinedTargetRow, combinedSecret, Fintype.sum_sum_type,
    Pi.single_apply]

/-- Adding a fresh error gives the exact native KSK body equation. -/
theorem fullSecretKSKBody_eq
    [CommSemiring R] [Fintype Prefix] [Fintype Suffix]
    [DecidableEq Suffix]
    (mask : Prefix → R) (gadget : R) (coordinate : Suffix)
    (prefixSecret : Prefix → R) (suffixSecret : Suffix → R) (error : R) :
    dotProduct (combinedTargetRow mask gadget coordinate)
          (combinedSecret prefixSecret suffixSecret) + error =
      dotProduct mask prefixSecret + gadget * suffixSecret coordinate + error := by
  rw [dotProduct_combinedTargetRow_combinedSecret]

/-- The production prefix/suffix split still contains all `1024` secret coordinates. -/
theorem productionCombinedDimension_eq :
    Fintype.card (Fin 630 ⊕ Fin 394) = 1024 := by
  norm_num

/-- Reindex the split production secret as one `Fin 1024` vector. -/
def productionIndexEquiv : Fin 630 ⊕ Fin 394 ≃ Fin 1024 := by
  simpa using (finSumFinEquiv : Fin 630 ⊕ Fin 394 ≃ Fin (630 + 394))

end FullSecretKSK

/-! ## Exact necessary candidate-capacity arithmetic -/

namespace ShortPreimageCapacity

set_option exponentiation.threshold 25000
set_option maxRecDepth 100000

/-- With `8036` ternary coefficients, the nonzero candidate family has at least `128` bits of
cardinality slack over the complete `32 * 394`-bit suffix-row target space. -/
theorem suffixTernaryCandidates_capacity :
    2 ^ (32 * 394 + 128) ≤ 3 ^ 8036 - 1 := by
  norm_num

/-- One fewer source coefficient does not meet the same exact cardinality target. -/
theorem suffixTernaryCandidates_minimal :
    3 ^ 8035 - 1 < 2 ^ (32 * 394 + 128) := by
  norm_num

/-- The complete suffix candidate box lies inside the proved integer norm radius. -/
theorem suffixTernaryCandidates_energy_fits :
    8036 ≤ 3104 ^ 2 := by
  norm_num

/-- Full-secret analogue of the exact candidate-capacity comparison. -/
theorem fullSecretTernaryCandidates_capacity :
    2 ^ (32 * 1024 + 128) ≤ 3 ^ 20756 - 1 := by
  have hblock : (2 : ℕ) ^ 84 < 3 ^ 53 := by
    norm_num
  have htail : (2 : ℕ) ^ 52 < 3 ^ 33 := by
    norm_num
  have hblockPow :
      ((2 : ℕ) ^ 84) ^ 391 ≤ ((3 : ℕ) ^ 53) ^ 391 :=
    Nat.pow_le_pow_left hblock.le 391
  have htwo : ((2 : ℕ) ^ 84) ^ 391 * 2 ^ 52 = 2 ^ 32896 := by
    rw [← pow_mul, ← pow_add]
  have hthree : ((3 : ℕ) ^ 53) ^ 391 * 3 ^ 33 = 3 ^ 20756 := by
    rw [← pow_mul, ← pow_add]
  have hstrict : (2 : ℕ) ^ 32896 < 3 ^ 20756 := by
    rw [← htwo, ← hthree]
    calc
      ((2 : ℕ) ^ 84) ^ 391 * 2 ^ 52 <
          ((2 : ℕ) ^ 84) ^ 391 * 3 ^ 33 :=
        Nat.mul_lt_mul_of_pos_left htail (by positivity)
      _ ≤ ((3 : ℕ) ^ 53) ^ 391 * 3 ^ 33 :=
        Nat.mul_le_mul_right (3 ^ 33) hblockPow
  norm_num only [Nat.reduceMul, Nat.reduceAdd]
  omega

/-- `20756` is the least row count meeting the selected full-secret cardinality target. -/
theorem fullSecretTernaryCandidates_minimal :
    3 ^ 20755 - 1 < 2 ^ (32 * 1024 + 128) := by
  have hblock : (3 : ℕ) ^ 306 < 2 ^ 485 := by
    norm_num
  have htail : (3 : ℕ) ^ 253 ≤ 2 ^ 401 := by
    norm_num
  have hblockPow :
      ((3 : ℕ) ^ 306) ^ 67 ≤ ((2 : ℕ) ^ 485) ^ 67 :=
    Nat.pow_le_pow_left hblock.le 67
  have hthree : ((3 : ℕ) ^ 306) ^ 67 * 3 ^ 253 = 3 ^ 20755 := by
    rw [← pow_mul, ← pow_add]
  have htwo : ((2 : ℕ) ^ 485) ^ 67 * 2 ^ 401 = 2 ^ 32896 := by
    rw [← pow_mul, ← pow_add]
  have hle : (3 : ℕ) ^ 20755 ≤ 2 ^ 32896 := by
    rw [← hthree, ← htwo]
    calc
      ((3 : ℕ) ^ 306) ^ 67 * 3 ^ 253 ≤
          ((3 : ℕ) ^ 306) ^ 67 * 2 ^ 401 :=
        Nat.mul_le_mul_left _ htail
      _ ≤ ((2 : ℕ) ^ 485) ^ 67 * 2 ^ 401 :=
        Nat.mul_le_mul_right _ hblockPow
  norm_num only [Nat.reduceMul, Nat.reduceAdd]
  have hpositive : 0 < (3 : ℕ) ^ 20755 := by positivity
  omega

/-- The complete full-secret candidate box also lies far inside the current norm radius. -/
theorem fullSecretTernaryCandidates_energy_fits :
    20756 ≤ 3104 ^ 2 := by
  norm_num

end ShortPreimageCapacity

end FormalProof4FHE.TFHE.TFHEppSubsetTechnical
