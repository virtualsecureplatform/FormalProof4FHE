/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.JointSubsetKeyBRKCenteredMixture
import Mathlib.Data.ZMod.Units

/-!
# Delayed-projection joint subset-key simulation

This module formalizes the remaining unequal-scale joint BRK/KSK proof route.  Instead of
projecting every large-modulus source sample separately, a simulator first combines source
samples at the large modulus and projects the result only once.

The algebra is stated through a translation-equivariant projection.  A scaled approximate
factorization

`L A = scale G + R`

then gives the exact projected identity

`project (L (A z + e)) = G z + project (R z + L e)`.

For TFHEpp's default word sizes, the file constructs the concrete embedding
`ZMod (2^16) -> ZMod (2^32)` by multiplication by `2^16`, defines canonical high-word
projection, and proves translation equivariance.  The same result is proved for the rounded
high-word operation using the implementation's `2^15` rounding offset.

The probabilistic section first proves the primitive two-budget counting screen.  If `C_L` is a
finite family of primitive postprocessing rows and `C_R` a finite residual family, then for a
uniform source matrix

`Pr[exists l in C_L, r in C_R, l A = g + r]
  <= |C_L| |C_R| / |R|^n`.

At modulus `2^32` and suffix dimension `394`, candidate descriptions with bit bounds `a,b` and
`a + b + s = 32 * 394` therefore have success probability at most `2^-s` for one prescribed
row.  This is a necessary-condition screen only.  It neither constructs a short preimage nor
shows that one can be found efficiently.

The image-aware extension removes the primitive-row restriction.  For every candidate row it
counts only residuals compatible with the row-combination image and divides by that image's
exact cardinality.  Over `ZMod (2^k)`, a row in valuation stratum `2^v u`, with `u` having a unit
coordinate, has image cardinality `2^((k-v)n)`.  Both fixed- and mixed-stratum union bounds and
the corresponding entropy-slack corollary are formalized below.  Every coefficient row on a
nonempty finite index type is automatically placed in its least bounded stratum; no witness from
the future solver is needed.

The finite-error section defines the complete secret/error joint law after rounded projection and
independent correction.  It proves the exact triple-convolution mass formula, characterizes
equality with an independent prescribed target error by pointwise equality of finite probability
tables, and transports either exact equality or total-variation distance through gadget assembly.
Thus a concrete finite implementation can be checked directly or charged by an explicit distance
without being identified with a continuous Gaussian.

The covariance definitions record the continuous proxy after scaling both `L` and `R` by the
inverse modulus ratio.  The companion module `JointSubsetKeyBRKDelayedProjectionSolver` supplies
exact box counts and a disjoint-block invertible-minor solver with zero residual, together with
its binary-rank failure and IID covariance bounds.  Positive-semidefinite realization for a
chosen continuous or discrete Gaussian sampler, the analytic ellipsoid-volume estimate, and a
concrete table equality or distance for the implementation sampler remain explicit analytic or
implementation obligations.
-/

open Matrix OracleComp
open scoped ENNReal BigOperators

namespace FormalProof4FHE.TFHE.JointSubsetKeyBRKDelayedProjection

/-! ## Translation-equivariant projection -/

/-- A target embedding and a possibly nonlinear projection which is exactly equivariant under
translations from the embedded target group.  High-word extraction is the motivating example. -/
structure TranslationProjection (Lifted Target : Type)
    [AddCommGroup Lifted] [AddCommGroup Target] where
  scale : Target →+ Lifted
  project : Lifted → Target
  project_scale_add : ∀ target error,
    project (scale target + error) = target + project error

namespace TranslationProjection

variable {Lifted Target : Type}
  [AddCommGroup Lifted] [AddCommGroup Target]

@[simp]
theorem project_scale (projection : TranslationProjection Lifted Target)
    (target : Target) :
    projection.project (projection.scale target) =
      target + projection.project 0 := by
  simpa using projection.project_scale_add target 0

/-- Applying a translation-equivariant projection coordinatewise preserves the same law. -/
def coordinatewise (projection : TranslationProjection Lifted Target)
    (Index : Type) : TranslationProjection (Index → Lifted) (Index → Target) where
  scale := {
    toFun := fun value index ↦ projection.scale (value index)
    map_zero' := by
      funext index
      simp
    map_add' := by
      intro left right
      funext index
      simp
  }
  project := fun value index ↦ projection.project (value index)
  project_scale_add := by
    intro target error
    funext index
    exact projection.project_scale_add (target index) (error index)

end TranslationProjection

/-! ## Scaled approximate factorization -/

/-- A factorization performed before modulus projection.  `postprocess` produces a lifted target
body, while the required gadget message is embedded by `scale`. -/
structure ScaledApproximateFactorization
    {Secret Source Lifted Target : Type}
    [AddCommGroup Secret] [AddCommGroup Source]
    [AddCommGroup Lifted] [AddCommGroup Target]
    (source : Secret →+ Source) (gadget : Secret →+ Target)
    (scale : Target →+ Lifted) where
  postprocess : Source →+ Lifted
  residual : Secret →+ Lifted
  postprocess_comp : postprocess.comp source = scale.comp gadget + residual

namespace ScaledApproximateFactorization

variable {Secret Source Lifted Target : Type}
  [AddCommGroup Secret] [AddCommGroup Source]
  [AddCommGroup Lifted] [AddCommGroup Target]
  {source : Secret →+ Source} {gadget : Secret →+ Target}
  {scale : Target →+ Lifted}

/-- Exact pre-projection algebra:

`L(Az + e) = scale(Gz) + (Rz + Le)`.
-/
theorem apply_real
    (certificate : ScaledApproximateFactorization source gadget scale)
    (secret : Secret) (sourceError : Source) :
    certificate.postprocess (source secret + sourceError) =
      scale (gadget secret) +
        (certificate.residual secret + certificate.postprocess sourceError) := by
  rw [map_add]
  have hcomp := congrArg
    (fun map : Secret →+ Lifted ↦ map secret) certificate.postprocess_comp
  change certificate.postprocess (source secret) =
    scale (gadget secret) + certificate.residual secret at hcomp
  rw [hcomp]
  abel

/-- **Delayed-projection identity.**  Combining at the lifted modulus and projecting once gives
the exact gadget message plus the projected complete derived error. -/
theorem project_real
    (projection : TranslationProjection Lifted Target)
    (certificate : ScaledApproximateFactorization source gadget projection.scale)
    (secret : Secret) (sourceError : Source) :
    projection.project
        (certificate.postprocess (source secret + sourceError)) =
      gadget secret + projection.project
        (certificate.residual secret + certificate.postprocess sourceError) := by
  rw [certificate.apply_real]
  exact projection.project_scale_add _ _

/-- The exact-factorization specialization has no residual-secret term before projection. -/
theorem project_real_of_residual_eq_zero
    (projection : TranslationProjection Lifted Target)
    (certificate : ScaledApproximateFactorization source gadget projection.scale)
    (residual_zero : certificate.residual = 0)
    (secret : Secret) (sourceError : Source) :
    projection.project
        (certificate.postprocess (source secret + sourceError)) =
      gadget secret + projection.project (certificate.postprocess sourceError) := by
  rw [certificate.project_real, residual_zero]
  simp

end ScaledApproximateFactorization

/-! ## Exact finite rounded-error bridge -/

namespace FiniteError

variable {Secret Source Lifted Target : Type}
  [AddCommGroup Secret] [AddCommGroup Source]
  [AddCommGroup Lifted] [AddCommGroup Target]
  {source : Secret →+ Source} {gadget : Secret →+ Target}

/-- The exact finite joint law of the secret and complete corrected error after
the delayed projection. -/
def roundedJointErrorSampler
    (projection : TranslationProjection Lifted Target)
    (certificate : ScaledApproximateFactorization source gadget projection.scale)
    (secretSampler : ProbComp Secret) (sourceErrorSampler : ProbComp Source)
    (correctionSampler : ProbComp Target) : ProbComp (Secret × Target) := do
  let secret ← secretSampler
  let sourceError ← sourceErrorSampler
  let correction ← correctionSampler
  return (secret, projection.project
    (certificate.residual secret + certificate.postprocess sourceError) + correction)

/-- The prescribed comparison law: the same secret paired with an independent
target-error sample. -/
def independentTargetErrorSampler
    (secretSampler : ProbComp Secret) (targetErrorSampler : ProbComp Target) :
    ProbComp (Secret × Target) := do
  let secret ← secretSampler
  let targetError ← targetErrorSampler
  return (secret, targetError)

def assembleGadgetError (gadget : Secret →+ Target) :
    Secret × Target → Target :=
  fun value ↦ gadget value.1 + value.2

/-- The projected honest value with an independent correction added at the
target modulus. -/
def projectedCorrectedRealSampler
    (projection : TranslationProjection Lifted Target)
    (certificate : ScaledApproximateFactorization source gadget projection.scale)
    (secretSampler : ProbComp Secret) (sourceErrorSampler : ProbComp Source)
    (correctionSampler : ProbComp Target) : ProbComp Target := do
  let secret ← secretSampler
  let sourceError ← sourceErrorSampler
  let correction ← correctionSampler
  return projection.project
    (certificate.postprocess (source secret + sourceError)) + correction

/-- The prescribed gadget message with an independent target error. -/
def prescribedTargetSampler
    (gadget : Secret →+ Target)
    (secretSampler : ProbComp Secret) (targetErrorSampler : ProbComp Target) :
    ProbComp Target :=
  assembleGadgetError gadget <$>
    independentTargetErrorSampler secretSampler targetErrorSampler

theorem projectedCorrectedRealSampler_evalDist_eq_map_jointError
    (projection : TranslationProjection Lifted Target)
    (certificate : ScaledApproximateFactorization source gadget projection.scale)
    (secretSampler : ProbComp Secret) (sourceErrorSampler : ProbComp Source)
    (correctionSampler : ProbComp Target) :
    evalDist (projectedCorrectedRealSampler projection certificate
      secretSampler sourceErrorSampler correctionSampler) =
      evalDist (assembleGadgetError gadget <$>
        roundedJointErrorSampler projection certificate
          secretSampler sourceErrorSampler correctionSampler) := by
  simp only [projectedCorrectedRealSampler, roundedJointErrorSampler,
    assembleGadgetError, map_eq_bind_pure_comp, bind_assoc, pure_bind,
    Function.comp_apply]
  simp_rw [certificate.project_real]
  simp only [add_assoc]

theorem projectedCorrectedReal_tvDist_prescribed_le_jointError
    (projection : TranslationProjection Lifted Target)
    (certificate : ScaledApproximateFactorization source gadget projection.scale)
    (secretSampler : ProbComp Secret) (sourceErrorSampler : ProbComp Source)
    (correctionSampler targetErrorSampler : ProbComp Target) :
    tvDist
        (projectedCorrectedRealSampler projection certificate
          secretSampler sourceErrorSampler correctionSampler)
        (prescribedTargetSampler gadget secretSampler targetErrorSampler) ≤
      tvDist
        (roundedJointErrorSampler projection certificate
          secretSampler sourceErrorSampler correctionSampler)
        (independentTargetErrorSampler secretSampler targetErrorSampler) := by
  rw [tvDist, projectedCorrectedRealSampler_evalDist_eq_map_jointError]
  exact tvDist_map_le (m := ProbComp) (assembleGadgetError gadget) _ _

theorem projectedCorrectedReal_evalDist_eq_prescribed_of_jointError
    (projection : TranslationProjection Lifted Target)
    (certificate : ScaledApproximateFactorization source gadget projection.scale)
    (secretSampler : ProbComp Secret) (sourceErrorSampler : ProbComp Source)
    (correctionSampler targetErrorSampler : ProbComp Target)
    (jointLaw :
      evalDist (roundedJointErrorSampler projection certificate
        secretSampler sourceErrorSampler correctionSampler) =
      evalDist (independentTargetErrorSampler secretSampler targetErrorSampler)) :
    evalDist (projectedCorrectedRealSampler projection certificate
      secretSampler sourceErrorSampler correctionSampler) =
      evalDist (prescribedTargetSampler gadget secretSampler targetErrorSampler) := by
  rw [projectedCorrectedRealSampler_evalDist_eq_map_jointError]
  exact evalDist_map_eq_of_evalDist_eq jointLaw (assembleGadgetError gadget)

noncomputable def roundedJointErrorMass
    [Fintype Secret] [Fintype Source] [Fintype Target]
    [DecidableEq Secret] [DecidableEq Target]
    (projection : TranslationProjection Lifted Target)
    (certificate : ScaledApproximateFactorization source gadget projection.scale)
    (secretSampler : ProbComp Secret) (sourceErrorSampler : ProbComp Source)
    (correctionSampler : ProbComp Target)
    (secret : Secret) (targetError : Target) : ENNReal :=
  Pr[= secret | secretSampler] *
    ∑ sourceError,
      Pr[= sourceError | sourceErrorSampler] *
        ∑ correction,
          Pr[= correction | correctionSampler] *
            if projection.project
                (certificate.residual secret + certificate.postprocess sourceError) +
              correction = targetError then 1 else 0

theorem probOutput_roundedJointErrorSampler_eq_mass
    [Fintype Secret] [Fintype Source] [Fintype Target]
    [DecidableEq Secret] [DecidableEq Target]
    (projection : TranslationProjection Lifted Target)
    (certificate : ScaledApproximateFactorization source gadget projection.scale)
    (secretSampler : ProbComp Secret) (sourceErrorSampler : ProbComp Source)
    (correctionSampler : ProbComp Target)
    (secret : Secret) (targetError : Target) :
    Pr[= (secret, targetError) |
        roundedJointErrorSampler projection certificate
          secretSampler sourceErrorSampler correctionSampler] =
      roundedJointErrorMass projection certificate secretSampler
        sourceErrorSampler correctionSampler secret targetError := by
  classical
  simp only [roundedJointErrorSampler, roundedJointErrorMass,
    probOutput_bind_eq_sum_fintype, probOutput_pure]
  rw [Finset.sum_eq_single secret]
  · simp [eq_comm]
  · intro other _ hother
    have hne : secret ≠ other := Ne.symm hother
    simp [hne]
  · simp

omit [AddCommGroup Secret] [AddCommGroup Target] in
theorem probOutput_independentTargetErrorSampler_eq_mul
    [Fintype Secret] [Fintype Target]
    [DecidableEq Secret] [DecidableEq Target]
    (secretSampler : ProbComp Secret) (targetErrorSampler : ProbComp Target)
    (secret : Secret) (targetError : Target) :
    Pr[= (secret, targetError) |
        independentTargetErrorSampler secretSampler targetErrorSampler] =
      Pr[= secret | secretSampler] * Pr[= targetError | targetErrorSampler] := by
  classical
  simp [independentTargetErrorSampler, probOutput_bind_eq_sum_fintype]

/-- A finite exact-convolution certificate is equivalent to a pointwise table
identity.  The left table is the explicit triple convolution above; the right
table is the product law expressing independence from the secret. -/
theorem roundedJointError_evalDist_eq_independent_iff_mass
    [Fintype Secret] [Fintype Source] [Fintype Target]
    [DecidableEq Secret] [DecidableEq Target]
    (projection : TranslationProjection Lifted Target)
    (certificate : ScaledApproximateFactorization source gadget projection.scale)
    (secretSampler : ProbComp Secret) (sourceErrorSampler : ProbComp Source)
    (correctionSampler targetErrorSampler : ProbComp Target) :
    evalDist (roundedJointErrorSampler projection certificate
        secretSampler sourceErrorSampler correctionSampler) =
      evalDist (independentTargetErrorSampler secretSampler targetErrorSampler) ↔
    ∀ secret targetError,
      roundedJointErrorMass projection certificate secretSampler
          sourceErrorSampler correctionSampler secret targetError =
        Pr[= secret | secretSampler] *
          Pr[= targetError | targetErrorSampler] := by
  constructor
  · intro law secret targetError
    rw [← probOutput_roundedJointErrorSampler_eq_mass,
      ← probOutput_independentTargetErrorSampler_eq_mul]
    exact evalDist_ext_iff.mp law (secret, targetError)
  · intro massEquality
    apply evalDist_ext
    rintro ⟨secret, targetError⟩
    rw [probOutput_roundedJointErrorSampler_eq_mass,
      probOutput_independentTargetErrorSampler_eq_mul]
    exact massEquality secret targetError

end FiniteError

/-! ## Concrete TFHEpp `2^32 -> 2^16` projection -/

namespace TFHEpp

set_option exponentiation.threshold 1024

/-- Embed a 16-bit torus value as a multiple of `2^16` in the 32-bit torus. -/
def scale16To32 : ZMod (2 ^ 16) →+ ZMod (2 ^ 32) :=
  ZMod.lift (2 ^ 16) ⟨
    (AddMonoidHom.mulLeft ((2 ^ 16 : ℕ) : ZMod (2 ^ 32))).comp
      (Int.castAddHom (ZMod (2 ^ 32))),
    by
      simp only [AddMonoidHom.comp_apply, AddMonoidHom.coe_mulLeft,
        Int.coe_castAddHom]
      rw [Int.cast_natCast]
      change (((2 ^ 16 : ℕ) : ZMod (2 ^ 32)) *
        ((2 ^ 16 : ℕ) : ZMod (2 ^ 32))) = 0
      rw [← Nat.cast_mul]
      norm_num only [show (2 ^ 16 : ℕ) * 2 ^ 16 = 2 ^ 32 by norm_num]
      exact ZMod.natCast_self _
  ⟩

@[simp]
theorem scale16To32_intCast (value : ℤ) :
    scale16To32 (value : ZMod (2 ^ 16)) =
      ((2 ^ 16 : ℤ) * value : ℤ) := by
  unfold scale16To32
  rw [ZMod.lift_coe]
  simp

@[simp]
theorem scale16To32_natCast (value : ℕ) :
    scale16To32 (value : ZMod (2 ^ 16)) =
      ((2 ^ 16 : ℕ) * value : ℕ) := by
  exact_mod_cast scale16To32_intCast (value : ℤ)

/-- Canonical unsigned high-word extraction. -/
def highWord32To16 (value : ZMod (2 ^ 32)) : ZMod (2 ^ 16) :=
  (value.val / 2 ^ 16 : ℕ)

private theorem scale16To32_eq_val (value : ZMod (2 ^ 16)) :
    scale16To32 value =
      ((2 ^ 16 * value.val : ℕ) : ZMod (2 ^ 32)) := by
  rw [← scale16To32_natCast value.val, ZMod.natCast_zmod_val]

/-- High-word extraction is exactly translation-equivariant under scaled 16-bit values. -/
theorem highWord32To16_scale_add
    (target : ZMod (2 ^ 16)) (error : ZMod (2 ^ 32)) :
    highWord32To16 (scale16To32 target + error) =
      target + highWord32To16 error := by
  apply ZMod.val_injective
  simp only [highWord32To16]
  rw [ZMod.val_add]
  rw [show (scale16To32 target).val = 2 ^ 16 * target.val by
    rw [scale16To32_eq_val, ZMod.val_natCast_of_lt]
    nlinarith [ZMod.val_lt target]]
  rw [ZMod.val_add]
  simp only [ZMod.val_natCast]
  norm_num only [pow_succ]
  omega

/-- Rounded high-word extraction with the offset used by TFHEpp when converting a 32-bit torus
word to a 16-bit word. -/
def roundedHighWord32To16 (value : ZMod (2 ^ 32)) : ZMod (2 ^ 16) :=
  highWord32To16 (value + ((2 ^ 15 : ℕ) : ZMod (2 ^ 32)))

/-- The rounded implementation operation has the same exact translation law. -/
theorem roundedHighWord32To16_scale_add
    (target : ZMod (2 ^ 16)) (error : ZMod (2 ^ 32)) :
    roundedHighWord32To16 (scale16To32 target + error) =
      target + roundedHighWord32To16 error := by
  unfold roundedHighWord32To16
  rw [add_assoc, highWord32To16_scale_add]

/-- Scalar unrounded delayed projection certificate. -/
def highWordProjection :
    TranslationProjection (ZMod (2 ^ 32)) (ZMod (2 ^ 16)) where
  scale := scale16To32
  project := highWord32To16
  project_scale_add := highWord32To16_scale_add

/-- Scalar rounded delayed projection certificate matching TFHEpp's word-conversion offset. -/
def roundedHighWordProjection :
    TranslationProjection (ZMod (2 ^ 32)) (ZMod (2 ^ 16)) where
  scale := scale16To32
  project := roundedHighWord32To16
  project_scale_add := roundedHighWord32To16_scale_add

/-- Coordinatewise rounded projection for a complete derived KSK body vector. -/
def coordinatewiseRoundedHighWordProjection (Index : Type) :
    TranslationProjection
      (Index → ZMod (2 ^ 32)) (Index → ZMod (2 ^ 16)) :=
  roundedHighWordProjection.coordinatewise Index

end TFHEpp

/-! ## Continuous covariance proxy after delayed scaling -/

open JointSubsetKeyBRKCenteredMixture

/-- Covariance correction for the continuous proxy after both the transformed source error and
residual shift are divided by the modulus ratio.  This definition does not identify rounded
finite errors with continuous Gaussians. -/
def delayedCovarianceMatchedCorrection
    {SourceCoordinate SecretCoordinate TargetCoordinate : Type}
    [Fintype SourceCoordinate] [Fintype SecretCoordinate]
    (inverseScale : ℝ)
    (postprocess : Matrix TargetCoordinate SourceCoordinate ℝ)
    (sourceCovariance : Matrix SourceCoordinate SourceCoordinate ℝ)
    (residual : Matrix TargetCoordinate SecretCoordinate ℝ)
    (secretCovariance : Matrix SecretCoordinate SecretCoordinate ℝ)
    (targetCovariance : Matrix TargetCoordinate TargetCoordinate ℝ) :
    Matrix TargetCoordinate TargetCoordinate ℝ :=
  covarianceMatchedCorrection
    (inverseScale • postprocess) sourceCovariance
    (inverseScale • residual) secretCovariance targetCovariance

/-- Exact covariance bookkeeping for the delayed-projection continuous proxy. -/
theorem transformed_add_delayedCorrection_add_residualCovariance
    {SourceCoordinate SecretCoordinate TargetCoordinate : Type}
    [Fintype SourceCoordinate] [Fintype SecretCoordinate]
    (inverseScale : ℝ)
    (postprocess : Matrix TargetCoordinate SourceCoordinate ℝ)
    (sourceCovariance : Matrix SourceCoordinate SourceCoordinate ℝ)
    (residual : Matrix TargetCoordinate SecretCoordinate ℝ)
    (secretCovariance : Matrix SecretCoordinate SecretCoordinate ℝ)
    (targetCovariance : Matrix TargetCoordinate TargetCoordinate ℝ) :
    (inverseScale • postprocess) * sourceCovariance *
          (inverseScale • postprocess).transpose +
        delayedCovarianceMatchedCorrection inverseScale postprocess sourceCovariance
          residual secretCovariance targetCovariance +
      residualCovariance (inverseScale • residual) secretCovariance =
        targetCovariance := by
  exact transformed_add_matchedCorrection_add_residualCovariance
    (inverseScale • postprocess) sourceCovariance
    (inverseScale • residual) secretCovariance targetCovariance

/-- Mahalanobis Gram matrix of the residual after delayed modulus scaling. -/
def delayedMahalanobisGram
    {OutputCoordinate SecretCoordinate : Type}
    [Fintype OutputCoordinate] [Fintype SecretCoordinate]
    (inverseScale : ℝ)
    (precision : Matrix OutputCoordinate OutputCoordinate ℝ)
    (residual : Matrix OutputCoordinate SecretCoordinate ℝ) :
    Matrix SecretCoordinate SecretCoordinate ℝ :=
  mahalanobisGram precision (inverseScale • residual)

/-! ## Two-budget counting obstruction -/

namespace Counting

open JointSubsetKeyBRKRefined

noncomputable section

variable {R Row Coordinate : Type}
  [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
  [Fintype Row] [DecidableEq Row]
  [Fintype Coordinate] [DecidableEq Coordinate]

noncomputable local instance coordinateFunctionSampleable :
    SampleableType (Coordinate → R) :=
  instSampleableTypePiFintype

noncomputable local instance matrixSampleable :
    SampleableType (Matrix Row Coordinate R) :=
  JointSubsetKeyBRKRefined.matrixSampleable

/-- **Two-budget factorization obstruction.**  Union-bound simultaneously over a finite family
of primitive postprocessing rows and a finite family of allowed residuals. -/
theorem twoBudgetFactorizationSuccess_le
    (postprocessCandidates : Finset (Row → R))
    (residualCandidates : Finset (Coordinate → R))
    (primitive : ∀ coefficient ∈ postprocessCandidates,
      HasUnitCoordinate coefficient)
    (target : Coordinate → R) :
    Pr[(fun matrix : Matrix Row Coordinate R ↦
          ∃ coefficient ∈ postprocessCandidates,
            ∃ residual ∈ residualCandidates,
              rowCombination coefficient matrix = target + residual) |
        ($ᵗ Matrix Row Coordinate R)] ≤
      (postprocessCandidates.card : ENNReal) *
        (residualCandidates.card : ENNReal) *
          (Fintype.card (Coordinate → R) : ENNReal)⁻¹ := by
  calc
    Pr[(fun matrix : Matrix Row Coordinate R ↦
          ∃ coefficient ∈ postprocessCandidates,
            ∃ residual ∈ residualCandidates,
              rowCombination coefficient matrix = target + residual) |
        ($ᵗ Matrix Row Coordinate R)] ≤
        ∑ coefficient ∈ postprocessCandidates,
          Pr[(fun matrix : Matrix Row Coordinate R ↦
              ∃ residual ∈ residualCandidates,
                rowCombination coefficient matrix = target + residual) |
            ($ᵗ Matrix Row Coordinate R)] :=
      probEvent_exists_finset_le_sum postprocessCandidates
        ($ᵗ Matrix Row Coordinate R)
        (fun coefficient matrix ↦
          ∃ residual ∈ residualCandidates,
            rowCombination coefficient matrix = target + residual)
    _ ≤ ∑ coefficient ∈ postprocessCandidates,
          ∑ residual ∈ residualCandidates,
            Pr[(fun matrix : Matrix Row Coordinate R ↦
                rowCombination coefficient matrix = target + residual) |
              ($ᵗ Matrix Row Coordinate R)] := by
      apply Finset.sum_le_sum
      intro coefficient _
      exact probEvent_exists_finset_le_sum residualCandidates
        ($ᵗ Matrix Row Coordinate R)
        (fun residual matrix ↦
          rowCombination coefficient matrix = target + residual)
    _ = ∑ _coefficient ∈ postprocessCandidates,
          ∑ _residual ∈ residualCandidates,
            (Fintype.card (Coordinate → R) : ENNReal)⁻¹ := by
      apply Finset.sum_congr rfl
      intro coefficient hcoefficient
      apply Finset.sum_congr rfl
      intro residual _
      rw [probEvent_rowCombination_eq coefficient
        (primitive coefficient hcoefficient) (target + residual)]
    _ = (postprocessCandidates.card : ENNReal) *
        (residualCandidates.card : ENNReal) *
          (Fintype.card (Coordinate → R) : ENNReal)⁻¹ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring

/-- Cardinality form exposing the full `|R|^n` denominator. -/
theorem twoBudgetFactorizationSuccess_le_card_pow
    (postprocessCandidates : Finset (Row → R))
    (residualCandidates : Finset (Coordinate → R))
    (primitive : ∀ coefficient ∈ postprocessCandidates,
      HasUnitCoordinate coefficient)
    (target : Coordinate → R) :
    Pr[(fun matrix : Matrix Row Coordinate R ↦
          ∃ coefficient ∈ postprocessCandidates,
            ∃ residual ∈ residualCandidates,
              rowCombination coefficient matrix = target + residual) |
        ($ᵗ Matrix Row Coordinate R)] ≤
      (postprocessCandidates.card : ENNReal) *
        (residualCandidates.card : ENNReal) *
          ((Fintype.card R : ENNReal) ^ Fintype.card Coordinate)⁻¹ := by
  simpa [Fintype.card_fun] using
    twoBudgetFactorizationSuccess_le postprocessCandidates residualCandidates
      primitive target

/-- Any claimed success lower bound must fit below the two-budget counting ratio. -/
theorem twoBudgetCandidateRatio_ge_of_success_ge
    (postprocessCandidates : Finset (Row → R))
    (residualCandidates : Finset (Coordinate → R))
    (primitive : ∀ coefficient ∈ postprocessCandidates,
      HasUnitCoordinate coefficient)
    (target : Coordinate → R) (successLowerBound : ENNReal)
    (highSuccess : successLowerBound ≤
      Pr[(fun matrix : Matrix Row Coordinate R ↦
            ∃ coefficient ∈ postprocessCandidates,
              ∃ residual ∈ residualCandidates,
                rowCombination coefficient matrix = target + residual) |
          ($ᵗ Matrix Row Coordinate R)]) :
    successLowerBound ≤
      (postprocessCandidates.card : ENNReal) *
        (residualCandidates.card : ENNReal) *
          ((Fintype.card R : ENNReal) ^ Fintype.card Coordinate)⁻¹ :=
  highSuccess.trans
    (twoBudgetFactorizationSuccess_le_card_pow
      postprocessCandidates residualCandidates primitive target)

set_option exponentiation.threshold 1024

/-- Concrete entropy-slack screen for the large-modulus TFHEpp suffix equation.  If the two
candidate families have at most `2^a` and `2^b` members and
`a + b + slack = 32 * 394`, one prescribed row succeeds with probability at most
`2^-slack`. -/
theorem tfheppTwoBudgetFactorizationSuccess_le
    {ActualRow : Type} [Fintype ActualRow] [DecidableEq ActualRow]
    (postprocessCandidates : Finset (ActualRow → ZMod (2 ^ 32)))
    (residualCandidates : Finset (Fin 394 → ZMod (2 ^ 32)))
    (primitive : ∀ coefficient ∈ postprocessCandidates,
      HasUnitCoordinate coefficient)
    (target : Fin 394 → ZMod (2 ^ 32))
    (postprocessBits residualBits slack : ℕ)
    (postprocessBound : postprocessCandidates.card ≤ 2 ^ postprocessBits)
    (residualBound : residualCandidates.card ≤ 2 ^ residualBits)
    (entropyBalance : postprocessBits + residualBits + slack = 32 * 394) :
    Pr[(fun matrix : Matrix ActualRow (Fin 394) (ZMod (2 ^ 32)) ↦
          ∃ coefficient ∈ postprocessCandidates,
            ∃ residual ∈ residualCandidates,
              rowCombination coefficient matrix = target + residual) |
        ($ᵗ Matrix ActualRow (Fin 394) (ZMod (2 ^ 32)))] ≤
      ((2 : ENNReal) ^ slack)⁻¹ := by
  calc
    Pr[(fun matrix : Matrix ActualRow (Fin 394) (ZMod (2 ^ 32)) ↦
          ∃ coefficient ∈ postprocessCandidates,
            ∃ residual ∈ residualCandidates,
              rowCombination coefficient matrix = target + residual) |
        ($ᵗ Matrix ActualRow (Fin 394) (ZMod (2 ^ 32)))] ≤
        (postprocessCandidates.card : ENNReal) *
          (residualCandidates.card : ENNReal) *
            ((Fintype.card (ZMod (2 ^ 32)) : ENNReal) ^
              Fintype.card (Fin 394))⁻¹ :=
      twoBudgetFactorizationSuccess_le_card_pow postprocessCandidates
        residualCandidates primitive target
    _ ≤ (2 ^ postprocessBits : ENNReal) *
          (2 ^ residualBits : ENNReal) *
            ((2 ^ 32 : ENNReal) ^ 394)⁻¹ := by
      simp only [ZMod.card, Fintype.card_fin]
      gcongr
      · exact_mod_cast postprocessBound
      · exact_mod_cast residualBound
      · norm_num
    _ = ((2 : ENNReal) ^ slack)⁻¹ := by
      let common : ENNReal :=
        (2 : ENNReal) ^ postprocessBits * 2 ^ residualBits
      have denominator_eq : ((2 ^ 32 : ENNReal) ^ 394) =
          common * (2 : ENNReal) ^ slack := by
        dsimp only [common]
        rw [← pow_add, ← pow_mul, ← entropyBalance, pow_add]
      change common * ((2 ^ 32 : ENNReal) ^ 394)⁻¹ =
        ((2 : ENNReal) ^ slack)⁻¹
      have common_ne_zero : common ≠ 0 := by
        dsimp only [common]
        simp
      have common_ne_top : common ≠ ⊤ := by
        dsimp only [common]
        exact ENNReal.mul_ne_top (by simp) (by simp)
      rw [denominator_eq,
        ENNReal.mul_inv (Or.inl common_ne_zero) (Or.inl common_ne_top),
        ← mul_assoc,
        ENNReal.mul_inv_cancel common_ne_zero common_ne_top, one_mul]

/-! ## Exact-image and power-of-two-stratum counting -/

def InRowCombinationRange (coefficient : Row → R)
    (target : Coordinate → R) : Prop :=
  target ∈ Set.range (rowCombination (Coordinate := Coordinate) coefficient)

noncomputable instance (coefficient : Row → R) (target : Coordinate → R) :
    Decidable (InRowCombinationRange coefficient target) :=
  Classical.propDecidable _

theorem probEvent_rowCombination_eq_image
    (coefficient : Row → R) (target : Coordinate → R) :
    Pr[(fun matrix : Matrix Row Coordinate R ↦
          rowCombination coefficient matrix = target) |
        ($ᵗ Matrix Row Coordinate R)] =
      if InRowCombinationRange coefficient target then
        (Fintype.card
          (rowCombination (Coordinate := Coordinate) coefficient).range : ENNReal)⁻¹
      else 0 := by
  classical
  let transform := rowCombination (Coordinate := Coordinate) coefficient
  by_cases htarget : InRowCombinationRange coefficient target
  · rw [if_pos htarget]
    let rangeTarget : transform.range := ⟨target, htarget⟩
    letI : SampleableType transform.range := SampleableType.ofFintype _
    have mapped_uniform :=
      evalDist_map_surjective_addHom_uniform transform.rangeRestrict
        (AddMonoidHom.rangeRestrict_surjective transform)
    calc
      Pr[(fun matrix : Matrix Row Coordinate R ↦
            rowCombination coefficient matrix = target) |
          ($ᵗ Matrix Row Coordinate R)] =
          Pr[(fun output : transform.range ↦ output = rangeTarget) |
            transform.rangeRestrict <$> ($ᵗ Matrix Row Coordinate R)] := by
        rw [probEvent_map]
        apply probEvent_congr' _ rfl
        intro output _
        simp only [Function.comp_apply, transform, rangeTarget, Subtype.ext_iff]
        rfl
      _ = Pr[(fun output : transform.range ↦ output = rangeTarget) |
            ($ᵗ transform.range)] :=
        probEvent_congr' (fun _ _ ↦ Iff.rfl) mapped_uniform
      _ = (Fintype.card transform.range : ENNReal)⁻¹ := by
        rw [probEvent_uniformSample]
        have filter_eq :
            (Finset.univ.filter fun output : transform.range ↦
              output = rangeTarget) = {rangeTarget} := by
          ext output
          simp
        rw [filter_eq]
        simp [div_eq_mul_inv]
  · rw [if_neg htarget]
    rw [probEvent_uniformSample]
    have filter_eq :
        (Finset.univ.filter fun matrix : Matrix Row Coordinate R ↦
          rowCombination coefficient matrix = target) = ∅ := by
      ext matrix
      have hne : rowCombination coefficient matrix ≠ target :=
        fun heq ↦ htarget ⟨matrix, heq⟩
      simp [hne]
    rw [filter_eq]
    simp

noncomputable def compatibleResidualCandidates
    (coefficient : Row → R) (target : Coordinate → R)
    (residualCandidates : Finset (Coordinate → R)) :
    Finset (Coordinate → R) :=
  residualCandidates.filter fun residual ↦
    InRowCombinationRange coefficient (target + residual)

theorem imageAwareTwoBudgetFactorizationSuccess_le
    (postprocessCandidates : Finset (Row → R))
    (residualCandidates : Finset (Coordinate → R))
    (target : Coordinate → R) :
    Pr[(fun matrix : Matrix Row Coordinate R ↦
          ∃ coefficient ∈ postprocessCandidates,
            ∃ residual ∈ residualCandidates,
              rowCombination coefficient matrix = target + residual) |
        ($ᵗ Matrix Row Coordinate R)] ≤
      ∑ coefficient ∈ postprocessCandidates,
        (compatibleResidualCandidates coefficient target residualCandidates).card *
          (Fintype.card
            (rowCombination (Coordinate := Coordinate) coefficient).range : ENNReal)⁻¹ := by
  calc
    Pr[(fun matrix : Matrix Row Coordinate R ↦
          ∃ coefficient ∈ postprocessCandidates,
            ∃ residual ∈ residualCandidates,
              rowCombination coefficient matrix = target + residual) |
        ($ᵗ Matrix Row Coordinate R)] ≤
        ∑ coefficient ∈ postprocessCandidates,
          Pr[(fun matrix : Matrix Row Coordinate R ↦
              ∃ residual ∈ residualCandidates,
                rowCombination coefficient matrix = target + residual) |
            ($ᵗ Matrix Row Coordinate R)] :=
      probEvent_exists_finset_le_sum postprocessCandidates
        ($ᵗ Matrix Row Coordinate R)
        (fun coefficient matrix ↦
          ∃ residual ∈ residualCandidates,
            rowCombination coefficient matrix = target + residual)
    _ ≤ ∑ coefficient ∈ postprocessCandidates,
          ∑ residual ∈ residualCandidates,
            Pr[(fun matrix : Matrix Row Coordinate R ↦
                rowCombination coefficient matrix = target + residual) |
              ($ᵗ Matrix Row Coordinate R)] := by
      apply Finset.sum_le_sum
      intro coefficient _
      exact probEvent_exists_finset_le_sum residualCandidates
        ($ᵗ Matrix Row Coordinate R)
        (fun residual matrix ↦
          rowCombination coefficient matrix = target + residual)
    _ = ∑ coefficient ∈ postprocessCandidates,
        (compatibleResidualCandidates coefficient target residualCandidates).card *
          (Fintype.card
            (rowCombination (Coordinate := Coordinate) coefficient).range : ENNReal)⁻¹ := by
      apply Finset.sum_congr rfl
      intro coefficient _
      simp_rw [probEvent_rowCombination_eq_image]
      rw [← Finset.sum_filter]
      simp only [compatibleResidualCandidates, Finset.sum_const, nsmul_eq_mul]

def scalarCombination (coefficient : Row → R) : (Row → R) →+ R where
  toFun := fun vector ↦ ∑ row, coefficient row * vector row
  map_zero' := by simp
  map_add' := by
    intro left right
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]

omit [Fintype R] [DecidableEq R] [SampleableType R] in
theorem scalarCombination_surjective
    (coefficient : Row → R) (primitive : HasUnitCoordinate coefficient) :
    Function.Surjective (scalarCombination coefficient) := by
  classical
  obtain ⟨pivot, hpivot⟩ := primitive
  intro target
  let unit : Rˣ := hpivot.unit
  let preimage : Row → R := fun row ↦
    if row = pivot then (↑unit⁻¹ : R) * target else 0
  refine ⟨preimage, ?_⟩
  change (∑ row, coefficient row * preimage row) = target
  simp only [preimage]
  rw [Finset.sum_eq_single pivot]
  · simp only [if_pos]
    have unit_spec : (↑unit : R) = coefficient pivot := hpivot.unit_spec
    have cancel : coefficient pivot * (↑unit⁻¹ : R) = 1 := by
      rw [← unit_spec, ← Units.val_mul]
      simp
    rw [← mul_assoc, cancel, one_mul]
  · intro row _ hrow
    simp [hrow]
  · simp

noncomputable def rowCombinationRangeEquivScalarRangePi
    (coefficient : Row → R) :
    (rowCombination (Coordinate := Coordinate) coefficient).range ≃
      (Coordinate → (scalarCombination coefficient).range) where
  toFun := fun output coordinate ↦ ⟨output.1 coordinate, by
    obtain ⟨matrix, hmatrix⟩ := output.2
    refine ⟨fun row ↦ matrix row coordinate, ?_⟩
    exact congrFun hmatrix coordinate⟩
  invFun := fun output ↦ ⟨fun coordinate ↦ (output coordinate).1, by
    let preimage : Matrix Row Coordinate R := fun row coordinate ↦
      Classical.choose (output coordinate).2 row
    refine ⟨preimage, ?_⟩
    funext coordinate
    exact Classical.choose_spec (output coordinate).2⟩
  left_inv := by
    intro output
    apply Subtype.ext
    funext coordinate
    rfl
  right_inv := by
    intro output
    funext coordinate
    rfl

omit [SampleableType R] in
theorem card_rowCombination_range_eq_scalarRange_pow
    (coefficient : Row → R) :
    Fintype.card (rowCombination (Coordinate := Coordinate) coefficient).range =
      Fintype.card (scalarCombination coefficient).range ^
        Fintype.card Coordinate := by
  rw [Fintype.card_congr (rowCombinationRangeEquivScalarRangePi coefficient),
    Fintype.card_fun]

def scaledCoefficient (scale : R) (coefficient : Row → R) : Row → R :=
  fun row ↦ scale * coefficient row

omit [Fintype R] [DecidableEq R] [SampleableType R] [DecidableEq Row] in
theorem scalarCombination_scaledCoefficient
    (scale : R) (coefficient vector : Row → R) :
    scalarCombination (scaledCoefficient scale coefficient) vector =
      scale * scalarCombination coefficient vector := by
  change (∑ row, (scale * coefficient row) * vector row) =
    scale * ∑ row, coefficient row * vector row
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro row _
  rw [mul_assoc]

def multiplyAddHom (scale : R) : R →+ R where
  toFun value := value * scale
  map_zero' := zero_mul scale
  map_add' left right := add_mul left right scale

omit [Fintype R] [DecidableEq R] [SampleableType R] in
theorem scalarCombination_scaled_range_eq_rightMul_range
    (scale : R) (coefficient : Row → R)
    (primitive : HasUnitCoordinate coefficient) :
    (scalarCombination (scaledCoefficient scale coefficient)).range =
      (multiplyAddHom scale).range := by
  ext value
  constructor
  · rintro ⟨vector, rfl⟩
    refine ⟨scalarCombination coefficient vector, ?_⟩
    simp only [scalarCombination_scaledCoefficient, multiplyAddHom]
    exact mul_comm _ _
  · rintro ⟨scalar, hscalar⟩
    obtain ⟨vector, hvector⟩ := scalarCombination_surjective coefficient primitive scalar
    refine ⟨vector, ?_⟩
    rw [scalarCombination_scaledCoefficient, hvector]
    change scalar * scale = value at hscalar
    calc
      scale * scalar = scalar * scale := mul_comm _ _
      _ = value := hscalar

theorem card_rightMul_pow_two_range
    (modulusExponent valuation : ℕ) (valuation_le : valuation ≤ modulusExponent) :
    Fintype.card
        (multiplyAddHom
          ((2 ^ valuation : ℕ) : ZMod (2 ^ modulusExponent))).range =
      2 ^ (modulusExponent - valuation) := by
  let scale : ZMod (2 ^ modulusExponent) := (2 ^ valuation : ℕ)
  have hom_eq :
      multiplyAddHom scale =
        nsmulAddMonoidHom (2 ^ valuation) := by
    ext value
    change value * scale = (2 ^ valuation) • value
    rw [nsmul_eq_mul]
    dsimp only [scale]
    exact mul_comm _ _
  rw [hom_eq, ← Nat.card_eq_fintype_card,
    IsAddCyclic.card_nsmulAddMonoidHom_range, Nat.card_zmod,
    Nat.gcd_eq_right_iff_dvd.mpr (Nat.pow_dvd_pow 2 valuation_le)]
  rw [← Nat.pow_sub_mul_pow 2 valuation_le]
  exact Nat.mul_div_left _ (pow_pos (by norm_num) _)

theorem card_rowCombination_scaledPrimitive_pow_two_range
    (modulusExponent valuation : ℕ) (valuation_le : valuation ≤ modulusExponent)
    (coefficient : Row → ZMod (2 ^ modulusExponent))
    (primitive : HasUnitCoordinate coefficient) :
    Fintype.card
        (rowCombination (Coordinate := Coordinate)
          (scaledCoefficient ((2 ^ valuation : ℕ) : ZMod (2 ^ modulusExponent))
            coefficient)).range =
      2 ^ ((modulusExponent - valuation) * Fintype.card Coordinate) := by
  rw [card_rowCombination_range_eq_scalarRange_pow]
  have scalarCard :
      Fintype.card
          (scalarCombination
            (scaledCoefficient
              ((2 ^ valuation : ℕ) : ZMod (2 ^ modulusExponent)) coefficient)).range =
        2 ^ (modulusExponent - valuation) := by
    have range_eq :=
      scalarCombination_scaled_range_eq_rightMul_range
        ((2 ^ valuation : ℕ) : ZMod (2 ^ modulusExponent)) coefficient primitive
    let rangeEquiv :
        (scalarCombination
          (scaledCoefficient
            ((2 ^ valuation : ℕ) : ZMod (2 ^ modulusExponent)) coefficient)).range ≃
          (multiplyAddHom
            ((2 ^ valuation : ℕ) : ZMod (2 ^ modulusExponent))).range :=
      Equiv.setCongr (congrArg (fun subgroup : AddSubgroup (ZMod (2 ^ modulusExponent)) ↦
        (subgroup : Set (ZMod (2 ^ modulusExponent)))) range_eq)
    rw [Fintype.card_congr rangeEquiv]
    exact card_rightMul_pow_two_range modulusExponent valuation valuation_le
  rw [scalarCard, ← pow_mul]

/-- A coefficient row lies in the exact `2^valuation` stratum when it is that
power of two times a row having a unit coordinate. -/
def IsPowerOfTwoStratum (modulusExponent valuation : ℕ)
    (coefficient : Row → ZMod (2 ^ modulusExponent)) : Prop :=
  ∃ primitiveCoefficient : Row → ZMod (2 ^ modulusExponent),
    HasUnitCoordinate primitiveCoefficient ∧
      coefficient =
        scaledCoefficient
          ((2 ^ valuation : ℕ) : ZMod (2 ^ modulusExponent))
          primitiveCoefficient

theorem card_rowCombination_range_of_powerOfTwoStratum
    (modulusExponent valuation : ℕ) (valuation_le : valuation ≤ modulusExponent)
    (coefficient : Row → ZMod (2 ^ modulusExponent))
    (stratum : IsPowerOfTwoStratum modulusExponent valuation coefficient) :
    Fintype.card
        (rowCombination (Coordinate := Coordinate) coefficient).range =
      2 ^ ((modulusExponent - valuation) * Fintype.card Coordinate) := by
  obtain ⟨primitiveCoefficient, primitive, rfl⟩ := stratum
  exact card_rowCombination_scaledPrimitive_pow_two_range
    modulusExponent valuation valuation_le primitiveCoefficient primitive

omit [Fintype R] [DecidableEq R] [SampleableType R]
  [Fintype Coordinate] [DecidableEq Coordinate] in
/-- For a scaled primitive row, membership in the row-combination image is
coordinatewise membership in the principal additive image generated by the scale. -/
theorem inRowCombinationRange_scaledPrimitive_iff
    (scale : R) (coefficient : Row → R)
    (primitive : HasUnitCoordinate coefficient) (target : Coordinate → R) :
    InRowCombinationRange (scaledCoefficient scale coefficient) target ↔
      ∀ coordinate,
        target coordinate ∈ (multiplyAddHom scale).range := by
  classical
  constructor
  · rintro ⟨matrix, hmatrix⟩ coordinate
    refine ⟨scalarCombination coefficient
      (fun row ↦ matrix row coordinate), ?_⟩
    change scalarCombination coefficient
        (fun row ↦ matrix row coordinate) * scale = target coordinate
    rw [← congrFun hmatrix coordinate]
    change scalarCombination coefficient
        (fun row ↦ matrix row coordinate) * scale =
      scalarCombination (scaledCoefficient scale coefficient)
        (fun row ↦ matrix row coordinate)
    rw [scalarCombination_scaledCoefficient, mul_comm]
  · intro htarget
    choose scalar hscalar using htarget
    have scalarSurjective := scalarCombination_surjective coefficient primitive
    choose vector hvector using fun coordinate ↦ scalarSurjective (scalar coordinate)
    let matrix : Matrix Row Coordinate R := fun row coordinate ↦
      vector coordinate row
    refine ⟨matrix, ?_⟩
    funext coordinate
    change scalarCombination (scaledCoefficient scale coefficient)
        (vector coordinate) = target coordinate
    rw [scalarCombination_scaledCoefficient, hvector coordinate]
    have hscalarCoordinate := hscalar coordinate
    change scalar coordinate * scale = target coordinate at hscalarCoordinate
    simpa [mul_comm] using hscalarCoordinate

/-- Exact union bound for one `2^valuation` stratum.  Only residuals compatible
with the actual additive image contribute. -/
theorem powerOfTwoStratumFactorizationSuccess_le
    (modulusExponent valuation : ℕ) (valuation_le : valuation ≤ modulusExponent)
    (postprocessCandidates :
      Finset (Row → ZMod (2 ^ modulusExponent)))
    (residualCandidates :
      Finset (Coordinate → ZMod (2 ^ modulusExponent)))
    (target : Coordinate → ZMod (2 ^ modulusExponent))
    (stratum : ∀ coefficient ∈ postprocessCandidates,
      IsPowerOfTwoStratum modulusExponent valuation coefficient) :
    Pr[(fun matrix : Matrix Row Coordinate (ZMod (2 ^ modulusExponent)) ↦
          ∃ coefficient ∈ postprocessCandidates,
            ∃ residual ∈ residualCandidates,
              rowCombination coefficient matrix = target + residual) |
        ($ᵗ Matrix Row Coordinate (ZMod (2 ^ modulusExponent)))] ≤
      ∑ coefficient ∈ postprocessCandidates,
        (compatibleResidualCandidates coefficient target residualCandidates).card *
          ((2 : ENNReal) ^
            ((modulusExponent - valuation) * Fintype.card Coordinate))⁻¹ := by
  calc
    Pr[(fun matrix : Matrix Row Coordinate (ZMod (2 ^ modulusExponent)) ↦
          ∃ coefficient ∈ postprocessCandidates,
            ∃ residual ∈ residualCandidates,
              rowCombination coefficient matrix = target + residual) |
        ($ᵗ Matrix Row Coordinate (ZMod (2 ^ modulusExponent)))] ≤
        ∑ coefficient ∈ postprocessCandidates,
          (compatibleResidualCandidates coefficient target residualCandidates).card *
            (Fintype.card
              (rowCombination (Coordinate := Coordinate) coefficient).range :
                ENNReal)⁻¹ :=
      imageAwareTwoBudgetFactorizationSuccess_le
        postprocessCandidates residualCandidates target
    _ = ∑ coefficient ∈ postprocessCandidates,
        (compatibleResidualCandidates coefficient target residualCandidates).card *
          ((2 : ENNReal) ^
            ((modulusExponent - valuation) * Fintype.card Coordinate))⁻¹ := by
      apply Finset.sum_congr rfl
      intro coefficient hcoefficient
      rw [card_rowCombination_range_of_powerOfTwoStratum
        modulusExponent valuation valuation_le coefficient
          (stratum coefficient hcoefficient)]
      norm_cast

/-- Mixed-stratum form: every candidate row contributes with its own exact
`2`-adic image entropy.  This is the direct nonprimitive replacement for the
primitive-only `|R|^n` denominator. -/
theorem powerOfTwoStrataFactorizationSuccess_le
    (modulusExponent : ℕ)
    (postprocessCandidates :
      Finset (Row → ZMod (2 ^ modulusExponent)))
    (residualCandidates :
      Finset (Coordinate → ZMod (2 ^ modulusExponent)))
    (target : Coordinate → ZMod (2 ^ modulusExponent))
    (rowValuation : (Row → ZMod (2 ^ modulusExponent)) → ℕ)
    (valuation_le : ∀ coefficient ∈ postprocessCandidates,
      rowValuation coefficient ≤ modulusExponent)
    (stratum : ∀ coefficient ∈ postprocessCandidates,
      IsPowerOfTwoStratum modulusExponent (rowValuation coefficient) coefficient) :
    Pr[(fun matrix : Matrix Row Coordinate (ZMod (2 ^ modulusExponent)) ↦
          ∃ coefficient ∈ postprocessCandidates,
            ∃ residual ∈ residualCandidates,
              rowCombination coefficient matrix = target + residual) |
        ($ᵗ Matrix Row Coordinate (ZMod (2 ^ modulusExponent)))] ≤
      ∑ coefficient ∈ postprocessCandidates,
        (compatibleResidualCandidates coefficient target residualCandidates).card *
          ((2 : ENNReal) ^
            ((modulusExponent - rowValuation coefficient) *
              Fintype.card Coordinate))⁻¹ := by
  calc
    Pr[(fun matrix : Matrix Row Coordinate (ZMod (2 ^ modulusExponent)) ↦
          ∃ coefficient ∈ postprocessCandidates,
            ∃ residual ∈ residualCandidates,
              rowCombination coefficient matrix = target + residual) |
        ($ᵗ Matrix Row Coordinate (ZMod (2 ^ modulusExponent)))] ≤
        ∑ coefficient ∈ postprocessCandidates,
          (compatibleResidualCandidates coefficient target residualCandidates).card *
            (Fintype.card
              (rowCombination (Coordinate := Coordinate) coefficient).range :
                ENNReal)⁻¹ :=
      imageAwareTwoBudgetFactorizationSuccess_le
        postprocessCandidates residualCandidates target
    _ = ∑ coefficient ∈ postprocessCandidates,
        (compatibleResidualCandidates coefficient target residualCandidates).card *
          ((2 : ENNReal) ^
            ((modulusExponent - rowValuation coefficient) *
              Fintype.card Coordinate))⁻¹ := by
      apply Finset.sum_congr rfl
      intro coefficient hcoefficient
      rw [card_rowCombination_range_of_powerOfTwoStratum
        modulusExponent (rowValuation coefficient)
          (valuation_le coefficient hcoefficient) coefficient
          (stratum coefficient hcoefficient)]
      norm_cast

/-- Entropy-slack corollary for a fixed valuation stratum.  The residual budget
counts only targets compatible with that row's actual additive image. -/
theorem powerOfTwoStratumFactorizationSuccess_le_of_card_bounds
    (modulusExponent valuation : ℕ) (valuation_le : valuation ≤ modulusExponent)
    (postprocessCandidates :
      Finset (Row → ZMod (2 ^ modulusExponent)))
    (residualCandidates :
      Finset (Coordinate → ZMod (2 ^ modulusExponent)))
    (target : Coordinate → ZMod (2 ^ modulusExponent))
    (stratum : ∀ coefficient ∈ postprocessCandidates,
      IsPowerOfTwoStratum modulusExponent valuation coefficient)
    (postprocessBits compatibleResidualBits slack : ℕ)
    (postprocessBound : postprocessCandidates.card ≤ 2 ^ postprocessBits)
    (compatibleResidualBound : ∀ coefficient ∈ postprocessCandidates,
      (compatibleResidualCandidates coefficient target residualCandidates).card ≤
        2 ^ compatibleResidualBits)
    (entropyBalance :
      postprocessBits + compatibleResidualBits + slack =
        (modulusExponent - valuation) * Fintype.card Coordinate) :
    Pr[(fun matrix : Matrix Row Coordinate (ZMod (2 ^ modulusExponent)) ↦
          ∃ coefficient ∈ postprocessCandidates,
            ∃ residual ∈ residualCandidates,
              rowCombination coefficient matrix = target + residual) |
        ($ᵗ Matrix Row Coordinate (ZMod (2 ^ modulusExponent)))] ≤
      ((2 : ENNReal) ^ slack)⁻¹ := by
  calc
    Pr[(fun matrix : Matrix Row Coordinate (ZMod (2 ^ modulusExponent)) ↦
          ∃ coefficient ∈ postprocessCandidates,
            ∃ residual ∈ residualCandidates,
              rowCombination coefficient matrix = target + residual) |
        ($ᵗ Matrix Row Coordinate (ZMod (2 ^ modulusExponent)))] ≤
        ∑ coefficient ∈ postprocessCandidates,
          (compatibleResidualCandidates coefficient target residualCandidates).card *
            ((2 : ENNReal) ^
              ((modulusExponent - valuation) * Fintype.card Coordinate))⁻¹ :=
      powerOfTwoStratumFactorizationSuccess_le
        modulusExponent valuation valuation_le postprocessCandidates
          residualCandidates target stratum
    _ ≤ ∑ _coefficient ∈ postprocessCandidates,
          (2 ^ compatibleResidualBits : ENNReal) *
            ((2 : ENNReal) ^
              ((modulusExponent - valuation) * Fintype.card Coordinate))⁻¹ := by
      apply Finset.sum_le_sum
      intro coefficient hcoefficient
      gcongr
      exact_mod_cast compatibleResidualBound coefficient hcoefficient
    _ = (postprocessCandidates.card : ENNReal) *
          (2 ^ compatibleResidualBits : ENNReal) *
            ((2 : ENNReal) ^
              ((modulusExponent - valuation) * Fintype.card Coordinate))⁻¹ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      ring
    _ ≤ (2 ^ postprocessBits : ENNReal) *
          (2 ^ compatibleResidualBits : ENNReal) *
            ((2 : ENNReal) ^
              ((modulusExponent - valuation) * Fintype.card Coordinate))⁻¹ := by
      gcongr
      exact_mod_cast postprocessBound
    _ = ((2 : ENNReal) ^ slack)⁻¹ := by
      let common : ENNReal :=
        (2 : ENNReal) ^ postprocessBits * 2 ^ compatibleResidualBits
      have denominator_eq :
          (2 : ENNReal) ^
              ((modulusExponent - valuation) * Fintype.card Coordinate) =
            common * (2 : ENNReal) ^ slack := by
        dsimp only [common]
        rw [← entropyBalance, pow_add, pow_add]
      change common *
          ((2 : ENNReal) ^
            ((modulusExponent - valuation) * Fintype.card Coordinate))⁻¹ =
        ((2 : ENNReal) ^ slack)⁻¹
      have common_ne_zero : common ≠ 0 := by
        dsimp only [common]
        simp
      have common_ne_top : common ≠ ⊤ := by
        dsimp only [common]
        exact ENNReal.mul_ne_top (by simp) (by simp)
      rw [denominator_eq,
        ENNReal.mul_inv (Or.inl common_ne_zero) (Or.inl common_ne_top),
        ← mul_assoc,
        ENNReal.mul_inv_cancel common_ne_zero common_ne_top, one_mul]

/-! ## Automatic power-of-two row stratification -/

theorem exists_unit_power_factor (modulusExponent : ℕ)
    (value : ZMod (2 ^ modulusExponent)) :
    ∃ valuation ≤ modulusExponent,
      ∃ unit : ZMod (2 ^ modulusExponent),
        IsUnit unit ∧
          value = ((2 ^ valuation : ℕ) : ZMod (2 ^ modulusExponent)) * unit := by
  obtain ⟨divisor, hdivisor, unit, hunit, hvalue⟩ :=
    ZMod.eq_unit_mul_divisor value
  obtain ⟨valuation, hvaluation, rfl⟩ :=
    (Nat.dvd_prime_pow Nat.prime_two).mp hdivisor
  refine ⟨valuation, hvaluation, unit, hunit, ?_⟩
  simpa [mul_comm] using hvalue

theorem exists_powerOfTwoStratum
    {Row : Type} [Fintype Row] [Nonempty Row]
    (modulusExponent : ℕ)
    (coefficient : Row → ZMod (2 ^ modulusExponent)) :
    ∃ valuation ≤ modulusExponent,
      IsPowerOfTwoStratum modulusExponent valuation coefficient := by
  classical
  choose coordinateValuation hcoordinateValuation coordinateUnit
    hcoordinateUnit hcoordinateFactor using
      fun row ↦ exists_unit_power_factor modulusExponent (coefficient row)
  let rows : Finset Row := Finset.univ
  have rowsNonempty : rows.Nonempty := Finset.univ_nonempty
  let valuation := rows.inf' rowsNonempty coordinateValuation
  obtain ⟨pivot, _hpivotMem, hpivot⟩ :=
    Finset.exists_mem_eq_inf' rowsNonempty coordinateValuation
  have valuation_le_coordinate (row : Row) :
      valuation ≤ coordinateValuation row := by
    exact Finset.inf'_le coordinateValuation (Finset.mem_univ row)
  let primitiveCoefficient : Row → ZMod (2 ^ modulusExponent) := fun row ↦
    ((2 ^ (coordinateValuation row - valuation) : ℕ) :
      ZMod (2 ^ modulusExponent)) * coordinateUnit row
  refine ⟨valuation, ?_, primitiveCoefficient, ?_, ?_⟩
  · calc
      valuation ≤ coordinateValuation pivot := valuation_le_coordinate pivot
      _ ≤ modulusExponent := hcoordinateValuation pivot
  · refine ⟨pivot, ?_⟩
    have hpivotValuation : coordinateValuation pivot = valuation := hpivot.symm
    simp only [primitiveCoefficient, hpivotValuation, Nat.sub_self, pow_zero,
      Nat.cast_one, one_mul]
    exact hcoordinateUnit pivot
  · funext row
    simp only [scaledCoefficient, primitiveCoefficient]
    rw [← mul_assoc, ← Nat.cast_mul, ← pow_add]
    rw [Nat.add_sub_of_le (valuation_le_coordinate row)]
    exact hcoordinateFactor row

noncomputable def powerOfTwoRowValuation
    {Row : Type} [Fintype Row] [Nonempty Row]
    (modulusExponent : ℕ)
    (coefficient : Row → ZMod (2 ^ modulusExponent)) : ℕ := by
  classical
  exact Nat.find (exists_powerOfTwoStratum modulusExponent coefficient)

theorem powerOfTwoRowValuation_le
    {Row : Type} [Fintype Row] [Nonempty Row]
    (modulusExponent : ℕ)
    (coefficient : Row → ZMod (2 ^ modulusExponent)) :
    powerOfTwoRowValuation modulusExponent coefficient ≤ modulusExponent := by
  classical
  exact (Nat.find_spec
    (exists_powerOfTwoStratum modulusExponent coefficient)).1

theorem powerOfTwoRowValuation_stratum
    {Row : Type} [Fintype Row] [Nonempty Row]
    (modulusExponent : ℕ)
    (coefficient : Row → ZMod (2 ^ modulusExponent)) :
    IsPowerOfTwoStratum modulusExponent
      (powerOfTwoRowValuation modulusExponent coefficient) coefficient := by
  classical
  exact (Nat.find_spec
    (exists_powerOfTwoStratum modulusExponent coefficient)).2

/-- The automatically selected exponent is the least bounded exponent carrying
a power-of-two-stratum witness. -/
theorem powerOfTwoRowValuation_minimal
    {ActualRow : Type} [Fintype ActualRow] [Nonempty ActualRow]
    (modulusExponent valuation : ℕ)
    (coefficient : ActualRow → ZMod (2 ^ modulusExponent))
    (valuation_le : valuation ≤ modulusExponent)
    (stratum : IsPowerOfTwoStratum modulusExponent valuation coefficient) :
    powerOfTwoRowValuation modulusExponent coefficient ≤ valuation := by
  classical
  exact Nat.find_min'
    (exists_powerOfTwoStratum modulusExponent coefficient)
    ⟨valuation_le, stratum⟩

theorem card_rowCombination_range_eq_powerOfTwoRowValuation
    {Row Coordinate : Type}
    [Fintype Row] [Nonempty Row] [DecidableEq Row]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (modulusExponent : ℕ)
    (coefficient : Row → ZMod (2 ^ modulusExponent)) :
    Fintype.card
        (rowCombination (Coordinate := Coordinate) coefficient).range =
      2 ^ ((modulusExponent -
          powerOfTwoRowValuation modulusExponent coefficient) *
        Fintype.card Coordinate) := by
  exact card_rowCombination_range_of_powerOfTwoStratum
    modulusExponent (powerOfTwoRowValuation modulusExponent coefficient)
      (powerOfTwoRowValuation_le modulusExponent coefficient) coefficient
      (powerOfTwoRowValuation_stratum modulusExponent coefficient)

theorem automaticPowerOfTwoStrataFactorizationSuccess_le
    {Row Coordinate : Type}
    [Fintype Row] [Nonempty Row] [DecidableEq Row]
    [Fintype Coordinate] [DecidableEq Coordinate]
    (modulusExponent : ℕ)
    (postprocessCandidates :
      Finset (Row → ZMod (2 ^ modulusExponent)))
    (residualCandidates :
      Finset (Coordinate → ZMod (2 ^ modulusExponent)))
    (target : Coordinate → ZMod (2 ^ modulusExponent)) :
    Pr[(fun matrix : Matrix Row Coordinate (ZMod (2 ^ modulusExponent)) ↦
          ∃ coefficient ∈ postprocessCandidates,
            ∃ residual ∈ residualCandidates,
              rowCombination coefficient matrix = target + residual) |
        ($ᵗ Matrix Row Coordinate (ZMod (2 ^ modulusExponent)))] ≤
      ∑ coefficient ∈ postprocessCandidates,
        (compatibleResidualCandidates coefficient target residualCandidates).card *
          ((2 : ENNReal) ^
            ((modulusExponent -
                powerOfTwoRowValuation modulusExponent coefficient) *
              Fintype.card Coordinate))⁻¹ := by
  exact powerOfTwoStrataFactorizationSuccess_le
    modulusExponent postprocessCandidates residualCandidates target
      (powerOfTwoRowValuation modulusExponent)
      (fun coefficient _ ↦
        powerOfTwoRowValuation_le modulusExponent coefficient)
      (fun coefficient _ ↦
        powerOfTwoRowValuation_stratum modulusExponent coefficient)

end

end Counting

end FormalProof4FHE.TFHE.JointSubsetKeyBRKDelayedProjection
