/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.BoundedMoment
import FormalProof4FHE.Probability.FiniteSurjectiveFiber
import FormalProof4FHE.TFHE.JointSubsetKeyBRK
import FormalProof4FHE.TFHE.NativeDiagonalPairBinaryRank
import Mathlib.Analysis.Real.Sqrt
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Refined Joint Subset-Key BRK/KSK Simulation

This module develops four quantitative refinements of
`FormalProof4FHE.TFHE.JointSubsetKeyBRK`.

* A simulator may add correction noise.  Its complete joint law, including the public solver
  context, is compared with the prescribed KSK error law.
* Exact factorization is relaxed to `L A = G + R`; the resulting additional error is exactly
  `R Z`.
* A finite Mahalanobis-mixture theorem turns pointwise equal-covariance shift bounds into the
  square root of the expected energy.  A covariance-completion interface isolates the analytic
  continuous/discrete Gaussian obligation.
* A uniform-matrix counting theorem upper-bounds the probability that any member of a finite
  family of unit-coordinate coefficient vectors represents a prescribed gadget row.
* Binary full rank is lifted to an actual factorization over a power-of-two local ring, both for
  scalar `ZMod (2^k)` matrices and for the native power-of-two negacyclic ring.

The Gaussian sampler identities remain explicit certificate fields: Mathlib does not currently
provide the finite, wrapped, or rounded multivariate Gaussian theory needed to derive them from a
covariance matrix.  All algebra, mixture accounting, finite counting, and local-ring lifting is
proved natively.
-/

open Matrix OracleComp
open scoped ENNReal

namespace FormalProof4FHE.TFHE.JointSubsetKeyBRKRefined

/-! ## Approximate factorization and correction noise -/

section ApproximateFactorization

variable {R VZ W T : Type}
  [Semiring R]
  [AddCommMonoid VZ] [Module R VZ]
  [AddCommMonoid W] [Module R W]
  [AddCommMonoid T] [Module R T]

/-- A constrained solver with an explicit residual map: `L A = G + R`. -/
structure ApproximateFactorization
    (source : VZ →ₗ[R] W) (gadget : VZ →ₗ[R] T) where
  postprocess : W →ₗ[R] T
  residual : VZ →ₗ[R] T
  postprocess_comp : postprocess.comp source = gadget + residual

namespace ApproximateFactorization

variable {source : VZ →ₗ[R] W} {gadget : VZ →ₗ[R] T}

/-- Exact factorization is the zero-residual special case. -/
def ofExact
    (certificate : JointSubsetKeyBRK.Factorization source gadget) :
    ApproximateFactorization source gadget where
  postprocess := certificate.postprocess
  residual := 0
  postprocess_comp := by simpa using certificate.postprocess_comp

/-- Applying an approximate solver to a noisy source creates precisely the residual-secret
term `R z` in addition to the transformed source error. -/
theorem apply_real
    (certificate : ApproximateFactorization source gadget)
    (suffix : VZ) (error : W) :
    certificate.postprocess (source suffix + error) =
      gadget suffix +
        (certificate.residual suffix + certificate.postprocess error) := by
  rw [map_add]
  have hcomp := congrArg
    (fun map : VZ →ₗ[R] T ↦ map suffix) certificate.postprocess_comp
  change certificate.postprocess (source suffix) =
    gadget suffix + certificate.residual suffix at hcomp
  rw [hcomp]
  ac_rfl

/-- Add independent or context-dependent correction noise after constrained postprocessing. -/
def correctedKSKValue {Mask : Type} (mask : Mask) (prefixTerm correction : T)
    (certificate : ApproximateFactorization source gadget) (sourceBody : W) : Mask × T :=
  (mask, prefixTerm + certificate.postprocess sourceBody + correction)

/-- Complete error in the corrected approximate construction. -/
def correctedError
    (certificate : ApproximateFactorization source gadget)
    (suffix : VZ) (sourceError : W) (correction : T) : T :=
  certificate.residual suffix + certificate.postprocess sourceError + correction

/-- Corrected approximate-factorization identity

`L(Az + e) + f = Gz + (Rz + Le + f)`.
-/
theorem correctedKSKValue_real {Mask : Type}
    (mask : Mask) (prefixTerm correction : T)
    (certificate : ApproximateFactorization source gadget)
    (suffix : VZ) (sourceError : W) :
    certificate.correctedKSKValue mask prefixTerm correction
        (source suffix + sourceError) =
      JointSubsetKeyBRK.targetKSKValue mask prefixTerm (gadget suffix)
        (certificate.correctedError suffix sourceError correction) := by
  rw [correctedKSKValue, JointSubsetKeyBRK.targetKSKValue,
    certificate.apply_real]
  simp only [correctedError]
  ac_rfl

end ApproximateFactorization

end ApproximateFactorization

section CorrectionLaw

variable {State Error View : Type} [Add Error]

/-- Retain the complete public solver state together with the corrected derived error. -/
def correctedJointError
    (stateSampler : ProbComp State) (derived : State → Error)
    (correction : State → ProbComp Error) : ProbComp (State × Error) := do
  let state ← stateSampler
  let fresh ← correction state
  return (state, derived state + fresh)

/-- Prescribed KSK error sampled independently after retaining the same public solver state. -/
def prescribedJointError
    (stateSampler : ProbComp State) (prescribed : ProbComp Error) :
    ProbComp (State × Error) := do
  let state ← stateSampler
  let error ← prescribed
  return (state, error)

/-- Proof-carrying boundary for covariance completion or an exact convolution decomposition.
The equality is deliberately on the full joint state, so it proves that correction removes every
solver-dependent error correlation, not only the error marginals. -/
structure ExactCorrectionNoiseCertificate
    (stateSampler : ProbComp State) (derived : State → Error)
    (prescribed : ProbComp Error) where
  correction : State → ProbComp Error
  corrected_joint_law :
    evalDist (correctedJointError stateSampler derived correction) =
      evalDist (prescribedJointError stateSampler prescribed)

/-- Exact full-joint correction remains exact after assembling the public KSK view. -/
theorem ExactCorrectionNoiseCertificate.assembled_evalDist_eq
    {stateSampler : ProbComp State} {derived : State → Error}
    {prescribed : ProbComp Error}
    (certificate : ExactCorrectionNoiseCertificate stateSampler derived prescribed)
    (assemble : State × Error → View) :
    evalDist (assemble <$> correctedJointError stateSampler derived certificate.correction) =
      evalDist (assemble <$> prescribedJointError stateSampler prescribed) :=
  evalDist_map_eq_of_evalDist_eq certificate.corrected_joint_law assemble

/-- Exact correction pays zero total-variation noise defect in every assembled public view. -/
theorem ExactCorrectionNoiseCertificate.tvDist_assembled_eq_zero
    {stateSampler : ProbComp State} {derived : State → Error}
    {prescribed : ProbComp Error}
    (certificate : ExactCorrectionNoiseCertificate stateSampler derived prescribed)
    (assemble : State × Error → View) :
    tvDist
        (assemble <$> correctedJointError stateSampler derived certificate.correction)
        (assemble <$> prescribedJointError stateSampler prescribed) = 0 := by
  exact (tvDist_eq_zero_iff _ _).2 (certificate.assembled_evalDist_eq assemble)

/-- Approximate full-joint correction is preserved by arbitrary public postprocessing. -/
theorem tvDist_corrected_assembled_le
    (stateSampler : ProbComp State) (derived : State → Error)
    (correction : State → ProbComp Error) (prescribed : ProbComp Error)
    (assemble : State × Error → View) (error : ℝ)
    (herror :
      tvDist (correctedJointError stateSampler derived correction)
        (prescribedJointError stateSampler prescribed) ≤ error) :
    tvDist
        (assemble <$> correctedJointError stateSampler derived correction)
        (assemble <$> prescribedJointError stateSampler prescribed) ≤ error :=
  (tvDist_map_le assemble _ _).trans herror

end CorrectionLaw

/-! ## Covariance completion and Mahalanobis mixtures -/

section CovarianceCompletion

variable {SourceCoordinate TargetCoordinate : Type}
  [Fintype SourceCoordinate]

/-- Covariance that correction noise must contribute after the transformed source error. -/
def correctionCovariance
    (postprocess : Matrix TargetCoordinate SourceCoordinate ℝ)
    (sourceCovariance : Matrix SourceCoordinate SourceCoordinate ℝ)
    (targetCovariance : Matrix TargetCoordinate TargetCoordinate ℝ) :
    Matrix TargetCoordinate TargetCoordinate ℝ :=
  targetCovariance - postprocess * sourceCovariance * postprocess.transpose

/-- Covariance bookkeeping behind Gaussian correction. -/
theorem transformed_add_correctionCovariance
    (postprocess : Matrix TargetCoordinate SourceCoordinate ℝ)
    (sourceCovariance : Matrix SourceCoordinate SourceCoordinate ℝ)
    (targetCovariance : Matrix TargetCoordinate TargetCoordinate ℝ) :
    postprocess * sourceCovariance * postprocess.transpose +
        correctionCovariance postprocess sourceCovariance targetCovariance =
      targetCovariance := by
  simp [correctionCovariance]

/-- Analytic boundary for continuous, wrapped, or discrete Gaussian covariance completion.
`residualPSD` is the checkable matrix condition; `exactCorrection` records the sampler theorem
which must be supplied for the chosen Gaussian model. -/
structure GaussianCovarianceCompletionCertificate
    {State Error : Type} [Add Error]
    (stateSampler : ProbComp State) (derived : State → Error)
    (prescribed : ProbComp Error)
    (postprocess : Matrix TargetCoordinate SourceCoordinate ℝ)
    (sourceCovariance : Matrix SourceCoordinate SourceCoordinate ℝ)
    (targetCovariance : Matrix TargetCoordinate TargetCoordinate ℝ) where
  residualPSD :
    (correctionCovariance postprocess sourceCovariance targetCovariance).PosSemidef
  exactCorrection :
    ExactCorrectionNoiseCertificate stateSampler derived prescribed

theorem GaussianCovarianceCompletionCertificate.covariance_eq
    {State Error : Type} [Add Error]
    {stateSampler : ProbComp State} {derived : State → Error}
    {prescribed : ProbComp Error}
    {postprocess : Matrix TargetCoordinate SourceCoordinate ℝ}
    {sourceCovariance : Matrix SourceCoordinate SourceCoordinate ℝ}
    {targetCovariance : Matrix TargetCoordinate TargetCoordinate ℝ}
    (_certificate : GaussianCovarianceCompletionCertificate
      stateSampler derived prescribed postprocess sourceCovariance targetCovariance) :
    postprocess * sourceCovariance * postprocess.transpose +
        correctionCovariance postprocess sourceCovariance targetCovariance =
      targetCovariance :=
  transformed_add_correctionCovariance postprocess sourceCovariance targetCovariance

end CovarianceCompletion

section MahalanobisMixture

open FormalProof4FHE.BoundedMoment
open FormalProof4FHE.FiniteProduct

/-- Finite Jensen/Cauchy--Schwarz bound `E[sqrt X] ≤ sqrt(E[X])`, proved directly for the
real point masses of a `ProbComp`. -/
theorem expectation_sqrt_le_sqrt_expectation
    {Secret : Type} [Fintype Secret]
    (sampler : ProbComp Secret) (energy : Secret → ℝ)
    (energy_nonneg : ∀ secret, 0 ≤ energy secret) :
    expectation sampler (fun secret ↦ Real.sqrt (energy secret)) ≤
      Real.sqrt (expectation sampler energy) := by
  classical
  let weight : Secret → ℝ := fun secret ↦ Pr[= secret | sampler].toReal
  have weight_nonneg : ∀ secret, 0 ≤ weight secret := fun _ ↦ ENNReal.toReal_nonneg
  have weight_sum : ∑ secret, weight secret = 1 := by
    dsimp only [weight]
    rw [← ENNReal.toReal_sum (fun secret _ ↦ probOutput_ne_top),
      sum_probOutput_eq_one (by simp), ENNReal.toReal_one]
  have hrewrite (secret : Secret) :
      weight secret * Real.sqrt (energy secret) =
        Real.sqrt (weight secret) *
          Real.sqrt (weight secret * energy secret) := by
    rw [Real.sqrt_mul (weight_nonneg secret),
      ← mul_assoc, Real.mul_self_sqrt (weight_nonneg secret)]
  have hcauchy := Real.sum_sqrt_mul_sqrt_le
    (Finset.univ : Finset Secret) weight_nonneg
    (fun secret ↦ mul_nonneg (weight_nonneg secret) (energy_nonneg secret))
  simp_rw [← hrewrite] at hcauchy
  rw [weight_sum, Real.sqrt_one, one_mul] at hcauchy
  simpa [expectation, weight] using hcauchy

/-- Pointwise equal-covariance Gaussian shift estimates tensor through an arbitrary finite secret
mixture.  Only the pointwise analytic estimate is assumed; averaging and the square-root energy
bound are native. -/
theorem tvDist_mixture_le_half_sqrt_expectedEnergy
    {Secret Output : Type} [Fintype Secret]
    (secretSampler : ProbComp Secret)
    (shifted target : Secret → ProbComp Output)
    (energy : Secret → ℝ)
    (energy_nonneg : ∀ secret, 0 ≤ energy secret)
    (pointwise : ∀ secret,
      tvDist (shifted secret) (target secret) ≤
        Real.sqrt (energy secret) / 2) :
    tvDist (secretSampler >>= shifted) (secretSampler >>= target) ≤
      Real.sqrt (expectation secretSampler energy) / 2 := by
  classical
  have hbind := tvDist_bind_left_le_expectation secretSampler shifted target
  rw [tsum_fintype] at hbind
  calc
    tvDist (secretSampler >>= shifted) (secretSampler >>= target) ≤
        ∑ secret,
          Pr[= secret | secretSampler].toReal *
            tvDist (shifted secret) (target secret) := hbind
    _ ≤ ∑ secret,
          Pr[= secret | secretSampler].toReal *
            (Real.sqrt (energy secret) / 2) := by
      apply Finset.sum_le_sum
      intro secret _
      exact mul_le_mul_of_nonneg_left (pointwise secret) ENNReal.toReal_nonneg
    _ = expectation secretSampler (fun secret ↦ Real.sqrt (energy secret)) / 2 := by
      unfold expectation
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro secret _
      ring
    _ ≤ Real.sqrt (expectation secretSampler energy) / 2 := by
      gcongr
      exact expectation_sqrt_le_sqrt_expectation
        secretSampler energy energy_nonneg

/-- A proof-carrying ternary residual-energy bound.  For a centered ternary vector and residual
matrix `R`, the intended value of `traceEnergy` is
`tr(Σ_K⁻¹ R Σ_Z Rᵀ)`.  The exact moment calculation may be supplied by an IID or
fixed-weight ternary sampler theorem. -/
structure TernaryMahalanobisCertificate
    {Secret : Type} [Fintype Secret]
    (secretSampler : ProbComp Secret) (energy : Secret → ℝ) where
  traceEnergy : ℝ
  energy_nonneg : ∀ secret, 0 ≤ energy secret
  traceEnergy_nonneg : 0 ≤ traceEnergy
  expectedEnergy_le : expectation secretSampler energy ≤ traceEnergy

/-- The advertised ternary Mahalanobis defect after installing the exact second-moment bound. -/
theorem TernaryMahalanobisCertificate.tvDist_mixture_le
    {Secret Output : Type} [Fintype Secret]
    {secretSampler : ProbComp Secret} {energy : Secret → ℝ}
    (certificate : TernaryMahalanobisCertificate secretSampler energy)
    (shifted target : Secret → ProbComp Output)
    (pointwise : ∀ secret,
      tvDist (shifted secret) (target secret) ≤
        Real.sqrt (energy secret) / 2) :
    tvDist (secretSampler >>= shifted) (secretSampler >>= target) ≤
      Real.sqrt certificate.traceEnergy / 2 := by
  refine (tvDist_mixture_le_half_sqrt_expectedEnergy
    secretSampler shifted target energy certificate.energy_nonneg pointwise).trans ?_
  gcongr
  exact certificate.expectedEnergy_le

/-! ### Constructor-level consequence -/

open JointSubsetKeyBRK
open DirectSubsetKeyBRK

/-- Installing the ternary Mahalanobis estimate `noiseError ≤ sqrt(traceEnergy)/2` changes the
two-real-branch joint bound's noise contribution from `2 * noiseError` to one square-root energy
term. -/
theorem targetAdvantage_le_mahalanobis
    {Sample Secret Output Prefix View : Type} [Add Output]
    {problem : LearningWithErrors.Problem Sample Secret Output}
    {prefixSampler : ProbComp Prefix} {targetView : Bool → ProbComp View}
    {constructor : PublicViewConstructor problem prefixSampler targetView}
    (certificate : DefectCertificate constructor)
    (traceEnergy : ℝ)
    (noise_le : certificate.noiseError ≤ Real.sqrt traceEnergy / 2)
    (distinguisher : Distinguisher View) :
    targetAdvantage targetView distinguisher ≤
      2 * LearningWithErrors.advantage problem (constructor.reduction distinguisher) +
        2 * certificate.factorizationError + Real.sqrt traceEnergy +
        certificate.uniformError + certificate.auxiliaryError := by
  have hbase := certificate.targetAdvantage_le_two_source_add_joint_errors distinguisher
  linarith

/-! ### Exact IID centered-ternary residual energy -/

/-- Symmetric centered embedding of a ternary digit. -/
def centeredTernaryDigit (digit : Fin 3) : ℝ :=
  if digit = 0 then -1 else if digit = 1 then 0 else 1

@[simp]
theorem centeredTernaryDigit_zero : centeredTernaryDigit (0 : Fin 3) = -1 := by
  simp [centeredTernaryDigit]

@[simp]
theorem centeredTernaryDigit_one : centeredTernaryDigit (1 : Fin 3) = 0 := by
  simp [centeredTernaryDigit]

@[simp]
theorem centeredTernaryDigit_two : centeredTernaryDigit (2 : Fin 3) = 1 := by
  norm_num [centeredTernaryDigit, Fin.ext_iff]

/-- A uniform centered ternary digit has mean zero. -/
theorem mean_uniform_centeredTernaryDigit_eq_zero :
    mean ($ᵗ (Fin 3)) centeredTernaryDigit = 0 := by
  simp [mean, expectation, Fin.sum_univ_three, centeredTernaryDigit,
    probOutput_uniformSample, ENNReal.toReal_inv]

/-- A uniform centered ternary digit has second moment `2/3`. -/
theorem secondMoment_uniform_centeredTernaryDigit_eq_two_thirds :
    secondMoment ($ᵗ (Fin 3)) centeredTernaryDigit = 2 / 3 := by
  have htwoZero : (2 : Fin 3) ≠ 0 := by decide
  have htwoOne : (2 : Fin 3) ≠ 1 := by decide
  norm_num [secondMoment, expectation, Fin.sum_univ_three,
    centeredTernaryDigit, probOutput_uniformSample, ENNReal.toReal_inv,
    htwoZero, htwoOne]

/-- Squared Euclidean/Mahalanobis residual energy for an IID centered ternary vector.  A scalar
precision factor can be folded into the rows of `residual`. -/
def iidTernaryResidualEnergy {OutputCoordinate : Type} [Fintype OutputCoordinate]
    {dimension : ℕ} (residual : Matrix OutputCoordinate (Fin dimension) ℝ)
    (secret : Fin dimension → Fin 3) : ℝ :=
  ∑ output,
    (weightedSum (residual output) centeredTernaryDigit secret) ^ 2

/-- Exact expectation

`E[‖R Z‖²] = (2/3) ∑ᵢ,ⱼ Rᵢⱼ²`

for independent uniform centered ternary coordinates. -/
theorem expectation_iidTernaryResidualEnergy_eq
    {OutputCoordinate : Type} [Fintype OutputCoordinate]
    (dimension : ℕ) (residual : Matrix OutputCoordinate (Fin dimension) ℝ) :
    expectation
        (ProbComp.sampleIID dimension ($ᵗ (Fin 3)))
        (iidTernaryResidualEnergy residual) =
      (2 / 3 : ℝ) * ∑ output, ∑ coordinate, (residual output coordinate) ^ 2 := by
  classical
  unfold expectation
  calc
    (∑ secret,
        Pr[= secret | ProbComp.sampleIID dimension ($ᵗ (Fin 3))].toReal *
          iidTernaryResidualEnergy residual secret) =
        ∑ secret, ∑ output,
          Pr[= secret | ProbComp.sampleIID dimension ($ᵗ (Fin 3))].toReal *
            (weightedSum (residual output) centeredTernaryDigit secret) ^ 2 := by
      apply Finset.sum_congr rfl
      intro secret _
      rw [iidTernaryResidualEnergy, Finset.mul_sum]
    _ = ∑ output, ∑ secret,
          Pr[= secret | ProbComp.sampleIID dimension ($ᵗ (Fin 3))].toReal *
            (weightedSum (residual output) centeredTernaryDigit secret) ^ 2 := by
      rw [Finset.sum_comm]
    _ = ∑ output, secondMoment
          (ProbComp.sampleIID dimension ($ᵗ (Fin 3)))
          (weightedSum (residual output) centeredTernaryDigit) := by
      rfl
    _ = ∑ output, (2 / 3 : ℝ) *
          ∑ coordinate, residual output coordinate ^ 2 := by
      apply Finset.sum_congr rfl
      intro output _
      rw [secondMoment_sampleIID_weightedSum_eq
          ($ᵗ (Fin 3)) centeredTernaryDigit
          mean_uniform_centeredTernaryDigit_eq_zero,
        secondMoment_uniform_centeredTernaryDigit_eq_two_thirds]
    _ = (2 / 3 : ℝ) *
          ∑ output, ∑ coordinate, residual output coordinate ^ 2 := by
      rw [Finset.mul_sum]

/-- Ready-to-use Mahalanobis certificate for the exact IID ternary moment. -/
noncomputable def iidTernaryMahalanobisCertificate
    {OutputCoordinate : Type} [Fintype OutputCoordinate]
    (dimension : ℕ) (residual : Matrix OutputCoordinate (Fin dimension) ℝ) :
    TernaryMahalanobisCertificate
      (ProbComp.sampleIID dimension ($ᵗ (Fin 3)))
      (iidTernaryResidualEnergy residual) where
  traceEnergy := (2 / 3 : ℝ) *
    ∑ output, ∑ coordinate, (residual output coordinate) ^ 2
  energy_nonneg := by
    intro secret
    unfold iidTernaryResidualEnergy
    positivity
  traceEnergy_nonneg := by positivity
  expectedEnergy_le :=
    (expectation_iidTernaryResidualEnergy_eq dimension residual).le

end MahalanobisMixture

/-! ## A finite short-factorization counting barrier -/

section ShortFactorizationCounting

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
  instSampleableTypePiFintype

/-- Combine the rows of a public matrix using one candidate coefficient vector. -/
def rowCombination (coefficient : Row → R) :
    Matrix Row Coordinate R →+ (Coordinate → R) where
  toFun matrix coordinate :=
    ∑ row, coefficient row * matrix row coordinate
  map_zero' := by
    ext coordinate
    simp
  map_add' := by
    intro left right
    ext coordinate
    simp only [Pi.add_apply, Matrix.add_apply, mul_add, Finset.sum_add_distrib]

omit [Fintype R] [DecidableEq R] [SampleableType R] [DecidableEq Row]
    [Fintype Coordinate] [DecidableEq Coordinate] in
@[simp]
theorem rowCombination_apply
    (coefficient : Row → R) (matrix : Matrix Row Coordinate R)
    (coordinate : Coordinate) :
    rowCombination coefficient matrix coordinate =
      ∑ row, coefficient row * matrix row coordinate :=
  rfl

/-- A coefficient vector is primitive in the concrete sense needed here when one coordinate is a
unit.  Over `ZMod (2^k)`, this says that at least one coefficient is odd. -/
def HasUnitCoordinate (coefficient : Row → R) : Prop :=
  ∃ row, IsUnit (coefficient row)

omit [Fintype R] [DecidableEq R] [SampleableType R]
    [DecidableEq Row] [Fintype Coordinate] [DecidableEq Coordinate] in
/-- If a gadget row remains nonzero in a residue field, every coefficient vector representing it
has a unit coordinate.  This removes the primitiveness premise automatically for odd gadget rows
over a power-of-two local ring. -/
theorem hasUnitCoordinate_of_rowCombination_eq_of_mappedTarget_ne_zero
    {F : Type} [Field F] (hom : R →+* F) [IsLocalHom hom]
    (coefficient : Row → R) (matrix : Matrix Row Coordinate R)
    (target : Coordinate → R)
    (representation : rowCombination coefficient matrix = target)
    (mappedTarget_ne_zero : ∃ coordinate, hom (target coordinate) ≠ 0) :
    HasUnitCoordinate coefficient := by
  classical
  by_contra not_primitive
  rw [HasUnitCoordinate, not_exists] at not_primitive
  have mappedCoefficient_zero : ∀ row, hom (coefficient row) = 0 := by
    intro row
    by_contra mapped_ne_zero
    apply not_primitive row
    exact IsUnit.of_map hom (coefficient row)
      (isUnit_iff_ne_zero.mpr mapped_ne_zero)
  obtain ⟨coordinate, target_ne_zero⟩ := mappedTarget_ne_zero
  have hcoordinate := congrArg hom (congrFun representation coordinate)
  simp only [rowCombination_apply, map_sum, map_mul, mappedCoefficient_zero,
    zero_mul, Finset.sum_const_zero] at hcoordinate
  exact target_ne_zero hcoordinate.symm

omit [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Coordinate] [DecidableEq Coordinate] in
/-- A unit coordinate makes the row-combination map surjective: put the desired vector in that
one matrix row after multiplying by the inverse unit. -/
theorem rowCombination_surjective
    (coefficient : Row → R) (primitive : HasUnitCoordinate coefficient) :
    Function.Surjective (rowCombination (Coordinate := Coordinate) coefficient) := by
  classical
  obtain ⟨pivot, hpivot⟩ := primitive
  intro target
  let unit : Rˣ := hpivot.unit
  let preimage : Matrix Row Coordinate R := fun row coordinate ↦
    if row = pivot then (↑unit⁻¹ : R) * target coordinate else 0
  refine ⟨preimage, ?_⟩
  funext coordinate
  simp only [rowCombination_apply, preimage]
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

/-- A surjective additive map sends the uniform law on a finite group to the uniform law on its
codomain. -/
theorem evalDist_map_surjective_addHom_uniform
    {Domain Codomain : Type}
    [AddGroup Domain] [Fintype Domain] [SampleableType Domain]
    [AddGroup Codomain] [Fintype Codomain] [DecidableEq Codomain]
    [SampleableType Codomain]
    (transform : Domain →+ Codomain) (surjective : Function.Surjective transform) :
    evalDist (transform <$> ($ᵗ Domain)) = evalDist ($ᵗ Codomain) := by
  classical
  apply evalDist_ext
  intro output
  rw [probOutput_uniformSample Codomain output,
    probOutput_map_eq_sum_fintype_ite]
  simp only [probOutput_uniformSample Domain]
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have fiber_eq :
      (Finset.univ.filter fun input : Domain ↦ output = transform input).card =
        (Finset.univ.filter fun input : Domain ↦ transform input = 0).card := by
    rw [show (Finset.univ.filter fun input : Domain ↦ output = transform input) =
        Finset.univ.filter fun input : Domain ↦ transform input = output by
      ext input
      simp [eq_comm]]
    exact AddMonoidHom.card_fiber_eq_of_mem_range transform
      (Set.mem_range.2 (surjective output)) (Set.mem_range.2 (surjective 0))
  rw [fiber_eq]
  let zeroFiber :=
    (Finset.univ.filter fun input : Domain ↦ transform input = 0).card
  have zeroFiber_pos : 0 < zeroFiber := by
    apply Finset.card_pos.mpr
    exact ⟨0, by simp⟩
  have card_eq : zeroFiber * Fintype.card Codomain = Fintype.card Domain :=
    FormalProof4FHE.FiniteSurjectiveFiber.zeroFiberCard_mul_card_eq_card_of_surjective
      transform surjective
  have card_eq_ennreal :
      (zeroFiber : ENNReal) * (Fintype.card Codomain : ENNReal) =
        (Fintype.card Domain : ENNReal) := by
    exact_mod_cast card_eq
  change (zeroFiber : ENNReal) * (Fintype.card Domain : ENNReal)⁻¹ = _
  rw [← card_eq_ennreal]
  have inverse_mul :
      ((zeroFiber : ENNReal) * (Fintype.card Codomain : ENNReal))⁻¹ =
        (zeroFiber : ENNReal)⁻¹ *
          (Fintype.card Codomain : ENNReal)⁻¹ :=
    ENNReal.mul_inv
      (Or.inr (ENNReal.natCast_ne_top (Fintype.card Codomain)))
      (Or.inl (ENNReal.natCast_ne_top zeroFiber))
  rw [inverse_mul]
  rw [← mul_assoc, ENNReal.mul_inv_cancel
    (Nat.cast_ne_zero.mpr zeroFiber_pos.ne')
    (ENNReal.natCast_ne_top zeroFiber), one_mul]

/-- A fixed unit-coordinate coefficient vector represents any prescribed gadget row with exactly
`1 / |R|^n` probability for a uniform public matrix. -/
theorem probEvent_rowCombination_eq
    (coefficient : Row → R) (primitive : HasUnitCoordinate coefficient)
    (target : Coordinate → R) :
    Pr[(fun matrix : Matrix Row Coordinate R ↦
          rowCombination coefficient matrix = target) |
        ($ᵗ Matrix Row Coordinate R)] =
      (Fintype.card (Coordinate → R) : ENNReal)⁻¹ := by
  classical
  have mapped_uniform := evalDist_map_surjective_addHom_uniform
    (rowCombination (Coordinate := Coordinate) coefficient)
    (rowCombination_surjective coefficient primitive)
  calc
    Pr[(fun matrix : Matrix Row Coordinate R ↦
          rowCombination coefficient matrix = target) |
        ($ᵗ Matrix Row Coordinate R)] =
        Pr[(fun output : Coordinate → R ↦ output = target) |
          rowCombination coefficient <$> ($ᵗ Matrix Row Coordinate R)] := by
      rw [probEvent_map]
      rfl
    _ = Pr[(fun output : Coordinate → R ↦ output = target) |
          ($ᵗ (Coordinate → R))] :=
      probEvent_congr' (fun _ _ ↦ Iff.rfl) mapped_uniform
    _ = (Fintype.card (Coordinate → R) : ENNReal)⁻¹ := by
      rw [probEvent_uniformSample]
      have filter_eq :
          (Finset.univ.filter fun output : Coordinate → R ↦ output = target) =
            {target} := by
        ext output
        simp [eq_comm]
      rw [filter_eq]
      simp [div_eq_mul_inv]

/-- **Short-factorization counting obstruction.**  For any finite candidate family `C` whose
members have a unit coordinate,

`Pr[∃ ℓ ∈ C, ℓᵀ A = g] ≤ |C| / |R|^n`.

The family may be a centered coefficient box, an `ℓ₂` ball, a sparse alphabet, or any other
computationally selected short set. -/
theorem shortFactorizationSuccess_le
    (candidates : Finset (Row → R))
    (primitive : ∀ coefficient ∈ candidates, HasUnitCoordinate coefficient)
    (target : Coordinate → R) :
    Pr[(fun matrix : Matrix Row Coordinate R ↦
          ∃ coefficient ∈ candidates,
            rowCombination coefficient matrix = target) |
        ($ᵗ Matrix Row Coordinate R)] ≤
      (candidates.card : ENNReal) *
        (Fintype.card (Coordinate → R) : ENNReal)⁻¹ := by
  calc
    Pr[(fun matrix : Matrix Row Coordinate R ↦
          ∃ coefficient ∈ candidates,
            rowCombination coefficient matrix = target) |
        ($ᵗ Matrix Row Coordinate R)] ≤
        ∑ coefficient ∈ candidates,
          Pr[(fun matrix : Matrix Row Coordinate R ↦
              rowCombination coefficient matrix = target) |
            ($ᵗ Matrix Row Coordinate R)] :=
      probEvent_exists_finset_le_sum candidates
        ($ᵗ Matrix Row Coordinate R)
        (fun coefficient matrix ↦ rowCombination coefficient matrix = target)
    _ = ∑ _coefficient ∈ candidates,
          (Fintype.card (Coordinate → R) : ENNReal)⁻¹ := by
      apply Finset.sum_congr rfl
      intro coefficient hcoefficient
      rw [probEvent_rowCombination_eq coefficient
        (primitive coefficient hcoefficient) target]
    _ = (candidates.card : ENNReal) *
        (Fintype.card (Coordinate → R) : ENNReal)⁻¹ := by
      rw [Finset.sum_const, nsmul_eq_mul]

/-- Cardinality form of the same obstruction, exposing `|R|^n`. -/
theorem shortFactorizationSuccess_le_card_pow
    (candidates : Finset (Row → R))
    (primitive : ∀ coefficient ∈ candidates, HasUnitCoordinate coefficient)
    (target : Coordinate → R) :
    Pr[(fun matrix : Matrix Row Coordinate R ↦
          ∃ coefficient ∈ candidates,
            rowCombination coefficient matrix = target) |
        ($ᵗ Matrix Row Coordinate R)] ≤
      (candidates.card : ENNReal) *
        ((Fintype.card R : ENNReal) ^ Fintype.card Coordinate)⁻¹ := by
  simpa [Fintype.card_fun] using
    shortFactorizationSuccess_le candidates primitive target

/-- Unit-coordinate part of a finite candidate family. -/
noncomputable def primitiveCandidates (candidates : Finset (Row → R)) :
    Finset (Row → R) := by
  classical
  exact candidates.filter HasUnitCoordinate

/-- For a target nonzero in a residue field, arbitrary candidates can first be filtered to their
unit-coordinate members without changing the success event. -/
theorem shortFactorizationSuccess_le_primitive_filter
    {F : Type} [Field F] (hom : R →+* F) [IsLocalHom hom]
    (candidates : Finset (Row → R)) (target : Coordinate → R)
    (mappedTarget_ne_zero : ∃ coordinate, hom (target coordinate) ≠ 0) :
    Pr[(fun matrix : Matrix Row Coordinate R ↦
          ∃ coefficient ∈ candidates,
            rowCombination coefficient matrix = target) |
        ($ᵗ Matrix Row Coordinate R)] ≤
      ((primitiveCandidates candidates).card : ENNReal) *
        ((Fintype.card R : ENNReal) ^ Fintype.card Coordinate)⁻¹ := by
  classical
  calc
    Pr[(fun matrix : Matrix Row Coordinate R ↦
          ∃ coefficient ∈ candidates,
            rowCombination coefficient matrix = target) |
        ($ᵗ Matrix Row Coordinate R)] =
        Pr[(fun matrix : Matrix Row Coordinate R ↦
          ∃ coefficient ∈ primitiveCandidates candidates,
            rowCombination coefficient matrix = target) |
        ($ᵗ Matrix Row Coordinate R)] := by
      apply probEvent_congr' _ rfl
      intro matrix _
      constructor
      · rintro ⟨coefficient, hcoefficient, representation⟩
        refine ⟨coefficient, ?_, representation⟩
        change coefficient ∈ candidates.filter HasUnitCoordinate
        apply Finset.mem_filter.mpr
        refine ⟨hcoefficient, ?_⟩
        exact hasUnitCoordinate_of_rowCombination_eq_of_mappedTarget_ne_zero
          hom coefficient matrix target representation mappedTarget_ne_zero
      · rintro ⟨coefficient, hcoefficient, representation⟩
        change coefficient ∈ candidates.filter HasUnitCoordinate at hcoefficient
        exact ⟨coefficient, (Finset.mem_filter.mp hcoefficient).1, representation⟩
    _ ≤ ((primitiveCandidates candidates).card : ENNReal) *
        ((Fintype.card R : ENNReal) ^ Fintype.card Coordinate)⁻¹ := by
      apply shortFactorizationSuccess_le_card_pow
      intro coefficient hcoefficient
      change coefficient ∈ candidates.filter HasUnitCoordinate at hcoefficient
      exact (Finset.mem_filter.mp hcoefficient).2

/-- Any claimed high-probability bounded solver must meet the counting lower threshold. -/
theorem candidateRatio_ge_of_success_ge
    (candidates : Finset (Row → R))
    (primitive : ∀ coefficient ∈ candidates, HasUnitCoordinate coefficient)
    (target : Coordinate → R) (successLowerBound : ENNReal)
    (highSuccess : successLowerBound ≤
      Pr[(fun matrix : Matrix Row Coordinate R ↦
            ∃ coefficient ∈ candidates,
              rowCombination coefficient matrix = target) |
          ($ᵗ Matrix Row Coordinate R)]) :
    successLowerBound ≤
      (candidates.card : ENNReal) *
        ((Fintype.card R : ENNReal) ^ Fintype.card Coordinate)⁻¹ :=
  highSuccess.trans
    (shortFactorizationSuccess_le_card_pow candidates primitive target)

end

end ShortFactorizationCounting

/-! ## Binary-rank lifting over power-of-two local rings -/

section LocalRingFactorization

noncomputable section

open FormalProof4FHE.TFHE.Native.ShiftedCandidateEvaluator.DiagonalNormalForm

variable {R F Row Coordinate Output : Type}
  [CommRing R] [Field F]
  [Fintype Row] [DecidableEq Row]
  [Fintype Coordinate] [DecidableEq Coordinate]

/-- If reduction through a surjective local homomorphism makes `A` injective, every gadget matrix
has a factorization `L A = G` over the source ring. -/
theorem exists_matrix_factorization_of_map_mulVec_injective
    (hom : R →+* F) [IsLocalHom hom]
    (hom_surjective : Function.Surjective hom)
    (source : Matrix Row Coordinate R)
    (gadget : Matrix Output Coordinate R)
    (mapped_injective : Function.Injective (source.map hom).mulVec) :
    ∃ postprocess : Matrix Output Row R, postprocess * source = gadget := by
  classical
  have transpose_surjective : Function.Surjective source.transpose.mulVec := by
    apply mulVec_surjective_of_map_transpose_mulVec_injective
      hom hom_surjective source.transpose
    simpa only [Matrix.transpose_map, Matrix.transpose_transpose] using mapped_injective
  let preimage (output : Output) : Row → R :=
    Function.surjInv transpose_surjective (gadget output)
  let postprocess : Matrix Output Row R := fun output row ↦ preimage output row
  refine ⟨postprocess, ?_⟩
  ext output coordinate
  have hpreimage := Function.surjInv_eq
    transpose_surjective (gadget output)
  have hcoordinate := congrFun hpreimage coordinate
  simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct,
    Matrix.transpose_apply, postprocess, preimage, mul_comm] using hcoordinate

/-- Full column rank after reduction to the residue field is a convenient sufficient condition. -/
theorem exists_matrix_factorization_of_map_rank_eq_width
    (hom : R →+* F) [IsLocalHom hom]
    (hom_surjective : Function.Surjective hom)
    (source : Matrix Row Coordinate R)
    (gadget : Matrix Output Coordinate R)
    (fullRank : (source.map hom).rank = Fintype.card Coordinate) :
    ∃ postprocess : Matrix Output Row R, postprocess * source = gadget := by
  apply exists_matrix_factorization_of_map_mulVec_injective
    hom hom_surjective source gadget
  exact mulVec_injective_of_rank_eq_card_width (source.map hom) fullRank

/-- Convert a matrix product certificate into the exact linear-map factorization used by the
joint BRK/KSK theorem. -/
def matrixFactorizationOfProduct
    (source : Matrix Row Coordinate R) (gadget : Matrix Output Coordinate R)
    (postprocess : Matrix Output Row R) (product_eq : postprocess * source = gadget) :
    JointSubsetKeyBRK.Factorization source.mulVecLin gadget.mulVecLin where
  postprocess := postprocess.mulVecLin
  postprocess_comp := by
    rw [← Matrix.mulVecLin_mul, product_eq]

/-- Residue-field rank therefore supplies the exact `Factorization` object consumed by the joint
constructor theorem. -/
theorem exists_linearMap_factorization_of_map_rank_eq_width
    (hom : R →+* F) [IsLocalHom hom]
    (hom_surjective : Function.Surjective hom)
    (source : Matrix Row Coordinate R)
    (gadget : Matrix Output Coordinate R)
    (fullRank : (source.map hom).rank = Fintype.card Coordinate) :
    Nonempty (JointSubsetKeyBRK.Factorization source.mulVecLin gadget.mulVecLin) := by
  obtain ⟨postprocess, product_eq⟩ :=
    exists_matrix_factorization_of_map_rank_eq_width
      hom hom_surjective source gadget fullRank
  exact ⟨matrixFactorizationOfProduct source gadget postprocess product_eq⟩

/-- Entrywise matrix map as an additive homomorphism. -/
def matrixMapAddHom
    {S : Type} [AddCommGroup S] (hom : R →+ S) :
    Matrix Row Coordinate R →+ Matrix Row Coordinate S :=
  hom.mapMatrix

omit [Fintype Row] [DecidableEq Row] [Fintype Coordinate] [DecidableEq Coordinate] in
/-- A surjective coefficient map is surjective entrywise on finite matrices. -/
theorem matrixMapAddHom_surjective
    {S : Type} [AddCommGroup S] (hom : R →+ S)
    (hom_surjective : Function.Surjective hom) :
    Function.Surjective (matrixMapAddHom (Row := Row) (Coordinate := Coordinate) hom) := by
  classical
  intro target
  let preimage : Matrix Row Coordinate R := fun row coordinate ↦
    Function.surjInv hom_surjective (target row coordinate)
  refine ⟨preimage, ?_⟩
  ext row coordinate
  exact Function.surjInv_eq hom_surjective (target row coordinate)

/-! ### Scalar `ZMod (2^k)` specialization -/

/-- Binary full column rank lifts to every scalar power-of-two modulus. -/
theorem zmodPowerOfTwo_exists_matrix_factorization_of_binary_rank
    (modulusExponent : ℕ) (modulusExponent_positive : 0 < modulusExponent)
    (source : Matrix Row Coordinate (ZMod (2 ^ modulusExponent)))
    (gadget : Matrix Output Coordinate (ZMod (2 ^ modulusExponent)))
    (fullRank :
      (source.map
        (ZMod.castHom
          (pow_dvd_pow 2 (by omega : 1 ≤ modulusExponent)) (ZMod 2))).rank =
        Fintype.card Coordinate) :
    ∃ postprocess : Matrix Output Row (ZMod (2 ^ modulusExponent)),
      postprocess * source = gadget := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let heven : 2 ∣ 2 ^ modulusExponent :=
    pow_dvd_pow 2 (by omega : 1 ≤ modulusExponent)
  let parity : ZMod (2 ^ modulusExponent) →+* ZMod 2 :=
    ZMod.castHom heven (ZMod 2)
  letI : IsLocalHom parity :=
    FormalProof4FHE.TFHE.Native.PowerOfTwoLocalRing.isLocalHom_toZModTwo_of_nilpotent_kernel
      parity (by
        intro value parity_zero
        exact FormalProof4FHE.TFHE.Native.PowerOfTwoLocalRing.zmod_powerOfTwo_isNilpotent_of_castHom_eq_zero
            modulusExponent modulusExponent_positive value parity_zero)
  apply exists_matrix_factorization_of_map_rank_eq_width
    parity (ZMod.castHom_surjective heven) source gadget
  simpa [parity, heven] using fullRank

/-- Linear-map form of the scalar power-of-two lift. -/
theorem zmodPowerOfTwo_exists_linearMap_factorization_of_binary_rank
    (modulusExponent : ℕ) (modulusExponent_positive : 0 < modulusExponent)
    (source : Matrix Row Coordinate (ZMod (2 ^ modulusExponent)))
    (gadget : Matrix Output Coordinate (ZMod (2 ^ modulusExponent)))
    (fullRank :
      (source.map
        (ZMod.castHom
          (pow_dvd_pow 2 (by omega : 1 ≤ modulusExponent)) (ZMod 2))).rank =
        Fintype.card Coordinate) :
    Nonempty (JointSubsetKeyBRK.Factorization source.mulVecLin gadget.mulVecLin) := by
  obtain ⟨postprocess, product_eq⟩ :=
    zmodPowerOfTwo_exists_matrix_factorization_of_binary_rank
      modulusExponent modulusExponent_positive source gadget fullRank
  exact ⟨matrixFactorizationOfProduct source gadget postprocess product_eq⟩

/-- Failure of a constrained factorization over `ZMod (2^k)` is contained in binary rectangular
rank failure.  Coefficient reduction of the uniform source matrix is proved exactly uniform. -/
theorem zmodPowerOfTwo_factorizationFailure_le_binaryRankFailure
    (modulusExponent : ℕ) (modulusExponent_positive : 0 < modulusExponent)
    (rows columns outputs : ℕ)
    (gadget : Matrix (Fin outputs) (Fin columns) (ZMod (2 ^ modulusExponent))) :
    Pr[(fun source : Matrix (Fin rows) (Fin columns) (ZMod (2 ^ modulusExponent)) ↦
          ¬ ∃ postprocess : Matrix (Fin outputs) (Fin rows)
              (ZMod (2 ^ modulusExponent)),
            postprocess * source = gadget) |
        ($ᵗ Matrix (Fin rows) (Fin columns) (ZMod (2 ^ modulusExponent)))] ≤
      Pr[(fun binary : Matrix (Fin rows) (Fin columns) (ZMod 2) ↦
            binary.rank < columns) |
        ($ᵗ Matrix (Fin rows) (Fin columns) (ZMod 2))] := by
  classical
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let heven : 2 ∣ 2 ^ modulusExponent :=
    pow_dvd_pow 2 (by omega : 1 ≤ modulusExponent)
  let parity : ZMod (2 ^ modulusExponent) →+* ZMod 2 :=
    ZMod.castHom heven (ZMod 2)
  let matrixParity :
      Matrix (Fin rows) (Fin columns) (ZMod (2 ^ modulusExponent)) →+
        Matrix (Fin rows) (Fin columns) (ZMod 2) :=
    matrixMapAddHom parity.toAddMonoidHom
  have matrixParity_surjective : Function.Surjective matrixParity :=
    matrixMapAddHom_surjective parity.toAddMonoidHom
      (ZMod.castHom_surjective heven)
  have mapped_uniform :
      evalDist
          (matrixParity <$>
            ($ᵗ Matrix (Fin rows) (Fin columns) (ZMod (2 ^ modulusExponent)))) =
        evalDist ($ᵗ Matrix (Fin rows) (Fin columns) (ZMod 2)) :=
    evalDist_map_surjective_addHom_uniform matrixParity matrixParity_surjective
  calc
    Pr[(fun source : Matrix (Fin rows) (Fin columns) (ZMod (2 ^ modulusExponent)) ↦
          ¬ ∃ postprocess : Matrix (Fin outputs) (Fin rows)
              (ZMod (2 ^ modulusExponent)),
            postprocess * source = gadget) |
        ($ᵗ Matrix (Fin rows) (Fin columns) (ZMod (2 ^ modulusExponent)))] ≤
        Pr[(fun source : Matrix (Fin rows) (Fin columns) (ZMod (2 ^ modulusExponent)) ↦
            (source.map parity).rank < columns) |
          ($ᵗ Matrix (Fin rows) (Fin columns) (ZMod (2 ^ modulusExponent)))] := by
      apply probEvent_mono
      intro source _ factorizationFailure
      by_contra rankNotLess
      have fullRank : (source.map parity).rank = columns := by
        have rank_le : (source.map parity).rank ≤ columns := Matrix.rank_le_width _
        omega
      apply factorizationFailure
      exact zmodPowerOfTwo_exists_matrix_factorization_of_binary_rank
        modulusExponent modulusExponent_positive source gadget
          (by simpa [parity, heven] using fullRank)
    _ = Pr[(fun binary : Matrix (Fin rows) (Fin columns) (ZMod 2) ↦
            binary.rank < columns) |
          matrixParity <$>
            ($ᵗ Matrix (Fin rows) (Fin columns) (ZMod (2 ^ modulusExponent)))] := by
      rw [probEvent_map]
      rfl
    _ = Pr[(fun binary : Matrix (Fin rows) (Fin columns) (ZMod 2) ↦
            binary.rank < columns) |
          ($ᵗ Matrix (Fin rows) (Fin columns) (ZMod 2))] :=
      probEvent_congr' (fun _ _ ↦ Iff.rfl) mapped_uniform

/-- With `rows = columns + slack`, factorization failure has the standard binary-field tail. -/
theorem zmodPowerOfTwo_factorizationFailure_le
    (modulusExponent : ℕ) (modulusExponent_positive : 0 < modulusExponent)
    (dimension slack outputs : ℕ)
    (gadget : Matrix (Fin outputs) (Fin dimension) (ZMod (2 ^ modulusExponent))) :
    Pr[(fun source : Matrix (Fin (dimension + slack)) (Fin dimension)
          (ZMod (2 ^ modulusExponent)) ↦
          ¬ ∃ postprocess : Matrix (Fin outputs) (Fin (dimension + slack))
              (ZMod (2 ^ modulusExponent)),
            postprocess * source = gadget) |
        ($ᵗ Matrix (Fin (dimension + slack)) (Fin dimension)
          (ZMod (2 ^ modulusExponent)))] ≤
      2 / (2 : ENNReal) ^ (slack + 1) := by
  refine (zmodPowerOfTwo_factorizationFailure_le_binaryRankFailure
    modulusExponent modulusExponent_positive
    (dimension + slack) dimension outputs gadget).trans ?_
  simpa using
    (FormalProof4FHE.FiniteFieldRank.rankFailure_le
      (F := ZMod 2) dimension slack)

end

end LocalRingFactorization

end FormalProof4FHE.TFHE.JointSubsetKeyBRKRefined
