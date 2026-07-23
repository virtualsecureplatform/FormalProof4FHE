/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AsymptoticAdaptiveAugmentedCandidateView
import FormalProof4FHE.TFHE.AsymptoticNativeShiftedDiscreteGaussianBounds
import FormalProof4FHE.TFHE.NativeCoupledShiftedResidualBounds
import FormalProof4FHE.TFHE.NativeAdaptivePostEvaluationSmudging
import FormalProof4FHE.TFHE.NativeAdaptiveMaskCollision
import FormalProof4FHE.TFHE.NativeStaticMaskDiagonalReduction
import FormalProof4FHE.TFHE.NativeDiagonalGlobalBudgetObstruction
import FormalProof4FHE.TFHE.NativeDiagonalRetainedFiberCokernel
import FormalProof4FHE.TFHE.NativeDiagonalRetainedFiberCharacterRowSum
import FormalProof4FHE.TFHE.NativeCenteredBinomialSourceParity
import FormalProof4FHE.TFHE.NativeDiagonalUnitRowSlice
import FormalProof4FHE.Probability.FinitePMFCompilerApproximation
import FormalProof4FHE.TFHE.SymmetricDiscreteGaussianSampler
import FormalProof4FHE.TFHE.NativeWrongControlFiberBound
import FormalProof4FHE.TFHE.NativeDiagonalResidualNormalForm
import FormalProof4FHE.TFHE.NativeOffDiagonalDigitNormalForm

/-!
# Security-Only Growing TFHE with a Discrete-Gaussian BRK Target

This module gives the native one-shot circular-security reduction a nondegenerate parameter family
whose checked discrete-Gaussian smudging window is exponentially large.  Ring dimension and
centered-binomial source width remain polynomial.  The coefficient modulus is

`(2N)^(lambda + 1)`,

so its bit length is polynomial, the exact base-`2N` gadget has `lambda + 1` levels, and relative
Gaussian width `1 / (2N)` gives integer standard deviation `(2N)^lambda >= 2^lambda`.

No correctness claim is made.  The purpose of this family is to expose a sound security-only
boundary without pretending that the existing polynomial modulus supports an exponential
smudging window.  The preferred endpoint explicitly adds fresh wide BRK body noise after native
candidate evaluation.  It internalizes finite-Gaussian compilation and conditional translation
loss, and exact uniform invariance preserves the generated-control wrong-view bound.  The remaining
security work is the canonical pre-smudging mask/residual-correlation estimate, the exact
control-failure estimate, and the native circular coordinate-prediction premise.
-/

open ENNReal OracleComp Filter Topology

namespace FormalProof4FHE.TFHE.DiscreteGaussianTarget.GrowingNoise

open Encryption.Adaptive.Asymptotic
open CenteredBinomial.GrowingNoiseEndToEnd
open Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery
open Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery.AugmentedResidual
open Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery.AugmentedResidual.NativeShifted

noncomputable section

/-- The native negacyclic ring size, written in the `degree + 1` form expected by the
candidate-view compiler. -/
abbrev nativeRingDegree (securityParameter : ℕ) : ℕ :=
  rotationDegree securityParameter + 1

@[simp]
theorem nativeRingDegree_eq_ringDegree (securityParameter : ℕ) :
    nativeRingDegree securityParameter = ringDegree securityParameter :=
  rotationDegree_add_one securityParameter

/-- Exact gadget base and native rotation order. -/
def gaussianBase (securityParameter : ℕ) : ℕ :=
  2 * ringDegree securityParameter

/-- A linearly growing exact gadget depth. -/
def gaussianLevels (securityParameter : ℕ) : ℕ :=
  securityParameter + 1

/-- Binary exponent of the canonical coefficient modulus. -/
def gaussianModulusExponent (securityParameter : ℕ) : ℕ :=
  (ringExponent securityParameter + 1) * gaussianLevels securityParameter

/-- Exponential numerical modulus with polynomial bit length. -/
def gaussianModulus (securityParameter : ℕ) : ℕ :=
  gaussianBase securityParameter ^ gaussianLevels securityParameter

theorem gaussianBase_eq_two_pow (securityParameter : ℕ) :
    gaussianBase securityParameter = 2 ^ (ringExponent securityParameter + 1) := by
  rw [gaussianBase, ringDegree_eq_two_pow_ringExponent, pow_succ]
  omega

theorem gaussianModulus_eq_two_pow (securityParameter : ℕ) :
    gaussianModulus securityParameter =
      2 ^ gaussianModulusExponent securityParameter := by
  rw [gaussianModulus, gaussianBase_eq_two_pow]
  exact (pow_mul 2 (ringExponent securityParameter + 1)
    (gaussianLevels securityParameter)).symm

theorem gaussianModulusExponent_pos (securityParameter : ℕ) :
    0 < gaussianModulusExponent securityParameter := by
  unfold gaussianModulusExponent gaussianLevels
  exact Nat.mul_pos (by omega) (by omega)

theorem one_lt_gaussianBase (securityParameter : ℕ) :
    1 < gaussianBase securityParameter := by
  unfold gaussianBase
  have := ringDegree_pos securityParameter
  omega

theorem gaussianModulus_pos (securityParameter : ℕ) :
    0 < gaussianModulus securityParameter := by
  exact Nat.pow_pos (Nat.zero_lt_of_lt (one_lt_gaussianBase securityParameter))

theorem two_dvd_gaussianModulus (securityParameter : ℕ) :
    2 ∣ gaussianModulus securityParameter := by
  unfold gaussianModulus gaussianBase gaussianLevels
  exact dvd_trans ⟨ringDegree securityParameter, rfl⟩
    (dvd_pow_self _ (by omega))

theorem one_lt_gaussianModulus (securityParameter : ℕ) :
    1 < gaussianModulus securityParameter := by
  obtain ⟨factor, hfactor⟩ := two_dvd_gaussianModulus securityParameter
  have hpositive := gaussianModulus_pos securityParameter
  rw [hfactor] at hpositive ⊢
  omega

instance instGaussianModulusNeZero (securityParameter : ℕ) :
    NeZero (gaussianModulus securityParameter) :=
  ⟨Nat.ne_of_gt (gaussianModulus_pos securityParameter)⟩

instance instGaussianModulusOneLt (securityParameter : ℕ) :
    Fact (1 < gaussianModulus securityParameter) :=
  ⟨one_lt_gaussianModulus securityParameter⟩

instance instGaussianRqNontrivial (securityParameter : ℕ) :
    Nontrivial (RLWE.Rq (gaussianModulus securityParameter)
      (rotationDegree securityParameter + 1)) := by
  change Nontrivial
    (Vector (ZMod (gaussianModulus securityParameter))
      (rotationDegree securityParameter + 1))
  exact Function.Injective.nontrivial
    (f := fun value : ZMod (gaussianModulus securityParameter) ↦
      Vector.replicate (rotationDegree securityParameter + 1) value)
    (by
      intro left right heq
      have hget := congrArg
        (fun value ↦ value.get ⟨0, by omega⟩) heq
      simpa using hget)

/-- Exact base decomposition at the exponential modulus. -/
def gaussianDecomposition (securityParameter : ℕ) :
    Gadget.Base.Parameters (gaussianModulus securityParameter) where
  base := gaussianBase securityParameter
  levels := gaussianLevels securityParameter
  one_lt_base := one_lt_gaussianBase securityParameter
  modulus_le_capacity := le_rfl

theorem gaussianBase_le_modulus (securityParameter : ℕ) :
    (gaussianDecomposition securityParameter).base ≤ gaussianModulus securityParameter := by
  change gaussianBase securityParameter ≤
    gaussianBase securityParameter ^ gaussianLevels securityParameter
  rw [gaussianLevels, pow_succ]
  have hpow : 1 ≤ gaussianBase securityParameter ^ securityParameter := by
    exact Nat.one_le_pow securityParameter (gaussianBase securityParameter)
      (Nat.zero_lt_of_lt (one_lt_gaussianBase securityParameter))
  simpa only [one_mul] using
    Nat.mul_le_mul_right (gaussianBase securityParameter) hpow

/-- Inverse-polynomial relative Gaussian width. -/
def gaussianAlpha (securityParameter : ℕ) : ℝ :=
  1 / gaussianBase securityParameter

theorem gaussianAlpha_pos (securityParameter : ℕ) :
    0 < gaussianAlpha securityParameter := by
  unfold gaussianAlpha
  apply one_div_pos.mpr
  exact_mod_cast Nat.zero_lt_of_lt (one_lt_gaussianBase securityParameter)

/-- The corresponding integer standard deviation is exactly `(2N)^lambda`. -/
theorem integerStddev_eq_base_pow (securityParameter : ℕ) :
    ModularGaussian.integerStddev
        (gaussianModulus securityParameter) (gaussianAlpha securityParameter) =
      (gaussianBase securityParameter : ℝ) ^ securityParameter := by
  unfold ModularGaussian.integerStddev gaussianAlpha gaussianModulus gaussianLevels
  rw [pow_add, pow_one, Nat.cast_mul, Nat.cast_pow]
  have hbase : (gaussianBase securityParameter : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt
      (Nat.zero_lt_of_lt (one_lt_gaussianBase securityParameter))
  field_simp

/-- The checked Gaussian window dominates `2^lambda`. -/
theorem two_pow_le_integerStddev (securityParameter : ℕ) :
    ((2 ^ securityParameter : ℕ) : ℝ) ≤
      ModularGaussian.integerStddev
        (gaussianModulus securityParameter) (gaussianAlpha securityParameter) := by
  rw [integerStddev_eq_base_pow]
  have hbase : 2 ≤ gaussianBase securityParameter := by
    have := one_lt_gaussianBase securityParameter
    omega
  exact_mod_cast pow_le_pow_left' hbase securityParameter

/-- Executable finite Gaussian tables, one for each security parameter. -/
abbrev ScalarCertificateFamily :=
  (securityParameter : ℕ) →
    DiscreteGaussianSampler.ScalarCertificate
      (gaussianModulus securityParameter) (gaussianAlpha securityParameter)
      (gaussianAlpha_pos securityParameter)

/-! ## Canonical finite Gaussian certificates -/

/-- A denominator large enough to make canonical finite-PMF rounding error inverse exponential.
The two modulus factors cancel the cardinality terms in the generic finite-PMF compiler bound. -/
def certificateDenominator (securityParameter : ℕ) : ℕ :=
  gaussianModulus securityParameter * (gaussianModulus securityParameter + 1) *
    2 ^ securityParameter

theorem certificateDenominator_pos (securityParameter : ℕ) :
    0 < certificateDenominator securityParameter := by
  unfold certificateDenominator
  exact Nat.mul_pos
    (Nat.mul_pos (gaussianModulus_pos securityParameter)
      (Nat.succ_pos (gaussianModulus securityParameter)))
    (Nat.pow_pos (by omega))

/-- A canonical finite ticket-table approximation to the exact centered modular Gaussian.

This is a noncomputably selected finite witness because the ideal PMF has real-valued masses; it
does not assert that materializing the exponentially large table is a PPT implementation. -/
noncomputable def canonicalCertificate : ScalarCertificateFamily :=
  fun securityParameter ↦
    FinitePMFCompiler.TicketTable.roundedCertificate
      (ModularGaussian.torusDistribution
        (gaussianModulus securityParameter) (gaussianAlpha securityParameter)
        (gaussianAlpha_pos securityParameter)) 0
      (certificateDenominator securityParameter)
      (certificateDenominator_pos securityParameter)

/-- The canonical ticket table has inverse-exponentially small total-variation certificate
error. -/
theorem canonicalCertificate_bound_le (securityParameter : ℕ) :
    (canonicalCertificate securityParameter).bound ≤
      ((2 : ℝ≥0∞) ^ securityParameter)⁻¹ := by
  rw [canonicalCertificate,
    FinitePMFCompiler.TicketTable.roundedCertificate_bound]
  simp only [FinitePMFCompiler.TicketTable.roundedPointwiseBound, ZMod.card]
  have hdenominator :
      (certificateDenominator securityParameter : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (certificateDenominator_pos securityParameter)
  have hpointwiseFinite :
      ((gaussianModulus securityParameter + 1 : ℕ) /
          (certificateDenominator securityParameter : ℝ≥0∞)) ≠ ⊤ :=
    ENNReal.div_ne_top (ENNReal.natCast_ne_top _) hdenominator
  have hleftFinite :
      (gaussianModulus securityParameter : ℝ≥0∞) *
            ((gaussianModulus securityParameter + 1 : ℕ) /
              (certificateDenominator securityParameter : ℝ≥0∞)) /
          2 ≠ ⊤ :=
    ENNReal.div_ne_top
      (ENNReal.mul_ne_top (ENNReal.natCast_ne_top _) hpointwiseFinite) (by norm_num)
  have hrightFinite :
      ((2 : ℝ≥0∞) ^ securityParameter)⁻¹ ≠ ⊤ :=
    ENNReal.inv_ne_top.mpr (pow_ne_zero _ (by norm_num))
  apply (ENNReal.toReal_le_toReal hleftFinite hrightFinite).mp
  simp only [ENNReal.toReal_div, ENNReal.toReal_mul, ENNReal.toReal_natCast,
    ENNReal.toReal_inv, ENNReal.toReal_pow, ENNReal.toReal_ofNat]
  unfold certificateDenominator
  push_cast
  have hmodulus : (gaussianModulus securityParameter : ℝ) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt (gaussianModulus_pos securityParameter)
  have hmodulusSucc : (gaussianModulus securityParameter : ℝ) + 1 ≠ 0 := by
    positivity
  have hpow : (2 : ℝ) ^ securityParameter ≠ 0 := by positivity
  field_simp
  nlinarith

/-- The canonical finite Gaussian compilation error is negligible. -/
theorem canonicalCertificate_bound_negligible :
    negligible (fun securityParameter ↦
      (canonicalCertificate securityParameter).bound) :=
  negligible_of_le canonicalCertificate_bound_le
    Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView.negligible_inv_two_pow

/-- Centering the leftover tickets at zero preserves exact negation symmetry of the ideal
Gaussian in the canonical finite table. -/
theorem canonicalCertificate_ticketNegationSymmetric (securityParameter : ℕ) :
    DiscreteGaussianSampler.TicketNegationSymmetric
      (canonicalCertificate securityParameter) := by
  intro residue
  rw [canonicalCertificate,
    FinitePMFCompiler.TicketTable.roundedCertificate_table,
    FinitePMFCompiler.TicketTable.roundedTable_count,
    FinitePMFCompiler.TicketTable.roundedTable_count]
  unfold FinitePMFCompiler.TicketTable.roundedCount
  congr 1
  · unfold FinitePMFCompiler.TicketTable.floorCount
    rw [ModularGaussian.torusDistribution_apply_neg]
  · simp

/-- Exact capped one-row finite-fiber loss for the generated centered-binomial message-one
control at the growing parameters.  Capping by one preserves the TV upper bound and ensures that
rare pathological controls contribute only their probability.  This is the construction-specific
nonlinear quantity governing the complementary candidate; it contains no correctness event. -/
noncomputable def canonicalWrongViewFiberLoss (securityParameter : ℕ) : ℝ :=
  averagedCanonicalMessageOneControlCappedFiberLoss
    (degree := rotationDegree securityParameter) (ringRank := 1)
    (gaussianDecomposition securityParameter) (errorWidth securityParameter)

theorem canonicalWrongViewFiberLoss_nonneg (securityParameter : ℕ) :
    0 ≤ canonicalWrongViewFiberLoss securityParameter := by
  exact averagedCanonicalMessageOneControlCappedFiberLoss_nonneg
    (degree := rotationDegree securityParameter) (ringRank := 1)
    (gaussianDecomposition securityParameter) (errorWidth securityParameter)

/-- Exact probability that the normalized identity-plus-homogeneous-control map is not
bijective under the native generated message-one control law.  Unlike a rowwise distance bound,
this single event controls the complete wrong public view without a BRK-layout multiplier. -/
noncomputable def canonicalWrongViewNonbijectivityError
    (securityParameter : ℕ) : ℝ :=
  averagedCanonicalMessageOneControlFailure
    (degree := rotationDegree securityParameter) (ringRank := 1)
    (gaussianDecomposition securityParameter) (errorWidth securityParameter)

theorem canonicalWrongViewNonbijectivityError_nonneg (securityParameter : ℕ) :
    0 ≤ canonicalWrongViewNonbijectivityError securityParameter :=
  ENNReal.toReal_nonneg

/-- Type of the generated message-one control whose nonlinear row map governs the canonical
wrong view. -/
abbrev CanonicalMessageOneControl (securityParameter : ℕ) :=
  RingGSWCiphertext (gaussianModulus securityParameter)
    (nativeRingDegree securityParameter) 1
    (gaussianDecomposition securityParameter).levels

/-- Probability that a generated message-one control fails a caller-supplied analytic
certificate.  This is an actual probability under the native centered-binomial control law,
not a support-wise maximum. -/
noncomputable def canonicalWrongControlBadProbability
    (Good : ∀ securityParameter, CanonicalMessageOneControl securityParameter → Prop)
    (securityParameter : ℕ) : ℝ :=
  Pr[(fun control ↦ ¬ Good securityParameter control) |
    canonicalMessageOneControlSampler
      (degree := rotationDegree securityParameter) (ringRank := 1)
      (gaussianDecomposition securityParameter) (errorWidth securityParameter)].toReal

theorem canonicalWrongControlBadProbability_nonneg
    (Good : ∀ securityParameter, CanonicalMessageOneControl securityParameter → Prop)
    (securityParameter : ℕ) :
    0 ≤ canonicalWrongControlBadProbability Good securityParameter :=
  ENNReal.toReal_nonneg

/-- A support-wise second-moment estimate is needed only on a high-probability set of generated
controls.  Capping the fiber loss by one charges all exceptional controls by their probability. -/
theorem canonicalWrongViewFiberLoss_le_of_goodFiberSecondMoment
    (Good : ∀ securityParameter, CanonicalMessageOneControl securityParameter → Prop)
    (ε : ℕ → ℝ)
    (hsecond : ∀ securityParameter
      (control : CanonicalMessageOneControl securityParameter),
      control ∈ support
        (canonicalMessageOneControlSampler
          (degree := rotationDegree securityParameter) (ringRank := 1)
          (gaussianDecomposition securityParameter) (errorWidth securityParameter)) →
      Good securityParameter control →
        messageOneControlFiberSecondMoment
            (gaussianDecomposition securityParameter) control ≤
          messageOneRowCard (gaussianModulus securityParameter)
              (nativeRingDegree securityParameter) 1 *
            (1 + ε securityParameter))
    (securityParameter : ℕ) :
    canonicalWrongViewFiberLoss securityParameter ≤
      Real.sqrt (ε securityParameter) / 2 +
        canonicalWrongControlBadProbability Good securityParameter := by
  simpa only [canonicalWrongViewFiberLoss, canonicalWrongControlBadProbability,
    nativeRingDegree] using
    (averagedCanonicalMessageOneControlCappedFiberLoss_le_of_goodFiberSecondMoment
      (degree := rotationDegree securityParameter) (ringRank := 1)
      (gaussianDecomposition securityParameter) (errorWidth securityParameter)
      (Good securityParameter) (ε securityParameter)
      (hsecond securityParameter))

/-- Negligible good-control collision excess plus negligible bad-control probability imply
negligible canonical wrong-view fiber loss. -/
theorem canonicalWrongViewFiberLoss_negligible_of_goodFiberSecondMoment
    (Good : ∀ securityParameter, CanonicalMessageOneControl securityParameter → Prop)
    (ε : ℕ → ℝ)
    (hsecond : ∀ securityParameter
      (control : CanonicalMessageOneControl securityParameter),
      control ∈ support
        (canonicalMessageOneControlSampler
          (degree := rotationDegree securityParameter) (ringRank := 1)
          (gaussianDecomposition securityParameter) (errorWidth securityParameter)) →
      Good securityParameter control →
        messageOneControlFiberSecondMoment
            (gaussianDecomposition securityParameter) control ≤
          messageOneRowCard (gaussianModulus securityParameter)
              (nativeRingDegree securityParameter) 1 *
            (1 + ε securityParameter))
    (hgood : negligible (fun securityParameter ↦
      ENNReal.ofReal (Real.sqrt (ε securityParameter) / 2)))
    (hbad : negligible (fun securityParameter ↦
      ENNReal.ofReal (canonicalWrongControlBadProbability Good securityParameter))) :
    negligible (fun securityParameter ↦
      ENNReal.ofReal (canonicalWrongViewFiberLoss securityParameter)) := by
  apply negligible_of_le (g := fun securityParameter ↦
    ENNReal.ofReal (Real.sqrt (ε securityParameter) / 2) +
      ENNReal.ofReal (canonicalWrongControlBadProbability Good securityParameter))
  · intro securityParameter
    exact
      (ENNReal.ofReal_le_ofReal
        (canonicalWrongViewFiberLoss_le_of_goodFiberSecondMoment
          Good ε hsecond securityParameter)).trans
        ENNReal.ofReal_add_le
  · exact negligible_add hgood hbad

/-- Packaged analytic certificate for the canonical wrong-control map.  Unlike a uniform
support-wise hypothesis, it permits exceptional generated controls and charges only their
probability. -/
structure CanonicalWrongViewGoodControlCertificate where
  Good : ∀ securityParameter, CanonicalMessageOneControl securityParameter → Prop
  ε : ℕ → ℝ
  secondMoment : ∀ securityParameter
    (control : CanonicalMessageOneControl securityParameter),
    control ∈ support
      (canonicalMessageOneControlSampler
        (degree := rotationDegree securityParameter) (ringRank := 1)
        (gaussianDecomposition securityParameter) (errorWidth securityParameter)) →
    Good securityParameter control →
      messageOneControlFiberSecondMoment
          (gaussianDecomposition securityParameter) control ≤
        messageOneRowCard (gaussianModulus securityParameter)
            (nativeRingDegree securityParameter) 1 *
          (1 + ε securityParameter)
  goodError_negligible : negligible (fun securityParameter ↦
    ENNReal.ofReal (Real.sqrt (ε securityParameter) / 2))
  badProbability_negligible : negligible (fun securityParameter ↦
    ENNReal.ofReal (canonicalWrongControlBadProbability Good securityParameter))

theorem CanonicalWrongViewGoodControlCertificate.fiberLoss_negligible
    (certificate : CanonicalWrongViewGoodControlCertificate) :
    negligible (fun securityParameter ↦
      ENNReal.ofReal (canonicalWrongViewFiberLoss securityParameter)) :=
  canonicalWrongViewFiberLoss_negligible_of_goodFiberSecondMoment
    certificate.Good certificate.ε certificate.secondMoment
    certificate.goodError_negligible certificate.badProbability_negligible

/-- Complete wrong-view bound obtained by multiplying the normalized one-control fiber loss by
the exact number of transformed BRK data rows. -/
noncomputable def canonicalWrongViewFreshnessError (securityParameter : ℕ) : ℝ :=
  (ringDegree securityParameter *
      TGSW.rowCount 1 (gaussianDecomposition securityParameter).levels : ℕ) *
    canonicalWrongViewFiberLoss securityParameter

theorem canonicalWrongViewFreshnessError_nonneg (securityParameter : ℕ) :
    0 ≤ canonicalWrongViewFreshnessError securityParameter :=
  mul_nonneg (Nat.cast_nonneg _)
    (canonicalWrongViewFiberLoss_nonneg securityParameter)

/-- Security parameters with centered-binomial KSK/input errors and a certified discrete-Gaussian
BRK target. -/
noncomputable def parameters (certificate : ScalarCertificateFamily) : Parameters Bool where
  q := gaussianModulus
  degree := nativeRingDegree
  ringRank := fun _ ↦ 1
  tgswLevels := gaussianLevels
  lweDimension := ringDegree
  keySwitchLevels := gaussianLevels
  ringErrorSampler := fun securityParameter ↦
    DiscreteGaussianSampler.ringSampler
      (nativeRingDegree securityParameter) (certificate securityParameter)
  keySwitchErrorSampler := fun securityParameter ↦
    CenteredBinomial.scalarSampler
      (gaussianModulus securityParameter) (errorWidth securityParameter)
  inputErrorSampler := fun securityParameter ↦
    CenteredBinomial.scalarSampler
      (gaussianModulus securityParameter) (errorWidth securityParameter)
  tgswGadget := fun securityParameter ↦
    Gadget.Base.ringGadget (degree := nativeRingDegree securityParameter)
      (gaussianDecomposition securityParameter)
  keySwitchGadget := fun securityParameter ↦
    Gadget.Base.gadget (gaussianDecomposition securityParameter)
  encode := fun securityParameter ↦
    CenteredBinomialDivisibleRefresh.inputCode
      (gaussianModulus securityParameter) (rotationDegree securityParameter)

instance instParametersNeZero (certificate : ScalarCertificateFamily) :
    ∀ securityParameter, NeZero ((parameters certificate).q securityParameter) :=
  fun securityParameter ↦ instGaussianModulusNeZero securityParameter

/-- Polynomial growth of every factor multiplying the Gaussian compiler/window errors. -/
def polynomialGrowth :
    Native.ShiftedDiscreteGaussian.Asymptotic.PolynomialGrowth
      gaussianDecomposition nativeRingDegree (fun _ ↦ 1) ringDegree errorWidth where
  degreePolynomial := 16 * (Polynomial.X + 1)
  ringRankPolynomial := 1
  lweDimensionPolynomial := 16 * (Polynomial.X + 1)
  levelsPolynomial := Polynomial.X + 1
  basePolynomial := 2 * (16 * (Polynomial.X + 1))
  etaPolynomial := Polynomial.X + 1
  degree_le := by
    intro securityParameter
    simpa [errorWidth] using
      ringDegree_le_sixteen_mul_errorWidth securityParameter
  ringRank_le := by intro securityParameter; simp
  lweDimension_le := by
    intro securityParameter
    simpa [errorWidth] using
      ringDegree_le_sixteen_mul_errorWidth securityParameter
  levels_le := by intro securityParameter; simp [gaussianDecomposition, gaussianLevels]
  base_le := by
    intro securityParameter
    have hdegree := ringDegree_le_sixteen_mul_errorWidth securityParameter
    simp only [gaussianDecomposition, gaussianBase, Polynomial.eval_mul,
      Polynomial.eval_ofNat, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_one]
    simp only [errorWidth] at hdegree
    omega
  eta_le := by intro securityParameter; simp [errorWidth]

/-- A negligible normalized message-one fiber loss remains negligible after the complete
polynomial BRK-layout factor is charged. -/
theorem canonicalWrongViewFreshnessError_negligible
    (hfiber : negligible (fun securityParameter ↦
      ENNReal.ofReal (canonicalWrongViewFiberLoss securityParameter))) :
    negligible (fun securityParameter ↦
      ENNReal.ofReal (canonicalWrongViewFreshnessError securityParameter)) := by
  apply negligible_of_le (g := fun securityParameter ↦
    (polynomialGrowth.layoutPolynomial.eval securityParameter : ℕ) *
      ENNReal.ofReal (canonicalWrongViewFiberLoss securityParameter))
  · intro securityParameter
    rw [canonicalWrongViewFreshnessError,
      ENNReal.ofReal_mul (by positivity)]
    exact mul_le_mul_left
      (by exact_mod_cast
        polynomialGrowth.layoutCount_le_polynomial securityParameter)
      (ENNReal.ofReal (canonicalWrongViewFiberLoss securityParameter))
  · exact negligible_polynomial_mul hfiber polynomialGrowth.layoutPolynomial

/-- The robust good/bad-control fiber criterion propagates through the complete polynomial BRK
layout, yielding the wrong-view freshness premise used by the security game. -/
theorem canonicalWrongViewFreshnessError_negligible_of_goodFiberSecondMoment
    (Good : ∀ securityParameter, CanonicalMessageOneControl securityParameter → Prop)
    (ε : ℕ → ℝ)
    (hsecond : ∀ securityParameter
      (control : CanonicalMessageOneControl securityParameter),
      control ∈ support
        (canonicalMessageOneControlSampler
          (degree := rotationDegree securityParameter) (ringRank := 1)
          (gaussianDecomposition securityParameter) (errorWidth securityParameter)) →
      Good securityParameter control →
        messageOneControlFiberSecondMoment
            (gaussianDecomposition securityParameter) control ≤
          messageOneRowCard (gaussianModulus securityParameter)
              (nativeRingDegree securityParameter) 1 *
            (1 + ε securityParameter))
    (hgood : negligible (fun securityParameter ↦
      ENNReal.ofReal (Real.sqrt (ε securityParameter) / 2)))
    (hbad : negligible (fun securityParameter ↦
      ENNReal.ofReal (canonicalWrongControlBadProbability Good securityParameter))) :
    negligible (fun securityParameter ↦
      ENNReal.ofReal (canonicalWrongViewFreshnessError securityParameter)) :=
  canonicalWrongViewFreshnessError_negligible
    (canonicalWrongViewFiberLoss_negligible_of_goodFiberSecondMoment
      Good ε hsecond hgood hbad)

theorem CanonicalWrongViewGoodControlCertificate.freshnessError_negligible
    (certificate : CanonicalWrongViewGoodControlCertificate) :
    negligible (fun securityParameter ↦
      ENNReal.ofReal (canonicalWrongViewFreshnessError securityParameter)) :=
  canonicalWrongViewFreshnessError_negligible certificate.fiberLoss_negligible

/-- The complete coupled correct-side smudging term is negligible for this family whenever the
finite Gaussian compiler has negligible one-draw error. -/
theorem correctSmudgingError_negligible
    (certificate : ScalarCertificateFamily)
    (hcertificate : negligible (fun securityParameter ↦
      (certificate securityParameter).bound)) :
    negligible
      (Native.ShiftedDiscreteGaussian.Asymptotic.correctSmudgingError
        gaussianDecomposition gaussianAlpha gaussianAlpha_pos certificate
        nativeRingDegree (fun _ ↦ 1) ringDegree errorWidth) :=
  Native.ShiftedDiscreteGaussian.Asymptotic.correctSmudgingError_negligible_of_two_pow_window
    polynomialGrowth gaussianAlpha gaussianAlpha_pos certificate
      two_pow_le_integerStddev hcertificate

/-- The correct-side Gaussian smudging term is negligible for the canonical ticket tables, with
no sampler-approximation premise left to the caller. -/
theorem canonicalCorrectSmudgingError_negligible :
    negligible
      (Native.ShiftedDiscreteGaussian.Asymptotic.correctSmudgingError
        gaussianDecomposition gaussianAlpha gaussianAlpha_pos canonicalCertificate
        nativeRingDegree (fun _ ↦ 1) ringDegree errorWidth) :=
  correctSmudgingError_negligible canonicalCertificate
    canonicalCertificate_bound_negligible

/-! ## Direct native certificate family -/

/-- Narrow centered-binomial BRK sampler used by the search/candidate source. -/
noncomputable abbrev sourceRingErrorSampler (securityParameter : ℕ) :=
  RLWE.CenteredBinomial.sampler
    (gaussianModulus securityParameter) (nativeRingDegree securityParameter)
    (errorWidth securityParameter)

/-- High-probability local-ring predicate used by the distribution-weighted cokernel route: at
least one native TGSW source-error row has nonzero residue modulo the maximal ideal. -/
def canonicalSourceErrorHasNonzeroParity (securityParameter : ℕ) :
    Native.ShiftedCandidateEvaluator.DiagonalNormalForm.DiagonalErrorVector
      (gaussianModulus securityParameter) (rotationDegree securityParameter) 1
      (gaussianDecomposition securityParameter).levels → Prop :=
  Native.CenteredBinomialSourceParity.HasNonzeroParity
    (two_dvd_gaussianModulus securityParameter)

/-- The parity map for the canonical power-of-two coefficient ring reflects units. -/
theorem canonicalRqParityEval_isLocalHom (securityParameter : ℕ) :
    IsLocalHom
      (Native.ShiftedCandidateEvaluator.DiagonalNormalForm.rqParityEval
        (two_dvd_gaussianModulus securityParameter)
        (Nat.succ_pos (rotationDegree securityParameter))) := by
  exact
    Native.PowerOfTwoLocalRing.rqParityEval_isLocalHom_of_modulus_eq_powerOfTwo_of_degree_eq
      (two_dvd_gaussianModulus securityParameter)
      (gaussianModulusExponent securityParameter)
      (gaussianModulusExponent_pos securityParameter)
      (gaussianModulus_eq_two_pow securityParameter)
      (ringExponent securityParameter)
      ((rotationDegree_add_one securityParameter).trans
        (ringDegree_eq_two_pow_ringExponent securityParameter))
      (Nat.succ_pos (rotationDegree securityParameter))

/-- Consequently, every source-error vector in the canonical good event contains an actual unit
row in the native coefficient ring. -/
theorem canonicalSourceErrorHasNonzeroParity_exists_isUnit
    (securityParameter : ℕ)
    {sourceError :
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.DiagonalErrorVector
        (gaussianModulus securityParameter) (rotationDegree securityParameter) 1
        (gaussianDecomposition securityParameter).levels}
    (hgood : canonicalSourceErrorHasNonzeroParity securityParameter sourceError) :
    ∃ row, IsUnit (sourceError row) := by
  exact Native.CenteredBinomialSourceParity.hasNonzeroParity_exists_isUnit
    (two_dvd_gaussianModulus securityParameter)
    (canonicalRqParityEval_isLocalHom securityParameter) hgood

/-- Every canonical good source-error vector has a distinguished unit column giving the explicit
one-column-removed bound on all of its native retained transformed-error fibers. -/
theorem canonicalSourceErrorHasNonzeroParity_exists_unitColumn_fiberBound
    (securityParameter : ℕ) (candidate : Bool)
    {sourceError :
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.DiagonalErrorVector
        (gaussianModulus securityParameter) (rotationDegree securityParameter) 1
        (gaussianDecomposition securityParameter).levels}
    (hgood : canonicalSourceErrorHasNonzeroParity securityParameter sourceError) :
    ∃ selected :
        Native.ShiftedCandidateEvaluator.DiagonalNormalForm.DifferenceDigitColumn 1
          (gaussianDecomposition securityParameter).levels,
      IsUnit (sourceError (finProdFinEquiv selected)) ∧
      ∀ transformedError :
          Native.ShiftedCandidateEvaluator.DiagonalNormalForm.DiagonalErrorVector
            (gaussianModulus securityParameter) (rotationDegree securityParameter) 1
            (gaussianDecomposition securityParameter).levels,
        Native.ShiftedCandidateEvaluator.DiagonalNormalForm.fixedErrorDifferenceFiberCard
            (gaussianDecomposition securityParameter) candidate sourceError transformedError ≤
          (gaussianDecomposition securityParameter).base ^
            (TGSW.rowCount 1 (gaussianDecomposition securityParameter).levels *
              (TGSW.rowCount 1 (gaussianDecomposition securityParameter).levels - 1) *
              (rotationDegree securityParameter + 1)) := by
  exact Native.ShiftedCandidateEvaluator.DiagonalNormalForm.exists_unitColumn_fixedErrorDifferenceFiberCard_le_pow
      (gaussianDecomposition securityParameter) rfl
      (gaussianBase_le_modulus securityParameter) candidate sourceError
      (canonicalSourceErrorHasNonzeroParity_exists_isUnit securityParameter hgood)

/-- The canonical source-error property produced by the unit-column slice: one selected unit
column bounds every retained transformed-error fiber by the one-column-removed digit count. -/
def canonicalUnitColumnFiberBoundEvent
    (securityParameter : ℕ) (candidate : Bool)
    (sourceError :
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.DiagonalErrorVector
        (gaussianModulus securityParameter) (rotationDegree securityParameter) 1
        (gaussianDecomposition securityParameter).levels) : Prop :=
  ∃ selected :
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.DifferenceDigitColumn 1
        (gaussianDecomposition securityParameter).levels,
    IsUnit (sourceError (finProdFinEquiv selected)) ∧
    ∀ transformedError :
        Native.ShiftedCandidateEvaluator.DiagonalNormalForm.DiagonalErrorVector
          (gaussianModulus securityParameter) (rotationDegree securityParameter) 1
          (gaussianDecomposition securityParameter).levels,
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.fixedErrorDifferenceFiberCard
          (gaussianDecomposition securityParameter) candidate sourceError transformedError ≤
        (gaussianDecomposition securityParameter).base ^
          (TGSW.rowCount 1 (gaussianDecomposition securityParameter).levels *
            (TGSW.rowCount 1 (gaussianDecomposition securityParameter).levels - 1) *
            (rotationDegree securityParameter + 1))

theorem canonicalUnitColumnFiberBoundEvent_of_nonzeroParity
    (securityParameter : ℕ) (candidate : Bool)
    {sourceError :
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.DiagonalErrorVector
        (gaussianModulus securityParameter) (rotationDegree securityParameter) 1
        (gaussianDecomposition securityParameter).levels}
    (hgood : canonicalSourceErrorHasNonzeroParity securityParameter sourceError) :
    canonicalUnitColumnFiberBoundEvent securityParameter candidate sourceError := by
  exact canonicalSourceErrorHasNonzeroParity_exists_unitColumn_fiberBound
    securityParameter candidate hgood

/-- The exceptional source-error event has exact probability `2^{-rowCount}` under the actual
canonical centered-binomial product law. -/
theorem canonicalSourceErrorAllZeroParityProbability
    (securityParameter : ℕ) :
    Pr[(fun sourceError ↦
          ¬ canonicalSourceErrorHasNonzeroParity securityParameter sourceError) |
      ProbComp.sampleIID
        (TGSW.rowCount 1 (gaussianDecomposition securityParameter).levels)
        (sourceRingErrorSampler securityParameter)] =
      ((2 : ENNReal) ^
        TGSW.rowCount 1 (gaussianDecomposition securityParameter).levels)⁻¹ := by
  simpa only [canonicalSourceErrorHasNonzeroParity, sourceRingErrorSampler,
    nativeRingDegree, errorWidth, ENNReal.inv_pow] using
    (Native.CenteredBinomialSourceParity.probEvent_not_hasNonzeroParity_sampleIID
      (gaussianModulus securityParameter) (rotationDegree securityParameter)
      securityParameter
      (TGSW.rowCount 1 (gaussianDecomposition securityParameter).levels)
      (two_dvd_gaussianModulus securityParameter))

/-- The explicit unit-column retained-fiber bound fails with at most the exact all-zero-parity
probability. -/
theorem canonicalUnitColumnFiberBoundFailureProbability_le
    (securityParameter : ℕ) (candidate : Bool) :
    Pr[(fun sourceError ↦
          ¬ canonicalUnitColumnFiberBoundEvent securityParameter candidate sourceError) |
      ProbComp.sampleIID
        (TGSW.rowCount 1 (gaussianDecomposition securityParameter).levels)
        (sourceRingErrorSampler securityParameter)] ≤
      ((2 : ENNReal) ^
        TGSW.rowCount 1 (gaussianDecomposition securityParameter).levels)⁻¹ := by
  calc
    Pr[(fun sourceError ↦
          ¬ canonicalUnitColumnFiberBoundEvent securityParameter candidate sourceError) |
        ProbComp.sampleIID
          (TGSW.rowCount 1 (gaussianDecomposition securityParameter).levels)
          (sourceRingErrorSampler securityParameter)] ≤
        Pr[(fun sourceError ↦
            ¬ canonicalSourceErrorHasNonzeroParity securityParameter sourceError) |
          ProbComp.sampleIID
            (TGSW.rowCount 1 (gaussianDecomposition securityParameter).levels)
            (sourceRingErrorSampler securityParameter)] := by
      apply probEvent_mono
      intro sourceError _ hfailure hgood
      exact hfailure
        (canonicalUnitColumnFiberBoundEvent_of_nonzeroParity
          securityParameter candidate hgood)
    _ = ((2 : ENNReal) ^
          TGSW.rowCount 1 (gaussianDecomposition securityParameter).levels)⁻¹ :=
      canonicalSourceErrorAllZeroParityProbability securityParameter

/-- Real-valued bad-event field used by the native good/bad certificate, in exact closed form. -/
theorem canonicalSourceErrorBadProbability_eq
    (securityParameter : ℕ) :
    Native.ShiftedCandidateEvaluator.DiagonalNormalForm.sourceErrorBadProbability
        (gaussianDecomposition securityParameter)
        (sourceRingErrorSampler securityParameter)
        (canonicalSourceErrorHasNonzeroParity securityParameter) =
      (((2 : ENNReal) ^
        TGSW.rowCount 1 (gaussianDecomposition securityParameter).levels)⁻¹).toReal := by
  unfold Native.ShiftedCandidateEvaluator.DiagonalNormalForm.sourceErrorBadProbability
  rw [canonicalSourceErrorAllZeroParityProbability]

/-- The exact all-nonunit source-error probability is negligible for the canonical growing
family. -/
theorem canonicalSourceErrorBadProbability_negligible :
    negligible (fun securityParameter ↦ ENNReal.ofReal
      (Native.ShiftedCandidateEvaluator.DiagonalNormalForm.sourceErrorBadProbability
        (gaussianDecomposition securityParameter)
        (sourceRingErrorSampler securityParameter)
        (canonicalSourceErrorHasNonzeroParity securityParameter))) := by
  have heq :
      (fun securityParameter ↦ ENNReal.ofReal
        (Native.ShiftedCandidateEvaluator.DiagonalNormalForm.sourceErrorBadProbability
          (gaussianDecomposition securityParameter)
          (sourceRingErrorSampler securityParameter)
          (canonicalSourceErrorHasNonzeroParity securityParameter))) =
      (fun securityParameter ↦
        ((2 : ENNReal) ^
          TGSW.rowCount 1 (gaussianDecomposition securityParameter).levels)⁻¹) := by
    funext securityParameter
    rw [canonicalSourceErrorBadProbability_eq]
    exact ENNReal.ofReal_toReal
      (ENNReal.inv_ne_top.mpr (pow_ne_zero _ (by norm_num)))
  rw [heq]
  apply
    Encryption.Adaptive.Asymptotic.KeySwitchFirstFiniteView.binaryGuessingBound_negligible_of_securityParameter_le_dimension
  intro securityParameter
  simp only [TGSW.rowCount, gaussianDecomposition, gaussianLevels]
  omega

/-- Target certified discrete-Gaussian BRK sampler. -/
noncomputable abbrev targetRingErrorSampler
    (certificate : ScalarCertificateFamily) (securityParameter : ℕ) :=
  DiscreteGaussianSampler.ringSampler
    (nativeRingDegree securityParameter) (certificate securityParameter)

/-- Shared centered-binomial KSK and adaptive-input error sampler. -/
noncomputable abbrev scalarErrorSampler (securityParameter : ℕ) :=
  CenteredBinomial.scalarSampler
    (gaussianModulus securityParameter) (errorWidth securityParameter)

/-- Exact base gadget used by the scalar KSK. -/
abbrev keySwitchGadget (securityParameter : ℕ) :=
  Gadget.Base.gadget (gaussianDecomposition securityParameter)

/-- Direct executable native candidate certificate at one tape length. -/
abbrev DirectCertificateAt
    (certificate : ScalarCertificateFamily)
    (queryCount securityParameter : ℕ) :=
  DirectStatisticalCertificate
    (ringRank := 1) (lweDimension := ringDegree securityParameter)
    (queryCount := queryCount)
    (gaussianDecomposition securityParameter)
    (sourceRingErrorSampler securityParameter)
    (targetRingErrorSampler certificate securityParameter)
    (scalarErrorSampler securityParameter)
    (scalarErrorSampler securityParameter)
    (keySwitchGadget securityParameter)

/-- Direct native certificates uniformly available for every polynomial tape schedule. -/
abbrev DirectCertificateFamily (certificate : ScalarCertificateFamily) :=
  (queryCount : ℕ → ℕ) → (securityParameter : ℕ) →
    DirectCertificateAt certificate (queryCount securityParameter) securityParameter

/-- The selected diagonal is bounded without a caller-supplied distributional law: the checked
sharp operator theorem leaves exactly an averaged challenge-fiber loss plus a mixed transformed-
error distance, maximized over the two hidden scalar bits. -/
noncomputable def canonicalSharpDiagonalError (securityParameter : ℕ) : ℝ :=
  Native.ShiftedCandidateEvaluator.DiagonalNormalForm.worstCaseSharpDiagonalOperatorLoss
    (degree := rotationDegree securityParameter) (ringRank := 1)
    (gaussianDecomposition securityParameter)
    (sourceRingErrorSampler securityParameter)
    (targetRingErrorSampler canonicalCertificate securityParameter)

theorem canonicalSharpDiagonalError_nonneg (securityParameter : ℕ) :
    0 ≤ canonicalSharpDiagonalError securityParameter :=
  Native.ShiftedCandidateEvaluator.DiagonalNormalForm.worstCaseSharpDiagonalOperatorLoss_nonneg
    (degree := rotationDegree securityParameter) (ringRank := 1)
    (gaussianDecomposition securityParameter)
    (sourceRingErrorSampler securityParameter)
    (targetRingErrorSampler canonicalCertificate securityParameter)

/-- Actual generated-control off-diagonal replacement expectation, maximized over the finite
native secret pair but not over individual supported controls. -/
noncomputable def canonicalAveragedOffDiagonalError
    (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) : ℝ :=
  Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.worstCaseAveragedOffDiagonalReplacementDistance
    (degree := rotationDegree securityParameter) (ringRank := 1)
    (gaussianDecomposition securityParameter)
    (sourceRingErrorSampler securityParameter)
    (targetRingErrorSampler canonicalCertificate securityParameter)
    coordinate

theorem canonicalAveragedOffDiagonalError_nonneg
    (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) :
    0 ≤ canonicalAveragedOffDiagonalError securityParameter coordinate :=
  Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.worstCaseAveragedOffDiagonalReplacementDistance_nonneg
    (degree := rotationDegree securityParameter) (ringRank := 1)
    (gaussianDecomposition securityParameter)
    (sourceRingErrorSampler securityParameter)
    (targetRingErrorSampler canonicalCertificate securityParameter)
    coordinate

/-- Explicit generated-control residual-vector `L²` loss at the growing native parameters.  The
quantity contains the exact centered-binomial control law, uniform internal-product difference,
source-error convolution, compiled target-error masses, and complete off-diagonal layout. -/
noncomputable def canonicalAveragedOffDiagonalResidualL2Error
    (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) : ℝ :=
  Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.worstCaseAveragedOffDiagonalResidualL2Loss
    (degree := rotationDegree securityParameter) (ringRank := 1)
    (gaussianDecomposition securityParameter)
    (sourceRingErrorSampler securityParameter)
    (targetRingErrorSampler canonicalCertificate securityParameter)
    coordinate

theorem canonicalAveragedOffDiagonalResidualL2Error_nonneg
    (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) :
    0 ≤ canonicalAveragedOffDiagonalResidualL2Error securityParameter coordinate :=
  Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.worstCaseAveragedOffDiagonalResidualL2Loss_nonneg
    (degree := rotationDegree securityParameter) (ringRank := 1)
    (gaussianDecomposition securityParameter)
    (sourceRingErrorSampler securityParameter)
    (targetRingErrorSampler canonicalCertificate securityParameter)
    coordinate

/-- Error-only off-diagonal `L²` loss.  The generated TGSW control has been reduced exactly to
its centered-binomial error vector, so the finite maximum ranges only over the selected bit. -/
noncomputable def canonicalAveragedOffDiagonalErrorOnlyL2Error
    (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) : ℝ :=
  Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.worstCaseAveragedOffDiagonalErrorOnlyL2Loss
    (degree := rotationDegree securityParameter) (ringRank := 1)
    (gaussianDecomposition securityParameter)
    (sourceRingErrorSampler securityParameter)
    (targetRingErrorSampler canonicalCertificate securityParameter)
    coordinate

theorem canonicalAveragedOffDiagonalErrorOnlyL2Error_nonneg
    (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) :
    0 ≤ canonicalAveragedOffDiagonalErrorOnlyL2Error securityParameter coordinate :=
  Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.worstCaseAveragedOffDiagonalErrorOnlyL2Loss_nonneg
    (degree := rotationDegree securityParameter) (ringRank := 1)
    (gaussianDecomposition securityParameter)
    (sourceRingErrorSampler securityParameter)
    (targetRingErrorSampler canonicalCertificate securityParameter)
    coordinate

/-- Exact finite-count normal form of the canonical off-diagonal term.  Candidate symmetry has
removed the Boolean maximum, the outer expectation is a uniform average over centered-binomial
control coins, and every summand is an explicit real/ideal fiber-cardinality `L²` expression. -/
noncomputable def canonicalAveragedOffDiagonalFiberL2Error
    (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) : ℝ :=
  Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.averagedCenteredBinomialResidualFiberL2Loss
    (degree := rotationDegree securityParameter) (ringRank := 1)
    (gaussianDecomposition securityParameter) (errorWidth securityParameter)
    (canonicalCertificate securityParameter) false coordinate

/-- Fully explicit finite-count normal form of the canonical off-diagonal term.  At exact gadget
capacity the uniform difference ciphertext has been replaced by its IID base-digit tensor, so
the only random inputs left are independent digit, centered-binomial, and Gaussian-ticket
coordinates. -/
noncomputable def canonicalAveragedOffDiagonalDigitFiberL2Error
    (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) : ℝ :=
  Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.averagedCenteredBinomialDigitResidualFiberL2Loss
    (degree := rotationDegree securityParameter) (ringRank := 1)
    (gaussianDecomposition securityParameter) (errorWidth securityParameter)
    (canonicalCertificate securityParameter) false coordinate

/-- The former probabilistic/maximization presentation is exactly the finite-count normal form. -/
theorem canonicalAveragedOffDiagonalErrorOnlyL2Error_eq_fiber
    (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) :
    canonicalAveragedOffDiagonalErrorOnlyL2Error securityParameter coordinate =
      canonicalAveragedOffDiagonalFiberL2Error securityParameter coordinate := by
  unfold canonicalAveragedOffDiagonalErrorOnlyL2Error
    canonicalAveragedOffDiagonalFiberL2Error
  rw [Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.worstCaseAveragedOffDiagonalErrorOnlyL2Loss_centeredBinomial_eq_false]
  exact
    Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.averagedOffDiagonalErrorOnlyL2Loss_centeredBinomial_ringSampler_eq_fiber
      (degree := rotationDegree securityParameter) (ringRank := 1)
      (gaussianDecomposition securityParameter) (errorWidth securityParameter)
      (canonicalCertificate securityParameter) false coordinate

theorem canonicalAveragedOffDiagonalFiberL2Error_nonneg
    (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) :
    0 ≤ canonicalAveragedOffDiagonalFiberL2Error securityParameter coordinate := by
  rw [← canonicalAveragedOffDiagonalErrorOnlyL2Error_eq_fiber]
  exact canonicalAveragedOffDiagonalErrorOnlyL2Error_nonneg securityParameter coordinate

/-- The probabilistic off-diagonal loss is exactly the IID digit/bit-pair/ticket fiber count. -/
theorem canonicalAveragedOffDiagonalErrorOnlyL2Error_eq_digitFiber
    (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) :
    canonicalAveragedOffDiagonalErrorOnlyL2Error securityParameter coordinate =
      canonicalAveragedOffDiagonalDigitFiberL2Error securityParameter coordinate := by
  unfold canonicalAveragedOffDiagonalErrorOnlyL2Error
    canonicalAveragedOffDiagonalDigitFiberL2Error
  rw [Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.worstCaseAveragedOffDiagonalErrorOnlyL2Loss_centeredBinomial_eq_false]
  exact
    Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.averagedOffDiagonalErrorOnlyL2Loss_centeredBinomial_ringSampler_eq_digitFiber
      (degree := rotationDegree securityParameter) (ringRank := 1)
      (gaussianDecomposition securityParameter) rfl (errorWidth securityParameter)
      (canonicalCertificate securityParameter) false coordinate

theorem canonicalAveragedOffDiagonalDigitFiberL2Error_nonneg
    (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) :
    0 ≤ canonicalAveragedOffDiagonalDigitFiberL2Error securityParameter coordinate := by
  rw [← canonicalAveragedOffDiagonalErrorOnlyL2Error_eq_digitFiber]
  exact canonicalAveragedOffDiagonalErrorOnlyL2Error_nonneg securityParameter coordinate

/-- Exact finite worst-case distance for one conditionally residualized off-diagonal entry.
This definition maximizes over the complete native scalar- and ring-secret spaces and over the
exact source-generator support for the control ciphertext, so it is a canonical construction
quantity rather than a supplied law. -/
noncomputable def canonicalOffDiagonalOperatorError
    (securityParameter : ℕ)
    (coordinate outputCoordinate : Fin (ringDegree securityParameter)) : ℝ :=
  Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.worstCaseConditionalResidualDistance
    (degree := rotationDegree securityParameter) (ringRank := 1)
    (gaussianDecomposition securityParameter)
    (sourceRingErrorSampler securityParameter)
    (targetRingErrorSampler canonicalCertificate securityParameter)
    coordinate outputCoordinate

theorem canonicalOffDiagonalOperatorError_nonneg
    (securityParameter : ℕ)
    (coordinate outputCoordinate : Fin (ringDegree securityParameter)) :
    0 ≤ canonicalOffDiagonalOperatorError securityParameter coordinate outputCoordinate :=
  Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.worstCaseConditionalResidualDistance_nonneg
    (degree := rotationDegree securityParameter) (ringRank := 1)
    (gaussianDecomposition securityParameter)
    (sourceRingErrorSampler securityParameter)
    (targetRingErrorSampler canonicalCertificate securityParameter)
    coordinate outputCoordinate

/-- The remaining correct-side laws after the selected diagonal has been reduced internally to
its sharp finite operator quantities. -/
structure CanonicalOffDiagonalLaws where
  offDiagonalError : (securityParameter : ℕ) →
    Fin (ringDegree securityParameter) → Fin (ringDegree securityParameter) → ℝ
  offDiagonalError_nonneg : ∀ securityParameter coordinate outputCoordinate,
    0 ≤ offDiagonalError securityParameter coordinate outputCoordinate
  offDiagonalDistance_le : ∀ securityParameter coordinate,
    ∀ hidden : BinarySecret (ringDegree securityParameter),
    ∀ ringSecret : RingBinarySecret 1 (nativeRingDegree securityParameter),
    ∀ control ∈ support
      (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
        (gaussianDecomposition securityParameter)
        (sourceRingErrorSampler securityParameter)
        hidden ringSecret coordinate),
    ∀ outputCoordinate, outputCoordinate ≠ coordinate →
      tvDist
          (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.residualizedCoordinateSampler
            (gaussianDecomposition securityParameter)
            (sourceRingErrorSampler securityParameter)
            hidden ringSecret coordinate control outputCoordinate)
          (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
            (gaussianDecomposition securityParameter)
            (targetRingErrorSampler canonicalCertificate securityParameter)
            hidden ringSecret outputCoordinate) ≤
        offDiagonalError securityParameter coordinate outputCoordinate

/-- Canonical off-diagonal laws obtained by taking the finite worst-case native operator
distance.  No statistical inequality is requested from the caller; the remaining task is the
asymptotic analysis showing that the selected sum of these exact finite maxima is negligible. -/
noncomputable def canonicalOffDiagonalOperatorLaws : CanonicalOffDiagonalLaws where
  offDiagonalError := canonicalOffDiagonalOperatorError
  offDiagonalError_nonneg := canonicalOffDiagonalOperatorError_nonneg
  offDiagonalDistance_le := by
    intro securityParameter coordinate hidden ringSecret control hcontrol
      outputCoordinate _hne
    exact
      Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.tvDist_residualizedCoordinateSampler_directEntry_le_worstCase
        (degree := rotationDegree securityParameter) (ringRank := 1)
        (gaussianDecomposition securityParameter)
        (sourceRingErrorSampler securityParameter)
        (targetRingErrorSampler canonicalCertificate securityParameter)
        hidden ringSecret coordinate outputCoordinate control hcontrol

/-- Explicit correct-view laws for the canonical Gaussian target.  They isolate the only
remaining fixed-secret statistical comparisons: one diagonal entry and the conditionally
residualized off-diagonal entries.  Wrong-branch freshness is not a field because it is supplied
by `canonicalWrongViewFreshnessError` and the checked message-one fiber theorem. -/
structure CanonicalCorrectViewLaws where
  diagonalError : (securityParameter : ℕ) →
    Fin (ringDegree securityParameter) → ℝ
  offDiagonalError : (securityParameter : ℕ) →
    Fin (ringDegree securityParameter) → Fin (ringDegree securityParameter) → ℝ
  diagonalError_nonneg : ∀ securityParameter coordinate,
    0 ≤ diagonalError securityParameter coordinate
  offDiagonalError_nonneg : ∀ securityParameter coordinate outputCoordinate,
    0 ≤ offDiagonalError securityParameter coordinate outputCoordinate
  diagonalDistance_le : ∀ securityParameter coordinate,
    ∀ hidden : BinarySecret (ringDegree securityParameter),
    ∀ ringSecret : RingBinarySecret 1 (nativeRingDegree securityParameter),
      tvDist
          (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.diagonalExperiment
            (gaussianDecomposition securityParameter)
            (sourceRingErrorSampler securityParameter)
            hidden ringSecret coordinate)
          (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
            (gaussianDecomposition securityParameter)
            (targetRingErrorSampler canonicalCertificate securityParameter)
            hidden ringSecret coordinate) ≤
        diagonalError securityParameter coordinate
  offDiagonalDistance_le : ∀ securityParameter coordinate,
    ∀ hidden : BinarySecret (ringDegree securityParameter),
    ∀ ringSecret : RingBinarySecret 1 (nativeRingDegree securityParameter),
    ∀ control ∈ support
      (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
        (gaussianDecomposition securityParameter)
        (sourceRingErrorSampler securityParameter)
        hidden ringSecret coordinate),
    ∀ outputCoordinate, outputCoordinate ≠ coordinate →
      tvDist
          (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.residualizedCoordinateSampler
            (gaussianDecomposition securityParameter)
            (sourceRingErrorSampler securityParameter)
            hidden ringSecret coordinate control outputCoordinate)
          (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
            (gaussianDecomposition securityParameter)
            (targetRingErrorSampler canonicalCertificate securityParameter)
            hidden ringSecret outputCoordinate) ≤
        offDiagonalError securityParameter coordinate outputCoordinate

/-- Fill the selected diagonal law with the checked sharp operator reduction. -/
noncomputable def CanonicalOffDiagonalLaws.toCanonicalCorrectViewLaws
    (laws : CanonicalOffDiagonalLaws) : CanonicalCorrectViewLaws where
  diagonalError := fun securityParameter _coordinate ↦
    canonicalSharpDiagonalError securityParameter
  offDiagonalError := laws.offDiagonalError
  diagonalError_nonneg := fun securityParameter _coordinate ↦
    canonicalSharpDiagonalError_nonneg securityParameter
  offDiagonalError_nonneg := laws.offDiagonalError_nonneg
  diagonalDistance_le := by
    intro securityParameter coordinate hidden ringSecret
    exact
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.tvDist_diagonalExperiment_directEntry_le_worstCaseSharpOperatorLoss
        (degree := rotationDegree securityParameter) (ringRank := 1)
        (gaussianDecomposition securityParameter)
        (sourceRingErrorSampler securityParameter)
        (targetRingErrorSampler canonicalCertificate securityParameter)
        hidden ringSecret coordinate
  offDiagonalDistance_le := laws.offDiagonalDistance_le

/-- Compile the explicit diagonal/off-diagonal laws and the proved message-one fiber bound into
direct native certificates for every polynomial query schedule. -/
noncomputable def CanonicalCorrectViewLaws.toDirectCertificateFamily
    (laws : CanonicalCorrectViewLaws) : DirectCertificateFamily canonicalCertificate :=
  fun queryCount securityParameter ↦
    DirectStatisticalCertificate.ofCenteredBinomialOffDiagonalIsolation
      (degree := rotationDegree securityParameter) (ringRank := 1)
      (lweDimension := ringDegree securityParameter)
      (queryCount := queryCount securityParameter)
      (eta := errorWidth securityParameter)
      (gaussianDecomposition securityParameter)
      (targetRingErrorSampler canonicalCertificate securityParameter)
      (scalarErrorSampler securityParameter)
      (scalarErrorSampler securityParameter)
      (keySwitchGadget securityParameter)
      (laws.diagonalError securityParameter)
      (laws.offDiagonalError securityParameter)
      (fun _ ↦ canonicalWrongViewFreshnessError securityParameter)
      (laws.diagonalError_nonneg securityParameter)
      (laws.offDiagonalError_nonneg securityParameter)
      (fun _ ↦ canonicalWrongViewFreshnessError_nonneg securityParameter)
      (laws.diagonalDistance_le securityParameter)
      (laws.offDiagonalDistance_le securityParameter)
      (fun coordinate ↦
        tvDist_averagedWrongTransform_uniformPublicView_le_card_mul_averagedMessageOneControlCappedFiberLoss
          (degree := rotationDegree securityParameter) (ringRank := 1)
          (lweDimension := ringDegree securityParameter)
          (queryCount := queryCount securityParameter)
          (eta := errorWidth securityParameter)
          (gaussianDecomposition securityParameter)
          (scalarErrorSampler securityParameter)
          (scalarErrorSampler securityParameter)
          (keySwitchGadget securityParameter) coordinate)

/-- Canonical direct certificates using the actual generated-control expectation for the complete
off-diagonal replacement hop.  This is the security-relevant constructor: it does not require a
support-wise off-diagonal law. -/
noncomputable def canonicalAveragedDirectCertificateFamily :
    DirectCertificateFamily canonicalCertificate :=
  fun queryCount securityParameter ↦
    DirectStatisticalCertificate.ofCenteredBinomialAveragedOffDiagonal
      (degree := rotationDegree securityParameter) (ringRank := 1)
      (lweDimension := ringDegree securityParameter)
      (queryCount := queryCount securityParameter)
      (eta := errorWidth securityParameter)
      (gaussianDecomposition securityParameter)
      (targetRingErrorSampler canonicalCertificate securityParameter)
      (scalarErrorSampler securityParameter)
      (scalarErrorSampler securityParameter)
      (keySwitchGadget securityParameter)
      (fun _coordinate ↦ canonicalSharpDiagonalError securityParameter)
      (fun _coordinate ↦ canonicalWrongViewFreshnessError securityParameter)
      (fun _coordinate ↦ canonicalSharpDiagonalError_nonneg securityParameter)
      (fun _coordinate ↦ canonicalWrongViewFreshnessError_nonneg securityParameter)
      (fun coordinate hidden ringSecret ↦
        Native.ShiftedCandidateEvaluator.DiagonalNormalForm.tvDist_diagonalExperiment_directEntry_le_worstCaseSharpOperatorLoss
          (degree := rotationDegree securityParameter) (ringRank := 1)
          (gaussianDecomposition securityParameter)
          (sourceRingErrorSampler securityParameter)
          (targetRingErrorSampler canonicalCertificate securityParameter)
          hidden ringSecret coordinate)
      (fun coordinate ↦
        tvDist_averagedWrongTransform_uniformPublicView_le_card_mul_averagedMessageOneControlCappedFiberLoss
          (degree := rotationDegree securityParameter) (ringRank := 1)
          (lweDimension := ringDegree securityParameter)
          (queryCount := queryCount securityParameter)
          (eta := errorWidth securityParameter)
          (gaussianDecomposition securityParameter)
          (scalarErrorSampler securityParameter)
          (scalarErrorSampler securityParameter)
          (keySwitchGadget securityParameter) coordinate)

/-- Canonical direct certificates whose off-diagonal term is the exposed effective-residual
`L²` loss rather than a ciphertext-level total-variation expression. -/
noncomputable def canonicalResidualL2DirectCertificateFamily :
    DirectCertificateFamily canonicalCertificate :=
  fun queryCount securityParameter =>
    DirectStatisticalCertificate.ofCenteredBinomialResidualL2
      (degree := rotationDegree securityParameter) (ringRank := 1)
      (lweDimension := ringDegree securityParameter)
      (queryCount := queryCount securityParameter)
      (eta := errorWidth securityParameter)
      (gaussianDecomposition securityParameter)
      (targetRingErrorSampler canonicalCertificate securityParameter)
      (scalarErrorSampler securityParameter)
      (scalarErrorSampler securityParameter)
      (keySwitchGadget securityParameter)
      (fun _coordinate => canonicalSharpDiagonalError securityParameter)
      (fun _coordinate => canonicalWrongViewFreshnessError securityParameter)
      (fun _coordinate => canonicalSharpDiagonalError_nonneg securityParameter)
      (fun _coordinate => canonicalWrongViewFreshnessError_nonneg securityParameter)
      (fun coordinate hidden ringSecret =>
        Native.ShiftedCandidateEvaluator.DiagonalNormalForm.tvDist_diagonalExperiment_directEntry_le_worstCaseSharpOperatorLoss
          (degree := rotationDegree securityParameter) (ringRank := 1)
          (gaussianDecomposition securityParameter)
          (sourceRingErrorSampler securityParameter)
          (targetRingErrorSampler canonicalCertificate securityParameter)
          hidden ringSecret coordinate)
      (fun coordinate =>
        tvDist_averagedWrongTransform_uniformPublicView_le_card_mul_averagedMessageOneControlCappedFiberLoss
          (degree := rotationDegree securityParameter) (ringRank := 1)
          (lweDimension := ringDegree securityParameter)
          (queryCount := queryCount securityParameter)
          (eta := errorWidth securityParameter)
          (gaussianDecomposition securityParameter)
          (scalarErrorSampler securityParameter)
          (scalarErrorSampler securityParameter)
          (keySwitchGadget securityParameter) coordinate)

/-- Canonical direct certificates using the fully normalized error-only off-diagonal law. -/
noncomputable def canonicalErrorOnlyL2DirectCertificateFamily :
    DirectCertificateFamily canonicalCertificate :=
  fun queryCount securityParameter =>
    DirectStatisticalCertificate.ofCenteredBinomialErrorOnlyL2
      (degree := rotationDegree securityParameter) (ringRank := 1)
      (lweDimension := ringDegree securityParameter)
      (queryCount := queryCount securityParameter)
      (eta := errorWidth securityParameter)
      (gaussianDecomposition securityParameter)
      (targetRingErrorSampler canonicalCertificate securityParameter)
      (scalarErrorSampler securityParameter)
      (scalarErrorSampler securityParameter)
      (keySwitchGadget securityParameter)
      (fun _coordinate => canonicalSharpDiagonalError securityParameter)
      (fun _coordinate => canonicalWrongViewFreshnessError securityParameter)
      (fun _coordinate => canonicalSharpDiagonalError_nonneg securityParameter)
      (fun _coordinate => canonicalWrongViewFreshnessError_nonneg securityParameter)
      (fun coordinate hidden ringSecret =>
        Native.ShiftedCandidateEvaluator.DiagonalNormalForm.tvDist_diagonalExperiment_directEntry_le_worstCaseSharpOperatorLoss
          (degree := rotationDegree securityParameter) (ringRank := 1)
          (gaussianDecomposition securityParameter)
          (sourceRingErrorSampler securityParameter)
          (targetRingErrorSampler canonicalCertificate securityParameter)
          hidden ringSecret coordinate)
      (fun coordinate =>
        tvDist_averagedWrongTransform_uniformPublicView_le_card_mul_averagedMessageOneControlCappedFiberLoss
          (degree := rotationDegree securityParameter) (ringRank := 1)
          (lweDimension := ringDegree securityParameter)
          (queryCount := queryCount securityParameter)
          (eta := errorWidth securityParameter)
          (gaussianDecomposition securityParameter)
          (scalarErrorSampler securityParameter)
          (scalarErrorSampler securityParameter)
          (keySwitchGadget securityParameter) coordinate)

/-- Strongest canonical direct certificates when the native normalized control map is analyzed
through its exact non-bijectivity event.  One good control makes the complete wrong public view
uniform, so no union bound over BRK entries or TGSW rows is charged. -/
noncomputable def canonicalErrorOnlyL2ControlFailureDirectCertificateFamily :
    DirectCertificateFamily canonicalCertificate :=
  fun queryCount securityParameter =>
    DirectStatisticalCertificate.ofCenteredBinomialErrorOnlyL2
      (degree := rotationDegree securityParameter) (ringRank := 1)
      (lweDimension := ringDegree securityParameter)
      (queryCount := queryCount securityParameter)
      (eta := errorWidth securityParameter)
      (gaussianDecomposition securityParameter)
      (targetRingErrorSampler canonicalCertificate securityParameter)
      (scalarErrorSampler securityParameter)
      (scalarErrorSampler securityParameter)
      (keySwitchGadget securityParameter)
      (fun _coordinate => canonicalSharpDiagonalError securityParameter)
      (fun _coordinate => canonicalWrongViewNonbijectivityError securityParameter)
      (fun _coordinate => canonicalSharpDiagonalError_nonneg securityParameter)
      (fun _coordinate => canonicalWrongViewNonbijectivityError_nonneg securityParameter)
      (fun coordinate hidden ringSecret =>
        Native.ShiftedCandidateEvaluator.DiagonalNormalForm.tvDist_diagonalExperiment_directEntry_le_worstCaseSharpOperatorLoss
          (degree := rotationDegree securityParameter) (ringRank := 1)
          (gaussianDecomposition securityParameter)
          (sourceRingErrorSampler securityParameter)
          (targetRingErrorSampler canonicalCertificate securityParameter)
          hidden ringSecret coordinate)
      (fun coordinate =>
        tvDist_averagedWrongTransform_uniformPublicView_le_averagedMessageOneControlFailure
          (degree := rotationDegree securityParameter) (ringRank := 1)
          (lweDimension := ringDegree securityParameter)
          (queryCount := queryCount securityParameter)
          (eta := errorWidth securityParameter)
          (gaussianDecomposition securityParameter)
          (scalarErrorSampler securityParameter)
          (scalarErrorSampler securityParameter)
          (keySwitchGadget securityParameter) coordinate)

/-- A direct certificate whose correct-side error is explicitly factored into output-normal-form
loss and the checked coupled Gaussian smudging term.  The existing finite constructor
`ofCoupledCenteredBinomialDiscreteGaussianLinearSmudging` produces this shape from its executable
native view laws. -/
structure CoupledDirectCertificateFamily (certificate : ScalarCertificateFamily) where
  directAt : DirectCertificateFamily certificate
  normalFormError :
    (queryCount : ℕ → ℕ) → (securityParameter : ℕ) →
      Fin (ringDegree securityParameter) → ℝ
  normalFormError_nonneg : ∀ queryCount securityParameter coordinate,
    0 ≤ normalFormError queryCount securityParameter coordinate
  correctError_eq : ∀ queryCount securityParameter coordinate,
    (directAt queryCount securityParameter).correctError coordinate =
      normalFormError queryCount securityParameter coordinate +
        coupledCenteredBinomialDiscreteGaussianLinearSmudgingError
          (gaussianDecomposition securityParameter)
          (certificate securityParameter)
          (nativeRingDegree securityParameter) 1 (ringDegree securityParameter)
          (errorWidth securityParameter)

/-- The two executable native view laws still required before Gaussian smudging.  Correct
candidate evaluation must reach the coupled residual normal form, and complementary-candidate
evaluation must approach the exact uniform-BRK public endpoint. -/
structure NativeViewLaws (certificate : ScalarCertificateFamily) where
  normalFormError :
    (queryCount : ℕ → ℕ) → (securityParameter : ℕ) →
      Fin (ringDegree securityParameter) → ℝ
  freshnessError :
    (queryCount : ℕ → ℕ) → (securityParameter : ℕ) →
      Fin (ringDegree securityParameter) → ℝ
  normalFormError_nonneg : ∀ queryCount securityParameter coordinate,
    0 ≤ normalFormError queryCount securityParameter coordinate
  freshnessError_nonneg : ∀ queryCount securityParameter coordinate,
    0 ≤ freshnessError queryCount securityParameter coordinate
  normalFormDistance_le : ∀ queryCount securityParameter coordinate,
    tvDist
        (averagedCorrectTransform (ringRank := 1)
          (queryCount := queryCount securityParameter)
          (gaussianDecomposition securityParameter)
          (RLWE.CenteredBinomial.sampler
            (gaussianModulus securityParameter) (nativeRingDegree securityParameter)
            (errorWidth securityParameter))
          (scalarErrorSampler securityParameter)
          (scalarErrorSampler securityParameter)
          (keySwitchGadget securityParameter) coordinate)
        (coupledAveragedResidualRealView (degree := rotationDegree securityParameter)
          (ringRank := 1)
          (queryCount := queryCount securityParameter)
          (eta := errorWidth securityParameter)
          (gaussianDecomposition securityParameter)
          (DiscreteGaussianSampler.ringSampler
            (nativeRingDegree securityParameter) (certificate securityParameter))
          (scalarErrorSampler securityParameter)
          (scalarErrorSampler securityParameter)
          (keySwitchGadget securityParameter) coordinate) ≤
      normalFormError queryCount securityParameter coordinate
  freshnessDistance_le : ∀ queryCount securityParameter coordinate,
    tvDist
        (averagedWrongTransform (ringRank := 1)
          (queryCount := queryCount securityParameter)
          (gaussianDecomposition securityParameter)
          (RLWE.CenteredBinomial.sampler
            (gaussianModulus securityParameter) (nativeRingDegree securityParameter)
            (errorWidth securityParameter))
          (scalarErrorSampler securityParameter)
          (scalarErrorSampler securityParameter)
          (keySwitchGadget securityParameter) coordinate)
        (uniformPublicView (ringRank := 1)
          (lweDimension := ringDegree securityParameter)
          (queryCount := queryCount securityParameter)
          (RLWE.CenteredBinomial.sampler
            (gaussianModulus securityParameter) (nativeRingDegree securityParameter)
            (errorWidth securityParameter))
          (scalarErrorSampler securityParameter)
          (scalarErrorSampler securityParameter)
          (Gadget.Base.ringGadget (degree := nativeRingDegree securityParameter)
            (gaussianDecomposition securityParameter))
          (keySwitchGadget securityParameter)) ≤
      freshnessError queryCount securityParameter coordinate

/-- Compile the executable native view laws through the checked coupled linear Gaussian
smudging constructor. -/
noncomputable def NativeViewLaws.toCoupledDirectCertificateFamily
    (certificate : ScalarCertificateFamily)
    (laws : NativeViewLaws certificate) :
    CoupledDirectCertificateFamily certificate where
  directAt queryCount securityParameter :=
    DirectStatisticalCertificate.ofCoupledCenteredBinomialDiscreteGaussianLinearSmudging
      (degree := rotationDegree securityParameter) (ringRank := 1)
      (lweDimension := ringDegree securityParameter)
      (queryCount := queryCount securityParameter)
      (eta := errorWidth securityParameter)
      (gaussianDecomposition securityParameter)
      (certificate securityParameter)
      (scalarErrorSampler securityParameter)
      (scalarErrorSampler securityParameter)
      (keySwitchGadget securityParameter)
      (laws.normalFormError queryCount securityParameter)
      (laws.freshnessError queryCount securityParameter)
      (laws.normalFormError_nonneg queryCount securityParameter)
      (laws.freshnessError_nonneg queryCount securityParameter)
      (laws.normalFormDistance_le queryCount securityParameter)
      (laws.freshnessDistance_le queryCount securityParameter)
  normalFormError := laws.normalFormError
  normalFormError_nonneg := laws.normalFormError_nonneg
  correctError_eq := by
    intro queryCount securityParameter coordinate
    rfl

/-! ## Explicit post-evaluation smudging route -/

/-- The sole correct-view normal-form obligation after the evaluator explicitly adds its fresh
wide BRK body noise.  The comparison endpoint already contains `residual + wideNoise`, so the
checked conditional-smudging theorem applies; it does not compare the narrow residual itself with
the wide Gaussian target.

The complementary-candidate law is not a field: exact uniform-BRK invariance and the generated
control non-bijectivity theorem discharge it below without an additional assumption. -/
structure CanonicalPostSmudgedNormalFormLaws where
  normalFormError :
    (queryCount : ℕ → ℕ) → (securityParameter : ℕ) →
      Fin (ringDegree securityParameter) → ℝ
  normalFormError_nonneg : ∀ queryCount securityParameter coordinate,
    0 ≤ normalFormError queryCount securityParameter coordinate
  normalFormDistance_le : ∀ queryCount securityParameter coordinate,
    tvDist
        (PostEvaluationSmudging.averagedCorrectTransform
          (ringRank := 1) (queryCount := queryCount securityParameter)
          (gaussianDecomposition securityParameter)
          (sourceRingErrorSampler securityParameter)
          (targetRingErrorSampler canonicalCertificate securityParameter)
          (scalarErrorSampler securityParameter)
          (scalarErrorSampler securityParameter)
          (keySwitchGadget securityParameter) coordinate)
        (coupledAveragedResidualRealView (degree := rotationDegree securityParameter)
          (ringRank := 1) (queryCount := queryCount securityParameter)
          (eta := errorWidth securityParameter)
          (gaussianDecomposition securityParameter)
          (targetRingErrorSampler canonicalCertificate securityParameter)
          (scalarErrorSampler securityParameter)
          (scalarErrorSampler securityParameter)
          (keySwitchGadget securityParameter) coordinate) ≤
      normalFormError queryCount securityParameter coordinate

/-- Exact pre-smudging mask/residual-correlation distance for the canonical family.  The target
has fresh uniform BRK masks and the evaluator's exact computed residual, but no fresh row error.
Post-evaluation wide noise is a common Markov kernel applied only after this distance. -/
noncomputable def canonicalPostSmudgedMaskNormalFormError
    (queryCount : ℕ → ℕ) (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) : ℝ :=
  tvDist
    (averagedCorrectTransform (ringRank := 1)
      (queryCount := queryCount securityParameter)
      (gaussianDecomposition securityParameter)
      (sourceRingErrorSampler securityParameter)
      (scalarErrorSampler securityParameter)
      (scalarErrorSampler securityParameter)
      (keySwitchGadget securityParameter) coordinate)
    (PostEvaluationSmudging.coupledAveragedZeroNoiseResidualRealView
      (degree := rotationDegree securityParameter) (ringRank := 1)
      (queryCount := queryCount securityParameter)
      (eta := errorWidth securityParameter)
      (gaussianDecomposition securityParameter)
      (scalarErrorSampler securityParameter)
      (scalarErrorSampler securityParameter)
      (keySwitchGadget securityParameter) coordinate)

theorem canonicalPostSmudgedMaskNormalFormError_nonneg
    (queryCount : ℕ → ℕ) (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) :
    0 ≤ canonicalPostSmudgedMaskNormalFormError queryCount securityParameter coordinate :=
  tvDist_nonneg _ _

/-- Explicit finite full-key collision budget for the canonical mask normal form.  Its retained
side coordinate contains both target secrets, the complete native evaluator residual, and the
transported KSK/input tape; its replaced coordinate is the entire BRK public-mask tensor. -/
noncomputable def canonicalPostSmudgedMaskCollisionLoss
    (queryCount : ℕ → ℕ) (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) : ℝ :=
  FullMaskCollision.correctMaskCollisionLoss
    (degree := nativeRingDegree securityParameter) (ringRank := 1)
    (queryCount := queryCount securityParameter)
    (gaussianDecomposition securityParameter)
    (sourceRingErrorSampler securityParameter)
    (scalarErrorSampler securityParameter)
    (scalarErrorSampler securityParameter)
    (keySwitchGadget securityParameter) coordinate

theorem canonicalPostSmudgedMaskCollisionLoss_nonneg
    (queryCount : ℕ → ℕ) (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) :
    0 ≤ canonicalPostSmudgedMaskCollisionLoss queryCount securityParameter coordinate :=
  FullMaskCollision.correctMaskCollisionLoss_nonneg _ _ _ _ _ _

/-- The formerly opaque exact mask/residual total variation is bounded by the full-key finite
side-information collision expression. -/
theorem canonicalPostSmudgedMaskNormalFormError_le_collisionLoss
    (queryCount : ℕ → ℕ) (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) :
    canonicalPostSmudgedMaskNormalFormError queryCount securityParameter coordinate ≤
      canonicalPostSmudgedMaskCollisionLoss queryCount securityParameter coordinate := by
  simpa only [canonicalPostSmudgedMaskNormalFormError,
    canonicalPostSmudgedMaskCollisionLoss, sourceRingErrorSampler,
    nativeRingDegree] using
    (FullMaskCollision.tvDist_averagedCorrectTransform_coupledZeroNoiseResidual_le_correctMaskCollisionLoss
      (degree := rotationDegree securityParameter) (ringRank := 1)
      (queryCount := queryCount securityParameter) (eta := errorWidth securityParameter)
      (gaussianDecomposition securityParameter)
      (scalarErrorSampler securityParameter) (scalarErrorSampler securityParameter)
      (keySwitchGadget securityParameter) coordinate)

/-- Concrete conditional pair-collision statement for the complete canonical evaluated BRK mask
given both target secrets, the complete residual, and the transported auxiliary context. -/
def canonicalPostSmudgedMaskConditionalCollisionBound
    (queryCount : ℕ → ℕ) (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) (ε : ℝ) : Prop :=
  FullMaskCollision.CorrectMaskConditionalCollisionBound
    (degree := nativeRingDegree securityParameter) (ringRank := 1)
    (queryCount := queryCount securityParameter)
    (gaussianDecomposition securityParameter)
    (sourceRingErrorSampler securityParameter)
    (scalarErrorSampler securityParameter)
    (scalarErrorSampler securityParameter)
    (keySwitchGadget securityParameter) coordinate ε

/-- A complete conditional pair-collision estimate gives the square-root mask-normal-form loss. -/
theorem canonicalPostSmudgedMaskNormalFormError_le_sqrt_of_collisionBound
    (queryCount : ℕ → ℕ) (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) (ε : ℝ)
    (hcollision : canonicalPostSmudgedMaskConditionalCollisionBound
      queryCount securityParameter coordinate ε) :
    canonicalPostSmudgedMaskNormalFormError queryCount securityParameter coordinate ≤
      Real.sqrt ε / 2 := by
  simpa only [canonicalPostSmudgedMaskNormalFormError,
    canonicalPostSmudgedMaskConditionalCollisionBound, sourceRingErrorSampler,
    nativeRingDegree] using
    (FullMaskCollision.tvDist_averagedCorrectTransform_coupledZeroNoiseResidual_le_sqrt_of_collisionBound
      (degree := rotationDegree securityParameter) (ringRank := 1)
      (queryCount := queryCount securityParameter) (eta := errorWidth securityParameter)
      (gaussianDecomposition securityParameter)
      (scalarErrorSampler securityParameter) (scalarErrorSampler securityParameter)
      (keySwitchGadget securityParameter) coordinate ε hcollision)

/-- Canonical post-smudged laws obtained without a caller-supplied statistical inequality.
The only exposed correct-side quantity is the exact finite mask/residual-correlation distance;
the wide discrete-Gaussian layer is eliminated internally by data processing. -/
noncomputable def canonicalPostSmudgedMaskNormalFormLaws :
    CanonicalPostSmudgedNormalFormLaws where
  normalFormError := canonicalPostSmudgedMaskNormalFormError
  normalFormError_nonneg := canonicalPostSmudgedMaskNormalFormError_nonneg
  normalFormDistance_le := by
    intro queryCount securityParameter coordinate
    simpa only [canonicalPostSmudgedMaskNormalFormError,
      sourceRingErrorSampler, targetRingErrorSampler, nativeRingDegree] using
      (PostEvaluationSmudging.tvDist_averagedCorrectTransform_coupledResidual_le_zeroNoiseNormalForm
        (degree := rotationDegree securityParameter) (ringRank := 1)
        (queryCount := queryCount securityParameter)
        (eta := errorWidth securityParameter)
        (gaussianDecomposition securityParameter)
        (targetRingErrorSampler canonicalCertificate securityParameter)
        (scalarErrorSampler securityParameter)
        (scalarErrorSampler securityParameter)
        (keySwitchGadget securityParameter) coordinate)

/-- Canonical post-smudged normal-form laws whose exposed correct-side premise is the explicit
full-key finite collision loss rather than a total-variation distance. -/
noncomputable def canonicalPostSmudgedMaskCollisionNormalFormLaws :
    CanonicalPostSmudgedNormalFormLaws where
  normalFormError := canonicalPostSmudgedMaskCollisionLoss
  normalFormError_nonneg := canonicalPostSmudgedMaskCollisionLoss_nonneg
  normalFormDistance_le := by
    intro queryCount securityParameter coordinate
    exact (canonicalPostSmudgedMaskNormalFormLaws.normalFormDistance_le
      queryCount securityParameter coordinate).trans
        (canonicalPostSmudgedMaskNormalFormError_le_collisionLoss
          queryCount securityParameter coordinate)

/-- A family of explicit complete-mask conditional collision estimates. -/
structure CanonicalPostSmudgedMaskCollisionCertificate where
  ε : (queryCount : ℕ → ℕ) → (securityParameter : ℕ) →
    Fin (ringDegree securityParameter) → ℝ
  collisionBound : ∀ queryCount securityParameter coordinate,
    canonicalPostSmudgedMaskConditionalCollisionBound queryCount securityParameter
      coordinate (ε queryCount securityParameter coordinate)

/-- Convert a complete conditional pair-collision certificate directly into the post-smudged
normal-form laws consumed by the security reduction. -/
noncomputable def CanonicalPostSmudgedMaskCollisionCertificate.normalFormLaws
    (certificate : CanonicalPostSmudgedMaskCollisionCertificate) :
    CanonicalPostSmudgedNormalFormLaws where
  normalFormError := fun queryCount securityParameter coordinate ↦
    Real.sqrt (certificate.ε queryCount securityParameter coordinate) / 2
  normalFormError_nonneg := by
    intro queryCount securityParameter coordinate
    positivity
  normalFormDistance_le := by
    intro queryCount securityParameter coordinate
    exact (canonicalPostSmudgedMaskNormalFormLaws.normalFormDistance_le
      queryCount securityParameter coordinate).trans
        (canonicalPostSmudgedMaskNormalFormError_le_sqrt_of_collisionBound
          queryCount securityParameter coordinate
          (certificate.ε queryCount securityParameter coordinate)
          (certificate.collisionBound queryCount securityParameter coordinate))

/-! ### Residual-first static-mask collision route -/

/-- Expected translation cost for erasing the canonical evaluator residual after the fresh wide
discrete-Gaussian layer has been sampled. -/
noncomputable def canonicalPostSmudgedResidualErasureCost
    (queryCount : ℕ → ℕ) (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) : ℝ :=
  FullMaskCollision.correctResidualErasureCost
    (degree := nativeRingDegree securityParameter) (ringRank := 1)
    (queryCount := queryCount securityParameter)
    (gaussianDecomposition securityParameter)
    (sourceRingErrorSampler securityParameter)
    (targetRingErrorSampler canonicalCertificate securityParameter)
    (scalarErrorSampler securityParameter)
    (scalarErrorSampler securityParameter)
    (keySwitchGadget securityParameter) coordinate

theorem canonicalPostSmudgedResidualErasureCost_nonneg
    (queryCount : ℕ → ℕ) (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) :
    0 ≤ canonicalPostSmudgedResidualErasureCost
      queryCount securityParameter coordinate := by
  exact FullMaskCollision.correctResidualErasureCost_nonneg
    (gaussianDecomposition securityParameter)
    (sourceRingErrorSampler securityParameter)
    (targetRingErrorSampler canonicalCertificate securityParameter)
    (scalarErrorSampler securityParameter)
    (scalarErrorSampler securityParameter)
    (keySwitchGadget securityParameter) coordinate

/-- The residual-first route pays no new analytic quantity: its expected erasure cost is bounded
by the already checked coupled centered-binomial/discrete-Gaussian linear-smudging budget. -/
theorem canonicalPostSmudgedResidualErasureCost_le_linearSmudgingError
    (queryCount : ℕ → ℕ) (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) :
    canonicalPostSmudgedResidualErasureCost queryCount securityParameter coordinate ≤
      coupledCenteredBinomialDiscreteGaussianLinearSmudgingError
        (gaussianDecomposition securityParameter)
        (canonicalCertificate securityParameter)
        (nativeRingDegree securityParameter) 1 (ringDegree securityParameter)
        (errorWidth securityParameter) := by
  simpa only [canonicalPostSmudgedResidualErasureCost,
    sourceRingErrorSampler, targetRingErrorSampler, nativeRingDegree] using
    (FullMaskCollision.correctResidualErasureCost_centeredBinomial_discreteGaussian_le_linear
      (degree := rotationDegree securityParameter) (ringRank := 1)
      (lweDimension := ringDegree securityParameter)
      (queryCount := queryCount securityParameter)
      (eta := errorWidth securityParameter)
      (gaussianDecomposition securityParameter)
      (canonicalCertificate securityParameter)
      (scalarErrorSampler securityParameter)
      (scalarErrorSampler securityParameter)
      (keySwitchGadget securityParameter) coordinate)

/-! ### Selected-diagonal residual-free mask route -/

/-- The sole native mask-correlation loss left after exact off-diagonal one-time-pad
factorization.  It is independent of the adaptive tape length and selected coordinate. -/
noncomputable def canonicalPostSmudgedSelectedDiagonalMaskLoss
    (securityParameter : ℕ) : ℝ :=
  FullMaskCollision.StaticDiagonal.worstCaseStaticMaskDiagonalChiSquareLoss
    (degree := rotationDegree securityParameter) (ringRank := 1)
    (gaussianDecomposition securityParameter)
    (sourceRingErrorSampler securityParameter)

theorem canonicalPostSmudgedSelectedDiagonalMaskLoss_nonneg
    (securityParameter : ℕ) :
    0 ≤ canonicalPostSmudgedSelectedDiagonalMaskLoss securityParameter := by
  exact
    FullMaskCollision.StaticDiagonal.worstCaseStaticMaskDiagonalChiSquareLoss_nonneg
      (degree := rotationDegree securityParameter) (ringRank := 1)
      (gaussianDecomposition securityParameter)
      (sourceRingErrorSampler securityParameter)

/-- Candidate-independent contribution of the retained equal-difference slice to the canonical
selected-diagonal mask loss. -/
noncomputable def canonicalPostSmudgedSelectedDiagonalSelfMaskLoss
    (securityParameter : ℕ) : ℝ :=
  max
    (Native.ShiftedCandidateEvaluator.DiagonalNormalForm.averagedSourceErrorDiagonalSelfChiSquareLoss
      (degree := rotationDegree securityParameter) (ringRank := 1)
      (gaussianDecomposition securityParameter)
      (sourceRingErrorSampler securityParameter) false)
    (Native.ShiftedCandidateEvaluator.DiagonalNormalForm.averagedSourceErrorDiagonalSelfChiSquareLoss
      (degree := rotationDegree securityParameter) (ringRank := 1)
      (gaussianDecomposition securityParameter)
      (sourceRingErrorSampler securityParameter) true)

/-- Candidate-independent contribution of the retained distinct-difference slice to the
canonical selected-diagonal mask loss. -/
noncomputable def canonicalPostSmudgedSelectedDiagonalDistinctMaskLoss
    (securityParameter : ℕ) : ℝ :=
  max
    (Native.ShiftedCandidateEvaluator.DiagonalNormalForm.averagedSourceErrorDiagonalDistinctChiSquareLoss
      (degree := rotationDegree securityParameter) (ringRank := 1)
      (gaussianDecomposition securityParameter)
      (sourceRingErrorSampler securityParameter) false)
    (Native.ShiftedCandidateEvaluator.DiagonalNormalForm.averagedSourceErrorDiagonalDistinctChiSquareLoss
      (degree := rotationDegree securityParameter) (ringRank := 1)
      (gaussianDecomposition securityParameter)
      (sourceRingErrorSampler securityParameter) true)

theorem canonicalPostSmudgedSelectedDiagonalSelfMaskLoss_nonneg
    (securityParameter : ℕ) :
    0 ≤ canonicalPostSmudgedSelectedDiagonalSelfMaskLoss securityParameter := by
  unfold canonicalPostSmudgedSelectedDiagonalSelfMaskLoss
  exact
    (Native.ShiftedCandidateEvaluator.DiagonalNormalForm.averagedSourceErrorDiagonalSelfChiSquareLoss_nonneg
      (degree := rotationDegree securityParameter) (ringRank := 1)
      (gaussianDecomposition securityParameter)
      (sourceRingErrorSampler securityParameter) false).trans (le_max_left _ _)

theorem canonicalPostSmudgedSelectedDiagonalDistinctMaskLoss_nonneg
    (securityParameter : ℕ) :
    0 ≤ canonicalPostSmudgedSelectedDiagonalDistinctMaskLoss securityParameter := by
  unfold canonicalPostSmudgedSelectedDiagonalDistinctMaskLoss
  exact
    (Native.ShiftedCandidateEvaluator.DiagonalNormalForm.averagedSourceErrorDiagonalDistinctChiSquareLoss_nonneg
      (degree := rotationDegree securityParameter) (ringRank := 1)
      (gaussianDecomposition securityParameter)
      (sourceRingErrorSampler securityParameter) false).trans (le_max_left _ _)

/-- The exact canonical selected-diagonal mask loss is controlled by the retained equal- and
distinct-difference slices.  Unlike the global source-independent relaxation, this inequality
keeps every transformed-error fiber normalization until after the collision split. -/
theorem canonicalPostSmudgedSelectedDiagonalMaskLoss_le_self_add_distinct
    (securityParameter : ℕ) :
    canonicalPostSmudgedSelectedDiagonalMaskLoss securityParameter ≤
      canonicalPostSmudgedSelectedDiagonalSelfMaskLoss securityParameter +
        canonicalPostSmudgedSelectedDiagonalDistinctMaskLoss securityParameter := by
  unfold canonicalPostSmudgedSelectedDiagonalMaskLoss
    FullMaskCollision.StaticDiagonal.worstCaseStaticMaskDiagonalChiSquareLoss
    canonicalPostSmudgedSelectedDiagonalSelfMaskLoss
    canonicalPostSmudgedSelectedDiagonalDistinctMaskLoss
  apply max_le
  · exact
      (Native.ShiftedCandidateEvaluator.DiagonalNormalForm.averagedSourceErrorDiagonalChiSquareLoss_le_self_add_distinct
        (degree := rotationDegree securityParameter) (ringRank := 1)
        (gaussianDecomposition securityParameter)
        (sourceRingErrorSampler securityParameter) false).trans
          (add_le_add (le_max_left _ _) (le_max_left _ _))
  · exact
      (Native.ShiftedCandidateEvaluator.DiagonalNormalForm.averagedSourceErrorDiagonalChiSquareLoss_le_self_add_distinct
        (degree := rotationDegree securityParameter) (ringRank := 1)
        (gaussianDecomposition securityParameter)
        (sourceRingErrorSampler securityParameter) true).trans
          (add_le_add (le_max_right _ _) (le_max_right _ _))

/-- Finite certificate for the retained equal-difference slice.  Its bound is conditional on the
actual transformed-error fiber and averaged over every difference in that fiber; it need not hold
pointwise for each difference ciphertext. -/
structure CanonicalSelectedDiagonalSelfFiberAverageCertificate where
  kernelAverageBound : ℕ → ℝ
  kernelAverageBound_nonneg : ∀ securityParameter,
    0 ≤ kernelAverageBound securityParameter
  fiberAverage : ∀ securityParameter candidate sourceError,
    sourceError ∈ support
        (ProbComp.sampleIID
          (TGSW.rowCount 1 (gaussianDecomposition securityParameter).levels)
          (sourceRingErrorSampler securityParameter)) →
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.fixedErrorDifferenceFiberKernelAverageBound
        (degree := rotationDegree securityParameter) (ringRank := 1)
        (gaussianDecomposition securityParameter) candidate sourceError
        (kernelAverageBound securityParameter)

/-- Challenge-normalized square-root loss certified for the retained equal-difference slice. -/
noncomputable def CanonicalSelectedDiagonalSelfFiberAverageCertificate.lossBound
    (certificate : CanonicalSelectedDiagonalSelfFiberAverageCertificate)
    (securityParameter : ℕ) : ℝ :=
  Real.sqrt
      (certificate.kernelAverageBound securityParameter /
        (Fintype.card
          (Native.ShiftedCandidateEvaluator.DiagonalNormalForm.DiagonalChallenge
            (gaussianModulus securityParameter) (rotationDegree securityParameter) 1
            (gaussianDecomposition securityParameter).levels) : ℝ)) /
    2

theorem CanonicalSelectedDiagonalSelfFiberAverageCertificate.lossBound_nonneg
    (certificate : CanonicalSelectedDiagonalSelfFiberAverageCertificate)
    (securityParameter : ℕ) :
    0 ≤ certificate.lossBound securityParameter := by
  unfold CanonicalSelectedDiagonalSelfFiberAverageCertificate.lossBound
  positivity

/-- The finite retained-fiber certificate bounds the exact canonical self-slice mask loss. -/
theorem CanonicalSelectedDiagonalSelfFiberAverageCertificate.selfMaskLoss_le
    (certificate : CanonicalSelectedDiagonalSelfFiberAverageCertificate)
    (securityParameter : ℕ) :
    canonicalPostSmudgedSelectedDiagonalSelfMaskLoss securityParameter ≤
      certificate.lossBound securityParameter := by
  unfold canonicalPostSmudgedSelectedDiagonalSelfMaskLoss
    CanonicalSelectedDiagonalSelfFiberAverageCertificate.lossBound
  apply max_le
  · exact
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.averagedSourceErrorDiagonalSelfChiSquareLoss_le_fiberAverage
        (degree := rotationDegree securityParameter) (ringRank := 1)
        (gaussianDecomposition securityParameter)
        (sourceRingErrorSampler securityParameter) false
        (certificate.kernelAverageBound securityParameter)
        (certificate.kernelAverageBound_nonneg securityParameter)
        (certificate.fiberAverage securityParameter false)
  · exact
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.averagedSourceErrorDiagonalSelfChiSquareLoss_le_fiberAverage
        (degree := rotationDegree securityParameter) (ringRank := 1)
        (gaussianDecomposition securityParameter)
        (sourceRingErrorSampler securityParameter) true
        (certificate.kernelAverageBound securityParameter)
        (certificate.kernelAverageBound_nonneg securityParameter)
        (certificate.fiberAverage securityParameter true)

/-- Finite retained-fiber certificate for distinct difference pairs. -/
structure CanonicalSelectedDiagonalDistinctFiberAverageCertificate where
  collisionAverageBound : ℕ → ℝ
  collisionAverageBound_nonneg : ∀ securityParameter,
    0 ≤ collisionAverageBound securityParameter
  fiberAverage : ∀ securityParameter candidate sourceError,
    sourceError ∈ support
        (ProbComp.sampleIID
          (TGSW.rowCount 1 (gaussianDecomposition securityParameter).levels)
          (sourceRingErrorSampler securityParameter)) →
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.fixedErrorDifferenceFiberDistinctCollisionAverageBound
        (degree := rotationDegree securityParameter) (ringRank := 1)
        (gaussianDecomposition securityParameter) candidate sourceError
        (collisionAverageBound securityParameter)

/-- Challenge-normalized square-root loss certified for retained distinct difference pairs. -/
noncomputable def CanonicalSelectedDiagonalDistinctFiberAverageCertificate.lossBound
    (certificate : CanonicalSelectedDiagonalDistinctFiberAverageCertificate)
    (securityParameter : ℕ) : ℝ :=
  Real.sqrt
      (certificate.collisionAverageBound securityParameter /
        (Fintype.card
          (Native.ShiftedCandidateEvaluator.DiagonalNormalForm.DiagonalChallenge
            (gaussianModulus securityParameter) (rotationDegree securityParameter) 1
            (gaussianDecomposition securityParameter).levels) : ℝ)) /
    2

theorem CanonicalSelectedDiagonalDistinctFiberAverageCertificate.lossBound_nonneg
    (certificate : CanonicalSelectedDiagonalDistinctFiberAverageCertificate)
    (securityParameter : ℕ) :
    0 ≤ certificate.lossBound securityParameter := by
  unfold CanonicalSelectedDiagonalDistinctFiberAverageCertificate.lossBound
  positivity

/-- The finite distinct-pair certificate bounds the exact canonical distinct-slice mask loss. -/
theorem CanonicalSelectedDiagonalDistinctFiberAverageCertificate.distinctMaskLoss_le
    (certificate : CanonicalSelectedDiagonalDistinctFiberAverageCertificate)
    (securityParameter : ℕ) :
    canonicalPostSmudgedSelectedDiagonalDistinctMaskLoss securityParameter ≤
      certificate.lossBound securityParameter := by
  unfold canonicalPostSmudgedSelectedDiagonalDistinctMaskLoss
    CanonicalSelectedDiagonalDistinctFiberAverageCertificate.lossBound
  apply max_le
  · exact
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.averagedSourceErrorDiagonalDistinctChiSquareLoss_le_fiberAverage
        (degree := rotationDegree securityParameter) (ringRank := 1)
        (gaussianDecomposition securityParameter)
        (sourceRingErrorSampler securityParameter) false
        (certificate.collisionAverageBound securityParameter)
        (certificate.collisionAverageBound_nonneg securityParameter)
        (certificate.fiberAverage securityParameter false)
  · exact
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.averagedSourceErrorDiagonalDistinctChiSquareLoss_le_fiberAverage
        (degree := rotationDegree securityParameter) (ringRank := 1)
        (gaussianDecomposition securityParameter)
        (sourceRingErrorSampler securityParameter) true
        (certificate.collisionAverageBound securityParameter)
        (certificate.collisionAverageBound_nonneg securityParameter)
        (certificate.fiberAverage securityParameter true)

/-- Canonical distinct-pair certificate stated using the exact native paired-row cokernel rather
than a challenge-collision or residue-rank envelope.  This is the construction-specific finite
matrix statement left by the exact cokernel factorization. -/
structure CanonicalSelectedDiagonalDistinctCokernelAverageCertificate where
  cokernelAverageBound : ℕ → ℝ
  cokernelAverageBound_nonneg : ∀ securityParameter,
    0 ≤ cokernelAverageBound securityParameter
  fiberAverage : ∀ securityParameter candidate sourceError,
    sourceError ∈ support
        (ProbComp.sampleIID
          (TGSW.rowCount 1 (gaussianDecomposition securityParameter).levels)
          (sourceRingErrorSampler securityParameter)) →
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.fixedErrorDifferenceFiberDistinctCokernelAverageBound
        (degree := rotationDegree securityParameter) (ringRank := 1)
        (gaussianDecomposition securityParameter) candidate sourceError
        (cokernelAverageBound securityParameter)

/-- The exact conditioned cokernel statement supplies the earlier retained distinct-collision
certificate without a rank or zero-fiber relaxation. -/
noncomputable def CanonicalSelectedDiagonalDistinctCokernelAverageCertificate.toDistinctFiberAverage
    (certificate : CanonicalSelectedDiagonalDistinctCokernelAverageCertificate) :
    CanonicalSelectedDiagonalDistinctFiberAverageCertificate where
  collisionAverageBound := certificate.cokernelAverageBound
  collisionAverageBound_nonneg := certificate.cokernelAverageBound_nonneg
  fiberAverage := by
    intro securityParameter candidate sourceError hsource
    exact
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.fixedErrorDifferenceFiberDistinctCollisionAverageBound_of_cokernel
        (degree := rotationDegree securityParameter) (ringRank := 1)
        (gaussianDecomposition securityParameter) candidate sourceError
        (certificate.cokernelAverageBound securityParameter)
        (certificate.fiberAverage securityParameter candidate sourceError hsource)

/-- Challenge-normalized square-root loss of the exact native cokernel certificate. -/
noncomputable def CanonicalSelectedDiagonalDistinctCokernelAverageCertificate.lossBound
    (certificate : CanonicalSelectedDiagonalDistinctCokernelAverageCertificate)
    (securityParameter : ℕ) : ℝ :=
  certificate.toDistinctFiberAverage.lossBound securityParameter

theorem CanonicalSelectedDiagonalDistinctCokernelAverageCertificate.lossBound_nonneg
    (certificate : CanonicalSelectedDiagonalDistinctCokernelAverageCertificate)
    (securityParameter : ℕ) :
    0 ≤ certificate.lossBound securityParameter :=
  certificate.toDistinctFiberAverage.lossBound_nonneg securityParameter

/-- The canonical selected-diagonal distinct mask loss is bounded directly by the exact
conditioned native cokernel average. -/
theorem CanonicalSelectedDiagonalDistinctCokernelAverageCertificate.distinctMaskLoss_le
    (certificate : CanonicalSelectedDiagonalDistinctCokernelAverageCertificate)
    (securityParameter : ℕ) :
    canonicalPostSmudgedSelectedDiagonalDistinctMaskLoss securityParameter ≤
      certificate.lossBound securityParameter :=
  certificate.toDistinctFiberAverage.distinctMaskLoss_le securityParameter

/-- Canonical distinct-pair certificate in the exact additive-character normal form.  Its finite
obligation is the factorial second moment of nontrivial common annihilators inside each retained
transformed-error fiber. -/
structure CanonicalSelectedDiagonalDistinctCharacterMomentCertificate where
  characterMomentAverageBound : ℕ → ℝ
  characterMomentAverageBound_nonneg : ∀ securityParameter,
    0 ≤ characterMomentAverageBound securityParameter
  fiberMoment : ∀ securityParameter candidate sourceError,
    sourceError ∈ support
        (ProbComp.sampleIID
          (TGSW.rowCount 1 (gaussianDecomposition securityParameter).levels)
          (sourceRingErrorSampler securityParameter)) →
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.fixedErrorDifferenceFiberCharacterFactorialMomentAverageBound
        (degree := rotationDegree securityParameter) (ringRank := 1)
        (gaussianDecomposition securityParameter) candidate sourceError
        (characterMomentAverageBound securityParameter)

/-- The character factorial-moment certificate is exactly the native retained-cokernel
certificate already consumed by the canonical security reduction. -/
noncomputable def CanonicalSelectedDiagonalDistinctCharacterMomentCertificate.toCokernel
    (certificate : CanonicalSelectedDiagonalDistinctCharacterMomentCertificate) :
    CanonicalSelectedDiagonalDistinctCokernelAverageCertificate where
  cokernelAverageBound := certificate.characterMomentAverageBound
  cokernelAverageBound_nonneg := certificate.characterMomentAverageBound_nonneg
  fiberAverage := by
    intro securityParameter candidate sourceError hsource
    exact
      (Native.ShiftedCandidateEvaluator.DiagonalNormalForm.fixedErrorDifferenceFiberDistinctCokernelAverageBound_iff_characterFactorialMoment
        (degree := rotationDegree securityParameter) (ringRank := 1)
        (gaussianDecomposition securityParameter) candidate sourceError
        (certificate.characterMomentAverageBound securityParameter)).2
          (certificate.fiberMoment securityParameter candidate sourceError hsource)

/-- Challenge-normalized square-root loss of the exact character factorial-moment certificate. -/
noncomputable def CanonicalSelectedDiagonalDistinctCharacterMomentCertificate.lossBound
    (certificate : CanonicalSelectedDiagonalDistinctCharacterMomentCertificate)
    (securityParameter : ℕ) : ℝ :=
  certificate.toCokernel.lossBound securityParameter

theorem CanonicalSelectedDiagonalDistinctCharacterMomentCertificate.lossBound_nonneg
    (certificate : CanonicalSelectedDiagonalDistinctCharacterMomentCertificate)
    (securityParameter : ℕ) :
    0 ≤ certificate.lossBound securityParameter :=
  certificate.toCokernel.lossBound_nonneg securityParameter

/-- The canonical selected-diagonal distinct mask loss is bounded by the retained nontrivial
character factorial moment. -/
theorem CanonicalSelectedDiagonalDistinctCharacterMomentCertificate.distinctMaskLoss_le
    (certificate : CanonicalSelectedDiagonalDistinctCharacterMomentCertificate)
    (securityParameter : ℕ) :
    canonicalPostSmudgedSelectedDiagonalDistinctMaskLoss securityParameter ≤
      certificate.lossBound securityParameter :=
  certificate.toCokernel.distinctMaskLoss_le securityParameter

/-- Canonical family of distribution-weighted retained-cokernel certificates.  Unlike the
support-wise certificate above, its finite self/cokernel estimates need hold only on a selected
good set; the native centered-binomial probability of the complementary set is part of the
certified loss. -/
structure CanonicalSelectedDiagonalGoodBadCokernelCertificate where
  certificateAt : ∀ securityParameter,
    FullMaskCollision.StaticDiagonal.RetainedCokernelGoodBadCertificate
      (degree := rotationDegree securityParameter) (ringRank := 1)
      (gaussianDecomposition securityParameter)
      (sourceRingErrorSampler securityParameter)

/-- Actual selected-mask loss of the distribution-weighted canonical certificate. -/
noncomputable def CanonicalSelectedDiagonalGoodBadCokernelCertificate.maskLoss
    (certificate : CanonicalSelectedDiagonalGoodBadCokernelCertificate)
    (securityParameter : ℕ) : ℝ :=
  (certificate.certificateAt securityParameter).lossBound

theorem CanonicalSelectedDiagonalGoodBadCokernelCertificate.maskLoss_nonneg
    (certificate : CanonicalSelectedDiagonalGoodBadCokernelCertificate)
    (securityParameter : ℕ) :
    0 ≤ certificate.maskLoss securityParameter :=
  (certificate.certificateAt securityParameter).lossBound_nonneg

/-- Canonical retained-cokernel certificate specialized to the high-probability event already
proved above: at least one source-error row is a unit modulo the native maximal ideal. -/
structure CanonicalSelectedDiagonalNonzeroParityCokernelCertificate where
  selfKernelAverageBound : ℕ → ℝ
  distinctCokernelAverageBound : ℕ → ℝ
  selfKernelAverageBound_nonneg : ∀ securityParameter,
    0 ≤ selfKernelAverageBound securityParameter
  distinctCokernelAverageBound_nonneg : ∀ securityParameter,
    0 ≤ distinctCokernelAverageBound securityParameter
  self : ∀ securityParameter candidate sourceError,
    sourceError ∈ support
        (ProbComp.sampleIID
          (TGSW.rowCount 1 (gaussianDecomposition securityParameter).levels)
          (sourceRingErrorSampler securityParameter)) →
      canonicalSourceErrorHasNonzeroParity securityParameter sourceError →
        Native.ShiftedCandidateEvaluator.DiagonalNormalForm.fixedErrorDifferenceFiberKernelAverageBound
          (degree := rotationDegree securityParameter) (ringRank := 1)
          (gaussianDecomposition securityParameter) candidate sourceError
          (selfKernelAverageBound securityParameter)
  distinct : ∀ securityParameter candidate sourceError,
    sourceError ∈ support
        (ProbComp.sampleIID
          (TGSW.rowCount 1 (gaussianDecomposition securityParameter).levels)
          (sourceRingErrorSampler securityParameter)) →
      canonicalSourceErrorHasNonzeroParity securityParameter sourceError →
        Native.ShiftedCandidateEvaluator.DiagonalNormalForm.fixedErrorDifferenceFiberDistinctCokernelAverageBound
          (degree := rotationDegree securityParameter) (ringRank := 1)
          (gaussianDecomposition securityParameter) candidate sourceError
          (distinctCokernelAverageBound securityParameter)

/-- Install the proved canonical parity event into the generic good/bad certificate. -/
noncomputable def CanonicalSelectedDiagonalNonzeroParityCokernelCertificate.toGoodBad
    (certificate : CanonicalSelectedDiagonalNonzeroParityCokernelCertificate) :
    CanonicalSelectedDiagonalGoodBadCokernelCertificate where
  certificateAt := fun securityParameter ↦ {
    Good := canonicalSourceErrorHasNonzeroParity securityParameter
    selfKernelAverageBound := certificate.selfKernelAverageBound securityParameter
    distinctCokernelAverageBound := certificate.distinctCokernelAverageBound securityParameter
    selfKernelAverageBound_nonneg :=
      certificate.selfKernelAverageBound_nonneg securityParameter
    distinctCokernelAverageBound_nonneg :=
      certificate.distinctCokernelAverageBound_nonneg securityParameter
    self := certificate.self securityParameter
    distinct := certificate.distinct securityParameter }

/-- Challenge-normalized loss on the proved high-probability nonzero-parity set. -/
noncomputable def CanonicalSelectedDiagonalNonzeroParityCokernelCertificate.goodLoss
    (certificate : CanonicalSelectedDiagonalNonzeroParityCokernelCertificate)
    (securityParameter : ℕ) : ℝ :=
  Native.ShiftedCandidateEvaluator.DiagonalNormalForm.retainedCokernelGoodErrorLossBound
    (degree := rotationDegree securityParameter) (ringRank := 1)
    (gaussianDecomposition securityParameter)
    (certificate.selfKernelAverageBound securityParameter)
    (certificate.distinctCokernelAverageBound securityParameter)

theorem CanonicalSelectedDiagonalNonzeroParityCokernelCertificate.goodLoss_nonneg
    (certificate : CanonicalSelectedDiagonalNonzeroParityCokernelCertificate)
    (securityParameter : ℕ) :
    0 ≤ certificate.goodLoss securityParameter :=
  Native.ShiftedCandidateEvaluator.DiagonalNormalForm.retainedCokernelGoodErrorLossBound_nonneg
    (degree := rotationDegree securityParameter)
    (gaussianDecomposition securityParameter)
    (certificate.selfKernelAverageBound securityParameter)
    (certificate.distinctCokernelAverageBound securityParameter)

theorem CanonicalSelectedDiagonalNonzeroParityCokernelCertificate.maskLoss_eq
    (certificate : CanonicalSelectedDiagonalNonzeroParityCokernelCertificate)
    (securityParameter : ℕ) :
    certificate.toGoodBad.maskLoss securityParameter =
      certificate.goodLoss securityParameter +
        Native.ShiftedCandidateEvaluator.DiagonalNormalForm.sourceErrorBadProbability
          (gaussianDecomposition securityParameter)
          (sourceRingErrorSampler securityParameter)
          (canonicalSourceErrorHasNonzeroParity securityParameter) := rfl

/-- Canonical good-event certificate with the distinct term stated directly as the exact
nontrivial-character factorial moment. -/
structure CanonicalSelectedDiagonalNonzeroParityCharacterMomentCertificate where
  selfKernelAverageBound : ℕ → ℝ
  distinctCharacterMomentAverageBound : ℕ → ℝ
  selfKernelAverageBound_nonneg : ∀ securityParameter,
    0 ≤ selfKernelAverageBound securityParameter
  distinctCharacterMomentAverageBound_nonneg : ∀ securityParameter,
    0 ≤ distinctCharacterMomentAverageBound securityParameter
  self : ∀ securityParameter candidate sourceError,
    sourceError ∈ support
        (ProbComp.sampleIID
          (TGSW.rowCount 1 (gaussianDecomposition securityParameter).levels)
          (sourceRingErrorSampler securityParameter)) →
      canonicalSourceErrorHasNonzeroParity securityParameter sourceError →
        Native.ShiftedCandidateEvaluator.DiagonalNormalForm.fixedErrorDifferenceFiberKernelAverageBound
          (degree := rotationDegree securityParameter) (ringRank := 1)
          (gaussianDecomposition securityParameter) candidate sourceError
          (selfKernelAverageBound securityParameter)
  distinct : ∀ securityParameter candidate sourceError,
    sourceError ∈ support
        (ProbComp.sampleIID
          (TGSW.rowCount 1 (gaussianDecomposition securityParameter).levels)
          (sourceRingErrorSampler securityParameter)) →
      canonicalSourceErrorHasNonzeroParity securityParameter sourceError →
        Native.ShiftedCandidateEvaluator.DiagonalNormalForm.fixedErrorDifferenceFiberCharacterFactorialMomentAverageBound
          (degree := rotationDegree securityParameter) (ringRank := 1)
          (gaussianDecomposition securityParameter) candidate sourceError
          (distinctCharacterMomentAverageBound securityParameter)

/-- Convert the exact character statement to the retained-cokernel interface with no loss. -/
noncomputable def CanonicalSelectedDiagonalNonzeroParityCharacterMomentCertificate.toCokernel
    (certificate : CanonicalSelectedDiagonalNonzeroParityCharacterMomentCertificate) :
    CanonicalSelectedDiagonalNonzeroParityCokernelCertificate where
  selfKernelAverageBound := certificate.selfKernelAverageBound
  distinctCokernelAverageBound := certificate.distinctCharacterMomentAverageBound
  selfKernelAverageBound_nonneg := certificate.selfKernelAverageBound_nonneg
  distinctCokernelAverageBound_nonneg :=
    certificate.distinctCharacterMomentAverageBound_nonneg
  self := certificate.self
  distinct := by
    intro securityParameter candidate sourceError hsource hgood
    exact
      (Native.ShiftedCandidateEvaluator.DiagonalNormalForm.fixedErrorDifferenceFiberDistinctCokernelAverageBound_iff_characterFactorialMoment
        (degree := rotationDegree securityParameter) (ringRank := 1)
        (gaussianDecomposition securityParameter) candidate sourceError
        (certificate.distinctCharacterMomentAverageBound securityParameter)).2
          (certificate.distinct securityParameter candidate sourceError hsource hgood)

/-- Install the exact character moment on the proved nonzero-parity event. -/
noncomputable def CanonicalSelectedDiagonalNonzeroParityCharacterMomentCertificate.toGoodBad
    (certificate : CanonicalSelectedDiagonalNonzeroParityCharacterMomentCertificate) :
    CanonicalSelectedDiagonalGoodBadCokernelCertificate :=
  certificate.toCokernel.toGoodBad

/-- Challenge-normalized loss of the good-event character certificate. -/
noncomputable def CanonicalSelectedDiagonalNonzeroParityCharacterMomentCertificate.goodLoss
    (certificate : CanonicalSelectedDiagonalNonzeroParityCharacterMomentCertificate)
    (securityParameter : ℕ) : ℝ :=
  certificate.toCokernel.goodLoss securityParameter

theorem CanonicalSelectedDiagonalNonzeroParityCharacterMomentCertificate.goodLoss_nonneg
    (certificate : CanonicalSelectedDiagonalNonzeroParityCharacterMomentCertificate)
    (securityParameter : ℕ) :
    0 ≤ certificate.goodLoss securityParameter :=
  certificate.toCokernel.goodLoss_nonneg securityParameter

theorem CanonicalSelectedDiagonalNonzeroParityCharacterMomentCertificate.maskLoss_eq
    (certificate : CanonicalSelectedDiagonalNonzeroParityCharacterMomentCertificate)
    (securityParameter : ℕ) :
    certificate.toGoodBad.maskLoss securityParameter =
      certificate.goodLoss securityParameter +
        Native.ShiftedCandidateEvaluator.DiagonalNormalForm.sourceErrorBadProbability
          (gaussianDecomposition securityParameter)
          (sourceRingErrorSampler securityParameter)
          (canonicalSourceErrorHasNonzeroParity securityParameter) := rfl

/-- Canonical good-event certificate whose distinct-pair obligation is stated entirely through
the explicit row-local Fourier square moment.  The canonical parity event supplies the selected
unit column used to reconstruct every retained fiber. -/
structure CanonicalSelectedDiagonalNonzeroParityRowFourierCertificate where
  selfKernelAverageBound : ℕ → ℝ
  distinctRowFourierSquareMomentAverageBound : ℕ → ℝ
  selfKernelAverageBound_nonneg : ∀ securityParameter,
    0 ≤ selfKernelAverageBound securityParameter
  distinctRowFourierSquareMomentAverageBound_nonneg : ∀ securityParameter,
    0 ≤ distinctRowFourierSquareMomentAverageBound securityParameter
  self : ∀ securityParameter candidate sourceError,
    sourceError ∈ support
        (ProbComp.sampleIID
          (TGSW.rowCount 1 (gaussianDecomposition securityParameter).levels)
          (sourceRingErrorSampler securityParameter)) →
      canonicalSourceErrorHasNonzeroParity securityParameter sourceError →
        Native.ShiftedCandidateEvaluator.DiagonalNormalForm.fixedErrorDifferenceFiberKernelAverageBound
          (degree := rotationDegree securityParameter) (ringRank := 1)
          (gaussianDecomposition securityParameter) candidate sourceError
          (selfKernelAverageBound securityParameter)
  distinct : ∀ securityParameter candidate sourceError,
    sourceError ∈ support
        (ProbComp.sampleIID
          (TGSW.rowCount 1 (gaussianDecomposition securityParameter).levels)
          (sourceRingErrorSampler securityParameter)) →
      canonicalSourceErrorHasNonzeroParity securityParameter sourceError →
        ∀ selected :
            Native.ShiftedCandidateEvaluator.DiagonalNormalForm.DifferenceDigitColumn 1
              (gaussianDecomposition securityParameter).levels,
          ∀ hunit : IsUnit (sourceError (finProdFinEquiv selected)),
            Native.ShiftedCandidateEvaluator.DiagonalNormalForm.fixedErrorDifferenceFiberRowFourierSquareMomentAverageBoundAt
              (degree := rotationDegree securityParameter) (ringRank := 1)
              (gaussianDecomposition securityParameter) candidate sourceError selected hunit
              (distinctRowFourierSquareMomentAverageBound securityParameter)

/-- Convert the row-local Fourier obligation to the exact nontrivial-character factorial-moment
certificate. -/
noncomputable def CanonicalSelectedDiagonalNonzeroParityRowFourierCertificate.toCharacterMoment
    (certificate : CanonicalSelectedDiagonalNonzeroParityRowFourierCertificate) :
    CanonicalSelectedDiagonalNonzeroParityCharacterMomentCertificate where
  selfKernelAverageBound := certificate.selfKernelAverageBound
  distinctCharacterMomentAverageBound :=
    certificate.distinctRowFourierSquareMomentAverageBound
  selfKernelAverageBound_nonneg := certificate.selfKernelAverageBound_nonneg
  distinctCharacterMomentAverageBound_nonneg :=
    certificate.distinctRowFourierSquareMomentAverageBound_nonneg
  self := certificate.self
  distinct := by
    intro securityParameter candidate sourceError hsource hgood
    obtain ⟨selected, hunit, _⟩ :=
      canonicalSourceErrorHasNonzeroParity_exists_unitColumn_fiberBound securityParameter
        candidate hgood
    exact
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.fixedErrorDifferenceFiberCharacterFactorialMomentAverageBound_of_rowFourierSquareMomentAt
          (gaussianDecomposition securityParameter) rfl
          (gaussianBase_le_modulus securityParameter) candidate sourceError selected hunit
          (certificate.distinctRowFourierSquareMomentAverageBound securityParameter)
          (certificate.distinct securityParameter candidate sourceError hsource hgood selected
            hunit)

/-- Row-Fourier certificate converted all the way to the retained native cokernel interface. -/
noncomputable def CanonicalSelectedDiagonalNonzeroParityRowFourierCertificate.toCokernel
    (certificate : CanonicalSelectedDiagonalNonzeroParityRowFourierCertificate) :
    CanonicalSelectedDiagonalNonzeroParityCokernelCertificate :=
  certificate.toCharacterMoment.toCokernel

/-- Install the row-Fourier certificate on the canonical high-probability parity event. -/
noncomputable def CanonicalSelectedDiagonalNonzeroParityRowFourierCertificate.toGoodBad
    (certificate : CanonicalSelectedDiagonalNonzeroParityRowFourierCertificate) :
    CanonicalSelectedDiagonalGoodBadCokernelCertificate :=
  certificate.toCharacterMoment.toGoodBad

/-- Challenge-normalized good-event loss of the row-Fourier certificate. -/
noncomputable def CanonicalSelectedDiagonalNonzeroParityRowFourierCertificate.goodLoss
    (certificate : CanonicalSelectedDiagonalNonzeroParityRowFourierCertificate)
    (securityParameter : ℕ) : ℝ :=
  certificate.toCharacterMoment.goodLoss securityParameter

theorem CanonicalSelectedDiagonalNonzeroParityRowFourierCertificate.goodLoss_nonneg
    (certificate : CanonicalSelectedDiagonalNonzeroParityRowFourierCertificate)
    (securityParameter : ℕ) :
    0 ≤ certificate.goodLoss securityParameter :=
  certificate.toCharacterMoment.goodLoss_nonneg securityParameter

theorem CanonicalSelectedDiagonalNonzeroParityRowFourierCertificate.maskLoss_eq
    (certificate : CanonicalSelectedDiagonalNonzeroParityRowFourierCertificate)
    (securityParameter : ℕ) :
    certificate.toGoodBad.maskLoss securityParameter =
      certificate.goodLoss securityParameter +
        Native.ShiftedCandidateEvaluator.DiagonalNormalForm.sourceErrorBadProbability
          (gaussianDecomposition securityParameter)
          (sourceRingErrorSampler securityParameter)
          (canonicalSourceErrorHasNonzeroParity securityParameter) := rfl

/-- Canonical good-event certificate whose distinct-pair obligation is the phase-aware rank-one
Fourier moment.  The structured source-error character mode has already been summed exactly, so
this interface asks only for a bound containing the non-source second-dual square mass. -/
structure CanonicalSelectedDiagonalNonzeroParityPhaseAwareFourierCertificate where
  selfKernelAverageBound : ℕ → ℝ
  distinctPhaseAwareSquareMomentAverageBound : ℕ → ℝ
  selfKernelAverageBound_nonneg : ∀ securityParameter,
    0 ≤ selfKernelAverageBound securityParameter
  distinctPhaseAwareSquareMomentAverageBound_nonneg : ∀ securityParameter,
    0 ≤ distinctPhaseAwareSquareMomentAverageBound securityParameter
  self : ∀ securityParameter candidate sourceError,
    sourceError ∈ support
        (ProbComp.sampleIID
          (TGSW.rowCount 1 (gaussianDecomposition securityParameter).levels)
          (sourceRingErrorSampler securityParameter)) →
      canonicalSourceErrorHasNonzeroParity securityParameter sourceError →
        Native.ShiftedCandidateEvaluator.DiagonalNormalForm.fixedErrorDifferenceFiberKernelAverageBound
          (degree := rotationDegree securityParameter) (ringRank := 1)
          (gaussianDecomposition securityParameter) candidate sourceError
          (selfKernelAverageBound securityParameter)
  distinct : ∀ securityParameter candidate sourceError,
    sourceError ∈ support
        (ProbComp.sampleIID
          (TGSW.rowCount 1 (gaussianDecomposition securityParameter).levels)
          (sourceRingErrorSampler securityParameter)) →
      canonicalSourceErrorHasNonzeroParity securityParameter sourceError →
        ∀ selected :
            Native.ShiftedCandidateEvaluator.DiagonalNormalForm.DifferenceDigitColumn 1
              (gaussianDecomposition securityParameter).levels,
          ∀ hunit : IsUnit (sourceError (finProdFinEquiv selected)),
            Native.ShiftedCandidateEvaluator.DiagonalNormalForm.fixedErrorDifferenceFiberRankOnePhaseAwareSquareMomentAverageBoundAt
              (degree := rotationDegree securityParameter)
              (gaussianDecomposition securityParameter) candidate sourceError selected hunit
              (distinctPhaseAwareSquareMomentAverageBound securityParameter)

/-- Convert the phase-aware Fourier obligation to the exact character factorial-moment
certificate. -/
noncomputable def CanonicalSelectedDiagonalNonzeroParityPhaseAwareFourierCertificate.toCharacterMoment
    (certificate : CanonicalSelectedDiagonalNonzeroParityPhaseAwareFourierCertificate) :
    CanonicalSelectedDiagonalNonzeroParityCharacterMomentCertificate where
  selfKernelAverageBound := certificate.selfKernelAverageBound
  distinctCharacterMomentAverageBound :=
    certificate.distinctPhaseAwareSquareMomentAverageBound
  selfKernelAverageBound_nonneg := certificate.selfKernelAverageBound_nonneg
  distinctCharacterMomentAverageBound_nonneg :=
    certificate.distinctPhaseAwareSquareMomentAverageBound_nonneg
  self := certificate.self
  distinct := by
    intro securityParameter candidate sourceError hsource hgood
    obtain ⟨selected, hunit, _⟩ :=
      canonicalSourceErrorHasNonzeroParity_exists_unitColumn_fiberBound securityParameter
        candidate hgood
    exact
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.fixedErrorDifferenceFiberCharacterFactorialMomentAverageBound_of_rankOnePhaseAwareSquareMomentAt
        (gaussianDecomposition securityParameter) rfl
        (gaussianBase_le_modulus securityParameter) candidate sourceError selected hunit
        (certificate.distinctPhaseAwareSquareMomentAverageBound securityParameter)
        (certificate.distinct securityParameter candidate sourceError hsource hgood selected hunit)

/-- Phase-aware Fourier certificate converted to the retained native cokernel interface. -/
noncomputable def CanonicalSelectedDiagonalNonzeroParityPhaseAwareFourierCertificate.toCokernel
    (certificate : CanonicalSelectedDiagonalNonzeroParityPhaseAwareFourierCertificate) :
    CanonicalSelectedDiagonalNonzeroParityCokernelCertificate :=
  certificate.toCharacterMoment.toCokernel

/-- Install the phase-aware Fourier certificate on the canonical high-probability parity event. -/
noncomputable def CanonicalSelectedDiagonalNonzeroParityPhaseAwareFourierCertificate.toGoodBad
    (certificate : CanonicalSelectedDiagonalNonzeroParityPhaseAwareFourierCertificate) :
    CanonicalSelectedDiagonalGoodBadCokernelCertificate :=
  certificate.toCharacterMoment.toGoodBad

/-- Challenge-normalized good-event loss of the phase-aware Fourier certificate. -/
noncomputable def CanonicalSelectedDiagonalNonzeroParityPhaseAwareFourierCertificate.goodLoss
    (certificate : CanonicalSelectedDiagonalNonzeroParityPhaseAwareFourierCertificate)
    (securityParameter : ℕ) : ℝ :=
  certificate.toCharacterMoment.goodLoss securityParameter

theorem CanonicalSelectedDiagonalNonzeroParityPhaseAwareFourierCertificate.goodLoss_nonneg
    (certificate : CanonicalSelectedDiagonalNonzeroParityPhaseAwareFourierCertificate)
    (securityParameter : ℕ) :
    0 ≤ certificate.goodLoss securityParameter :=
  certificate.toCharacterMoment.goodLoss_nonneg securityParameter

theorem CanonicalSelectedDiagonalNonzeroParityPhaseAwareFourierCertificate.maskLoss_eq
    (certificate : CanonicalSelectedDiagonalNonzeroParityPhaseAwareFourierCertificate)
    (securityParameter : ℕ) :
    certificate.toGoodBad.maskLoss securityParameter =
      certificate.goodLoss securityParameter +
        Native.ShiftedCandidateEvaluator.DiagonalNormalForm.sourceErrorBadProbability
          (gaussianDecomposition securityParameter)
          (sourceRingErrorSampler securityParameter)
          (canonicalSourceErrorHasNonzeroParity securityParameter) := rfl

/-- Complete retained-fiber certificate for the selected native diagonal. -/
structure CanonicalSelectedDiagonalRetainedFiberAverageCertificate where
  self : CanonicalSelectedDiagonalSelfFiberAverageCertificate
  distinct : CanonicalSelectedDiagonalDistinctFiberAverageCertificate

/-- Total selected-diagonal statistical loss exposed by the two retained-fiber certificates. -/
noncomputable def CanonicalSelectedDiagonalRetainedFiberAverageCertificate.lossBound
    (certificate : CanonicalSelectedDiagonalRetainedFiberAverageCertificate)
    (securityParameter : ℕ) : ℝ :=
  certificate.self.lossBound securityParameter +
    certificate.distinct.lossBound securityParameter

theorem CanonicalSelectedDiagonalRetainedFiberAverageCertificate.lossBound_nonneg
    (certificate : CanonicalSelectedDiagonalRetainedFiberAverageCertificate)
    (securityParameter : ℕ) :
    0 ≤ certificate.lossBound securityParameter :=
  add_nonneg
    (certificate.self.lossBound_nonneg securityParameter)
    (certificate.distinct.lossBound_nonneg securityParameter)

/-- The complete finite retained-fiber certificate bounds the exact selected-diagonal mask
loss. -/
theorem CanonicalSelectedDiagonalRetainedFiberAverageCertificate.maskLoss_le
    (certificate : CanonicalSelectedDiagonalRetainedFiberAverageCertificate)
    (securityParameter : ℕ) :
    canonicalPostSmudgedSelectedDiagonalMaskLoss securityParameter ≤
      certificate.lossBound securityParameter :=
  (canonicalPostSmudgedSelectedDiagonalMaskLoss_le_self_add_distinct
    securityParameter).trans
      (add_le_add
        (certificate.self.selfMaskLoss_le securityParameter)
        (certificate.distinct.distinctMaskLoss_le securityParameter))

/-- Source-independent finite paired-fiber bound for the sole selected-diagonal mask loss. -/
noncomputable def canonicalPostSmudgedSelectedDiagonalPairCollisionBound
    (securityParameter : ℕ) : ℝ :=
  max
    (Real.sqrt
        (Native.ShiftedCandidateEvaluator.DiagonalNormalForm.globalDifferencePairCollisionBudget
          (degree := rotationDegree securityParameter) (ringRank := 1)
          (gaussianDecomposition securityParameter) false) / 2)
    (Real.sqrt
        (Native.ShiftedCandidateEvaluator.DiagonalNormalForm.globalDifferencePairCollisionBudget
          (degree := rotationDegree securityParameter) (ringRank := 1)
          (gaussianDecomposition securityParameter) true) / 2)

theorem canonicalPostSmudgedSelectedDiagonalPairCollisionBound_nonneg
    (securityParameter : ℕ) :
    0 ≤ canonicalPostSmudgedSelectedDiagonalPairCollisionBound securityParameter := by
  unfold canonicalPostSmudgedSelectedDiagonalPairCollisionBound
  exact (div_nonneg (Real.sqrt_nonneg _) (by positivity)).trans (le_max_left _ _)

/-- The source-independent global pair budget used by the explicit corollary retains the square
single-difference obstruction on its equal-difference slice.  It is therefore at least one half
for either candidate, despite the growing rectangular paired-rank slack. -/
theorem one_half_le_canonicalPostSmudgedSelectedDiagonalGlobalBudget
    (securityParameter : ℕ) (candidate : Bool) :
    (1 : ℝ) / 2 ≤
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.globalDifferencePairCollisionBudget
        (degree := rotationDegree securityParameter) (ringRank := 1)
        (gaussianDecomposition securityParameter) candidate := by
  letI : NeZero (ringDegree securityParameter) :=
    ⟨Nat.ne_of_gt (ringDegree_pos securityParameter)⟩
  apply
    Native.ShiftedCandidateEvaluator.DiagonalNormalForm.one_half_le_globalDifferencePairCollisionBudget
      (degree := rotationDegree securityParameter)
      (gaussianDecomposition securityParameter)
      (by rfl) (ringDegree securityParameter)
  · simp [gaussianDecomposition, gaussianBase, Nat.mul_comm]
  · simp [gaussianDecomposition, gaussianLevels]

/-- Consequently the displayed source-independent pair-collision upper bound itself has a
parameter-independent positive floor.  This says nothing negative about the exact retained-fiber
selected-diagonal loss; it identifies the unconditional relaxation as the invalid asymptotic
endpoint. -/
theorem one_fourth_le_canonicalPostSmudgedSelectedDiagonalPairCollisionBound
    (securityParameter : ℕ) :
    (1 : ℝ) / 4 ≤
      canonicalPostSmudgedSelectedDiagonalPairCollisionBound securityParameter := by
  let budget :=
    Native.ShiftedCandidateEvaluator.DiagonalNormalForm.globalDifferencePairCollisionBudget
      (degree := rotationDegree securityParameter) (ringRank := 1)
      (gaussianDecomposition securityParameter) false
  have hbudget : (1 : ℝ) / 2 ≤ budget :=
    one_half_le_canonicalPostSmudgedSelectedDiagonalGlobalBudget securityParameter false
  have hsqrt : (1 : ℝ) / 2 ≤ Real.sqrt budget := by
    apply Real.le_sqrt_of_sq_le
    nlinarith
  unfold canonicalPostSmudgedSelectedDiagonalPairCollisionBound
  change (1 : ℝ) / 4 ≤ max (Real.sqrt budget / 2) _
  exact (by linarith : (1 : ℝ) / 4 ≤ Real.sqrt budget / 2).trans
    (le_max_left _ _)

/-- The explicit global pair-collision premise of the previous convenience corollary is false
for the canonical family: its proposed bound is not negligible. -/
theorem canonicalPostSmudgedSelectedDiagonalPairCollisionBound_not_negligible :
    ¬ negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalPostSmudgedSelectedDiagonalPairCollisionBound securityParameter)) := by
  intro hnegligible
  have htendsto : Tendsto
      (fun securityParameter ↦ ENNReal.ofReal
        (canonicalPostSmudgedSelectedDiagonalPairCollisionBound securityParameter))
      atTop (𝓝 0) := by
    simpa [negligible, Asymptotics.SuperpolynomialDecay] using hnegligible 0
  have hconstant : (0 : ℝ≥0∞) < ENNReal.ofReal ((1 : ℝ) / 4) := by
    norm_num
  have heventually : ∀ᶠ securityParameter in atTop,
      ENNReal.ofReal
          (canonicalPostSmudgedSelectedDiagonalPairCollisionBound securityParameter) <
        ENNReal.ofReal ((1 : ℝ) / 4) :=
    (tendsto_order.1 htendsto).2 _ hconstant
  obtain ⟨securityParameter, hsmall⟩ := heventually.exists
  exact (not_lt_of_ge (ENNReal.ofReal_le_ofReal
    (one_fourth_le_canonicalPostSmudgedSelectedDiagonalPairCollisionBound
      securityParameter))) hsmall

/-- The exact averaged selected-diagonal mask loss is bounded by the explicit global paired-fiber
count for the two possible encrypted scalar bits. -/
theorem canonicalPostSmudgedSelectedDiagonalMaskLoss_le_pairCollisionBound
    (securityParameter : ℕ) :
    canonicalPostSmudgedSelectedDiagonalMaskLoss securityParameter ≤
      canonicalPostSmudgedSelectedDiagonalPairCollisionBound securityParameter := by
  unfold canonicalPostSmudgedSelectedDiagonalMaskLoss
    canonicalPostSmudgedSelectedDiagonalPairCollisionBound
    FullMaskCollision.StaticDiagonal.worstCaseStaticMaskDiagonalChiSquareLoss
  exact max_le_max
    (Native.ShiftedCandidateEvaluator.DiagonalNormalForm.averagedSourceErrorDiagonalChiSquareLoss_le_globalDifferencePairCollisionBudget
      (degree := rotationDegree securityParameter) (ringRank := 1)
      (gaussianDecomposition securityParameter)
      (sourceRingErrorSampler securityParameter) false)
    (Native.ShiftedCandidateEvaluator.DiagonalNormalForm.averagedSourceErrorDiagonalChiSquareLoss_le_globalDifferencePairCollisionBudget
      (degree := rotationDegree securityParameter) (ringRank := 1)
      (gaussianDecomposition securityParameter)
      (sourceRingErrorSampler securityParameter) true)

/-- Complete correct-view loss for the preferred selected-diagonal route. -/
noncomputable def canonicalPostSmudgedSelectedDiagonalCorrectError
    (queryCount : ℕ → ℕ) (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) : ℝ :=
  canonicalPostSmudgedResidualErasureCost queryCount securityParameter coordinate +
    canonicalPostSmudgedSelectedDiagonalMaskLoss securityParameter

theorem canonicalPostSmudgedSelectedDiagonalCorrectError_nonneg
    (queryCount : ℕ → ℕ) (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) :
    0 ≤ canonicalPostSmudgedSelectedDiagonalCorrectError
      queryCount securityParameter coordinate :=
  add_nonneg
    (canonicalPostSmudgedResidualErasureCost_nonneg
      queryCount securityParameter coordinate)
    (canonicalPostSmudgedSelectedDiagonalMaskLoss_nonneg securityParameter)

/-- Canonical correct-view theorem with all off-diagonal mask coordinates discharged exactly.
The remaining statistical terms are residual translation and the selected diagonal joint
chi-square loss. -/
theorem canonicalPostSmudgedSelectedDiagonalCorrectDistance_le
    (queryCount : ℕ → ℕ) (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) :
    tvDist
        (PostEvaluationSmudging.averagedCorrectTransform
          (ringRank := 1) (queryCount := queryCount securityParameter)
          (gaussianDecomposition securityParameter)
          (sourceRingErrorSampler securityParameter)
          (targetRingErrorSampler canonicalCertificate securityParameter)
          (scalarErrorSampler securityParameter)
          (scalarErrorSampler securityParameter)
          (keySwitchGadget securityParameter) coordinate)
        (realPublicView (ringRank := 1)
          (lweDimension := ringDegree securityParameter)
          (queryCount := queryCount securityParameter)
          (targetRingErrorSampler canonicalCertificate securityParameter)
          (scalarErrorSampler securityParameter)
          (scalarErrorSampler securityParameter)
          (Gadget.Base.ringGadget (degree := nativeRingDegree securityParameter)
            (gaussianDecomposition securityParameter))
          (keySwitchGadget securityParameter)) ≤
      canonicalPostSmudgedSelectedDiagonalCorrectError
        queryCount securityParameter coordinate := by
  simpa only [canonicalPostSmudgedSelectedDiagonalCorrectError,
    canonicalPostSmudgedResidualErasureCost,
    canonicalPostSmudgedSelectedDiagonalMaskLoss,
    sourceRingErrorSampler, targetRingErrorSampler, nativeRingDegree] using
    (FullMaskCollision.StaticDiagonal.tvDist_averagedPostSmudgedCorrectTransform_realPublicView_le_selectedDiagonal
      (degree := rotationDegree securityParameter) (ringRank := 1)
      (lweDimension := ringDegree securityParameter)
      (queryCount := queryCount securityParameter)
      (eta := errorWidth securityParameter)
      (gaussianDecomposition securityParameter)
      (targetRingErrorSampler canonicalCertificate securityParameter)
      (scalarErrorSampler securityParameter)
      (scalarErrorSampler securityParameter)
      (keySwitchGadget securityParameter) coordinate)

/-- Complete correct-view loss using the source-error-distribution-weighted retained-cokernel
certificate. -/
noncomputable def CanonicalSelectedDiagonalGoodBadCokernelCertificate.correctError
    (certificate : CanonicalSelectedDiagonalGoodBadCokernelCertificate)
    (queryCount : ℕ → ℕ) (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) : ℝ :=
  canonicalPostSmudgedResidualErasureCost queryCount securityParameter coordinate +
    certificate.maskLoss securityParameter

theorem CanonicalSelectedDiagonalGoodBadCokernelCertificate.correctError_nonneg
    (certificate : CanonicalSelectedDiagonalGoodBadCokernelCertificate)
    (queryCount : ℕ → ℕ) (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) :
    0 ≤ certificate.correctError queryCount securityParameter coordinate :=
  add_nonneg
    (canonicalPostSmudgedResidualErasureCost_nonneg
      queryCount securityParameter coordinate)
    (certificate.maskLoss_nonneg securityParameter)

/-- The packaged good/bad cokernel law proves the actual correct native TFHE view, not merely an
averaged algebraic surrogate. -/
theorem CanonicalSelectedDiagonalGoodBadCokernelCertificate.correctDistance_le
    (certificate : CanonicalSelectedDiagonalGoodBadCokernelCertificate)
    (queryCount : ℕ → ℕ) (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) :
    tvDist
        (PostEvaluationSmudging.averagedCorrectTransform
          (ringRank := 1) (queryCount := queryCount securityParameter)
          (gaussianDecomposition securityParameter)
          (sourceRingErrorSampler securityParameter)
          (targetRingErrorSampler canonicalCertificate securityParameter)
          (scalarErrorSampler securityParameter)
          (scalarErrorSampler securityParameter)
          (keySwitchGadget securityParameter) coordinate)
        (realPublicView (ringRank := 1)
          (lweDimension := ringDegree securityParameter)
          (queryCount := queryCount securityParameter)
          (targetRingErrorSampler canonicalCertificate securityParameter)
          (scalarErrorSampler securityParameter)
          (scalarErrorSampler securityParameter)
          (Gadget.Base.ringGadget (degree := nativeRingDegree securityParameter)
            (gaussianDecomposition securityParameter))
          (keySwitchGadget securityParameter)) ≤
      certificate.correctError queryCount securityParameter coordinate := by
  simpa only [CanonicalSelectedDiagonalGoodBadCokernelCertificate.correctError,
    CanonicalSelectedDiagonalGoodBadCokernelCertificate.maskLoss,
    canonicalPostSmudgedResidualErasureCost, sourceRingErrorSampler,
    targetRingErrorSampler, nativeRingDegree] using
    (FullMaskCollision.StaticDiagonal.tvDist_averagedPostSmudgedCorrectTransform_realPublicView_le_retainedCokernelGoodBad
      (degree := rotationDegree securityParameter) (ringRank := 1)
      (lweDimension := ringDegree securityParameter)
      (queryCount := queryCount securityParameter)
      (eta := errorWidth securityParameter)
      (gaussianDecomposition securityParameter)
      (targetRingErrorSampler canonicalCertificate securityParameter)
      (scalarErrorSampler securityParameter)
      (scalarErrorSampler securityParameter)
      (keySwitchGadget securityParameter) coordinate
      (certificate.certificateAt securityParameter))

/-- Residual-free conditional collision premise for the canonical complete BRK mask.  In contrast
to the earlier full-side premise, the conditioning side does not retain the narrow residual. -/
def canonicalPostSmudgedStaticMaskConditionalCollisionBound
    (queryCount : ℕ → ℕ) (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) (ε : ℝ) : Prop :=
  FullMaskCollision.CorrectStaticMaskConditionalCollisionBound
    (degree := nativeRingDegree securityParameter) (ringRank := 1)
    (queryCount := queryCount securityParameter)
    (gaussianDecomposition securityParameter)
    (sourceRingErrorSampler securityParameter)
    (scalarErrorSampler securityParameter)
    (scalarErrorSampler securityParameter)
    (keySwitchGadget securityParameter) coordinate ε

/-- A family of residual-free complete-mask collision estimates. -/
structure CanonicalPostSmudgedStaticMaskCollisionCertificate where
  ε : (queryCount : ℕ → ℕ) → (securityParameter : ℕ) →
    Fin (ringDegree securityParameter) → ℝ
  collisionBound : ∀ queryCount securityParameter coordinate,
    canonicalPostSmudgedStaticMaskConditionalCollisionBound queryCount securityParameter
      coordinate (ε queryCount securityParameter coordinate)

/-- Correct-view statistical loss exposed by the residual-first collision certificate. -/
noncomputable def CanonicalPostSmudgedStaticMaskCollisionCertificate.correctError
    (certificate : CanonicalPostSmudgedStaticMaskCollisionCertificate)
    (queryCount : ℕ → ℕ) (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) : ℝ :=
  canonicalPostSmudgedResidualErasureCost queryCount securityParameter coordinate +
    Real.sqrt (certificate.ε queryCount securityParameter coordinate) / 2

theorem CanonicalPostSmudgedStaticMaskCollisionCertificate.correctError_nonneg
    (certificate : CanonicalPostSmudgedStaticMaskCollisionCertificate)
    (queryCount : ℕ → ℕ) (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) :
    0 ≤ certificate.correctError queryCount securityParameter coordinate := by
  exact add_nonneg
    (canonicalPostSmudgedResidualErasureCost_nonneg
      queryCount securityParameter coordinate) (by positivity)

/-- Canonical security-only normal form with the residual erased before mask replacement. -/
theorem CanonicalPostSmudgedStaticMaskCollisionCertificate.correctDistance_le
    (certificate : CanonicalPostSmudgedStaticMaskCollisionCertificate)
    (queryCount : ℕ → ℕ) (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) :
    tvDist
        (PostEvaluationSmudging.averagedCorrectTransform
          (ringRank := 1) (queryCount := queryCount securityParameter)
          (gaussianDecomposition securityParameter)
          (sourceRingErrorSampler securityParameter)
          (targetRingErrorSampler canonicalCertificate securityParameter)
          (scalarErrorSampler securityParameter)
          (scalarErrorSampler securityParameter)
          (keySwitchGadget securityParameter) coordinate)
        (realPublicView (ringRank := 1)
          (lweDimension := ringDegree securityParameter)
          (queryCount := queryCount securityParameter)
          (targetRingErrorSampler canonicalCertificate securityParameter)
          (scalarErrorSampler securityParameter)
          (scalarErrorSampler securityParameter)
          (Gadget.Base.ringGadget (degree := nativeRingDegree securityParameter)
            (gaussianDecomposition securityParameter))
          (keySwitchGadget securityParameter)) ≤
      certificate.correctError queryCount securityParameter coordinate := by
  simpa only [CanonicalPostSmudgedStaticMaskCollisionCertificate.correctError,
    canonicalPostSmudgedResidualErasureCost,
    canonicalPostSmudgedStaticMaskConditionalCollisionBound,
    sourceRingErrorSampler, targetRingErrorSampler, nativeRingDegree] using
    (FullMaskCollision.tvDist_averagedPostSmudgedCorrectTransform_centeredBinomial_realPublicView_le
      (degree := rotationDegree securityParameter) (ringRank := 1)
      (lweDimension := ringDegree securityParameter)
      (queryCount := queryCount securityParameter)
      (eta := errorWidth securityParameter)
      (gaussianDecomposition securityParameter)
      (targetRingErrorSampler canonicalCertificate securityParameter)
      (scalarErrorSampler securityParameter)
      (scalarErrorSampler securityParameter)
      (keySwitchGadget securityParameter) coordinate
      (certificate.ε queryCount securityParameter coordinate)
      (certificate.collisionBound queryCount securityParameter coordinate))

/-- At one parameter and tape length, install explicit post-evaluation smudging into the generic
averaged candidate-view interface.  Conditional Gaussian smudging supplies the correct-side
second term; exact uniform invariance preserves the one-event wrong-side bound. -/
noncomputable def CanonicalPostSmudgedNormalFormLaws.transformerAt
    (laws : CanonicalPostSmudgedNormalFormLaws)
    (queryCount : ℕ → ℕ) (securityParameter : ℕ) :
    AveragedCandidateViewTransformer
      (ringRank := 1) (lweDimension := ringDegree securityParameter)
      (queryCount := queryCount securityParameter)
      (sourceRingErrorSampler securityParameter)
      (targetRingErrorSampler canonicalCertificate securityParameter)
      (scalarErrorSampler securityParameter)
      (scalarErrorSampler securityParameter)
      (scalarErrorSampler securityParameter)
      (Gadget.Base.ringGadget (degree := nativeRingDegree securityParameter)
        (gaussianDecomposition securityParameter))
      (keySwitchGadget securityParameter) where
  transform := PostEvaluationSmudging.transform
    (gaussianDecomposition securityParameter)
    (targetRingErrorSampler canonicalCertificate securityParameter)
  correctError := fun coordinate ↦
    laws.normalFormError queryCount securityParameter coordinate +
      coupledCenteredBinomialDiscreteGaussianLinearSmudgingError
        (gaussianDecomposition securityParameter)
        (canonicalCertificate securityParameter)
        (nativeRingDegree securityParameter) 1 (ringDegree securityParameter)
        (errorWidth securityParameter)
  wrongError := fun _coordinate ↦
    canonicalWrongViewNonbijectivityError securityParameter
  correctError_nonneg := fun coordinate ↦
    add_nonneg (laws.normalFormError_nonneg queryCount securityParameter coordinate) (by
      unfold coupledCenteredBinomialDiscreteGaussianLinearSmudgingError
      exact mul_nonneg (by positivity)
        (mul_nonneg (by positivity)
          (DiscreteGaussianSampler.scalarLinearShiftBound_nonneg _ _)))
  wrongError_nonneg := fun _coordinate ↦
    canonicalWrongViewNonbijectivityError_nonneg securityParameter
  correctDistance := by
    intro coordinate
    let middle := coupledAveragedResidualRealView
      (degree := rotationDegree securityParameter) (ringRank := 1)
      (queryCount := queryCount securityParameter)
      (eta := errorWidth securityParameter)
      (gaussianDecomposition securityParameter)
      (targetRingErrorSampler canonicalCertificate securityParameter)
      (scalarErrorSampler securityParameter)
      (scalarErrorSampler securityParameter)
      (keySwitchGadget securityParameter) coordinate
    have hnormal := laws.normalFormDistance_le queryCount securityParameter coordinate
    have hsmudge : tvDist middle
        (realPublicView (ringRank := 1)
          (lweDimension := ringDegree securityParameter)
          (queryCount := queryCount securityParameter)
          (targetRingErrorSampler canonicalCertificate securityParameter)
          (scalarErrorSampler securityParameter)
          (scalarErrorSampler securityParameter)
          (Gadget.Base.ringGadget (degree := nativeRingDegree securityParameter)
            (gaussianDecomposition securityParameter))
          (keySwitchGadget securityParameter)) ≤
        coupledCenteredBinomialDiscreteGaussianLinearSmudgingError
          (gaussianDecomposition securityParameter)
          (canonicalCertificate securityParameter)
          (nativeRingDegree securityParameter) 1 (ringDegree securityParameter)
          (errorWidth securityParameter) := by
      simpa only [middle, targetRingErrorSampler, nativeRingDegree,
        coupledCenteredBinomialDiscreteGaussianLinearSmudgingError] using
        (tvDist_coupledAveragedResidualRealView_realPublicView_le_linear
          (degree := rotationDegree securityParameter) (ringRank := 1)
          (queryCount := queryCount securityParameter)
          (eta := errorWidth securityParameter)
          (gaussianDecomposition securityParameter)
          (canonicalCertificate securityParameter)
          (scalarErrorSampler securityParameter)
          (scalarErrorSampler securityParameter)
          (keySwitchGadget securityParameter) coordinate)
    unfold tvDist at hnormal hsmudge ⊢
    rw [PostEvaluationSmudging.averaged_transform_correct_evalDist
      (ringRank := 1) (queryCount := queryCount securityParameter)
      (gaussianDecomposition securityParameter)
      (sourceRingErrorSampler securityParameter)
      (targetRingErrorSampler canonicalCertificate securityParameter)
      (scalarErrorSampler securityParameter)
      (scalarErrorSampler securityParameter)
      (keySwitchGadget securityParameter) coordinate]
    exact (PMF.tvDist_triangle _ (evalDist middle) _).trans
      (add_le_add hnormal hsmudge)
  wrongDistance := by
    intro coordinate
    have horiginal :=
      tvDist_averagedWrongTransform_uniformPublicView_le_averagedMessageOneControlFailure
        (degree := rotationDegree securityParameter) (ringRank := 1)
        (lweDimension := ringDegree securityParameter)
        (queryCount := queryCount securityParameter)
        (eta := errorWidth securityParameter)
        (gaussianDecomposition securityParameter)
        (scalarErrorSampler securityParameter)
        (scalarErrorSampler securityParameter)
        (keySwitchGadget securityParameter) coordinate
    have hsmudged :=
      PostEvaluationSmudging.tvDist_averagedWrongTransform_uniformPublicView_le
        (ringRank := 1) (queryCount := queryCount securityParameter)
        (gaussianDecomposition securityParameter)
        (sourceRingErrorSampler securityParameter)
        (targetRingErrorSampler canonicalCertificate securityParameter)
        (scalarErrorSampler securityParameter)
        (scalarErrorSampler securityParameter)
        (keySwitchGadget securityParameter) coordinate
        (canonicalWrongViewNonbijectivityError securityParameter) horiginal
    unfold tvDist at hsmudged ⊢
    rw [PostEvaluationSmudging.averaged_transform_wrong_evalDist
      (ringRank := 1) (queryCount := queryCount securityParameter)
      (gaussianDecomposition securityParameter)
      (sourceRingErrorSampler securityParameter)
      (targetRingErrorSampler canonicalCertificate securityParameter)
      (scalarErrorSampler securityParameter)
      (scalarErrorSampler securityParameter)
      (keySwitchGadget securityParameter) coordinate]
    rw [← freshUniformView_eq_uniformPublicView
      (ringRank := 1) (lweDimension := ringDegree securityParameter)
      (queryCount := queryCount securityParameter)
      (sourceRingErrorSampler securityParameter)
      (scalarErrorSampler securityParameter)
      (scalarErrorSampler securityParameter)
      (Gadget.Base.ringGadget (degree := nativeRingDegree securityParameter)
        (gaussianDecomposition securityParameter))
      (keySwitchGadget securityParameter)] at hsmudged
    rw [← freshUniformView_eq_uniformPublicView
      (ringRank := 1) (lweDimension := ringDegree securityParameter)
      (queryCount := queryCount securityParameter)
      (targetRingErrorSampler canonicalCertificate securityParameter)
      (scalarErrorSampler securityParameter)
      (scalarErrorSampler securityParameter)
      (Gadget.Base.ringGadget (degree := nativeRingDegree securityParameter)
        (gaussianDecomposition securityParameter))
      (keySwitchGadget securityParameter)]
    exact hsmudged

/-- Candidate-view transformer for the residual-first collision route.  It reuses the proved
post-smudging wrong branch and replaces only the correct-view bound by the direct real-view
estimate above. -/
noncomputable def CanonicalPostSmudgedStaticMaskCollisionCertificate.transformerAt
    (certificate : CanonicalPostSmudgedStaticMaskCollisionCertificate)
    (queryCount : ℕ → ℕ) (securityParameter : ℕ) :
    AveragedCandidateViewTransformer
      (ringRank := 1) (lweDimension := ringDegree securityParameter)
      (queryCount := queryCount securityParameter)
      (sourceRingErrorSampler securityParameter)
      (targetRingErrorSampler canonicalCertificate securityParameter)
      (scalarErrorSampler securityParameter)
      (scalarErrorSampler securityParameter)
      (scalarErrorSampler securityParameter)
      (Gadget.Base.ringGadget (degree := nativeRingDegree securityParameter)
        (gaussianDecomposition securityParameter))
      (keySwitchGadget securityParameter) :=
  { canonicalPostSmudgedMaskNormalFormLaws.transformerAt
      queryCount securityParameter with
    correctError := certificate.correctError queryCount securityParameter
    correctError_nonneg := certificate.correctError_nonneg queryCount securityParameter
    correctDistance := by
      intro coordinate
      have h := certificate.correctDistance_le queryCount securityParameter coordinate
      unfold tvDist at h ⊢
      simp only [CanonicalPostSmudgedNormalFormLaws.transformerAt]
      rw [PostEvaluationSmudging.averaged_transform_correct_evalDist
        (ringRank := 1) (queryCount := queryCount securityParameter)
        (gaussianDecomposition securityParameter)
        (sourceRingErrorSampler securityParameter)
        (targetRingErrorSampler canonicalCertificate securityParameter)
        (scalarErrorSampler securityParameter)
        (scalarErrorSampler securityParameter)
        (keySwitchGadget securityParameter) coordinate]
      exact h }

/-- Parameter-indexed one-shot transformer for the residual-free static-mask certificate. -/
noncomputable def CanonicalPostSmudgedStaticMaskCollisionCertificate.toOneShotTransformer
    (certificate : CanonicalPostSmudgedStaticMaskCollisionCertificate) :
    Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.TransformerFamily
      (parameters canonicalCertificate) errorWidth errorWidth where
  transformerAt := certificate.transformerAt

@[simp]
theorem CanonicalPostSmudgedStaticMaskCollisionCertificate.transformerAt_correctError
    (certificate : CanonicalPostSmudgedStaticMaskCollisionCertificate)
    (queryCount : ℕ → ℕ) (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) :
    (certificate.transformerAt queryCount securityParameter).correctError coordinate =
      certificate.correctError queryCount securityParameter coordinate := rfl

@[simp]
theorem CanonicalPostSmudgedStaticMaskCollisionCertificate.transformerAt_wrongError
    (certificate : CanonicalPostSmudgedStaticMaskCollisionCertificate)
    (queryCount : ℕ → ℕ) (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) :
    (certificate.transformerAt queryCount securityParameter).wrongError coordinate =
      canonicalWrongViewNonbijectivityError securityParameter := rfl

/-- Candidate-view transformer whose correct branch is certified by the actual
source-error-weighted retained-cokernel law. -/
noncomputable def CanonicalSelectedDiagonalGoodBadCokernelCertificate.transformerAt
    (certificate : CanonicalSelectedDiagonalGoodBadCokernelCertificate)
    (queryCount : ℕ → ℕ) (securityParameter : ℕ) :
    AveragedCandidateViewTransformer
      (ringRank := 1) (lweDimension := ringDegree securityParameter)
      (queryCount := queryCount securityParameter)
      (sourceRingErrorSampler securityParameter)
      (targetRingErrorSampler canonicalCertificate securityParameter)
      (scalarErrorSampler securityParameter)
      (scalarErrorSampler securityParameter)
      (scalarErrorSampler securityParameter)
      (Gadget.Base.ringGadget (degree := nativeRingDegree securityParameter)
        (gaussianDecomposition securityParameter))
      (keySwitchGadget securityParameter) :=
  { canonicalPostSmudgedMaskNormalFormLaws.transformerAt
      queryCount securityParameter with
    correctError := certificate.correctError queryCount securityParameter
    correctError_nonneg := certificate.correctError_nonneg queryCount securityParameter
    correctDistance := by
      intro coordinate
      have h := certificate.correctDistance_le queryCount securityParameter coordinate
      unfold tvDist at h ⊢
      simp only [CanonicalPostSmudgedNormalFormLaws.transformerAt]
      rw [PostEvaluationSmudging.averaged_transform_correct_evalDist
        (ringRank := 1) (queryCount := queryCount securityParameter)
        (gaussianDecomposition securityParameter)
        (sourceRingErrorSampler securityParameter)
        (targetRingErrorSampler canonicalCertificate securityParameter)
        (scalarErrorSampler securityParameter)
        (scalarErrorSampler securityParameter)
        (keySwitchGadget securityParameter) coordinate]
      exact h }

/-- Parameter-indexed one-shot transformer for the distribution-weighted retained-cokernel
proof. -/
noncomputable def CanonicalSelectedDiagonalGoodBadCokernelCertificate.toOneShotTransformer
    (certificate : CanonicalSelectedDiagonalGoodBadCokernelCertificate) :
    Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.TransformerFamily
      (parameters canonicalCertificate) errorWidth errorWidth where
  transformerAt := certificate.transformerAt

@[simp]
theorem CanonicalSelectedDiagonalGoodBadCokernelCertificate.transformerAt_correctError
    (certificate : CanonicalSelectedDiagonalGoodBadCokernelCertificate)
    (queryCount : ℕ → ℕ) (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) :
    (certificate.transformerAt queryCount securityParameter).correctError coordinate =
      certificate.correctError queryCount securityParameter coordinate := rfl

@[simp]
theorem CanonicalSelectedDiagonalGoodBadCokernelCertificate.transformerAt_wrongError
    (certificate : CanonicalSelectedDiagonalGoodBadCokernelCertificate)
    (queryCount : ℕ → ℕ) (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) :
    (certificate.transformerAt queryCount securityParameter).wrongError coordinate =
      canonicalWrongViewNonbijectivityError securityParameter := rfl

/-- Candidate transformer for the selected-diagonal route.  The correct branch uses the direct
real-view theorem above; the already proved post-smudged wrong branch is reused unchanged. -/
noncomputable def canonicalPostSmudgedSelectedDiagonalTransformerAt
    (queryCount : ℕ → ℕ) (securityParameter : ℕ) :
    AveragedCandidateViewTransformer
      (ringRank := 1) (lweDimension := ringDegree securityParameter)
      (queryCount := queryCount securityParameter)
      (sourceRingErrorSampler securityParameter)
      (targetRingErrorSampler canonicalCertificate securityParameter)
      (scalarErrorSampler securityParameter)
      (scalarErrorSampler securityParameter)
      (scalarErrorSampler securityParameter)
      (Gadget.Base.ringGadget (degree := nativeRingDegree securityParameter)
        (gaussianDecomposition securityParameter))
      (keySwitchGadget securityParameter) :=
  { canonicalPostSmudgedMaskNormalFormLaws.transformerAt
      queryCount securityParameter with
    correctError := canonicalPostSmudgedSelectedDiagonalCorrectError
      queryCount securityParameter
    correctError_nonneg := canonicalPostSmudgedSelectedDiagonalCorrectError_nonneg
      queryCount securityParameter
    correctDistance := by
      intro coordinate
      have h := canonicalPostSmudgedSelectedDiagonalCorrectDistance_le
        queryCount securityParameter coordinate
      unfold tvDist at h ⊢
      simp only [CanonicalPostSmudgedNormalFormLaws.transformerAt]
      rw [PostEvaluationSmudging.averaged_transform_correct_evalDist
        (ringRank := 1) (queryCount := queryCount securityParameter)
        (gaussianDecomposition securityParameter)
        (sourceRingErrorSampler securityParameter)
        (targetRingErrorSampler canonicalCertificate securityParameter)
        (scalarErrorSampler securityParameter)
        (scalarErrorSampler securityParameter)
        (keySwitchGadget securityParameter) coordinate]
      exact h }

/-- Parameter-indexed one-shot candidate transformer for the selected-diagonal proof. -/
noncomputable def canonicalPostSmudgedSelectedDiagonalOneShotTransformer :
    Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.TransformerFamily
      (parameters canonicalCertificate) errorWidth errorWidth where
  transformerAt := canonicalPostSmudgedSelectedDiagonalTransformerAt

@[simp]
theorem canonicalPostSmudgedSelectedDiagonalTransformerAt_correctError
    (queryCount : ℕ → ℕ) (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) :
    (canonicalPostSmudgedSelectedDiagonalTransformerAt
      queryCount securityParameter).correctError coordinate =
        canonicalPostSmudgedSelectedDiagonalCorrectError
          queryCount securityParameter coordinate := rfl

@[simp]
theorem canonicalPostSmudgedSelectedDiagonalTransformerAt_wrongError
    (queryCount : ℕ → ℕ) (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) :
    (canonicalPostSmudgedSelectedDiagonalTransformerAt
      queryCount securityParameter).wrongError coordinate =
        canonicalWrongViewNonbijectivityError securityParameter := rfl

/-- Parameter-indexed one-shot transformer using the explicit post-evaluation smudger. -/
noncomputable def CanonicalPostSmudgedNormalFormLaws.toOneShotTransformer
    (laws : CanonicalPostSmudgedNormalFormLaws) :
    Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.TransformerFamily
      (parameters canonicalCertificate) errorWidth errorWidth where
  transformerAt := laws.transformerAt

@[simp]
theorem CanonicalPostSmudgedNormalFormLaws.transformerAt_correctError
    (laws : CanonicalPostSmudgedNormalFormLaws)
    (queryCount : ℕ → ℕ) (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) :
    (laws.transformerAt queryCount securityParameter).correctError coordinate =
      laws.normalFormError queryCount securityParameter coordinate +
        coupledCenteredBinomialDiscreteGaussianLinearSmudgingError
          (gaussianDecomposition securityParameter)
          (canonicalCertificate securityParameter)
          (nativeRingDegree securityParameter) 1 (ringDegree securityParameter)
          (errorWidth securityParameter) := rfl

@[simp]
theorem CanonicalPostSmudgedNormalFormLaws.transformerAt_wrongError
    (laws : CanonicalPostSmudgedNormalFormLaws)
    (queryCount : ℕ → ℕ) (securityParameter : ℕ)
    (coordinate : Fin (ringDegree securityParameter)) :
    (laws.transformerAt queryCount securityParameter).wrongError coordinate =
      canonicalWrongViewNonbijectivityError securityParameter := rfl

/-- Canonical selected scalar coordinate for the nonzero growing dimension. -/
def referenceCoordinate (securityParameter : ℕ) :
    Fin (ringDegree securityParameter) :=
  ⟨0, ringDegree_pos securityParameter⟩

/-- Selected-coordinate generated-control off-diagonal expectation used by the preferred
security-only endpoint. -/
noncomputable def canonicalSelectedAveragedOffDiagonalError
    (securityParameter : ℕ) : ℝ :=
  canonicalAveragedOffDiagonalError securityParameter
    (referenceCoordinate securityParameter)

theorem canonicalSelectedAveragedOffDiagonalError_nonneg
    (securityParameter : ℕ) :
    0 ≤ canonicalSelectedAveragedOffDiagonalError securityParameter :=
  canonicalAveragedOffDiagonalError_nonneg securityParameter
    (referenceCoordinate securityParameter)

/-- Selected-coordinate effective-residual `L²` loss used by the strongest security-only
endpoint. -/
noncomputable def canonicalSelectedAveragedOffDiagonalResidualL2Error
    (securityParameter : ℕ) : ℝ :=
  canonicalAveragedOffDiagonalResidualL2Error securityParameter
    (referenceCoordinate securityParameter)

theorem canonicalSelectedAveragedOffDiagonalResidualL2Error_nonneg
    (securityParameter : ℕ) :
    0 ≤ canonicalSelectedAveragedOffDiagonalResidualL2Error securityParameter :=
  canonicalAveragedOffDiagonalResidualL2Error_nonneg securityParameter
    (referenceCoordinate securityParameter)

/-- Selected-coordinate error-only off-diagonal loss used by the strongest security endpoint. -/
noncomputable def canonicalSelectedAveragedOffDiagonalErrorOnlyL2Error
    (securityParameter : ℕ) : ℝ :=
  canonicalAveragedOffDiagonalErrorOnlyL2Error securityParameter
    (referenceCoordinate securityParameter)

theorem canonicalSelectedAveragedOffDiagonalErrorOnlyL2Error_nonneg
    (securityParameter : ℕ) :
    0 ≤ canonicalSelectedAveragedOffDiagonalErrorOnlyL2Error securityParameter :=
  canonicalAveragedOffDiagonalErrorOnlyL2Error_nonneg securityParameter
    (referenceCoordinate securityParameter)

/-- Selected-coordinate explicit finite-count off-diagonal loss. -/
noncomputable def canonicalSelectedAveragedOffDiagonalFiberL2Error
    (securityParameter : ℕ) : ℝ :=
  canonicalAveragedOffDiagonalFiberL2Error securityParameter
    (referenceCoordinate securityParameter)

/-- Selected-coordinate IID digit/bit-pair/ticket fiber loss. -/
noncomputable def canonicalSelectedAveragedOffDiagonalDigitFiberL2Error
    (securityParameter : ℕ) : ℝ :=
  canonicalAveragedOffDiagonalDigitFiberL2Error securityParameter
    (referenceCoordinate securityParameter)

theorem canonicalSelectedAveragedOffDiagonalErrorOnlyL2Error_eq_fiber
    (securityParameter : ℕ) :
    canonicalSelectedAveragedOffDiagonalErrorOnlyL2Error securityParameter =
      canonicalSelectedAveragedOffDiagonalFiberL2Error securityParameter :=
  canonicalAveragedOffDiagonalErrorOnlyL2Error_eq_fiber securityParameter
    (referenceCoordinate securityParameter)

theorem canonicalSelectedAveragedOffDiagonalFiberL2Error_nonneg
    (securityParameter : ℕ) :
    0 ≤ canonicalSelectedAveragedOffDiagonalFiberL2Error securityParameter :=
  canonicalAveragedOffDiagonalFiberL2Error_nonneg securityParameter
    (referenceCoordinate securityParameter)

theorem canonicalSelectedAveragedOffDiagonalErrorOnlyL2Error_eq_digitFiber
    (securityParameter : ℕ) :
    canonicalSelectedAveragedOffDiagonalErrorOnlyL2Error securityParameter =
      canonicalSelectedAveragedOffDiagonalDigitFiberL2Error securityParameter :=
  canonicalAveragedOffDiagonalErrorOnlyL2Error_eq_digitFiber securityParameter
    (referenceCoordinate securityParameter)

theorem canonicalSelectedAveragedOffDiagonalDigitFiberL2Error_nonneg
    (securityParameter : ℕ) :
    0 ≤ canonicalSelectedAveragedOffDiagonalDigitFiberL2Error securityParameter :=
  canonicalAveragedOffDiagonalDigitFiberL2Error_nonneg securityParameter
    (referenceCoordinate securityParameter)

/-- Sum of the explicit conditionally residualized off-diagonal losses in the selected output
row. -/
noncomputable def CanonicalOffDiagonalLaws.selectedOffDiagonalError
    (laws : CanonicalOffDiagonalLaws) (securityParameter : ℕ) : ℝ :=
  ∑ outputCoordinate ∈ Finset.univ.erase (referenceCoordinate securityParameter),
    laws.offDiagonalError securityParameter (referenceCoordinate securityParameter)
      outputCoordinate

theorem CanonicalOffDiagonalLaws.selectedOffDiagonalError_nonneg
    (laws : CanonicalOffDiagonalLaws) (securityParameter : ℕ) :
    0 ≤ laws.selectedOffDiagonalError securityParameter := by
  exact Finset.sum_nonneg fun outputCoordinate _ ↦
    laws.offDiagonalError_nonneg securityParameter
      (referenceCoordinate securityParameter) outputCoordinate

/-- Selected off-diagonal loss for the canonical finite worst-case operator laws. -/
noncomputable def canonicalSelectedOffDiagonalOperatorError
    (securityParameter : ℕ) : ℝ :=
  canonicalOffDiagonalOperatorLaws.selectedOffDiagonalError securityParameter

theorem canonicalSelectedOffDiagonalOperatorError_nonneg
    (securityParameter : ℕ) :
    0 ≤ canonicalSelectedOffDiagonalOperatorError securityParameter :=
  canonicalOffDiagonalOperatorLaws.selectedOffDiagonalError_nonneg securityParameter

/-- Exact selected-coordinate correct loss exposed by the direct diagonal/off-diagonal compiler. -/
noncomputable def CanonicalCorrectViewLaws.selectedCorrectError
    (laws : CanonicalCorrectViewLaws) (securityParameter : ℕ) : ℝ :=
  laws.diagonalError securityParameter (referenceCoordinate securityParameter) +
    ∑ outputCoordinate ∈ Finset.univ.erase (referenceCoordinate securityParameter),
      laws.offDiagonalError securityParameter (referenceCoordinate securityParameter)
        outputCoordinate

@[simp]
theorem CanonicalOffDiagonalLaws.toCanonicalCorrectViewLaws_selectedCorrectError
    (laws : CanonicalOffDiagonalLaws) (securityParameter : ℕ) :
    laws.toCanonicalCorrectViewLaws.selectedCorrectError securityParameter =
      canonicalSharpDiagonalError securityParameter +
        laws.selectedOffDiagonalError securityParameter := rfl

@[simp]
theorem CanonicalCorrectViewLaws.toDirectCertificateFamily_correctError
    (laws : CanonicalCorrectViewLaws) (queryCount : ℕ → ℕ)
    (securityParameter : ℕ) :
    (laws.toDirectCertificateFamily queryCount securityParameter).correctError
        (referenceCoordinate securityParameter) =
      laws.selectedCorrectError securityParameter := rfl

@[simp]
theorem CanonicalCorrectViewLaws.toDirectCertificateFamily_freshnessError
    (laws : CanonicalCorrectViewLaws) (queryCount : ℕ → ℕ)
    (securityParameter : ℕ) :
    (laws.toDirectCertificateFamily queryCount securityParameter).freshnessError
        (referenceCoordinate securityParameter) =
      canonicalWrongViewFreshnessError securityParameter := rfl

@[simp]
theorem canonicalAveragedDirectCertificateFamily_correctError
    (queryCount : ℕ → ℕ) (securityParameter : ℕ) :
    (canonicalAveragedDirectCertificateFamily queryCount securityParameter).correctError
        (referenceCoordinate securityParameter) =
      canonicalSharpDiagonalError securityParameter +
        canonicalSelectedAveragedOffDiagonalError securityParameter := rfl

@[simp]
theorem canonicalAveragedDirectCertificateFamily_freshnessError
    (queryCount : ℕ → ℕ) (securityParameter : ℕ) :
    (canonicalAveragedDirectCertificateFamily queryCount securityParameter).freshnessError
        (referenceCoordinate securityParameter) =
      canonicalWrongViewFreshnessError securityParameter := rfl

@[simp]
theorem canonicalResidualL2DirectCertificateFamily_correctError
    (queryCount : ℕ → ℕ) (securityParameter : ℕ) :
    (canonicalResidualL2DirectCertificateFamily queryCount securityParameter).correctError
        (referenceCoordinate securityParameter) =
      canonicalSharpDiagonalError securityParameter +
        canonicalSelectedAveragedOffDiagonalResidualL2Error securityParameter := rfl

@[simp]
theorem canonicalErrorOnlyL2DirectCertificateFamily_correctError
    (queryCount : ℕ → ℕ) (securityParameter : ℕ) :
    (canonicalErrorOnlyL2DirectCertificateFamily queryCount securityParameter).correctError
        (referenceCoordinate securityParameter) =
      canonicalSharpDiagonalError securityParameter +
        canonicalSelectedAveragedOffDiagonalErrorOnlyL2Error securityParameter := rfl

@[simp]
theorem canonicalResidualL2DirectCertificateFamily_freshnessError
    (queryCount : ℕ → ℕ) (securityParameter : ℕ) :
    (canonicalResidualL2DirectCertificateFamily queryCount securityParameter).freshnessError
        (referenceCoordinate securityParameter) =
      canonicalWrongViewFreshnessError securityParameter := rfl

@[simp]
theorem canonicalErrorOnlyL2DirectCertificateFamily_freshnessError
    (queryCount : ℕ → ℕ) (securityParameter : ℕ) :
    (canonicalErrorOnlyL2DirectCertificateFamily queryCount securityParameter).freshnessError
        (referenceCoordinate securityParameter) =
      canonicalWrongViewFreshnessError securityParameter := rfl

@[simp]
theorem canonicalErrorOnlyL2ControlFailureDirectCertificateFamily_correctError
    (queryCount : ℕ → ℕ) (securityParameter : ℕ) :
    (canonicalErrorOnlyL2ControlFailureDirectCertificateFamily queryCount
        securityParameter).correctError (referenceCoordinate securityParameter) =
      canonicalSharpDiagonalError securityParameter +
        canonicalSelectedAveragedOffDiagonalErrorOnlyL2Error securityParameter := rfl

@[simp]
theorem canonicalErrorOnlyL2ControlFailureDirectCertificateFamily_freshnessError
    (queryCount : ℕ → ℕ) (securityParameter : ℕ) :
    (canonicalErrorOnlyL2ControlFailureDirectCertificateFamily queryCount
        securityParameter).freshnessError (referenceCoordinate securityParameter) =
      canonicalWrongViewNonbijectivityError securityParameter := rfl

/-- The direct certificate's selected-coordinate correct error is negligible once its native
normal-form term and the finite Gaussian compilation error are negligible. -/
theorem selectedCorrectError_negligible
    (certificate : ScalarCertificateFamily)
    (native : CoupledDirectCertificateFamily certificate)
    (queryCount : ℕ → ℕ)
    (hcertificate : negligible (fun securityParameter ↦
      (certificate securityParameter).bound))
    (hnormalForm : negligible (fun securityParameter ↦ ENNReal.ofReal
      (native.normalFormError queryCount securityParameter
        (referenceCoordinate securityParameter)))) :
    negligible (fun securityParameter ↦ ENNReal.ofReal
      ((native.directAt queryCount securityParameter).correctError
        (referenceCoordinate securityParameter))) := by
  have h :=
    Native.ShiftedDiscreteGaussian.Asymptotic.candidateCorrectError_negligible_of_two_pow_window
      polynomialGrowth gaussianAlpha gaussianAlpha_pos certificate
      (fun securityParameter ↦ ENNReal.ofReal
        (native.normalFormError queryCount securityParameter
          (referenceCoordinate securityParameter)))
      two_pow_le_integerStddev hcertificate hnormalForm
  have heq :
      (fun securityParameter ↦ ENNReal.ofReal
        ((native.directAt queryCount securityParameter).correctError
          (referenceCoordinate securityParameter))) =
      (fun securityParameter ↦
        ENNReal.ofReal
            (native.normalFormError queryCount securityParameter
              (referenceCoordinate securityParameter)) +
          Native.ShiftedDiscreteGaussian.Asymptotic.correctSmudgingError
            gaussianDecomposition gaussianAlpha gaussianAlpha_pos certificate
            nativeRingDegree (fun _ ↦ 1) ringDegree errorWidth securityParameter) := by
    funext securityParameter
    rw [native.correctError_eq]
    have hsmudge :
        0 ≤ coupledCenteredBinomialDiscreteGaussianLinearSmudgingError
          (gaussianDecomposition securityParameter)
          (certificate securityParameter)
          (nativeRingDegree securityParameter) 1 (ringDegree securityParameter)
          (errorWidth securityParameter) := by
      unfold coupledCenteredBinomialDiscreteGaussianLinearSmudgingError
      apply mul_nonneg
      · positivity
      · apply mul_nonneg
        · positivity
        · exact DiscreteGaussianSampler.scalarLinearShiftBound_nonneg _ _
    rw [ENNReal.ofReal_add
      (native.normalFormError_nonneg queryCount securityParameter
        (referenceCoordinate securityParameter)) hsmudge]
    rfl
  rw [heq]
  exact h

/-- Canonical finite Gaussian rounding discharges the compilation premise in the selected
correct-side error theorem. -/
theorem canonicalSelectedCorrectError_negligible
    (native : CoupledDirectCertificateFamily canonicalCertificate)
    (queryCount : ℕ → ℕ)
    (hnormalForm : negligible (fun securityParameter ↦ ENNReal.ofReal
      (native.normalFormError queryCount securityParameter
        (referenceCoordinate securityParameter)))) :
    negligible (fun securityParameter ↦ ENNReal.ofReal
      ((native.directAt queryCount securityParameter).correctError
        (referenceCoordinate securityParameter))) :=
  selectedCorrectError_negligible canonicalCertificate native queryCount
    canonicalCertificate_bound_negligible hnormalForm

/-- The selected correct-view error of the explicit post-evaluation smudger is negligible once
its sole normal-form loss is negligible.  The finite wide-Gaussian translation loss is discharged
by the canonical exponential window, rather than exposed as a security assumption. -/
theorem CanonicalPostSmudgedNormalFormLaws.selectedCorrectError_negligible
    (laws : CanonicalPostSmudgedNormalFormLaws)
    (queryCount : ℕ → ℕ)
    (hnormalForm : negligible (fun securityParameter ↦ ENNReal.ofReal
      (laws.normalFormError queryCount securityParameter
        (referenceCoordinate securityParameter)))) :
    negligible (fun securityParameter ↦ ENNReal.ofReal
      ((laws.transformerAt queryCount securityParameter).correctError
        (referenceCoordinate securityParameter))) := by
  have h :=
    Native.ShiftedDiscreteGaussian.Asymptotic.candidateCorrectError_negligible_of_two_pow_window
      polynomialGrowth gaussianAlpha gaussianAlpha_pos canonicalCertificate
      (fun securityParameter ↦ ENNReal.ofReal
        (laws.normalFormError queryCount securityParameter
          (referenceCoordinate securityParameter)))
      two_pow_le_integerStddev canonicalCertificate_bound_negligible hnormalForm
  have heq :
      (fun securityParameter ↦ ENNReal.ofReal
        ((laws.transformerAt queryCount securityParameter).correctError
          (referenceCoordinate securityParameter))) =
      (fun securityParameter ↦
        ENNReal.ofReal
            (laws.normalFormError queryCount securityParameter
              (referenceCoordinate securityParameter)) +
          Native.ShiftedDiscreteGaussian.Asymptotic.correctSmudgingError
            gaussianDecomposition gaussianAlpha gaussianAlpha_pos canonicalCertificate
            nativeRingDegree (fun _ ↦ 1) ringDegree errorWidth securityParameter) := by
    funext securityParameter
    rw [laws.transformerAt_correctError]
    have hsmudge :
        0 ≤ coupledCenteredBinomialDiscreteGaussianLinearSmudgingError
          (gaussianDecomposition securityParameter)
          (canonicalCertificate securityParameter)
          (nativeRingDegree securityParameter) 1 (ringDegree securityParameter)
          (errorWidth securityParameter) := by
      unfold coupledCenteredBinomialDiscreteGaussianLinearSmudgingError
      apply mul_nonneg
      · positivity
      · apply mul_nonneg
        · positivity
        · exact DiscreteGaussianSampler.scalarLinearShiftBound_nonneg _ _
    rw [ENNReal.ofReal_add
      (laws.normalFormError_nonneg queryCount securityParameter
        (referenceCoordinate securityParameter)) hsmudge]
    rfl
  rw [heq]
  exact h

/-- The canonical residual-erasure expectation is negligible for every polynomial tape-length
function; it is pointwise dominated by the already checked growing-window Gaussian term. -/
theorem canonicalPostSmudgedResidualErasureCost_negligible
    (queryCount : ℕ → ℕ) :
    negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalPostSmudgedResidualErasureCost queryCount securityParameter
        (referenceCoordinate securityParameter))) := by
  apply negligible_of_le _ canonicalCorrectSmudgingError_negligible
  intro securityParameter
  exact ENNReal.ofReal_le_ofReal
    (canonicalPostSmudgedResidualErasureCost_le_linearSmudgingError
      queryCount securityParameter (referenceCoordinate securityParameter))

/-- A negligible distribution-weighted retained-cokernel loss gives a negligible complete
correct-view error; the wide-noise residual-erasure term remains discharged internally. -/
theorem CanonicalSelectedDiagonalGoodBadCokernelCertificate.correctError_negligible
    (certificate : CanonicalSelectedDiagonalGoodBadCokernelCertificate)
    (queryCount : ℕ → ℕ)
    (hMask : negligible (fun securityParameter ↦ ENNReal.ofReal
      (certificate.maskLoss securityParameter))) :
    negligible (fun securityParameter ↦ ENNReal.ofReal
      ((certificate.transformerAt queryCount securityParameter).correctError
        (referenceCoordinate securityParameter))) := by
  have hsum := negligible_add
    (canonicalPostSmudgedResidualErasureCost_negligible queryCount) hMask
  have heq :
      (fun securityParameter ↦ ENNReal.ofReal
        ((certificate.transformerAt queryCount securityParameter).correctError
          (referenceCoordinate securityParameter))) =
      (fun securityParameter ↦
        ENNReal.ofReal
            (canonicalPostSmudgedResidualErasureCost queryCount securityParameter
              (referenceCoordinate securityParameter)) +
          ENNReal.ofReal (certificate.maskLoss securityParameter)) := by
    funext securityParameter
    rw [certificate.transformerAt_correctError]
    unfold CanonicalSelectedDiagonalGoodBadCokernelCertificate.correctError
    rw [ENNReal.ofReal_add
      (canonicalPostSmudgedResidualErasureCost_nonneg queryCount securityParameter
        (referenceCoordinate securityParameter))
      (certificate.maskLoss_nonneg securityParameter)]
  rw [heq]
  exact hsum

/-- For the specialized nonzero-parity certificate, negligibility of the good-error cokernel
loss is sufficient: the bad-error term is the inverse-exponential probability proved internally. -/
theorem CanonicalSelectedDiagonalNonzeroParityCokernelCertificate.maskLoss_negligible
    (certificate : CanonicalSelectedDiagonalNonzeroParityCokernelCertificate)
    (hGood : negligible (fun securityParameter ↦ ENNReal.ofReal
      (certificate.goodLoss securityParameter))) :
    negligible (fun securityParameter ↦ ENNReal.ofReal
      (certificate.toGoodBad.maskLoss securityParameter)) := by
  have hsum := negligible_add hGood canonicalSourceErrorBadProbability_negligible
  have heq :
      (fun securityParameter ↦ ENNReal.ofReal
        (certificate.toGoodBad.maskLoss securityParameter)) =
      (fun securityParameter ↦
        ENNReal.ofReal (certificate.goodLoss securityParameter) +
          ENNReal.ofReal
            (Native.ShiftedCandidateEvaluator.DiagonalNormalForm.sourceErrorBadProbability
              (gaussianDecomposition securityParameter)
              (sourceRingErrorSampler securityParameter)
              (canonicalSourceErrorHasNonzeroParity securityParameter))) := by
    funext securityParameter
    rw [certificate.maskLoss_eq]
    rw [ENNReal.ofReal_add
      (certificate.goodLoss_nonneg securityParameter)
      (Native.ShiftedCandidateEvaluator.DiagonalNormalForm.sourceErrorBadProbability_nonneg
        (gaussianDecomposition securityParameter)
        (sourceRingErrorSampler securityParameter)
        (canonicalSourceErrorHasNonzeroParity securityParameter))]
  rw [heq]
  exact hsum

/-- The exact character-moment formulation inherits the complete good/bad selected-mask
negligibility theorem without any relaxation. -/
theorem CanonicalSelectedDiagonalNonzeroParityCharacterMomentCertificate.maskLoss_negligible
    (certificate : CanonicalSelectedDiagonalNonzeroParityCharacterMomentCertificate)
    (hGood : negligible (fun securityParameter ↦ ENNReal.ofReal
      (certificate.goodLoss securityParameter))) :
    negligible (fun securityParameter ↦ ENNReal.ofReal
      (certificate.toGoodBad.maskLoss securityParameter)) := by
  simpa only [CanonicalSelectedDiagonalNonzeroParityCharacterMomentCertificate.goodLoss,
    CanonicalSelectedDiagonalNonzeroParityCharacterMomentCertificate.toGoodBad] using
      certificate.toCokernel.maskLoss_negligible hGood

/-- The row-local Fourier formulation inherits the complete good/bad selected-mask
negligibility theorem through its exact character-moment conversion. -/
theorem CanonicalSelectedDiagonalNonzeroParityRowFourierCertificate.maskLoss_negligible
    (certificate : CanonicalSelectedDiagonalNonzeroParityRowFourierCertificate)
    (hGood : negligible (fun securityParameter ↦ ENNReal.ofReal
      (certificate.goodLoss securityParameter))) :
    negligible (fun securityParameter ↦ ENNReal.ofReal
      (certificate.toGoodBad.maskLoss securityParameter)) := by
  simpa only [CanonicalSelectedDiagonalNonzeroParityRowFourierCertificate.goodLoss,
    CanonicalSelectedDiagonalNonzeroParityRowFourierCertificate.toGoodBad] using
      certificate.toCharacterMoment.maskLoss_negligible hGood

/-- The phase-aware Fourier formulation inherits the complete good/bad selected-mask
negligibility theorem after exact conversion to the character factorial moment. -/
theorem CanonicalSelectedDiagonalNonzeroParityPhaseAwareFourierCertificate.maskLoss_negligible
    (certificate : CanonicalSelectedDiagonalNonzeroParityPhaseAwareFourierCertificate)
    (hGood : negligible (fun securityParameter ↦ ENNReal.ofReal
      (certificate.goodLoss securityParameter))) :
    negligible (fun securityParameter ↦ ENNReal.ofReal
      (certificate.toGoodBad.maskLoss securityParameter)) := by
  simpa only [CanonicalSelectedDiagonalNonzeroParityPhaseAwareFourierCertificate.goodLoss,
    CanonicalSelectedDiagonalNonzeroParityPhaseAwareFourierCertificate.toGoodBad] using
      certificate.toCharacterMoment.maskLoss_negligible hGood

/-- The selected correct-view error is negligible once the sole selected-diagonal mask loss is
negligible.  The wide-noise residual-erasure term is discharged internally. -/
theorem canonicalPostSmudgedSelectedDiagonalCorrectError_negligible
    (queryCount : ℕ → ℕ)
    (hDiagonal : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalPostSmudgedSelectedDiagonalMaskLoss securityParameter))) :
    negligible (fun securityParameter ↦ ENNReal.ofReal
      ((canonicalPostSmudgedSelectedDiagonalTransformerAt
        queryCount securityParameter).correctError
          (referenceCoordinate securityParameter))) := by
  have hsum := negligible_add
    (canonicalPostSmudgedResidualErasureCost_negligible queryCount) hDiagonal
  have heq :
      (fun securityParameter ↦ ENNReal.ofReal
        ((canonicalPostSmudgedSelectedDiagonalTransformerAt
          queryCount securityParameter).correctError
            (referenceCoordinate securityParameter))) =
      (fun securityParameter ↦
        ENNReal.ofReal
            (canonicalPostSmudgedResidualErasureCost queryCount securityParameter
              (referenceCoordinate securityParameter)) +
          ENNReal.ofReal
            (canonicalPostSmudgedSelectedDiagonalMaskLoss securityParameter)) := by
    funext securityParameter
    rw [canonicalPostSmudgedSelectedDiagonalTransformerAt_correctError]
    unfold canonicalPostSmudgedSelectedDiagonalCorrectError
    rw [ENNReal.ofReal_add
      (canonicalPostSmudgedResidualErasureCost_nonneg queryCount securityParameter
        (referenceCoordinate securityParameter))
      (canonicalPostSmudgedSelectedDiagonalMaskLoss_nonneg securityParameter)]
  rw [heq]
  exact hsum

/-- Retained-fiber route to the exact selected-diagonal mask premise.  It is enough to prove
negligibility separately for the equal- and distinct-difference square-root slices. -/
theorem canonicalPostSmudgedSelectedDiagonalMaskLoss_negligible_of_self_and_distinct
    (hSelf : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalPostSmudgedSelectedDiagonalSelfMaskLoss securityParameter)))
    (hDistinct : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalPostSmudgedSelectedDiagonalDistinctMaskLoss securityParameter))) :
    negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalPostSmudgedSelectedDiagonalMaskLoss securityParameter)) := by
  apply negligible_of_le _ (negligible_add hSelf hDistinct)
  intro securityParameter
  calc
    ENNReal.ofReal
        (canonicalPostSmudgedSelectedDiagonalMaskLoss securityParameter) ≤
      ENNReal.ofReal
        (canonicalPostSmudgedSelectedDiagonalSelfMaskLoss securityParameter +
          canonicalPostSmudgedSelectedDiagonalDistinctMaskLoss securityParameter) :=
      ENNReal.ofReal_le_ofReal
        (canonicalPostSmudgedSelectedDiagonalMaskLoss_le_self_add_distinct
          securityParameter)
    _ = ENNReal.ofReal
          (canonicalPostSmudgedSelectedDiagonalSelfMaskLoss securityParameter) +
        ENNReal.ofReal
          (canonicalPostSmudgedSelectedDiagonalDistinctMaskLoss securityParameter) := by
      rw [ENNReal.ofReal_add
        (canonicalPostSmudgedSelectedDiagonalSelfMaskLoss_nonneg securityParameter)
        (canonicalPostSmudgedSelectedDiagonalDistinctMaskLoss_nonneg securityParameter)]

/-- Negligibility of the challenge-normalized certificate loss discharges the exact canonical
self-slice premise. -/
theorem CanonicalSelectedDiagonalSelfFiberAverageCertificate.selfMaskLoss_negligible
    (certificate : CanonicalSelectedDiagonalSelfFiberAverageCertificate)
    (hLoss : negligible (fun securityParameter ↦ ENNReal.ofReal
      (certificate.lossBound securityParameter))) :
    negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalPostSmudgedSelectedDiagonalSelfMaskLoss securityParameter)) := by
  apply negligible_of_le _ hLoss
  intro securityParameter
  exact ENNReal.ofReal_le_ofReal (certificate.selfMaskLoss_le securityParameter)

/-- Negligibility of the distinct certificate loss discharges the exact distinct-slice premise. -/
theorem CanonicalSelectedDiagonalDistinctFiberAverageCertificate.distinctMaskLoss_negligible
    (certificate : CanonicalSelectedDiagonalDistinctFiberAverageCertificate)
    (hLoss : negligible (fun securityParameter ↦ ENNReal.ofReal
      (certificate.lossBound securityParameter))) :
    negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalPostSmudgedSelectedDiagonalDistinctMaskLoss securityParameter)) := by
  apply negligible_of_le _ hLoss
  intro securityParameter
  exact ENNReal.ofReal_le_ofReal (certificate.distinctMaskLoss_le securityParameter)

/-- Negligibility of the exact character factorial-moment loss discharges the canonical
distinct selected-diagonal slice. -/
theorem CanonicalSelectedDiagonalDistinctCharacterMomentCertificate.distinctMaskLoss_negligible
    (certificate : CanonicalSelectedDiagonalDistinctCharacterMomentCertificate)
    (hLoss : negligible (fun securityParameter ↦ ENNReal.ofReal
      (certificate.lossBound securityParameter))) :
    negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalPostSmudgedSelectedDiagonalDistinctMaskLoss securityParameter)) := by
  apply negligible_of_le _ hLoss
  intro securityParameter
  exact ENNReal.ofReal_le_ofReal (certificate.distinctMaskLoss_le securityParameter)

/-- Separate negligible self and distinct certificate losses give a negligible combined
certificate loss. -/
theorem CanonicalSelectedDiagonalRetainedFiberAverageCertificate.lossBound_negligible
    (certificate : CanonicalSelectedDiagonalRetainedFiberAverageCertificate)
    (hSelf : negligible (fun securityParameter ↦ ENNReal.ofReal
      (certificate.self.lossBound securityParameter)))
    (hDistinct : negligible (fun securityParameter ↦ ENNReal.ofReal
      (certificate.distinct.lossBound securityParameter))) :
    negligible (fun securityParameter ↦ ENNReal.ofReal
      (certificate.lossBound securityParameter)) := by
  have hsum := negligible_add hSelf hDistinct
  have heq :
      (fun securityParameter ↦ ENNReal.ofReal
        (certificate.lossBound securityParameter)) =
      (fun securityParameter ↦
        ENNReal.ofReal (certificate.self.lossBound securityParameter) +
          ENNReal.ofReal (certificate.distinct.lossBound securityParameter)) := by
    funext securityParameter
    unfold CanonicalSelectedDiagonalRetainedFiberAverageCertificate.lossBound
    rw [ENNReal.ofReal_add
      (certificate.self.lossBound_nonneg securityParameter)
      (certificate.distinct.lossBound_nonneg securityParameter)]
  rw [heq]
  exact hsum

/-- A negligible complete retained-fiber certificate loss discharges the exact selected-diagonal
mask premise. -/
theorem CanonicalSelectedDiagonalRetainedFiberAverageCertificate.maskLoss_negligible
    (certificate : CanonicalSelectedDiagonalRetainedFiberAverageCertificate)
    (hLoss : negligible (fun securityParameter ↦ ENNReal.ofReal
      (certificate.lossBound securityParameter))) :
    negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalPostSmudgedSelectedDiagonalMaskLoss securityParameter)) := by
  apply negligible_of_le _ hLoss
  intro securityParameter
  exact ENNReal.ofReal_le_ofReal (certificate.maskLoss_le securityParameter)

/-- Concrete finite-certificate route to the exact selected-diagonal mask premise.  Only the
distinct-difference slice remains as a direct statistical assumption. -/
theorem canonicalPostSmudgedSelectedDiagonalMaskLoss_negligible_of_selfFiberAverage_and_distinct
    (certificate : CanonicalSelectedDiagonalSelfFiberAverageCertificate)
    (hSelfFiberAverage : negligible (fun securityParameter ↦ ENNReal.ofReal
      (certificate.lossBound securityParameter)))
    (hDistinct : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalPostSmudgedSelectedDiagonalDistinctMaskLoss securityParameter))) :
    negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalPostSmudgedSelectedDiagonalMaskLoss securityParameter)) :=
  canonicalPostSmudgedSelectedDiagonalMaskLoss_negligible_of_self_and_distinct
    (certificate.selfMaskLoss_negligible hSelfFiberAverage) hDistinct

/-- The retained-fiber slice premises also discharge the full selected correct-view error;
wide-noise residual erasure remains internal to the canonical transformer. -/
theorem canonicalPostSmudgedSelectedDiagonalCorrectError_negligible_of_self_and_distinct
    (queryCount : ℕ → ℕ)
    (hSelf : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalPostSmudgedSelectedDiagonalSelfMaskLoss securityParameter)))
    (hDistinct : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalPostSmudgedSelectedDiagonalDistinctMaskLoss securityParameter))) :
    negligible (fun securityParameter ↦ ENNReal.ofReal
      ((canonicalPostSmudgedSelectedDiagonalTransformerAt
        queryCount securityParameter).correctError
          (referenceCoordinate securityParameter))) :=
  canonicalPostSmudgedSelectedDiagonalCorrectError_negligible queryCount
    (canonicalPostSmudgedSelectedDiagonalMaskLoss_negligible_of_self_and_distinct
      hSelf hDistinct)

/-- Correct-view consequence of a finite self-fiber certificate and a negligible distinct
slice. -/
theorem canonicalPostSmudgedSelectedDiagonalCorrectError_negligible_of_selfFiberAverage_and_distinct
    (queryCount : ℕ → ℕ)
    (certificate : CanonicalSelectedDiagonalSelfFiberAverageCertificate)
    (hSelfFiberAverage : negligible (fun securityParameter ↦ ENNReal.ofReal
      (certificate.lossBound securityParameter)))
    (hDistinct : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalPostSmudgedSelectedDiagonalDistinctMaskLoss securityParameter))) :
    negligible (fun securityParameter ↦ ENNReal.ofReal
      ((canonicalPostSmudgedSelectedDiagonalTransformerAt
        queryCount securityParameter).correctError
          (referenceCoordinate securityParameter))) :=
  canonicalPostSmudgedSelectedDiagonalCorrectError_negligible queryCount
    (canonicalPostSmudgedSelectedDiagonalMaskLoss_negligible_of_selfFiberAverage_and_distinct
      certificate hSelfFiberAverage hDistinct)

/-- Correct-view consequence of the complete finite retained-fiber certificate. -/
theorem canonicalPostSmudgedSelectedDiagonalCorrectError_negligible_of_retainedFiberAverage
    (queryCount : ℕ → ℕ)
    (certificate : CanonicalSelectedDiagonalRetainedFiberAverageCertificate)
    (hLoss : negligible (fun securityParameter ↦ ENNReal.ofReal
      (certificate.lossBound securityParameter))) :
    negligible (fun securityParameter ↦ ENNReal.ofReal
      ((canonicalPostSmudgedSelectedDiagonalTransformerAt
        queryCount securityParameter).correctError
          (referenceCoordinate securityParameter))) :=
  canonicalPostSmudgedSelectedDiagonalCorrectError_negligible queryCount
    (certificate.maskLoss_negligible hLoss)

/-- Logically valid compatibility implication from the explicit global pair-collision bound to
the exact selected-diagonal mask loss.  For the canonical family its premise is refuted by
`canonicalPostSmudgedSelectedDiagonalPairCollisionBound_not_negligible`; use the exact retained-
fiber mask-loss endpoint instead. -/
theorem canonicalPostSmudgedSelectedDiagonalMaskLoss_negligible_of_pairCollisionBound
    (hPairCollision : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalPostSmudgedSelectedDiagonalPairCollisionBound securityParameter))) :
    negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalPostSmudgedSelectedDiagonalMaskLoss securityParameter)) := by
  apply negligible_of_le _ hPairCollision
  intro securityParameter
  exact ENNReal.ofReal_le_ofReal
    (canonicalPostSmudgedSelectedDiagonalMaskLoss_le_pairCollisionBound
      securityParameter)

/-- Pair-collision form of the selected correct-view negligibility theorem. -/
theorem canonicalPostSmudgedSelectedDiagonalCorrectError_negligible_of_pairCollisionBound
    (queryCount : ℕ → ℕ)
    (hPairCollision : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalPostSmudgedSelectedDiagonalPairCollisionBound securityParameter))) :
    negligible (fun securityParameter ↦ ENNReal.ofReal
      ((canonicalPostSmudgedSelectedDiagonalTransformerAt
        queryCount securityParameter).correctError
          (referenceCoordinate securityParameter))) :=
  canonicalPostSmudgedSelectedDiagonalCorrectError_negligible queryCount
    (canonicalPostSmudgedSelectedDiagonalMaskLoss_negligible_of_pairCollisionBound
      hPairCollision)

/-- The selected correct-view error of a residual-free static-mask certificate is negligible as
soon as the square-root collision excess is negligible.  Gaussian residual erasure is discharged
internally. -/
theorem CanonicalPostSmudgedStaticMaskCollisionCertificate.selectedCorrectError_negligible
    (certificate : CanonicalPostSmudgedStaticMaskCollisionCertificate)
    (queryCount : ℕ → ℕ)
    (hcollision : negligible (fun securityParameter ↦ ENNReal.ofReal
      (Real.sqrt (certificate.ε queryCount securityParameter
        (referenceCoordinate securityParameter)) / 2))) :
    negligible (fun securityParameter ↦ ENNReal.ofReal
      ((certificate.transformerAt queryCount securityParameter).correctError
        (referenceCoordinate securityParameter))) := by
  have hsum := negligible_add
    (canonicalPostSmudgedResidualErasureCost_negligible queryCount) hcollision
  have heq :
      (fun securityParameter ↦ ENNReal.ofReal
        ((certificate.transformerAt queryCount securityParameter).correctError
          (referenceCoordinate securityParameter))) =
      (fun securityParameter ↦
        ENNReal.ofReal
            (canonicalPostSmudgedResidualErasureCost queryCount securityParameter
              (referenceCoordinate securityParameter)) +
          ENNReal.ofReal
            (Real.sqrt (certificate.ε queryCount securityParameter
              (referenceCoordinate securityParameter)) / 2)) := by
    funext securityParameter
    rw [certificate.transformerAt_correctError]
    unfold CanonicalPostSmudgedStaticMaskCollisionCertificate.correctError
    rw [ENNReal.ofReal_add
      (canonicalPostSmudgedResidualErasureCost_nonneg queryCount securityParameter
        (referenceCoordinate securityParameter)) (by positivity)]
  rw [heq]
  exact hsum

/-! ## Security-only adaptive composition -/

/-- Install the direct native certificates into the one-shot candidate transformer. -/
noncomputable def oneShotTransformer
    (certificate : ScalarCertificateFamily)
    (native : CoupledDirectCertificateFamily certificate) :
    Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.TransformerFamily
      (parameters certificate) errorWidth errorWidth where
  transformerAt queryCount securityParameter :=
    (native.directAt queryCount securityParameter).toAveraged

/-- Install an arbitrary family of direct native certificates into the one-shot transformer.
This interface is used by the diagonal/off-diagonal compiler, whose correct loss is already a
direct distance to the canonical Gaussian target. -/
noncomputable def oneShotTransformerOfDirectCertificates
    (certificate : ScalarCertificateFamily)
    (direct : DirectCertificateFamily certificate) :
    Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.TransformerFamily
      (parameters certificate) errorWidth errorWidth where
  transformerAt queryCount securityParameter :=
    (direct queryCount securityParameter).toAveraged

/-- Public augmented circular distinguishers for the Gaussian-target family. -/
abbrev PublicDistinguisherFamily (certificate : ScalarCertificateFamily) :=
  Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.PublicDistinguisherFamily
    (parameters certificate)

/-- Selected-coordinate predictors induced by public circular distinguishers. -/
abbrev CoordinatePredictorFamily (certificate : ScalarCertificateFamily) :=
  Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.CoordinatePredictorFamily
    (parameters certificate)

/-- Positive signed bias for predicting the canonical scalar coordinate. -/
noncomputable abbrev coordinatePredictionSecurityGame
    (certificate : ScalarCertificateFamily) :=
  Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.coordinatePredictionSecurityGame
    (parameters certificate) errorWidth errorWidth

/-- Correct plus freshness loss of the executable one-shot native evaluator. -/
noncomputable abbrev statisticalErrorSecurityGame
    (certificate : ScalarCertificateFamily)
    (native : CoupledDirectCertificateFamily certificate) :=
  Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.statisticalErrorSecurityGame
    (parameters certificate) errorWidth errorWidth
    (oneShotTransformer certificate native) referenceCoordinate

/-- Selected-coordinate correct plus freshness loss for arbitrary direct certificates. -/
noncomputable abbrev directStatisticalErrorSecurityGame
    (certificate : ScalarCertificateFamily)
    (direct : DirectCertificateFamily certificate) :=
  Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.statisticalErrorSecurityGame
    (parameters certificate) errorWidth errorWidth
    (oneShotTransformerOfDirectCertificates certificate direct) referenceCoordinate

/-- Exact pointwise adaptive TFHE reduction for the Gaussian-target family. -/
theorem securityGame_advantage_le_coordinatePrediction_add_statisticalError_add_three_jointLWE
    (certificate : ScalarCertificateFamily)
    (native : CoupledDirectCertificateFamily certificate)
    (adversary : PolynomialQueryAdversary (parameters certificate))
    (securityParameter : ℕ) :
    (securityGame (parameters certificate)).advantage adversary securityParameter ≤
      ((coordinatePredictionSecurityGame certificate).advantage
          (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
            (parameters certificate) errorWidth errorWidth
            (oneShotTransformer certificate native) referenceCoordinate
            (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
              (parameters certificate) adversary)) securityParameter +
        (statisticalErrorSecurityGame certificate native).advantage
          (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
            (parameters certificate) adversary) securityParameter) +
        (jointLWESecurityGame (parameters certificate)).advantage
          (jointLWEReduction (parameters certificate) adversary) securityParameter +
        (jointLWESecurityGame (parameters certificate)).advantage
          (jointLWEReduction (parameters certificate) adversary) securityParameter +
        (jointLWESecurityGame (parameters certificate)).advantage
          (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
            (parameters certificate) adversary) securityParameter := by
  let distinguisher :=
    Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
      (parameters certificate) adversary
  have hTFHE :=
    Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.securityGame_advantage_le_publicCircular_add_three_jointLWE
      (parameters certificate) adversary securityParameter
  have hCircular :=
    Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.publicCircularLWE_advantage_le_coordinatePrediction_add_error
      (parameters certificate) errorWidth errorWidth
      (oneShotTransformer certificate native) referenceCoordinate distinguisher
      securityParameter
  change (securityGame (parameters certificate)).advantage adversary securityParameter ≤
    ((Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicCircularLWESecurityGame
        (parameters certificate)).advantage distinguisher securityParameter +
      (jointLWESecurityGame (parameters certificate)).advantage
        (jointLWEReduction (parameters certificate) adversary) securityParameter +
      (jointLWESecurityGame (parameters certificate)).advantage
        (jointLWEReduction (parameters certificate) adversary) securityParameter) +
      (jointLWESecurityGame (parameters certificate)).advantage
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters certificate) adversary) securityParameter at hTFHE
  calc
    _ ≤ ((Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicCircularLWESecurityGame
            (parameters certificate)).advantage distinguisher securityParameter +
          (jointLWESecurityGame (parameters certificate)).advantage
            (jointLWEReduction (parameters certificate) adversary) securityParameter +
          (jointLWESecurityGame (parameters certificate)).advantage
            (jointLWEReduction (parameters certificate) adversary) securityParameter) +
        (jointLWESecurityGame (parameters certificate)).advantage
          (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
            (parameters certificate) adversary) securityParameter := hTFHE
    _ ≤ _ := by
      exact add_le_add
        (add_le_add (add_le_add hCircular le_rfl) le_rfl) le_rfl

/-- Security-only adaptive TFHE from any one-shot native transformer whose selected-coordinate
correct and wrong statistical losses are negligible.  This is the composition boundary shared by
the direct-certificate and explicit post-evaluation-smudging routes. -/
theorem secureAgainst_of_transformer_coordinatePrediction_and_jointLWE
    (certificate : ScalarCertificateFamily)
    (transformer :
      Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.TransformerFamily
        (parameters certificate) errorWidth errorWidth)
    (isPPT : PolynomialQueryAdversary (parameters certificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily certificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily certificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters certificate) → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters certificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters certificate) errorWidth errorWidth transformer referenceCoordinate
          distinguisher))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT (jointLWEReduction (parameters certificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters certificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame certificate).secureAgainst predictorIsPPT)
    (hCorrect : ∀ distinguisher, publicIsPPT distinguisher →
      negligible (fun securityParameter ↦ ENNReal.ofReal
        ((transformer.transformerAt distinguisher.queryCount securityParameter).correctError
          (referenceCoordinate securityParameter))))
    (hWrong : ∀ distinguisher, publicIsPPT distinguisher →
      negligible (fun securityParameter ↦ ENNReal.ofReal
        ((transformer.transformerAt distinguisher.queryCount securityParameter).wrongError
          (referenceCoordinate securityParameter))))
    (hJointLWE :
      (jointLWESecurityGame (parameters certificate)).secureAgainst jointLWEIsPPT) :
    (securityGame (parameters certificate)).secureAgainst isPPT := by
  have hStatisticalError :
      (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.statisticalErrorSecurityGame
        (parameters certificate) errorWidth errorWidth transformer referenceCoordinate).secureAgainst
          publicIsPPT := by
    apply Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.statisticalErrorSecurityGame_secureAgainst_of_components
      (parameters certificate) errorWidth errorWidth transformer referenceCoordinate publicIsPPT
    · exact hCorrect
    · exact hWrong
  have hCircular :
      (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicCircularLWESecurityGame
        (parameters certificate)).secureAgainst publicIsPPT :=
    Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.publicCircularLWESecurityGame_secureAgainst_of_coordinatePrediction_and_error
      (parameters certificate) errorWidth errorWidth transformer referenceCoordinate
      publicIsPPT predictorIsPPT hPredictorClosed hPrediction hStatisticalError
  exact
    Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.secureAgainst_of_publicCircular_and_jointLWE
      (parameters certificate) isPPT publicIsPPT jointLWEIsPPT hPublicClosed
      hJointLWEClosed hUniformJointLWEClosed hCircular hJointLWE

/-- **Security-only adaptive TFHE via explicit post-evaluation smudging.**

The executable candidate evaluator first computes the native shifted view and then adds fresh
wide noise to every BRK body.  Consequently the correct-view premise is a comparison with the
post-smudged residual normal form, rather than an impossible direct comparison between a narrow
residual and a wide Gaussian.  Exact uniform-BRK invariance leaves only the single generated-control
non-bijectivity probability on the wrong side.  Together with circular coordinate prediction and
ordinary joint LWE these assumptions imply adaptive confidentiality; no correctness proposition is
used. -/
theorem secureAgainst_of_postEvaluationSmudging_normalForm_coordinatePrediction_controlFailure_and_jointLWE
    (laws : CanonicalPostSmudgedNormalFormLaws)
    (isPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          laws.toOneShotTransformer referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hNormalForm : ∀ distinguisher, publicIsPPT distinguisher →
      negligible (fun securityParameter ↦ ENNReal.ofReal
        (laws.normalFormError distinguisher.queryCount securityParameter
          (referenceCoordinate securityParameter))))
    (hControlFailure : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalWrongViewNonbijectivityError securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (securityGame (parameters canonicalCertificate)).secureAgainst isPPT := by
  apply secureAgainst_of_transformer_coordinatePrediction_and_jointLWE
    canonicalCertificate laws.toOneShotTransformer isPPT publicIsPPT predictorIsPPT
    jointLWEIsPPT hPublicClosed hPredictorClosed hJointLWEClosed hUniformJointLWEClosed
    hPrediction
  · intro distinguisher hdistinguisher
    simpa only [CanonicalPostSmudgedNormalFormLaws.toOneShotTransformer] using
      laws.selectedCorrectError_negligible distinguisher.queryCount
        (hNormalForm distinguisher hdistinguisher)
  · intro _distinguisher _hdistinguisher
    simpa only [CanonicalPostSmudgedNormalFormLaws.toOneShotTransformer,
      CanonicalPostSmudgedNormalFormLaws.transformerAt_wrongError] using hControlFailure
  · exact hJointLWE

/-- **Canonical mask-normal-form TFHE security endpoint.**

This specialization removes the abstract post-smudged law object.  Its sole correct-view premise
is negligibility of the exact finite distance between the native evaluator and the zero-error
fresh-mask residual view.  The executable wide Gaussian, its compilation loss, and its placement
after evaluation are all discharged internally. -/
theorem secureAgainst_of_canonicalPostSmudgedMaskLoss_coordinatePrediction_controlFailure_and_jointLWE
    (isPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          canonicalPostSmudgedMaskNormalFormLaws.toOneShotTransformer
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hMaskNormalForm : ∀ distinguisher, publicIsPPT distinguisher →
      negligible (fun securityParameter ↦ ENNReal.ofReal
        (canonicalPostSmudgedMaskNormalFormError distinguisher.queryCount
          securityParameter (referenceCoordinate securityParameter))))
    (hControlFailure : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalWrongViewNonbijectivityError securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (securityGame (parameters canonicalCertificate)).secureAgainst isPPT :=
  secureAgainst_of_postEvaluationSmudging_normalForm_coordinatePrediction_controlFailure_and_jointLWE
    canonicalPostSmudgedMaskNormalFormLaws isPPT publicIsPPT predictorIsPPT
    jointLWEIsPPT hPublicClosed hPredictorClosed hJointLWEClosed
    hUniformJointLWEClosed hPrediction hMaskNormalForm hControlFailure hJointLWE

/-- **Canonical full-mask-collision TFHE security endpoint.**

The correct-view hypothesis is now negligibility of an explicit finite side-wise `L²` expression
for the complete BRK mask.  The retained side contains the complete residual and correlated
auxiliary view, so no diagonal or off-diagonal correlation is silently discarded.  Circular
coordinate prediction, generated-control failure, and ordinary joint LWE remain the genuinely
cryptographic assumptions; correctness is absent. -/
theorem secureAgainst_of_canonicalPostSmudgedMaskCollision_coordinatePrediction_controlFailure_and_jointLWE
    (isPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          canonicalPostSmudgedMaskCollisionNormalFormLaws.toOneShotTransformer
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hMaskCollision : ∀ distinguisher, publicIsPPT distinguisher →
      negligible (fun securityParameter ↦ ENNReal.ofReal
        (canonicalPostSmudgedMaskCollisionLoss distinguisher.queryCount
          securityParameter (referenceCoordinate securityParameter))))
    (hControlFailure : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalWrongViewNonbijectivityError securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (securityGame (parameters canonicalCertificate)).secureAgainst isPPT :=
  secureAgainst_of_postEvaluationSmudging_normalForm_coordinatePrediction_controlFailure_and_jointLWE
    canonicalPostSmudgedMaskCollisionNormalFormLaws isPPT publicIsPPT predictorIsPPT
    jointLWEIsPPT hPublicClosed hPredictorClosed hJointLWEClosed
    hUniformJointLWEClosed hPrediction hMaskCollision hControlFailure hJointLWE

/-- **Canonical conditional pair-collision TFHE security endpoint.**

This version removes even the full-mask `L²` premise.  A caller supplies the explicit
side-fiber pair-collision inequality for the complete evaluated BRK mask and proves only that its
square-root excess is negligible. -/
theorem secureAgainst_of_canonicalPostSmudgedMaskPairCollision_coordinatePrediction_controlFailure_and_jointLWE
    (certificate : CanonicalPostSmudgedMaskCollisionCertificate)
    (isPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          certificate.normalFormLaws.toOneShotTransformer
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hCollisionError : ∀ distinguisher, publicIsPPT distinguisher →
      negligible (fun securityParameter ↦ ENNReal.ofReal
        (Real.sqrt
          (certificate.ε distinguisher.queryCount securityParameter
            (referenceCoordinate securityParameter)) / 2)))
    (hControlFailure : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalWrongViewNonbijectivityError securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (securityGame (parameters canonicalCertificate)).secureAgainst isPPT :=
  secureAgainst_of_postEvaluationSmudging_normalForm_coordinatePrediction_controlFailure_and_jointLWE
    certificate.normalFormLaws isPPT publicIsPPT predictorIsPPT jointLWEIsPPT
    hPublicClosed hPredictorClosed hJointLWEClosed hUniformJointLWEClosed
    hPrediction hCollisionError hControlFailure hJointLWE

/-- **Preferred residual-first conditional-collision TFHE security endpoint.**

The mask-collision side information omits the evaluator's complete narrow residual.  That
residual is first erased after adding the certified wide discrete Gaussian, whose negligible
translation loss is proved internally.  The remaining assumptions are the residual-free mask
collision excess, circular coordinate prediction, generated-control failure, and ordinary joint
LWE; no correctness premise is used. -/
theorem secureAgainst_of_canonicalPostSmudgedStaticMaskPairCollision_coordinatePrediction_controlFailure_and_jointLWE
    (certificate : CanonicalPostSmudgedStaticMaskCollisionCertificate)
    (isPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          certificate.toOneShotTransformer referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hCollisionError : ∀ distinguisher, publicIsPPT distinguisher →
      negligible (fun securityParameter ↦ ENNReal.ofReal
        (Real.sqrt
          (certificate.ε distinguisher.queryCount securityParameter
            (referenceCoordinate securityParameter)) / 2)))
    (hControlFailure : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalWrongViewNonbijectivityError securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (securityGame (parameters canonicalCertificate)).secureAgainst isPPT := by
  apply secureAgainst_of_transformer_coordinatePrediction_and_jointLWE
    canonicalCertificate certificate.toOneShotTransformer isPPT publicIsPPT
    predictorIsPPT jointLWEIsPPT hPublicClosed hPredictorClosed hJointLWEClosed
    hUniformJointLWEClosed hPrediction
  · intro distinguisher hdistinguisher
    simpa only [CanonicalPostSmudgedStaticMaskCollisionCertificate.toOneShotTransformer] using
      certificate.selectedCorrectError_negligible distinguisher.queryCount
        (hCollisionError distinguisher hdistinguisher)
  · intro _distinguisher _hdistinguisher
    simpa only [CanonicalPostSmudgedStaticMaskCollisionCertificate.toOneShotTransformer,
      CanonicalPostSmudgedStaticMaskCollisionCertificate.transformerAt_wrongError] using
      hControlFailure
  · exact hJointLWE

/-- **Distribution-weighted retained-cokernel TFHE security endpoint.**

The finite self/cokernel estimates are imposed only on a high-probability set of native
centered-binomial source errors.  The complementary event is charged by its exact probability in
the real TFHE game.  This is strictly more faithful than the support-wise selected-diagonal
endpoint; circular coordinate prediction and ordinary joint LWE remain explicit computational
premises. -/
theorem secureAgainst_of_canonicalPostSmudgedGoodBadRetainedCokernel_coordinatePrediction_controlFailure_and_jointLWE
    (certificate : CanonicalSelectedDiagonalGoodBadCokernelCertificate)
    (isPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          certificate.toOneShotTransformer referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hMask : negligible (fun securityParameter ↦ ENNReal.ofReal
      (certificate.maskLoss securityParameter)))
    (hControlFailure : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalWrongViewNonbijectivityError securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (securityGame (parameters canonicalCertificate)).secureAgainst isPPT := by
  apply secureAgainst_of_transformer_coordinatePrediction_and_jointLWE
    canonicalCertificate certificate.toOneShotTransformer isPPT publicIsPPT
    predictorIsPPT jointLWEIsPPT hPublicClosed hPredictorClosed hJointLWEClosed
    hUniformJointLWEClosed hPrediction
  · intro distinguisher _hdistinguisher
    simpa only [CanonicalSelectedDiagonalGoodBadCokernelCertificate.toOneShotTransformer] using
      certificate.correctError_negligible distinguisher.queryCount hMask
  · intro _distinguisher _hdistinguisher
    simpa only [CanonicalSelectedDiagonalGoodBadCokernelCertificate.toOneShotTransformer,
      CanonicalSelectedDiagonalGoodBadCokernelCertificate.transformerAt_wrongError] using
      hControlFailure
  · exact hJointLWE

/-- **Canonical nonzero-parity retained-cokernel TFHE security endpoint.**

The exceptional all-nonunit centered-binomial source-error event has already been proved
negligible.  The only remaining selected-diagonal statistical premise is negligibility of the
exact retained self/cokernel loss on source errors containing a unit. -/
theorem secureAgainst_of_canonicalPostSmudgedNonzeroParityRetainedCokernel_coordinatePrediction_controlFailure_and_jointLWE
    (certificate : CanonicalSelectedDiagonalNonzeroParityCokernelCertificate)
    (isPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          certificate.toGoodBad.toOneShotTransformer referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hGoodCokernel : negligible (fun securityParameter ↦ ENNReal.ofReal
      (certificate.goodLoss securityParameter)))
    (hControlFailure : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalWrongViewNonbijectivityError securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (securityGame (parameters canonicalCertificate)).secureAgainst isPPT :=
  secureAgainst_of_canonicalPostSmudgedGoodBadRetainedCokernel_coordinatePrediction_controlFailure_and_jointLWE
    certificate.toGoodBad isPPT publicIsPPT predictorIsPPT jointLWEIsPPT
    hPublicClosed hPredictorClosed hJointLWEClosed hUniformJointLWEClosed hPrediction
    (certificate.maskLoss_negligible hGoodCokernel) hControlFailure hJointLWE

/-- **Phase-aware rank-one Fourier TFHE security endpoint.**

Exact outer-character orthogonality has removed the structured source-error Fourier spike from
the selected-diagonal statistical obligation.  The good-event premise is therefore the explicit
phase-aware moment containing only the non-source second-dual square mass.  Circular coordinate
prediction and ordinary joint LWE remain explicit computational premises. -/
theorem secureAgainst_of_canonicalPostSmudgedNonzeroParityPhaseAwareFourier_coordinatePrediction_controlFailure_and_jointLWE
    (certificate : CanonicalSelectedDiagonalNonzeroParityPhaseAwareFourierCertificate)
    (isPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          certificate.toGoodBad.toOneShotTransformer referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hGoodPhaseAware : negligible (fun securityParameter ↦ ENNReal.ofReal
      (certificate.goodLoss securityParameter)))
    (hControlFailure : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalWrongViewNonbijectivityError securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (securityGame (parameters canonicalCertificate)).secureAgainst isPPT :=
  secureAgainst_of_canonicalPostSmudgedGoodBadRetainedCokernel_coordinatePrediction_controlFailure_and_jointLWE
    certificate.toGoodBad isPPT publicIsPPT predictorIsPPT jointLWEIsPPT
    hPublicClosed hPredictorClosed hJointLWEClosed hUniformJointLWEClosed hPrediction
    (certificate.maskLoss_negligible hGoodPhaseAware) hControlFailure hJointLWE

/-- **Selected-diagonal TFHE security endpoint.**

After wide-noise residual erasure, every off-diagonal evaluated BRK mask is eliminated exactly
as an additive one-time pad.  Thus the complete correct-view assumption is only negligibility of
the selected-diagonal joint chi-square loss.  Circular coordinate prediction, generated-control
failure, and joint LWE remain explicit computational assumptions; no correctness premise occurs. -/
theorem secureAgainst_of_canonicalPostSmudgedSelectedDiagonal_coordinatePrediction_controlFailure_and_jointLWE
    (isPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          canonicalPostSmudgedSelectedDiagonalOneShotTransformer
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hSelectedDiagonalMask : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalPostSmudgedSelectedDiagonalMaskLoss securityParameter)))
    (hControlFailure : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalWrongViewNonbijectivityError securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (securityGame (parameters canonicalCertificate)).secureAgainst isPPT := by
  apply secureAgainst_of_transformer_coordinatePrediction_and_jointLWE
    canonicalCertificate canonicalPostSmudgedSelectedDiagonalOneShotTransformer
    isPPT publicIsPPT predictorIsPPT jointLWEIsPPT hPublicClosed hPredictorClosed
    hJointLWEClosed hUniformJointLWEClosed hPrediction
  · intro distinguisher _hdistinguisher
    simpa only [canonicalPostSmudgedSelectedDiagonalOneShotTransformer] using
      canonicalPostSmudgedSelectedDiagonalCorrectError_negligible
        distinguisher.queryCount hSelectedDiagonalMask
  · intro _distinguisher _hdistinguisher
    simpa only [canonicalPostSmudgedSelectedDiagonalOneShotTransformer,
      canonicalPostSmudgedSelectedDiagonalTransformerAt_wrongError] using
      hControlFailure
  · exact hJointLWE

/-- Security-only TFHE endpoint using the exact retained-fiber collision split.  The selected
diagonal premise is reduced to separate negligibility statements for equal and distinct
difference pairs; circular coordinate prediction and ordinary joint LWE remain explicit
computational assumptions. -/
theorem secureAgainst_of_canonicalPostSmudgedSelectedDiagonalRetainedFiberSlices_coordinatePrediction_controlFailure_and_jointLWE
    (isPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          canonicalPostSmudgedSelectedDiagonalOneShotTransformer
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hSelf : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalPostSmudgedSelectedDiagonalSelfMaskLoss securityParameter)))
    (hDistinct : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalPostSmudgedSelectedDiagonalDistinctMaskLoss securityParameter)))
    (hControlFailure : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalWrongViewNonbijectivityError securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (securityGame (parameters canonicalCertificate)).secureAgainst isPPT :=
  secureAgainst_of_canonicalPostSmudgedSelectedDiagonal_coordinatePrediction_controlFailure_and_jointLWE
    isPPT publicIsPPT predictorIsPPT jointLWEIsPPT hPublicClosed hPredictorClosed
    hJointLWEClosed hUniformJointLWEClosed hPrediction
    (canonicalPostSmudgedSelectedDiagonalMaskLoss_negligible_of_self_and_distinct
      hSelf hDistinct)
    hControlFailure hJointLWE

/-- Security-only TFHE endpoint whose equal-difference statistical premise is a finite
retained-fiber average-kernel certificate.  The only direct selected-diagonal negligibility
premise left is the distinct-difference slice. -/
theorem secureAgainst_of_canonicalPostSmudgedSelectedDiagonalSelfFiberAverage_coordinatePrediction_controlFailure_and_jointLWE
    (isPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          canonicalPostSmudgedSelectedDiagonalOneShotTransformer
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (certificate : CanonicalSelectedDiagonalSelfFiberAverageCertificate)
    (hSelfFiberAverage : negligible (fun securityParameter ↦ ENNReal.ofReal
      (certificate.lossBound securityParameter)))
    (hDistinct : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalPostSmudgedSelectedDiagonalDistinctMaskLoss securityParameter)))
    (hControlFailure : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalWrongViewNonbijectivityError securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (securityGame (parameters canonicalCertificate)).secureAgainst isPPT :=
  secureAgainst_of_canonicalPostSmudgedSelectedDiagonalRetainedFiberSlices_coordinatePrediction_controlFailure_and_jointLWE
    isPPT publicIsPPT predictorIsPPT jointLWEIsPPT hPublicClosed hPredictorClosed
    hJointLWEClosed hUniformJointLWEClosed hPrediction
    (certificate.selfMaskLoss_negligible hSelfFiberAverage) hDistinct
    hControlFailure hJointLWE

/-- Security-only TFHE endpoint with the complete selected-diagonal statistical argument exposed
as two finite retained-fiber average certificates and one negligible certified loss. -/
theorem secureAgainst_of_canonicalPostSmudgedSelectedDiagonalRetainedFiberAverage_coordinatePrediction_controlFailure_and_jointLWE
    (isPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          canonicalPostSmudgedSelectedDiagonalOneShotTransformer
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (certificate : CanonicalSelectedDiagonalRetainedFiberAverageCertificate)
    (hRetainedFiber : negligible (fun securityParameter ↦ ENNReal.ofReal
      (certificate.lossBound securityParameter)))
    (hControlFailure : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalWrongViewNonbijectivityError securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (securityGame (parameters canonicalCertificate)).secureAgainst isPPT :=
  secureAgainst_of_canonicalPostSmudgedSelectedDiagonal_coordinatePrediction_controlFailure_and_jointLWE
    isPPT publicIsPPT predictorIsPPT jointLWEIsPPT hPublicClosed hPredictorClosed
    hJointLWEClosed hUniformJointLWEClosed hPrediction
    (certificate.maskLoss_negligible hRetainedFiber)
    hControlFailure hJointLWE

/-- Compatibility corollary from the source-independent global pair-collision relaxation.  Its
canonical negligibility premise is formally false, so the exact selected-diagonal security
endpoint above is the usable statistical interface. -/
theorem secureAgainst_of_canonicalPostSmudgedSelectedDiagonalPairCollision_coordinatePrediction_controlFailure_and_jointLWE
    (isPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          canonicalPostSmudgedSelectedDiagonalOneShotTransformer
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hPairCollision : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalPostSmudgedSelectedDiagonalPairCollisionBound securityParameter)))
    (hControlFailure : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalWrongViewNonbijectivityError securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (securityGame (parameters canonicalCertificate)).secureAgainst isPPT :=
  secureAgainst_of_canonicalPostSmudgedSelectedDiagonal_coordinatePrediction_controlFailure_and_jointLWE
    isPPT publicIsPPT predictorIsPPT jointLWEIsPPT hPublicClosed hPredictorClosed
    hJointLWEClosed hUniformJointLWEClosed hPrediction
    (canonicalPostSmudgedSelectedDiagonalMaskLoss_negligible_of_pairCollisionBound
      hPairCollision)
    hControlFailure hJointLWE

/-- Security-only adaptive TFHE from arbitrary direct native certificates.  This is the common
one-coordinate composition theorem used by both the coupled-smudging and explicit
diagonal/off-diagonal routes. -/
theorem secureAgainst_of_directCertificates_coordinatePrediction_and_jointLWE
    (certificate : ScalarCertificateFamily)
    (direct : DirectCertificateFamily certificate)
    (isPPT : PolynomialQueryAdversary (parameters certificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily certificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily certificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters certificate) → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters certificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters certificate) errorWidth errorWidth
          (oneShotTransformerOfDirectCertificates certificate direct)
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT (jointLWEReduction (parameters certificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters certificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame certificate).secureAgainst predictorIsPPT)
    (hCorrect : ∀ distinguisher, publicIsPPT distinguisher →
      negligible (fun securityParameter ↦ ENNReal.ofReal
        ((direct distinguisher.queryCount securityParameter).correctError
          (referenceCoordinate securityParameter))))
    (hFreshness : ∀ distinguisher, publicIsPPT distinguisher →
      negligible (fun securityParameter ↦ ENNReal.ofReal
        ((direct distinguisher.queryCount securityParameter).freshnessError
          (referenceCoordinate securityParameter))))
    (hJointLWE :
      (jointLWESecurityGame (parameters certificate)).secureAgainst jointLWEIsPPT) :
    (securityGame (parameters certificate)).secureAgainst isPPT := by
  let transformer := oneShotTransformerOfDirectCertificates certificate direct
  have hStatisticalError :
      (directStatisticalErrorSecurityGame certificate direct).secureAgainst
        publicIsPPT := by
    apply Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.statisticalErrorSecurityGame_secureAgainst_of_components
      (parameters certificate) errorWidth errorWidth transformer referenceCoordinate
      publicIsPPT
    · intro distinguisher hdistinguisher
      simpa [transformer, directStatisticalErrorSecurityGame,
        oneShotTransformerOfDirectCertificates] using
          hCorrect distinguisher hdistinguisher
    · intro distinguisher hdistinguisher
      simpa [transformer, directStatisticalErrorSecurityGame,
        oneShotTransformerOfDirectCertificates] using
          hFreshness distinguisher hdistinguisher
  have hCircular :
      (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicCircularLWESecurityGame
        (parameters certificate)).secureAgainst publicIsPPT :=
    Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.publicCircularLWESecurityGame_secureAgainst_of_coordinatePrediction_and_error
      (parameters certificate) errorWidth errorWidth transformer referenceCoordinate
      publicIsPPT predictorIsPPT hPredictorClosed hPrediction hStatisticalError
  exact
    Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.secureAgainst_of_publicCircular_and_jointLWE
      (parameters certificate) isPPT publicIsPPT jointLWEIsPPT hPublicClosed
      hJointLWEClosed hUniformJointLWEClosed hCircular hJointLWE

/-- **Security-only adaptive TFHE with the Gaussian smudging term discharged.**

Negligible native coordinate-prediction bias, negligible finite Gaussian compilation error,
negligible selected-coordinate output-normal-form and freshness errors, and ordinary joint LWE
imply adaptive confidentiality.  The exponential Gaussian window is proved internally from the
family parameters.  No correctness proposition or whole-key amplification premise occurs. -/
theorem secureAgainst_of_coordinatePrediction_normalForm_freshness_and_jointLWE
    (certificate : ScalarCertificateFamily)
    (native : CoupledDirectCertificateFamily certificate)
    (isPPT : PolynomialQueryAdversary (parameters certificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily certificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily certificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters certificate) → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters certificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters certificate) errorWidth errorWidth
          (oneShotTransformer certificate native) referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT (jointLWEReduction (parameters certificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters certificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame certificate).secureAgainst predictorIsPPT)
    (hcertificate : negligible (fun securityParameter ↦
      (certificate securityParameter).bound))
    (hNormalForm : ∀ distinguisher, publicIsPPT distinguisher →
      negligible (fun securityParameter ↦ ENNReal.ofReal
        (native.normalFormError distinguisher.queryCount securityParameter
          (referenceCoordinate securityParameter))))
    (hFreshness : ∀ distinguisher, publicIsPPT distinguisher →
      negligible (fun securityParameter ↦ ENNReal.ofReal
        ((native.directAt distinguisher.queryCount securityParameter).freshnessError
          (referenceCoordinate securityParameter))))
    (hJointLWE :
      (jointLWESecurityGame (parameters certificate)).secureAgainst jointLWEIsPPT) :
    (securityGame (parameters certificate)).secureAgainst isPPT := by
  let transformer := oneShotTransformer certificate native
  have hStatisticalError :
      (statisticalErrorSecurityGame certificate native).secureAgainst publicIsPPT := by
    apply Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.statisticalErrorSecurityGame_secureAgainst_of_components
      (parameters certificate) errorWidth errorWidth transformer referenceCoordinate
      publicIsPPT
    · intro distinguisher hdistinguisher
      simpa [transformer, statisticalErrorSecurityGame, oneShotTransformer] using
        selectedCorrectError_negligible certificate native distinguisher.queryCount
          hcertificate (hNormalForm distinguisher hdistinguisher)
    · intro distinguisher hdistinguisher
      simpa [transformer, statisticalErrorSecurityGame, oneShotTransformer] using
        hFreshness distinguisher hdistinguisher
  have hCircular :
      (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicCircularLWESecurityGame
        (parameters certificate)).secureAgainst publicIsPPT :=
    Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.publicCircularLWESecurityGame_secureAgainst_of_coordinatePrediction_and_error
      (parameters certificate) errorWidth errorWidth transformer referenceCoordinate
      publicIsPPT predictorIsPPT hPredictorClosed hPrediction hStatisticalError
  exact
    Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.secureAgainst_of_publicCircular_and_jointLWE
      (parameters certificate) isPPT publicIsPPT jointLWEIsPPT hPublicClosed
      hJointLWEClosed hUniformJointLWEClosed hCircular hJointLWE

/-- **Security-only adaptive TFHE for the canonical finite Gaussian family.**

This specialization removes the finite-Gaussian compilation hypothesis: the canonical rounded
ticket tables and their negligible error were constructed above.  The remaining assumptions are
the circular coordinate-prediction claim, native normal-form and freshness estimates, ordinary
joint LWE, and the corresponding computational closure conditions. -/
theorem secureAgainst_of_coordinatePrediction_normalForm_freshness_and_jointLWE_canonical
    (native : CoupledDirectCertificateFamily canonicalCertificate)
    (isPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          (oneShotTransformer canonicalCertificate native) referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hNormalForm : ∀ distinguisher, publicIsPPT distinguisher →
      negligible (fun securityParameter ↦ ENNReal.ofReal
        (native.normalFormError distinguisher.queryCount securityParameter
          (referenceCoordinate securityParameter))))
    (hFreshness : ∀ distinguisher, publicIsPPT distinguisher →
      negligible (fun securityParameter ↦ ENNReal.ofReal
        ((native.directAt distinguisher.queryCount securityParameter).freshnessError
          (referenceCoordinate securityParameter))))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (securityGame (parameters canonicalCertificate)).secureAgainst isPPT :=
  secureAgainst_of_coordinatePrediction_normalForm_freshness_and_jointLWE
    canonicalCertificate native isPPT publicIsPPT predictorIsPPT jointLWEIsPPT
    hPublicClosed hPredictorClosed hJointLWEClosed hUniformJointLWEClosed hPrediction
    canonicalCertificate_bound_negligible hNormalForm hFreshness hJointLWE

/-- **Canonical TFHE confidentiality from explicit native finite quantities.**

The correct side is reduced to the selected diagonal distance plus the sum of its conditionally
residualized off-diagonal distances.  The wrong side is reduced internally to the expected
message-one control fiber loss and its polynomial BRK-layout factor.  Thus neither an opaque
native freshness law, a Gaussian compilation premise, nor any correctness proposition appears. -/
theorem secureAgainst_of_explicitNativeLaws_coordinatePrediction_fiber_and_jointLWE_canonical
    (laws : CanonicalCorrectViewLaws)
    (isPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          (oneShotTransformerOfDirectCertificates canonicalCertificate
            laws.toDirectCertificateFamily)
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hCorrect : negligible (fun securityParameter ↦ ENNReal.ofReal
      (laws.selectedCorrectError securityParameter)))
    (hFiber : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalWrongViewFiberLoss securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (securityGame (parameters canonicalCertificate)).secureAgainst isPPT := by
  apply secureAgainst_of_directCertificates_coordinatePrediction_and_jointLWE
    canonicalCertificate laws.toDirectCertificateFamily isPPT publicIsPPT
    predictorIsPPT jointLWEIsPPT hPublicClosed hPredictorClosed hJointLWEClosed
    hUniformJointLWEClosed hPrediction
  · intro _distinguisher _hdistinguisher
    simpa using hCorrect
  · intro _distinguisher _hdistinguisher
    simpa using canonicalWrongViewFreshnessError_negligible hFiber
  · exact hJointLWE

/-- **Support-wise canonical security-only endpoint with the diagonal law discharged.**

The selected diagonal is reduced internally to the sharp challenge-fiber plus mixed-error
quantity.  Callers supply only negligible bounds for that explicit quantity, the selected sum of
off-diagonal residual distances, and the message-one wrong-control fiber loss, together with the
coordinate-prediction and ordinary joint-LWE security premises. -/
theorem secureAgainst_of_sharpDiagonal_offDiagonal_fiber_and_jointLWE_canonical
    (laws : CanonicalOffDiagonalLaws)
    (isPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          (oneShotTransformerOfDirectCertificates canonicalCertificate
            laws.toCanonicalCorrectViewLaws.toDirectCertificateFamily)
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hDiagonal : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalSharpDiagonalError securityParameter)))
    (hOffDiagonal : negligible (fun securityParameter ↦ ENNReal.ofReal
      (laws.selectedOffDiagonalError securityParameter)))
    (hFiber : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalWrongViewFiberLoss securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (securityGame (parameters canonicalCertificate)).secureAgainst isPPT := by
  apply
    secureAgainst_of_explicitNativeLaws_coordinatePrediction_fiber_and_jointLWE_canonical
      laws.toCanonicalCorrectViewLaws isPPT publicIsPPT predictorIsPPT jointLWEIsPPT
      hPublicClosed hPredictorClosed hJointLWEClosed hUniformJointLWEClosed hPrediction
  · have hsum : negligible (fun securityParameter ↦
        ENNReal.ofReal (canonicalSharpDiagonalError securityParameter) +
          ENNReal.ofReal (laws.selectedOffDiagonalError securityParameter)) :=
      negligible_add hDiagonal hOffDiagonal
    simpa only [CanonicalOffDiagonalLaws.toCanonicalCorrectViewLaws_selectedCorrectError,
      ENNReal.ofReal_add (canonicalSharpDiagonalError_nonneg _)
        (laws.selectedOffDiagonalError_nonneg _)] using hsum
  · exact hFiber
  · exact hJointLWE

/-- **Support-wise finite-operator compatibility endpoint.**

The correct branch is represented by two exact finite operator quantities: the checked sharp
diagonal loss and the selected sum of worst-case conditional off-diagonal distances.  The wrong
branch is represented by the exact message-one control fiber loss.  Callers prove negligibility
of those three canonical quantities, but no longer construct diagonal, off-diagonal, freshness,
or Gaussian-table laws.  This bound can be much stronger than the generated-control average used
by the preferred endpoint below. -/
theorem secureAgainst_of_canonicalOperatorLosses_coordinatePrediction_fiber_and_jointLWE
    (isPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          (oneShotTransformerOfDirectCertificates canonicalCertificate
            canonicalOffDiagonalOperatorLaws.toCanonicalCorrectViewLaws.toDirectCertificateFamily)
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hDiagonal : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalSharpDiagonalError securityParameter)))
    (hOffDiagonal : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalSelectedOffDiagonalOperatorError securityParameter)))
    (hFiber : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalWrongViewFiberLoss securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (securityGame (parameters canonicalCertificate)).secureAgainst isPPT := by
  exact
    secureAgainst_of_sharpDiagonal_offDiagonal_fiber_and_jointLWE_canonical
      canonicalOffDiagonalOperatorLaws isPPT publicIsPPT predictorIsPPT jointLWEIsPPT
      hPublicClosed hPredictorClosed hJointLWEClosed hUniformJointLWEClosed hPrediction
      hDiagonal hOffDiagonal hFiber hJointLWE

/-- **Preferred canonical security-only endpoint with control averaging preserved.**

The correct branch is charged by the sharp selected-diagonal quantity plus the complete
off-diagonal replacement distance averaged under the actual generated control and maximized only
over the finite secret pair.  The wrong branch is charged by the exact message-one fiber loss.
No support-wise native law, Gaussian-table premise, or correctness proposition remains. -/
theorem secureAgainst_of_canonicalAveragedOperatorLosses_coordinatePrediction_fiber_and_jointLWE
    (isPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          (oneShotTransformerOfDirectCertificates canonicalCertificate
            canonicalAveragedDirectCertificateFamily)
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hDiagonal : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalSharpDiagonalError securityParameter)))
    (hOffDiagonal : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalSelectedAveragedOffDiagonalError securityParameter)))
    (hFiber : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalWrongViewFiberLoss securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (securityGame (parameters canonicalCertificate)).secureAgainst isPPT := by
  apply secureAgainst_of_directCertificates_coordinatePrediction_and_jointLWE
    canonicalCertificate canonicalAveragedDirectCertificateFamily isPPT publicIsPPT
    predictorIsPPT jointLWEIsPPT hPublicClosed hPredictorClosed hJointLWEClosed
    hUniformJointLWEClosed hPrediction
  · intro _distinguisher _hdistinguisher
    have hsum : negligible (fun securityParameter ↦
        ENNReal.ofReal (canonicalSharpDiagonalError securityParameter) +
          ENNReal.ofReal (canonicalSelectedAveragedOffDiagonalError securityParameter)) :=
      negligible_add hDiagonal hOffDiagonal
    simpa only [canonicalAveragedDirectCertificateFamily_correctError,
      ENNReal.ofReal_add (canonicalSharpDiagonalError_nonneg _)
        (canonicalSelectedAveragedOffDiagonalError_nonneg _)] using hsum
  · intro _distinguisher _hdistinguisher
    simpa using canonicalWrongViewFreshnessError_negligible hFiber
  · exact hJointLWE

/-- **Preferred security-only TFHE endpoint with the off-diagonal ciphertext layer removed.**

The correct branch now depends on the sharp diagonal quantity and an explicit finite `L²`
comparison between the native effective residual
`internal-product phase + centered-binomial source error` and the compiled target error vector,
averaged under the generated control.  Circular coordinate prediction, the message-one fiber
quantity, and ordinary joint LWE remain the computational/analytic security assumptions.  No
correctness proposition occurs. -/
theorem secureAgainst_of_canonicalResidualL2Losses_coordinatePrediction_fiber_and_jointLWE
    (isPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          (oneShotTransformerOfDirectCertificates canonicalCertificate
            canonicalResidualL2DirectCertificateFamily)
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hDiagonal : negligible (fun securityParameter => ENNReal.ofReal
      (canonicalSharpDiagonalError securityParameter)))
    (hOffDiagonalL2 : negligible (fun securityParameter => ENNReal.ofReal
      (canonicalSelectedAveragedOffDiagonalResidualL2Error securityParameter)))
    (hFiber : negligible (fun securityParameter => ENNReal.ofReal
      (canonicalWrongViewFiberLoss securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (securityGame (parameters canonicalCertificate)).secureAgainst isPPT := by
  apply secureAgainst_of_directCertificates_coordinatePrediction_and_jointLWE
    canonicalCertificate canonicalResidualL2DirectCertificateFamily isPPT publicIsPPT
    predictorIsPPT jointLWEIsPPT hPublicClosed hPredictorClosed hJointLWEClosed
    hUniformJointLWEClosed hPrediction
  · intro _distinguisher _hdistinguisher
    have hsum : negligible (fun securityParameter =>
        ENNReal.ofReal (canonicalSharpDiagonalError securityParameter) +
          ENNReal.ofReal
            (canonicalSelectedAveragedOffDiagonalResidualL2Error securityParameter)) :=
      negligible_add hDiagonal hOffDiagonalL2
    simpa only [canonicalResidualL2DirectCertificateFamily_correctError,
      ENNReal.ofReal_add (canonicalSharpDiagonalError_nonneg _)
        (canonicalSelectedAveragedOffDiagonalResidualL2Error_nonneg _)] using hsum
  · intro _distinguisher _hdistinguisher
    simpa using canonicalWrongViewFreshnessError_negligible hFiber
  · exact hJointLWE

/-- **Strongest security-only TFHE endpoint.**

The off-diagonal obligation is now solely the finite law of
`fresh centered-binomial error + uniform-digit operator (signed centered-binomial control error)`
against the compiled target discrete-Gaussian vector.  Honest control masks, the ring secret,
and the TGSW gadget message have been eliminated by exact distributional equalities.  Centered-
binomial sign symmetry removes the selected-Boolean maximum as well.  The remaining premise is
the negligibility of one explicit finite average of explicit fiber counts.  This theorem still
assumes the sharp diagonal estimate, circular coordinate prediction, message-one fiber decay,
and ordinary joint LWE; it has no correctness premise. -/
theorem secureAgainst_of_canonicalErrorOnlyL2Losses_coordinatePrediction_fiber_and_jointLWE
    (isPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          (oneShotTransformerOfDirectCertificates canonicalCertificate
            canonicalErrorOnlyL2DirectCertificateFamily)
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hDiagonal : negligible (fun securityParameter => ENNReal.ofReal
      (canonicalSharpDiagonalError securityParameter)))
    (hOffDiagonalL2 : negligible (fun securityParameter => ENNReal.ofReal
      (canonicalSelectedAveragedOffDiagonalDigitFiberL2Error securityParameter)))
    (hFiber : negligible (fun securityParameter => ENNReal.ofReal
      (canonicalWrongViewFiberLoss securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (securityGame (parameters canonicalCertificate)).secureAgainst isPPT := by
  apply secureAgainst_of_directCertificates_coordinatePrediction_and_jointLWE
    canonicalCertificate canonicalErrorOnlyL2DirectCertificateFamily isPPT publicIsPPT
    predictorIsPPT jointLWEIsPPT hPublicClosed hPredictorClosed hJointLWEClosed
    hUniformJointLWEClosed hPrediction
  · intro _distinguisher _hdistinguisher
    have hOffDiagonalErrorOnly : negligible (fun securityParameter => ENNReal.ofReal
        (canonicalSelectedAveragedOffDiagonalErrorOnlyL2Error securityParameter)) := by
      simpa only [canonicalSelectedAveragedOffDiagonalErrorOnlyL2Error_eq_digitFiber] using
        hOffDiagonalL2
    have hsum : negligible (fun securityParameter =>
        ENNReal.ofReal (canonicalSharpDiagonalError securityParameter) +
          ENNReal.ofReal
            (canonicalSelectedAveragedOffDiagonalErrorOnlyL2Error securityParameter)) :=
      negligible_add hDiagonal hOffDiagonalErrorOnly
    simpa only [canonicalErrorOnlyL2DirectCertificateFamily_correctError,
      ENNReal.ofReal_add (canonicalSharpDiagonalError_nonneg _)
        (canonicalSelectedAveragedOffDiagonalErrorOnlyL2Error_nonneg _)] using hsum
  · intro _distinguisher _hdistinguisher
    simpa using canonicalWrongViewFreshnessError_negligible hFiber
  · exact hJointLWE

/-- Strongest security-only endpoint with the opaque wrong-view negligibility premise replaced
by a high-probability, generated-control second-moment certificate.  Exceptional controls are
allowed and contribute only their negligible native sampling probability. -/
theorem secureAgainst_of_canonicalErrorOnlyL2Losses_coordinatePrediction_goodControlFiber_and_jointLWE
    (isPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          (oneShotTransformerOfDirectCertificates canonicalCertificate
            canonicalErrorOnlyL2DirectCertificateFamily)
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hDiagonal : negligible (fun securityParameter => ENNReal.ofReal
      (canonicalSharpDiagonalError securityParameter)))
    (hOffDiagonalL2 : negligible (fun securityParameter => ENNReal.ofReal
      (canonicalSelectedAveragedOffDiagonalDigitFiberL2Error securityParameter)))
    (fiberCertificate : CanonicalWrongViewGoodControlCertificate)
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (securityGame (parameters canonicalCertificate)).secureAgainst isPPT :=
  secureAgainst_of_canonicalErrorOnlyL2Losses_coordinatePrediction_fiber_and_jointLWE
    isPPT publicIsPPT predictorIsPPT jointLWEIsPPT hPublicClosed hPredictorClosed
    hJointLWEClosed hUniformJointLWEClosed hPrediction hDiagonal hOffDiagonalL2
    fiberCertificate.fiberLoss_negligible hJointLWE

/-- **Strongest native security-only endpoint.**

The wrong-view hypothesis is the exact probability that the one normalized generated-control
map is non-bijective.  Bijectivity makes the complete wrong public view uniform at once, so this
theorem strictly avoids the BRK-layout multiplier required by rowwise fiber-distance bounds. -/
theorem secureAgainst_of_canonicalErrorOnlyL2Losses_coordinatePrediction_controlFailure_and_jointLWE
    (isPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hPublicClosed : ∀ adversary, isPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          (oneShotTransformerOfDirectCertificates canonicalCertificate
            canonicalErrorOnlyL2ControlFailureDirectCertificateFamily)
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, isPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hDiagonal : negligible (fun securityParameter => ENNReal.ofReal
      (canonicalSharpDiagonalError securityParameter)))
    (hOffDiagonalL2 : negligible (fun securityParameter => ENNReal.ofReal
      (canonicalSelectedAveragedOffDiagonalDigitFiberL2Error securityParameter)))
    (hControlFailure : negligible (fun securityParameter => ENNReal.ofReal
      (canonicalWrongViewNonbijectivityError securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (securityGame (parameters canonicalCertificate)).secureAgainst isPPT := by
  apply secureAgainst_of_directCertificates_coordinatePrediction_and_jointLWE
    canonicalCertificate canonicalErrorOnlyL2ControlFailureDirectCertificateFamily
    isPPT publicIsPPT predictorIsPPT jointLWEIsPPT hPublicClosed hPredictorClosed
    hJointLWEClosed hUniformJointLWEClosed hPrediction
  · intro _distinguisher _hdistinguisher
    have hOffDiagonalErrorOnly : negligible (fun securityParameter => ENNReal.ofReal
        (canonicalSelectedAveragedOffDiagonalErrorOnlyL2Error securityParameter)) := by
      simpa only [canonicalSelectedAveragedOffDiagonalErrorOnlyL2Error_eq_digitFiber] using
        hOffDiagonalL2
    have hsum : negligible (fun securityParameter =>
        ENNReal.ofReal (canonicalSharpDiagonalError securityParameter) +
          ENNReal.ofReal
            (canonicalSelectedAveragedOffDiagonalErrorOnlyL2Error securityParameter)) :=
      negligible_add hDiagonal hOffDiagonalErrorOnly
    simpa only [canonicalErrorOnlyL2ControlFailureDirectCertificateFamily_correctError,
      ENNReal.ofReal_add (canonicalSharpDiagonalError_nonneg _)
        (canonicalSelectedAveragedOffDiagonalErrorOnlyL2Error_nonneg _)] using hsum
  · intro _distinguisher _hdistinguisher
    simpa only [canonicalErrorOnlyL2ControlFailureDirectCertificateFamily_freshnessError] using
      hControlFailure
  · exact hJointLWE

/-- Public evaluation preserves the explicit post-evaluation-smudging security theorem.  The
evaluator-facing corollary adds only the closure of compiling an output adversary into the base
adaptive game and still contains no correctness premise. -/
theorem evaluationSecureAgainst_of_postEvaluationSmudging_normalForm_coordinatePrediction_controlFailure_and_jointLWE
    {Output : Type}
    (laws : CanonicalPostSmudgedNormalFormLaws)
    (evaluate :
      PublicEvaluatorFamily (Output := Output) (parameters canonicalCertificate))
    (baseIsPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary
        (Output := Output) (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT
        (compileEvaluationAdversary
          (parameters canonicalCertificate) evaluate adversary))
    (hPublicClosed : ∀ adversary, baseIsPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          laws.toOneShotTransformer referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hNormalForm : ∀ distinguisher, publicIsPPT distinguisher →
      negligible (fun securityParameter ↦ ENNReal.ofReal
        (laws.normalFormError distinguisher.queryCount securityParameter
          (referenceCoordinate securityParameter))))
    (hControlFailure : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalWrongViewNonbijectivityError securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (evaluationSecurityGame (parameters canonicalCertificate) evaluate).secureAgainst
      evaluationIsPPT := by
  apply evaluationSecureAgainst_of_security
    (parameters canonicalCertificate) evaluate baseIsPPT evaluationIsPPT hEvaluationClosed
  exact
    secureAgainst_of_postEvaluationSmudging_normalForm_coordinatePrediction_controlFailure_and_jointLWE
      laws baseIsPPT publicIsPPT predictorIsPPT jointLWEIsPPT hPublicClosed
      hPredictorClosed hJointLWEClosed hUniformJointLWEClosed hPrediction hNormalForm
      hControlFailure hJointLWE

/-- Public-evaluation corollary for the canonical mask-normal-form endpoint.  As in the base
theorem, the wide Gaussian and its placement after evaluation are proved internally and no
correctness proposition is assumed. -/
theorem evaluationSecureAgainst_of_canonicalPostSmudgedMaskLoss_coordinatePrediction_controlFailure_and_jointLWE
    {Output : Type}
    (evaluate :
      PublicEvaluatorFamily (Output := Output) (parameters canonicalCertificate))
    (baseIsPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary
        (Output := Output) (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT
        (compileEvaluationAdversary
          (parameters canonicalCertificate) evaluate adversary))
    (hPublicClosed : ∀ adversary, baseIsPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          canonicalPostSmudgedMaskNormalFormLaws.toOneShotTransformer
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hMaskNormalForm : ∀ distinguisher, publicIsPPT distinguisher →
      negligible (fun securityParameter ↦ ENNReal.ofReal
        (canonicalPostSmudgedMaskNormalFormError distinguisher.queryCount
          securityParameter (referenceCoordinate securityParameter))))
    (hControlFailure : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalWrongViewNonbijectivityError securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (evaluationSecurityGame (parameters canonicalCertificate) evaluate).secureAgainst
      evaluationIsPPT :=
  evaluationSecureAgainst_of_postEvaluationSmudging_normalForm_coordinatePrediction_controlFailure_and_jointLWE
    canonicalPostSmudgedMaskNormalFormLaws evaluate baseIsPPT evaluationIsPPT
    publicIsPPT predictorIsPPT jointLWEIsPPT hEvaluationClosed hPublicClosed
    hPredictorClosed hJointLWEClosed hUniformJointLWEClosed hPrediction
    hMaskNormalForm hControlFailure hJointLWE

/-- Public-evaluation corollary for the explicit full-mask-collision endpoint.  Public
homomorphic evaluation is compiled into the base confidentiality game; neither this compilation
nor the collision premise assumes functional correctness. -/
theorem evaluationSecureAgainst_of_canonicalPostSmudgedMaskCollision_coordinatePrediction_controlFailure_and_jointLWE
    {Output : Type}
    (evaluate :
      PublicEvaluatorFamily (Output := Output) (parameters canonicalCertificate))
    (baseIsPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary
        (Output := Output) (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT
        (compileEvaluationAdversary
          (parameters canonicalCertificate) evaluate adversary))
    (hPublicClosed : ∀ adversary, baseIsPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          canonicalPostSmudgedMaskCollisionNormalFormLaws.toOneShotTransformer
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hMaskCollision : ∀ distinguisher, publicIsPPT distinguisher →
      negligible (fun securityParameter ↦ ENNReal.ofReal
        (canonicalPostSmudgedMaskCollisionLoss distinguisher.queryCount
          securityParameter (referenceCoordinate securityParameter))))
    (hControlFailure : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalWrongViewNonbijectivityError securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (evaluationSecurityGame (parameters canonicalCertificate) evaluate).secureAgainst
      evaluationIsPPT :=
  evaluationSecureAgainst_of_postEvaluationSmudging_normalForm_coordinatePrediction_controlFailure_and_jointLWE
    canonicalPostSmudgedMaskCollisionNormalFormLaws evaluate baseIsPPT evaluationIsPPT
    publicIsPPT predictorIsPPT jointLWEIsPPT hEvaluationClosed hPublicClosed
    hPredictorClosed hJointLWEClosed hUniformJointLWEClosed hPrediction
    hMaskCollision hControlFailure hJointLWE

/-- Public-evaluation corollary for the complete conditional pair-collision certificate. -/
theorem evaluationSecureAgainst_of_canonicalPostSmudgedMaskPairCollision_coordinatePrediction_controlFailure_and_jointLWE
    {Output : Type}
    (certificate : CanonicalPostSmudgedMaskCollisionCertificate)
    (evaluate :
      PublicEvaluatorFamily (Output := Output) (parameters canonicalCertificate))
    (baseIsPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary
        (Output := Output) (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT
        (compileEvaluationAdversary
          (parameters canonicalCertificate) evaluate adversary))
    (hPublicClosed : ∀ adversary, baseIsPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          certificate.normalFormLaws.toOneShotTransformer
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hCollisionError : ∀ distinguisher, publicIsPPT distinguisher →
      negligible (fun securityParameter ↦ ENNReal.ofReal
        (Real.sqrt
          (certificate.ε distinguisher.queryCount securityParameter
            (referenceCoordinate securityParameter)) / 2)))
    (hControlFailure : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalWrongViewNonbijectivityError securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (evaluationSecurityGame (parameters canonicalCertificate) evaluate).secureAgainst
      evaluationIsPPT :=
  evaluationSecureAgainst_of_postEvaluationSmudging_normalForm_coordinatePrediction_controlFailure_and_jointLWE
    certificate.normalFormLaws evaluate baseIsPPT evaluationIsPPT publicIsPPT
    predictorIsPPT jointLWEIsPPT hEvaluationClosed hPublicClosed hPredictorClosed
    hJointLWEClosed hUniformJointLWEClosed hPrediction hCollisionError
    hControlFailure hJointLWE

/-- Public-evaluation corollary for the preferred residual-first static-mask collision route.
Evaluation is compiled into the base confidentiality game and adds no correctness assumption. -/
theorem evaluationSecureAgainst_of_canonicalPostSmudgedStaticMaskPairCollision_coordinatePrediction_controlFailure_and_jointLWE
    {Output : Type}
    (certificate : CanonicalPostSmudgedStaticMaskCollisionCertificate)
    (evaluate :
      PublicEvaluatorFamily (Output := Output) (parameters canonicalCertificate))
    (baseIsPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary
        (Output := Output) (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT
        (compileEvaluationAdversary
          (parameters canonicalCertificate) evaluate adversary))
    (hPublicClosed : ∀ adversary, baseIsPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          certificate.toOneShotTransformer referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hCollisionError : ∀ distinguisher, publicIsPPT distinguisher →
      negligible (fun securityParameter ↦ ENNReal.ofReal
        (Real.sqrt
          (certificate.ε distinguisher.queryCount securityParameter
            (referenceCoordinate securityParameter)) / 2)))
    (hControlFailure : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalWrongViewNonbijectivityError securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (evaluationSecurityGame (parameters canonicalCertificate) evaluate).secureAgainst
      evaluationIsPPT := by
  apply evaluationSecureAgainst_of_security
    (parameters canonicalCertificate) evaluate baseIsPPT evaluationIsPPT hEvaluationClosed
  exact
    secureAgainst_of_canonicalPostSmudgedStaticMaskPairCollision_coordinatePrediction_controlFailure_and_jointLWE
      certificate baseIsPPT publicIsPPT predictorIsPPT jointLWEIsPPT hPublicClosed
      hPredictorClosed hJointLWEClosed hUniformJointLWEClosed hPrediction hCollisionError
      hControlFailure hJointLWE

/-- Public evaluation preserves the preferred exact selected-diagonal security endpoint.
Evaluation is compiled into the base confidentiality game and adds no correctness premise. -/
theorem evaluationSecureAgainst_of_canonicalPostSmudgedSelectedDiagonal_coordinatePrediction_controlFailure_and_jointLWE
    {Output : Type}
    (evaluate :
      PublicEvaluatorFamily (Output := Output) (parameters canonicalCertificate))
    (baseIsPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary
        (Output := Output) (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT
        (compileEvaluationAdversary
          (parameters canonicalCertificate) evaluate adversary))
    (hPublicClosed : ∀ adversary, baseIsPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          canonicalPostSmudgedSelectedDiagonalOneShotTransformer
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hSelectedDiagonalMask : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalPostSmudgedSelectedDiagonalMaskLoss securityParameter)))
    (hControlFailure : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalWrongViewNonbijectivityError securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (evaluationSecurityGame (parameters canonicalCertificate) evaluate).secureAgainst
      evaluationIsPPT := by
  apply evaluationSecureAgainst_of_security
    (parameters canonicalCertificate) evaluate baseIsPPT evaluationIsPPT hEvaluationClosed
  exact
    secureAgainst_of_canonicalPostSmudgedSelectedDiagonal_coordinatePrediction_controlFailure_and_jointLWE
      baseIsPPT publicIsPPT predictorIsPPT jointLWEIsPPT hPublicClosed
      hPredictorClosed hJointLWEClosed hUniformJointLWEClosed hPrediction
      hSelectedDiagonalMask hControlFailure hJointLWE

/-- Public evaluation preserves the retained-fiber-slice security endpoint and introduces no
correctness premise. -/
theorem evaluationSecureAgainst_of_canonicalPostSmudgedSelectedDiagonalRetainedFiberSlices_coordinatePrediction_controlFailure_and_jointLWE
    {Output : Type}
    (evaluate :
      PublicEvaluatorFamily (Output := Output) (parameters canonicalCertificate))
    (baseIsPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary
        (Output := Output) (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT
        (compileEvaluationAdversary
          (parameters canonicalCertificate) evaluate adversary))
    (hPublicClosed : ∀ adversary, baseIsPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          canonicalPostSmudgedSelectedDiagonalOneShotTransformer
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hSelf : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalPostSmudgedSelectedDiagonalSelfMaskLoss securityParameter)))
    (hDistinct : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalPostSmudgedSelectedDiagonalDistinctMaskLoss securityParameter)))
    (hControlFailure : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalWrongViewNonbijectivityError securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (evaluationSecurityGame (parameters canonicalCertificate) evaluate).secureAgainst
      evaluationIsPPT :=
  evaluationSecureAgainst_of_canonicalPostSmudgedSelectedDiagonal_coordinatePrediction_controlFailure_and_jointLWE
    evaluate baseIsPPT evaluationIsPPT publicIsPPT predictorIsPPT jointLWEIsPPT
    hEvaluationClosed hPublicClosed hPredictorClosed hJointLWEClosed hUniformJointLWEClosed
    hPrediction
    (canonicalPostSmudgedSelectedDiagonalMaskLoss_negligible_of_self_and_distinct
      hSelf hDistinct)
    hControlFailure hJointLWE

/-- Public evaluation preserves the finite self-fiber-average certificate endpoint and adds no
correctness premise. -/
theorem evaluationSecureAgainst_of_canonicalPostSmudgedSelectedDiagonalSelfFiberAverage_coordinatePrediction_controlFailure_and_jointLWE
    {Output : Type}
    (evaluate :
      PublicEvaluatorFamily (Output := Output) (parameters canonicalCertificate))
    (baseIsPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary
        (Output := Output) (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT
        (compileEvaluationAdversary
          (parameters canonicalCertificate) evaluate adversary))
    (hPublicClosed : ∀ adversary, baseIsPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          canonicalPostSmudgedSelectedDiagonalOneShotTransformer
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (certificate : CanonicalSelectedDiagonalSelfFiberAverageCertificate)
    (hSelfFiberAverage : negligible (fun securityParameter ↦ ENNReal.ofReal
      (certificate.lossBound securityParameter)))
    (hDistinct : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalPostSmudgedSelectedDiagonalDistinctMaskLoss securityParameter)))
    (hControlFailure : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalWrongViewNonbijectivityError securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (evaluationSecurityGame (parameters canonicalCertificate) evaluate).secureAgainst
      evaluationIsPPT :=
  evaluationSecureAgainst_of_canonicalPostSmudgedSelectedDiagonalRetainedFiberSlices_coordinatePrediction_controlFailure_and_jointLWE
    evaluate baseIsPPT evaluationIsPPT publicIsPPT predictorIsPPT jointLWEIsPPT
    hEvaluationClosed hPublicClosed hPredictorClosed hJointLWEClosed hUniformJointLWEClosed
    hPrediction (certificate.selfMaskLoss_negligible hSelfFiberAverage) hDistinct
    hControlFailure hJointLWE

/-- Public evaluation preserves the complete retained-fiber-average certificate endpoint and
introduces no correctness premise. -/
theorem evaluationSecureAgainst_of_canonicalPostSmudgedSelectedDiagonalRetainedFiberAverage_coordinatePrediction_controlFailure_and_jointLWE
    {Output : Type}
    (evaluate :
      PublicEvaluatorFamily (Output := Output) (parameters canonicalCertificate))
    (baseIsPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary
        (Output := Output) (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT
        (compileEvaluationAdversary
          (parameters canonicalCertificate) evaluate adversary))
    (hPublicClosed : ∀ adversary, baseIsPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          canonicalPostSmudgedSelectedDiagonalOneShotTransformer
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (certificate : CanonicalSelectedDiagonalRetainedFiberAverageCertificate)
    (hRetainedFiber : negligible (fun securityParameter ↦ ENNReal.ofReal
      (certificate.lossBound securityParameter)))
    (hControlFailure : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalWrongViewNonbijectivityError securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (evaluationSecurityGame (parameters canonicalCertificate) evaluate).secureAgainst
      evaluationIsPPT :=
  evaluationSecureAgainst_of_canonicalPostSmudgedSelectedDiagonal_coordinatePrediction_controlFailure_and_jointLWE
    evaluate baseIsPPT evaluationIsPPT publicIsPPT predictorIsPPT jointLWEIsPPT
    hEvaluationClosed hPublicClosed hPredictorClosed hJointLWEClosed hUniformJointLWEClosed
    hPrediction (certificate.maskLoss_negligible hRetainedFiber)
    hControlFailure hJointLWE

/-- Public-evaluation compatibility corollary for the source-independent global pair-collision
relaxation.  Its canonical negligibility premise is formally false; evaluation itself is still
compiled into the base confidentiality game and adds no correctness premise. -/
theorem evaluationSecureAgainst_of_canonicalPostSmudgedSelectedDiagonalPairCollision_coordinatePrediction_controlFailure_and_jointLWE
    {Output : Type}
    (evaluate :
      PublicEvaluatorFamily (Output := Output) (parameters canonicalCertificate))
    (baseIsPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary
        (Output := Output) (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT
        (compileEvaluationAdversary
          (parameters canonicalCertificate) evaluate adversary))
    (hPublicClosed : ∀ adversary, baseIsPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          canonicalPostSmudgedSelectedDiagonalOneShotTransformer
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hPairCollision : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalPostSmudgedSelectedDiagonalPairCollisionBound securityParameter)))
    (hControlFailure : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalWrongViewNonbijectivityError securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (evaluationSecurityGame (parameters canonicalCertificate) evaluate).secureAgainst
      evaluationIsPPT :=
  evaluationSecureAgainst_of_canonicalPostSmudgedSelectedDiagonal_coordinatePrediction_controlFailure_and_jointLWE
    evaluate baseIsPPT evaluationIsPPT publicIsPPT predictorIsPPT jointLWEIsPPT
    hEvaluationClosed hPublicClosed hPredictorClosed hJointLWEClosed hUniformJointLWEClosed
    hPrediction
    (canonicalPostSmudgedSelectedDiagonalMaskLoss_negligible_of_pairCollisionBound
      hPairCollision)
    hControlFailure hJointLWE

/-- Public evaluation preserves the security-only Gaussian-target TFHE theorem.  This corollary
adds only the computational closure of compiling an evaluated-output adversary into the base
adaptive game; it introduces no correctness premise. -/
theorem evaluationSecureAgainst_of_coordinatePrediction_normalForm_freshness_and_jointLWE
    {Output : Type}
    (certificate : ScalarCertificateFamily)
    (native : CoupledDirectCertificateFamily certificate)
    (evaluate : PublicEvaluatorFamily (Output := Output) (parameters certificate))
    (baseIsPPT : PolynomialQueryAdversary (parameters certificate) → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary (Output := Output) (parameters certificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily certificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily certificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters certificate) → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT
        (compileEvaluationAdversary (parameters certificate) evaluate adversary))
    (hPublicClosed : ∀ adversary, baseIsPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters certificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters certificate) errorWidth errorWidth
          (oneShotTransformer certificate native) referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT (jointLWEReduction (parameters certificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters certificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame certificate).secureAgainst predictorIsPPT)
    (hcertificate : negligible (fun securityParameter ↦
      (certificate securityParameter).bound))
    (hNormalForm : ∀ distinguisher, publicIsPPT distinguisher →
      negligible (fun securityParameter ↦ ENNReal.ofReal
        (native.normalFormError distinguisher.queryCount securityParameter
          (referenceCoordinate securityParameter))))
    (hFreshness : ∀ distinguisher, publicIsPPT distinguisher →
      negligible (fun securityParameter ↦ ENNReal.ofReal
        ((native.directAt distinguisher.queryCount securityParameter).freshnessError
          (referenceCoordinate securityParameter))))
    (hJointLWE :
      (jointLWESecurityGame (parameters certificate)).secureAgainst jointLWEIsPPT) :
    (evaluationSecurityGame (parameters certificate) evaluate).secureAgainst evaluationIsPPT := by
  apply evaluationSecureAgainst_of_security
    (parameters certificate) evaluate baseIsPPT evaluationIsPPT hEvaluationClosed
  exact secureAgainst_of_coordinatePrediction_normalForm_freshness_and_jointLWE
    certificate native baseIsPPT publicIsPPT predictorIsPPT jointLWEIsPPT
    hPublicClosed hPredictorClosed hJointLWEClosed hUniformJointLWEClosed hPrediction
    hcertificate hNormalForm hFreshness hJointLWE

/-- Public evaluation corollary for the canonical finite Gaussian family.  As in the base
canonical theorem, no correctness or finite-Gaussian approximation premise is exposed. -/
theorem evaluationSecureAgainst_of_coordinatePrediction_normalForm_freshness_and_jointLWE_canonical
    {Output : Type}
    (native : CoupledDirectCertificateFamily canonicalCertificate)
    (evaluate :
      PublicEvaluatorFamily (Output := Output) (parameters canonicalCertificate))
    (baseIsPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary
        (Output := Output) (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT
        (compileEvaluationAdversary
          (parameters canonicalCertificate) evaluate adversary))
    (hPublicClosed : ∀ adversary, baseIsPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          (oneShotTransformer canonicalCertificate native) referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hNormalForm : ∀ distinguisher, publicIsPPT distinguisher →
      negligible (fun securityParameter ↦ ENNReal.ofReal
        (native.normalFormError distinguisher.queryCount securityParameter
          (referenceCoordinate securityParameter))))
    (hFreshness : ∀ distinguisher, publicIsPPT distinguisher →
      negligible (fun securityParameter ↦ ENNReal.ofReal
        ((native.directAt distinguisher.queryCount securityParameter).freshnessError
          (referenceCoordinate securityParameter))))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (evaluationSecurityGame (parameters canonicalCertificate) evaluate).secureAgainst
      evaluationIsPPT :=
  evaluationSecureAgainst_of_coordinatePrediction_normalForm_freshness_and_jointLWE
    canonicalCertificate native evaluate baseIsPPT evaluationIsPPT publicIsPPT
    predictorIsPPT jointLWEIsPPT hEvaluationClosed hPublicClosed hPredictorClosed
    hJointLWEClosed hUniformJointLWEClosed hPrediction
    canonicalCertificate_bound_negligible hNormalForm hFreshness hJointLWE

/-- Public-evaluation confidentiality from the same explicit diagonal, off-diagonal, and
message-one fiber quantities.  Evaluation adds only the usual adversary-class closure premise. -/
theorem evaluationSecureAgainst_of_explicitNativeLaws_coordinatePrediction_fiber_and_jointLWE_canonical
    {Output : Type}
    (laws : CanonicalCorrectViewLaws)
    (evaluate :
      PublicEvaluatorFamily (Output := Output) (parameters canonicalCertificate))
    (baseIsPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary
        (Output := Output) (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT
        (compileEvaluationAdversary
          (parameters canonicalCertificate) evaluate adversary))
    (hPublicClosed : ∀ adversary, baseIsPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          (oneShotTransformerOfDirectCertificates canonicalCertificate
            laws.toDirectCertificateFamily)
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hCorrect : negligible (fun securityParameter ↦ ENNReal.ofReal
      (laws.selectedCorrectError securityParameter)))
    (hFiber : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalWrongViewFiberLoss securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (evaluationSecurityGame (parameters canonicalCertificate) evaluate).secureAgainst
      evaluationIsPPT := by
  apply evaluationSecureAgainst_of_security
    (parameters canonicalCertificate) evaluate baseIsPPT evaluationIsPPT
    hEvaluationClosed
  exact
    secureAgainst_of_explicitNativeLaws_coordinatePrediction_fiber_and_jointLWE_canonical
      laws baseIsPPT publicIsPPT predictorIsPPT jointLWEIsPPT hPublicClosed
      hPredictorClosed hJointLWEClosed hUniformJointLWEClosed hPrediction hCorrect
      hFiber hJointLWE

/-- Public-evaluation version of the support-wise sharp-diagonal endpoint. -/
theorem evaluationSecureAgainst_of_sharpDiagonal_offDiagonal_fiber_and_jointLWE_canonical
    {Output : Type}
    (laws : CanonicalOffDiagonalLaws)
    (evaluate :
      PublicEvaluatorFamily (Output := Output) (parameters canonicalCertificate))
    (baseIsPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary
        (Output := Output) (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT
        (compileEvaluationAdversary
          (parameters canonicalCertificate) evaluate adversary))
    (hPublicClosed : ∀ adversary, baseIsPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          (oneShotTransformerOfDirectCertificates canonicalCertificate
            laws.toCanonicalCorrectViewLaws.toDirectCertificateFamily)
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hDiagonal : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalSharpDiagonalError securityParameter)))
    (hOffDiagonal : negligible (fun securityParameter ↦ ENNReal.ofReal
      (laws.selectedOffDiagonalError securityParameter)))
    (hFiber : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalWrongViewFiberLoss securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (evaluationSecurityGame (parameters canonicalCertificate) evaluate).secureAgainst
      evaluationIsPPT := by
  apply evaluationSecureAgainst_of_security
    (parameters canonicalCertificate) evaluate baseIsPPT evaluationIsPPT
    hEvaluationClosed
  exact
    secureAgainst_of_sharpDiagonal_offDiagonal_fiber_and_jointLWE_canonical
      laws baseIsPPT publicIsPPT predictorIsPPT jointLWEIsPPT hPublicClosed
      hPredictorClosed hJointLWEClosed hUniformJointLWEClosed hPrediction hDiagonal
      hOffDiagonal hFiber hJointLWE

/-- Public-evaluation version of the support-wise finite-operator endpoint. -/
theorem evaluationSecureAgainst_of_canonicalOperatorLosses_coordinatePrediction_fiber_and_jointLWE
    {Output : Type}
    (evaluate :
      PublicEvaluatorFamily (Output := Output) (parameters canonicalCertificate))
    (baseIsPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary
        (Output := Output) (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT
        (compileEvaluationAdversary
          (parameters canonicalCertificate) evaluate adversary))
    (hPublicClosed : ∀ adversary, baseIsPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          (oneShotTransformerOfDirectCertificates canonicalCertificate
            canonicalOffDiagonalOperatorLaws.toCanonicalCorrectViewLaws.toDirectCertificateFamily)
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hDiagonal : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalSharpDiagonalError securityParameter)))
    (hOffDiagonal : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalSelectedOffDiagonalOperatorError securityParameter)))
    (hFiber : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalWrongViewFiberLoss securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (evaluationSecurityGame (parameters canonicalCertificate) evaluate).secureAgainst
      evaluationIsPPT := by
  exact
    evaluationSecureAgainst_of_sharpDiagonal_offDiagonal_fiber_and_jointLWE_canonical
      canonicalOffDiagonalOperatorLaws evaluate baseIsPPT evaluationIsPPT publicIsPPT
      predictorIsPPT jointLWEIsPPT hEvaluationClosed hPublicClosed hPredictorClosed
      hJointLWEClosed hUniformJointLWEClosed hPrediction hDiagonal hOffDiagonal hFiber
      hJointLWE

/-- Public-evaluation version of the preferred control-averaged canonical endpoint. -/
theorem evaluationSecureAgainst_of_canonicalAveragedOperatorLosses_coordinatePrediction_fiber_and_jointLWE
    {Output : Type}
    (evaluate :
      PublicEvaluatorFamily (Output := Output) (parameters canonicalCertificate))
    (baseIsPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary
        (Output := Output) (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT
        (compileEvaluationAdversary
          (parameters canonicalCertificate) evaluate adversary))
    (hPublicClosed : ∀ adversary, baseIsPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          (oneShotTransformerOfDirectCertificates canonicalCertificate
            canonicalAveragedDirectCertificateFamily)
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hDiagonal : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalSharpDiagonalError securityParameter)))
    (hOffDiagonal : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalSelectedAveragedOffDiagonalError securityParameter)))
    (hFiber : negligible (fun securityParameter ↦ ENNReal.ofReal
      (canonicalWrongViewFiberLoss securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (evaluationSecurityGame (parameters canonicalCertificate) evaluate).secureAgainst
      evaluationIsPPT := by
  apply evaluationSecureAgainst_of_security
    (parameters canonicalCertificate) evaluate baseIsPPT evaluationIsPPT
    hEvaluationClosed
  exact
    secureAgainst_of_canonicalAveragedOperatorLosses_coordinatePrediction_fiber_and_jointLWE
      baseIsPPT publicIsPPT predictorIsPPT jointLWEIsPPT hPublicClosed
      hPredictorClosed hJointLWEClosed hUniformJointLWEClosed hPrediction hDiagonal
      hOffDiagonal hFiber hJointLWE

/-- Public-evaluation version of the explicit residual-`L²` security-only endpoint. -/
theorem evaluationSecureAgainst_of_canonicalResidualL2Losses_coordinatePrediction_fiber_and_jointLWE
    {Output : Type}
    (evaluate :
      PublicEvaluatorFamily (Output := Output) (parameters canonicalCertificate))
    (baseIsPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary
        (Output := Output) (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT
        (compileEvaluationAdversary
          (parameters canonicalCertificate) evaluate adversary))
    (hPublicClosed : ∀ adversary, baseIsPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          (oneShotTransformerOfDirectCertificates canonicalCertificate
            canonicalResidualL2DirectCertificateFamily)
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hDiagonal : negligible (fun securityParameter => ENNReal.ofReal
      (canonicalSharpDiagonalError securityParameter)))
    (hOffDiagonalL2 : negligible (fun securityParameter => ENNReal.ofReal
      (canonicalSelectedAveragedOffDiagonalResidualL2Error securityParameter)))
    (hFiber : negligible (fun securityParameter => ENNReal.ofReal
      (canonicalWrongViewFiberLoss securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (evaluationSecurityGame (parameters canonicalCertificate) evaluate).secureAgainst
      evaluationIsPPT := by
  apply evaluationSecureAgainst_of_security
    (parameters canonicalCertificate) evaluate baseIsPPT evaluationIsPPT
    hEvaluationClosed
  exact
    secureAgainst_of_canonicalResidualL2Losses_coordinatePrediction_fiber_and_jointLWE
      baseIsPPT publicIsPPT predictorIsPPT jointLWEIsPPT hPublicClosed
      hPredictorClosed hJointLWEClosed hUniformJointLWEClosed hPrediction hDiagonal
      hOffDiagonalL2 hFiber hJointLWE

/-- Public-evaluation version of the fully normalized error-only security endpoint. -/
theorem evaluationSecureAgainst_of_canonicalErrorOnlyL2Losses_coordinatePrediction_fiber_and_jointLWE
    {Output : Type}
    (evaluate :
      PublicEvaluatorFamily (Output := Output) (parameters canonicalCertificate))
    (baseIsPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary
        (Output := Output) (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT
        (compileEvaluationAdversary
          (parameters canonicalCertificate) evaluate adversary))
    (hPublicClosed : ∀ adversary, baseIsPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          (oneShotTransformerOfDirectCertificates canonicalCertificate
            canonicalErrorOnlyL2DirectCertificateFamily)
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hDiagonal : negligible (fun securityParameter => ENNReal.ofReal
      (canonicalSharpDiagonalError securityParameter)))
    (hOffDiagonalL2 : negligible (fun securityParameter => ENNReal.ofReal
      (canonicalSelectedAveragedOffDiagonalDigitFiberL2Error securityParameter)))
    (hFiber : negligible (fun securityParameter => ENNReal.ofReal
      (canonicalWrongViewFiberLoss securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (evaluationSecurityGame (parameters canonicalCertificate) evaluate).secureAgainst
      evaluationIsPPT := by
  apply evaluationSecureAgainst_of_security
    (parameters canonicalCertificate) evaluate baseIsPPT evaluationIsPPT
    hEvaluationClosed
  exact
    secureAgainst_of_canonicalErrorOnlyL2Losses_coordinatePrediction_fiber_and_jointLWE
      baseIsPPT publicIsPPT predictorIsPPT jointLWEIsPPT hPublicClosed
      hPredictorClosed hJointLWEClosed hUniformJointLWEClosed hPrediction hDiagonal
      hOffDiagonalL2 hFiber hJointLWE

/-- Public-evaluation version of the security-only endpoint using the robust generated-control
fiber certificate. -/
theorem evaluationSecureAgainst_of_canonicalErrorOnlyL2Losses_coordinatePrediction_goodControlFiber_and_jointLWE
    {Output : Type}
    (evaluate :
      PublicEvaluatorFamily (Output := Output) (parameters canonicalCertificate))
    (baseIsPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary
        (Output := Output) (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT
        (compileEvaluationAdversary
          (parameters canonicalCertificate) evaluate adversary))
    (hPublicClosed : ∀ adversary, baseIsPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          (oneShotTransformerOfDirectCertificates canonicalCertificate
            canonicalErrorOnlyL2DirectCertificateFamily)
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hDiagonal : negligible (fun securityParameter => ENNReal.ofReal
      (canonicalSharpDiagonalError securityParameter)))
    (hOffDiagonalL2 : negligible (fun securityParameter => ENNReal.ofReal
      (canonicalSelectedAveragedOffDiagonalDigitFiberL2Error securityParameter)))
    (fiberCertificate : CanonicalWrongViewGoodControlCertificate)
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (evaluationSecurityGame (parameters canonicalCertificate) evaluate).secureAgainst
      evaluationIsPPT := by
  apply evaluationSecureAgainst_of_security
    (parameters canonicalCertificate) evaluate baseIsPPT evaluationIsPPT
    hEvaluationClosed
  exact
    secureAgainst_of_canonicalErrorOnlyL2Losses_coordinatePrediction_goodControlFiber_and_jointLWE
      baseIsPPT publicIsPPT predictorIsPPT jointLWEIsPPT hPublicClosed
      hPredictorClosed hJointLWEClosed hUniformJointLWEClosed hPrediction hDiagonal
      hOffDiagonalL2 fiberCertificate hJointLWE

/-- Public-evaluation version of the strongest native endpoint, using the exact probability of
non-bijectivity of the single generated-control map. -/
theorem evaluationSecureAgainst_of_canonicalErrorOnlyL2Losses_coordinatePrediction_controlFailure_and_jointLWE
    {Output : Type}
    (evaluate :
      PublicEvaluatorFamily (Output := Output) (parameters canonicalCertificate))
    (baseIsPPT : PolynomialQueryAdversary (parameters canonicalCertificate) → Prop)
    (evaluationIsPPT :
      PolynomialQueryEvaluationAdversary
        (Output := Output) (parameters canonicalCertificate) → Prop)
    (publicIsPPT : PublicDistinguisherFamily canonicalCertificate → Prop)
    (predictorIsPPT : CoordinatePredictorFamily canonicalCertificate → Prop)
    (jointLWEIsPPT : JointLWEAdversaryFamily (parameters canonicalCertificate) → Prop)
    (hEvaluationClosed : ∀ adversary, evaluationIsPPT adversary →
      baseIsPPT
        (compileEvaluationAdversary
          (parameters canonicalCertificate) evaluate adversary))
    (hPublicClosed : ∀ adversary, baseIsPPT adversary →
      publicIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.publicDistinguisherReduction
          (parameters canonicalCertificate) adversary))
    (hPredictorClosed : ∀ distinguisher, publicIsPPT distinguisher →
      predictorIsPPT
        (Encryption.Adaptive.Asymptotic.PublicAuxiliaryInputCircular.AugmentedCandidate.OneShot.toCoordinatePredictorFamily
          (parameters canonicalCertificate) errorWidth errorWidth
          (oneShotTransformerOfDirectCertificates canonicalCertificate
            canonicalErrorOnlyL2ControlFailureDirectCertificateFamily)
          referenceCoordinate distinguisher))
    (hJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (jointLWEReduction (parameters canonicalCertificate) adversary))
    (hUniformJointLWEClosed : ∀ adversary, baseIsPPT adversary →
      jointLWEIsPPT
        (MonomialKDM.AuxiliaryInput.uniformBootstrapJointLWEReduction
          (parameters canonicalCertificate) adversary))
    (hPrediction :
      (coordinatePredictionSecurityGame canonicalCertificate).secureAgainst predictorIsPPT)
    (hDiagonal : negligible (fun securityParameter => ENNReal.ofReal
      (canonicalSharpDiagonalError securityParameter)))
    (hOffDiagonalL2 : negligible (fun securityParameter => ENNReal.ofReal
      (canonicalSelectedAveragedOffDiagonalDigitFiberL2Error securityParameter)))
    (hControlFailure : negligible (fun securityParameter => ENNReal.ofReal
      (canonicalWrongViewNonbijectivityError securityParameter)))
    (hJointLWE :
      (jointLWESecurityGame (parameters canonicalCertificate)).secureAgainst jointLWEIsPPT) :
    (evaluationSecurityGame (parameters canonicalCertificate) evaluate).secureAgainst
      evaluationIsPPT := by
  apply evaluationSecureAgainst_of_security
    (parameters canonicalCertificate) evaluate baseIsPPT evaluationIsPPT
    hEvaluationClosed
  exact
    secureAgainst_of_canonicalErrorOnlyL2Losses_coordinatePrediction_controlFailure_and_jointLWE
      baseIsPPT publicIsPPT predictorIsPPT jointLWEIsPPT hPublicClosed
      hPredictorClosed hJointLWEClosed hUniformJointLWEClosed hPrediction hDiagonal
      hOffDiagonalL2 hControlFailure hJointLWE

end

end FormalProof4FHE.TFHE.DiscreteGaussianTarget.GrowingNoise
