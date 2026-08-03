/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeTRGSWAggregateRobustLeakage

/-!
# Composition theorems at the native-TRGSW research boundary

The canonical high-pass laws, their exact Fourier identity, their polynomial normalization bound,
and the robust projected-leakage obstruction are proved in the modules imported above. This file
formalizes the remaining game-composition implications:

* one public complete-view aggregate compiler gives a one-shot aggregate-tail reduction;
* a distribution-aware constrained-batch compiler gives the advertised joint BRK/KSK bound;
* two scaled short public preimages yield a nonzero short kernel vector;
* a hidden dual mode gives the advertised hybrid bound; and
* the support-sensitive low-frequency estimate composes with the one-shot aggregate reduction.

The existence of the public compiler, the short noise-compatible factorization, and the hidden
lossy mode remain hypotheses. No such cryptographic construction is introduced as a primitive.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.NativeTRGSWHardTheoremComposition

noncomputable section

open NativeTRGSWBarrierAndSpectralBoundary
open NativeTRGSWAggregateSecurityAndComplexityLeveraging
open NativeTRGSWAggregateConcreteChannel
open NativeTRGSWAggregateRobustLeakage
open NativeTRGSWCompleteChannel

/-! ## One-shot complete-view aggregate composition -/

/-- Scalar form of the branch-selection reduction.

The real values are the two public compiler outputs on the real source, the uniform values are
their outputs on the uniform source, and the ideal values are the target aggregate games. The
source hypothesis is exactly the gap obtained by guessing the compiler branch. -/
theorem idealGap_le_two_mul_source_add_compilerDefects
    (idealPositive idealNegative realPositive realNegative
      uniformPositive uniformNegative sourceAdvantage
      positiveDefect negativeDefect uniformDefect : ℝ)
    (hpositive : |realPositive - idealPositive| ≤ positiveDefect)
    (hnegative : |realNegative - idealNegative| ≤ negativeDefect)
    (hsource :
      |(realPositive - realNegative) -
          (uniformPositive - uniformNegative)| ≤
        2 * sourceAdvantage)
    (huniform :
      |uniformPositive - uniformNegative| ≤ uniformDefect) :
    |idealPositive - idealNegative| ≤
      2 * sourceAdvantage + positiveDefect + negativeDefect + uniformDefect := by
  have hreal :
      |realPositive - realNegative| ≤
        2 * sourceAdvantage + uniformDefect := by
    calc
      |realPositive - realNegative| =
          |((realPositive - realNegative) -
              (uniformPositive - uniformNegative)) +
            (uniformPositive - uniformNegative)| := by
              congr 1
              ring
      _ ≤
          |(realPositive - realNegative) -
              (uniformPositive - uniformNegative)| +
            |uniformPositive - uniformNegative| :=
        abs_add_le _ _
      _ ≤ 2 * sourceAdvantage + uniformDefect :=
        add_le_add hsource huniform
  have hideal := abs_ideal_gap_le_actual_gap_add_defects
    idealPositive idealNegative realPositive realNegative
    positiveDefect negativeDefect hpositive hnegative
  linarith

/-- Hard Theorem A, conditional on the two public complete-view compiler branches.

The exact signed Fourier tail is charged to one source distinguisher with loss twice the aggregate
normalization, plus the three whole-transcript construction defects. -/
theorem abs_signedHighDegreeSum_le_of_completeViewCompiler
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (response : BitVector Index → BitVector Index → ℝ)
    (degree : ℕ) (hdegree : degree < Fintype.card Index)
    (realPositive realNegative uniformPositive uniformNegative
      sourceAdvantage positiveDefect negativeDefect uniformDefect : ℝ)
    (hpositive :
      |realPositive - aggregateAcceptance true response degree| ≤ positiveDefect)
    (hnegative :
      |realNegative - aggregateAcceptance false response degree| ≤ negativeDefect)
    (hsource :
      |(realPositive - realNegative) -
          (uniformPositive - uniformNegative)| ≤
        2 * sourceAdvantage)
    (huniform :
      |uniformPositive - uniformNegative| ≤ uniformDefect) :
    |signedHighDegreeSum response degree| ≤
      2 * aggregateNormalization Index degree * sourceAdvantage +
        aggregateNormalization Index degree *
          (positiveDefect + negativeDefect + uniformDefect) := by
  have hgap := idealGap_le_two_mul_source_add_compilerDefects
    (aggregateAcceptance true response degree)
    (aggregateAcceptance false response degree)
    realPositive realNegative uniformPositive uniformNegative
    sourceAdvantage positiveDefect negativeDefect uniformDefect
    hpositive hnegative hsource huniform
  have hnormalization : 0 ≤ aggregateNormalization Index degree :=
    Finset.sum_nonneg fun mask _ ↦
      positiveHighPassWeight_nonneg Index degree mask
  rw [signedHighDegreeSum_eq_aggregateNormalization_mul_gap
    response degree hdegree, abs_mul, abs_of_nonneg hnormalization]
  calc
    aggregateNormalization Index degree *
        |aggregateAcceptance true response degree -
          aggregateAcceptance false response degree| ≤
      aggregateNormalization Index degree *
        (2 * sourceAdvantage + positiveDefect + negativeDefect + uniformDefect) :=
      mul_le_mul_of_nonneg_left hgap hnormalization
    _ = 2 * aggregateNormalization Index degree * sourceAdvantage +
        aggregateNormalization Index degree *
          (positiveDefect + negativeDefect + uniformDefect) := by ring

/-- Exact polynomial normalization coefficient from the high-pass Jordan decomposition. -/
theorem two_mul_aggregateNormalization_le_one_add_sqrt_card
    (Index : Type) [Fintype Index] [DecidableEq Index] (degree : ℕ) :
    2 * aggregateNormalization Index degree ≤
      1 + Real.sqrt (boundedFrequencies Index degree).card := by
  have hbound :=
    aggregateNormalization_le_one_add_sqrt_card_div_two Index degree
  linarith

/-- Hard Theorem A with the normalization coefficient replaced by its explicit upper bound.
For fixed cutoff, the cardinality under the square root is the bounded-degree binomial sum. -/
theorem abs_signedHighDegreeSum_le_polynomialNormalization
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (response : BitVector Index → BitVector Index → ℝ)
    (degree : ℕ) (hdegree : degree < Fintype.card Index)
    (realPositive realNegative uniformPositive uniformNegative
      sourceAdvantage positiveDefect negativeDefect uniformDefect : ℝ)
    (hpositive :
      |realPositive - aggregateAcceptance true response degree| ≤ positiveDefect)
    (hnegative :
      |realNegative - aggregateAcceptance false response degree| ≤ negativeDefect)
    (hsource :
      |(realPositive - realNegative) -
          (uniformPositive - uniformNegative)| ≤
        2 * sourceAdvantage)
    (huniform :
      |uniformPositive - uniformNegative| ≤ uniformDefect) :
    |signedHighDegreeSum response degree| ≤
      (1 + Real.sqrt (boundedFrequencies Index degree).card) * sourceAdvantage +
        aggregateNormalization Index degree *
          (positiveDefect + negativeDefect + uniformDefect) := by
  have htail := abs_signedHighDegreeSum_le_of_completeViewCompiler
    response degree hdegree realPositive realNegative
    uniformPositive uniformNegative sourceAdvantage
    positiveDefect negativeDefect uniformDefect
    hpositive hnegative hsource huniform
  have hsourceNonneg : 0 ≤ sourceAdvantage := by
    have habs :
        0 ≤ |(realPositive - realNegative) -
          (uniformPositive - uniformNegative)| := abs_nonneg _
    linarith
  have hcoefficient :=
    two_mul_aggregateNormalization_le_one_add_sqrt_card Index degree
  have hscaled := mul_le_mul_of_nonneg_right hcoefficient hsourceNonneg
  linarith

/-! ## Distribution-aware constrained-batch composition -/

/-- Hard Theorem B's implication from a constrained compiler.

The algebraic factorization and complete joint error comparison occur only through the two branch
simulation bounds. This theorem does not assert that a suitable short factorization exists. -/
theorem constrainedBatchCompiler_advantage_le
    (targetOne targetZero realOne realZero uniformOne uniformZero
      sourceAdvantage factorizationDefect noiseDefect uniformDefect
      auxiliaryOne auxiliaryZero : ℝ)
    (hone :
      |realOne - targetOne| ≤
        factorizationDefect + noiseDefect + auxiliaryOne)
    (hzero :
      |realZero - targetZero| ≤
        factorizationDefect + noiseDefect + auxiliaryZero)
    (hsource :
      |(realOne - realZero) - (uniformOne - uniformZero)| ≤
        2 * sourceAdvantage)
    (huniform : |uniformOne - uniformZero| ≤ uniformDefect) :
    |targetOne - targetZero| ≤
      2 * sourceAdvantage +
        2 * factorizationDefect +
        2 * noiseDefect +
        uniformDefect +
        auxiliaryOne + auxiliaryZero := by
  have hbound := idealGap_le_two_mul_source_add_compilerDefects
    targetOne targetZero realOne realZero uniformOne uniformZero
    sourceAdvantage
    (factorizationDefect + noiseDefect + auxiliaryOne)
    (factorizationDefect + noiseDefect + auxiliaryZero)
    uniformDefect hone hzero hsource huniform
  linarith

/-! ## The short-preimage SIS witness -/

/-- A coefficient vector whose entries are all minus one, zero, or one. -/
def IsTernaryVector {Index : Type} (vector : Index → ℤ) : Prop :=
  ∀ index, vector index = -1 ∨ vector index = 0 ∨ vector index = 1

theorem abs_apply_le_one_of_isTernaryVector
    {Index : Type} {vector : Index → ℤ}
    (hvector : IsTernaryVector vector) (index : Index) :
    |vector index| ≤ 1 := by
  rcases hvector index with h | h | h <;> simp [h]

/-- Difference of preimages of a target and its scaled version. -/
def scaledKernelVector {Index : Type}
    (scale : ℕ) (first second : Index → ℤ) : Index → ℤ :=
  fun index ↦ (scale : ℤ) * first index - second index

/-- If the first ternary preimage is nonzero and the scale is at least two, the scaled difference
cannot vanish. -/
theorem scaledKernelVector_ne_zero
    {Index : Type} (scale : ℕ) (first second : Index → ℤ)
    (hscale : 2 ≤ scale)
    (hfirst : IsTernaryVector first)
    (hsecond : IsTernaryVector second)
    (hfirstNonzero : first ≠ 0) :
    scaledKernelVector scale first second ≠ 0 := by
  intro hkernel
  apply hfirstNonzero
  funext index
  change first index = 0
  have hcoordinate := congrFun hkernel index
  change (scale : ℤ) * first index - second index = 0 at hcoordinate
  have hscaleInt : (2 : ℤ) ≤ scale := by exact_mod_cast hscale
  rcases hfirst index with hleft | hleft | hleft
  · rcases hsecond index with hright | hright | hright
    · simp [hleft, hright] at hcoordinate
      omega
    · simp [hleft, hright] at hcoordinate
      omega
    · simp [hleft, hright] at hcoordinate
      omega
  · exact hleft
  · rcases hsecond index with hright | hright | hright
    · simp [hleft, hright] at hcoordinate
      omega
    · simp [hleft, hright] at hcoordinate
      omega
    · simp [hleft, hright] at hcoordinate
      omega

/-- The scaled difference has coefficient bound scale plus one. -/
theorem abs_scaledKernelVector_apply_le
    {Index : Type} (scale : ℕ) (first second : Index → ℤ)
    (hfirst : IsTernaryVector first)
    (hsecond : IsTernaryVector second)
    (index : Index) :
    |scaledKernelVector scale first second index| ≤ (scale : ℤ) + 1 := by
  have hfirstAbs := abs_apply_le_one_of_isTernaryVector hfirst index
  have hsecondAbs := abs_apply_le_one_of_isTernaryVector hsecond index
  have hscaleNonneg : (0 : ℤ) ≤ scale := Int.natCast_nonneg scale
  calc
    |scaledKernelVector scale first second index| =
        |(scale : ℤ) * first index - second index| := rfl
    _ ≤ |(scale : ℤ) * first index| + |second index| := abs_sub _ _
    _ = (scale : ℤ) * |first index| + |second index| := by
      rw [abs_mul, abs_of_nonneg hscaleNonneg]
    _ ≤ (scale : ℤ) * 1 + 1 :=
      add_le_add
        (mul_le_mul_of_nonneg_left hfirstAbs hscaleNonneg)
        hsecondAbs
    _ = (scale : ℤ) + 1 := by ring

/-- Two scaled ternary preimages produce a nonzero bounded vector in the kernel of the public
linear map. This is the precise SIS obstruction used by the constrained-batch route. -/
theorem scaledTernaryPreimages_yield_shortKernel
    {Index Target : Type} [AddCommGroup Target]
    (publicMap : (Index → ℤ) →+ Target)
    (target : Target) (scale : ℕ) (first second : Index → ℤ)
    (hscale : 2 ≤ scale)
    (hfirst : IsTernaryVector first)
    (hsecond : IsTernaryVector second)
    (hfirstNonzero : first ≠ 0)
    (hfirstImage : publicMap first = target)
    (hsecondImage : publicMap second = scale • target) :
    let kernel := scaledKernelVector scale first second
    kernel ≠ 0 ∧ publicMap kernel = 0 ∧
      ∀ index, |kernel index| ≤ (scale : ℤ) + 1 := by
  let kernel := scaledKernelVector scale first second
  have hkernelForm :
      kernel = scale • first - second := by
    funext index
    simp [kernel, scaledKernelVector]
  have hkernelForm' :
      scaledKernelVector scale first second =
        scale • first - second := by
    simpa [kernel] using hkernelForm
  refine ⟨scaledKernelVector_ne_zero scale first second hscale
      hfirst hsecond hfirstNonzero, ?_, ?_⟩
  · rw [hkernelForm', map_sub, map_nsmul, hfirstImage, hsecondImage]
    exact sub_self (scale • target)
  · exact abs_scaledKernelVector_apply_le scale first second hfirst hsecond

/-! ## Approximate prefix recovery forces half-Renyi concentration -/

/-- Leakage marginal of an arbitrary finite joint mass table. -/
def leakageMarginalMass
    {Prefix Leakage : Type} [Fintype Prefix]
    (jointMass : Prefix → Leakage → ℝ) (leakageValue : Leakage) : ℝ :=
  ∑ keyValue, jointMass keyValue leakageValue

/-- Joint mass on which a deterministic decoder recovers the prefix. -/
def decoderSuccessMass
    {Prefix Leakage : Type} [Fintype Leakage]
    (jointMass : Prefix → Leakage → ℝ) (decoder : Leakage → Prefix) : ℝ :=
  ∑ leakageValue, jointMass (decoder leakageValue) leakageValue

/-- Half-Renyi concentration of the leakage marginal, written for a generic finite joint table. -/
def halfRenyiJointMass
    {Prefix Leakage : Type} [Fintype Prefix] [Fintype Leakage]
    (jointMass : Prefix → Leakage → ℝ) : ℝ :=
  (∑ leakageValue, Real.sqrt (leakageMarginalMass jointMass leakageValue)) ^ 2

/-- If every correctly decoded joint atom has mass at most the reciprocal prefix cardinality,
decoder success forces the corresponding half-Renyi concentration. -/
theorem card_mul_decoderSuccessMass_sq_le_halfRenyiJointMass
    {Prefix Leakage : Type} [Fintype Prefix] [Fintype Leakage]
    (jointMass : Prefix → Leakage → ℝ) (decoder : Leakage → Prefix)
    (hmass : ∀ keyValue leakageValue, 0 ≤ jointMass keyValue leakageValue)
    (hcap : ∀ leakageValue,
      (Fintype.card Prefix : ℝ) *
          jointMass (decoder leakageValue) leakageValue ≤ 1) :
    (Fintype.card Prefix : ℝ) *
        decoderSuccessMass jointMass decoder ^ 2 ≤
      halfRenyiJointMass jointMass := by
  classical
  let prefixCard : ℝ := Fintype.card Prefix
  have hprefixCard : 0 ≤ prefixCard := by
    simp [prefixCard]
  have hpoint : ∀ leakageValue,
      Real.sqrt prefixCard *
          jointMass (decoder leakageValue) leakageValue ≤
        Real.sqrt (leakageMarginalMass jointMass leakageValue) := by
    intro leakageValue
    let selectedMass := jointMass (decoder leakageValue) leakageValue
    let marginalMass := leakageMarginalMass jointMass leakageValue
    have hselected : 0 ≤ selectedMass :=
      hmass (decoder leakageValue) leakageValue
    have hmarginal : 0 ≤ marginalMass := by
      exact Finset.sum_nonneg fun keyValue _ ↦ hmass keyValue leakageValue
    have hselectedLe : selectedMass ≤ marginalMass := by
      unfold selectedMass marginalMass leakageMarginalMass
      exact Finset.single_le_sum
        (fun keyValue _ ↦ hmass keyValue leakageValue)
        (Finset.mem_univ (decoder leakageValue))
    have hscaledSelected : prefixCard * selectedMass ≤ 1 := by
      simpa [prefixCard, selectedMass] using hcap leakageValue
    have hquadratic : prefixCard * selectedMass ^ 2 ≤ marginalMass := by
      calc
        prefixCard * selectedMass ^ 2 =
            (prefixCard * selectedMass) * selectedMass := by ring
        _ ≤ 1 * selectedMass :=
          mul_le_mul_of_nonneg_right hscaledSelected hselected
        _ = selectedMass := one_mul _
        _ ≤ marginalMass := hselectedLe
    apply Real.le_sqrt_of_sq_le
    calc
      (Real.sqrt prefixCard * selectedMass) ^ 2 =
          prefixCard * selectedMass ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hprefixCard]
      _ ≤ marginalMass := hquadratic
  have hsum :
      Real.sqrt prefixCard * decoderSuccessMass jointMass decoder ≤
        ∑ leakageValue,
          Real.sqrt (leakageMarginalMass jointMass leakageValue) := by
    calc
      Real.sqrt prefixCard * decoderSuccessMass jointMass decoder =
          ∑ leakageValue,
            Real.sqrt prefixCard *
              jointMass (decoder leakageValue) leakageValue := by
        simp [decoderSuccessMass, Finset.mul_sum]
      _ ≤ ∑ leakageValue,
          Real.sqrt (leakageMarginalMass jointMass leakageValue) :=
        Finset.sum_le_sum fun leakageValue _ ↦ hpoint leakageValue
  have hsuccessNonneg : 0 ≤ decoderSuccessMass jointMass decoder := by
    exact Finset.sum_nonneg fun leakageValue _ ↦
      hmass (decoder leakageValue) leakageValue
  have hleftNonneg :
      0 ≤ Real.sqrt prefixCard * decoderSuccessMass jointMass decoder :=
    mul_nonneg (Real.sqrt_nonneg _) hsuccessNonneg
  have hsquare := mul_self_le_mul_self hleftNonneg hsum
  calc
    (Fintype.card Prefix : ℝ) *
        decoderSuccessMass jointMass decoder ^ 2 =
      (Real.sqrt prefixCard * decoderSuccessMass jointMass decoder) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hprefixCard]
    _ ≤
      (∑ leakageValue,
        Real.sqrt (leakageMarginalMass jointMass leakageValue)) ^ 2 := by
      simpa only [pow_two] using hsquare
    _ = halfRenyiJointMass jointMass := rfl

/-- Uniform prefix marginal implies the atom cap required by the decoder-concentration theorem. -/
theorem card_mul_decoderSuccessMass_sq_le_halfRenyiJointMass_of_uniformPrefix
    {Prefix Leakage : Type} [Fintype Prefix] [Nonempty Prefix] [Fintype Leakage]
    (jointMass : Prefix → Leakage → ℝ) (decoder : Leakage → Prefix)
    (hmass : ∀ keyValue leakageValue, 0 ≤ jointMass keyValue leakageValue)
    (hprefix : ∀ keyValue,
      (∑ leakageValue, jointMass keyValue leakageValue) =
        1 / (Fintype.card Prefix : ℝ)) :
    (Fintype.card Prefix : ℝ) *
        decoderSuccessMass jointMass decoder ^ 2 ≤
      halfRenyiJointMass jointMass := by
  classical
  have hcardPos : (0 : ℝ) < Fintype.card Prefix := by
    exact_mod_cast Fintype.card_pos
  apply card_mul_decoderSuccessMass_sq_le_halfRenyiJointMass
    jointMass decoder hmass
  intro leakageValue
  have hatom :
      jointMass (decoder leakageValue) leakageValue ≤
        ∑ candidate, jointMass (decoder leakageValue) candidate :=
    Finset.single_le_sum
      (fun candidate _ ↦ hmass (decoder leakageValue) candidate)
      (Finset.mem_univ leakageValue)
  calc
    (Fintype.card Prefix : ℝ) *
        jointMass (decoder leakageValue) leakageValue ≤
      (Fintype.card Prefix : ℝ) *
        ∑ candidate, jointMass (decoder leakageValue) candidate :=
      mul_le_mul_of_nonneg_left hatom hcardPos.le
    _ = (Fintype.card Prefix : ℝ) *
        (1 / (Fintype.card Prefix : ℝ)) := by
      rw [hprefix]
    _ = 1 := by field_simp [ne_of_gt hcardPos]

/-- If the decoder succeeds with mass at least one minus failure, the concentration is at least
the prefix cardinality times the square of one minus failure. For a uniform binary prefix this is
the note's two-to-the-prefix-size factor. -/
theorem card_mul_one_sub_failure_sq_le_halfRenyiJointMass_of_uniformPrefix
    {Prefix Leakage : Type} [Fintype Prefix] [Nonempty Prefix] [Fintype Leakage]
    (jointMass : Prefix → Leakage → ℝ) (decoder : Leakage → Prefix)
    (failure : ℝ)
    (hmass : ∀ keyValue leakageValue, 0 ≤ jointMass keyValue leakageValue)
    (hprefix : ∀ keyValue,
      (∑ leakageValue, jointMass keyValue leakageValue) =
        1 / (Fintype.card Prefix : ℝ))
    (hfailure : 0 ≤ 1 - failure)
    (hsuccess :
      1 - failure ≤ decoderSuccessMass jointMass decoder) :
    (Fintype.card Prefix : ℝ) * (1 - failure) ^ 2 ≤
      halfRenyiJointMass jointMass := by
  have hdecoder :=
    card_mul_decoderSuccessMass_sq_le_halfRenyiJointMass_of_uniformPrefix
      jointMass decoder hmass hprefix
  have hsquare :
      (1 - failure) ^ 2 ≤ decoderSuccessMass jointMass decoder ^ 2 := by
    have hmul := mul_self_le_mul_self hfailure hsuccess
    simpa only [pow_two] using hmul
  have hcardNonneg : (0 : ℝ) ≤ Fintype.card Prefix := by positivity
  exact (mul_le_mul_of_nonneg_left hsquare hcardNonneg).trans hdecoder

/-! ## Hidden dual-mode composition -/

/-- Hard Theorem C's complete hybrid chain.

The central bound includes the total finite-sampler comparison cost. The hidden witness does not
occur in this scalar composition theorem; using it to construct either public compiled view would
require an additional premise. -/
theorem hiddenModeComposition_advantage_le
    (viewOne ordinaryOne lossyOne lossyZero ordinaryZero viewZero
      compilationOne modeOne lossiness modeZero compilationZero samplerDefect : ℝ)
    (hcompilationOne : |viewOne - ordinaryOne| ≤ compilationOne)
    (hmodeOne : |ordinaryOne - lossyOne| ≤ modeOne)
    (hlossiness :
      |lossyOne - lossyZero| ≤ lossiness + samplerDefect)
    (hmodeZero : |lossyZero - ordinaryZero| ≤ modeZero)
    (hcompilationZero : |ordinaryZero - viewZero| ≤ compilationZero) :
    |viewOne - viewZero| ≤
      compilationOne + modeOne + lossiness + modeZero +
        compilationZero + samplerDefect := by
  have hfirst := abs_sub_le viewOne ordinaryOne viewZero
  have hsecond := abs_sub_le ordinaryOne lossyOne viewZero
  have hthird := abs_sub_le lossyOne lossyZero viewZero
  have hfourth := abs_sub_le lossyZero ordinaryZero viewZero
  linarith

/-! ## Support-sensitive combined theorem -/

/-- Combined form of Hard Theorem A: exact support-sensitive leakage removal, the one-shot
complete-view aggregate reduction, and the independent-message endpoint. -/
theorem jointSecurity_le_supportSum_add_completeViewCompiler
    {Index View : Type} [Fintype Index] [DecidableEq Index]
    [SampleableType (BitVector Index)] [Fintype View]
    (channel : CompleteChannel Index View) (response : View → ℝ)
    (degree : ℕ) (hdegree : degree < Fintype.card Index) (delta : ℝ)
    (certificate : LowDegreeAffineSourceCertificate channel response degree delta)
    (realPositive realNegative uniformPositive uniformNegative
      sourceAdvantage positiveDefect negativeDefect uniformDefect
      endpoint endpointBound : ℝ)
    (hpositive :
      |realPositive -
        aggregateAcceptance true
          (completeChannelResponse channel response) degree| ≤ positiveDefect)
    (hnegative :
      |realNegative -
        aggregateAcceptance false
          (completeChannelResponse channel response) degree| ≤ negativeDefect)
    (hsource :
      |(realPositive - realNegative) -
          (uniformPositive - uniformNegative)| ≤
        2 * sourceAdvantage)
    (huniform :
      |uniformPositive - uniformNegative| ≤ uniformDefect)
    (hendpoint : endpoint ≤ endpointBound) :
    |diagonalMean (completeChannelResponse channel response) -
        independentMean (completeChannelResponse channel response)| + endpoint ≤
      (∑ cardinality ∈ Finset.Icc 1 degree,
        (Nat.choose (Fintype.card Index) cardinality : ℝ) *
          Real.sqrt ((2 : ℝ) ^ (cardinality + 1) * delta)) +
        2 * aggregateNormalization Index degree * sourceAdvantage +
        aggregateNormalization Index degree *
          (positiveDefect + negativeDefect + uniformDefect) +
        endpointBound := by
  have haggregate := idealGap_le_two_mul_source_add_compilerDefects
    (aggregateAcceptance true
      (completeChannelResponse channel response) degree)
    (aggregateAcceptance false
      (completeChannelResponse channel response) degree)
    realPositive realNegative uniformPositive uniformNegative
    sourceAdvantage positiveDefect negativeDefect uniformDefect
    hpositive hnegative hsource huniform
  have hbase := diagonalGap_add_endpoint_le_binomialSupportBounds
    (completeChannelResponse channel response) degree hdegree
    (fun cardinality ↦
      Real.sqrt ((2 : ℝ) ^ (cardinality + 1) * delta))
    (2 * sourceAdvantage + positiveDefect + negativeDefect + uniformDefect)
    endpoint endpointBound
    (supportSizeLowFrequencyBound_of_certificate certificate)
    haggregate hendpoint
  calc
    |diagonalMean (completeChannelResponse channel response) -
          independentMean (completeChannelResponse channel response)| + endpoint ≤
        (∑ cardinality ∈ Finset.Icc 1 degree,
          (Nat.choose (Fintype.card Index) cardinality : ℝ) *
            Real.sqrt ((2 : ℝ) ^ (cardinality + 1) * delta)) +
          aggregateNormalization Index degree *
            (2 * sourceAdvantage + positiveDefect + negativeDefect + uniformDefect) +
          endpointBound := hbase
    _ = _ := by ring

/-- The combined theorem with the source coefficient exposed through the exact polynomial
normalization bound. -/
theorem jointSecurity_le_supportSum_add_polynomialSourceLoss
    {Index View : Type} [Fintype Index] [DecidableEq Index]
    [SampleableType (BitVector Index)] [Fintype View]
    (channel : CompleteChannel Index View) (response : View → ℝ)
    (degree : ℕ) (hdegree : degree < Fintype.card Index) (delta : ℝ)
    (certificate : LowDegreeAffineSourceCertificate channel response degree delta)
    (realPositive realNegative uniformPositive uniformNegative
      sourceAdvantage positiveDefect negativeDefect uniformDefect
      endpoint endpointBound : ℝ)
    (hpositive :
      |realPositive -
        aggregateAcceptance true
          (completeChannelResponse channel response) degree| ≤ positiveDefect)
    (hnegative :
      |realNegative -
        aggregateAcceptance false
          (completeChannelResponse channel response) degree| ≤ negativeDefect)
    (hsource :
      |(realPositive - realNegative) -
          (uniformPositive - uniformNegative)| ≤
        2 * sourceAdvantage)
    (huniform :
      |uniformPositive - uniformNegative| ≤ uniformDefect)
    (hendpoint : endpoint ≤ endpointBound) :
    |diagonalMean (completeChannelResponse channel response) -
        independentMean (completeChannelResponse channel response)| + endpoint ≤
      (∑ cardinality ∈ Finset.Icc 1 degree,
        (Nat.choose (Fintype.card Index) cardinality : ℝ) *
          Real.sqrt ((2 : ℝ) ^ (cardinality + 1) * delta)) +
        (1 + Real.sqrt (boundedFrequencies Index degree).card) * sourceAdvantage +
        aggregateNormalization Index degree *
          (positiveDefect + negativeDefect + uniformDefect) +
        endpointBound := by
  have hbase := jointSecurity_le_supportSum_add_completeViewCompiler
    channel response degree hdegree delta certificate
    realPositive realNegative uniformPositive uniformNegative
    sourceAdvantage positiveDefect negativeDefect uniformDefect endpoint endpointBound
    hpositive hnegative hsource huniform hendpoint
  have hsourceNonneg : 0 ≤ sourceAdvantage := by
    have habs :
        0 ≤ |(realPositive - realNegative) -
          (uniformPositive - uniformNegative)| := abs_nonneg _
    linarith
  have hcoefficient :=
    two_mul_aggregateNormalization_le_one_add_sqrt_card Index degree
  have hscaled := mul_le_mul_of_nonneg_right hcoefficient hsourceNonneg
  linarith

end

end FormalProof4FHE.TFHE.NativeTRGSWHardTheoremComposition
