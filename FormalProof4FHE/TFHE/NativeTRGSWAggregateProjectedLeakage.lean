/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeTRGSWAggregateConcreteChannel

/-!
# Projected leakage and the native-TRGSW aggregate barrier

This module formalizes the additional results in `sketch/trgswaggregate.md`.

The first part packages the generic two-copy leakage-removal theorem for an arbitrary deterministic
projection of the complete key.  It also proves the approximate uniform-source-erasure variant and
an exact witness showing that the weighted diagonal Cauchy--Schwarz factor is sharp.

The second part studies the canonical aggregate mask laws.  Common translation invariance of their
positive and negative Jordan laws forces every high-degree Walsh character of the translation to
be one.  For cutoff at most two below the dimension this makes the translation zero.  Consequently,
any exact phase-oblivious plaintext builder must separate every binary prefix.  The final finite
probability theorem turns such recovery into the lower bound `2 ^ card Index` on the Renyi-half
concentration of the projected leakage.  At the exceptional cutoff one below the dimension, the
surviving full-parity bit instead gives the exact residual lower bound `2`.

The module does not postulate a nonlinear zero-row simulator, a synthesized KSK, or a trapdoor.
Those are precisely the cryptographic alternatives not covered by the translation-only barrier.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.NativeTRGSWAggregateProjectedLeakage

noncomputable section

open NativeTRGSWBarrierAndSpectralBoundary
open NativeTRGSWAggregateSecurityAndComplexityLeveraging
open NativeTRGSWAggregateConcreteChannel
open RGSWCoefficientCircularSecurity

/-! ## Exact known-message construction from zero rows -/

/-- Public gadget translation turns a homogeneous zero-row batch into the native known-message
TGSW batch, preserving the source error vector exactly.  The shifted mask matrix simultaneously
accounts for the native nonce rows. -/
theorem addKnownGadgetToZeroRows
    {R : Type} [Ring R] {dimension levels : ℕ}
    (secret : Fin dimension → R)
    (challenge : Matrix (Fin dimension) (Fin (TGSW.rowCount dimension levels)) R)
    (error : Fin (TGSW.rowCount dimension levels) → R)
    (gadget : Fin levels → R) (message : R) :
    TGSW.addGadget gadget message
        (challenge, Matrix.vecMul secret challenge + error) =
      TLWE.batchAssemble secret
        (TGSW.shiftChallenge (dimension := dimension) gadget message challenge)
        (TGSW.gadgetPhase secret gadget message) error := by
  exact TGSW.addGadget_homogeneous secret challenge error gadget message

/-- On a uniform complete zero-row source, any two fixed known-message translations have exactly
the same law.  This is the finite uniform-source sign-erasure identity used by the aggregate
builder. -/
theorem knownMessageTranslations_uniform_evalDist_eq
    {R : Type} [Ring R] [Fintype R] [SampleableType R] {levels : ℕ}
    (gadget : Fin levels → R) (firstMessage secondMessage : R) :
    evalDist
        (TGSW.addGadget gadget firstMessage <$>
          ($ᵗ (RGSWChallenge R levels))) =
      evalDist
        (TGSW.addGadget gadget secondMessage <$>
          ($ᵗ (RGSWChallenge R levels))) := by
  calc
    _ = evalDist ($ᵗ (RGSWChallenge R levels)) :=
      addGadget_uniform_evalDist gadget firstMessage
    _ = _ := (addGadget_uniform_evalDist gadget secondMessage).symm

/-! ## Projected-leakage match-and-square -/

/-- Genuine diagonal aggregate advantage when only deterministic leakage is supplied to the
builder. -/
def projectedAggregateAdvantage
    {Key Leakage : Type} (keySampler : ProbComp Key) (leakage : Key → Leakage)
    (plus minus : Leakage → Key → ProbComp Bool) : ℝ :=
  leakedAdvantage keySampler leakage plus minus

/-- Two-copy source advantage after independently sampling a fake leakage value. -/
def projectedMatchSquareAdvantage
    {Key Leakage : Type} (keySampler : ProbComp Key)
    (fakeLeakageSampler : ProbComp Leakage)
    (plus minus : Leakage → Key → ProbComp Bool) : ℝ :=
  leakageRemovalAdvantage keySampler fakeLeakageSampler plus minus

/-- Order-`1/2` concentration of the projected key law. -/
def projectedLeakageConcentration
    {Key Leakage : Type} [Fintype Leakage]
    (keySampler : ProbComp Key) (leakage : Key → Leakage) : ℝ :=
  halfRenyiConcentration (leakageLaw keySampler leakage)

theorem projectedLeakageConcentration_nonneg
    {Key Leakage : Type} [Fintype Leakage]
    (keySampler : ProbComp Key) (leakage : Key → Leakage) :
    0 ≤ projectedLeakageConcentration keySampler leakage := by
  exact sq_nonneg _

/-- The projected-leakage form of match-and-square.  The fake leakage law is the square-root tilt
of the actual leakage marginal; realizability of that exact law remains an explicit premise. -/
theorem projectedAggregateAdvantage_le_sqrt_matchSquare
    {Key Leakage : Type} [Fintype Key] [Fintype Leakage]
    (keySampler : ProbComp Key) (fakeLeakageSampler : ProbComp Leakage)
    (leakage : Key → Leakage)
    (plus minus : Leakage → Key → ProbComp Bool)
    (hcover : ∀ key, probabilityMass keySampler key ≠ 0 →
      probabilityMass fakeLeakageSampler (leakage key) ≠ 0)
    (hoptimized : ∀ value,
      probabilityMass fakeLeakageSampler value =
        Real.sqrt (probabilityMass (leakageLaw keySampler leakage) value) /
          halfRenyiNormalizer keySampler leakage) :
    projectedAggregateAdvantage keySampler leakage plus minus ≤
      Real.sqrt (2 * projectedLeakageConcentration keySampler leakage *
        projectedMatchSquareAdvantage keySampler fakeLeakageSampler plus minus) := by
  unfold projectedAggregateAdvantage projectedLeakageConcentration
    projectedMatchSquareAdvantage
  rw [← leakageGamma_eq_halfRenyiConcentration_of_optimizedLaw
    keySampler fakeLeakageSampler leakage hoptimized]
  exact leakedAdvantage_le_sqrt_two_mul_gamma_mul_removal
    keySampler fakeLeakageSampler leakage plus minus hcover

/-- Projected diagonal construction with explicit complete-view defects and a source bound. -/
theorem nativeProjectedAggregateGap_le_defects_add_sqrt
    {Key Leakage : Type} [Fintype Key] [Fintype Leakage]
    (keySampler : ProbComp Key) (fakeLeakageSampler : ProbComp Leakage)
    (leakage : Key → Leakage)
    (plus minus : Leakage → Key → ProbComp Bool)
    (nativeAggregateGap sigmaPlus sigmaMinus sourceBound : ℝ)
    (hdiagonal : nativeAggregateGap ≤ sigmaPlus + sigmaMinus +
      projectedAggregateAdvantage keySampler leakage plus minus)
    (hsource : projectedMatchSquareAdvantage
      keySampler fakeLeakageSampler plus minus ≤ sourceBound)
    (hcover : ∀ key, probabilityMass keySampler key ≠ 0 →
      probabilityMass fakeLeakageSampler (leakage key) ≠ 0)
    (hoptimized : ∀ value,
      probabilityMass fakeLeakageSampler value =
        Real.sqrt (probabilityMass (leakageLaw keySampler leakage) value) /
          halfRenyiNormalizer keySampler leakage) :
    nativeAggregateGap ≤ sigmaPlus + sigmaMinus +
      Real.sqrt (2 * projectedLeakageConcentration keySampler leakage * sourceBound) := by
  have hmatch := projectedAggregateAdvantage_le_sqrt_matchSquare
    keySampler fakeLeakageSampler leakage plus minus hcover hoptimized
  have hconcentration := projectedLeakageConcentration_nonneg keySampler leakage
  have hradicand :
      2 * projectedLeakageConcentration keySampler leakage *
          projectedMatchSquareAdvantage keySampler fakeLeakageSampler plus minus ≤
        2 * projectedLeakageConcentration keySampler leakage * sourceBound := by
    exact mul_le_mul_of_nonneg_left hsource
      (mul_nonneg (by norm_num) hconcentration)
  calc
    nativeAggregateGap ≤ sigmaPlus + sigmaMinus +
        projectedAggregateAdvantage keySampler leakage plus minus := hdiagonal
    _ ≤ sigmaPlus + sigmaMinus +
        Real.sqrt (2 * projectedLeakageConcentration keySampler leakage *
          projectedMatchSquareAdvantage keySampler fakeLeakageSampler plus minus) := by
      gcongr
    _ ≤ sigmaPlus + sigmaMinus +
        Real.sqrt (2 * projectedLeakageConcentration keySampler leakage * sourceBound) := by
      gcongr

/-! ## Approximate uniform-source erasure -/

/-- Scalar second-moment form of the approximate-erasure calculation.  The hypotheses say that
the source game changes the real and uniform squared gaps by at most `2 * sourceAdvantage`, and
that the uniform signed gap is at most `uniformGap` in absolute value. -/
theorem approximateErasure_secondMoment_le
    (realSecondMoment uniformSignedGap sourceAdvantage uniformGap : ℝ)
    (hsource : |realSecondMoment - uniformSignedGap ^ 2| ≤ 2 * sourceAdvantage)
    (herasure : |uniformSignedGap| ≤ uniformGap) :
    realSecondMoment ≤ 2 * sourceAdvantage + uniformGap ^ 2 := by
  have hgapSq : uniformSignedGap ^ 2 ≤ uniformGap ^ 2 := by
    have huniformGap : 0 ≤ uniformGap := (abs_nonneg uniformSignedGap).trans herasure
    rw [sq_le_sq]
    simpa [abs_of_nonneg huniformGap] using herasure
  have hsourceOneSide :
      realSecondMoment - uniformSignedGap ^ 2 ≤ 2 * sourceAdvantage :=
    (le_abs_self (realSecondMoment - uniformSignedGap ^ 2)).trans hsource
  linarith

/-- Approximate uniform-source sign erasure contributes inside the square root as
`concentration * uniformGap^2`, exactly as in the sketch. -/
theorem nativeAggregateGap_le_of_approximateErasure
    (nativeAggregateGap sigmaPlus sigmaMinus concentration
      realSecondMoment uniformSignedGap sourceAdvantage uniformGap : ℝ)
    (hconcentration : 0 ≤ concentration)
    (hdiagonal : nativeAggregateGap ≤ sigmaPlus + sigmaMinus +
      Real.sqrt (concentration * realSecondMoment))
    (hsource : |realSecondMoment - uniformSignedGap ^ 2| ≤ 2 * sourceAdvantage)
    (herasure : |uniformSignedGap| ≤ uniformGap) :
    nativeAggregateGap ≤ sigmaPlus + sigmaMinus +
      Real.sqrt (concentration * (2 * sourceAdvantage + uniformGap ^ 2)) := by
  have hmoment := approximateErasure_secondMoment_le
    realSecondMoment uniformSignedGap sourceAdvantage uniformGap hsource herasure
  calc
    nativeAggregateGap ≤ sigmaPlus + sigmaMinus +
        Real.sqrt (concentration * realSecondMoment) := hdiagonal
    _ ≤ sigmaPlus + sigmaMinus +
        Real.sqrt (concentration * (2 * sourceAdvantage + uniformGap ^ 2)) := by
      gcongr

/-! ## Exact sharpness witness for the diagonal norm -/

/-- The extremizing direction in the weighted diagonal Cauchy--Schwarz inequality. -/
def inverseWeightWitness {A : Type} (constant : ℝ) (weight : A → ℝ) : A → ℝ :=
  fun value ↦ constant / weight value

theorem sum_weighted_inverseWeightWitness
    {A : Type} [Fintype A]
    (p weight : A → ℝ) (constant : ℝ)
    (hweight : ∀ value, weight value ≠ 0) :
    (∑ value, p value * inverseWeightWitness constant weight value) =
      constant * ∑ value, p value / weight value := by
  classical
  unfold inverseWeightWitness
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro value _
  field_simp [hweight value]

theorem sum_weighted_sq_inverseWeightWitness
    {A : Type} [Fintype A]
    (p weight : A → ℝ) (constant : ℝ)
    (hweight : ∀ value, weight value ≠ 0) :
    (∑ value, p value * weight value *
      inverseWeightWitness constant weight value ^ 2) =
      constant ^ 2 * ∑ value, p value / weight value := by
  classical
  unfold inverseWeightWitness
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro value _
  field_simp [hweight value]

/-- Exact saturation of the weighted diagonal Cauchy--Schwarz bound.  Together with
`weighted_diagonal_cauchy`, this proves the claimed operator norm; the nonzero constant can be
scaled arbitrarily to enforce any desired pointwise bound on the witness. -/
theorem weighted_diagonal_cauchy_inverseWeightWitness_eq
    {A : Type} [Fintype A]
    (p weight : A → ℝ) (constant : ℝ)
    (hweight : ∀ value, weight value ≠ 0) :
    (∑ value, p value * inverseWeightWitness constant weight value) ^ 2 =
      (∑ value, p value / weight value) *
        ∑ value, p value * weight value *
          inverseWeightWitness constant weight value ^ 2 := by
  rw [sum_weighted_inverseWeightWitness p weight constant hweight,
    sum_weighted_sq_inverseWeightWitness p weight constant hweight]
  ring

/-- Rayleigh quotient of the diagonal functional in the weighted second-moment norm. -/
def diagonalFunctionalRatio
    {A : Type} [Fintype A] (p weight delta : A → ℝ) : ℝ :=
  (∑ value, p value * delta value) ^ 2 /
    ∑ value, p value * weight value * delta value ^ 2

/-- The inverse-weight witness attains the exact factor `sum p/weight` whenever that factor is
nonzero. -/
theorem diagonalFunctionalRatio_inverseWeightWitness_eq
    {A : Type} [Fintype A]
    (p weight : A → ℝ)
    (hweight : ∀ value, weight value ≠ 0)
    (hfactor : (∑ value, p value / weight value) ≠ 0) :
    diagonalFunctionalRatio p weight (inverseWeightWitness 1 weight) =
      ∑ value, p value / weight value := by
  unfold diagonalFunctionalRatio
  rw [sum_weighted_inverseWeightWitness p weight 1 hweight,
    sum_weighted_sq_inverseWeightWitness p weight 1 hweight]
  simp only [one_mul, one_pow]
  field_simp [hfactor]

/-- No direction with positive weighted second moment exceeds the diagonal factor. -/
theorem diagonalFunctionalRatio_le_sum_div
    {A : Type} [Fintype A]
    (p weight delta : A → ℝ)
    (hp : ∀ value, 0 ≤ p value)
    (hweightNonneg : ∀ value, 0 ≤ weight value)
    (hcover : ∀ value, p value ≠ 0 → weight value ≠ 0)
    (hsecond : 0 < ∑ value, p value * weight value * delta value ^ 2) :
    diagonalFunctionalRatio p weight delta ≤
      ∑ value, p value / weight value := by
  rw [diagonalFunctionalRatio, div_le_iff₀ hsecond]
  simpa [mul_comm] using
    (weighted_diagonal_cauchy p weight delta hp hweightNonneg hcover)

/-! ## Deterministic processing cannot increase Renyi-half concentration -/

theorem probabilityMass_map_eq_sum_ite
    {Input Output : Type} [Fintype Input] [DecidableEq Output]
    (sampler : ProbComp Input) (transform : Input → Output) (output : Output) :
    probabilityMass (transform <$> sampler) output =
      ∑ input, if output = transform input then probabilityMass sampler input else 0 := by
  classical
  unfold probabilityMass
  calc
    Pr[= output | transform <$> sampler].toReal =
        (∑ input : Input,
          if output = transform input then Pr[= input | sampler] else 0).toReal := by
      rw [probOutput_map_eq_sum_fintype_ite]
    _ = ∑ input : Input,
          (if output = transform input then Pr[= input | sampler] else 0).toReal := by
      rw [ENNReal.toReal_sum]
      intro input _
      split <;> simp [probOutput_ne_top]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro input _
      split <;> simp

theorem sqrt_add_le_add_sqrt (left right : ℝ)
    (hleft : 0 ≤ left) (hright : 0 ≤ right) :
    Real.sqrt (left + right) ≤ Real.sqrt left + Real.sqrt right := by
  rw [Real.sqrt_le_iff]
  constructor
  · positivity
  · nlinarith [Real.sq_sqrt hleft, Real.sq_sqrt hright,
      mul_nonneg (Real.sqrt_nonneg left) (Real.sqrt_nonneg right)]

theorem sqrt_sum_le_sum_sqrt_nonneg
    {A : Type} [DecidableEq A] (support : Finset A) (weight : A → ℝ)
    (hweight : ∀ value ∈ support, 0 ≤ weight value) :
    Real.sqrt (∑ value ∈ support, weight value) ≤
      ∑ value ∈ support, Real.sqrt (weight value) := by
  classical
  induction support using Finset.induction_on with
  | empty => simp
  | @insert value support hnotmem ih =>
      rw [Finset.sum_insert hnotmem, Finset.sum_insert hnotmem]
      apply (sqrt_add_le_add_sqrt (weight value)
        (∑ candidate ∈ support, weight candidate)
        (hweight value (by simp))
        (Finset.sum_nonneg fun candidate hcandidate ↦
          hweight candidate (by simp [hcandidate]))).trans
      gcongr
      exact ih (fun candidate hcandidate ↦
        hweight candidate (by simp [hcandidate]))

/-- Renyi-half concentration is monotone under deterministic coarsening. -/
theorem halfRenyiConcentration_map_le
    {Input Output : Type} [Fintype Input] [Fintype Output]
    [DecidableEq Input] [DecidableEq Output]
    (sampler : ProbComp Input) (transform : Input → Output) :
    halfRenyiConcentration (transform <$> sampler) ≤
      halfRenyiConcentration sampler := by
  classical
  let inputMass : Input → ℝ := probabilityMass sampler
  have hfiber (output : Output) :
      Real.sqrt (probabilityMass (transform <$> sampler) output) ≤
        ∑ input : Input,
          if output = transform input then Real.sqrt (inputMass input) else 0 := by
    rw [probabilityMass_map_eq_sum_ite]
    calc
      Real.sqrt (∑ input : Input,
          if output = transform input then probabilityMass sampler input else 0) ≤
          ∑ input : Input,
            Real.sqrt (if output = transform input then
              probabilityMass sampler input else 0) := by
        simpa using
          (sqrt_sum_le_sum_sqrt_nonneg (Finset.univ : Finset Input)
            (fun input ↦ if output = transform input then
              probabilityMass sampler input else 0)
            (fun input _ ↦ by split <;> simp [probabilityMass_nonneg]))
      _ = _ := by
        apply Finset.sum_congr rfl
        intro input _
        split <;> simp [inputMass]
  have hnormalizer :
      (∑ output : Output,
        Real.sqrt (probabilityMass (transform <$> sampler) output)) ≤
        ∑ input : Input, Real.sqrt (probabilityMass sampler input) := by
    calc
      _ ≤ ∑ output : Output, ∑ input : Input,
          if output = transform input then Real.sqrt (inputMass input) else 0 :=
        Finset.sum_le_sum fun output _ ↦ hfiber output
      _ = ∑ input : Input, ∑ output : Output,
          if output = transform input then Real.sqrt (inputMass input) else 0 := by
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro input _
        simp [inputMass]
  unfold halfRenyiConcentration
  nlinarith [Finset.sum_nonneg
      (s := Finset.univ)
      (fun output _ ↦ Real.sqrt_nonneg
        (probabilityMass (transform <$> sampler) output)),
    Finset.sum_nonneg
      (s := Finset.univ)
      (fun input _ ↦ Real.sqrt_nonneg (probabilityMass sampler input))]

/-! ## Translation stabilizer of the canonical aggregate laws -/

theorem xorEquiv_comm
    {Index : Type} (left right : BitVector Index) :
    xorEquiv left right = xorEquiv right left := by
  funext coordinate
  cases hleft : left coordinate <;> cases hright : right coordinate <;>
    simp [xorEquiv, LWE.MultiKeyAffine.maskedBit, hleft, hright]

theorem xorEquiv_assoc
    {Index : Type} (first second third : BitVector Index) :
    xorEquiv (xorEquiv first second) third =
      xorEquiv first (xorEquiv second third) := by
  funext coordinate
  cases hfirst : first coordinate <;> cases hsecond : second coordinate <;>
      cases hthird : third coordinate <;>
    simp [xorEquiv, LWE.MultiKeyAffine.maskedBit, hfirst, hsecond, hthird]

@[simp]
theorem xorEquiv_self
    {Index : Type} (word : BitVector Index) :
    xorEquiv word word = zeroFrequency := by
  funext coordinate
  cases hword : word coordinate <;>
    simp [xorEquiv, LWE.MultiKeyAffine.maskedBit, zeroFrequency, hword]

@[simp]
theorem xorEquiv_zero_left
    {Index : Type} (word : BitVector Index) :
    xorEquiv (zeroFrequency : BitVector Index) word = word := by
  funext coordinate
  cases hword : word coordinate <;>
    simp [xorEquiv, LWE.MultiKeyAffine.maskedBit, zeroFrequency, hword]

@[simp]
theorem xorEquiv_zero_right
    {Index : Type} (word : BitVector Index) :
    xorEquiv word (zeroFrequency : BitVector Index) = word := by
  rw [xorEquiv_comm, xorEquiv_zero_left]

theorem xorEquiv_left_cancel_zero
    {Index : Type} {left right : BitVector Index}
    (hzero : xorEquiv left right = zeroFrequency) :
    left = right := by
  funext coordinate
  have hcoordinate := congrFun hzero coordinate
  cases hleft : left coordinate <;> cases hright : right coordinate <;>
    simp [xorEquiv, LWE.MultiKeyAffine.maskedBit, zeroFrequency,
      hleft, hright] at hcoordinate ⊢

/-- Translation invariance of a real table on the binary cube. -/
def TranslationInvariant
    {Index : Type} (weight : BitVector Index → ℝ) (shift : BitVector Index) : Prop :=
  ∀ word, weight (xorEquiv shift word) = weight word

/-- Common translation stabilizer of the positive and negative normalized aggregate laws. -/
def CommonAggregateTranslationInvariant
    (Index : Type) [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (shift : BitVector Index) : Prop :=
  TranslationInvariant (aggregatePositiveWeight Index degree) shift ∧
    TranslationInvariant (aggregateNegativeWeight Index degree) shift

/-- Invariance of both normalized Jordan laws implies invariance of their signed high-pass
measure.  Positivity of the common normalization is why the cutoff hypothesis is required. -/
theorem highPassTranslationInvariant_of_commonAggregate
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree < Fintype.card Index)
    (shift : BitVector Index)
    (hinvariant : CommonAggregateTranslationInvariant Index degree shift) :
    TranslationInvariant (highPassWeight Index degree) shift := by
  intro word
  have hnormalization : aggregateNormalization Index degree ≠ 0 :=
    ne_of_gt (aggregateNormalization_pos Index degree hdegree)
  have hpositive := hinvariant.1 word
  have hnegative := hinvariant.2 word
  unfold aggregatePositiveWeight at hpositive
  unfold aggregateNegativeWeight at hnegative
  field_simp [hnormalization] at hpositive hnegative
  rw [← positive_sub_negativeHighPassWeight Index degree,
    ← positive_sub_negativeHighPassWeight Index degree,
    hpositive, hnegative]

/-- A translation-invariant table has Walsh transform fixed by multiplication with the
corresponding character value. -/
theorem walshTransform_eq_character_mul_of_translationInvariant
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (weight : BitVector Index → ℝ) (shift frequency : BitVector Index)
    (hinvariant : TranslationInvariant weight shift) :
    walshTransform weight frequency =
      walsh frequency shift * walshTransform weight frequency := by
  classical
  unfold walshTransform
  calc
    (∑ word : BitVector Index, weight word * walsh frequency word) =
        ∑ word : BitVector Index,
          weight (xorEquiv shift word) * walsh frequency (xorEquiv shift word) := by
      exact ((xorEquiv shift).sum_comp
        (fun word ↦ weight word * walsh frequency word)).symm
    _ = ∑ word : BitVector Index,
          weight word * (walsh frequency shift * walsh frequency word) := by
      apply Finset.sum_congr rfl
      intro word _
      rw [hinvariant word]
      rw [show walsh frequency (xorEquiv shift word) =
          walsh frequency shift * walsh frequency word by
        simpa [xorEquiv] using walsh_maskedBit frequency shift word]
    _ = walsh frequency shift *
        ∑ word : BitVector Index, weight word * walsh frequency word := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro word _
      ring

/-- Every Walsh frequency retained by the canonical high-pass measure annihilates a common
translation stabilizer. -/
theorem walsh_eq_one_of_commonAggregateTranslationInvariant
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree < Fintype.card Index)
    (shift frequency : BitVector Index)
    (hinvariant : CommonAggregateTranslationInvariant Index degree shift)
    (hfrequency : frequency ∉ boundedFrequencies Index degree) :
    walsh frequency shift = 1 := by
  have htranslation :=
    walshTransform_eq_character_mul_of_translationInvariant
      (highPassWeight Index degree) shift frequency
      (highPassTranslationInvariant_of_commonAggregate
        degree hdegree shift hinvariant)
  rw [walshTransform_highPassWeight, if_neg hfrequency] at htranslation
  simpa using htranslation.symm

/-- Finite Walsh inversion for an arbitrary real table on the binary cube. -/
theorem walshInverse
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (weight : BitVector Index → ℝ) (word : BitVector Index) :
    (∑ frequency : BitVector Index,
        walshTransform weight frequency * walsh frequency word) /
        cubeSize Index = weight word := by
  classical
  unfold walshTransform
  calc
    (∑ frequency : BitVector Index,
        (∑ candidate : BitVector Index,
          weight candidate * walsh frequency candidate) * walsh frequency word) /
        cubeSize Index =
      (∑ candidate : BitVector Index, weight candidate *
        (∑ frequency : BitVector Index,
          walsh frequency candidate * walsh frequency word)) /
        cubeSize Index := by
      congr 1
      calc
        (∑ frequency : BitVector Index,
            (∑ candidate : BitVector Index,
              weight candidate * walsh frequency candidate) * walsh frequency word) =
          ∑ frequency : BitVector Index, ∑ candidate : BitVector Index,
            weight candidate *
              (walsh frequency candidate * walsh frequency word) := by
            apply Finset.sum_congr rfl
            intro frequency _
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro candidate _
            ring
        _ = ∑ candidate : BitVector Index, ∑ frequency : BitVector Index,
            weight candidate *
              (walsh frequency candidate * walsh frequency word) := by
          rw [Finset.sum_comm]
        _ = ∑ candidate : BitVector Index, weight candidate *
            (∑ frequency : BitVector Index,
              walsh frequency candidate * walsh frequency word) := by
          apply Finset.sum_congr rfl
          intro candidate _
          rw [Finset.mul_sum]
    _ = (∑ candidate : BitVector Index,
          weight candidate *
            (if candidate = word then cubeSize Index else 0)) /
        cubeSize Index := by
      apply congrArg (fun value : ℝ ↦ value / cubeSize Index)
      apply Finset.sum_congr rfl
      intro candidate _
      rw [walsh_completeness]
    _ = weight word * cubeSize Index / cubeSize Index := by simp
    _ = weight word := by field_simp [cubeSize_ne_zero Index]

/-- The Walsh character condition is also sufficient for high-pass translation invariance. -/
theorem highPassTranslationInvariant_of_walsh_eq_one
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (shift : BitVector Index)
    (hcharacters : ∀ frequency, frequency ∉ boundedFrequencies Index degree →
      walsh frequency shift = 1) :
    TranslationInvariant (highPassWeight Index degree) shift := by
  intro word
  rw [← walshInverse (highPassWeight Index degree) (xorEquiv shift word),
    ← walshInverse (highPassWeight Index degree) word]
  congr 1
  apply Finset.sum_congr rfl
  intro frequency _
  rw [show walsh frequency (xorEquiv shift word) =
      walsh frequency shift * walsh frequency word by
    simpa [xorEquiv] using walsh_maskedBit frequency shift word]
  by_cases hfrequency : frequency ∈ boundedFrequencies Index degree
  · rw [walshTransform_highPassWeight, if_pos hfrequency]
    ring
  · rw [walshTransform_highPassWeight, if_neg hfrequency,
      hcharacters frequency hfrequency]
    ring

/-- High-pass invariance is inherited by both normalized Jordan laws. -/
theorem commonAggregateTranslationInvariant_of_highPass
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (shift : BitVector Index)
    (hinvariant : TranslationInvariant (highPassWeight Index degree) shift) :
    CommonAggregateTranslationInvariant Index degree shift := by
  constructor
  · intro word
    unfold aggregatePositiveWeight positiveHighPassWeight
    rw [hinvariant word]
  · intro word
    unfold aggregateNegativeWeight negativeHighPassWeight
    rw [hinvariant word]

/-- Exact Walsh characterization of the common stabilizer. -/
theorem commonAggregateTranslationInvariant_iff_walsh_eq_one
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree < Fintype.card Index)
    (shift : BitVector Index) :
    CommonAggregateTranslationInvariant Index degree shift ↔
      ∀ frequency, frequency ∉ boundedFrequencies Index degree →
        walsh frequency shift = 1 := by
  constructor
  · intro hinvariant frequency hfrequency
    exact walsh_eq_one_of_commonAggregateTranslationInvariant
      degree hdegree shift frequency hinvariant hfrequency
  · intro hcharacters
    exact commonAggregateTranslationInvariant_of_highPass degree shift
      (highPassTranslationInvariant_of_walsh_eq_one degree shift hcharacters)

theorem supportSize_le_card
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (frequency : BitVector Index) :
    supportSize frequency ≤ Fintype.card Index := by
  unfold supportSize
  exact Finset.card_le_card (Finset.filter_subset _ _)

theorem eq_fullFrequency_of_supportSize_eq_card
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (frequency : BitVector Index)
    (hsize : supportSize frequency = Fintype.card Index) :
    frequency = fullFrequency Index := by
  have hcard : (Finset.univ : Finset Index).card ≤
      (frequencySupport frequency).card := by
    simpa [supportSize] using hsize.ge
  have hsupport : frequencySupport frequency = (Finset.univ : Finset Index) :=
    Finset.eq_of_subset_of_card_le (Finset.subset_univ _) hcard
  apply (frequencyFinsetEquiv Index).injective
  change frequencySupport frequency = frequencySupport (fullFrequency Index)
  rw [hsupport]
  simp [frequencySupport, fullFrequency]

/-- At cutoff exactly one below the dimension, the full-support frequency is the only frequency
outside the bounded set. -/
theorem eq_fullFrequency_of_not_mem_bounded_of_degree_add_one_eq_card
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree + 1 = Fintype.card Index)
    (frequency : BitVector Index)
    (hfrequency : frequency ∉ boundedFrequencies Index degree) :
    frequency = fullFrequency Index := by
  have hnonzero : frequency ≠ (zeroFrequency : BitVector Index) := by
    intro hzero
    apply hfrequency
    rw [hzero]
    exact zeroFrequency_mem_boundedFrequencies Index degree
  have hnotle : ¬ supportSize frequency ≤ degree := by
    intro hle
    apply hfrequency
    apply Finset.mem_insert_of_mem
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_erase.mpr ⟨hnonzero, Finset.mem_univ _⟩, hle⟩
  have hsize : supportSize frequency = Fintype.card Index := by
    have hle := supportSize_le_card frequency
    omega
  exact eq_fullFrequency_of_supportSize_eq_card frequency hsize

/-- Even parity written as its equivalent full Walsh-character equation. -/
def EvenWalshParity
    (Index : Type) [Fintype Index] [DecidableEq Index]
    (word : BitVector Index) : Prop :=
  walsh (fullFrequency Index) word = 1

/-- At cutoff `t-1`, the common stabilizer is exactly the even-parity subgroup. -/
theorem commonAggregateTranslationInvariant_iff_evenWalshParity
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree + 1 = Fintype.card Index)
    (shift : BitVector Index) :
    CommonAggregateTranslationInvariant Index degree shift ↔
      EvenWalshParity Index shift := by
  have hdegreeLt : degree < Fintype.card Index := by omega
  rw [commonAggregateTranslationInvariant_iff_walsh_eq_one
    degree hdegreeLt shift]
  constructor
  · intro hcharacters
    exact hcharacters (fullFrequency Index)
      (fullFrequency_not_mem_boundedFrequencies Index degree hdegreeLt)
  · intro hparity frequency hfrequency
    rw [eq_fullFrequency_of_not_mem_bounded_of_degree_add_one_eq_card
      degree hdegree frequency hfrequency]
    exact hparity

/-- Frequency supported on every coordinate except one. -/
def puncturedFrequency
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (coordinate : Index) : BitVector Index :=
  frequencyOfFinset (Finset.univ.erase coordinate)

@[simp]
theorem frequencySupport_frequencyOfFinset
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (support : Finset Index) :
    frequencySupport (frequencyOfFinset support) = support := by
  change (frequencyFinsetEquiv Index)
      ((frequencyFinsetEquiv Index).symm support) = support
  exact (frequencyFinsetEquiv Index).apply_symm_apply support

@[simp]
theorem supportSize_puncturedFrequency
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (coordinate : Index) :
    supportSize (puncturedFrequency coordinate) = Fintype.card Index - 1 := by
  simp [supportSize, puncturedFrequency]

theorem puncturedFrequency_not_mem_boundedFrequencies
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree + 2 ≤ Fintype.card Index)
    (coordinate : Index) :
    puncturedFrequency coordinate ∉ boundedFrequencies Index degree := by
  intro hmember
  rcases Finset.mem_insert.mp hmember with hzero | hlow
  · have hsize := congrArg supportSize hzero
    rw [supportSize_puncturedFrequency] at hsize
    simp [supportSize, frequencySupport_zeroFrequency] at hsize
    omega
  · have hsize := (Finset.mem_filter.mp hlow).2
    rw [supportSize_puncturedFrequency] at hsize
    omega

theorem walsh_puncturedFrequency_eq_prod_erase
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (coordinate : Index) (word : BitVector Index) :
    walsh (puncturedFrequency coordinate) word =
      ∏ candidate ∈ Finset.univ.erase coordinate, bitSign (word candidate) := by
  classical
  unfold walsh puncturedFrequency frequencyOfFinset
  simp only [decide_eq_true_eq, Finset.mem_erase, Finset.mem_univ, and_true]
  rw [← Fintype.prod_ite_mem (Finset.univ.erase coordinate)
    (fun candidate ↦ bitSign (word candidate))]
  apply Finset.prod_congr rfl
  intro candidate _
  simp

theorem walsh_fullFrequency_eq_bitSign_mul_punctured
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (coordinate : Index) (word : BitVector Index) :
    walsh (fullFrequency Index) word =
      bitSign (word coordinate) * walsh (puncturedFrequency coordinate) word := by
  classical
  rw [walsh_puncturedFrequency_eq_prod_erase]
  unfold walsh fullFrequency
  simp only [if_true]
  exact (Finset.mul_prod_erase Finset.univ
    (fun candidate ↦ bitSign (word candidate)) (Finset.mem_univ coordinate)).symm

/-- Unit binary word at one coordinate. -/
def coordinateUnit
    {Index : Type} [DecidableEq Index] (coordinate : Index) : BitVector Index :=
  fun candidate ↦ decide (candidate = coordinate)

theorem walsh_fullFrequency_coordinateUnit
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (coordinate : Index) :
    walsh (fullFrequency Index) (coordinateUnit coordinate) = -1 := by
  rw [walsh_fullFrequency_eq_bitSign_mul_punctured coordinate,
    walsh_puncturedFrequency_eq_prod_erase]
  simp [coordinateUnit, bitSign]

theorem walsh_eq_one_or_neg_one
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (frequency word : BitVector Index) :
    walsh frequency word = 1 ∨ walsh frequency word = -1 := by
  have habsolute := abs_walsh frequency word
  rw [abs_eq (by norm_num : (0 : ℝ) ≤ 1)] at habsolute
  exact habsolute

/-- Boolean encoding of full Walsh parity. -/
def fullWalshParityBit
    (Index : Type) [Fintype Index] [DecidableEq Index]
    (word : BitVector Index) : Bool :=
  decide (walsh (fullFrequency Index) word = -1)

/-- Toggling one coordinate complements full Walsh parity. -/
theorem fullWalshParityBit_xor_coordinateUnit
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (coordinate : Index) (word : BitVector Index) :
    fullWalshParityBit Index (xorEquiv (coordinateUnit coordinate) word) =
      !fullWalshParityBit Index word := by
  have htranslated :
      walsh (fullFrequency Index) (xorEquiv (coordinateUnit coordinate) word) =
        -walsh (fullFrequency Index) word := by
    rw [show walsh (fullFrequency Index) (xorEquiv (coordinateUnit coordinate) word) =
        walsh (fullFrequency Index) (coordinateUnit coordinate) *
          walsh (fullFrequency Index) word by
      simpa [xorEquiv] using
        walsh_maskedBit (fullFrequency Index) (coordinateUnit coordinate) word,
      walsh_fullFrequency_coordinateUnit]
    ring
  rcases walsh_eq_one_or_neg_one (fullFrequency Index) word with hone | hnegative
  · norm_num [fullWalshParityBit, htranslated, hone]
  · norm_num [fullWalshParityBit, htranslated, hnegative]

/-- Full parity of a uniform nonempty binary cube is a uniform bit, stated as its exact
Renyi-half concentration. -/
theorem halfRenyiConcentration_fullWalshParityBit_uniform_eq_two
    (Index : Type) [Fintype Index] [DecidableEq Index] [Nonempty Index]
    [SampleableType (BitVector Index)] :
    halfRenyiConcentration
        (fullWalshParityBit Index <$> ($ᵗ (BitVector Index))) = 2 := by
  let coordinate : Index := Classical.choice inferInstance
  let paritySampler : ProbComp Bool :=
    fullWalshParityBit Index <$> ($ᵗ (BitVector Index))
  have htoggle :
      evalDist (xorEquiv (coordinateUnit coordinate) <$>
          ($ᵗ (BitVector Index))) =
        evalDist ($ᵗ (BitVector Index)) :=
    evalDist_map_bijective_uniform_cross
      (α := BitVector Index) (β := BitVector Index)
      (xorEquiv (coordinateUnit coordinate))
      (xorEquiv (coordinateUnit coordinate)).bijective
  have hmapped := evalDist_map_eq_of_evalDist_eq htoggle
    (fullWalshParityBit Index)
  have hfunctions :
      (fun word ↦ fullWalshParityBit Index
        (xorEquiv (coordinateUnit coordinate) word)) =
        (fun word ↦ !fullWalshParityBit Index word) := by
    funext word
    exact fullWalshParityBit_xor_coordinateUnit coordinate word
  simp only [Functor.map_map] at hmapped
  rw [hfunctions] at hmapped
  have hprobability := (evalDist_ext_iff.mp hmapped) true
  have hnotProbability :
      Pr[= true | Bool.not <$> paritySampler] =
        Pr[= false | paritySampler] := by
    simpa [paritySampler] using
      (probOutput_map_injective paritySampler (f := Bool.not)
        (fun first second hequal ↦ by
          cases first <;> cases second <;> simp_all) false)
  have hcomposition :
      (fun word ↦ !fullWalshParityBit Index word) <$> ($ᵗ (BitVector Index)) =
        Bool.not <$> paritySampler := by
    simp [paritySampler, Functor.map_map]
  rw [hcomposition, hnotProbability] at hprobability
  have hequalMass :
      probabilityMass paritySampler false = probabilityMass paritySampler true :=
    congrArg ENNReal.toReal hprobability
  have hsum := sum_probabilityMass_eq_one paritySampler
  rw [Fintype.sum_bool] at hsum
  have hfalse : probabilityMass paritySampler false = (1 : ℝ) / 2 := by
    linarith
  have htrue : probabilityMass paritySampler true = (1 : ℝ) / 2 := by
    linarith
  change halfRenyiConcentration paritySampler = 2
  unfold halfRenyiConcentration
  rw [Fintype.sum_bool, htrue, hfalse]
  nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]

theorem walsh_eq_of_xor_character_eq_one
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (frequency left right : BitVector Index)
    (hcharacter : walsh frequency (xorEquiv left right) = 1) :
    walsh frequency left = walsh frequency right := by
  have hproduct : walsh frequency left * walsh frequency right = 1 := by
    rw [← hcharacter]
    simpa [xorEquiv] using (walsh_maskedBit frequency left right).symm
  have hleftSq : walsh frequency left ^ 2 = 1 := by
    rw [← sq_abs, abs_walsh]
    norm_num
  have hrightSq : walsh frequency right ^ 2 = 1 := by
    rw [← sq_abs, abs_walsh]
    norm_num
  nlinarith [sq_nonneg (walsh frequency left - walsh frequency right)]

/-- For `degree ≤ card Index - 2`, the common translation stabilizer is trivial. -/
theorem commonAggregateTranslationInvariant_iff_eq_zero_of_degree_add_two_le
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree + 2 ≤ Fintype.card Index)
    (shift : BitVector Index) :
    CommonAggregateTranslationInvariant Index degree shift ↔
      shift = zeroFrequency := by
  constructor
  · intro hinvariant
    have hdegreeLt : degree < Fintype.card Index := by omega
    have hfullNot := fullFrequency_not_mem_boundedFrequencies
      Index degree hdegreeLt
    have hfull := walsh_eq_one_of_commonAggregateTranslationInvariant
      degree hdegreeLt shift (fullFrequency Index) hinvariant hfullNot
    funext coordinate
    have hpuncturedNot := puncturedFrequency_not_mem_boundedFrequencies
      degree hdegree coordinate
    have hpunctured := walsh_eq_one_of_commonAggregateTranslationInvariant
      degree hdegreeLt shift (puncturedFrequency coordinate) hinvariant hpuncturedNot
    have hrelation := walsh_fullFrequency_eq_bitSign_mul_punctured coordinate shift
    rw [hfull, hpunctured, mul_one] at hrelation
    cases hvalue : shift coordinate <;>
      simp [zeroFrequency, bitSign, hvalue] at hrelation ⊢
    norm_num at hrelation
  · rintro rfl
    constructor <;> intro word <;> rw [xorEquiv_zero_left]

/-! ## Phase-oblivious projected plaintext builders -/

/-- Exact diagonal correctness for the natural builder class: after receiving projected leakage,
the builder selects a known plaintext whose law is the prefix-translate of the chosen aggregate
mask law. -/
def PhaseObliviousPlaintextCorrect
    {Index Key Leakage : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (prefixValue : Key → BitVector Index) (leakage : Key → Leakage)
    (plaintextLaw : Bool → Leakage → BitVector Index → ℝ) : Prop :=
  ∀ positive key message,
    plaintextLaw positive (leakage key) message =
      aggregateMaskWeight positive Index degree
        (xorEquiv (prefixValue key) message)

/-- If two keys have the same projected leakage, exact phase-oblivious correctness makes their
prefix difference a common translation stabilizer of the two aggregate laws. -/
theorem commonAggregateTranslationInvariant_of_equal_leakage
    {Index Key Leakage : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (prefixValue : Key → BitVector Index) (leakage : Key → Leakage)
    (plaintextLaw : Bool → Leakage → BitVector Index → ℝ)
    (hcorrect : PhaseObliviousPlaintextCorrect
      degree prefixValue leakage plaintextLaw)
    (first second : Key) (hleakage : leakage first = leakage second) :
    CommonAggregateTranslationInvariant Index degree
      (xorEquiv (prefixValue first) (prefixValue second)) := by
  have hsign (positive : Bool) :
      TranslationInvariant (aggregateMaskWeight positive Index degree)
        (xorEquiv (prefixValue first) (prefixValue second)) := by
    intro word
    let message := xorEquiv (prefixValue first) word
    have hfirstMessage : xorEquiv (prefixValue first) message = word := by
      exact (xorEquiv (prefixValue first)).left_inv word
    have hsecondMessage :
        xorEquiv (prefixValue second) message =
          xorEquiv (xorEquiv (prefixValue first) (prefixValue second)) word := by
      calc
        xorEquiv (prefixValue second) (xorEquiv (prefixValue first) word) =
            xorEquiv (xorEquiv (prefixValue second) (prefixValue first)) word := by
          rw [xorEquiv_assoc]
        _ = xorEquiv (xorEquiv (prefixValue first) (prefixValue second)) word := by
          rw [xorEquiv_comm (prefixValue second) (prefixValue first)]
    calc
      aggregateMaskWeight positive Index degree
          (xorEquiv (xorEquiv (prefixValue first) (prefixValue second)) word) =
        aggregateMaskWeight positive Index degree
          (xorEquiv (prefixValue second) message) := by rw [hsecondMessage]
      _ = plaintextLaw positive (leakage second) message :=
        (hcorrect positive second message).symm
      _ = plaintextLaw positive (leakage first) message := by rw [hleakage]
      _ = aggregateMaskWeight positive Index degree
          (xorEquiv (prefixValue first) message) := hcorrect positive first message
      _ = aggregateMaskWeight positive Index degree word := by rw [hfirstMessage]
  constructor
  · intro word
    simpa [aggregateMaskWeight] using hsign true word
  · intro word
    simpa [aggregateMaskWeight] using hsign false word

/-- For the usual cutoff `degree ≤ t-2`, equal projected leakage forces equal binary prefixes. -/
theorem prefix_eq_of_equal_leakage_phaseOblivious
    {Index Key Leakage : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree + 2 ≤ Fintype.card Index)
    (prefixValue : Key → BitVector Index) (leakage : Key → Leakage)
    (plaintextLaw : Bool → Leakage → BitVector Index → ℝ)
    (hcorrect : PhaseObliviousPlaintextCorrect
      degree prefixValue leakage plaintextLaw)
    (first second : Key) (hleakage : leakage first = leakage second) :
    prefixValue first = prefixValue second := by
  have hinvariant := commonAggregateTranslationInvariant_of_equal_leakage
    degree prefixValue leakage plaintextLaw hcorrect first second hleakage
  have hzero :=
    (commonAggregateTranslationInvariant_iff_eq_zero_of_degree_add_two_le
      degree hdegree (xorEquiv (prefixValue first) (prefixValue second))).mp hinvariant
  exact xorEquiv_left_cancel_zero hzero

/-- At the exceptional cutoff `t-1`, equal leakage need only force equal full parity. -/
theorem fullWalshParityBit_eq_of_equal_leakage_phaseOblivious
    {Index Key Leakage : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree + 1 = Fintype.card Index)
    (prefixValue : Key → BitVector Index) (leakage : Key → Leakage)
    (plaintextLaw : Bool → Leakage → BitVector Index → ℝ)
    (hcorrect : PhaseObliviousPlaintextCorrect
      degree prefixValue leakage plaintextLaw)
    (first second : Key) (hleakage : leakage first = leakage second) :
    fullWalshParityBit Index (prefixValue first) =
      fullWalshParityBit Index (prefixValue second) := by
  have hinvariant := commonAggregateTranslationInvariant_of_equal_leakage
    degree prefixValue leakage plaintextLaw hcorrect first second hleakage
  have heven :=
    (commonAggregateTranslationInvariant_iff_evenWalshParity
      degree hdegree (xorEquiv (prefixValue first) (prefixValue second))).mp hinvariant
  have hwalsh := walsh_eq_of_xor_character_eq_one
    (fullFrequency Index) (prefixValue first) (prefixValue second) heven
  unfold fullWalshParityBit
  rw [hwalsh]

/-! ## Recovery and the concentration lower bound -/

/-- Recover a separated attribute from a leakage value.  Values outside the image use an arbitrary
default; they never occur in the pushed-forward key law. -/
noncomputable def recoverSeparatedAttribute
    {Key Attribute Leakage : Type}
    (default : Attribute) (attributeFn : Key → Attribute) (leakage : Key → Leakage)
    (value : Leakage) : Attribute := by
  letI : Decidable (∃ key, leakage key = value) := Classical.propDecidable _
  exact if hvalue : ∃ key, leakage key = value then
      attributeFn (Classical.choose hvalue)
    else default

@[simp]
theorem recoverSeparatedAttribute_leakage
    {Key Attribute Leakage : Type}
    (default : Attribute) (attributeFn : Key → Attribute) (leakage : Key → Leakage)
    (hseparated : ∀ first second, leakage first = leakage second →
      attributeFn first = attributeFn second)
    (key : Key) :
    recoverSeparatedAttribute default attributeFn leakage (leakage key) = attributeFn key := by
  unfold recoverSeparatedAttribute
  split
  · rename_i himage
    exact hseparated (Classical.choose himage) key
      (Classical.choose_spec himage)
  · rename_i houtside
    exact False.elim (houtside ⟨key, rfl⟩)

theorem halfRenyiConcentration_eq_of_evalDist_eq
    {A : Type} [Fintype A] (first second : ProbComp A)
    (hdistribution : evalDist first = evalDist second) :
    halfRenyiConcentration first = halfRenyiConcentration second := by
  classical
  unfold halfRenyiConcentration
  apply congrArg (fun value : ℝ ↦ value ^ 2)
  apply Finset.sum_congr rfl
  intro value _
  congr 1
  unfold probabilityMass
  rw [(evalDist_ext_iff.mp hdistribution) value]

theorem recoverSeparatedAttribute_map_leakageLaw_evalDist
    {Key Attribute Leakage : Type}
    (keySampler : ProbComp Key)
    (default : Attribute) (attributeFn : Key → Attribute) (leakage : Key → Leakage)
    (hseparated : ∀ first second, leakage first = leakage second →
      attributeFn first = attributeFn second) :
    evalDist
        (recoverSeparatedAttribute default attributeFn leakage <$>
          leakageLaw keySampler leakage) =
      evalDist (attributeFn <$> keySampler) := by
  have hfunctions :
      (fun key ↦ recoverSeparatedAttribute default attributeFn leakage (leakage key)) =
        attributeFn := by
    funext key
    exact recoverSeparatedAttribute_leakage
      default attributeFn leakage hseparated key
  simp only [leakageLaw, Functor.map_map]
  rw [hfunctions]

/-- Any leakage from which an attribute can be recovered has at least the Renyi-half
concentration of that attribute. -/
theorem halfRenyiConcentration_attribute_le_leakage
    {Key Attribute Leakage : Type}
    [Fintype Attribute] [DecidableEq Attribute]
    [Fintype Leakage] [DecidableEq Leakage]
    (keySampler : ProbComp Key)
    (default : Attribute) (attributeFn : Key → Attribute) (leakage : Key → Leakage)
    (hseparated : ∀ first second, leakage first = leakage second →
      attributeFn first = attributeFn second) :
    halfRenyiConcentration (attributeFn <$> keySampler) ≤
      halfRenyiConcentration (leakageLaw keySampler leakage) := by
  let recover := recoverSeparatedAttribute default attributeFn leakage
  have hprocessing := halfRenyiConcentration_map_le
    (leakageLaw keySampler leakage) recover
  have hdistribution := recoverSeparatedAttribute_map_leakageLaw_evalDist
    keySampler default attributeFn leakage hseparated
  rw [halfRenyiConcentration_eq_of_evalDist_eq
    (recover <$> leakageLaw keySampler leakage)
    (attributeFn <$> keySampler) hdistribution] at hprocessing
  exact hprocessing

/-- A separated attribute of a uniform product key costs its complete carrier cardinality in
Renyi-half concentration. -/
theorem card_le_halfRenyiConcentration_leakageLaw_uniform_product
    {Attribute Suffix Leakage : Type}
    [Fintype Attribute] [DecidableEq Attribute] [Nonempty Attribute]
    [Fintype Suffix] [Nonempty Suffix]
    [Fintype Leakage] [DecidableEq Leakage]
    [SampleableType Attribute] [SampleableType Suffix]
    [SampleableType (Attribute × Suffix)]
    (leakage : Attribute × Suffix → Leakage)
    (hseparated : ∀ first second, leakage first = leakage second →
      first.1 = second.1) :
    (Fintype.card Attribute : ℝ) ≤
      halfRenyiConcentration
        (leakageLaw ($ᵗ (Attribute × Suffix)) leakage) := by
  let default : Attribute := Classical.choice inferInstance
  have hlower := halfRenyiConcentration_attribute_le_leakage
    ($ᵗ (Attribute × Suffix)) default Prod.fst leakage hseparated
  have hmarginal :
      evalDist (Prod.fst <$> ($ᵗ (Attribute × Suffix))) =
        evalDist ($ᵗ Attribute) :=
    evalDist_map_fst_uniformSample_prod
  rw [halfRenyiConcentration_eq_of_evalDist_eq
    (Prod.fst <$> ($ᵗ (Attribute × Suffix))) ($ᵗ Attribute) hmarginal,
    halfRenyiConcentration_uniform] at hlower
  exact hlower

/-- At the exceptional cutoff `degree = t - 1`, exact phase-oblivious correctness still forces
the leakage to reveal full binary parity.  For a uniform nonempty binary prefix this costs at
least `2` in Renyi-half concentration. -/
theorem two_le_projectedLeakageConcentration_of_phaseOblivious_lastCutoff
    {Index Suffix Leakage : Type}
    [Fintype Index] [DecidableEq Index] [Nonempty Index]
    [Fintype Suffix] [Nonempty Suffix]
    [Fintype Leakage] [DecidableEq Leakage]
    [SampleableType (BitVector Index)] [SampleableType Suffix]
    [SampleableType (BitVector Index × Suffix)]
    (degree : ℕ) (hdegree : degree + 1 = Fintype.card Index)
    (leakage : BitVector Index × Suffix → Leakage)
    (plaintextLaw : Bool → Leakage → BitVector Index → ℝ)
    (hcorrect : PhaseObliviousPlaintextCorrect
      degree Prod.fst leakage plaintextLaw) :
    (2 : ℝ) ≤ projectedLeakageConcentration
      ($ᵗ (BitVector Index × Suffix)) leakage := by
  let parityKey : BitVector Index × Suffix → Bool :=
    fun key ↦ fullWalshParityBit Index key.1
  have hseparated : ∀ first second : BitVector Index × Suffix,
      leakage first = leakage second → parityKey first = parityKey second := by
    intro first second hequal
    exact fullWalshParityBit_eq_of_equal_leakage_phaseOblivious
      degree hdegree Prod.fst leakage plaintextLaw hcorrect first second hequal
  have hlower := halfRenyiConcentration_attribute_le_leakage
    ($ᵗ (BitVector Index × Suffix)) false parityKey leakage hseparated
  have hmarginal :
      evalDist (Prod.fst <$> ($ᵗ (BitVector Index × Suffix))) =
        evalDist ($ᵗ (BitVector Index)) :=
    evalDist_map_fst_uniformSample_prod
  have hparityMarginal :
      evalDist (parityKey <$> ($ᵗ (BitVector Index × Suffix))) =
        evalDist
          (fullWalshParityBit Index <$> ($ᵗ (BitVector Index))) := by
    have hmapped := evalDist_map_eq_of_evalDist_eq hmarginal
      (fullWalshParityBit Index)
    simpa [parityKey, Functor.map_map] using hmapped
  rw [halfRenyiConcentration_eq_of_evalDist_eq
      (parityKey <$> ($ᵗ (BitVector Index × Suffix)))
      (fullWalshParityBit Index <$> ($ᵗ (BitVector Index))) hparityMarginal,
    halfRenyiConcentration_fullWalshParityBit_uniform_eq_two] at hlower
  unfold projectedLeakageConcentration
  exact hlower

/-- Main negative result for the natural projected builder.  With a uniform binary prefix and
`degree ≤ t-2`, its leakage concentration is at least `2^t`, independently of the suffix law's
carrier size. -/
theorem twoPow_card_le_projectedLeakageConcentration_of_phaseOblivious
    {Index Suffix Leakage : Type}
    [Fintype Index] [DecidableEq Index]
    [Fintype Suffix] [Nonempty Suffix]
    [Fintype Leakage] [DecidableEq Leakage]
    [SampleableType (BitVector Index)] [SampleableType Suffix]
    [SampleableType (BitVector Index × Suffix)]
    (degree : ℕ) (hdegree : degree + 2 ≤ Fintype.card Index)
    (leakage : BitVector Index × Suffix → Leakage)
    (plaintextLaw : Bool → Leakage → BitVector Index → ℝ)
    (hcorrect : PhaseObliviousPlaintextCorrect
      degree Prod.fst leakage plaintextLaw) :
    (2 : ℝ) ^ Fintype.card Index ≤
      projectedLeakageConcentration
        ($ᵗ (BitVector Index × Suffix)) leakage := by
  have hseparated : ∀ first second : BitVector Index × Suffix,
      leakage first = leakage second → first.1 = second.1 := by
    intro first second hequal
    exact prefix_eq_of_equal_leakage_phaseOblivious
      degree hdegree Prod.fst leakage plaintextLaw hcorrect first second hequal
  have hlower := card_le_halfRenyiConcentration_leakageLaw_uniform_product
    leakage hseparated
  unfold projectedLeakageConcentration
  simpa [Fintype.card_fun] using hlower

end

end FormalProof4FHE.TFHE.NativeTRGSWAggregateProjectedLeakage
