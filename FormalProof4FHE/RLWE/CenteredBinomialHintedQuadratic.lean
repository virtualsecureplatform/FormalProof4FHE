/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.WeightedSquare
import FormalProof4FHE.Probability.SquaredBias
import FormalProof4FHE.RLWE.CenteredBinomialMoment
import FormalProof4FHE.RLWE.IntervalMaskedQuadratic

/-!
# Centered-Binomial Randomized Hints for Quadratic RLWE

The interval-masked quadratic compiler uses a uniform injective encoding.  Centered-binomial
mask values are not an injective image of their uniform bit-pair tables, so applying that
counting theorem to CBD would be unsound.  This file gives the corresponding arbitrary-law
reduction.

For a secret `S`, an independent mask `Z`, and public hint `H = S - Z`, the genuine context law
is the joint law `(H,S)`.  The ordinary-RLWE source law used by the reduction samples `H` from
its genuine marginal and then samples an independent `S`.  Their exact change-of-measure cost is

`C₂ = ∑_(h,s) P[H=h,S=s]² / (P[H=h] P[S=s])`.

The checked squared-bias theorem loses `sqrt (2 C₂ Adv₂)`.  This is an exact finite constant;
an asymptotic CBD shift/concentration bound may be proved later without changing the game proof.
The file also records the exact centered quadratic identity, whose residual is `E - Z²`.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.RLWE.CenteredBinomialHintedQuadratic

noncomputable section

open FormalProof4FHE.WeightedSquare

/-! ## Randomized finite hint channels -/

/-- Algebraic data for a randomized-mask hint.  No injectivity is required. -/
structure Encoding (R Secret Mask Hint : Type) [Sub R] where
  secretValue : Secret → R
  maskValue : Mask → R
  hint : Secret → Mask → Hint
  hintValue : Hint → R
  hintValue_hint : ∀ secret mask,
    hintValue (hint secret mask) = secretValue secret - maskValue mask

/-- Conditional public-hint channel for a fixed secret. -/
def hintChannel
    {R Secret Mask Hint : Type} [Sub R]
    (encoding : Encoding R Secret Mask Hint) (maskSampler : ProbComp Mask)
    (secret : Secret) : ProbComp Hint := do
  let mask ← maskSampler
  return encoding.hint secret mask

/-- Genuine joint context `(H,S)`. -/
def jointContextSampler
    {R Secret Mask Hint : Type} [Sub R]
    (encoding : Encoding R Secret Mask Hint)
    (secretSampler : ProbComp Secret) (maskSampler : ProbComp Mask) :
    ProbComp (Hint × Secret) := do
  let secret ← secretSampler
  let hint ← hintChannel encoding maskSampler secret
  return (hint, secret)

/-- Genuine marginal law of the public hint. -/
def hintMarginalSampler
    {R Secret Mask Hint : Type} [Sub R]
    (encoding : Encoding R Secret Mask Hint)
    (secretSampler : ProbComp Secret) (maskSampler : ProbComp Mask) :
    ProbComp Hint := do
  let secret ← secretSampler
  hintChannel encoding maskSampler secret

/-- Reference context: a genuine marginal hint and an independently resampled secret. -/
def independentContextSampler
    {R Secret Mask Hint : Type} [Sub R]
    (encoding : Encoding R Secret Mask Hint)
    (secretSampler : ProbComp Secret) (maskSampler : ProbComp Mask) :
    ProbComp (Hint × Secret) := do
  let hint ← hintMarginalSampler encoding secretSampler maskSampler
  let secret ← secretSampler
  return (hint, secret)

theorem probabilityMass_jointContextSampler
    {R Secret Mask Hint : Type} [Sub R]
    [Fintype Secret] [Fintype Hint] [DecidableEq Secret] [DecidableEq Hint]
    (encoding : Encoding R Secret Mask Hint)
    (secretSampler : ProbComp Secret) (maskSampler : ProbComp Mask)
    (hint : Hint) (secret : Secret) :
    probabilityMass
        (jointContextSampler encoding secretSampler maskSampler) (hint, secret) =
      probabilityMass secretSampler secret *
        probabilityMass (hintChannel encoding maskSampler secret) hint := by
  unfold probabilityMass
  rw [show
      Pr[= (hint, secret) |
          jointContextSampler encoding secretSampler maskSampler] =
        Pr[= secret | secretSampler] *
          Pr[= hint | hintChannel encoding maskSampler secret] by
    simp [jointContextSampler, probOutput_bind_eq_sum_fintype]]
  rw [ENNReal.toReal_mul]

theorem probabilityMass_hintMarginalSampler
    {R Secret Mask Hint : Type} [Sub R]
    [Fintype Secret] [Fintype Hint] [DecidableEq Hint]
    (encoding : Encoding R Secret Mask Hint)
    (secretSampler : ProbComp Secret) (maskSampler : ProbComp Mask)
    (hint : Hint) :
    probabilityMass
        (hintMarginalSampler encoding secretSampler maskSampler) hint =
      ∑ secret, probabilityMass secretSampler secret *
        probabilityMass (hintChannel encoding maskSampler secret) hint := by
  classical
  unfold probabilityMass hintMarginalSampler
  rw [probOutput_bind_eq_sum_fintype,
    ENNReal.toReal_sum (fun secret _ ↦ ENNReal.mul_ne_top
      probOutput_ne_top probOutput_ne_top)]
  apply Finset.sum_congr rfl
  intro secret _
  rw [ENNReal.toReal_mul]

theorem probabilityMass_independentContextSampler
    {R Secret Mask Hint : Type} [Sub R]
    [Fintype Secret] [Fintype Hint] [DecidableEq Secret] [DecidableEq Hint]
    (encoding : Encoding R Secret Mask Hint)
    (secretSampler : ProbComp Secret) (maskSampler : ProbComp Mask)
    (hint : Hint) (secret : Secret) :
    probabilityMass
        (independentContextSampler encoding secretSampler maskSampler) (hint, secret) =
      probabilityMass
          (hintMarginalSampler encoding secretSampler maskSampler) hint *
        probabilityMass secretSampler secret := by
  unfold probabilityMass
  rw [show
      Pr[= (hint, secret) |
          independentContextSampler encoding secretSampler maskSampler] =
        Pr[= hint | hintMarginalSampler encoding secretSampler maskSampler] *
          Pr[= secret | secretSampler] by
    simp [independentContextSampler, probOutput_bind_eq_sum_fintype]]
  rw [ENNReal.toReal_mul]

/-- The independent context automatically covers the genuine joint context. -/
theorem independentContext_covers_jointContext
    {R Secret Mask Hint : Type} [Sub R]
    [Fintype Secret] [Fintype Hint] [DecidableEq Secret] [DecidableEq Hint]
    (encoding : Encoding R Secret Mask Hint)
    (secretSampler : ProbComp Secret) (maskSampler : ProbComp Mask) :
    ∀ context,
      probabilityMass (jointContextSampler encoding secretSampler maskSampler) context ≠ 0 →
        probabilityMass
          (independentContextSampler encoding secretSampler maskSampler) context ≠ 0 := by
  classical
  rintro ⟨hint, secret⟩ hJoint
  rw [probabilityMass_jointContextSampler] at hJoint
  have hSecret : probabilityMass secretSampler secret ≠ 0 := by
    exact left_ne_zero_of_mul hJoint
  have hConditional :
      probabilityMass (hintChannel encoding maskSampler secret) hint ≠ 0 := by
    exact right_ne_zero_of_mul hJoint
  have hTermPos :
      0 < probabilityMass secretSampler secret *
        probabilityMass (hintChannel encoding maskSampler secret) hint :=
    mul_pos
      (lt_of_le_of_ne (probabilityMass_nonneg secretSampler secret)
        (Ne.symm hSecret))
      (lt_of_le_of_ne
        (probabilityMass_nonneg (hintChannel encoding maskSampler secret) hint)
        (Ne.symm hConditional))
  have hMarginalPos :
      0 < probabilityMass
        (hintMarginalSampler encoding secretSampler maskSampler) hint := by
    rw [probabilityMass_hintMarginalSampler]
    exact lt_of_lt_of_le hTermPos
      (Finset.single_le_sum
        (fun candidate _ ↦ mul_nonneg
          (probabilityMass_nonneg secretSampler candidate)
          (probabilityMass_nonneg (hintChannel encoding maskSampler candidate) hint))
        (Finset.mem_univ secret))
  rw [probabilityMass_independentContextSampler]
  exact mul_ne_zero (ne_of_gt hMarginalPos) hSecret

/-- Exact finite order-two mutual-density cost of revealing a randomized hint. -/
def hintDensityCost
    {R Secret Mask Hint : Type} [Sub R]
    [Fintype Secret] [Fintype Hint]
    (encoding : Encoding R Secret Mask Hint)
    (secretSampler : ProbComp Secret) (maskSampler : ProbComp Mask) : ℝ :=
  densitySecondMoment
    (jointContextSampler encoding secretSampler maskSampler)
    (independentContextSampler encoding secretSampler maskSampler)

theorem hintDensityCost_nonneg
    {R Secret Mask Hint : Type} [Sub R]
    [Fintype Secret] [Fintype Hint]
    (encoding : Encoding R Secret Mask Hint)
    (secretSampler : ProbComp Secret) (maskSampler : ProbComp Mask) :
    0 ≤ hintDensityCost encoding secretSampler maskSampler :=
  densitySecondMoment_nonneg _ _

/-- Expanded finite-sum form of the randomized-hint loss. -/
theorem hintDensityCost_eq_sum_ratio
    {R Secret Mask Hint : Type} [Sub R]
    [Fintype Secret] [Fintype Hint] [DecidableEq Secret] [DecidableEq Hint]
    (encoding : Encoding R Secret Mask Hint)
    (secretSampler : ProbComp Secret) (maskSampler : ProbComp Mask) :
    hintDensityCost encoding secretSampler maskSampler =
      ∑ context : Hint × Secret,
        (probabilityMass secretSampler context.2 *
            probabilityMass
              (hintChannel encoding maskSampler context.2) context.1) ^ 2 /
          (probabilityMass
              (hintMarginalSampler encoding secretSampler maskSampler) context.1 *
            probabilityMass secretSampler context.2) := by
  classical
  unfold hintDensityCost densitySecondMoment
  apply Finset.sum_congr rfl
  rintro ⟨hint, secret⟩ _
  rw [probabilityMass_jointContextSampler,
    probabilityMass_independentContextSampler]

/-! ## Hinted RLWE and the exact weighted two-copy reduction -/

abbrev HintTranscript (Hint R : Type) :=
  IntervalMaskedQuadratic.HintTranscript Hint R

abbrev HintDistinguisher (Hint R : Type) :=
  HintTranscript Hint R → ProbComp Bool

/-- One real ring-LWE block for a fixed encoded secret. -/
def fixedSecretRealBlock
    {R Secret Mask Hint : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (encoding : Encoding R Secret Mask Hint) (errorSampler : ProbComp R)
    (secret : Secret) : ProbComp (R × R) := do
  let publicMask ← $ᵗ R
  let error ← errorSampler
  return (publicMask, publicMask * encoding.secretValue secret + error)

/-- One ideal uniform ring-LWE block. -/
def uniformBlock {R : Type} [SampleableType R] : ProbComp (R × R) :=
  $ᵗ (R × R)

def contextReal
    {R Secret Mask Hint : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (encoding : Encoding R Secret Mask Hint) (errorSampler : ProbComp R)
    (adversary : HintDistinguisher Hint R) (context : Hint × Secret) : ProbComp Bool := do
  let sample ← fixedSecretRealBlock encoding errorSampler context.2
  adversary ⟨context.1, sample.1, sample.2⟩

def contextIdeal
    {R Secret Mask Hint : Type}
    [Sub R] [SampleableType R]
    (_encoding : Encoding R Secret Mask Hint)
    (adversary : HintDistinguisher Hint R) (context : Hint × Secret) : ProbComp Bool := do
  let sample ← uniformBlock (R := R)
  adversary ⟨context.1, sample.1, sample.2⟩

def contextGap
    {R Secret Mask Hint : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (encoding : Encoding R Secret Mask Hint) (errorSampler : ProbComp R)
    (adversary : HintDistinguisher Hint R) (context : Hint × Secret) : ℝ :=
  SquaredBias.signedGap
    (contextReal encoding errorSampler adversary context)
    (contextIdeal encoding adversary context)

def hintedRealGame
    {R Secret Mask Hint : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (encoding : Encoding R Secret Mask Hint)
    (secretSampler : ProbComp Secret) (maskSampler : ProbComp Mask)
    (errorSampler : ProbComp R) (adversary : HintDistinguisher Hint R) : ProbComp Bool :=
  jointContextSampler encoding secretSampler maskSampler >>=
    contextReal encoding errorSampler adversary

def hintedIdealGame
    {R Secret Mask Hint : Type}
    [Sub R] [SampleableType R]
    (encoding : Encoding R Secret Mask Hint)
    (secretSampler : ProbComp Secret) (maskSampler : ProbComp Mask)
    (adversary : HintDistinguisher Hint R) : ProbComp Bool :=
  jointContextSampler encoding secretSampler maskSampler >>=
    contextIdeal encoding adversary

def hintAdvantage
    {R Secret Mask Hint : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (encoding : Encoding R Secret Mask Hint)
    (secretSampler : ProbComp Secret) (maskSampler : ProbComp Mask)
    (errorSampler : ProbComp R) (adversary : HintDistinguisher Hint R) : ℝ :=
  (hintedRealGame encoding secretSampler maskSampler errorSampler adversary).boolDistAdvantage
    (hintedIdealGame encoding secretSampler maskSampler adversary)

def twoCopyRealGame
    {R Secret Mask Hint : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (encoding : Encoding R Secret Mask Hint)
    (secretSampler : ProbComp Secret) (maskSampler : ProbComp Mask)
    (errorSampler : ProbComp R) (adversary : HintDistinguisher Hint R) : ProbComp Bool :=
  SquaredBias.contextualExperiment
    (independentContextSampler encoding secretSampler maskSampler)
    (contextReal encoding errorSampler adversary)
    (contextIdeal encoding adversary)

def twoCopyIdealGame
    {R Secret Mask Hint : Type}
    [Sub R] [SampleableType R]
    (encoding : Encoding R Secret Mask Hint)
    (secretSampler : ProbComp Secret) (maskSampler : ProbComp Mask)
    (adversary : HintDistinguisher Hint R) : ProbComp Bool :=
  SquaredBias.contextualExperiment
    (independentContextSampler encoding secretSampler maskSampler)
    (contextIdeal encoding adversary)
    (contextIdeal encoding adversary)

def twoCopyRLWEAdvantage
    {R Secret Mask Hint : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    (encoding : Encoding R Secret Mask Hint)
    (secretSampler : ProbComp Secret) (maskSampler : ProbComp Mask)
    (errorSampler : ProbComp R) (adversary : HintDistinguisher Hint R) : ℝ :=
  (twoCopyRealGame encoding secretSampler maskSampler errorSampler adversary).boolDistAdvantage
    (twoCopyIdealGame encoding secretSampler maskSampler adversary)

theorem twoCopyRLWEAdvantage_eq_half_secondMoment
    {R Secret Mask Hint : Type}
    [Ring R] [DecidableEq R] [SampleableType R]
    [Fintype Secret] [Fintype Hint]
    (encoding : Encoding R Secret Mask Hint)
    (secretSampler : ProbComp Secret) (maskSampler : ProbComp Mask)
    (errorSampler : ProbComp R) (adversary : HintDistinguisher Hint R) :
    twoCopyRLWEAdvantage encoding secretSampler maskSampler errorSampler adversary =
      BoundedMoment.expectation
        (independentContextSampler encoding secretSampler maskSampler)
        (fun context ↦ contextGap encoding errorSampler adversary context ^ 2) / 2 := by
  have hReal := SquaredBias.probOutput_contextualExperiment_true
    (independentContextSampler encoding secretSampler maskSampler)
    (contextReal encoding errorSampler adversary)
    (contextIdeal encoding adversary)
  have hReal' :
      Pr[= true | twoCopyRealGame encoding secretSampler maskSampler
        errorSampler adversary].toReal =
        (1 + BoundedMoment.expectation
          (independentContextSampler encoding secretSampler maskSampler)
          (fun context ↦ contextGap encoding errorSampler adversary context ^ 2)) / 2 := by
    simpa only [twoCopyRealGame, contextGap] using hReal
  have hIdeal' :
      Pr[= true | twoCopyIdealGame encoding secretSampler maskSampler adversary].toReal =
        1 / 2 := by
    rw [show twoCopyIdealGame encoding secretSampler maskSampler adversary =
        SquaredBias.contextualExperiment
          (independentContextSampler encoding secretSampler maskSampler)
          (contextIdeal encoding adversary) (contextIdeal encoding adversary) by rfl,
      SquaredBias.probOutput_contextualExperiment_true]
    simp only [SquaredBias.signedGap, sub_self, OfNat.ofNat]
    rw [BoundedMoment.expectation_const]
    norm_num
  have hNonneg : 0 ≤ BoundedMoment.expectation
      (independentContextSampler encoding secretSampler maskSampler)
      (fun context ↦ contextGap encoding errorSampler adversary context ^ 2) :=
    BoundedMoment.secondMoment_nonneg _ _
  unfold twoCopyRLWEAdvantage ProbComp.boolDistAdvantage
  rw [hReal', hIdeal', abs_of_nonneg]
  · ring
  · linarith

/-- **Randomized-hint squared-bias theorem.** -/
theorem hintAdvantage_sq_le_two_mul_densityCost_mul_twoCopy
    {R Secret Mask Hint : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Secret] [DecidableEq Secret]
    [Fintype Hint] [DecidableEq Hint]
    (encoding : Encoding R Secret Mask Hint)
    (secretSampler : ProbComp Secret) (maskSampler : ProbComp Mask)
    (errorSampler : ProbComp R) (adversary : HintDistinguisher Hint R) :
    hintAdvantage encoding secretSampler maskSampler errorSampler adversary ^ 2 ≤
      2 * hintDensityCost encoding secretSampler maskSampler *
        twoCopyRLWEAdvantage encoding secretSampler maskSampler errorSampler adversary := by
  have hMean := SquaredBias.signedGap_bind
    (jointContextSampler encoding secretSampler maskSampler)
    (contextReal encoding errorSampler adversary)
    (contextIdeal encoding adversary)
  have hWeighted :=
    sq_expectation_le_densitySecondMoment_mul_secondMoment
      (jointContextSampler encoding secretSampler maskSampler)
      (independentContextSampler encoding secretSampler maskSampler)
      (contextGap encoding errorSampler adversary)
      (independentContext_covers_jointContext encoding secretSampler maskSampler)
  unfold hintAdvantage hintedRealGame hintedIdealGame ProbComp.boolDistAdvantage
  rw [show
      |Pr[= true |
          jointContextSampler encoding secretSampler maskSampler >>=
            contextReal encoding errorSampler adversary].toReal -
        Pr[= true |
          jointContextSampler encoding secretSampler maskSampler >>=
            contextIdeal encoding adversary].toReal| ^ 2 =
        SquaredBias.signedGap
          (jointContextSampler encoding secretSampler maskSampler >>=
            contextReal encoding errorSampler adversary)
          (jointContextSampler encoding secretSampler maskSampler >>=
            contextIdeal encoding adversary) ^ 2 by
      rw [sq_abs]
      rfl,
    hMean]
  calc
    _ ≤ hintDensityCost encoding secretSampler maskSampler *
        BoundedMoment.expectation
          (independentContextSampler encoding secretSampler maskSampler)
          (fun context ↦ contextGap encoding errorSampler adversary context ^ 2) :=
      hWeighted
    _ = 2 * hintDensityCost encoding secretSampler maskSampler *
        twoCopyRLWEAdvantage encoding secretSampler maskSampler errorSampler adversary := by
      rw [twoCopyRLWEAdvantage_eq_half_secondMoment]
      ring

theorem hintAdvantage_le_sqrt_two_mul_densityCost_mul_twoCopy
    {R Secret Mask Hint : Type}
    [Ring R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Secret] [DecidableEq Secret]
    [Fintype Hint] [DecidableEq Hint]
    (encoding : Encoding R Secret Mask Hint)
    (secretSampler : ProbComp Secret) (maskSampler : ProbComp Mask)
    (errorSampler : ProbComp R) (adversary : HintDistinguisher Hint R) :
    hintAdvantage encoding secretSampler maskSampler errorSampler adversary ≤
      Real.sqrt (2 * hintDensityCost encoding secretSampler maskSampler *
        twoCopyRLWEAdvantage encoding secretSampler maskSampler errorSampler adversary) :=
  Real.le_sqrt_of_sq_le
    (hintAdvantage_sq_le_two_mul_densityCost_mul_twoCopy
      encoding secretSampler maskSampler errorSampler adversary)

/-! ## Quadratic KDM composition -/

abbrev Distinguisher (R : Type) := (R × R) → ProbComp Bool

/-- Public affine transform of one randomized-hint transcript. -/
def encodedQuadraticTransform
    {R Secret Mask Hint : Type} [Ring R]
    (encoding : Encoding R Secret Mask Hint) (transcript : HintTranscript Hint R) :
    R × R :=
  (transcript.mask - 2 * encoding.hintValue transcript.hint,
    transcript.body - encoding.hintValue transcript.hint ^ 2)

/-- Exact algebraic compiler identity for an arbitrary mask law. -/
theorem encodedQuadraticTransform_real
    {R Secret Mask Hint : Type} [CommRing R]
    (encoding : Encoding R Secret Mask Hint)
    (secret : Secret) (mask : Mask) (publicMask error : R) :
    encodedQuadraticTransform encoding
        ⟨encoding.hint secret mask, publicMask,
          publicMask * encoding.secretValue secret + error⟩ =
      (publicMask - 2 * (encoding.secretValue secret - encoding.maskValue mask),
        (publicMask - 2 * (encoding.secretValue secret - encoding.maskValue mask)) *
            encoding.secretValue secret + encoding.secretValue secret ^ 2 +
          (error - encoding.maskValue mask ^ 2)) := by
  rw [encodedQuadraticTransform, encoding.hintValue_hint]
  apply Prod.ext
  · rfl
  · dsimp
    ring

/-- Public reduction from quadratic-row distinguishing to randomized hinted RLWE. -/
def quadraticReduction
    {R Secret Mask Hint : Type} [Ring R]
    (encoding : Encoding R Secret Mask Hint) (adversary : Distinguisher R) :
    HintDistinguisher Hint R :=
  fun transcript ↦ adversary (encodedQuadraticTransform encoding transcript)

/-- Compiled quadratic real game.  The preceding identity exposes its canonical phase as
`S² + E - Z²`. -/
def quadraticRealGame
    {R Secret Mask Hint : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (encoding : Encoding R Secret Mask Hint)
    (secretSampler : ProbComp Secret) (maskSampler : ProbComp Mask)
    (errorSampler : ProbComp R) (adversary : Distinguisher R) : ProbComp Bool :=
  hintedRealGame encoding secretSampler maskSampler errorSampler
    (quadraticReduction encoding adversary)

/-- The transformed random hinted branch used as the middle hybrid. -/
def quadraticRandomGame
    {R Secret Mask Hint : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (encoding : Encoding R Secret Mask Hint)
    (secretSampler : ProbComp Secret) (maskSampler : ProbComp Mask)
    (adversary : Distinguisher R) : ProbComp Bool :=
  hintedIdealGame encoding secretSampler maskSampler
    (quadraticReduction encoding adversary)

/-- Canonical zero-message endpoint with the same effective error `E-Z²`. -/
def zeroRealGame
    {R Secret Mask Hint : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (encoding : Encoding R Secret Mask Hint)
    (secretSampler : ProbComp Secret) (maskSampler : ProbComp Mask)
    (errorSampler : ProbComp R) (adversary : Distinguisher R) : ProbComp Bool := do
  let secret ← secretSampler
  let mask ← maskSampler
  let publicMask ← $ᵗ R
  let error ← errorSampler
  adversary (publicMask,
    publicMask * encoding.secretValue secret +
      (error - encoding.maskValue mask ^ 2))

/-- Quadratic-versus-zero KDM advantage for arbitrary secret and mask samplers. -/
def kdmAdvantage
    {R Secret Mask Hint : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (encoding : Encoding R Secret Mask Hint)
    (secretSampler : ProbComp Secret) (maskSampler : ProbComp Mask)
    (errorSampler : ProbComp R) (adversary : Distinguisher R) : ℝ :=
  (quadraticRealGame encoding secretSampler maskSampler errorSampler adversary).boolDistAdvantage
    (zeroRealGame encoding secretSampler maskSampler errorSampler adversary)

/-- Standard zero-message endpoint charge.  Its middle game is a public bijective transform of
uniform ring pairs; a concrete ordinary-RLWE reduction can target this exact game. -/
def zeroEndpointAdvantage
    {R Secret Mask Hint : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (encoding : Encoding R Secret Mask Hint)
    (secretSampler : ProbComp Secret) (maskSampler : ProbComp Mask)
    (errorSampler : ProbComp R) (adversary : Distinguisher R) : ℝ :=
  (quadraticRandomGame encoding secretSampler maskSampler adversary).boolDistAdvantage
    (zeroRealGame encoding secretSampler maskSampler errorSampler adversary)

/-- For each fixed hint, the affine transform of a pair is a bijection. -/
theorem encodedQuadraticTransform_pair_bijective
    {R Secret Mask Hint : Type} [Ring R]
    (encoding : Encoding R Secret Mask Hint) (hint : Hint) :
    Function.Bijective (fun sample : R × R ↦
      (sample.1 - 2 * encoding.hintValue hint,
        sample.2 - encoding.hintValue hint ^ 2)) := by
  let inverse : R × R → R × R := fun sample ↦
    (sample.1 + 2 * encoding.hintValue hint,
      sample.2 + encoding.hintValue hint ^ 2)
  refine Function.bijective_iff_has_inverse.mpr ⟨inverse, ?_, ?_⟩
  · intro sample
    apply Prod.ext <;> simp [inverse]
  · intro sample
    apply Prod.ext <;> simp [inverse]

/-- The transformed random hinted branch is exactly uniform. -/
theorem quadraticRandomGame_evalDist_uniform
    {R Secret Mask Hint : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Secret] [Fintype Hint]
    (encoding : Encoding R Secret Mask Hint)
    (secretSampler : ProbComp Secret) (maskSampler : ProbComp Mask)
    (adversary : Distinguisher R) :
    evalDist (quadraticRandomGame encoding secretSampler maskSampler adversary) =
      evalDist (uniformBlock (R := R) >>= adversary) := by
  unfold quadraticRandomGame hintedIdealGame contextIdeal quadraticReduction
  change evalDist
      (jointContextSampler encoding secretSampler maskSampler >>= fun context ↦
        ($ᵗ (R × R)) >>= fun sample ↦
          adversary
            (sample.1 - 2 * encoding.hintValue context.1,
              sample.2 - encoding.hintValue context.1 ^ 2)) = _
  calc
    _ = evalDist
        (jointContextSampler encoding secretSampler maskSampler >>= fun _context ↦
          ($ᵗ (R × R)) >>= adversary) := by
      refine evalDist_bind_congr'
        (jointContextSampler encoding secretSampler maskSampler) fun context ↦ ?_
      let transform : R × R → R × R := fun sample ↦
        (sample.1 - 2 * encoding.hintValue context.1,
          sample.2 - encoding.hintValue context.1 ^ 2)
      have hUniform :
          evalDist (transform <$> ($ᵗ (R × R))) = evalDist ($ᵗ (R × R)) :=
        evalDist_map_bijective_uniform_cross
          (α := R × R) (β := R × R) transform
          (encodedQuadraticTransform_pair_bijective encoding context.1)
      simpa only [transform, map_eq_bind_pure_comp, Function.comp_def, bind_assoc,
        pure_bind] using
          FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
            hUniform adversary
    _ = evalDist (($ᵗ (R × R)) >>= adversary) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        (jointContextSampler encoding secretSampler maskSampler) (by simp) _

/-- One-sample ordinary RLWE problem with the selected arbitrary secret law. -/
def oneSampleProblem
    {R Secret Mask Hint : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    (encoding : Encoding R Secret Mask Hint)
    (secretSampler : ProbComp Secret) (errorSampler : ProbComp R) :
    LearningWithErrors.Problem R Secret R where
  sampleChallenge := $ᵗ R
  sampleSecret := secretSampler
  sampleError := errorSampler
  noiseless := fun secret publicMask ↦ publicMask * encoding.secretValue secret
  sampleUniform := $ᵗ R

/-- Subtract an independently sampled mask square from an ordinary RLWE body. -/
def zeroReduction
    {R Secret Mask Hint : Type}
    [CommRing R] [DecidableEq R] [SampleableType R]
    {errorSampler : ProbComp R}
    (encoding : Encoding R Secret Mask Hint)
    (secretSampler : ProbComp Secret) (maskSampler : ProbComp Mask)
    (adversary : Distinguisher R) :
    LearningWithErrors.Adversary
      (oneSampleProblem encoding secretSampler errorSampler) :=
  fun transcript ↦ do
    let mask ← maskSampler
    adversary (transcript.1,
      transcript.2 - encoding.maskValue mask ^ 2)

theorem zeroReduction_real_evalDist
    {R Secret Mask Hint : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Secret] [Fintype Mask]
    (encoding : Encoding R Secret Mask Hint)
    (secretSampler : ProbComp Secret) (maskSampler : ProbComp Mask)
    (errorSampler : ProbComp R) (adversary : Distinguisher R) :
    evalDist (LearningWithErrors.game0
        (oneSampleProblem encoding secretSampler errorSampler)
        (zeroReduction encoding secretSampler maskSampler adversary)) =
      evalDist
        (zeroRealGame encoding secretSampler maskSampler errorSampler adversary) := by
  simp only [LearningWithErrors.game0, LearningWithErrors.distr, oneSampleProblem,
    zeroReduction, zeroRealGame, bind_assoc, pure_bind]
  calc
    evalDist (($ᵗ R) >>= fun publicMask ↦
        secretSampler >>= fun secret ↦
          errorSampler >>= fun error ↦
            maskSampler >>= fun mask ↦
              adversary (publicMask,
                publicMask * encoding.secretValue secret + error -
                  encoding.maskValue mask ^ 2)) =
      evalDist (secretSampler >>= fun secret ↦
        ($ᵗ R) >>= fun publicMask ↦
          errorSampler >>= fun error ↦
            maskSampler >>= fun mask ↦
              adversary (publicMask,
                publicMask * encoding.secretValue secret + error -
                  encoding.maskValue mask ^ 2)) :=
        evalDist_bind_bind_swap ($ᵗ R) secretSampler _
    _ = evalDist (secretSampler >>= fun secret ↦
        ($ᵗ R) >>= fun publicMask ↦
          maskSampler >>= fun mask ↦
            errorSampler >>= fun error ↦
              adversary (publicMask,
                publicMask * encoding.secretValue secret + error -
                  encoding.maskValue mask ^ 2)) := by
      refine evalDist_bind_congr' secretSampler fun secret ↦ ?_
      refine evalDist_bind_congr' ($ᵗ R) fun publicMask ↦ ?_
      exact evalDist_bind_bind_swap errorSampler maskSampler _
    _ = evalDist (secretSampler >>= fun secret ↦
        maskSampler >>= fun mask ↦
          ($ᵗ R) >>= fun publicMask ↦
            errorSampler >>= fun error ↦
              adversary (publicMask,
                publicMask * encoding.secretValue secret +
                  (error - encoding.maskValue mask ^ 2))) := by
      refine evalDist_bind_congr' secretSampler fun secret ↦ ?_
      calc
        _ = evalDist (maskSampler >>= fun mask ↦
            ($ᵗ R) >>= fun publicMask ↦
              errorSampler >>= fun error ↦
                adversary (publicMask,
                  publicMask * encoding.secretValue secret + error -
                    encoding.maskValue mask ^ 2)) :=
          evalDist_bind_bind_swap ($ᵗ R) maskSampler _
        _ = _ := by
          refine evalDist_bind_congr' maskSampler fun mask ↦ ?_
          refine evalDist_bind_congr' ($ᵗ R) fun publicMask ↦ ?_
          refine evalDist_bind_congr' errorSampler fun error ↦ ?_
          congr 2
          ring_nf

/-- Translating the second uniform coordinate by a fixed mask square is bijective. -/
theorem zeroShift_bijective {R : Type} [Ring R] (mask : R) :
    Function.Bijective (fun transcript : R × R ↦
      (transcript.1, transcript.2 - mask ^ 2)) := by
  let inverse : R × R → R × R := fun transcript ↦
    (transcript.1, transcript.2 + mask ^ 2)
  refine Function.bijective_iff_has_inverse.mpr ⟨inverse, ?_, ?_⟩
  · intro transcript
    apply Prod.ext <;> simp [inverse]
  · intro transcript
    apply Prod.ext <;> simp [inverse]

theorem zeroReduction_random_evalDist
    {R Secret Mask Hint : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Secret] [Fintype Mask]
    (encoding : Encoding R Secret Mask Hint)
    (secretSampler : ProbComp Secret) (maskSampler : ProbComp Mask)
    (errorSampler : ProbComp R) (adversary : Distinguisher R) :
    evalDist (LearningWithErrors.game1
        (oneSampleProblem encoding secretSampler errorSampler)
        (zeroReduction encoding secretSampler maskSampler adversary)) =
      evalDist (uniformBlock (R := R) >>= adversary) := by
  simp only [LearningWithErrors.game1, LearningWithErrors.uniformDistr,
    oneSampleProblem, zeroReduction, uniformBlock, bind_assoc, pure_bind]
  calc
    evalDist (($ᵗ R) >>= fun publicMask ↦
        ($ᵗ R) >>= fun body ↦
          maskSampler >>= fun mask ↦
            adversary (publicMask, body - encoding.maskValue mask ^ 2)) =
      evalDist (maskSampler >>= fun mask ↦
        ($ᵗ (R × R)) >>= fun transcript ↦
          adversary (transcript.1,
            transcript.2 - encoding.maskValue mask ^ 2)) := by
      calc
        _ = evalDist (($ᵗ R) >>= fun publicMask ↦
            maskSampler >>= fun mask ↦
              ($ᵗ R) >>= fun body ↦
                adversary (publicMask,
                  body - encoding.maskValue mask ^ 2)) := by
          refine evalDist_bind_congr' ($ᵗ R) fun publicMask ↦ ?_
          exact evalDist_bind_bind_swap ($ᵗ R) maskSampler _
        _ = evalDist (maskSampler >>= fun mask ↦
            ($ᵗ R) >>= fun publicMask ↦
              ($ᵗ R) >>= fun body ↦
                adversary (publicMask,
                  body - encoding.maskValue mask ^ 2)) :=
          evalDist_bind_bind_swap ($ᵗ R) maskSampler _
        _ = _ := by
          refine evalDist_bind_congr' maskSampler fun mask ↦ ?_
          have hProduct :=
            FormalProof4FHE.FiniteProduct.evalDist_independent_uniform_product
              (first := R) (second := R)
          simpa only [bind_assoc, pure_bind] using
            FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
              hProduct
              (fun transcript : R × R ↦
                adversary (transcript.1,
                  transcript.2 - encoding.maskValue mask ^ 2))
    _ = evalDist (maskSampler >>= fun _mask ↦
        ($ᵗ (R × R)) >>= adversary) := by
      refine evalDist_bind_congr' maskSampler fun mask ↦ ?_
      let transform : R × R → R × R := fun transcript ↦
        (transcript.1, transcript.2 - encoding.maskValue mask ^ 2)
      have hUniform :
          evalDist (transform <$> ($ᵗ (R × R))) = evalDist ($ᵗ (R × R)) :=
        evalDist_map_bijective_uniform_cross
          (α := R × R) (β := R × R) transform
          (zeroShift_bijective (encoding.maskValue mask))
      simpa only [transform, map_eq_bind_pure_comp, Function.comp_def, bind_assoc,
        pure_bind] using
          FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
            hUniform adversary
    _ = evalDist (($ᵗ (R × R)) >>= adversary) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        maskSampler (by simp) _

/-- The named zero endpoint is exactly an ordinary one-sample RLWE advantage. -/
theorem zeroEndpointAdvantage_eq_lwe
    {R Secret Mask Hint : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Secret] [Fintype Mask] [Fintype Hint]
    (encoding : Encoding R Secret Mask Hint)
    (secretSampler : ProbComp Secret) (maskSampler : ProbComp Mask)
    (errorSampler : ProbComp R) (adversary : Distinguisher R) :
    zeroEndpointAdvantage encoding secretSampler maskSampler errorSampler adversary =
      LearningWithErrors.advantage
        (oneSampleProblem encoding secretSampler errorSampler)
        (zeroReduction encoding secretSampler maskSampler adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold zeroEndpointAdvantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (quadraticRandomGame_evalDist_uniform
        encoding secretSampler maskSampler adversary) true,
    evalDist_ext_iff.mp
      (zeroReduction_real_evalDist
        encoding secretSampler maskSampler errorSampler adversary) true,
    evalDist_ext_iff.mp
      (zeroReduction_random_evalDist
        encoding secretSampler maskSampler errorSampler adversary) true,
    abs_sub_comm]

/-- Hybrid composition: randomized hinted RLWE plus the standard zero-message endpoint implies
quadratic KDM security. -/
theorem kdmAdvantage_le_hint_add_zeroEndpoint
    {R Secret Mask Hint : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Secret] [Fintype Hint]
    (encoding : Encoding R Secret Mask Hint)
    (secretSampler : ProbComp Secret) (maskSampler : ProbComp Mask)
    (errorSampler : ProbComp R) (adversary : Distinguisher R) :
    kdmAdvantage encoding secretSampler maskSampler errorSampler adversary ≤
      hintAdvantage encoding secretSampler maskSampler errorSampler
          (quadraticReduction encoding adversary) +
        zeroEndpointAdvantage encoding secretSampler maskSampler errorSampler adversary := by
  unfold kdmAdvantage quadraticRealGame hintAdvantage zeroEndpointAdvantage
    quadraticRandomGame
  exact ProbComp.boolDistAdvantage_triangle
    (hintedRealGame encoding secretSampler maskSampler errorSampler
      (quadraticReduction encoding adversary))
    (hintedIdealGame encoding secretSampler maskSampler
      (quadraticReduction encoding adversary))
    (zeroRealGame encoding secretSampler maskSampler errorSampler adversary)

/-- Main arbitrary-law quadratic KDM theorem. -/
theorem kdmAdvantage_le_sqrt_densityCost_add_zeroEndpoint
    {R Secret Mask Hint : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    [Fintype Secret] [DecidableEq Secret]
    [Fintype Hint] [DecidableEq Hint]
    (encoding : Encoding R Secret Mask Hint)
    (secretSampler : ProbComp Secret) (maskSampler : ProbComp Mask)
    (errorSampler : ProbComp R) (adversary : Distinguisher R) :
    kdmAdvantage encoding secretSampler maskSampler errorSampler adversary ≤
      Real.sqrt (2 * hintDensityCost encoding secretSampler maskSampler *
        twoCopyRLWEAdvantage encoding secretSampler maskSampler errorSampler
          (quadraticReduction encoding adversary)) +
      zeroEndpointAdvantage encoding secretSampler maskSampler errorSampler adversary := by
  exact (kdmAdvantage_le_hint_add_zeroEndpoint
      encoding secretSampler maskSampler errorSampler adversary).trans
    (add_le_add
      (hintAdvantage_le_sqrt_two_mul_densityCost_mul_twoCopy
        encoding secretSampler maskSampler errorSampler
          (quadraticReduction encoding adversary)) le_rfl)

/-! ## CBD instantiation and exact quadratic residual -/

/- Keep one coherent algebra dictionary for the executable negacyclic carrier. -/
local instance cbdRqCommRing (q degree : ℕ) : CommRing (Rq q degree) :=
  LatticeCrypto.vectorNegacyclicRing_instCommRing (ZMod q) degree

local instance cbdRqAddCommGroup (q degree : ℕ) : AddCommGroup (Rq q degree) :=
  (cbdRqCommRing q degree).toAddCommGroup

local instance cbdRqAdd (q degree : ℕ) : Add (Rq q degree) :=
  (cbdRqAddCommGroup q degree).toAdd

local instance cbdRqSub (q degree : ℕ) : Sub (Rq q degree) :=
  (cbdRqCommRing q degree).toAddGroupWithOne.toAddGroup.toSub

local instance cbdRqNeg (q degree : ℕ) : Neg (Rq q degree) :=
  (cbdRqAddCommGroup q degree).toNeg

local instance cbdRqZero (q degree : ℕ) : Zero (Rq q degree) :=
  (cbdRqAddCommGroup q degree).toZero

/-- Ring-valued difference hint `H = S - Z`. -/
def differenceEncoding
    {R Secret : Type} [Sub R] (secretValue : Secret → R) :
    Encoding R Secret R R where
  secretValue := secretValue
  maskValue := id
  hint secret mask := secretValue secret - mask
  hintValue := id
  hintValue_hint := fun _ _ ↦ rfl

/-- Two independent samples from one finite sampler. -/
def independentPairSampler {A : Type} (sampler : ProbComp A) : ProbComp (A × A) := do
  let first ← sampler
  let second ← sampler
  return (first, second)

/-- Two difference hints, encoded as one product-ring hint channel.  Its source secret is the
diagonal pair `(S,S)` and its mask is `(Z₁,Z₂)`. -/
def doubleDifferenceEncoding
    {R Secret : Type} [AddGroup R] (secretValue : Secret → R) :
    Encoding (R × R) Secret (R × R) (R × R) where
  secretValue secret := (secretValue secret, secretValue secret)
  maskValue := id
  hint secret mask :=
    (secretValue secret - mask.1, secretValue secret - mask.2)
  hintValue := id
  hintValue_hint := by
    intro secret mask
    rfl

/-- Exact finite CBD hint-concentration constant, suitable for external parameter evaluation. -/
def cbdHintDensityCost
    (q degree eta : ℕ) [NeZero q]
    {Secret : Type} [Fintype Secret]
    (secretSampler : ProbComp Secret) (secretValue : Secret → Rq q degree) : ℝ :=
  hintDensityCost (differenceEncoding secretValue) secretSampler
    (CenteredBinomial.sampler q degree eta)

/-- Exact density cost for the joint pair `(S-Z₁,S-Z₂)` with independent CBD masks. -/
def cbdTwoHintDensityCost
    (q degree eta : ℕ) [NeZero q]
    {Secret : Type} [Fintype Secret]
    (secretSampler : ProbComp Secret) (secretValue : Secret → Rq q degree) : ℝ :=
  hintDensityCost (doubleDifferenceEncoding secretValue) secretSampler
    (independentPairSampler (CenteredBinomial.sampler q degree eta))

/-- CBD masks obtain the generic weighted hinted-RLWE bound with no uniformity or injectivity
assumption on the CBD output law. -/
theorem cbd_hintAdvantage_le
    (q degree eta : ℕ) [NeZero q]
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (secretSampler : ProbComp Secret)
    (secretValue : Secret → Rq q degree)
    (errorSampler : ProbComp (Rq q degree))
    (adversary : HintDistinguisher
      (Rq q degree) (Rq q degree)) :
    hintAdvantage (differenceEncoding secretValue) secretSampler
        (CenteredBinomial.sampler q degree eta) errorSampler adversary ≤
      Real.sqrt
        (2 * cbdHintDensityCost q degree eta secretSampler secretValue *
          twoCopyRLWEAdvantage (differenceEncoding secretValue) secretSampler
            (CenteredBinomial.sampler q degree eta) errorSampler adversary) := by
  simpa only [cbdHintDensityCost] using
    hintAdvantage_le_sqrt_two_mul_densityCost_mul_twoCopy
    (differenceEncoding secretValue) secretSampler
    (CenteredBinomial.sampler q degree eta) errorSampler adversary

/-- End-to-end one-hint CBD quadratic-KDM theorem, up to the ordinary zero-message endpoint. -/
theorem cbd_kdmAdvantage_le
    (q degree eta : ℕ) [NeZero q]
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (secretSampler : ProbComp Secret)
    (secretValue : Secret → Rq q degree)
    (errorSampler : ProbComp (Rq q degree))
    (adversary : Distinguisher (Rq q degree)) :
    kdmAdvantage (differenceEncoding secretValue) secretSampler
        (CenteredBinomial.sampler q degree eta) errorSampler adversary ≤
      Real.sqrt
        (2 * cbdHintDensityCost q degree eta secretSampler secretValue *
          twoCopyRLWEAdvantage (differenceEncoding secretValue) secretSampler
            (CenteredBinomial.sampler q degree eta) errorSampler
            (quadraticReduction (differenceEncoding secretValue) adversary)) +
      zeroEndpointAdvantage (differenceEncoding secretValue) secretSampler
        (CenteredBinomial.sampler q degree eta) errorSampler adversary := by
  simpa only [cbdHintDensityCost] using
    kdmAdvantage_le_sqrt_densityCost_add_zeroEndpoint
      (differenceEncoding secretValue) secretSampler
      (CenteredBinomial.sampler q degree eta) errorSampler adversary

/-- Same CBD theorem with the endpoint discharged by the explicit ordinary one-sample RLWE
reduction. -/
theorem cbd_kdmAdvantage_le_standardRLWE
    (q degree eta : ℕ) [NeZero q]
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (secretSampler : ProbComp Secret)
    (secretValue : Secret → Rq q degree)
    (errorSampler : ProbComp (Rq q degree))
    (adversary : Distinguisher (Rq q degree)) :
    kdmAdvantage (differenceEncoding secretValue) secretSampler
        (CenteredBinomial.sampler q degree eta) errorSampler adversary ≤
      Real.sqrt
        (2 * cbdHintDensityCost q degree eta secretSampler secretValue *
          twoCopyRLWEAdvantage (differenceEncoding secretValue) secretSampler
            (CenteredBinomial.sampler q degree eta) errorSampler
            (quadraticReduction (differenceEncoding secretValue) adversary)) +
      LearningWithErrors.advantage
        (oneSampleProblem (differenceEncoding secretValue) secretSampler errorSampler)
        (zeroReduction (differenceEncoding secretValue) secretSampler
          (CenteredBinomial.sampler q degree eta) adversary) := by
  rw [← zeroEndpointAdvantage_eq_lwe
    (differenceEncoding secretValue) secretSampler
    (CenteredBinomial.sampler q degree eta) errorSampler adversary]
  exact cbd_kdmAdvantage_le q degree eta secretSampler secretValue
    errorSampler adversary

/-- Weighted hinted-RLWE bound for two independent CBD difference hints.  The source block is
over the product ring and therefore represents two same-secret RLWE rows. -/
theorem cbd_twoHintAdvantage_le
    (q degree eta : ℕ) [NeZero q]
    {Secret : Type} [Fintype Secret] [DecidableEq Secret]
    (secretSampler : ProbComp Secret)
    (secretValue : Secret → Rq q degree)
    (errorSampler : ProbComp (Rq q degree × Rq q degree))
    (adversary : HintDistinguisher
      (Rq q degree × Rq q degree) (Rq q degree × Rq q degree)) :
    hintAdvantage (doubleDifferenceEncoding secretValue) secretSampler
        (independentPairSampler (CenteredBinomial.sampler q degree eta))
        errorSampler adversary ≤
      Real.sqrt
        (2 * cbdTwoHintDensityCost q degree eta secretSampler secretValue *
          twoCopyRLWEAdvantage (doubleDifferenceEncoding secretValue) secretSampler
            (independentPairSampler (CenteredBinomial.sampler q degree eta))
            errorSampler adversary) := by
  simpa only [cbdTwoHintDensityCost] using
    hintAdvantage_le_sqrt_two_mul_densityCost_mul_twoCopy
      (doubleDifferenceEncoding secretValue) secretSampler
      (independentPairSampler (CenteredBinomial.sampler q degree eta))
      errorSampler adversary

/-- Public affine transform for a ring-valued difference hint. -/
def quadraticTransform {R : Type} [Ring R]
    (transcript : HintTranscript R R) : R × R :=
  (transcript.mask - 2 * transcript.hint,
    transcript.body - transcript.hint ^ 2)

/-- The one-hint compiler identity is exact for CBD as for every other mask law. -/
theorem quadraticTransform_real
    {R : Type} [CommRing R] (secret mask publicMask error : R) :
    quadraticTransform
        ⟨secret - mask, publicMask, publicMask * secret + error⟩ =
      (publicMask - 2 * (secret - mask),
        (publicMask - 2 * (secret - mask)) * secret + secret ^ 2 +
          (error - mask ^ 2)) := by
  apply Prod.ext
  · rfl
  · dsimp [quadraticTransform]
    ring

/-- Adding a public centre `mu` merely rewrites the residual as `E - (Z² - mu)`. -/
theorem quadraticTransform_real_centered
    {R : Type} [CommRing R] (secret mask publicMask error mu : R) :
    let transformed := quadraticTransform
      ⟨secret - mask, publicMask, publicMask * secret + error⟩
    (transformed.1, transformed.2 + mu) =
      (publicMask - 2 * (secret - mask),
        (publicMask - 2 * (secret - mask)) * secret + secret ^ 2 +
          (error - (mask ^ 2 - mu))) := by
  rw [quadraticTransform_real]
  dsimp
  apply Prod.ext
  · rfl
  · ring

/-- Public two-hint compiler.  It consumes two hinted RLWE rows and returns one quadratic row. -/
def twoHintQuadraticTransform {R : Type} [Ring R]
    (transcript : HintTranscript (R × R) (R × R)) : R × R :=
  (transcript.mask.1 + transcript.mask.2 - transcript.hint.1 - transcript.hint.2,
    transcript.body.1 + transcript.body.2 - transcript.hint.1 * transcript.hint.2)

/-- **Independent-product residual identity.**  For `Hᵢ=S-Zᵢ`, two hinted rows compile to an
encryption of `S²` whose extra residual is `-Z₁Z₂`, instead of the correlated square
`-Z²` left by the one-hint compiler. -/
theorem twoHintQuadraticTransform_real
    {R : Type} [CommRing R]
    (secret mask₁ mask₂ publicMask₁ publicMask₂ error₁ error₂ : R) :
    twoHintQuadraticTransform
        ⟨(secret - mask₁, secret - mask₂),
          (publicMask₁, publicMask₂),
          (publicMask₁ * secret + error₁,
            publicMask₂ * secret + error₂)⟩ =
      (publicMask₁ + publicMask₂ - (secret - mask₁) - (secret - mask₂),
        (publicMask₁ + publicMask₂ - (secret - mask₁) - (secret - mask₂)) *
            secret + secret ^ 2 + (error₁ + error₂ - mask₁ * mask₂)) := by
  apply Prod.ext
  · rfl
  · dsimp [twoHintQuadraticTransform]
    ring

end

end FormalProof4FHE.RLWE.CenteredBinomialHintedQuadratic
