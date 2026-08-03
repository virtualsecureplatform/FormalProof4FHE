/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.SubspaceLWE.Simulator
import FormalProof4FHE.TFHE.NativeTRGSWHashCompressedSecurity
import FormalProof4FHE.TFHE.NativeTRGSWAggregateRobustLeakage
import FormalProof4FHE.TFHE.NativeTRGSWHardTheoremComposition

/-!
# Hash-lossy complete-view security for native TFHE

This module formalizes the finite mathematical content of
`sketch/hash_lossy_complete_view_native_tfhe.tex`.

There are four proved components.

* A surjective linear hash gives an executable uniform-fiber resampler.  Complete views generated
  after resampling depend only on the digest, and resampling a uniform prefix preserves its exact
  marginal distribution.
* The projected match-and-square estimate is combined with approximate uniform-source branch
  erasure.  For a balanced `r`-bit digest, the concentration is exactly `2 ^ r`; ordinary/lossy
  mode switches and the final sampler defect are then composed without duplicate charges.
* Existing Walsh high-pass results imply both the exact injectivity barrier and its robust
  total-variation-scale counterpart for phase-oblivious translation builders.
* A finite mass-table theorem proves the information-theoretic decoding barrier.  A view which
  factors through a digest permits prefix recovery with probability at most
  `|Digest| / |Prefix|`, and total variation transfers this into the stated mode-switch lower
  bound.

The module does not construct the cryptographic ordinary/lossy native BRK/KSK/auxiliary
generator.  Its mode-switch, diagonal correctness, source advantage, and sampler terms remain
explicit theorem premises, exactly as required by the manuscript.
-/

set_option autoImplicit false

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.NativeTRGSWHashLossyCompleteView

noncomputable section

open FormalProof4FHE.GeneralizedSubspaceLWE.Adaptive
open NativeTRGSWAggregateProjectedLeakage
open NativeTRGSWAggregateSecurityAndComplexityLeveraging
open NativeTRGSWAggregateRobustLeakage
open NativeTRGSWHashCompressedSecurity
open NativeTRGSWBarrierAndSpectralBoundary
open RGSWCoefficientCircularSecurity

/-! ## Optimal digest matching -/

/-- The square-root-tilted law is optimal for digest matching: every fake-digest distribution
covering the actual digest law pays at least its Renyi-half concentration. -/
theorem projectedLeakageConcentration_le_gamma
    {Key Digest : Type} [Fintype Key] [Fintype Digest]
    (keySampler : ProbComp Key) (fakeDigestSampler : ProbComp Digest)
    (digest : Key → Digest)
    (hcover : ∀ digestValue,
      probabilityMass (leakageLaw keySampler digest) digestValue ≠ 0 →
        probabilityMass fakeDigestSampler digestValue ≠ 0) :
    projectedLeakageConcentration keySampler digest ≤
      leakageGamma keySampler fakeDigestSampler digest := by
  classical
  let digestSampler := leakageLaw keySampler digest
  have hfull := fullKeyConcentration_le_leakageGamma
    digestSampler fakeDigestSampler hcover
  unfold fullKeyConcentration at hfull
  unfold projectedLeakageConcentration
  rw [leakageGamma_eq_sum_ratio] at hfull
  rw [leakageGamma_eq_sum_ratio]
  unfold halfRenyiConcentration at hfull ⊢
  simp_rw [probabilityMass_leakageLaw_id] at hfull
  simpa [digestSampler] using hfull

/-- A sampler realizing the square-root tilt attains the preceding lower bound exactly. -/
theorem projectedLeakageGamma_eq_concentration_of_squareRootTilt
    {Key Digest : Type} [Fintype Key] [Fintype Digest]
    (keySampler : ProbComp Key) (fakeDigestSampler : ProbComp Digest)
    (digest : Key → Digest)
    (hoptimized : ∀ digestValue,
      probabilityMass fakeDigestSampler digestValue =
        Real.sqrt
            (probabilityMass (leakageLaw keySampler digest) digestValue) /
          halfRenyiNormalizer keySampler digest) :
    leakageGamma keySampler fakeDigestSampler digest =
      projectedLeakageConcentration keySampler digest := by
  exact leakageGamma_eq_halfRenyiConcentration_of_optimizedLaw
    keySampler fakeDigestSampler digest hoptimized

/-! ## Exact uniform-fiber view mode -/

/-- Sample a uniformly random point in the fiber of `hash` containing `prefix`.  The affine-fiber
sampler is implemented by a linear splitting into the digest and kernel coordinates. -/
def hashFiberResample
    {K Prefix Digest : Type}
    [Field K]
    [AddCommGroup Prefix] [Module K Prefix] [Fintype Prefix]
    [AddCommGroup Digest] [Module K Digest] [Fintype Digest] [DecidableEq Digest]
    (hash : Prefix →ₗ[K] Digest) (hsurjective : Function.Surjective hash)
    (prefixValue : Prefix) : ProbComp Prefix :=
  samplePreimage hash hsurjective (hash prefixValue)

/-- Generate an arbitrary complete view after uniformly randomizing the latent prefix inside its
hash fiber.  `ordinary` may return a BRK, KSK, and all auxiliary objects in one joint carrier. -/
def hashFiberLossyView
    {K Prefix Digest Suffix View : Type}
    [Field K]
    [AddCommGroup Prefix] [Module K Prefix] [Fintype Prefix]
    [AddCommGroup Digest] [Module K Digest] [Fintype Digest] [DecidableEq Digest]
    (hash : Prefix →ₗ[K] Digest) (hsurjective : Function.Surjective hash)
    (ordinary : Prefix → Suffix → ProbComp View)
    (prefixValue : Prefix) (suffix : Suffix) : ProbComp View := do
  let randomizedPrefix ← hashFiberResample hash hsurjective prefixValue
  ordinary randomizedPrefix suffix

/-- Digest-only presentation of the same view-level simulator. -/
def hashDigestViewSimulator
    {K Prefix Digest Suffix View : Type}
    [Field K]
    [AddCommGroup Prefix] [Module K Prefix] [Fintype Prefix]
    [AddCommGroup Digest] [Module K Digest] [Fintype Digest] [DecidableEq Digest]
    (hash : Prefix →ₗ[K] Digest) (hsurjective : Function.Surjective hash)
    (ordinary : Prefix → Suffix → ProbComp View)
    (digest : Digest) (suffix : Suffix) : ProbComp View := do
  let randomizedPrefix ← samplePreimage hash hsurjective digest
  ordinary randomizedPrefix suffix

/-- The kernel-randomized view factors exactly through the public digest. -/
theorem hashFiberLossyView_evalDist_eq_digestSimulator
    {K Prefix Digest Suffix View : Type}
    [Field K]
    [AddCommGroup Prefix] [Module K Prefix] [Fintype Prefix]
    [AddCommGroup Digest] [Module K Digest] [Fintype Digest] [DecidableEq Digest]
    (hash : Prefix →ₗ[K] Digest) (hsurjective : Function.Surjective hash)
    (ordinary : Prefix → Suffix → ProbComp View)
    (prefixValue : Prefix) (suffix : Suffix) :
    evalDist (hashFiberLossyView hash hsurjective ordinary prefixValue suffix) =
      evalDist (hashDigestViewSimulator hash hsurjective ordinary (hash prefixValue) suffix) := by
  rfl

/-- Exact fiber invariance: two prefixes with the same digest induce identical complete-view
laws, with no assumption on the internal correlations of the ordinary view. -/
theorem hashFiberLossyView_evalDist_eq_of_hash_eq
    {K Prefix Digest Suffix View : Type}
    [Field K]
    [AddCommGroup Prefix] [Module K Prefix] [Fintype Prefix]
    [AddCommGroup Digest] [Module K Digest] [Fintype Digest] [DecidableEq Digest]
    (hash : Prefix →ₗ[K] Digest) (hsurjective : Function.Surjective hash)
    (ordinary : Prefix → Suffix → ProbComp View)
    (first second : Prefix) (suffix : Suffix)
    (hequal : hash first = hash second) :
    evalDist (hashFiberLossyView hash hsurjective ordinary first suffix) =
      evalDist (hashFiberLossyView hash hsurjective ordinary second suffix) := by
  simp only [hashFiberLossyView, hashFiberResample]
  rw [hequal]

/-- Resampling the fiber of a uniformly sampled prefix returns an exactly uniform prefix. -/
theorem hashFiberResample_uniform_evalDist
    {K Prefix Digest : Type}
    [Field K]
    [AddCommGroup Prefix] [Module K Prefix] [Fintype Prefix] [SampleableType Prefix]
    [AddCommGroup Digest] [Module K Digest] [Fintype Digest] [DecidableEq Digest]
    [SampleableType Digest]
    (hash : Prefix →ₗ[K] Digest) (hsurjective : Function.Surjective hash) :
    evalDist (do
      let prefixValue ← $ᵗ Prefix
      hashFiberResample hash hsurjective prefixValue) =
      evalDist ($ᵗ Prefix) := by
  have hhash :
      evalDist (hash <$> ($ᵗ Prefix)) = evalDist ($ᵗ Digest) := by
    have hsurjectiveAdd : Function.Surjective hash.toAddHom := by
      simpa using hsurjective
    have huniform :=
      NativeTRGSWHashCompressedSecurity.hasUniformOutput_of_surjectiveAddHom
        (Prefix := Prefix) (Digest := Digest) hash.toAddHom hsurjectiveAdd
    unfold HasUniformOutput at huniform
    simpa using huniform
  rw [show (do
      let prefixValue ← $ᵗ Prefix
      hashFiberResample hash hsurjective prefixValue) =
        (hash <$> ($ᵗ Prefix)) >>= fun digest ↦
          samplePreimage hash hsurjective digest by
      simp [hashFiberResample, monad_norm]]
  rw [evalDist_bind, hhash, ← evalDist_bind]
  exact evalDist_samplePreimage_uniformTarget hash hsurjective

/-- Ordinary complete-view marginal with an independent uniform prefix. -/
def ordinaryUniformPrefixView
    {Prefix Suffix View : Type} [SampleableType Prefix]
    (ordinary : Prefix → Suffix → ProbComp View)
    (suffixSampler : ProbComp Suffix) : ProbComp View := do
  let suffix ← suffixSampler
  let prefixValue ← $ᵗ Prefix
  ordinary prefixValue suffix

/-- Complete-view marginal after the formal hash-fiber randomization mode. -/
def lossyUniformPrefixView
    {K Prefix Digest Suffix View : Type}
    [Field K]
    [AddCommGroup Prefix] [Module K Prefix] [Fintype Prefix] [SampleableType Prefix]
    [AddCommGroup Digest] [Module K Digest] [Fintype Digest] [DecidableEq Digest]
    (hash : Prefix →ₗ[K] Digest) (hsurjective : Function.Surjective hash)
    (ordinary : Prefix → Suffix → ProbComp View)
    (suffixSampler : ProbComp Suffix) : ProbComp View := do
  let suffix ← suffixSampler
  let prefixValue ← $ᵗ Prefix
  hashFiberLossyView hash hsurjective ordinary prefixValue suffix

/-- With an independent uniform prefix, the ordinary and formal lossy public marginals are
exactly equal.  This is a distributional identity, not a source-coupled security reduction. -/
theorem lossyUniformPrefixView_evalDist_eq_ordinary
    {K Prefix Digest Suffix View : Type}
    [Field K]
    [AddCommGroup Prefix] [Module K Prefix] [Fintype Prefix] [SampleableType Prefix]
    [AddCommGroup Digest] [Module K Digest] [Fintype Digest] [DecidableEq Digest]
    [SampleableType Digest]
    (hash : Prefix →ₗ[K] Digest) (hsurjective : Function.Surjective hash)
    (ordinary : Prefix → Suffix → ProbComp View)
    (suffixSampler : ProbComp Suffix) :
    evalDist (lossyUniformPrefixView hash hsurjective ordinary suffixSampler) =
      evalDist (ordinaryUniformPrefixView ordinary suffixSampler) := by
  unfold lossyUniformPrefixView ordinaryUniformPrefixView
  apply evalDist_bind_congr' suffixSampler
  intro suffix
  rw [show (do
      let prefixValue ← $ᵗ Prefix
      hashFiberLossyView hash hsurjective ordinary prefixValue suffix) =
        (do
          let prefixValue ← $ᵗ Prefix
          hashFiberResample hash hsurjective prefixValue) >>= fun randomizedPrefix ↦
            ordinary randomizedPrefix suffix by
      simp [hashFiberLossyView, monad_norm]]
  rw [evalDist_bind, hashFiberResample_uniform_evalDist hash hsurjective,
    ← evalDist_bind]

/-! ## Digest match-and-square with approximate erasure -/

/-- Average conditional Renyi-half concentration when the public hash seed is sampled first and
then treated as public context. -/
def averagedConditionalDigestConcentration
    {HashSeed Prefix Suffix : Type} [Fintype HashSeed]
    [Fintype Prefix] [SampleableType Prefix]
    [Fintype Suffix] [SampleableType Suffix]
    [Fintype (Prefix × Suffix)] [SampleableType (Prefix × Suffix)]
    (hashSeedSampler : ProbComp HashSeed) (digestCount : ℕ)
    (hash : HashSeed → Prefix → (Fin digestCount → Bool)) : ℝ :=
  FormalProof4FHE.BoundedMoment.expectation hashSeedSampler fun hashSeed ↦
    projectedLeakageConcentration
      ($ᵗ (Prefix × Suffix))
      (hashedPrefixLeakage (Suffix := Suffix) (hash hashSeed))

/-- If every realized public hash is balanced, the averaged conditional concentration is exactly
`2 ^ r`; the entropy of the public hash seed itself is not charged. -/
theorem averagedConditionalDigestConcentration_eq_twoPow
    {HashSeed Prefix Suffix : Type} [Fintype HashSeed]
    [Fintype Prefix] [SampleableType Prefix]
    [Fintype Suffix] [SampleableType Suffix]
    [Fintype (Prefix × Suffix)] [SampleableType (Prefix × Suffix)]
    (hashSeedSampler : ProbComp HashSeed) (digestCount : ℕ)
    (hash : HashSeed → Prefix → (Fin digestCount → Bool))
    (huniform : ∀ hashSeed, HasUniformOutput (hash hashSeed)) :
    averagedConditionalDigestConcentration
      (Prefix := Prefix) (Suffix := Suffix)
      hashSeedSampler digestCount hash = (2 : ℝ) ^ digestCount := by
  unfold averagedConditionalDigestConcentration
  have hpoint :
      (fun hashSeed ↦
        projectedLeakageConcentration
          ($ᵗ (Prefix × Suffix))
          (hashedPrefixLeakage (Suffix := Suffix) (hash hashSeed))) =
        fun _ ↦ (2 : ℝ) ^ digestCount := by
    funext hashSeed
    exact hashedBinaryPrefixConcentration_eq_twoPow
      digestCount (hash hashSeed) (huniform hashSeed)
  rw [hpoint, FormalProof4FHE.BoundedMoment.expectation_const]

/-- Public-hash-family form of the digest match-and-square theorem.  The diagonal estimate uses
the averaged conditional concentration, and balanced `r`-bit hashes reduce it to `2 ^ r`. -/
theorem averagedUniformBinaryDigestMatchSquareGap_le
    {HashSeed Prefix Suffix : Type} [Fintype HashSeed]
    [Fintype Prefix] [SampleableType Prefix]
    [Fintype Suffix] [SampleableType Suffix]
    [Fintype (Prefix × Suffix)] [SampleableType (Prefix × Suffix)]
    (hashSeedSampler : ProbComp HashSeed) (digestCount : ℕ)
    (hash : HashSeed → Prefix → (Fin digestCount → Bool))
    (huniform : ∀ hashSeed, HasUniformOutput (hash hashSeed))
    (lossyGap rhoPlus rhoMinus realSecondMoment uniformSignedGap
      sourceAdvantage erasureDefect : ℝ)
    (hdiagonal : lossyGap ≤ rhoPlus + rhoMinus +
      Real.sqrt
        (averagedConditionalDigestConcentration
          (Prefix := Prefix) (Suffix := Suffix)
          hashSeedSampler digestCount hash * realSecondMoment))
    (hsource : |realSecondMoment - uniformSignedGap ^ 2| ≤ 2 * sourceAdvantage)
    (herasure : |uniformSignedGap| ≤ erasureDefect) :
    lossyGap ≤ rhoPlus + rhoMinus +
      Real.sqrt ((2 : ℝ) ^ digestCount *
        (2 * sourceAdvantage + erasureDefect ^ 2)) := by
  have hconcentration :
      0 ≤ averagedConditionalDigestConcentration
        (Prefix := Prefix) (Suffix := Suffix)
        hashSeedSampler digestCount hash := by
    rw [averagedConditionalDigestConcentration_eq_twoPow
      hashSeedSampler digestCount hash huniform]
    positivity
  have hbound := nativeAggregateGap_le_of_approximateErasure
    lossyGap rhoPlus rhoMinus
    (averagedConditionalDigestConcentration
      (Prefix := Prefix) (Suffix := Suffix)
      hashSeedSampler digestCount hash)
    realSecondMoment uniformSignedGap sourceAdvantage erasureDefect
    hconcentration hdiagonal hsource herasure
  rw [averagedConditionalDigestConcentration_eq_twoPow
    hashSeedSampler digestCount hash huniform] at hbound
  exact hbound

/-- Source-coupled digest match-and-square in its exact scalar interface.  The real second moment
is the two-copy source statistic; `uniformSignedGap` is the residual plus/minus gap on the
uniform source. -/
theorem digestMatchSquareGap_le_of_approximateErasure
    {Key Digest : Type} [Fintype Digest]
    (keySampler : ProbComp Key) (digest : Key → Digest)
    (lossyGap rhoPlus rhoMinus realSecondMoment uniformSignedGap
      sourceAdvantage erasureDefect : ℝ)
    (hdiagonal : lossyGap ≤ rhoPlus + rhoMinus +
      Real.sqrt (projectedLeakageConcentration keySampler digest * realSecondMoment))
    (hsource : |realSecondMoment - uniformSignedGap ^ 2| ≤ 2 * sourceAdvantage)
    (herasure : |uniformSignedGap| ≤ erasureDefect) :
    lossyGap ≤ rhoPlus + rhoMinus +
      Real.sqrt (projectedLeakageConcentration keySampler digest *
        (2 * sourceAdvantage + erasureDefect ^ 2)) := by
  exact nativeAggregateGap_le_of_approximateErasure
    lossyGap rhoPlus rhoMinus
    (projectedLeakageConcentration keySampler digest)
    realSecondMoment uniformSignedGap sourceAdvantage erasureDefect
    (projectedLeakageConcentration_nonneg keySampler digest)
    hdiagonal hsource herasure

/-- A balanced `r`-bit digest replaces the full-prefix concentration by exactly `2 ^ r`. -/
theorem uniformBinaryDigestMatchSquareGap_le
    {Prefix Suffix : Type}
    [Fintype Prefix] [SampleableType Prefix]
    [Fintype Suffix] [SampleableType Suffix]
    [Fintype (Prefix × Suffix)] [SampleableType (Prefix × Suffix)]
    (digestCount : ℕ) (hash : Prefix → (Fin digestCount → Bool))
    (huniformHash : HasUniformOutput hash)
    (lossyGap rhoPlus rhoMinus realSecondMoment uniformSignedGap
      sourceAdvantage erasureDefect : ℝ)
    (hdiagonal : lossyGap ≤ rhoPlus + rhoMinus +
      Real.sqrt
        (projectedLeakageConcentration
            ($ᵗ (Prefix × Suffix))
            (hashedPrefixLeakage (Suffix := Suffix) hash) * realSecondMoment))
    (hsource : |realSecondMoment - uniformSignedGap ^ 2| ≤ 2 * sourceAdvantage)
    (herasure : |uniformSignedGap| ≤ erasureDefect) :
    lossyGap ≤ rhoPlus + rhoMinus +
      Real.sqrt ((2 : ℝ) ^ digestCount *
        (2 * sourceAdvantage + erasureDefect ^ 2)) := by
  have hbound := digestMatchSquareGap_le_of_approximateErasure
    ($ᵗ (Prefix × Suffix))
    (hashedPrefixLeakage (Suffix := Suffix) hash)
    lossyGap rhoPlus rhoMinus realSecondMoment uniformSignedGap
    sourceAdvantage erasureDefect hdiagonal hsource herasure
  rw [hashedBinaryPrefixConcentration_eq_twoPow
    digestCount hash huniformHash] at hbound
  exact hbound

/-- Exact uniform-source erasure removes the erasure term and gives the manuscript's
`sqrt (2^(r+1) * sourceAdvantage)` loss. -/
theorem uniformBinaryDigestMatchSquareGap_le_of_exactErasure
    {Prefix Suffix : Type}
    [Fintype Prefix] [SampleableType Prefix]
    [Fintype Suffix] [SampleableType Suffix]
    [Fintype (Prefix × Suffix)] [SampleableType (Prefix × Suffix)]
    (digestCount : ℕ) (hash : Prefix → (Fin digestCount → Bool))
    (huniformHash : HasUniformOutput hash)
    (lossyGap rhoPlus rhoMinus realSecondMoment sourceAdvantage : ℝ)
    (hdiagonal : lossyGap ≤ rhoPlus + rhoMinus +
      Real.sqrt
        (projectedLeakageConcentration
            ($ᵗ (Prefix × Suffix))
            (hashedPrefixLeakage (Suffix := Suffix) hash) * realSecondMoment))
    (hsource : |realSecondMoment| ≤ 2 * sourceAdvantage) :
    lossyGap ≤ rhoPlus + rhoMinus +
      Real.sqrt ((2 : ℝ) ^ (digestCount + 1) * sourceAdvantage) := by
  have hbound := uniformBinaryDigestMatchSquareGap_le
    digestCount hash huniformHash
    lossyGap rhoPlus rhoMinus realSecondMoment 0 sourceAdvantage 0
    hdiagonal (by simpa using hsource) (by simp)
  simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hbound

/-- Final ordinary/lossy hybrid composition with approximate uniform-source erasure. -/
theorem hashLossyCompleteViewComposition_le
    (nativeGap lossyGap modePlus modeMinus rhoPlus rhoMinus
      concentration realSecondMoment uniformSignedGap sourceAdvantage
      erasureDefect samplerDefect : ℝ)
    (hmode : nativeGap ≤ modePlus + modeMinus + lossyGap + samplerDefect)
    (hconcentration : 0 ≤ concentration)
    (hdiagonal : lossyGap ≤ rhoPlus + rhoMinus +
      Real.sqrt (concentration * realSecondMoment))
    (hsource : |realSecondMoment - uniformSignedGap ^ 2| ≤ 2 * sourceAdvantage)
    (herasure : |uniformSignedGap| ≤ erasureDefect) :
    nativeGap ≤ modePlus + modeMinus + rhoPlus + rhoMinus +
      Real.sqrt (concentration *
        (2 * sourceAdvantage + erasureDefect ^ 2)) + samplerDefect := by
  have hlossy := nativeAggregateGap_le_of_approximateErasure
    lossyGap rhoPlus rhoMinus concentration realSecondMoment uniformSignedGap
    sourceAdvantage erasureDefect hconcentration hdiagonal hsource herasure
  linarith

/-- Uniform balanced-hash specialization of the final complete-view theorem. -/
theorem uniformBinaryHashLossyCompleteViewComposition_le
    {Prefix Suffix : Type}
    [Fintype Prefix] [SampleableType Prefix]
    [Fintype Suffix] [SampleableType Suffix]
    [Fintype (Prefix × Suffix)] [SampleableType (Prefix × Suffix)]
    (digestCount : ℕ) (hash : Prefix → (Fin digestCount → Bool))
    (huniformHash : HasUniformOutput hash)
    (nativeGap lossyGap modePlus modeMinus rhoPlus rhoMinus
      realSecondMoment uniformSignedGap sourceAdvantage erasureDefect samplerDefect : ℝ)
    (hmode : nativeGap ≤ modePlus + modeMinus + lossyGap + samplerDefect)
    (hdiagonal : lossyGap ≤ rhoPlus + rhoMinus +
      Real.sqrt
        (projectedLeakageConcentration
            ($ᵗ (Prefix × Suffix))
            (hashedPrefixLeakage (Suffix := Suffix) hash) * realSecondMoment))
    (hsource : |realSecondMoment - uniformSignedGap ^ 2| ≤ 2 * sourceAdvantage)
    (herasure : |uniformSignedGap| ≤ erasureDefect) :
    nativeGap ≤ modePlus + modeMinus + rhoPlus + rhoMinus +
      Real.sqrt ((2 : ℝ) ^ digestCount *
        (2 * sourceAdvantage + erasureDefect ^ 2)) + samplerDefect := by
  have hconcentration := projectedLeakageConcentration_nonneg
    ($ᵗ (Prefix × Suffix))
    (hashedPrefixLeakage (Suffix := Suffix) hash)
  have hbound := hashLossyCompleteViewComposition_le
    nativeGap lossyGap modePlus modeMinus rhoPlus rhoMinus
    (projectedLeakageConcentration
      ($ᵗ (Prefix × Suffix))
      (hashedPrefixLeakage (Suffix := Suffix) hash))
    realSecondMoment uniformSignedGap sourceAdvantage erasureDefect samplerDefect
    hmode hconcentration hdiagonal hsource herasure
  rw [hashedBinaryPrefixConcentration_eq_twoPow
    digestCount hash huniformHash] at hbound
  exact hbound

/-- Exact-erasure form of the final uniform-hash complete-view theorem. -/
theorem uniformBinaryHashLossyCompleteViewComposition_le_of_exactErasure
    {Prefix Suffix : Type}
    [Fintype Prefix] [SampleableType Prefix]
    [Fintype Suffix] [SampleableType Suffix]
    [Fintype (Prefix × Suffix)] [SampleableType (Prefix × Suffix)]
    (digestCount : ℕ) (hash : Prefix → (Fin digestCount → Bool))
    (huniformHash : HasUniformOutput hash)
    (nativeGap lossyGap modePlus modeMinus rhoPlus rhoMinus
      realSecondMoment sourceAdvantage samplerDefect : ℝ)
    (hmode : nativeGap ≤ modePlus + modeMinus + lossyGap + samplerDefect)
    (hdiagonal : lossyGap ≤ rhoPlus + rhoMinus +
      Real.sqrt
        (projectedLeakageConcentration
            ($ᵗ (Prefix × Suffix))
            (hashedPrefixLeakage (Suffix := Suffix) hash) * realSecondMoment))
    (hsource : |realSecondMoment| ≤ 2 * sourceAdvantage) :
    nativeGap ≤ modePlus + modeMinus + rhoPlus + rhoMinus +
      Real.sqrt ((2 : ℝ) ^ (digestCount + 1) * sourceAdvantage) +
        samplerDefect := by
  have hbound := uniformBinaryHashLossyCompleteViewComposition_le
    digestCount hash huniformHash
    nativeGap lossyGap modePlus modeMinus rhoPlus rhoMinus
    realSecondMoment 0 sourceAdvantage 0 samplerDefect
    hmode hdiagonal (by simpa using hsource) (by simp)
  simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hbound

/-! ## Exact and robust translation-only barriers -/

/-- Exact phase-oblivious correctness below cutoff `t - 2` forces every digest collision to be a
prefix equality. -/
theorem phaseObliviousHash_injective
    {Index Digest : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree + 2 ≤ Fintype.card Index)
    (hash : BitVector Index → Digest)
    (plaintextLaw : Bool → Digest → BitVector Index → ℝ)
    (hcorrect : PhaseObliviousPlaintextCorrect degree id hash plaintextLaw) :
    Function.Injective hash := by
  intro first second hequal
  exact prefix_eq_of_equal_leakage_phaseOblivious
    degree hdegree id hash plaintextLaw hcorrect first second hequal

/-- Cardinal form of the exact no-go theorem. -/
theorem card_prefix_le_card_digest_of_phaseOblivious
    {Index Digest : Type} [Fintype Index] [DecidableEq Index] [Fintype Digest]
    (degree : ℕ) (hdegree : degree + 2 ≤ Fintype.card Index)
    (hash : BitVector Index → Digest)
    (plaintextLaw : Bool → Digest → BitVector Index → ℝ)
    (hcorrect : PhaseObliviousPlaintextCorrect degree id hash plaintextLaw) :
    Fintype.card (BitVector Index) ≤ Fintype.card Digest := by
  exact Fintype.card_le_of_injective hash
    (phaseObliviousHash_injective degree hdegree hash plaintextLaw hcorrect)

/-- For a binary digest, exact correctness forces at least as many digest bits as prefix bits. -/
theorem prefixCard_le_digestCount_of_phaseOblivious
    {Index : Type} [Fintype Index] [DecidableEq Index]
    (digestCount degree : ℕ) (hdegree : degree + 2 ≤ Fintype.card Index)
    (hash : BitVector Index → (Fin digestCount → Bool))
    (plaintextLaw : Bool → (Fin digestCount → Bool) → BitVector Index → ℝ)
    (hcorrect : PhaseObliviousPlaintextCorrect degree id hash plaintextLaw) :
    Fintype.card Index ≤ digestCount := by
  have hcard := card_prefix_le_card_digest_of_phaseOblivious
    degree hdegree hash plaintextLaw hcorrect
  simp only [BitVector, Fintype.card_fun, Fintype.card_bool, Fintype.card_fin] at hcard
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp hcard

/-- If a digest collision exists, a phase-oblivious builder whose per-key total variation is at
most `epsilon` has `epsilon >= 1 / (4 * lambda_d)`.  The existing table defect is the `L1`
distance, hence the premise supplies the factor `2 * epsilon`. -/
theorem approximatePhaseObliviousHash_defect_lowerBound
    {Index Digest : Type} [Fintype Index] [DecidableEq Index]
    (degree : ℕ) (hdegree : degree + 2 ≤ Fintype.card Index)
    (hash : BitVector Index → Digest)
    (plaintextLaw : Bool → Digest → BitVector Index → ℝ)
    (epsilon : ℝ)
    (hdefect : ∀ positive prefixValue,
      phaseObliviousPlaintextL1Defect
        degree id hash plaintextLaw positive prefixValue ≤ 2 * epsilon)
    (first second : BitVector Index) (hhash : hash first = hash second)
    (hne : first ≠ second) :
    1 / (4 * aggregateNormalization Index degree) ≤ epsilon := by
  have hlower := two_le_four_mul_normalization_mul_defect_of_prefix_collision
    degree hdegree id hash plaintextLaw (2 * epsilon) hdefect
    first second hhash hne
  have hnormalization : 0 < 4 * aggregateNormalization Index degree := by
    exact mul_pos (by norm_num)
      (aggregateNormalization_pos Index degree (by omega))
  apply (div_le_iff₀ hnormalization).2
  nlinarith

/-! ## Statistical key-decoding barrier -/

/-- Boolean test that a decoder recovers the labelled prefix. -/
def labelledDecoderCheck
    {Prefix View : Type} [DecidableEq Prefix]
    (decoder : View → Prefix) (labelledView : Prefix × View) : Bool :=
  decide (decoder labelledView.2 = labelledView.1)

/-- Decoder success in a uniform-prefix view whose conditional mass table depends on the prefix
only through `hash`. -/
def hashFactorizedDecoderSuccess
    {Prefix Digest View : Type} [Fintype Prefix] [DecidableEq Prefix] [Fintype View]
    (hash : Prefix → Digest) (viewMass : Digest → View → ℝ)
    (decoder : View → Prefix) : ℝ :=
  (∑ keyValue, ∑ view,
      if decoder view = keyValue then viewMass (hash keyValue) view else 0) /
    Fintype.card Prefix

/-- Executable finite decoding experiment corresponding to the preceding mass-table
functional. -/
def hashFactorizedDecodingGame
    {Prefix Digest View : Type}
    [SampleableType Prefix] [DecidableEq Prefix]
    (hash : Prefix → Digest) (viewSampler : Digest → ProbComp View)
    (decoder : View → Prefix) : ProbComp Bool := do
  let keyValue ← $ᵗ Prefix
  let view ← viewSampler (hash keyValue)
  return decide (decoder view = keyValue)

/-- Key-labelled form of a digest-factorized complete view. -/
def hashFactorizedLabelledView
    {Prefix Digest View : Type} [SampleableType Prefix]
    (hash : Prefix → Digest) (viewSampler : Digest → ProbComp View) :
    ProbComp (Prefix × View) := do
  let keyValue ← $ᵗ Prefix
  let view ← viewSampler (hash keyValue)
  return (keyValue, view)

/-- Applying the labelled decoder to the factorized view is exactly the direct decoding game. -/
theorem labelledDecoder_hashFactorizedLabelledView_evalDist
    {Prefix Digest View : Type}
    [SampleableType Prefix] [DecidableEq Prefix]
    (hash : Prefix → Digest) (viewSampler : Digest → ProbComp View)
    (decoder : View → Prefix) :
    evalDist
        (labelledDecoderCheck decoder <$>
          hashFactorizedLabelledView hash viewSampler) =
      evalDist (hashFactorizedDecodingGame hash viewSampler decoder) := by
  simp [hashFactorizedLabelledView, hashFactorizedDecodingGame,
    labelledDecoderCheck, monad_norm]

/-- The mass-table expression is exactly the success probability of the finite decoding game. -/
theorem hashFactorizedDecoderSuccess_eq_probability
    {Prefix Digest View : Type}
    [Fintype Prefix] [SampleableType Prefix] [DecidableEq Prefix]
    [Fintype View]
    (hash : Prefix → Digest) (viewSampler : Digest → ProbComp View)
    (decoder : View → Prefix) :
    hashFactorizedDecoderSuccess hash
        (fun digestValue view ↦ probabilityMass (viewSampler digestValue) view)
        decoder =
      Pr[= true | hashFactorizedDecodingGame hash viewSampler decoder].toReal := by
  classical
  unfold hashFactorizedDecoderSuccess hashFactorizedDecodingGame probabilityMass
  rw [probOutput_bind_eq_sum_fintype,
    ENNReal.toReal_sum (fun _ _ ↦
      ENNReal.mul_ne_top probOutput_ne_top probOutput_ne_top)]
  simp_rw [probOutput_uniformSample, ENNReal.toReal_mul,
    ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [div_eq_mul_inv, mul_comm, ← Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro keyValue _
  rw [probOutput_bind_eq_sum_fintype,
    ENNReal.toReal_sum (fun _ _ ↦
      ENNReal.mul_ne_top probOutput_ne_top probOutput_ne_top)]
  simp_rw [ENNReal.toReal_mul]
  apply Finset.sum_congr rfl
  intro view _
  by_cases hequal : decoder view = keyValue
  · simp [hequal]
  · simp [hequal]

/-- No decoder can recover a uniform prefix from a digest-factorized view with probability above
the cardinality ratio `|Digest| / |Prefix|`. -/
theorem hashFactorizedDecoderSuccess_le_cardRatio
    {Prefix Digest View : Type}
    [Fintype Prefix] [Nonempty Prefix] [DecidableEq Prefix]
    [Fintype Digest] [Fintype View]
    (hash : Prefix → Digest) (viewMass : Digest → View → ℝ)
    (decoder : View → Prefix)
    (hmass : ∀ digest view, 0 ≤ viewMass digest view)
    (htotal : ∀ digest, ∑ view, viewMass digest view = 1) :
    hashFactorizedDecoderSuccess hash viewMass decoder ≤
      Fintype.card Digest / Fintype.card Prefix := by
  classical
  have hreindex :
      (∑ keyValue, ∑ view,
        if decoder view = keyValue then viewMass (hash keyValue) view else 0) =
        ∑ view, viewMass (hash (decoder view)) view := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro view _
    simp
  have hpoint (view : View) :
      viewMass (hash (decoder view)) view ≤
        ∑ digest, viewMass digest view := by
    exact Finset.single_le_sum
      (fun digest _ ↦ hmass digest view)
      (Finset.mem_univ (hash (decoder view)))
  have hsum :
      (∑ view, viewMass (hash (decoder view)) view) ≤
        Fintype.card Digest := by
    calc
      (∑ view, viewMass (hash (decoder view)) view) ≤
          ∑ view, ∑ digest, viewMass digest view :=
        Finset.sum_le_sum fun view _ ↦ hpoint view
      _ = ∑ digest, ∑ view, viewMass digest view := Finset.sum_comm
      _ = Fintype.card Digest := by simp [htotal]
  unfold hashFactorizedDecoderSuccess
  rw [hreindex]
  exact div_le_div_of_nonneg_right hsum (by positivity)

/-- Game-level form of the best-decoding bound. -/
theorem hashFactorizedDecodingProbability_le_cardRatio
    {Prefix Digest View : Type}
    [Fintype Prefix] [Nonempty Prefix] [SampleableType Prefix] [DecidableEq Prefix]
    [Fintype Digest] [Fintype View]
    (hash : Prefix → Digest) (viewSampler : Digest → ProbComp View)
    (decoder : View → Prefix) :
    Pr[= true | hashFactorizedDecodingGame hash viewSampler decoder].toReal ≤
      Fintype.card Digest / Fintype.card Prefix := by
  rw [← hashFactorizedDecoderSuccess_eq_probability]
  exact hashFactorizedDecoderSuccess_le_cardRatio
    hash (fun digestValue view ↦ probabilityMass (viewSampler digestValue) view)
    decoder (fun digestValue view ↦ probabilityMass_nonneg _ _)
    (fun digestValue ↦ sum_probabilityMass_eq_one (viewSampler digestValue))

/-- Binary specialization of the decoding bound, written without negative exponents. -/
theorem binaryHashFactorizedDecoderSuccess_le
    (prefixCount digestCount : ℕ)
    {View : Type} [Fintype View]
    (hash : (Fin prefixCount → Bool) → (Fin digestCount → Bool))
    (viewMass : (Fin digestCount → Bool) → View → ℝ)
    (decoder : View → (Fin prefixCount → Bool))
    (hmass : ∀ digest view, 0 ≤ viewMass digest view)
    (htotal : ∀ digest, ∑ view, viewMass digest view = 1) :
    hashFactorizedDecoderSuccess hash viewMass decoder ≤
      (2 : ℝ) ^ digestCount / (2 : ℝ) ^ prefixCount := by
  have hbound := hashFactorizedDecoderSuccess_le_cardRatio
    hash viewMass decoder hmass htotal
  simpa using hbound

/-- For `r ≤ t`, the binary cardinality ratio is the reciprocal hash-fiber cardinality. -/
theorem binaryDigestCardRatio_eq_inverseFiberCard
    (prefixCount digestCount : ℕ) (hcount : digestCount ≤ prefixCount) :
    (2 : ℝ) ^ digestCount / (2 : ℝ) ^ prefixCount =
      1 / (2 : ℝ) ^ (prefixCount - digestCount) := by
  have hpow :
      (2 : ℝ) ^ prefixCount =
        (2 : ℝ) ^ (prefixCount - digestCount) * (2 : ℝ) ^ digestCount := by
    rw [← pow_add, Nat.sub_add_cancel hcount]
  rw [hpow]
  field_simp

/-- Total variation between key-labelled experiments bounds the change in decoding success. -/
theorem labelledDecoderSuccessGap_le_tvDist
    {Prefix View : Type} [DecidableEq Prefix]
    (ordinary lossy : ProbComp (Prefix × View)) (decoder : View → Prefix) :
    |Pr[= true | labelledDecoderCheck decoder <$> ordinary].toReal -
        Pr[= true | labelledDecoderCheck decoder <$> lossy].toReal| ≤
      tvDist ordinary lossy := by
  calc
    _ ≤ tvDist
        (labelledDecoderCheck decoder <$> ordinary)
        (labelledDecoderCheck decoder <$> lossy) :=
      abs_probOutput_toReal_sub_le_tvDist _ _
    _ ≤ tvDist ordinary lossy :=
      tvDist_map_le (m := ProbComp) (labelledDecoderCheck decoder) ordinary lossy

/-- Statistical mode-switch lower bound.  This is the exact finite form of
`epsilon >= 1 - kappa - |Digest| / |Prefix|`; the preceding theorem supplies the lossy success
bound whenever the complete view factors through the digest. -/
theorem statisticalModeSwitch_lowerBound
    {Prefix View : Type} [DecidableEq Prefix]
    (ordinary lossy : ProbComp (Prefix × View)) (decoder : View → Prefix)
    (kappa epsilon lossySuccessBound : ℝ)
    (hordinary : 1 - kappa ≤
      Pr[= true | labelledDecoderCheck decoder <$> ordinary].toReal)
    (hlossy :
      Pr[= true | labelledDecoderCheck decoder <$> lossy].toReal ≤ lossySuccessBound)
    (hmode : tvDist ordinary lossy ≤ epsilon) :
    1 - kappa - lossySuccessBound ≤ epsilon := by
  have hgap := labelledDecoderSuccessGap_le_tvDist ordinary lossy decoder
  have honeSide :
      Pr[= true | labelledDecoderCheck decoder <$> ordinary].toReal -
          Pr[= true | labelledDecoderCheck decoder <$> lossy].toReal ≤ epsilon :=
    (le_abs_self _).trans (hgap.trans hmode)
  linarith

/-- Binary hash-factorized specialization of the statistical lower bound. -/
theorem binaryHashStatisticalModeSwitch_lowerBound
    (prefixCount digestCount : ℕ) (hcount : digestCount ≤ prefixCount)
    {View : Type} [Fintype View]
    (hash : (Fin prefixCount → Bool) → (Fin digestCount → Bool))
    (viewMass : (Fin digestCount → Bool) → View → ℝ)
    (decoder : View → (Fin prefixCount → Bool))
    (ordinary lossy : ProbComp ((Fin prefixCount → Bool) × View))
    (kappa epsilon : ℝ)
    (hmass : ∀ digestValue view, 0 ≤ viewMass digestValue view)
    (htotal : ∀ digestValue, ∑ view, viewMass digestValue view = 1)
    (hordinary : 1 - kappa ≤
      Pr[= true | labelledDecoderCheck decoder <$> ordinary].toReal)
    (hlossy :
      Pr[= true | labelledDecoderCheck decoder <$> lossy].toReal ≤
        hashFactorizedDecoderSuccess hash viewMass decoder)
    (hmode : tvDist ordinary lossy ≤ epsilon) :
    1 - kappa - 1 / (2 : ℝ) ^ (prefixCount - digestCount) ≤ epsilon := by
  have hdecoder := binaryHashFactorizedDecoderSuccess_le
    prefixCount digestCount hash viewMass decoder hmass htotal
  have hratio := binaryDigestCardRatio_eq_inverseFiberCard
    prefixCount digestCount hcount
  apply statisticalModeSwitch_lowerBound ordinary lossy decoder
    kappa epsilon (1 / (2 : ℝ) ^ (prefixCount - digestCount))
    hordinary
  · calc
      Pr[= true | labelledDecoderCheck decoder <$> lossy].toReal ≤
          hashFactorizedDecoderSuccess hash viewMass decoder := hlossy
      _ ≤ (2 : ℝ) ^ digestCount / (2 : ℝ) ^ prefixCount := hdecoder
      _ = 1 / (2 : ℝ) ^ (prefixCount - digestCount) := hratio
  · exact hmode

/-- Direct game-level statistical barrier for a complete lossy view that factors through a
binary digest. -/
theorem binaryHashStatisticalModeSwitch_lowerBound_of_factorizedView
    (prefixCount digestCount : ℕ) (hcount : digestCount ≤ prefixCount)
    {View : Type} [Fintype View]
    (hash : (Fin prefixCount → Bool) → (Fin digestCount → Bool))
    (viewSampler : (Fin digestCount → Bool) → ProbComp View)
    (decoder : View → (Fin prefixCount → Bool))
    (ordinary : ProbComp ((Fin prefixCount → Bool) × View))
    (kappa epsilon : ℝ)
    (hordinary : 1 - kappa ≤
      Pr[= true | labelledDecoderCheck decoder <$> ordinary].toReal)
    (hmode : tvDist ordinary
      (hashFactorizedLabelledView hash viewSampler) ≤ epsilon) :
    1 - kappa - 1 / (2 : ℝ) ^ (prefixCount - digestCount) ≤ epsilon := by
  let lossy := hashFactorizedLabelledView hash viewSampler
  have hgame := labelledDecoder_hashFactorizedLabelledView_evalDist
    hash viewSampler decoder
  have hlossy :
      Pr[= true | labelledDecoderCheck decoder <$> lossy].toReal ≤
        (2 : ℝ) ^ digestCount / (2 : ℝ) ^ prefixCount := by
    have hprob := hashFactorizedDecodingProbability_le_cardRatio
      hash viewSampler decoder
    have hprobEq :
        Pr[= true | labelledDecoderCheck decoder <$> lossy].toReal =
          Pr[= true | hashFactorizedDecodingGame hash viewSampler decoder].toReal := by
      have hprob :
          Pr[= true | labelledDecoderCheck decoder <$> lossy] =
            Pr[= true | hashFactorizedDecodingGame hash viewSampler decoder] := by
        rw [probOutput_def, probOutput_def, hgame]
      exact congrArg ENNReal.toReal hprob
    rw [hprobEq]
    simpa using hprob
  have hratio := binaryDigestCardRatio_eq_inverseFiberCard
    prefixCount digestCount hcount
  apply statisticalModeSwitch_lowerBound ordinary lossy decoder
    kappa epsilon (1 / (2 : ℝ) ^ (prefixCount - digestCount))
    hordinary
  · exact hlossy.trans_eq hratio
  · exact hmode

end

end FormalProof4FHE.TFHE.NativeTRGSWHashLossyCompleteView
