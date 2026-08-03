/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeTRGSWHashLossyCompleteView
import FormalProof4FHE.TFHE.NativeTRGSWQuadraticKDMAndTFHET

/-!
# Conditional hash-lossy dual mode for native TFHE

This module formalizes the additional finite claims in `sketch/proofdualmode.md`.  The exact
fiber resampler, digest match-and-square theorem, translation-only lower bounds, and statistical
decoder barrier are supplied by `NativeTRGSWHashLossyCompleteView`; the native nonce polynomial
identities are supplied by `NativeTRGSWQuadraticKDMAndTFHET`.

The new results here make three points precise.

* A constructor which ignores its source cannot simultaneously approximate two target branches
  and erase a nontrivial gap between them: the target distance is at most the two diagonal
  defects plus the erasure defect.
* The full native/ordinary/lossy hybrid includes both ordinary-fidelity terms, both mode-switch
  terms, both diagonal defects, the conditional digest match-and-square radical, and one sampler
  defect.  A balanced public `r`-bit hash gives exactly the coefficient `2 ^ r`.
* A hidden-rank factorization of the linear residual does not by itself factor a native nonce
  row.  If a hash fiber contains two prefixes with different nonce KDM messages, adding that
  message to an already digest-factorized residual destroys exact digest factorization.

No ordinary/lossy native BRK/KSK/auxiliary generator is constructed.  Diagonal correctness,
reference-source erasure, source advantage, and computational mode-switch bounds remain explicit
premises rather than axioms or claimed constructions.
-/

set_option autoImplicit false

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.NativeTRGSWProofDualMode

noncomputable section

open NativeTRGSWBarrierAndSpectralBoundary
open NativeTRGSWAggregateProjectedLeakage
open NativeTRGSWHashCompressedSecurity
open NativeTRGSWHashLossyCompleteView
open NativeTRGSWHardTheoremComposition
open NativeTRGSWQuadraticKDMAndTFHET

/-! ## A source-independent constructor is not a source reduction -/

/-- Lift a public-view constructor to a source interface while deliberately ignoring the supplied
source state. -/
def sourceIndependentConstructor
    {Source HashSeed Digest View : Type}
    (constructor : HashSeed → Digest → ProbComp View) :
    HashSeed → Digest → Source → ProbComp View :=
  fun hashSeed digest _ => constructor hashSeed digest

@[simp]
theorem sourceIndependentConstructor_apply
    {Source HashSeed Digest View : Type}
    (constructor : HashSeed → Digest → ProbComp View)
    (hashSeed : HashSeed) (digest : Digest) (source : Source) :
    sourceIndependentConstructor constructor hashSeed digest source =
      constructor hashSeed digest := rfl

/-- In particular, changing a real source state to a reference source state has no effect at all
on a source-independent constructor's output law. -/
@[simp]
theorem sourceIndependentConstructor_real_reference_evalDist_eq
    {Source HashSeed Digest View : Type}
    (constructor : HashSeed → Digest → ProbComp View)
    (hashSeed : HashSeed) (digest : Digest)
    (realSource referenceSource : Source) :
    evalDist
        (sourceIndependentConstructor constructor hashSeed digest realSource) =
      evalDist
        (sourceIndependentConstructor constructor hashSeed digest referenceSource) := rfl

/-- A source-independent builder satisfying diagonal correctness and reference-branch erasure
forces the two target lossy branches themselves to be statistically close.  This is equation (6)
of the sketch's source-independence discussion. -/
theorem target_tvDist_le_of_sourceIndependent_erasure
    {View : Type}
    (targetPlus targetMinus builderPlus builderMinus : ProbComp View)
    (rhoPlus rhoMinus erasureDefect : ℝ)
    (hplus : tvDist builderPlus targetPlus ≤ rhoPlus)
    (hminus : tvDist builderMinus targetMinus ≤ rhoMinus)
    (herasure : tvDist builderPlus builderMinus ≤ erasureDefect) :
    tvDist targetPlus targetMinus ≤ rhoPlus + rhoMinus + erasureDefect := by
  have hplus' : tvDist targetPlus builderPlus ≤ rhoPlus := by
    simpa only [tvDist_comm] using hplus
  calc
    tvDist targetPlus targetMinus ≤
        tvDist targetPlus builderPlus + tvDist builderPlus targetMinus :=
      tvDist_triangle _ _ _
    _ ≤ tvDist targetPlus builderPlus +
        (tvDist builderPlus builderMinus + tvDist builderMinus targetMinus) :=
      by
        have htriangle := tvDist_triangle builderPlus builderMinus targetMinus
        linarith
    _ ≤ rhoPlus + (erasureDefect + rhoMinus) :=
      add_le_add hplus' (add_le_add herasure hminus)
    _ = rhoPlus + rhoMinus + erasureDefect := by ring

/-- Interface-level form of the preceding result.  The diagonal experiments use real source
states and the erasure experiment uses reference source states, but source independence makes
those choices definitionally irrelevant. -/
theorem target_tvDist_le_of_sourceIndependentConstructor
    {Source HashSeed Digest View : Type}
    (constructorPlus constructorMinus : HashSeed → Digest → ProbComp View)
    (hashSeed : HashSeed) (digest : Digest)
    (realSource referenceSource : Source)
    (targetPlus targetMinus : ProbComp View)
    (rhoPlus rhoMinus erasureDefect : ℝ)
    (hplus : tvDist
      (sourceIndependentConstructor constructorPlus hashSeed digest realSource)
      targetPlus ≤ rhoPlus)
    (hminus : tvDist
      (sourceIndependentConstructor constructorMinus hashSeed digest realSource)
      targetMinus ≤ rhoMinus)
    (herasure : tvDist
      (sourceIndependentConstructor constructorPlus hashSeed digest referenceSource)
      (sourceIndependentConstructor constructorMinus hashSeed digest referenceSource) ≤
        erasureDefect) :
    tvDist targetPlus targetMinus ≤ rhoPlus + rhoMinus + erasureDefect := by
  apply target_tvDist_le_of_sourceIndependent_erasure
    targetPlus targetMinus
    (sourceIndependentConstructor constructorPlus hashSeed digest realSource)
    (sourceIndependentConstructor constructorMinus hashSeed digest realSource)
    rhoPlus rhoMinus erasureDefect hplus hminus
  simpa only [sourceIndependentConstructor_apply] using herasure

/-! ## Complete native/ordinary/lossy composition -/

/-- The five-edge hybrid chain, with the final sampler comparison charged exactly once on the
central lossy edge. -/
theorem completeAcceptanceHybrid_le
    (nativePlus ordinaryPlus lossyPlus lossyMinus ordinaryMinus nativeMinus
      ordinaryPlusDefect ordinaryMinusDefect modePlusDefect modeMinusDefect
      centralBound samplerDefect : ℝ)
    (hordinaryPlus : |nativePlus - ordinaryPlus| ≤ ordinaryPlusDefect)
    (hmodePlus : |ordinaryPlus - lossyPlus| ≤ modePlusDefect)
    (hcentral : |lossyPlus - lossyMinus| ≤ centralBound)
    (hmodeMinus : |lossyMinus - ordinaryMinus| ≤ modeMinusDefect)
    (hordinaryMinus : |ordinaryMinus - nativeMinus| ≤ ordinaryMinusDefect)
    (hsampler : 0 ≤ samplerDefect) :
    |nativePlus - nativeMinus| ≤
      ordinaryPlusDefect + ordinaryMinusDefect +
        modePlusDefect + modeMinusDefect + centralBound + samplerDefect := by
  have hcentralWithSampler :
      |lossyPlus - lossyMinus| ≤ centralBound + samplerDefect := by
    linarith
  have hhybrid := hiddenModeComposition_advantage_le
    nativePlus ordinaryPlus lossyPlus lossyMinus ordinaryMinus nativeMinus
    ordinaryPlusDefect modePlusDefect centralBound modeMinusDefect
    ordinaryMinusDefect samplerDefect
    hordinaryPlus hmodePlus hcentralWithSampler hmodeMinus hordinaryMinus
  linarith

/-- Full conditional composition with an arbitrary nonnegative conditional digest
concentration.  This is the scalar form of equation (22) in the sketch. -/
theorem completeConditionalDigestComposition_le
    (nativePlus ordinaryPlus lossyPlus lossyMinus ordinaryMinus nativeMinus
      ordinaryPlusDefect ordinaryMinusDefect modePlusDefect modeMinusDefect
      rhoPlus rhoMinus concentration realSecondMoment uniformSignedGap
      sourceAdvantage erasureDefect samplerDefect : ℝ)
    (hordinaryPlus : |nativePlus - ordinaryPlus| ≤ ordinaryPlusDefect)
    (hmodePlus : |ordinaryPlus - lossyPlus| ≤ modePlusDefect)
    (hconcentration : 0 ≤ concentration)
    (hdiagonal : |lossyPlus - lossyMinus| ≤ rhoPlus + rhoMinus +
      Real.sqrt (concentration * realSecondMoment))
    (hsource : |realSecondMoment - uniformSignedGap ^ 2| ≤
      2 * sourceAdvantage)
    (herasure : |uniformSignedGap| ≤ erasureDefect)
    (hmodeMinus : |lossyMinus - ordinaryMinus| ≤ modeMinusDefect)
    (hordinaryMinus : |ordinaryMinus - nativeMinus| ≤ ordinaryMinusDefect)
    (hsampler : 0 ≤ samplerDefect) :
    |nativePlus - nativeMinus| ≤
      ordinaryPlusDefect + ordinaryMinusDefect +
        modePlusDefect + modeMinusDefect + rhoPlus + rhoMinus +
        Real.sqrt
          (concentration * (2 * sourceAdvantage + erasureDefect ^ 2)) +
        samplerDefect := by
  have hcentral := nativeAggregateGap_le_of_approximateErasure
    |lossyPlus - lossyMinus| rhoPlus rhoMinus concentration
    realSecondMoment uniformSignedGap sourceAdvantage erasureDefect
    hconcentration hdiagonal hsource herasure
  have hhybrid := completeAcceptanceHybrid_le
    nativePlus ordinaryPlus lossyPlus lossyMinus ordinaryMinus nativeMinus
    ordinaryPlusDefect ordinaryMinusDefect modePlusDefect modeMinusDefect
    (rhoPlus + rhoMinus +
      Real.sqrt
        (concentration * (2 * sourceAdvantage + erasureDefect ^ 2)))
    samplerDefect hordinaryPlus hmodePlus hcentral hmodeMinus hordinaryMinus hsampler
  linarith

/-- Public-hash-family specialization.  Balance of every realized `r`-bit hash makes the
averaged conditional Renyi-half concentration exactly `2 ^ r`; entropy in the public hash seed
is not charged. -/
theorem averagedUniformBinaryCompleteDigestComposition_le
    {HashSeed Prefix Suffix : Type} [Fintype HashSeed]
    [Fintype Prefix] [SampleableType Prefix]
    [Fintype Suffix] [SampleableType Suffix]
    [Fintype (Prefix × Suffix)] [SampleableType (Prefix × Suffix)]
    (hashSeedSampler : ProbComp HashSeed) (digestCount : ℕ)
    (hash : HashSeed → Prefix → (Fin digestCount → Bool))
    (huniform : ∀ hashSeed, HasUniformOutput (hash hashSeed))
    (nativePlus ordinaryPlus lossyPlus lossyMinus ordinaryMinus nativeMinus
      ordinaryPlusDefect ordinaryMinusDefect modePlusDefect modeMinusDefect
      rhoPlus rhoMinus realSecondMoment uniformSignedGap sourceAdvantage
      erasureDefect samplerDefect : ℝ)
    (hordinaryPlus : |nativePlus - ordinaryPlus| ≤ ordinaryPlusDefect)
    (hmodePlus : |ordinaryPlus - lossyPlus| ≤ modePlusDefect)
    (hdiagonal : |lossyPlus - lossyMinus| ≤ rhoPlus + rhoMinus +
      Real.sqrt
        (averagedConditionalDigestConcentration
          (Prefix := Prefix) (Suffix := Suffix)
          hashSeedSampler digestCount hash * realSecondMoment))
    (hsource : |realSecondMoment - uniformSignedGap ^ 2| ≤
      2 * sourceAdvantage)
    (herasure : |uniformSignedGap| ≤ erasureDefect)
    (hmodeMinus : |lossyMinus - ordinaryMinus| ≤ modeMinusDefect)
    (hordinaryMinus : |ordinaryMinus - nativeMinus| ≤ ordinaryMinusDefect)
    (hsampler : 0 ≤ samplerDefect) :
    |nativePlus - nativeMinus| ≤
      ordinaryPlusDefect + ordinaryMinusDefect +
        modePlusDefect + modeMinusDefect + rhoPlus + rhoMinus +
        Real.sqrt ((2 : ℝ) ^ digestCount *
          (2 * sourceAdvantage + erasureDefect ^ 2)) + samplerDefect := by
  have hcentral := averagedUniformBinaryDigestMatchSquareGap_le
    hashSeedSampler digestCount hash huniform
    |lossyPlus - lossyMinus| rhoPlus rhoMinus realSecondMoment
    uniformSignedGap sourceAdvantage erasureDefect
    hdiagonal hsource herasure
  have hhybrid := completeAcceptanceHybrid_le
    nativePlus ordinaryPlus lossyPlus lossyMinus ordinaryMinus nativeMinus
    ordinaryPlusDefect ordinaryMinusDefect modePlusDefect modeMinusDefect
    (rhoPlus + rhoMinus +
      Real.sqrt ((2 : ℝ) ^ digestCount *
        (2 * sourceAdvantage + erasureDefect ^ 2)))
    samplerDefect hordinaryPlus hmodePlus hcentral hmodeMinus hordinaryMinus hsampler
  linarith

/-- Exact reference-source erasure gives the manuscript's
`sqrt (2^(r+1) * sourceAdvantage)` central term. -/
theorem averagedUniformBinaryCompleteDigestComposition_le_of_exactErasure
    {HashSeed Prefix Suffix : Type} [Fintype HashSeed]
    [Fintype Prefix] [SampleableType Prefix]
    [Fintype Suffix] [SampleableType Suffix]
    [Fintype (Prefix × Suffix)] [SampleableType (Prefix × Suffix)]
    (hashSeedSampler : ProbComp HashSeed) (digestCount : ℕ)
    (hash : HashSeed → Prefix → (Fin digestCount → Bool))
    (huniform : ∀ hashSeed, HasUniformOutput (hash hashSeed))
    (nativePlus ordinaryPlus lossyPlus lossyMinus ordinaryMinus nativeMinus
      ordinaryPlusDefect ordinaryMinusDefect modePlusDefect modeMinusDefect
      rhoPlus rhoMinus realSecondMoment sourceAdvantage samplerDefect : ℝ)
    (hordinaryPlus : |nativePlus - ordinaryPlus| ≤ ordinaryPlusDefect)
    (hmodePlus : |ordinaryPlus - lossyPlus| ≤ modePlusDefect)
    (hdiagonal : |lossyPlus - lossyMinus| ≤ rhoPlus + rhoMinus +
      Real.sqrt
        (averagedConditionalDigestConcentration
          (Prefix := Prefix) (Suffix := Suffix)
          hashSeedSampler digestCount hash * realSecondMoment))
    (hsource : |realSecondMoment| ≤ 2 * sourceAdvantage)
    (hmodeMinus : |lossyMinus - ordinaryMinus| ≤ modeMinusDefect)
    (hordinaryMinus : |ordinaryMinus - nativeMinus| ≤ ordinaryMinusDefect)
    (hsampler : 0 ≤ samplerDefect) :
    |nativePlus - nativeMinus| ≤
      ordinaryPlusDefect + ordinaryMinusDefect +
        modePlusDefect + modeMinusDefect + rhoPlus + rhoMinus +
        Real.sqrt ((2 : ℝ) ^ (digestCount + 1) * sourceAdvantage) +
        samplerDefect := by
  have hcentralRaw := averagedUniformBinaryDigestMatchSquareGap_le
    hashSeedSampler digestCount hash huniform
    |lossyPlus - lossyMinus| rhoPlus rhoMinus realSecondMoment
    0 sourceAdvantage 0 hdiagonal (by simpa using hsource) (by simp)
  have hcentral :
      |lossyPlus - lossyMinus| ≤ rhoPlus + rhoMinus +
        Real.sqrt ((2 : ℝ) ^ (digestCount + 1) * sourceAdvantage) := by
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hcentralRaw
  have hhybrid := completeAcceptanceHybrid_le
    nativePlus ordinaryPlus lossyPlus lossyMinus ordinaryMinus nativeMinus
    ordinaryPlusDefect ordinaryMinusDefect modePlusDefect modeMinusDefect
    (rhoPlus + rhoMinus +
      Real.sqrt ((2 : ℝ) ^ (digestCount + 1) * sourceAdvantage))
    samplerDefect hordinaryPlus hmodePlus hcentral hmodeMinus hordinaryMinus hsampler
  linarith

/-- Final boxed form from the sketch: when the native and ordinary branches are exactly equal and
the reference source erases the sign exactly, only the two computational mode switches, the two
diagonal defects, the `2 ^ r` source term, and one sampler defect remain. -/
theorem averagedUniformBinaryCompleteDigestComposition_le_of_exactFidelityAndErasure
    {HashSeed Prefix Suffix : Type} [Fintype HashSeed]
    [Fintype Prefix] [SampleableType Prefix]
    [Fintype Suffix] [SampleableType Suffix]
    [Fintype (Prefix × Suffix)] [SampleableType (Prefix × Suffix)]
    (hashSeedSampler : ProbComp HashSeed) (digestCount : ℕ)
    (hash : HashSeed → Prefix → (Fin digestCount → Bool))
    (huniform : ∀ hashSeed, HasUniformOutput (hash hashSeed))
    (nativePlus ordinaryPlus lossyPlus lossyMinus ordinaryMinus nativeMinus
      modePlusDefect modeMinusDefect rhoPlus rhoMinus realSecondMoment
      sourceAdvantage samplerDefect : ℝ)
    (hordinaryPlus : nativePlus = ordinaryPlus)
    (hmodePlus : |ordinaryPlus - lossyPlus| ≤ modePlusDefect)
    (hdiagonal : |lossyPlus - lossyMinus| ≤ rhoPlus + rhoMinus +
      Real.sqrt
        (averagedConditionalDigestConcentration
          (Prefix := Prefix) (Suffix := Suffix)
          hashSeedSampler digestCount hash * realSecondMoment))
    (hsource : |realSecondMoment| ≤ 2 * sourceAdvantage)
    (hmodeMinus : |lossyMinus - ordinaryMinus| ≤ modeMinusDefect)
    (hordinaryMinus : ordinaryMinus = nativeMinus)
    (hsampler : 0 ≤ samplerDefect) :
    |nativePlus - nativeMinus| ≤
      modePlusDefect + modeMinusDefect + rhoPlus + rhoMinus +
        Real.sqrt ((2 : ℝ) ^ (digestCount + 1) * sourceAdvantage) +
        samplerDefect := by
  have hbound :=
    averagedUniformBinaryCompleteDigestComposition_le_of_exactErasure
      hashSeedSampler digestCount hash huniform
      nativePlus ordinaryPlus lossyPlus lossyMinus ordinaryMinus nativeMinus
      0 0 modePlusDefect modeMinusDefect rhoPlus rhoMinus
      realSecondMoment sourceAdvantage samplerDefect
      (by simp [hordinaryPlus]) hmodePlus hdiagonal hsource hmodeMinus
      (by simp [hordinaryMinus]) hsampler
  simpa using hbound

/-! ## Hidden-rank factorization does not absorb the nonce term -/

/-- A deterministic target factors through a public digest if it is a function of that digest
alone. -/
def FactorsThroughDigest
    {Prefix Digest Target : Type}
    (hash : Prefix → Digest) (target : Prefix → Target) : Prop :=
  ∃ simulator : Digest → Target, ∀ prefixValue,
    target prefixValue = simulator (hash prefixValue)

/-- Exact digest factorization makes a target constant on every hash fiber. -/
theorem factorsThroughDigest_eq_of_hash_eq
    {Prefix Digest Target : Type}
    (hash : Prefix → Digest) (target : Prefix → Target)
    (hfactor : FactorsThroughDigest hash target)
    (first second : Prefix) (hhash : hash first = hash second) :
    target first = target second := by
  rcases hfactor with ⟨simulator, hsimulator⟩
  calc
    target first = simulator (hash first) := hsimulator first
    _ = simulator (hash second) := congrArg simulator hhash
    _ = target second := (hsimulator second).symm

/-- One nonconstant pair in a hash fiber rules out exact digest-only generation. -/
theorem not_factorsThroughDigest_of_hash_collision
    {Prefix Digest Target : Type}
    (hash : Prefix → Digest) (target : Prefix → Target)
    (first second : Prefix) (hhash : hash first = hash second)
    (htarget : target first ≠ target second) :
    ¬ FactorsThroughDigest hash target := by
  intro hfactor
  exact htarget
    (factorsThroughDigest_eq_of_hash_eq hash target hfactor first second hhash)

/-- If a residual is already digest-factorized, adding a nonce contribution which varies inside
one fiber destroys exact digest factorization. -/
theorem factorizedResidual_add_nonce_not_factorsThroughDigest
    {Prefix Digest R : Type} [AddLeftCancelSemigroup R]
    (hash : Prefix → Digest) (residual nonce : Prefix → R)
    (hresidual : FactorsThroughDigest hash residual)
    (first second : Prefix) (hhash : hash first = hash second)
    (hnonce : nonce first ≠ nonce second) :
    ¬ FactorsThroughDigest hash (fun prefixValue ↦
      residual prefixValue + nonce prefixValue) := by
  have hresidualEqual : residual first = residual second :=
    factorsThroughDigest_eq_of_hash_eq
      hash residual hresidual first second hhash
  apply not_factorsThroughDigest_of_hash_collision
    hash (fun prefixValue ↦ residual prefixValue + nonce prefixValue)
    first second hhash
  intro hequal
  rw [hresidualEqual] at hequal
  exact hnonce (add_left_cancel hequal)

/-- A hidden-rank identity rewrites the linear term, but leaves the entire native nonce KDM
message in the residual.  This identity supplies no digest factorization for that message. -/
theorem hiddenRank_nonceResidual_identity
    {R : Type} [CommRing R]
    (linearTerm digestTerm residual gadget secret error : R)
    (control : Bool) (hhiddenRank : linearTerm = digestTerm + residual) :
    linearTerm - gadget * bitScalar control * secret + error =
      digestTerm +
        (residual - gadget * bitScalar control * secret + error) := by
  rw [hhiddenRank]
  ring

/-- Switching a control bit from zero to one changes the nonce KDM message whenever the gadget
does not annihilate the second subset secret. -/
theorem nonceKDMMessage_ne_of_false_true
    {R Index : Type} [CommRing R] [Fintype Index]
    (basis : Index → R) (suffix gadget : R) (control : Index)
    (first second : Index → Bool)
    (hfirst : first control = false) (hsecond : second control = true)
    (hnonzero : gadget * subsetSecret basis second suffix ≠ 0) :
    nonceKDMMessage basis first suffix gadget control ≠
      nonceKDMMessage basis second suffix gadget control := by
  have hneg :
      -(gadget * subsetSecret basis second suffix) ≠ 0 :=
    neg_ne_zero.mpr hnonzero
  simpa [nonceKDMMessage, hfirst, hsecond] using hneg.symm

/-- Concrete nonce-row obstruction.  Even when the hidden-rank residual already factors through
the digest, a same-digest collision crossing a nondegenerate nonce control bit prevents the
combined residual from being generated from the digest alone. -/
theorem factorizedHiddenRankResidual_add_nonceKDMMessage_not_factorsThroughDigest
    {R Index Digest : Type} [CommRing R] [Fintype Index]
    (basis : Index → R) (suffix gadget : R) (control : Index)
    (hash : (Index → Bool) → Digest) (residual : (Index → Bool) → R)
    (hresidual : FactorsThroughDigest hash residual)
    (first second : Index → Bool) (hhash : hash first = hash second)
    (hfirst : first control = false) (hsecond : second control = true)
    (hnonzero : gadget * subsetSecret basis second suffix ≠ 0) :
    ¬ FactorsThroughDigest hash (fun prefixBits ↦
      residual prefixBits +
        nonceKDMMessage basis prefixBits suffix gadget control) := by
  apply factorizedResidual_add_nonce_not_factorsThroughDigest
    hash residual
    (fun prefixBits ↦ nonceKDMMessage basis prefixBits suffix gadget control)
    hresidual first second hhash
  exact nonceKDMMessage_ne_of_false_true
    basis suffix gadget control first second hfirst hsecond hnonzero

end

end FormalProof4FHE.TFHE.NativeTRGSWProofDualMode
