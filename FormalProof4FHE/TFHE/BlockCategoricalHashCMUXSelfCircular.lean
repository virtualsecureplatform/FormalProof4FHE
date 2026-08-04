/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.BlockCategoricalSelfCircular
import FormalProof4FHE.TFHE.JointSubsetKeyBRKRefined
import FormalProof4FHE.TFHE.NativeTRGSWHashLossyCompleteView
import FormalProof4FHE.TFHE.NativeTRGSWProofDualMode
import FormalProof4FHE.TFHE.SourceAlignedBRKKSKJointLaw
import Mathlib.Data.Finset.SymmDiff

/-!
# Hash-CMUX sanitization for block-categorical self-circular TFHE

This module formalizes the new part of
`block_categorical_hash_cmux_self_circular_tfhe.tex`.  Sections 1--18 of that note repeat the
block-categorical argument already checked in `BlockCategoricalSelfCircular`; this file imports
that result and starts at the complete-vector CMUX sanitizer.

The checked results are deliberately joint-law statements.  A fresh zero encryption translates
the *complete* public mask by an independent uniform mask, and the corrected error is compared
with the prescribed error together with every retained public context.  This rules out the
invalid marginal-only interpretation of the sanitizer.

The module proves:

* the exact mask and phase identities of complete-batch sanitization;
* uniform-mask rerandomization conditioned on arbitrary retained state;
* data processing from a joint context/error comparison to canonical fresh encryption;
* conditional smudging, deterministic decoding-box correctness, and their explicit tradeoff;
* the covariance no-go for returning to an already saturated narrow covariance;
* exact uniformization of the wrong-candidate mask/body pair;
* the hash-candidate prediction identity and its additional digest-cardinality loss;
* the projected hidden-mode and final sanitized-security compositions.

Equal-covariance Gaussian translation, discrete/rounded/wrapped approximation, homomorphic hash
equality, and the contextual source assumption remain explicit interfaces.  Mathlib does not
currently supply the required finite wrapped multivariate Gaussian law.  No ordinary-RLWE
compiler for the secret-message BRK is asserted.
-/

set_option autoImplicit false

open Matrix OracleComp
open scoped BigOperators symmDiff

namespace FormalProof4FHE.TFHE.Native.BlockCategoricalHashCMUXSelfCircular

noncomputable section

open FormalProof4FHE.FiniteProduct
open JointSubsetKeyBRK
open JointSubsetKeyBRKRefined
open NativeTRGSWAggregateProjectedLeakage
open NativeTRGSWHashCompressedSecurity
open NativeTRGSWHashLossyCompleteView
open NativeTRGSWProofDualMode
open RGSWCoefficientCircularSecurity
open SourceAlignedBRKKSKJointLaw.NativeCompiler

/-! ## Complete-vector sanitizer algebra -/

/-- Add a fresh zero encryption and a body-only correction to a complete TLWE batch.  The
fresh-zero body is `s R + E₀`; consequently this definition is the literal ciphertext addition
performed by the sanitizer, not a phase-only idealization. -/
def sanitizeBatch
    {R : Type} [Ring R] {dimension samples : ℕ}
    (secret : Fin dimension → R)
    (raw : TLWE.BatchCiphertext R dimension samples)
    (freshMask : Matrix (Fin dimension) (Fin samples) R)
    (zeroError correction : Fin samples → R) :
    TLWE.BatchCiphertext R dimension samples :=
  (raw.1 + freshMask,
    raw.2 + vecMul secret freshMask + zeroError + correction)

@[simp]
theorem sanitizeBatch_mask
    {R : Type} [Ring R] {dimension samples : ℕ}
    (secret : Fin dimension → R)
    (raw : TLWE.BatchCiphertext R dimension samples)
    (freshMask : Matrix (Fin dimension) (Fin samples) R)
    (zeroError correction : Fin samples → R) :
    (sanitizeBatch secret raw freshMask zeroError correction).1 =
      raw.1 + freshMask :=
  rfl

/-- Exact phase identity of complete-vector sanitization:
`phase(Y_raw + Enc(0; R,E₀) + (0,F)) = phase(Y_raw) + E₀ + F`. -/
theorem batchPhase_sanitizeBatch
    {R : Type} [Ring R] {dimension samples : ℕ}
    (secret : Fin dimension → R)
    (raw : TLWE.BatchCiphertext R dimension samples)
    (freshMask : Matrix (Fin dimension) (Fin samples) R)
    (zeroError correction : Fin samples → R) :
    TLWE.batchPhase secret
        (sanitizeBatch secret raw freshMask zeroError correction) =
      TLWE.batchPhase secret raw + zeroError + correction := by
  funext row
  simp only [TLWE.batchPhase, sanitizeBatch, Pi.sub_apply, Pi.add_apply,
    Matrix.vecMul_add]
  noncomm_ring

/-- On a successful CMUX normal form, sanitization is exactly a fresh-mask encryption whose
error is the evaluator residual plus zero-encryption error plus correction. -/
theorem sanitizeBatch_batchAssemble
    {R : Type} [CommRing R] {dimension samples : ℕ}
    (secret : Fin dimension → R)
    (rawMask freshMask : Matrix (Fin dimension) (Fin samples) R)
    (message residual zeroError correction : Fin samples → R) :
    sanitizeBatch secret
        (TLWE.batchAssemble secret rawMask message residual)
        freshMask zeroError correction =
      TLWE.batchAssemble secret (rawMask + freshMask) message
        (residual + zeroError + correction) := by
  apply Prod.ext
  · rfl
  · funext row
    simp only [sanitizeBatch, TLWE.batchAssemble, Pi.add_apply,
      Matrix.vecMul_add]
    ring

/-! ## Exact uniform mask rerandomization with retained context -/

/-- Translation by a fixed element is a permutation of an additive group. -/
def addLeftEquiv {A : Type} [AddGroup A] (offset : A) : A ≃ A where
  toFun value := offset + value
  invFun value := -offset + value
  left_inv value := by simp
  right_inv value := by simp

/-- A fixed translation of an exactly uniform finite additive carrier remains exactly uniform. -/
theorem add_uniform_evalDist
    {A : Type} [AddGroup A] [Fintype A] [SampleableType A]
    (offset : A) :
    evalDist ((fun value ↦ offset + value) <$> ($ᵗ A)) =
      evalDist ($ᵗ A) :=
  evalDist_map_bijective_uniform_cross
    (α := A) (β := A) (fun value ↦ offset + value)
    (addLeftEquiv offset).bijective

/-- Sample a retained context and then translate a fresh uniform mask by a context-dependent raw
mask. -/
def rerandomizedMaskView
    {Context Mask : Type} [AddGroup Mask] [Fintype Mask] [SampleableType Mask]
    (contextSampler : ProbComp Context) (rawMask : Context → Mask) :
    ProbComp (Context × Mask) := do
  let context ← contextSampler
  let mask ← (fun freshMask ↦ rawMask context + freshMask) <$> ($ᵗ Mask)
  return (context, mask)

/-- The reference law keeps the same context and samples an independent uniform mask. -/
def independentMaskView
    {Context Mask : Type} [Fintype Mask] [SampleableType Mask]
    (contextSampler : ProbComp Context) : ProbComp (Context × Mask) := do
  let context ← contextSampler
  let mask ← $ᵗ Mask
  return (context, mask)

/-- Exact conditional mask rerandomization.  The equality includes the retained context, so it
states both uniformity and independence rather than only a uniform marginal. -/
theorem rerandomizedMaskView_evalDist_eq_independent
    {Context Mask : Type} [AddGroup Mask] [Fintype Mask] [SampleableType Mask]
    (contextSampler : ProbComp Context) (rawMask : Context → Mask) :
    evalDist (rerandomizedMaskView contextSampler rawMask) =
      evalDist (independentMaskView (Mask := Mask) contextSampler) := by
  unfold rerandomizedMaskView independentMaskView
  refine evalDist_bind_congr' contextSampler fun context ↦ ?_
  have hmask := add_uniform_evalDist (rawMask context)
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    hmask (fun mask ↦ pure (context, mask))

/-! ## Context-aware canonical fresh encryption -/

/-- Assemble a canonical encryption after sampling a joint retained-context/error law.  The mask
is sampled independently only after the joint law has been fixed. -/
def canonicalMaskedBatchView
    {R Context : Type} [CommRing R] [Fintype R] [SampleableType R]
    {dimension samples : ℕ}
    (jointError : ProbComp (Context × (Fin samples → R)))
    (secret : Context → Fin dimension → R)
    (message : Context → Fin samples → R) :
    ProbComp (Context × TLWE.BatchCiphertext R dimension samples) := do
  let contextError ← jointError
  let mask ← $ᵗ (Matrix (Fin dimension) (Fin samples) R)
  return (contextError.1,
    TLWE.batchAssemble (secret contextError.1) mask
      (message contextError.1) contextError.2)

/-- The successful sanitizer normal form before erasing its translated raw mask. -/
def translatedMaskedBatchView
    {R Context : Type} [CommRing R] [Fintype R] [SampleableType R]
    {dimension samples : ℕ}
    (jointError : ProbComp (Context × (Fin samples → R)))
    (rawMask : Context → (Fin samples → R) →
      Matrix (Fin dimension) (Fin samples) R)
    (secret : Context → Fin dimension → R)
    (message : Context → Fin samples → R) :
    ProbComp (Context × TLWE.BatchCiphertext R dimension samples) := do
  let contextError ← jointError
  let mask ←
    (fun freshMask ↦ rawMask contextError.1 contextError.2 + freshMask) <$>
      ($ᵗ (Matrix (Fin dimension) (Fin samples) R))
  return (contextError.1,
    TLWE.batchAssemble (secret contextError.1)
      mask
      (message contextError.1) contextError.2)

/-- The translated raw mask disappears exactly even when it depends on the complete retained
context and corrected error. -/
theorem translatedMaskedBatchView_evalDist_eq_canonical
    {R Context : Type} [CommRing R] [Fintype R] [SampleableType R]
    {dimension samples : ℕ}
    (jointError : ProbComp (Context × (Fin samples → R)))
    (rawMask : Context → (Fin samples → R) →
      Matrix (Fin dimension) (Fin samples) R)
    (secret : Context → Fin dimension → R)
    (message : Context → Fin samples → R) :
    evalDist (translatedMaskedBatchView jointError rawMask secret message) =
      evalDist (canonicalMaskedBatchView jointError secret message) := by
  unfold translatedMaskedBatchView canonicalMaskedBatchView
  refine evalDist_bind_congr' jointError fun contextError ↦ ?_
  let assemble := fun mask ↦
    (contextError.1,
      TLWE.batchAssemble (secret contextError.1) mask
        (message contextError.1) contextError.2)
  have hmask := add_uniform_evalDist (rawMask contextError.1 contextError.2)
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    hmask (fun mask ↦ pure (assemble mask))

/-- Continuation used after the joint context/error law in a canonical masked batch. -/
def canonicalMaskedBatchContinuation
    {R Context : Type} [CommRing R] [Fintype R] [SampleableType R]
    {dimension samples : ℕ}
    (secret : Context → Fin dimension → R)
    (message : Context → Fin samples → R)
    (contextError : Context × (Fin samples → R)) :
    ProbComp (Context × TLWE.BatchCiphertext R dimension samples) := do
  let mask ← $ᵗ (Matrix (Fin dimension) (Fin samples) R)
  return (contextError.1,
    TLWE.batchAssemble (secret contextError.1) mask
      (message contextError.1) contextError.2)

theorem canonicalMaskedBatchView_eq_bind
    {R Context : Type} [CommRing R] [Fintype R] [SampleableType R]
    {dimension samples : ℕ}
    (jointError : ProbComp (Context × (Fin samples → R)))
    (secret : Context → Fin dimension → R)
    (message : Context → Fin samples → R) :
    canonicalMaskedBatchView jointError secret message =
      jointError >>= canonicalMaskedBatchContinuation secret message := by
  rfl

/-- A comparison of complete joint context/error laws survives fresh-mask encryption. -/
theorem tvDist_canonicalMaskedBatchView_le_jointError
    {R Context : Type} [CommRing R] [Fintype R] [SampleableType R]
    {dimension samples : ℕ}
    (derived prescribed : ProbComp (Context × (Fin samples → R)))
    (secret : Context → Fin dimension → R)
    (message : Context → Fin samples → R) :
    tvDist
        (canonicalMaskedBatchView derived secret message)
        (canonicalMaskedBatchView prescribed secret message) ≤
      tvDist derived prescribed := by
  rw [canonicalMaskedBatchView_eq_bind, canonicalMaskedBatchView_eq_bind]
  exact tvDist_bind_right_le
    (canonicalMaskedBatchContinuation secret message) derived prescribed

/-- Complete-vector sanitizer theorem.  Evaluator failure is charged by `evaluationDefect`; the
only other statistical premise is the distance of the *joint* corrected-error law from the
prescribed joint law. -/
theorem tvDist_sanitized_canonical_le
    {R Context : Type} [CommRing R] [Fintype R] [SampleableType R]
    {dimension samples : ℕ}
    (actual : ProbComp (Context × TLWE.BatchCiphertext R dimension samples))
    (derived prescribed : ProbComp (Context × (Fin samples → R)))
    (rawMask : Context → (Fin samples → R) →
      Matrix (Fin dimension) (Fin samples) R)
    (secret : Context → Fin dimension → R)
    (message : Context → Fin samples → R)
    (evaluationDefect errorDefect : ℝ)
    (hevaluation : tvDist actual
      (translatedMaskedBatchView derived rawMask secret message) ≤ evaluationDefect)
    (herror : tvDist derived prescribed ≤ errorDefect) :
    tvDist actual (canonicalMaskedBatchView prescribed secret message) ≤
      evaluationDefect + errorDefect := by
  have hrerandomized :
      tvDist
          (translatedMaskedBatchView derived rawMask secret message)
          (canonicalMaskedBatchView derived secret message) = 0 := by
    rw [tvDist_eq_zero_iff]
    exact translatedMaskedBatchView_evalDist_eq_canonical
      derived rawMask secret message
  calc
    tvDist actual (canonicalMaskedBatchView prescribed secret message) ≤
        tvDist actual (translatedMaskedBatchView derived rawMask secret message) +
          tvDist (translatedMaskedBatchView derived rawMask secret message)
            (canonicalMaskedBatchView derived secret message) +
          tvDist (canonicalMaskedBatchView derived secret message)
            (canonicalMaskedBatchView prescribed secret message) := by
      have hfirst := tvDist_triangle actual
        (translatedMaskedBatchView derived rawMask secret message)
        (canonicalMaskedBatchView prescribed secret message)
      have hsecond := tvDist_triangle
        (translatedMaskedBatchView derived rawMask secret message)
        (canonicalMaskedBatchView derived secret message)
        (canonicalMaskedBatchView prescribed secret message)
      linarith
    _ ≤ evaluationDefect + 0 + errorDefect := by
      exact add_le_add (add_le_add hevaluation (le_of_eq hrerandomized))
        ((tvDist_canonicalMaskedBatchView_le_jointError
          derived prescribed secret message).trans herror)
    _ = evaluationDefect + errorDefect := by ring

/-! ## Conditional smudging -/

/-- View of a state-dependent residual shifted by independent correction noise. -/
def shiftedCorrectionView
    {State Context Error : Type} [Add Error]
    (context : State → Context) (derived : State → Error)
    (correction : ProbComp Error) (state : State) :
    ProbComp (Context × Error) :=
  (fun fresh ↦ (context state, derived state + fresh)) <$> correction

/-- Reference view with the same retained context and unshifted correction noise. -/
def unshiftedCorrectionView
    {State Context Error : Type}
    (context : State → Context) (correction : ProbComp Error) (state : State) :
    ProbComp (Context × Error) :=
  (fun fresh ↦ (context state, fresh)) <$> correction

/-- Retaining a deterministic context cannot increase the translation distance of correction
noise. -/
theorem tvDist_shiftedCorrectionView_le
    {State Context Error : Type} [Add Error]
    (context : State → Context) (derived : State → Error)
    (correction : ProbComp Error) (state : State) :
    tvDist (shiftedCorrectionView context derived correction state)
        (unshiftedCorrectionView context correction state) ≤
      addShiftDistance correction (derived state) := by
  have hdata := tvDist_map_le (m := ProbComp)
    (fun error ↦ (context state, error))
    ((fun fresh ↦ derived state + fresh) <$> correction) correction
  simpa only [shiftedCorrectionView, unshiftedCorrectionView,
    addShiftDistance, Functor.map_map, Function.comp_apply] using hdata

/-- Conditional smudging with an explicit bad-state probability.  On a good state every residual
translation costs at most `shiftBound`; on a bad state the first hybrid keeps the shifted law,
and the patch-removal theorem charges exactly the bad probability. -/
theorem tvDist_conditionalSmudging_le
    {State Context Error : Type} [Add Error]
    (stateSampler : ProbComp State)
    (context : State → Context) (derived : State → Error)
    (correction : ProbComp Error)
    (bad : State → Prop) [DecidablePred bad]
    (badBound shiftBound : ℝ)
    (hshiftNonneg : 0 ≤ shiftBound)
    (hgood : ∀ state, ¬ bad state →
      addShiftDistance correction (derived state) ≤ shiftBound)
    (hbad : Pr[bad | stateSampler].toReal ≤ badBound) :
    tvDist
        (stateSampler >>= shiftedCorrectionView context derived correction)
        (stateSampler >>= unshiftedCorrectionView context correction) ≤
      badBound + shiftBound := by
  let shifted := shiftedCorrectionView context derived correction
  let target := unshiftedCorrectionView context correction
  let patched := patchedTarget bad shifted target
  have hshiftedPatched :
      tvDist (stateSampler >>= shifted) (stateSampler >>= patched) ≤ shiftBound := by
    refine tvDist_bind_left_le_const' stateSampler shifted patched shiftBound fun state ↦ ?_
    by_cases hstate : bad state
    · simp [patched, patchedTarget, hstate, hshiftNonneg]
    · simp only [patched, patchedTarget, hstate, ↓reduceIte]
      exact (tvDist_shiftedCorrectionView_le context derived correction state).trans
        (hgood state hstate)
  have hpatch :=
    (tvDist_patchedTarget_target_le stateSampler bad shifted target).trans hbad
  calc
    tvDist (stateSampler >>= shifted) (stateSampler >>= target) ≤
        tvDist (stateSampler >>= shifted) (stateSampler >>= patched) +
          tvDist (stateSampler >>= patched) (stateSampler >>= target) :=
      tvDist_triangle _ _ _
    _ ≤ shiftBound + badBound := add_le_add hshiftedPatched hpatch
    _ = badBound + shiftBound := add_comm _ _

/-- Finite-box specialization once the pointwise no-wrap translation estimate has been
established for the selected correction sampler. -/
theorem tvDist_conditionalFiniteBoxSmudging_le
    {State Context Error : Type} [Add Error]
    (stateSampler : ProbComp State)
    (context : State → Context) (derived : State → Error)
    (correction : ProbComp Error)
    (bad : State → Prop) [DecidablePred bad]
    (badBound coordinateCount residualBound correctionRadius : ℝ)
    (hcoordinateCount : 0 ≤ coordinateCount)
    (hresidualBound : 0 ≤ residualBound)
    (hdenom : 0 ≤ 2 * correctionRadius + 1)
    (hgood : ∀ state, ¬ bad state →
      addShiftDistance correction (derived state) ≤
        coordinateCount * residualBound / (2 * correctionRadius + 1))
    (hbad : Pr[bad | stateSampler].toReal ≤ badBound) :
    tvDist
        (stateSampler >>= shiftedCorrectionView context derived correction)
        (stateSampler >>= unshiftedCorrectionView context correction) ≤
      badBound + coordinateCount * residualBound /
        (2 * correctionRadius + 1) := by
  exact tvDist_conditionalSmudging_le stateSampler context derived correction bad
    badBound (coordinateCount * residualBound / (2 * correctionRadius + 1))
    (div_nonneg (mul_nonneg hcoordinateCount hresidualBound) hdenom)
    hgood hbad

/-- Gaussian/Mahalanobis specialization of conditional smudging. -/
theorem tvDist_conditionalGaussianSmudging_le
    {State Context Error : Type} [Add Error]
    (stateSampler : ProbComp State)
    (context : State → Context) (derived : State → Error)
    (correction : ProbComp Error)
    (bad : State → Prop) [DecidablePred bad]
    (badBound mahalanobisBound : ℝ)
    (hmahalanobis : 0 ≤ mahalanobisBound)
    (hgood : ∀ state, ¬ bad state →
      addShiftDistance correction (derived state) ≤ mahalanobisBound / 2)
    (hbad : Pr[bad | stateSampler].toReal ≤ badBound) :
    tvDist
        (stateSampler >>= shiftedCorrectionView context derived correction)
        (stateSampler >>= unshiftedCorrectionView context correction) ≤
      badBound + mahalanobisBound / 2 := by
  exact tvDist_conditionalSmudging_le stateSampler context derived correction bad
    badBound (mahalanobisBound / 2) (by positivity) hgood hbad

/-! ## Finite-box and Gaussian translation profiles -/

/-- Exact product-overlap expression for an independent centered box.  The coordinates are
allowed to have different normalized overlap losses. -/
def boxTranslationDistance
    {Coordinate : Type} [Fintype Coordinate]
    (coordinateLoss : Coordinate → ℝ) : ℝ :=
  1 - ∏ coordinate, (1 - coordinateLoss coordinate)

/-- The exact product expression is bounded by the coordinatewise union bound. -/
theorem boxTranslationDistance_le_sum
    {Coordinate : Type} [Fintype Coordinate]
    (coordinateLoss : Coordinate → ℝ)
    (hnonneg : ∀ coordinate, 0 ≤ coordinateLoss coordinate)
    (hle : ∀ coordinate, coordinateLoss coordinate ≤ 1) :
    boxTranslationDistance coordinateLoss ≤
      ∑ coordinate, coordinateLoss coordinate := by
  exact one_sub_prod_one_sub_le_sum_real coordinateLoss hnonneg hle

/-- If every coordinate loses at most one common amount, the complete box distance is at most
the coordinate count times that amount. -/
theorem boxTranslationDistance_le_card_mul
    {Coordinate : Type} [Fintype Coordinate]
    (coordinateLoss : Coordinate → ℝ) (perCoordinate : ℝ)
    (hnonneg : ∀ coordinate, 0 ≤ coordinateLoss coordinate)
    (hleOne : ∀ coordinate, coordinateLoss coordinate ≤ 1)
    (hle : ∀ coordinate, coordinateLoss coordinate ≤ perCoordinate) :
    boxTranslationDistance coordinateLoss ≤
      Fintype.card Coordinate * perCoordinate := by
  calc
    boxTranslationDistance coordinateLoss ≤
        ∑ coordinate, coordinateLoss coordinate :=
      boxTranslationDistance_le_sum coordinateLoss hnonneg hleOne
    _ ≤ ∑ _coordinate : Coordinate, perCoordinate := by
      exact Finset.sum_le_sum fun coordinate _ ↦ hle coordinate
    _ = Fintype.card Coordinate * perCoordinate := by simp

/-! ### Exact finite uniform-support distance -/

/-- Two uniform laws on nonempty finite supports of the same size have total variation equal to
one minus their normalized overlap.  This theorem is stated in an arbitrary finite ambient
carrier; centered intervals below provide the exact overlap count. -/
theorem tvDist_uniformFinset_sameCard
    {Omega : Type} [Fintype Omega] [DecidableEq Omega] [SampleableType Omega]
    (left right : Finset Omega) [Nonempty left] [Nonempty right]
    (hcard : left.card = right.card) :
    tvDist (uniformFinset left) (uniformFinset right) =
      1 - (left ∩ right).card / left.card := by
  classical
  rw [FormalProof4FHE.LeftoverHash.tvDist_eq_half_sum_abs]
  simp_rw [probOutput_uniformFinset]
  have hleftPosNat : 0 < left.card := by
    exact Finset.card_pos.mpr (by
      obtain ⟨value, hvalue⟩ := (inferInstance : Nonempty left)
      exact ⟨value, hvalue⟩)
  have hleftPos : (0 : ℝ) < left.card := by exact_mod_cast hleftPosNat
  have hinterLe : (left ∩ right).card ≤ left.card :=
    Finset.card_le_card Finset.inter_subset_left
  have hpoint (output : Omega) :
      |(if output ∈ left then (left.card : ENNReal)⁻¹ else 0).toReal -
          (if output ∈ right then (right.card : ENNReal)⁻¹ else 0).toReal| =
        if output ∈ (left ∆ right) then (left.card : ℝ)⁻¹ else 0 := by
    by_cases hleft : output ∈ left <;> by_cases hright : output ∈ right
    · have hnot : output ∉ left ∆ right := by
        simp [Finset.mem_symmDiff, hleft, hright]
      simp [hleft, hright, hnot, hcard]
    · have hmem : output ∈ left ∆ right := by
        simp [Finset.mem_symmDiff, hleft, hright]
      simp [hleft, hright, hmem,
        ENNReal.toReal_inv, ENNReal.toReal_natCast]
    · have hmem : output ∈ left ∆ right := by
        simp [Finset.mem_symmDiff, hleft, hright]
      simp [hleft, hright, hmem, hcard,
        ENNReal.toReal_inv, ENNReal.toReal_natCast]
    · have hnot : output ∉ left ∆ right := by
        simp [Finset.mem_symmDiff, hleft, hright]
      simp [hleft, hright, hnot]
  simp_rw [hpoint]
  have hsymmCard : (left ∆ right).card =
      2 * (left.card - (left ∩ right).card) := by
    rw [Finset.symmDiff_def,
      Finset.card_union_of_disjoint
        (Finset.disjoint_sdiff.mono_left Finset.sdiff_subset),
      Finset.card_sdiff, Finset.card_sdiff, hcard,
      Finset.inter_comm right left]
    omega
  rw [Finset.sum_ite_mem]
  simp only [Finset.univ_inter, Finset.sum_const, nsmul_eq_mul, hsymmCard]
  push_cast [Nat.cast_sub hinterLe]
  field_simp

/-! ### Exact centered-interval overlap -/

/-- Centered integer interval used by the finite-box correction sampler. -/
def centeredIntegerInterval (radius : ℕ) : Finset ℤ :=
  Finset.Icc (-(radius : ℤ)) (radius : ℤ)

/-- Translate the centered interval without modular wrap. -/
def shiftedCenteredIntegerInterval (radius : ℕ) (shift : ℤ) : Finset ℤ :=
  Finset.Icc (-(radius : ℤ) + shift) ((radius : ℤ) + shift)

@[simp]
theorem card_centeredIntegerInterval (radius : ℕ) :
    (centeredIntegerInterval radius).card = 2 * radius + 1 := by
  simp [centeredIntegerInterval]
  omega

@[simp]
theorem card_shiftedCenteredIntegerInterval (radius : ℕ) (shift : ℤ) :
    (shiftedCenteredIntegerInterval radius shift).card = 2 * radius + 1 := by
  simp [shiftedCenteredIntegerInterval]
  omega

/-- Exact no-wrap overlap count.  Natural subtraction supplies the positive part automatically:
the overlap is `2R+1-|v|` while positive and zero after the intervals separate. -/
theorem card_centeredIntegerInterval_inter_shifted
    (radius : ℕ) (shift : ℤ) :
    (centeredIntegerInterval radius ∩
        shiftedCenteredIntegerInterval radius shift).card =
      (2 * radius + 1) - shift.natAbs := by
  have hinter :
      centeredIntegerInterval radius ∩ shiftedCenteredIntegerInterval radius shift =
        Finset.Icc
          (max (-(radius : ℤ)) (-(radius : ℤ) + shift))
          (min (radius : ℤ) ((radius : ℤ) + shift)) := by
    ext value
    simp only [centeredIntegerInterval, shiftedCenteredIntegerInterval,
      Finset.mem_inter, Finset.mem_Icc]
    omega
  rw [hinter, Int.card_Icc]
  by_cases hshift : 0 ≤ shift
  · rw [max_eq_right (by omega), min_eq_left (by omega)]
    have habs : (shift.natAbs : ℤ) = shift :=
      Int.natAbs_of_nonneg hshift
    omega
  · have hshift' : shift ≤ 0 := le_of_not_ge hshift
    rw [max_eq_left (by omega), min_eq_right (by omega)]
    have habs : (shift.natAbs : ℤ) = -shift :=
      Int.ofNat_natAbs_of_nonpos hshift'
    omega

/-- Normalized one-coordinate loss from a no-wrap centered interval. -/
def centeredIntervalCoordinateLoss (radius : ℕ) (shift : ℤ) : ℝ :=
  (min (2 * radius + 1) shift.natAbs : ℝ) / (2 * radius + 1)

theorem centeredIntervalCoordinateLoss_nonneg (radius : ℕ) (shift : ℤ) :
    0 ≤ centeredIntervalCoordinateLoss radius shift := by
  unfold centeredIntervalCoordinateLoss
  positivity

theorem centeredIntervalCoordinateLoss_le_one (radius : ℕ) (shift : ℤ) :
    centeredIntervalCoordinateLoss radius shift ≤ 1 := by
  unfold centeredIntervalCoordinateLoss
  have hdenom : (0 : ℝ) < 2 * radius + 1 := by positivity
  rw [div_le_one hdenom]
  exact_mod_cast Nat.min_le_left (2 * radius + 1) shift.natAbs

/-- The normalized missing-overlap expression is exactly the clipped coordinate loss. -/
theorem one_sub_centeredIntervalOverlap_eq_loss (radius : ℕ) (shift : ℤ) :
    1 -
        ((centeredIntegerInterval radius ∩
          shiftedCenteredIntegerInterval radius shift).card : ℝ) /
          (centeredIntegerInterval radius).card =
      centeredIntervalCoordinateLoss radius shift := by
  rw [card_centeredIntegerInterval_inter_shifted,
    card_centeredIntegerInterval]
  unfold centeredIntervalCoordinateLoss
  by_cases hshift : shift.natAbs ≤ 2 * radius + 1
  · have hshiftR : (shift.natAbs : ℝ) ≤ 2 * radius + 1 := by
      exact_mod_cast hshift
    rw [min_eq_right hshiftR]
    push_cast [Nat.cast_sub hshift]
    have hdenom : (0 : ℝ) < 2 * radius + 1 := by positivity
    field_simp
    ring
  · have hlarge : 2 * radius + 1 ≤ shift.natAbs := le_of_not_ge hshift
    have hlargeR : (2 * radius + 1 : ℕ) ≤ shift.natAbs := hlarge
    have hlargeReal : (2 * radius + 1 : ℝ) ≤ shift.natAbs := by
      exact_mod_cast hlargeR
    rw [Nat.sub_eq_zero_of_le hlarge, min_eq_left hlargeReal]
    have hdenom : (2 * radius + 1 : ℝ) ≠ 0 := by positivity
    simp [hdenom]

/-- Coordinate losses for an independent centered box are bounded by the familiar L1 ratio. -/
theorem centeredIntervalCoordinateLoss_le_absRatio
    (radius : ℕ) (shift : ℤ) :
    centeredIntervalCoordinateLoss radius shift ≤
      (shift.natAbs : ℝ) / (2 * radius + 1) := by
  unfold centeredIntervalCoordinateLoss
  gcongr
  exact_mod_cast Nat.min_le_right (2 * radius + 1) shift.natAbs

/-- Exact coordinatewise overlap fraction of a centered product box. -/
def centeredBoxOverlapFraction
    {Coordinate : Type} [Fintype Coordinate]
    (radius : ℕ) (shift : Coordinate → ℤ) : ℝ :=
  ∏ coordinate,
    ((centeredIntegerInterval radius ∩
      shiftedCenteredIntegerInterval radius (shift coordinate)).card : ℝ) /
      (centeredIntegerInterval radius).card

/-- The product-box overlap is exactly the product of one minus the clipped coordinate losses. -/
theorem centeredBoxOverlapFraction_eq
    {Coordinate : Type} [Fintype Coordinate]
    (radius : ℕ) (shift : Coordinate → ℤ) :
    centeredBoxOverlapFraction radius shift =
      ∏ coordinate, (1 - centeredIntervalCoordinateLoss radius (shift coordinate)) := by
  unfold centeredBoxOverlapFraction
  apply Finset.prod_congr rfl
  intro coordinate _
  linarith [one_sub_centeredIntervalOverlap_eq_loss radius (shift coordinate)]

/-! ### Literal Cartesian realization of the centered box -/

/-- The finite set of integer vectors whose coordinates lie in the centered interval. -/
def centeredIntegerBox
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (radius : ℕ) : Finset (Coordinate → ℤ) :=
  Fintype.piFinset fun _coordinate ↦ centeredIntegerInterval radius

/-- The coordinatewise translate of `centeredIntegerBox`. -/
def shiftedCenteredIntegerBox
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (radius : ℕ) (shift : Coordinate → ℤ) : Finset (Coordinate → ℤ) :=
  Fintype.piFinset fun coordinate ↦
    shiftedCenteredIntegerInterval radius (shift coordinate)

@[simp]
theorem mem_centeredIntegerBox
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (radius : ℕ) (value : Coordinate → ℤ) :
    value ∈ centeredIntegerBox radius ↔
      ∀ coordinate, value coordinate ∈ centeredIntegerInterval radius := by
  simp [centeredIntegerBox]

@[simp]
theorem mem_shiftedCenteredIntegerBox
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (radius : ℕ) (shift value : Coordinate → ℤ) :
    value ∈ shiftedCenteredIntegerBox radius shift ↔
      ∀ coordinate,
        value coordinate ∈ shiftedCenteredIntegerInterval radius (shift coordinate) := by
  simp [shiftedCenteredIntegerBox]

@[simp]
theorem card_centeredIntegerBox
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (radius : ℕ) :
    (centeredIntegerBox (Coordinate := Coordinate) radius).card =
      ∏ _coordinate : Coordinate, (2 * radius + 1) := by
  simp [centeredIntegerBox]

@[simp]
theorem card_shiftedCenteredIntegerBox
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (radius : ℕ) (shift : Coordinate → ℤ) :
    (shiftedCenteredIntegerBox radius shift).card =
      ∏ _coordinate : Coordinate, (2 * radius + 1) := by
  simp [shiftedCenteredIntegerBox]

/-- Intersecting two Cartesian boxes acts coordinatewise. -/
theorem centeredIntegerBox_inter_shifted
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (radius : ℕ) (shift : Coordinate → ℤ) :
    centeredIntegerBox radius ∩ shiftedCenteredIntegerBox radius shift =
      Fintype.piFinset fun coordinate ↦
        centeredIntegerInterval radius ∩
          shiftedCenteredIntegerInterval radius (shift coordinate) := by
  ext value
  simp only [Finset.mem_inter, mem_centeredIntegerBox,
    mem_shiftedCenteredIntegerBox, Fintype.mem_piFinset]
  constructor
  · rintro ⟨hleft, hright⟩ coordinate
    exact ⟨hleft coordinate, hright coordinate⟩
  · intro h
    exact ⟨fun coordinate ↦ (h coordinate).1,
      fun coordinate ↦ (h coordinate).2⟩

@[simp]
theorem card_centeredIntegerBox_inter_shifted
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (radius : ℕ) (shift : Coordinate → ℤ) :
    (centeredIntegerBox radius ∩
        shiftedCenteredIntegerBox radius shift).card =
      ∏ coordinate : Coordinate,
        ((2 * radius + 1) - (shift coordinate).natAbs) := by
  rw [centeredIntegerBox_inter_shifted]
  simp only [Fintype.card_piFinset,
    card_centeredIntegerInterval_inter_shifted]

/-- The literal Cartesian supports have precisely the normalized overlap used by
`centeredBoxOverlapFraction`; no independence or support-factorization premise remains. -/
theorem centeredIntegerBox_overlap_fraction_eq
    {Coordinate : Type} [Fintype Coordinate] [DecidableEq Coordinate]
    (radius : ℕ) (shift : Coordinate → ℤ) :
    (((centeredIntegerBox radius ∩
        shiftedCenteredIntegerBox radius shift).card : ℝ) /
      (centeredIntegerBox (Coordinate := Coordinate) radius).card) =
        centeredBoxOverlapFraction radius shift := by
  rw [card_centeredIntegerBox_inter_shifted, card_centeredIntegerBox]
  unfold centeredBoxOverlapFraction
  simp_rw [card_centeredIntegerInterval_inter_shifted,
    card_centeredIntegerInterval]
  push_cast
  rw [Finset.prod_div_distrib]

/-- Abstract finite-ambient realization of the exact product-box formula.  For the literal
Cartesian interval support, `hoverlap` follows from `centeredIntegerBox_overlap_fraction_eq`;
keeping the
ambient carrier abstract also covers injective centered encodings into a modular no-wrap region. -/
theorem tvDist_uniformBoxSupport_eq
    {Omega Coordinate : Type}
    [Fintype Omega] [DecidableEq Omega] [SampleableType Omega]
    [Fintype Coordinate]
    (left right : Finset Omega) [Nonempty left] [Nonempty right]
    (radius : ℕ) (shift : Coordinate → ℤ)
    (hcard : left.card = right.card)
    (hoverlap : ((left ∩ right).card : ℝ) / left.card =
      centeredBoxOverlapFraction radius shift) :
    tvDist (uniformFinset left) (uniformFinset right) =
      boxTranslationDistance
        (fun coordinate ↦ centeredIntervalCoordinateLoss radius (shift coordinate)) := by
  rw [tvDist_uniformFinset_sameCard left right hcard,
    boxTranslationDistance, hoverlap, centeredBoxOverlapFraction_eq]

/-- The exact finite-box formula implies the L1 translation bound. -/
theorem centeredBoxTranslationDistance_le_l1
    {Coordinate : Type} [Fintype Coordinate]
    (radius : ℕ) (shift : Coordinate → ℤ) :
    boxTranslationDistance
        (fun coordinate ↦ centeredIntervalCoordinateLoss radius (shift coordinate)) ≤
      (∑ coordinate, (shift coordinate).natAbs : ℝ) /
        (2 * radius + 1) := by
  calc
    boxTranslationDistance
        (fun coordinate ↦ centeredIntervalCoordinateLoss radius (shift coordinate)) ≤
      ∑ coordinate, centeredIntervalCoordinateLoss radius (shift coordinate) :=
        boxTranslationDistance_le_sum _
          (fun coordinate ↦ centeredIntervalCoordinateLoss_nonneg radius (shift coordinate))
          (fun coordinate ↦ centeredIntervalCoordinateLoss_le_one radius (shift coordinate))
    _ ≤ ∑ coordinate,
        ((shift coordinate).natAbs : ℝ) / (2 * radius + 1) := by
      exact Finset.sum_le_sum fun coordinate _ ↦
        centeredIntervalCoordinateLoss_le_absRatio radius (shift coordinate)
    _ = (∑ coordinate, (shift coordinate).natAbs : ℝ) /
        (2 * radius + 1) := by rw [Finset.sum_div]

/-- Infinity-bound specialization of the finite-box translation estimate. -/
theorem centeredBoxTranslationDistance_le_card_mul
    {Coordinate : Type} [Fintype Coordinate]
    (radius bound : ℕ) (shift : Coordinate → ℤ)
    (hbound : ∀ coordinate, (shift coordinate).natAbs ≤ bound) :
    boxTranslationDistance
        (fun coordinate ↦ centeredIntervalCoordinateLoss radius (shift coordinate)) ≤
      Fintype.card Coordinate * (bound : ℝ) / (2 * radius + 1) := by
  calc
    boxTranslationDistance
        (fun coordinate ↦ centeredIntervalCoordinateLoss radius (shift coordinate)) ≤
      (∑ coordinate, (shift coordinate).natAbs : ℝ) /
        (2 * radius + 1) :=
      centeredBoxTranslationDistance_le_l1 radius shift
    _ ≤ (∑ _coordinate : Coordinate, (bound : ℝ)) /
        (2 * radius + 1) := by
      gcongr
      exact_mod_cast hbound coordinate
    _ = Fintype.card Coordinate * (bound : ℝ) /
        (2 * radius + 1) := by simp

/-- Mahalanobis energy of a shift against a supplied precision matrix. -/
def mahalanobisEnergy
    {Coordinate : Type} [Fintype Coordinate]
    (precision : Matrix Coordinate Coordinate ℝ)
    (shift : Coordinate → ℝ) : ℝ :=
  dotProduct shift (precision.mulVec shift)

/-- Proof-carrying boundary for the equal-covariance Gaussian shift inequality.  Discrete
sampling, rounding, and modular wrapping defects are intentionally not hidden in this field. -/
structure GaussianShiftCertificate
    {Coordinate Output : Type} [Fintype Coordinate]
    (precision : Matrix Coordinate Coordinate ℝ)
    (shift : Coordinate → ℝ)
    (shifted reference : ProbComp Output) where
  energy_nonneg : 0 ≤ mahalanobisEnergy precision shift
  tvDist_le : tvDist shifted reference ≤
    Real.sqrt (mahalanobisEnergy precision shift) / 2

/-- Install the certified equal-covariance Gaussian inequality and add explicit implementation
defects for discretization, rounding, and wrapping. -/
theorem gaussianReferenceTranslation_le
    {Coordinate Output : Type} [Fintype Coordinate]
    (precision : Matrix Coordinate Coordinate ℝ)
    (shift : Coordinate → ℝ)
    (shifted reference implemented : ProbComp Output)
    (certificate : GaussianShiftCertificate precision shift shifted reference)
    (implementationDefect : ℝ)
    (himplementation : tvDist implemented shifted ≤ implementationDefect) :
    tvDist implemented reference ≤ implementationDefect +
      Real.sqrt (mahalanobisEnergy precision shift) / 2 := by
  exact (tvDist_triangle implemented shifted reference).trans
    (add_le_add himplementation certificate.tvDist_le)

/-! ## Decoding-box correctness and privacy/correctness tradeoff -/

/-- Coordinatewise centered real box. -/
def InCenteredBox {Coordinate : Type} (radius : ℝ)
    (value : Coordinate → ℝ) : Prop :=
  ∀ coordinate, |value coordinate| ≤ radius

/-- Two centered boxes add into the box whose radius is the sum of their radii. -/
theorem inCenteredBox_add
    {Coordinate : Type} (firstRadius secondRadius : ℝ)
    (first second : Coordinate → ℝ)
    (hfirst : InCenteredBox firstRadius first)
    (hsecond : InCenteredBox secondRadius second) :
    InCenteredBox (firstRadius + secondRadius) (first + second) := by
  intro coordinate
  exact (abs_add_le (first coordinate) (second coordinate)).trans
    (add_le_add (hfirst coordinate) (hsecond coordinate))

/-- If the residual and correction radii fit strictly inside the decoding radius, their sum is
decodable. -/
theorem inCenteredBox_add_decode
    {Coordinate : Type} (residualRadius correctionRadius decodingRadius : ℝ)
    (residual correction : Coordinate → ℝ)
    (hresidual : InCenteredBox residualRadius residual)
    (hcorrection : InCenteredBox correctionRadius correction)
    (hmargin : residualRadius + correctionRadius < decodingRadius) :
    ∀ coordinate, |(residual + correction) coordinate| < decodingRadius := by
  intro coordinate
  exact (inCenteredBox_add residualRadius correctionRadius residual correction
    hresidual hcorrection coordinate).trans_lt hmargin

/-- Joint sampler used to state correctness of residual plus correction noise. -/
def residualCorrectionPair
    {Coordinate : Type}
    (residual correction : ProbComp (Coordinate → ℝ)) :
    ProbComp ((Coordinate → ℝ) × (Coordinate → ℝ)) := do
  let residualValue ← residual
  let correctionValue ← correction
  return (residualValue, correctionValue)

/-- Sample the complete post-sanitization phase error. -/
def correctedErrorSampler
    {Coordinate : Type}
    (residual correction : ProbComp (Coordinate → ℝ)) :
    ProbComp (Coordinate → ℝ) :=
  (fun pair ↦ pair.1 + pair.2) <$> residualCorrectionPair residual correction

theorem residualCorrectionPair_fst_evalDist
    {Coordinate : Type}
    (residual correction : ProbComp (Coordinate → ℝ)) :
    evalDist (Prod.fst <$> residualCorrectionPair residual correction) =
      evalDist residual := by
  unfold residualCorrectionPair
  simp only [map_eq_bind_pure_comp, bind_assoc, pure_bind]
  calc
    evalDist (residual >>= fun residualValue ↦
        correction >>= fun _correctionValue ↦ pure residualValue) =
      evalDist (residual >>= fun residualValue ↦ pure residualValue) := by
        refine evalDist_bind_congr' residual fun residualValue ↦ ?_
        exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
          correction (probFailure_eq_zero (mx := correction)) (pure residualValue)
    _ = evalDist residual := by simp

/-- If correction noise is always in its advertised box, every decoding failure implies that the
residual was outside its good box.  Consequently the correctness failure is bounded by the
residual bad-event probability. -/
theorem correctedError_failure_le_residual_bad
    {Coordinate : Type}
    (residual correction : ProbComp (Coordinate → ℝ))
    (residualRadius correctionRadius decodingRadius : ℝ)
    (hcorrection : ∀ value ∈ support correction,
      InCenteredBox correctionRadius value)
    (hmargin : residualRadius + correctionRadius < decodingRadius) :
    Pr[(fun error ↦ ¬ ∀ coordinate, |error coordinate| < decodingRadius) |
        correctedErrorSampler residual correction] ≤
      Pr[(fun value ↦ ¬ InCenteredBox residualRadius value) | residual] := by
  let pairSampler := residualCorrectionPair residual correction
  have hmono :
      Pr[(fun pair : (Coordinate → ℝ) × (Coordinate → ℝ) ↦
          ¬ ∀ coordinate, |(pair.1 + pair.2) coordinate| < decodingRadius) |
          pairSampler] ≤
        Pr[(fun pair : (Coordinate → ℝ) × (Coordinate → ℝ) ↦
          ¬ InCenteredBox residualRadius pair.1) | pairSampler] := by
    apply probEvent_mono
    intro pair hpair hfailure hgood
    apply hfailure
    apply inCenteredBox_add_decode residualRadius correctionRadius decodingRadius
      pair.1 pair.2 hgood
    · apply hcorrection pair.2
      have hsupport := hpair
      unfold pairSampler residualCorrectionPair at hsupport
      simp only [mem_support_bind_iff, support_pure,
        Set.mem_singleton_iff] at hsupport
      obtain ⟨residualValue, _hresidual, correctionValue,
        hcorrectionValue, rfl⟩ := hsupport
      exact hcorrectionValue
    · exact hmargin
  have hmarginal :
      Pr[(fun pair : (Coordinate → ℝ) × (Coordinate → ℝ) ↦
          ¬ InCenteredBox residualRadius pair.1) | pairSampler] =
        Pr[(fun value ↦ ¬ InCenteredBox residualRadius value) | residual] := by
    calc
      _ = Pr[(fun value ↦ ¬ InCenteredBox residualRadius value) |
          Prod.fst <$> pairSampler] :=
        (probEvent_fst_map pairSampler
          (fun value ↦ ¬ InCenteredBox residualRadius value)).symm
      _ = _ := by
        apply probEvent_congr' (fun _value _hvalue ↦ Iff.rfl)
        exact residualCorrectionPair_fst_evalDist residual correction
  unfold correctedErrorSampler
  rw [probEvent_map]
  exact hmono.trans_eq hmarginal

/-- Correctness and finite-box privacy with the *actual* correction radius.  Under the strict
decoding condition `B + R < rho`, replacing `R` by `rho-B` would make the denominator larger and
is not a valid upper-bound step. -/
theorem finiteBoxPrivacyCorrectness
    (badBound coordinateCount residualRadius correctionRadius decodingRadius
      privacyDefect : ℝ)
    (hprivacy : privacyDefect ≤ badBound +
      coordinateCount * residualRadius / (2 * correctionRadius + 1))
    (hmargin : residualRadius + correctionRadius < decodingRadius) :
    privacyDefect ≤ badBound +
        coordinateCount * residualRadius / (2 * correctionRadius + 1) ∧
      residualRadius + correctionRadius < decodingRadius :=
  ⟨hprivacy, hmargin⟩

/-- The manuscript's displayed denominator `2(rho-B)+1` is valid when a closed decoding region
permits the boundary choice `R = rho-B` (or when the same choice is otherwise certified). -/
theorem finiteBoxPrivacyClosedBoundary
    (badBound coordinateCount residualRadius correctionRadius decodingRadius
      privacyDefect : ℝ)
    (hprivacy : privacyDefect ≤ badBound +
      coordinateCount * residualRadius / (2 * correctionRadius + 1))
    (hchoice : correctionRadius = decodingRadius - residualRadius) :
    privacyDefect ≤ badBound +
      coordinateCount * residualRadius /
        (2 * (decodingRadius - residualRadius) + 1) := by
  simpa [hchoice] using hprivacy

/-! ## Covariance obstruction -/

/-- If independent correction noise completes a natural covariance to a target covariance, the
matrix difference `target - natural` must be positive semidefinite. -/
theorem target_sub_natural_posSemidef
    {Coordinate : Type}
    (target natural correction : Matrix Coordinate Coordinate ℝ)
    (hsum : target = natural + correction)
    (hcorrection : correction.PosSemidef) :
    (target - natural).PosSemidef := by
  have heq : target - natural = correction := by
    rw [hsum]
    abel
  rwa [heq]

/-- If the natural error already has the target covariance and an independent evaluator residual
has positive variance in some direction, adding any independent correction covariance cannot
return to the original target covariance. -/
theorem no_exact_narrow_covariance_after_independent_residual
    {Coordinate : Type} [DecidableEq Coordinate]
    (target evaluation correction : Matrix Coordinate Coordinate ℝ)
    (_hevaluation : evaluation.PosSemidef)
    (hcorrection : correction.PosSemidef)
    (coordinate : Coordinate)
    (hpositive : 0 < evaluation coordinate coordinate) :
    target ≠ target + evaluation + correction := by
  intro heq
  have hcorrectionDiag : 0 ≤ correction coordinate coordinate := by
    simpa using hcorrection.2 (Finsupp.single coordinate 1)
  have hdiag := congrArg (fun matrix ↦ matrix coordinate coordinate) heq
  simp only [Matrix.add_apply] at hdiag
  linarith

/-! ## Wrong-candidate exact uniformization -/

/-- Sample a retained state and translate two independent uniform carriers by arbitrary
state-dependent offsets.  The second carrier represents the random fallback plaintext plus every
fixed canonical error/body term. -/
def translatedUniformPairView
    {State Context Mask Body : Type}
    [AddGroup Mask] [Fintype Mask] [SampleableType Mask]
    [AddGroup Body] [Fintype Body] [SampleableType Body]
    (stateSampler : ProbComp State) (context : State → Context)
    (maskOffset : State → Mask) (bodyOffset : State → Body) :
    ProbComp (Context × (Mask × Body)) := do
  let state ← stateSampler
  let mask ← (fun fresh ↦ maskOffset state + fresh) <$> ($ᵗ Mask)
  let body ← (fun fresh ↦ bodyOffset state + fresh) <$> ($ᵗ Body)
  return (context state, (mask, body))

/-- Reference law with an exactly uniform mask/body pair independent of retained state. -/
def independentUniformPairView
    {State Context Mask Body : Type}
    [Fintype Mask] [SampleableType Mask]
    [Fintype Body] [SampleableType Body]
    (stateSampler : ProbComp State) (context : State → Context) :
    ProbComp (Context × (Mask × Body)) := do
  let state ← stateSampler
  let mask ← $ᵗ Mask
  let body ← $ᵗ Body
  return (context state, (mask, body))

/-- The wrong-candidate fallback makes the complete mask/body pair exactly uniform, jointly with
all retained auxiliary context.  Taking `Mask` and `Body` to be complete row-table function types
gives the manuscript's row-pair-table statement. -/
theorem translatedUniformPairView_evalDist_eq_independent
    {State Context Mask Body : Type}
    [AddGroup Mask] [Fintype Mask] [SampleableType Mask]
    [AddGroup Body] [Fintype Body] [SampleableType Body]
    (stateSampler : ProbComp State) (context : State → Context)
    (maskOffset : State → Mask) (bodyOffset : State → Body) :
    evalDist
        (translatedUniformPairView stateSampler context maskOffset bodyOffset) =
      evalDist
        (independentUniformPairView
          (Mask := Mask) (Body := Body) stateSampler context) := by
  unfold translatedUniformPairView independentUniformPairView
  refine evalDist_bind_congr' stateSampler fun state ↦ ?_
  calc
    _ = evalDist (do
        let mask ← $ᵗ Mask
        let body ← (fun fresh ↦ bodyOffset state + fresh) <$> ($ᵗ Body)
        return (context state, (mask, body))) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        (add_uniform_evalDist (maskOffset state)) _
    _ = _ := by
      refine evalDist_bind_congr' ($ᵗ Mask) fun mask ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        (add_uniform_evalDist (bodyOffset state)) _

/-- A canonical sanitized target is not automatically the native target.  A separate comparison
between those two laws is charged explicitly. -/
theorem tvDist_sanitized_native_le
    {View : Type} (actual canonical native : ProbComp View)
    (sanitizerDefect nativeComparisonDefect : ℝ)
    (hsanitizer : tvDist actual canonical ≤ sanitizerDefect)
    (hnative : tvDist canonical native ≤ nativeComparisonDefect) :
    tvDist actual native ≤ sanitizerDefect + nativeComparisonDefect :=
  (tvDist_triangle actual canonical native).trans
    (add_le_add hsanitizer hnative)

/-! ## Hash-candidate prediction -/

/-- Formal interface for encrypted hash-equality evaluation.  The selector target is indexed by
the actual key and the equality bit, and closeness is required for every key/candidate pair. -/
structure HashEqualityEvaluationCertificate
    (Key Digest Input Selector : Type) [DecidableEq Digest] where
  hash : Key → Digest
  input : Key → ProbComp Input
  evaluate : Digest → Input → ProbComp Selector
  canonicalSelector : Bool → Key → ProbComp Selector
  defect : ℝ
  close : ∀ key candidate,
    tvDist
        (input key >>= evaluate candidate)
        (canonicalSelector (decide (hash key = candidate)) key) ≤ defect

/-- Three-step correct-candidate hybrid: selector evaluation, CMUX evaluation, and joint
canonicalization are charged exactly once. -/
theorem correctHashCandidateView_le
    {View : Type}
    (transformed selectorCorrect evaluationCorrect canonical : ProbComp View)
    (equalityDefect evaluationDefect errorDefect : ℝ)
    (hequality : tvDist transformed selectorCorrect ≤ equalityDefect)
    (hevaluation : tvDist selectorCorrect evaluationCorrect ≤ evaluationDefect)
    (herror : tvDist evaluationCorrect canonical ≤ errorDefect) :
    tvDist transformed canonical ≤
      equalityDefect + evaluationDefect + errorDefect := by
  have hfirst := tvDist_triangle transformed selectorCorrect canonical
  have hsecond := tvDist_triangle selectorCorrect evaluationCorrect canonical
  linarith

/-- Wrong-candidate hybrid.  When the canonical fallback law is exactly the independent uniform
pair law, the same three implementation defects are the complete distance. -/
theorem wrongHashCandidateView_le
    {View : Type}
    (transformed selectorWrong evaluationWrong canonical uniform : ProbComp View)
    (equalityDefect evaluationDefect errorDefect : ℝ)
    (hequality : tvDist transformed selectorWrong ≤ equalityDefect)
    (hevaluation : tvDist selectorWrong evaluationWrong ≤ evaluationDefect)
    (herror : tvDist evaluationWrong canonical ≤ errorDefect)
    (huniform : evalDist canonical = evalDist uniform) :
    tvDist transformed uniform ≤
      equalityDefect + evaluationDefect + errorDefect := by
  have hcanonical : tvDist canonical uniform = 0 :=
    (tvDist_eq_zero_iff canonical uniform).2 huniform
  have hfirst := tvDist_triangle transformed selectorWrong uniform
  have hsecond := tvDist_triangle selectorWrong evaluationWrong uniform
  have hthird := tvDist_triangle evaluationWrong canonical uniform
  linarith

/-- Success probability of the candidate strategy: a uniformly chosen candidate is returned on
acceptance; on rejection, a uniformly chosen *different* digest is returned.  After averaging
over the true digest, this simplifies to `(1 + a - w)/M`. -/
def hashCandidatePredictionSuccess
    (digestCardinality correctAccept wrongAccept : ℝ) : ℝ :=
  (1 + correctAccept - wrongAccept) / digestCardinality

/-- Exact excess over the uniform-guess baseline. -/
theorem hashCandidatePredictionExcess_eq
    (digestCardinality correctAccept wrongAccept : ℝ) :
    hashCandidatePredictionSuccess digestCardinality correctAccept wrongAccept -
        1 / digestCardinality =
      (correctAccept - wrongAccept) / digestCardinality := by
  unfold hashCandidatePredictionSuccess
  ring

/-- Rearranged prediction inequality.  A distinguisher gap is at most the digest carrier times
the prediction excess, plus the hash/CMUX simulation defect. -/
theorem hashGap_le_card_mul_prediction
    (digestCardinality distinguisherGap predictionExcess simulationDefect : ℝ)
    (hgap : distinguisherGap - simulationDefect ≤
      digestCardinality * predictionExcess) :
    distinguisherGap ≤
      digestCardinality * predictionExcess + simulationDefect := by
  linarith

/-- Contextual match-and-square followed by candidate guessing. -/
theorem contextualHashCandidateGap_le
    (digestCardinality concentration distinguisherGap predictionExcess
      contextualAdvantage simulationDefect : ℝ)
    (hdigestCardinality : 0 ≤ digestCardinality)
    (hgap : distinguisherGap ≤
      digestCardinality * predictionExcess + simulationDefect)
    (hsecondMoment : predictionExcess ^ 2 ≤
      2 * concentration * contextualAdvantage) :
    distinguisherGap ≤
      digestCardinality *
        Real.sqrt (2 * concentration * contextualAdvantage) + simulationDefect := by
  have hprediction : predictionExcess ≤
      Real.sqrt (2 * concentration * contextualAdvantage) :=
    Real.le_sqrt_of_sq_le hsecondMoment
  exact hgap.trans (add_le_add
    (mul_le_mul_of_nonneg_left hprediction hdigestCardinality) le_rfl)

/-- Exact real coefficient for the uniform `r`-bit hash route, avoiding any rounding of the
half-integer exponent `(3r+1)/2`. -/
def binaryHashCMUXContextualLoss (digestCount : ℕ) : ℝ :=
  (2 : ℝ) ^ digestCount * Real.sqrt ((2 : ℝ) ^ (digestCount + 1))

theorem binaryHashCMUXContextualLoss_nonneg (digestCount : ℕ) :
    0 ≤ binaryHashCMUXContextualLoss digestCount := by
  exact mul_nonneg (pow_nonneg (by norm_num) _)
    (Real.sqrt_nonneg _)

/-- Squaring the coefficient recovers the exact integer exponent `3r+1`; this is the rigorous
real-number interpretation of `2^((3r+1)/2)`. -/
theorem binaryHashCMUXContextualLoss_sq (digestCount : ℕ) :
    binaryHashCMUXContextualLoss digestCount ^ 2 =
      (2 : ℝ) ^ (3 * digestCount + 1) := by
  unfold binaryHashCMUXContextualLoss
  rw [mul_pow, Real.sq_sqrt (by positivity)]
  rw [← pow_mul, ← pow_add]
  congr 1
  omega

/-- Uniform `r`-bit specialization of the contextual candidate route. -/
theorem uniformBinaryHashCandidateGap_le
    (digestCount : ℕ)
    (distinguisherGap predictionExcess contextualAdvantage simulationDefect : ℝ)
    (hgap : distinguisherGap ≤
      (2 : ℝ) ^ digestCount * predictionExcess + simulationDefect)
    (hsecondMoment : predictionExcess ^ 2 ≤
      2 * (2 : ℝ) ^ digestCount * contextualAdvantage) :
    distinguisherGap ≤
      binaryHashCMUXContextualLoss digestCount *
        Real.sqrt contextualAdvantage + simulationDefect := by
  have hbound := contextualHashCandidateGap_le
    ((2 : ℝ) ^ digestCount) ((2 : ℝ) ^ digestCount)
    distinguisherGap predictionExcess contextualAdvantage simulationDefect
    (by positivity) hgap hsecondMoment
  rw [Real.sqrt_mul (by positivity : 0 ≤ 2 * (2 : ℝ) ^ digestCount),
    show 2 * (2 : ℝ) ^ digestCount = (2 : ℝ) ^ (digestCount + 1) by
      rw [pow_succ]
      ring] at hbound
  simpa [binaryHashCMUXContextualLoss, mul_assoc] using hbound

/-! ### Game-level contextual hash leakage removal -/

/-- Game-level form of contextual hash leakage removal for an arbitrary digest distribution.
The fake digest must be the square-root tilt of the actual digest marginal. -/
theorem contextualHashLeakageRemoval
    {Key Digest : Type} [Fintype Key] [Fintype Digest]
    (keySampler : ProbComp Key) (fakeDigestSampler : ProbComp Digest)
    (digest : Key → Digest)
    (plus minus : Digest → Key → ProbComp Bool)
    (hcover : ∀ key, probabilityMass keySampler key ≠ 0 →
      probabilityMass fakeDigestSampler (digest key) ≠ 0)
    (hoptimized : ∀ value,
      probabilityMass fakeDigestSampler value =
        Real.sqrt (probabilityMass (leakageLaw keySampler digest) value) /
          halfRenyiNormalizer keySampler digest) :
    projectedAggregateAdvantage keySampler digest plus minus ≤
      Real.sqrt (2 * projectedLeakageConcentration keySampler digest *
        projectedMatchSquareAdvantage keySampler fakeDigestSampler plus minus) := by
  exact projectedAggregateAdvantage_le_sqrt_matchSquare
    keySampler fakeDigestSampler digest plus minus hcover hoptimized

/-- Balanced `r`-bit specialization of contextual hash leakage removal. -/
theorem uniformBinaryContextualHashLeakageRemoval
    {Prefix Suffix : Type}
    [Fintype Prefix] [SampleableType Prefix]
    [Fintype Suffix] [SampleableType Suffix]
    [Fintype (Prefix × Suffix)] [SampleableType (Prefix × Suffix)]
    (digestCount : ℕ)
    (hash : Prefix → (Fin digestCount → Bool))
    (huniformHash : HasUniformOutput hash)
    (fakeDigestSampler : ProbComp (Fin digestCount → Bool))
    (plus minus : (Fin digestCount → Bool) →
      Prefix × Suffix → ProbComp Bool)
    (hcover : ∀ key,
      probabilityMass ($ᵗ (Prefix × Suffix)) key ≠ 0 →
        probabilityMass fakeDigestSampler
          (hashedPrefixLeakage (Suffix := Suffix) hash key) ≠ 0)
    (hoptimized : ∀ digest,
      probabilityMass fakeDigestSampler digest =
        Real.sqrt
            (probabilityMass
              (leakageLaw ($ᵗ (Prefix × Suffix))
                (hashedPrefixLeakage (Suffix := Suffix) hash)) digest) /
          halfRenyiNormalizer
            ($ᵗ (Prefix × Suffix))
            (hashedPrefixLeakage (Suffix := Suffix) hash)) :
    projectedAggregateAdvantage
        ($ᵗ (Prefix × Suffix))
        (hashedPrefixLeakage (Suffix := Suffix) hash) plus minus ≤
      Real.sqrt ((2 : ℝ) ^ (digestCount + 1) *
        projectedMatchSquareAdvantage
          ($ᵗ (Prefix × Suffix)) fakeDigestSampler plus minus) := by
  have hbound := contextualHashLeakageRemoval
    ($ᵗ (Prefix × Suffix)) fakeDigestSampler
    (hashedPrefixLeakage (Suffix := Suffix) hash)
    plus minus hcover hoptimized
  rw [hashedBinaryPrefixConcentration_eq_twoPow
    digestCount hash huniformHash] at hbound
  simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using hbound

/-! ## Projected hidden-mode and final security composition -/

/-- The projected hidden-mode theorem from the manuscript.  This is the direct scalar interface
to the already checked complete-view match-and-square theorem. -/
theorem projectedHiddenModeGap_le
    (nativeGap lossyGap modeOne modeZero fidelityOne fidelityZero concentration
      realSecondMoment uniformSignedGap sourceAdvantage uniformGap samplerDefect : ℝ)
    (hmode : nativeGap ≤ modeOne + modeZero + lossyGap + samplerDefect)
    (hconcentration : 0 ≤ concentration)
    (hdiagonal : lossyGap ≤ fidelityOne + fidelityZero +
      Real.sqrt (concentration * realSecondMoment))
    (hsource : |realSecondMoment - uniformSignedGap ^ 2| ≤
      2 * sourceAdvantage)
    (herasure : |uniformSignedGap| ≤ uniformGap) :
    nativeGap ≤ modeOne + modeZero + fidelityOne + fidelityZero +
      Real.sqrt (concentration *
        (2 * sourceAdvantage + uniformGap ^ 2)) + samplerDefect := by
  exact hashLossyCompleteViewComposition_le
    nativeGap lossyGap modeOne modeZero fidelityOne fidelityZero concentration
    realSecondMoment uniformSignedGap sourceAdvantage uniformGap samplerDefect
    hmode hconcentration hdiagonal hsource herasure

/-- Direct projected-source route for a balanced `r`-bit digest with exact uniform-source
erasure.  Unlike candidate guessing, it has no additional factor `2^r`. -/
theorem directProjectedUniformBinaryGap_le
    {Prefix Suffix : Type}
    [Fintype Prefix] [SampleableType Prefix]
    [Fintype Suffix] [SampleableType Suffix]
    [Fintype (Prefix × Suffix)] [SampleableType (Prefix × Suffix)]
    (digestCount : ℕ) (hash : Prefix → (Fin digestCount → Bool))
    (huniformHash : HasUniformOutput hash)
    (lossyGap fidelityOne fidelityZero realSecondMoment sourceAdvantage : ℝ)
    (hdiagonal : lossyGap ≤ fidelityOne + fidelityZero +
      Real.sqrt
        (projectedLeakageConcentration
          ($ᵗ (Prefix × Suffix))
          (hashedPrefixLeakage (Suffix := Suffix) hash) * realSecondMoment))
    (hsource : |realSecondMoment| ≤ 2 * sourceAdvantage) :
    lossyGap ≤ fidelityOne + fidelityZero +
      Real.sqrt ((2 : ℝ) ^ (digestCount + 1) * sourceAdvantage) := by
  exact uniformBinaryDigestMatchSquareGap_le_of_exactErasure
    digestCount hash huniformHash lossyGap fidelityOne fidelityZero
    realSecondMoment sourceAdvantage hdiagonal hsource

/-- Final direct-projected route after adding the equality, sanitizer, and endpoint defects. -/
theorem directProjectedSanitizedSecurity_le
    {Prefix Suffix : Type}
    [Fintype Prefix] [SampleableType Prefix]
    [Fintype Suffix] [SampleableType Suffix]
    [Fintype (Prefix × Suffix)] [SampleableType (Prefix × Suffix)]
    (digestCount : ℕ) (hash : Prefix → (Fin digestCount → Bool))
    (huniformHash : HasUniformOutput hash)
    (securityGap lossyGap fidelityOne fidelityZero realSecondMoment
      projectedAdvantage equalityDefect sanitizerDefect endpointDefect : ℝ)
    (houter : securityGap ≤ lossyGap +
      equalityDefect + sanitizerDefect + endpointDefect)
    (hdiagonal : lossyGap ≤ fidelityOne + fidelityZero +
      Real.sqrt
        (projectedLeakageConcentration
          ($ᵗ (Prefix × Suffix))
          (hashedPrefixLeakage (Suffix := Suffix) hash) * realSecondMoment))
    (hsource : |realSecondMoment| ≤ 2 * projectedAdvantage) :
    securityGap ≤ fidelityOne + fidelityZero +
      Real.sqrt ((2 : ℝ) ^ (digestCount + 1) * projectedAdvantage) +
      equalityDefect + sanitizerDefect + endpointDefect := by
  have hlossy := directProjectedUniformBinaryGap_le
    digestCount hash huniformHash lossyGap fidelityOne fidelityZero
    realSecondMoment projectedAdvantage hdiagonal hsource
  linarith

/-- Final conditional security statement for the contextual hash-candidate route.  Equality
evaluation, complete-vector sanitization, and the terminal endpoint are each charged exactly
once. -/
theorem sanitizedSelfCircularSecurity_le
    (digestCount : ℕ)
    (securityGap predictionExcess contextualAdvantage
      equalityDefect cmuxSanitizerDefect endpointDefect : ℝ)
    (hgap : securityGap ≤
      (2 : ℝ) ^ digestCount * predictionExcess +
        (equalityDefect + cmuxSanitizerDefect + endpointDefect))
    (hsecondMoment : predictionExcess ^ 2 ≤
      2 * (2 : ℝ) ^ digestCount * contextualAdvantage) :
    securityGap ≤
      binaryHashCMUXContextualLoss digestCount *
        Real.sqrt contextualAdvantage +
      equalityDefect + cmuxSanitizerDefect + endpointDefect := by
  have hbound := uniformBinaryHashCandidateGap_le
    digestCount securityGap predictionExcess contextualAdvantage
    (equalityDefect + cmuxSanitizerDefect + endpointDefect)
    hgap hsecondMoment
  linarith

/-! ## Native nonce-row boundary -/

/-- Rewriting the displayed native nonce mask exposes the exact secret-product term. -/
theorem nativeNoncePhase_identity
    {R : Type} [Ring R] (mask hashWeight message secret error : R) :
    mask * secret + error -
        (mask + hashWeight * message) * secret =
      error - (hashWeight * message) * secret := by
  noncomm_ring

/-- When the encrypted hash selector depends on a secret-key message, the sanitizer theorem does
not itself turn the nonce row into an ordinary zero-row RLWE sample.  This predicate records the
additional source-to-complete-BRK premise without pretending to construct it. -/
structure SecretMessageSourceCompiler
    (SourceView CompleteBRK : Type) where
  compile : SourceView → CompleteBRK
  realSource : ProbComp SourceView
  uniformSource : ProbComp SourceView
  realTarget : ProbComp CompleteBRK
  uniformTarget : ProbComp CompleteBRK
  realDefect : ℝ
  uniformDefect : ℝ
  real_close : tvDist (compile <$> realSource) realTarget ≤ realDefect
  uniform_close : tvDist (compile <$> uniformSource) uniformTarget ≤ uniformDefect

end

end FormalProof4FHE.TFHE.Native.BlockCategoricalHashCMUXSelfCircular
