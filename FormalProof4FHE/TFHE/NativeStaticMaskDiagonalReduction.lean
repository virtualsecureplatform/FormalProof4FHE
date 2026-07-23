/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeAdaptiveMaskCollision
import FormalProof4FHE.TFHE.NativeAdaptiveOffDiagonalSecurity
import FormalProof4FHE.TFHE.NativeDiagonalPairCollisionNormalForm
import FormalProof4FHE.TFHE.NativeDiagonalRetainedFiberCokernel

/-!
# Selected-Diagonal Reduction for the Residual-Free Native TFHE Mask

After post-evaluation wide noise has erased the narrow residual, the remaining correct-branch
hybrid replaces only the complete public mask of the evaluated bootstrapping key.  At every
off-diagonal scalar coordinate, an independently uniform source mask is added to a perturbation;
therefore that output mask is an exact one-time pad even when the selected control is retained.
Only the selected coordinate reuses the control mask inside its own perturbation.

This module first proves the fixed-secret mask-only factorization.  It then connects the sole
selected-coordinate defect to the joint diagonal collision law without charging any
off-diagonal residual term.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery.AugmentedResidual.NativeShifted.FullMaskCollision.StaticDiagonal

noncomputable section

open FormalProof4FHE.TFHE
open Native
open Native.ShiftedCandidateEvaluator

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing

/-- A direct native TGSW entry exposes an exactly uniform public mask, independently of its
message, secret, and error sampler. -/
theorem directEntrySampler_mask_evalDist_eq_uniform
    {q degree ringRank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    evalDist
        (Prod.fst <$> OffDiagonalNormalForm.directEntrySampler params errorSampler
          hidden ringSecret coordinate) =
      evalDist
        ($ᵗ (DiagonalNormalForm.DiagonalChallenge
          q degree ringRank params.levels)) := by
  let Challenge : ProbComp
      (DiagonalNormalForm.DiagonalChallenge q degree ringRank params.levels) :=
    $ᵗ (DiagonalNormalForm.DiagonalChallenge q degree ringRank params.levels)
  let Errors := ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) errorSampler
  have h : evalDist (Challenge >>= fun challenge ↦
      Errors >>= fun _error ↦ pure challenge) = evalDist Challenge := by
    calc
      _ = evalDist (Challenge >>= fun challenge ↦ pure challenge) := by
        refine evalDist_bind_congr' Challenge fun challenge ↦ ?_
        exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
          Errors (by simp [Errors]) (pure challenge)
      _ = evalDist Challenge := by simp
  simpa only [OffDiagonalNormalForm.directEntrySampler, TGSW.directEncrypt,
    TLWE.batchEncrypt, TLWE.batchAssemble, Challenge, Errors,
    map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind] using h

/-- At an off-diagonal coordinate, residualization changes only the body law; its public mask is
still the same fresh uniform matrix as a direct entry. -/
theorem residualizedCoordinateSampler_mask_evalDist_eq_directEntry
    {q degree ringRank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate outputCoordinate : Fin lweDimension)
    (control : RingGSWCiphertext q (degree + 1) ringRank params.levels)
    (hne : outputCoordinate ≠ coordinate) :
    evalDist
        (Prod.fst <$>
          OffDiagonalNormalForm.residualizedCoordinateSampler params errorSampler
            hidden ringSecret coordinate control outputCoordinate) =
      evalDist
        (Prod.fst <$> OffDiagonalNormalForm.directEntrySampler params errorSampler
          hidden ringSecret outputCoordinate) := by
  let Difference : ProbComp
      (RingGSWCiphertext q (degree + 1) ringRank params.levels) :=
    $ᵗ (RingGSWCiphertext q (degree + 1) ringRank params.levels)
  let Challenge : ProbComp
      (DiagonalNormalForm.DiagonalChallenge q degree ringRank params.levels) :=
    $ᵗ (DiagonalNormalForm.DiagonalChallenge q degree ringRank params.levels)
  let Errors := ProbComp.sampleIID (TGSW.rowCount ringRank params.levels) errorSampler
  have h : evalDist (Difference >>= fun _difference ↦
      Challenge >>= fun challenge ↦ Errors >>= fun _error ↦ pure challenge) =
    evalDist (Challenge >>= fun challenge ↦ Errors >>= fun _error ↦ pure challenge) :=
    FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
      Difference (by simp [Difference])
        (Challenge >>= fun challenge ↦ Errors >>= fun _error ↦ pure challenge)
  simpa only [OffDiagonalNormalForm.residualizedCoordinateSampler, if_neg hne,
    OffDiagonalNormalForm.fixedControlPerturbationSampler,
    OffDiagonalNormalForm.directEntrySampler, TGSW.directEncryptWithResidual,
    TGSW.directEncrypt, TLWE.batchEncryptWithResidual, TLWE.batchEncrypt,
    TLWE.batchAssemble, Difference, Challenge, Errors,
    map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind] using h

/-- Mapping the residualized whole key to public masks makes every off-diagonal replacement
exact.  The selected coordinate is unchanged on both sides. -/
theorem residualizedKeyExperiment_mask_evalDist_eq_offDiagonalReplaced
    {q degree ringRank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    evalDist
        (Native.ConditionalSmudging.bootstrappingMask <$>
          OffDiagonalNormalForm.residualizedKeyExperiment params errorSampler
            hidden ringSecret coordinate) =
      evalDist
        (Native.ConditionalSmudging.bootstrappingMask <$>
          OffDiagonalNormalForm.offDiagonalReplacedKeyExperiment params errorSampler
            hidden ringSecret coordinate) := by
  let Control := OffDiagonalNormalForm.directEntrySampler params errorSampler
    hidden ringSecret coordinate
  let Residualized := fun
      (control : RingGSWCiphertext q (degree + 1) ringRank params.levels)
      (outputCoordinate : Fin lweDimension) ↦
    OffDiagonalNormalForm.residualizedCoordinateSampler params errorSampler
      hidden ringSecret coordinate control outputCoordinate
  let Replaced := fun
      (control : RingGSWCiphertext q (degree + 1) ringRank params.levels)
      (outputCoordinate : Fin lweDimension) ↦
    OffDiagonalNormalForm.offDiagonalReplacedCoordinateSampler params errorSampler
      hidden ringSecret coordinate control outputCoordinate
  simp only [OffDiagonalNormalForm.residualizedKeyExperiment,
    OffDiagonalNormalForm.offDiagonalReplacedKeyExperiment,
    map_eq_bind_pure_comp, bind_assoc]
  refine evalDist_bind_congr' Control fun control ↦ ?_
  have hmapped : evalDist
      ((fun values index ↦ (values index).1) <$>
        Fin.mOfFn lweDimension (Residualized control)) =
    evalDist
      ((fun values index ↦ (values index).1) <$>
        Fin.mOfFn lweDimension (Replaced control)) := by
    rw [FormalProof4FHE.FiniteProduct.map_fin_mOfFn lweDimension
      (Residualized control) (fun _ ciphertext ↦ ciphertext.1)]
    rw [FormalProof4FHE.FiniteProduct.map_fin_mOfFn lweDimension
      (Replaced control) (fun _ ciphertext ↦ ciphertext.1)]
    apply FormalProof4FHE.FiniteProduct.evalDist_fin_mOfFn_congr
    intro outputCoordinate
    by_cases hCoordinate : outputCoordinate = coordinate
    · subst outputCoordinate
      simp [Residualized, Replaced,
        OffDiagonalNormalForm.residualizedCoordinateSampler,
        OffDiagonalNormalForm.offDiagonalReplacedCoordinateSampler]
    · have h := residualizedCoordinateSampler_mask_evalDist_eq_directEntry
        params errorSampler hidden ringSecret coordinate outputCoordinate control hCoordinate
      simpa only [Residualized, Replaced,
        OffDiagonalNormalForm.offDiagonalReplacedCoordinateSampler,
        if_neg hCoordinate] using h
  unfold Native.ConditionalSmudging.bootstrappingMask
  simpa only [map_eq_bind_pure_comp, Function.comp_def, Residualized, Replaced] using hmapped

/-- The honest fixed-secret correct evaluator and the diagonal-isolated key have exactly the same
complete public-mask distribution. -/
theorem correctKeyExperiment_mask_evalDist_eq_offDiagonalReplaced
    {q degree ringRank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    evalDist
        (Native.ConditionalSmudging.bootstrappingMask <$>
          OffDiagonalNormalForm.correctKeyExperiment params errorSampler
            hidden ringSecret coordinate) =
      evalDist
        (Native.ConditionalSmudging.bootstrappingMask <$>
          OffDiagonalNormalForm.offDiagonalReplacedKeyExperiment params errorSampler
            hidden ringSecret coordinate) := by
  have hcorrect := OffDiagonalNormalForm.correctKeyExperiment_evalDist_eq_residualized
    params errorSampler hidden ringSecret coordinate
  exact (evalDist_map_eq_of_evalDist_eq hcorrect
      Native.ConditionalSmudging.bootstrappingMask).trans
    (residualizedKeyExperiment_mask_evalDist_eq_offDiagonalReplaced
      params errorSampler hidden ringSecret coordinate)

/-- Complete one supplied selected-coordinate mask with fresh independent uniform masks at all
other scalar-key coordinates. -/
noncomputable def completeMaskFromDiagonal
    {q degree ringRank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension)
    (diagonal : DiagonalNormalForm.DiagonalChallenge
      q degree ringRank params.levels) :
    ProbComp (Native.ConditionalSmudging.BootstrappingMask
      q (degree + 1) ringRank params.levels lweDimension) :=
  Fin.mOfFn lweDimension fun outputCoordinate ↦
    if outputCoordinate = coordinate then pure diagonal
    else $ᵗ (DiagonalNormalForm.DiagonalChallenge
      q degree ringRank params.levels)

/-- Public-mask projection commutes, in distribution, with completing a diagonal ciphertext by
fresh direct TGSW entries. -/
theorem completeKeyFromDiagonal_mask_evalDist_eq_completeMask
    {q degree ringRank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension)
    (diagonal : RingGSWCiphertext q (degree + 1) ringRank params.levels) :
    evalDist
        (Native.ConditionalSmudging.bootstrappingMask <$>
          OffDiagonalNormalForm.completeKeyFromDiagonal params errorSampler
            hidden ringSecret coordinate diagonal) =
      evalDist
        (completeMaskFromDiagonal params coordinate diagonal.1) := by
  unfold Native.ConditionalSmudging.bootstrappingMask
  unfold OffDiagonalNormalForm.completeKeyFromDiagonal completeMaskFromDiagonal
  rw [FormalProof4FHE.FiniteProduct.map_fin_mOfFn lweDimension
    (fun outputCoordinate ↦
      if outputCoordinate = coordinate then pure diagonal
      else OffDiagonalNormalForm.directEntrySampler params errorSampler
        hidden ringSecret outputCoordinate)
    (fun _ ciphertext ↦ ciphertext.1)]
  apply FormalProof4FHE.FiniteProduct.evalDist_fin_mOfFn_congr
  intro outputCoordinate
  by_cases hCoordinate : outputCoordinate = coordinate
  · simp [hCoordinate]
  · simpa only [hCoordinate, if_false] using
      (directEntrySampler_mask_evalDist_eq_uniform params errorSampler hidden
        ringSecret outputCoordinate)

/-- The complete residual-free evaluated mask is obtained by sampling the actual selected
diagonal mask and independently filling every other coordinate with a uniform mask. -/
theorem offDiagonalReplacedKeyExperiment_mask_evalDist_eq_diagonalCompletion
    {q degree ringRank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    evalDist
        (Native.ConditionalSmudging.bootstrappingMask <$>
          OffDiagonalNormalForm.offDiagonalReplacedKeyExperiment params errorSampler
            hidden ringSecret coordinate) =
      evalDist
        ((Prod.fst <$> OffDiagonalNormalForm.diagonalExperiment params errorSampler
            hidden ringSecret coordinate) >>=
          completeMaskFromDiagonal params coordinate) := by
  have hKey :=
    OffDiagonalNormalForm.offDiagonalReplacedKeyExperiment_evalDist_eq_diagonalCompletion
      params errorSampler hidden ringSecret coordinate
  have hMap := evalDist_map_eq_of_evalDist_eq hKey
    Native.ConditionalSmudging.bootstrappingMask
  calc
    _ = evalDist
        (Native.ConditionalSmudging.bootstrappingMask <$>
          (OffDiagonalNormalForm.diagonalExperiment params errorSampler
            hidden ringSecret coordinate >>=
          OffDiagonalNormalForm.completeKeyFromDiagonal params errorSampler
            hidden ringSecret coordinate)) := hMap
    _ = evalDist
        (OffDiagonalNormalForm.diagonalExperiment params errorSampler
            hidden ringSecret coordinate >>= fun diagonal ↦
          Native.ConditionalSmudging.bootstrappingMask <$>
            OffDiagonalNormalForm.completeKeyFromDiagonal params errorSampler
              hidden ringSecret coordinate diagonal) := by
      simp only [map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist
        (OffDiagonalNormalForm.diagonalExperiment params errorSampler
            hidden ringSecret coordinate >>= fun diagonal ↦
          completeMaskFromDiagonal params coordinate diagonal.1) := by
      refine evalDist_bind_congr'
        (OffDiagonalNormalForm.diagonalExperiment params errorSampler
          hidden ringSecret coordinate) fun diagonal ↦ ?_
      exact completeKeyFromDiagonal_mask_evalDist_eq_completeMask
        params errorSampler hidden ringSecret coordinate diagonal
    _ = _ := by
      simp only [map_eq_bind_pure_comp, bind_assoc, Function.comp_apply, pure_bind]

/-- Pulling the selected coordinate out of a fresh complete mask product preserves the exactly
uniform complete-mask distribution. -/
theorem uniform_diagonalCompletion_evalDist_eq_freshMask
    {q degree ringRank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) :
    evalDist
        (($ᵗ (DiagonalNormalForm.DiagonalChallenge
            q degree ringRank params.levels)) >>=
          completeMaskFromDiagonal params coordinate) =
      evalDist
        (Native.ConditionalSmudging.sampleFreshBootstrappingMask
          q (degree + 1) ringRank params.levels lweDimension) := by
  let Entry := fun _outputCoordinate : Fin lweDimension ↦
    $ᵗ (DiagonalNormalForm.DiagonalChallenge
      q degree ringRank params.levels)
  unfold completeMaskFromDiagonal
  unfold Native.ConditionalSmudging.sampleFreshBootstrappingMask
  simpa only [Entry] using
    (FormalProof4FHE.FiniteProduct.evalDist_pull_coordinate
      lweDimension Entry coordinate)

/-- The public mask of the mask-replaced selected-diagonal ciphertext is exactly uniform.  Its
fixed gadget translation is a permutation, and the independently mixed error is invisible to
mask projection. -/
theorem maskReplacedDiagonalExperiment_mask_evalDist_eq_uniform
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    evalDist
        (Prod.fst <$> DiagonalNormalForm.maskReplacedDiagonalExperiment
          (ringRank := ringRank) params sourceErrorSampler candidate ringSecret) =
      evalDist
        ($ᵗ (DiagonalNormalForm.DiagonalChallenge
          q degree ringRank params.levels)) := by
  let Challenge : ProbComp
      (DiagonalNormalForm.DiagonalChallenge q degree ringRank params.levels) :=
    $ᵗ (DiagonalNormalForm.DiagonalChallenge q degree ringRank params.levels)
  let Errors := DiagonalNormalForm.mixedDiagonalErrorSampler
    (ringRank := ringRank) params sourceErrorSampler candidate
  let Shift := TGSW.shiftChallenge (dimension := ringRank)
    (Gadget.Base.ringGadget params)
    (embedConstantBit q (degree + 1) candidate)
  have hDrop : evalDist (Challenge >>= fun challenge ↦
      Errors >>= fun _error ↦ pure (Shift challenge)) =
      evalDist (Shift <$> Challenge) := by
    calc
      _ = evalDist (Challenge >>= fun challenge ↦ pure (Shift challenge)) := by
        refine evalDist_bind_congr' Challenge fun challenge ↦ ?_
        exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
          Errors (by simp [Errors, DiagonalNormalForm.mixedDiagonalErrorSampler])
            (pure (Shift challenge))
      _ = _ := by simp only [map_eq_bind_pure_comp, Function.comp_def]
  have hUniform : evalDist (Shift <$> Challenge) = evalDist Challenge :=
    evalDist_map_bijective_uniform_cross
      (α := DiagonalNormalForm.DiagonalChallenge
        q degree ringRank params.levels)
      (β := DiagonalNormalForm.DiagonalChallenge
        q degree ringRank params.levels)
      (TGSW.shiftChallenge (dimension := ringRank)
        (Gadget.Base.ringGadget params)
        (embedConstantBit q (degree + 1) candidate))
      (TGSW.shiftChallenge_bijective (dimension := ringRank)
        (Gadget.Base.ringGadget params)
        (embedConstantBit q (degree + 1) candidate))
  calc
    _ = evalDist (Challenge >>= fun challenge ↦
        Errors >>= fun _error ↦ pure (Shift challenge)) := by
      simp only [DiagonalNormalForm.maskReplacedDiagonalExperiment,
        SamplerReplacement.independentPair, Challenge, Errors, Shift,
        map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind,
        TGSW.addGadget, TLWE.batchAssemble, TGSW.shiftChallenge]
    _ = evalDist (Shift <$> Challenge) := hDrop
    _ = _ := hUniform

/-- The selected public mask is close to uniform with exactly the existing joint diagonal
chi-square loss; projecting away the body cannot increase total variation. -/
theorem tvDist_diagonalExperiment_mask_uniform_le_jointChiSquare
    {q degree ringRank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    tvDist
        (Prod.fst <$> OffDiagonalNormalForm.diagonalExperiment params
          sourceErrorSampler hidden ringSecret coordinate)
        ($ᵗ (DiagonalNormalForm.DiagonalChallenge
          q degree ringRank params.levels)) ≤
      DiagonalNormalForm.averagedSourceErrorDiagonalChiSquareLoss
        (ringRank := ringRank) params sourceErrorSampler (hidden coordinate) := by
  have hDiagonal := DiagonalNormalForm.diagonalExperiment_evalDist_eq_operator
    params sourceErrorSampler hidden ringSecret coordinate
  have hDiagonalMask := evalDist_map_eq_of_evalDist_eq hDiagonal Prod.fst
  have hUniform := maskReplacedDiagonalExperiment_mask_evalDist_eq_uniform
    (ringRank := ringRank) params sourceErrorSampler (hidden coordinate) ringSecret
  have hFull := DiagonalNormalForm.tvDist_operatorDiagonal_maskReplaced_le_jointChiSquare
    (ringRank := ringRank) params sourceErrorSampler (hidden coordinate) ringSecret
  have hProjected := (tvDist_map_le (m := ProbComp) Prod.fst
    (DiagonalNormalForm.operatorDiagonalExperiment params sourceErrorSampler
      (hidden coordinate) ringSecret)
    (DiagonalNormalForm.maskReplacedDiagonalExperiment (ringRank := ringRank)
      params sourceErrorSampler (hidden coordinate) ringSecret)).trans hFull
  unfold tvDist at hProjected ⊢
  rw [← hDiagonalMask, hUniform] at hProjected
  exact hProjected

/-- Distribution-weighted selected-mask replacement.  Retained-fiber estimates are required
only on a caller-supplied good set of source errors; exceptional errors contribute exactly their
probability under the native source-error law. -/
theorem tvDist_diagonalExperiment_mask_uniform_le_goodBadRetainedCokernel
    {q degree ringRank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension)
    (Good : DiagonalNormalForm.DiagonalErrorVector
      q degree ringRank params.levels → Prop)
    (selfKernelAverageBound distinctCokernelAverageBound : ℝ)
    (hSelfNonneg : 0 ≤ selfKernelAverageBound)
    (hDistinctNonneg : 0 ≤ distinctCokernelAverageBound)
    (hSelf : ∀ sourceError ∈ support
      (ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
        sourceErrorSampler),
      Good sourceError →
        DiagonalNormalForm.fixedErrorDifferenceFiberKernelAverageBound
          params (hidden coordinate) sourceError selfKernelAverageBound)
    (hDistinct : ∀ sourceError ∈ support
      (ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
        sourceErrorSampler),
      Good sourceError →
        DiagonalNormalForm.fixedErrorDifferenceFiberDistinctCokernelAverageBound
          params (hidden coordinate) sourceError distinctCokernelAverageBound) :
    tvDist
        (Prod.fst <$> OffDiagonalNormalForm.diagonalExperiment params
          sourceErrorSampler hidden ringSecret coordinate)
        ($ᵗ (DiagonalNormalForm.DiagonalChallenge
          q degree ringRank params.levels)) ≤
      DiagonalNormalForm.retainedCokernelGoodErrorLossBound
          (degree := degree) (ringRank := ringRank) params
          selfKernelAverageBound distinctCokernelAverageBound +
        DiagonalNormalForm.sourceErrorBadProbability
          params sourceErrorSampler Good := by
  have hDiagonal := DiagonalNormalForm.diagonalExperiment_evalDist_eq_operator
    params sourceErrorSampler hidden ringSecret coordinate
  have hDiagonalMask := evalDist_map_eq_of_evalDist_eq hDiagonal Prod.fst
  have hUniform := maskReplacedDiagonalExperiment_mask_evalDist_eq_uniform
    (ringRank := ringRank) params sourceErrorSampler (hidden coordinate) ringSecret
  have hFull :=
    DiagonalNormalForm.tvDist_operatorDiagonal_maskReplaced_le_goodBadRetainedCokernel
      (ringRank := ringRank) params sourceErrorSampler (hidden coordinate) ringSecret Good
      selfKernelAverageBound distinctCokernelAverageBound hSelfNonneg hDistinctNonneg
      hSelf hDistinct
  have hProjected := (tvDist_map_le (m := ProbComp) Prod.fst
    (DiagonalNormalForm.operatorDiagonalExperiment params sourceErrorSampler
      (hidden coordinate) ringSecret)
    (DiagonalNormalForm.maskReplacedDiagonalExperiment (ringRank := ringRank)
      params sourceErrorSampler (hidden coordinate) ringSecret)).trans hFull
  unfold tvDist at hProjected ⊢
  rw [← hDiagonalMask, hUniform] at hProjected
  exact hProjected

/-- Fixed-secret whole-mask reduction: after residual erasure, the complete native evaluated
mask differs from a fresh direct mask only through the selected diagonal chi-square loss. -/
theorem tvDist_correctKeyExperiment_mask_fresh_le_jointChiSquare
    {q degree ringRank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    tvDist
        (Native.ConditionalSmudging.bootstrappingMask <$>
          OffDiagonalNormalForm.correctKeyExperiment params sourceErrorSampler
            hidden ringSecret coordinate)
        (Native.ConditionalSmudging.sampleFreshBootstrappingMask
          q (degree + 1) ringRank params.levels lweDimension) ≤
      DiagonalNormalForm.averagedSourceErrorDiagonalChiSquareLoss
        (ringRank := ringRank) params sourceErrorSampler (hidden coordinate) := by
  have hCorrect := correctKeyExperiment_mask_evalDist_eq_offDiagonalReplaced
    params sourceErrorSampler hidden ringSecret coordinate
  have hCompletion :=
    offDiagonalReplacedKeyExperiment_mask_evalDist_eq_diagonalCompletion
      params sourceErrorSampler hidden ringSecret coordinate
  have hActual := hCorrect.trans hCompletion
  have hFresh := uniform_diagonalCompletion_evalDist_eq_freshMask
    (degree := degree) (ringRank := ringRank) params coordinate
  have hDiagonal := tvDist_diagonalExperiment_mask_uniform_le_jointChiSquare
    params sourceErrorSampler hidden ringSecret coordinate
  have hProcessed := (tvDist_bind_right_le (m := ProbComp)
    (completeMaskFromDiagonal params coordinate)
    (Prod.fst <$> OffDiagonalNormalForm.diagonalExperiment params
      sourceErrorSampler hidden ringSecret coordinate)
    ($ᵗ (DiagonalNormalForm.DiagonalChallenge
      q degree ringRank params.levels))).trans hDiagonal
  unfold tvDist at hProcessed ⊢
  rw [← hActual, hFresh] at hProcessed
  exact hProcessed

/-- Complete-mask form of the distribution-weighted selected-diagonal theorem.  All
off-diagonal scalar coordinates remain exact one-time pads, so the complete evaluated
bootstrapping mask pays only the selected good-error loss and the bad-error probability. -/
theorem tvDist_correctKeyExperiment_mask_fresh_le_goodBadRetainedCokernel
    {q degree ringRank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension)
    (Good : DiagonalNormalForm.DiagonalErrorVector
      q degree ringRank params.levels → Prop)
    (selfKernelAverageBound distinctCokernelAverageBound : ℝ)
    (hSelfNonneg : 0 ≤ selfKernelAverageBound)
    (hDistinctNonneg : 0 ≤ distinctCokernelAverageBound)
    (hSelf : ∀ sourceError ∈ support
      (ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
        sourceErrorSampler),
      Good sourceError →
        DiagonalNormalForm.fixedErrorDifferenceFiberKernelAverageBound
          params (hidden coordinate) sourceError selfKernelAverageBound)
    (hDistinct : ∀ sourceError ∈ support
      (ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
        sourceErrorSampler),
      Good sourceError →
        DiagonalNormalForm.fixedErrorDifferenceFiberDistinctCokernelAverageBound
          params (hidden coordinate) sourceError distinctCokernelAverageBound) :
    tvDist
        (Native.ConditionalSmudging.bootstrappingMask <$>
          OffDiagonalNormalForm.correctKeyExperiment params sourceErrorSampler
            hidden ringSecret coordinate)
        (Native.ConditionalSmudging.sampleFreshBootstrappingMask
          q (degree + 1) ringRank params.levels lweDimension) ≤
      DiagonalNormalForm.retainedCokernelGoodErrorLossBound
          (degree := degree) (ringRank := ringRank) params
          selfKernelAverageBound distinctCokernelAverageBound +
        DiagonalNormalForm.sourceErrorBadProbability
          params sourceErrorSampler Good := by
  have hCorrect := correctKeyExperiment_mask_evalDist_eq_offDiagonalReplaced
    params sourceErrorSampler hidden ringSecret coordinate
  have hCompletion :=
    offDiagonalReplacedKeyExperiment_mask_evalDist_eq_diagonalCompletion
      params sourceErrorSampler hidden ringSecret coordinate
  have hActual := hCorrect.trans hCompletion
  have hFresh := uniform_diagonalCompletion_evalDist_eq_freshMask
    (degree := degree) (ringRank := ringRank) params coordinate
  have hDiagonal :=
    tvDist_diagonalExperiment_mask_uniform_le_goodBadRetainedCokernel
      params sourceErrorSampler hidden ringSecret coordinate Good
      selfKernelAverageBound distinctCokernelAverageBound hSelfNonneg hDistinctNonneg
      hSelf hDistinct
  have hProcessed := (tvDist_bind_right_le (m := ProbComp)
    (completeMaskFromDiagonal params coordinate)
    (Prod.fst <$> OffDiagonalNormalForm.diagonalExperiment params
      sourceErrorSampler hidden ringSecret coordinate)
    ($ᵗ (DiagonalNormalForm.DiagonalChallenge
      q degree ringRank params.levels))).trans hDiagonal
  unfold tvDist at hProcessed ⊢
  rw [← hActual, hFresh] at hProcessed
  exact hProcessed

/-- Reusable distribution-weighted retained-cokernel certificate for both possible selected
secret bits.  A single good predicate is sufficient; callers may take the intersection of
candidate-specific predicates and bound its failure by a union bound. -/
structure RetainedCokernelGoodBadCertificate
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1))) where
  Good : DiagonalNormalForm.DiagonalErrorVector
    q degree ringRank params.levels → Prop
  selfKernelAverageBound : ℝ
  distinctCokernelAverageBound : ℝ
  selfKernelAverageBound_nonneg : 0 ≤ selfKernelAverageBound
  distinctCokernelAverageBound_nonneg : 0 ≤ distinctCokernelAverageBound
  self : ∀ candidate sourceError,
    sourceError ∈ support
        (ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
          sourceErrorSampler) →
      Good sourceError →
      DiagonalNormalForm.fixedErrorDifferenceFiberKernelAverageBound
        params candidate sourceError selfKernelAverageBound
  distinct : ∀ candidate sourceError,
    sourceError ∈ support
        (ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
          sourceErrorSampler) →
      Good sourceError →
      DiagonalNormalForm.fixedErrorDifferenceFiberDistinctCokernelAverageBound
        params candidate sourceError distinctCokernelAverageBound

/-- Exact statistical budget represented by a distribution-weighted retained-cokernel
certificate. -/
noncomputable def RetainedCokernelGoodBadCertificate.lossBound
    {q degree ringRank : ℕ} [NeZero q]
    {params : Gadget.Base.Parameters q}
    {sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1))}
    (certificate : RetainedCokernelGoodBadCertificate
      (ringRank := ringRank) params sourceErrorSampler) : ℝ :=
  DiagonalNormalForm.retainedCokernelGoodErrorLossBound
      (degree := degree) (ringRank := ringRank) params
      certificate.selfKernelAverageBound certificate.distinctCokernelAverageBound +
    DiagonalNormalForm.sourceErrorBadProbability
      params sourceErrorSampler certificate.Good

theorem RetainedCokernelGoodBadCertificate.lossBound_nonneg
    {q degree ringRank : ℕ} [NeZero q]
    {params : Gadget.Base.Parameters q}
    {sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1))}
    (certificate : RetainedCokernelGoodBadCertificate
      (ringRank := ringRank) params sourceErrorSampler) :
    0 ≤ certificate.lossBound :=
  add_nonneg
    (DiagonalNormalForm.retainedCokernelGoodErrorLossBound_nonneg
      (degree := degree) params certificate.selfKernelAverageBound
        certificate.distinctCokernelAverageBound)
    (DiagonalNormalForm.sourceErrorBadProbability_nonneg
      params sourceErrorSampler certificate.Good)

/-- A packaged retained-cokernel certificate bounds the complete evaluated bootstrapping mask
for every fixed native key pair and selected coordinate. -/
theorem RetainedCokernelGoodBadCertificate.tvDist_correctKeyExperiment_mask_fresh_le
    {q degree ringRank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (certificate : RetainedCokernelGoodBadCertificate
      (ringRank := ringRank) params sourceErrorSampler)
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    tvDist
        (Native.ConditionalSmudging.bootstrappingMask <$>
          OffDiagonalNormalForm.correctKeyExperiment params sourceErrorSampler
            hidden ringSecret coordinate)
        (Native.ConditionalSmudging.sampleFreshBootstrappingMask
          q (degree + 1) ringRank params.levels lweDimension) ≤
      certificate.lossBound := by
  exact tvDist_correctKeyExperiment_mask_fresh_le_goodBadRetainedCokernel
    params sourceErrorSampler hidden ringSecret coordinate certificate.Good
    certificate.selfKernelAverageBound certificate.distinctCokernelAverageBound
    certificate.selfKernelAverageBound_nonneg
    certificate.distinctCokernelAverageBound_nonneg
    (certificate.self (hidden coordinate))
    (certificate.distinct (hidden coordinate))

/-- Candidate-independent mask-only diagonal chi-square budget. -/
noncomputable def worstCaseStaticMaskDiagonalChiSquareLoss
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1))) : ℝ :=
  max
    (DiagonalNormalForm.averagedSourceErrorDiagonalChiSquareLoss
      (ringRank := ringRank) params sourceErrorSampler false)
    (DiagonalNormalForm.averagedSourceErrorDiagonalChiSquareLoss
      (ringRank := ringRank) params sourceErrorSampler true)

theorem averagedSourceErrorDiagonalChiSquareLoss_le_worstCaseStatic
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (candidate : Bool) :
    DiagonalNormalForm.averagedSourceErrorDiagonalChiSquareLoss
        (ringRank := ringRank) params sourceErrorSampler candidate ≤
      worstCaseStaticMaskDiagonalChiSquareLoss
        (ringRank := ringRank) params sourceErrorSampler := by
  cases candidate
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem worstCaseStaticMaskDiagonalChiSquareLoss_nonneg
    {q degree ringRank : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1))) :
    0 ≤ worstCaseStaticMaskDiagonalChiSquareLoss
      (ringRank := ringRank) params sourceErrorSampler :=
  (DiagonalNormalForm.averagedSourceErrorDiagonalChiSquareLoss_nonneg
    (ringRank := ringRank) params sourceErrorSampler false).trans (le_max_left _ _)

/-- Candidate-independent fixed-secret whole-mask reduction. -/
theorem tvDist_correctKeyExperiment_mask_fresh_le_worstCaseStatic
    {q degree ringRank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hidden : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coordinate : Fin lweDimension) :
    tvDist
        (Native.ConditionalSmudging.bootstrappingMask <$>
          OffDiagonalNormalForm.correctKeyExperiment params sourceErrorSampler
            hidden ringSecret coordinate)
        (Native.ConditionalSmudging.sampleFreshBootstrappingMask
          q (degree + 1) ringRank params.levels lweDimension) ≤
      worstCaseStaticMaskDiagonalChiSquareLoss
        (ringRank := ringRank) params sourceErrorSampler :=
  (tvDist_correctKeyExperiment_mask_fresh_le_jointChiSquare
    params sourceErrorSampler hidden ringSecret coordinate).trans
    (averagedSourceErrorDiagonalChiSquareLoss_le_worstCaseStatic
      params sourceErrorSampler (hidden coordinate))

/-! ## Adaptive static-side lift -/

/-- Fully expanded latent static-mask experiment before replacing the uniform true branch by an
independent difference. -/
noncomputable def expandedCorrectStaticMaskTrueBranchExperiment
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    ProbComp
      (CorrectStaticMaskSide q (degree + 1) ringRank lweDimension
          keySwitchLevels queryCount ×
        Native.ConditionalSmudging.BootstrappingMask
          q (degree + 1) ringRank params.levels lweDimension) := do
  let secrets ← KeySwitchFirstFiniteView.secretSampler
    lweDimension ringRank (degree + 1)
  let sourceKey ← Native.BootstrapSecurity.MonomialKDM.generateBootstrappingKey
    q (degree + 1) ringRank params.levels lweDimension
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
    (Gadget.Base.ringGadget params) secrets.1 secrets.2
  let auxiliary ← sourceAuxiliarySampler (queryCount := queryCount)
    keySwitchErrorSampler inputErrorSampler keySwitchGadget secrets.1 secrets.2
  let mask ← $ᵗ BinarySecret lweDimension
  let trueBranch ←
    $ᵗ Native.BootstrappingKey q (degree + 1) ringRank
      params.levels lweDimension
  let transportedSource := Native.ScalarSecretRandomization.transformBootstrappingKey
    (Gadget.Base.ringGadget params) mask sourceKey
  let targetSecret := Native.ScalarSecretRandomization.maskedSecret secrets.1 mask
  let bootstrappingKey := Native.ShiftedCandidateEvaluator.selectBootstrappingKey
    params coordinate (targetSecret coordinate) transportedSource trueBranch
  return ((targetSecret, secrets.2, transportSourceAuxiliary mask auxiliary),
    Native.ConditionalSmudging.bootstrappingMask bootstrappingKey)

/-- The same expanded static-mask law under the independent-difference parametrization. -/
noncomputable def expandedCorrectStaticMaskDifferenceExperiment
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    ProbComp
      (CorrectStaticMaskSide q (degree + 1) ringRank lweDimension
          keySwitchLevels queryCount ×
        Native.ConditionalSmudging.BootstrappingMask
          q (degree + 1) ringRank params.levels lweDimension) := do
  let secrets ← KeySwitchFirstFiniteView.secretSampler
    lweDimension ringRank (degree + 1)
  let sourceKey ← Native.BootstrapSecurity.MonomialKDM.generateBootstrappingKey
    q (degree + 1) ringRank params.levels lweDimension
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
    (Gadget.Base.ringGadget params) secrets.1 secrets.2
  let auxiliary ← sourceAuxiliarySampler (queryCount := queryCount)
    keySwitchErrorSampler inputErrorSampler keySwitchGadget secrets.1 secrets.2
  let mask ← $ᵗ BinarySecret lweDimension
  let difference ←
    $ᵗ Native.BootstrappingKey q (degree + 1) ringRank
      params.levels lweDimension
  let transportedSource := Native.ScalarSecretRandomization.transformBootstrappingKey
    (Gadget.Base.ringGadget params) mask sourceKey
  let targetSecret := Native.ScalarSecretRandomization.maskedSecret secrets.1 mask
  let bootstrappingKey := Native.ShiftedCandidateEvaluator.selectBootstrappingKey
    params coordinate (targetSecret coordinate) transportedSource
    (Native.ShiftedCandidateEvaluator.addDifference transportedSource difference)
  return ((targetSecret, secrets.2, transportSourceAuxiliary mask auxiliary),
    Native.ConditionalSmudging.bootstrappingMask bootstrappingKey)

/-- Fixed-secret direct normal form of the complete adaptive static-mask joint law. -/
noncomputable def coupledDirectCorrectStaticMaskExperiment
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    ProbComp
      (CorrectStaticMaskSide q (degree + 1) ringRank lweDimension
          keySwitchLevels queryCount ×
        Native.ConditionalSmudging.BootstrappingMask
          q (degree + 1) ringRank params.levels lweDimension) := do
  let secrets ← KeySwitchFirstFiniteView.secretSampler
    lweDimension ringRank (degree + 1)
  let auxiliary ← sourceAuxiliarySampler (queryCount := queryCount)
    keySwitchErrorSampler inputErrorSampler keySwitchGadget secrets.1 secrets.2
  let mask ← $ᵗ BinarySecret lweDimension
  let targetSecret := Native.ScalarSecretRandomization.maskedSecret secrets.1 mask
  let bootstrappingKey ← OffDiagonalNormalForm.correctKeyExperiment params
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
    targetSecret secrets.2 coordinate
  return ((targetSecret, secrets.2, transportSourceAuxiliary mask auxiliary),
    Native.ConditionalSmudging.bootstrappingMask bootstrappingKey)

/-- Unfolding the paired source and static projection yields the explicit true-branch law. -/
theorem correctStaticMaskJointExperiment_evalDist_eq_expandedTrueBranch
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    evalDist
        (correctStaticMaskJointExperiment (degree := degree + 1)
          (ringRank := ringRank) (queryCount := queryCount) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) =
      evalDist
        (expandedCorrectStaticMaskTrueBranchExperiment
          (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
          (eta := eta) params keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate) := by
  simp [correctStaticMaskJointExperiment, correctMaskJointExperiment,
    correctStaticMaskSideOfCorrectMaskSide, correctMaskSide,
    correctEvaluatedMask, expandedCorrectStaticMaskTrueBranchExperiment,
    pairedSource, sampleCoin, transformWithCoin, transportedView,
    sourceAuxiliarySampler, transportSourceAuxiliary,
    problem, LWE.AuxiliaryInput.Search.exactRecoveryProblem,
    KeySwitchFirstFiniteView.augmentedCircularProblem,
    KeySwitchFirstFiniteView.secretSampler, ScalarTransport.transformView,
    Native.ScalarSecretRandomization.transformEvaluationKeyPair,
    Native.ScalarSecretRandomization.maskedSecret, transportCandidate,
    monad_norm]

/-- Translating the uniform true branch by the fixed transported source exposes an independent
uniform BRK difference without changing the retained static side or evaluated mask. -/
theorem expandedCorrectStaticMaskTrueBranch_evalDist_eq_difference
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    evalDist
        (expandedCorrectStaticMaskTrueBranchExperiment
          (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
          (eta := eta) params keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate) =
      evalDist
        (expandedCorrectStaticMaskDifferenceExperiment
          (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
          (eta := eta) params keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate) := by
  let Secrets := KeySwitchFirstFiniteView.secretSampler
    lweDimension ringRank (degree + 1)
  let Source := fun secrets : Secret lweDimension ringRank (degree + 1) ↦
    Native.BootstrapSecurity.MonomialKDM.generateBootstrappingKey
      q (degree + 1) ringRank params.levels lweDimension
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      (Gadget.Base.ringGadget params) secrets.1 secrets.2
  let Aux := fun secrets : Secret lweDimension ringRank (degree + 1) ↦
    sourceAuxiliarySampler (queryCount := queryCount)
      keySwitchErrorSampler inputErrorSampler keySwitchGadget secrets.1 secrets.2
  let Masks := $ᵗ BinarySecret lweDimension
  let Branches :=
    $ᵗ Native.BootstrappingKey q (degree + 1) ringRank
      params.levels lweDimension
  unfold expandedCorrectStaticMaskTrueBranchExperiment
    expandedCorrectStaticMaskDifferenceExperiment
  change evalDist (Secrets >>= fun secrets ↦
      Source secrets >>= fun sourceKey ↦
      Aux secrets >>= fun auxiliary ↦
      Masks >>= fun mask ↦
      Branches >>= fun trueBranch ↦
      pure ((Native.ScalarSecretRandomization.maskedSecret secrets.1 mask,
          secrets.2, transportSourceAuxiliary mask auxiliary),
        Native.ConditionalSmudging.bootstrappingMask
          (Native.ShiftedCandidateEvaluator.selectBootstrappingKey params coordinate
            ((Native.ScalarSecretRandomization.maskedSecret secrets.1 mask) coordinate)
            (Native.ScalarSecretRandomization.transformBootstrappingKey
              (Gadget.Base.ringGadget params) mask sourceKey)
            trueBranch))) =
    evalDist (Secrets >>= fun secrets ↦
      Source secrets >>= fun sourceKey ↦
      Aux secrets >>= fun auxiliary ↦
      Masks >>= fun mask ↦
      Branches >>= fun difference ↦
      pure ((Native.ScalarSecretRandomization.maskedSecret secrets.1 mask,
          secrets.2, transportSourceAuxiliary mask auxiliary),
        Native.ConditionalSmudging.bootstrappingMask
          (Native.ShiftedCandidateEvaluator.selectBootstrappingKey params coordinate
            ((Native.ScalarSecretRandomization.maskedSecret secrets.1 mask) coordinate)
            (Native.ScalarSecretRandomization.transformBootstrappingKey
              (Gadget.Base.ringGadget params) mask sourceKey)
            (Native.ShiftedCandidateEvaluator.addDifference
              (Native.ScalarSecretRandomization.transformBootstrappingKey
                (Gadget.Base.ringGadget params) mask sourceKey)
              difference))))
  refine evalDist_bind_congr' Secrets fun secrets ↦ ?_
  refine evalDist_bind_congr' (Source secrets) fun sourceKey ↦ ?_
  refine evalDist_bind_congr' (Aux secrets) fun auxiliary ↦ ?_
  refine evalDist_bind_congr' Masks fun mask ↦ ?_
  let Transported := Native.ScalarSecretRandomization.transformBootstrappingKey
    (Gadget.Base.ringGadget params) mask sourceKey
  let Finish := fun trueBranch : Native.BootstrappingKey q (degree + 1)
      ringRank params.levels lweDimension ↦
    ((Native.ScalarSecretRandomization.maskedSecret secrets.1 mask,
        secrets.2, transportSourceAuxiliary mask auxiliary),
      Native.ConditionalSmudging.bootstrappingMask
        (Native.ShiftedCandidateEvaluator.selectBootstrappingKey params coordinate
          ((Native.ScalarSecretRandomization.maskedSecret secrets.1 mask) coordinate)
          Transported trueBranch))
  have h := evalDist_map_eq_of_evalDist_eq
    (Native.ShiftedCandidateEvaluator.addDifference_uniform_evalDist Transported)
    Finish
  simpa only [Transported, Finish, map_eq_bind_pure_comp, Function.comp_def,
    bind_assoc, pure_bind] using h.symm

/-- Commuting the independent source components and transporting the centered-binomial source
BRK identifies the expanded difference law with the fixed-secret direct experiment. -/
theorem expandedCorrectStaticMaskDifference_evalDist_eq_coupledDirect
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    evalDist
        (expandedCorrectStaticMaskDifferenceExperiment
          (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
          (eta := eta) params keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate) =
      evalDist
        (coupledDirectCorrectStaticMaskExperiment
          (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
          (eta := eta) params keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate) := by
  let Secrets := KeySwitchFirstFiniteView.secretSampler
    lweDimension ringRank (degree + 1)
  let Gadget : Fin params.levels → RLWE.Rq q (degree + 1) :=
    Gadget.Base.ringGadget params
  let Source := fun secrets : Secret lweDimension ringRank (degree + 1) ↦
    Native.BootstrapSecurity.MonomialKDM.generateBootstrappingKey
      q (degree + 1) ringRank params.levels lweDimension
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      Gadget secrets.1 secrets.2
  let DirectSource := fun secrets : Secret lweDimension ringRank (degree + 1) ↦
    Native.BootstrapSecurity.generateDirectBootstrappingKey
      q (degree + 1) ringRank params.levels lweDimension
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      Gadget secrets.1 secrets.2
  let Aux := fun secrets : Secret lweDimension ringRank (degree + 1) ↦
    sourceAuxiliarySampler (queryCount := queryCount)
      keySwitchErrorSampler inputErrorSampler keySwitchGadget secrets.1 secrets.2
  let Masks := $ᵗ BinarySecret lweDimension
  let Difference :=
    $ᵗ Native.BootstrappingKey q (degree + 1) ringRank
      params.levels lweDimension
  let Transform := fun mask : BinarySecret lweDimension ↦
    Native.ScalarSecretRandomization.transformBootstrappingKey
      (dimension := ringRank) Gadget mask
  let TargetSecret := fun (secrets : Secret lweDimension ringRank (degree + 1))
      (mask : BinarySecret lweDimension) ↦
    Native.ScalarSecretRandomization.maskedSecret secrets.1 mask
  let Target := fun (secrets : Secret lweDimension ringRank (degree + 1))
      (mask : BinarySecret lweDimension) ↦
    Native.BootstrapSecurity.generateDirectBootstrappingKey
      q (degree + 1) ringRank params.levels lweDimension
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      Gadget (TargetSecret secrets mask) secrets.2
  let Finish := fun (secrets : Secret lweDimension ringRank (degree + 1))
      (auxiliary : Auxiliary q ringRank (degree + 1) lweDimension
        keySwitchLevels queryCount)
      (mask : BinarySecret lweDimension)
      (sourceKey difference : Native.BootstrappingKey q (degree + 1) ringRank
        params.levels lweDimension) ↦
    (pure ((TargetSecret secrets mask, secrets.2,
          transportSourceAuxiliary mask auxiliary),
        Native.ConditionalSmudging.bootstrappingMask
          (Native.ShiftedCandidateEvaluator.selectBootstrappingKey
            params coordinate ((TargetSecret secrets mask) coordinate) sourceKey
            (Native.ShiftedCandidateEvaluator.addDifference sourceKey difference))) :
      ProbComp
        (CorrectStaticMaskSide q (degree + 1) ringRank lweDimension
            keySwitchLevels queryCount ×
          Native.ConditionalSmudging.BootstrappingMask
            q (degree + 1) ringRank params.levels lweDimension))
  unfold expandedCorrectStaticMaskDifferenceExperiment
    coupledDirectCorrectStaticMaskExperiment
  simp only [OffDiagonalNormalForm.correctKeyExperiment, bind_assoc, pure_bind]
  change evalDist (Secrets >>= fun secrets ↦
      Source secrets >>= fun sourceKey ↦
      Aux secrets >>= fun auxiliary ↦
      Masks >>= fun mask ↦
      Difference >>= fun difference ↦
      Finish secrets auxiliary mask (Transform mask sourceKey) difference) =
    evalDist (Secrets >>= fun secrets ↦
      Aux secrets >>= fun auxiliary ↦
      Masks >>= fun mask ↦
      Target secrets mask >>= fun sourceKey ↦
      Difference >>= fun difference ↦
      Finish secrets auxiliary mask sourceKey difference)
  calc
    _ = evalDist (Secrets >>= fun secrets ↦
        Aux secrets >>= fun auxiliary ↦
        Source secrets >>= fun sourceKey ↦
        Masks >>= fun mask ↦
        Difference >>= fun difference ↦
        Finish secrets auxiliary mask (Transform mask sourceKey) difference) := by
      refine evalDist_bind_congr' Secrets fun secrets ↦ ?_
      exact evalDist_bind_bind_swap (Source secrets) (Aux secrets) _
    _ = evalDist (Secrets >>= fun secrets ↦
        Aux secrets >>= fun auxiliary ↦
        Masks >>= fun mask ↦
        Source secrets >>= fun sourceKey ↦
        Difference >>= fun difference ↦
        Finish secrets auxiliary mask (Transform mask sourceKey) difference) := by
      refine evalDist_bind_congr' Secrets fun secrets ↦ ?_
      refine evalDist_bind_congr' (Aux secrets) fun auxiliary ↦ ?_
      exact evalDist_bind_bind_swap (Source secrets) Masks _
    _ = _ := by
      refine evalDist_bind_congr' Secrets fun secrets ↦ ?_
      refine evalDist_bind_congr' (Aux secrets) fun auxiliary ↦ ?_
      refine evalDist_bind_congr' Masks fun mask ↦ ?_
      have hSource : Source secrets = DirectSource secrets :=
        Native.BootstrapSecurity.MonomialKDM.generateBootstrappingKey_eq_direct
          q (degree + 1) ringRank params.levels lweDimension
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          Gadget secrets.1 secrets.2
      have hTransport : evalDist (Transform mask <$> DirectSource secrets) =
          evalDist (Target secrets mask) := by
        simpa only [Transform, DirectSource, Target, TargetSecret] using
          (transformDirectBootstrappingKey_centeredBinomial_evalDist
            (degree := degree) params secrets.1 mask secrets.2)
      let continuation := fun sourceKey : Native.BootstrappingKey q (degree + 1)
          ringRank params.levels lweDimension ↦
        Difference >>= fun difference ↦
          Finish secrets auxiliary mask sourceKey difference
      have hBind := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        hTransport continuation
      rw [hSource]
      simpa only [continuation, map_eq_bind_pure_comp, Function.comp_def,
        bind_assoc, pure_bind] using hBind

/-- Exact adaptive identification of the residual-free static mask joint law with its nested
fixed-secret direct normal form. -/
theorem correctStaticMaskJointExperiment_evalDist_eq_coupledDirect
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    evalDist
        (correctStaticMaskJointExperiment (degree := degree + 1)
          (ringRank := ringRank) (queryCount := queryCount) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) =
      evalDist
        (coupledDirectCorrectStaticMaskExperiment
          (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
          (eta := eta) params keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate) :=
  (correctStaticMaskJointExperiment_evalDist_eq_expandedTrueBranch
    (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
    (eta := eta) params keySwitchErrorSampler inputErrorSampler
    keySwitchGadget coordinate).trans
  ((expandedCorrectStaticMaskTrueBranch_evalDist_eq_difference
    (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
    (eta := eta) params keySwitchErrorSampler inputErrorSampler
    keySwitchGadget coordinate).trans
  (expandedCorrectStaticMaskDifference_evalDist_eq_coupledDirect
    (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
    (eta := eta) params keySwitchErrorSampler inputErrorSampler
    keySwitchGadget coordinate))

/-- The corresponding direct comparison samples a completely fresh native mask while retaining
the same transformed static side. -/
noncomputable def coupledDirectFreshStaticMaskExperiment
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    ProbComp
      (CorrectStaticMaskSide q (degree + 1) ringRank lweDimension
          keySwitchLevels queryCount ×
        Native.ConditionalSmudging.BootstrappingMask
          q (degree + 1) ringRank params.levels lweDimension) := do
  let secrets ← KeySwitchFirstFiniteView.secretSampler
    lweDimension ringRank (degree + 1)
  let auxiliary ← sourceAuxiliarySampler (queryCount := queryCount)
    keySwitchErrorSampler inputErrorSampler keySwitchGadget secrets.1 secrets.2
  let mask ← $ᵗ BinarySecret lweDimension
  let targetSecret := Native.ScalarSecretRandomization.maskedSecret secrets.1 mask
  let freshMask ← Native.ConditionalSmudging.sampleFreshBootstrappingMask
    q (degree + 1) ringRank params.levels lweDimension
  return ((targetSecret, secrets.2, transportSourceAuxiliary mask auxiliary), freshMask)

/-- Marginal sampler for the transformed static side in the direct adaptive normal form. -/
noncomputable def coupledDirectStaticSideExperiment
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    ProbComp
      (CorrectStaticMaskSide q (degree + 1) ringRank lweDimension
        keySwitchLevels queryCount) := do
  let secrets ← KeySwitchFirstFiniteView.secretSampler
    lweDimension ringRank (degree + 1)
  let auxiliary ← sourceAuxiliarySampler (queryCount := queryCount)
    keySwitchErrorSampler inputErrorSampler keySwitchGadget secrets.1 secrets.2
  let mask ← $ᵗ BinarySecret lweDimension
  let targetSecret := Native.ScalarSecretRandomization.maskedSecret secrets.1 mask
  return (targetSecret, secrets.2, transportSourceAuxiliary mask auxiliary)

/-- Evaluated mask sampler at one retained transformed secret pair. -/
noncomputable def correctMaskAtStaticSide
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension)
    (side : CorrectStaticMaskSide q (degree + 1) ringRank lweDimension
      keySwitchLevels queryCount) :
    ProbComp (Native.ConditionalSmudging.BootstrappingMask
      q (degree + 1) ringRank params.levels lweDimension) :=
  Native.ConditionalSmudging.bootstrappingMask <$>
    OffDiagonalNormalForm.correctKeyExperiment params
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      side.1 side.2.1 coordinate

/-- The direct correct joint is a shared static-side sampler followed by its fixed-secret mask
kernel. -/
theorem coupledDirectCorrectStaticMaskExperiment_evalDist_eq_sideBind
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    evalDist
        (coupledDirectCorrectStaticMaskExperiment
          (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
          (eta := eta) params keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate) =
      evalDist
        (coupledDirectStaticSideExperiment (degree := degree)
            (ringRank := ringRank) (queryCount := queryCount)
            keySwitchErrorSampler inputErrorSampler keySwitchGadget >>= fun side ↦
          correctMaskAtStaticSide (eta := eta) params coordinate side >>= fun mask ↦
          pure (side, mask)) := by
  simp [coupledDirectCorrectStaticMaskExperiment,
    coupledDirectStaticSideExperiment, correctMaskAtStaticSide,
    map_eq_bind_pure_comp, monad_norm]

/-- The direct fresh comparison uses the same static-side sampler followed by the fresh product
mask sampler. -/
theorem coupledDirectFreshStaticMaskExperiment_evalDist_eq_sideBind
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    evalDist
        (coupledDirectFreshStaticMaskExperiment
          (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
          params keySwitchErrorSampler inputErrorSampler keySwitchGadget) =
      evalDist
        (coupledDirectStaticSideExperiment (degree := degree)
            (ringRank := ringRank) (queryCount := queryCount)
            keySwitchErrorSampler inputErrorSampler keySwitchGadget >>= fun side ↦
          Native.ConditionalSmudging.sampleFreshBootstrappingMask
              q (degree + 1) ringRank params.levels lweDimension >>= fun mask ↦
          pure (side, mask)) := by
  simp [coupledDirectFreshStaticMaskExperiment,
    coupledDirectStaticSideExperiment, monad_norm]

/-- Resampling the output of a total side-dependent kernel independently retains only the side
marginal; the discarded original output draw vanishes exactly. -/
theorem sideIndependentOutput_sideBind_evalDist_eq
    {Side Output : Type} [Finite Side] [Finite Output]
    (sideSampler : ProbComp Side)
    (outputKernel : Side → ProbComp Output)
    (freshOutput : ProbComp Output)
    (htotal : ∀ side, probFailure (outputKernel side) = 0) :
    evalDist
        (FormalProof4FHE.ConditionalCollision.sideIndependentOutput
          (sideSampler >>= fun side ↦
            outputKernel side >>= fun output ↦ pure (side, output))
          freshOutput) =
      evalDist
        (sideSampler >>= fun side ↦
          freshOutput >>= fun output ↦ pure (side, output)) := by
  unfold FormalProof4FHE.ConditionalCollision.sideIndependentOutput
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_congr' sideSampler fun side ↦ ?_
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
    (outputKernel side) (htotal side)
      (freshOutput >>= fun output ↦ pure (side, output))

/-- The library's independently refreshed static-mask experiment is exactly the direct static
side followed by the native fresh product-mask sampler. -/
theorem correctStaticMaskIndependentExperiment_evalDist_eq_coupledDirectFresh
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    evalDist
        (correctStaticMaskIndependentExperiment (degree := degree + 1)
          (ringRank := ringRank) (queryCount := queryCount) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) =
      evalDist
        (coupledDirectFreshStaticMaskExperiment
          (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
          params keySwitchErrorSampler inputErrorSampler keySwitchGadget) := by
  let ActualJoint := correctStaticMaskJointExperiment (degree := degree + 1)
    (ringRank := ringRank) (queryCount := queryCount) params
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
    keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
  let DirectJoint := coupledDirectCorrectStaticMaskExperiment
    (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
    (eta := eta) params keySwitchErrorSampler inputErrorSampler
    keySwitchGadget coordinate
  let SideSampler := coupledDirectStaticSideExperiment (degree := degree)
    (ringRank := ringRank) (lweDimension := lweDimension)
    (queryCount := queryCount)
    keySwitchErrorSampler inputErrorSampler keySwitchGadget
  let Kernel := correctMaskAtStaticSide (degree := degree)
    (ringRank := ringRank) (lweDimension := lweDimension)
    (keySwitchLevels := keySwitchLevels) (queryCount := queryCount)
    (eta := eta) params coordinate
  let ShapedJoint := SideSampler >>= fun side ↦
    Kernel side >>= fun mask ↦ pure (side, mask)
  let UniformMasks : ProbComp
      (Native.ConditionalSmudging.BootstrappingMask
        q (degree + 1) ringRank params.levels lweDimension) :=
    $ᵗ (Native.ConditionalSmudging.BootstrappingMask
      q (degree + 1) ringRank params.levels lweDimension)
  let FreshMasks := Native.ConditionalSmudging.sampleFreshBootstrappingMask
    q (degree + 1) ringRank params.levels lweDimension
  have hActualDirect : evalDist ActualJoint = evalDist DirectJoint := by
    simpa only [ActualJoint, DirectJoint] using
      (correctStaticMaskJointExperiment_evalDist_eq_coupledDirect
        (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
        (eta := eta) params keySwitchErrorSampler inputErrorSampler
        keySwitchGadget coordinate)
  have hDirectShape : evalDist DirectJoint = evalDist ShapedJoint := by
    simpa only [DirectJoint, SideSampler, Kernel, ShapedJoint] using
      (coupledDirectCorrectStaticMaskExperiment_evalDist_eq_sideBind
        (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
        (eta := eta) params keySwitchErrorSampler inputErrorSampler
        keySwitchGadget coordinate)
  have hJointShape : evalDist ActualJoint = evalDist ShapedJoint :=
    hActualDirect.trans hDirectShape
  have hIndependent :
      evalDist
          (FormalProof4FHE.ConditionalCollision.sideIndependentOutput
            ActualJoint UniformMasks) =
        evalDist
          (FormalProof4FHE.ConditionalCollision.sideIndependentOutput
            ShapedJoint UniformMasks) := by
    have hBind := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
      hJointShape
      (fun value ↦ UniformMasks >>= fun output ↦ pure (value.1, output))
    simpa only [FormalProof4FHE.ConditionalCollision.sideIndependentOutput]
      using hBind
  have hKernelTotal : ∀ side, probFailure (Kernel side) = 0 := by
    intro side
    simp [Kernel, correctMaskAtStaticSide,
      OffDiagonalNormalForm.correctKeyExperiment]
  have hDiscard :
      evalDist
          (FormalProof4FHE.ConditionalCollision.sideIndependentOutput
            ShapedJoint UniformMasks) =
        evalDist (SideSampler >>= fun side ↦
          UniformMasks >>= fun output ↦ pure (side, output)) := by
    simpa only [ShapedJoint] using
      (sideIndependentOutput_sideBind_evalDist_eq
        SideSampler Kernel UniformMasks hKernelTotal)
  have hMasks : evalDist UniformMasks = evalDist FreshMasks := by
    simpa only [UniformMasks, FreshMasks] using
      (Native.ConditionalSmudging.sampleFreshBootstrappingMask_evalDist_eq_uniform
        q (degree + 1) ringRank params.levels lweDimension).symm
  have hFreshBind :
      evalDist (SideSampler >>= fun side ↦
          UniformMasks >>= fun output ↦ pure (side, output)) =
        evalDist (SideSampler >>= fun side ↦
          FreshMasks >>= fun output ↦ pure (side, output)) := by
    refine evalDist_bind_congr' SideSampler fun side ↦ ?_
    exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
      hMasks (fun output ↦ pure (side, output))
  have hFreshShape :
      evalDist
          (coupledDirectFreshStaticMaskExperiment
            (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
            params keySwitchErrorSampler inputErrorSampler keySwitchGadget) =
        evalDist (SideSampler >>= fun side ↦
          FreshMasks >>= fun output ↦ pure (side, output)) := by
    simpa only [SideSampler, FreshMasks] using
      (coupledDirectFreshStaticMaskExperiment_evalDist_eq_sideBind
        (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
        params keySwitchErrorSampler inputErrorSampler keySwitchGadget)
  calc
    _ = evalDist
        (FormalProof4FHE.ConditionalCollision.sideIndependentOutput
          ActualJoint UniformMasks) := by
      rfl
    _ = evalDist
        (FormalProof4FHE.ConditionalCollision.sideIndependentOutput
          ShapedJoint UniformMasks) := hIndependent
    _ = evalDist (SideSampler >>= fun side ↦
        UniformMasks >>= fun output ↦ pure (side, output)) := hDiscard
    _ = evalDist (SideSampler >>= fun side ↦
        FreshMasks >>= fun output ↦ pure (side, output)) := hFreshBind
    _ = _ := hFreshShape.symm

/-- Averaging the fixed-secret selected-diagonal theorem preserves its candidate-independent
loss while retaining the complete transformed static side. -/
theorem tvDist_coupledDirectCorrectStaticMask_fresh_le_worstCaseStatic
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    tvDist
        (coupledDirectCorrectStaticMaskExperiment
          (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
          (eta := eta) params keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate)
        (coupledDirectFreshStaticMaskExperiment
          (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
          params keySwitchErrorSampler inputErrorSampler keySwitchGadget) ≤
      worstCaseStaticMaskDiagonalChiSquareLoss (ringRank := ringRank) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta) := by
  let Secrets := KeySwitchFirstFiniteView.secretSampler
    lweDimension ringRank (degree + 1)
  let Aux := fun secrets : Secret lweDimension ringRank (degree + 1) ↦
    sourceAuxiliarySampler (queryCount := queryCount)
      keySwitchErrorSampler inputErrorSampler keySwitchGadget secrets.1 secrets.2
  let Masks := $ᵗ BinarySecret lweDimension
  unfold coupledDirectCorrectStaticMaskExperiment
    coupledDirectFreshStaticMaskExperiment
  change tvDist
      (Secrets >>= fun secrets ↦
        Aux secrets >>= fun auxiliary ↦
        Masks >>= fun mask ↦
        let targetSecret :=
          Native.ScalarSecretRandomization.maskedSecret secrets.1 mask
        OffDiagonalNormalForm.correctKeyExperiment params
            (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
            targetSecret secrets.2 coordinate >>= fun bootstrappingKey ↦
          pure ((targetSecret, secrets.2,
              transportSourceAuxiliary mask auxiliary),
            Native.ConditionalSmudging.bootstrappingMask bootstrappingKey))
      (Secrets >>= fun secrets ↦
        Aux secrets >>= fun auxiliary ↦
        Masks >>= fun mask ↦
        let targetSecret :=
          Native.ScalarSecretRandomization.maskedSecret secrets.1 mask
        Native.ConditionalSmudging.sampleFreshBootstrappingMask
            q (degree + 1) ringRank params.levels lweDimension >>= fun freshMask ↦
          pure ((targetSecret, secrets.2,
              transportSourceAuxiliary mask auxiliary), freshMask)) ≤ _
  apply tvDist_bind_left_le_const'
  intro secrets
  apply tvDist_bind_left_le_const'
  intro auxiliary
  apply tvDist_bind_left_le_const'
  intro mask
  let TargetSecret := Native.ScalarSecretRandomization.maskedSecret secrets.1 mask
  let Side : CorrectStaticMaskSide q (degree + 1) ringRank lweDimension
      keySwitchLevels queryCount :=
    (TargetSecret, secrets.2, transportSourceAuxiliary mask auxiliary)
  let ActualMasks := Native.ConditionalSmudging.bootstrappingMask <$>
    OffDiagonalNormalForm.correctKeyExperiment params
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      TargetSecret secrets.2 coordinate
  let FreshMasks := Native.ConditionalSmudging.sampleFreshBootstrappingMask
    q (degree + 1) ringRank params.levels lweDimension
  let Attach := fun freshMask : Native.ConditionalSmudging.BootstrappingMask
      q (degree + 1) ringRank params.levels lweDimension ↦
    (Side, freshMask)
  have hFixed := tvDist_correctKeyExperiment_mask_fresh_le_worstCaseStatic
    params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      TargetSecret secrets.2 coordinate
  have hMapped := (tvDist_map_le (m := ProbComp) Attach
    ActualMasks FreshMasks).trans hFixed
  simpa only [TargetSecret, Side, ActualMasks, FreshMasks, Attach,
    map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] using hMapped

/-- Adaptive residual-free mask replacement is bounded solely by the worst selected-diagonal
chi-square loss.  No off-diagonal term and no residual-conditioned collision premise remain. -/
theorem tvDist_correctStaticMaskJoint_independent_le_worstCaseStatic
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    tvDist
        (correctStaticMaskJointExperiment (degree := degree + 1)
          (ringRank := ringRank) (queryCount := queryCount) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
        (correctStaticMaskIndependentExperiment (degree := degree + 1)
          (ringRank := ringRank) (queryCount := queryCount) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) ≤
      worstCaseStaticMaskDiagonalChiSquareLoss (ringRank := ringRank) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta) := by
  have hActual := correctStaticMaskJointExperiment_evalDist_eq_coupledDirect
    (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
    (eta := eta) params keySwitchErrorSampler inputErrorSampler
    keySwitchGadget coordinate
  have hFresh := correctStaticMaskIndependentExperiment_evalDist_eq_coupledDirectFresh
    (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
    (eta := eta) params keySwitchErrorSampler inputErrorSampler
    keySwitchGadget coordinate
  have hBound := tvDist_coupledDirectCorrectStaticMask_fresh_le_worstCaseStatic
    (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
    (eta := eta) params keySwitchErrorSampler inputErrorSampler
    keySwitchGadget coordinate
  unfold tvDist at hBound ⊢
  rw [← hActual, ← hFresh] at hBound
  exact hBound

/-- Data processing through wide-noise assembly preserves the selected-diagonal static-mask
bound at the complete public-context level. -/
theorem tvDist_correctStaticMaskWideView_independent_le_worstCaseStatic
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (wideNoise : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    tvDist
        (correctStaticMaskWideView (degree := degree + 1)
          (ringRank := ringRank) (queryCount := queryCount) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
        (correctStaticMaskIndependentWideView (degree := degree + 1)
          (ringRank := ringRank) (queryCount := queryCount) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) ≤
      worstCaseStaticMaskDiagonalChiSquareLoss (ringRank := ringRank) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta) := by
  let Joint := correctStaticMaskJointExperiment (degree := degree + 1)
    (ringRank := ringRank) (queryCount := queryCount) params
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
    keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
  let Independent := correctStaticMaskIndependentExperiment (degree := degree + 1)
    (ringRank := ringRank) (queryCount := queryCount) params
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
    keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
  let Finish := Function.uncurry
    (fixedMaskWidePublicContext (degree := degree + 1) (ringRank := ringRank)
      (lweDimension := lweDimension) (keySwitchLevels := keySwitchLevels)
      (queryCount := queryCount) params wideNoise)
  have hData := tvDist_bind_right_le (m := ProbComp) Finish Joint Independent
  have hJoint := tvDist_correctStaticMaskJoint_independent_le_worstCaseStatic
    (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
    (eta := eta) params keySwitchErrorSampler inputErrorSampler
    keySwitchGadget coordinate
  simpa only [correctStaticMaskWideView, correctStaticMaskIndependentWideView,
    Joint, Independent, Finish] using hData.trans hJoint

/-- Residual-first post-smudging hybrid with the static-mask step discharged by the selected
diagonal theorem rather than by a full-mask collision premise. -/
theorem tvDist_averagedPostSmudgedCorrectTransform_staticMaskIndependent_le_selectedDiagonal
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (wideNoise : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    tvDist
        (PostEvaluationSmudging.averagedCorrectTransform
          (degree := degree + 1) (ringRank := ringRank)
          (queryCount := queryCount) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
        (correctStaticMaskIndependentWideView (degree := degree + 1)
          (ringRank := ringRank) (queryCount := queryCount) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) ≤
      correctResidualErasureCost (degree := degree + 1)
          (ringRank := ringRank) (queryCount := queryCount) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate +
        worstCaseStaticMaskDiagonalChiSquareLoss (ringRank := ringRank) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta) := by
  let Actual := correctResidualSmudgedView (degree := degree + 1)
    (ringRank := ringRank) (queryCount := queryCount) params
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
    keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
  let Erased := correctStaticMaskWideView (degree := degree + 1)
    (ringRank := ringRank) (queryCount := queryCount) params
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
    keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
  let Independent := correctStaticMaskIndependentWideView (degree := degree + 1)
    (ringRank := ringRank) (queryCount := queryCount) params
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
    keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
  have hErase : tvDist Actual Erased ≤
      correctResidualErasureCost (degree := degree + 1)
        (ringRank := ringRank) (queryCount := queryCount) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
        keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate := by
    have h := tvDist_correctResidualSmudgedView_erasedWideView_le
      (degree := degree + 1) (ringRank := ringRank) (queryCount := queryCount)
      params (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
    unfold tvDist at h ⊢
    rw [correctResidualErasedWideView_evalDist_eq_correctStaticMaskWideView
      (degree := degree + 1) (ringRank := ringRank) (queryCount := queryCount)
      params (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate] at h
    exact h
  have hMask : tvDist Erased Independent ≤
      worstCaseStaticMaskDiagonalChiSquareLoss (ringRank := ringRank) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta) :=
    tvDist_correctStaticMaskWideView_independent_le_worstCaseStatic
      (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
      (eta := eta) params wideNoise keySwitchErrorSampler inputErrorSampler
      keySwitchGadget coordinate
  have hTriangle := (tvDist_triangle Actual Erased Independent).trans
    (add_le_add hErase hMask)
  unfold tvDist at hTriangle ⊢
  rw [correctResidualSmudgedView_evalDist_eq_averagedCorrectTransform
    (degree := degree + 1) (ringRank := ringRank) (queryCount := queryCount)
    params (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
    keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate] at hTriangle
  exact hTriangle

/-- Security-only selected-diagonal endpoint: the correct post-smudged TFHE view is close to the
ordinary real public view by residual translation plus one mask-only diagonal chi-square loss. -/
theorem tvDist_averagedPostSmudgedCorrectTransform_realPublicView_le_selectedDiagonal
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (wideNoise : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    tvDist
        (PostEvaluationSmudging.averagedCorrectTransform
          (degree := degree + 1) (ringRank := ringRank)
          (queryCount := queryCount) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
        (realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) wideNoise keySwitchErrorSampler
          inputErrorSampler (Gadget.Base.ringGadget params) keySwitchGadget) ≤
      correctResidualErasureCost (degree := degree + 1)
          (ringRank := ringRank) (queryCount := queryCount) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate +
        worstCaseStaticMaskDiagonalChiSquareLoss (ringRank := ringRank) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta) := by
  have h :=
    tvDist_averagedPostSmudgedCorrectTransform_staticMaskIndependent_le_selectedDiagonal
      (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
      (eta := eta) params wideNoise keySwitchErrorSampler inputErrorSampler
      keySwitchGadget coordinate
  unfold tvDist at h ⊢
  rw [correctStaticMaskIndependentWideView_centeredBinomial_evalDist_eq_realPublicView
    (degree := degree) (ringRank := ringRank) (lweDimension := lweDimension)
    (queryCount := queryCount) (eta := eta) params wideNoise
    keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate] at h
  exact h

/-! ## Adaptive distribution-weighted retained-cokernel route -/

/-- Secret averaging preserves a packaged distribution-weighted retained-cokernel bound. -/
theorem tvDist_coupledDirectCorrectStaticMask_fresh_le_retainedCokernelGoodBad
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension)
    (certificate : RetainedCokernelGoodBadCertificate
      (ringRank := ringRank) params
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta)) :
    tvDist
        (coupledDirectCorrectStaticMaskExperiment
          (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
          (eta := eta) params keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate)
        (coupledDirectFreshStaticMaskExperiment
          (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
          params keySwitchErrorSampler inputErrorSampler keySwitchGadget) ≤
      certificate.lossBound := by
  let Secrets := KeySwitchFirstFiniteView.secretSampler
    lweDimension ringRank (degree + 1)
  let Aux := fun secrets : Secret lweDimension ringRank (degree + 1) ↦
    sourceAuxiliarySampler (queryCount := queryCount)
      keySwitchErrorSampler inputErrorSampler keySwitchGadget secrets.1 secrets.2
  let Masks := $ᵗ BinarySecret lweDimension
  unfold coupledDirectCorrectStaticMaskExperiment
    coupledDirectFreshStaticMaskExperiment
  change tvDist
      (Secrets >>= fun secrets ↦
        Aux secrets >>= fun auxiliary ↦
        Masks >>= fun mask ↦
        let targetSecret :=
          Native.ScalarSecretRandomization.maskedSecret secrets.1 mask
        OffDiagonalNormalForm.correctKeyExperiment params
            (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
            targetSecret secrets.2 coordinate >>= fun bootstrappingKey ↦
          pure ((targetSecret, secrets.2,
              transportSourceAuxiliary mask auxiliary),
            Native.ConditionalSmudging.bootstrappingMask bootstrappingKey))
      (Secrets >>= fun secrets ↦
        Aux secrets >>= fun auxiliary ↦
        Masks >>= fun mask ↦
        let targetSecret :=
          Native.ScalarSecretRandomization.maskedSecret secrets.1 mask
        Native.ConditionalSmudging.sampleFreshBootstrappingMask
            q (degree + 1) ringRank params.levels lweDimension >>= fun freshMask ↦
          pure ((targetSecret, secrets.2,
              transportSourceAuxiliary mask auxiliary), freshMask)) ≤ _
  apply tvDist_bind_left_le_const'
  intro secrets
  apply tvDist_bind_left_le_const'
  intro auxiliary
  apply tvDist_bind_left_le_const'
  intro mask
  let TargetSecret := Native.ScalarSecretRandomization.maskedSecret secrets.1 mask
  let Side : CorrectStaticMaskSide q (degree + 1) ringRank lweDimension
      keySwitchLevels queryCount :=
    (TargetSecret, secrets.2, transportSourceAuxiliary mask auxiliary)
  let ActualMasks := Native.ConditionalSmudging.bootstrappingMask <$>
    OffDiagonalNormalForm.correctKeyExperiment params
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      TargetSecret secrets.2 coordinate
  let FreshMasks := Native.ConditionalSmudging.sampleFreshBootstrappingMask
    q (degree + 1) ringRank params.levels lweDimension
  let Attach := fun freshMask : Native.ConditionalSmudging.BootstrappingMask
      q (degree + 1) ringRank params.levels lweDimension ↦
    (Side, freshMask)
  have hFixed :=
    RetainedCokernelGoodBadCertificate.tvDist_correctKeyExperiment_mask_fresh_le
      params (RLWE.CenteredBinomial.sampler q (degree + 1) eta) certificate
      TargetSecret secrets.2 coordinate
  have hMapped := (tvDist_map_le (m := ProbComp) Attach
    ActualMasks FreshMasks).trans hFixed
  simpa only [TargetSecret, Side, ActualMasks, FreshMasks, Attach,
    map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] using hMapped

/-- The adaptive static-side joint experiment inherits the distribution-weighted native
retained-cokernel bound. -/
theorem tvDist_correctStaticMaskJoint_independent_le_retainedCokernelGoodBad
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension)
    (certificate : RetainedCokernelGoodBadCertificate
      (ringRank := ringRank) params
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta)) :
    tvDist
        (correctStaticMaskJointExperiment (degree := degree + 1)
          (ringRank := ringRank) (queryCount := queryCount) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
        (correctStaticMaskIndependentExperiment (degree := degree + 1)
          (ringRank := ringRank) (queryCount := queryCount) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) ≤
      certificate.lossBound := by
  have hActual := correctStaticMaskJointExperiment_evalDist_eq_coupledDirect
    (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
    (eta := eta) params keySwitchErrorSampler inputErrorSampler
    keySwitchGadget coordinate
  have hFresh := correctStaticMaskIndependentExperiment_evalDist_eq_coupledDirectFresh
    (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
    (eta := eta) params keySwitchErrorSampler inputErrorSampler
    keySwitchGadget coordinate
  have hBound :=
    tvDist_coupledDirectCorrectStaticMask_fresh_le_retainedCokernelGoodBad
      (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
      (eta := eta) params keySwitchErrorSampler inputErrorSampler
      keySwitchGadget coordinate certificate
  unfold tvDist at hBound ⊢
  rw [← hActual, ← hFresh] at hBound
  exact hBound

/-- Data processing through wide-noise assembly preserves the distribution-weighted
retained-cokernel bound. -/
theorem tvDist_correctStaticMaskWideView_independent_le_retainedCokernelGoodBad
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (wideNoise : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension)
    (certificate : RetainedCokernelGoodBadCertificate
      (ringRank := ringRank) params
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta)) :
    tvDist
        (correctStaticMaskWideView (degree := degree + 1)
          (ringRank := ringRank) (queryCount := queryCount) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
        (correctStaticMaskIndependentWideView (degree := degree + 1)
          (ringRank := ringRank) (queryCount := queryCount) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) ≤
      certificate.lossBound := by
  let Joint := correctStaticMaskJointExperiment (degree := degree + 1)
    (ringRank := ringRank) (queryCount := queryCount) params
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
    keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
  let Independent := correctStaticMaskIndependentExperiment (degree := degree + 1)
    (ringRank := ringRank) (queryCount := queryCount) params
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
    keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
  let Finish := Function.uncurry
    (fixedMaskWidePublicContext (degree := degree + 1) (ringRank := ringRank)
      (lweDimension := lweDimension) (keySwitchLevels := keySwitchLevels)
      (queryCount := queryCount) params wideNoise)
  have hData := tvDist_bind_right_le (m := ProbComp) Finish Joint Independent
  have hJoint :=
    tvDist_correctStaticMaskJoint_independent_le_retainedCokernelGoodBad
      (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
      (eta := eta) params keySwitchErrorSampler inputErrorSampler
      keySwitchGadget coordinate certificate
  simpa only [correctStaticMaskWideView, correctStaticMaskIndependentWideView,
    Joint, Independent, Finish] using hData.trans hJoint

/-- Residual erasure plus the distribution-weighted mask theorem bounds the complete correct
post-smudged public context. -/
theorem tvDist_averagedPostSmudgedCorrectTransform_staticMaskIndependent_le_retainedCokernelGoodBad
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (wideNoise : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension)
    (certificate : RetainedCokernelGoodBadCertificate
      (ringRank := ringRank) params
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta)) :
    tvDist
        (PostEvaluationSmudging.averagedCorrectTransform
          (degree := degree + 1) (ringRank := ringRank)
          (queryCount := queryCount) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
        (correctStaticMaskIndependentWideView (degree := degree + 1)
          (ringRank := ringRank) (queryCount := queryCount) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) ≤
      correctResidualErasureCost (degree := degree + 1)
          (ringRank := ringRank) (queryCount := queryCount) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate +
        certificate.lossBound := by
  let Actual := correctResidualSmudgedView (degree := degree + 1)
    (ringRank := ringRank) (queryCount := queryCount) params
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
    keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
  let Erased := correctStaticMaskWideView (degree := degree + 1)
    (ringRank := ringRank) (queryCount := queryCount) params
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
    keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
  let Independent := correctStaticMaskIndependentWideView (degree := degree + 1)
    (ringRank := ringRank) (queryCount := queryCount) params
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
    keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
  have hErase : tvDist Actual Erased ≤
      correctResidualErasureCost (degree := degree + 1)
        (ringRank := ringRank) (queryCount := queryCount) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
        keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate := by
    have h := tvDist_correctResidualSmudgedView_erasedWideView_le
      (degree := degree + 1) (ringRank := ringRank) (queryCount := queryCount)
      params (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
    unfold tvDist at h ⊢
    rw [correctResidualErasedWideView_evalDist_eq_correctStaticMaskWideView
      (degree := degree + 1) (ringRank := ringRank) (queryCount := queryCount)
      params (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate] at h
    exact h
  have hMask : tvDist Erased Independent ≤ certificate.lossBound :=
    tvDist_correctStaticMaskWideView_independent_le_retainedCokernelGoodBad
      (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
      (eta := eta) params wideNoise keySwitchErrorSampler inputErrorSampler
      keySwitchGadget coordinate certificate
  have hTriangle := (tvDist_triangle Actual Erased Independent).trans
    (add_le_add hErase hMask)
  unfold tvDist at hTriangle ⊢
  rw [correctResidualSmudgedView_evalDist_eq_averagedCorrectTransform
    (degree := degree + 1) (ringRank := ringRank) (queryCount := queryCount)
    params (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
    keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate] at hTriangle
  exact hTriangle

/-- Security-facing endpoint: the actual correct post-smudged native TFHE view is close to the
ordinary real public view by residual translation plus the distribution-weighted retained
cokernel loss. -/
theorem tvDist_averagedPostSmudgedCorrectTransform_realPublicView_le_retainedCokernelGoodBad
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (wideNoise : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension)
    (certificate : RetainedCokernelGoodBadCertificate
      (ringRank := ringRank) params
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta)) :
    tvDist
        (PostEvaluationSmudging.averagedCorrectTransform
          (degree := degree + 1) (ringRank := ringRank)
          (queryCount := queryCount) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
        (realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) wideNoise keySwitchErrorSampler
          inputErrorSampler (Gadget.Base.ringGadget params) keySwitchGadget) ≤
      correctResidualErasureCost (degree := degree + 1)
          (ringRank := ringRank) (queryCount := queryCount) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate +
        certificate.lossBound := by
  have h :=
    tvDist_averagedPostSmudgedCorrectTransform_staticMaskIndependent_le_retainedCokernelGoodBad
      (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
      (eta := eta) params wideNoise keySwitchErrorSampler inputErrorSampler
      keySwitchGadget coordinate certificate
  unfold tvDist at h ⊢
  rw [correctStaticMaskIndependentWideView_centeredBinomial_evalDist_eq_realPublicView
    (degree := degree) (ringRank := ringRank) (lweDimension := lweDimension)
    (queryCount := queryCount) (eta := eta) params wideNoise
    keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate] at h
  exact h

end

end FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery.AugmentedResidual.NativeShifted.FullMaskCollision.StaticDiagonal
