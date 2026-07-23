/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.Probability.ConditionalCollision
import FormalProof4FHE.TFHE.NativeAdaptivePostEvaluationSmudging

/-!
# Full-Mask Conditional Collision for the Native Adaptive TFHE Evaluator

The correct native shifted evaluator and its zero-fresh-error residual endpoint have the same
target phase.  Their remaining difference is therefore the public BRK mask.  This module exposes
that statement without discarding correlated data:

* the target scalar and ring secrets;
* the complete evaluator residual, including every diagonal and off-diagonal row; and
* the transported KSK and adaptive input tape

are retained as side information.  Only the complete BRK public-mask tensor is replaced by an
independent fresh tensor.  A generic side-information collision inequality then bounds the
original mask/residual total variation by one explicit finite `L²` quantity.

Retaining the whole residual and auxiliary context is essential: a diagonal-only marginal would
not justify replacing off-diagonal masks that share the selected control ciphertext.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery.AugmentedResidual.NativeShifted.FullMaskCollision

noncomputable section

open FormalProof4FHE.TFHE
open Native
open FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing

/-- Everything needed to reconstruct the correct public context after supplying its BRK mask.
This deliberately retains the complete residual and transported auxiliary view. -/
abbrev CorrectMaskSide
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ) :=
  BinarySecret lweDimension ×
    RingBinarySecret ringRank degree ×
      Native.ConditionalSmudging.BootstrappingResidual
        q degree ringRank tgswLevels lweDimension ×
        Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount

/-- Side information extracted from one latent paired source and one evaluator coin. -/
def correctMaskSide
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ}
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension)
    (source : Secret lweDimension ringRank degree ×
      PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount)
    (coin : Coin q degree ringRank params.levels lweDimension) :
    CorrectMaskSide q degree ringRank params.levels lweDimension
      keySwitchLevels queryCount :=
  let targetSecret := Native.ScalarSecretRandomization.maskedSecret source.1.1 coin.1
  let residual :=
    (correctResidualAtTarget params coordinate targetSecret source.2.1 source.2.2
      source.1.2 coin).1
  let auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount :=
    ((transportedView params source.2.1 source.2.2 coin.1).1.2,
      (transportedView params source.2.1 source.2.2 coin.1).2)
  (targetSecret, source.1.2, residual, auxiliary)

/-- Complete evaluated BRK mask for the honest candidate at one latent source and coin. -/
def correctEvaluatedMask
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ}
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension)
    (source : Secret lweDimension ringRank degree ×
      PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount)
    (coin : Coin q degree ringRank params.levels lweDimension) :
    Native.ConditionalSmudging.BootstrappingMask
      q degree ringRank params.levels lweDimension :=
  Native.ConditionalSmudging.bootstrappingMask
    (transformWithCoin params coordinate (source.1.1 coordinate)
      source.2.1 source.2.2 coin).1

/-- Reconstruct a complete public context from retained phase-side information and one BRK mask. -/
def reconstructPublicContext
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ}
    (params : Gadget.Base.Parameters q)
    (side : CorrectMaskSide q degree ringRank params.levels lweDimension
      keySwitchLevels queryCount)
    (mask : Native.ConditionalSmudging.BootstrappingMask
      q degree ringRank params.levels lweDimension) :
    PublicContext q degree ringRank params.levels lweDimension
      keySwitchLevels queryCount :=
  (Native.ConditionalSmudging.assembleResidualBootstrappingKey
      q degree ringRank params.levels lweDimension
      (Gadget.Base.ringGadget params) side.1 side.2.1 side.2.2.1 mask,
    side.2.2.2)

/-- Pointwise phase reconstruction: the honest native evaluator is exactly recovered from its
complete public mask and the retained side tuple. -/
theorem reconstructPublicContext_correctMaskSide_correctEvaluatedMask
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ}
    [NeZero q] [NeZero degree]
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension)
    (source : Secret lweDimension ringRank degree ×
      PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount)
    (coin : Coin q degree ringRank params.levels lweDimension) :
    reconstructPublicContext params (correctMaskSide params coordinate source coin)
        (correctEvaluatedMask params coordinate source coin) =
      transformWithCoin params coordinate (source.1.1 coordinate)
        source.2.1 source.2.2 coin := by
  obtain ⟨degree, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne degree)
  let targetSecret := Native.ScalarSecretRandomization.maskedSecret source.1.1 coin.1
  let evaluated := transformWithCoin params coordinate (source.1.1 coordinate)
    source.2.1 source.2.2 coin
  apply Prod.ext
  · funext outputCoordinate
    apply Prod.ext
    · rfl
    · funext row
      have hphase := phase_transformWithCoin_correct params coordinate source.1.1
        source.2.1 source.2.2 source.1.2 coin outputCoordinate row
      have hphase' :
          (evaluated.1 outputCoordinate).2 row -
              (embedRingSecret q source.1.2 ⬝ᵥ fun component ↦
                (evaluated.1 outputCoordinate).1 component row) =
            TGSW.gadgetPhase (embedRingSecret q source.1.2)
                (Gadget.Base.ringGadget params)
                (embedConstantBit q (degree + 1) (targetSecret outputCoordinate)) row +
              (correctResidualAtTarget params coordinate targetSecret
                source.2.1 source.2.2 source.1.2 coin).1 outputCoordinate row := by
        simpa only [evaluated, targetSecret, TLWE.phase, TLWE.entry,
          TGSW.cmuxMessage_zero, BlindRotation.embedConstantBit_eq_embedBit,
          Native.ShiftedCandidateEvaluator.proofAdd_eq_add] using hphase
      change
        (Matrix.vecMul (embedRingSecret q source.1.2)
              (evaluated.1 outputCoordinate).1 +
            TGSW.gadgetPhase (embedRingSecret q source.1.2)
              (Gadget.Base.ringGadget params)
              (embedConstantBit q (degree + 1) (targetSecret outputCoordinate)) +
            (correctResidualAtTarget params coordinate targetSecret
              source.2.1 source.2.2 source.1.2 coin).1 outputCoordinate) row =
          (evaluated.1 outputCoordinate).2 row
      simp only [Pi.add_apply, Matrix.vecMul]
      rw [add_assoc, ← hphase']
      abel
  · rfl

/-! ## Complete latent joint experiment -/

/-- Joint law of the retained correct-side information and the complete BRK mask produced by the
native evaluator.  The paired secret is a latent proof witness; only the reconstructed public
context is exposed after data processing. -/
noncomputable def correctMaskJointExperiment
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    ProbComp
      (CorrectMaskSide q degree ringRank params.levels lweDimension
          keySwitchLevels queryCount ×
        Native.ConditionalSmudging.BootstrappingMask
          q degree ringRank params.levels lweDimension) := do
  let source ← pairedSource (ringRank := ringRank) (lweDimension := lweDimension)
    (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler inputErrorSampler
    (Gadget.Base.ringGadget params) keySwitchGadget
  let coin ← sampleCoin q degree ringRank params.levels lweDimension
  return (correctMaskSide params coordinate source coin,
    correctEvaluatedMask params coordinate source coin)

/-- Replace only the full evaluated mask by the independent product mask sampler, while retaining
the exact side marginal of `correctMaskJointExperiment`. -/
noncomputable def correctMaskIndependentExperiment
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    ProbComp
      (CorrectMaskSide q degree ringRank params.levels lweDimension
          keySwitchLevels queryCount ×
        Native.ConditionalSmudging.BootstrappingMask
          q degree ringRank params.levels lweDimension) :=
  FormalProof4FHE.ConditionalCollision.sideIndependentOutput
    (correctMaskJointExperiment (ringRank := ringRank) (queryCount := queryCount)
      params ringErrorSampler keySwitchErrorSampler inputErrorSampler
      keySwitchGadget coordinate)
    (Native.ConditionalSmudging.sampleFreshBootstrappingMask
      q degree ringRank params.levels lweDimension)

/-- Exact finite side-wise `L²` loss for decoupling the complete correct-evaluator BRK mask from
all retained phase and auxiliary information. -/
noncomputable def correctMaskCollisionLoss
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) : ℝ :=
  FormalProof4FHE.ConditionalCollision.outputReplacementL2Loss
    (correctMaskJointExperiment (ringRank := ringRank) (queryCount := queryCount)
      params ringErrorSampler keySwitchErrorSampler inputErrorSampler
      keySwitchGadget coordinate)
    (Native.ConditionalSmudging.sampleFreshBootstrappingMask
      q degree ringRank params.levels lweDimension)

theorem correctMaskCollisionLoss_nonneg
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    0 ≤ correctMaskCollisionLoss (ringRank := ringRank) (queryCount := queryCount)
      params ringErrorSampler keySwitchErrorSampler inputErrorSampler
      keySwitchGadget coordinate :=
  FormalProof4FHE.ConditionalCollision.outputReplacementL2Loss_nonneg _ _

/-- Data processing turns the full latent collision comparison into a public-context comparison. -/
theorem tvDist_reconstruct_correctMaskJoint_independent_le_collisionLoss
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    tvDist
        (Function.uncurry (reconstructPublicContext params) <$>
          correctMaskJointExperiment (ringRank := ringRank) (queryCount := queryCount)
            params ringErrorSampler keySwitchErrorSampler inputErrorSampler
            keySwitchGadget coordinate)
        (Function.uncurry (reconstructPublicContext params) <$>
          correctMaskIndependentExperiment (ringRank := ringRank)
            (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
            inputErrorSampler keySwitchGadget coordinate) ≤
      correctMaskCollisionLoss (ringRank := ringRank) (queryCount := queryCount)
        params ringErrorSampler keySwitchErrorSampler inputErrorSampler
        keySwitchGadget coordinate := by
  refine (tvDist_map_le (m := ProbComp) (Function.uncurry (reconstructPublicContext params))
    (correctMaskJointExperiment (ringRank := ringRank) (queryCount := queryCount)
      params ringErrorSampler keySwitchErrorSampler inputErrorSampler
      keySwitchGadget coordinate)
    (correctMaskIndependentExperiment (ringRank := ringRank) (queryCount := queryCount)
      params ringErrorSampler keySwitchErrorSampler inputErrorSampler
      keySwitchGadget coordinate)).trans ?_
  exact FormalProof4FHE.ConditionalCollision.tvDist_sideIndependentOutput_le_outputReplacementL2Loss
    _ _

/-- Reconstructing the real latent mask joint law gives exactly the original averaged honest
native evaluator.  The latent paired source disappears by the existing exact projection theorem. -/
theorem reconstruct_correctMaskJoint_evalDist_eq_averagedCorrectTransform
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ}
    [NeZero q] [NeZero degree]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    evalDist
        (Function.uncurry (reconstructPublicContext params) <$>
          correctMaskJointExperiment (ringRank := ringRank) (queryCount := queryCount)
            params ringErrorSampler keySwitchErrorSampler inputErrorSampler
            keySwitchGadget coordinate) =
      evalDist
        (averagedCorrectTransform (ringRank := ringRank) (queryCount := queryCount)
          params ringErrorSampler keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate) := by
  let Source := pairedSource (ringRank := ringRank) (lweDimension := lweDimension)
    (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler inputErrorSampler
    (Gadget.Base.ringGadget params) keySwitchGadget
  let Projected :=
    (fun source : Secret lweDimension ringRank degree ×
        PublicContext q degree ringRank params.levels lweDimension
          keySwitchLevels queryCount ↦
      (source.1.1 coordinate, source.2)) <$> Source
  let CoordinateSource := coordinateSource (ringRank := ringRank)
    (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler inputErrorSampler
    (Gadget.Base.ringGadget params) keySwitchGadget coordinate
  let Finish := fun hiddenAndContext : Bool ×
      PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount ↦
    transform params coordinate hiddenAndContext.1
      hiddenAndContext.2.1 hiddenAndContext.2.2
  have hProjected : evalDist Projected = evalDist CoordinateSource := by
    simpa only [Projected, Source, CoordinateSource] using
      (pairedSource_project_evalDist (ringRank := ringRank)
        (lweDimension := lweDimension) (queryCount := queryCount)
        ringErrorSampler keySwitchErrorSampler inputErrorSampler
        (Gadget.Base.ringGadget params) keySwitchGadget coordinate)
  have hBind := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    hProjected Finish
  calc
    evalDist
        (Function.uncurry (reconstructPublicContext params) <$>
          correctMaskJointExperiment (ringRank := ringRank) (queryCount := queryCount)
            params ringErrorSampler keySwitchErrorSampler inputErrorSampler
            keySwitchGadget coordinate) =
      evalDist (Source >>= fun source ↦
        sampleCoin q degree ringRank params.levels lweDimension >>= fun coin ↦
          pure (transformWithCoin params coordinate (source.1.1 coordinate)
            source.2.1 source.2.2 coin)) := by
        unfold correctMaskJointExperiment
        simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
        refine evalDist_bind_congr' Source fun source ↦ ?_
        refine evalDist_bind_congr'
          (sampleCoin q degree ringRank params.levels lweDimension) fun coin ↦ ?_
        change evalDist (pure (reconstructPublicContext params
            (correctMaskSide params coordinate source coin)
            (correctEvaluatedMask params coordinate source coin))) =
          evalDist (pure (transformWithCoin params coordinate (source.1.1 coordinate)
            source.2.1 source.2.2 coin))
        rw [reconstructPublicContext_correctMaskSide_correctEvaluatedMask
          params coordinate source coin]
    _ = evalDist (Projected >>= Finish) := by
      simp [Projected, Finish, transform, Source, map_eq_bind_pure_comp, monad_norm]
    _ = evalDist (CoordinateSource >>= Finish) := hBind
    _ = evalDist
        (averagedCorrectTransform (ringRank := ringRank) (queryCount := queryCount)
          params ringErrorSampler keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate) := by
      rfl

/-- For one latent source and coin, reconstructing from an independent product mask is exactly
the coupled residual view with deterministic zero fresh row error. -/
theorem reconstruct_freshMask_evalDist_eq_coupledResidualView_zero
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension)
    (source : Secret lweDimension ringRank degree ×
      PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount)
    (coin : Coin q degree ringRank params.levels lweDimension) :
    evalDist
        (reconstructPublicContext params (correctMaskSide params coordinate source coin) <$>
          Native.ConditionalSmudging.sampleFreshBootstrappingMask
            q degree ringRank params.levels lweDimension) =
      evalDist
        (coupledResidualViewAtSourceCoin params
          (pure (Native.ConditionalSmudging.ringAdditiveZero q degree))
          coordinate source coin) := by
  let targetSecret := Native.ScalarSecretRandomization.maskedSecret source.1.1 coin.1
  let residual :=
    (correctResidualAtTarget params coordinate targetSecret source.2.1 source.2.2
      source.1.2 coin).1
  let auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount :=
    ((transportedView params source.2.1 source.2.2 coin.1).1.2,
      (transportedView params source.2.1 source.2.2 coin.1).2)
  let Generate := Native.ConditionalSmudging.generateResidualBootstrappingKey
    q degree ringRank params.levels lweDimension
    (pure (Native.ConditionalSmudging.ringAdditiveZero q degree))
    (Gadget.Base.ringGadget params) targetSecret source.1.2 residual
  let Assemble := Native.ConditionalSmudging.assembleResidualBootstrappingKey
    q degree ringRank params.levels lweDimension
    (Gadget.Base.ringGadget params) targetSecret source.1.2 residual
  let Masks := Native.ConditionalSmudging.sampleFreshBootstrappingMask
    q degree ringRank params.levels lweDimension
  let finish := fun bootstrappingKey :
      Native.BootstrappingKey q degree ringRank params.levels lweDimension ↦
    (bootstrappingKey, auxiliary)
  have hKey : evalDist Generate = evalDist (Assemble <$> Masks) := by
    simpa only [Generate, Assemble, Masks] using
      (Native.ConditionalSmudging.generateResidualBootstrappingKey_zero_evalDist_eq_assembleFreshMask
        q degree ringRank params.levels lweDimension
        (Gadget.Base.ringGadget params) targetSecret source.1.2 residual)
  have hMapped := evalDist_map_eq_of_evalDist_eq hKey finish
  simpa [reconstructPublicContext, correctMaskSide, coupledResidualViewAtSourceCoin,
    targetSecret, residual, auxiliary, Generate, Assemble, Masks, finish,
    map_eq_bind_pure_comp, monad_norm] using hMapped.symm

/-- Averaging the fixed-source identity identifies the independently replaced latent mask law
with the canonical zero-noise residual public view. -/
theorem reconstruct_correctMaskIndependent_evalDist_eq_coupledAveragedZeroNoiseResidualRealView
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    evalDist
        (Function.uncurry (reconstructPublicContext params) <$>
          correctMaskIndependentExperiment (degree := degree + 1)
            (ringRank := ringRank) (queryCount := queryCount) params
            (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
            keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) =
      evalDist
        (PostEvaluationSmudging.coupledAveragedZeroNoiseResidualRealView
          (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
          (eta := eta) params keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate) := by
  let Source := pairedSource (ringRank := ringRank) (lweDimension := lweDimension)
    (queryCount := queryCount)
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
    keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
    keySwitchGadget
  let Coins := sampleCoin q (degree + 1) ringRank params.levels lweDimension
  let Masks := Native.ConditionalSmudging.sampleFreshBootstrappingMask
    q (degree + 1) ringRank params.levels lweDimension
  calc
    evalDist
        (Function.uncurry (reconstructPublicContext params) <$>
          correctMaskIndependentExperiment (degree := degree + 1)
            (ringRank := ringRank) (queryCount := queryCount) params
            (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
            keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) =
      evalDist (Source >>= fun source ↦
        Coins >>= fun coin ↦
          reconstructPublicContext params (correctMaskSide params coordinate source coin) <$>
            Masks) := by
        simp [correctMaskIndependentExperiment,
          FormalProof4FHE.ConditionalCollision.sideIndependentOutput,
          correctMaskJointExperiment, Source, Coins, Masks,
          map_eq_bind_pure_comp, monad_norm]
    _ = evalDist (Source >>= fun source ↦
        Coins >>= fun coin ↦
          coupledResidualViewAtSourceCoin params
            (pure (Native.ConditionalSmudging.ringAdditiveZero q (degree + 1)))
            coordinate source coin) := by
      refine evalDist_bind_congr' Source fun source ↦ ?_
      refine evalDist_bind_congr' Coins fun coin ↦ ?_
      exact reconstruct_freshMask_evalDist_eq_coupledResidualView_zero
        params coordinate source coin
    _ = evalDist
        (PostEvaluationSmudging.coupledAveragedZeroNoiseResidualRealView
          (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
          (eta := eta) params keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate) := by
      rfl

/-- **Full-mask collision normal form.**  The exact pre-smudging correct-view distance is bounded
by one explicit finite side-wise `L²` loss.  The side coordinate retains the full residual, both
target secrets, and the transported KSK/tape, so this theorem replaces the entire BRK mask at
once without dropping shared diagonal/off-diagonal correlations. -/
theorem tvDist_averagedCorrectTransform_coupledZeroNoiseResidual_le_correctMaskCollisionLoss
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    tvDist
        (averagedCorrectTransform (ringRank := ringRank) (queryCount := queryCount)
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
        (PostEvaluationSmudging.coupledAveragedZeroNoiseResidualRealView
          (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
          (eta := eta) params keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate) ≤
      correctMaskCollisionLoss (degree := degree + 1) (ringRank := ringRank)
        (queryCount := queryCount) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate := by
  have hbound := tvDist_reconstruct_correctMaskJoint_independent_le_collisionLoss
    (degree := degree + 1) (ringRank := ringRank) (queryCount := queryCount)
    params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
    keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
  have hreal := reconstruct_correctMaskJoint_evalDist_eq_averagedCorrectTransform
    (degree := degree + 1) (ringRank := ringRank) (queryCount := queryCount)
    params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
    keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
  have hideal :=
    reconstruct_correctMaskIndependent_evalDist_eq_coupledAveragedZeroNoiseResidualRealView
      (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
      (eta := eta) params keySwitchErrorSampler inputErrorSampler
      keySwitchGadget coordinate
  unfold tvDist at hbound ⊢
  rw [hreal, hideal] at hbound
  exact hbound

/-! ## Conditional Pearson and pair-collision endpoint -/

/-- Independent-mask comparison using the uniform sampler on the complete mask type.  This is
distributionally equal to `correctMaskIndependentExperiment`, whose product sampler mirrors
native generation more directly. -/
noncomputable def correctMaskUniformIndependentExperiment
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    ProbComp
      (CorrectMaskSide q degree ringRank params.levels lweDimension
          keySwitchLevels queryCount ×
        Native.ConditionalSmudging.BootstrappingMask
          q degree ringRank params.levels lweDimension) :=
  FormalProof4FHE.ConditionalCollision.sideIndependentOutput
    (correctMaskJointExperiment (ringRank := ringRank) (queryCount := queryCount)
      params ringErrorSampler keySwitchErrorSampler inputErrorSampler
      keySwitchGadget coordinate)
    ($ᵗ (Native.ConditionalSmudging.BootstrappingMask
      q degree ringRank params.levels lweDimension))

/-- The native full-mask joint experiment is total. -/
@[simp]
theorem probFailure_correctMaskJointExperiment
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    probFailure
        (correctMaskJointExperiment (ringRank := ringRank) (queryCount := queryCount)
          params ringErrorSampler keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate) = 0 := by
  simp [correctMaskJointExperiment, pairedSource]

/-- Product sampling and uniform sampling give the same complete fresh-mask law, even after
retaining the exact side marginal. -/
theorem correctMaskIndependentExperiment_evalDist_eq_uniform
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    evalDist
        (correctMaskIndependentExperiment (ringRank := ringRank)
          (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
          inputErrorSampler keySwitchGadget coordinate) =
      evalDist
        (correctMaskUniformIndependentExperiment (ringRank := ringRank)
          (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
          inputErrorSampler keySwitchGadget coordinate) := by
  let Joint := correctMaskJointExperiment (ringRank := ringRank)
    (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
    inputErrorSampler keySwitchGadget coordinate
  let ProductMasks := Native.ConditionalSmudging.sampleFreshBootstrappingMask
    q degree ringRank params.levels lweDimension
  let UniformMasks := $ᵗ (Native.ConditionalSmudging.BootstrappingMask
    q degree ringRank params.levels lweDimension)
  have hmask : evalDist ProductMasks = evalDist UniformMasks := by
    simpa only [ProductMasks, UniformMasks] using
      (Native.ConditionalSmudging.sampleFreshBootstrappingMask_evalDist_eq_uniform
        q degree ringRank params.levels lweDimension)
  unfold correctMaskIndependentExperiment correctMaskUniformIndependentExperiment
    FormalProof4FHE.ConditionalCollision.sideIndependentOutput
  refine evalDist_bind_congr' Joint fun value ↦ ?_
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    hmask (fun mask ↦ pure (value.1, mask))

/-- Reconstructing the uniform-mask comparison gives exactly the zero-noise residual endpoint. -/
theorem reconstruct_correctMaskUniformIndependent_evalDist_eq_coupledAveragedZeroNoiseResidualRealView
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    evalDist
        (Function.uncurry (reconstructPublicContext params) <$>
          correctMaskUniformIndependentExperiment (degree := degree + 1)
            (ringRank := ringRank) (queryCount := queryCount) params
            (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
            keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) =
      evalDist
        (PostEvaluationSmudging.coupledAveragedZeroNoiseResidualRealView
          (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
          (eta := eta) params keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate) := by
  have hindependent := evalDist_map_eq_of_evalDist_eq
    (correctMaskIndependentExperiment_evalDist_eq_uniform
      (degree := degree + 1) (ringRank := ringRank) (queryCount := queryCount)
      params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
    (Function.uncurry (reconstructPublicContext params))
  exact hindependent.symm.trans
    (reconstruct_correctMaskIndependent_evalDist_eq_coupledAveragedZeroNoiseResidualRealView
      (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
      (eta := eta) params keySwitchErrorSampler inputErrorSampler
      keySwitchGadget coordinate)

/-- Conditional Pearson divergence of the complete native evaluated mask given all retained
correct-side information. -/
noncomputable def correctMaskPearsonChiSquare
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) : ℝ :=
  FormalProof4FHE.ConditionalCollision.outputReplacementChiSquare
    (correctMaskJointExperiment (ringRank := ringRank) (queryCount := queryCount)
      params ringErrorSampler keySwitchErrorSampler inputErrorSampler
      keySwitchGadget coordinate)

/-- Pointwise pair-collision certificate for the complete native evaluated mask. -/
def CorrectMaskConditionalCollisionBound
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) (ε : ℝ) : Prop :=
  FormalProof4FHE.ConditionalCollision.OutputConditionalCollisionBound
    (correctMaskJointExperiment (ringRank := ringRank) (queryCount := queryCount)
      params ringErrorSampler keySwitchErrorSampler inputErrorSampler
      keySwitchGadget coordinate) ε

/-- A uniform random-tape normal form reduces the native full-mask collision premise to literal
finite side/output fiber counts.  The tape may contain every secret, encryption error, public
mask, and evaluator coin used by the concrete experiment; no independence is inferred here. -/
theorem correctMaskConditionalCollisionBound_of_uniformTapeFiberBound
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) (ε : ℝ)
    {Tape : Type} [Fintype Tape] [SampleableType Tape]
    (tapeSide : Tape →
      CorrectMaskSide q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount)
    (tapeMask : Tape → Native.ConditionalSmudging.BootstrappingMask
      q degree ringRank params.levels lweDimension)
    (hnormalForm :
      evalDist
          (correctMaskJointExperiment (ringRank := ringRank)
            (queryCount := queryCount) params ringErrorSampler
            keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) =
        evalDist
          (FormalProof4FHE.ConditionalCollision.uniformJointImage
            tapeSide tapeMask))
    (hfiber : ∀ sideValue,
      (Fintype.card
          (Native.ConditionalSmudging.BootstrappingMask
            q degree ringRank params.levels lweDimension) : ℝ) *
          ∑ maskValue,
            (@FormalProof4FHE.ConditionalCollision.jointFiberCard
              Tape
              (CorrectMaskSide q degree ringRank params.levels lweDimension
                keySwitchLevels queryCount)
              (Native.ConditionalSmudging.BootstrappingMask
                q degree ringRank params.levels lweDimension)
              inferInstance (Classical.decEq _) (Classical.decEq _)
              tapeSide tapeMask sideValue maskValue : ℝ) ^ 2 ≤
        (1 + ε) *
          (@FormalProof4FHE.ConditionalCollision.sideFiberCard
            Tape
            (CorrectMaskSide q degree ringRank params.levels lweDimension
              keySwitchLevels queryCount)
            inferInstance (Classical.decEq _) tapeSide sideValue : ℝ) ^ 2) :
    CorrectMaskConditionalCollisionBound (ringRank := ringRank)
      (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
      inputErrorSampler keySwitchGadget coordinate ε := by
  letI : DecidableEq
      (CorrectMaskSide q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount) := Classical.decEq _
  letI : DecidableEq
      (Native.ConditionalSmudging.BootstrappingMask
        q degree ringRank params.levels lweDimension) := Classical.decEq _
  exact
    FormalProof4FHE.ConditionalCollision.outputConditionalCollisionBound_of_evalDist_eq_uniformJointImage
      (correctMaskJointExperiment (ringRank := ringRank) (queryCount := queryCount)
        params ringErrorSampler keySwitchErrorSampler inputErrorSampler
        keySwitchGadget coordinate)
      tapeSide tapeMask ε hnormalForm hfiber

/-- Full public correct-view replacement from a complete conditional pair-collision bound. -/
theorem tvDist_averagedCorrectTransform_coupledZeroNoiseResidual_le_sqrt_of_collisionBound
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) (ε : ℝ)
    (hcollision : CorrectMaskConditionalCollisionBound
      (degree := degree + 1) (ringRank := ringRank) (queryCount := queryCount)
      params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate ε) :
    tvDist
        (averagedCorrectTransform (ringRank := ringRank) (queryCount := queryCount)
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
        (PostEvaluationSmudging.coupledAveragedZeroNoiseResidualRealView
          (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
          (eta := eta) params keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate) ≤
      Real.sqrt ε / 2 := by
  letI : DecidableEq
      (CorrectMaskSide q (degree + 1) ringRank params.levels lweDimension
        keySwitchLevels queryCount) := Classical.decEq _
  letI : DecidableEq
      (Native.ConditionalSmudging.BootstrappingMask
        q (degree + 1) ringRank params.levels lweDimension) := Classical.decEq _
  let Joint := correctMaskJointExperiment (degree := degree + 1)
    (ringRank := ringRank) (queryCount := queryCount) params
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
    keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
  let UniformIdeal := correctMaskUniformIndependentExperiment (degree := degree + 1)
    (ringRank := ringRank) (queryCount := queryCount) params
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
    keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
  have hmap := tvDist_map_le (m := ProbComp)
    (Function.uncurry (reconstructPublicContext params)) Joint UniformIdeal
  have hcollisionBound : tvDist Joint UniformIdeal ≤ Real.sqrt ε / 2 := by
    exact FormalProof4FHE.ConditionalCollision.tvDist_sideIndependentUniform_le_sqrt_of_conditionalCollisionBound
      Joint ε (by simp [Joint]) hcollision
  have hbound := hmap.trans hcollisionBound
  have hreal := reconstruct_correctMaskJoint_evalDist_eq_averagedCorrectTransform
    (degree := degree + 1) (ringRank := ringRank) (queryCount := queryCount)
    params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
    keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
  have hideal :=
    reconstruct_correctMaskUniformIndependent_evalDist_eq_coupledAveragedZeroNoiseResidualRealView
      (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
      (eta := eta) params keySwitchErrorSampler inputErrorSampler
      keySwitchGadget coordinate
  unfold tvDist at hbound ⊢
  rw [hreal, hideal] at hbound
  exact hbound

/-- Counting-form specialization of the full public-view replacement theorem.  Once the concrete
native source is compiled into one uniform finite tape, the only remaining premise is the displayed
ordered-pair fiber inequality. -/
theorem tvDist_averagedCorrectTransform_coupledZeroNoiseResidual_le_sqrt_of_uniformTapeFiberBound
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) (ε : ℝ)
    {Tape : Type} [Fintype Tape] [SampleableType Tape]
    (tapeSide : Tape →
      CorrectMaskSide q (degree + 1) ringRank params.levels lweDimension
        keySwitchLevels queryCount)
    (tapeMask : Tape → Native.ConditionalSmudging.BootstrappingMask
      q (degree + 1) ringRank params.levels lweDimension)
    (hnormalForm :
      evalDist
          (correctMaskJointExperiment (degree := degree + 1)
            (ringRank := ringRank) (queryCount := queryCount) params
            (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
            keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) =
        evalDist
          (FormalProof4FHE.ConditionalCollision.uniformJointImage
            tapeSide tapeMask))
    (hfiber : ∀ sideValue,
      (Fintype.card
          (Native.ConditionalSmudging.BootstrappingMask
            q (degree + 1) ringRank params.levels lweDimension) : ℝ) *
          ∑ maskValue,
            (@FormalProof4FHE.ConditionalCollision.jointFiberCard
              Tape
              (CorrectMaskSide q (degree + 1) ringRank params.levels lweDimension
                keySwitchLevels queryCount)
              (Native.ConditionalSmudging.BootstrappingMask
                q (degree + 1) ringRank params.levels lweDimension)
              inferInstance (Classical.decEq _) (Classical.decEq _)
              tapeSide tapeMask sideValue maskValue : ℝ) ^ 2 ≤
        (1 + ε) *
          (@FormalProof4FHE.ConditionalCollision.sideFiberCard
            Tape
            (CorrectMaskSide q (degree + 1) ringRank params.levels lweDimension
              keySwitchLevels queryCount)
            inferInstance (Classical.decEq _) tapeSide sideValue : ℝ) ^ 2) :
    tvDist
        (averagedCorrectTransform (ringRank := ringRank) (queryCount := queryCount)
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
        (PostEvaluationSmudging.coupledAveragedZeroNoiseResidualRealView
          (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
          (eta := eta) params keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate) ≤
      Real.sqrt ε / 2 := by
  apply
    tvDist_averagedCorrectTransform_coupledZeroNoiseResidual_le_sqrt_of_collisionBound
      (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
      (eta := eta) params keySwitchErrorSampler inputErrorSampler
      keySwitchGadget coordinate ε
  exact correctMaskConditionalCollisionBound_of_uniformTapeFiberBound
    (degree := degree + 1) (ringRank := ringRank) (queryCount := queryCount)
    params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
    keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate ε
    tapeSide tapeMask hnormalForm hfiber

/-! ## Post-smudging mask marginal

The preceding full-side certificate is deliberately strong: it retains the complete *unsmudged*
residual while replacing the evaluated mask.  In the actual security experiment the independent
wide body noise is added first.  The following hybrid therefore erases the narrow residual by
Gaussian translation before asking for mask freshness.  Its retained side is only the transformed
secret pair and transported public auxiliary context. -/

/-- Static information needed to assemble a zero-residual wide-noise BRK from its public mask. -/
abbrev CorrectStaticMaskSide
    (q degree ringRank lweDimension keySwitchLevels queryCount : ℕ) :=
  BinarySecret lweDimension ×
    RingBinarySecret ringRank degree ×
      Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount

/-- Forget the narrow evaluator residual before performing the mask-replacement hybrid. -/
def correctStaticMaskSideOfCorrectMaskSide
    {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ}
    (side : CorrectMaskSide q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount) :
    CorrectStaticMaskSide q degree ringRank lweDimension keySwitchLevels queryCount :=
  (side.1, side.2.1, side.2.2.2)

/-- With one mask fixed, sample only independent wide body noise and assemble the target BRK. -/
def fixedMaskWidePublicContext
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ}
    (params : Gadget.Base.Parameters q)
    (wideNoise : ProbComp (RLWE.Rq q degree))
    (side : CorrectStaticMaskSide q degree ringRank lweDimension
      keySwitchLevels queryCount)
    (mask : Native.ConditionalSmudging.BootstrappingMask
      q degree ringRank params.levels lweDimension) :
    ProbComp
      (PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount) := do
  let bootstrappingKey ← Native.ConditionalSmudging.fixedMaskWideKey
    wideNoise (Gadget.Base.ringGadget params) side.1 side.2.1 mask
  return (bootstrappingKey, side.2.2)

/-- Joint marginal of the transformed static side and the complete evaluated BRK mask. -/
noncomputable def correctStaticMaskJointExperiment
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    ProbComp
      (CorrectStaticMaskSide q degree ringRank lweDimension
          keySwitchLevels queryCount ×
        Native.ConditionalSmudging.BootstrappingMask
          q degree ringRank params.levels lweDimension) :=
  (fun value ↦
      (correctStaticMaskSideOfCorrectMaskSide value.1, value.2)) <$>
    correctMaskJointExperiment (ringRank := ringRank) (queryCount := queryCount)
      params ringErrorSampler keySwitchErrorSampler inputErrorSampler
      keySwitchGadget coordinate

/-- Replace the evaluated mask only after the narrow residual has been forgotten. -/
noncomputable def correctStaticMaskIndependentExperiment
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    ProbComp
      (CorrectStaticMaskSide q degree ringRank lweDimension
          keySwitchLevels queryCount ×
        Native.ConditionalSmudging.BootstrappingMask
          q degree ringRank params.levels lweDimension) :=
  FormalProof4FHE.ConditionalCollision.sideIndependentOutput
    (correctStaticMaskJointExperiment (ringRank := ringRank)
      (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
      inputErrorSampler keySwitchGadget coordinate)
    ($ᵗ (Native.ConditionalSmudging.BootstrappingMask
      q degree ringRank params.levels lweDimension))

/-- Pair-collision certificate for the mask marginal after erasing the narrow residual. -/
def CorrectStaticMaskConditionalCollisionBound
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) (ε : ℝ) : Prop :=
  FormalProof4FHE.ConditionalCollision.OutputConditionalCollisionBound
    (correctStaticMaskJointExperiment (ringRank := ringRank)
      (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
      inputErrorSampler keySwitchGadget coordinate) ε

/-- The native static mask joint experiment is total. -/
@[simp]
theorem probFailure_correctStaticMaskJointExperiment
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    probFailure
        (correctStaticMaskJointExperiment (ringRank := ringRank)
          (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
          inputErrorSampler keySwitchGadget coordinate) = 0 := by
  simp [correctStaticMaskJointExperiment]

/-- Wide-noise view using the evaluator's actual mask marginal. -/
noncomputable def correctStaticMaskWideView
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler wideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    ProbComp
      (PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount) :=
  correctStaticMaskJointExperiment (ringRank := ringRank)
      (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
      inputErrorSampler keySwitchGadget coordinate >>=
    Function.uncurry (fixedMaskWidePublicContext params wideNoise)

/-- Wide-noise view after independently refreshing the complete mask. -/
noncomputable def correctStaticMaskIndependentWideView
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler wideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    ProbComp
      (PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount) :=
  correctStaticMaskIndependentExperiment (ringRank := ringRank)
      (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
      inputErrorSampler keySwitchGadget coordinate >>=
    Function.uncurry (fixedMaskWidePublicContext params wideNoise)

/-- Data processing turns the relaxed pair-collision certificate into a complete public-view
bound after residual erasure. -/
theorem tvDist_correctStaticMaskWideView_independent_le_sqrt_of_collisionBound
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler wideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) (ε : ℝ)
    (hcollision : CorrectStaticMaskConditionalCollisionBound
      (ringRank := ringRank) (queryCount := queryCount) params ringErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate ε) :
    tvDist
        (correctStaticMaskWideView (ringRank := ringRank)
          (queryCount := queryCount) params ringErrorSampler wideNoise
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
        (correctStaticMaskIndependentWideView (ringRank := ringRank)
          (queryCount := queryCount) params ringErrorSampler wideNoise
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) ≤
      Real.sqrt ε / 2 := by
  letI : DecidableEq
      (CorrectStaticMaskSide q degree ringRank lweDimension
        keySwitchLevels queryCount) := Classical.decEq _
  letI : DecidableEq
      (Native.ConditionalSmudging.BootstrappingMask
        q degree ringRank params.levels lweDimension) := Classical.decEq _
  let Joint := correctStaticMaskJointExperiment (ringRank := ringRank)
    (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
    inputErrorSampler keySwitchGadget coordinate
  let Independent := correctStaticMaskIndependentExperiment (ringRank := ringRank)
    (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
    inputErrorSampler keySwitchGadget coordinate
  let Finish := Function.uncurry
    (fixedMaskWidePublicContext (ringRank := ringRank)
      (lweDimension := lweDimension) (keySwitchLevels := keySwitchLevels)
      (queryCount := queryCount) params wideNoise)
  have hdata := tvDist_bind_right_le (m := ProbComp) Finish Joint Independent
  have hjoint : tvDist Joint Independent ≤ Real.sqrt ε / 2 :=
    FormalProof4FHE.ConditionalCollision.tvDist_sideIndependentUniform_le_sqrt_of_conditionalCollisionBound
      Joint ε (by simp [Joint]) hcollision
  simpa only [correctStaticMaskWideView, correctStaticMaskIndependentWideView,
    Joint, Independent, Finish] using hdata.trans hjoint

/-- The actual evaluated mask/residual key followed by executable post-evaluation smudging,
presented over the latent full-mask joint experiment. -/
noncomputable def correctResidualSmudgedView
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler wideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    ProbComp
      (PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount) :=
  correctMaskJointExperiment (ringRank := ringRank) (queryCount := queryCount)
      params ringErrorSampler keySwitchErrorSampler inputErrorSampler
      keySwitchGadget coordinate >>=
    fun value ↦ PostEvaluationSmudging.smudgePublicContext wideNoise
      (reconstructPublicContext params value.1 value.2)

/-- The intermediate view with the same evaluated mask but with the narrow residual erased before
the independent wide noise is assembled. -/
noncomputable def correctResidualErasedWideView
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler wideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    ProbComp
      (PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount) :=
  correctMaskJointExperiment (ringRank := ringRank) (queryCount := queryCount)
      params ringErrorSampler keySwitchErrorSampler inputErrorSampler
      keySwitchGadget coordinate >>=
    fun value ↦ fixedMaskWidePublicContext params wideNoise
      (correctStaticMaskSideOfCorrectMaskSide value.1) value.2

/-- Expected exact translation cost for erasing the narrow residual after wide noise has been
sampled. -/
noncomputable def correctResidualErasureCost
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler wideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) : ℝ :=
  ∑' value,
    Pr[= value |
      correctMaskJointExperiment (ringRank := ringRank) (queryCount := queryCount)
        params ringErrorSampler keySwitchErrorSampler inputErrorSampler
        keySwitchGadget coordinate].toReal *
      Native.ConditionalSmudging.bootstrappingSmudgingCost
        wideNoise value.1.2.2.1

theorem correctResidualErasureCost_nonneg
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler wideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    0 ≤ correctResidualErasureCost (ringRank := ringRank)
      (queryCount := queryCount) params ringErrorSampler wideNoise
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate := by
  apply tsum_nonneg
  intro value
  exact mul_nonneg ENNReal.toReal_nonneg
    (Native.ConditionalSmudging.bootstrappingSmudgingCost_nonneg
      wideNoise value.1.2.2.1)

/-- For a coupled centered-binomial source and a certified discrete-Gaussian wide sampler, the
expected residual-erasure cost is bounded by the same checked linear translation budget used by
the coupled residual proof. -/
theorem correctResidualErasureCost_centeredBinomial_discreteGaussian_le_linear
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    {alpha : ℝ} {halpha : 0 < alpha}
    (params : Gadget.Base.Parameters q)
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    correctResidualErasureCost (degree := degree + 1)
        (ringRank := ringRank) (queryCount := queryCount) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
        keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate ≤
      coupledCenteredBinomialDiscreteGaussianLinearSmudgingError
        params certificate (degree + 1) ringRank lweDimension eta := by
  let Value :=
    CorrectMaskSide q (degree + 1) ringRank params.levels lweDimension
        keySwitchLevels queryCount ×
      Native.ConditionalSmudging.BootstrappingMask
        q (degree + 1) ringRank params.levels lweDimension
  let Joint : ProbComp Value :=
    correctMaskJointExperiment (ringRank := ringRank) (queryCount := queryCount)
      params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
  let Cost := coupledCenteredBinomialDiscreteGaussianLinearSmudgingError
    params certificate (degree + 1) ringRank lweDimension eta
  letI : Fintype Value := Fintype.ofFinite Value
  have hmass : (∑ value : Value, Pr[= value | Joint].toReal) = 1 := by
    rw [← ENNReal.toReal_sum (fun _ _ ↦ probOutput_ne_top),
      sum_probOutput_eq_one (by simp [Joint]), ENNReal.toReal_one]
  have hpoint : ∀ value : Value, value ∈ support Joint →
      Native.ConditionalSmudging.bootstrappingSmudgingCost
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
          value.1.2.2.1 ≤ Cost := by
    intro value hvalue
    dsimp only [Joint, correctMaskJointExperiment] at hvalue
    rw [mem_support_bind_iff] at hvalue
    obtain ⟨source, hsource, hvalue⟩ := hvalue
    rw [mem_support_bind_iff] at hvalue
    obtain ⟨coin, _hcoin, hvalue⟩ := hvalue
    simp only [support_pure, Set.mem_singleton_iff] at hvalue
    subst value
    change Native.ConditionalSmudging.bootstrappingSmudgingCost
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
        (Native.ShiftedCandidateEvaluator.correctBootstrappingResidual params
          (embedRingSecret q source.1.2)
          (Native.ScalarSecretRandomization.maskedSecret source.1.1 coin.1)
          coordinate (transportedView params source.2.1 source.2.2 coin.1).1.1
          coin.2) ≤ Cost
    dsimp only [Cost,
      coupledCenteredBinomialDiscreteGaussianLinearSmudgingError]
    apply
      Native.ShiftedResidualBounds.bootstrappingSmudgingCost_correctResidual_discreteGaussian_le_linear
    intro outputCoordinate index
    exact cInfNorm_pairedSource_transportedRowError_le_eta params
      keySwitchErrorSampler inputErrorSampler keySwitchGadget hsource coin.1
      outputCoordinate index
  change (∑' value : Value, Pr[= value | Joint].toReal *
      Native.ConditionalSmudging.bootstrappingSmudgingCost
        (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
        value.1.2.2.1) ≤ Cost
  rw [tsum_fintype]
  calc
    ∑ value : Value, Pr[= value | Joint].toReal *
        Native.ConditionalSmudging.bootstrappingSmudgingCost
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
          value.1.2.2.1 ≤
      ∑ value : Value, Pr[= value | Joint].toReal * Cost := by
        apply Finset.sum_le_sum
        intro value _
        by_cases hvalue : value ∈ support Joint
        · exact mul_le_mul_of_nonneg_left (hpoint value hvalue)
            ENNReal.toReal_nonneg
        · have hzero : Pr[= value | Joint] = 0 :=
            probOutput_eq_zero_of_not_mem_support hvalue
          simp [hzero]
    _ = (∑ value : Value, Pr[= value | Joint].toReal) * Cost := by
      rw [Finset.sum_mul]
    _ = Cost := by rw [hmass, one_mul]

/-- Reconstructing and smudging the latent full-mask joint is exactly the original averaged
post-evaluation correct view. -/
theorem correctResidualSmudgedView_evalDist_eq_averagedCorrectTransform
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ}
    [NeZero q] [NeZero degree]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler wideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    evalDist
        (correctResidualSmudgedView (ringRank := ringRank)
          (queryCount := queryCount) params ringErrorSampler wideNoise
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) =
      evalDist
        (PostEvaluationSmudging.averagedCorrectTransform
          (ringRank := ringRank) (queryCount := queryCount) params
          ringErrorSampler wideNoise keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate) := by
  let Joint := correctMaskJointExperiment (ringRank := ringRank)
    (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
    inputErrorSampler keySwitchGadget coordinate
  let Reconstructed :=
    Function.uncurry (reconstructPublicContext params) <$> Joint
  let Smudge := PostEvaluationSmudging.smudgePublicContext
    (ringRank := ringRank) (tgswLevels := params.levels)
    (lweDimension := lweDimension) (keySwitchLevels := keySwitchLevels)
    (queryCount := queryCount) wideNoise
  have hbase : evalDist Reconstructed =
      evalDist
        (averagedCorrectTransform (ringRank := ringRank)
          (queryCount := queryCount) params ringErrorSampler
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) := by
    simpa only [Reconstructed, Joint] using
      (reconstruct_correctMaskJoint_evalDist_eq_averagedCorrectTransform
        (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
        params ringErrorSampler keySwitchErrorSampler inputErrorSampler
        keySwitchGadget coordinate)
  have hsmudged := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    hbase Smudge
  simpa [correctResidualSmudgedView,
    PostEvaluationSmudging.averagedCorrectTransform, Joint, Reconstructed,
    Smudge, Function.uncurry, map_eq_bind_pure_comp, bind_assoc] using hsmudged

/-- Forgetting the residual in the latent experiment gives exactly the static-mask wide view. -/
theorem correctResidualErasedWideView_evalDist_eq_correctStaticMaskWideView
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler wideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    evalDist
        (correctResidualErasedWideView (ringRank := ringRank)
          (queryCount := queryCount) params ringErrorSampler wideNoise
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) =
      evalDist
        (correctStaticMaskWideView (ringRank := ringRank)
          (queryCount := queryCount) params ringErrorSampler wideNoise
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) := by
  simp [correctResidualErasedWideView, correctStaticMaskWideView,
    correctStaticMaskJointExperiment, map_eq_bind_pure_comp, bind_assoc,
    Function.uncurry]

/-- Pointwise residual erasure at one retained source/mask pair. -/
theorem tvDist_smudge_reconstruct_fixedMaskWide_le_erasureCost
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (wideNoise : ProbComp (RLWE.Rq q degree))
    (side : CorrectMaskSide q degree ringRank params.levels lweDimension
      keySwitchLevels queryCount)
    (mask : Native.ConditionalSmudging.BootstrappingMask
      q degree ringRank params.levels lweDimension) :
    tvDist
        (PostEvaluationSmudging.smudgePublicContext wideNoise
          (reconstructPublicContext params side mask))
        (fixedMaskWidePublicContext params wideNoise
          (correctStaticMaskSideOfCorrectMaskSide side) mask) ≤
      Native.ConditionalSmudging.bootstrappingSmudgingCost
        wideNoise side.2.2.1 := by
  let ResidualKey := Native.ConditionalSmudging.fixedMaskResidualSmudgedKey
    wideNoise (Gadget.Base.ringGadget params) side.1 side.2.1 side.2.2.1 mask
  let WideKey := Native.ConditionalSmudging.fixedMaskWideKey
    wideNoise (Gadget.Base.ringGadget params) side.1 side.2.1 mask
  let Attach := fun bootstrappingKey :
      Native.BootstrappingKey q degree ringRank params.levels lweDimension ↦
    (bootstrappingKey, side.2.2.2)
  have hkeys : tvDist ResidualKey WideKey ≤
      Native.ConditionalSmudging.bootstrappingSmudgingCost
        wideNoise side.2.2.1 := by
    exact Native.ConditionalSmudging.tvDist_fixedMaskResidualSmudgedKey_fixedMaskWideKey_le
      wideNoise (Gadget.Base.ringGadget params) side.1 side.2.1
      side.2.2.1 mask
  have hdata := (tvDist_map_le (m := ProbComp) Attach ResidualKey WideKey).trans hkeys
  have hresidual :=
    Native.ConditionalSmudging.smudgeBootstrappingKey_assembleResidual_evalDist
      wideNoise (Gadget.Base.ringGadget params) side.1 side.2.1
      side.2.2.1 mask
  have hattached := evalDist_map_eq_of_evalDist_eq hresidual Attach
  have hleftShape :
      evalDist
          (PostEvaluationSmudging.smudgePublicContext wideNoise
            (reconstructPublicContext params side mask)) =
        evalDist
          (Attach <$>
            Native.ConditionalSmudging.smudgeBootstrappingKey wideNoise
              (Native.ConditionalSmudging.assembleResidualBootstrappingKey
                q degree ringRank params.levels lweDimension
                (Gadget.Base.ringGadget params) side.1 side.2.1 side.2.2.1 mask)) := by
    simp [PostEvaluationSmudging.smudgePublicContext,
      reconstructPublicContext, Attach, map_eq_bind_pure_comp]
  have hrightShape :
      evalDist
          (fixedMaskWidePublicContext params wideNoise
            (correctStaticMaskSideOfCorrectMaskSide side) mask) =
        evalDist (Attach <$> WideKey) := by
    simp [fixedMaskWidePublicContext, correctStaticMaskSideOfCorrectMaskSide,
      WideKey, Attach, map_eq_bind_pure_comp]
  unfold tvDist at hdata ⊢
  rw [hleftShape, hrightShape, hattached]
  exact hdata

/-- Averaging the pointwise Gaussian translations erases the entire narrow residual before the
mask marginal is replaced. -/
theorem tvDist_correctResidualSmudgedView_erasedWideView_le
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler wideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    tvDist
        (correctResidualSmudgedView (ringRank := ringRank)
          (queryCount := queryCount) params ringErrorSampler wideNoise
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
        (correctResidualErasedWideView (ringRank := ringRank)
          (queryCount := queryCount) params ringErrorSampler wideNoise
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) ≤
      correctResidualErasureCost (ringRank := ringRank)
        (queryCount := queryCount) params ringErrorSampler wideNoise
        keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate := by
  let Joint := correctMaskJointExperiment (ringRank := ringRank)
    (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
    inputErrorSampler keySwitchGadget coordinate
  let JointValue :=
    CorrectMaskSide q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount ×
      Native.ConditionalSmudging.BootstrappingMask
        q degree ringRank params.levels lweDimension
  let Left : JointValue →
      ProbComp (PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount) :=
    fun value ↦ PostEvaluationSmudging.smudgePublicContext wideNoise
      (reconstructPublicContext params value.1 value.2)
  let Right : JointValue →
      ProbComp (PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount) :=
    fun value ↦ fixedMaskWidePublicContext params wideNoise
      (correctStaticMaskSideOfCorrectMaskSide value.1) value.2
  have havg := FormalProof4FHE.FiniteProduct.tvDist_bind_left_le_expectation
    Joint Left Right
  calc
    tvDist
        (correctResidualSmudgedView (ringRank := ringRank)
          (queryCount := queryCount) params ringErrorSampler wideNoise
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
        (correctResidualErasedWideView (ringRank := ringRank)
          (queryCount := queryCount) params ringErrorSampler wideNoise
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) ≤
      ∑' value, Pr[= value | Joint].toReal * tvDist (Left value) (Right value) := by
        simpa only [correctResidualSmudgedView, correctResidualErasedWideView,
          Joint, Left, Right] using havg
    _ ≤ ∑' value, Pr[= value | Joint].toReal *
        Native.ConditionalSmudging.bootstrappingSmudgingCost
          wideNoise value.1.2.2.1 := by
      rw [tsum_fintype, tsum_fintype]
      apply Finset.sum_le_sum
      intro value _
      exact mul_le_mul_of_nonneg_left
        (tvDist_smudge_reconstruct_fixedMaskWide_le_erasureCost
          params wideNoise value.1 value.2) ENNReal.toReal_nonneg
    _ = correctResidualErasureCost (ringRank := ringRank)
        (queryCount := queryCount) params ringErrorSampler wideNoise
        keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate := by
      rfl

/-- Reordered post-smudging hybrid.  Its mask premise no longer conditions on the complete narrow
residual: that residual has already been paid for by the explicit Gaussian translation cost. -/
theorem tvDist_averagedPostSmudgedCorrectTransform_staticMaskIndependent_le
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ}
    [NeZero q] [NeZero degree]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler wideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) (ε : ℝ)
    (hcollision : CorrectStaticMaskConditionalCollisionBound
      (ringRank := ringRank) (queryCount := queryCount) params ringErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate ε) :
    tvDist
        (PostEvaluationSmudging.averagedCorrectTransform
          (ringRank := ringRank) (queryCount := queryCount) params
          ringErrorSampler wideNoise keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate)
        (correctStaticMaskIndependentWideView (ringRank := ringRank)
          (queryCount := queryCount) params ringErrorSampler wideNoise
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) ≤
      correctResidualErasureCost (ringRank := ringRank)
          (queryCount := queryCount) params ringErrorSampler wideNoise
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate +
        Real.sqrt ε / 2 := by
  let Actual := correctResidualSmudgedView (ringRank := ringRank)
    (queryCount := queryCount) params ringErrorSampler wideNoise
    keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
  let Erased := correctStaticMaskWideView (ringRank := ringRank)
    (queryCount := queryCount) params ringErrorSampler wideNoise
    keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
  let Independent := correctStaticMaskIndependentWideView (ringRank := ringRank)
    (queryCount := queryCount) params ringErrorSampler wideNoise
    keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
  have herase : tvDist Actual Erased ≤
      correctResidualErasureCost (ringRank := ringRank)
        (queryCount := queryCount) params ringErrorSampler wideNoise
        keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate := by
    have h := tvDist_correctResidualSmudgedView_erasedWideView_le
      (ringRank := ringRank) (queryCount := queryCount) params
      ringErrorSampler wideNoise keySwitchErrorSampler inputErrorSampler
      keySwitchGadget coordinate
    unfold tvDist at h ⊢
    rw [correctResidualErasedWideView_evalDist_eq_correctStaticMaskWideView
      (ringRank := ringRank) (queryCount := queryCount) params
      ringErrorSampler wideNoise keySwitchErrorSampler inputErrorSampler
      keySwitchGadget coordinate] at h
    exact h
  have hmask : tvDist Erased Independent ≤ Real.sqrt ε / 2 :=
    tvDist_correctStaticMaskWideView_independent_le_sqrt_of_collisionBound
      (ringRank := ringRank) (queryCount := queryCount) params
      ringErrorSampler wideNoise keySwitchErrorSampler inputErrorSampler
      keySwitchGadget coordinate ε hcollision
  have htriangle := (tvDist_triangle Actual Erased Independent).trans
    (add_le_add herase hmask)
  unfold tvDist at htriangle ⊢
  rw [correctResidualSmudgedView_evalDist_eq_averagedCorrectTransform
    (ringRank := ringRank) (queryCount := queryCount) params
    ringErrorSampler wideNoise keySwitchErrorSampler inputErrorSampler
    keySwitchGadget coordinate] at htriangle
  exact htriangle

/-- Static side extracted directly from one latent source and evaluator coin.  Unlike
`correctMaskSide`, this definition never constructs the narrow residual. -/
def correctStaticMaskSideAtSourceCoin
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ}
    (params : Gadget.Base.Parameters q)
    (source : Secret lweDimension ringRank degree ×
      PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount)
    (coin : Coin q degree ringRank params.levels lweDimension) :
    CorrectStaticMaskSide q degree ringRank lweDimension
      keySwitchLevels queryCount :=
  let targetSecret :=
    Native.ScalarSecretRandomization.maskedSecret source.1.1 coin.1
  let auxiliary : Auxiliary q ringRank degree lweDimension
      keySwitchLevels queryCount :=
    ((transportedView params source.2.1 source.2.2 coin.1).1.2,
      (transportedView params source.2.1 source.2.2 coin.1).2)
  (targetSecret, source.1.2, auxiliary)

@[simp]
theorem correctStaticMaskSideOfCorrectMaskSide_correctMaskSide
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ}
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension)
    (source : Secret lweDimension ringRank degree ×
      PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount)
    (coin : Coin q degree ringRank params.levels lweDimension) :
    correctStaticMaskSideOfCorrectMaskSide
        (correctMaskSide params coordinate source coin) =
      correctStaticMaskSideAtSourceCoin params source coin := by
  rfl

/-- For one latent source and evaluator coin, refreshing the complete mask after residual erasure
is exactly native monomial BRK generation at the transformed target secret. -/
theorem freshMask_fixedMaskWidePublicContext_evalDist_eq_coupledMonomialViewAtSourceCoin
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (wideNoise : ProbComp (RLWE.Rq q degree))
    (source : Secret lweDimension ringRank degree ×
      PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount)
    (coin : Coin q degree ringRank params.levels lweDimension) :
    evalDist
        (Native.ConditionalSmudging.sampleFreshBootstrappingMask
            q degree ringRank params.levels lweDimension >>=
          fixedMaskWidePublicContext params wideNoise
            (correctStaticMaskSideAtSourceCoin params source coin)) =
      evalDist
        (coupledMonomialViewAtSourceCoin params wideNoise source coin) := by
  let targetSecret :=
    Native.ScalarSecretRandomization.maskedSecret source.1.1 coin.1
  let auxiliary : Auxiliary q ringRank degree lweDimension
      keySwitchLevels queryCount :=
    ((transportedView params source.2.1 source.2.2 coin.1).1.2,
      (transportedView params source.2.1 source.2.2 coin.1).2)
  let FreshKey :=
    Native.ConditionalSmudging.sampleFreshBootstrappingMask
        q degree ringRank params.levels lweDimension >>=
      Native.ConditionalSmudging.fixedMaskWideKey wideNoise
        (Gadget.Base.ringGadget params) targetSecret source.1.2
  let MonomialKey :=
    Native.BootstrapSecurity.MonomialKDM.generateBootstrappingKey
      q degree ringRank params.levels lweDimension wideNoise
      (Gadget.Base.ringGadget params) targetSecret source.1.2
  let Attach := fun bootstrappingKey :
      Native.BootstrappingKey q degree ringRank params.levels lweDimension ↦
    (bootstrappingKey, auxiliary)
  have hkey : evalDist FreshKey = evalDist MonomialKey := by
    simpa only [FreshKey, MonomialKey] using
      (Native.ConditionalSmudging.sampleFreshBootstrappingMask_fixedMaskWideKey_evalDist_eq_generateMonomial
        q degree ringRank params.levels lweDimension wideNoise
        (Gadget.Base.ringGadget params) targetSecret source.1.2)
  have hattached := evalDist_map_eq_of_evalDist_eq hkey Attach
  simpa [fixedMaskWidePublicContext, correctStaticMaskSideAtSourceCoin,
    coupledMonomialViewAtSourceCoin, targetSecret, auxiliary, FreshKey,
    MonomialKey, Attach, map_eq_bind_pure_comp] using hattached

/-- Averaging the fixed-source identity identifies the residual-free independent-mask view with
the existing coupled monomial endpoint. -/
theorem correctStaticMaskIndependentWideView_centeredBinomial_evalDist_eq_coupledAveragedMonomial
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (wideNoise : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    evalDist
        (correctStaticMaskIndependentWideView (degree := degree + 1)
          (ringRank := ringRank) (queryCount := queryCount) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) =
      evalDist
        (coupledAveragedMonomialRealView (degree := degree)
          (ringRank := ringRank) (queryCount := queryCount) (eta := eta)
          params wideNoise keySwitchErrorSampler inputErrorSampler
          keySwitchGadget) := by
  let Source := pairedSource (ringRank := ringRank)
    (lweDimension := lweDimension) (queryCount := queryCount)
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
    keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
    keySwitchGadget
  let Coins := sampleCoin q (degree + 1) ringRank params.levels lweDimension
  let Masks := Native.ConditionalSmudging.sampleFreshBootstrappingMask
    q (degree + 1) ringRank params.levels lweDimension
  let UniformMasks : ProbComp
      (Native.ConditionalSmudging.BootstrappingMask
        q (degree + 1) ringRank params.levels lweDimension) :=
    $ᵗ (Native.ConditionalSmudging.BootstrappingMask
      q (degree + 1) ringRank params.levels lweDimension)
  have hMasks : evalDist UniformMasks = evalDist Masks := by
    simpa only [UniformMasks, Masks] using
      (Native.ConditionalSmudging.sampleFreshBootstrappingMask_evalDist_eq_uniform
        q (degree + 1) ringRank params.levels lweDimension).symm
  calc
    evalDist
        (correctStaticMaskIndependentWideView (degree := degree + 1)
          (ringRank := ringRank) (queryCount := queryCount) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) =
      evalDist (Source >>= fun source ↦
        Coins >>= fun coin ↦
          UniformMasks >>= fixedMaskWidePublicContext params wideNoise
            (correctStaticMaskSideAtSourceCoin params source coin)) := by
      simp [correctStaticMaskIndependentWideView,
        correctStaticMaskIndependentExperiment,
        FormalProof4FHE.ConditionalCollision.sideIndependentOutput,
        correctStaticMaskJointExperiment, correctMaskJointExperiment,
        Source, Coins, UniformMasks,
        map_eq_bind_pure_comp, bind_assoc,
        Function.uncurry]
    _ = evalDist (Source >>= fun source ↦
        Coins >>= fun coin ↦
          Masks >>= fixedMaskWidePublicContext params wideNoise
            (correctStaticMaskSideAtSourceCoin params source coin)) := by
      refine evalDist_bind_congr' Source fun source ↦ ?_
      refine evalDist_bind_congr' Coins fun coin ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        hMasks (fixedMaskWidePublicContext params wideNoise
          (correctStaticMaskSideAtSourceCoin params source coin))
    _ = evalDist (Source >>= fun source ↦
        Coins >>= fun coin ↦
          coupledMonomialViewAtSourceCoin params wideNoise source coin) := by
      refine evalDist_bind_congr' Source fun source ↦ ?_
      refine evalDist_bind_congr' Coins fun coin ↦ ?_
      exact freshMask_fixedMaskWidePublicContext_evalDist_eq_coupledMonomialViewAtSourceCoin
        params wideNoise source coin
    _ = evalDist
        (coupledAveragedMonomialRealView (degree := degree)
          (ringRank := ringRank) (queryCount := queryCount) (eta := eta)
          params wideNoise keySwitchErrorSampler inputErrorSampler
          keySwitchGadget) := by
      rfl

/-- The residual-free independent-mask view is exactly the ordinary augmented real TFHE public
view at the chosen wide ring-error law. -/
theorem correctStaticMaskIndependentWideView_centeredBinomial_evalDist_eq_realPublicView
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (wideNoise : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    evalDist
        (correctStaticMaskIndependentWideView (degree := degree + 1)
          (ringRank := ringRank) (queryCount := queryCount) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) =
      evalDist
        (realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) wideNoise keySwitchErrorSampler
          inputErrorSampler (Gadget.Base.ringGadget params) keySwitchGadget) :=
  (correctStaticMaskIndependentWideView_centeredBinomial_evalDist_eq_coupledAveragedMonomial
      (degree := degree) (ringRank := ringRank) (queryCount := queryCount)
      (eta := eta) params wideNoise keySwitchErrorSampler inputErrorSampler
      keySwitchGadget coordinate).trans
    (coupledAveragedMonomialRealView_evalDist_eq_realPublicView
      (degree := degree) (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) (eta := eta) params wideNoise
      keySwitchErrorSampler inputErrorSampler keySwitchGadget)

/-- Security-only post-smudging endpoint.  For centered-binomial native errors, the evaluator's
correct branch is close to the ordinary real TFHE public view using only the explicit residual
translation cost and the residual-free static-mask collision certificate.  No decryption or
correctness premise occurs in this statement. -/
theorem tvDist_averagedPostSmudgedCorrectTransform_centeredBinomial_realPublicView_le
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (wideNoise : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) (ε : ℝ)
    (hcollision : CorrectStaticMaskConditionalCollisionBound
      (degree := degree + 1) (ringRank := ringRank) (queryCount := queryCount)
      params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate ε) :
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
        Real.sqrt ε / 2 := by
  have h := tvDist_averagedPostSmudgedCorrectTransform_staticMaskIndependent_le
    (degree := degree + 1) (ringRank := ringRank) (queryCount := queryCount)
    params (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
    keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate ε
    hcollision
  unfold tvDist at h ⊢
  rw [correctStaticMaskIndependentWideView_centeredBinomial_evalDist_eq_realPublicView
    (degree := degree) (ringRank := ringRank) (lweDimension := lweDimension)
    (queryCount := queryCount) (eta := eta) params wideNoise
    keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate] at h
  exact h

end

end FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery.AugmentedResidual.NativeShifted.FullMaskCollision
