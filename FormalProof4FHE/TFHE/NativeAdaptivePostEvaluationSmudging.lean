/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeAdaptiveShiftedCandidateEvaluator
import FormalProof4FHE.TFHE.NativeConditionalSmudging
import FormalProof4FHE.TFHE.NativeCoupledShiftedResidualBounds

/-!
# Post-Evaluation Smudging for the Adaptive Native TFHE Candidate View

The CircLWE search-to-decision strategy adds independent wide noise after homomorphically
computing a candidate public view.  Merely comparing the evaluator's narrow residual with a wide
target sampler is a different experiment and can have statistical distance close to one.

This module installs the executable post-evaluation operation at the complete adaptive public-view
boundary.  It proves two exact facts needed by the security reduction:

* the operation is the native candidate transform followed by fresh BRK body noise; and
* post-evaluation smudging leaves the uniform-BRK endpoint exactly unchanged.

Consequently every established wrong-candidate distance bound survives post-evaluation smudging
without an additional loss.  The correct branch can now be connected separately to the existing
conditional residual-smudging theorems.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery.AugmentedResidual.NativeShifted.PostEvaluationSmudging

noncomputable section

open FormalProof4FHE.TFHE
open Native
open FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery

/-- Add independent wide noise to every BRK body in a complete public context, retaining the KSK
and adaptive input tape verbatim. -/
def smudgePublicContext
    {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ}
    (wideNoise : ProbComp (RLWE.Rq q degree))
    (context : PublicContext q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount) :
    ProbComp (PublicContext q degree ringRank tgswLevels lweDimension
      keySwitchLevels queryCount) := do
  let bootstrappingKey ←
    Native.ConditionalSmudging.smudgeBootstrappingKey wideNoise context.1
  return (bootstrappingKey, context.2)

/-- The concrete native shifted evaluator followed by fresh wide BRK body noise. -/
def transform
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (wideNoise : ProbComp (RLWE.Rq q degree))
    (coordinate : Fin lweDimension) (candidate : Bool)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount) :
    ProbComp
      (PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount) := do
  let context ← NativeShifted.transform params coordinate candidate challenge auxiliary
  smudgePublicContext wideNoise context

/-- Smudging after an already averaged correct-candidate view. -/
def averagedCorrectTransform
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceRingErrorSampler wideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    ProbComp
      (PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount) :=
  NativeShifted.averagedCorrectTransform (ringRank := ringRank)
      (queryCount := queryCount) params sourceRingErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate >>=
    smudgePublicContext wideNoise

/-- Smudging after an already averaged complementary-candidate view. -/
def averagedWrongTransform
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceRingErrorSampler wideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    ProbComp
      (PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount) :=
  NativeShifted.averagedWrongTransform (ringRank := ringRank)
      (queryCount := queryCount) params sourceRingErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate >>=
    smudgePublicContext wideNoise

/-- Averaging the post-smudged per-context correct transform is exactly postprocessing the
existing averaged correct view. -/
theorem averaged_transform_correct_evalDist
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceRingErrorSampler wideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    evalDist (do
        let hiddenAndContext ← coordinateSource
          (ringRank := ringRank) (queryCount := queryCount)
          sourceRingErrorSampler keySwitchErrorSampler inputErrorSampler
          (Gadget.Base.ringGadget params) keySwitchGadget coordinate
        transform params wideNoise coordinate hiddenAndContext.1
          hiddenAndContext.2.1 hiddenAndContext.2.2) =
      evalDist
        (averagedCorrectTransform (ringRank := ringRank) (queryCount := queryCount)
          params sourceRingErrorSampler wideNoise keySwitchErrorSampler
          inputErrorSampler keySwitchGadget coordinate) := by
  simp [transform, averagedCorrectTransform,
    NativeShifted.averagedCorrectTransform, monad_norm]

/-- The analogous identity for the complementary candidate. -/
theorem averaged_transform_wrong_evalDist
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceRingErrorSampler wideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    evalDist (do
        let hiddenAndContext ← coordinateSource
          (ringRank := ringRank) (queryCount := queryCount)
          sourceRingErrorSampler keySwitchErrorSampler inputErrorSampler
          (Gadget.Base.ringGadget params) keySwitchGadget coordinate
        transform params wideNoise coordinate (!hiddenAndContext.1)
          hiddenAndContext.2.1 hiddenAndContext.2.2) =
      evalDist
        (averagedWrongTransform (ringRank := ringRank) (queryCount := queryCount)
          params sourceRingErrorSampler wideNoise keySwitchErrorSampler
          inputErrorSampler keySwitchGadget coordinate) := by
  simp [transform, averagedWrongTransform,
    NativeShifted.averagedWrongTransform, monad_norm]

/-! ## Exact factorization through a zero-noise residual key -/

/-- At one fixed latent source and evaluator coin, generating the coupled residual key with zero
fresh error and then applying post-evaluation smudging is exactly the coupled residual key with
the wide error sampled during generation.  The transported KSK and input tape remain verbatim. -/
theorem coupledResidualViewAtSourceCoin_zero_then_smudge_evalDist
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ}
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (wideNoise : ProbComp (RLWE.Rq q degree))
    (coordinate : Fin lweDimension)
    (source : Secret lweDimension ringRank degree ×
      PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount)
    (coin : Coin q degree ringRank params.levels lweDimension) :
    evalDist
        (coupledResidualViewAtSourceCoin params
            (pure (Native.ConditionalSmudging.ringAdditiveZero q degree))
            coordinate source coin >>=
          smudgePublicContext wideNoise) =
      evalDist
        (coupledResidualViewAtSourceCoin params wideNoise coordinate source coin) := by
  let targetSecret :=
    Native.ScalarSecretRandomization.maskedSecret source.1.1 coin.1
  let residual :=
    (correctResidualAtTarget params coordinate targetSecret
      source.2.1 source.2.2 source.1.2 coin).1
  let ZeroKey :=
    Native.ConditionalSmudging.generateResidualBootstrappingKey
      q degree ringRank params.levels lweDimension
      (pure (Native.ConditionalSmudging.ringAdditiveZero q degree))
      (Gadget.Base.ringGadget params) targetSecret source.1.2 residual
  let WideKey :=
    Native.ConditionalSmudging.generateResidualBootstrappingKey
      q degree ringRank params.levels lweDimension wideNoise
      (Gadget.Base.ringGadget params) targetSecret source.1.2 residual
  let Smudge := Native.ConditionalSmudging.smudgeBootstrappingKey
    (ringRank := ringRank) (tgswLevels := params.levels)
    (lweDimension := lweDimension) wideNoise
  let auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount :=
    ((transportedView params source.2.1 source.2.2 coin.1).1.2,
      (transportedView params source.2.1 source.2.2 coin.1).2)
  let finish := fun bootstrappingKey :
      Native.BootstrappingKey q degree ringRank params.levels lweDimension ↦
    (pure (bootstrappingKey, auxiliary) :
      ProbComp (PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount))
  have hKey : evalDist (ZeroKey >>= Smudge) = evalDist WideKey := by
    simpa only [ZeroKey, WideKey, Smudge] using
      (Native.ConditionalSmudging.generateResidualBootstrappingKey_zero_then_smudge_evalDist
        q degree ringRank params.levels lweDimension wideNoise
        (Gadget.Base.ringGadget params) targetSecret source.1.2 residual)
  have hFinish := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    hKey finish
  simpa [coupledResidualViewAtSourceCoin, smudgePublicContext, targetSecret,
    residual, ZeroKey, WideKey, Smudge, auxiliary, finish, bind_assoc,
    monad_norm] using hFinish

/-- Averaged coupled residual view with a fresh uniform mask but no fresh row error.  Its phase is
the exact correct-evaluator residual, so the distance to the actual correct view isolates the
remaining public-mask/residual correlation before wide-noise data processing. -/
noncomputable def coupledAveragedZeroNoiseResidualRealView
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ}
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    ProbComp
      (PublicContext q (degree + 1) ringRank params.levels lweDimension
        keySwitchLevels queryCount) :=
  coupledAveragedResidualRealView (ringRank := ringRank)
    (queryCount := queryCount) (eta := eta) params
    (pure (Native.ConditionalSmudging.ringAdditiveZero q (degree + 1)))
    keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate

/-- Averaging the fixed-source identity proves that post-smudging the zero-noise residual view
is exactly the wide-noise coupled residual endpoint. -/
theorem coupledAveragedZeroNoiseResidualRealView_smudge_evalDist
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ}
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (wideNoise : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    evalDist
        (coupledAveragedZeroNoiseResidualRealView
            (ringRank := ringRank) (queryCount := queryCount) (eta := eta)
            params keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate >>=
          smudgePublicContext wideNoise) =
      evalDist
        (coupledAveragedResidualRealView (ringRank := ringRank)
          (queryCount := queryCount) (eta := eta) params wideNoise
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) := by
  let Source := pairedSource (ringRank := ringRank) (lweDimension := lweDimension)
    (queryCount := queryCount)
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
    keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
    keySwitchGadget
  let Coins := sampleCoin q (degree + 1) ringRank params.levels lweDimension
  unfold coupledAveragedZeroNoiseResidualRealView coupledAveragedResidualRealView
  simp only [bind_assoc]
  refine evalDist_bind_congr' Source fun source ↦ ?_
  refine evalDist_bind_congr' Coins fun coin ↦ ?_
  exact coupledResidualViewAtSourceCoin_zero_then_smudge_evalDist
    params wideNoise coordinate source coin

/-- **Mask-only post-smudging normal form.**  The wide-noise correct-view distance is bounded by
the distance from the original evaluator to the zero-noise coupled residual view.  Thus the
Gaussian layer adds no new normal-form premise: it is a common public Markov kernel applied after
all remaining mask/residual correlation. -/
theorem tvDist_averagedCorrectTransform_coupledResidual_le_zeroNoiseNormalForm
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ}
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (wideNoise : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    tvDist
        (averagedCorrectTransform (ringRank := ringRank) (queryCount := queryCount)
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta) wideNoise
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
        (coupledAveragedResidualRealView (ringRank := ringRank)
          (queryCount := queryCount) (eta := eta) params wideNoise
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) ≤
      tvDist
        (NativeShifted.averagedCorrectTransform
          (ringRank := ringRank) (queryCount := queryCount) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
        (coupledAveragedZeroNoiseResidualRealView
          (ringRank := ringRank) (queryCount := queryCount) (eta := eta)
          params keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate) := by
  let Correct := NativeShifted.averagedCorrectTransform
    (ringRank := ringRank) (queryCount := queryCount) params
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
    keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
  let ZeroResidual := coupledAveragedZeroNoiseResidualRealView
    (degree := degree) (ringRank := ringRank) (queryCount := queryCount) (eta := eta)
    params keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
  have hData := tvDist_bind_right_le (m := ProbComp)
    (smudgePublicContext wideNoise) Correct ZeroResidual
  unfold tvDist at hData ⊢
  rw [coupledAveragedZeroNoiseResidualRealView_smudge_evalDist
    (ringRank := ringRank) (queryCount := queryCount) (eta := eta)
    params wideNoise keySwitchErrorSampler inputErrorSampler keySwitchGadget
    coordinate] at hData
  simpa only [averagedCorrectTransform, Correct, ZeroResidual] using hData

/-- Post-evaluation body smudging leaves the complete uniform-BRK public endpoint exactly
unchanged, including its correlated real KSK and adaptive input tape. -/
theorem uniformPublicView_smudge_evalDist
    {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ}
    [NeZero q]
    (ringErrorSampler wideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    evalDist
        (uniformPublicView (ringRank := ringRank)
            (lweDimension := lweDimension) (queryCount := queryCount)
            ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget keySwitchGadget >>=
          smudgePublicContext wideNoise) =
      evalDist
        (uniformPublicView (ringRank := ringRank)
          (lweDimension := lweDimension) (queryCount := queryCount)
          ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget) := by
  let Problem := KeySwitchFirstFiniteView.augmentedCircularProblem
    (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
    ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget
  let Secrets := Problem.sampleSecret
  let Uniform : ProbComp
      (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension) :=
    $ᵗ (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
  let AuxSampler := fun secrets ↦ Problem.sampleAuxiliary secrets
  let Smudge := Native.ConditionalSmudging.smudgeBootstrappingKey
    (ringRank := ringRank) (tgswLevels := tgswLevels)
    (lweDimension := lweDimension) wideNoise
  let finish := fun
      (bootstrappingKey : Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount) ↦
    (pure (bootstrappingKey, auxiliary) :
      ProbComp (PublicContext q degree ringRank tgswLevels lweDimension
        keySwitchLevels queryCount))
  have hUniform : evalDist (Uniform >>= Smudge) = evalDist Uniform := by
    simpa only [Uniform, Smudge] using
      (Native.ConditionalSmudging.smudge_uniformBootstrappingKey_evalDist
        (ringRank := ringRank) (tgswLevels := tgswLevels)
        (lweDimension := lweDimension) wideNoise)
  unfold uniformPublicView smudgePublicContext
  simp only [bind_assoc, pure_bind]
  change evalDist (Secrets >>= fun secrets ↦
      Uniform >>= fun bootstrappingKey ↦
      AuxSampler secrets >>= fun auxiliary ↦
      Smudge bootstrappingKey >>= fun smudgedKey ↦
      finish smudgedKey auxiliary) =
    evalDist (Secrets >>= fun secrets ↦
      Uniform >>= fun bootstrappingKey ↦
      AuxSampler secrets >>= fun auxiliary ↦
      finish bootstrappingKey auxiliary)
  refine evalDist_bind_congr' Secrets fun secrets ↦ ?_
  calc
    _ = evalDist (AuxSampler secrets >>= fun auxiliary ↦
          (Uniform >>= Smudge) >>= fun bootstrappingKey ↦
          finish bootstrappingKey auxiliary) := by
      simp only [bind_assoc]
      exact evalDist_bind_bind_swap Uniform (AuxSampler secrets)
        (fun bootstrappingKey auxiliary ↦
          Smudge bootstrappingKey >>= fun smudgedKey ↦
          finish smudgedKey auxiliary)
    _ = evalDist (AuxSampler secrets >>= fun auxiliary ↦
          Uniform >>= fun bootstrappingKey ↦
          finish bootstrappingKey auxiliary) := by
      refine evalDist_bind_congr' (AuxSampler secrets) fun auxiliary ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        hUniform (fun bootstrappingKey ↦ finish bootstrappingKey auxiliary)
    _ = _ := by
      exact evalDist_bind_bind_swap (AuxSampler secrets) Uniform
        (fun auxiliary bootstrappingKey ↦ finish bootstrappingKey auxiliary)

/-- Data processing plus exact uniform invariance: post-evaluation smudging never worsens a
wrong-candidate distance to the uniform public endpoint. -/
theorem tvDist_smudgePublicContext_uniformPublicView_le
    {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ}
    [NeZero q]
    (source : ProbComp
      (PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount))
    (ringErrorSampler wideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    tvDist
        (source >>= smudgePublicContext wideNoise)
        (uniformPublicView (ringRank := ringRank)
          (lweDimension := lweDimension) (queryCount := queryCount)
          ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget) ≤
      tvDist source
        (uniformPublicView (ringRank := ringRank)
          (lweDimension := lweDimension) (queryCount := queryCount)
          ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget) := by
  have hdata := tvDist_bind_right_le (m := ProbComp)
    (smudgePublicContext wideNoise) source
    (uniformPublicView (ringRank := ringRank)
      (lweDimension := lweDimension) (queryCount := queryCount)
      ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget)
  unfold tvDist at hdata ⊢
  rw [uniformPublicView_smudge_evalDist ringErrorSampler wideNoise
    keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget] at hdata
  exact hdata

/-- Every averaged wrong-view bound for the original native evaluator is inherited unchanged by
the post-smudged evaluator. -/
theorem tvDist_averagedWrongTransform_uniformPublicView_le
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceRingErrorSampler wideNoise : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) (bound : ℝ)
    (hbound :
      tvDist
          (NativeShifted.averagedWrongTransform (ringRank := ringRank)
            (queryCount := queryCount) params sourceRingErrorSampler
            keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
          (uniformPublicView (ringRank := ringRank)
            (lweDimension := lweDimension) (queryCount := queryCount)
            sourceRingErrorSampler keySwitchErrorSampler inputErrorSampler
            (Gadget.Base.ringGadget params) keySwitchGadget) ≤ bound) :
    tvDist
        (averagedWrongTransform (ringRank := ringRank) (queryCount := queryCount)
          params sourceRingErrorSampler wideNoise keySwitchErrorSampler
          inputErrorSampler keySwitchGadget coordinate)
        (uniformPublicView (ringRank := ringRank)
          (lweDimension := lweDimension) (queryCount := queryCount)
          sourceRingErrorSampler keySwitchErrorSampler inputErrorSampler
          (Gadget.Base.ringGadget params) keySwitchGadget) ≤ bound :=
  (tvDist_smudgePublicContext_uniformPublicView_le
      (NativeShifted.averagedWrongTransform (ringRank := ringRank)
        (queryCount := queryCount) params sourceRingErrorSampler
        keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
      sourceRingErrorSampler wideNoise keySwitchErrorSampler inputErrorSampler
      (Gadget.Base.ringGadget params) keySwitchGadget).trans hbound

end

end FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery.AugmentedResidual.NativeShifted.PostEvaluationSmudging
