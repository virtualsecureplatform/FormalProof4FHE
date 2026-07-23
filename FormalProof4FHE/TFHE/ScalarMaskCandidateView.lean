/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AveragedCandidateView
import FormalProof4FHE.TFHE.AuxiliaryInputCircularSearch

/-!
# Native Scalar-Mask Candidate Views

This module audits the exact scalar-secret randomization step of the CircLWE
search-to-decision strategy in the native TFHE public experiment.  With centered-binomial
ring noise, XOR-masking a uniformly sampled scalar key and applying the corresponding public
BRK+KSK transport preserves the complete real public-view distribution exactly.

The transport deliberately ignores a proposed coordinate candidate.  Consequently it gives an
exact correct-candidate averaged view, but its wrong-candidate view is still the real endpoint,
not the uniform-BRK endpoint.  The final zero-gap theorem records the resulting obstruction:
postcomposing this scalar-only transport with any public distinguisher yields no candidate-check
signal.  A full native CircLWE reduction must add the shifted-function evaluation/rank-freshness
step that turns a wrong candidate into the uniform endpoint.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.ScalarMaskCandidateView

/-- Apply the checked scalar-key XOR transport to a complete native BRK+KSK context. -/
noncomputable def transformContext
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ}
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (mask : BinarySecret lweDimension)
    (context : PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels :=
  ScalarSecretRandomization.transformEvaluationKeyPair tgswGadget mask context

/-- Sample a fresh uniform scalar mask and transport the supplied public context. -/
noncomputable def randomizeContext
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ}
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (context : PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels) :
    ProbComp (PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels) := do
  let mask ← $ᵗ BinarySecret lweDimension
  return transformContext tgswGadget mask context

/-- The real public view factored into uniform scalar and ring secrets followed by the
fixed-secret native view. -/
theorem realPublicView_eq_sample_fixedSecretRealView
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget =
      (do
        let lweSecret ← $ᵗ BinarySecret lweDimension
        let ringSecret ← $ᵗ RingBinarySecret ringRank degree
        fixedSecretRealView q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
          (lweSecret, ringSecret)) := by
  simp [realPublicView, problem, LWE.AuxiliaryInput.Search.exactRecoveryProblem,
    AuxiliaryInput.problem, fixedSecretRealView, Native.sampleLweSecret,
    Native.sampleRingSecret, monad_norm]

/-- A fixed public scalar mask preserves the complete real BRK+KSK distribution after averaging
over the native uniform scalar key.  The ring key remains fixed during the scalar transport and
is averaged only outside the fixed-key identity. -/
theorem transform_realPublicView_centeredBinomial_evalDist
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta : ℕ}
    [NeZero q]
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (mask : BinarySecret lweDimension) :
    evalDist
        (transformContext tgswGadget mask <$>
          realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
            (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
            keySwitchErrorSampler tgswGadget keySwitchGadget) =
      evalDist
        (realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
          keySwitchErrorSampler tgswGadget keySwitchGadget) := by
  rw [realPublicView_eq_sample_fixedSecretRealView]
  simp only [map_eq_bind_pure_comp, bind_assoc]
  calc
    _ = evalDist (($ᵗ RingBinarySecret ringRank (degree + 1)) >>= fun ringSecret ↦
        ($ᵗ BinarySecret lweDimension) >>= fun lweSecret ↦
          fixedSecretRealView q (degree + 1) ringRank tgswLevels lweDimension
              keySwitchLevels (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
              keySwitchErrorSampler tgswGadget keySwitchGadget (lweSecret, ringSecret) >>=
            fun view ↦ pure (transformContext tgswGadget mask view)) :=
      evalDist_bind_bind_swap
        ($ᵗ BinarySecret lweDimension)
        ($ᵗ RingBinarySecret ringRank (degree + 1)) _
    _ = evalDist (($ᵗ RingBinarySecret ringRank (degree + 1)) >>= fun ringSecret ↦
        ($ᵗ BinarySecret lweDimension) >>= fun lweSecret ↦
          fixedSecretRealView q (degree + 1) ringRank tgswLevels lweDimension
            keySwitchLevels (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
            keySwitchErrorSampler tgswGadget keySwitchGadget (lweSecret, ringSecret)) := by
      refine evalDist_bind_congr' ($ᵗ RingBinarySecret ringRank (degree + 1)) fun ringSecret ↦ ?_
      change evalDist (do
          let lweSecret ← $ᵗ BinarySecret lweDimension
          let view ← fixedSecretRealView q (degree + 1) ringRank tgswLevels
            lweDimension keySwitchLevels
            (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
            keySwitchErrorSampler tgswGadget keySwitchGadget (lweSecret, ringSecret)
          return ScalarSecretRandomization.transformEvaluationKeyPair tgswGadget mask view) =
        evalDist (do
          let lweSecret ← $ᵗ BinarySecret lweDimension
          fixedSecretRealView q (degree + 1) ringRank tgswLevels lweDimension
            keySwitchLevels (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
            keySwitchErrorSampler tgswGadget keySwitchGadget (lweSecret, ringSecret))
      exact ScalarSecretRandomization.transform_uniformSecretView_evalDist mask
        (fun lweSecret ↦
          fixedSecretRealView q (degree + 1) ringRank tgswLevels lweDimension
            keySwitchLevels (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
            keySwitchErrorSampler tgswGadget keySwitchGadget (lweSecret, ringSecret))
        (ScalarSecretRandomization.transformEvaluationKeyPair tgswGadget)
        (fun lweSecret ↦
          transform_fixedSecretRealView_centeredBinomial_evalDist
            keySwitchErrorSampler tgswGadget keySwitchGadget lweSecret mask ringSecret)
    _ = evalDist (($ᵗ BinarySecret lweDimension) >>= fun lweSecret ↦
        ($ᵗ RingBinarySecret ringRank (degree + 1)) >>= fun ringSecret ↦
          fixedSecretRealView q (degree + 1) ringRank tgswLevels lweDimension
            keySwitchLevels (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
            keySwitchErrorSampler tgswGadget keySwitchGadget (lweSecret, ringSecret)) :=
      (evalDist_bind_bind_swap
        ($ᵗ BinarySecret lweDimension)
        ($ᵗ RingBinarySecret ringRank (degree + 1)) _).symm

/-- Sampling the scalar mask after the real context preserves the complete real public view
exactly. -/
theorem randomize_realPublicView_centeredBinomial_evalDist
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta : ℕ}
    [NeZero q]
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    evalDist (do
        let context ← realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
          keySwitchErrorSampler tgswGadget keySwitchGadget
        randomizeContext tgswGadget context) =
      evalDist
        (realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
          keySwitchErrorSampler tgswGadget keySwitchGadget) := by
  let realView := realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
    (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
    keySwitchErrorSampler tgswGadget keySwitchGadget
  let masks : ProbComp (BinarySecret lweDimension) := $ᵗ BinarySecret lweDimension
  change evalDist (realView >>= fun context ↦
      masks >>= fun mask ↦ pure (transformContext tgswGadget mask context)) =
    evalDist realView
  calc
    _ = evalDist (masks >>= fun mask ↦
        realView >>= fun context ↦ pure (transformContext tgswGadget mask context)) :=
      evalDist_bind_bind_swap realView masks _
    _ = evalDist (masks >>= fun _ ↦ realView) := by
      refine evalDist_bind_congr' masks fun mask ↦ ?_
      dsimp only [realView]
      simpa only [map_eq_bind_pure_comp, Function.comp_def] using
        (transform_realPublicView_centeredBinomial_evalDist
          (ringRank := ringRank) (ringEta := ringEta)
          keySwitchErrorSampler tgswGadget keySwitchGadget mask)
    _ = evalDist realView :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        masks (by simp [masks]) realView

/-- Forgetting the hidden coordinate bit from the native coordinate source gives exactly the
complete real public-view distribution. -/
theorem coordinateSource_context_evalDist_eq_realPublicView
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    evalDist
        ((fun hiddenAndContext ↦ hiddenAndContext.2) <$>
          coordinateSource (ringRank := ringRank)
            ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget coordinate) =
      evalDist
        (realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget) := by
  simp [coordinateSource, realPublicView, problem,
    LWE.AuxiliaryInput.Search.exactRecoveryProblem, AuxiliaryInput.problem, monad_norm]

/-- Scalar masking a context drawn from the coordinate source still produces the real public
endpoint exactly.  This statement is independent of the supplied coordinate candidate. -/
theorem coordinateSource_randomizeContext_centeredBinomial_evalDist
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta : ℕ}
    [NeZero q]
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    evalDist (do
        let hiddenAndContext ← coordinateSource (ringRank := ringRank)
          (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
          keySwitchErrorSampler tgswGadget keySwitchGadget coordinate
        randomizeContext tgswGadget hiddenAndContext.2) =
      evalDist
        (realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
          keySwitchErrorSampler tgswGadget keySwitchGadget) := by
  let source := coordinateSource (ringRank := ringRank)
    (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
    keySwitchErrorSampler tgswGadget keySwitchGadget coordinate
  let realView := realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
    (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
    keySwitchErrorSampler tgswGadget keySwitchGadget
  calc
    evalDist (source >>= fun hiddenAndContext ↦
        randomizeContext tgswGadget hiddenAndContext.2) =
      evalDist (((fun hiddenAndContext ↦ hiddenAndContext.2) <$> source) >>=
        randomizeContext tgswGadget) := by
          simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
    _ = evalDist (realView >>= randomizeContext tgswGadget) := by
      rw [evalDist_bind,
        coordinateSource_context_evalDist_eq_realPublicView
          (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
          keySwitchErrorSampler tgswGadget keySwitchGadget coordinate,
        ← evalDist_bind]
    _ = evalDist realView :=
      randomize_realPublicView_centeredBinomial_evalDist
        (ringRank := ringRank) (ringEta := ringEta)
        keySwitchErrorSampler tgswGadget keySwitchGadget

/-- Postcompose candidate-independent scalar masking with a public native distinguisher. -/
noncomputable def toCandidateCheck
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ}
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    CandidateCheck q degree ringRank tgswLevels lweDimension keySwitchLevels :=
  fun _coordinate _candidate challenge auxiliary ↦ do
    let transformed ← randomizeContext tgswGadget (challenge, auxiliary)
    distinguisher transformed.1 transformed.2

/-- Scalar masking alone contains no candidate-dependent signal: for every source distribution,
orientation, coordinate, and public distinguisher, its correct and wrong checks are the same
experiment and the oriented candidate gap is exactly zero. -/
theorem candidateCheckGap_toCandidateCheck_eq_zero
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (orientation : Fin lweDimension → Bool)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension) :
    candidateCheckGap ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        orientation (toCandidateCheck tgswGadget distinguisher) coordinate = 0 := by
  simp [candidateCheckGap, FormalProof4FHE.BinaryGuessCheck.orientedGap,
    FormalProof4FHE.BinaryGuessCheck.correctCheck,
    FormalProof4FHE.BinaryGuessCheck.wrongCheck, toCandidateCheck]

/-- The scalar-mask audit packaged as an averaged candidate-view transformer.

Its correct endpoint error is zero.  Since the candidate is ignored, the wrong endpoint remains
the real public view, so its exact advertised error is the full real-versus-uniform statistical
distance.  This is a valid but cryptographically non-amplifying transformer; the preceding
zero-gap theorem explains the boundary. -/
noncomputable def toAveraged
    {q degree ringRank tgswLevels lweDimension keySwitchLevels ringEta : ℕ}
    [NeZero q]
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (degree + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    AveragedCandidateViewTransformer (ringRank := ringRank)
      (lweDimension := lweDimension)
      (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
      (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
      keySwitchErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget where
  transform := fun _coordinate _candidate challenge auxiliary ↦
    randomizeContext tgswGadget (challenge, auxiliary)
  correctError := fun _ ↦ 0
  wrongError := fun _ ↦
    tvDist
      (realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
        (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
        keySwitchErrorSampler tgswGadget keySwitchGadget)
      (uniformPublicView (ringRank := ringRank) (lweDimension := lweDimension)
        (RLWE.CenteredBinomial.sampler q (degree + 1) ringEta)
        keySwitchErrorSampler tgswGadget keySwitchGadget)
  correctError_nonneg := fun _ ↦ le_rfl
  wrongError_nonneg := fun _ ↦ tvDist_nonneg _ _
  correctDistance := by
    intro coordinate
    unfold tvDist
    rw [coordinateSource_randomizeContext_centeredBinomial_evalDist
      keySwitchErrorSampler tgswGadget keySwitchGadget coordinate]
    exact le_of_eq (SPMF.tvDist_self _)
  wrongDistance := by
    intro coordinate
    unfold tvDist
    rw [coordinateSource_randomizeContext_centeredBinomial_evalDist
      keySwitchErrorSampler tgswGadget keySwitchGadget coordinate]


end FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery.ScalarMaskCandidateView
