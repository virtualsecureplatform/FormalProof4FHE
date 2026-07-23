/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.ScalarCoordinateRecovery

/-!
# Pointwise Freshness Boundary for Native TFHE Candidate Views

The PKC 2024 CircLWE search-to-decision strategy randomizes the secret, homomorphically evaluates
the shifted auxiliary-input function, and adds smudging noise.  Repeating a candidate check against
one supplied native BRK+KSK view is sound only when that construction is fresh after the supplied
view has been fixed.

This module records exactly that conditional distributional statement.  For every supported
hidden-bit/public-context pair, the correct candidate transform must be close to the native real
view and the wrong candidate transform must be close to the uniform-BRK endpoint.  Data processing
through an arbitrary decision distinguisher then gives the checked pointwise gap

`decisionAdvantage - correctError - wrongError`.

The structure is deliberately stronger than the averaged `CandidateViewTransformer`; the latter
does not imply this conditional law.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery

/-- Scheme-level shifted-evaluation/smudging certificate that remains valid after fixing the
original native BRK+KSK context. -/
structure PointwiseCandidateViewTransformer
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (sourceKeySwitchErrorSampler targetKeySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) where
  transform : Fin lweDimension → Bool →
    Challenge q degree ringRank tgswLevels lweDimension →
      Auxiliary q degree ringRank lweDimension keySwitchLevels →
        ProbComp (PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels)
  correctError : Fin lweDimension → ℝ
  wrongError : Fin lweDimension → ℝ
  correctError_nonneg : ∀ coordinate, 0 ≤ correctError coordinate
  wrongError_nonneg : ∀ coordinate, 0 ≤ wrongError coordinate
  correctDistance : ∀ coordinate hiddenAndContext,
    hiddenAndContext ∈ support
      (coordinateSource sourceRingErrorSampler sourceKeySwitchErrorSampler tgswGadget
        keySwitchGadget coordinate) →
      tvDist
        (transform coordinate hiddenAndContext.1 hiddenAndContext.2.1
          hiddenAndContext.2.2)
        (realPublicView targetRingErrorSampler targetKeySwitchErrorSampler
          tgswGadget keySwitchGadget) ≤
          correctError coordinate
  wrongDistance : ∀ coordinate hiddenAndContext,
    hiddenAndContext ∈ support
      (coordinateSource sourceRingErrorSampler sourceKeySwitchErrorSampler tgswGadget
        keySwitchGadget coordinate) →
      tvDist
        (transform coordinate (!hiddenAndContext.1) hiddenAndContext.2.1
          hiddenAndContext.2.2)
        (uniformPublicView targetRingErrorSampler targetKeySwitchErrorSampler
          tgswGadget keySwitchGadget) ≤
          wrongError coordinate

namespace PointwiseCandidateViewTransformer

/-- **Overlap obstruction for pointwise freshness.**  If the very same public context can occur
with both values of the hidden scalar bit, then a pointwise transformer must statistically bridge
the complete real and uniform target views.  More precisely, their distance is at most the sum of
the advertised correct- and wrong-candidate errors.

This theorem is useful when auditing a proposed native evaluator: a small per-context error is
impossible on overlapping source fibers unless the two unconditional decision endpoints are
already statistically close.  Computational indistinguishability of those endpoints is not
enough to discharge this statistical requirement. -/
theorem realUniformDistance_le_errors_of_context_overlap
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    {sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {sourceKeySwitchErrorSampler targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (transformer : PointwiseCandidateViewTransformer (ringRank := ringRank)
      (lweDimension := lweDimension) sourceRingErrorSampler targetRingErrorSampler
      sourceKeySwitchErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget)
    (coordinate : Fin lweDimension)
    (context : PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels)
    (hfalse : (false, context) ∈ support
      (coordinateSource sourceRingErrorSampler sourceKeySwitchErrorSampler tgswGadget
        keySwitchGadget coordinate))
    (htrue : (true, context) ∈ support
      (coordinateSource sourceRingErrorSampler sourceKeySwitchErrorSampler tgswGadget
        keySwitchGadget coordinate)) :
    tvDist
        (realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          targetRingErrorSampler targetKeySwitchErrorSampler
          tgswGadget keySwitchGadget)
        (uniformPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          targetRingErrorSampler targetKeySwitchErrorSampler
          tgswGadget keySwitchGadget) ≤
      transformer.correctError coordinate + transformer.wrongError coordinate := by
  let middle := transformer.transform coordinate false context.1 context.2
  have hcorrect : tvDist middle
      (realPublicView targetRingErrorSampler targetKeySwitchErrorSampler
        tgswGadget keySwitchGadget) ≤ transformer.correctError coordinate := by
    simpa only [middle] using
      (transformer.correctDistance coordinate (false, context) hfalse)
  have hwrong : tvDist middle
      (uniformPublicView targetRingErrorSampler targetKeySwitchErrorSampler
        tgswGadget keySwitchGadget) ≤ transformer.wrongError coordinate := by
    simpa only [Bool.not_true, middle] using
      (transformer.wrongDistance coordinate (true, context) htrue)
  calc
    tvDist
        (realPublicView targetRingErrorSampler targetKeySwitchErrorSampler
          tgswGadget keySwitchGadget)
        (uniformPublicView targetRingErrorSampler targetKeySwitchErrorSampler
          tgswGadget keySwitchGadget) ≤
      tvDist
          (realPublicView targetRingErrorSampler targetKeySwitchErrorSampler
            tgswGadget keySwitchGadget) middle +
        tvDist middle
          (uniformPublicView targetRingErrorSampler targetKeySwitchErrorSampler
            tgswGadget keySwitchGadget) := tvDist_triangle _ middle _
    _ = tvDist middle
          (realPublicView targetRingErrorSampler targetKeySwitchErrorSampler
            tgswGadget keySwitchGadget) +
        tvDist middle
          (uniformPublicView targetRingErrorSampler targetKeySwitchErrorSampler
            tgswGadget keySwitchGadget) := by
      rw [tvDist_comm
        (realPublicView targetRingErrorSampler targetKeySwitchErrorSampler
          tgswGadget keySwitchGadget) middle]
    _ ≤ transformer.correctError coordinate + transformer.wrongError coordinate :=
      add_le_add hcorrect hwrong

/-- Postcompose a conditional candidate-view transformer with a public decision distinguisher. -/
def toCheck
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    {sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {sourceKeySwitchErrorSampler targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (transformer : PointwiseCandidateViewTransformer (ringRank := ringRank)
      (lweDimension := lweDimension) sourceRingErrorSampler targetRingErrorSampler
      sourceKeySwitchErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    CandidateCheck q degree ringRank tgswLevels lweDimension keySwitchLevels :=
  fun coordinate candidate challenge auxiliary => do
    let transformed ← transformer.transform coordinate candidate challenge auxiliary
    distinguisher transformed.1 transformed.2

/-- The paper's conditional freshness/smudging law yields the pointwise candidate gap needed by
shared-context amplification. -/
theorem decisionAdvantage_sub_errors_le_pointwiseCandidateCheckGap
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    {sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {sourceKeySwitchErrorSampler targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (transformer : PointwiseCandidateViewTransformer (ringRank := ringRank)
      (lweDimension := lweDimension) sourceRingErrorSampler targetRingErrorSampler
      sourceKeySwitchErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension)
    (hiddenAndContext : Bool ×
      PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels)
    (hsupport : hiddenAndContext ∈ support
      (coordinateSource sourceRingErrorSampler sourceKeySwitchErrorSampler tgswGadget
        keySwitchGadget coordinate)) :
    decisionAdvantage targetRingErrorSampler targetKeySwitchErrorSampler
        tgswGadget keySwitchGadget
        distinguisher - transformer.correctError coordinate - transformer.wrongError coordinate ≤
      pointwiseCandidateCheckGap
        (fun _ => CandidateViewTransformer.orientation targetRingErrorSampler
          targetKeySwitchErrorSampler tgswGadget keySwitchGadget distinguisher)
        (transformer.toCheck distinguisher) coordinate hiddenAndContext := by
  let finish := fun context :
      PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels =>
    distinguisher context.1 context.2
  let correct := transformer.transform coordinate hiddenAndContext.1
    hiddenAndContext.2.1 hiddenAndContext.2.2 >>= finish
  let wrong := transformer.transform coordinate (!hiddenAndContext.1)
    hiddenAndContext.2.1 hiddenAndContext.2.2 >>= finish
  have hcorrect : tvDist correct
      (realDecisionGame targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget
        keySwitchGadget distinguisher) ≤ transformer.correctError coordinate := by
    rw [realDecisionGame_eq_bind_realPublicView]
    exact (tvDist_bind_right_le finish _ _).trans
      (transformer.correctDistance coordinate hiddenAndContext hsupport)
  have hwrong : tvDist wrong
      (uniformDecisionGame targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget
        keySwitchGadget distinguisher) ≤ transformer.wrongError coordinate := by
    rw [uniformDecisionGame_eq_bind_uniformPublicView]
    exact (tvDist_bind_right_le finish _ _).trans
      (transformer.wrongDistance coordinate hiddenAndContext hsupport)
  have hgap := FormalProof4FHE.BinaryGuessCheck.orientedAcceptanceGap_lowerBound_of_tvDist
    correct wrong
    (realDecisionGame targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget
      keySwitchGadget distinguisher)
    (uniformDecisionGame targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget
      keySwitchGadget distinguisher)
    (CandidateViewTransformer.orientation targetRingErrorSampler
      targetKeySwitchErrorSampler tgswGadget keySwitchGadget distinguisher)
    (transformer.correctError coordinate) (transformer.wrongError coordinate)
    (CandidateViewTransformer.orientation_le targetRingErrorSampler
      targetKeySwitchErrorSampler tgswGadget keySwitchGadget distinguisher)
    hcorrect hwrong
  simpa [decisionAdvantage, pointwiseCandidateCheckGap,
    FormalProof4FHE.BinaryGuessCheck.orientedGap,
    FormalProof4FHE.BinaryGuessCheck.correctCheck,
    FormalProof4FHE.BinaryGuessCheck.wrongCheck, toCheck, correct, wrong, finish,
    monad_norm] using hgap

end PointwiseCandidateViewTransformer

end FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery
