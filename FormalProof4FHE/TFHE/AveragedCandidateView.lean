/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.SharedRandomness.Reduction
import FormalProof4FHE.TFHE.PointwiseCandidateView

/-!
# Averaged Native TFHE Candidate Views

The pointwise candidate-view interface is sufficient for lossless shared-context amplification,
but it can be stronger than a native evaluator can satisfy: after fixing one public BRK+KSK
context, it still asks the evaluator to reproduce an endpoint with freshly sampled secrets.

This file records the strictly weaker averaged distributional contract.  Correct and wrong
candidates need only approach the real and uniform public endpoints after averaging over the
native source experiment.  Data processing yields the expected one-shot candidate gap.  The
threshold theorem from `Probability.MajorityAmplification` then gives the sound multi-run bound

`amplifiedError rounds threshold + averageError / threshold`.

The division term is intentional.  An averaged distinguishing advantage alone cannot be treated
as a uniform conditional advantage when repetitions share the same public context.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery

/-- Candidate-view transformation whose correctness laws hold over the complete native source
distribution, rather than separately on every fixed public-context fiber. -/
structure AveragedCandidateViewTransformer
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
  correctDistance : ∀ coordinate,
    tvDist
        (do
          let hiddenAndContext ← coordinateSource (ringRank := ringRank)
            sourceRingErrorSampler
            sourceKeySwitchErrorSampler tgswGadget keySwitchGadget coordinate
          transform coordinate hiddenAndContext.1 hiddenAndContext.2.1
            hiddenAndContext.2.2)
        (realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          targetRingErrorSampler targetKeySwitchErrorSampler
          tgswGadget keySwitchGadget) ≤ correctError coordinate
  wrongDistance : ∀ coordinate,
    tvDist
        (do
          let hiddenAndContext ← coordinateSource (ringRank := ringRank)
            sourceRingErrorSampler
            sourceKeySwitchErrorSampler tgswGadget keySwitchGadget coordinate
          transform coordinate (!hiddenAndContext.1) hiddenAndContext.2.1
            hiddenAndContext.2.2)
        (uniformPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          targetRingErrorSampler targetKeySwitchErrorSampler
          tgswGadget keySwitchGadget) ≤ wrongError coordinate

namespace AveragedCandidateViewTransformer

/-- Postcompose an averaged candidate-view transformer with a public decision distinguisher. -/
def toCheck
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    {sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {sourceKeySwitchErrorSampler targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (transformer : AveragedCandidateViewTransformer (ringRank := ringRank)
      (lweDimension := lweDimension) sourceRingErrorSampler targetRingErrorSampler
      sourceKeySwitchErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    CandidateCheck q degree ringRank tgswLevels lweDimension keySwitchLevels :=
  fun coordinate candidate challenge auxiliary ↦ do
    let transformed ← transformer.transform coordinate candidate challenge auxiliary
    distinguisher transformed.1 transformed.2

/-- Averaged correct/wrong view distances yield the one-shot oriented candidate gap. -/
theorem decisionAdvantage_sub_errors_le_candidateCheckGap
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    {sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {sourceKeySwitchErrorSampler targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (transformer : AveragedCandidateViewTransformer (ringRank := ringRank)
      (lweDimension := lweDimension) sourceRingErrorSampler targetRingErrorSampler
      sourceKeySwitchErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension) :
    decisionAdvantage targetRingErrorSampler targetKeySwitchErrorSampler
        tgswGadget keySwitchGadget distinguisher - transformer.correctError coordinate -
          transformer.wrongError coordinate ≤
      candidateCheckGap sourceRingErrorSampler sourceKeySwitchErrorSampler
        tgswGadget keySwitchGadget
        (fun _ ↦ CandidateViewTransformer.orientation targetRingErrorSampler
          targetKeySwitchErrorSampler tgswGadget keySwitchGadget distinguisher)
        (transformer.toCheck distinguisher) coordinate := by
  let source := coordinateSource (ringRank := ringRank)
    sourceRingErrorSampler sourceKeySwitchErrorSampler
    tgswGadget keySwitchGadget coordinate
  let finish := fun context :
      PublicContext q degree ringRank tgswLevels lweDimension keySwitchLevels ↦
    distinguisher context.1 context.2
  let correctView := source >>= fun hiddenAndContext ↦
    transformer.transform coordinate hiddenAndContext.1
      hiddenAndContext.2.1 hiddenAndContext.2.2
  let wrongView := source >>= fun hiddenAndContext ↦
    transformer.transform coordinate (!hiddenAndContext.1)
      hiddenAndContext.2.1 hiddenAndContext.2.2
  let correct := correctView >>= finish
  let wrong := wrongView >>= finish
  have hcorrect : tvDist correct
      (realDecisionGame targetRingErrorSampler targetKeySwitchErrorSampler
        tgswGadget keySwitchGadget distinguisher) ≤
      transformer.correctError coordinate := by
    rw [realDecisionGame_eq_bind_realPublicView]
    exact (tvDist_bind_right_le finish _ _).trans
      (by simpa only [correctView, source] using transformer.correctDistance coordinate)
  have hwrong : tvDist wrong
      (uniformDecisionGame targetRingErrorSampler targetKeySwitchErrorSampler
        tgswGadget keySwitchGadget distinguisher) ≤
      transformer.wrongError coordinate := by
    rw [uniformDecisionGame_eq_bind_uniformPublicView]
    exact (tvDist_bind_right_le finish _ _).trans
      (by simpa only [wrongView, source] using transformer.wrongDistance coordinate)
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
  simpa [decisionAdvantage, candidateCheckGap,
    FormalProof4FHE.BinaryGuessCheck.orientedGap,
    FormalProof4FHE.BinaryGuessCheck.correctCheck,
    FormalProof4FHE.BinaryGuessCheck.wrongCheck, toCheck, correct, wrong,
    correctView, wrongView, source, finish, monad_norm] using hgap

/-- One-shot coordinate failure induced by an averaged transformer. -/
theorem coordinateFailure_le
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    {sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {sourceKeySwitchErrorSampler targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (transformer : AveragedCandidateViewTransformer (ringRank := ringRank)
      (lweDimension := lweDimension) sourceRingErrorSampler targetRingErrorSampler
      sourceKeySwitchErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (coordinate : Fin lweDimension) :
    Pr[= false |
      coordinateGame sourceRingErrorSampler sourceKeySwitchErrorSampler
        tgswGadget keySwitchGadget
        (testerOfCheck
          (fun _ ↦ CandidateViewTransformer.orientation targetRingErrorSampler
            targetKeySwitchErrorSampler tgswGadget keySwitchGadget distinguisher)
          (transformer.toCheck distinguisher)) coordinate] ≤
      ENNReal.ofReal
        ((1 - (decisionAdvantage targetRingErrorSampler targetKeySwitchErrorSampler
          tgswGadget keySwitchGadget distinguisher - transformer.correctError coordinate -
            transformer.wrongError coordinate)) / 2) := by
  apply coordinateGame_testerOfCheck_failureProbability_le_of_gap
  exact transformer.decisionAdvantage_sub_errors_le_candidateCheckGap
    distinguisher coordinate

/-- Thresholded shared-context amplification from an averaged candidate-view law. -/
theorem amplifiedCoordinateFailure_le_threshold
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    {sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {sourceKeySwitchErrorSampler targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (transformer : AveragedCandidateViewTransformer (ringRank := ringRank)
      (lweDimension := lweDimension) sourceRingErrorSampler targetRingErrorSampler
      sourceKeySwitchErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget)
    (distinguisher : PublicDistinguisher q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (rounds : Fin lweDimension → ℕ) (coordinate : Fin lweDimension)
    (threshold : ENNReal) (hthreshold_pos : 0 < threshold)
    (hthreshold_one : threshold ≤ 1) :
    Pr[= false |
      coordinateGame sourceRingErrorSampler sourceKeySwitchErrorSampler
        tgswGadget keySwitchGadget
        (amplifiedTesterOfCheck rounds
          (fun _ ↦ CandidateViewTransformer.orientation targetRingErrorSampler
            targetKeySwitchErrorSampler tgswGadget keySwitchGadget distinguisher)
          (transformer.toCheck distinguisher)) coordinate] ≤
      FormalProof4FHE.MajorityAmplification.amplifiedError
          (rounds coordinate) threshold +
        ENNReal.ofReal
          ((1 - (decisionAdvantage targetRingErrorSampler targetKeySwitchErrorSampler
            tgswGadget keySwitchGadget distinguisher - transformer.correctError coordinate -
              transformer.wrongError coordinate)) / 2) / threshold := by
  apply coordinateGame_amplifiedTesterOfCheck_failureProbability_le_of_average
    sourceRingErrorSampler sourceKeySwitchErrorSampler tgswGadget keySwitchGadget rounds
    (fun _ ↦ CandidateViewTransformer.orientation targetRingErrorSampler
      targetKeySwitchErrorSampler tgswGadget keySwitchGadget distinguisher)
    (transformer.toCheck distinguisher) coordinate threshold
    (ENNReal.ofReal
      ((1 - (decisionAdvantage targetRingErrorSampler targetKeySwitchErrorSampler
        tgswGadget keySwitchGadget distinguisher - transformer.correctError coordinate -
          transformer.wrongError coordinate)) / 2))
    hthreshold_pos hthreshold_one
  exact transformer.coordinateFailure_le distinguisher coordinate

end AveragedCandidateViewTransformer

namespace PointwiseCandidateViewTransformer

/-- Every pointwise transformer induces the averaged contract with the same two errors. -/
noncomputable def toAveraged
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    {sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {sourceKeySwitchErrorSampler targetKeySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (transformer : PointwiseCandidateViewTransformer (ringRank := ringRank)
      (lweDimension := lweDimension) sourceRingErrorSampler targetRingErrorSampler
      sourceKeySwitchErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget) :
    AveragedCandidateViewTransformer (ringRank := ringRank)
      (lweDimension := lweDimension) sourceRingErrorSampler targetRingErrorSampler
      sourceKeySwitchErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget where
  transform := transformer.transform
  correctError := transformer.correctError
  wrongError := transformer.wrongError
  correctError_nonneg := transformer.correctError_nonneg
  wrongError_nonneg := transformer.wrongError_nonneg
  correctDistance := by
    intro coordinate
    let source := coordinateSource (ringRank := ringRank)
      sourceRingErrorSampler sourceKeySwitchErrorSampler
      tgswGadget keySwitchGadget coordinate
    let target := realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
      targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget
    have hmix := tvDist_bind_left_le_const (m := ProbComp) source
      (fun hiddenAndContext ↦ transformer.transform coordinate hiddenAndContext.1
        hiddenAndContext.2.1 hiddenAndContext.2.2)
      (fun _ ↦ target) (transformer.correctError coordinate)
      (fun hiddenAndContext hsupport ↦
        transformer.correctDistance coordinate hiddenAndContext hsupport)
    have heq : evalDist (source >>= fun _ ↦ target) = evalDist target :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        source (by simp) target
    unfold tvDist at hmix ⊢
    rw [heq] at hmix
    simpa only [source, target] using hmix
  wrongDistance := by
    intro coordinate
    let source := coordinateSource (ringRank := ringRank)
      sourceRingErrorSampler sourceKeySwitchErrorSampler
      tgswGadget keySwitchGadget coordinate
    let target := uniformPublicView (ringRank := ringRank) (lweDimension := lweDimension)
      targetRingErrorSampler targetKeySwitchErrorSampler tgswGadget keySwitchGadget
    have hmix := tvDist_bind_left_le_const (m := ProbComp) source
      (fun hiddenAndContext ↦ transformer.transform coordinate (!hiddenAndContext.1)
        hiddenAndContext.2.1 hiddenAndContext.2.2)
      (fun _ ↦ target) (transformer.wrongError coordinate)
      (fun hiddenAndContext hsupport ↦
        transformer.wrongDistance coordinate hiddenAndContext hsupport)
    have heq : evalDist (source >>= fun _ ↦ target) = evalDist target :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        source (by simp) target
    unfold tvDist at hmix ⊢
    rw [heq] at hmix
    simpa only [source, target] using hmix

end PointwiseCandidateViewTransformer

namespace CandidateViewTransformer

/-- An exact averaged transformer is the zero-error specialization of the quantitative averaged
interface. -/
noncomputable def toAveraged
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    {ringErrorSampler : ProbComp (RLWE.Rq q degree)}
    {keySwitchErrorSampler : ProbComp (ZMod q)}
    {tgswGadget : Fin tgswLevels → RLWE.Rq q degree}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (transformer : CandidateViewTransformer (ringRank := ringRank)
      (lweDimension := lweDimension) ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget) :
    AveragedCandidateViewTransformer (ringRank := ringRank)
      (lweDimension := lweDimension) ringErrorSampler ringErrorSampler
      keySwitchErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget where
  transform := transformer.transform
  correctError := fun _ ↦ 0
  wrongError := fun _ ↦ 0
  correctError_nonneg := fun _ ↦ le_rfl
  wrongError_nonneg := fun _ ↦ le_rfl
  correctDistance := by
    intro coordinate
    unfold tvDist
    rw [transformer.correctLaw coordinate]
    exact le_of_eq (SPMF.tvDist_self _)
  wrongDistance := by
    intro coordinate
    unfold tvDist
    rw [transformer.wrongLaw coordinate]
    exact le_of_eq (SPMF.tvDist_self _)

end CandidateViewTransformer

end FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.Search.PairedRecovery.CoordinateRecovery
