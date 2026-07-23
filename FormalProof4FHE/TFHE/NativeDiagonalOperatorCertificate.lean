/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeDiagonalDeterminantNormalForm
import FormalProof4FHE.TFHE.NativeDiagonalJointCollision
import FormalProof4FHE.TFHE.NativeDiagonalPairCollisionNormalForm
import FormalProof4FHE.TFHE.NativeDiagonalPairZeroFiber
import FormalProof4FHE.TFHE.NativeWrongControlFiberBound

/-!
# Whole-Key Certificate from the Native Selected-Diagonal Operator

This module installs the selected-diagonal finite reduction in the construction-specific native
TFHE certificate.  The caller no longer supplies an opaque diagonal-distance premise.  Two
fully explicit diagonal routes are available.  The direct route extracts the public challenge
while retaining the transformed error as side information and does not condition on the hidden
difference.  A relaxed constructor accepts a source-error-independent total paired-collision
budget over the rectangular two-copy operator.  Older diagnostic routes use either the expected
fixed-difference challenge-map
fiber loss or the probability that the fixed-difference row operator is non-bijective.  Every
route retains the entire transformed source-error smoothing in one source-to-target marginal
distance.

The remaining quantitative inputs are the conditionally independent off-diagonal bounds and a
bound on the explicit message-one wrong-control fiber loss.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery.AugmentedResidual.NativeShifted

noncomputable section

open FormalProof4FHE.TFHE
open Native
open FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery

namespace WholeKeyRankCertificate

/-- Build the whole-key certificate using the direct side-information collision bound for the
correct selected diagonal and the message-one fiber bound for the wrong branch.  This is the
certificate constructor that bypasses fixed-difference rank failure. -/
noncomputable def ofDiagonalJointCollisionAndMessageOneControlFiberLoss
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (offDiagonalError : Fin lweDimension → Fin lweDimension → ℝ)
    (freshnessError : ℝ)
    (offDiagonalError_nonneg : ∀ coordinate outputCoordinate,
      0 ≤ offDiagonalError coordinate outputCoordinate)
    (freshnessError_nonneg : 0 ≤ freshnessError)
    (offDiagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
      ∀ control ∈ support
        (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          hidden ringSecret coordinate),
      ∀ outputCoordinate, outputCoordinate ≠ coordinate →
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.residualizedCoordinateSampler
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate control outputCoordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret outputCoordinate) ≤
          offDiagonalError coordinate outputCoordinate)
    (messageOneControlFiberLoss_le :
      (lweDimension * TGSW.rowCount ringRank params.levels : ℕ) *
          averagedCanonicalMessageOneControlFiberLoss (degree := degree)
            (ringRank := ringRank) params eta ≤
        freshnessError) :
    WholeKeyRankCertificate (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget :=
  ofMessageOneControlFiberLoss params targetRingErrorSampler
    keySwitchErrorSampler inputErrorSampler keySwitchGadget
    (fun _ =>
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.worstCaseJointCollisionDiagonalOperatorLoss
        (ringRank := ringRank) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        targetRingErrorSampler)
    offDiagonalError freshnessError
    (fun _ =>
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.worstCaseJointCollisionDiagonalOperatorLoss_nonneg
        (ringRank := ringRank) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        targetRingErrorSampler)
    offDiagonalError_nonneg freshnessError_nonneg
    (fun coordinate hidden ringSecret =>
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.tvDist_diagonalExperiment_directEntry_le_worstCaseJointCollision
        params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        targetRingErrorSampler hidden ringSecret coordinate)
    offDiagonalDistance_le messageOneControlFiberLoss_le

/-- Build the whole-key certificate using the normalized finite-fiber chi-square bound for the
correct selected diagonal and the message-one fiber bound for the wrong branch.  This exposes
the direct route in a form suitable for construction-specific counting estimates. -/
noncomputable def ofDiagonalJointChiSquareAndMessageOneControlFiberLoss
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (offDiagonalError : Fin lweDimension → Fin lweDimension → ℝ)
    (freshnessError : ℝ)
    (offDiagonalError_nonneg : ∀ coordinate outputCoordinate,
      0 ≤ offDiagonalError coordinate outputCoordinate)
    (freshnessError_nonneg : 0 ≤ freshnessError)
    (offDiagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
      ∀ control ∈ support
        (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          hidden ringSecret coordinate),
      ∀ outputCoordinate, outputCoordinate ≠ coordinate →
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.residualizedCoordinateSampler
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate control outputCoordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret outputCoordinate) ≤
          offDiagonalError coordinate outputCoordinate)
    (messageOneControlFiberLoss_le :
      (lweDimension * TGSW.rowCount ringRank params.levels : ℕ) *
          averagedCanonicalMessageOneControlFiberLoss (degree := degree)
            (ringRank := ringRank) params eta ≤
        freshnessError) :
    WholeKeyRankCertificate (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget :=
  ofMessageOneControlFiberLoss params targetRingErrorSampler
    keySwitchErrorSampler inputErrorSampler keySwitchGadget
    (fun _ =>
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.worstCaseJointChiSquareDiagonalOperatorLoss
        (ringRank := ringRank) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        targetRingErrorSampler)
    offDiagonalError freshnessError
    (fun _ =>
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.worstCaseJointChiSquareDiagonalOperatorLoss_nonneg
        (ringRank := ringRank) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        targetRingErrorSampler)
    offDiagonalError_nonneg freshnessError_nonneg
    (fun coordinate hidden ringSecret =>
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.tvDist_diagonalExperiment_directEntry_le_worstCaseJointChiSquare
        params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        targetRingErrorSampler hidden ringSecret coordinate)
    offDiagonalDistance_le messageOneControlFiberLoss_le

/-- Preferred paired-collision constructor.  It consumes the exact globally normalized
two-copy excess for each supported source-error vector, avoiding any worst-case retained-side
fiber estimate. -/
noncomputable def ofDiagonalNormalizedPairCollisionExcessAndMessageOneControlFiberLoss
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (pairCollisionEpsilon mixedErrorBound : ℝ)
    (offDiagonalError : Fin lweDimension → Fin lweDimension → ℝ)
    (freshnessError : ℝ)
    (mixedErrorBound_nonneg : 0 ≤ mixedErrorBound)
    (offDiagonalError_nonneg : ∀ coordinate outputCoordinate,
      0 ≤ offDiagonalError coordinate outputCoordinate)
    (freshnessError_nonneg : 0 ≤ freshnessError)
    (normalizedPairCollisionExcess_le : ∀ candidate sourceError,
      sourceError ∈ support
        (ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)) →
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.fixedErrorDiagonalNormalizedPairCollisionExcess
          params candidate sourceError ≤
        pairCollisionEpsilon)
    (mixedErrorDistance_le : ∀ candidate,
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.mixedDiagonalErrorDistance
          (ringRank := ringRank) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          targetRingErrorSampler candidate ≤
        mixedErrorBound)
    (offDiagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
      ∀ control ∈ support
        (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          hidden ringSecret coordinate),
      ∀ outputCoordinate, outputCoordinate ≠ coordinate →
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.residualizedCoordinateSampler
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate control outputCoordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret outputCoordinate) ≤
          offDiagonalError coordinate outputCoordinate)
    (messageOneControlFiberLoss_le :
      (lweDimension * TGSW.rowCount ringRank params.levels : ℕ) *
          averagedCanonicalMessageOneControlFiberLoss (degree := degree)
            (ringRank := ringRank) params eta ≤
        freshnessError) :
    WholeKeyRankCertificate (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget :=
  ofMessageOneControlFiberLoss params targetRingErrorSampler
    keySwitchErrorSampler inputErrorSampler keySwitchGadget
    (fun _ => Real.sqrt pairCollisionEpsilon / 2 + mixedErrorBound)
    offDiagonalError freshnessError
    (fun _ => add_nonneg (div_nonneg (Real.sqrt_nonneg _) (by norm_num))
      mixedErrorBound_nonneg)
    offDiagonalError_nonneg freshnessError_nonneg
    (fun coordinate hidden ringSecret =>
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.tvDist_diagonalExperiment_directEntry_le_of_normalizedPairCollisionExcess
        params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        targetRingErrorSampler hidden ringSecret coordinate pairCollisionEpsilon
        mixedErrorBound normalizedPairCollisionExcess_le mixedErrorDistance_le)
    offDiagonalDistance_le messageOneControlFiberLoss_le

/-- Source-error-independent paired-collision constructor.  The diagonal premise is a
single total rectangular-pair budget for each hidden-bit candidate; it does not quantify over
centered-binomial error vectors or retained side fibers.  This convenience comes from replacing
every nonempty retained-fiber cardinality by one, so the exact normalized constructor can be
quantitatively tighter. -/
noncomputable def ofDiagonalGlobalPairCollisionBudgetAndMessageOneControlFiberLoss
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (pairCollisionEpsilon mixedErrorBound : ℝ)
    (offDiagonalError : Fin lweDimension → Fin lweDimension → ℝ)
    (freshnessError : ℝ)
    (mixedErrorBound_nonneg : 0 ≤ mixedErrorBound)
    (offDiagonalError_nonneg : ∀ coordinate outputCoordinate,
      0 ≤ offDiagonalError coordinate outputCoordinate)
    (freshnessError_nonneg : 0 ≤ freshnessError)
    (globalPairCollisionBudget_le : ∀ candidate,
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.globalDifferencePairCollisionBudget
          (degree := degree) (ringRank := ringRank) params candidate ≤
        pairCollisionEpsilon)
    (mixedErrorDistance_le : ∀ candidate,
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.mixedDiagonalErrorDistance
          (ringRank := ringRank) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          targetRingErrorSampler candidate ≤
        mixedErrorBound)
    (offDiagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
      ∀ control ∈ support
        (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          hidden ringSecret coordinate),
      ∀ outputCoordinate, outputCoordinate ≠ coordinate →
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.residualizedCoordinateSampler
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate control outputCoordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret outputCoordinate) ≤
          offDiagonalError coordinate outputCoordinate)
    (messageOneControlFiberLoss_le :
      (lweDimension * TGSW.rowCount ringRank params.levels : ℕ) *
          averagedCanonicalMessageOneControlFiberLoss (degree := degree)
            (ringRank := ringRank) params eta ≤
        freshnessError) :
    WholeKeyRankCertificate (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget :=
  ofDiagonalNormalizedPairCollisionExcessAndMessageOneControlFiberLoss params
    targetRingErrorSampler keySwitchErrorSampler inputErrorSampler keySwitchGadget
    pairCollisionEpsilon mixedErrorBound offDiagonalError freshnessError
    mixedErrorBound_nonneg offDiagonalError_nonneg freshnessError_nonneg
    (fun candidate sourceError _ =>
      (Native.ShiftedCandidateEvaluator.DiagonalNormalForm.fixedErrorDiagonalNormalizedPairCollisionExcess_le_globalBudget
          params candidate sourceError).trans
        (globalPairCollisionBudget_le candidate))
    mixedErrorDistance_le offDiagonalDistance_le messageOneControlFiberLoss_le

/-- Rank-profile specialization of the source-independent paired-collision constructor.  Instead
of a candidate-wise premise on the original global excess, the caller bounds one explicit sum of
the residue-rank-sensitive zero-fiber envelopes.  Full-rank pairs contribute exactly zero through
the local-ring lift. -/
noncomputable def ofDiagonalBinaryRankWeightedBudgetAndMessageOneControlFiberLoss
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (heven : 2 ∣ q)
    (localParity : IsLocalHom
      (Native.ShiftedCandidateEvaluator.DiagonalNormalForm.rqParityEval
        heven (Nat.succ_pos degree)))
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (pairCollisionEpsilon mixedErrorBound : ℝ)
    (offDiagonalError : Fin lweDimension → Fin lweDimension → ℝ)
    (freshnessError : ℝ)
    (mixedErrorBound_nonneg : 0 ≤ mixedErrorBound)
    (offDiagonalError_nonneg : ∀ coordinate outputCoordinate,
      0 ≤ offDiagonalError coordinate outputCoordinate)
    (freshnessError_nonneg : 0 ≤ freshnessError)
    (rankWeightedBudget_le :
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.binaryRankWeightedDifferencePairCollisionBudget
          (degree := degree) (ringRank := ringRank) params ≤
        pairCollisionEpsilon)
    (mixedErrorDistance_le : ∀ candidate,
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.mixedDiagonalErrorDistance
          (ringRank := ringRank) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          targetRingErrorSampler candidate ≤
        mixedErrorBound)
    (offDiagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
      ∀ control ∈ support
        (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          hidden ringSecret coordinate),
      ∀ outputCoordinate, outputCoordinate ≠ coordinate →
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.residualizedCoordinateSampler
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate control outputCoordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret outputCoordinate) ≤
          offDiagonalError coordinate outputCoordinate)
    (messageOneControlFiberLoss_le :
      (lweDimension * TGSW.rowCount ringRank params.levels : ℕ) *
          averagedCanonicalMessageOneControlFiberLoss (degree := degree)
            (ringRank := ringRank) params eta ≤
        freshnessError) :
    WholeKeyRankCertificate (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget :=
  ofDiagonalGlobalPairCollisionBudgetAndMessageOneControlFiberLoss params
    targetRingErrorSampler keySwitchErrorSampler inputErrorSampler keySwitchGadget
    pairCollisionEpsilon mixedErrorBound offDiagonalError freshnessError
    mixedErrorBound_nonneg offDiagonalError_nonneg freshnessError_nonneg
    (fun candidate =>
      (Native.ShiftedCandidateEvaluator.DiagonalNormalForm.globalDifferencePairCollisionBudget_le_binaryRankWeighted
        params heven candidate localParity).trans rankWeightedBudget_le)
    mixedErrorDistance_le offDiagonalDistance_le messageOneControlFiberLoss_le

/-- Build the whole-key certificate from a concrete support-wise pair-collision estimate for
the diagonal extractor, a bound on its mixed transformed-error marginal, and the existing
message-one wrong-control fiber estimate. -/
noncomputable def ofDiagonalPairCollisionBoundAndMessageOneControlFiberLoss
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (pairCollisionEpsilon mixedErrorBound : ℝ)
    (offDiagonalError : Fin lweDimension → Fin lweDimension → ℝ)
    (freshnessError : ℝ)
    (mixedErrorBound_nonneg : 0 ≤ mixedErrorBound)
    (offDiagonalError_nonneg : ∀ coordinate outputCoordinate,
      0 ≤ offDiagonalError coordinate outputCoordinate)
    (freshnessError_nonneg : 0 ≤ freshnessError)
    (pairCollisionBound : ∀ candidate sourceError,
      sourceError ∈ support
        (ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)) →
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.fixedErrorDiagonalPairCollisionBound
        params candidate sourceError pairCollisionEpsilon)
    (mixedErrorDistance_le : ∀ candidate,
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.mixedDiagonalErrorDistance
          (ringRank := ringRank) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          targetRingErrorSampler candidate ≤
        mixedErrorBound)
    (offDiagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
      ∀ control ∈ support
        (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          hidden ringSecret coordinate),
      ∀ outputCoordinate, outputCoordinate ≠ coordinate →
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.residualizedCoordinateSampler
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate control outputCoordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret outputCoordinate) ≤
          offDiagonalError coordinate outputCoordinate)
    (messageOneControlFiberLoss_le :
      (lweDimension * TGSW.rowCount ringRank params.levels : ℕ) *
          averagedCanonicalMessageOneControlFiberLoss (degree := degree)
            (ringRank := ringRank) params eta ≤
        freshnessError) :
    WholeKeyRankCertificate (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget :=
  ofMessageOneControlFiberLoss params targetRingErrorSampler
    keySwitchErrorSampler inputErrorSampler keySwitchGadget
    (fun _ => Real.sqrt pairCollisionEpsilon / 2 + mixedErrorBound)
    offDiagonalError freshnessError
    (fun _ => add_nonneg (div_nonneg (Real.sqrt_nonneg _) (by norm_num))
      mixedErrorBound_nonneg)
    offDiagonalError_nonneg freshnessError_nonneg
    (fun coordinate hidden ringSecret =>
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.tvDist_diagonalExperiment_directEntry_le_of_pairCollisionBound
        params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        targetRingErrorSampler hidden ringSecret coordinate pairCollisionEpsilon
        mixedErrorBound pairCollisionBound mixedErrorDistance_le)
    offDiagonalDistance_le messageOneControlFiberLoss_le

/-- Build the whole-key certificate directly from the normalized summed excess of the paired
rectangular challenge operator.  Surjective difference pairs have zero excess automatically;
the premise only needs to control the remaining rank-deficient pairs in each retained side
fiber. -/
noncomputable def ofDiagonalPairCollisionExcessAndMessageOneControlFiberLoss
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (pairCollisionEpsilon mixedErrorBound : ℝ)
    (offDiagonalError : Fin lweDimension → Fin lweDimension → ℝ)
    (freshnessError : ℝ)
    (mixedErrorBound_nonneg : 0 ≤ mixedErrorBound)
    (offDiagonalError_nonneg : ∀ coordinate outputCoordinate,
      0 ≤ offDiagonalError coordinate outputCoordinate)
    (freshnessError_nonneg : 0 ≤ freshnessError)
    (pairCollisionExcessBound : ∀ candidate sourceError,
      sourceError ∈ support
        (ProbComp.sampleIID (TGSW.rowCount ringRank params.levels)
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)) →
      ∀ transformedError,
        Native.ShiftedCandidateEvaluator.DiagonalNormalForm.fixedErrorDiagonalPairCollisionExcess
            params candidate sourceError transformedError ≤
          pairCollisionEpsilon *
              (Fintype.card
                (Native.ShiftedCandidateEvaluator.DiagonalNormalForm.DiagonalChallenge
                  q degree ringRank params.levels) : ℝ) *
            (Native.ShiftedCandidateEvaluator.DiagonalNormalForm.fixedErrorDifferenceFiberCard
              params candidate sourceError transformedError : ℝ) ^ 2)
    (mixedErrorDistance_le : ∀ candidate,
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.mixedDiagonalErrorDistance
          (ringRank := ringRank) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          targetRingErrorSampler candidate ≤
        mixedErrorBound)
    (offDiagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
      ∀ control ∈ support
        (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          hidden ringSecret coordinate),
      ∀ outputCoordinate, outputCoordinate ≠ coordinate →
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.residualizedCoordinateSampler
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate control outputCoordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret outputCoordinate) ≤
          offDiagonalError coordinate outputCoordinate)
    (messageOneControlFiberLoss_le :
      (lweDimension * TGSW.rowCount ringRank params.levels : ℕ) *
          averagedCanonicalMessageOneControlFiberLoss (degree := degree)
            (ringRank := ringRank) params eta ≤
        freshnessError) :
    WholeKeyRankCertificate (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget :=
  ofDiagonalPairCollisionBoundAndMessageOneControlFiberLoss params
    targetRingErrorSampler keySwitchErrorSampler inputErrorSampler keySwitchGadget
    pairCollisionEpsilon mixedErrorBound offDiagonalError freshnessError
    mixedErrorBound_nonneg offDiagonalError_nonneg freshnessError_nonneg
    (fun candidate sourceError hsource =>
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.fixedErrorDiagonalPairCollisionBound_of_excess
        params candidate sourceError pairCollisionEpsilon
        (pairCollisionExcessBound candidate sourceError hsource))
    mixedErrorDistance_le offDiagonalDistance_le messageOneControlFiberLoss_le

/-- Build the whole-key certificate with the correct selected-diagonal distance discharged by
the exact finite operator reduction and the wrong branch discharged by the message-one fiber
bound. -/
noncomputable def ofDiagonalOperatorAndMessageOneControlFiberLoss
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (offDiagonalError : Fin lweDimension → Fin lweDimension → ℝ)
    (freshnessError : ℝ)
    (offDiagonalError_nonneg : ∀ coordinate outputCoordinate,
      0 ≤ offDiagonalError coordinate outputCoordinate)
    (freshnessError_nonneg : 0 ≤ freshnessError)
    (offDiagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
      ∀ control ∈ support
        (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          hidden ringSecret coordinate),
      ∀ outputCoordinate, outputCoordinate ≠ coordinate →
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.residualizedCoordinateSampler
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate control outputCoordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret outputCoordinate) ≤
          offDiagonalError coordinate outputCoordinate)
    (messageOneControlFiberLoss_le :
      (lweDimension * TGSW.rowCount ringRank params.levels : ℕ) *
          averagedCanonicalMessageOneControlFiberLoss (degree := degree)
            (ringRank := ringRank) params eta ≤
        freshnessError) :
    WholeKeyRankCertificate (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget :=
  ofMessageOneControlFiberLoss params targetRingErrorSampler
    keySwitchErrorSampler inputErrorSampler keySwitchGadget
    (fun _ =>
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.worstCaseSharpDiagonalOperatorLoss
        (ringRank := ringRank) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        targetRingErrorSampler)
    offDiagonalError freshnessError
    (fun _ =>
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.worstCaseSharpDiagonalOperatorLoss_nonneg
        (ringRank := ringRank) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        targetRingErrorSampler)
    offDiagonalError_nonneg freshnessError_nonneg
    (fun coordinate hidden ringSecret =>
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.tvDist_diagonalExperiment_directEntry_le_worstCaseSharpOperatorLoss
        params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        targetRingErrorSampler hidden ringSecret coordinate)
    offDiagonalDistance_le messageOneControlFiberLoss_le

/-- Build the whole-key certificate using the exact selected-diagonal bad-rank event for the
public-mask hop and the message-one fiber bound for the wrong-control branch. -/
noncomputable def ofDiagonalRankFailureAndMessageOneControlFiberLoss
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (offDiagonalError : Fin lweDimension → Fin lweDimension → ℝ)
    (freshnessError : ℝ)
    (offDiagonalError_nonneg : ∀ coordinate outputCoordinate,
      0 ≤ offDiagonalError coordinate outputCoordinate)
    (freshnessError_nonneg : 0 ≤ freshnessError)
    (offDiagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
      ∀ control ∈ support
        (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          hidden ringSecret coordinate),
      ∀ outputCoordinate, outputCoordinate ≠ coordinate →
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.residualizedCoordinateSampler
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate control outputCoordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret outputCoordinate) ≤
          offDiagonalError coordinate outputCoordinate)
    (messageOneControlFiberLoss_le :
      (lweDimension * TGSW.rowCount ringRank params.levels : ℕ) *
          averagedCanonicalMessageOneControlFiberLoss (degree := degree)
            (ringRank := ringRank) params eta ≤
        freshnessError) :
    WholeKeyRankCertificate (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget :=
  ofMessageOneControlFiberLoss params targetRingErrorSampler
    keySwitchErrorSampler inputErrorSampler keySwitchGadget
    (fun _ =>
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.worstCaseRankSharpDiagonalOperatorLoss
        (ringRank := ringRank) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        targetRingErrorSampler)
    offDiagonalError freshnessError
    (fun _ =>
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.worstCaseRankSharpDiagonalOperatorLoss_nonneg
        (ringRank := ringRank) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        targetRingErrorSampler)
    offDiagonalError_nonneg freshnessError_nonneg
    (fun coordinate hidden ringSecret =>
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.tvDist_diagonalExperiment_directEntry_le_worstCaseRankSharpOperatorLoss
        params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        targetRingErrorSampler hidden ringSecret coordinate)
    offDiagonalDistance_le messageOneControlFiberLoss_le

/-- Build the whole-key certificate from any explicit upper bound on the exact selected-diagonal
determinant non-unit probability.  This is the quantitative entry point for local-ring,
number-theoretic, or certified finite estimates of the concrete row matrix. -/
noncomputable def ofDiagonalDeterminantBoundAndMessageOneControlFiberLoss
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (targetRingErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (determinantFailureBound : Bool → ℝ)
    (offDiagonalError : Fin lweDimension → Fin lweDimension → ℝ)
    (freshnessError : ℝ)
    (determinantFailureBound_nonneg : ∀ candidate,
      0 ≤ determinantFailureBound candidate)
    (offDiagonalError_nonneg : ∀ coordinate outputCoordinate,
      0 ≤ offDiagonalError coordinate outputCoordinate)
    (freshnessError_nonneg : 0 ≤ freshnessError)
    (determinantFailureProbability_le : ∀ candidate,
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.diagonalRowDeterminantFailureProbability
          (degree := degree) (ringRank := ringRank) params candidate ≤
        determinantFailureBound candidate)
    (offDiagonalDistance_le : ∀ coordinate,
      ∀ hidden : BinarySecret lweDimension,
      ∀ ringSecret : RingBinarySecret ringRank (degree + 1),
      ∀ control ∈ support
        (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          hidden ringSecret coordinate),
      ∀ outputCoordinate, outputCoordinate ≠ coordinate →
        tvDist
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.residualizedCoordinateSampler
              params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
              hidden ringSecret coordinate control outputCoordinate)
            (Native.ShiftedCandidateEvaluator.OffDiagonalNormalForm.directEntrySampler
              params targetRingErrorSampler hidden ringSecret outputCoordinate) ≤
          offDiagonalError coordinate outputCoordinate)
    (messageOneControlFiberLoss_le :
      (lweDimension * TGSW.rowCount ringRank params.levels : ℕ) *
          averagedCanonicalMessageOneControlFiberLoss (degree := degree)
            (ringRank := ringRank) params eta ≤
        freshnessError) :
    WholeKeyRankCertificate (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) (eta := eta) params targetRingErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget :=
  ofMessageOneControlFiberLoss params targetRingErrorSampler
    keySwitchErrorSampler inputErrorSampler keySwitchGadget
    (fun _ =>
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.worstCaseDeterminantBoundedDiagonalOperatorLoss
        (ringRank := ringRank) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        targetRingErrorSampler determinantFailureBound)
    offDiagonalError freshnessError
    (fun _ =>
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.worstCaseDeterminantBoundedDiagonalOperatorLoss_nonneg
        (ringRank := ringRank) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        targetRingErrorSampler determinantFailureBound determinantFailureBound_nonneg)
    offDiagonalError_nonneg freshnessError_nonneg
    (fun coordinate hidden ringSecret =>
      Native.ShiftedCandidateEvaluator.DiagonalNormalForm.tvDist_diagonalExperiment_directEntry_le_worstCaseDeterminantBoundedOperatorLoss
        params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        targetRingErrorSampler determinantFailureBound determinantFailureProbability_le
        hidden ringSecret coordinate)
    offDiagonalDistance_le messageOneControlFiberLoss_le

end WholeKeyRankCertificate

end

end FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery.AugmentedResidual.NativeShifted
