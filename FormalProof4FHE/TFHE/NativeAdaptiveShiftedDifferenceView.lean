/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeAdaptiveShiftedCandidateEvaluator
import FormalProof4FHE.TFHE.NativeShiftedDifferenceReparameterization

/-!
# Independent-Difference Form of the Adaptive Native Shifted Evaluator

This module lifts the fixed-BRK translation equivalence to the complete adaptive evaluator.  For
each public scalar mask, the uniform true branch is replaced exactly by a fresh uniform difference
from the already transported source BRK.  The evaluator then reconstructs the true branch by
translation before running the unchanged CMux.

The correct complete-ciphertext and phase laws expose a retained transported source row plus an
independent zero-control perturbation.  This is the refined normal-form boundary: source noise is
base noise, rather than part of a residual to which a second fresh error is automatically added.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery.AugmentedResidual.NativeShifted

noncomputable section

open FormalProof4FHE.TFHE
open Native
open FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery

attribute [local instance] NoiseBounds.positiveRqCommRing NoiseBounds.positiveRqRing

/-- Fixed-coin evaluator where the second coin component is interpreted as an independent
difference from the scalar-transported source BRK. -/
noncomputable def transformWithDifference
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ}
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (candidate : Bool)
    (challenge : Challenge q (degree + 1) ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank (degree + 1) lweDimension
      keySwitchLevels queryCount)
    (coin : Coin q (degree + 1) ringRank params.levels lweDimension) :
    PublicContext q (degree + 1) ringRank params.levels lweDimension
      keySwitchLevels queryCount :=
  let transported := transportedView params challenge auxiliary coin.1
  transformWithCoin params coordinate candidate challenge auxiliary
    (coin.1, Native.ShiftedCandidateEvaluator.addDifference
      transported.1.1 coin.2)

/-- Randomized adaptive evaluator with an independent uniform difference coin. -/
noncomputable def transformFromDifference
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (candidate : Bool)
    (challenge : Challenge q (degree + 1) ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank (degree + 1) lweDimension
      keySwitchLevels queryCount) :
    ProbComp
      (PublicContext q (degree + 1) ringRank params.levels lweDimension
        keySwitchLevels queryCount) :=
  transformWithDifference params coordinate candidate challenge auxiliary <$>
    sampleCoin q (degree + 1) ringRank params.levels lweDimension

/-- The original adaptive evaluator and its independent-difference form have exactly the same
distribution for every fixed public context and candidate. -/
theorem transform_evalDist_eq_transformFromDifference
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (candidate : Bool)
    (challenge : Challenge q (degree + 1) ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank (degree + 1) lweDimension
      keySwitchLevels queryCount) :
    evalDist (transform params coordinate candidate challenge auxiliary) =
      evalDist
        (transformFromDifference params coordinate candidate challenge auxiliary) := by
  let masks := $ᵗ BinarySecret lweDimension
  let branches :=
    $ᵗ Native.BootstrappingKey q (degree + 1) ringRank params.levels lweDimension
  unfold transform transformFromDifference sampleCoin
  simp only [map_eq_bind_pure_comp, Function.comp_apply, bind_assoc, pure_bind]
  change evalDist (masks >>= fun mask =>
      branches >>= fun trueBranch =>
        pure (transformWithCoin params coordinate candidate challenge auxiliary
          (mask, trueBranch))) =
    evalDist (masks >>= fun mask =>
      branches >>= fun difference =>
        pure (transformWithDifference params coordinate candidate challenge auxiliary
          (mask, difference)))
  refine evalDist_bind_congr' masks fun mask => ?_
  let source := (transportedView params challenge auxiliary mask).1.1
  let finish := fun trueBranch : Native.BootstrappingKey q (degree + 1) ringRank
      params.levels lweDimension =>
    transformWithCoin params coordinate candidate challenge auxiliary (mask, trueBranch)
  have h := evalDist_map_eq_of_evalDist_eq
    (Native.ShiftedCandidateEvaluator.addDifference_uniform_evalDist source) finish
  simpa only [map_eq_bind_pure_comp, Function.comp_apply, Function.comp_def,
    bind_assoc, pure_bind, transformWithDifference, source, finish] using h.symm

/-- Correct complete-ciphertext endpoint in which every digit input is visibly the independent
difference row, while the base ciphertext is the transported source entry. -/
theorem transformWithDifference_challenge_correct_ciphertext
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ}
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (candidate : Bool)
    (targetSecret : BinarySecret lweDimension)
    (challenge : Challenge q (degree + 1) ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank (degree + 1) lweDimension
      keySwitchLevels queryCount)
    (coin : Coin q (degree + 1) ringRank params.levels lweDimension)
    (outputCoordinate : Fin lweDimension)
    (hcandidate : transportCandidate coordinate candidate coin.1 =
      targetSecret coordinate) :
    (transformWithDifference params coordinate candidate challenge auxiliary coin).1
        outputCoordinate =
      Native.ShiftedCandidateEvaluator.addInternalProduct params
        ((transportedView params challenge auxiliary coin.1).1.1 outputCoordinate)
        (fun row => Gadget.Base.ringExtendedDigits params
          (TLWE.entry (coin.2 outputCoordinate) row))
        (Native.ShiftedCandidateEvaluator.candidateHomogeneousPart params
          Native.ShiftedCandidateEvaluator.proofZero
          (targetSecret coordinate)
          ((transportedView params challenge auxiliary coin.1).1.1 coordinate)) := by
  change Native.ShiftedCandidateEvaluator.selectBootstrappingKey params coordinate
      (transportCandidate coordinate candidate coin.1)
      (transportedView params challenge auxiliary coin.1).1.1
      (Native.ShiftedCandidateEvaluator.addDifference
        (transportedView params challenge auxiliary coin.1).1.1 coin.2)
      outputCoordinate = _
  rw [hcandidate]
  exact Native.ShiftedCandidateEvaluator.selectBootstrappingKey_correct_ciphertext_addDifference
    params targetSecret coordinate outputCoordinate
    (transportedView params challenge auxiliary coin.1).1.1 coin.2

/-- Correct phase law after retaining the transported source-row error as base noise and naming
only the independent zero-control term as the added perturbation. -/
theorem phase_transformWithDifference_eq_gadgetPhase_add_sourceError_add_controlResidual
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ}
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (candidate : Bool)
    (targetSecret : BinarySecret lweDimension)
    (challenge : Challenge q (degree + 1) ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank (degree + 1) lweDimension
      keySwitchLevels queryCount)
    (ringSecret : RingBinarySecret ringRank (degree + 1))
    (coin : Coin q (degree + 1) ringRank params.levels lweDimension)
    (outputCoordinate : Fin lweDimension)
    (index : Fin (ringRank + 1) × Fin params.levels)
    (hcandidate : transportCandidate coordinate candidate coin.1 =
      targetSecret coordinate) :
    TLWE.phase (embedRingSecret q ringSecret)
        (TLWE.entry
          ((transformWithDifference params coordinate candidate challenge auxiliary
            coin).1 outputCoordinate) (finProdFinEquiv index)) =
      Native.ShiftedCandidateEvaluator.proofAdd
        (TGSW.gadgetPhase (embedRingSecret q ringSecret)
          (Gadget.Base.ringGadget params)
          (TGSW.cmuxMessage 0 0 (embedBit (targetSecret outputCoordinate)))
          (finProdFinEquiv index))
        (Native.ShiftedCandidateEvaluator.proofAdd
          (TGSW.rowError (embedRingSecret q ringSecret)
            (Gadget.Base.ringGadget params) (embedBit (targetSecret outputCoordinate))
            ((transportedView params challenge auxiliary coin.1).1.1
              outputCoordinate) index)
          (Native.ShiftedCandidateEvaluator.independentControlResidual params
            (embedRingSecret q ringSecret) targetSecret coordinate
            (transportedView params challenge auxiliary coin.1).1.1 coin.2
            outputCoordinate (finProdFinEquiv index))) := by
  let source := (transportedView params challenge auxiliary coin.1).1.1
  let reconstructedCoin : Coin q (degree + 1) ringRank params.levels lweDimension :=
    (coin.1, Native.ShiftedCandidateEvaluator.addDifference source coin.2)
  have h := phase_transformWithCoin_eq_gadgetPhase_add_correctResidualAtTarget
    params coordinate candidate targetSecret challenge auxiliary ringSecret
    reconstructedCoin outputCoordinate (finProdFinEquiv index) hcandidate
  change TLWE.phase (embedRingSecret q ringSecret)
      (TLWE.entry
        ((transformWithDifference params coordinate candidate challenge auxiliary
          coin).1 outputCoordinate) (finProdFinEquiv index)) = _ at h
  change _ = Native.ShiftedCandidateEvaluator.proofAdd _
      (Native.ShiftedCandidateEvaluator.correctBootstrappingResidual params
        (embedRingSecret q ringSecret) targetSecret coordinate source
        (Native.ShiftedCandidateEvaluator.addDifference source coin.2)
        outputCoordinate (finProdFinEquiv index)) at h
  rw [Native.ShiftedCandidateEvaluator.correctBootstrappingResidual_addDifference_eq_sourceError_add_controlResidual]
    at h
  exact h

end

end FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery.AugmentedResidual.NativeShifted
