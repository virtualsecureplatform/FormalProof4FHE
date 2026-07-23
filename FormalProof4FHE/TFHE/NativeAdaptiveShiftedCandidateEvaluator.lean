/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeShiftedCandidateEvaluator
import FormalProof4FHE.TFHE.AdaptiveAugmentedResidualCandidateView

/-!
# Native Adaptive Shifted-Candidate Evaluator

This file wires the executable native TGSW shifted evaluator into the complete adaptive public
context `(BRK, KSK, input tape)` used by augmented TFHE CircLWE recovery.

One evaluator coin contains a uniform scalar XOR mask and a uniform true-branch BRK.  The scalar
mask publicly transports all three correlated components.  The candidate bit is transported by
the same coordinate mask, and the resulting candidate-controlled CMux is applied pointwise to the
transported BRK.  The transported KSK and input tape are retained unchanged after that CMux step.
The correct and complementary fixed-coin branches also expose exact complete-ciphertext forms:
the selected base BRK entry plus one named homogeneous-control internal-product perturbation.

Thus the remaining construction-specific premise is no longer allowed to choose an arbitrary
candidate transform: it must prove averaged correct-view and rank/freshness bounds for the
concrete `transform` below.  The correct branch has a fixed executable residual sampler and an
exact conditioned-coin reparameterization, leaving only output-mask/error-law freshness and
quantitative smudging of that explicit perturbation on that side; the minimal direct interface
remains available.
-/

open OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery.AugmentedResidual.NativeShifted

open Native
open FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery
open FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery
open FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery.AugmentedResidual

variable
  {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ}

/-- Randomness used by one complete native candidate evaluation: a scalar XOR mask and an
independent uniform true-branch BRK. -/
abbrev Coin (q degree ringRank tgswLevels lweDimension : ℕ) :=
  BinarySecret lweDimension ×
    Native.BootstrappingKey q degree ringRank tgswLevels lweDimension

/-- Uniform, independent evaluator coins. -/
noncomputable def sampleCoin (q degree ringRank tgswLevels lweDimension : ℕ) [NeZero q] :
    ProbComp (Coin q degree ringRank tgswLevels lweDimension) := do
  let mask ← $ᵗ (BinarySecret lweDimension)
  let trueBranch ←
    $ᵗ (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
  return (mask, trueBranch)

/-- Transport a candidate by the same public XOR mask used for the scalar secret. -/
def transportCandidate {lweDimension : ℕ} (coordinate : Fin lweDimension)
    (candidate : Bool) (mask : BinarySecret lweDimension) : Bool :=
  LWE.MultiKeyAffine.maskedBit candidate (mask coordinate)

/-- Correctness of candidate transport is definitional: an honest candidate is sent to the
corresponding coordinate of the transported secret. -/
theorem transportCandidate_correct {lweDimension : ℕ}
    (coordinate : Fin lweDimension) (hidden mask : BinarySecret lweDimension) :
    transportCandidate coordinate (hidden coordinate) mask =
      Native.ScalarSecretRandomization.maskedSecret hidden mask coordinate := by
  rfl

/-- Complementary candidates remain complementary after XOR transport. -/
theorem transportCandidate_wrong {lweDimension : ℕ}
    (coordinate : Fin lweDimension) (hidden mask : BinarySecret lweDimension) :
    transportCandidate coordinate (!hidden coordinate) mask =
      !(Native.ScalarSecretRandomization.maskedSecret hidden mask coordinate) := by
  simp only [transportCandidate, Native.ScalarSecretRandomization.maskedSecret]
  cases hhidden : hidden coordinate <;> cases hmask : mask coordinate <;>
    simp [LWE.MultiKeyAffine.maskedBit]

/-- Applying the transported complementary candidate to the transported selected BRK control
cancels the scalar XOR mask exactly. -/
theorem candidateControl_transformBootstrappingKey_wrong
    (params : Gadget.Base.Parameters q) (coordinate : Fin lweDimension)
    (hidden : Bool) (mask : BinarySecret lweDimension)
    (source : Native.BootstrappingKey q degree ringRank params.levels lweDimension) :
    Native.ShiftedCandidateEvaluator.candidateControl params
        (transportCandidate coordinate (!hidden) mask)
        ((Native.ScalarSecretRandomization.transformBootstrappingKey
          (Gadget.Base.ringGadget params) mask source) coordinate) =
      Native.ShiftedCandidateEvaluator.candidateControl params (!hidden)
        (source coordinate) := by
  exact Native.ScalarSecretRandomization.toggleTGSW_maskedBit_comp
    (Gadget.Base.ringGadget params) (!hidden) (mask coordinate) (source coordinate)

/-- Override one mask coordinate with the unique XOR mask that transports `sourceBit` to
`targetBit`.  All other coordinates remain supplied by `baseMask`. -/
def conditionedMask {lweDimension : ℕ} (coordinate : Fin lweDimension)
    (sourceBit targetBit : Bool) (baseMask : BinarySecret lweDimension) :
    BinarySecret lweDimension :=
  Function.update baseMask coordinate
    (LWE.MultiKeyAffine.maskedBit sourceBit targetBit)

@[simp]
theorem conditionedMask_coordinate {lweDimension : ℕ}
    (coordinate : Fin lweDimension) (sourceBit targetBit : Bool)
    (baseMask : BinarySecret lweDimension) :
    conditionedMask coordinate sourceBit targetBit baseMask coordinate =
      LWE.MultiKeyAffine.maskedBit sourceBit targetBit := by
  simp [conditionedMask]

/-- The conditioned coordinate transports the supplied source bit to the requested target bit. -/
@[simp]
theorem transportCandidate_conditionedMask {lweDimension : ℕ}
    (coordinate : Fin lweDimension) (sourceBit targetBit : Bool)
    (baseMask : BinarySecret lweDimension) :
    transportCandidate coordinate sourceBit
        (conditionedMask coordinate sourceBit targetBit baseMask) = targetBit := by
  simp [transportCandidate, conditionedMask]

/-- XOR by one fixed source bit as a permutation of Boolean mask bits. -/
def maskedBitEquiv (sourceBit : Bool) : Bool ≃ Bool where
  toFun := LWE.MultiKeyAffine.maskedBit sourceBit
  invFun := LWE.MultiKeyAffine.maskedBit sourceBit
  left_inv := LWE.MultiKeyAffine.maskedBit_involutive sourceBit
  right_inv := LWE.MultiKeyAffine.maskedBit_involutive sourceBit

/-- The mask bit solving `sourceBit XOR maskBit = targetBit` is uniform when `targetBit` is. -/
theorem maskedBit_uniform_evalDist (sourceBit : Bool) :
    evalDist (LWE.MultiKeyAffine.maskedBit sourceBit <$> ($ᵗ Bool)) =
      evalDist ($ᵗ Bool) :=
  evalDist_map_bijective_uniform_cross
    (α := Bool) (β := Bool) (LWE.MultiKeyAffine.maskedBit sourceBit)
    (maskedBitEquiv sourceBit).bijective

/-- Sample a uniform target bit and a mask conditioned to transport the fixed source bit to it. -/
noncomputable def sampleConditionedBitAndMask
    (coordinate : Fin lweDimension) (sourceBit : Bool) :
    ProbComp (Bool × BinarySecret lweDimension) := do
  let targetBit ← $ᵗ Bool
  let baseMask ← $ᵗ BinarySecret lweDimension
  return (targetBit, conditionedMask coordinate sourceBit targetBit baseMask)

/-- Sample an ordinary uniform mask and derive the transported candidate bit from it. -/
noncomputable def sampleDerivedBitAndMask
    (coordinate : Fin lweDimension) (sourceBit : Bool) :
    ProbComp (Bool × BinarySecret lweDimension) := do
  let mask ← $ᵗ BinarySecret lweDimension
  return (transportCandidate coordinate sourceBit mask, mask)

/-- Conditioning on a fresh uniform target bit is an exact reparameterization of the original
uniform scalar mask at the selected coordinate.  Hence this part of the concrete residual sampler
introduces no statistical loss. -/
theorem sampleConditionedBitAndMask_evalDist
    (coordinate : Fin lweDimension) (sourceBit : Bool) :
    evalDist (sampleConditionedBitAndMask coordinate sourceBit) =
      evalDist (sampleDerivedBitAndMask coordinate sourceBit) := by
  let bits : ProbComp Bool := $ᵗ Bool
  let masks : ProbComp (BinarySecret lweDimension) := $ᵗ BinarySecret lweDimension
  let maskedBits := LWE.MultiKeyAffine.maskedBit sourceBit <$> bits
  let overwritten : ProbComp (BinarySecret lweDimension) := do
    let maskBit ← bits
    let baseMask ← masks
    return Function.update baseMask coordinate maskBit
  let finish := fun mask : BinarySecret lweDimension =>
    (transportCandidate coordinate sourceBit mask, mask)
  have hoverwritten : evalDist overwritten = evalDist masks := by
    simpa only [overwritten, bits, masks] using
      (evalDist_uniformSample_bind_update (R := Bool) coordinate)
  calc
    evalDist (sampleConditionedBitAndMask coordinate sourceBit) =
        evalDist (maskedBits >>= fun maskBit =>
          masks >>= fun baseMask =>
            pure (LWE.MultiKeyAffine.maskedBit sourceBit maskBit,
              Function.update baseMask coordinate maskBit)) := by
      simp [sampleConditionedBitAndMask, conditionedMask, maskedBits, bits,
        masks, map_eq_bind_pure_comp, monad_norm]
    _ = evalDist (bits >>= fun maskBit =>
          masks >>= fun baseMask =>
            pure (LWE.MultiKeyAffine.maskedBit sourceBit maskBit,
              Function.update baseMask coordinate maskBit)) := by
      rw [evalDist_bind, maskedBit_uniform_evalDist sourceBit, ← evalDist_bind]
    _ = evalDist (finish <$> overwritten) := by
      simp [overwritten, finish, transportCandidate, bits, masks,
        map_eq_bind_pure_comp, monad_norm]
    _ = evalDist (finish <$> masks) := by
      rw [evalDist_map, hoverwritten, ← evalDist_map]
    _ = evalDist (sampleDerivedBitAndMask coordinate sourceBit) := by
      simp [sampleDerivedBitAndMask, finish, masks, map_eq_bind_pure_comp,
        monad_norm]

/-- Add the same independent uniform true-branch BRK to the conditioned mask experiment. -/
noncomputable def sampleConditionedBitAndCoin [NeZero q]
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (sourceBit : Bool) :
    ProbComp (Bool × Coin q degree ringRank params.levels lweDimension) := do
  let targetAndMask ← sampleConditionedBitAndMask coordinate sourceBit
  let trueBranch ←
    $ᵗ Native.BootstrappingKey q degree ringRank params.levels lweDimension
  return (targetAndMask.1, (targetAndMask.2, trueBranch))

/-- Original unconditioned coin experiment with its transported candidate bit exposed. -/
noncomputable def sampleDerivedBitAndCoin [NeZero q]
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (sourceBit : Bool) :
    ProbComp (Bool × Coin q degree ringRank params.levels lweDimension) := do
  let targetAndMask ← sampleDerivedBitAndMask coordinate sourceBit
  let trueBranch ←
    $ᵗ Native.BootstrappingKey q degree ringRank params.levels lweDimension
  return (targetAndMask.1, (targetAndMask.2, trueBranch))

/-- The complete conditioned evaluator coin, including its independent uniform true branch, is
an exact reparameterization of the original coin together with the transported candidate bit. -/
theorem sampleConditionedBitAndCoin_evalDist [NeZero q]
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (sourceBit : Bool) :
    evalDist (sampleConditionedBitAndCoin (degree := degree) (ringRank := ringRank)
        params coordinate sourceBit) =
      evalDist (sampleDerivedBitAndCoin (degree := degree) (ringRank := ringRank)
        params coordinate sourceBit) := by
  unfold sampleConditionedBitAndCoin sampleDerivedBitAndCoin
  rw [evalDist_bind,
    sampleConditionedBitAndMask_evalDist coordinate sourceBit, ← evalDist_bind]

/-- Evaluator coins conditioned only on the target scalar bit at the selected coordinate.  The
base mask remains uniform off that coordinate and the true-branch BRK remains fully uniform. -/
noncomputable def sampleConditionedCoin [NeZero q]
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (sourceBit : Bool)
    (targetSecret : BinarySecret lweDimension) :
    ProbComp (Coin q degree ringRank params.levels lweDimension) := do
  let baseMask ← $ᵗ BinarySecret lweDimension
  let trueBranch ←
    $ᵗ Native.BootstrappingKey q degree ringRank params.levels lweDimension
  return (conditionedMask coordinate sourceBit (targetSecret coordinate) baseMask,
    trueBranch)

@[simp]
theorem probFailure_sampleConditionedCoin [NeZero q]
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (sourceBit : Bool)
    (targetSecret : BinarySecret lweDimension) :
    probFailure (sampleConditionedCoin (degree := degree) (ringRank := ringRank)
      params coordinate sourceBit targetSecret) = 0 := by
  simp [sampleConditionedCoin]

/-- Public scalar transport of the complete evaluation-key-pair-plus-tape layout. -/
noncomputable def transportedView
    (params : Gadget.Base.Parameters q)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount)
    (mask : BinarySecret lweDimension) :
    ScalarTransport.View q degree ringRank params.levels lweDimension
      keySwitchLevels queryCount :=
  ScalarTransport.transformView
    (ringRank := ringRank) (keySwitchLevels := keySwitchLevels)
    (queryCount := queryCount) (Gadget.Base.ringGadget params) mask
    ((challenge, auxiliary.1), auxiliary.2)

/-- The normalized complementary-candidate control map is invariant under the complete public
scalar transport.  It is exactly the map obtained from the original selected BRK entry and the
original hidden bit. -/
theorem controlBranchTransform_transported_wrong
    (params : Gadget.Base.Parameters q) (coordinate : Fin lweDimension)
    (hidden : Bool)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount)
    (mask : BinarySecret lweDimension) :
    Native.ShiftedCandidateEvaluator.controlBranchTransform params
        (transportCandidate coordinate (!hidden) mask)
        ((transportedView params challenge auxiliary mask).1.1 coordinate) =
      Native.ShiftedCandidateEvaluator.controlBranchTransform params (!hidden)
        (challenge coordinate) := by
  funext difference
  unfold Native.ShiftedCandidateEvaluator.controlBranchTransform
  rw [show ((transportedView params challenge auxiliary mask).1.1 coordinate) =
      (Native.ScalarSecretRandomization.transformBootstrappingKey
        (Gadget.Base.ringGadget params) mask challenge) coordinate by rfl]
  rw [candidateControl_transformBootstrappingKey_wrong]

/-- The normalized one-row statistical defect is likewise invariant under scalar transport. -/
theorem controlBranchDistance_transported_wrong [NeZero q]
    (params : Gadget.Base.Parameters q) (coordinate : Fin lweDimension)
    (hidden : Bool)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount)
    (mask : BinarySecret lweDimension) :
    Native.ShiftedCandidateEvaluator.controlBranchDistance params
        (transportCandidate coordinate (!hidden) mask)
        ((transportedView params challenge auxiliary mask).1.1 coordinate) =
      Native.ShiftedCandidateEvaluator.controlBranchDistance params (!hidden)
        (challenge coordinate) := by
  unfold Native.ShiftedCandidateEvaluator.controlBranchDistance
  rw [controlBranchTransform_transported_wrong]

/-- Deterministic complete-context evaluator for fixed public coins. -/
noncomputable def transformWithCoin
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (candidate : Bool)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount)
    (coin : Coin q degree ringRank params.levels lweDimension) :
    PublicContext q degree ringRank params.levels lweDimension keySwitchLevels queryCount :=
  let transported := transportedView params challenge auxiliary coin.1
  let selected := Native.ShiftedCandidateEvaluator.selectBootstrappingKey
    params coordinate (transportCandidate coordinate candidate coin.1)
    transported.1.1 coin.2
  (selected, transported.1.2, transported.2)

/-- The concrete randomized shifted evaluator used by the augmented coordinate reduction. -/
noncomputable def transform [NeZero q]
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (candidate : Bool)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount) :
    ProbComp
      (PublicContext q degree ringRank params.levels lweDimension keySwitchLevels queryCount) :=
  transformWithCoin params coordinate candidate challenge auxiliary <$>
    sampleCoin q degree ringRank params.levels lweDimension

/-- Unfolding the randomized frontend exposes exactly one uniform coin sample. -/
theorem transform_eq_map_sampleCoin [NeZero q]
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (candidate : Bool)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount) :
    transform params coordinate candidate challenge auxiliary =
      transformWithCoin params coordinate candidate challenge auxiliary <$>
        sampleCoin q degree ringRank params.levels lweDimension := by
  rfl

/-- The selected challenge component is precisely the whole-BRK native shifted evaluator applied
after scalar transport. -/
theorem transformWithCoin_challenge
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (candidate : Bool)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount)
    (coin : Coin q degree ringRank params.levels lweDimension) :
    (transformWithCoin params coordinate candidate challenge auxiliary coin).1 =
      Native.ShiftedCandidateEvaluator.selectBootstrappingKey params coordinate
        (transportCandidate coordinate candidate coin.1)
        (transportedView params challenge auxiliary coin.1).1.1
      coin.2 := by
  rfl

/-- Complete-ciphertext correct endpoint at the adaptive fixed-coin boundary.  Once candidate
transport agrees with the supplied target-secret coordinate, the selected BRK entry is the
transported source entry plus the native homogeneous-control internal-product perturbation. -/
theorem transformWithCoin_challenge_correct_ciphertext
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (candidate : Bool)
    (targetSecret : BinarySecret lweDimension)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount)
    (coin : Coin q degree ringRank params.levels lweDimension)
    (outputCoordinate : Fin lweDimension)
    (hcandidate : transportCandidate coordinate candidate coin.1 =
      targetSecret coordinate) :
    (transformWithCoin params coordinate candidate challenge auxiliary coin).1
        outputCoordinate =
      Native.ShiftedCandidateEvaluator.addInternalProduct params
        ((transportedView params challenge auxiliary coin.1).1.1 outputCoordinate)
        (Native.ShiftedCandidateEvaluator.differenceDigits params
          (coin.2 outputCoordinate)
          ((transportedView params challenge auxiliary coin.1).1.1 outputCoordinate))
        (Native.ShiftedCandidateEvaluator.candidateHomogeneousPart params
          Native.ShiftedCandidateEvaluator.proofZero
          (targetSecret coordinate)
          ((transportedView params challenge auxiliary coin.1).1.1 coordinate)) := by
  change Native.ShiftedCandidateEvaluator.selectBootstrappingKey params coordinate
      (transportCandidate coordinate candidate coin.1)
      (transportedView params challenge auxiliary coin.1).1.1 coin.2 outputCoordinate = _
  rw [hcandidate]
  exact Native.ShiftedCandidateEvaluator.selectBootstrappingKey_correct_ciphertext
    params targetSecret coordinate outputCoordinate
    (transportedView params challenge auxiliary coin.1).1.1 coin.2

/-- Complete-ciphertext wrong endpoint at the adaptive fixed-coin boundary.  A complementary
transported candidate yields the fresh true-branch entry plus the native homogeneous-control
internal-product perturbation. -/
theorem transformWithCoin_challenge_wrong_ciphertext [NeZero q]
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (candidate : Bool)
    (targetSecret : BinarySecret lweDimension)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount)
    (coin : Coin q degree ringRank params.levels lweDimension)
    (outputCoordinate : Fin lweDimension)
    (hcandidate : transportCandidate coordinate candidate coin.1 =
      !targetSecret coordinate) :
    (transformWithCoin params coordinate candidate challenge auxiliary coin).1
        outputCoordinate =
      Native.ShiftedCandidateEvaluator.addInternalProduct params
        (coin.2 outputCoordinate)
        (Native.ShiftedCandidateEvaluator.differenceDigits params
          (coin.2 outputCoordinate)
          ((transportedView params challenge auxiliary coin.1).1.1 outputCoordinate))
        (Native.ShiftedCandidateEvaluator.candidateHomogeneousPart params
          Native.ShiftedCandidateEvaluator.proofOne
          (!targetSecret coordinate)
          ((transportedView params challenge auxiliary coin.1).1.1 coordinate)) := by
  change Native.ShiftedCandidateEvaluator.selectBootstrappingKey params coordinate
      (transportCandidate coordinate candidate coin.1)
      (transportedView params challenge auxiliary coin.1).1.1 coin.2 outputCoordinate = _
  rw [hcandidate]
  exact Native.ShiftedCandidateEvaluator.selectBootstrappingKey_wrong_ciphertext
    params targetSecret coordinate outputCoordinate
    (transportedView params challenge auxiliary coin.1).1.1 coin.2

/-- The KSK and tape are exactly the scalar-transported auxiliary context; the CMux step changes
only the BRK component. -/
theorem transformWithCoin_auxiliary
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (candidate : Bool)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount)
    (coin : Coin q degree ringRank params.levels lweDimension) :
    (transformWithCoin params coordinate candidate challenge auxiliary coin).2 =
      ((transportedView params challenge auxiliary coin.1).1.2,
       (transportedView params challenge auxiliary coin.1).2) := by
  rfl

/-! ## Concrete correct-branch residual -/

/-- The concrete BRK residual computed from a target secret, transported public source, and one
evaluator coin.  The KSK residual is zero because the CMux changes only the BRK; KSK and tape are
handled by the exact scalar-transport theorem. -/
noncomputable def correctResidualAtTarget
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension)
    (targetSecret : BinarySecret lweDimension)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount)
    (ringSecret : RingBinarySecret ringRank degree)
    (coin : Coin q degree ringRank params.levels lweDimension) :
    EvaluationKeyResidual q degree ringRank params.levels lweDimension keySwitchLevels :=
  (Native.ShiftedCandidateEvaluator.correctBootstrappingResidual params
      (embedRingSecret q ringSecret) targetSecret coordinate
      (transportedView params challenge auxiliary coin.1).1.1 coin.2,
    0)

/-- The actual fixed-coin evaluator has the exact target-secret phase plus the concrete computed
residual whenever its transported candidate equals the selected target-secret coordinate. -/
theorem phase_transformWithCoin_eq_gadgetPhase_add_correctResidualAtTarget
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (candidate : Bool)
    (targetSecret : BinarySecret lweDimension)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount)
    (ringSecret : RingBinarySecret ringRank degree)
    (coin : Coin q degree ringRank params.levels lweDimension)
    (outputCoordinate : Fin lweDimension)
    (row : Fin (TGSW.rowCount ringRank params.levels))
    (hcandidate : transportCandidate coordinate candidate coin.1 =
      targetSecret coordinate) :
    TLWE.phase (embedRingSecret q ringSecret)
        (TLWE.entry
          ((transformWithCoin params coordinate candidate challenge auxiliary coin).1
            outputCoordinate) row) =
      Native.ShiftedCandidateEvaluator.proofAdd
        (TGSW.gadgetPhase (embedRingSecret q ringSecret)
          (Gadget.Base.ringGadget params)
          (TGSW.cmuxMessage 0 0 (embedBit (targetSecret outputCoordinate))) row)
        ((correctResidualAtTarget params coordinate targetSecret challenge auxiliary
          ringSecret coin).1 outputCoordinate row) := by
  change TLWE.phase (embedRingSecret q ringSecret)
      (TLWE.entry
        (Native.ShiftedCandidateEvaluator.selectBootstrappingKey params coordinate
          (transportCandidate coordinate candidate coin.1)
          (transportedView params challenge auxiliary coin.1).1.1 coin.2
          outputCoordinate) row) = _
  rw [hcandidate]
  exact Native.ShiftedCandidateEvaluator.phase_entry_selectBootstrappingKey_correctResidual
    params (embedRingSecret q ringSecret) targetSecret coordinate outputCoordinate
    (transportedView params challenge auxiliary coin.1).1.1 coin.2 row

/-- Specialization to the actual correct candidate and its XOR-transported full scalar secret. -/
theorem phase_transformWithCoin_correct
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (hidden : BinarySecret lweDimension)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount)
    (ringSecret : RingBinarySecret ringRank degree)
    (coin : Coin q degree ringRank params.levels lweDimension)
    (outputCoordinate : Fin lweDimension)
    (row : Fin (TGSW.rowCount ringRank params.levels)) :
    TLWE.phase (embedRingSecret q ringSecret)
        (TLWE.entry
          ((transformWithCoin params coordinate (hidden coordinate)
            challenge auxiliary coin).1 outputCoordinate) row) =
      Native.ShiftedCandidateEvaluator.proofAdd
        (TGSW.gadgetPhase (embedRingSecret q ringSecret)
          (Gadget.Base.ringGadget params)
          (TGSW.cmuxMessage 0 0
            (embedBit
              (Native.ScalarSecretRandomization.maskedSecret hidden coin.1
                outputCoordinate))) row)
        ((correctResidualAtTarget params coordinate
          (Native.ScalarSecretRandomization.maskedSecret hidden coin.1)
          challenge auxiliary ringSecret coin).1 outputCoordinate row) :=
  phase_transformWithCoin_eq_gadgetPhase_add_correctResidualAtTarget
    params coordinate (hidden coordinate)
    (Native.ScalarSecretRandomization.maskedSecret hidden coin.1)
    challenge auxiliary ringSecret coin outputCoordinate row
    (transportCandidate_correct coordinate hidden coin.1)

/-- Residual sampler used by the concrete sampled-normal-form boundary.  It conditions the one
selected mask coordinate so the evaluator's candidate is exactly the supplied target-secret bit,
then computes the actual native CMux residual from that coin. -/
noncomputable def concreteCorrectResidualSampler [NeZero q]
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (sourceBit : Bool)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount)
    (secrets : Secret lweDimension ringRank degree) :
    ProbComp
      (EvaluationKeyResidual q degree ringRank params.levels lweDimension keySwitchLevels) := do
  let coin ← sampleConditionedCoin (degree := degree) (ringRank := ringRank)
    params coordinate sourceBit secrets.1
  return correctResidualAtTarget params coordinate secrets.1 challenge auxiliary
    secrets.2 coin

@[simp]
theorem probFailure_concreteCorrectResidualSampler [NeZero q]
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (sourceBit : Bool)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount)
    (secrets : Secret lweDimension ringRank degree) :
    probFailure (concreteCorrectResidualSampler params coordinate sourceBit
      challenge auxiliary secrets) = 0 := by
  simp [concreteCorrectResidualSampler]

/-- Every explicitly conditioned coin satisfies the concrete residual phase law. -/
theorem phase_transformWithConditionedCoin_correct
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (sourceBit : Bool)
    (targetSecret : BinarySecret lweDimension)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount)
    (ringSecret : RingBinarySecret ringRank degree)
    (baseMask : BinarySecret lweDimension)
    (trueBranch : Native.BootstrappingKey q degree ringRank params.levels lweDimension)
    (outputCoordinate : Fin lweDimension)
    (row : Fin (TGSW.rowCount ringRank params.levels)) :
    let coin : Coin q degree ringRank params.levels lweDimension :=
      (conditionedMask coordinate sourceBit (targetSecret coordinate) baseMask,
        trueBranch)
    TLWE.phase (embedRingSecret q ringSecret)
        (TLWE.entry
          ((transformWithCoin params coordinate sourceBit challenge auxiliary coin).1
            outputCoordinate) row) =
      Native.ShiftedCandidateEvaluator.proofAdd
        (TGSW.gadgetPhase (embedRingSecret q ringSecret)
          (Gadget.Base.ringGadget params)
          (TGSW.cmuxMessage 0 0 (embedBit (targetSecret outputCoordinate))) row)
        ((correctResidualAtTarget params coordinate targetSecret challenge auxiliary
          ringSecret coin).1 outputCoordinate row) := by
  dsimp only
  exact phase_transformWithCoin_eq_gadgetPhase_add_correctResidualAtTarget
    params coordinate sourceBit targetSecret challenge auxiliary ringSecret
    (conditionedMask coordinate sourceBit (targetSecret coordinate) baseMask,
      trueBranch) outputCoordinate row
    (transportCandidate_conditionedMask coordinate sourceBit
      (targetSecret coordinate) baseMask)

/-! ## Concrete wrong-branch freshness boundary -/

/-- Freshness predicate after fixing the public source context, scalar mask, and candidate. -/
def BranchFreshAtMask
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (candidate : Bool)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount)
    (mask : BinarySecret lweDimension) : Prop :=
  Native.ShiftedCandidateEvaluator.BranchFresh params coordinate
    (transportCandidate coordinate candidate mask)
    (transportedView params challenge auxiliary mask).1.1

/-- Rowwise formulation of freshness after fixing the public context and scalar mask. -/
def RowwiseBranchFreshAtMask
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (candidate : Bool)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount)
    (mask : BinarySecret lweDimension) : Prop :=
  Native.ShiftedCandidateEvaluator.RowwiseBranchFresh params coordinate
    (transportCandidate coordinate candidate mask)
    (transportedView params challenge auxiliary mask).1.1

/-- Fixed-mask rowwise freshness implies the original whole-BRK freshness predicate. -/
theorem branchFreshAtMask_of_rowwiseBranchFreshAtMask
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (candidate : Bool)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount)
    (mask : BinarySecret lweDimension)
    (hFresh : RowwiseBranchFreshAtMask params coordinate candidate challenge auxiliary mask) :
    BranchFreshAtMask params coordinate candidate challenge auxiliary mask :=
  Native.ShiftedCandidateEvaluator.branchFresh_of_rowwiseBranchFresh
    params coordinate (transportCandidate coordinate candidate mask)
    (transportedView params challenge auxiliary mask).1.1 hFresh

/-- Evaluate at one fixed scalar mask while sampling only the uniform true-branch BRK. -/
noncomputable def branchExperimentAtMask [NeZero q]
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (candidate : Bool)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount)
    (mask : BinarySecret lweDimension) :
    ProbComp
      (PublicContext q degree ringRank params.levels lweDimension keySwitchLevels queryCount) :=
  (fun trueBranch =>
    transformWithCoin params coordinate candidate challenge auxiliary
      (mask, trueBranch)) <$>
    ($ᵗ Native.BootstrappingKey q degree ringRank params.levels lweDimension)

/-- Uniform-BRK endpoint with the same fixed transported KSK and tape. -/
noncomputable def uniformExperimentAtMask [NeZero q]
    (params : Gadget.Base.Parameters q)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount)
    (mask : BinarySecret lweDimension) :
    ProbComp
      (PublicContext q degree ringRank params.levels lweDimension keySwitchLevels queryCount) :=
  (fun bootstrappingKey =>
    (bootstrappingKey, (transportedView params challenge auxiliary mask).1.2,
      (transportedView params challenge auxiliary mask).2)) <$>
    ($ᵗ Native.BootstrappingKey q degree ringRank params.levels lweDimension)

/-- Conditional exact wrong-branch law.  Once the concrete branch map is bijective, sampling its
true branch uniformly gives a uniform BRK independent of the fixed transported auxiliary context. -/
theorem branchExperimentAtMask_evalDist_eq_uniform [NeZero q]
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (candidate : Bool)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount)
    (mask : BinarySecret lweDimension)
    (hFresh : BranchFreshAtMask params coordinate candidate challenge auxiliary mask) :
    evalDist
        (branchExperimentAtMask params coordinate candidate challenge auxiliary mask) =
      evalDist (uniformExperimentAtMask params challenge auxiliary mask) := by
  let transported := transportedView params challenge auxiliary mask
  let branch := Native.ShiftedCandidateEvaluator.branchTransform params coordinate
    (transportCandidate coordinate candidate mask) transported.1.1
  let finish := fun bootstrappingKey : Native.BootstrappingKey q degree ringRank
      params.levels lweDimension =>
    (bootstrappingKey, transported.1.2, transported.2)
  have hbranch := Native.ShiftedCandidateEvaluator.branchTransform_uniform_evalDist
    params coordinate (transportCandidate coordinate candidate mask)
    transported.1.1 hFresh
  have hmapped := evalDist_map_eq_of_evalDist_eq hbranch finish
  simpa only [branchExperimentAtMask, uniformExperimentAtMask, transformWithCoin,
    transported, branch, finish, Native.ShiftedCandidateEvaluator.branchTransform,
    Native.ShiftedCandidateEvaluator.selectBootstrappingKey,
    map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind] using hmapped

/-- Construction-level freshness hypothesis: the complementary-candidate branch map is a
permutation for every hidden bit, public context, and scalar mask.  This is the exact algebraic
rank/freshness statement that remains to be proved (or weakened to a statistical bad-event
bound) for the native CMux map. -/
def WrongBranchFresh
    (params : Gadget.Base.Parameters q) : Prop :=
  ∀ (coordinate : Fin lweDimension) (hidden : Bool)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount)
    (mask : BinarySecret lweDimension),
    BranchFreshAtMask params coordinate (!hidden) challenge auxiliary mask

/-- Entrywise formulation of exact complementary-branch freshness after scalar-mask transport. -/
def WrongBranchEntrywiseFresh
    (params : Gadget.Base.Parameters q) : Prop :=
  ∀ (coordinate : Fin lweDimension) (hidden : Bool)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount)
    (mask : BinarySecret lweDimension),
    Native.ShiftedCandidateEvaluator.EntrywiseBranchFresh params coordinate
      (transportCandidate coordinate (!hidden) mask)
      (transportedView params challenge auxiliary mask).1.1

/-- Rowwise formulation of exact complementary-branch freshness.  It exposes only explicit
bijectivity predicates on one native TLWE row at a time. -/
def WrongBranchRowwiseFresh
    (params : Gadget.Base.Parameters q) : Prop :=
  ∀ (coordinate : Fin lweDimension) (hidden : Bool)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount)
    (mask : BinarySecret lweDimension),
    Native.ShiftedCandidateEvaluator.RowwiseBranchFresh params coordinate
      (transportCandidate coordinate (!hidden) mask)
      (transportedView params challenge auxiliary mask).1.1

/-- Rowwise native CMux bijectivity lifts to the entrywise transported condition. -/
theorem wrongBranchEntrywiseFresh_of_rowwise
    (params : Gadget.Base.Parameters q)
    (hFresh : WrongBranchRowwiseFresh (degree := degree) (ringRank := ringRank)
      (lweDimension := lweDimension) (keySwitchLevels := keySwitchLevels)
      (queryCount := queryCount) params) :
    WrongBranchEntrywiseFresh (degree := degree) (ringRank := ringRank)
      (lweDimension := lweDimension) (keySwitchLevels := keySwitchLevels)
      (queryCount := queryCount) params := by
  intro coordinate hidden challenge auxiliary mask
  exact Native.ShiftedCandidateEvaluator.entrywiseBranchFresh_of_rowwiseBranchFresh
    params coordinate (transportCandidate coordinate (!hidden) mask)
    (transportedView params challenge auxiliary mask).1.1
    (hFresh coordinate hidden challenge auxiliary mask)

/-- Entrywise transported bijectivity discharges the original whole-BRK freshness predicate. -/
theorem wrongBranchFresh_of_entrywise
    (params : Gadget.Base.Parameters q)
    (hFresh : WrongBranchEntrywiseFresh (degree := degree) (ringRank := ringRank)
      (lweDimension := lweDimension) (keySwitchLevels := keySwitchLevels)
      (queryCount := queryCount) params) :
    WrongBranchFresh (degree := degree) (ringRank := ringRank)
      (lweDimension := lweDimension) (keySwitchLevels := keySwitchLevels)
      (queryCount := queryCount) params := by
  intro coordinate hidden challenge auxiliary mask
  exact Native.ShiftedCandidateEvaluator.branchFresh_of_entrywiseBranchFresh
    params coordinate (transportCandidate coordinate (!hidden) mask)
    (transportedView params challenge auxiliary mask).1.1
    (hFresh coordinate hidden challenge auxiliary mask)

/-- Exact wrong-branch freshness follows from the family of explicit single-row bijectivity laws. -/
theorem wrongBranchFresh_of_rowwise
    (params : Gadget.Base.Parameters q)
    (hFresh : WrongBranchRowwiseFresh (degree := degree) (ringRank := ringRank)
      (lweDimension := lweDimension) (keySwitchLevels := keySwitchLevels)
      (queryCount := queryCount) params) :
    WrongBranchFresh (degree := degree) (ringRank := ringRank)
      (lweDimension := lweDimension) (keySwitchLevels := keySwitchLevels)
      (queryCount := queryCount) params :=
  wrongBranchFresh_of_entrywise params
    (wrongBranchEntrywiseFresh_of_rowwise params hFresh)

/-- Actual correct-candidate experiment averaged over the complete augmented coordinate source. -/
noncomputable def averagedCorrectTransform [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    ProbComp
      (PublicContext q degree ringRank params.levels lweDimension keySwitchLevels queryCount) := do
  let hiddenAndContext ← coordinateSource (ringRank := ringRank)
    (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler inputErrorSampler
    (Gadget.Base.ringGadget params) keySwitchGadget coordinate
  transform params coordinate hiddenAndContext.1
    hiddenAndContext.2.1 hiddenAndContext.2.2

/-- Actual wrong-candidate experiment averaged over the complete augmented coordinate source. -/
noncomputable def averagedWrongTransform [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    ProbComp
      (PublicContext q degree ringRank params.levels lweDimension keySwitchLevels queryCount) := do
  let hiddenAndContext ← coordinateSource (ringRank := ringRank)
    (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler inputErrorSampler
    (Gadget.Base.ringGadget params) keySwitchGadget coordinate
  transform params coordinate (!hiddenAndContext.1)
    hiddenAndContext.2.1 hiddenAndContext.2.2

/-- Same averaged source after replacing the CMux output by an exactly uniform BRK for each fixed
context and scalar mask. -/
noncomputable def averagedUniformized [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    ProbComp
      (PublicContext q degree ringRank params.levels lweDimension keySwitchLevels queryCount) := do
  let hiddenAndContext ← coordinateSource (ringRank := ringRank)
    (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler inputErrorSampler
    (Gadget.Base.ringGadget params) keySwitchGadget coordinate
  let mask ← $ᵗ BinarySecret lweDimension
  uniformExperimentAtMask params hiddenAndContext.2.1 hiddenAndContext.2.2 mask

/-- **Averaged wrong-candidate reduction to the explicit freshness predicate.**  If every native
wrong branch is bijective, then the actual complete-context evaluator is exactly its
uniform-BRK-per-mask endpoint. -/
theorem averagedWrongTransform_evalDist_eq_uniformized [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension)
    (hFresh : WrongBranchFresh (degree := degree) (ringRank := ringRank)
      (lweDimension := lweDimension) (keySwitchLevels := keySwitchLevels)
      (queryCount := queryCount) params) :
    evalDist
        (averagedWrongTransform (ringRank := ringRank) (queryCount := queryCount)
          params ringErrorSampler keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate) =
      evalDist
        (averagedUniformized (ringRank := ringRank) (queryCount := queryCount)
          params ringErrorSampler keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate) := by
  let source := coordinateSource (ringRank := ringRank) (queryCount := queryCount)
    ringErrorSampler keySwitchErrorSampler inputErrorSampler
    (Gadget.Base.ringGadget params) keySwitchGadget coordinate
  let masks := $ᵗ BinarySecret lweDimension
  unfold averagedWrongTransform transform sampleCoin
  simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
  calc
    _ = evalDist (source >>= fun hiddenAndContext =>
        masks >>= fun mask =>
          uniformExperimentAtMask params hiddenAndContext.2.1
            hiddenAndContext.2.2 mask) := by
      refine evalDist_bind_congr' source fun hiddenAndContext => ?_
      refine evalDist_bind_congr' masks fun mask => ?_
      simpa only [branchExperimentAtMask, map_eq_bind_pure_comp,
        Function.comp_def] using
        (branchExperimentAtMask_evalDist_eq_uniform params coordinate
          (!hiddenAndContext.1) hiddenAndContext.2.1 hiddenAndContext.2.2 mask
          (hFresh coordinate hiddenAndContext.1 hiddenAndContext.2.1
            hiddenAndContext.2.2 mask))
    _ = _ := by
      simp [averagedUniformized, source, masks, monad_norm]

/-- The explicit uniformized experiment is exactly the pre-existing augmented public uniform
endpoint.  This theorem discharges all scalar-mask, KSK, and adaptive-tape bookkeeping: only the
native BRK branch-freshness statement remains conditional. -/
theorem averagedUniformized_evalDist_eq_uniformPublicView [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    evalDist
        (averagedUniformized (ringRank := ringRank) (queryCount := queryCount)
          params ringErrorSampler keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate) =
      evalDist
        (uniformPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler
          inputErrorSampler (Gadget.Base.ringGadget params) keySwitchGadget) := by
  let ScalarSecrets := sampleLweSecret lweDimension
  let RingSecrets := sampleRingSecret ringRank degree
  let RealBootstrap := fun (lweSecret : BinarySecret lweDimension)
      (ringSecret : RingBinarySecret ringRank degree) =>
    BootstrapSecurity.MonomialKDM.generateBootstrappingKey q degree ringRank
      params.levels lweDimension ringErrorSampler (Gadget.Base.ringGadget params)
      lweSecret ringSecret
  let Aux := fun (lweSecret : BinarySecret lweDimension)
      (ringSecret : RingBinarySecret ringRank degree) => do
    let keySwitchKey ← generateKeySwitchKey q lweDimension (ringRank * degree)
      keySwitchLevels keySwitchErrorSampler keySwitchGadget
      (keyExtract ringSecret) lweSecret
    let tape ← TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
      (embedBinarySecret lweSecret) 0
    return (keySwitchKey, tape)
  let Masks := $ᵗ BinarySecret lweDimension
  let UniformBootstrap :=
    $ᵗ Native.BootstrappingKey q degree ringRank params.levels lweDimension
  let finish := fun (mask : BinarySecret lweDimension)
      (bootstrappingKey : Native.BootstrappingKey q degree ringRank
        params.levels lweDimension)
      (aux : Native.KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels ×
        KeySwitchFirstSecurity.InputTape q lweDimension queryCount) =>
    (bootstrappingKey,
      Native.ScalarSecretRandomization.transformKeySwitchKey mask aux.1,
      Native.ScalarSecretRandomization.transformBatch mask aux.2)
  let contextOfMasked := fun
      (maskedAndView : BinarySecret lweDimension ×
        ScalarTransport.View q degree ringRank params.levels lweDimension
          keySwitchLevels queryCount) =>
    (maskedAndView.2.1.1, maskedAndView.2.1.2, maskedAndView.2.2)
  let contextOfView := fun
      (view : ScalarTransport.View q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount) =>
    (view.1.1, view.1.2, view.2)
  have hshape :
      evalDist
          (averagedUniformized (ringRank := ringRank) (queryCount := queryCount)
            params ringErrorSampler keySwitchErrorSampler inputErrorSampler
            keySwitchGadget coordinate) =
        evalDist (ScalarSecrets >>= fun lweSecret =>
          RingSecrets >>= fun ringSecret =>
          RealBootstrap lweSecret ringSecret >>= fun _ =>
          Aux lweSecret ringSecret >>= fun aux =>
          Masks >>= fun mask =>
          UniformBootstrap >>= fun bootstrappingKey =>
          pure (finish mask bootstrappingKey aux)) := by
    simp [averagedUniformized, uniformExperimentAtMask, transportedView,
      coordinateSource, scalarSource, problem,
      LWE.AuxiliaryInput.Search.exactRecoveryProblem,
      KeySwitchFirstFiniteView.augmentedCircularProblem,
      KeySwitchFirstFiniteView.secretSampler, ScalarTransport.transformView,
      Native.ScalarSecretRandomization.transformEvaluationKeyPair,
      ScalarSecrets, RingSecrets, RealBootstrap, Aux, Masks, UniformBootstrap,
      finish, monad_norm]
  rw [hshape]
  calc
    _ = evalDist (ScalarSecrets >>= fun lweSecret =>
        RingSecrets >>= fun ringSecret =>
        Aux lweSecret ringSecret >>= fun aux =>
        Masks >>= fun mask =>
        UniformBootstrap >>= fun bootstrappingKey =>
        pure (finish mask bootstrappingKey aux)) := by
      refine evalDist_bind_congr' ScalarSecrets fun lweSecret => ?_
      refine evalDist_bind_congr' RingSecrets fun ringSecret => ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        (RealBootstrap lweSecret ringSecret) (by simp [RealBootstrap]) _
    _ = evalDist (ScalarSecrets >>= fun lweSecret =>
        RingSecrets >>= fun ringSecret =>
        Masks >>= fun mask =>
        Aux lweSecret ringSecret >>= fun aux =>
        UniformBootstrap >>= fun bootstrappingKey =>
        pure (finish mask bootstrappingKey aux)) := by
      refine evalDist_bind_congr' ScalarSecrets fun lweSecret => ?_
      refine evalDist_bind_congr' RingSecrets fun ringSecret => ?_
      exact evalDist_bind_bind_swap (Aux lweSecret ringSecret) Masks _
    _ = evalDist (ScalarSecrets >>= fun lweSecret =>
        RingSecrets >>= fun ringSecret =>
        Masks >>= fun mask =>
        UniformBootstrap >>= fun bootstrappingKey =>
        Aux lweSecret ringSecret >>= fun aux =>
        pure (finish mask bootstrappingKey aux)) := by
      refine evalDist_bind_congr' ScalarSecrets fun lweSecret => ?_
      refine evalDist_bind_congr' RingSecrets fun ringSecret => ?_
      refine evalDist_bind_congr' Masks fun mask => ?_
      exact evalDist_bind_bind_swap (Aux lweSecret ringSecret) UniformBootstrap _
    _ = evalDist (ScalarSecrets >>= fun lweSecret =>
        RingSecrets >>= fun ringSecret =>
        contextOfMasked <$>
          ScalarTransport.sampleMaskedUniformBootstrapView q degree ringRank
            params.levels lweDimension keySwitchLevels queryCount
            keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
            keySwitchGadget lweSecret ringSecret) := by
      refine evalDist_bind_congr' ScalarSecrets fun lweSecret => ?_
      refine evalDist_bind_congr' RingSecrets fun ringSecret => ?_
      unfold ScalarTransport.sampleMaskedUniformBootstrapView
      simp only [map_eq_bind_pure_comp, Function.comp_def, bind_assoc, pure_bind]
      refine evalDist_bind_congr' Masks fun mask => ?_
      rw [evalDist_bind,
        ← Native.ScalarSecretRandomization.transformBootstrappingKey_uniform_evalDist
          (Gadget.Base.ringGadget params) mask,
        ← evalDist_bind]
      simp [ScalarTransport.sampleUniformBootstrapView,
        Native.ScalarSecretRandomization.sampleUniformBootstrapEvaluationKeyPair,
        ScalarTransport.transformView, Aux,
        Native.ScalarSecretRandomization.transformEvaluationKeyPair,
        finish, contextOfMasked, monad_norm]
    _ = evalDist (ScalarSecrets >>= fun _ =>
        RingSecrets >>= fun ringSecret =>
        contextOfMasked <$>
          ScalarTransport.sampleFreshUniformBootstrapView q degree ringRank
            params.levels lweDimension keySwitchLevels queryCount
            keySwitchErrorSampler inputErrorSampler keySwitchGadget ringSecret) := by
      refine evalDist_bind_congr' ScalarSecrets fun lweSecret => ?_
      refine evalDist_bind_congr' RingSecrets fun ringSecret => ?_
      exact evalDist_map_eq_of_evalDist_eq
        (ScalarTransport.sampleMaskedUniformBootstrapView_evalDist
          keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
          keySwitchGadget lweSecret ringSecret) contextOfMasked
    _ = evalDist (RingSecrets >>= fun ringSecret =>
        contextOfMasked <$>
          ScalarTransport.sampleFreshUniformBootstrapView q degree ringRank
            params.levels lweDimension keySwitchLevels queryCount
            keySwitchErrorSampler inputErrorSampler keySwitchGadget ringSecret) := by
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        ScalarSecrets (by simp [ScalarSecrets]) _
    _ = evalDist (ScalarSecrets >>= fun lweSecret =>
        RingSecrets >>= fun ringSecret =>
        contextOfView <$>
          ScalarTransport.sampleUniformBootstrapView q degree ringRank
            params.levels lweDimension keySwitchLevels queryCount
            keySwitchErrorSampler inputErrorSampler keySwitchGadget
            lweSecret ringSecret) := by
      unfold ScalarTransport.sampleFreshUniformBootstrapView
      simpa only [ScalarSecrets, sampleLweSecret, contextOfMasked,
        contextOfView, map_eq_bind_pure_comp, Function.comp_def, bind_assoc,
        pure_bind] using
        (evalDist_bind_bind_swap RingSecrets ScalarSecrets
          (fun ringSecret lweSecret =>
            contextOfView <$>
              ScalarTransport.sampleUniformBootstrapView q degree ringRank
                params.levels lweDimension keySwitchLevels queryCount
                keySwitchErrorSampler inputErrorSampler keySwitchGadget
                lweSecret ringSecret))
    _ = _ := by
      simp [uniformPublicView,
        ScalarTransport.sampleUniformBootstrapView,
        Native.ScalarSecretRandomization.sampleUniformBootstrapEvaluationKeyPair,
        KeySwitchFirstFiniteView.augmentedCircularProblem,
        KeySwitchFirstFiniteView.secretSampler, ScalarSecrets, RingSecrets,
        contextOfView, monad_norm]

/-- **Conditional native wrong-candidate endpoint.**  Under the explicit construction-level
branch-freshness predicate, the executable wrong-candidate evaluator reaches the exact augmented
uniform public view. -/
theorem averagedWrongTransform_evalDist_eq_uniformPublicView [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension)
    (hFresh : WrongBranchFresh (degree := degree) (ringRank := ringRank)
      (lweDimension := lweDimension) (keySwitchLevels := keySwitchLevels)
      (queryCount := queryCount) params) :
    evalDist
        (averagedWrongTransform (ringRank := ringRank) (queryCount := queryCount)
          params ringErrorSampler keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate) =
      evalDist
        (uniformPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler
          inputErrorSampler (Gadget.Base.ringGadget params) keySwitchGadget) :=
  (averagedWrongTransform_evalDist_eq_uniformized
    params ringErrorSampler keySwitchErrorSampler inputErrorSampler
    keySwitchGadget coordinate hFresh).trans
    (averagedUniformized_evalDist_eq_uniformPublicView
      params ringErrorSampler keySwitchErrorSampler inputErrorSampler
      keySwitchGadget coordinate)

/-! ## Statistical branch-freshness boundary -/

/-- Average one fixed public context over the scalar mask while retaining the actual native
branch transform.  Unlike `BranchFreshAtMask`, this experiment permits rank loss on a small set
of masks and records its effect through total variation. -/
noncomputable def maskedBranchExperiment [NeZero q]
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (candidate : Bool)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount) :
    ProbComp
      (PublicContext q degree ringRank params.levels lweDimension keySwitchLevels queryCount) := do
  let mask ← $ᵗ BinarySecret lweDimension
  branchExperimentAtMask params coordinate candidate challenge auxiliary mask

/-- Uniform-BRK comparison experiment averaged over the same scalar mask. -/
noncomputable def maskedUniformExperiment [NeZero q]
    (params : Gadget.Base.Parameters q)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount) :
    ProbComp
      (PublicContext q degree ringRank params.levels lweDimension keySwitchLevels queryCount) := do
  let mask ← $ᵗ BinarySecret lweDimension
  uniformExperimentAtMask params challenge auxiliary mask

/-- Zero-one cost of rowwise freshness failure at one fixed public context and mask. -/
noncomputable def rowwiseFailureIndicator
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (candidate : Bool)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount)
    (mask : BinarySecret lweDimension) : ℝ := by
  classical
  exact if RowwiseBranchFreshAtMask params coordinate candidate challenge auxiliary mask
    then 0 else 1

/-- The fixed-mask branch distance is zero on rowwise-fresh contexts and is always at most one
otherwise.  This converts the exact rowwise algebraic condition into a statistical bad event. -/
theorem tvDist_branchExperimentAtMask_uniformExperimentAtMask_le_rowwiseFailureIndicator
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (candidate : Bool)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount)
    (mask : BinarySecret lweDimension) :
    tvDist
        (branchExperimentAtMask params coordinate candidate challenge auxiliary mask)
        (uniformExperimentAtMask params challenge auxiliary mask) ≤
      rowwiseFailureIndicator params coordinate candidate challenge auxiliary mask := by
  classical
  unfold rowwiseFailureIndicator
  by_cases hFresh :
      RowwiseBranchFreshAtMask params coordinate candidate challenge auxiliary mask
  · simp only [hFresh, if_pos]
    unfold tvDist
    rw [branchExperimentAtMask_evalDist_eq_uniform params coordinate candidate
      challenge auxiliary mask
      (branchFreshAtMask_of_rowwiseBranchFreshAtMask params coordinate candidate
        challenge auxiliary mask hFresh)]
    exact le_of_eq (SPMF.tvDist_self _)
  · simp only [hFresh]
    exact tvDist_le_one _ _

/-- Joint sampler of the real augmented coordinate context and the independent scalar XOR mask
used by the wrong-candidate evaluator. -/
noncomputable def wrongBranchRowwiseFailureSampler [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    ProbComp
      ((Bool × PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount) × BinarySecret lweDimension) := do
  let hiddenAndContext ← coordinateSource (ringRank := ringRank)
    (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler inputErrorSampler
    (Gadget.Base.ringGadget params) keySwitchGadget coordinate
  let mask ← $ᵗ BinarySecret lweDimension
  return (hiddenAndContext, mask)

/-- Projecting away the independent evaluator mask recovers the original correlated coordinate
source exactly. -/
theorem wrongBranchRowwiseFailureSampler_fst_evalDist [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    evalDist ((fun sample => sample.1) <$>
        wrongBranchRowwiseFailureSampler (ringRank := ringRank)
          (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
          inputErrorSampler keySwitchGadget coordinate) =
      evalDist (coordinateSource (ringRank := ringRank) (queryCount := queryCount)
        ringErrorSampler keySwitchErrorSampler inputErrorSampler
        (Gadget.Base.ringGadget params) keySwitchGadget coordinate) := by
  let source := coordinateSource (ringRank := ringRank) (queryCount := queryCount)
    ringErrorSampler keySwitchErrorSampler inputErrorSampler
    (Gadget.Base.ringGadget params) keySwitchGadget coordinate
  calc
    _ = evalDist (source >>= fun hiddenAndContext =>
        ($ᵗ BinarySecret lweDimension) >>= fun _ => pure hiddenAndContext) := by
      simp [wrongBranchRowwiseFailureSampler, source, map_eq_bind_pure_comp,
        monad_norm]
    _ = evalDist (source >>= fun hiddenAndContext => pure hiddenAndContext) := by
      refine evalDist_bind_congr' source fun hiddenAndContext => ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        ($ᵗ BinarySecret lweDimension) (by simp) (pure hiddenAndContext)
    _ = _ := by simp [source]

/-- Bad event that at least one explicit TLWE-row map fails the sufficient bijectivity condition
for the complementary candidate in the sampled public context and mask. -/
def WrongBranchRowwiseFailure
    (params : Gadget.Base.Parameters q) (coordinate : Fin lweDimension)
    (sample :
      (Bool × PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount) × BinarySecret lweDimension) : Prop :=
  ¬RowwiseBranchFreshAtMask params coordinate (!sample.1.1)
    sample.1.2.1 sample.1.2.2 sample.2

/-- Actual average-case native rowwise-rank failure over both the generated public context and
the independent scalar XOR mask.  Unlike a support-wise premise, rare bad BRKs are charged by
their probability. -/
noncomputable def averagedWrongBranchRowwiseFailure [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) : ℝ :=
  Pr[WrongBranchRowwiseFailure params coordinate |
    wrongBranchRowwiseFailureSampler (ringRank := ringRank) (queryCount := queryCount)
      params ringErrorSampler keySwitchErrorSampler inputErrorSampler keySwitchGadget
      coordinate].toReal

/-- Failure of one named TLWE-row branch map in the sampled public context and scalar mask. -/
def WrongBranchRowFailure
    (params : Gadget.Base.Parameters q) (coordinate outputCoordinate : Fin lweDimension)
    (row : Fin (TGSW.rowCount ringRank params.levels))
    (sample :
      (Bool × PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount) × BinarySecret lweDimension) : Prop :=
  ¬Native.ShiftedCandidateEvaluator.RowBranchFresh params
    (transportCandidate coordinate (!sample.1.1) sample.2)
    ((transportedView params sample.1.2.1 sample.1.2.2 sample.2).1.1 coordinate)
    (TLWE.entry
      ((transportedView params sample.1.2.1 sample.1.2.2 sample.2).1.1 outputCoordinate)
      row)

/-- The single normalized control-map failure shared by every row of the sampled wrong branch.
The false/data row is absent because it changes the row map only by translation conjugacy. -/
def WrongBranchControlFailure
    (params : Gadget.Base.Parameters q) (coordinate : Fin lweDimension)
    (sample :
      (Bool × PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount) × BinarySecret lweDimension) : Prop :=
  ¬Native.ShiftedCandidateEvaluator.ControlBranchFresh params
    (transportCandidate coordinate (!sample.1.1) sample.2)
    ((transportedView params sample.1.2.1 sample.1.2.2 sample.2).1.1 coordinate)

/-- The same normalized failure event before scalar transport and before adjoining the evaluator
mask.  It depends only on the hidden coordinate bit and its original selected BRK control. -/
def WrongBranchSourceControlFailure
    (params : Gadget.Base.Parameters q) (coordinate : Fin lweDimension)
    (hiddenAndContext :
      Bool × PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount) : Prop :=
  ¬Native.ShiftedCandidateEvaluator.ControlBranchFresh params
    (!hiddenAndContext.1) (hiddenAndContext.2.1 coordinate)

/-- Minimal marginal exposed by the native freshness obligation: one hidden scalar bit and its
selected original BRK control. -/
noncomputable def wrongBranchSelectedControlSampler [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    ProbComp (Bool × RingGSWCiphertext q degree ringRank params.levels) :=
  (fun hiddenAndContext =>
    (hiddenAndContext.1, hiddenAndContext.2.1 coordinate)) <$>
    coordinateSource (ringRank := ringRank) (queryCount := queryCount)
      ringErrorSampler keySwitchErrorSampler inputErrorSampler
      (Gadget.Base.ringGadget params) keySwitchGadget coordinate

/-- One native TRGSW control generated from only the data that can affect it: a scalar bit and
the shared ring secret.  This is the per-coordinate sampler hidden inside native BRK generation. -/
noncomputable def generatedControlSampler [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (hidden : Bool) (ringSecret : RingBinarySecret ringRank degree) :
    ProbComp (RingGSWCiphertext q degree ringRank params.levels) :=
  TGSW.MonomialKDM.expandedDirectEncrypt ringRank params.levels ringErrorSampler
    (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
    (embedConstantBit q degree hidden)
    (TGSW.MonomialKDM.crossMonomial
      (embedRingSecret q ringSecret) (embedConstantBit q degree hidden))

/-- Canonical one-control experiment.  It contains no KSK, input tape, unselected scalar bits,
or unselected BRK entries, and its law is independent of the named scalar coordinate. -/
noncomputable def canonicalWrongBranchControlSampler [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree)) :
    ProbComp (Bool × RingGSWCiphertext q degree ringRank params.levels) := do
  let hidden ← $ᵗ Bool
  let ringSecret ← sampleRingSecret ringRank degree
  let control ← generatedControlSampler (ringRank := ringRank)
    params ringErrorSampler hidden ringSecret
  return (hidden, control)

/-- For centered-binomial noise, applying the complementary candidate to one generated native
control changes its law exactly to that of a generated message-one control.  The sign change in
the homogeneous TGSW noise is absorbed by coefficientwise centered-binomial symmetry. -/
theorem candidateControl_generatedControl_centeredBinomial_wrong_evalDist
    {q degree ringRank eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) (hidden : Bool)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    evalDist
        (Native.ShiftedCandidateEvaluator.candidateControl params (!hidden) <$>
          generatedControlSampler (ringRank := ringRank) params
            (RLWE.CenteredBinomial.sampler q (degree + 1) eta) hidden ringSecret) =
      evalDist
        (generatedControlSampler (ringRank := ringRank) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta) true ringSecret) := by
  unfold generatedControlSampler Native.ShiftedCandidateEvaluator.candidateControl
  rw [← TGSW.MonomialKDM.directEncrypt_eq_expandedDirectEncrypt,
    ← TGSW.MonomialKDM.directEncrypt_eq_expandedDirectEncrypt]
  calc
    _ = evalDist
        (Native.ScalarSecretRandomization.toggleTGSW
            (Gadget.Base.ringGadget params) (!hidden) <$>
          TGSW.encrypt ringRank params.levels
            (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
            (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
            (embedConstantBit q (degree + 1) hidden)) := by
      exact evalDist_map_eq_of_evalDist_eq
        (TGSW.encrypt_evalDist_eq_directEncrypt ringRank params.levels
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) hidden)).symm _
    _ = evalDist
        (TGSW.encrypt ringRank params.levels
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) true)) := by
      simpa [Native.ShiftedCandidateEvaluator.maskedBit_not_self] using
        (Native.ScalarSecretRandomization.toggleTGSW_centeredBinomial_encrypt_evalDist
          (q := q) (degree := degree) (eta := eta)
          (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
          hidden (!hidden))
    _ = _ := TGSW.encrypt_evalDist_eq_directEncrypt ringRank params.levels
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
      (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
      (embedConstantBit q (degree + 1) true)

/-- Canonical normalized wrong-control experiment after eliminating the hidden scalar bit.  It
samples only a uniform ring secret and one native centered-binomial TRGSW encryption of message
one. -/
noncomputable def canonicalMessageOneControlSampler [NeZero q]
    (params : Gadget.Base.Parameters q) (eta : ℕ) :
    ProbComp (RingGSWCiphertext q (degree + 1) ringRank params.levels) := do
  let ringSecret ← sampleRingSecret ringRank (degree + 1)
  generatedControlSampler (ringRank := ringRank) params
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta) true ringSecret

/-- Toggling the canonical wrong-candidate control erases the uniform hidden bit exactly and
leaves the canonical message-one control law. -/
theorem canonicalWrongBranchControl_candidateControl_evalDist_eq_messageOne
    {q degree ringRank eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) :
    evalDist
        ((fun hiddenAndControl =>
            Native.ShiftedCandidateEvaluator.candidateControl params
              (!hiddenAndControl.1) hiddenAndControl.2) <$>
          canonicalWrongBranchControlSampler (ringRank := ringRank) params
            (RLWE.CenteredBinomial.sampler q (degree + 1) eta)) =
      evalDist
        (canonicalMessageOneControlSampler (ringRank := ringRank) params eta) := by
  let RingSecrets := sampleRingSecret ringRank (degree + 1)
  let normalized := fun (hidden : Bool)
      (ringSecret : RingBinarySecret ringRank (degree + 1)) =>
    Native.ShiftedCandidateEvaluator.candidateControl params (!hidden) <$>
      generatedControlSampler (ringRank := ringRank) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta) hidden ringSecret
  let messageOne := fun (ringSecret : RingBinarySecret ringRank (degree + 1)) =>
    generatedControlSampler (ringRank := ringRank) params
      (RLWE.CenteredBinomial.sampler q (degree + 1) eta) true ringSecret
  calc
    _ = evalDist (($ᵗ Bool) >>= fun hidden =>
        RingSecrets >>= normalized hidden) := by
      simp [canonicalWrongBranchControlSampler, RingSecrets, normalized,
        map_eq_bind_pure_comp, bind_assoc, monad_norm]
    _ = evalDist (($ᵗ Bool) >>= fun _ => RingSecrets >>= messageOne) := by
      refine evalDist_bind_congr' ($ᵗ Bool) fun hidden => ?_
      refine evalDist_bind_congr' RingSecrets fun ringSecret => ?_
      exact candidateControl_generatedControl_centeredBinomial_wrong_evalDist
        params hidden ringSecret
    _ = evalDist (RingSecrets >>= messageOne) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        ($ᵗ Bool) (by simp) _
    _ = _ := by
      simp [canonicalMessageOneControlSampler, RingSecrets, messageOne]

/-- The actual selected-control marginal has exactly the canonical one-control law whenever the
discarded KSK and input-error samplers are total.  In particular, all scalar coordinates have
the same freshness experiment. -/
theorem wrongBranchSelectedControlSampler_evalDist_eq_canonical [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    evalDist
        (wrongBranchSelectedControlSampler (ringRank := ringRank)
          (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
          inputErrorSampler keySwitchGadget coordinate) =
      evalDist
        (canonicalWrongBranchControlSampler (ringRank := ringRank)
          params ringErrorSampler) := by
  let LweSecrets := sampleLweSecret lweDimension
  let RingSecrets := sampleRingSecret ringRank degree
  let Controls := fun (lweSecret : BinarySecret lweDimension)
      (ringSecret : RingBinarySecret ringRank degree) =>
    Native.BootstrapSecurity.MonomialKDM.generateBootstrappingKey
      q degree ringRank params.levels lweDimension ringErrorSampler
      (Gadget.Base.ringGadget params) lweSecret ringSecret
  let Auxiliary := fun (lweSecret : BinarySecret lweDimension)
      (ringSecret : RingBinarySecret ringRank degree) => do
    let keySwitchKey ← generateKeySwitchKey q lweDimension (ringRank * degree)
      keySwitchLevels keySwitchErrorSampler keySwitchGadget
      (keyExtract ringSecret) lweSecret
    let tape ← TLWE.batchEncrypt lweDimension queryCount inputErrorSampler
      (embedBinarySecret lweSecret) 0
    return (keySwitchKey, tape)
  let Selected := fun (hidden : Bool)
      (ringSecret : RingBinarySecret ringRank degree) => do
    let control ← generatedControlSampler (ringRank := ringRank)
      params ringErrorSampler hidden ringSecret
    return (hidden, control)
  have hshape :
      evalDist
          (wrongBranchSelectedControlSampler (ringRank := ringRank)
            (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
            inputErrorSampler keySwitchGadget coordinate) =
        evalDist (LweSecrets >>= fun lweSecret =>
          RingSecrets >>= fun ringSecret =>
          Controls lweSecret ringSecret >>= fun controls =>
          Auxiliary lweSecret ringSecret >>= fun _ =>
          pure (lweSecret coordinate, controls coordinate)) := by
    simp [wrongBranchSelectedControlSampler, coordinateSource, scalarSource, problem,
      LWE.AuxiliaryInput.Search.exactRecoveryProblem,
      KeySwitchFirstFiniteView.augmentedCircularProblem,
      KeySwitchFirstFiniteView.secretSampler, LweSecrets, RingSecrets, Controls,
      Auxiliary, map_eq_bind_pure_comp, bind_assoc, monad_norm]
  rw [hshape]
  calc
    _ = evalDist (LweSecrets >>= fun lweSecret =>
        RingSecrets >>= fun ringSecret =>
        Controls lweSecret ringSecret >>= fun controls =>
        pure (lweSecret coordinate, controls coordinate)) := by
      refine evalDist_bind_congr' LweSecrets fun lweSecret => ?_
      refine evalDist_bind_congr' RingSecrets fun ringSecret => ?_
      refine evalDist_bind_congr' (Controls lweSecret ringSecret) fun controls => ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        (Auxiliary lweSecret ringSecret)
        (by simp [Auxiliary]) _
    _ = evalDist (LweSecrets >>= fun lweSecret =>
        RingSecrets >>= fun ringSecret =>
        Selected (lweSecret coordinate) ringSecret) := by
      refine evalDist_bind_congr' LweSecrets fun lweSecret => ?_
      refine evalDist_bind_congr' RingSecrets fun ringSecret => ?_
      simpa [Controls, Selected, generatedControlSampler,
          Native.BootstrapSecurity.MonomialKDM.generateBootstrappingKey,
          map_eq_bind_pure_comp] using
        (FormalProof4FHE.FiniteProduct.evalDist_map_fin_mOfFn_apply lweDimension
          (fun selectedCoordinate =>
            generatedControlSampler (ringRank := ringRank) params ringErrorSampler
              (lweSecret selectedCoordinate) ringSecret)
          coordinate (fun control => (lweSecret coordinate, control)))
    _ = evalDist (((fun lweSecret : BinarySecret lweDimension => lweSecret coordinate) <$>
          LweSecrets) >>= fun hidden => RingSecrets >>= Selected hidden) := by
      simp [map_eq_bind_pure_comp, bind_assoc]
    _ = evalDist (($ᵗ Bool) >>= fun hidden => RingSecrets >>= Selected hidden) := by
      apply FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
      exact FormalProof4FHE.FiniteProduct.evalDist_map_apply_uniformSample_fun coordinate
    _ = evalDist
        (canonicalWrongBranchControlSampler (ringRank := ringRank)
          params ringErrorSampler) := by
      simp [canonicalWrongBranchControlSampler, Selected, RingSecrets]

/-- Projecting the joint context-and-mask sampler directly to its original hidden bit and
selected control gives the same canonical one-control law. -/
theorem wrongBranchRowwiseFailureSampler_selectedControl_evalDist_eq_canonical [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    evalDist
        ((fun sample :
            (Bool × PublicContext q degree ringRank params.levels lweDimension
              keySwitchLevels queryCount) × BinarySecret lweDimension =>
            (sample.1.1, sample.1.2.1 coordinate)) <$>
          wrongBranchRowwiseFailureSampler (ringRank := ringRank)
            (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
            inputErrorSampler keySwitchGadget coordinate) =
      evalDist
        (canonicalWrongBranchControlSampler (ringRank := ringRank)
          params ringErrorSampler) := by
  let sampler := wrongBranchRowwiseFailureSampler (ringRank := ringRank)
    (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
    inputErrorSampler keySwitchGadget coordinate
  let source := coordinateSource (ringRank := ringRank) (queryCount := queryCount)
    ringErrorSampler keySwitchErrorSampler inputErrorSampler
    (Gadget.Base.ringGadget params) keySwitchGadget coordinate
  let select := fun hiddenAndContext :
      Bool × PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount =>
    (hiddenAndContext.1, hiddenAndContext.2.1 coordinate)
  have hsource : evalDist ((fun sample => sample.1) <$> sampler) =
      evalDist source := by
    simpa only [sampler, source] using
      (wrongBranchRowwiseFailureSampler_fst_evalDist
        (ringRank := ringRank) (queryCount := queryCount) params ringErrorSampler
        keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
  calc
    _ = evalDist (select <$> ((fun sample => sample.1) <$> sampler)) := by
      simp [sampler, select, Functor.map_map]
    _ = evalDist (select <$> source) :=
      evalDist_map_eq_of_evalDist_eq hsource select
    _ = evalDist
        (wrongBranchSelectedControlSampler (ringRank := ringRank)
          (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
          inputErrorSampler keySwitchGadget coordinate) := by
      rfl
    _ = _ := wrongBranchSelectedControlSampler_evalDist_eq_canonical
      (ringRank := ringRank) (queryCount := queryCount) params ringErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate

/-- Non-bijectivity predicate on the minimal hidden-bit/selected-control marginal. -/
def WrongBranchSelectedControlFailure
    (params : Gadget.Base.Parameters q)
    (hiddenAndControl :
      Bool × RingGSWCiphertext q degree ringRank params.levels) : Prop :=
  ¬Native.ShiftedCandidateEvaluator.ControlBranchFresh params
    (!hiddenAndControl.1) hiddenAndControl.2

/-- Direct one-row statistical defect on the minimal hidden-bit/control marginal.  This remains
meaningful even when the normalized map is not bijective. -/
noncomputable def wrongBranchSelectedControlDistance [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hiddenAndControl :
      Bool × RingGSWCiphertext q degree ringRank params.levels) : ℝ :=
  Native.ShiftedCandidateEvaluator.controlBranchDistance params
    (!hiddenAndControl.1) hiddenAndControl.2

/-- Non-bijectivity predicate after the complementary candidate has already been absorbed into
the control.  Its input is a message-one control, so no hidden scalar bit remains. -/
def MessageOneControlFailure
    (params : Gadget.Base.Parameters q)
    (control : RingGSWCiphertext q degree ringRank params.levels) : Prop :=
  ¬Native.ShiftedCandidateEvaluator.ControlBranchFresh params false control

/-- Direct normalized one-row defect of an already-toggled message-one control. -/
noncomputable def messageOneControlDistance [NeZero q]
    (params : Gadget.Base.Parameters q)
    (control : RingGSWCiphertext q degree ringRank params.levels) : ℝ :=
  Native.ShiftedCandidateEvaluator.controlBranchDistance params false control

/-- The old hidden-bit/control failure event is exactly the message-one event after toggling the
sampled control by the complementary candidate. -/
theorem wrongBranchSelectedControlFailure_iff_messageOneControlFailure
    (params : Gadget.Base.Parameters q)
    (hiddenAndControl :
      Bool × RingGSWCiphertext q degree ringRank params.levels) :
    WrongBranchSelectedControlFailure params hiddenAndControl ↔
      MessageOneControlFailure params
        (Native.ShiftedCandidateEvaluator.candidateControl params
          (!hiddenAndControl.1) hiddenAndControl.2) := by
  unfold WrongBranchSelectedControlFailure MessageOneControlFailure
    Native.ShiftedCandidateEvaluator.ControlBranchFresh
  rw [Native.ShiftedCandidateEvaluator.controlBranchTransform_false_candidateControl]

/-- The direct normalized defect likewise depends only on the already-toggled message-one
control. -/
theorem wrongBranchSelectedControlDistance_eq_messageOneControlDistance
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hiddenAndControl :
      Bool × RingGSWCiphertext q degree ringRank params.levels) :
    wrongBranchSelectedControlDistance params hiddenAndControl =
      messageOneControlDistance params
        (Native.ShiftedCandidateEvaluator.candidateControl params
          (!hiddenAndControl.1) hiddenAndControl.2) := by
  unfold wrongBranchSelectedControlDistance messageOneControlDistance
  exact (Native.ShiftedCandidateEvaluator.controlBranchDistance_false_candidateControl
    params (!hiddenAndControl.1) hiddenAndControl.2).symm

/-- Scalar transport and its independent mask do not change the normalized wrong-control
failure event. -/
theorem wrongBranchControlFailure_iff_sourceControlFailure
    (params : Gadget.Base.Parameters q) (coordinate : Fin lweDimension)
    (sample :
      (Bool × PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount) × BinarySecret lweDimension) :
    WrongBranchControlFailure params coordinate sample ↔
      WrongBranchSourceControlFailure params coordinate sample.1 := by
  unfold WrongBranchControlFailure WrongBranchSourceControlFailure
  unfold Native.ShiftedCandidateEvaluator.ControlBranchFresh
  rw [controlBranchTransform_transported_wrong]

/-- Every named data-row failure is exactly the same normalized control-map failure. -/
theorem wrongBranchRowFailure_iff_controlFailure
    (params : Gadget.Base.Parameters q) (coordinate outputCoordinate : Fin lweDimension)
    (row : Fin (TGSW.rowCount ringRank params.levels))
    (sample :
      (Bool × PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount) × BinarySecret lweDimension) :
    WrongBranchRowFailure params coordinate outputCoordinate row sample ↔
      WrongBranchControlFailure params coordinate sample := by
  unfold WrongBranchRowFailure WrongBranchControlFailure
  exact not_congr
    (Native.ShiftedCandidateEvaluator.rowBranchFresh_iff_controlBranchFresh
      params (transportCandidate coordinate (!sample.1.1) sample.2)
      ((transportedView params sample.1.2.1 sample.1.2.2 sample.2).1.1 coordinate)
      (TLWE.entry
        ((transportedView params sample.1.2.1 sample.1.2.2 sample.2).1.1
          outputCoordinate) row))

/-- If any row loses freshness, then the one shared normalized control map loses freshness.  No
nonemptiness assumption on the row index is needed for this implication. -/
theorem wrongBranchRowwiseFailure_imp_controlFailure
    (params : Gadget.Base.Parameters q) (coordinate : Fin lweDimension)
    (sample :
      (Bool × PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount) × BinarySecret lweDimension) :
    WrongBranchRowwiseFailure params coordinate sample →
      WrongBranchControlFailure params coordinate sample := by
  classical
  intro hfailure
  simp only [WrongBranchRowwiseFailure, RowwiseBranchFreshAtMask,
    Native.ShiftedCandidateEvaluator.RowwiseBranchFresh, not_forall] at hfailure
  obtain ⟨outputCoordinate, row, hrow⟩ := hfailure
  exact (wrongBranchRowFailure_iff_controlFailure params coordinate
    outputCoordinate row sample).1 hrow

/-- Average-case failure probability of one named row map. -/
noncomputable def averagedWrongBranchRowFailure [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate outputCoordinate : Fin lweDimension)
    (row : Fin (TGSW.rowCount ringRank params.levels)) : ℝ :=
  Pr[WrongBranchRowFailure params coordinate outputCoordinate row |
    wrongBranchRowwiseFailureSampler (ringRank := ringRank) (queryCount := queryCount)
      params ringErrorSampler keySwitchErrorSampler inputErrorSampler keySwitchGadget
      coordinate].toReal

/-- Actual probability that the single normalized wrong-candidate control map is non-bijective.
Unlike the previous row union, this event is not multiplied by the number of BRK entries or TGSW
rows. -/
noncomputable def averagedWrongBranchControlFailure [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) : ℝ :=
  Pr[WrongBranchControlFailure params coordinate |
    wrongBranchRowwiseFailureSampler (ringRank := ringRank) (queryCount := queryCount)
      params ringErrorSampler keySwitchErrorSampler inputErrorSampler keySwitchGadget
      coordinate].toReal

/-- The normalized control-failure probability on the original coordinate source, before
sampling the evaluator mask or transporting the public context. -/
noncomputable def averagedWrongBranchSourceControlFailure [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) : ℝ :=
  Pr[WrongBranchSourceControlFailure params coordinate |
    coordinateSource (ringRank := ringRank) (queryCount := queryCount)
      ringErrorSampler keySwitchErrorSampler inputErrorSampler
      (Gadget.Base.ringGadget params) keySwitchGadget coordinate].toReal

/-- Failure probability on the minimal selected-control marginal. -/
noncomputable def averagedWrongBranchSelectedControlFailure [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) : ℝ :=
  Pr[WrongBranchSelectedControlFailure params |
    wrongBranchSelectedControlSampler (ringRank := ringRank)
      (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
      inputErrorSampler keySwitchGadget coordinate].toReal

/-- Coordinate-free freshness defect of the canonical native one-control experiment. -/
noncomputable def averagedCanonicalWrongBranchControlFailure [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree)) : ℝ :=
  Pr[WrongBranchSelectedControlFailure params |
    canonicalWrongBranchControlSampler (ringRank := ringRank)
      params ringErrorSampler].toReal

/-- Expected direct one-row defect in the coordinate-free canonical control experiment. -/
noncomputable def averagedCanonicalWrongBranchControlDistance [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree)) : ℝ :=
  ∑' hiddenAndControl,
    Pr[= hiddenAndControl |
      canonicalWrongBranchControlSampler (ringRank := ringRank)
        params ringErrorSampler].toReal *
      wrongBranchSelectedControlDistance params hiddenAndControl

/-- Coordinate-free non-bijectivity probability after centered-binomial symmetry has removed
the hidden bit.  The experiment now contains only a uniform ring secret and a generated
message-one control. -/
noncomputable def averagedCanonicalMessageOneControlFailure [NeZero q]
    (params : Gadget.Base.Parameters q) (eta : ℕ) : ℝ :=
  Pr[MessageOneControlFailure (degree := degree + 1) params |
    canonicalMessageOneControlSampler (degree := degree) (ringRank := ringRank)
      params eta].toReal

/-- Expected direct one-row defect under the canonical centered-binomial message-one control
law. -/
noncomputable def averagedCanonicalMessageOneControlDistance [NeZero q]
    (params : Gadget.Base.Parameters q) (eta : ℕ) : ℝ :=
  ∑' control : RingGSWCiphertext q (degree + 1) ringRank params.levels,
    Pr[= control |
      canonicalMessageOneControlSampler (degree := degree) (ringRank := ringRank)
        params eta].toReal *
      messageOneControlDistance (degree := degree + 1) params control

theorem wrongBranchSelectedControlDistance_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (hiddenAndControl :
      Bool × RingGSWCiphertext q degree ringRank params.levels) :
    0 ≤ wrongBranchSelectedControlDistance params hiddenAndControl :=
  tvDist_nonneg _ _

theorem averagedCanonicalWrongBranchControlDistance_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree)) :
    0 ≤ averagedCanonicalWrongBranchControlDistance (ringRank := ringRank)
      params ringErrorSampler := by
  unfold averagedCanonicalWrongBranchControlDistance
  exact tsum_nonneg fun _ ↦ mul_nonneg ENNReal.toReal_nonneg
    (wrongBranchSelectedControlDistance_nonneg params _)

theorem messageOneControlDistance_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q)
    (control : RingGSWCiphertext q degree ringRank params.levels) :
    0 ≤ messageOneControlDistance params control :=
  tvDist_nonneg _ _

theorem averagedCanonicalMessageOneControlDistance_nonneg [NeZero q]
    (params : Gadget.Base.Parameters q) (eta : ℕ) :
    0 ≤ averagedCanonicalMessageOneControlDistance (degree := degree)
      (ringRank := ringRank) params eta := by
  unfold averagedCanonicalMessageOneControlDistance
  exact tsum_nonneg fun _ ↦ mul_nonneg ENNReal.toReal_nonneg
    (messageOneControlDistance_nonneg params _)

/-- Centered-binomial symmetry eliminates the hidden bit from the canonical failure probability
with no statistical loss. -/
theorem averagedCanonicalWrongBranchControlFailure_eq_messageOne
    {q degree ringRank eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) :
    averagedCanonicalWrongBranchControlFailure (ringRank := ringRank) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta) =
      averagedCanonicalMessageOneControlFailure (degree := degree)
        (ringRank := ringRank) params eta := by
  unfold averagedCanonicalWrongBranchControlFailure
    averagedCanonicalMessageOneControlFailure
  apply congrArg ENNReal.toReal
  let sampler := canonicalWrongBranchControlSampler (ringRank := ringRank) params
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
  let normalize := fun hiddenAndControl :
      Bool × RingGSWCiphertext q (degree + 1) ringRank params.levels =>
    Native.ShiftedCandidateEvaluator.candidateControl params
      (!hiddenAndControl.1) hiddenAndControl.2
  have hdist : evalDist (normalize <$> sampler) =
      evalDist (canonicalMessageOneControlSampler (ringRank := ringRank) params eta) := by
    simpa only [sampler, normalize] using
      (canonicalWrongBranchControl_candidateControl_evalDist_eq_messageOne
        (ringRank := ringRank) (eta := eta) params)
  calc
    Pr[WrongBranchSelectedControlFailure params | sampler] =
        Pr[MessageOneControlFailure params ∘ normalize | sampler] := by
      apply le_antisymm <;> apply probEvent_mono
      · intro sample _ hfailure
        exact (wrongBranchSelectedControlFailure_iff_messageOneControlFailure
          params sample).1 hfailure
      · intro sample _ hfailure
        exact (wrongBranchSelectedControlFailure_iff_messageOneControlFailure
          params sample).2 hfailure
    _ = Pr[MessageOneControlFailure params | normalize <$> sampler] :=
      (probEvent_map sampler normalize (MessageOneControlFailure params)).symm
    _ = Pr[MessageOneControlFailure params |
        canonicalMessageOneControlSampler (ringRank := ringRank) params eta] :=
      probEvent_congr' (fun _ _ => Iff.rfl) hdist

/-- The same hidden-bit elimination is exact for the expected direct one-row TV defect. -/
theorem averagedCanonicalWrongBranchControlDistance_eq_messageOne
    {q degree ringRank eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q) :
    averagedCanonicalWrongBranchControlDistance (ringRank := ringRank) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta) =
      averagedCanonicalMessageOneControlDistance (degree := degree)
        (ringRank := ringRank) params eta := by
  let sampler := canonicalWrongBranchControlSampler (ringRank := ringRank) params
    (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
  let normalize := fun hiddenAndControl :
      Bool × RingGSWCiphertext q (degree + 1) ringRank params.levels =>
    Native.ShiftedCandidateEvaluator.candidateControl params
      (!hiddenAndControl.1) hiddenAndControl.2
  let cost := messageOneControlDistance (degree := degree + 1)
    (ringRank := ringRank) params
  have hdist : evalDist (normalize <$> sampler) =
      evalDist (canonicalMessageOneControlSampler (ringRank := ringRank) params eta) := by
    simpa only [sampler, normalize] using
      (canonicalWrongBranchControl_candidateControl_evalDist_eq_messageOne
        (ringRank := ringRank) (eta := eta) params)
  unfold averagedCanonicalWrongBranchControlDistance
    averagedCanonicalMessageOneControlDistance
  calc
    ∑' hiddenAndControl,
        Pr[= hiddenAndControl | sampler].toReal *
          wrongBranchSelectedControlDistance params hiddenAndControl =
      ∑' hiddenAndControl,
        Pr[= hiddenAndControl | sampler].toReal * cost (normalize hiddenAndControl) := by
          apply tsum_congr
          intro hiddenAndControl
          rw [wrongBranchSelectedControlDistance_eq_messageOneControlDistance]
    _ = ∑' control,
        Pr[= control | normalize <$> sampler].toReal * cost control :=
      (FormalProof4FHE.FiniteProduct.tsum_probOutput_map_toReal_mul
        sampler normalize cost (messageOneControlDistance_nonneg params)).symm
    _ = ∑' control,
        Pr[= control |
          canonicalMessageOneControlSampler (ringRank := ringRank) params eta].toReal *
          cost control :=
      FormalProof4FHE.FiniteProduct.tsum_probOutput_toReal_mul_congr hdist cost

/-- The minimal actual marginal has exactly the coordinate-free canonical failure probability. -/
theorem averagedWrongBranchSelectedControlFailure_eq_canonical [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    averagedWrongBranchSelectedControlFailure (ringRank := ringRank)
        (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
        inputErrorSampler keySwitchGadget coordinate =
      averagedCanonicalWrongBranchControlFailure (ringRank := ringRank)
        params ringErrorSampler := by
  unfold averagedWrongBranchSelectedControlFailure
    averagedCanonicalWrongBranchControlFailure
  apply congrArg ENNReal.toReal
  exact probEvent_congr' (fun _ _ => Iff.rfl)
    (wrongBranchSelectedControlSampler_evalDist_eq_canonical
      (ringRank := ringRank) (queryCount := queryCount) params ringErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)

/-- Projecting the original coordinate source to its hidden bit and selected control preserves
the failure probability exactly. -/
theorem averagedWrongBranchSourceControlFailure_eq_selectedControlFailure [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    averagedWrongBranchSourceControlFailure (ringRank := ringRank)
        (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
        inputErrorSampler keySwitchGadget coordinate =
      averagedWrongBranchSelectedControlFailure (ringRank := ringRank)
        (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
        inputErrorSampler keySwitchGadget coordinate := by
  unfold averagedWrongBranchSourceControlFailure
    averagedWrongBranchSelectedControlFailure wrongBranchSelectedControlSampler
  rw [probEvent_map]
  rfl

/-- The transported, mask-averaged control event has exactly the same probability as the
untransported selected-control event. -/
theorem averagedWrongBranchControlFailure_eq_sourceControlFailure [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    averagedWrongBranchControlFailure (ringRank := ringRank)
        (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
        inputErrorSampler keySwitchGadget coordinate =
      averagedWrongBranchSourceControlFailure (ringRank := ringRank)
        (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
        inputErrorSampler keySwitchGadget coordinate := by
  unfold averagedWrongBranchControlFailure averagedWrongBranchSourceControlFailure
  apply congrArg ENNReal.toReal
  let sampler := wrongBranchRowwiseFailureSampler (ringRank := ringRank)
    (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
    inputErrorSampler keySwitchGadget coordinate
  let source := coordinateSource (ringRank := ringRank) (queryCount := queryCount)
    ringErrorSampler keySwitchErrorSampler inputErrorSampler
    (Gadget.Base.ringGadget params) keySwitchGadget coordinate
  let project := fun sample :
      (Bool × PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount) × BinarySecret lweDimension => sample.1
  have hpredicate :
      Pr[WrongBranchControlFailure params coordinate | sampler] =
        Pr[WrongBranchSourceControlFailure params coordinate ∘ project | sampler] := by
    apply le_antisymm
    · apply probEvent_mono
      intro sample _ hfailure
      exact (wrongBranchControlFailure_iff_sourceControlFailure
        params coordinate sample).1 hfailure
    · apply probEvent_mono
      intro sample _ hfailure
      exact (wrongBranchControlFailure_iff_sourceControlFailure
        params coordinate sample).2 hfailure
  have hmap :
      Pr[WrongBranchSourceControlFailure params coordinate |
          project <$> sampler] =
        Pr[WrongBranchSourceControlFailure params coordinate ∘ project | sampler] :=
    probEvent_map sampler project (WrongBranchSourceControlFailure params coordinate)
  have hdist : evalDist (project <$> sampler) = evalDist source := by
    simpa only [sampler, source, project] using
      (wrongBranchRowwiseFailureSampler_fst_evalDist
        (ringRank := ringRank) (queryCount := queryCount) params ringErrorSampler
        keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
  calc
    _ = Pr[WrongBranchSourceControlFailure params coordinate ∘ project | sampler] :=
      hpredicate
    _ = Pr[WrongBranchSourceControlFailure params coordinate |
        project <$> sampler] := hmap.symm
    _ = Pr[WrongBranchSourceControlFailure params coordinate | source] :=
      probEvent_congr' (fun _ _ => Iff.rfl) hdist

/-- Combined marginalization: the joint transported control failure is exactly the minimal
hidden-bit/selected-control failure probability. -/
theorem averagedWrongBranchControlFailure_eq_selectedControlFailure [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    averagedWrongBranchControlFailure (ringRank := ringRank)
        (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
        inputErrorSampler keySwitchGadget coordinate =
      averagedWrongBranchSelectedControlFailure (ringRank := ringRank)
        (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
        inputErrorSampler keySwitchGadget coordinate :=
  (averagedWrongBranchControlFailure_eq_sourceControlFailure
    (ringRank := ringRank) (queryCount := queryCount) params ringErrorSampler
    keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate).trans
    (averagedWrongBranchSourceControlFailure_eq_selectedControlFailure
      (ringRank := ringRank) (queryCount := queryCount) params ringErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)

/-- Complete marginalization of the native wrong-branch freshness defect.  The actual joint
BRK/KSK/input-tape/mask experiment is exactly one uniform hidden bit, one uniform ring secret,
and one generated TRGSW control; consequently the defect is independent of the scalar coordinate
and every auxiliary sampler and gadget. -/
theorem averagedWrongBranchControlFailure_eq_canonical [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    averagedWrongBranchControlFailure (ringRank := ringRank)
        (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
        inputErrorSampler keySwitchGadget coordinate =
      averagedCanonicalWrongBranchControlFailure (ringRank := ringRank)
        params ringErrorSampler :=
  (averagedWrongBranchControlFailure_eq_selectedControlFailure
    (ringRank := ringRank) (queryCount := queryCount) params ringErrorSampler
    keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate).trans
    (averagedWrongBranchSelectedControlFailure_eq_canonical
      (ringRank := ringRank) (queryCount := queryCount) params ringErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)

/-- All named row-failure probabilities coincide with the one normalized control-failure
probability. -/
theorem averagedWrongBranchRowFailure_eq_controlFailure [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate outputCoordinate : Fin lweDimension)
    (row : Fin (TGSW.rowCount ringRank params.levels)) :
    averagedWrongBranchRowFailure (ringRank := ringRank) (queryCount := queryCount)
        params ringErrorSampler keySwitchErrorSampler inputErrorSampler keySwitchGadget
        coordinate outputCoordinate row =
      averagedWrongBranchControlFailure (ringRank := ringRank)
        (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
        inputErrorSampler keySwitchGadget coordinate := by
  unfold averagedWrongBranchRowFailure averagedWrongBranchControlFailure
  apply congrArg ENNReal.toReal
  apply le_antisymm
  · apply probEvent_mono
    intro sample _ hfailure
    exact (wrongBranchRowFailure_iff_controlFailure params coordinate
      outputCoordinate row sample).1 hfailure
  · apply probEvent_mono
    intro sample _ hfailure
    exact (wrongBranchRowFailure_iff_controlFailure params coordinate
      outputCoordinate row sample).2 hfailure

/-- The old rowwise bad event is bounded by the single shared control bad event. -/
theorem averagedWrongBranchRowwiseFailure_le_controlFailure [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    averagedWrongBranchRowwiseFailure (ringRank := ringRank) (queryCount := queryCount)
        params ringErrorSampler keySwitchErrorSampler inputErrorSampler keySwitchGadget
        coordinate ≤
      averagedWrongBranchControlFailure (ringRank := ringRank)
        (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
        inputErrorSampler keySwitchGadget coordinate := by
  unfold averagedWrongBranchRowwiseFailure averagedWrongBranchControlFailure
  apply ENNReal.toReal_mono (by simp)
  apply probEvent_mono
  intro sample _ hfailure
  exact wrongBranchRowwiseFailure_imp_controlFailure params coordinate sample hfailure

/-- Union-bound the joint rowwise-freshness failure by the sum of the named row-map failures.
This leaves each summand ready for an algebraic or finite-field rank estimate. -/
theorem averagedWrongBranchRowwiseFailure_le_sum_rowFailure [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    averagedWrongBranchRowwiseFailure (ringRank := ringRank) (queryCount := queryCount)
        params ringErrorSampler keySwitchErrorSampler inputErrorSampler keySwitchGadget
        coordinate ≤
      ∑ outputCoordinate, ∑ row,
        averagedWrongBranchRowFailure (ringRank := ringRank) (queryCount := queryCount)
          params ringErrorSampler keySwitchErrorSampler inputErrorSampler keySwitchGadget
          coordinate outputCoordinate row := by
  classical
  let sampler := wrongBranchRowwiseFailureSampler (ringRank := ringRank)
    (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
    inputErrorSampler keySwitchGadget coordinate
  have houter :
      Pr[WrongBranchRowwiseFailure params coordinate | sampler] ≤
        ∑ outputCoordinate,
          Pr[(fun sample => ∃ row,
            WrongBranchRowFailure params coordinate outputCoordinate row sample) |
            sampler] := by
    calc
      _ ≤ Pr[(fun sample => ∃ outputCoordinate ∈
          (Finset.univ : Finset (Fin lweDimension)), ∃ row,
            WrongBranchRowFailure params coordinate outputCoordinate row sample) |
          sampler] := by
        apply probEvent_mono
        intro sample _ hfailure
        simp only [WrongBranchRowwiseFailure, RowwiseBranchFreshAtMask,
          Native.ShiftedCandidateEvaluator.RowwiseBranchFresh, not_forall] at hfailure
        obtain ⟨outputCoordinate, row, hrow⟩ := hfailure
        exact ⟨outputCoordinate, Finset.mem_univ _, row, hrow⟩
      _ ≤ _ :=
        probEvent_exists_finset_le_sum (Finset.univ : Finset (Fin lweDimension))
          sampler (fun outputCoordinate sample => ∃ row,
            WrongBranchRowFailure params coordinate outputCoordinate row sample)
  have hinner : ∀ outputCoordinate,
      Pr[(fun sample => ∃ row,
        WrongBranchRowFailure params coordinate outputCoordinate row sample) | sampler] ≤
        ∑ row,
          Pr[WrongBranchRowFailure params coordinate outputCoordinate row | sampler] := by
    intro outputCoordinate
    calc
      _ ≤ Pr[(fun sample => ∃ row ∈
          (Finset.univ : Finset (Fin (TGSW.rowCount ringRank params.levels))),
            WrongBranchRowFailure params coordinate outputCoordinate row sample) |
          sampler] := by
        apply probEvent_mono
        intro sample _ hfailure
        obtain ⟨row, hrow⟩ := hfailure
        exact ⟨row, Finset.mem_univ _, hrow⟩
      _ ≤ _ := probEvent_exists_finset_le_sum
        (Finset.univ : Finset (Fin (TGSW.rowCount ringRank params.levels)))
        sampler (WrongBranchRowFailure params coordinate outputCoordinate)
  have hENN :
      Pr[WrongBranchRowwiseFailure params coordinate | sampler] ≤
        ∑ outputCoordinate, ∑ row,
          Pr[WrongBranchRowFailure params coordinate outputCoordinate row | sampler] :=
    houter.trans (Finset.sum_le_sum fun outputCoordinate _ => hinner outputCoordinate)
  have hreal := ENNReal.toReal_mono (by simp) hENN
  rw [ENNReal.toReal_sum (fun _ _ => by simp)] at hreal
  simp_rw [ENNReal.toReal_sum (fun _ _ => probEvent_ne_top)] at hreal
  simpa only [averagedWrongBranchRowwiseFailure, averagedWrongBranchRowFailure,
    sampler] using hreal

/-- Convenient pointwise form of the row union bound. -/
theorem averagedWrongBranchRowwiseFailure_le_sum_of_rowFailure_le [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension)
    (rowError : Fin lweDimension →
      Fin (TGSW.rowCount ringRank params.levels) → ℝ)
    (hrow : ∀ outputCoordinate row,
      averagedWrongBranchRowFailure (ringRank := ringRank) (queryCount := queryCount)
          params ringErrorSampler keySwitchErrorSampler inputErrorSampler keySwitchGadget
          coordinate outputCoordinate row ≤ rowError outputCoordinate row) :
    averagedWrongBranchRowwiseFailure (ringRank := ringRank) (queryCount := queryCount)
        params ringErrorSampler keySwitchErrorSampler inputErrorSampler keySwitchGadget
        coordinate ≤
      ∑ outputCoordinate, ∑ row, rowError outputCoordinate row :=
  (averagedWrongBranchRowwiseFailure_le_sum_rowFailure
    (ringRank := ringRank) (queryCount := queryCount) params ringErrorSampler
    keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate).trans
    (Finset.sum_le_sum fun outputCoordinate _ =>
      Finset.sum_le_sum fun row _ => hrow outputCoordinate row)

/-- The complete wrong-candidate public-view distance is at most the probability of rowwise rank
failure over the real generated public context and scalar mask.  This is the average-case bridge
needed to apply random-matrix rank estimates; no worst-case requirement over the support remains. -/
theorem tvDist_averagedWrongTransform_uniformPublicView_le_averagedWrongBranchRowwiseFailure
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    tvDist
        (averagedWrongTransform (ringRank := ringRank) (queryCount := queryCount)
          params ringErrorSampler keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate)
        (uniformPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler
          inputErrorSampler (Gadget.Base.ringGadget params) keySwitchGadget) ≤
      averagedWrongBranchRowwiseFailure (ringRank := ringRank)
        (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
        inputErrorSampler keySwitchGadget coordinate := by
  classical
  let Sample :=
    (Bool × PublicContext q degree ringRank params.levels lweDimension
      keySwitchLevels queryCount) × BinarySecret lweDimension
  let sampler : ProbComp Sample := wrongBranchRowwiseFailureSampler (ringRank := ringRank)
    (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
    inputErrorSampler keySwitchGadget coordinate
  let left : Sample → ProbComp
      (PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount) := fun sample =>
    branchExperimentAtMask params coordinate (!sample.1.1)
      sample.1.2.1 sample.1.2.2 sample.2
  let right : Sample → ProbComp
      (PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount) := fun sample =>
    uniformExperimentAtMask params sample.1.2.1 sample.1.2.2 sample.2
  have hpoint : ∀ sample : Sample,
      tvDist (left sample) (right sample) ≤
        Pr[WrongBranchRowwiseFailure params coordinate |
          (pure sample : ProbComp Sample)].toReal := by
    intro sample
    rw [probEvent_pure]
    by_cases hFresh : RowwiseBranchFreshAtMask params coordinate (!sample.1.1)
        sample.1.2.1 sample.1.2.2 sample.2
    · simpa [left, right, WrongBranchRowwiseFailure, hFresh,
        rowwiseFailureIndicator] using
        (tvDist_branchExperimentAtMask_uniformExperimentAtMask_le_rowwiseFailureIndicator
          params coordinate (!sample.1.1) sample.1.2.1 sample.1.2.2 sample.2)
    · simpa [left, right, WrongBranchRowwiseFailure, hFresh,
        rowwiseFailureIndicator] using
        (tvDist_branchExperimentAtMask_uniformExperimentAtMask_le_rowwiseFailureIndicator
          params coordinate (!sample.1.1) sample.1.2.1 sample.1.2.2 sample.2)
  have hmix := FormalProof4FHE.FiniteProduct.tvDist_bind_left_le_probEvent_cont
    sampler left right (fun sample : Sample => (pure sample : ProbComp Sample))
    (WrongBranchRowwiseFailure params coordinate) hpoint
  have hmain :
      tvDist
          (averagedWrongTransform (ringRank := ringRank) (queryCount := queryCount)
            params ringErrorSampler keySwitchErrorSampler inputErrorSampler
            keySwitchGadget coordinate)
          (averagedUniformized (ringRank := ringRank) (queryCount := queryCount)
            params ringErrorSampler keySwitchErrorSampler inputErrorSampler
            keySwitchGadget coordinate) ≤
        averagedWrongBranchRowwiseFailure (ringRank := ringRank)
          (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
          inputErrorSampler keySwitchGadget coordinate := by
    simpa [Sample, sampler, left, right, wrongBranchRowwiseFailureSampler,
      averagedWrongBranchRowwiseFailure, averagedWrongTransform, transform, sampleCoin,
      branchExperimentAtMask, transformWithCoin, averagedUniformized,
      uniformExperimentAtMask, monad_norm] using hmix
  unfold tvDist at hmain ⊢
  rw [averagedUniformized_evalDist_eq_uniformPublicView
    params ringErrorSampler keySwitchErrorSampler inputErrorSampler
    keySwitchGadget coordinate] at hmain
  exact hmain

/-- **Single-control native wrong-candidate endpoint.**  The complete wrong public-view distance
is bounded by one normalized control-map failure probability.  Translation conjugacy removes the
previous artificial union over every output coordinate and TGSW row. -/
theorem tvDist_averagedWrongTransform_uniformPublicView_le_averagedWrongBranchControlFailure
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    tvDist
        (averagedWrongTransform (ringRank := ringRank) (queryCount := queryCount)
          params ringErrorSampler keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate)
        (uniformPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler
          inputErrorSampler (Gadget.Base.ringGadget params) keySwitchGadget) ≤
      averagedWrongBranchControlFailure (ringRank := ringRank)
        (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
        inputErrorSampler keySwitchGadget coordinate :=
  (tvDist_averagedWrongTransform_uniformPublicView_le_averagedWrongBranchRowwiseFailure
    (ringRank := ringRank) (queryCount := queryCount) params ringErrorSampler
    keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate).trans
    (averagedWrongBranchRowwiseFailure_le_controlFailure
      (ringRank := ringRank) (queryCount := queryCount) params ringErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)

/-- **Untransported single-control endpoint.**  The wrong public-view loss is bounded directly by
non-bijectivity of the selected original BRK control's identity-plus-homogeneous perturbation
map.  The evaluator mask, KSK, tape, output coordinates, and data-row indices no longer occur in
the event itself. -/
theorem tvDist_averagedWrongTransform_uniformPublicView_le_averagedWrongBranchSourceControlFailure
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    tvDist
        (averagedWrongTransform (ringRank := ringRank) (queryCount := queryCount)
          params ringErrorSampler keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate)
        (uniformPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler
          inputErrorSampler (Gadget.Base.ringGadget params) keySwitchGadget) ≤
      averagedWrongBranchSourceControlFailure (ringRank := ringRank)
        (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
        inputErrorSampler keySwitchGadget coordinate := by
  calc
    _ ≤ averagedWrongBranchControlFailure (ringRank := ringRank)
        (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
        inputErrorSampler keySwitchGadget coordinate :=
      tvDist_averagedWrongTransform_uniformPublicView_le_averagedWrongBranchControlFailure
        (ringRank := ringRank) (queryCount := queryCount) params ringErrorSampler
        keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
    _ = _ := averagedWrongBranchControlFailure_eq_sourceControlFailure
      (ringRank := ringRank) (queryCount := queryCount) params ringErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate

/-- **Minimal-marginal native wrong-candidate endpoint.**  The complete public-view loss is
bounded by a bad event whose sampled value is only `(hidden bit, selected original TRGSW
control)`. -/
theorem tvDist_averagedWrongTransform_uniformPublicView_le_averagedWrongBranchSelectedControlFailure
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    tvDist
        (averagedWrongTransform (ringRank := ringRank) (queryCount := queryCount)
          params ringErrorSampler keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate)
        (uniformPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler
          inputErrorSampler (Gadget.Base.ringGadget params) keySwitchGadget) ≤
      averagedWrongBranchSelectedControlFailure (ringRank := ringRank)
        (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
        inputErrorSampler keySwitchGadget coordinate := by
  calc
    _ ≤ averagedWrongBranchSourceControlFailure (ringRank := ringRank)
        (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
        inputErrorSampler keySwitchGadget coordinate :=
      tvDist_averagedWrongTransform_uniformPublicView_le_averagedWrongBranchSourceControlFailure
        (ringRank := ringRank) (queryCount := queryCount) params ringErrorSampler
        keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
    _ = _ := averagedWrongBranchSourceControlFailure_eq_selectedControlFailure
      (ringRank := ringRank) (queryCount := queryCount) params ringErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate

/-- **Canonical one-control endpoint.**  The entire native wrong-view loss is bounded by a
coordinate-free experiment containing only a uniform hidden bit, a uniform ring secret, and its
single generated TRGSW control.  KSK and input-tape distributions do not affect this bound. -/
theorem tvDist_averagedWrongTransform_uniformPublicView_le_averagedCanonicalControlFailure
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    tvDist
        (averagedWrongTransform (ringRank := ringRank) (queryCount := queryCount)
          params ringErrorSampler keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate)
        (uniformPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler
          inputErrorSampler (Gadget.Base.ringGadget params) keySwitchGadget) ≤
      averagedCanonicalWrongBranchControlFailure (ringRank := ringRank)
        params ringErrorSampler := by
  calc
    _ ≤ averagedWrongBranchSelectedControlFailure (ringRank := ringRank)
        (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
        inputErrorSampler keySwitchGadget coordinate :=
      tvDist_averagedWrongTransform_uniformPublicView_le_averagedWrongBranchSelectedControlFailure
        (ringRank := ringRank) (queryCount := queryCount) params ringErrorSampler
        keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
    _ = _ := averagedWrongBranchSelectedControlFailure_eq_canonical
      (ringRank := ringRank) (queryCount := queryCount) params ringErrorSampler
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate

/-- **Centered-binomial message-one endpoint.**  The complete native wrong-view loss is bounded
by non-bijectivity in an experiment containing only a uniform ring secret and one generated
message-one TRGSW control.  The hidden scalar bit has been eliminated exactly. -/
theorem tvDist_averagedWrongTransform_uniformPublicView_le_averagedMessageOneControlFailure
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    tvDist
        (averagedWrongTransform (ringRank := ringRank) (queryCount := queryCount)
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
        (uniformPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount)
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
          keySwitchGadget) ≤
      averagedCanonicalMessageOneControlFailure (degree := degree)
        (ringRank := ringRank) params eta := by
  calc
    _ ≤ averagedCanonicalWrongBranchControlFailure (ringRank := ringRank) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta) :=
      tvDist_averagedWrongTransform_uniformPublicView_le_averagedCanonicalControlFailure
        (ringRank := ringRank) (lweDimension := lweDimension)
        (queryCount := queryCount) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
    _ = _ := averagedCanonicalWrongBranchControlFailure_eq_messageOne
      (ringRank := ringRank) (eta := eta) params

/-- **Direct canonical-control endpoint.**  Without assuming bijectivity, the complete native
wrong-view loss is bounded by the number of independently transformed TLWE data rows times the
expected one-row TV defect in the canonical control experiment.  This is the explicit statistical
fallback when the zero-one rank event is too strong. -/
theorem tvDist_averagedWrongTransform_uniformPublicView_le_card_mul_averagedCanonicalControlDistance
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    tvDist
        (averagedWrongTransform (ringRank := ringRank) (queryCount := queryCount)
          params ringErrorSampler keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate)
        (uniformPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler
          inputErrorSampler (Gadget.Base.ringGadget params) keySwitchGadget) ≤
      (lweDimension * TGSW.rowCount ringRank params.levels : ℕ) *
        averagedCanonicalWrongBranchControlDistance (ringRank := ringRank)
          params ringErrorSampler := by
  classical
  let Sample :=
    (Bool × PublicContext q degree ringRank params.levels lweDimension
      keySwitchLevels queryCount) × BinarySecret lweDimension
  let sampler : ProbComp Sample :=
    wrongBranchRowwiseFailureSampler (ringRank := ringRank)
      (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
      inputErrorSampler keySwitchGadget coordinate
  let left : Sample → ProbComp
      (PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount) := fun sample =>
    branchExperimentAtMask params coordinate (!sample.1.1)
      sample.1.2.1 sample.1.2.2 sample.2
  let right : Sample → ProbComp
      (PublicContext q degree ringRank params.levels lweDimension
        keySwitchLevels queryCount) := fun sample =>
    uniformExperimentAtMask params sample.1.2.1 sample.1.2.2 sample.2
  let project : Sample →
      Bool × RingGSWCiphertext q degree ringRank params.levels := fun sample =>
    (sample.1.1, sample.1.2.1 coordinate)
  let cost :
      (Bool × RingGSWCiphertext q degree ringRank params.levels) → ℝ :=
    wrongBranchSelectedControlDistance (degree := degree) (ringRank := ringRank) params
  let rowCount : ℝ :=
    (lweDimension * TGSW.rowCount ringRank params.levels : ℕ)
  have hpoint : ∀ sample : Sample,
      tvDist (left sample) (right sample) ≤ rowCount * cost (project sample) := by
    intro sample
    calc
      _ ≤ Native.ShiftedCandidateEvaluator.branchDistance params coordinate
          (transportCandidate coordinate (!sample.1.1) sample.2)
          (transportedView params sample.1.2.1 sample.1.2.2 sample.2).1.1 :=
        by
          let transported :=
            transportedView params sample.1.2.1 sample.1.2.2 sample.2
          let finish := fun bootstrappingKey : Native.BootstrappingKey q degree
              ringRank params.levels lweDimension =>
            (bootstrappingKey, transported.1.2, transported.2)
          have hdata := tvDist_map_le (m := ProbComp) finish
            (Native.ShiftedCandidateEvaluator.branchTransform params coordinate
                (transportCandidate coordinate (!sample.1.1) sample.2)
                transported.1.1 <$>
              ($ᵗ Native.BootstrappingKey q degree ringRank params.levels
                lweDimension))
            ($ᵗ Native.BootstrappingKey q degree ringRank params.levels
              lweDimension)
          simpa only [left, right, branchExperimentAtMask, uniformExperimentAtMask,
            transformWithCoin, Native.ShiftedCandidateEvaluator.branchDistance,
            Native.ShiftedCandidateEvaluator.branchTransform,
            Native.ShiftedCandidateEvaluator.selectBootstrappingKey,
            transported, finish, map_eq_bind_pure_comp, Function.comp_def,
            bind_assoc, pure_bind] using hdata
      _ ≤ rowCount * Native.ShiftedCandidateEvaluator.controlBranchDistance params
          (transportCandidate coordinate (!sample.1.1) sample.2)
          ((transportedView params sample.1.2.1 sample.1.2.2 sample.2).1.1
            coordinate) := by
        simpa only [rowCount] using
          (Native.ShiftedCandidateEvaluator.branchDistance_le_card_mul_controlBranchDistance
            params coordinate (transportCandidate coordinate (!sample.1.1) sample.2)
            (transportedView params sample.1.2.1 sample.1.2.2 sample.2).1.1)
      _ = rowCount * cost (project sample) := by
        unfold cost project wrongBranchSelectedControlDistance
        rw [controlBranchDistance_transported_wrong]
  have hmix := FormalProof4FHE.FiniteProduct.tvDist_bind_left_le_expectation
    sampler left right
  have hcostNonneg : ∀ value,
      0 ≤ cost value := fun value => by
    exact wrongBranchSelectedControlDistance_nonneg params value
  have hprojection :
      evalDist (project <$> sampler) =
        evalDist (canonicalWrongBranchControlSampler (ringRank := ringRank)
          params ringErrorSampler) := by
    simpa only [sampler, project, Sample] using
      (wrongBranchRowwiseFailureSampler_selectedControl_evalDist_eq_canonical
        (ringRank := ringRank) (queryCount := queryCount) params ringErrorSampler
        keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
  have hexpectation :
      (∑' sample : Sample,
          Pr[= sample | sampler].toReal * cost (project sample)) =
        averagedCanonicalWrongBranchControlDistance (ringRank := ringRank)
          params ringErrorSampler := by
    calc
      _ = ∑' value,
          Pr[= value | project <$> sampler].toReal * cost value :=
        (FormalProof4FHE.FiniteProduct.tsum_probOutput_map_toReal_mul
          sampler project cost hcostNonneg).symm
      _ = ∑' value,
          Pr[= value |
            canonicalWrongBranchControlSampler (ringRank := ringRank)
              params ringErrorSampler].toReal * cost value :=
        FormalProof4FHE.FiniteProduct.tsum_probOutput_toReal_mul_congr
          hprojection cost
      _ = _ := by
        rfl
  have hmain :
      tvDist
          (averagedWrongTransform (ringRank := ringRank) (queryCount := queryCount)
            params ringErrorSampler keySwitchErrorSampler inputErrorSampler
            keySwitchGadget coordinate)
          (averagedUniformized (ringRank := ringRank) (queryCount := queryCount)
            params ringErrorSampler keySwitchErrorSampler inputErrorSampler
            keySwitchGadget coordinate) ≤
        rowCount * averagedCanonicalWrongBranchControlDistance
          (ringRank := ringRank) params ringErrorSampler := by
    calc
      _ ≤ ∑' sample : Sample,
          Pr[= sample | sampler].toReal * tvDist (left sample) (right sample) := by
        simpa [Sample, sampler, left, right, wrongBranchRowwiseFailureSampler,
          averagedWrongTransform, transform, sampleCoin, maskedBranchExperiment,
          branchExperimentAtMask, transformWithCoin, averagedUniformized,
          uniformExperimentAtMask, monad_norm] using hmix
      _ ≤ ∑' sample : Sample,
          Pr[= sample | sampler].toReal * (rowCount * cost (project sample)) := by
        apply Summable.tsum_le_tsum
        · intro sample
          exact mul_le_mul_of_nonneg_left (hpoint sample) ENNReal.toReal_nonneg
        · exact Summable.of_finite
        · exact Summable.of_finite
      _ = rowCount * ∑' sample : Sample,
          Pr[= sample | sampler].toReal * cost (project sample) := by
        rw [← tsum_mul_left]
        exact tsum_congr fun sample ↦ by ring
      _ = _ := by rw [hexpectation]
  unfold tvDist at hmain ⊢
  rw [averagedUniformized_evalDist_eq_uniformPublicView
    params ringErrorSampler keySwitchErrorSampler inputErrorSampler
    keySwitchGadget coordinate] at hmain
  simpa only [rowCount, Nat.cast_mul] using hmain

/-- **Direct centered-binomial message-one endpoint.**  Without a bijectivity assumption, the
complete wrong-view distance is bounded by the explicit row count times the expected normalized
one-row defect of a single generated message-one control. -/
theorem
    tvDist_averagedWrongTransform_uniformPublicView_le_card_mul_averagedMessageOneControlDistance
    {q degree ringRank lweDimension keySwitchLevels queryCount eta : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    tvDist
        (averagedWrongTransform (ringRank := ringRank) (queryCount := queryCount)
          params (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
        (uniformPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount)
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
          keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
          keySwitchGadget) ≤
      (lweDimension * TGSW.rowCount ringRank params.levels : ℕ) *
        averagedCanonicalMessageOneControlDistance (degree := degree)
          (ringRank := ringRank) params eta := by
  calc
    _ ≤ (lweDimension * TGSW.rowCount ringRank params.levels : ℕ) *
        averagedCanonicalWrongBranchControlDistance (ringRank := ringRank) params
          (RLWE.CenteredBinomial.sampler q (degree + 1) eta) :=
      tvDist_averagedWrongTransform_uniformPublicView_le_card_mul_averagedCanonicalControlDistance
        (ringRank := ringRank) (lweDimension := lweDimension)
        (queryCount := queryCount) params
        (RLWE.CenteredBinomial.sampler q (degree + 1) eta)
        keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate
    _ = _ := by
      rw [averagedCanonicalWrongBranchControlDistance_eq_messageOne
        (ringRank := ringRank) (eta := eta) params]

/-- Sum of the explicit single-row shifted-CMux defects in one fixed transported public
context.  The two sums range over the BRK output coordinates and the TGSW rows. -/
noncomputable def branchRowDistanceAtMask [NeZero q]
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (candidate : Bool)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount)
    (mask : BinarySecret lweDimension) : ℝ :=
  let transported := transportedView params challenge auxiliary mask
  ∑ outputCoordinate, ∑ row,
    Native.ShiftedCandidateEvaluator.rowBranchDistance params
      (transportCandidate coordinate candidate mask)
      (transported.1.1 coordinate)
      (TLWE.entry (transported.1.1 outputCoordinate) row)

/-- At a fixed scalar mask, retaining the transported KSK and tape is postprocessing.  Hence the
complete-context branch distance is bounded by the whole-BRK branch distance. -/
theorem tvDist_branchExperimentAtMask_uniformExperimentAtMask_le_branchDistance [NeZero q]
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (candidate : Bool)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount)
    (mask : BinarySecret lweDimension) :
    tvDist
        (branchExperimentAtMask params coordinate candidate challenge auxiliary mask)
        (uniformExperimentAtMask params challenge auxiliary mask) ≤
      Native.ShiftedCandidateEvaluator.branchDistance params coordinate
        (transportCandidate coordinate candidate mask)
        (transportedView params challenge auxiliary mask).1.1 := by
  let transported := transportedView params challenge auxiliary mask
  let finish := fun bootstrappingKey : Native.BootstrappingKey q degree ringRank
      params.levels lweDimension =>
    (bootstrappingKey, transported.1.2, transported.2)
  have hdata := tvDist_map_le (m := ProbComp) finish
    (Native.ShiftedCandidateEvaluator.branchTransform params coordinate
        (transportCandidate coordinate candidate mask) transported.1.1 <$>
      ($ᵗ Native.BootstrappingKey q degree ringRank params.levels lweDimension))
    ($ᵗ Native.BootstrappingKey q degree ringRank params.levels lweDimension)
  simpa only [branchExperimentAtMask, uniformExperimentAtMask, transformWithCoin,
    Native.ShiftedCandidateEvaluator.branchDistance,
    Native.ShiftedCandidateEvaluator.branchTransform,
    Native.ShiftedCandidateEvaluator.selectBootstrappingKey,
    transported, finish, map_eq_bind_pure_comp, Function.comp_def, bind_assoc,
    pure_bind] using hdata

/-- The fixed-mask complete-context defect is bounded by the sum of the explicit TLWE-row
defects.  This is the quantitative counterpart of the exact rowwise freshness lift. -/
theorem tvDist_branchExperimentAtMask_uniformExperimentAtMask_le_rowBranchDistance [NeZero q]
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (candidate : Bool)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount)
    (mask : BinarySecret lweDimension) :
    tvDist
        (branchExperimentAtMask params coordinate candidate challenge auxiliary mask)
        (uniformExperimentAtMask params challenge auxiliary mask) ≤
      branchRowDistanceAtMask params coordinate candidate challenge auxiliary mask := by
  let transported := transportedView params challenge auxiliary mask
  exact (tvDist_branchExperimentAtMask_uniformExperimentAtMask_le_branchDistance
      params coordinate candidate challenge auxiliary mask).trans
    (by
      simpa only [branchRowDistanceAtMask, transported] using
        (Native.ShiftedCandidateEvaluator.branchDistance_le_sum_rowBranchDistance
          params coordinate (transportCandidate coordinate candidate mask)
          transported.1.1))

/-- Exact mask average of the explicit rowwise statistical defects. -/
noncomputable def maskedRowBranchDistance [NeZero q]
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (candidate : Bool)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount) : ℝ :=
  ∑ mask : BinarySecret lweDimension,
    Pr[= mask | ($ᵗ BinarySecret lweDimension)].toReal *
      branchRowDistanceAtMask params coordinate candidate challenge auxiliary mask

/-- Averaging over the scalar XOR mask preserves the sharp expected rowwise cost.  No worst-case
maximum over masks and no additional hybrid loss is introduced. -/
theorem tvDist_maskedBranchExperiment_maskedUniformExperiment_le_maskedRowBranchDistance
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (candidate : Bool)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount) :
    tvDist
        (maskedBranchExperiment params coordinate candidate challenge auxiliary)
        (maskedUniformExperiment params challenge auxiliary) ≤
      maskedRowBranchDistance params coordinate candidate challenge auxiliary := by
  have hmix := FormalProof4FHE.FiniteProduct.tvDist_bind_left_le_expectation
    ($ᵗ BinarySecret lweDimension)
    (fun mask =>
      branchExperimentAtMask params coordinate candidate challenge auxiliary mask)
    (fun mask => uniformExperimentAtMask params challenge auxiliary mask)
  rw [tsum_fintype] at hmix
  refine (show tvDist
      (maskedBranchExperiment params coordinate candidate challenge auxiliary)
      (maskedUniformExperiment params challenge auxiliary) ≤
        ∑ mask : BinarySecret lweDimension,
          Pr[= mask | ($ᵗ BinarySecret lweDimension)].toReal *
            tvDist
              (branchExperimentAtMask params coordinate candidate challenge auxiliary mask)
              (uniformExperimentAtMask params challenge auxiliary mask) by
      simpa only [maskedBranchExperiment, maskedUniformExperiment] using hmix).trans ?_
  unfold maskedRowBranchDistance
  exact Finset.sum_le_sum fun mask _ =>
    mul_le_mul_of_nonneg_left
      (tvDist_branchExperimentAtMask_uniformExperimentAtMask_le_rowBranchDistance
        params coordinate candidate challenge auxiliary mask)
      ENNReal.toReal_nonneg

/-- A claimed bound on the explicit mask-averaged row defects is therefore a valid statistical
branch-freshness bound for the complete native public context. -/
theorem tvDist_maskedBranchExperiment_maskedUniformExperiment_le_of_maskedRowBranchDistance_le
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (coordinate : Fin lweDimension) (candidate : Bool)
    (challenge : Challenge q degree ringRank params.levels lweDimension)
    (auxiliary : Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount)
    (bound : ℝ)
    (hbound : maskedRowBranchDistance params coordinate candidate challenge auxiliary ≤
      bound) :
    tvDist
        (maskedBranchExperiment params coordinate candidate challenge auxiliary)
        (maskedUniformExperiment params challenge auxiliary) ≤ bound :=
  (tvDist_maskedBranchExperiment_maskedUniformExperiment_le_maskedRowBranchDistance
    params coordinate candidate challenge auxiliary).trans hbound

/-- Lift a contextwise statistical branch-freshness bound over the complete augmented source.
This is the usable replacement for the generally over-strong universal bijectivity predicate:
the hypothesis may account for bad masks and non-bijective native CMux maps probabilistically. -/
theorem tvDist_averagedWrongTransform_averagedUniformized_le [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) (bound : ℝ)
    (hbound : ∀ hiddenAndContext,
      hiddenAndContext ∈ support
        (coordinateSource (ringRank := ringRank) (queryCount := queryCount)
          ringErrorSampler keySwitchErrorSampler inputErrorSampler
          (Gadget.Base.ringGadget params) keySwitchGadget coordinate) →
      tvDist
          (maskedBranchExperiment params coordinate (!hiddenAndContext.1)
            hiddenAndContext.2.1 hiddenAndContext.2.2)
          (maskedUniformExperiment params hiddenAndContext.2.1
            hiddenAndContext.2.2) ≤ bound) :
    tvDist
        (averagedWrongTransform (ringRank := ringRank) (queryCount := queryCount)
          params ringErrorSampler keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate)
        (averagedUniformized (ringRank := ringRank) (queryCount := queryCount)
          params ringErrorSampler keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate) ≤ bound := by
  let source := coordinateSource (ringRank := ringRank) (queryCount := queryCount)
    ringErrorSampler keySwitchErrorSampler inputErrorSampler
    (Gadget.Base.ringGadget params) keySwitchGadget coordinate
  have hmix := tvDist_bind_left_le_const (m := ProbComp) source
    (fun hiddenAndContext =>
      maskedBranchExperiment params coordinate (!hiddenAndContext.1)
        hiddenAndContext.2.1 hiddenAndContext.2.2)
    (fun hiddenAndContext =>
      maskedUniformExperiment params hiddenAndContext.2.1 hiddenAndContext.2.2)
    bound (fun hiddenAndContext hsupport => hbound hiddenAndContext hsupport)
  simpa [averagedWrongTransform, transform, sampleCoin,
    maskedBranchExperiment, branchExperimentAtMask, transformWithCoin,
    averagedUniformized, maskedUniformExperiment, source, monad_norm] using hmix

/-- **Statistical native wrong-candidate endpoint.**  A contextwise rank/freshness bound for the
actual executable CMux map yields the same bound against the established augmented uniform public
view. -/
theorem tvDist_averagedWrongTransform_uniformPublicView_le [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) (bound : ℝ)
    (hbound : ∀ hiddenAndContext,
      hiddenAndContext ∈ support
        (coordinateSource (ringRank := ringRank) (queryCount := queryCount)
          ringErrorSampler keySwitchErrorSampler inputErrorSampler
          (Gadget.Base.ringGadget params) keySwitchGadget coordinate) →
      tvDist
          (maskedBranchExperiment params coordinate (!hiddenAndContext.1)
            hiddenAndContext.2.1 hiddenAndContext.2.2)
          (maskedUniformExperiment params hiddenAndContext.2.1
            hiddenAndContext.2.2) ≤ bound) :
    tvDist
        (averagedWrongTransform (ringRank := ringRank) (queryCount := queryCount)
          params ringErrorSampler keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate)
        (uniformPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) ringErrorSampler keySwitchErrorSampler
          inputErrorSampler (Gadget.Base.ringGadget params) keySwitchGadget) ≤ bound := by
  have h := tvDist_averagedWrongTransform_averagedUniformized_le
    params ringErrorSampler keySwitchErrorSampler inputErrorSampler
    keySwitchGadget coordinate bound hbound
  unfold tvDist at h ⊢
  rw [← averagedUniformized_evalDist_eq_uniformPublicView
    params ringErrorSampler keySwitchErrorSampler inputErrorSampler
    keySwitchGadget coordinate]
  exact h

/-! ## Direct statistical fixed-frontend certificate -/

/-- Minimal security certificate for the concrete native frontend.  It fixes the executable
`transform` above and exposes exactly the two averaged statistical obligations consumed by the
generic candidate-recovery reduction.  In particular, it does not require a deterministic
residual representation of the correct branch: randomized output-mask freshness and residual
smudging may be proved together by any sound construction-specific argument.

The wrong obligation is stated only after averaging over the complete generated source.  Thus a
proof may charge bad masks and rank-deficient public contexts by their actual probability rather
than proving a worst-case support-wise bound.  The KSK error sampler is shared between source and
target because the concrete scalar transport preserves the KSK and adaptive tape exactly. -/
structure DirectStatisticalCertificate [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) where
  correctError : Fin lweDimension → ℝ
  freshnessError : Fin lweDimension → ℝ
  correctError_nonneg : ∀ coordinate, 0 ≤ correctError coordinate
  freshnessError_nonneg : ∀ coordinate, 0 ≤ freshnessError coordinate
  correctDistance_le : ∀ coordinate,
    tvDist
        (averagedCorrectTransform (ringRank := ringRank) (queryCount := queryCount)
          params sourceRingErrorSampler keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate)
        (realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) targetRingErrorSampler keySwitchErrorSampler
          inputErrorSampler (Gadget.Base.ringGadget params) keySwitchGadget) ≤
      correctError coordinate
  freshnessDistance_le : ∀ coordinate,
    tvDist
        (averagedWrongTransform (ringRank := ringRank) (queryCount := queryCount)
          params sourceRingErrorSampler keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate)
        (uniformPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) sourceRingErrorSampler keySwitchErrorSampler
          inputErrorSampler (Gadget.Base.ringGadget params) keySwitchGadget) ≤
      freshnessError coordinate

namespace DirectStatisticalCertificate

/-- Install the fixed native evaluator and its two statistical laws into the complete averaged
candidate-view interface used by scalar recovery and amplification. -/
noncomputable def toAveraged [NeZero q]
    {params : Gadget.Base.Parameters q}
    {sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q)}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (certificate : DirectStatisticalCertificate (ringRank := ringRank)
      (lweDimension := lweDimension) (queryCount := queryCount) params
      sourceRingErrorSampler targetRingErrorSampler keySwitchErrorSampler
      inputErrorSampler keySwitchGadget) :
    AveragedCandidateViewTransformer
      (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
      sourceRingErrorSampler targetRingErrorSampler keySwitchErrorSampler
      keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
      keySwitchGadget where
  transform := transform params
  correctError := certificate.correctError
  wrongError := certificate.freshnessError
  correctError_nonneg := certificate.correctError_nonneg
  wrongError_nonneg := certificate.freshnessError_nonneg
  correctDistance := by
    intro coordinate
    simpa only [averagedCorrectTransform] using
      certificate.correctDistance_le coordinate
  wrongDistance := by
    intro coordinate
    have h := certificate.freshnessDistance_le coordinate
    rw [← freshUniformView_eq_uniformPublicView
      (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
      sourceRingErrorSampler keySwitchErrorSampler inputErrorSampler
      (Gadget.Base.ringGadget params) keySwitchGadget] at h
    rw [← freshUniformView_eq_uniformPublicView
      (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
      targetRingErrorSampler keySwitchErrorSampler inputErrorSampler
      (Gadget.Base.ringGadget params) keySwitchGadget]
    exact h

@[simp]
theorem toAveraged_correctError [NeZero q]
    {params : Gadget.Base.Parameters q}
    {sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q)}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (certificate : DirectStatisticalCertificate (ringRank := ringRank)
      (lweDimension := lweDimension) (queryCount := queryCount) params
      sourceRingErrorSampler targetRingErrorSampler keySwitchErrorSampler
      inputErrorSampler keySwitchGadget)
    (coordinate : Fin lweDimension) :
    certificate.toAveraged.correctError coordinate = certificate.correctError coordinate := rfl

@[simp]
theorem toAveraged_wrongError [NeZero q]
    {params : Gadget.Base.Parameters q}
    {sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q)}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (certificate : DirectStatisticalCertificate (ringRank := ringRank)
      (lweDimension := lweDimension) (queryCount := queryCount) params
      sourceRingErrorSampler targetRingErrorSampler keySwitchErrorSampler
      inputErrorSampler keySwitchGadget)
    (coordinate : Fin lweDimension) :
    certificate.toAveraged.wrongError coordinate =
      certificate.freshnessError coordinate := rfl

end DirectStatisticalCertificate

/-! ## Sampled-residual statistical fixed-frontend certificate -/

/-- Security certificate in which the correct native evaluation has an exact normal form with a
sampled BRK/KSK residual.  This is the natural interface for CMux: its residual depends on the
uniform true-branch BRK and other evaluator coins, so it need not be a deterministic function of
the source context.  Totality and a support-wise smudging bound are explicit.

The complementary candidate continues to use the direct mask-averaged branch distance, avoiding
the stronger exact wrong-residual normal form. -/
structure SampledResidualCertificate [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) where
  correctResidualSampler : Fin lweDimension → Bool →
    Challenge q degree ringRank params.levels lweDimension →
    Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount →
    Secret lweDimension ringRank degree →
    ProbComp (EvaluationKeyResidual q degree ringRank params.levels
      lweDimension keySwitchLevels)
  correctError : Fin lweDimension → ℝ
  freshnessError : Fin lweDimension → ℝ
  correctError_nonneg : ∀ coordinate, 0 ≤ correctError coordinate
  freshnessError_nonneg : ∀ coordinate, 0 ≤ freshnessError coordinate
  correctResidualSampler_total : ∀ coordinate hiddenAndContext,
    hiddenAndContext ∈ support
      (coordinateSource (ringRank := ringRank) (queryCount := queryCount)
        sourceRingErrorSampler keySwitchErrorSampler inputErrorSampler
        (Gadget.Base.ringGadget params) keySwitchGadget coordinate) →
    ∀ secrets,
      probFailure (correctResidualSampler coordinate hiddenAndContext.1
        hiddenAndContext.2.1 hiddenAndContext.2.2 secrets) = 0
  correctNormalForm : ∀ coordinate,
    evalDist
        (averagedCorrectTransform (ringRank := ringRank) (queryCount := queryCount)
          params sourceRingErrorSampler keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate) =
      evalDist
        (averagedSampledResidualRealView (ringRank := ringRank)
          (queryCount := queryCount) sourceRingErrorSampler targetRingErrorSampler
          keySwitchErrorSampler keySwitchErrorSampler inputErrorSampler
          (Gadget.Base.ringGadget params) keySwitchGadget coordinate
          (correctResidualSampler coordinate))
  correctCost_le : ∀ coordinate hiddenAndContext,
    hiddenAndContext ∈ support
      (coordinateSource (ringRank := ringRank) (queryCount := queryCount)
        sourceRingErrorSampler keySwitchErrorSampler inputErrorSampler
        (Gadget.Base.ringGadget params) keySwitchGadget coordinate) →
    ∀ secrets residual,
      residual ∈ support
        (correctResidualSampler coordinate hiddenAndContext.1
          hiddenAndContext.2.1 hiddenAndContext.2.2 secrets) →
      ConditionalSmudging.evaluationKeySmudgingCost
          targetRingErrorSampler keySwitchErrorSampler residual.1 residual.2 ≤
        correctError coordinate
  freshnessDistance_le : ∀ coordinate hiddenAndContext,
    hiddenAndContext ∈ support
      (coordinateSource (ringRank := ringRank) (queryCount := queryCount)
        sourceRingErrorSampler keySwitchErrorSampler inputErrorSampler
        (Gadget.Base.ringGadget params) keySwitchGadget coordinate) →
    tvDist
        (maskedBranchExperiment params coordinate (!hiddenAndContext.1)
          hiddenAndContext.2.1 hiddenAndContext.2.2)
        (maskedUniformExperiment params hiddenAndContext.2.1
          hiddenAndContext.2.2) ≤ freshnessError coordinate

namespace SampledResidualCertificate

/-- Sampled residual smudging discharges the direct correct-view distance for the fixed native
evaluator. -/
noncomputable def toDirect [NeZero q]
    {params : Gadget.Base.Parameters q}
    {sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q)}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (certificate : SampledResidualCertificate (ringRank := ringRank)
      (lweDimension := lweDimension) (queryCount := queryCount) params
      sourceRingErrorSampler targetRingErrorSampler keySwitchErrorSampler
      inputErrorSampler keySwitchGadget) :
    DirectStatisticalCertificate (ringRank := ringRank)
      (lweDimension := lweDimension) (queryCount := queryCount) params
      sourceRingErrorSampler targetRingErrorSampler keySwitchErrorSampler
      inputErrorSampler keySwitchGadget where
  correctError := certificate.correctError
  freshnessError := certificate.freshnessError
  correctError_nonneg := certificate.correctError_nonneg
  freshnessError_nonneg := certificate.freshnessError_nonneg
  correctDistance_le := by
    intro coordinate
    unfold tvDist
    rw [certificate.correctNormalForm coordinate]
    simpa only [tvDist] using
      (tvDist_averagedSampledResidualRealView_realPublicView_le
        (ringRank := ringRank) (queryCount := queryCount)
        sourceRingErrorSampler targetRingErrorSampler keySwitchErrorSampler
        keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
        keySwitchGadget coordinate (certificate.correctResidualSampler coordinate)
        (certificate.correctError coordinate)
        (certificate.correctResidualSampler_total coordinate)
        (certificate.correctCost_le coordinate))
  freshnessDistance_le := by
    intro coordinate
    exact tvDist_averagedWrongTransform_uniformPublicView_le
      params sourceRingErrorSampler keySwitchErrorSampler inputErrorSampler
      keySwitchGadget coordinate (certificate.freshnessError coordinate)
      (certificate.freshnessDistance_le coordinate)

/-- Install the sampled-residual certificate into the complete averaged candidate-recovery
interface. -/
noncomputable def toAveraged [NeZero q]
    {params : Gadget.Base.Parameters q}
    {sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q)}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (certificate : SampledResidualCertificate (ringRank := ringRank)
      (lweDimension := lweDimension) (queryCount := queryCount) params
      sourceRingErrorSampler targetRingErrorSampler keySwitchErrorSampler
      inputErrorSampler keySwitchGadget) :
    AveragedCandidateViewTransformer
      (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
      sourceRingErrorSampler targetRingErrorSampler keySwitchErrorSampler
      keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
      keySwitchGadget :=
  certificate.toDirect.toAveraged

end SampledResidualCertificate

/-! ## Concrete sampled-residual statistical certificate -/

/-- Construction-specific certificate with no abstract residual sampler.  The correct residual is
the executable `concreteCorrectResidualSampler` above.  Its loss is split into:

* `normalFormError`, measuring output-mask and error-law freshness between the actual evaluator
  and the fresh-mask sampled-residual experiment;
* `smudgingError`, bounding translation of every supported computed residual; and
* `freshnessError`, measuring the complementary branch's distance to the exact uniform-BRK
  endpoint.

The already-proved phase theorem and sampler totality are not premises of this structure. -/
structure ConcreteStatisticalCertificate [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) where
  normalFormError : Fin lweDimension → ℝ
  smudgingError : Fin lweDimension → ℝ
  freshnessError : Fin lweDimension → ℝ
  normalFormError_nonneg : ∀ coordinate, 0 ≤ normalFormError coordinate
  smudgingError_nonneg : ∀ coordinate, 0 ≤ smudgingError coordinate
  freshnessError_nonneg : ∀ coordinate, 0 ≤ freshnessError coordinate
  normalFormDistance_le : ∀ coordinate,
    tvDist
        (averagedCorrectTransform (ringRank := ringRank) (queryCount := queryCount)
          params sourceRingErrorSampler keySwitchErrorSampler inputErrorSampler
          keySwitchGadget coordinate)
        (averagedSampledResidualRealView (ringRank := ringRank)
          (queryCount := queryCount) sourceRingErrorSampler targetRingErrorSampler
          keySwitchErrorSampler keySwitchErrorSampler inputErrorSampler
          (Gadget.Base.ringGadget params) keySwitchGadget coordinate
          (concreteCorrectResidualSampler params coordinate)) ≤
      normalFormError coordinate
  smudgingCost_le : ∀ coordinate hiddenAndContext,
    hiddenAndContext ∈ support
      (coordinateSource (ringRank := ringRank) (queryCount := queryCount)
        sourceRingErrorSampler keySwitchErrorSampler inputErrorSampler
        (Gadget.Base.ringGadget params) keySwitchGadget coordinate) →
    ∀ secrets residual,
      residual ∈ support
        (concreteCorrectResidualSampler params coordinate hiddenAndContext.1
          hiddenAndContext.2.1 hiddenAndContext.2.2 secrets) →
      ConditionalSmudging.evaluationKeySmudgingCost
          targetRingErrorSampler keySwitchErrorSampler residual.1 residual.2 ≤
        smudgingError coordinate
  freshnessDistance_le : ∀ coordinate hiddenAndContext,
    hiddenAndContext ∈ support
      (coordinateSource (ringRank := ringRank) (queryCount := queryCount)
        sourceRingErrorSampler keySwitchErrorSampler inputErrorSampler
        (Gadget.Base.ringGadget params) keySwitchGadget coordinate) →
    tvDist
        (maskedBranchExperiment params coordinate (!hiddenAndContext.1)
          hiddenAndContext.2.1 hiddenAndContext.2.2)
        (maskedUniformExperiment params hiddenAndContext.2.1
          hiddenAndContext.2.2) ≤ freshnessError coordinate

namespace ConcreteStatisticalCertificate

/-- Triangle inequality composes concrete output freshness with sampled residual smudging, while
the wrong side uses the established exact uniform endpoint. -/
noncomputable def toDirect [NeZero q]
    {params : Gadget.Base.Parameters q}
    {sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q)}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (certificate : ConcreteStatisticalCertificate (ringRank := ringRank)
      (lweDimension := lweDimension) (queryCount := queryCount) params
      sourceRingErrorSampler targetRingErrorSampler keySwitchErrorSampler
      inputErrorSampler keySwitchGadget) :
    DirectStatisticalCertificate (ringRank := ringRank)
      (lweDimension := lweDimension) (queryCount := queryCount) params
      sourceRingErrorSampler targetRingErrorSampler keySwitchErrorSampler
      inputErrorSampler keySwitchGadget where
  correctError := fun coordinate =>
    certificate.normalFormError coordinate + certificate.smudgingError coordinate
  freshnessError := certificate.freshnessError
  correctError_nonneg := fun coordinate =>
    add_nonneg (certificate.normalFormError_nonneg coordinate)
      (certificate.smudgingError_nonneg coordinate)
  freshnessError_nonneg := certificate.freshnessError_nonneg
  correctDistance_le := by
    intro coordinate
    let residualView := averagedSampledResidualRealView (ringRank := ringRank)
      (queryCount := queryCount) sourceRingErrorSampler targetRingErrorSampler
      keySwitchErrorSampler keySwitchErrorSampler inputErrorSampler
      (Gadget.Base.ringGadget params) keySwitchGadget coordinate
      (concreteCorrectResidualSampler params coordinate)
    have hsmudge : tvDist residualView
        (realPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount) targetRingErrorSampler keySwitchErrorSampler
          inputErrorSampler (Gadget.Base.ringGadget params) keySwitchGadget) ≤
        certificate.smudgingError coordinate := by
      exact tvDist_averagedSampledResidualRealView_realPublicView_le
        (ringRank := ringRank) (queryCount := queryCount)
        sourceRingErrorSampler targetRingErrorSampler keySwitchErrorSampler
        keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
        keySwitchGadget coordinate (concreteCorrectResidualSampler params coordinate)
        (certificate.smudgingError coordinate)
        (by
          intro hiddenAndContext _ secrets
          exact probFailure_concreteCorrectResidualSampler params coordinate
            hiddenAndContext.1 hiddenAndContext.2.1 hiddenAndContext.2.2 secrets)
        (certificate.smudgingCost_le coordinate)
    exact (tvDist_triangle _ residualView _).trans
      (add_le_add (certificate.normalFormDistance_le coordinate) hsmudge)
  freshnessDistance_le := by
    intro coordinate
    exact tvDist_averagedWrongTransform_uniformPublicView_le
      params sourceRingErrorSampler keySwitchErrorSampler inputErrorSampler
      keySwitchGadget coordinate (certificate.freshnessError coordinate)
      (certificate.freshnessDistance_le coordinate)

/-- Install the fully concrete three-term certificate into averaged TFHE candidate recovery. -/
noncomputable def toAveraged [NeZero q]
    {params : Gadget.Base.Parameters q}
    {sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q)}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (certificate : ConcreteStatisticalCertificate (ringRank := ringRank)
      (lweDimension := lweDimension) (queryCount := queryCount) params
      sourceRingErrorSampler targetRingErrorSampler keySwitchErrorSampler
      inputErrorSampler keySwitchGadget) :
    AveragedCandidateViewTransformer
      (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
      sourceRingErrorSampler targetRingErrorSampler keySwitchErrorSampler
      keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
      keySwitchGadget :=
  certificate.toDirect.toAveraged

end ConcreteStatisticalCertificate

/-! ## Deterministic-residual statistical fixed-frontend certificate -/

/-- Security certificate for the concrete native frontend with statistical wrong-branch
freshness.  Correct-candidate evaluation is charged through its exact residual normal form.  The
wrong candidate is charged directly by the native branch-map distance after averaging over its
uniform scalar mask; no universal bijectivity or exact wrong normal form is assumed.

The KSK error sampler is shared between source and target because scalar XOR transport preserves
the KSK and adaptive tape exactly.  The target ring sampler may be widened to absorb the correct
CMux residual. -/
structure StatisticalCertificate [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) where
  correctRingResidual : Fin lweDimension → Bool →
    Challenge q degree ringRank params.levels lweDimension →
    Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount →
    Secret lweDimension ringRank degree →
    ConditionalSmudging.BootstrappingResidual
      q degree ringRank params.levels lweDimension
  correctKeySwitchResidual : Fin lweDimension → Bool →
    Challenge q degree ringRank params.levels lweDimension →
    Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount →
    Secret lweDimension ringRank degree →
    ConditionalSmudging.KeySwitchResidual q ringRank degree keySwitchLevels
  correctError : Fin lweDimension → ℝ
  freshnessError : Fin lweDimension → ℝ
  correctError_nonneg : ∀ coordinate, 0 ≤ correctError coordinate
  freshnessError_nonneg : ∀ coordinate, 0 ≤ freshnessError coordinate
  correctNormalForm : ∀ coordinate,
    evalDist (do
        let hiddenAndContext ← coordinateSource (ringRank := ringRank)
          (queryCount := queryCount) sourceRingErrorSampler keySwitchErrorSampler
          inputErrorSampler (Gadget.Base.ringGadget params) keySwitchGadget coordinate
        transform params coordinate hiddenAndContext.1 hiddenAndContext.2.1
          hiddenAndContext.2.2) =
      evalDist
        (averagedResidualRealView (ringRank := ringRank) (queryCount := queryCount)
          sourceRingErrorSampler targetRingErrorSampler keySwitchErrorSampler
          keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
          keySwitchGadget coordinate (correctRingResidual coordinate)
          (correctKeySwitchResidual coordinate))
  correctCost_le : ∀ coordinate hiddenAndContext,
    hiddenAndContext ∈ support
      (coordinateSource (ringRank := ringRank) (queryCount := queryCount)
        sourceRingErrorSampler keySwitchErrorSampler inputErrorSampler
        (Gadget.Base.ringGadget params) keySwitchGadget coordinate) →
    ∀ secrets,
      ConditionalSmudging.evaluationKeySmudgingCost
          targetRingErrorSampler keySwitchErrorSampler
          (correctRingResidual coordinate hiddenAndContext.1
            hiddenAndContext.2.1 hiddenAndContext.2.2 secrets)
          (correctKeySwitchResidual coordinate hiddenAndContext.1
            hiddenAndContext.2.1 hiddenAndContext.2.2 secrets) ≤
        correctError coordinate
  freshnessDistance_le : ∀ coordinate hiddenAndContext,
    hiddenAndContext ∈ support
      (coordinateSource (ringRank := ringRank) (queryCount := queryCount)
        sourceRingErrorSampler keySwitchErrorSampler inputErrorSampler
        (Gadget.Base.ringGadget params) keySwitchGadget coordinate) →
    tvDist
        (maskedBranchExperiment params coordinate (!hiddenAndContext.1)
          hiddenAndContext.2.1 hiddenAndContext.2.2)
        (maskedUniformExperiment params hiddenAndContext.2.1
          hiddenAndContext.2.2) ≤ freshnessError coordinate

namespace StatisticalCertificate

/-- Regard a deterministic residual as a probability-one sampled residual.  This proves the
hierarchy between the legacy fixed-residual interface and the coin-aware sampled interface. -/
noncomputable def toSampled [NeZero q]
    {params : Gadget.Base.Parameters q}
    {sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q)}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (certificate : StatisticalCertificate (ringRank := ringRank)
      (lweDimension := lweDimension) (queryCount := queryCount) params
      sourceRingErrorSampler targetRingErrorSampler keySwitchErrorSampler
      inputErrorSampler keySwitchGadget) :
    SampledResidualCertificate (ringRank := ringRank)
      (lweDimension := lweDimension) (queryCount := queryCount) params
      sourceRingErrorSampler targetRingErrorSampler keySwitchErrorSampler
      inputErrorSampler keySwitchGadget where
  correctResidualSampler := fun coordinate hidden challenge auxiliary secrets ↦
    pure (certificate.correctRingResidual coordinate hidden challenge auxiliary secrets,
      certificate.correctKeySwitchResidual coordinate hidden challenge auxiliary secrets)
  correctError := certificate.correctError
  freshnessError := certificate.freshnessError
  correctError_nonneg := certificate.correctError_nonneg
  freshnessError_nonneg := certificate.freshnessError_nonneg
  correctResidualSampler_total := by
    intros
    simp
  correctNormalForm := by
    intro coordinate
    unfold averagedCorrectTransform
    rw [certificate.correctNormalForm coordinate]
    simp [averagedSampledResidualRealView, freshSampledResidualRealView,
      residualRealViewAtSecret, averagedResidualRealView, freshResidualRealView,
      monad_norm]
  correctCost_le := by
    intro coordinate hiddenAndContext hsupport secrets residual hresidual
    simp only [support_pure, Set.mem_singleton_iff] at hresidual
    subst residual
    exact certificate.correctCost_le coordinate hiddenAndContext hsupport secrets
  freshnessDistance_le := certificate.freshnessDistance_le

/-- Discharge the direct correct-distance obligation through the probability-one sampled
residual specialization and conditional smudging theorem. -/
noncomputable def toDirect [NeZero q]
    {params : Gadget.Base.Parameters q}
    {sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q)}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (certificate : StatisticalCertificate (ringRank := ringRank)
      (lweDimension := lweDimension) (queryCount := queryCount) params
      sourceRingErrorSampler targetRingErrorSampler keySwitchErrorSampler
      inputErrorSampler keySwitchGadget) :
    DirectStatisticalCertificate (ringRank := ringRank)
      (lweDimension := lweDimension) (queryCount := queryCount) params
      sourceRingErrorSampler targetRingErrorSampler keySwitchErrorSampler
      inputErrorSampler keySwitchGadget :=
  certificate.toSampled.toDirect

/-- Install the residual-specialized certificate into the complete averaged candidate-view
interface by first forgetting its stronger exact normal-form witness. -/
noncomputable def toAveraged [NeZero q]
    {params : Gadget.Base.Parameters q}
    {sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q)}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (certificate : StatisticalCertificate (ringRank := ringRank)
      (lweDimension := lweDimension) (queryCount := queryCount) params
      sourceRingErrorSampler targetRingErrorSampler keySwitchErrorSampler
      inputErrorSampler keySwitchGadget) :
    AveragedCandidateViewTransformer
      (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
      sourceRingErrorSampler targetRingErrorSampler keySwitchErrorSampler
      keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
      keySwitchGadget :=
  certificate.toDirect.toAveraged

end StatisticalCertificate

/-! ## Exact fixed-frontend residual certificate -/

/-- Residual certificate for the concrete native evaluator above.  Unlike the generic residual
transformer, this structure has no `transform` field: the two averaged distribution laws must hold
for `NativeShifted.transform` itself. -/
structure Certificate [NeZero q]
    (params : Gadget.Base.Parameters q)
    (sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree))
    (sourceKeySwitchErrorSampler targetKeySwitchErrorSampler inputErrorSampler :
      ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) where
  correctRingResidual : Fin lweDimension → Bool →
    Challenge q degree ringRank params.levels lweDimension →
    Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount →
    Secret lweDimension ringRank degree →
    ConditionalSmudging.BootstrappingResidual
      q degree ringRank params.levels lweDimension
  correctKeySwitchResidual : Fin lweDimension → Bool →
    Challenge q degree ringRank params.levels lweDimension →
    Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount →
    Secret lweDimension ringRank degree →
    ConditionalSmudging.KeySwitchResidual q ringRank degree keySwitchLevels
  wrongKeySwitchResidual : Fin lweDimension → Bool →
    Challenge q degree ringRank params.levels lweDimension →
    Auxiliary q ringRank degree lweDimension keySwitchLevels queryCount →
    Secret lweDimension ringRank degree →
    ConditionalSmudging.KeySwitchResidual q ringRank degree keySwitchLevels
  correctError : Fin lweDimension → ℝ
  wrongError : Fin lweDimension → ℝ
  correctError_nonneg : ∀ coordinate, 0 ≤ correctError coordinate
  wrongError_nonneg : ∀ coordinate, 0 ≤ wrongError coordinate
  correctNormalForm : ∀ coordinate,
    evalDist (do
        let hiddenAndContext ← coordinateSource (ringRank := ringRank)
          (queryCount := queryCount) sourceRingErrorSampler sourceKeySwitchErrorSampler
          inputErrorSampler (Gadget.Base.ringGadget params) keySwitchGadget coordinate
        transform params coordinate hiddenAndContext.1 hiddenAndContext.2.1
          hiddenAndContext.2.2) =
      evalDist
        (averagedResidualRealView (ringRank := ringRank) (queryCount := queryCount)
          sourceRingErrorSampler targetRingErrorSampler sourceKeySwitchErrorSampler
          targetKeySwitchErrorSampler inputErrorSampler
          (Gadget.Base.ringGadget params) keySwitchGadget coordinate
          (correctRingResidual coordinate)
          (correctKeySwitchResidual coordinate))
  wrongNormalForm : ∀ coordinate,
    evalDist (do
        let hiddenAndContext ← coordinateSource (ringRank := ringRank)
          (queryCount := queryCount) sourceRingErrorSampler sourceKeySwitchErrorSampler
          inputErrorSampler (Gadget.Base.ringGadget params) keySwitchGadget coordinate
        transform params coordinate (!hiddenAndContext.1) hiddenAndContext.2.1
          hiddenAndContext.2.2) =
      evalDist
        (averagedResidualUniformView (ringRank := ringRank)
          (lweDimension := lweDimension) (queryCount := queryCount)
          sourceRingErrorSampler sourceKeySwitchErrorSampler targetKeySwitchErrorSampler
          inputErrorSampler (Gadget.Base.ringGadget params) keySwitchGadget coordinate
          (wrongKeySwitchResidual coordinate))
  correctCost_le : ∀ coordinate hiddenAndContext,
    hiddenAndContext ∈ support
      (coordinateSource (ringRank := ringRank) (queryCount := queryCount)
        sourceRingErrorSampler sourceKeySwitchErrorSampler inputErrorSampler
        (Gadget.Base.ringGadget params) keySwitchGadget coordinate) →
    ∀ secrets,
      ConditionalSmudging.evaluationKeySmudgingCost
          targetRingErrorSampler targetKeySwitchErrorSampler
          (correctRingResidual coordinate hiddenAndContext.1
            hiddenAndContext.2.1 hiddenAndContext.2.2 secrets)
          (correctKeySwitchResidual coordinate hiddenAndContext.1
            hiddenAndContext.2.1 hiddenAndContext.2.2 secrets) ≤
        correctError coordinate
  wrongCost_le : ∀ coordinate hiddenAndContext,
    hiddenAndContext ∈ support
      (coordinateSource (ringRank := ringRank) (queryCount := queryCount)
        sourceRingErrorSampler sourceKeySwitchErrorSampler inputErrorSampler
        (Gadget.Base.ringGadget params) keySwitchGadget coordinate) →
    ∀ secrets,
      ConditionalSmudging.keySwitchSmudgingCost targetKeySwitchErrorSampler
          (wrongKeySwitchResidual coordinate hiddenAndContext.1
            hiddenAndContext.2.1 hiddenAndContext.2.2 secrets) ≤
        wrongError coordinate

namespace Certificate

/-- Forget that the frontend is fixed only after installing the concrete native transform into
the generic augmented residual interface. -/
noncomputable def toTransformer [NeZero q]
    {params : Gadget.Base.Parameters q}
    {sourceRingErrorSampler targetRingErrorSampler : ProbComp (RLWE.Rq q degree)}
    {sourceKeySwitchErrorSampler targetKeySwitchErrorSampler inputErrorSampler :
      ProbComp (ZMod q)}
    {keySwitchGadget : Fin keySwitchLevels → ZMod q}
    (certificate : Certificate (ringRank := ringRank)
      (lweDimension := lweDimension) (queryCount := queryCount) params
      sourceRingErrorSampler targetRingErrorSampler sourceKeySwitchErrorSampler
      targetKeySwitchErrorSampler inputErrorSampler keySwitchGadget) :
    AveragedResidualCandidateViewTransformer
      (ringRank := ringRank) (lweDimension := lweDimension) (queryCount := queryCount)
      sourceRingErrorSampler targetRingErrorSampler sourceKeySwitchErrorSampler
      targetKeySwitchErrorSampler inputErrorSampler
      (Gadget.Base.ringGadget params) keySwitchGadget where
  transform := transform params
  correctRingResidual := certificate.correctRingResidual
  correctKeySwitchResidual := certificate.correctKeySwitchResidual
  wrongKeySwitchResidual := certificate.wrongKeySwitchResidual
  correctError := certificate.correctError
  wrongError := certificate.wrongError
  correctError_nonneg := certificate.correctError_nonneg
  wrongError_nonneg := certificate.wrongError_nonneg
  correctNormalForm := certificate.correctNormalForm
  wrongNormalForm := certificate.wrongNormalForm
  correctCost_le := certificate.correctCost_le
  wrongCost_le := certificate.wrongCost_le

end Certificate

end FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery.AugmentedResidual.NativeShifted
