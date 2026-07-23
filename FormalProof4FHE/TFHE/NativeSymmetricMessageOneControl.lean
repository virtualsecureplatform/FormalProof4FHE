/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeWrongControlFiberBound
import FormalProof4FHE.TFHE.SymmetricDiscreteGaussianSampler

/-!
# Message-One Wrong-Control Normalization for Symmetric Ring Noise

The centered-binomial message-one normalization is not distribution-specific.  Its real
requirement is exact invariance of the native ring-error sampler under negation.  This module
states that interface directly and instantiates it with a symmetrically compiled discrete
Gaussian.  The resulting wrong-control fiber bound is therefore available with the same wide
Gaussian sampler used by conditional smudging.
-/

open OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery.AugmentedResidual.NativeShifted

noncomputable section

open FormalProof4FHE.TFHE
open Native
open FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery

variable {q degree ringRank : ℕ}

/-- Canonical generated message-one control for an arbitrary native ring-error sampler. -/
noncomputable def canonicalMessageOneControlSamplerOf [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q (degree + 1))) :
    ProbComp (RingGSWCiphertext q (degree + 1) ringRank params.levels) := do
  let ringSecret ← sampleRingSecret ringRank (degree + 1)
  generatedControlSampler (ringRank := ringRank) params ringErrorSampler true ringSecret

/-- Complementary-candidate normalization for every exactly negation-symmetric ring-error
sampler. -/
theorem candidateControl_generatedControl_wrong_evalDist_of_negationSymmetric
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hsymmetric : Native.ScalarSecretRandomization.NegationSymmetric ringErrorSampler)
    (hidden : Bool) (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    evalDist
        (Native.ShiftedCandidateEvaluator.candidateControl params (!hidden) <$>
          generatedControlSampler (ringRank := ringRank) params
            ringErrorSampler hidden ringSecret) =
      evalDist
        (generatedControlSampler (ringRank := ringRank) params
          ringErrorSampler true ringSecret) := by
  unfold generatedControlSampler Native.ShiftedCandidateEvaluator.candidateControl
  rw [← TGSW.MonomialKDM.directEncrypt_eq_expandedDirectEncrypt,
    ← TGSW.MonomialKDM.directEncrypt_eq_expandedDirectEncrypt]
  calc
    _ = evalDist
        (Native.ScalarSecretRandomization.toggleTGSW
            (Gadget.Base.ringGadget params) (!hidden) <$>
          TGSW.encrypt ringRank params.levels ringErrorSampler
            (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
            (embedConstantBit q (degree + 1) hidden)) := by
      exact evalDist_map_eq_of_evalDist_eq
        (TGSW.encrypt_evalDist_eq_directEncrypt ringRank params.levels
          ringErrorSampler (embedRingSecret q ringSecret)
          (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) hidden)).symm _
    _ = evalDist
        (TGSW.encrypt ringRank params.levels ringErrorSampler
          (embedRingSecret q ringSecret) (Gadget.Base.ringGadget params)
          (embedConstantBit q (degree + 1) true)) := by
      rw [BlindRotation.embedConstantBit_eq_embedBit,
        BlindRotation.embedConstantBit_eq_embedBit]
      simpa [Native.ShiftedCandidateEvaluator.maskedBit_not_self] using
        (Native.ScalarSecretRandomization.toggleTGSW_encrypt_evalDist
          ringErrorSampler hsymmetric (embedRingSecret q ringSecret)
          (Gadget.Base.ringGadget params) hidden (!hidden))
    _ = _ := TGSW.encrypt_evalDist_eq_directEncrypt ringRank params.levels
      ringErrorSampler (embedRingSecret q ringSecret)
      (Gadget.Base.ringGadget params) (embedConstantBit q (degree + 1) true)

/-- Toggling the canonical wrong-candidate control erases the hidden bit for every symmetric
ring-error sampler. -/
theorem canonicalWrongBranchControl_candidateControl_evalDist_eq_messageOne_of_negationSymmetric
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hsymmetric : Native.ScalarSecretRandomization.NegationSymmetric ringErrorSampler) :
    evalDist
        ((fun hiddenAndControl =>
            Native.ShiftedCandidateEvaluator.candidateControl params
              (!hiddenAndControl.1) hiddenAndControl.2) <$>
          canonicalWrongBranchControlSampler (ringRank := ringRank) params
            ringErrorSampler) =
      evalDist
        (canonicalMessageOneControlSamplerOf (ringRank := ringRank)
          params ringErrorSampler) := by
  let RingSecrets := sampleRingSecret ringRank (degree + 1)
  let normalized := fun (hidden : Bool)
      (ringSecret : RingBinarySecret ringRank (degree + 1)) =>
    Native.ShiftedCandidateEvaluator.candidateControl params (!hidden) <$>
      generatedControlSampler (ringRank := ringRank) params
        ringErrorSampler hidden ringSecret
  let messageOne := fun (ringSecret : RingBinarySecret ringRank (degree + 1)) =>
    generatedControlSampler (ringRank := ringRank) params ringErrorSampler true ringSecret
  calc
    _ = evalDist (($ᵗ Bool) >>= fun hidden =>
        RingSecrets >>= normalized hidden) := by
      simp [canonicalWrongBranchControlSampler, RingSecrets, normalized,
        map_eq_bind_pure_comp, bind_assoc, monad_norm]
    _ = evalDist (($ᵗ Bool) >>= fun _ => RingSecrets >>= messageOne) := by
      refine evalDist_bind_congr' ($ᵗ Bool) fun hidden => ?_
      refine evalDist_bind_congr' RingSecrets fun ringSecret => ?_
      exact candidateControl_generatedControl_wrong_evalDist_of_negationSymmetric
        params ringErrorSampler hsymmetric hidden ringSecret
    _ = evalDist (RingSecrets >>= messageOne) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
        ($ᵗ Bool) (by simp) _
    _ = _ := by
      simp [canonicalMessageOneControlSamplerOf, RingSecrets, messageOne]

/-- Expected normalized one-row defect under an arbitrary canonical message-one control law. -/
noncomputable def averagedCanonicalMessageOneControlDistanceOf [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q (degree + 1))) : ℝ :=
  ∑' control : RingGSWCiphertext q (degree + 1) ringRank params.levels,
    Pr[= control |
      canonicalMessageOneControlSamplerOf (degree := degree) (ringRank := ringRank)
        params ringErrorSampler].toReal *
      messageOneControlDistance (degree := degree + 1) params control

/-- Exact expected finite-fiber loss under an arbitrary canonical message-one control law. -/
noncomputable def averagedCanonicalMessageOneControlFiberLossOf [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q (degree + 1))) : ℝ :=
  ∑' control : RingGSWCiphertext q (degree + 1) ringRank params.levels,
    Pr[= control |
      canonicalMessageOneControlSamplerOf (degree := degree) (ringRank := ringRank)
        params ringErrorSampler].toReal *
      messageOneControlFiberLoss (degree := degree + 1) params control

/-- Hidden-bit elimination for the expected normalized defect under every symmetric source
sampler. -/
theorem averagedCanonicalWrongBranchControlDistance_eq_messageOne_of_negationSymmetric
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hsymmetric : Native.ScalarSecretRandomization.NegationSymmetric ringErrorSampler) :
    averagedCanonicalWrongBranchControlDistance (ringRank := ringRank)
        params ringErrorSampler =
      averagedCanonicalMessageOneControlDistanceOf (degree := degree)
        (ringRank := ringRank) params ringErrorSampler := by
  let sampler := canonicalWrongBranchControlSampler (ringRank := ringRank)
    params ringErrorSampler
  let normalize := fun hiddenAndControl :
      Bool × RingGSWCiphertext q (degree + 1) ringRank params.levels =>
    Native.ShiftedCandidateEvaluator.candidateControl params
      (!hiddenAndControl.1) hiddenAndControl.2
  let cost := messageOneControlDistance (degree := degree + 1)
    (ringRank := ringRank) params
  have hdist : evalDist (normalize <$> sampler) =
      evalDist (canonicalMessageOneControlSamplerOf (ringRank := ringRank)
        params ringErrorSampler) := by
    simpa only [sampler, normalize] using
      (canonicalWrongBranchControl_candidateControl_evalDist_eq_messageOne_of_negationSymmetric
        (ringRank := ringRank) params ringErrorSampler hsymmetric)
  unfold averagedCanonicalWrongBranchControlDistance
    averagedCanonicalMessageOneControlDistanceOf
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
          canonicalMessageOneControlSamplerOf (ringRank := ringRank)
            params ringErrorSampler].toReal * cost control :=
      FormalProof4FHE.FiniteProduct.tsum_probOutput_toReal_mul_congr hdist cost

/-- The pointwise finite-fiber bound averages under every generated message-one law. -/
theorem averagedCanonicalMessageOneControlDistanceOf_le_fiberLoss
    [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q (degree + 1))) :
    averagedCanonicalMessageOneControlDistanceOf (degree := degree)
        (ringRank := ringRank) params ringErrorSampler ≤
      averagedCanonicalMessageOneControlFiberLossOf (degree := degree)
        (ringRank := ringRank) params ringErrorSampler := by
  unfold averagedCanonicalMessageOneControlDistanceOf
    averagedCanonicalMessageOneControlFiberLossOf
  apply Summable.tsum_le_tsum
  · intro control
    exact mul_le_mul_of_nonneg_left
      (messageOneControlDistance_le_fiberLoss params control)
      ENNReal.toReal_nonneg
  · exact Summable.of_finite
  · exact Summable.of_finite

/-- Complete native wrong-view fiber bound for every exactly negation-symmetric source-noise
sampler. -/
theorem
    tvDist_averagedWrongTransform_uniformPublicView_le_card_mul_averagedMessageOneControlFiberLossOf
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hsymmetric : Native.ScalarSecretRandomization.NegationSymmetric ringErrorSampler)
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
        averagedCanonicalMessageOneControlFiberLossOf (degree := degree)
          (ringRank := ringRank) params ringErrorSampler := by
  calc
    _ ≤ (lweDimension * TGSW.rowCount ringRank params.levels : ℕ) *
        averagedCanonicalWrongBranchControlDistance (ringRank := ringRank)
          params ringErrorSampler :=
      tvDist_averagedWrongTransform_uniformPublicView_le_card_mul_averagedCanonicalControlDistance
        (ringRank := ringRank) (lweDimension := lweDimension)
        (queryCount := queryCount) params ringErrorSampler keySwitchErrorSampler
        inputErrorSampler keySwitchGadget coordinate
    _ = (lweDimension * TGSW.rowCount ringRank params.levels : ℕ) *
        averagedCanonicalMessageOneControlDistanceOf (degree := degree)
          (ringRank := ringRank) params ringErrorSampler := by
      rw [averagedCanonicalWrongBranchControlDistance_eq_messageOne_of_negationSymmetric
        (ringRank := ringRank) params ringErrorSampler hsymmetric]
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (averagedCanonicalMessageOneControlDistanceOf_le_fiberLoss
        (degree := degree) (ringRank := ringRank) params ringErrorSampler)
      (Nat.cast_nonneg _)

/-- Symmetrically compiled discrete-Gaussian source controls satisfy the generic wrong-view fiber
bound exactly, while retaining their independent Gaussian approximation certificate. -/
theorem
    tvDist_averagedWrongTransform_uniformPublicView_le_symmetricDiscreteGaussianFiberLoss
    {q degree ringRank lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    {alpha : ℝ} {halpha : 0 < alpha}
    (params : Gadget.Base.Parameters q)
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (hsymmetric : DiscreteGaussianSampler.TicketNegationSymmetric certificate)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (coordinate : Fin lweDimension) :
    tvDist
        (averagedWrongTransform (ringRank := ringRank) (queryCount := queryCount)
          params (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
          keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate)
        (uniformPublicView (ringRank := ringRank) (lweDimension := lweDimension)
          (queryCount := queryCount)
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
          keySwitchErrorSampler inputErrorSampler (Gadget.Base.ringGadget params)
          keySwitchGadget) ≤
      (lweDimension * TGSW.rowCount ringRank params.levels : ℕ) *
        averagedCanonicalMessageOneControlFiberLossOf (degree := degree)
          (ringRank := ringRank) params
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate) := by
  exact
    tvDist_averagedWrongTransform_uniformPublicView_le_card_mul_averagedMessageOneControlFiberLossOf
      (ringRank := ringRank) (lweDimension := lweDimension)
      (queryCount := queryCount) params
      (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
      (DiscreteGaussianSampler.ringSampler_negationSymmetric
        (degree + 1) certificate hsymmetric)
      keySwitchErrorSampler inputErrorSampler keySwitchGadget coordinate

end

end FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery.AugmentedResidual.NativeShifted

namespace FormalProof4FHE.TFHE.Native.ScalarSecretRandomization

open FormalProof4FHE.TFHE

/-- Scalar XOR transport of a generated native BRK is exact for every negation-symmetric ring
error sampler. -/
theorem transformBootstrappingKey_generate_of_negationSymmetric
    {q degree ringRank levels lweDimension : ℕ} [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hsymmetric : NegationSymmetric errorSampler)
    (gadget : Fin levels → RLWE.Rq q (degree + 1))
    (lweSecret mask : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    evalDist (transformBootstrappingKey gadget mask <$>
        Native.generateBootstrappingKey q (degree + 1) ringRank levels lweDimension
          errorSampler gadget lweSecret ringSecret) =
      evalDist (Native.generateBootstrappingKey q (degree + 1) ringRank levels lweDimension
        errorSampler gadget (maskedSecret lweSecret mask) ringSecret) := by
  rw [show transformBootstrappingKey gadget mask =
      (fun bootstrappingKey coordinate =>
        toggleTGSW gadget (mask coordinate) (bootstrappingKey coordinate)) by rfl]
  simpa only [Native.generateBootstrappingKey, maskedSecret] using
    mOfFn_map_evalDist_congr lweDimension
      (fun coordinate =>
        TGSW.encrypt ringRank levels errorSampler
          (embedRingSecret q ringSecret) gadget
          (embedConstantBit q (degree + 1) (lweSecret coordinate)))
      (fun coordinate =>
        TGSW.encrypt ringRank levels errorSampler
          (embedRingSecret q ringSecret) gadget
          (embedConstantBit q (degree + 1)
            (LWE.MultiKeyAffine.maskedBit (lweSecret coordinate) (mask coordinate))))
      (fun coordinate => toggleTGSW gadget (mask coordinate))
      (fun coordinate => by
        simpa only [BlindRotation.embedConstantBit_eq_embedBit] using
          toggleTGSW_encrypt_evalDist errorSampler hsymmetric
            (embedRingSecret q ringSecret) gadget
            (lweSecret coordinate) (mask coordinate))

end FormalProof4FHE.TFHE.Native.ScalarSecretRandomization

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery.AugmentedResidual.NativeShifted

open FormalProof4FHE.TFHE
open Native

/-- The same symmetric-noise transport law for the direct native BRK presentation used by the
off-diagonal normal form. -/
theorem transformDirectBootstrappingKey_of_negationSymmetric_evalDist
    {q degree ringRank lweDimension : ℕ} [NeZero q]
    (params : Gadget.Base.Parameters q)
    (ringErrorSampler : ProbComp (RLWE.Rq q (degree + 1)))
    (hsymmetric : Native.ScalarSecretRandomization.NegationSymmetric ringErrorSampler)
    (hidden mask : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    evalDist
        (Native.ScalarSecretRandomization.transformBootstrappingKey
            (Gadget.Base.ringGadget params) mask <$>
          Native.BootstrapSecurity.generateDirectBootstrappingKey
            q (degree + 1) ringRank params.levels lweDimension ringErrorSampler
            (Gadget.Base.ringGadget params) hidden ringSecret) =
      evalDist
        (Native.BootstrapSecurity.generateDirectBootstrappingKey
          q (degree + 1) ringRank params.levels lweDimension ringErrorSampler
          (Gadget.Base.ringGadget params)
          (Native.ScalarSecretRandomization.maskedSecret hidden mask) ringSecret) := by
  let Gadget : Fin params.levels → RLWE.Rq q (degree + 1) :=
    Gadget.Base.ringGadget params
  let Transform := Native.ScalarSecretRandomization.transformBootstrappingKey
    (dimension := ringRank) Gadget mask
  let SourceNative := Native.generateBootstrappingKey
    q (degree + 1) ringRank params.levels lweDimension ringErrorSampler
    Gadget hidden ringSecret
  let SourceDirect := Native.BootstrapSecurity.generateDirectBootstrappingKey
    q (degree + 1) ringRank params.levels lweDimension ringErrorSampler
    Gadget hidden ringSecret
  let TargetNative := Native.generateBootstrappingKey
    q (degree + 1) ringRank params.levels lweDimension ringErrorSampler
    Gadget (Native.ScalarSecretRandomization.maskedSecret hidden mask) ringSecret
  let TargetDirect := Native.BootstrapSecurity.generateDirectBootstrappingKey
    q (degree + 1) ringRank params.levels lweDimension ringErrorSampler
    Gadget (Native.ScalarSecretRandomization.maskedSecret hidden mask) ringSecret
  have hSource : evalDist SourceNative = evalDist SourceDirect :=
    Native.BootstrapSecurity.generateBootstrappingKey_evalDist_eq_direct
      q (degree + 1) ringRank params.levels lweDimension ringErrorSampler
      Gadget hidden ringSecret
  have hMapped : evalDist (Transform <$> SourceNative) =
      evalDist (Transform <$> SourceDirect) :=
    evalDist_map_eq_of_evalDist_eq hSource Transform
  calc
    evalDist (Transform <$> SourceDirect) =
        evalDist (Transform <$> SourceNative) := hMapped.symm
    _ = evalDist TargetNative :=
      Native.ScalarSecretRandomization.transformBootstrappingKey_generate_of_negationSymmetric
        ringErrorSampler hsymmetric Gadget hidden mask ringSecret
    _ = evalDist TargetDirect :=
      Native.BootstrapSecurity.generateBootstrappingKey_evalDist_eq_direct
        q (degree + 1) ringRank params.levels lweDimension ringErrorSampler
        Gadget (Native.ScalarSecretRandomization.maskedSecret hidden mask) ringSecret

/-- Symmetrically compiled discrete-Gaussian BRKs transport exactly under scalar XOR masking. -/
theorem transformDirectBootstrappingKey_symmetricDiscreteGaussian_evalDist
    {q degree ringRank lweDimension : ℕ} [NeZero q]
    {alpha : ℝ} {halpha : 0 < alpha}
    (params : Gadget.Base.Parameters q)
    (certificate : DiscreteGaussianSampler.ScalarCertificate q alpha halpha)
    (hsymmetric : DiscreteGaussianSampler.TicketNegationSymmetric certificate)
    (hidden mask : BinarySecret lweDimension)
    (ringSecret : RingBinarySecret ringRank (degree + 1)) :
    evalDist
        (Native.ScalarSecretRandomization.transformBootstrappingKey
            (Gadget.Base.ringGadget params) mask <$>
          Native.BootstrapSecurity.generateDirectBootstrappingKey
            q (degree + 1) ringRank params.levels lweDimension
            (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
            (Gadget.Base.ringGadget params) hidden ringSecret) =
      evalDist
        (Native.BootstrapSecurity.generateDirectBootstrappingKey
          q (degree + 1) ringRank params.levels lweDimension
          (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
          (Gadget.Base.ringGadget params)
          (Native.ScalarSecretRandomization.maskedSecret hidden mask) ringSecret) := by
  exact transformDirectBootstrappingKey_of_negationSymmetric_evalDist
    params (DiscreteGaussianSampler.ringSampler (degree + 1) certificate)
    (DiscreteGaussianSampler.ringSampler_negationSymmetric
      (degree + 1) certificate hsymmetric)
    hidden mask ringSecret

end FormalProof4FHE.TFHE.Encryption.Adaptive.PublicAuxiliaryInputCircular.Search.PairedRecovery.CoordinateRecovery.AugmentedResidual.NativeShifted
