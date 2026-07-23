/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AsymptoticAuxiliaryInputCircularLWE
import FormalProof4FHE.TFHE.CutCycleSecurity

/-!
# Eliminating TFHE's Adaptive Auxiliary-Input Zero Term

The auxiliary-input CircLWE bridge leaves a zero-message-BRK-versus-uniform-BRK term while the
real KSK remains visible.  For arbitrary continuations this is genuinely a side-information
problem.  For the continuations induced by query-bounded adaptive TFHE IND-CPA adversaries, it
reduces to ordinary scalar LWE without another ring-LWE premise.

The key observation is exact: a native zero-message BRK whose ring errors are uniform is itself
uniform on the native BRK carrier.  Thus the two endpoints of the auxiliary-input zero game are
both native bootstrap-zero games, once with the construction's ring sampler and once with a
uniform ring sampler.  Each game's hidden-bit advantage is exactly one query-counted joint-LWE
advantage.  A triangle through the fair hidden-bit endpoint bounds their distance by the sum of
those two conventional LWE advantages.

The asymptotic equal-scalar-noise specialization flattens both joint problems to the same
ordinary binary-secret batch-LWE family.  Consequently adaptive native monomial KDM follows from
one named auxiliary-input CircLWE premise and ordinary batch LWE; no separate zero-side security
assumption remains.
-/

open ENNReal OracleComp

namespace FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput

/-- The generic auxiliary-input zero game is exactly the native bootstrap-zero continuation
game.  The monomial and native cycle specifications differ only on the unused real-BRK field. -/
theorem zeroGame_eq_nativeCycle
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation : Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (Challenge q degree ringRank tgswLevels lweDimension)
      (Auxiliary q degree ringRank lweDimension keySwitchLevels)) :
    LWE.AuxiliaryInput.zeroGame
        (problem q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        (packContinuation continuation) =
      Circular.bootstrapZeroContinuationGame
        (Native.nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        continuation := by
  rw [zeroGame_eq_native]
  rfl

/-- The generic uniform-BRK game is distributionally the native bootstrap-zero game obtained by
using uniform ring errors.  The real KSK and its correlation with both native secrets are
retained exactly. -/
theorem uniformGame_evalDist_eq_uniformError_zeroGame
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation : Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (Challenge q degree ringRank tgswLevels lweDimension)
      (Auxiliary q degree ringRank lweDimension keySwitchLevels)) :
    evalDist (LWE.AuxiliaryInput.uniformGame
        (problem q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        (packContinuation continuation)) =
      evalDist (Circular.bootstrapZeroContinuationGame
        (Native.nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
          ($ᵗ (RLWE.Rq q degree)) keySwitchErrorSampler
          tgswGadget keySwitchGadget)
        continuation) := by
  simp only [LWE.AuxiliaryInput.uniformGame, problem, packContinuation,
    Circular.bootstrapZeroContinuationGame, Native.nativeCycleSpec]
  simp only [bind_assoc, pure_bind]
  refine evalDist_bind_congr' (Native.sampleLweSecret lweDimension) fun lweSecret ↦ ?_
  refine evalDist_bind_congr' (Native.sampleRingSecret ringRank degree) fun ringSecret ↦ ?_
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (Native.BootstrapCutSecurity.generateZeroBootstrappingKey_uniformError_evalDist
      q degree ringRank tgswLevels lweDimension tgswGadget ringSecret).symm
    (fun bootstrapKey ↦
      Native.generateKeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels
        keySwitchErrorSampler keySwitchGadget (keyExtract ringSecret) lweSecret >>=
      fun keySwitchKey ↦ continuation lweSecret ringSecret bootstrapKey keySwitchKey)

/-- For a query-bounded adaptive TFHE continuation, the complete auxiliary-input zero term is at
most two conventional shared-secret joint-LWE advantages.  The first reduction uses the actual
zero BRK context; the second uses the exactly uniform BRK context. -/
theorem adaptiveZeroLweAdvantage_le_two_jointLwe
    {Message : Type}
    {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (hbound : Encryption.Adaptive.IsQueryBound adversary queryCount) :
    zeroLweAdvantage ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        (Encryption.Adaptive.continuation queryCount inputErrorSampler encode adversary) ≤
      LearningWithErrors.advantage
        (Encryption.Adaptive.jointLweProblem q lweDimension
          (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
          keySwitchErrorSampler inputErrorSampler)
        (Encryption.Adaptive.keySwitchMessageReduction ringErrorSampler
          keySwitchErrorSampler inputErrorSampler tgswGadget
          (Encryption.Adaptive.nativeKeySwitchMessage keySwitchGadget) encode adversary) +
      LearningWithErrors.advantage
        (Encryption.Adaptive.jointLweProblem q lweDimension
          (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
          keySwitchErrorSampler inputErrorSampler)
        (Encryption.Adaptive.keySwitchMessageReduction ($ᵗ (RLWE.Rq q degree))
          keySwitchErrorSampler inputErrorSampler tgswGadget
          (Encryption.Adaptive.nativeKeySwitchMessage keySwitchGadget) encode adversary) := by
  rw [← Encryption.Adaptive.abs_signedAdvantage_bootstrapZero_eq_jointLwe queryCount
      ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
      encode adversary hbound,
    ← Encryption.Adaptive.abs_signedAdvantage_bootstrapZero_eq_jointLwe queryCount
      ($ᵗ (RLWE.Rq q degree)) keySwitchErrorSampler inputErrorSampler tgswGadget
      keySwitchGadget encode adversary hbound]
  unfold zeroLweAdvantage LWE.AuxiliaryInput.zeroLweAdvantage
  rw [zeroGame_eq_nativeCycle ringErrorSampler keySwitchErrorSampler
    tgswGadget keySwitchGadget
    (Encryption.Adaptive.continuation queryCount inputErrorSampler encode adversary)]
  unfold Encryption.signedAdvantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
    (uniformGame_evalDist_eq_uniformError_zeroGame ringErrorSampler
      keySwitchErrorSampler tgswGadget keySwitchGadget
      (Encryption.Adaptive.continuation queryCount inputErrorSampler encode adversary)) true]
  have h := abs_sub_le
    (Pr[= true | Encryption.Adaptive.bootstrapZeroGame queryCount ringErrorSampler
      keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary]).toReal
    (1 / 2 : ℝ)
    (Pr[= true | Encryption.Adaptive.bootstrapZeroGame queryCount ($ᵗ (RLWE.Rq q degree))
      keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary]).toReal
  rw [abs_sub_comm (1 / 2 : ℝ)] at h
  simpa only [Encryption.Adaptive.bootstrapZeroGame] using h

/-- Equal scalar noises flatten both joint-LWE terms to ordinary binary-secret batch LWE with
exactly all KSK rows and all adaptive encryption-query rows. -/
theorem adaptiveZeroLweAdvantage_le_two_batchLwe_of_same_noise
    {Message : Type}
    {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (errorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (hbound : Encryption.Adaptive.IsQueryBound adversary queryCount) :
    zeroLweAdvantage ringErrorSampler errorSampler tgswGadget keySwitchGadget
        (Encryption.Adaptive.continuation queryCount errorSampler encode adversary) ≤
      LearningWithErrors.advantage
        (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
          (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels + queryCount)
          errorSampler)
        (FormalProof4FHE.LWE.TwoBlock.reduction
          (Encryption.Adaptive.keySwitchMessageReduction ringErrorSampler
            errorSampler errorSampler tgswGadget
            (Encryption.Adaptive.nativeKeySwitchMessage keySwitchGadget) encode adversary)) +
      LearningWithErrors.advantage
        (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
          (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels + queryCount)
          errorSampler)
        (FormalProof4FHE.LWE.TwoBlock.reduction
          (Encryption.Adaptive.keySwitchMessageReduction ($ᵗ (RLWE.Rq q degree))
            errorSampler errorSampler tgswGadget
            (Encryption.Adaptive.nativeKeySwitchMessage keySwitchGadget) encode adversary)) := by
  have h := adaptiveZeroLweAdvantage_le_two_jointLwe
    ringErrorSampler errorSampler errorSampler tgswGadget keySwitchGadget encode adversary hbound
  let samples := Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels
  let actualReduction : LearningWithErrors.Adversary
      (Encryption.Adaptive.jointLweProblem q lweDimension samples queryCount
        errorSampler errorSampler) :=
    Encryption.Adaptive.keySwitchMessageReduction ringErrorSampler
      errorSampler errorSampler tgswGadget
      (Encryption.Adaptive.nativeKeySwitchMessage keySwitchGadget) encode adversary
  let uniformReduction : LearningWithErrors.Adversary
      (Encryption.Adaptive.jointLweProblem q lweDimension samples queryCount
        errorSampler errorSampler) :=
    Encryption.Adaptive.keySwitchMessageReduction
      ($ᵗ (RLWE.Rq q degree)) errorSampler errorSampler tgswGadget
      (Encryption.Adaptive.nativeKeySwitchMessage keySwitchGadget) encode adversary
  have hActual := FormalProof4FHE.LWE.TwoBlock.advantage_eq_batch
    lweDimension samples queryCount (Native.sampleLweSecret lweDimension)
    embedBinarySecret errorSampler actualReduction
  have hUniform := FormalProof4FHE.LWE.TwoBlock.advantage_eq_batch
    lweDimension samples queryCount (Native.sampleLweSecret lweDimension)
    embedBinarySecret errorSampler uniformReduction
  change zeroLweAdvantage ringErrorSampler errorSampler tgswGadget keySwitchGadget
      (Encryption.Adaptive.continuation queryCount errorSampler encode adversary) ≤
    LearningWithErrors.advantage
      (FormalProof4FHE.LWE.TwoBlock.problem lweDimension samples queryCount
        (Native.sampleLweSecret lweDimension) embedBinarySecret errorSampler)
      actualReduction +
    LearningWithErrors.advantage
      (FormalProof4FHE.LWE.TwoBlock.problem lweDimension samples queryCount
        (Native.sampleLweSecret lweDimension) embedBinarySecret errorSampler)
      uniformReduction at h
  rw [hActual, hUniform] at h
  simpa [samples, actualReduction, uniformReduction,
    Native.KeySwitchSecurity.binaryLweProblem] using h

end FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput

/-- Query-counted joint-LWE reduction whose public BRK context is generated by uniform ring
errors and hence is exactly a uniform native BRK. -/
noncomputable def uniformBootstrapJointLWEReduction {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (adversary : PolynomialQueryAdversary params) : JointLWEAdversaryFamily params where
  queryCount := adversary.queryCount
  queryPolynomial := adversary.queryPolynomial
  queryCount_le := adversary.queryCount_le
  run securityParameter :=
    Encryption.Adaptive.keySwitchMessageReduction
      ($ᵗ (RLWE.Rq (params.q securityParameter) (params.degree securityParameter)))
      (params.keySwitchErrorSampler securityParameter)
      (params.inputErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (Encryption.Adaptive.nativeKeySwitchMessage
        (params.keySwitchGadget securityParameter))
      (params.encode securityParameter)
      (adversary.run securityParameter)

/-- Equal-noise flattened batch-LWE form of `uniformBootstrapJointLWEReduction`. -/
noncomputable def uniformBootstrapBatchLWEReduction {Message : Type}
    (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (adversary : PolynomialQueryAdversary params) : BatchLWEAdversaryFamily params where
  queryCount := adversary.queryCount
  queryPolynomial := adversary.queryPolynomial
  queryCount_le := adversary.queryCount_le
  run securityParameter :=
    FormalProof4FHE.LWE.TwoBlock.reduction
      (Encryption.Adaptive.keySwitchMessageReduction
        ($ᵗ (RLWE.Rq (params.q securityParameter) (params.degree securityParameter)))
        (params.keySwitchErrorSampler securityParameter)
        (params.keySwitchErrorSampler securityParameter)
        (params.tgswGadget securityParameter)
        (Encryption.Adaptive.nativeKeySwitchMessage
          (params.keySwitchGadget securityParameter))
        (params.encode securityParameter)
        (adversary.run securityParameter))

/-- Pointwise asymptotic lift: the induced auxiliary-input zero game costs the actual-context
and uniform-BRK-context joint-LWE reductions. -/
theorem adaptiveZeroLWESecurityGame_advantage_le_two_jointLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (adversary : PolynomialQueryAdversary params) (securityParameter : ℕ) :
    (adaptiveZeroLWESecurityGame params).advantage adversary securityParameter ≤
      (jointLWESecurityGame params).advantage
          (jointLWEReduction params adversary) securityParameter +
        (jointLWESecurityGame params).advantage
          (uniformBootstrapJointLWEReduction params adversary) securityParameter := by
  have h :=
    Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.adaptiveZeroLweAdvantage_le_two_jointLwe
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.inputErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (params.encode securityParameter)
      (adversary.run securityParameter)
      (adversary.isQueryBound securityParameter)
  have hLift := ENNReal.ofReal_le_ofReal h
  exact hLift.trans ENNReal.ofReal_add_le

/-- Equal-noise asymptotic lift to two ordinary binary-secret batch-LWE advantages. -/
theorem adaptiveZeroLWESecurityGame_advantage_le_two_batchLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (hEqualNoise : ∀ securityParameter,
      params.inputErrorSampler securityParameter =
        params.keySwitchErrorSampler securityParameter)
    (adversary : PolynomialQueryAdversary params) (securityParameter : ℕ) :
    (adaptiveZeroLWESecurityGame params).advantage adversary securityParameter ≤
      (batchLWESecurityGame params).advantage
          (batchLWEReduction params adversary) securityParameter +
        (batchLWESecurityGame params).advantage
          (uniformBootstrapBatchLWEReduction params adversary) securityParameter := by
  have h :=
    Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput.adaptiveZeroLweAdvantage_le_two_batchLwe_of_same_noise
      (params.ringErrorSampler securityParameter)
      (params.keySwitchErrorSampler securityParameter)
      (params.tgswGadget securityParameter)
      (params.keySwitchGadget securityParameter)
      (params.encode securityParameter)
      (adversary.run securityParameter)
      (adversary.isQueryBound securityParameter)
  have hLift := ENNReal.ofReal_le_ofReal h
  simpa only [adaptiveZeroLWESecurityGame, zeroLWESecurityGame,
    continuationReduction, batchLWESecurityGame, batchLWEReduction,
    uniformBootstrapBatchLWEReduction, hEqualNoise securityParameter] using
      hLift.trans ENNReal.ofReal_add_le

/-- Ordinary batch-LWE security discharges the previously explicit induced zero-side game. -/
theorem adaptiveZeroLWESecurityGame_secureAgainst_of_batchLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (hEqualNoise : ∀ securityParameter,
      params.inputErrorSampler securityParameter =
        params.keySwitchErrorSampler securityParameter)
    (isPPT : PolynomialQueryAdversary params → Prop)
    (batchLWEIsPPT : BatchLWEAdversaryFamily params → Prop)
    (hActualClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT (batchLWEReduction params adversary))
    (hUniformClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT (uniformBootstrapBatchLWEReduction params adversary))
    (hBatchLWE : (batchLWESecurityGame params).secureAgainst batchLWEIsPPT) :
    (adaptiveZeroLWESecurityGame params).secureAgainst isPPT := by
  intro adversary hadversary
  exact negligible_of_le
    (adaptiveZeroLWESecurityGame_advantage_le_two_batchLWE
      params hEqualNoise adversary)
    (negligible_add
      (hBatchLWE _ (hActualClosed adversary hadversary))
      (hBatchLWE _ (hUniformClosed adversary hadversary)))

/-- **Adaptive native monomial KDM from auxiliary-input CircLWE and ordinary LWE.**  The former
zero-side premise is replaced pointwise by two explicit ordinary batch-LWE reductions. -/
theorem adaptiveSecurityGame_advantage_le_circularLWE_add_two_batchLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (hEqualNoise : ∀ securityParameter,
      params.inputErrorSampler securityParameter =
        params.keySwitchErrorSampler securityParameter)
    (adversary : PolynomialQueryAdversary params) (securityParameter : ℕ) :
    (MonomialKDM.adaptiveSecurityGame params).advantage adversary securityParameter ≤
      (adaptiveCircularLWESecurityGame params).advantage adversary securityParameter +
        ((batchLWESecurityGame params).advantage
            (batchLWEReduction params adversary) securityParameter +
          (batchLWESecurityGame params).advantage
            (uniformBootstrapBatchLWEReduction params adversary)
            securityParameter) := by
  calc
    _ ≤ (adaptiveCircularLWESecurityGame params).advantage adversary securityParameter +
        (adaptiveZeroLWESecurityGame params).advantage adversary securityParameter :=
      adaptiveSecurityGame_advantage_le_circularLWE_add_zeroLWE
        params adversary securityParameter
    _ ≤ _ := add_le_add le_rfl
      (adaptiveZeroLWESecurityGame_advantage_le_two_batchLWE
        params hEqualNoise adversary securityParameter)

/-- Negligible auxiliary-input CircLWE plus ordinary batch LWE implies negligible native
adaptive monomial-KDM advantage; no independent zero-side assumption is needed. -/
theorem adaptiveSecurityGame_secureAgainst_of_circularLWE_and_batchLWE
    {Message : Type} (params : Parameters Message)
    [∀ securityParameter, NeZero (params.q securityParameter)]
    (hEqualNoise : ∀ securityParameter,
      params.inputErrorSampler securityParameter =
        params.keySwitchErrorSampler securityParameter)
    (isPPT : PolynomialQueryAdversary params → Prop)
    (batchLWEIsPPT : BatchLWEAdversaryFamily params → Prop)
    (hActualClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT (batchLWEReduction params adversary))
    (hUniformClosed : ∀ adversary, isPPT adversary →
      batchLWEIsPPT (uniformBootstrapBatchLWEReduction params adversary))
    (hCircular : (adaptiveCircularLWESecurityGame params).secureAgainst isPPT)
    (hBatchLWE : (batchLWESecurityGame params).secureAgainst batchLWEIsPPT) :
    (MonomialKDM.adaptiveSecurityGame params).secureAgainst isPPT := by
  intro adversary hadversary
  exact negligible_of_le
    (adaptiveSecurityGame_advantage_le_circularLWE_add_two_batchLWE
      params hEqualNoise adversary)
    (negligible_add
      (hCircular adversary hadversary)
      (negligible_add
        (hBatchLWE _ (hActualClosed adversary hadversary))
        (hBatchLWE _ (hUniformClosed adversary hadversary))))

end FormalProof4FHE.TFHE.Encryption.Adaptive.Asymptotic.MonomialKDM.AuxiliaryInput
