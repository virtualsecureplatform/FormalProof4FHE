/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SharedRandomnessOneCycleAdaptiveEncryption
import FormalProof4FHE.TFHE.SharedRandomnessOneCycleAuxiliaryInput

/-!
# Narrow-Noise Adaptive TFHE Security from One-Cycle CircLWE

This module composes the exact shared-randomness one-cycle CircLWE problem with the reusable-key
adaptive encryption game.  Unlike the unconditional uniform-error endpoint, the theorem here
places no closeness-to-uniform requirement on the native ring-error sampler.  It therefore
accepts narrow centered-binomial or discrete-Gaussian ring errors.

For every query-bounded adversary, the complete security loss is split into exactly two terms:

1. one native rank-one, self-circular BRK-versus-uniform auxiliary-input CircLWE advantage; and
2. one ordinary binary-secret batch-LWE advantage containing the suffix KSK and all charged
   input-encryption rows.

Public deterministic FHE evaluation is closed under the same bound.  The result is a precise
conditional security theorem for the real native circular object; proving the first term from a
standard assumption remains the research problem rather than an implicit axiom of this file.
-/

open Matrix OracleComp OracleSpec

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.SharedRandomnessOneCycle.CircularSecurity

noncomputable section

variable {Message : Type}
  {q prefixDimension suffixDimension tgswLevels keySwitchLevels queryCount : ℕ} [NeZero q]

/-- The exact one-key auxiliary-input CircLWE term seen by the adaptive encryption experiment. -/
noncomputable def circularLweAdvantage
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) : ℝ :=
  Native.SharedRandomnessOneCycle.AuxiliaryInput.circularLweAdvantage
    ringErrorSampler keySwitchErrorSampler
    tgswGadget keySwitchGadget
    (continuation queryCount inputErrorSampler encode adversary)

/-- The literal one-circular KDM term seen by the adaptive encryption experiment.  Its two
endpoints are `BRK_S(prefix(S))` and `BRK_S(0)` under the same complete master key `S`, with the
same suffix-only KSK and adaptive input-encryption continuation.  The master key is retained by
the experiment only to generate that continuation; it is not given to the public adversary. -/
noncomputable def oneCircularKdmAdvantage
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) : ℝ :=
  Native.SharedRandomnessOneCycle.AuxiliaryInput.kdmAdvantage
    ringErrorSampler keySwitchErrorSampler
    tgswGadget keySwitchGadget
    (continuation queryCount inputErrorSampler encode adversary)

/-- Non-circular zero-message BRK versus uniform-BRK side-information term for the same adaptive
continuation.  Keeping this term separate prevents the real-versus-zero circular assumption from
being silently strengthened to real-versus-uniform CircLWE. -/
noncomputable def zeroBootstrapLweAdvantage
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) : ℝ :=
  Native.SharedRandomnessOneCycle.AuxiliaryInput.zeroLweAdvantage
    ringErrorSampler keySwitchErrorSampler
    tgswGadget keySwitchGadget
    (continuation queryCount inputErrorSampler encode adversary)

/-- The named adaptive KDM term is definitionally the distance from the honest game to the
native zero-message BRK game.  In the honest endpoint the BRK plaintext key is the prefix of the
same master key used for ring encryption. -/
theorem oneCircularKdmAdvantage_eq_real_boolDistAdvantage_bootstrapZero
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) :
    oneCircularKdmAdvantage queryCount ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget encode adversary =
      (realGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget encode adversary).boolDistAdvantage
        (Native.SharedRandomnessOneCycle.bootstrapZeroSecretContinuationGame q
          prefixDimension suffixDimension tgswLevels keySwitchLevels ringErrorSampler
          keySwitchErrorSampler tgswGadget keySwitchGadget
          (continuation queryCount inputErrorSampler encode adversary)) := by
  unfold oneCircularKdmAdvantage
  rw [Native.SharedRandomnessOneCycle.AuxiliaryInput.kdmAdvantage_eq_secretContinuationAdvantage]
  rfl

/-- Real-versus-uniform CircLWE is bounded by the literal real-versus-zero one-circular KDM game
plus the separate zero-message encryption branch. -/
theorem circularLweAdvantage_le_oneCircularKdm_add_zeroBootstrapLwe
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) :
    circularLweAdvantage queryCount ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget encode adversary ≤
      oneCircularKdmAdvantage queryCount ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget encode adversary +
        zeroBootstrapLweAdvantage queryCount ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget encode adversary := by
  unfold circularLweAdvantage oneCircularKdmAdvantage zeroBootstrapLweAdvantage
  exact
    LWE.AuxiliaryInput.circularLweAdvantage_le_kdm_add_zeroLwe
      (Native.SharedRandomnessOneCycle.AuxiliaryInput.problem q prefixDimension
        suffixDimension tgswLevels keySwitchLevels ringErrorSampler
        keySwitchErrorSampler tgswGadget keySwitchGadget)
      (Native.SharedRandomnessOneCycle.AuxiliaryInput.packContinuation
        (continuation queryCount inputErrorSampler encode adversary))

/-- The named one-cycle term is exactly the honest adaptive game versus the uniform-BRK
endpoint, with the same master key, suffix KSK, and input-encryption continuation. -/
theorem circularLweAdvantage_eq_real_boolDistAdvantage_masterUniform
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels) :
    circularLweAdvantage queryCount ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget encode adversary =
      (realGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget encode adversary).boolDistAdvantage
        (masterUniformBootstrapGame queryCount keySwitchErrorSampler inputErrorSampler
          keySwitchGadget encode adversary) := by
  unfold circularLweAdvantage
    Native.SharedRandomnessOneCycle.AuxiliaryInput.circularLweAdvantage
    LWE.AuxiliaryInput.circularLweAdvantage
  rw [Native.SharedRandomnessOneCycle.AuxiliaryInput.realGame_eq_native,
    Native.SharedRandomnessOneCycle.AuxiliaryInput.uniformGame_eq_native]
  rfl

/-- The uniform-BRK master-key endpoint is exactly the ordinary unequal-noise joint-LWE term. -/
theorem abs_signedAdvantage_masterUniformBootstrap_eq_jointLwe
    (queryCount : ℕ)
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels)
    (hbound : Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (masterUniformBootstrapGame queryCount keySwitchErrorSampler inputErrorSampler
        keySwitchGadget encode adversary)| =
      LearningWithErrors.advantage
        (jointLweProblem q prefixDimension suffixDimension keySwitchLevels queryCount
          keySwitchErrorSampler inputErrorSampler)
        (jointLweReduction keySwitchErrorSampler inputErrorSampler keySwitchGadget
          encode adversary) := by
  have hGame := masterUniformBootstrapGame_evalDist_eq_independent
    (q := q) (prefixDimension := prefixDimension) (suffixDimension := suffixDimension)
    (tgswLevels := tgswLevels) (keySwitchLevels := keySwitchLevels)
    queryCount keySwitchErrorSampler inputErrorSampler keySwitchGadget encode adversary
  have hSigned :
      Encryption.signedAdvantage
          (masterUniformBootstrapGame queryCount keySwitchErrorSampler inputErrorSampler
            keySwitchGadget encode adversary) =
        Encryption.signedAdvantage
          (independentUniformBootstrapGame queryCount keySwitchErrorSampler
            inputErrorSampler keySwitchGadget encode adversary) := by
    unfold Encryption.signedAdvantage
    rw [evalDist_ext_iff.mp hGame true]
  rw [hSigned]
  exact abs_signedAdvantage_independentUniformBootstrap_eq_jointLwe queryCount
    keySwitchErrorSampler inputErrorSampler keySwitchGadget encode adversary hbound

/-- **Reusable-key adaptive narrow-noise TFHE security.**  The honest game is bounded by one
native self-circular BRK CircLWE term plus the ordinary LWE term for the suffix KSK and all input
queries.  No statistical replacement of the ring noise is used. -/
theorem abs_signedAdvantage_real_le_circularLwe_add_jointLwe
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels)
    (hbound : Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (realGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      circularLweAdvantage queryCount ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget encode adversary +
        LearningWithErrors.advantage
          (jointLweProblem q prefixDimension suffixDimension keySwitchLevels queryCount
            keySwitchErrorSampler inputErrorSampler)
          (jointLweReduction keySwitchErrorSampler inputErrorSampler keySwitchGadget
            encode adversary) := by
  let honestGame := realGame queryCount ringErrorSampler keySwitchErrorSampler
    inputErrorSampler tgswGadget keySwitchGadget encode adversary
  let uniformGame := masterUniformBootstrapGame queryCount keySwitchErrorSampler
    inputErrorSampler keySwitchGadget encode adversary
  have hCircular :
      honestGame.boolDistAdvantage uniformGame =
        circularLweAdvantage queryCount ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget encode adversary := by
    exact (circularLweAdvantage_eq_real_boolDistAdvantage_masterUniform queryCount
      ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget
      keySwitchGadget encode adversary).symm
  have hUniform :
      |Encryption.signedAdvantage uniformGame| =
        LearningWithErrors.advantage
          (jointLweProblem q prefixDimension suffixDimension keySwitchLevels queryCount
            keySwitchErrorSampler inputErrorSampler)
          (jointLweReduction keySwitchErrorSampler inputErrorSampler keySwitchGadget
            encode adversary) := by
    exact abs_signedAdvantage_masterUniformBootstrap_eq_jointLwe queryCount
      keySwitchErrorSampler inputErrorSampler keySwitchGadget encode adversary hbound
  calc
    |Encryption.signedAdvantage
        (realGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget encode adversary)| =
        |(Pr[= true | honestGame]).toReal - 1 / 2| := by
      rfl
    _ ≤ |(Pr[= true | honestGame]).toReal -
          (Pr[= true | uniformGame]).toReal| +
        |(Pr[= true | uniformGame]).toReal - 1 / 2| :=
      abs_sub_le _ _ _
    _ = honestGame.boolDistAdvantage uniformGame +
        |Encryption.signedAdvantage uniformGame| := by
      rfl
    _ = circularLweAdvantage queryCount ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget encode adversary +
        LearningWithErrors.advantage
          (jointLweProblem q prefixDimension suffixDimension keySwitchLevels queryCount
            keySwitchErrorSampler inputErrorSampler)
          (jointLweReduction keySwitchErrorSampler inputErrorSampler keySwitchGadget
            encode adversary) := by
      rw [hCircular, hUniform]

/-- With equal KSK and input noises, the non-circular endpoint is one conventional binary-secret
batch-LWE problem with exactly `suffixDimension * keySwitchLevels + queryCount` rows. -/
theorem abs_signedAdvantage_real_le_circularLwe_add_batchLwe_of_same_noise
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (errorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels)
    (hbound : Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (realGame queryCount ringErrorSampler errorSampler errorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      circularLweAdvantage queryCount ringErrorSampler errorSampler errorSampler
          tgswGadget keySwitchGadget encode adversary +
        LearningWithErrors.advantage
          (Native.KeySwitchSecurity.binaryLweProblem q prefixDimension
            (keySwitchSamples suffixDimension keySwitchLevels + queryCount) errorSampler)
          (FormalProof4FHE.LWE.TwoBlock.reduction
            (jointLweReduction errorSampler errorSampler keySwitchGadget
              encode adversary)) := by
  calc
    |Encryption.signedAdvantage
        (realGame queryCount ringErrorSampler errorSampler errorSampler
          tgswGadget keySwitchGadget encode adversary)| ≤
      circularLweAdvantage queryCount ringErrorSampler errorSampler errorSampler
          tgswGadget keySwitchGadget encode adversary +
        LearningWithErrors.advantage
          (jointLweProblem q prefixDimension suffixDimension keySwitchLevels queryCount
            errorSampler errorSampler)
          (jointLweReduction errorSampler errorSampler keySwitchGadget encode adversary) :=
      abs_signedAdvantage_real_le_circularLwe_add_jointLwe queryCount
        ringErrorSampler errorSampler errorSampler tgswGadget keySwitchGadget
        encode adversary hbound
    _ = circularLweAdvantage queryCount ringErrorSampler errorSampler errorSampler
          tgswGadget keySwitchGadget encode adversary +
        LearningWithErrors.advantage
          (Native.KeySwitchSecurity.binaryLweProblem q prefixDimension
            (keySwitchSamples suffixDimension keySwitchLevels + queryCount) errorSampler)
          (FormalProof4FHE.LWE.TwoBlock.reduction
            (jointLweReduction errorSampler errorSampler keySwitchGadget
              encode adversary)) := by
      congr 1
      change LearningWithErrors.advantage
          (FormalProof4FHE.LWE.TwoBlock.problem prefixDimension
            (keySwitchSamples suffixDimension keySwitchLevels) queryCount
            (Native.sampleLweSecret prefixDimension) embedBinarySecret errorSampler)
          (jointLweReduction errorSampler errorSampler keySwitchGadget encode adversary) = _
      simpa [Native.KeySwitchSecurity.binaryLweProblem] using
        (FormalProof4FHE.LWE.TwoBlock.advantage_eq_batch
          prefixDimension (keySwitchSamples suffixDimension keySwitchLevels) queryCount
          (Native.sampleLweSecret prefixDimension) embedBinarySecret errorSampler
          (jointLweReduction errorSampler errorSampler keySwitchGadget encode adversary))

/-- **Reusable-key adaptive security from the literal one-circular game.**  The complete honest
advantage is bounded by the actual `BRK_S(prefix(S))` versus `BRK_S(0)` KDM advantage, the
separate zero-message-BRK versus uniform-BRK encryption term, and one conventional scalar
batch-LWE term.  This statement does not rename the two full master states of a randomizer as
TFHE source and target keys. -/
theorem abs_signedAdvantage_real_le_oneCircularKdm_add_zeroBootstrapLwe_add_batchLwe
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (errorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels)
    (hbound : Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (realGame queryCount ringErrorSampler errorSampler errorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      (oneCircularKdmAdvantage queryCount ringErrorSampler errorSampler errorSampler
          tgswGadget keySwitchGadget encode adversary +
        zeroBootstrapLweAdvantage queryCount ringErrorSampler errorSampler errorSampler
          tgswGadget keySwitchGadget encode adversary) +
        LearningWithErrors.advantage
          (Native.KeySwitchSecurity.binaryLweProblem q prefixDimension
            (keySwitchSamples suffixDimension keySwitchLevels + queryCount) errorSampler)
          (FormalProof4FHE.LWE.TwoBlock.reduction
            (jointLweReduction errorSampler errorSampler keySwitchGadget
              encode adversary)) := by
  calc
    |Encryption.signedAdvantage
        (realGame queryCount ringErrorSampler errorSampler errorSampler
          tgswGadget keySwitchGadget encode adversary)| ≤
      circularLweAdvantage queryCount ringErrorSampler errorSampler errorSampler
          tgswGadget keySwitchGadget encode adversary +
        LearningWithErrors.advantage
          (Native.KeySwitchSecurity.binaryLweProblem q prefixDimension
            (keySwitchSamples suffixDimension keySwitchLevels + queryCount) errorSampler)
          (FormalProof4FHE.LWE.TwoBlock.reduction
            (jointLweReduction errorSampler errorSampler keySwitchGadget
              encode adversary)) :=
      abs_signedAdvantage_real_le_circularLwe_add_batchLwe_of_same_noise
        queryCount ringErrorSampler errorSampler tgswGadget keySwitchGadget
        encode adversary hbound
    _ ≤ _ := add_le_add
      (circularLweAdvantage_le_oneCircularKdm_add_zeroBootstrapLwe
        queryCount ringErrorSampler errorSampler errorSampler tgswGadget
        keySwitchGadget encode adversary)
      le_rfl

/-- Public deterministic ciphertext evaluation preserves the one-cycle CircLWE plus batch-LWE
bound and does not consume additional encryption queries. -/
theorem abs_signedAdvantage_publicEvaluation_le_circularLwe_add_batchLwe
    {Output : Type}
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (errorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (evaluate : CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels →
      TLWE.Ciphertext (ZMod q) prefixDimension → Output)
    (adversary : Adaptive.Adversary Message
      (CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels) Output)
    (hbound : Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (realGame queryCount ringErrorSampler errorSampler errorSampler
        tgswGadget keySwitchGadget encode
        (Adaptive.compilePublicEvaluation evaluate adversary))| ≤
      circularLweAdvantage queryCount ringErrorSampler errorSampler errorSampler
          tgswGadget keySwitchGadget encode
          (Adaptive.compilePublicEvaluation evaluate adversary) +
        LearningWithErrors.advantage
          (Native.KeySwitchSecurity.binaryLweProblem q prefixDimension
            (keySwitchSamples suffixDimension keySwitchLevels + queryCount) errorSampler)
          (FormalProof4FHE.LWE.TwoBlock.reduction
            (jointLweReduction errorSampler errorSampler keySwitchGadget encode
              (Adaptive.compilePublicEvaluation evaluate adversary))) := by
  letI : IsUniformSpec
      ((Message × Message) →ₒ TLWE.Ciphertext (ZMod q) prefixDimension) :=
    IsUniformSpec.ofFintypeInhabited _
  apply abs_signedAdvantage_real_le_circularLwe_add_batchLwe_of_same_noise
  exact Adaptive.compilePublicEvaluation_isQueryBound evaluate adversary queryCount hbound

/-- Public deterministic ciphertext evaluation preserves the literal one-circular KDM bound.
The evaluator is compiled into the public adversary and introduces no new circular edge. -/
theorem abs_signedAdvantage_publicEvaluation_le_oneCircularKdm_add_zeroBootstrapLwe_add_batchLwe
    {Output : Type}
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (errorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (evaluate : CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels →
      TLWE.Ciphertext (ZMod q) prefixDimension → Output)
    (adversary : Adaptive.Adversary Message
      (CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels) Output)
    (hbound : Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (realGame queryCount ringErrorSampler errorSampler errorSampler
        tgswGadget keySwitchGadget encode
        (Adaptive.compilePublicEvaluation evaluate adversary))| ≤
      (oneCircularKdmAdvantage queryCount ringErrorSampler errorSampler errorSampler
          tgswGadget keySwitchGadget encode
          (Adaptive.compilePublicEvaluation evaluate adversary) +
        zeroBootstrapLweAdvantage queryCount ringErrorSampler errorSampler errorSampler
          tgswGadget keySwitchGadget encode
          (Adaptive.compilePublicEvaluation evaluate adversary)) +
        LearningWithErrors.advantage
          (Native.KeySwitchSecurity.binaryLweProblem q prefixDimension
            (keySwitchSamples suffixDimension keySwitchLevels + queryCount) errorSampler)
          (FormalProof4FHE.LWE.TwoBlock.reduction
            (jointLweReduction errorSampler errorSampler keySwitchGadget encode
              (Adaptive.compilePublicEvaluation evaluate adversary))) := by
  letI : IsUniformSpec
      ((Message × Message) →ₒ TLWE.Ciphertext (ZMod q) prefixDimension) :=
    IsUniformSpec.ofFintypeInhabited _
  apply abs_signedAdvantage_real_le_oneCircularKdm_add_zeroBootstrapLwe_add_batchLwe
  exact Adaptive.compilePublicEvaluation_isQueryBound evaluate adversary queryCount hbound

/-- Adversary-class hardness for the exact adaptive one-cycle CircLWE term. -/
def CircularHardAgainst
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (allowed : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels → Prop)
    (bound : ℝ) : Prop :=
  ∀ adversary, allowed adversary →
    circularLweAdvantage queryCount ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget encode adversary ≤ bound

/-- Adversary-class hardness for the literal `BRK_S(prefix(S))` versus `BRK_S(0)` adaptive
one-circular game. -/
def OneCircularKdmHardAgainst
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (allowed : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels → Prop)
    (bound : ℝ) : Prop :=
  ∀ adversary, allowed adversary →
    oneCircularKdmAdvantage queryCount ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget encode adversary ≤ bound

/-- Adversary-class hardness for the non-circular zero-message BRK encryption branch. -/
def ZeroBootstrapLweHardAgainst
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (allowed : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels → Prop)
    (bound : ℝ) : Prop :=
  ∀ adversary, allowed adversary →
    zeroBootstrapLweAdvantage queryCount ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget encode adversary ≤ bound

/-- One-cycle CircLWE hardness and ordinary batch-LWE hardness prove reusable-key adaptive
confidentiality for arbitrary narrow ring noise. -/
theorem hardAgainst_of_circularLwe_and_batchLwe_same_noise
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (errorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (allowed : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels → Prop)
    (batchLweAllowed : LearningWithErrors.Adversary
      (Native.KeySwitchSecurity.binaryLweProblem q prefixDimension
        (keySwitchSamples suffixDimension keySwitchLevels + queryCount) errorSampler) → Prop)
    (circularBound batchLweBound : ℝ)
    (hCircular : CircularHardAgainst queryCount ringErrorSampler errorSampler errorSampler
      tgswGadget keySwitchGadget encode allowed circularBound)
    (hBatchLweClosed : ∀ adversary, allowed adversary →
      batchLweAllowed
        (FormalProof4FHE.LWE.TwoBlock.reduction
          (jointLweReduction errorSampler errorSampler keySwitchGadget encode adversary)))
    (hBatchLwe : FormalProof4FHE.LWE.HardAgainst
      (Native.KeySwitchSecurity.binaryLweProblem q prefixDimension
        (keySwitchSamples suffixDimension keySwitchLevels + queryCount) errorSampler)
      batchLweAllowed batchLweBound) :
    HardAgainst queryCount ringErrorSampler errorSampler errorSampler
      tgswGadget keySwitchGadget encode allowed (circularBound + batchLweBound) := by
  intro adversary hadversary hbound
  exact (abs_signedAdvantage_real_le_circularLwe_add_batchLwe_of_same_noise
    queryCount ringErrorSampler errorSampler tgswGadget keySwitchGadget encode
    adversary hbound).trans
      (add_le_add (hCircular adversary hadversary)
        (hBatchLwe _ (hBatchLweClosed adversary hadversary)))

/-- Literal one-circular KDM hardness, non-circular zero-BRK encryption hardness, and ordinary
batch-LWE hardness prove reusable-key adaptive confidentiality.  This is the finite end-to-end
statement whose sole secret-dependent-message premise is the actual shared-key one-cycle. -/
theorem hardAgainst_of_oneCircularKdm_zeroBootstrapLwe_and_batchLwe_same_noise
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (errorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (allowed : SharedAdversary Message q prefixDimension suffixDimension
      tgswLevels keySwitchLevels → Prop)
    (batchLweAllowed : LearningWithErrors.Adversary
      (Native.KeySwitchSecurity.binaryLweProblem q prefixDimension
        (keySwitchSamples suffixDimension keySwitchLevels + queryCount) errorSampler) → Prop)
    (oneCircularBound zeroBootstrapBound batchLweBound : ℝ)
    (hOneCircular : OneCircularKdmHardAgainst queryCount ringErrorSampler
      errorSampler errorSampler tgswGadget keySwitchGadget encode allowed oneCircularBound)
    (hZeroBootstrap : ZeroBootstrapLweHardAgainst queryCount ringErrorSampler
      errorSampler errorSampler tgswGadget keySwitchGadget encode allowed zeroBootstrapBound)
    (hBatchLweClosed : ∀ adversary, allowed adversary →
      batchLweAllowed
        (FormalProof4FHE.LWE.TwoBlock.reduction
          (jointLweReduction errorSampler errorSampler keySwitchGadget encode adversary)))
    (hBatchLwe : FormalProof4FHE.LWE.HardAgainst
      (Native.KeySwitchSecurity.binaryLweProblem q prefixDimension
        (keySwitchSamples suffixDimension keySwitchLevels + queryCount) errorSampler)
      batchLweAllowed batchLweBound) :
    HardAgainst queryCount ringErrorSampler errorSampler errorSampler
      tgswGadget keySwitchGadget encode allowed
      ((oneCircularBound + zeroBootstrapBound) + batchLweBound) := by
  intro adversary hadversary hbound
  exact
    (abs_signedAdvantage_real_le_oneCircularKdm_add_zeroBootstrapLwe_add_batchLwe
      queryCount ringErrorSampler errorSampler tgswGadget keySwitchGadget
      encode adversary hbound).trans
      (add_le_add
        (add_le_add
          (hOneCircular adversary hadversary)
          (hZeroBootstrap adversary hadversary))
        (hBatchLwe _ (hBatchLweClosed adversary hadversary)))

end

end FormalProof4FHE.TFHE.Encryption.Adaptive.SharedRandomnessOneCycle.CircularSecurity
