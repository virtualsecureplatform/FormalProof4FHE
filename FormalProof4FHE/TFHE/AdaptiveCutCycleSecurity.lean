/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AdaptiveEncryptionSecurity
import FormalProof4FHE.TFHE.CutCycleSecurity

/-!
# Adaptive TFHE Security after Cutting the Evaluation-Key Cycle

This file lifts the native KSK-first cut-cycle decomposition from the one-time experiment to the
query-bounded sequential adaptive TFHE game.  The real cloud key is compared first with a hybrid
whose KSK messages are zero while its real BRK remains visible.  After that intact-cycle hop, the
BRK replacement is reduced to two ordinary binary-secret module-LWE batches.  The all-zero cloud
endpoint is reduced to the existing query-counted scalar joint-LWE problem.

Consequently the full adaptive theorem pays exactly one explicitly named native KSK-first
circular/KDM term.  Every other term is a conventional LWE or module-LWE advantage, and the cloud
key is replaced once for the complete adaptive oracle continuation rather than once per query.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Encryption.Adaptive.CutCycleSecurity

open Native

variable {Message : Type}
  {q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ} [NeZero q]

/-- Restrict the adaptive continuation to the interface used by the post-cut BRK reduction.  The
adaptive encryption experiment never reads the ring secret directly. -/
noncomputable def cutContinuation
    (queryCount : ℕ) (inputErrorSampler : ProbComp (ZMod q))
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    Native.BootstrapCutSecurity.Continuation q degree ringRank tgswLevels
      lweDimension keySwitchLevels :=
  fun lweSecret bootstrapKey keySwitchKey ↦
    Adaptive.continuation queryCount inputErrorSampler encode adversary
      lweSecret (fun _ _ ↦ false) bootstrapKey keySwitchKey

/-- Lifting the restricted post-cut continuation recovers the complete adaptive continuation. -/
theorem lift_cutContinuation
    (queryCount : ℕ) (inputErrorSampler : ProbComp (ZMod q))
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    Native.BootstrapCutSecurity.liftContinuation
        (cutContinuation queryCount inputErrorSampler encode adversary) =
      Adaptive.continuation queryCount inputErrorSampler encode adversary := by
  funext lweSecret ringSecret bootstrapKey keySwitchKey
  rfl

/-- Alternative adaptive hybrid with the real native BRK and a zero-message KSK. -/
noncomputable def keySwitchZeroGame
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ProbComp Bool :=
  Circular.keySwitchZeroContinuationGame
    (Native.nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    (Adaptive.continuation queryCount inputErrorSampler encode adversary)

/-- Adaptive endpoint in which both native evaluation-key directions encrypt zero. -/
noncomputable def zeroCloudGame
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ProbComp Bool :=
  Circular.zeroContinuationGame
    (Native.nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    (Adaptive.continuation queryCount inputErrorSampler encode adversary)

/-- Intact-cycle cost of replacing the KSK before the BRK for the whole adaptive continuation. -/
noncomputable def keySwitchFirstReplacementAdvantage
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ℝ :=
  (Adaptive.realGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget encode adversary).boolDistAdvantage
  (keySwitchZeroGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget encode adversary)

/-- The concrete adaptive first-hop cost is exactly the generic KSK-first native KDM cost. -/
theorem keySwitchFirstReplacementAdvantage_eq_abstract
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    keySwitchFirstReplacementAdvantage queryCount ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget encode adversary =
      Circular.continuationKeySwitchFirstReplacementAdvantage
        (Native.nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        (Adaptive.continuation queryCount inputErrorSampler encode adversary) := by
  rfl

/-- Post-cut adaptive BRK cost after the opposite KSK edge carries zero messages. -/
noncomputable def cutBootstrapReplacementAdvantage
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ℝ :=
  Native.BootstrapCutSecurity.cutBootstrapReplacementAdvantage
    q degree ringRank tgswLevels lweDimension keySwitchLevels
    ringErrorSampler keySwitchErrorSampler tgswGadget
    (cutContinuation queryCount inputErrorSampler encode adversary)

/-- The concrete post-cut adaptive BRK cost is the generic second KSK-first hybrid hop. -/
theorem cutBootstrapReplacementAdvantage_eq_abstract
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    cutBootstrapReplacementAdvantage queryCount ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget encode adversary =
      Circular.continuationBootstrapAfterKeySwitchReplacementAdvantage
        (Native.nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        (Adaptive.continuation queryCount inputErrorSampler encode adversary) := by
  rw [← lift_cutContinuation queryCount inputErrorSampler encode adversary]
  exact
    Native.BootstrapCutSecurity.cutBootstrapReplacementAdvantage_eq_continuationBootstrapAfterKeySwitch
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
      (cutContinuation queryCount inputErrorSampler encode adversary)

/-! ## Ordinary post-cut reductions -/

/-- After cutting the KSK edge, the complete adaptive BRK hop reduces to two ordinary parallel
binary-secret module-LWE advantages. -/
theorem cutBootstrapReplacementAdvantage_le_two_parallelModuleLwe
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    cutBootstrapReplacementAdvantage queryCount ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget encode adversary ≤
      LearningWithErrors.advantage
        (Native.BootstrapCutSecurity.parallelModuleLweProblem q degree ringRank tgswLevels
          lweDimension ringErrorSampler)
        (Native.BootstrapCutSecurity.realMessageReduction ringErrorSampler
          keySwitchErrorSampler tgswGadget
          (cutContinuation queryCount inputErrorSampler encode adversary)) +
      LearningWithErrors.advantage
        (Native.BootstrapCutSecurity.parallelModuleLweProblem q degree ringRank tgswLevels
          lweDimension ringErrorSampler)
        (Native.BootstrapCutSecurity.zeroMessageReduction ringErrorSampler
          keySwitchErrorSampler
          (cutContinuation queryCount inputErrorSampler encode adversary)) := by
  exact Native.BootstrapCutSecurity.cutBootstrapReplacementAdvantage_le_two_parallelModuleLwe
    ringErrorSampler keySwitchErrorSampler tgswGadget
    (cutContinuation queryCount inputErrorSampler encode adversary)

/-- Conventional flattened-batch form of the adaptive post-cut BRK reduction. -/
theorem cutBootstrapReplacementAdvantage_le_two_batchModuleLwe
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    cutBootstrapReplacementAdvantage queryCount ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget encode adversary ≤
      LearningWithErrors.advantage
        (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
          lweDimension ringErrorSampler)
        (Native.BootstrapCutSecurity.realBatchReduction ringErrorSampler
          keySwitchErrorSampler tgswGadget
          (cutContinuation queryCount inputErrorSampler encode adversary)) +
      LearningWithErrors.advantage
        (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
          lweDimension ringErrorSampler)
        (Native.BootstrapCutSecurity.zeroBatchReduction ringErrorSampler
          keySwitchErrorSampler
          (cutContinuation queryCount inputErrorSampler encode adversary)) := by
  exact Native.BootstrapCutSecurity.cutBootstrapReplacementAdvantage_le_two_batchModuleLwe
    ringErrorSampler keySwitchErrorSampler tgswGadget
    (cutContinuation queryCount inputErrorSampler encode adversary)

/-! ## All-zero cloud endpoint -/

/-- The adaptive all-zero native cloud endpoint is the arbitrary-KSK-message game instantiated
with the zero message vector. -/
theorem zeroCloudGame_eq_keySwitchMessageGame_zero
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    zeroCloudGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary =
      Adaptive.keySwitchMessageGame queryCount ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget (fun _ ↦ 0) encode adversary := by
  simp [zeroCloudGame, Circular.zeroContinuationGame, Native.nativeCycleSpec,
    Adaptive.keySwitchMessageGame, Adaptive.continuation,
    Native.generateZeroKeySwitchKey]

/-- Translating the adaptive KSK block by zero is the unshifted zero-cloud reduction. -/
theorem keySwitchMessageReduction_zero_eq_zeroCloud
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    Adaptive.keySwitchMessageReduction (queryCount := queryCount)
        ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget (fun _ ↦ 0) encode adversary =
      Adaptive.zeroCloudReduction (queryCount := queryCount)
        ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget encode adversary := by
  funext transcript
  simp [Adaptive.keySwitchMessageReduction, Adaptive.zeroCloudReduction,
    Adaptive.transcriptGame, Encryption.Security.shiftFirstBlock,
    MultiQuery.keySwitchTranscript, MultiQuery.inputTranscript,
    FormalProof4FHE.LWE.TwoBlock.toTranscriptPair, monad_norm]

/-- The all-zero adaptive cloud endpoint is exactly the real branch of the unshifted joint-LWE
reduction. -/
theorem zeroCloudGame_evalDist_eq_jointLwe_game0
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    evalDist (zeroCloudGame queryCount ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget encode adversary) =
      evalDist (LearningWithErrors.game0
        (Adaptive.jointLweProblem q lweDimension
          (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
          keySwitchErrorSampler inputErrorSampler)
        (Adaptive.zeroCloudReduction ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget encode adversary)) := by
  rw [zeroCloudGame_eq_keySwitchMessageGame_zero,
    ← keySwitchMessageReduction_zero_eq_zeroCloud queryCount ringErrorSampler
      keySwitchErrorSampler inputErrorSampler tgswGadget encode adversary]
  exact Adaptive.keySwitchMessageGame_evalDist_eq_game0 queryCount
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget
    (fun _ ↦ 0) encode adversary

/-- The all-zero adaptive cloud endpoint has exactly the advantage of the unshifted query-counted
joint-LWE reduction. -/
theorem abs_signedAdvantage_zeroCloud_eq_jointLwe
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (hbound : Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (zeroCloudGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| =
      LearningWithErrors.advantage
        (Adaptive.jointLweProblem q lweDimension
          (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
          keySwitchErrorSampler inputErrorSampler)
        (Adaptive.zeroCloudReduction ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget encode adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold Encryption.signedAdvantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (zeroCloudGame_evalDist_eq_jointLwe_game0 queryCount ringErrorSampler
        keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary)
      true,
    Adaptive.jointLwe_game1_probOutput_true queryCount ringErrorSampler
      keySwitchErrorSampler inputErrorSampler tgswGadget encode adversary hbound]
  norm_num

/-! ## The opposite post-cut edge and first-hop equivalence -/

/-- Adaptive cost of replacing the KSK after the BRK messages have already been zeroed. -/
noncomputable def keySwitchReplacementAdvantage
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ℝ :=
  (Adaptive.bootstrapZeroGame queryCount ringErrorSampler keySwitchErrorSampler
    inputErrorSampler tgswGadget keySwitchGadget encode adversary).boolDistAdvantage
  (zeroCloudGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget encode adversary)

/-- The concrete adaptive opposite post-cut edge is exactly the generic continuation edge. -/
theorem keySwitchReplacementAdvantage_eq_abstract
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    keySwitchReplacementAdvantage queryCount ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget encode adversary =
      Circular.continuationKeySwitchReplacementAdvantage
        (Native.nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        (Adaptive.continuation queryCount inputErrorSampler encode adversary) := by
  rfl

/-- The adaptive KSK-after-zero-BRK edge costs at most two shared-secret joint-LWE advantages:
one reduction carries the native KSK messages and the other carries zero messages. -/
theorem keySwitchReplacementAdvantage_le_two_jointLwe
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    keySwitchReplacementAdvantage queryCount ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget encode adversary ≤
      LearningWithErrors.advantage
        (Adaptive.jointLweProblem q lweDimension
          (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
          keySwitchErrorSampler inputErrorSampler)
        (Adaptive.keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget
          (Adaptive.nativeKeySwitchMessage keySwitchGadget) encode adversary) +
      LearningWithErrors.advantage
        (Adaptive.jointLweProblem q lweDimension
          (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
          keySwitchErrorSampler inputErrorSampler)
        (Adaptive.zeroCloudReduction ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget encode adversary) := by
  rw [FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage,
    FormalProof4FHE.LWE.advantage_eq_boolDistAdvantage]
  unfold keySwitchReplacementAdvantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
      (Adaptive.bootstrapZeroGame_evalDist_eq_jointLwe_game0 queryCount ringErrorSampler
        keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary)
      true,
    evalDist_ext_iff.mp
      (zeroCloudGame_evalDist_eq_jointLwe_game0 queryCount ringErrorSampler
        keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary)
      true]
  let realProbability : ℝ := (Pr[= true | LearningWithErrors.game0
    (Adaptive.jointLweProblem q lweDimension
      (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
      keySwitchErrorSampler inputErrorSampler)
    (Adaptive.keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget
      (Adaptive.nativeKeySwitchMessage keySwitchGadget) encode adversary)]).toReal
  let uniformRealProbability : ℝ := (Pr[= true | LearningWithErrors.game1
    (Adaptive.jointLweProblem q lweDimension
      (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
      keySwitchErrorSampler inputErrorSampler)
    (Adaptive.keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget
      (Adaptive.nativeKeySwitchMessage keySwitchGadget) encode adversary)]).toReal
  let uniformZeroProbability : ℝ := (Pr[= true | LearningWithErrors.game1
    (Adaptive.jointLweProblem q lweDimension
      (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
      keySwitchErrorSampler inputErrorSampler)
    (Adaptive.zeroCloudReduction ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget encode adversary)]).toReal
  let zeroProbability : ℝ := (Pr[= true | LearningWithErrors.game0
    (Adaptive.jointLweProblem q lweDimension
      (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
      keySwitchErrorSampler inputErrorSampler)
    (Adaptive.zeroCloudReduction ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget encode adversary)]).toReal
  have hUniform : uniformRealProbability = uniformZeroProbability := by
    exact congrArg ENNReal.toReal (evalDist_ext_iff.mp
      (Adaptive.keySwitchMessageReduction_game1_evalDist_eq_zeroCloud
        ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget
        (Adaptive.nativeKeySwitchMessage keySwitchGadget) encode adversary) true)
  change |realProbability - zeroProbability| ≤
    |realProbability - uniformRealProbability| +
      |zeroProbability - uniformZeroProbability|
  rw [hUniform, abs_sub_comm zeroProbability uniformZeroProbability]
  exact abs_sub_le realProbability uniformZeroProbability zeroProbability

/-- The BRK-first intact-cycle cost is at most the KSK-first cost plus both opposite post-cut
edges for the complete adaptive continuation. -/
theorem bootstrapReplacementAdvantage_le_keySwitchFirst_add_postCuts
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    Adaptive.bootstrapReplacementAdvantage queryCount ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget encode adversary ≤
      keySwitchFirstReplacementAdvantage queryCount ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget encode adversary +
        cutBootstrapReplacementAdvantage queryCount ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget encode adversary +
        keySwitchReplacementAdvantage queryCount ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget encode adversary := by
  have h := Circular.continuationBootstrapReplacementAdvantage_le_keySwitchFirst_add_postCuts
    (Native.nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    (Adaptive.continuation queryCount inputErrorSampler encode adversary)
  rw [← keySwitchFirstReplacementAdvantage_eq_abstract queryCount ringErrorSampler
    keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary,
    ← cutBootstrapReplacementAdvantage_eq_abstract queryCount ringErrorSampler
      keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary,
    ← keySwitchReplacementAdvantage_eq_abstract queryCount ringErrorSampler
      keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary] at h
  simpa [Adaptive.bootstrapReplacementAdvantage,
    Circular.continuationBootstrapReplacementAdvantage,
    Adaptive.realGame, Adaptive.bootstrapZeroGame] using h

/-- Conversely, the KSK-first intact-cycle cost is at most the BRK-first cost plus the same two
post-cut edges for the complete adaptive continuation. -/
theorem keySwitchFirstReplacementAdvantage_le_bootstrapFirst_add_postCuts
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    keySwitchFirstReplacementAdvantage queryCount ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget encode adversary ≤
      Adaptive.bootstrapReplacementAdvantage queryCount ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget encode adversary +
        keySwitchReplacementAdvantage queryCount ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget encode adversary +
        cutBootstrapReplacementAdvantage queryCount ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget encode adversary := by
  have h :=
    Circular.continuationKeySwitchFirstReplacementAdvantage_le_bootstrapFirst_add_postCuts
      (Native.nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
      (Adaptive.continuation queryCount inputErrorSampler encode adversary)
  rw [← keySwitchFirstReplacementAdvantage_eq_abstract queryCount ringErrorSampler
    keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary,
    ← keySwitchReplacementAdvantage_eq_abstract queryCount ringErrorSampler
      keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary,
    ← cutBootstrapReplacementAdvantage_eq_abstract queryCount ringErrorSampler
      keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary] at h
  simpa [Adaptive.bootstrapReplacementAdvantage,
    Circular.continuationBootstrapReplacementAdvantage,
    Adaptive.realGame, Adaptive.bootstrapZeroGame] using h

/-- For the full adaptive continuation, the KSK-first intact-cycle assumption follows from the
BRK-first direct-bilinear assumption up to two ordinary ring batches and two query-counted
joint-LWE reductions. -/
theorem keySwitchFirstReplacementAdvantage_le_directBilinear_add_postCutLwe
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    keySwitchFirstReplacementAdvantage queryCount ringErrorSampler keySwitchErrorSampler
        inputErrorSampler tgswGadget keySwitchGadget encode adversary ≤
      Native.BootstrapSecurity.directBilinearAdvantage ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget
          (Adaptive.continuation queryCount inputErrorSampler encode adversary) +
        LearningWithErrors.advantage
          (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
            lweDimension ringErrorSampler)
          (Native.BootstrapCutSecurity.realBatchReduction ringErrorSampler
            keySwitchErrorSampler tgswGadget
            (cutContinuation queryCount inputErrorSampler encode adversary)) +
        LearningWithErrors.advantage
          (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
            lweDimension ringErrorSampler)
          (Native.BootstrapCutSecurity.zeroBatchReduction ringErrorSampler
            keySwitchErrorSampler
            (cutContinuation queryCount inputErrorSampler encode adversary)) +
        LearningWithErrors.advantage
          (Adaptive.jointLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
            keySwitchErrorSampler inputErrorSampler)
          (Adaptive.keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler
            inputErrorSampler tgswGadget
            (Adaptive.nativeKeySwitchMessage keySwitchGadget) encode adversary) +
        LearningWithErrors.advantage
          (Adaptive.jointLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
            keySwitchErrorSampler inputErrorSampler)
          (Adaptive.zeroCloudReduction ringErrorSampler keySwitchErrorSampler
            inputErrorSampler tgswGadget encode adversary) := by
  have hRelation := keySwitchFirstReplacementAdvantage_le_bootstrapFirst_add_postCuts
    queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget
    keySwitchGadget encode adversary
  have hCut := cutBootstrapReplacementAdvantage_le_two_batchModuleLwe queryCount
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget encode adversary
  have hKeySwitch := keySwitchReplacementAdvantage_le_two_jointLwe queryCount
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
    encode adversary
  rw [Adaptive.bootstrapReplacementAdvantage_eq_directBilinear queryCount ringErrorSampler
    keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary]
    at hRelation
  linarith

/-- Conversely, the BRK-first direct-bilinear adaptive assumption follows from the KSK-first
intact-cycle assumption up to exactly the same checked ring and scalar LWE terms. -/
theorem directBilinearAdvantage_le_keySwitchFirst_add_postCutLwe
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    Native.BootstrapSecurity.directBilinearAdvantage ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget
        (Adaptive.continuation queryCount inputErrorSampler encode adversary) ≤
      keySwitchFirstReplacementAdvantage queryCount ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget encode adversary +
        LearningWithErrors.advantage
          (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
            lweDimension ringErrorSampler)
          (Native.BootstrapCutSecurity.realBatchReduction ringErrorSampler
            keySwitchErrorSampler tgswGadget
            (cutContinuation queryCount inputErrorSampler encode adversary)) +
        LearningWithErrors.advantage
          (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
            lweDimension ringErrorSampler)
          (Native.BootstrapCutSecurity.zeroBatchReduction ringErrorSampler
            keySwitchErrorSampler
            (cutContinuation queryCount inputErrorSampler encode adversary)) +
        LearningWithErrors.advantage
          (Adaptive.jointLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
            keySwitchErrorSampler inputErrorSampler)
          (Adaptive.keySwitchMessageReduction ringErrorSampler keySwitchErrorSampler
            inputErrorSampler tgswGadget
            (Adaptive.nativeKeySwitchMessage keySwitchGadget) encode adversary) +
        LearningWithErrors.advantage
          (Adaptive.jointLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
            keySwitchErrorSampler inputErrorSampler)
          (Adaptive.zeroCloudReduction ringErrorSampler keySwitchErrorSampler
            inputErrorSampler tgswGadget encode adversary) := by
  have hRelation := bootstrapReplacementAdvantage_le_keySwitchFirst_add_postCuts
    queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget
    keySwitchGadget encode adversary
  have hCut := cutBootstrapReplacementAdvantage_le_two_batchModuleLwe queryCount
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget encode adversary
  have hKeySwitch := keySwitchReplacementAdvantage_le_two_jointLwe queryCount
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
    encode adversary
  rw [Adaptive.bootstrapReplacementAdvantage_eq_directBilinear queryCount ringErrorSampler
    keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary]
    at hRelation
  linarith

/-! ## Complete adaptive cut-cycle theorem -/

/-- Contextual cost of replacing the complete native cloud key for the full adaptive
continuation. -/
noncomputable def circularAdvantage
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ℝ :=
  (Adaptive.realGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget encode adversary).boolDistAdvantage
  (zeroCloudGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget encode adversary)

/-- In KSK-first order, the adaptive circular cost is one intact-cycle hop followed by the
ordinary post-cut BRK hop. -/
theorem circularAdvantage_le_keySwitchFirst_add_cutBootstrap
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    circularAdvantage queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary ≤
      keySwitchFirstReplacementAdvantage queryCount ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget encode adversary +
        cutBootstrapReplacementAdvantage queryCount ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget encode adversary := by
  have h := Circular.continuationCircularAdvantage_le_keySwitchFirst_add_bootstrapAfter
    (Native.nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    (Adaptive.continuation queryCount inputErrorSampler encode adversary)
  rw [← keySwitchFirstReplacementAdvantage_eq_abstract queryCount ringErrorSampler
    keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary,
    ← cutBootstrapReplacementAdvantage_eq_abstract queryCount ringErrorSampler
      keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary] at h
  simpa [circularAdvantage, Circular.continuationCircularAdvantage,
    Adaptive.realGame, zeroCloudGame] using h

/-- Replacing the complete cloud once and then analyzing the all-zero cloud bounds the honest
adaptive signed advantage. -/
theorem abs_signedAdvantage_real_le_circular_add_zero
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    |Encryption.signedAdvantage
      (Adaptive.realGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      circularAdvantage queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget encode adversary +
        |Encryption.signedAdvantage
          (zeroCloudGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
            tgswGadget keySwitchGadget encode adversary)| := by
  unfold Encryption.signedAdvantage circularAdvantage ProbComp.boolDistAdvantage
  exact abs_sub_le
    (Pr[= true | Adaptive.realGame queryCount ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget encode adversary]).toReal
    (Pr[= true | zeroCloudGame queryCount ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget encode adversary]).toReal
    (1 / 2 : ℝ)

/-- **Alternative-order adaptive native TFHE security theorem.** The complete adaptive honest
advantage is bounded by one explicitly named intact-cycle KSK-first term, two ordinary post-cut
parallel module-LWE terms, and one query-counted joint-LWE term. -/
theorem abs_signedAdvantage_real_le_keySwitchFirst_add_two_parallelModuleLwe_add_jointLwe
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (hbound : Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (Adaptive.realGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      keySwitchFirstReplacementAdvantage queryCount ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget encode adversary +
        LearningWithErrors.advantage
          (Native.BootstrapCutSecurity.parallelModuleLweProblem q degree ringRank tgswLevels
            lweDimension ringErrorSampler)
          (Native.BootstrapCutSecurity.realMessageReduction ringErrorSampler
            keySwitchErrorSampler tgswGadget
            (cutContinuation queryCount inputErrorSampler encode adversary)) +
        LearningWithErrors.advantage
          (Native.BootstrapCutSecurity.parallelModuleLweProblem q degree ringRank tgswLevels
            lweDimension ringErrorSampler)
          (Native.BootstrapCutSecurity.zeroMessageReduction ringErrorSampler
            keySwitchErrorSampler
            (cutContinuation queryCount inputErrorSampler encode adversary)) +
        LearningWithErrors.advantage
          (Adaptive.jointLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
            keySwitchErrorSampler inputErrorSampler)
          (Adaptive.zeroCloudReduction ringErrorSampler keySwitchErrorSampler
            inputErrorSampler tgswGadget encode adversary) := by
  have hOuter := abs_signedAdvantage_real_le_circular_add_zero queryCount
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
    encode adversary
  have hCircular := circularAdvantage_le_keySwitchFirst_add_cutBootstrap queryCount
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
    encode adversary
  have hCut := cutBootstrapReplacementAdvantage_le_two_parallelModuleLwe queryCount
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget encode adversary
  have hZero := abs_signedAdvantage_zeroCloud_eq_jointLwe queryCount ringErrorSampler
    keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode adversary hbound
  rw [hZero] at hOuter
  linarith

/-- Conventional flattened-batch form of the complete adaptive alternative-order theorem. -/
theorem abs_signedAdvantage_real_le_keySwitchFirst_add_two_batchModuleLwe_add_jointLwe
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (hbound : Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (Adaptive.realGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      keySwitchFirstReplacementAdvantage queryCount ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget keySwitchGadget encode adversary +
        LearningWithErrors.advantage
          (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
            lweDimension ringErrorSampler)
          (Native.BootstrapCutSecurity.realBatchReduction ringErrorSampler
            keySwitchErrorSampler tgswGadget
            (cutContinuation queryCount inputErrorSampler encode adversary)) +
        LearningWithErrors.advantage
          (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
            lweDimension ringErrorSampler)
          (Native.BootstrapCutSecurity.zeroBatchReduction ringErrorSampler
            keySwitchErrorSampler
            (cutContinuation queryCount inputErrorSampler encode adversary)) +
        LearningWithErrors.advantage
          (Adaptive.jointLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
            keySwitchErrorSampler inputErrorSampler)
          (Adaptive.zeroCloudReduction ringErrorSampler keySwitchErrorSampler
            inputErrorSampler tgswGadget encode adversary) := by
  have h := abs_signedAdvantage_real_le_keySwitchFirst_add_two_parallelModuleLwe_add_jointLwe
    queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget
    keySwitchGadget encode adversary hbound
  rw [Native.BootstrapCutSecurity.realMessageReduction_advantage_eq_batch,
    Native.BootstrapCutSecurity.zeroMessageReduction_advantage_eq_batch] at h
  exact h

/-- Equal-noise specialization: all three non-circular terms are standard binary-secret batch
LWE instances, with the scalar batch containing all KSK rows and all adaptive input rows. -/
theorem
    abs_signedAdvantage_real_le_keySwitchFirst_add_two_batchModuleLwe_add_batchLwe_of_same_noise
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (errorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels)
    (hbound : Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (Adaptive.realGame queryCount ringErrorSampler errorSampler errorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      keySwitchFirstReplacementAdvantage queryCount ringErrorSampler errorSampler errorSampler
          tgswGadget keySwitchGadget encode adversary +
        LearningWithErrors.advantage
          (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
            lweDimension ringErrorSampler)
          (Native.BootstrapCutSecurity.realBatchReduction ringErrorSampler
            errorSampler tgswGadget
            (cutContinuation queryCount errorSampler encode adversary)) +
        LearningWithErrors.advantage
          (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
            lweDimension ringErrorSampler)
          (Native.BootstrapCutSecurity.zeroBatchReduction ringErrorSampler
            errorSampler (cutContinuation queryCount errorSampler encode adversary)) +
        LearningWithErrors.advantage
          (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels + queryCount)
            errorSampler)
          (FormalProof4FHE.LWE.TwoBlock.reduction
            (Adaptive.zeroCloudReduction ringErrorSampler errorSampler errorSampler
              tgswGadget encode adversary)) := by
  have h := abs_signedAdvantage_real_le_keySwitchFirst_add_two_batchModuleLwe_add_jointLwe
    queryCount ringErrorSampler errorSampler errorSampler tgswGadget keySwitchGadget
    encode adversary hbound
  have hBatch := FormalProof4FHE.LWE.TwoBlock.advantage_eq_batch
    lweDimension (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels)
    queryCount (Native.sampleLweSecret lweDimension) embedBinarySecret errorSampler
    (Adaptive.zeroCloudReduction ringErrorSampler errorSampler errorSampler
      tgswGadget encode adversary)
  change |Encryption.signedAdvantage
      (Adaptive.realGame queryCount ringErrorSampler errorSampler errorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
    keySwitchFirstReplacementAdvantage queryCount ringErrorSampler errorSampler errorSampler
        tgswGadget keySwitchGadget encode adversary +
      LearningWithErrors.advantage
        (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
          lweDimension ringErrorSampler)
        (Native.BootstrapCutSecurity.realBatchReduction ringErrorSampler errorSampler
          tgswGadget (cutContinuation queryCount errorSampler encode adversary)) +
      LearningWithErrors.advantage
        (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
          lweDimension ringErrorSampler)
        (Native.BootstrapCutSecurity.zeroBatchReduction ringErrorSampler errorSampler
          (cutContinuation queryCount errorSampler encode adversary)) +
      LearningWithErrors.advantage
        (FormalProof4FHE.LWE.TwoBlock.problem lweDimension
          (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
          (Native.sampleLweSecret lweDimension) embedBinarySecret errorSampler)
        (Adaptive.zeroCloudReduction ringErrorSampler errorSampler errorSampler
          tgswGadget encode adversary) at h
  rw [hBatch] at h
  simpa [Native.KeySwitchSecurity.binaryLweProblem] using h

/-! ## Adversary-class interface -/

/-- The exact scheme-specific circular/KDM premise left by the adaptive native proof.  It pays
once for replacing all KSK messages while the real structured BRK and the complete adaptive
continuation remain visible. -/
def NativeIntactCycleKDMHardAgainst
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (allowed : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels → Prop)
    (bound : ℝ) : Prop :=
  ∀ adversary, allowed adversary →
    keySwitchFirstReplacementAdvantage queryCount ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget encode adversary ≤ bound

/-- A generic native KSK-first continuation assumption implies the exact adaptive specialization
whenever the chosen adversary class is closed under the continuation reduction. -/
theorem nativeIntactCycleKDMHardAgainst_of_continuation
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (allowed : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels → Prop)
    (continuationAllowed : Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (Native.KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) → Prop)
    (bound : ℝ)
    (hClosed : ∀ adversary, allowed adversary →
      continuationAllowed (Adaptive.continuation queryCount inputErrorSampler encode adversary))
    (hCircular : Circular.KeySwitchFirstHardAgainst
      (Native.nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
      continuationAllowed bound) :
    NativeIntactCycleKDMHardAgainst queryCount ringErrorSampler keySwitchErrorSampler
      inputErrorSampler tgswGadget keySwitchGadget encode allowed bound := by
  intro adversary hadversary
  rw [keySwitchFirstReplacementAdvantage_eq_abstract]
  exact hCircular _ (hClosed adversary hadversary)

/-- **Conditional adaptive TFHE security after cutting the cycle.** Native intact-cycle KDM,
two conventional binary-secret ring batch-LWE assumptions, and the exact query-counted
zero-cloud joint-LWE assumption imply security of the full sequential adaptive game. -/
theorem hardAgainst_of_nativeIntactCycleKDM_and_batchLwe
    (queryCount : ℕ)
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (allowed : Adaptive.NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels → Prop)
    (realBatchAllowed zeroBatchAllowed : LearningWithErrors.Adversary
      (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
        lweDimension ringErrorSampler) → Prop)
    (jointLweAllowed : LearningWithErrors.Adversary
      (Adaptive.jointLweProblem q lweDimension
        (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
        keySwitchErrorSampler inputErrorSampler) → Prop)
    (intactCycleBound realBatchBound zeroBatchBound jointLweBound : ℝ)
    (hRealBatchClosed : ∀ adversary, allowed adversary →
      realBatchAllowed
        (Native.BootstrapCutSecurity.realBatchReduction ringErrorSampler
          keySwitchErrorSampler tgswGadget
          (cutContinuation queryCount inputErrorSampler encode adversary)))
    (hZeroBatchClosed : ∀ adversary, allowed adversary →
      zeroBatchAllowed
        (Native.BootstrapCutSecurity.zeroBatchReduction ringErrorSampler
          keySwitchErrorSampler
          (cutContinuation queryCount inputErrorSampler encode adversary)))
    (hJointLweClosed : ∀ adversary, allowed adversary →
      jointLweAllowed
        (Adaptive.zeroCloudReduction ringErrorSampler keySwitchErrorSampler
          inputErrorSampler tgswGadget encode adversary))
    (hIntactCycle : NativeIntactCycleKDMHardAgainst queryCount ringErrorSampler
      keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget encode allowed
      intactCycleBound)
    (hRealBatch : FormalProof4FHE.LWE.HardAgainst
      (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
        lweDimension ringErrorSampler) realBatchAllowed realBatchBound)
    (hZeroBatch : FormalProof4FHE.LWE.HardAgainst
      (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
        lweDimension ringErrorSampler) zeroBatchAllowed zeroBatchBound)
    (hJointLwe : FormalProof4FHE.LWE.HardAgainst
      (Adaptive.jointLweProblem q lweDimension
        (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
        keySwitchErrorSampler inputErrorSampler) jointLweAllowed jointLweBound) :
    Adaptive.HardAgainst queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget encode allowed
      (intactCycleBound + realBatchBound + zeroBatchBound + jointLweBound) := by
  intro adversary hadversary hbound
  calc
    |Encryption.signedAdvantage
        (Adaptive.realGame queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget encode adversary)| ≤
        keySwitchFirstReplacementAdvantage queryCount ringErrorSampler keySwitchErrorSampler
            inputErrorSampler tgswGadget keySwitchGadget encode adversary +
          LearningWithErrors.advantage
            (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
              lweDimension ringErrorSampler)
            (Native.BootstrapCutSecurity.realBatchReduction ringErrorSampler
              keySwitchErrorSampler tgswGadget
              (cutContinuation queryCount inputErrorSampler encode adversary)) +
          LearningWithErrors.advantage
            (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
              lweDimension ringErrorSampler)
            (Native.BootstrapCutSecurity.zeroBatchReduction ringErrorSampler
              keySwitchErrorSampler
              (cutContinuation queryCount inputErrorSampler encode adversary)) +
          LearningWithErrors.advantage
            (Adaptive.jointLweProblem q lweDimension
              (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
              keySwitchErrorSampler inputErrorSampler)
            (Adaptive.zeroCloudReduction ringErrorSampler keySwitchErrorSampler
              inputErrorSampler tgswGadget encode adversary) :=
      abs_signedAdvantage_real_le_keySwitchFirst_add_two_batchModuleLwe_add_jointLwe
        queryCount ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget
        keySwitchGadget encode adversary hbound
    _ ≤ intactCycleBound + realBatchBound + zeroBatchBound + jointLweBound :=
      add_le_add
        (add_le_add
          (add_le_add (hIntactCycle adversary hadversary)
            (hRealBatch _ (hRealBatchClosed adversary hadversary)))
          (hZeroBatch _ (hZeroBatchClosed adversary hadversary)))
        (hJointLwe _ (hJointLweClosed adversary hadversary))

end FormalProof4FHE.TFHE.Encryption.Adaptive.CutCycleSecurity
