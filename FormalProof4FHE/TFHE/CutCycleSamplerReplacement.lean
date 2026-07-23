/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.AdaptiveCutCycleSecurity
import FormalProof4FHE.TFHE.SamplerReplacement

/-!
# Finite Sampler Replacement for the Adaptive TFHE Cut-Cycle Proof

The exact KSK-first native proof is stated for a reference sampler triple.  This file transfers
it to an arbitrary implementation triple by paying the already-checked whole-execution total
variation cost for every BRK, KSK, and adaptive-input error draw.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.SamplerReplacement.CutCycleSecurity

/-- **Finite implementation-level KSK-first TFHE bound.** The honest implementation advantage
is at most the four reference cut-cycle terms plus the exact complete sampler-replacement cost. -/
theorem
    abs_signedAdvantage_implementation_le_keySwitchFirst_add_two_batchModuleLwe_add_jointLwe_add_replacement
    {Message : Type}
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ) [NeZero q]
    (ringImplementation ringReference : ProbComp (RLWE.Rq q degree))
    (keySwitchImplementation keySwitchReference inputImplementation inputReference :
      ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.Adaptive.NativeAdversary Message q degree ringRank
      tgswLevels lweDimension keySwitchLevels)
    (hbound : Encryption.Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (Encryption.Adaptive.realGame queryCount ringImplementation keySwitchImplementation
        inputImplementation tgswGadget keySwitchGadget encode adversary)| ≤
      Encryption.Adaptive.CutCycleSecurity.keySwitchFirstReplacementAdvantage queryCount
          ringReference keySwitchReference inputReference tgswGadget keySwitchGadget
          encode adversary +
        LearningWithErrors.advantage
          (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
            lweDimension ringReference)
          (Native.BootstrapCutSecurity.realBatchReduction ringReference keySwitchReference
            tgswGadget
            (Encryption.Adaptive.CutCycleSecurity.cutContinuation queryCount inputReference
              encode adversary)) +
        LearningWithErrors.advantage
          (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
            lweDimension ringReference)
          (Native.BootstrapCutSecurity.zeroBatchReduction ringReference keySwitchReference
            (Encryption.Adaptive.CutCycleSecurity.cutContinuation queryCount inputReference
              encode adversary)) +
        LearningWithErrors.advantage
          (Encryption.Adaptive.jointLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
            keySwitchReference inputReference)
          (Encryption.Adaptive.zeroCloudReduction ringReference keySwitchReference
            inputReference tgswGadget encode adversary) +
        adaptiveReplacementCost q degree ringRank tgswLevels lweDimension keySwitchLevels
          queryCount ringImplementation ringReference keySwitchImplementation
          keySwitchReference inputImplementation inputReference := by
  calc
    |Encryption.signedAdvantage
      (Encryption.Adaptive.realGame queryCount ringImplementation keySwitchImplementation
        inputImplementation tgswGadget keySwitchGadget encode adversary)| ≤
      |Encryption.signedAdvantage
        (Encryption.Adaptive.realGame queryCount ringReference keySwitchReference
          inputReference tgswGadget keySwitchGadget encode adversary)| +
        adaptiveReplacementCost q degree ringRank tgswLevels lweDimension keySwitchLevels
          queryCount ringImplementation ringReference keySwitchImplementation
          keySwitchReference inputImplementation inputReference :=
      abs_signedAdvantage_adaptiveReal_le_reference_add q degree ringRank tgswLevels
        lweDimension keySwitchLevels queryCount ringImplementation ringReference
        keySwitchImplementation keySwitchReference inputImplementation inputReference
        tgswGadget keySwitchGadget encode adversary
    _ ≤
      (Encryption.Adaptive.CutCycleSecurity.keySwitchFirstReplacementAdvantage queryCount
          ringReference keySwitchReference inputReference tgswGadget keySwitchGadget
          encode adversary +
        LearningWithErrors.advantage
          (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
            lweDimension ringReference)
          (Native.BootstrapCutSecurity.realBatchReduction ringReference keySwitchReference
            tgswGadget
            (Encryption.Adaptive.CutCycleSecurity.cutContinuation queryCount inputReference
              encode adversary)) +
        LearningWithErrors.advantage
          (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
            lweDimension ringReference)
          (Native.BootstrapCutSecurity.zeroBatchReduction ringReference keySwitchReference
            (Encryption.Adaptive.CutCycleSecurity.cutContinuation queryCount inputReference
              encode adversary)) +
        LearningWithErrors.advantage
          (Encryption.Adaptive.jointLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels) queryCount
            keySwitchReference inputReference)
          (Encryption.Adaptive.zeroCloudReduction ringReference keySwitchReference
            inputReference tgswGadget encode adversary)) +
        adaptiveReplacementCost q degree ringRank tgswLevels lweDimension keySwitchLevels
          queryCount ringImplementation ringReference keySwitchImplementation
          keySwitchReference inputImplementation inputReference :=
      add_le_add
        (Encryption.Adaptive.CutCycleSecurity.abs_signedAdvantage_real_le_keySwitchFirst_add_two_batchModuleLwe_add_jointLwe
          queryCount ringReference keySwitchReference inputReference tgswGadget
          keySwitchGadget encode adversary hbound)
        le_rfl

/-- Equal reference scalar noises make all three non-circular reference terms ordinary
binary-secret batch-LWE advantages; implementation scalar samplers may remain distinct. -/
theorem
    abs_signedAdvantage_implementation_le_keySwitchFirst_add_three_batchLwe_add_replacement
    {Message : Type}
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ) [NeZero q]
    (ringImplementation ringReference : ProbComp (RLWE.Rq q degree))
    (keySwitchImplementation inputImplementation errorReference : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.Adaptive.NativeAdversary Message q degree ringRank
      tgswLevels lweDimension keySwitchLevels)
    (hbound : Encryption.Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (Encryption.Adaptive.realGame queryCount ringImplementation keySwitchImplementation
        inputImplementation tgswGadget keySwitchGadget encode adversary)| ≤
      Encryption.Adaptive.CutCycleSecurity.keySwitchFirstReplacementAdvantage queryCount
          ringReference errorReference errorReference tgswGadget keySwitchGadget
          encode adversary +
        LearningWithErrors.advantage
          (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
            lweDimension ringReference)
          (Native.BootstrapCutSecurity.realBatchReduction ringReference errorReference
            tgswGadget
            (Encryption.Adaptive.CutCycleSecurity.cutContinuation queryCount errorReference
              encode adversary)) +
        LearningWithErrors.advantage
          (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
            lweDimension ringReference)
          (Native.BootstrapCutSecurity.zeroBatchReduction ringReference errorReference
            (Encryption.Adaptive.CutCycleSecurity.cutContinuation queryCount errorReference
              encode adversary)) +
        LearningWithErrors.advantage
          (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels + queryCount)
            errorReference)
          (FormalProof4FHE.LWE.TwoBlock.reduction
            (Encryption.Adaptive.zeroCloudReduction ringReference errorReference errorReference
              tgswGadget encode adversary)) +
        adaptiveReplacementCost q degree ringRank tgswLevels lweDimension keySwitchLevels
          queryCount ringImplementation ringReference keySwitchImplementation errorReference
          inputImplementation errorReference := by
  calc
    |Encryption.signedAdvantage
      (Encryption.Adaptive.realGame queryCount ringImplementation keySwitchImplementation
        inputImplementation tgswGadget keySwitchGadget encode adversary)| ≤
      |Encryption.signedAdvantage
        (Encryption.Adaptive.realGame queryCount ringReference errorReference errorReference
          tgswGadget keySwitchGadget encode adversary)| +
        adaptiveReplacementCost q degree ringRank tgswLevels lweDimension keySwitchLevels
          queryCount ringImplementation ringReference keySwitchImplementation errorReference
          inputImplementation errorReference :=
      abs_signedAdvantage_adaptiveReal_le_reference_add q degree ringRank tgswLevels
        lweDimension keySwitchLevels queryCount ringImplementation ringReference
        keySwitchImplementation errorReference inputImplementation errorReference
        tgswGadget keySwitchGadget encode adversary
    _ ≤
      (Encryption.Adaptive.CutCycleSecurity.keySwitchFirstReplacementAdvantage queryCount
          ringReference errorReference errorReference tgswGadget keySwitchGadget
          encode adversary +
        LearningWithErrors.advantage
          (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
            lweDimension ringReference)
          (Native.BootstrapCutSecurity.realBatchReduction ringReference errorReference
            tgswGadget
            (Encryption.Adaptive.CutCycleSecurity.cutContinuation queryCount errorReference
              encode adversary)) +
        LearningWithErrors.advantage
          (Native.BootstrapCutSecurity.batchModuleLweProblem q degree ringRank tgswLevels
            lweDimension ringReference)
          (Native.BootstrapCutSecurity.zeroBatchReduction ringReference errorReference
            (Encryption.Adaptive.CutCycleSecurity.cutContinuation queryCount errorReference
              encode adversary)) +
        LearningWithErrors.advantage
          (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels + queryCount)
            errorReference)
          (FormalProof4FHE.LWE.TwoBlock.reduction
            (Encryption.Adaptive.zeroCloudReduction ringReference errorReference errorReference
              tgswGadget encode adversary))) +
        adaptiveReplacementCost q degree ringRank tgswLevels lweDimension keySwitchLevels
          queryCount ringImplementation ringReference keySwitchImplementation errorReference
          inputImplementation errorReference :=
      add_le_add
        (Encryption.Adaptive.CutCycleSecurity.abs_signedAdvantage_real_le_keySwitchFirst_add_two_batchModuleLwe_add_batchLwe_of_same_noise
          queryCount ringReference errorReference tgswGadget keySwitchGadget encode
          adversary hbound)
        le_rfl

end FormalProof4FHE.TFHE.SamplerReplacement.CutCycleSecurity
