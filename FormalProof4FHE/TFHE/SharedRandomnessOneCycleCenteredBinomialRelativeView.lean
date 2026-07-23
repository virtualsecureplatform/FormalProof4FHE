/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.SharedRandomnessOneCycleRelativeViewRandomization

/-!
# Concrete Relative-Then-Complement View Randomization

This module instantiates the exact global-complement half of one-cycle TFHE key randomization for
the complete correlated centered-binomial bootstrapping key and shared-randomness suffix KSK.
The full binary master key has `prefixDimension + suffixTail + 1` coefficients.  Its normalized
relative mask has one fewer coefficient, and the remaining Boolean mask selects global complement.

The centered-binomial BRK error vector is shear-orbit symmetrized, so complementing the BRK and
KSK is distributionally exact and contributes zero total-variation error.  Consequently any
relative-mask evaluator satisfying the displayed `relativeDistance_le` obligation yields the full
fresh-master-key `ViewRandomization` interface with exactly the same error.  Constructing that
nonlinear relative evaluator, and reducing its decision view to ordinary hardness, remain the
research obligations; neither is assumed silently here.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle.SecretRandomization

noncomputable section

abbrev CenteredBinomialShearEvaluationKeyView
    (q prefixDimension suffixTail tgswLevels keySwitchLevels : ℕ) :=
  Native.BootstrappingKey q (prefixDimension + suffixTail + 1) 1
      tgswLevels prefixDimension ×
    Native.KeySwitchKey q prefixDimension (suffixTail + 1) keySwitchLevels

noncomputable def sampleCenteredBinomialShearEvaluationKeyView
    (q prefixDimension suffixTail tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringEta keySwitchEta : ℕ)
    (tgswGadget :
      Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixTail + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (masterSecret : BinarySecret (prefixDimension + suffixTail + 1)) :
    ProbComp (CenteredBinomialShearEvaluationKeyView q prefixDimension suffixTail
      tgswLevels keySwitchLevels) := do
  let ringSecret : RingBinarySecret 1 (prefixDimension + suffixTail + 1) :=
    fun _ ↦ masterSecret
  let bootstrappingKey ←
    generateBootstrappingKeyWithErrorVector q (prefixDimension + suffixTail)
      tgswLevels prefixDimension
      (centeredBinomialShearErrorVector q (prefixDimension + suffixTail)
        tgswLevels ringEta)
      tgswGadget
      (prefixSecret
        (prefixDimension := prefixDimension)
        (suffixDimension := suffixTail + 1)
        ringSecret)
      ringSecret
  let keySwitchKey ←
    Native.generateKeySwitchKey q prefixDimension (suffixTail + 1)
      keySwitchLevels (CenteredBinomial.scalarSampler q keySwitchEta)
      keySwitchGadget
      (suffixSecret
        (prefixDimension := prefixDimension)
        (suffixDimension := suffixTail + 1)
        ringSecret)
      (prefixSecret
        (prefixDimension := prefixDimension)
        (suffixDimension := suffixTail + 1)
        ringSecret)
  return (bootstrappingKey, keySwitchKey)

def transformCenteredBinomialShearEvaluationKeyView
    {q prefixDimension suffixTail tgswLevels keySwitchLevels : ℕ}
    (tgswGadget :
      Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixTail + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (toggle : Bool)
    (view : CenteredBinomialShearEvaluationKeyView q prefixDimension suffixTail
      tgswLevels keySwitchLevels) :
    CenteredBinomialShearEvaluationKeyView q prefixDimension suffixTail
      tgswLevels keySwitchLevels :=
  if toggle then
    globalComplementEvaluationKeyPair
      (embedBinaryPolynomial q (prefixDimension + suffixTail + 1)
        (allTruePolynomial (prefixDimension + suffixTail + 1)))
      tgswGadget keySwitchGadget view
  else view

@[simp]
theorem globalComplementAction_false_local
    {dimension : ℕ} (secret : BinarySecret dimension) :
    globalComplementAction secret false = secret := by
  funext coordinate
  simp [globalComplementAction,
    FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret,
    LWE.MultiKeyAffine.maskedBit]

theorem sampleCenteredBinomialShearEvaluationKeyView_complement_evalDist
    {q prefixDimension suffixTail tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringEta keySwitchEta : ℕ)
    (tgswGadget :
      Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixTail + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (masterSecret : BinarySecret (prefixDimension + suffixTail + 1))
    (toggle : Bool) :
    evalDist
        (sampleCenteredBinomialShearEvaluationKeyView q prefixDimension suffixTail
          tgswLevels keySwitchLevels ringEta keySwitchEta tgswGadget
          keySwitchGadget masterSecret >>= fun view ↦
            pure (transformCenteredBinomialShearEvaluationKeyView
              tgswGadget keySwitchGadget toggle view)) =
      evalDist
        (sampleCenteredBinomialShearEvaluationKeyView q prefixDimension suffixTail
          tgswLevels keySwitchLevels ringEta keySwitchEta tgswGadget
          keySwitchGadget (globalComplementAction masterSecret toggle)) := by
  cases toggle
  · simp [transformCenteredBinomialShearEvaluationKeyView]
  · unfold sampleCenteredBinomialShearEvaluationKeyView
    simp only [transformCenteredBinomialShearEvaluationKeyView, if_true]
    let ringSecret : RingBinarySecret 1 (prefixDimension + suffixTail + 1) :=
      fun _ ↦ masterSecret
    let targetRingSecret :
        RingBinarySecret 1 (prefixDimension + suffixTail + 1) :=
      fun _ ↦ globalComplementAction masterSecret true
    have hring :
        maskedRingSecret ringSecret
            (fun _ _ ↦ true :
              RingBinarySecret 1 (prefixDimension + suffixTail + 1)) =
          targetRingSecret := by
      funext component coordinate
      simp [ringSecret, targetRingSecret, maskedRingSecret,
        globalComplementAction,
        FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret]
    have hprefix :
        globalComplementAction
            (prefixSecret
              (prefixDimension := prefixDimension)
              (suffixDimension := suffixTail + 1)
              ringSecret)
            true =
          prefixSecret
            (prefixDimension := prefixDimension)
            (suffixDimension := suffixTail + 1)
            targetRingSecret := by
      funext coordinate
      simp [ringSecret, targetRingSecret, prefixSecret,
        globalComplementAction,
        FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret]
    have hsuffix :
        globalComplementAction
            (suffixSecret
              (prefixDimension := prefixDimension)
              (suffixDimension := suffixTail + 1)
              ringSecret)
            true =
          suffixSecret
            (prefixDimension := prefixDimension)
            (suffixDimension := suffixTail + 1)
            targetRingSecret := by
      funext coordinate
      simp [ringSecret, targetRingSecret, suffixSecret,
        globalComplementAction,
        FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret]
    have hmain := globalComplementEvaluationKeyPair_centeredBinomialShear_evalDist
      (q := q) (degree := prefixDimension + suffixTail)
      (tgswLevels := tgswLevels) (lweDimension := prefixDimension)
      (sourceDimension := suffixTail + 1)
      (keySwitchLevels := keySwitchLevels)
      ringEta keySwitchEta tgswGadget keySwitchGadget
      (prefixSecret
        (prefixDimension := prefixDimension)
        (suffixDimension := suffixTail + 1)
        ringSecret)
      ringSecret
      (suffixSecret
        (prefixDimension := prefixDimension)
        (suffixDimension := suffixTail + 1)
        ringSecret)
    dsimp only at hmain
    rw [hring, hprefix, hsuffix] at hmain
    simpa only [ringSecret, targetRingSecret, map_eq_bind_pure_comp,
      Function.comp_def] using hmain

/-- Package any normalized-relative evaluator for the concrete centered-binomial view with the
exact global-complement transform.  The complement step contributes zero statistical error. -/
noncomputable def centeredBinomialShearRelativeThenComplementEvaluator
    {q prefixDimension suffixTail tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringEta keySwitchEta : ℕ)
    (tgswGadget :
      Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixTail + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (sampleNarrowView : BinarySecret (prefixDimension + suffixTail + 1) →
      ProbComp (CenteredBinomialShearEvaluationKeyView q prefixDimension suffixTail
        tgswLevels keySwitchLevels))
    (evaluateRelative : BinarySecret (prefixDimension + suffixTail) →
      CenteredBinomialShearEvaluationKeyView q prefixDimension suffixTail
        tgswLevels keySwitchLevels →
      ProbComp (CenteredBinomialShearEvaluationKeyView q prefixDimension suffixTail
        tgswLevels keySwitchLevels))
    (relativeError : ℝ) (relativeError_nonneg : 0 ≤ relativeError)
    (relativeDistance_le : ∀ secret relativeMask,
      tvDist
          (sampleNarrowView secret >>= evaluateRelative relativeMask)
          (sampleCenteredBinomialShearEvaluationKeyView q prefixDimension suffixTail
            tgswLevels keySwitchLevels ringEta keySwitchEta tgswGadget
            keySwitchGadget
            (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
              secret (relativeMaskLift relativeMask))) ≤ relativeError) :
    RelativeThenComplementEvaluator (prefixDimension + suffixTail)
      (CenteredBinomialShearEvaluationKeyView q prefixDimension suffixTail
        tgswLevels keySwitchLevels) :=
  RelativeThenComplementEvaluator.ofExactComplement
    sampleNarrowView
    (sampleCenteredBinomialShearEvaluationKeyView q prefixDimension suffixTail
      tgswLevels keySwitchLevels ringEta keySwitchEta tgswGadget keySwitchGadget)
    evaluateRelative relativeError relativeError_nonneg relativeDistance_le
    (transformCenteredBinomialShearEvaluationKeyView tgswGadget keySwitchGadget)
    (sampleCenteredBinomialShearEvaluationKeyView_complement_evalDist
      ringEta keySwitchEta tgswGadget keySwitchGadget)

/-- The concrete relative evaluator certificate yields the complete fresh-master-key
`ViewRandomization` interface.  Its error is exactly the supplied relative-step error. -/
noncomputable def centeredBinomialShearViewRandomizationOfRelative
    {q prefixDimension suffixTail tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringEta keySwitchEta : ℕ)
    (tgswGadget :
      Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixTail + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (sampleNarrowView : BinarySecret (prefixDimension + suffixTail + 1) →
      ProbComp (CenteredBinomialShearEvaluationKeyView q prefixDimension suffixTail
        tgswLevels keySwitchLevels))
    (evaluateRelative : BinarySecret (prefixDimension + suffixTail) →
      CenteredBinomialShearEvaluationKeyView q prefixDimension suffixTail
        tgswLevels keySwitchLevels →
      ProbComp (CenteredBinomialShearEvaluationKeyView q prefixDimension suffixTail
        tgswLevels keySwitchLevels))
    (relativeError : ℝ) (relativeError_nonneg : 0 ≤ relativeError)
    (relativeDistance_le : ∀ secret relativeMask,
      tvDist
          (sampleNarrowView secret >>= evaluateRelative relativeMask)
          (sampleCenteredBinomialShearEvaluationKeyView q prefixDimension suffixTail
            tgswLevels keySwitchLevels ringEta keySwitchEta tgswGadget
            keySwitchGadget
            (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
              secret (relativeMaskLift relativeMask))) ≤ relativeError) :
    LWE.AuxiliaryInput.SearchToDecision.ViewRandomization
      (BinarySecret (prefixDimension + suffixTail + 1))
      (BinarySecret (prefixDimension + suffixTail) × Bool)
      (CenteredBinomialShearEvaluationKeyView q prefixDimension suffixTail
        tgswLevels keySwitchLevels) :=
  (centeredBinomialShearRelativeThenComplementEvaluator ringEta keySwitchEta
    tgswGadget keySwitchGadget sampleNarrowView evaluateRelative relativeError
    relativeError_nonneg relativeDistance_le).toViewRandomization

@[simp]
theorem centeredBinomialShearViewRandomizationOfRelative_error
    {q prefixDimension suffixTail tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringEta keySwitchEta : ℕ)
    (tgswGadget :
      Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixTail + 1))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (sampleNarrowView : BinarySecret (prefixDimension + suffixTail + 1) →
      ProbComp (CenteredBinomialShearEvaluationKeyView q prefixDimension suffixTail
        tgswLevels keySwitchLevels))
    (evaluateRelative : BinarySecret (prefixDimension + suffixTail) →
      CenteredBinomialShearEvaluationKeyView q prefixDimension suffixTail
        tgswLevels keySwitchLevels →
      ProbComp (CenteredBinomialShearEvaluationKeyView q prefixDimension suffixTail
        tgswLevels keySwitchLevels))
    (relativeError : ℝ) (relativeError_nonneg : 0 ≤ relativeError)
    (relativeDistance_le : ∀ secret relativeMask,
      tvDist
          (sampleNarrowView secret >>= evaluateRelative relativeMask)
          (sampleCenteredBinomialShearEvaluationKeyView q prefixDimension suffixTail
            tgswLevels keySwitchLevels ringEta keySwitchEta tgswGadget
            keySwitchGadget
            (FormalProof4FHE.TFHE.Native.ScalarSecretRandomization.maskedSecret
              secret (relativeMaskLift relativeMask))) ≤ relativeError) :
    (centeredBinomialShearViewRandomizationOfRelative ringEta keySwitchEta
      tgswGadget keySwitchGadget sampleNarrowView evaluateRelative relativeError
      relativeError_nonneg relativeDistance_le).error = relativeError := by
  simp [centeredBinomialShearViewRandomizationOfRelative,
    centeredBinomialShearRelativeThenComplementEvaluator,
    RelativeThenComplementEvaluator.toViewRandomization,
    RelativeThenComplementEvaluator.ofExactComplement]

end

end FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle.SecretRandomization
