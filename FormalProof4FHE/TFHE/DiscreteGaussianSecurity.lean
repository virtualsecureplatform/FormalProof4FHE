/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.DiscreteGaussianSampler
import FormalProof4FHE.TFHE.MonomialKDM

/-!
# Adaptive TFHE Security with Certified Discrete-Gaussian Samplers

This file states the finite end-to-end security theorem in the form closest to the native TFHE
construction.  Its three terms are:

1. the exact intact-cycle degree-two monomial-KDM advantage of the normalized native
   bootstrapping key;
2. one conventional binary-secret batch-LWE advantage for the key-switch rows and adaptive
   input rows; and
3. the fully explicit statistical loss of replacing the reference modular discrete-Gaussian
   tables by implementation tables.

The first term is the circular-security assumption.  The cited ACPS, BV, and BGK results prove
KDM security for modified encryption/key geometries, not for this native TFHE fixed-hint
distribution, so it is deliberately not rewritten as ordinary LWE.  Every other computational
and statistical step is discharged by the checked reductions.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.DiscreteGaussianSecurity

/-- Complete certificate-derived replacement loss for the BRK, KSK, and adaptive input tape. -/
noncomputable def certifiedReplacementBound
    (degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ)
    {q : ℕ} [NeZero q]
    {ringAlpha scalarAlpha : ℝ}
    {hringAlpha : 0 < ringAlpha} {hscalarAlpha : 0 < scalarAlpha}
    (ringImplementation ringReference :
      DiscreteGaussianSampler.ScalarCertificate q ringAlpha hringAlpha)
    (keySwitchImplementation inputImplementation referenceError :
      DiscreteGaussianSampler.ScalarCertificate q scalarAlpha hscalarAlpha) : ℝ :=
  ((SamplerReplacement.bootstrappingErrorCount ringRank tgswLevels lweDimension : ℝ) *
      ((degree : ℝ) *
        DiscreteGaussianSampler.pairBound ringImplementation ringReference) +
    (SamplerReplacement.keySwitchErrorCount ringRank degree keySwitchLevels : ℝ) *
      DiscreteGaussianSampler.pairBound keySwitchImplementation referenceError) +
    (queryCount : ℝ) *
      DiscreteGaussianSampler.pairBound inputImplementation referenceError

/-- **Finite native TFHE security with certified modular discrete-Gaussian samplers.**

The reference KSK and adaptive-input samplers coincide, so their rows flatten to one ordinary
batch-LWE instance.  The two implementation scalar samplers may differ.  The intact-cycle term
uses the exact degree-two monomial presentation proved equal to the native normalized BRK. -/
theorem abs_signedAdvantage_le_monomialKDM_add_batchLWE_add_certificates
    {Message : Type}
    (q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount : ℕ) [NeZero q]
    {ringAlpha scalarAlpha : ℝ}
    {hringAlpha : 0 < ringAlpha} {hscalarAlpha : 0 < scalarAlpha}
    (ringImplementation ringReference :
      DiscreteGaussianSampler.ScalarCertificate q ringAlpha hringAlpha)
    (keySwitchImplementation inputImplementation referenceError :
      DiscreteGaussianSampler.ScalarCertificate q scalarAlpha hscalarAlpha)
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : Encryption.Adaptive.NativeAdversary Message q degree ringRank
      tgswLevels lweDimension keySwitchLevels)
    (hbound : Encryption.Adaptive.IsQueryBound adversary queryCount) :
    |Encryption.signedAdvantage
      (Encryption.Adaptive.realGame queryCount
        (DiscreteGaussianSampler.ringSampler degree ringImplementation)
        (DiscreteGaussianSampler.scalarSampler keySwitchImplementation)
        (DiscreteGaussianSampler.scalarSampler inputImplementation)
        tgswGadget keySwitchGadget encode adversary)| ≤
      Native.BootstrapSecurity.MonomialKDM.advantage
          (DiscreteGaussianSampler.ringSampler degree ringReference)
          (DiscreteGaussianSampler.scalarSampler referenceError)
          tgswGadget keySwitchGadget
          (Encryption.Adaptive.continuation queryCount
            (DiscreteGaussianSampler.scalarSampler referenceError) encode adversary) +
        LearningWithErrors.advantage
          (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels + queryCount)
            (DiscreteGaussianSampler.scalarSampler referenceError))
          (FormalProof4FHE.LWE.TwoBlock.reduction
            (Encryption.Adaptive.keySwitchMessageReduction
              (DiscreteGaussianSampler.ringSampler degree ringReference)
              (DiscreteGaussianSampler.scalarSampler referenceError)
              (DiscreteGaussianSampler.scalarSampler referenceError)
              tgswGadget
              (Encryption.Adaptive.nativeKeySwitchMessage keySwitchGadget)
              encode adversary)) +
        certifiedReplacementBound degree ringRank tgswLevels lweDimension keySwitchLevels
          queryCount ringImplementation ringReference keySwitchImplementation
          inputImplementation referenceError := by
  let ringImplementationSampler :=
    DiscreteGaussianSampler.ringSampler degree ringImplementation
  let ringReferenceSampler :=
    DiscreteGaussianSampler.ringSampler degree ringReference
  let keySwitchImplementationSampler :=
    DiscreteGaussianSampler.scalarSampler keySwitchImplementation
  let inputImplementationSampler :=
    DiscreteGaussianSampler.scalarSampler inputImplementation
  let referenceSampler := DiscreteGaussianSampler.scalarSampler referenceError
  have hBase :=
    SamplerReplacement.abs_signedAdvantage_implementation_le_directBilinear_add_batchLwe_add_replacement
      q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount
      ringImplementationSampler ringReferenceSampler keySwitchImplementationSampler
      inputImplementationSampler referenceSampler tgswGadget keySwitchGadget encode adversary hbound
  have hReplacement :
      SamplerReplacement.adaptiveReplacementCost q degree ringRank tgswLevels lweDimension
          keySwitchLevels queryCount ringImplementationSampler ringReferenceSampler
          keySwitchImplementationSampler referenceSampler inputImplementationSampler
          referenceSampler ≤
        certifiedReplacementBound degree ringRank tgswLevels lweDimension keySwitchLevels
          queryCount ringImplementation ringReference keySwitchImplementation
          inputImplementation referenceError := by
    exact DiscreteGaussianSampler.adaptiveReplacementCost_le_certificates
      q degree ringRank tgswLevels lweDimension keySwitchLevels queryCount
      ringImplementation ringReference keySwitchImplementation referenceError
      inputImplementation referenceError
  change |Encryption.signedAdvantage
      (Encryption.Adaptive.realGame queryCount ringImplementationSampler
        keySwitchImplementationSampler inputImplementationSampler
        tgswGadget keySwitchGadget encode adversary)| ≤ _
  calc
    |Encryption.signedAdvantage
      (Encryption.Adaptive.realGame queryCount ringImplementationSampler
        keySwitchImplementationSampler inputImplementationSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      Native.BootstrapSecurity.directBilinearAdvantage
          ringReferenceSampler referenceSampler tgswGadget keySwitchGadget
          (Encryption.Adaptive.continuation queryCount referenceSampler encode adversary) +
        LearningWithErrors.advantage
          (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels + queryCount)
            referenceSampler)
          (FormalProof4FHE.LWE.TwoBlock.reduction
            (Encryption.Adaptive.keySwitchMessageReduction ringReferenceSampler
              referenceSampler referenceSampler tgswGadget
              (Encryption.Adaptive.nativeKeySwitchMessage keySwitchGadget)
              encode adversary)) +
        SamplerReplacement.adaptiveReplacementCost q degree ringRank tgswLevels
          lweDimension keySwitchLevels queryCount ringImplementationSampler
          ringReferenceSampler keySwitchImplementationSampler referenceSampler
          inputImplementationSampler referenceSampler :=
      hBase
    _ = Native.BootstrapSecurity.MonomialKDM.advantage
          ringReferenceSampler referenceSampler tgswGadget keySwitchGadget
          (Encryption.Adaptive.continuation queryCount referenceSampler encode adversary) +
        LearningWithErrors.advantage
          (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels + queryCount)
            referenceSampler)
          (FormalProof4FHE.LWE.TwoBlock.reduction
            (Encryption.Adaptive.keySwitchMessageReduction ringReferenceSampler
              referenceSampler referenceSampler tgswGadget
              (Encryption.Adaptive.nativeKeySwitchMessage keySwitchGadget)
              encode adversary)) +
        SamplerReplacement.adaptiveReplacementCost q degree ringRank tgswLevels
          lweDimension keySwitchLevels queryCount ringImplementationSampler
          ringReferenceSampler keySwitchImplementationSampler referenceSampler
          inputImplementationSampler referenceSampler := by
      rw [Native.BootstrapSecurity.MonomialKDM.advantage_eq_directBilinear]
    _ ≤ Native.BootstrapSecurity.MonomialKDM.advantage
          ringReferenceSampler referenceSampler tgswGadget keySwitchGadget
          (Encryption.Adaptive.continuation queryCount referenceSampler encode adversary) +
        LearningWithErrors.advantage
          (Native.KeySwitchSecurity.binaryLweProblem q lweDimension
            (Encryption.Security.keySwitchSamples ringRank degree keySwitchLevels + queryCount)
            referenceSampler)
          (FormalProof4FHE.LWE.TwoBlock.reduction
            (Encryption.Adaptive.keySwitchMessageReduction ringReferenceSampler
              referenceSampler referenceSampler tgswGadget
              (Encryption.Adaptive.nativeKeySwitchMessage keySwitchGadget)
              encode adversary)) +
        certifiedReplacementBound degree ringRank tgswLevels lweDimension keySwitchLevels
          queryCount ringImplementation ringReference keySwitchImplementation
          inputImplementation referenceError :=
      add_le_add_right hReplacement _

end FormalProof4FHE.TFHE.DiscreteGaussianSecurity
