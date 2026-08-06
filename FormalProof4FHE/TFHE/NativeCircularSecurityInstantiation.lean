/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.CircularSecurityMinimalAssumption
import FormalProof4FHE.TFHE.NativeTRGSWCompleteChannel

/-!
# Concrete native instantiation of the minimal TFHE circular assumption

This file specializes the generic coefficient-product experiment to the literal shared-prefix
native cloud-key samplers.  The encryption prefix is sampled once.  In the self game it is also
the encrypted BRK message, in the independent game the BRK message is a fresh binary vector, and
in the zero game it is the all-zero vector.  Every game samples the genuine independent suffix
and the genuine same-key suffix KSK through `fixedPrefixMessageView`.

The resulting assumption is no longer parameterized by arbitrary `productView` and `zeroView`
functions: it names one exact native distribution.  A second constructor attaches a prescribed
secret-dependent payload or auxiliary transcript, allowing the base ciphertext challenge to be
included in the same complete public view.
-/

set_option autoImplicit false

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.NativeCircularSecurityInstantiation

noncomputable section

open CircularSecurityMinimalAssumption
open CircularSecurityMinimalAssumption.CoefficientProductExperiment
open NativeTRGSWCompleteChannel
open Native.SharedRandomnessOneCycle

/-- The exact native shared-prefix BRK/KSK carrier used by the concrete experiment. -/
abbrev NativeCloudKey
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) :=
  CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels

/-- Native zero-message cloud key under a freshly sampled shared prefix and suffix. -/
noncomputable def zeroMessageNativeView
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    ProbComp (NativeCloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels) := do
  let prefixKey ← Native.sampleLweSecret prefixDimension
  fixedPrefixMessageView q prefixDimension suffixDimension tgswLevels keySwitchLevels
    ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget prefixKey
      (fun _ ↦ false)

/-- Literal native coefficient-product experiment on the complete BRK/KSK cloud key. -/
noncomputable def nativeCloudKeyExperiment
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    CoefficientProductExperiment (BinarySecret prefixDimension)
      (NativeCloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels) where
  secretSampler := Native.sampleLweSecret prefixDimension
  productView encryptionPrefix controlPrefix :=
    fixedPrefixMessageView q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
      encryptionPrefix controlPrefix
  zeroView encryptionPrefix :=
    fixedPrefixMessageView q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
      encryptionPrefix (fun _ ↦ false)

/-- The self sampler is definitionally the diagonal native sampler. -/
theorem nativeCloudKeyExperiment_selfSampler_eq_diagonalNativeView
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    (nativeCloudKeyExperiment q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).selfSampler =
      diagonalNativeView q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget := by
  rfl

/-- The independent sampler is definitionally the concrete independent-message native view. -/
theorem nativeCloudKeyExperiment_independentSampler_eq_independentMessageNativeView
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    (nativeCloudKeyExperiment q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).independentSampler =
      independentMessageNativeView q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget := by
  rfl

/-- The zero sampler is definitionally the native all-zero BRK view with the genuine same-key
suffix KSK. -/
theorem nativeCloudKeyExperiment_zeroSampler_eq_zeroMessageNativeView
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    (nativeCloudKeyExperiment q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).zeroSampler =
      zeroMessageNativeView q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget := by
  rfl

/-- The exact self sampler has the literal native real-cloud-key distribution. -/
theorem nativeCloudKeyExperiment_selfSampler_evalDist_eq_realCloudKeyView
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    evalDist
        (nativeCloudKeyExperiment q prefixDimension suffixDimension tgswLevels keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).selfSampler =
      evalDist (Native.SharedRandomnessOneCycle.realCloudKeyView q prefixDimension
        suffixDimension tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget) := by
  rw [nativeCloudKeyExperiment_selfSampler_eq_diagonalNativeView]
  exact diagonalNativeView_evalDist_eq_realCloudKeyView q prefixDimension suffixDimension
    tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler
    tgswGadget keySwitchGadget

/-- Exact concrete wording of the remaining native coefficient-product correlation premise. -/
def NativeCorrelationHardAgainst
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (allowed : Distinguisher
      (NativeCloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels) → Prop)
    (bound : ℝ) : Prop :=
  (nativeCloudKeyExperiment q prefixDimension suffixDimension tgswLevels keySwitchLevels
    ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).CorrelationHardAgainst
      allowed bound

/-- Exact compact native cloud-key theorem.  The only nonstandard term is the diagonal-to-
independent correlation bound.  All independent-message hiding and the final zero endpoint may
be supplied together as `standardBound`. -/
theorem nativeCloudKeySecurity_le_correlation_add_standard
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (ideal : ProbComp
      (NativeCloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels))
    (distinguisher : Distinguisher
      (NativeCloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels))
    (correlationBound standardBound : ℝ)
    (hcorrelation :
      (nativeCloudKeyExperiment q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).correlationAdvantage
          distinguisher ≤ correlationBound)
    (hstandard : distinguishingAdvantage
      (independentMessageNativeView q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
      ideal distinguisher ≤ standardBound) :
    distinguishingAdvantage
      (Native.SharedRandomnessOneCycle.realCloudKeyView q prefixDimension suffixDimension
        tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget)
      ideal distinguisher ≤ correlationBound + standardBound := by
  let experiment := nativeCloudKeyExperiment q prefixDimension suffixDimension tgswLevels
    keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
  have hself : evalDist
      (Native.SharedRandomnessOneCycle.realCloudKeyView q prefixDimension suffixDimension
        tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget) = evalDist experiment.selfSampler :=
    (nativeCloudKeyExperiment_selfSampler_evalDist_eq_realCloudKeyView q prefixDimension
      suffixDimension tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget).symm
  have hsampler : distinguishingAdvantage
      (Native.SharedRandomnessOneCycle.realCloudKeyView q prefixDimension suffixDimension
        tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget)
      experiment.selfSampler distinguisher ≤ 0 := by
    rw [distinguishingAdvantage_eq_zero_of_evalDist_eq hself]
  have hbound := experiment.toThreeGame.security_le_correlation_add_standard_add_sampler
    (Native.SharedRandomnessOneCycle.realCloudKeyView q prefixDimension suffixDimension
      tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler
      tgswGadget keySwitchGadget)
    ideal distinguisher correlationBound standardBound 0 hsampler hcorrelation
  have hstandard' : distinguishingAdvantage experiment.toThreeGame.independentSampler
      ideal distinguisher ≤ standardBound := by
    simpa [experiment, CoefficientProductExperiment.toThreeGame,
      nativeCloudKeyExperiment_independentSampler_eq_independentMessageNativeView] using hstandard
  exact (hbound hstandard').trans_eq (by ring)

/-! ## Prescribed payload or auxiliary transcript -/

/-- Complete native public view with a prescribed transcript under the encryption prefix.
The transcript can be a base ciphertext challenge, public metadata, or their product. -/
abbrev NativeCompleteView
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ)
    (Auxiliary : Type) :=
  NativeCloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels × Auxiliary

/-- Attach the same prescribed encryption-prefix-dependent transcript in all three games. -/
noncomputable def nativeCompleteViewExperiment
    {Auxiliary : Type}
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (auxiliarySampler : BinarySecret prefixDimension → ProbComp Auxiliary) :
    CoefficientProductExperiment (BinarySecret prefixDimension)
      (NativeCompleteView q prefixDimension suffixDimension tgswLevels keySwitchLevels
        Auxiliary) where
  secretSampler := Native.sampleLweSecret prefixDimension
  productView encryptionPrefix controlPrefix := do
    let cloudKey ← fixedPrefixMessageView q prefixDimension suffixDimension tgswLevels
      keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
      encryptionPrefix controlPrefix
    let auxiliary ← auxiliarySampler encryptionPrefix
    return (cloudKey, auxiliary)
  zeroView encryptionPrefix := do
    let cloudKey ← fixedPrefixMessageView q prefixDimension suffixDimension tgswLevels
      keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
      encryptionPrefix (fun _ ↦ false)
    let auxiliary ← auxiliarySampler encryptionPrefix
    return (cloudKey, auxiliary)

/-- Compact complete-view theorem.  Once the exact transcript sampler is chosen, only its
correlation and bundled standard endpoint occur in the public security statement. -/
theorem nativeCompleteViewSecurity_le_correlation_add_standard
    {Auxiliary : Type}
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (auxiliarySampler : BinarySecret prefixDimension → ProbComp Auxiliary)
    (ideal : ProbComp
      (NativeCompleteView q prefixDimension suffixDimension tgswLevels keySwitchLevels
        Auxiliary))
    (distinguisher : Distinguisher
      (NativeCompleteView q prefixDimension suffixDimension tgswLevels keySwitchLevels
        Auxiliary))
    (correlationBound standardBound : ℝ)
    (hcorrelation :
      (nativeCompleteViewExperiment q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        auxiliarySampler).correlationAdvantage distinguisher ≤ correlationBound)
    (hstandard : distinguishingAdvantage
      (nativeCompleteViewExperiment q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        auxiliarySampler).independentSampler ideal distinguisher ≤ standardBound) :
    distinguishingAdvantage
      (nativeCompleteViewExperiment q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        auxiliarySampler).selfSampler ideal distinguisher ≤
      correlationBound + standardBound := by
  let experiment := nativeCompleteViewExperiment q prefixDimension suffixDimension tgswLevels
    keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
    auxiliarySampler
  have hsampler : distinguishingAdvantage experiment.selfSampler experiment.selfSampler
      distinguisher ≤ 0 := by
    rw [distinguishingAdvantage_eq_zero_of_evalDist_eq rfl]
  have hbound := experiment.toThreeGame.security_le_correlation_add_standard_add_sampler
    experiment.selfSampler ideal distinguisher correlationBound standardBound 0
      hsampler hcorrelation hstandard
  exact hbound.trans_eq (by ring)

end

end FormalProof4FHE.TFHE.NativeCircularSecurityInstantiation
