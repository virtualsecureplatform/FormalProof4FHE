/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.SharedRandomness.KeySwitching
import FormalProof4FHE.TFHE.MonomialKDM
import FormalProof4FHE.TFHE.SamplerReplacement

/-!
# Native TFHE with a Shared-Randomness Suffix KSK

This module defines the nested-secret TFHE variant in which the scalar TLWE key is the prefix of
the coefficient-extracted rank-one ring key.  Only the independent suffix is published in the
key-switch table.  Thus the KSK edge is an ordinary affine-message LWE batch, while the BRK
encrypts prefix bits of its own ring encryption key and is a genuine one-key circular object.

The construction changes only the key relation and KSK layout.  It does not claim that ordinary
RLWE proves security of the remaining one-key native TRGSW distribution.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle

noncomputable section

open FormalProof4FHE.SharedRandomness

variable {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ}

/-- Prefix of the coefficient-extracted rank-one ring key, used as the scalar TLWE key. -/
def prefixSecret
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    BinarySecret prefixDimension :=
  fun coordinate ↦ ringSecret 0 (Fin.castAdd suffixDimension coordinate)

/-- Fresh suffix of the coefficient-extracted rank-one ring key. -/
def suffixSecret
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    BinarySecret suffixDimension :=
  fun coordinate ↦ ringSecret 0 (Fin.natAdd prefixDimension coordinate)

/-- Every coefficient of the complete extracted ring key is exactly the corresponding entry of
its shared prefix/suffix concatenation. -/
theorem keyExtract_apply_eq_append_prefix_suffix
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension))
    (coordinate : Fin (prefixDimension + suffixDimension)) :
    keyExtract ringSecret (finProdFinEquiv (0, coordinate)) =
      Fin.append (prefixSecret ringSecret) (suffixSecret ringSecret) coordinate := by
  rw [keyExtract_apply]
  refine Fin.addCases ?_ ?_ coordinate
  · intro prefixCoordinate
    simp only [prefixSecret, Fin.append_left]
  · intro suffixCoordinate
    simp only [suffixSecret, Fin.append_right]

/-- Assemble a rank-one ring key from an independently sampled shared prefix and suffix. -/
def nestedRingSecret
    (prefixKey : BinarySecret prefixDimension)
    (suffixKey : BinarySecret suffixDimension) :
    RingBinarySecret 1 (prefixDimension + suffixDimension) :=
  fun _ coordinate ↦ Fin.append prefixKey suffixKey coordinate

@[simp]
theorem keyExtract_nestedRingSecret_apply
    (prefixKey : BinarySecret prefixDimension)
    (suffixKey : BinarySecret suffixDimension)
    (coordinate : Fin (prefixDimension + suffixDimension)) :
    keyExtract (nestedRingSecret prefixKey suffixKey) (finProdFinEquiv (0, coordinate)) =
      Fin.append prefixKey suffixKey coordinate := by
  rw [keyExtract_apply]
  rfl

@[simp]
theorem prefixSecret_nestedRingSecret
    (prefixKey : BinarySecret prefixDimension)
    (suffixKey : BinarySecret suffixDimension) :
    prefixSecret (nestedRingSecret prefixKey suffixKey) = prefixKey := by
  funext coordinate
  simp [prefixSecret, nestedRingSecret]

@[simp]
theorem suffixSecret_nestedRingSecret
    (prefixKey : BinarySecret prefixDimension)
    (suffixKey : BinarySecret suffixDimension) :
    suffixSecret (nestedRingSecret prefixKey suffixKey) = suffixKey := by
  funext coordinate
  simp [suffixSecret, nestedRingSecret]

@[simp]
theorem nestedRingSecret_prefix_suffix
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    nestedRingSecret (prefixSecret ringSecret) (suffixSecret ringSecret) = ringSecret := by
  funext component coordinate
  have hcomponent : component = 0 := Subsingleton.elim _ _
  subst component
  refine Fin.addCases ?_ ?_ coordinate
  · intro prefixCoordinate
    simp [nestedRingSecret, prefixSecret]
  · intro suffixCoordinate
    simp [nestedRingSecret, suffixSecret]

/-- Splitting a rank-one master key into its shared prefix and suffix is an equivalence. -/
def splitNestedSecret
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    BinarySecret prefixDimension × BinarySecret suffixDimension :=
  (prefixSecret ringSecret, suffixSecret ringSecret)

/-- Splitting a rank-one master key into its shared prefix and suffix is an equivalence. -/
def nestedSecretEquiv (prefixDimension suffixDimension : ℕ) :
    RingBinarySecret 1 (prefixDimension + suffixDimension) ≃
      BinarySecret prefixDimension × BinarySecret suffixDimension where
  toFun := splitNestedSecret
  invFun := fun keys ↦ nestedRingSecret keys.1 keys.2
  left_inv := nestedRingSecret_prefix_suffix
  right_inv := by
    rintro ⟨prefixKey, suffixKey⟩
    simp [splitNestedSecret]

/-- A uniform master ring key induces exactly independent uniform prefix and suffix keys. -/
theorem sampleRingSecret_prefix_suffix_evalDist
    (prefixDimension suffixDimension : ℕ) :
    evalDist (do
      let ringSecret ← Native.sampleRingSecret 1 (prefixDimension + suffixDimension)
      return splitNestedSecret ringSecret) =
      evalDist (do
        let prefixKey ← Native.sampleLweSecret prefixDimension
        let suffixKey ← Native.sampleLweSecret suffixDimension
        return (prefixKey, suffixKey)) := by
  calc
    _ = evalDist ($ᵗ (BinarySecret prefixDimension × BinarySecret suffixDimension)) := by
      simpa only [Native.sampleRingSecret, map_eq_bind_pure_comp, Function.comp_def] using
        (evalDist_map_bijective_uniform_cross
          (α := RingBinarySecret 1 (prefixDimension + suffixDimension))
          (β := BinarySecret prefixDimension × BinarySecret suffixDimension)
          (splitNestedSecret (prefixDimension := prefixDimension)
            (suffixDimension := suffixDimension))
          (nestedSecretEquiv prefixDimension suffixDimension).bijective)
    _ = _ := by
      simpa only [Native.sampleLweSecret] using
        (FormalProof4FHE.FiniteProduct.evalDist_independent_uniform_product
          (first := BinarySecret prefixDimension)
          (second := BinarySecret suffixDimension)).symm

/-- The suffix-only KSK contains no rows for the prefix coordinates already shared with the
target scalar key. -/
abbrev SharedKeySwitchKey
    (q prefixDimension suffixDimension keySwitchLevels : ℕ) :=
  KeySwitchKey q prefixDimension suffixDimension keySwitchLevels

/-- Native rank-one BRK for the nested ring degree. -/
abbrev SharedBootstrappingKey
    (q prefixDimension suffixDimension tgswLevels : ℕ) :=
  BootstrappingKey q (prefixDimension + suffixDimension) 1 tgswLevels prefixDimension

/-- Native cloud key for the shared-randomness one-cycle construction. -/
structure CloudKey
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) where
  bootstrappingKey :
    SharedBootstrappingKey q prefixDimension suffixDimension tgswLevels
  keySwitchKey :
    SharedKeySwitchKey q prefixDimension suffixDimension keySwitchLevels

/-- Real BRK: the encrypted scalar bits are a prefix of the BRK encryption key itself. -/
noncomputable def generateBootstrappingKey
    (q prefixDimension suffixDimension tgswLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (gadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    ProbComp (SharedBootstrappingKey q prefixDimension suffixDimension tgswLevels) :=
  Native.generateBootstrappingKey q (prefixDimension + suffixDimension) 1 tgswLevels
    prefixDimension errorSampler gadget (prefixSecret ringSecret) ringSecret

/-- The TFHE source key encrypted in the BRK is exactly a prefix of the TFHE target ring key.
This named normal form makes the shared-randomness one-cycle explicit: there are not two
independent keys and there is no second BRK encryption key. -/
theorem generateBootstrappingKey_eq_native_prefix_under_master
    (q prefixDimension suffixDimension tgswLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (gadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (targetRingKey : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    generateBootstrappingKey q prefixDimension suffixDimension tgswLevels
        errorSampler gadget targetRingKey =
      Native.generateBootstrappingKey q (prefixDimension + suffixDimension) 1
        tgswLevels prefixDimension errorSampler gadget
        (prefixSecret targetRingKey) targetRingKey := by
  rfl

/-- Zero-message BRK with the same nested ring encryption key. -/
noncomputable def generateZeroBootstrappingKey
    (q prefixDimension suffixDimension tgswLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (gadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    ProbComp (SharedBootstrappingKey q prefixDimension suffixDimension tgswLevels) :=
  Native.generateZeroBootstrappingKey q (prefixDimension + suffixDimension) 1 tgswLevels
    prefixDimension errorSampler gadget ringSecret

/-- Real suffix-only KSK.  Its message secret is independent of its prefix encryption key under
the equivalent prefix/suffix sampling presentation. -/
def generateKeySwitchKey
    (q prefixDimension suffixDimension keySwitchLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (ZMod q))
    (gadget : Fin keySwitchLevels → ZMod q)
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    ProbComp (SharedKeySwitchKey q prefixDimension suffixDimension keySwitchLevels) :=
  Native.generateKeySwitchKey q prefixDimension suffixDimension keySwitchLevels errorSampler
    gadget (suffixSecret ringSecret) (prefixSecret ringSecret)

/-- Zero-message suffix-only KSK under the shared prefix key. -/
def generateZeroKeySwitchKey
    (q prefixDimension suffixDimension keySwitchLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (ZMod q))
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    ProbComp (SharedKeySwitchKey q prefixDimension suffixDimension keySwitchLevels) :=
  Native.generateZeroKeySwitchKey q prefixDimension suffixDimension keySwitchLevels errorSampler
    (prefixSecret ringSecret)

/-- Real shared-randomness cloud key for one fixed master ring key. -/
noncomputable def generateCloudKey
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    ProbComp
      (CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels) := do
  let bootstrappingKey ← generateBootstrappingKey q prefixDimension suffixDimension tgswLevels
    ringErrorSampler tgswGadget ringSecret
  let keySwitchKey ← generateKeySwitchKey q prefixDimension suffixDimension keySwitchLevels
    keySwitchErrorSampler keySwitchGadget ringSecret
  return ⟨bootstrappingKey, keySwitchKey⟩

/-- BRK-zero hybrid retaining the real suffix-only KSK.  This is the comparison endpoint for the
one-key circular BRK problem. -/
noncomputable def generateBootstrapZeroCloudKey
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    ProbComp
      (CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels) := do
  let bootstrappingKey ←
    generateZeroBootstrappingKey q prefixDimension suffixDimension tgswLevels
      ringErrorSampler tgswGadget ringSecret
  let keySwitchKey ← generateKeySwitchKey q prefixDimension suffixDimension keySwitchLevels
    keySwitchErrorSampler keySwitchGadget ringSecret
  return ⟨bootstrappingKey, keySwitchKey⟩

/-- Sample the real one-cycle cloud-key view from one uniform master ring key. -/
noncomputable def realCloudKeyView
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    ProbComp
      (CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels) := do
  let ringSecret ← Native.sampleRingSecret 1 (prefixDimension + suffixDimension)
  generateCloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels
    ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget ringSecret

/-- Explicit one-cycle normal form of the real cloud key.  The BRK source scalar key is
`prefixSecret targetRingKey`, while the BRK encryption/target key is `targetRingKey` itself. -/
theorem realCloudKeyView_eq_prefixUnderMaster
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    realCloudKeyView q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget =
      (do
        let targetRingKey ←
          Native.sampleRingSecret 1 (prefixDimension + suffixDimension)
        let bootstrappingKey ←
          Native.generateBootstrappingKey q (prefixDimension + suffixDimension) 1
            tgswLevels prefixDimension ringErrorSampler tgswGadget
            (prefixSecret targetRingKey) targetRingKey
        let keySwitchKey ←
          generateKeySwitchKey q prefixDimension suffixDimension keySwitchLevels
            keySwitchErrorSampler keySwitchGadget targetRingKey
        return ⟨bootstrappingKey, keySwitchKey⟩) := by
  rfl

/-- Sample the BRK-zero comparison view while retaining the real suffix-only KSK. -/
noncomputable def bootstrapZeroCloudKeyView
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    ProbComp
      (CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels) := do
  let ringSecret ← Native.sampleRingSecret 1 (prefixDimension + suffixDimension)
  generateBootstrapZeroCloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels
    ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget ringSecret

/-- Distinguisher for the shared-randomness one-cycle cloud key. -/
abbrev Adversary
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) :=
  CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels → ProbComp Bool

/-- Real one-cycle BRK game, including the real suffix-only KSK as auxiliary input. -/
noncomputable def realGame
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary :
      Adversary q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    ProbComp Bool :=
  realCloudKeyView q prefixDimension suffixDimension tgswLevels keySwitchLevels
    ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget >>= adversary

/-- Zero-message comparison game for the one-cycle BRK, retaining the real suffix-only KSK. -/
noncomputable def bootstrapZeroGame
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary :
      Adversary q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    ProbComp Bool :=
  bootstrapZeroCloudKeyView q prefixDimension suffixDimension tgswLevels keySwitchLevels
    ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget >>= adversary

/-- Exact distinguishing advantage of the remaining native one-key circular BRK problem. -/
noncomputable def oneCircularAdvantage
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary :
      Adversary q prefixDimension suffixDimension tgswLevels keySwitchLevels) : ℝ :=
  (realGame q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary).boolDistAdvantage
    (bootstrapZeroGame q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary)

/-- Hardness interface for the exact one-key circular BRK distribution. -/
def OneCircularHardAgainst
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (allowed :
      Adversary q prefixDimension suffixDimension tgswLevels keySwitchLevels → Prop)
    (bound : ℝ) : Prop :=
  ∀ adversary, allowed adversary →
    oneCircularAdvantage q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary ≤ bound

/-! A cloud-key distinguisher is enough to state the circular-key problem, but an FHE security
proof subsequently generates challenge ciphertexts and evaluated values with the same master
secret.  The following contextual game therefore gives an arbitrary continuation the master
secret as well as both public evaluation keys.  Equality in this stronger game can be used under
any later secret-dependent encryption or evaluation experiment. -/

/-- Arbitrary secret-dependent continuation after generating the shared evaluation keys. -/
abbrev SecretContinuation
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) :=
  RingBinarySecret 1 (prefixDimension + suffixDimension) →
    SharedBootstrappingKey q prefixDimension suffixDimension tgswLevels →
    SharedKeySwitchKey q prefixDimension suffixDimension keySwitchLevels →
    ProbComp Bool

/-- Real shared-key BRK followed by an arbitrary continuation that may use the master secret. -/
noncomputable def realSecretContinuationGame
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    ProbComp Bool := do
  let ringSecret ← Native.sampleRingSecret 1 (prefixDimension + suffixDimension)
  let bootstrappingKey ←
    generateBootstrappingKey q prefixDimension suffixDimension tgswLevels
      ringErrorSampler tgswGadget ringSecret
  let keySwitchKey ←
    generateKeySwitchKey q prefixDimension suffixDimension keySwitchLevels
      keySwitchErrorSampler keySwitchGadget ringSecret
  continuation ringSecret bootstrappingKey keySwitchKey

/-- Zero-message BRK hybrid with the same secret-dependent continuation and real suffix KSK. -/
noncomputable def bootstrapZeroSecretContinuationGame
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    ProbComp Bool := do
  let ringSecret ← Native.sampleRingSecret 1 (prefixDimension + suffixDimension)
  let bootstrappingKey ←
    generateZeroBootstrappingKey q prefixDimension suffixDimension tgswLevels
      ringErrorSampler tgswGadget ringSecret
  let keySwitchKey ←
    generateKeySwitchKey q prefixDimension suffixDimension keySwitchLevels
      keySwitchErrorSampler keySwitchGadget ringSecret
  continuation ringSecret bootstrappingKey keySwitchKey

/-- Circular BRK advantage in the stronger secret-dependent continuation experiment. -/
noncomputable def secretContinuationAdvantage
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels) : ℝ :=
  (realSecretContinuationGame q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
      continuation).boolDistAdvantage
    (bootstrapZeroSecretContinuationGame q prefixDimension suffixDimension tgswLevels
      keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
      continuation)

/-- Hardness interface for all selected secret-dependent continuations. -/
def SecretContinuationHardAgainst
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (allowed :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels → Prop)
    (bound : ℝ) : Prop :=
  ∀ continuation, allowed continuation →
    secretContinuationAdvantage q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget continuation ≤ bound

/-- Suffix-only KSK sampled from the single uniform master ring key. -/
def masterKeySwitchKeyView
    (q prefixDimension suffixDimension keySwitchLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (ZMod q))
    (gadget : Fin keySwitchLevels → ZMod q) :
    ProbComp (SharedKeySwitchKey q prefixDimension suffixDimension keySwitchLevels) := do
  let ringSecret ← Native.sampleRingSecret 1 (prefixDimension + suffixDimension)
  generateKeySwitchKey q prefixDimension suffixDimension keySwitchLevels errorSampler gadget
    ringSecret

/-- Equivalent KSK sampler with the prefix and suffix drawn independently. -/
def independentKeySwitchKeyView
    (q prefixDimension suffixDimension keySwitchLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (ZMod q))
    (gadget : Fin keySwitchLevels → ZMod q) :
    ProbComp (SharedKeySwitchKey q prefixDimension suffixDimension keySwitchLevels) := do
  let prefixKey ← Native.sampleLweSecret prefixDimension
  let suffixKey ← Native.sampleLweSecret suffixDimension
  Native.generateKeySwitchKey q prefixDimension suffixDimension keySwitchLevels errorSampler
    gadget suffixKey prefixKey

/-- Exact suffix-only native KSK problem in the generic affine-IKSK interface. -/
def sharedKeySwitchProblem
    (q prefixDimension suffixDimension keySwitchLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (ZMod q))
    (gadget : Fin keySwitchLevels → ZMod q) :=
  KeySwitching.sharedIKSKProblem prefixDimension (suffixDimension * keySwitchLevels)
    (Native.sampleLweSecret prefixDimension) embedBinarySecret
    (Native.sampleLweSecret suffixDimension)
    (Native.keySwitchMessages suffixDimension keySwitchLevels gadget) errorSampler

/-- Sampling the KSK from one uniform master key is exactly equivalent to independently drawing
its prefix encryption key and suffix message key. -/
theorem masterKeySwitchKeyView_evalDist_eq_independent
    (q prefixDimension suffixDimension keySwitchLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (ZMod q))
    (gadget : Fin keySwitchLevels → ZMod q) :
    evalDist (masterKeySwitchKeyView q prefixDimension suffixDimension keySwitchLevels
      errorSampler gadget) =
      evalDist (independentKeySwitchKeyView q prefixDimension suffixDimension keySwitchLevels
        errorSampler gadget) := by
  let splitSampler : ProbComp
      (BinarySecret prefixDimension × BinarySecret suffixDimension) := do
    let ringSecret ← Native.sampleRingSecret 1 (prefixDimension + suffixDimension)
    return splitNestedSecret ringSecret
  let independentSampler : ProbComp
      (BinarySecret prefixDimension × BinarySecret suffixDimension) := do
    let prefixKey ← Native.sampleLweSecret prefixDimension
    let suffixKey ← Native.sampleLweSecret suffixDimension
    return (prefixKey, suffixKey)
  let finish := fun keys : BinarySecret prefixDimension × BinarySecret suffixDimension ↦
    Native.generateKeySwitchKey q prefixDimension suffixDimension keySwitchLevels errorSampler
      gadget keys.2 keys.1
  have hsampler : evalDist splitSampler = evalDist independentSampler := by
    exact sampleRingSecret_prefix_suffix_evalDist prefixDimension suffixDimension
  have hbind := FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    hsampler finish
  simpa only [masterKeySwitchKeyView, independentKeySwitchKeyView, generateKeySwitchKey,
    splitSampler, independentSampler, splitNestedSecret, finish, bind_assoc, monad_norm] using hbind

/-- The independently sampled native suffix KSK is exactly the real distribution of the generic
affine-IKSK problem. -/
theorem independentKeySwitchKeyView_evalDist_eq_problem
    (q prefixDimension suffixDimension keySwitchLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (ZMod q))
    (gadget : Fin keySwitchLevels → ZMod q) :
    evalDist (independentKeySwitchKeyView q prefixDimension suffixDimension keySwitchLevels
      errorSampler gadget) =
      evalDist (LearningWithErrors.distr
        (sharedKeySwitchProblem q prefixDimension suffixDimension keySwitchLevels
          errorSampler gadget)) := by
  let prefixes := Native.sampleLweSecret prefixDimension
  let suffixes := Native.sampleLweSecret suffixDimension
  let challenges : ProbComp (Matrix (Fin prefixDimension)
      (Fin (suffixDimension * keySwitchLevels)) (ZMod q)) :=
    $ᵗ Matrix (Fin prefixDimension) (Fin (suffixDimension * keySwitchLevels)) (ZMod q)
  let errors := ProbComp.sampleIID (suffixDimension * keySwitchLevels) errorSampler
  let finish : BinarySecret prefixDimension → BinarySecret suffixDimension →
      Matrix (Fin prefixDimension) (Fin (suffixDimension * keySwitchLevels)) (ZMod q) →
      (Fin (suffixDimension * keySwitchLevels) → ZMod q) →
      ProbComp (SharedKeySwitchKey q prefixDimension suffixDimension keySwitchLevels) :=
    fun prefixKey suffixKey challenge error ↦
      pure (TLWE.batchAssemble (embedBinarySecret prefixKey) challenge
        (Native.keySwitchMessages suffixDimension keySwitchLevels gadget suffixKey) error)
  have hleft :
      independentKeySwitchKeyView q prefixDimension suffixDimension keySwitchLevels
          errorSampler gadget =
        (prefixes >>= fun prefixKey ↦
          suffixes >>= fun suffixKey ↦
          challenges >>= fun challenge ↦
          errors >>= fun error ↦
          finish prefixKey suffixKey challenge error) := by
    simp [independentKeySwitchKeyView, Native.generateKeySwitchKey, TLWE.batchEncrypt,
      prefixes, suffixes, challenges, errors, finish, monad_norm]
  have hright :
      LearningWithErrors.distr
          (sharedKeySwitchProblem q prefixDimension suffixDimension keySwitchLevels
            errorSampler gadget) =
        (challenges >>= fun challenge ↦
          prefixes >>= fun prefixKey ↦
          suffixes >>= fun suffixKey ↦
          errors >>= fun error ↦
          finish prefixKey suffixKey challenge error) := by
    simp [LearningWithErrors.distr, sharedKeySwitchProblem,
      KeySwitching.sharedIKSKProblem, KeySwitching.affineIKSKProblem,
      prefixes, suffixes, challenges, errors, finish, TLWE.batchAssemble,
      add_assoc, monad_norm]
  rw [hleft, hright]
  calc
    _ = evalDist (challenges >>= fun challenge ↦
        prefixes >>= fun prefixKey ↦
        errors >>= fun error ↦
        suffixes >>= fun suffixKey ↦
        finish prefixKey suffixKey challenge error) :=
      Native.KeySwitchSecurity.evalDist_bind_four_reorder prefixes suffixes challenges errors
        finish
    _ = _ := by
      refine evalDist_bind_congr' challenges fun challenge ↦ ?_
      refine evalDist_bind_congr' prefixes fun prefixKey ↦ ?_
      exact evalDist_bind_bind_swap errors suffixes
        (fun error suffixKey ↦ finish prefixKey suffixKey challenge error)

/-- The actual master-key KSK view is exactly the affine-IKSK real distribution. -/
theorem masterKeySwitchKeyView_evalDist_eq_problem
    (q prefixDimension suffixDimension keySwitchLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (ZMod q))
    (gadget : Fin keySwitchLevels → ZMod q) :
    evalDist (masterKeySwitchKeyView q prefixDimension suffixDimension keySwitchLevels
      errorSampler gadget) =
      evalDist (LearningWithErrors.distr
        (sharedKeySwitchProblem q prefixDimension suffixDimension keySwitchLevels
          errorSampler gadget)) :=
  (masterKeySwitchKeyView_evalDist_eq_independent q prefixDimension suffixDimension
      keySwitchLevels errorSampler gadget).trans
    (independentKeySwitchKeyView_evalDist_eq_problem q prefixDimension suffixDimension
      keySwitchLevels errorSampler gadget)

/-- The suffix-only KSK has exactly the advantage of ordinary binary-secret batch LWE under the
shared prefix key. -/
theorem sharedKeySwitchAdvantage_eq_lwe
    (q prefixDimension suffixDimension keySwitchLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (ZMod q))
    (gadget : Fin keySwitchLevels → ZMod q)
    (adversary : LearningWithErrors.Adversary
      (sharedKeySwitchProblem q prefixDimension suffixDimension keySwitchLevels
        errorSampler gadget)) :
    LearningWithErrors.advantage
        (sharedKeySwitchProblem q prefixDimension suffixDimension keySwitchLevels
          errorSampler gadget) adversary =
      LearningWithErrors.advantage
        (FormalProof4FHE.LWE.embeddedBatchProblem prefixDimension
          (suffixDimension * keySwitchLevels)
          (Native.sampleLweSecret prefixDimension) embedBinarySecret errorSampler)
        (KeySwitching.affineIKSKReduction
          (Native.sampleLweSecret suffixDimension)
          (Native.keySwitchMessages suffixDimension keySwitchLevels gadget) adversary) := by
  exact KeySwitching.affineIKSK_advantage_eq_lwe prefixDimension
    (suffixDimension * keySwitchLevels)
    (Native.sampleLweSecret prefixDimension) embedBinarySecret
    (Native.sampleLweSecret suffixDimension)
    (Native.keySwitchMessages suffixDimension keySwitchLevels gadget) errorSampler
    (by simp [Native.sampleLweSecret]) adversary

/-! ## Exact boundary of the remaining one-key BRK -/

/-- A binary vector carrying two independently chosen bits at two selected coordinates.  It is
used to test whether an off-diagonal self-product can be represented by an affine function of a
single complete key. -/
def twoSelectedBits {dimension : ℕ}
    (firstCoordinate secondCoordinate : Fin dimension)
    (first second : Bool) : BinarySecret dimension :=
  fun coordinate ↦
    if coordinate = firstCoordinate then first
    else if coordinate = secondCoordinate then second
    else false

@[simp]
theorem twoSelectedBits_first {dimension : ℕ}
    (firstCoordinate secondCoordinate : Fin dimension)
    (first second : Bool) :
    twoSelectedBits firstCoordinate secondCoordinate first second firstCoordinate = first := by
  simp [twoSelectedBits]

@[simp]
theorem twoSelectedBits_second {dimension : ℕ}
    {firstCoordinate secondCoordinate : Fin dimension}
    (hcoordinates : firstCoordinate ≠ secondCoordinate)
    (first second : Bool) :
    twoSelectedBits firstCoordinate secondCoordinate first second secondCoordinate = second := by
  simp [twoSelectedBits, hcoordinates.symm]

/-- An affine form on the two-coordinate test key keeps only the two selected coefficients. -/
theorem sum_mul_embedBit_twoSelectedBits {R : Type} [CommRing R] {dimension : ℕ}
    (coefficients : Fin dimension → R)
    {firstCoordinate secondCoordinate : Fin dimension}
    (hcoordinates : firstCoordinate ≠ secondCoordinate)
    (first second : Bool) :
    (∑ coordinate, coefficients coordinate *
        embedBit (twoSelectedBits firstCoordinate secondCoordinate first second coordinate)) =
      coefficients firstCoordinate * embedBit first +
        coefficients secondCoordinate * embedBit second := by
  classical
  have hpoint (coordinate : Fin dimension) :
      (embedBit
          (twoSelectedBits firstCoordinate secondCoordinate first second coordinate) : R) =
        embedBit (TGSW.MonomialKDM.singleBit firstCoordinate first coordinate) +
          embedBit (TGSW.MonomialKDM.singleBit secondCoordinate second coordinate) := by
    by_cases hfirst : coordinate = firstCoordinate
    · subst coordinate
      simp [twoSelectedBits, TGSW.MonomialKDM.singleBit, embedBit, hcoordinates]
    · by_cases hsecond : coordinate = secondCoordinate
      · subst coordinate
        simp [twoSelectedBits, TGSW.MonomialKDM.singleBit, embedBit,
          hcoordinates.symm]
      · simp [twoSelectedBits, TGSW.MonomialKDM.singleBit, embedBit, hfirst, hsecond]
  simp_rw [hpoint, mul_add, Finset.sum_add_distrib,
    TGSW.MonomialKDM.sum_mul_embedBit_singleBit]

/-- Affineness of one degree-two product when both factors are coordinates of the same complete
binary key. -/
def BinarySelfProductAffine {R : Type} [CommRing R] {dimension : ℕ}
    (firstCoordinate secondCoordinate : Fin dimension) (gadgetValue : R) : Prop :=
  ∃ coefficients : Fin dimension → R, ∃ constant : R,
    ∀ secret : BinarySecret dimension,
      -(embedBit (secret firstCoordinate) *
          (embedBit (secret secondCoordinate) * gadgetValue)) =
        (∑ coordinate, coefficients coordinate * embedBit (secret coordinate)) + constant

/-- A nonzero off-diagonal Boolean self-product is not affine even though both factors belong to
one key.  Sharing the KSK key therefore removes one heterogeneous key edge, but it does not turn
the native TRGSW mask block into an ordinary affine-RLWE message. -/
theorem offDiagonalBinarySelfProduct_not_affine {R : Type} [CommRing R] {dimension : ℕ}
    {firstCoordinate secondCoordinate : Fin dimension}
    {gadgetValue : R}
    (hcoordinates : firstCoordinate ≠ secondCoordinate)
    (hgadget : gadgetValue ≠ 0) :
    ¬ BinarySelfProductAffine firstCoordinate secondCoordinate gadgetValue := by
  rintro ⟨coefficients, constant, haffine⟩
  apply TGSW.MonomialKDM.not_binaryScaledProductAffine hgadget
  refine ⟨coefficients firstCoordinate, coefficients secondCoordinate, constant, ?_⟩
  intro first second
  simpa only [twoSelectedBits_first,
    twoSelectedBits_second hcoordinates,
    sum_mul_embedBit_twoSelectedBits coefficients hcoordinates] using
      (haffine (twoSelectedBits firstCoordinate secondCoordinate first second))

/-- On a diagonal coordinate the apparent degree-two Boolean self-product collapses exactly to
an affine term because binary keys satisfy `s² = s`. -/
theorem diagonalBinarySelfProduct_eq_affine {R : Type} [CommRing R]
    (bit : Bool) (gadgetValue : R) :
    -(embedBit bit * (embedBit bit * gadgetValue)) =
      -(embedBit bit * gadgetValue) := by
  cases bit <;> simp [embedBit]

/-! ## An unconditional security-only endpoint with uniform ring errors -/

/-- Remove a fixed TGSW gadget translation. -/
def removeGadget {R : Type} [Ring R] {dimension levels : ℕ}
    (gadget : Fin levels → R) (message : R)
    (ciphertext : TGSW.Ciphertext R dimension levels) :
    TGSW.Ciphertext R dimension levels :=
  (ciphertext.1 - TGSW.gadgetMaskShift gadget message,
    ciphertext.2 - TGSW.gadgetBodyShift gadget message)

@[simp]
theorem removeGadget_addGadget {R : Type} [Ring R] {dimension levels : ℕ}
    (gadget : Fin levels → R) (message : R)
    (ciphertext : TGSW.Ciphertext R dimension levels) :
    removeGadget gadget message (TGSW.addGadget gadget message ciphertext) = ciphertext := by
  apply Prod.ext
  · funext coordinate row
    simp [removeGadget, TGSW.addGadget]
  · funext row
    simp [removeGadget, TGSW.addGadget]

@[simp]
theorem addGadget_removeGadget {R : Type} [Ring R] {dimension levels : ℕ}
    (gadget : Fin levels → R) (message : R)
    (ciphertext : TGSW.Ciphertext R dimension levels) :
    TGSW.addGadget gadget message (removeGadget gadget message ciphertext) = ciphertext := by
  apply Prod.ext
  · funext coordinate row
    simp [removeGadget, TGSW.addGadget]
  · funext row
    simp [removeGadget, TGSW.addGadget]

/-- Adding a fixed TGSW gadget matrix is a permutation of the complete ciphertext carrier. -/
theorem addGadget_bijective {R : Type} [Ring R] {dimension levels : ℕ}
    (gadget : Fin levels → R) (message : R) :
    Function.Bijective
      (TGSW.addGadget (dimension := dimension) gadget message) := by
  refine Function.bijective_iff_has_inverse.mpr
    ⟨removeGadget gadget message, ?_, ?_⟩
  · exact removeGadget_addGadget gadget message
  · exact addGadget_removeGadget gadget message

/-- A fixed-message TLWE batch with uniform errors is exactly uniform on its complete public
transcript, for every fixed encryption key. -/
theorem batchEncrypt_uniformError_evalDist {R : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (dimension samples : ℕ) (secret : Fin dimension → R)
    (message : Fin samples → R) :
    evalDist (TLWE.batchEncrypt dimension samples ($ᵗ R) secret message) =
      evalDist ($ᵗ (TLWE.BatchCiphertext R dimension samples)) := by
  let Challenge := Matrix (Fin dimension) (Fin samples) R
  let Output := Fin samples → R
  let challenges : ProbComp Challenge := $ᵗ Challenge
  let errors : ProbComp Output := ProbComp.sampleIID samples ($ᵗ R)
  have hErrors : evalDist errors = evalDist ($ᵗ Output) := by
    simpa [errors, Output] using
      (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
        (alpha := R) samples)
  let shift : Challenge → Output := fun challenge ↦
    vecMul secret challenge + message
  have hShift (challenge : Challenge) :
      evalDist (($ᵗ Output) >>= fun error ↦
        pure (challenge, shift challenge + error)) =
        evalDist (($ᵗ Output) >>= fun output ↦ pure (challenge, output)) := by
    have h := evalDist_bind_bijective_add_right_uniform
      (α := Output) (β := Output) id Function.bijective_id (shift challenge)
      (fun output ↦ (pure (challenge, output) : ProbComp (Challenge × Output)))
    change evalDist (($ᵗ Output) >>= fun error ↦
        pure (challenge, error + shift challenge)) =
      evalDist (($ᵗ Output) >>= fun output ↦ pure (challenge, output)) at h
    rw [show (fun error : Output ↦
        (pure (challenge, shift challenge + error) :
          ProbComp (Challenge × Output))) =
      fun error ↦ pure (challenge, error + shift challenge) by
        funext error
        rw [add_comm]]
    exact h
  have uniformProduct :
      ($ᵗ (Challenge × Output) : ProbComp (Challenge × Output)) =
        Prod.mk <$> ($ᵗ Challenge) <*> ($ᵗ Output) := rfl
  calc
    evalDist (TLWE.batchEncrypt dimension samples ($ᵗ R) secret message) =
        evalDist (challenges >>= fun challenge ↦
          errors >>= fun error ↦ pure (challenge, shift challenge + error)) := by
      simp [TLWE.batchEncrypt, TLWE.batchAssemble, challenges, errors, shift,
        Challenge, Output, monad_norm]
    _ = evalDist (challenges >>= fun challenge ↦
        ($ᵗ Output) >>= fun error ↦ pure (challenge, shift challenge + error)) := by
      refine evalDist_bind_congr' challenges fun challenge ↦ ?_
      exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        hErrors (fun error ↦ pure (challenge, shift challenge + error))
    _ = evalDist (challenges >>= fun challenge ↦
        ($ᵗ Output) >>= fun output ↦ pure (challenge, output)) := by
      exact evalDist_bind_congr' challenges hShift
    _ = evalDist ($ᵗ (Challenge × Output)) := by
      rw [uniformProduct]
      simp [challenges, monad_norm]
    _ = evalDist ($ᵗ (TLWE.BatchCiphertext R dimension samples)) := by
      rfl

/-- With uniform row errors, a native TGSW encryption of any fixed message is exactly uniform.
This is a security-only fact: uniform errors do not provide a useful TFHE correctness margin. -/
theorem tgswEncrypt_uniformError_evalDist {R : Type}
    [CommRing R] [Fintype R] [DecidableEq R] [SampleableType R]
    (dimension levels : ℕ) (secret : Fin dimension → R)
    (gadget : Fin levels → R) (message : R) :
    evalDist (TGSW.encrypt dimension levels ($ᵗ R) secret gadget message) =
      evalDist ($ᵗ (TGSW.Ciphertext R dimension levels)) := by
  unfold TGSW.encrypt
  calc
    _ = evalDist (($ᵗ (TGSW.Ciphertext R dimension levels)) >>= fun homogeneous ↦
        pure (TGSW.addGadget gadget message homogeneous)) :=
      FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
        (batchEncrypt_uniformError_evalDist dimension (TGSW.rowCount dimension levels)
          secret 0)
        (fun homogeneous ↦ pure (TGSW.addGadget gadget message homogeneous))
    _ = evalDist ($ᵗ (TGSW.Ciphertext R dimension levels)) := by
      simpa only [map_eq_bind_pure_comp, Function.comp_def] using
        (evalDist_map_bijective_uniform_cross
          (α := TGSW.Ciphertext R dimension levels)
          (β := TGSW.Ciphertext R dimension levels)
          (TGSW.addGadget gadget message)
          (addGadget_bijective gadget message))

/-- The complete shared-key BRK is exactly uniform when every native ring-row error is uniform. -/
theorem generateBootstrappingKey_uniformError_evalDist
    (q prefixDimension suffixDimension tgswLevels : ℕ) [NeZero q]
    (gadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    evalDist (generateBootstrappingKey q prefixDimension suffixDimension tgswLevels
      ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))) gadget ringSecret) =
      evalDist ($ᵗ (SharedBootstrappingKey q prefixDimension suffixDimension tgswLevels)) := by
  letI : CommRing (RLWE.Rq q (prefixDimension + suffixDimension)) :=
    LatticeCrypto.vectorNegacyclicRing_instCommRing
      (ZMod q) (prefixDimension + suffixDimension)
  unfold generateBootstrappingKey Native.generateBootstrappingKey
  calc
    _ = evalDist (Fin.mOfFn prefixDimension fun _ ↦
        $ᵗ (TGSW.Ciphertext (RLWE.Rq q (prefixDimension + suffixDimension)) 1
          tgswLevels)) := by
      apply FormalProof4FHE.FiniteProduct.evalDist_fin_mOfFn_congr
      intro coordinate
      exact tgswEncrypt_uniformError_evalDist 1 tgswLevels
        (embedRingSecret q ringSecret) gadget
        (embedConstantBit q (prefixDimension + suffixDimension)
          (prefixSecret ringSecret coordinate))
    _ = evalDist ($ᵗ
        (SharedBootstrappingKey q prefixDimension suffixDimension tgswLevels)) := by
      simpa only [ProbComp.sampleIID] using
        (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
          (alpha := TGSW.Ciphertext
            (RLWE.Rq q (prefixDimension + suffixDimension)) 1 tgswLevels)
          prefixDimension)

/-- The zero-message shared-key BRK is also exactly uniform under uniform ring errors. -/
theorem generateZeroBootstrappingKey_uniformError_evalDist
    (q prefixDimension suffixDimension tgswLevels : ℕ) [NeZero q]
    (gadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    evalDist (generateZeroBootstrappingKey q prefixDimension suffixDimension tgswLevels
      ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))) gadget ringSecret) =
      evalDist ($ᵗ (SharedBootstrappingKey q prefixDimension suffixDimension tgswLevels)) := by
  let rqCommRing : CommRing (RLWE.Rq q (prefixDimension + suffixDimension)) :=
    LatticeCrypto.vectorNegacyclicRing_instCommRing
      (ZMod q) (prefixDimension + suffixDimension)
  letI := rqCommRing
  unfold generateZeroBootstrappingKey Native.generateZeroBootstrappingKey TGSW.encryptZero
  calc
    _ = evalDist (Fin.mOfFn prefixDimension fun _ ↦
        $ᵗ (TGSW.Ciphertext (RLWE.Rq q (prefixDimension + suffixDimension)) 1
          tgswLevels)) := by
      apply FormalProof4FHE.FiniteProduct.evalDist_fin_mOfFn_congr
      intro _
      let zeroMessage : RLWE.Rq q (prefixDimension + suffixDimension) :=
        @OfNat.ofNat (RLWE.Rq q (prefixDimension + suffixDimension)) 0
          (@Zero.toOfNat0 (RLWE.Rq q (prefixDimension + suffixDimension))
            (@MulZeroClass.toZero (RLWE.Rq q (prefixDimension + suffixDimension))
              (@instMulZeroClassOfSemiring
                (RLWE.Rq q (prefixDimension + suffixDimension)) rqCommRing.toSemiring)))
      change evalDist (TGSW.encrypt 1 tgswLevels
          ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension)))
          (embedRingSecret q ringSecret) gadget zeroMessage) = _
      exact tgswEncrypt_uniformError_evalDist 1 tgswLevels
        (embedRingSecret q ringSecret) gadget zeroMessage
    _ = evalDist ($ᵗ
        (SharedBootstrappingKey q prefixDimension suffixDimension tgswLevels)) := by
      simpa only [ProbComp.sampleIID] using
        (FormalProof4FHE.FiniteProduct.evalDist_sampleIID_uniform
          (alpha := TGSW.Ciphertext
            (RLWE.Rq q (prefixDimension + suffixDimension)) 1 tgswLevels)
          prefixDimension)

/-- Under uniform ring errors, real and zero-message shared-key BRKs have identical laws even for
the same fixed master key. -/
theorem generateBootstrappingKey_uniformError_evalDist_eq_zero
    (q prefixDimension suffixDimension tgswLevels : ℕ) [NeZero q]
    (gadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    evalDist (generateBootstrappingKey q prefixDimension suffixDimension tgswLevels
      ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))) gadget ringSecret) =
    evalDist (generateZeroBootstrappingKey q prefixDimension suffixDimension tgswLevels
      ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))) gadget ringSecret) :=
  (generateBootstrappingKey_uniformError_evalDist q prefixDimension suffixDimension
    tgswLevels gadget ringSecret).trans
      (generateZeroBootstrappingKey_uniformError_evalDist q prefixDimension suffixDimension
        tgswLevels gadget ringSecret).symm

/-- Uniform ring errors erase the complete real/zero BRK distinction while retaining the exact
same master-key-correlated suffix KSK. -/
theorem realCloudKeyView_uniformRingError_evalDist_eq_bootstrapZero
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    evalDist (realCloudKeyView q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))) keySwitchErrorSampler
      tgswGadget keySwitchGadget) =
    evalDist (bootstrapZeroCloudKeyView q prefixDimension suffixDimension tgswLevels
      keySwitchLevels ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension)))
      keySwitchErrorSampler tgswGadget keySwitchGadget) := by
  unfold realCloudKeyView bootstrapZeroCloudKeyView generateCloudKey
    generateBootstrapZeroCloudKey
  refine evalDist_bind_congr'
    (Native.sampleRingSecret 1 (prefixDimension + suffixDimension)) fun ringSecret ↦ ?_
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (generateBootstrappingKey_uniformError_evalDist_eq_zero q prefixDimension
      suffixDimension tgswLevels tgswGadget ringSecret)
    (fun bootstrappingKey ↦
      generateKeySwitchKey q prefixDimension suffixDimension keySwitchLevels
          keySwitchErrorSampler keySwitchGadget ringSecret >>= fun keySwitchKey ↦
        pure (CloudKey.mk bootstrappingKey keySwitchKey))

/-- Every adversary has identical output distributions in the real and BRK-zero one-cycle games
when the ring errors are uniform. -/
theorem realGame_uniformRingError_evalDist_eq_bootstrapZero
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary :
      Adversary q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    evalDist (realGame q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))) keySwitchErrorSampler
      tgswGadget keySwitchGadget adversary) =
    evalDist (bootstrapZeroGame q prefixDimension suffixDimension tgswLevels
      keySwitchLevels ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension)))
      keySwitchErrorSampler tgswGadget keySwitchGadget adversary) := by
  unfold realGame bootstrapZeroGame
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (realCloudKeyView_uniformRingError_evalDist_eq_bootstrapZero q prefixDimension
      suffixDimension tgswLevels keySwitchLevels keySwitchErrorSampler tgswGadget
      keySwitchGadget)
    adversary

/-- Uniform ring errors erase the BRK message even inside an arbitrary continuation which is
given the same master secret and the correlated suffix KSK.  In particular, the continuation may
generate challenge ciphertexts, invoke public evaluation, or reveal any other function of the
master secret after the evaluation key has been sampled. -/
theorem realSecretContinuationGame_uniformRingError_evalDist_eq_bootstrapZero
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    evalDist (realSecretContinuationGame q prefixDimension suffixDimension tgswLevels
      keySwitchLevels ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension)))
      keySwitchErrorSampler tgswGadget keySwitchGadget continuation) =
    evalDist (bootstrapZeroSecretContinuationGame q prefixDimension suffixDimension
      tgswLevels keySwitchLevels ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension)))
      keySwitchErrorSampler tgswGadget keySwitchGadget continuation) := by
  unfold realSecretContinuationGame bootstrapZeroSecretContinuationGame
  refine evalDist_bind_congr'
    (Native.sampleRingSecret 1 (prefixDimension + suffixDimension)) fun ringSecret ↦ ?_
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (generateBootstrappingKey_uniformError_evalDist_eq_zero q prefixDimension
      suffixDimension tgswLevels tgswGadget ringSecret)
    (fun bootstrappingKey ↦
      generateKeySwitchKey q prefixDimension suffixDimension keySwitchLevels
          keySwitchErrorSampler keySwitchGadget ringSecret >>= fun keySwitchKey ↦
        continuation ringSecret bootstrappingKey keySwitchKey)

/-- The contextual one-cycle advantage is exactly zero under uniform ring errors. -/
theorem secretContinuationAdvantage_uniformRingError_eq_zero
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    secretContinuationAdvantage q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))) keySwitchErrorSampler
      tgswGadget keySwitchGadget continuation = 0 := by
  unfold secretContinuationAdvantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
    (realSecretContinuationGame_uniformRingError_evalDist_eq_bootstrapZero q
      prefixDimension suffixDimension tgswLevels keySwitchLevels keySwitchErrorSampler
      tgswGadget keySwitchGadget continuation) true]
  simp

/-- Uniform ring errors give contextual one-cycle security against every continuation class. -/
theorem secretContinuationHardAgainst_uniformRingError
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (allowed :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels → Prop) :
    SecretContinuationHardAgainst q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))) keySwitchErrorSampler
      tgswGadget keySwitchGadget allowed 0 := by
  intro continuation _
  rw [secretContinuationAdvantage_uniformRingError_eq_zero]

/-- Exact one-circular security of the shared-randomness cloud-key distribution under uniform
ring errors.  This discharges the circular game without an RLWE or KDM assumption, but is only a
security endpoint: uniform decryption error is incompatible with ordinary TFHE correctness. -/
theorem oneCircularAdvantage_uniformRingError_eq_zero
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary :
      Adversary q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    oneCircularAdvantage q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))) keySwitchErrorSampler
      tgswGadget keySwitchGadget adversary = 0 := by
  unfold oneCircularAdvantage ProbComp.boolDistAdvantage
  rw [evalDist_ext_iff.mp
    (realGame_uniformRingError_evalDist_eq_bootstrapZero q prefixDimension suffixDimension
      tgswLevels keySwitchLevels keySwitchErrorSampler tgswGadget keySwitchGadget
      adversary) true]
  simp

/-- Uniform ring errors give a zero one-circular bound against every chosen adversary class. -/
theorem oneCircularHardAgainst_uniformRingError
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (allowed :
      Adversary q prefixDimension suffixDimension tgswLevels keySwitchLevels → Prop) :
    OneCircularHardAgainst q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))) keySwitchErrorSampler
      tgswGadget keySwitchGadget allowed 0 := by
  intro adversary _
  rw [oneCircularAdvantage_uniformRingError_eq_zero]

/-! ## Quantitative transfer from a near-uniform ring-error sampler -/

/-- Replacing the ring-error sampler in the real shared-key BRK costs once per native TGSW row. -/
theorem tvDist_generateBootstrappingKey_le
    (q prefixDimension suffixDimension tgswLevels : ℕ) [NeZero q]
    (left right : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (gadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    tvDist
        (generateBootstrappingKey q prefixDimension suffixDimension tgswLevels
          left gadget ringSecret)
        (generateBootstrappingKey q prefixDimension suffixDimension tgswLevels
          right gadget ringSecret) ≤
      (SamplerReplacement.bootstrappingErrorCount 1 tgswLevels prefixDimension : ℝ) *
        tvDist left right := by
  simpa only [generateBootstrappingKey] using
    (SamplerReplacement.tvDist_generateBootstrappingKey_le q
      (prefixDimension + suffixDimension) 1 tgswLevels prefixDimension
      left right gadget (prefixSecret ringSecret) ringSecret)

/-- The zero-message shared-key BRK has the same sampler-replacement cost. -/
theorem tvDist_generateZeroBootstrappingKey_le
    (q prefixDimension suffixDimension tgswLevels : ℕ) [NeZero q]
    (left right : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (gadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    tvDist
        (generateZeroBootstrappingKey q prefixDimension suffixDimension tgswLevels
          left gadget ringSecret)
        (generateZeroBootstrappingKey q prefixDimension suffixDimension tgswLevels
          right gadget ringSecret) ≤
      (SamplerReplacement.bootstrappingErrorCount 1 tgswLevels prefixDimension : ℝ) *
        tvDist left right := by
  simpa only [generateZeroBootstrappingKey] using
    (SamplerReplacement.tvDist_generateZeroBootstrappingKey_le q
      (prefixDimension + suffixDimension) 1 tgswLevels prefixDimension
      left right gadget ringSecret)

/-- Fixed-master real cloud-key replacement bound. -/
theorem tvDist_generateCloudKey_ringError_le
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (left right : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    tvDist
        (generateCloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels
          left keySwitchErrorSampler tgswGadget keySwitchGadget ringSecret)
        (generateCloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels
          right keySwitchErrorSampler tgswGadget keySwitchGadget ringSecret) ≤
      (SamplerReplacement.bootstrappingErrorCount 1 tgswLevels prefixDimension : ℝ) *
        tvDist left right := by
  unfold generateCloudKey
  let finish := fun
      (bootstrappingKey :
        SharedBootstrappingKey q prefixDimension suffixDimension tgswLevels) ↦
    generateKeySwitchKey q prefixDimension suffixDimension keySwitchLevels
        keySwitchErrorSampler keySwitchGadget ringSecret >>= fun keySwitchKey ↦
      pure (CloudKey.mk bootstrappingKey keySwitchKey)
  change tvDist
      (generateBootstrappingKey q prefixDimension suffixDimension tgswLevels
        left tgswGadget ringSecret >>= finish)
      (generateBootstrappingKey q prefixDimension suffixDimension tgswLevels
        right tgswGadget ringSecret >>= finish) ≤ _
  exact (tvDist_bind_right_le finish _ _).trans
    (tvDist_generateBootstrappingKey_le q prefixDimension suffixDimension tgswLevels
      left right tgswGadget ringSecret)

/-- Real cloud-key view replacement bound after averaging the same uniform master key. -/
theorem tvDist_realCloudKeyView_ringError_le
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (left right : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    tvDist
        (realCloudKeyView q prefixDimension suffixDimension tgswLevels keySwitchLevels
          left keySwitchErrorSampler tgswGadget keySwitchGadget)
        (realCloudKeyView q prefixDimension suffixDimension tgswLevels keySwitchLevels
          right keySwitchErrorSampler tgswGadget keySwitchGadget) ≤
      (SamplerReplacement.bootstrappingErrorCount 1 tgswLevels prefixDimension : ℝ) *
        tvDist left right := by
  unfold realCloudKeyView
  exact tvDist_bind_left_le_const' (m := ProbComp)
    (Native.sampleRingSecret 1 (prefixDimension + suffixDimension)) _ _
    ((SamplerReplacement.bootstrappingErrorCount 1 tgswLevels prefixDimension : ℝ) *
      tvDist left right)
    (fun ringSecret ↦
      tvDist_generateCloudKey_ringError_le q prefixDimension suffixDimension
        tgswLevels keySwitchLevels left right keySwitchErrorSampler tgswGadget
        keySwitchGadget ringSecret)

/-- Fixed-master BRK-zero cloud-key replacement bound. -/
theorem tvDist_generateBootstrapZeroCloudKey_ringError_le
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (left right : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    tvDist
        (generateBootstrapZeroCloudKey q prefixDimension suffixDimension tgswLevels
          keySwitchLevels left keySwitchErrorSampler tgswGadget keySwitchGadget ringSecret)
        (generateBootstrapZeroCloudKey q prefixDimension suffixDimension tgswLevels
          keySwitchLevels right keySwitchErrorSampler tgswGadget keySwitchGadget ringSecret) ≤
      (SamplerReplacement.bootstrappingErrorCount 1 tgswLevels prefixDimension : ℝ) *
        tvDist left right := by
  unfold generateBootstrapZeroCloudKey
  let finish := fun
      (bootstrappingKey :
        SharedBootstrappingKey q prefixDimension suffixDimension tgswLevels) ↦
    generateKeySwitchKey q prefixDimension suffixDimension keySwitchLevels
        keySwitchErrorSampler keySwitchGadget ringSecret >>= fun keySwitchKey ↦
      pure (CloudKey.mk bootstrappingKey keySwitchKey)
  change tvDist
      (generateZeroBootstrappingKey q prefixDimension suffixDimension tgswLevels
        left tgswGadget ringSecret >>= finish)
      (generateZeroBootstrappingKey q prefixDimension suffixDimension tgswLevels
        right tgswGadget ringSecret >>= finish) ≤ _
  exact (tvDist_bind_right_le finish _ _).trans
    (tvDist_generateZeroBootstrappingKey_le q prefixDimension suffixDimension tgswLevels
      left right tgswGadget ringSecret)

/-- BRK-zero cloud-key view replacement bound after averaging the same master key. -/
theorem tvDist_bootstrapZeroCloudKeyView_ringError_le
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (left right : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    tvDist
        (bootstrapZeroCloudKeyView q prefixDimension suffixDimension tgswLevels
          keySwitchLevels left keySwitchErrorSampler tgswGadget keySwitchGadget)
        (bootstrapZeroCloudKeyView q prefixDimension suffixDimension tgswLevels
          keySwitchLevels right keySwitchErrorSampler tgswGadget keySwitchGadget) ≤
      (SamplerReplacement.bootstrappingErrorCount 1 tgswLevels prefixDimension : ℝ) *
        tvDist left right := by
  unfold bootstrapZeroCloudKeyView
  exact tvDist_bind_left_le_const' (m := ProbComp)
    (Native.sampleRingSecret 1 (prefixDimension + suffixDimension)) _ _
    ((SamplerReplacement.bootstrappingErrorCount 1 tgswLevels prefixDimension : ℝ) *
      tvDist left right)
    (fun ringSecret ↦
      tvDist_generateBootstrapZeroCloudKey_ringError_le q prefixDimension
        suffixDimension tgswLevels keySwitchLevels left right keySwitchErrorSampler
        tgswGadget keySwitchGadget ringSecret)

/-- Replacing only the BRK row-error sampler in the real one-cycle game inherits the complete
BRK draw count; the shared KSK and arbitrary adversarial postprocessing add no loss. -/
theorem tvDist_realGame_ringError_le
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (left right : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary :
      Adversary q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    tvDist
        (realGame q prefixDimension suffixDimension tgswLevels keySwitchLevels
          left keySwitchErrorSampler tgswGadget keySwitchGadget adversary)
        (realGame q prefixDimension suffixDimension tgswLevels keySwitchLevels
          right keySwitchErrorSampler tgswGadget keySwitchGadget adversary) ≤
      (SamplerReplacement.bootstrappingErrorCount 1 tgswLevels prefixDimension : ℝ) *
        tvDist left right := by
  unfold realGame
  exact (tvDist_bind_right_le adversary _ _).trans
    (tvDist_realCloudKeyView_ringError_le q prefixDimension suffixDimension
      tgswLevels keySwitchLevels left right keySwitchErrorSampler tgswGadget
      keySwitchGadget)

/-- The same replacement theorem for the BRK-zero comparison game. -/
theorem tvDist_bootstrapZeroGame_ringError_le
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (left right : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary :
      Adversary q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    tvDist
        (bootstrapZeroGame q prefixDimension suffixDimension tgswLevels keySwitchLevels
          left keySwitchErrorSampler tgswGadget keySwitchGadget adversary)
        (bootstrapZeroGame q prefixDimension suffixDimension tgswLevels keySwitchLevels
          right keySwitchErrorSampler tgswGadget keySwitchGadget adversary) ≤
      (SamplerReplacement.bootstrappingErrorCount 1 tgswLevels prefixDimension : ℝ) *
        tvDist left right := by
  unfold bootstrapZeroGame
  exact (tvDist_bind_right_le adversary _ _).trans
    (tvDist_bootstrapZeroCloudKeyView_ringError_le q prefixDimension suffixDimension
      tgswLevels keySwitchLevels left right keySwitchErrorSampler tgswGadget
      keySwitchGadget)

/-- Ring-error replacement remains valid for an arbitrary continuation that receives the master
secret, real suffix KSK, and real BRK.  This is the contextual form needed by later FHE games. -/
theorem tvDist_realSecretContinuationGame_ringError_le
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (left right : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    tvDist
        (realSecretContinuationGame q prefixDimension suffixDimension tgswLevels
          keySwitchLevels left keySwitchErrorSampler tgswGadget keySwitchGadget continuation)
        (realSecretContinuationGame q prefixDimension suffixDimension tgswLevels
          keySwitchLevels right keySwitchErrorSampler tgswGadget keySwitchGadget continuation) ≤
      (SamplerReplacement.bootstrappingErrorCount 1 tgswLevels prefixDimension : ℝ) *
        tvDist left right := by
  unfold realSecretContinuationGame
  exact tvDist_bind_left_le_const' (m := ProbComp)
    (Native.sampleRingSecret 1 (prefixDimension + suffixDimension)) _ _
    ((SamplerReplacement.bootstrappingErrorCount 1 tgswLevels prefixDimension : ℝ) *
      tvDist left right)
    (fun ringSecret ↦ by
      let finish := fun
          (bootstrappingKey :
            SharedBootstrappingKey q prefixDimension suffixDimension tgswLevels) ↦
        generateKeySwitchKey q prefixDimension suffixDimension keySwitchLevels
            keySwitchErrorSampler keySwitchGadget ringSecret >>= fun keySwitchKey ↦
          continuation ringSecret bootstrappingKey keySwitchKey
      change tvDist
          (generateBootstrappingKey q prefixDimension suffixDimension tgswLevels
            left tgswGadget ringSecret >>= finish)
          (generateBootstrappingKey q prefixDimension suffixDimension tgswLevels
            right tgswGadget ringSecret >>= finish) ≤ _
      exact (tvDist_bind_right_le finish _ _).trans
        (tvDist_generateBootstrappingKey_le q prefixDimension suffixDimension
          tgswLevels left right tgswGadget ringSecret))

/-- The same contextual replacement theorem for the zero-message BRK hybrid. -/
theorem tvDist_bootstrapZeroSecretContinuationGame_ringError_le
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (left right : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    tvDist
        (bootstrapZeroSecretContinuationGame q prefixDimension suffixDimension tgswLevels
          keySwitchLevels left keySwitchErrorSampler tgswGadget keySwitchGadget continuation)
        (bootstrapZeroSecretContinuationGame q prefixDimension suffixDimension tgswLevels
          keySwitchLevels right keySwitchErrorSampler tgswGadget keySwitchGadget continuation) ≤
      (SamplerReplacement.bootstrappingErrorCount 1 tgswLevels prefixDimension : ℝ) *
        tvDist left right := by
  unfold bootstrapZeroSecretContinuationGame
  exact tvDist_bind_left_le_const' (m := ProbComp)
    (Native.sampleRingSecret 1 (prefixDimension + suffixDimension)) _ _
    ((SamplerReplacement.bootstrappingErrorCount 1 tgswLevels prefixDimension : ℝ) *
      tvDist left right)
    (fun ringSecret ↦ by
      let finish := fun
          (bootstrappingKey :
            SharedBootstrappingKey q prefixDimension suffixDimension tgswLevels) ↦
        generateKeySwitchKey q prefixDimension suffixDimension keySwitchLevels
            keySwitchErrorSampler keySwitchGadget ringSecret >>= fun keySwitchKey ↦
          continuation ringSecret bootstrappingKey keySwitchKey
      change tvDist
          (generateZeroBootstrappingKey q prefixDimension suffixDimension tgswLevels
            left tgswGadget ringSecret >>= finish)
          (generateZeroBootstrappingKey q prefixDimension suffixDimension tgswLevels
            right tgswGadget ringSecret >>= finish) ≤ _
      exact (tvDist_bind_right_le finish _ _).trans
        (tvDist_generateZeroBootstrappingKey_le q prefixDimension suffixDimension
          tgswLevels left right tgswGadget ringSecret))

/-- Contextual security-only near-uniform theorem.  It applies inside any subsequent experiment
that uses the same secret and both public evaluation keys. -/
theorem secretContinuationAdvantage_le_uniformRingError
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    secretContinuationAdvantage q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget continuation ≤
      2 * (SamplerReplacement.bootstrappingErrorCount 1 tgswLevels prefixDimension : ℝ) *
        tvDist ringErrorSampler
          ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))) := by
  let uniformRingError : ProbComp
      (RLWE.Rq q (prefixDimension + suffixDimension)) :=
    $ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))
  let realActual := realSecretContinuationGame q prefixDimension suffixDimension
    tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget
    keySwitchGadget continuation
  let realUniform := realSecretContinuationGame q prefixDimension suffixDimension
    tgswLevels keySwitchLevels uniformRingError keySwitchErrorSampler tgswGadget
    keySwitchGadget continuation
  let zeroActual := bootstrapZeroSecretContinuationGame q prefixDimension suffixDimension
    tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget
    keySwitchGadget continuation
  let zeroUniform := bootstrapZeroSecretContinuationGame q prefixDimension suffixDimension
    tgswLevels keySwitchLevels uniformRingError keySwitchErrorSampler tgswGadget
    keySwitchGadget continuation
  let replacementBound :=
    (SamplerReplacement.bootstrappingErrorCount 1 tgswLevels prefixDimension : ℝ) *
      tvDist ringErrorSampler uniformRingError
  have hReal : tvDist realActual realUniform ≤ replacementBound := by
    exact tvDist_realSecretContinuationGame_ringError_le q prefixDimension
      suffixDimension tgswLevels keySwitchLevels ringErrorSampler uniformRingError
      keySwitchErrorSampler tgswGadget keySwitchGadget continuation
  have hZero : tvDist zeroActual zeroUniform ≤ replacementBound := by
    exact tvDist_bootstrapZeroSecretContinuationGame_ringError_le q prefixDimension
      suffixDimension tgswLevels keySwitchLevels ringErrorSampler uniformRingError
      keySwitchErrorSampler tgswGadget keySwitchGadget continuation
  have hUniform : evalDist realUniform = evalDist zeroUniform := by
    exact realSecretContinuationGame_uniformRingError_evalDist_eq_bootstrapZero q
      prefixDimension suffixDimension tgswLevels keySwitchLevels keySwitchErrorSampler
      tgswGadget keySwitchGadget continuation
  have hUniformToActual : tvDist realUniform zeroActual = tvDist zeroUniform zeroActual := by
    unfold tvDist
    rw [hUniform]
  calc
    secretContinuationAdvantage q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget continuation ≤
        tvDist realActual zeroActual := by
      unfold secretContinuationAdvantage realActual zeroActual
      exact abs_probOutput_toReal_sub_le_tvDist _ _
    _ ≤ tvDist realActual realUniform + tvDist realUniform zeroActual :=
      tvDist_triangle _ _ _
    _ = tvDist realActual realUniform + tvDist zeroUniform zeroActual := by
      rw [hUniformToActual]
    _ ≤ replacementBound + replacementBound := by
      exact add_le_add hReal (by simpa [tvDist_comm] using hZero)
    _ = 2 * (SamplerReplacement.bootstrappingErrorCount 1 tgswLevels
          prefixDimension : ℝ) *
        tvDist ringErrorSampler
          ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))) := by
      simp [replacementBound, uniformRingError]
      ring

/-- A certified one-draw distance from uniform gives a concrete contextual security theorem for
the complete selected class of later secret-dependent encryption/evaluation experiments. -/
theorem secretContinuationHardAgainst_of_ringError_close_uniform
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (allowed :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels → Prop)
    (errorDistanceBound : ℝ)
    (herror : tvDist ringErrorSampler
      ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))) ≤ errorDistanceBound) :
    SecretContinuationHardAgainst q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget allowed
      (2 * (SamplerReplacement.bootstrappingErrorCount 1 tgswLevels
        prefixDimension : ℝ) * errorDistanceBound) := by
  intro continuation _
  calc
    secretContinuationAdvantage q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget continuation ≤
      2 * (SamplerReplacement.bootstrappingErrorCount 1 tgswLevels
        prefixDimension : ℝ) *
          tvDist ringErrorSampler
            ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))) :=
      secretContinuationAdvantage_le_uniformRingError q prefixDimension suffixDimension
        tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget
        keySwitchGadget continuation
    _ ≤ 2 * (SamplerReplacement.bootstrappingErrorCount 1 tgswLevels
        prefixDimension : ℝ) * errorDistanceBound := by
      gcongr

/-- Security-only near-uniform theorem.  The exact shared-key one-circular advantage is at most
twice the complete BRK row count times the one-draw distance of the ring-error sampler from
uniform.  A centered-binomial or discrete-Gaussian instantiation may use this theorem after
proving that finite-modulus distance; no circular or RLWE assumption is then needed. -/
theorem oneCircularAdvantage_le_uniformRingError
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary :
      Adversary q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    oneCircularAdvantage q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary ≤
      2 * (SamplerReplacement.bootstrappingErrorCount 1 tgswLevels prefixDimension : ℝ) *
        tvDist ringErrorSampler
          ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))) := by
  let uniformRingError : ProbComp
      (RLWE.Rq q (prefixDimension + suffixDimension)) :=
    $ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))
  let realActual := realGame q prefixDimension suffixDimension tgswLevels keySwitchLevels
    ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary
  let realUniform := realGame q prefixDimension suffixDimension tgswLevels keySwitchLevels
    uniformRingError keySwitchErrorSampler tgswGadget keySwitchGadget adversary
  let zeroActual := bootstrapZeroGame q prefixDimension suffixDimension tgswLevels
    keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary
  let zeroUniform := bootstrapZeroGame q prefixDimension suffixDimension tgswLevels
    keySwitchLevels uniformRingError keySwitchErrorSampler tgswGadget keySwitchGadget adversary
  let replacementBound :=
    (SamplerReplacement.bootstrappingErrorCount 1 tgswLevels prefixDimension : ℝ) *
      tvDist ringErrorSampler uniformRingError
  have hReal : tvDist realActual realUniform ≤ replacementBound := by
    exact tvDist_realGame_ringError_le q prefixDimension suffixDimension tgswLevels
      keySwitchLevels ringErrorSampler uniformRingError keySwitchErrorSampler
      tgswGadget keySwitchGadget adversary
  have hZero : tvDist zeroActual zeroUniform ≤ replacementBound := by
    exact tvDist_bootstrapZeroGame_ringError_le q prefixDimension suffixDimension
      tgswLevels keySwitchLevels ringErrorSampler uniformRingError keySwitchErrorSampler
      tgswGadget keySwitchGadget adversary
  have hUniform : evalDist realUniform = evalDist zeroUniform := by
    exact realGame_uniformRingError_evalDist_eq_bootstrapZero q prefixDimension
      suffixDimension tgswLevels keySwitchLevels keySwitchErrorSampler tgswGadget
      keySwitchGadget adversary
  have hUniformToActual : tvDist realUniform zeroActual = tvDist zeroUniform zeroActual := by
    unfold tvDist
    rw [hUniform]
  calc
    oneCircularAdvantage q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary ≤
        tvDist realActual zeroActual := by
      unfold oneCircularAdvantage realActual zeroActual
      exact abs_probOutput_toReal_sub_le_tvDist _ _
    _ ≤ tvDist realActual realUniform + tvDist realUniform zeroActual :=
      tvDist_triangle _ _ _
    _ = tvDist realActual realUniform + tvDist zeroUniform zeroActual := by
      rw [hUniformToActual]
    _ ≤ replacementBound + replacementBound := by
      exact add_le_add hReal (by simpa [tvDist_comm] using hZero)
    _ = 2 * (SamplerReplacement.bootstrappingErrorCount 1 tgswLevels
          prefixDimension : ℝ) *
        tvDist ringErrorSampler
          ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))) := by
      simp [replacementBound, uniformRingError]
      ring

/-- A certified one-draw distance from uniform gives a concrete one-circular hardness bound for
every selected adversary class. -/
theorem oneCircularHardAgainst_of_ringError_close_uniform
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (allowed :
      Adversary q prefixDimension suffixDimension tgswLevels keySwitchLevels → Prop)
    (errorDistanceBound : ℝ)
    (herror : tvDist ringErrorSampler
      ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))) ≤ errorDistanceBound) :
    OneCircularHardAgainst q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget allowed
      (2 * (SamplerReplacement.bootstrappingErrorCount 1 tgswLevels
        prefixDimension : ℝ) * errorDistanceBound) := by
  intro adversary _
  calc
    oneCircularAdvantage q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary ≤
      2 * (SamplerReplacement.bootstrappingErrorCount 1 tgswLevels
        prefixDimension : ℝ) *
          tvDist ringErrorSampler
            ($ᵗ (RLWE.Rq q (prefixDimension + suffixDimension))) :=
      oneCircularAdvantage_le_uniformRingError q prefixDimension suffixDimension
        tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget
        keySwitchGadget adversary
    _ ≤ 2 * (SamplerReplacement.bootstrappingErrorCount 1 tgswLevels
        prefixDimension : ℝ) * errorDistanceBound := by
      gcongr

/-- Degree-two coordinates of the BRK are self-monomials of one master ring key. -/
def selfCrossMonomial
    (q prefixDimension suffixDimension : ℕ)
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension))
    (coordinate : Fin prefixDimension) :
    Fin 1 → RLWE.Rq q (prefixDimension + suffixDimension) :=
  TGSW.MonomialKDM.crossMonomial (embedRingSecret q ringSecret)
    (embedConstantBit q (prefixDimension + suffixDimension)
      (prefixSecret ringSecret coordinate))

/-- Direct monomial presentation of the one-key BRK. -/
noncomputable def generateSelfMonomialBootstrappingKey
    (q prefixDimension suffixDimension tgswLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (gadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    ProbComp (SharedBootstrappingKey q prefixDimension suffixDimension tgswLevels) :=
  Fin.mOfFn prefixDimension fun coordinate ↦
    TGSW.MonomialKDM.expandedDirectEncrypt 1 tgswLevels errorSampler
      (embedRingSecret q ringSecret) gadget
      (embedConstantBit q (prefixDimension + suffixDimension)
        (prefixSecret ringSecret coordinate))
      (selfCrossMonomial q prefixDimension suffixDimension ringSecret coordinate)

/-- The native shared-key BRK and its one-key degree-two monomial presentation have exactly the
same output distribution. -/
theorem generateBootstrappingKey_evalDist_eq_selfMonomial
    (q prefixDimension suffixDimension tgswLevels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (gadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    evalDist (generateBootstrappingKey q prefixDimension suffixDimension tgswLevels
      errorSampler gadget ringSecret) =
      evalDist (generateSelfMonomialBootstrappingKey q prefixDimension suffixDimension
        tgswLevels errorSampler gadget ringSecret) := by
  unfold generateBootstrappingKey
  rw [Native.BootstrapSecurity.generateBootstrappingKey_evalDist_eq_direct]
  congr 1
  unfold Native.BootstrapSecurity.generateDirectBootstrappingKey
    generateSelfMonomialBootstrappingKey selfCrossMonomial
  congr 1
  funext coordinate
  exact TGSW.MonomialKDM.directEncrypt_eq_expandedDirectEncrypt 1 tgswLevels errorSampler
    (embedRingSecret q ringSecret) gadget
    (embedConstantBit q (prefixDimension + suffixDimension)
      (prefixSecret ringSecret coordinate))

/-- Cloud-key view with the BRK written explicitly through one-key degree-two monomials. -/
noncomputable def selfMonomialCloudKeyView
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    ProbComp
      (CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels) := do
  let ringSecret ← Native.sampleRingSecret 1 (prefixDimension + suffixDimension)
  let bootstrappingKey ←
    generateSelfMonomialBootstrappingKey q prefixDimension suffixDimension tgswLevels
      ringErrorSampler tgswGadget ringSecret
  let keySwitchKey ← generateKeySwitchKey q prefixDimension suffixDimension keySwitchLevels
    keySwitchErrorSampler keySwitchGadget ringSecret
  return ⟨bootstrappingKey, keySwitchKey⟩

/-- The actual shared-key cloud view is exactly the one-key monomial view.  Thus shared
randomness removes the heterogeneous cross-key edge but does not erase the native quadratic
self-monomials. -/
theorem realCloudKeyView_evalDist_eq_selfMonomial
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    evalDist (realCloudKeyView q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget) =
      evalDist (selfMonomialCloudKeyView q prefixDimension suffixDimension tgswLevels
        keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget
          keySwitchGadget) := by
  unfold realCloudKeyView generateCloudKey selfMonomialCloudKeyView
  refine evalDist_bind_congr'
    (Native.sampleRingSecret 1 (prefixDimension + suffixDimension)) fun ringSecret ↦ ?_
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (generateBootstrappingKey_evalDist_eq_selfMonomial q prefixDimension suffixDimension
      tgswLevels ringErrorSampler tgswGadget ringSecret)
    (fun bootstrappingKey ↦
      generateKeySwitchKey q prefixDimension suffixDimension keySwitchLevels
          keySwitchErrorSampler keySwitchGadget ringSecret >>= fun keySwitchKey ↦
        pure (CloudKey.mk bootstrappingKey keySwitchKey))

end

end FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle
