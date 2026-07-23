/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.Native

/-!
# Native TFHE Encryption and One-Time IND-CPA Games

TFHE is a symmetric-key FHE scheme: the adversary receives a public cloud key, while fresh scalar
TLWE ciphertexts are generated with the hidden scalar key.  Consequently its IND-CPA game is not
the ordinary public-key game supplied by `AsymmEncAlg`.  This module defines the appropriate
one-time experiment directly.

The adversary first receives the native cloud key, chooses two messages, and then receives one
fresh scalar TLWE encryption under the same hidden key that occurs in the evaluation-key cycle.
The experiment is packaged as a `Circular.Continuation`, so the real, bootstrap-zero, and
all-zero-message cloud-key games are instances of the checked continuation-level circular hybrid.

This file proves the scheme-independent end-to-end inequality. Security of the all-zero-message
cloud-key game is the ordinary binary-secret LWE obligation; contextual replacement of the native
structured TRGSW bootstrapping key is left explicit here. `TFHE.BootstrappingSecurity` subsequently
identifies that term exactly with direct bilinear cross-key module-LWE KDM.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Encryption

/-- Fresh scalar finite-modulus TLWE encryption used for TFHE inputs and outputs. -/
def encrypt {Message : Type} (q dimension : ℕ) [NeZero q]
    (errorSampler : ProbComp (ZMod q)) (encode : Message → ZMod q)
    (secret : BinarySecret dimension) (message : Message) :
    ProbComp (ScalarCiphertext q dimension) :=
  TLWE.encrypt errorSampler (embedBinarySecret secret) (encode message)

/-- Scalar TLWE decryption: compute the phase and apply the chosen message decoder. -/
def decrypt {Message : Type} {q dimension : ℕ}
    (decode : ZMod q → Option Message) (secret : BinarySecret dimension)
    (ciphertext : ScalarCiphertext q dimension) : Option Message :=
  decode (TLWE.phase (embedBinarySecret secret) ciphertext)

/-- Deterministic correctness equation for an assembled scalar TLWE row. -/
@[simp]
theorem decrypt_assemble {Message : Type} {q dimension : ℕ}
    (decode : ZMod q → Option Message) (secret : BinarySecret dimension)
    (mask : Fin dimension → ZMod q) (message error : ZMod q) :
    decrypt decode secret
        (TLWE.assemble (embedBinarySecret secret) mask message error) =
      decode (message + error) := by
  simp [decrypt]

/-- A one-time TFHE adversary: choose messages after seeing the cloud key, retain arbitrary state,
then distinguish the scalar TLWE challenge. -/
structure OneTimeAdversary
    (Message CloudKey Ciphertext : Type) where
  State : Type
  chooseMessages : CloudKey → ProbComp (Message × Message × State)
  distinguish : State → Ciphertext → ProbComp Bool

section Games

variable {Message : Type}
  {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]

abbrev NativeCloudKey
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) :=
  Native.CloudKey q degree ringRank tgswLevels lweDimension keySwitchLevels

abbrev NativeAdversary (Message : Type)
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) :=
  OneTimeAdversary Message
    (NativeCloudKey q degree ringRank tgswLevels lweDimension keySwitchLevels)
    (ScalarCiphertext q lweDimension)

/-- Downstream one-time IND-CPA experiment for already-generated secrets and evaluation keys. -/
def oneTimeContinuation
    (inputErrorSampler : ProbComp (ZMod q)) (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (Native.BootstrappingKey q degree ringRank tgswLevels lweDimension)
      (Native.KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels) :=
  fun lweSecret _ bootstrapKey keySwitchKey ↦ do
    let bit ← $ᵗ Bool
    let (message₀, message₁, state) ←
      adversary.chooseMessages ⟨bootstrapKey, keySwitchKey⟩
    let ciphertext ← encrypt q lweDimension inputErrorSampler encode lweSecret
      (if bit then message₀ else message₁)
    let guess ← adversary.distinguish state ciphertext
    return (bit == guess)

/-- Honest one-time TFHE IND-CPA game with the native real cloud key. -/
noncomputable def realGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ProbComp Bool :=
  Circular.realContinuationGame
    (Native.nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    (oneTimeContinuation inputErrorSampler encode adversary)

/-- First IND-CPA circular hybrid: bootstrapping-key messages are zero, key-switch messages real. -/
noncomputable def bootstrapZeroGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ProbComp Bool :=
  Circular.bootstrapZeroContinuationGame
    (Native.nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    (oneTimeContinuation inputErrorSampler encode adversary)

/-- Base IND-CPA hybrid in which both native evaluation-key components encrypt zero. -/
noncomputable def zeroCloudGame
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ProbComp Bool :=
  Circular.zeroContinuationGame
    (Native.nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    (oneTimeContinuation inputErrorSampler encode adversary)

/-- Signed winning advantage relative to a fair guess. -/
noncomputable def signedAdvantage (game : ProbComp Bool) : ℝ :=
  (Pr[= true | game]).toReal - 1 / 2

/-- Contextual circular cost of replacing the complete cloud key inside the IND-CPA experiment. -/
noncomputable def circularAdvantage
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ℝ :=
  (realGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget encode adversary).boolDistAdvantage
  (zeroCloudGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget encode adversary)

/-- Contextual native TRGSW bootstrapping-key replacement cost in the IND-CPA experiment. -/
noncomputable def bootstrapReplacementAdvantage
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ℝ :=
  (realGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget encode adversary).boolDistAdvantage
  (bootstrapZeroGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget encode adversary)

/-- Contextual direct-TLWE key-switch replacement cost in the IND-CPA experiment. -/
noncomputable def keySwitchReplacementAdvantage
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) : ℝ :=
  (bootstrapZeroGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget encode adversary).boolDistAdvantage
  (zeroCloudGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
    tgswGadget keySwitchGadget encode adversary)

/-- The adaptive IND-CPA circular cost splits into the native bootstrap and key-switch hops. -/
theorem circularAdvantage_le_replacements
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    circularAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary ≤
      bootstrapReplacementAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget encode adversary +
        keySwitchReplacementAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget encode adversary := by
  exact Circular.continuationCircularAdvantage_le_replacements
    (Native.nativeCycleSpec q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    (oneTimeContinuation inputErrorSampler encode adversary)

/-- Replacing the native cloud key and then proving the zero-cloud-key game bounds the honest
one-time signed advantage. -/
theorem abs_signedAdvantage_real_le_circular_add_zero
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    |signedAdvantage (realGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      circularAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget encode adversary +
        |signedAdvantage (zeroCloudGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget encode adversary)| := by
  unfold signedAdvantage circularAdvantage ProbComp.boolDistAdvantage
  exact abs_sub_le
    (Pr[= true | realGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget encode adversary]).toReal
    (Pr[= true | zeroCloudGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
      tgswGadget keySwitchGadget encode adversary]).toReal
    (1 / 2 : ℝ)

/-- Fully expanded conditional TFHE one-time IND-CPA bound.  The remaining three terms correspond
exactly to structured bootstrap replacement, direct key-switch replacement, and base TLWE security
with zero-message evaluation keys. -/
theorem abs_signedAdvantage_real_le_bootstrap_add_keySwitch_add_zero
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler inputErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (encode : Message → ZMod q)
    (adversary : NativeAdversary Message q degree ringRank tgswLevels
      lweDimension keySwitchLevels) :
    |signedAdvantage (realGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
        tgswGadget keySwitchGadget encode adversary)| ≤
      bootstrapReplacementAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget encode adversary +
        keySwitchReplacementAdvantage ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget encode adversary +
        |signedAdvantage (zeroCloudGame ringErrorSampler keySwitchErrorSampler inputErrorSampler
          tgswGadget keySwitchGadget encode adversary)| := by
  have hOuter := abs_signedAdvantage_real_le_circular_add_zero
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
    encode adversary
  have hCircular := circularAdvantage_le_replacements
    ringErrorSampler keySwitchErrorSampler inputErrorSampler tgswGadget keySwitchGadget
    encode adversary
  linarith

end Games

end FormalProof4FHE.TFHE.Encryption
