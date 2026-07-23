/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.AffineCircular

/-!
# TFHE Evaluation-Key Circular Security

This module gives the native TFHE key cycle a precise game boundary.  A TFHE cloud key contains
two heterogeneous components:

* the bootstrapping key encrypts the coefficients of a TLWE key under a TRLWE key, using the
  structured TGSW/TRGSW format;
* the key-switching key encrypts gadget multiples of the coefficient-extracted TRLWE key under the
  original TLWE key, using direct TLWE samples.

The two components therefore form a directed cycle.  `CycleSpec` records exactly that dependency
graph while leaving concrete ciphertext layouts abstract.  The real cloud-key view, its two
replacement hybrids, and the all-zero-message view are executable `ProbComp` games.  The main
theorems prove:

1. real-to-zero circular advantage is at most the sum of the two replacement-hop advantages; and
2. full payload indistinguishability with the real cloud key follows from circular replacement on
   each payload branch plus payload security in the zero-message cloud-key game.

These are composition theorems, not an unconditional reduction of native TRGSW circular security
to RLWE. `TFHE.BootstrappingSecurity` later reparameterizes the native hop exactly as direct
gadget-phase module-LWE rows; hardness of its bilinear cross-key messages remains the explicit
TFHE circular-security premise. For direct fresh affine TLWE rows, `LWE.AffineCircular` supplies
an exact ordinary-LWE reduction, but affine security must not be silently applied to those
bilinear messages.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.Circular

/-- The dependency graph and samplers for TFHE's heterogeneous two-key evaluation-key cycle.

`bootstrapReal lweSecret ringSecret` models TRGSW encryptions of the TLWE-key coefficients under
the TRLWE key.  `keySwitchReal extractedSecret lweSecret` models TLWE encryptions of gadget
multiples of the extracted TRLWE-key coefficients under the TLWE key.  The corresponding `Zero`
fields retain the native ciphertext formats while replacing all encrypted messages by zero. -/
structure CycleSpec
    (LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey : Type) where
  sampleLweSecret : ProbComp LweSecret
  sampleRingSecret : ProbComp RingSecret
  extractRingSecret : RingSecret → ExtractedRingSecret
  bootstrapReal : LweSecret → RingSecret → ProbComp BootstrapKey
  bootstrapZero : RingSecret → ProbComp BootstrapKey
  keySwitchReal : ExtractedRingSecret → LweSecret → ProbComp KeySwitchKey
  keySwitchZero : LweSecret → ProbComp KeySwitchKey

/-- The public view delivered to a TFHE adversary: an arbitrary challenge payload together with
the two components of the cloud key. -/
structure View (Payload BootstrapKey KeySwitchKey : Type) where
  payload : Payload
  bootstrapKey : BootstrapKey
  keySwitchKey : KeySwitchKey

/-- An adversary against a TFHE cloud-key or payload game. -/
abbrev Adversary (Payload BootstrapKey KeySwitchKey : Type) :=
  View Payload BootstrapKey KeySwitchKey → ProbComp Bool

section Games

variable {LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey Payload : Type}

/-- Sample the native real evaluation-key view.  The payload sampler can model a TFHE challenge
ciphertext or can be `evaluationKeyOnlyPayload` when only the cloud key is exposed. -/
def realView
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (payload : LweSecret → RingSecret → ProbComp Payload) :
    ProbComp (View Payload BootstrapKey KeySwitchKey) := do
  let lweSecret ← spec.sampleLweSecret
  let ringSecret ← spec.sampleRingSecret
  let bootstrapKey ← spec.bootstrapReal lweSecret ringSecret
  let keySwitchKey ← spec.keySwitchReal (spec.extractRingSecret ringSecret) lweSecret
  let challenge ← payload lweSecret ringSecret
  return ⟨challenge, bootstrapKey, keySwitchKey⟩

/-- First replacement hybrid: the bootstrapping key encrypts zero, while the real key-switching
key still closes the key cycle in the other direction. -/
def bootstrapZeroView
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (payload : LweSecret → RingSecret → ProbComp Payload) :
    ProbComp (View Payload BootstrapKey KeySwitchKey) := do
  let lweSecret ← spec.sampleLweSecret
  let ringSecret ← spec.sampleRingSecret
  let bootstrapKey ← spec.bootstrapZero ringSecret
  let keySwitchKey ← spec.keySwitchReal (spec.extractRingSecret ringSecret) lweSecret
  let challenge ← payload lweSecret ringSecret
  return ⟨challenge, bootstrapKey, keySwitchKey⟩

/-- All-zero-message evaluation-key view.  Ciphertext randomness, encryption keys, dimensions, and
native formats are retained; only the messages carried by both evaluation-key components change. -/
def zeroView
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (payload : LweSecret → RingSecret → ProbComp Payload) :
    ProbComp (View Payload BootstrapKey KeySwitchKey) := do
  let lweSecret ← spec.sampleLweSecret
  let ringSecret ← spec.sampleRingSecret
  let bootstrapKey ← spec.bootstrapZero ringSecret
  let keySwitchKey ← spec.keySwitchZero lweSecret
  let challenge ← payload lweSecret ringSecret
  return ⟨challenge, bootstrapKey, keySwitchKey⟩

/-- Payload sampler for the cloud-key-only circular-security game. -/
def evaluationKeyOnlyPayload : LweSecret → RingSecret → ProbComp Unit :=
  fun _ _ ↦ pure ()

/-- Invoke an adversary on a real TFHE evaluation-key view. -/
def realGame
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (payload : LweSecret → RingSecret → ProbComp Payload)
    (adversary : Adversary Payload BootstrapKey KeySwitchKey) : ProbComp Bool :=
  realView spec payload >>= adversary

/-- Invoke an adversary after replacing the bootstrapping-key messages by zero. -/
def bootstrapZeroGame
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (payload : LweSecret → RingSecret → ProbComp Payload)
    (adversary : Adversary Payload BootstrapKey KeySwitchKey) : ProbComp Bool :=
  bootstrapZeroView spec payload >>= adversary

/-- Invoke an adversary on the all-zero-message evaluation-key view. -/
def zeroGame
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (payload : LweSecret → RingSecret → ProbComp Payload)
    (adversary : Adversary Payload BootstrapKey KeySwitchKey) : ProbComp Bool :=
  zeroView spec payload >>= adversary

/-- Contextual circular advantage for replacing both native evaluation-key components by
zero-message ciphertexts. -/
noncomputable def circularAdvantage
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (payload : LweSecret → RingSecret → ProbComp Payload)
    (adversary : Adversary Payload BootstrapKey KeySwitchKey) : ℝ :=
  (realGame spec payload adversary).boolDistAdvantage
    (zeroGame spec payload adversary)

/-- Cost of replacing the native bootstrapping-key messages while retaining the real
key-switching key as auxiliary input.  This is the intrinsically circular TRGSW hop. -/
noncomputable def bootstrapReplacementAdvantage
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (payload : LweSecret → RingSecret → ProbComp Payload)
    (adversary : Adversary Payload BootstrapKey KeySwitchKey) : ℝ :=
  (realGame spec payload adversary).boolDistAdvantage
    (bootstrapZeroGame spec payload adversary)

/-- Cost of replacing key-switching-key messages after the bootstrapping-key messages have already
been zeroed.  A concrete direct-TLWE instantiation can target an ordinary-LWE reduction here. -/
noncomputable def keySwitchReplacementAdvantage
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (payload : LweSecret → RingSecret → ProbComp Payload)
    (adversary : Adversary Payload BootstrapKey KeySwitchKey) : ℝ :=
  (bootstrapZeroGame spec payload adversary).boolDistAdvantage
    (zeroGame spec payload adversary)

/-- The native TFHE circular replacement splits into exactly two heterogeneous game hops. -/
theorem circularAdvantage_le_replacements
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (payload : LweSecret → RingSecret → ProbComp Payload)
    (adversary : Adversary Payload BootstrapKey KeySwitchKey) :
    circularAdvantage spec payload adversary ≤
      bootstrapReplacementAdvantage spec payload adversary +
        keySwitchReplacementAdvantage spec payload adversary := by
  exact ProbComp.boolDistAdvantage_triangle
    (realGame spec payload adversary)
    (bootstrapZeroGame spec payload adversary)
    (zeroGame spec payload adversary)

/-- Circular security against a selected class of adversaries, with an explicit concrete bound. -/
def CircularHardAgainst
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (payload : LweSecret → RingSecret → ProbComp Payload)
    (allowed : Adversary Payload BootstrapKey KeySwitchKey → Prop)
    (bound : ℝ) : Prop :=
  ∀ adversary, allowed adversary → circularAdvantage spec payload adversary ≤ bound

/-- Bounds for the two replacement hops imply a bound for the complete circular view. -/
theorem circularHardAgainst_of_replacementBounds
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (payload : LweSecret → RingSecret → ProbComp Payload)
    (allowed : Adversary Payload BootstrapKey KeySwitchKey → Prop)
    (bootstrapBound keySwitchBound : ℝ)
    (hBootstrap : ∀ adversary, allowed adversary →
      bootstrapReplacementAdvantage spec payload adversary ≤ bootstrapBound)
    (hKeySwitch : ∀ adversary, allowed adversary →
      keySwitchReplacementAdvantage spec payload adversary ≤ keySwitchBound) :
    CircularHardAgainst spec payload allowed (bootstrapBound + keySwitchBound) := by
  intro adversary hadversary
  calc
    circularAdvantage spec payload adversary ≤
        bootstrapReplacementAdvantage spec payload adversary +
          keySwitchReplacementAdvantage spec payload adversary :=
      circularAdvantage_le_replacements spec payload adversary
    _ ≤ bootstrapBound + keySwitchBound :=
      add_le_add (hBootstrap adversary hadversary) (hKeySwitch adversary hadversary)

end Games

section PayloadComposition

variable {LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey Payload : Type}

/-- Distinguishing two payload branches while retaining the native real TFHE evaluation key.  This
is the generic endpoint used by an IND-CPA instantiation. -/
noncomputable def fullAdvantage
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (leftPayload rightPayload : LweSecret → RingSecret → ProbComp Payload)
    (adversary : Adversary Payload BootstrapKey KeySwitchKey) : ℝ :=
  (realGame spec leftPayload adversary).boolDistAdvantage
    (realGame spec rightPayload adversary)

/-- Distinguishing the same two payload branches after both evaluation-key components have had
their messages replaced by zero.  This is the base-security obligation left after circular hops. -/
noncomputable def zeroKeyPayloadAdvantage
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (leftPayload rightPayload : LweSecret → RingSecret → ProbComp Payload)
    (adversary : Adversary Payload BootstrapKey KeySwitchKey) : ℝ :=
  (zeroGame spec leftPayload adversary).boolDistAdvantage
    (zeroGame spec rightPayload adversary)

/-- **TFHE circular-security composition theorem.**  Security with the real cloud key reduces to
circular replacement on each challenge branch and payload security with a zero-message cloud key.
The two circular terms are both necessary because the final hybrid restores the real cloud key. -/
theorem fullAdvantage_le_circular_add_zeroKey_add_circular
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (leftPayload rightPayload : LweSecret → RingSecret → ProbComp Payload)
    (adversary : Adversary Payload BootstrapKey KeySwitchKey) :
    fullAdvantage spec leftPayload rightPayload adversary ≤
      circularAdvantage spec leftPayload adversary +
        zeroKeyPayloadAdvantage spec leftPayload rightPayload adversary +
          circularAdvantage spec rightPayload adversary := by
  let realLeft := realGame spec leftPayload adversary
  let zeroLeft := zeroGame spec leftPayload adversary
  let zeroRight := zeroGame spec rightPayload adversary
  let realRight := realGame spec rightPayload adversary
  have firstHop := ProbComp.boolDistAdvantage_triangle realLeft zeroLeft realRight
  have remainingHops := ProbComp.boolDistAdvantage_triangle zeroLeft zeroRight realRight
  have reverseRight : zeroRight.boolDistAdvantage realRight =
      realRight.boolDistAdvantage zeroRight := by
    unfold ProbComp.boolDistAdvantage
    rw [abs_sub_comm]
  unfold fullAdvantage circularAdvantage zeroKeyPayloadAdvantage
  change realLeft.boolDistAdvantage realRight ≤
    realLeft.boolDistAdvantage zeroLeft +
      zeroLeft.boolDistAdvantage zeroRight +
        realRight.boolDistAdvantage zeroRight
  calc
    realLeft.boolDistAdvantage realRight ≤
        realLeft.boolDistAdvantage zeroLeft +
          zeroLeft.boolDistAdvantage realRight := firstHop
    _ ≤ realLeft.boolDistAdvantage zeroLeft +
        (zeroLeft.boolDistAdvantage zeroRight +
          zeroRight.boolDistAdvantage realRight) :=
      add_le_add_right remainingHops _
    _ = realLeft.boolDistAdvantage zeroLeft +
        zeroLeft.boolDistAdvantage zeroRight +
          realRight.boolDistAdvantage zeroRight := by rw [reverseRight, add_assoc]

/-- Fully expanded TFHE hybrid bound, isolating the bootstrapping and key-switching replacement
obligations on both payload branches. -/
theorem fullAdvantage_le_replacements_add_zeroKey_add_replacements
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (leftPayload rightPayload : LweSecret → RingSecret → ProbComp Payload)
    (adversary : Adversary Payload BootstrapKey KeySwitchKey) :
    fullAdvantage spec leftPayload rightPayload adversary ≤
      bootstrapReplacementAdvantage spec leftPayload adversary +
        keySwitchReplacementAdvantage spec leftPayload adversary +
          zeroKeyPayloadAdvantage spec leftPayload rightPayload adversary +
            bootstrapReplacementAdvantage spec rightPayload adversary +
              keySwitchReplacementAdvantage spec rightPayload adversary := by
  have hFull := fullAdvantage_le_circular_add_zeroKey_add_circular
    spec leftPayload rightPayload adversary
  have hLeft := circularAdvantage_le_replacements spec leftPayload adversary
  have hRight := circularAdvantage_le_replacements spec rightPayload adversary
  linarith

/-- Full real-cloud-key payload security against a selected adversary class. -/
def FullHardAgainst
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (leftPayload rightPayload : LweSecret → RingSecret → ProbComp Payload)
    (allowed : Adversary Payload BootstrapKey KeySwitchKey → Prop)
    (bound : ℝ) : Prop :=
  ∀ adversary, allowed adversary →
    fullAdvantage spec leftPayload rightPayload adversary ≤ bound

/-- Base payload security in the all-zero-message evaluation-key hybrid. -/
def ZeroKeyPayloadHardAgainst
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (leftPayload rightPayload : LweSecret → RingSecret → ProbComp Payload)
    (allowed : Adversary Payload BootstrapKey KeySwitchKey → Prop)
    (bound : ℝ) : Prop :=
  ∀ adversary, allowed adversary →
    zeroKeyPayloadAdvantage spec leftPayload rightPayload adversary ≤ bound

/-- Conditional end-to-end security theorem: two contextual circular assumptions and security of
the payload challenge with zero-message evaluation keys imply security with the native real TFHE
cloud key. -/
theorem fullHardAgainst_of_circular_and_zeroKey
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (leftPayload rightPayload : LweSecret → RingSecret → ProbComp Payload)
    (allowed : Adversary Payload BootstrapKey KeySwitchKey → Prop)
    (leftCircularBound zeroKeyBound rightCircularBound : ℝ)
    (hLeft : CircularHardAgainst spec leftPayload allowed leftCircularBound)
    (hZero : ZeroKeyPayloadHardAgainst spec leftPayload rightPayload allowed zeroKeyBound)
    (hRight : CircularHardAgainst spec rightPayload allowed rightCircularBound) :
    FullHardAgainst spec leftPayload rightPayload allowed
      (leftCircularBound + zeroKeyBound + rightCircularBound) := by
  intro adversary hadversary
  calc
    fullAdvantage spec leftPayload rightPayload adversary ≤
        circularAdvantage spec leftPayload adversary +
          zeroKeyPayloadAdvantage spec leftPayload rightPayload adversary +
            circularAdvantage spec rightPayload adversary :=
      fullAdvantage_le_circular_add_zeroKey_add_circular
        spec leftPayload rightPayload adversary
    _ ≤ leftCircularBound + zeroKeyBound + rightCircularBound :=
      add_le_add
        (add_le_add (hLeft adversary hadversary) (hZero adversary hadversary))
        (hRight adversary hadversary)

end PayloadComposition

section DependentContinuation

variable {LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey : Type}

/-- A continuation that may inspect both hidden secrets and both generated evaluation-key
components.  The secrets are supplied only to the experiment, not necessarily to the adversary
inside the continuation.  This interface supports adaptive IND-CPA games in which the adversary
first sees the cloud key and then receives an encryption under the same hidden TLWE key. -/
abbrev Continuation (LweSecret RingSecret BootstrapKey KeySwitchKey : Type) :=
  LweSecret → RingSecret → BootstrapKey → KeySwitchKey → ProbComp Bool

/-- Execute a secret-dependent continuation after generating the real native key cycle. -/
def realContinuationGame
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (continuation : Continuation LweSecret RingSecret BootstrapKey KeySwitchKey) :
    ProbComp Bool := do
  let lweSecret ← spec.sampleLweSecret
  let ringSecret ← spec.sampleRingSecret
  let bootstrapKey ← spec.bootstrapReal lweSecret ringSecret
  let keySwitchKey ← spec.keySwitchReal (spec.extractRingSecret ringSecret) lweSecret
  continuation lweSecret ringSecret bootstrapKey keySwitchKey

/-- Continuation game after replacing only the bootstrapping-key messages by zero. -/
def bootstrapZeroContinuationGame
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (continuation : Continuation LweSecret RingSecret BootstrapKey KeySwitchKey) :
    ProbComp Bool := do
  let lweSecret ← spec.sampleLweSecret
  let ringSecret ← spec.sampleRingSecret
  let bootstrapKey ← spec.bootstrapZero ringSecret
  let keySwitchKey ← spec.keySwitchReal (spec.extractRingSecret ringSecret) lweSecret
  continuation lweSecret ringSecret bootstrapKey keySwitchKey

/-- Alternative first hybrid: keep the real bootstrapping key and replace only the key-switch
messages by zero.  This exposes the opposite ordering of the same two-edge key cycle. -/
def keySwitchZeroContinuationGame
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (continuation : Continuation LweSecret RingSecret BootstrapKey KeySwitchKey) :
    ProbComp Bool := do
  let lweSecret ← spec.sampleLweSecret
  let ringSecret ← spec.sampleRingSecret
  let bootstrapKey ← spec.bootstrapReal lweSecret ringSecret
  let keySwitchKey ← spec.keySwitchZero lweSecret
  continuation lweSecret ringSecret bootstrapKey keySwitchKey

/-- Continuation game after replacing both evaluation-key message families by zero. -/
def zeroContinuationGame
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (continuation : Continuation LweSecret RingSecret BootstrapKey KeySwitchKey) :
    ProbComp Bool := do
  let lweSecret ← spec.sampleLweSecret
  let ringSecret ← spec.sampleRingSecret
  let bootstrapKey ← spec.bootstrapZero ringSecret
  let keySwitchKey ← spec.keySwitchZero lweSecret
  continuation lweSecret ringSecret bootstrapKey keySwitchKey

/-- Contextual circular advantage for a complete secret-dependent downstream experiment. -/
noncomputable def continuationCircularAdvantage
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (continuation : Continuation LweSecret RingSecret BootstrapKey KeySwitchKey) : ℝ :=
  (realContinuationGame spec continuation).boolDistAdvantage
    (zeroContinuationGame spec continuation)

/-- Bootstrapping-key replacement cost in the presence of the real key-switch key and the full
downstream continuation. -/
noncomputable def continuationBootstrapReplacementAdvantage
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (continuation : Continuation LweSecret RingSecret BootstrapKey KeySwitchKey) : ℝ :=
  (realContinuationGame spec continuation).boolDistAdvantage
    (bootstrapZeroContinuationGame spec continuation)

/-- Key-switch replacement cost after the bootstrapping-key messages have been zeroed, with the
full downstream continuation retained. -/
noncomputable def continuationKeySwitchReplacementAdvantage
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (continuation : Continuation LweSecret RingSecret BootstrapKey KeySwitchKey) : ℝ :=
  (bootstrapZeroContinuationGame spec continuation).boolDistAdvantage
    (zeroContinuationGame spec continuation)

/-- Key-switch replacement cost while the real bootstrapping key is still exposed.  This is the
intact-cycle first hop in the alternative hybrid ordering. -/
noncomputable def continuationKeySwitchFirstReplacementAdvantage
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (continuation : Continuation LweSecret RingSecret BootstrapKey KeySwitchKey) : ℝ :=
  (realContinuationGame spec continuation).boolDistAdvantage
    (keySwitchZeroContinuationGame spec continuation)

/-- Bootstrapping replacement after the opposite key-switch edge has already been cut. -/
noncomputable def continuationBootstrapAfterKeySwitchReplacementAdvantage
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (continuation : Continuation LweSecret RingSecret BootstrapKey KeySwitchKey) : ℝ :=
  (keySwitchZeroContinuationGame spec continuation).boolDistAdvantage
    (zeroContinuationGame spec continuation)

/-- The two-hop native circular decomposition remains valid for arbitrary secret-dependent
continuations, including adaptive one-time IND-CPA challenge experiments. -/
theorem continuationCircularAdvantage_le_replacements
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (continuation : Continuation LweSecret RingSecret BootstrapKey KeySwitchKey) :
    continuationCircularAdvantage spec continuation ≤
      continuationBootstrapReplacementAdvantage spec continuation +
        continuationKeySwitchReplacementAdvantage spec continuation := by
  exact ProbComp.boolDistAdvantage_triangle
    (realContinuationGame spec continuation)
    (bootstrapZeroContinuationGame spec continuation)
    (zeroContinuationGame spec continuation)

/-- The same circular advantage decomposed in the opposite order: first replace the KSK while the
BRK is real, then replace the BRK after the KSK edge has been cut. -/
theorem continuationCircularAdvantage_le_keySwitchFirst_add_bootstrapAfter
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (continuation : Continuation LweSecret RingSecret BootstrapKey KeySwitchKey) :
    continuationCircularAdvantage spec continuation ≤
      continuationKeySwitchFirstReplacementAdvantage spec continuation +
        continuationBootstrapAfterKeySwitchReplacementAdvantage spec continuation := by
  exact ProbComp.boolDistAdvantage_triangle
    (realContinuationGame spec continuation)
    (keySwitchZeroContinuationGame spec continuation)
    (zeroContinuationGame spec continuation)

/-- The BRK-first intact-cycle cost is bounded by the KSK-first intact-cycle cost plus both
post-cut edges.  Thus the choice of first hybrid cannot hide an additional assumption. -/
theorem continuationBootstrapReplacementAdvantage_le_keySwitchFirst_add_postCuts
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (continuation : Continuation LweSecret RingSecret BootstrapKey KeySwitchKey) :
    continuationBootstrapReplacementAdvantage spec continuation ≤
      continuationKeySwitchFirstReplacementAdvantage spec continuation +
        continuationBootstrapAfterKeySwitchReplacementAdvantage spec continuation +
        continuationKeySwitchReplacementAdvantage spec continuation := by
  let real := realContinuationGame spec continuation
  let bootstrapZero := bootstrapZeroContinuationGame spec continuation
  let keySwitchZero := keySwitchZeroContinuationGame spec continuation
  let zero := zeroContinuationGame spec continuation
  have hFirst := ProbComp.boolDistAdvantage_triangle real keySwitchZero bootstrapZero
  have hMiddle := ProbComp.boolDistAdvantage_triangle keySwitchZero zero bootstrapZero
  have hReverse : zero.boolDistAdvantage bootstrapZero =
      bootstrapZero.boolDistAdvantage zero := by
    unfold ProbComp.boolDistAdvantage
    rw [abs_sub_comm]
  unfold continuationBootstrapReplacementAdvantage
    continuationKeySwitchFirstReplacementAdvantage
    continuationBootstrapAfterKeySwitchReplacementAdvantage
    continuationKeySwitchReplacementAdvantage
  change real.boolDistAdvantage bootstrapZero ≤
    real.boolDistAdvantage keySwitchZero +
      keySwitchZero.boolDistAdvantage zero + bootstrapZero.boolDistAdvantage zero
  rw [← hReverse]
  linarith

/-- Conversely, the KSK-first intact-cycle cost is bounded by the BRK-first cost plus both
post-cut edges. -/
theorem continuationKeySwitchFirstReplacementAdvantage_le_bootstrapFirst_add_postCuts
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (continuation : Continuation LweSecret RingSecret BootstrapKey KeySwitchKey) :
    continuationKeySwitchFirstReplacementAdvantage spec continuation ≤
      continuationBootstrapReplacementAdvantage spec continuation +
        continuationKeySwitchReplacementAdvantage spec continuation +
        continuationBootstrapAfterKeySwitchReplacementAdvantage spec continuation := by
  let real := realContinuationGame spec continuation
  let bootstrapZero := bootstrapZeroContinuationGame spec continuation
  let keySwitchZero := keySwitchZeroContinuationGame spec continuation
  let zero := zeroContinuationGame spec continuation
  have hFirst := ProbComp.boolDistAdvantage_triangle real bootstrapZero keySwitchZero
  have hMiddle := ProbComp.boolDistAdvantage_triangle bootstrapZero zero keySwitchZero
  have hReverse : zero.boolDistAdvantage keySwitchZero =
      keySwitchZero.boolDistAdvantage zero := by
    unfold ProbComp.boolDistAdvantage
    rw [abs_sub_comm]
  unfold continuationKeySwitchFirstReplacementAdvantage
    continuationBootstrapReplacementAdvantage
    continuationKeySwitchReplacementAdvantage
    continuationBootstrapAfterKeySwitchReplacementAdvantage
  change real.boolDistAdvantage keySwitchZero ≤
    real.boolDistAdvantage bootstrapZero +
      bootstrapZero.boolDistAdvantage zero + keySwitchZero.boolDistAdvantage zero
  rw [← hReverse]
  linarith

/-- A continuation-level circular-security premise for selected downstream experiments. -/
def ContinuationHardAgainst
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (allowed : Continuation LweSecret RingSecret BootstrapKey KeySwitchKey → Prop)
    (bound : ℝ) : Prop :=
  ∀ continuation, allowed continuation →
    continuationCircularAdvantage spec continuation ≤ bound

/-- Hardness of the BRK-first intact-cycle hop for a selected class of continuations.  This is a
scheme-specific fixed-hint KDM premise: the real KSK remains visible while the BRK messages are
replaced. -/
def BootstrapFirstHardAgainst
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (allowed : Continuation LweSecret RingSecret BootstrapKey KeySwitchKey → Prop)
    (bound : ℝ) : Prop :=
  ∀ continuation, allowed continuation →
    continuationBootstrapReplacementAdvantage spec continuation ≤ bound

/-- Hardness of the KSK-first intact-cycle hop for a selected class of continuations.  The real
BRK remains visible while the KSK messages are replaced by zero. -/
def KeySwitchFirstHardAgainst
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (allowed : Continuation LweSecret RingSecret BootstrapKey KeySwitchKey → Prop)
    (bound : ℝ) : Prop :=
  ∀ continuation, allowed continuation →
    continuationKeySwitchFirstReplacementAdvantage spec continuation ≤ bound

/-- Hardness of the ordinary post-cut KSK hop after BRK messages have already been zeroed. -/
def KeySwitchAfterBootstrapHardAgainst
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (allowed : Continuation LweSecret RingSecret BootstrapKey KeySwitchKey → Prop)
    (bound : ℝ) : Prop :=
  ∀ continuation, allowed continuation →
    continuationKeySwitchReplacementAdvantage spec continuation ≤ bound

/-- Hardness of the ordinary post-cut BRK hop after KSK messages have already been zeroed. -/
def BootstrapAfterKeySwitchHardAgainst
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (allowed : Continuation LweSecret RingSecret BootstrapKey KeySwitchKey → Prop)
    (bound : ℝ) : Prop :=
  ∀ continuation, allowed continuation →
    continuationBootstrapAfterKeySwitchReplacementAdvantage spec continuation ≤ bound

/-- A bound for the named KSK-first intact-cycle KDM premise and a bound for the post-cut BRK hop
compose into security of the complete native circular view. -/
theorem continuationHardAgainst_of_keySwitchFirst_and_bootstrapAfter
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (allowed : Continuation LweSecret RingSecret BootstrapKey KeySwitchKey → Prop)
    (keySwitchFirstBound bootstrapAfterBound : ℝ)
    (hKeySwitchFirst : KeySwitchFirstHardAgainst spec allowed keySwitchFirstBound)
    (hBootstrapAfter : BootstrapAfterKeySwitchHardAgainst spec allowed bootstrapAfterBound) :
    ContinuationHardAgainst spec allowed (keySwitchFirstBound + bootstrapAfterBound) := by
  intro continuation hallowed
  calc
    continuationCircularAdvantage spec continuation ≤
        continuationKeySwitchFirstReplacementAdvantage spec continuation +
          continuationBootstrapAfterKeySwitchReplacementAdvantage spec continuation :=
      continuationCircularAdvantage_le_keySwitchFirst_add_bootstrapAfter spec continuation
    _ ≤ keySwitchFirstBound + bootstrapAfterBound :=
      add_le_add (hKeySwitchFirst continuation hallowed)
        (hBootstrapAfter continuation hallowed)

/-- KSK-first intact-cycle hardness plus the two checked post-cut assumptions implies BRK-first
intact-cycle hardness, with their concrete bounds made explicit. -/
theorem bootstrapFirstHardAgainst_of_keySwitchFirst_and_postCuts
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (allowed : Continuation LweSecret RingSecret BootstrapKey KeySwitchKey → Prop)
    (keySwitchFirstBound bootstrapAfterBound keySwitchAfterBound : ℝ)
    (hKeySwitchFirst : KeySwitchFirstHardAgainst spec allowed keySwitchFirstBound)
    (hBootstrapAfter : BootstrapAfterKeySwitchHardAgainst spec allowed bootstrapAfterBound)
    (hKeySwitchAfter : KeySwitchAfterBootstrapHardAgainst spec allowed keySwitchAfterBound) :
    BootstrapFirstHardAgainst spec allowed
      (keySwitchFirstBound + bootstrapAfterBound + keySwitchAfterBound) := by
  intro continuation hallowed
  calc
    continuationBootstrapReplacementAdvantage spec continuation ≤
        continuationKeySwitchFirstReplacementAdvantage spec continuation +
          continuationBootstrapAfterKeySwitchReplacementAdvantage spec continuation +
          continuationKeySwitchReplacementAdvantage spec continuation :=
      continuationBootstrapReplacementAdvantage_le_keySwitchFirst_add_postCuts spec continuation
    _ ≤ keySwitchFirstBound + bootstrapAfterBound + keySwitchAfterBound :=
      add_le_add
        (add_le_add (hKeySwitchFirst continuation hallowed)
          (hBootstrapAfter continuation hallowed))
        (hKeySwitchAfter continuation hallowed)

/-- Conversely, BRK-first intact-cycle hardness plus both checked post-cut assumptions implies
KSK-first intact-cycle hardness.  Thus choosing the first hybrid only changes standard terms. -/
theorem keySwitchFirstHardAgainst_of_bootstrapFirst_and_postCuts
    (spec : CycleSpec LweSecret RingSecret ExtractedRingSecret BootstrapKey KeySwitchKey)
    (allowed : Continuation LweSecret RingSecret BootstrapKey KeySwitchKey → Prop)
    (bootstrapFirstBound keySwitchAfterBound bootstrapAfterBound : ℝ)
    (hBootstrapFirst : BootstrapFirstHardAgainst spec allowed bootstrapFirstBound)
    (hKeySwitchAfter : KeySwitchAfterBootstrapHardAgainst spec allowed keySwitchAfterBound)
    (hBootstrapAfter : BootstrapAfterKeySwitchHardAgainst spec allowed bootstrapAfterBound) :
    KeySwitchFirstHardAgainst spec allowed
      (bootstrapFirstBound + keySwitchAfterBound + bootstrapAfterBound) := by
  intro continuation hallowed
  calc
    continuationKeySwitchFirstReplacementAdvantage spec continuation ≤
        continuationBootstrapReplacementAdvantage spec continuation +
          continuationKeySwitchReplacementAdvantage spec continuation +
          continuationBootstrapAfterKeySwitchReplacementAdvantage spec continuation :=
      continuationKeySwitchFirstReplacementAdvantage_le_bootstrapFirst_add_postCuts
        spec continuation
    _ ≤ bootstrapFirstBound + keySwitchAfterBound + bootstrapAfterBound :=
      add_le_add
        (add_le_add (hBootstrapFirst continuation hallowed)
          (hKeySwitchAfter continuation hallowed))
        (hBootstrapAfter continuation hallowed)

end DependentContinuation

end FormalProof4FHE.TFHE.Circular
