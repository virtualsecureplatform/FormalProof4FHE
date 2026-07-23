/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.AuxiliaryInput
import FormalProof4FHE.TFHE.SharedRandomnessOneCycle

/-!
# Shared-Randomness One-Cycle TFHE as Auxiliary-Input CircLWE

The shared-randomness TFHE layout uses one rank-one master ring key.  Its prefix is the scalar
TLWE key, and the key-switch key encrypts only the independent suffix under that prefix.  This
removes the heterogeneous two-key cycle, but the native bootstrapping key still encrypts prefix
bits under the complete ring key that contains them.

This module gives that remaining one-key object an exact auxiliary-input CircLWE statement:

* the secret is the complete rank-one master ring key;
* the real challenge is the native self-circular bootstrapping key;
* the zero challenge is the same native bootstrapping-key format with zero gadget messages;
* the uniform challenge has the identical native ciphertext type; and
* the auxiliary input is the real suffix-only key-switch key.

The generic real and zero games are definitionally the native one-cycle games.  The real
challenge also has exactly the previously proved degree-two self-monomial presentation.  Thus
the interface neither hides a second circular edge nor asserts that ordinary LWE/RLWE proves the
remaining quadratic one-key premise.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle.AuxiliaryInput

noncomputable section

/-- The complete rank-one master key is the sole secret in the one-cycle problem. -/
abbrev Secret (prefixDimension suffixDimension : ℕ) :=
  RingBinarySecret 1 (prefixDimension + suffixDimension)

/-- The native rank-one BRK is the one-cycle CircLWE challenge. -/
abbrev Challenge
    (q prefixDimension suffixDimension tgswLevels : ℕ) :=
  SharedBootstrappingKey q prefixDimension suffixDimension tgswLevels

/-- The real suffix-only KSK is retained as correlated auxiliary information. -/
abbrev Auxiliary
    (q prefixDimension suffixDimension keySwitchLevels : ℕ) :=
  SharedKeySwitchKey q prefixDimension suffixDimension keySwitchLevels

/-- Exact auxiliary-input CircLWE problem for the native shared-randomness one-cycle layout. -/
noncomputable def problem
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    LWE.AuxiliaryInput.Problem
      (Secret prefixDimension suffixDimension)
      (Challenge q prefixDimension suffixDimension tgswLevels)
      (Auxiliary q prefixDimension suffixDimension keySwitchLevels) where
  sampleSecret := Native.sampleRingSecret 1 (prefixDimension + suffixDimension)
  sampleReal := fun masterSecret ↦
    generateBootstrappingKey q prefixDimension suffixDimension tgswLevels
      ringErrorSampler tgswGadget masterSecret
  sampleZero := fun masterSecret ↦
    generateZeroBootstrappingKey q prefixDimension suffixDimension tgswLevels
      ringErrorSampler tgswGadget masterSecret
  sampleUniform :=
    $ᵗ (Challenge q prefixDimension suffixDimension tgswLevels)
  sampleAuxiliary := fun masterSecret ↦
    generateKeySwitchKey q prefixDimension suffixDimension keySwitchLevels
      keySwitchErrorSampler keySwitchGadget masterSecret

/-- The real challenge of the exact one-cycle problem has the native degree-two
self-monomial distribution. -/
theorem sampleReal_evalDist_eq_selfMonomial
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (masterSecret : Secret prefixDimension suffixDimension) :
    evalDist
        ((problem q prefixDimension suffixDimension tgswLevels keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget).sampleReal
          masterSecret) =
      evalDist (generateSelfMonomialBootstrappingKey q prefixDimension suffixDimension
        tgswLevels ringErrorSampler tgswGadget masterSecret) := by
  exact generateBootstrappingKey_evalDist_eq_selfMonomial q prefixDimension suffixDimension
    tgswLevels ringErrorSampler tgswGadget masterSecret

/-- The generic continuation type is exactly the native one-cycle secret continuation. -/
def packContinuation
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ}
    (continuation :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    LWE.AuxiliaryInput.Continuation
      (Secret prefixDimension suffixDimension)
      (Challenge q prefixDimension suffixDimension tgswLevels)
      (Auxiliary q prefixDimension suffixDimension keySwitchLevels) :=
  continuation

/-- Uniform-BRK comparison retaining the same master secret and real suffix KSK. -/
noncomputable def uniformSecretContinuationGame
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    ProbComp Bool := do
  let masterSecret ← Native.sampleRingSecret 1 (prefixDimension + suffixDimension)
  let bootstrappingKey ←
    $ᵗ (SharedBootstrappingKey q prefixDimension suffixDimension tgswLevels)
  let keySwitchKey ←
    generateKeySwitchKey q prefixDimension suffixDimension keySwitchLevels
      keySwitchErrorSampler keySwitchGadget masterSecret
  continuation masterSecret bootstrappingKey keySwitchKey

/-- The auxiliary-input real game is definitionally the native one-cycle real game. -/
theorem realGame_eq_native
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    LWE.AuxiliaryInput.realGame
        (problem q prefixDimension suffixDimension tgswLevels keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        (packContinuation continuation) =
      realSecretContinuationGame q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget continuation := by
  rfl

/-- The auxiliary-input zero game is definitionally the native BRK-zero hybrid. -/
theorem zeroGame_eq_native
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    LWE.AuxiliaryInput.zeroGame
        (problem q prefixDimension suffixDimension tgswLevels keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        (packContinuation continuation) =
      bootstrapZeroSecretContinuationGame q prefixDimension suffixDimension tgswLevels
        keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        continuation := by
  rfl

/-- The auxiliary-input uniform game is exactly the uniform-BRK one-cycle comparison. -/
theorem uniformGame_eq_native
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    LWE.AuxiliaryInput.uniformGame
        (problem q prefixDimension suffixDimension tgswLevels keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        (packContinuation continuation) =
      uniformSecretContinuationGame q prefixDimension suffixDimension tgswLevels
        keySwitchLevels keySwitchErrorSampler keySwitchGadget continuation := by
  rfl

/-- Exact native real-versus-zero advantage through the generic fixed-hint KDM interface. -/
noncomputable def kdmAdvantage
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels) : ℝ :=
  LWE.AuxiliaryInput.kdmAdvantage
    (problem q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    (packContinuation continuation)

/-- Native one-key self-circular BRK versus uniform, retaining the real suffix KSK. -/
noncomputable def circularLweAdvantage
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels) : ℝ :=
  LWE.AuxiliaryInput.circularLweAdvantage
    (problem q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    (packContinuation continuation)

/-- Native zero-message BRK versus uniform with the same real suffix KSK side information. -/
noncomputable def zeroLweAdvantage
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels) : ℝ :=
  LWE.AuxiliaryInput.zeroLweAdvantage
    (problem q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    (packContinuation continuation)

/-- The generic fixed-hint KDM advantage is exactly the native one-cycle secret-continuation
advantage. -/
theorem kdmAdvantage_eq_secretContinuationAdvantage
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    kdmAdvantage ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        continuation =
      secretContinuationAdvantage q prefixDimension suffixDimension tgswLevels
        keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        continuation := by
  unfold kdmAdvantage LWE.AuxiliaryInput.kdmAdvantage secretContinuationAdvantage
  rw [realGame_eq_native, zeroGame_eq_native]

/-- The native one-cycle KDM hop is bounded by its exact auxiliary-input CircLWE statement plus
the explicit zero-message side-information LWE branch. -/
theorem secretContinuationAdvantage_le_circularLwe_add_zeroLwe
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    secretContinuationAdvantage q prefixDimension suffixDimension tgswLevels
        keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        continuation ≤
      circularLweAdvantage ringErrorSampler keySwitchErrorSampler tgswGadget
          keySwitchGadget continuation +
        zeroLweAdvantage ringErrorSampler keySwitchErrorSampler tgswGadget
          keySwitchGadget continuation := by
  rw [← kdmAdvantage_eq_secretContinuationAdvantage]
  exact LWE.AuxiliaryInput.kdmAdvantage_le_circularLwe_add_zeroLwe _ _

/-- Conversely, the exact one-key auxiliary-input CircLWE term is bounded by the native KDM hop
plus the same zero-message side-information branch. -/
theorem circularLweAdvantage_le_secretContinuation_add_zeroLwe
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation :
      SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    circularLweAdvantage ringErrorSampler keySwitchErrorSampler tgswGadget
        keySwitchGadget continuation ≤
      secretContinuationAdvantage q prefixDimension suffixDimension tgswLevels
          keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
          continuation +
        zeroLweAdvantage ringErrorSampler keySwitchErrorSampler tgswGadget
          keySwitchGadget continuation := by
  rw [← kdmAdvantage_eq_secretContinuationAdvantage]
  exact LWE.AuxiliaryInput.circularLweAdvantage_le_kdm_add_zeroLwe _ _

/-- A public cloud-key adversary is a secret continuation that simply ignores the secret. -/
def packAdversary
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ}
    (adversary : Adversary q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    SecretContinuation q prefixDimension suffixDimension tgswLevels keySwitchLevels :=
  fun _ bootstrappingKey keySwitchKey ↦
    adversary ⟨bootstrappingKey, keySwitchKey⟩

/-- The public cloud-key one-circular advantage is the same generic one-key KDM advantage. -/
theorem oneCircularAdvantage_eq_kdmAdvantage
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : Adversary q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    oneCircularAdvantage q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary =
      kdmAdvantage ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
        (packAdversary adversary) := by
  unfold oneCircularAdvantage kdmAdvantage LWE.AuxiliaryInput.kdmAdvantage
  rw [realGame_eq_native, zeroGame_eq_native]
  congr 1 <;>
    simp [realGame, bootstrapZeroGame, realCloudKeyView, bootstrapZeroCloudKeyView,
      generateCloudKey, generateBootstrapZeroCloudKey, realSecretContinuationGame,
      bootstrapZeroSecretContinuationGame, packAdversary, bind_assoc, monad_norm]

/-- The actual shared-randomness one-circular game is bounded by the corresponding public
real-versus-uniform CircLWE game and its zero-message-versus-uniform ordinary-encryption branch.
This theorem states the one-cycle target directly: the KSK is retained only as correlated
auxiliary input and does not create a second circular edge. -/
theorem oneCircularAdvantage_le_circularLwe_add_zeroLwe
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : Adversary q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    oneCircularAdvantage q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary ≤
      circularLweAdvantage ringErrorSampler keySwitchErrorSampler tgswGadget
          keySwitchGadget (packAdversary adversary) +
        zeroLweAdvantage ringErrorSampler keySwitchErrorSampler tgswGadget
          keySwitchGadget (packAdversary adversary) := by
  rw [oneCircularAdvantage_eq_kdmAdvantage]
  exact LWE.AuxiliaryInput.kdmAdvantage_le_circularLwe_add_zeroLwe _ _

/-- Bounds for the public CircLWE and zero-message branches prove the exact one-circular cloud-key
hardness predicate.  This is the direct security endpoint for the shared-randomness construction,
not a definition of ring-key transport. -/
theorem oneCircularHardAgainst_of_circularLwe_and_zeroLwe
    {q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (allowed :
      Adversary q prefixDimension suffixDimension tgswLevels keySwitchLevels → Prop)
    (circularBound zeroBound : ℝ)
    (hCircular : ∀ adversary, allowed adversary →
      circularLweAdvantage ringErrorSampler keySwitchErrorSampler tgswGadget
        keySwitchGadget (packAdversary adversary) ≤ circularBound)
    (hZero : ∀ adversary, allowed adversary →
      zeroLweAdvantage ringErrorSampler keySwitchErrorSampler tgswGadget
        keySwitchGadget (packAdversary adversary) ≤ zeroBound) :
    OneCircularHardAgainst q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget allowed
      (circularBound + zeroBound) := by
  intro adversary hadversary
  exact (oneCircularAdvantage_le_circularLwe_add_zeroLwe
    ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary).trans
      (add_le_add (hCircular adversary hadversary) (hZero adversary hadversary))

end

end FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle.AuxiliaryInput
