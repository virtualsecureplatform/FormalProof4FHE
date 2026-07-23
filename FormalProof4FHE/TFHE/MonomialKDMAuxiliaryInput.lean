/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.AuxiliaryInput
import FormalProof4FHE.TFHE.MonomialKDM

/-!
# Native TFHE Monomial KDM as Auxiliary-Input CircLWE

The PKC 2024 CircLWE formulation compares gadget-LWE encodings of a fixed secret function with a
uniform transcript, while retaining any specified side information.  Native TFHE has exactly such
a fixed side input: during bootstrapping-key replacement, the real key-switch key remains visible
and is correlated with both hidden keys.

This file instantiates `LWE.AuxiliaryInput.Problem` with the exact native finite distribution:

* the secret is the pair of native scalar and ring keys;
* the real challenge is the degree-two monomial presentation of the native bootstrapping key;
* the zero challenge is the native zero-message bootstrapping key;
* the uniform challenge has the identical native ciphertext type; and
* the auxiliary input is the real native key-switch key.

The real and zero games are proved definitionally equal to the existing native monomial-KDM
games.  Consequently the exact native first hop is equivalent to auxiliary-input CircLWE modulo
one explicit zero-message-versus-uniform side-information LWE term.  This is a classification of
the assumption, not a reduction from ordinary LWE or RLWE.
-/

open OracleComp

namespace FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput

/-- The two native hidden keys packaged as the secret of the auxiliary-input problem. -/
abbrev Secret (lweDimension ringRank degree : ℕ) :=
  BinarySecret lweDimension × RingBinarySecret ringRank degree

/-- The native bootstrapping-key type is the CircLWE challenge type. -/
abbrev Challenge (q degree ringRank tgswLevels lweDimension : ℕ) :=
  Native.BootstrappingKey q degree ringRank tgswLevels lweDimension

/-- The retained real key-switch key is the fixed correlated side information. -/
abbrev Auxiliary (q degree ringRank lweDimension keySwitchLevels : ℕ) :=
  Native.KeySwitchKey q lweDimension (ringRank * degree) keySwitchLevels

/-- Exact auxiliary-input CircLWE problem underlying native TFHE's monomial BRK-first hop. -/
noncomputable def problem
    (q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    LWE.AuxiliaryInput.Problem
      (Secret lweDimension ringRank degree)
      (Challenge q degree ringRank tgswLevels lweDimension)
      (Auxiliary q degree ringRank lweDimension keySwitchLevels) where
  sampleSecret := do
    let lweSecret ← Native.sampleLweSecret lweDimension
    let ringSecret ← Native.sampleRingSecret ringRank degree
    return (lweSecret, ringSecret)
  sampleReal := fun secrets ↦
    MonomialKDM.generateBootstrappingKey
      q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget
      secrets.1 secrets.2
  sampleZero := fun secrets ↦
    Native.generateZeroBootstrappingKey
      q degree ringRank tgswLevels lweDimension ringErrorSampler tgswGadget secrets.2
  sampleUniform :=
    $ᵗ (Challenge q degree ringRank tgswLevels lweDimension)
  sampleAuxiliary := fun secrets ↦
    Native.generateKeySwitchKey
      q lweDimension (ringRank * degree) keySwitchLevels
      keySwitchErrorSampler keySwitchGadget (keyExtract secrets.2) secrets.1

/-- Package an existing native two-key continuation for the paired-secret problem. -/
def packContinuation
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ}
    (continuation : Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (Challenge q degree ringRank tgswLevels lweDimension)
      (Auxiliary q degree ringRank lweDimension keySwitchLevels)) :
    LWE.AuxiliaryInput.Continuation
      (Secret lweDimension ringRank degree)
      (Challenge q degree ringRank tgswLevels lweDimension)
      (Auxiliary q degree ringRank lweDimension keySwitchLevels) :=
  fun secrets bootstrapKey keySwitchKey ↦
    continuation secrets.1 secrets.2 bootstrapKey keySwitchKey

/-- The auxiliary-input real game is exactly the native monomial real continuation game. -/
theorem realGame_eq_native
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation : Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (Challenge q degree ringRank tgswLevels lweDimension)
      (Auxiliary q degree ringRank lweDimension keySwitchLevels)) :
    LWE.AuxiliaryInput.realGame
        (problem q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        (packContinuation continuation) =
      Circular.realContinuationGame
        (MonomialKDM.cycleSpec
          q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        continuation := by
  simp [LWE.AuxiliaryInput.realGame, problem, packContinuation,
    Circular.realContinuationGame, MonomialKDM.cycleSpec, monad_norm]

/-- The auxiliary-input zero game is exactly the native monomial bootstrap-zero game. -/
theorem zeroGame_eq_native
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation : Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (Challenge q degree ringRank tgswLevels lweDimension)
      (Auxiliary q degree ringRank lweDimension keySwitchLevels)) :
    LWE.AuxiliaryInput.zeroGame
        (problem q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        (packContinuation continuation) =
      Circular.bootstrapZeroContinuationGame
        (MonomialKDM.cycleSpec
          q degree ringRank tgswLevels lweDimension keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
        continuation := by
  simp [LWE.AuxiliaryInput.zeroGame, problem, packContinuation,
    Circular.bootstrapZeroContinuationGame, MonomialKDM.cycleSpec, monad_norm]

/-- Exact native real-versus-zero advantage through the generic fixed-hint KDM interface. -/
noncomputable def kdmAdvantage
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation : Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (Challenge q degree ringRank tgswLevels lweDimension)
      (Auxiliary q degree ringRank lweDimension keySwitchLevels)) : ℝ :=
  LWE.AuxiliaryInput.kdmAdvantage
    (problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    (packContinuation continuation)

/-- Native monomial gadget-LWE versus uniform, retaining the real KSK as fixed side information. -/
noncomputable def circularLweAdvantage
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation : Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (Challenge q degree ringRank tgswLevels lweDimension)
      (Auxiliary q degree ringRank lweDimension keySwitchLevels)) : ℝ :=
  LWE.AuxiliaryInput.circularLweAdvantage
    (problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    (packContinuation continuation)

/-- Native zero-message gadget-LWE versus uniform with the same real KSK side information. -/
noncomputable def zeroLweAdvantage
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation : Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (Challenge q degree ringRank tgswLevels lweDimension)
      (Auxiliary q degree ringRank lweDimension keySwitchLevels)) : ℝ :=
  LWE.AuxiliaryInput.zeroLweAdvantage
    (problem q degree ringRank tgswLevels lweDimension keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    (packContinuation continuation)

/-- The generic fixed-hint KDM advantage is exactly the previously classified native
degree-two monomial-KDM advantage. -/
theorem kdmAdvantage_eq_monomial
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation : Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (Challenge q degree ringRank tgswLevels lweDimension)
      (Auxiliary q degree ringRank lweDimension keySwitchLevels)) :
    kdmAdvantage ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget continuation =
      MonomialKDM.advantage ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget continuation := by
  unfold kdmAdvantage LWE.AuxiliaryInput.kdmAdvantage MonomialKDM.advantage
  rw [realGame_eq_native, zeroGame_eq_native]

/-- **Native monomial KDM from auxiliary-input CircLWE.**  The remaining native first hop is
bounded by its named real-versus-uniform CircLWE formulation plus the explicit zero-message
side-information LWE branch. -/
theorem monomialAdvantage_le_circularLwe_add_zeroLwe
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation : Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (Challenge q degree ringRank tgswLevels lweDimension)
      (Auxiliary q degree ringRank lweDimension keySwitchLevels)) :
    MonomialKDM.advantage ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget continuation ≤
      circularLweAdvantage ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget continuation +
        zeroLweAdvantage ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget continuation := by
  rw [← kdmAdvantage_eq_monomial]
  exact LWE.AuxiliaryInput.kdmAdvantage_le_circularLwe_add_zeroLwe _ _

/-- Conversely, native auxiliary-input CircLWE is bounded by native monomial KDM plus the same
zero-message side-information LWE branch. -/
theorem circularLweAdvantage_le_monomial_add_zeroLwe
    {q degree ringRank tgswLevels lweDimension keySwitchLevels : ℕ} [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q degree))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q degree)
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (continuation : Circular.Continuation
      (BinarySecret lweDimension) (RingBinarySecret ringRank degree)
      (Challenge q degree ringRank tgswLevels lweDimension)
      (Auxiliary q degree ringRank lweDimension keySwitchLevels)) :
    circularLweAdvantage ringErrorSampler keySwitchErrorSampler
        tgswGadget keySwitchGadget continuation ≤
      MonomialKDM.advantage ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget continuation +
        zeroLweAdvantage ringErrorSampler keySwitchErrorSampler
          tgswGadget keySwitchGadget continuation := by
  rw [← kdmAdvantage_eq_monomial]
  exact LWE.AuxiliaryInput.circularLweAdvantage_le_kdm_add_zeroLwe _ _

end FormalProof4FHE.TFHE.Native.BootstrapSecurity.MonomialKDM.AuxiliaryInput
