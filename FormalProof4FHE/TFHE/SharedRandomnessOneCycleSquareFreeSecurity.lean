/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.FullBRKQuadraticSpan
import FormalProof4FHE.TFHE.SharedRandomnessOneCycle

set_option autoImplicit false

/-!
# Square-Free Circular Boundary for Shared-Randomness TFHE

The shared-randomness construction has one circular edge, but its native TRGSW mask rows still
contain products between a prefix message bit and coefficients of the complete master ring key.
This file factors that edge through an exact diagonal-only hybrid.

For binary keys the one matching coefficient is a Boolean square and therefore affine.  Every
other coefficient is a product of two distinct master-key bits.  The real native BRK is proved
equal in distribution to the sampler obtained by adding this square-free phase to the
diagonal-only phase.  A triangle theorem consequently splits the original one-circular
advantage into exactly two named terms:

* real versus diagonal-only: the fixed square-free outer-product KDM obligation;
* diagonal-only versus zero: the remaining coefficient-affine circular obligation.

This does not assume either term secure.  It makes precise that a general degree-two KDM premise
is stronger than native TFHE needs, while nonce placement does not erase the off-diagonal term.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle.SquareFreeSecurity

open FullBRKQuadraticSpan

noncomputable section

/-- The master-ring coefficient corresponding to one scalar prefix coordinate. -/
def prefixCoefficient {prefixDimension suffixDimension : ℕ}
    (coordinate : Fin prefixDimension) : Fin (prefixDimension + suffixDimension) :=
  Fin.castAdd suffixDimension coordinate

/-- The unique diagonal coordinate vector for one encrypted prefix bit. -/
def prefixDiagonalCross
    (q prefixDimension suffixDimension : ℕ)
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension))
    (coordinate : Fin prefixDimension) :
    Fin 1 → RLWE.Rq q (prefixDimension + suffixDimension) :=
  diagonalCrossAtDegree q (prefixDimension + suffixDimension) 1 ringSecret 0
    (prefixCoefficient coordinate)

/-- All distinct-coordinate products for one encrypted prefix bit. -/
def prefixSquareFreeCross
    (q prefixDimension suffixDimension : ℕ)
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension))
    (coordinate : Fin prefixDimension) :
    Fin 1 → RLWE.Rq q (prefixDimension + suffixDimension) :=
  squareFreeCrossAtDegree q (prefixDimension + suffixDimension) 1 ringSecret 0
    (prefixCoefficient coordinate)

/-- The one-cycle monomial vector is exactly its Boolean diagonal plus the square-free
remainder. -/
theorem selfCrossMonomial_eq_prefixDiagonal_add_squareFree
    (q prefixDimension suffixDimension : ℕ)
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension))
    (coordinate : Fin prefixDimension) :
    selfCrossMonomial q prefixDimension suffixDimension ringSecret coordinate =
      prefixDiagonalCross q prefixDimension suffixDimension ringSecret coordinate +
        prefixSquareFreeCross q prefixDimension suffixDimension ringSecret coordinate := by
  simpa [selfCrossMonomial, prefixDiagonalCross, prefixSquareFreeCross,
    prefixCoefficient, prefixSecret] using
    (crossMonomial_eq_diagonalCrossAtDegree_add_squareFreeCrossAtDegree
      q (prefixDimension + suffixDimension) 1 ringSecret 0
        (prefixCoefficient coordinate))

/-- Affine-plus-diagonal phase of one prefix-message TGSW entry. -/
def diagonalPhase
    (q prefixDimension suffixDimension levels : ℕ)
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension))
    (gadget : Fin levels → RLWE.Rq q (prefixDimension + suffixDimension))
    (coordinate : Fin prefixDimension) :
    Fin (TGSW.rowCount 1 levels) → RLWE.Rq q (prefixDimension + suffixDimension) :=
  TGSW.CircularBoundary.affinePhasePart gadget
      (embedConstantBit q (prefixDimension + suffixDimension)
        (prefixSecret ringSecret coordinate)) +
    TGSW.MonomialKDM.monomialPhasePart gadget
      (prefixDiagonalCross q prefixDimension suffixDimension ringSecret coordinate)

/-- Genuinely nonlinear square-free phase of one prefix-message TGSW entry. -/
def squareFreePhase
    (q prefixDimension suffixDimension levels : ℕ)
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension))
    (gadget : Fin levels → RLWE.Rq q (prefixDimension + suffixDimension))
    (coordinate : Fin prefixDimension) :
    Fin (TGSW.rowCount 1 levels) → RLWE.Rq q (prefixDimension + suffixDimension) :=
  TGSW.MonomialKDM.monomialPhasePart gadget
    (prefixSquareFreeCross q prefixDimension suffixDimension ringSecret coordinate)

/-- Complete split phase. -/
def splitPhase
    (q prefixDimension suffixDimension levels : ℕ)
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension))
    (gadget : Fin levels → RLWE.Rq q (prefixDimension + suffixDimension))
    (coordinate : Fin prefixDimension) :
    Fin (TGSW.rowCount 1 levels) → RLWE.Rq q (prefixDimension + suffixDimension) :=
  diagonalPhase q prefixDimension suffixDimension levels ringSecret gadget coordinate +
    squareFreePhase q prefixDimension suffixDimension levels ringSecret gadget coordinate

/-- Every actual native prefix-message gadget phase is exactly the complete split phase. -/
theorem gadgetPhase_prefix_eq_splitPhase
    (q prefixDimension suffixDimension levels : ℕ)
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension))
    (gadget : Fin levels → RLWE.Rq q (prefixDimension + suffixDimension))
    (coordinate : Fin prefixDimension) :
    TGSW.gadgetPhase (embedRingSecret q ringSecret) gadget
        (embedConstantBit q (prefixDimension + suffixDimension)
          (prefixSecret ringSecret coordinate)) =
      splitPhase q prefixDimension suffixDimension levels ringSecret gadget coordinate := by
  simpa [splitPhase, diagonalPhase, squareFreePhase, prefixDiagonalCross,
    prefixSquareFreeCross, prefixCoefficient, prefixSecret] using
    (gadgetPhase_self_eq_diagonalAtDegree_add_squareFreeAtDegree
      q (prefixDimension + suffixDimension) 1 levels ringSecret gadget 0
        (prefixCoefficient coordinate))

/-- One normalized native entry with only its affine and Boolean-diagonal phase retained. -/
def diagonalOnlyEntry
    (q prefixDimension suffixDimension levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension))
    (gadget : Fin levels → RLWE.Rq q (prefixDimension + suffixDimension))
    (coordinate : Fin prefixDimension) :
    ProbComp (RingGSWCiphertext q (prefixDimension + suffixDimension) 1 levels) :=
  TLWE.batchEncrypt 1 (TGSW.rowCount 1 levels) errorSampler
    (embedRingSecret q ringSecret)
    (diagonalPhase q prefixDimension suffixDimension levels ringSecret gadget coordinate)

/-- One normalized native entry with the diagonal and square-free phases displayed separately. -/
def splitEntry
    (q prefixDimension suffixDimension levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension))
    (gadget : Fin levels → RLWE.Rq q (prefixDimension + suffixDimension))
    (coordinate : Fin prefixDimension) :
    ProbComp (RingGSWCiphertext q (prefixDimension + suffixDimension) 1 levels) :=
  TLWE.batchEncrypt 1 (TGSW.rowCount 1 levels) errorSampler
    (embedRingSecret q ringSecret)
    (splitPhase q prefixDimension suffixDimension levels ringSecret gadget coordinate)

/-- The existing self-monomial entry is exactly the split native entry. -/
theorem expandedDirectEncrypt_self_eq_splitEntry
    (q prefixDimension suffixDimension levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension))
    (gadget : Fin levels → RLWE.Rq q (prefixDimension + suffixDimension))
    (coordinate : Fin prefixDimension) :
    TGSW.MonomialKDM.expandedDirectEncrypt 1 levels errorSampler
        (embedRingSecret q ringSecret) gadget
        (embedConstantBit q (prefixDimension + suffixDimension)
          (prefixSecret ringSecret coordinate))
        (selfCrossMonomial q prefixDimension suffixDimension ringSecret coordinate) =
      splitEntry q prefixDimension suffixDimension levels errorSampler ringSecret gadget
        coordinate := by
  calc
    _ = TGSW.directEncrypt 1 levels errorSampler (embedRingSecret q ringSecret) gadget
        (embedConstantBit q (prefixDimension + suffixDimension)
          (prefixSecret ringSecret coordinate)) := by
      exact (TGSW.MonomialKDM.directEncrypt_eq_expandedDirectEncrypt 1 levels
        errorSampler (embedRingSecret q ringSecret) gadget
        (embedConstantBit q (prefixDimension + suffixDimension)
          (prefixSecret ringSecret coordinate))).symm
    _ = _ := by
      unfold TGSW.directEncrypt splitEntry
      rw [gadgetPhase_prefix_eq_splitPhase]

/-- Complete diagonal-only prefix BRK. -/
def generateDiagonalOnlyBootstrappingKey
    (q prefixDimension suffixDimension levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (gadget : Fin levels → RLWE.Rq q (prefixDimension + suffixDimension))
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    ProbComp (SharedBootstrappingKey q prefixDimension suffixDimension levels) :=
  Fin.mOfFn prefixDimension fun coordinate ↦
    diagonalOnlyEntry q prefixDimension suffixDimension levels errorSampler ringSecret gadget
      coordinate

/-- Complete BRK with the diagonal and square-free terms displayed separately. -/
def generateSplitBootstrappingKey
    (q prefixDimension suffixDimension levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (gadget : Fin levels → RLWE.Rq q (prefixDimension + suffixDimension))
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    ProbComp (SharedBootstrappingKey q prefixDimension suffixDimension levels) :=
  Fin.mOfFn prefixDimension fun coordinate ↦
    splitEntry q prefixDimension suffixDimension levels errorSampler ringSecret gadget coordinate

/-- The explicit monomial BRK and the explicit diagonal-plus-square-free BRK are equal as
probabilistic programs. -/
theorem generateSelfMonomialBootstrappingKey_eq_split
    (q prefixDimension suffixDimension levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (gadget : Fin levels → RLWE.Rq q (prefixDimension + suffixDimension))
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    generateSelfMonomialBootstrappingKey q prefixDimension suffixDimension levels
        errorSampler gadget ringSecret =
      generateSplitBootstrappingKey q prefixDimension suffixDimension levels
        errorSampler gadget ringSecret := by
  unfold generateSelfMonomialBootstrappingKey generateSplitBootstrappingKey
  congr 1
  funext coordinate
  exact expandedDirectEncrypt_self_eq_splitEntry q prefixDimension suffixDimension levels
    errorSampler ringSecret gadget coordinate

/-- The honest native BRK is exactly the diagonal-plus-square-free sampler in distribution. -/
theorem generateBootstrappingKey_evalDist_eq_split
    (q prefixDimension suffixDimension levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (gadget : Fin levels → RLWE.Rq q (prefixDimension + suffixDimension))
    (ringSecret : RingBinarySecret 1 (prefixDimension + suffixDimension)) :
    evalDist (generateBootstrappingKey q prefixDimension suffixDimension levels
        errorSampler gadget ringSecret) =
      evalDist (generateSplitBootstrappingKey q prefixDimension suffixDimension levels
        errorSampler gadget ringSecret) := by
  rw [generateBootstrappingKey_evalDist_eq_selfMonomial,
    generateSelfMonomialBootstrappingKey_eq_split]

/-- Cloud view retaining only the affine and Boolean-diagonal BRK phases, together with the real
shared-randomness KSK. -/
def diagonalOnlyCloudKeyView
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    ProbComp (CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels) := do
  let ringSecret ← Native.sampleRingSecret 1 (prefixDimension + suffixDimension)
  let bootstrappingKey ←
    generateDiagonalOnlyBootstrappingKey q prefixDimension suffixDimension tgswLevels
      ringErrorSampler tgswGadget ringSecret
  let keySwitchKey ← generateKeySwitchKey q prefixDimension suffixDimension keySwitchLevels
    keySwitchErrorSampler keySwitchGadget ringSecret
  return ⟨bootstrappingKey, keySwitchKey⟩

/-- Cloud view with the real BRK written in split form. -/
def splitCloudKeyView
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    ProbComp (CloudKey q prefixDimension suffixDimension tgswLevels keySwitchLevels) := do
  let ringSecret ← Native.sampleRingSecret 1 (prefixDimension + suffixDimension)
  let bootstrappingKey ← generateSplitBootstrappingKey q prefixDimension suffixDimension
    tgswLevels ringErrorSampler tgswGadget ringSecret
  let keySwitchKey ← generateKeySwitchKey q prefixDimension suffixDimension keySwitchLevels
    keySwitchErrorSampler keySwitchGadget ringSecret
  return ⟨bootstrappingKey, keySwitchKey⟩

/-- The honest native cloud view is exactly its diagonal-plus-square-free presentation. -/
theorem realCloudKeyView_evalDist_eq_split
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q) :
    evalDist (realCloudKeyView q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget) =
      evalDist (splitCloudKeyView q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget) := by
  unfold realCloudKeyView generateCloudKey splitCloudKeyView
  refine evalDist_bind_congr'
    (Native.sampleRingSecret 1 (prefixDimension + suffixDimension)) fun ringSecret ↦ ?_
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (generateBootstrappingKey_evalDist_eq_split q prefixDimension suffixDimension
      tgswLevels ringErrorSampler tgswGadget ringSecret)
    (fun bootstrappingKey ↦
      generateKeySwitchKey q prefixDimension suffixDimension keySwitchLevels
          keySwitchErrorSampler keySwitchGadget ringSecret >>= fun keySwitchKey ↦
        pure (CloudKey.mk bootstrappingKey keySwitchKey))

/-- Diagonal-only intermediate experiment. -/
def diagonalOnlyGame
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : Adversary q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    ProbComp Bool :=
  diagonalOnlyCloudKeyView q prefixDimension suffixDimension tgswLevels keySwitchLevels
    ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget >>= adversary

/-- Split-form real experiment, used only to expose exact distribution preservation. -/
def splitGame
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : Adversary q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    ProbComp Bool :=
  splitCloudKeyView q prefixDimension suffixDimension tgswLevels keySwitchLevels
    ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget >>= adversary

/-- The original real game is exactly the split-form real game. -/
theorem realGame_evalDist_eq_splitGame
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : Adversary q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    evalDist (realGame q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary) =
      evalDist (splitGame q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary) := by
  unfold realGame splitGame
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (realCloudKeyView_evalDist_eq_split q prefixDimension suffixDimension tgswLevels
      keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget)
    adversary

/-- Exact fixed-table square-free KDM advantage: remove only the distinct-coordinate products. -/
def squareFreeAdvantage
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : Adversary q prefixDimension suffixDimension tgswLevels keySwitchLevels) : ℝ :=
  (realGame q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary).boolDistAdvantage
    (diagonalOnlyGame q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary)

/-- Remaining coefficient-affine circular advantage after the square-free table is removed. -/
def diagonalAdvantage
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : Adversary q prefixDimension suffixDimension tgswLevels keySwitchLevels) : ℝ :=
  (diagonalOnlyGame q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary).boolDistAdvantage
    (bootstrapZeroGame q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary)

/-- **Exact restricted-degree security boundary.**  One-circular TFHE security costs the fixed
square-free outer-product hybrid plus the diagonal coefficient-affine hybrid; no arbitrary
degree-two KDM family appears. -/
theorem oneCircularAdvantage_le_squareFree_add_diagonal
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (adversary : Adversary q prefixDimension suffixDimension tgswLevels keySwitchLevels) :
    oneCircularAdvantage q prefixDimension suffixDimension tgswLevels keySwitchLevels
        ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary ≤
      squareFreeAdvantage q prefixDimension suffixDimension tgswLevels keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary +
        diagonalAdvantage q prefixDimension suffixDimension tgswLevels keySwitchLevels
          ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary := by
  unfold oneCircularAdvantage squareFreeAdvantage diagonalAdvantage
    ProbComp.boolDistAdvantage
  exact abs_sub_le
    (Pr[= true | realGame q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary]).toReal
    (Pr[= true | diagonalOnlyGame q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary]).toReal
    (Pr[= true | bootstrapZeroGame q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary]).toReal

/-- Hardness interface for the fixed square-free table only. -/
def SquareFreeHardAgainst
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (allowed : Adversary q prefixDimension suffixDimension tgswLevels keySwitchLevels → Prop)
    (bound : ℝ) : Prop :=
  ∀ adversary, allowed adversary →
    squareFreeAdvantage q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary ≤ bound

/-- Hardness interface for the diagonal-only circular table. -/
def DiagonalHardAgainst
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (allowed : Adversary q prefixDimension suffixDimension tgswLevels keySwitchLevels → Prop)
    (bound : ℝ) : Prop :=
  ∀ adversary, allowed adversary →
    diagonalAdvantage q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget adversary ≤ bound

/-- Bounds for the two exact restricted components imply the original one-circular bound. -/
theorem oneCircularHardAgainst_of_squareFree_and_diagonal
    (q prefixDimension suffixDimension tgswLevels keySwitchLevels : ℕ) [NeZero q]
    (ringErrorSampler : ProbComp (RLWE.Rq q (prefixDimension + suffixDimension)))
    (keySwitchErrorSampler : ProbComp (ZMod q))
    (tgswGadget : Fin tgswLevels → RLWE.Rq q (prefixDimension + suffixDimension))
    (keySwitchGadget : Fin keySwitchLevels → ZMod q)
    (allowed : Adversary q prefixDimension suffixDimension tgswLevels keySwitchLevels → Prop)
    (squareFreeBound diagonalBound : ℝ)
    (hSquareFree : SquareFreeHardAgainst q prefixDimension suffixDimension tgswLevels
      keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
      allowed squareFreeBound)
    (hDiagonal : DiagonalHardAgainst q prefixDimension suffixDimension tgswLevels
      keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget
      allowed diagonalBound) :
    OneCircularHardAgainst q prefixDimension suffixDimension tgswLevels keySwitchLevels
      ringErrorSampler keySwitchErrorSampler tgswGadget keySwitchGadget allowed
      (squareFreeBound + diagonalBound) := by
  intro adversary hadversary
  exact (oneCircularAdvantage_le_squareFree_add_diagonal q prefixDimension suffixDimension
    tgswLevels keySwitchLevels ringErrorSampler keySwitchErrorSampler tgswGadget
    keySwitchGadget adversary).trans
      (add_le_add (hSquareFree adversary hadversary) (hDiagonal adversary hadversary))

end

end FormalProof4FHE.TFHE.Native.SharedRandomnessOneCycle.SquareFreeSecurity
