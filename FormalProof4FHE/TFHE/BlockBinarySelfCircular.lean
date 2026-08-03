/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.BlockBinary
import FormalProof4FHE.TFHE.SharedRandomnessOneCycleSquareFreeSecurity

set_option autoImplicit false

/-!
# Block-binary self-circular native TFHE

This file performs the technical specialization of the native one-key BRK boundary to the
block-binary secret law used by the implementation.  A compact block key is packed into one
binary negacyclic polynomial.  The ordinary diagonal/square-free split then sharpens exactly:
all distinct-coordinate products inside one block vanish, so the square-free remainder is
supported only on pairs of different blocks.

The second half defines a BRK-only, auxiliary-input experiment.  It contains no key-switch key:
the scalar input key and the rank-one ring key are the same packed block key.  Its triangle
theorems stop at two explicit cryptographic hypotheses--cross-block square-free security and
diagonal coefficient-affine security--plus a caller-supplied zero-BRK endpoint.  Thus the module
does not disguise any of those research obligations as an ordinary RLWE theorem.

The implementation samples an integer in the inclusive interval `0 .. blockLength`, using the
last value for the zero block.  The proof representation instead uses `0` for zero.  The final
section gives the exact coordinatewise permutation between the two representations and proves
that it transports the uniform implementation law to the proof law.
-/

open Matrix OracleComp

namespace FormalProof4FHE.TFHE.Native.BlockBinarySelfCircular

open Native.FullBRKQuadraticSpan

noncomputable section

/-! ## Exact key packing -/

/-- Ring degree occupied by a compact block-binary key. -/
abbrev degree (blockLength blockCount : ℕ) : ℕ := blockCount * blockLength

/-- Flatten one block/offset pair in the same order as `BlockBinary.bits`. -/
def coordinate {blockLength blockCount : ℕ}
    (block : Fin blockCount) (offset : Fin blockLength) :
    Fin (degree blockLength blockCount) :=
  finProdFinEquiv (block, offset)

/-- Recover the block containing a flattened coefficient. -/
def coordinateBlock {blockLength blockCount : ℕ}
    (index : Fin (degree blockLength blockCount)) : Fin blockCount :=
  (finProdFinEquiv.symm index).1

/-- Recover the within-block offset of a flattened coefficient. -/
def coordinateOffset {blockLength blockCount : ℕ}
    (index : Fin (degree blockLength blockCount)) : Fin blockLength :=
  (finProdFinEquiv.symm index).2

@[simp]
theorem coordinateBlock_coordinate {blockLength blockCount : ℕ}
    (block : Fin blockCount) (offset : Fin blockLength) :
    coordinateBlock (coordinate block offset) = block := by
  simp [coordinateBlock, coordinate]

@[simp]
theorem coordinateOffset_coordinate {blockLength blockCount : ℕ}
    (block : Fin blockCount) (offset : Fin blockLength) :
    coordinateOffset (coordinate block offset) = offset := by
  simp [coordinateOffset, coordinate]

@[simp]
theorem coordinate_roundtrip {blockLength blockCount : ℕ}
    (index : Fin (degree blockLength blockCount)) :
    coordinate (coordinateBlock index) (coordinateOffset index) = index := by
  exact finProdFinEquiv.apply_symm_apply index

/-- Pack a compact block key as the coefficient vector of one rank-one native ring key. -/
def packedRingSecret {blockLength blockCount : ℕ}
    (key : BlockBinary.Key blockLength blockCount) :
    RingBinarySecret 1 (degree blockLength blockCount) :=
  fun _ index => BlockBinary.bits key index

@[simp]
theorem packedRingSecret_apply {blockLength blockCount : ℕ}
    (key : BlockBinary.Key blockLength blockCount)
    (component : Fin 1) (index : Fin (degree blockLength blockCount)) :
    packedRingSecret key component index = BlockBinary.bits key index :=
  rfl

@[simp]
theorem prefixSecret_packedRingSecret {blockLength blockCount : ℕ}
    (key : BlockBinary.Key blockLength blockCount) :
    Native.SharedRandomnessOneCycle.prefixSecret
        (prefixDimension := degree blockLength blockCount) (suffixDimension := 0)
        (packedRingSecret key) =
      BlockBinary.bits key := by
  funext index
  simp [Native.SharedRandomnessOneCycle.prefixSecret, packedRingSecret]

@[simp]
theorem bits_coordinate {blockLength blockCount : ℕ}
    (key : BlockBinary.Key blockLength blockCount)
    (block : Fin blockCount) (offset : Fin blockLength) :
    BlockBinary.bits key (coordinate block offset) =
      BlockBinary.pairedBits key (block, offset) := by
  simp [BlockBinary.bits, coordinate]

/-- Ring embeddings of two distinct coordinates in one block multiply to zero. -/
theorem embedBits_mul_eq_zero_of_same_block
    {R : Type} [Semiring R] {blockLength blockCount : ℕ}
    (key : BlockBinary.Key blockLength blockCount)
    (block : Fin blockCount) (first second : Fin blockLength)
    (hne : first ≠ second) :
    (embedBit (BlockBinary.bits key (coordinate block first)) : R) *
        embedBit (BlockBinary.bits key (coordinate block second)) = 0 := by
  rw [bits_coordinate, bits_coordinate]
  by_cases hfirst : BlockBinary.pairedBits key (block, first) = true
  · by_cases hsecond : BlockBinary.pairedBits key (block, second) = true
    · exact (hne (BlockBinary.pairedBits_atMostOne key block hfirst hsecond)).elim
    · have hsecondFalse := Bool.eq_false_of_not_eq_true hsecond
      simp [embedBit, hfirst, hsecondFalse]
  · have hfirstFalse := Bool.eq_false_of_not_eq_true hfirst
    simp [embedBit, hfirstFalse]

/-- Coordinate-generic form of the same-block annihilation law. -/
theorem embedBits_mul_eq_zero_of_coordinateBlock_eq
    {R : Type} [Semiring R] {blockLength blockCount : ℕ}
    (key : BlockBinary.Key blockLength blockCount)
    (first second : Fin (degree blockLength blockCount))
    (hsame : coordinateBlock first = coordinateBlock second)
    (hne : first ≠ second) :
    (embedBit (BlockBinary.bits key first) : R) *
        embedBit (BlockBinary.bits key second) = 0 := by
  obtain ⟨⟨firstBlock, firstOffset⟩, rfl⟩ := finProdFinEquiv.surjective first
  obtain ⟨⟨secondBlock, secondOffset⟩, rfl⟩ := finProdFinEquiv.surjective second
  change coordinateBlock (coordinate firstBlock firstOffset) =
    coordinateBlock (coordinate secondBlock secondOffset) at hsame
  simp only [coordinateBlock_coordinate] at hsame
  subst secondBlock
  apply embedBits_mul_eq_zero_of_same_block
  intro hoffset
  apply hne
  simp [hoffset]

/-! ## Square-free support is exactly cross-block support -/

/-- Generic coefficient formula for the degree-generic square-free remainder on a
non-diagonal coordinate. -/
@[simp]
theorem squareFreeCrossAtDegree_coefficient_of_not_diagonal
    (q ringDegree ringRank : ℕ) [NeZero q]
    (ringSecret : RingBinarySecret ringRank ringDegree)
    (messageComponent maskComponent : Fin ringRank)
    (messageCoefficient maskCoefficient : Fin ringDegree)
    (hnotDiagonal : ¬ (maskComponent = messageComponent ∧
      maskCoefficient = messageCoefficient)) :
    LatticeCrypto.Poly.toPi
        (squareFreeCrossAtDegree q ringDegree ringRank ringSecret messageComponent
          messageCoefficient maskComponent) maskCoefficient =
      (embedBit (ringSecret maskComponent maskCoefficient) : ZMod q) *
        embedBit (ringSecret messageComponent messageCoefficient) := by
  cases ringDegree with
  | zero => exact messageCoefficient.elim0
  | succ ringDegree =>
      rw [squareFreeCrossAtDegree_succ_eq_squareFreeCross]
      exact extractedSquareFreePart_coefficient_of_not_diagonal q ringDegree ringRank
        ringSecret messageComponent maskComponent messageCoefficient maskCoefficient
        hnotDiagonal

/-- Generic diagonal coefficient of the degree-generic square-free remainder. -/
@[simp]
theorem squareFreeCrossAtDegree_diagonal_coefficient
    (q ringDegree ringRank : ℕ) [NeZero q]
    (ringSecret : RingBinarySecret ringRank ringDegree)
    (component : Fin ringRank) (coefficient : Fin ringDegree) :
    LatticeCrypto.Poly.toPi
        (squareFreeCrossAtDegree q ringDegree ringRank ringSecret component coefficient
          component) coefficient = 0 := by
  cases ringDegree with
  | zero => exact coefficient.elim0
  | succ ringDegree =>
      rw [squareFreeCrossAtDegree_succ_eq_squareFreeCross]
      exact extractedSquareFreePart_diagonal_coefficient q ringDegree ringRank ringSecret
        component coefficient

/-- Explicit cross-block part of one packed self-key outer product. -/
def crossBlockCross
    (q blockLength blockCount : ℕ)
    (key : BlockBinary.Key blockLength blockCount)
    (messageCoordinate : Fin (degree blockLength blockCount)) :
    Fin 1 → RLWE.Rq q (degree blockLength blockCount) :=
  fun _ => LatticeCrypto.Poly.ofPi fun maskCoordinate =>
    if coordinateBlock maskCoordinate = coordinateBlock messageCoordinate then 0
    else
      (embedBit (BlockBinary.bits key maskCoordinate) : ZMod q) *
        embedBit (BlockBinary.bits key messageCoordinate)

@[simp]
theorem crossBlockCross_coefficient
    (q blockLength blockCount : ℕ)
    (key : BlockBinary.Key blockLength blockCount)
    (messageCoordinate maskCoordinate : Fin (degree blockLength blockCount))
    (component : Fin 1) :
    LatticeCrypto.Poly.toPi
        (crossBlockCross q blockLength blockCount key messageCoordinate component)
        maskCoordinate =
      if coordinateBlock maskCoordinate = coordinateBlock messageCoordinate then 0
      else
        (embedBit (BlockBinary.bits key maskCoordinate) : ZMod q) *
          embedBit (BlockBinary.bits key messageCoordinate) := by
  simp [crossBlockCross]

/-- For a packed block-binary key, the entire nominal square-free remainder is exactly the
cross-block table.  Same-block off-diagonal products have disappeared, not merely been hidden
behind a later security assumption. -/
theorem squareFreeCrossAtDegree_packed_eq_crossBlockCross
    (q blockLength blockCount : ℕ) [NeZero q]
    (key : BlockBinary.Key blockLength blockCount)
    (messageCoordinate : Fin (degree blockLength blockCount)) :
    squareFreeCrossAtDegree q (degree blockLength blockCount) 1
        (packedRingSecret key) 0 messageCoordinate =
      crossBlockCross q blockLength blockCount key messageCoordinate := by
  funext component
  apply (Native.CoefficientStructuredLWE.coefficientEquiv q
    (degree blockLength blockCount)).injective
  funext maskCoordinate
  change LatticeCrypto.Poly.toPi
      (squareFreeCrossAtDegree q (degree blockLength blockCount) 1
        (packedRingSecret key) 0 messageCoordinate component) maskCoordinate =
    LatticeCrypto.Poly.toPi
      (crossBlockCross q blockLength blockCount key messageCoordinate component)
        maskCoordinate
  rw [crossBlockCross_coefficient]
  have hcomponent : component = 0 := Subsingleton.elim _ _
  subst component
  by_cases hsame : coordinateBlock maskCoordinate = coordinateBlock messageCoordinate
  · rw [if_pos hsame]
    by_cases hcoordinate : maskCoordinate = messageCoordinate
    · subst maskCoordinate
      exact squareFreeCrossAtDegree_diagonal_coefficient q
        (degree blockLength blockCount) 1 (packedRingSecret key) 0 messageCoordinate
    · rw [squareFreeCrossAtDegree_coefficient_of_not_diagonal]
      · exact embedBits_mul_eq_zero_of_coordinateBlock_eq key maskCoordinate
          messageCoordinate hsame hcoordinate
      · simp [hcoordinate]
  · rw [if_neg hsame, squareFreeCrossAtDegree_coefficient_of_not_diagonal]
    · simp [packedRingSecret]
    · intro hdiagonal
      exact hsame (congrArg coordinateBlock hdiagonal.2)

/-! ## Exact native phase and BRK split -/

/-- Affine body term plus the unique Boolean diagonal for one packed self-key message. -/
def diagonalPhase
    (q blockLength blockCount levels : ℕ)
    (key : BlockBinary.Key blockLength blockCount)
    (gadget : Fin levels → RLWE.Rq q (degree blockLength blockCount))
    (messageCoordinate : Fin (degree blockLength blockCount)) :
    Fin (TGSW.rowCount 1 levels) → RLWE.Rq q (degree blockLength blockCount) :=
  TGSW.CircularBoundary.affinePhasePart gadget
      (embedConstantBit q (degree blockLength blockCount)
        (BlockBinary.bits key messageCoordinate)) +
    TGSW.MonomialKDM.monomialPhasePart gadget
      (diagonalCrossAtDegree q (degree blockLength blockCount) 1
        (packedRingSecret key) 0 messageCoordinate)

/-- The genuinely nonlinear phase, now containing cross-block products only. -/
def crossBlockPhase
    (q blockLength blockCount levels : ℕ)
    (key : BlockBinary.Key blockLength blockCount)
    (gadget : Fin levels → RLWE.Rq q (degree blockLength blockCount))
    (messageCoordinate : Fin (degree blockLength blockCount)) :
    Fin (TGSW.rowCount 1 levels) → RLWE.Rq q (degree blockLength blockCount) :=
  TGSW.MonomialKDM.monomialPhasePart gadget
    (crossBlockCross q blockLength blockCount key messageCoordinate)

/-- Full block-aware direct phase. -/
def splitPhase
    (q blockLength blockCount levels : ℕ)
    (key : BlockBinary.Key blockLength blockCount)
    (gadget : Fin levels → RLWE.Rq q (degree blockLength blockCount))
    (messageCoordinate : Fin (degree blockLength blockCount)) :
    Fin (TGSW.rowCount 1 levels) → RLWE.Rq q (degree blockLength blockCount) :=
  diagonalPhase q blockLength blockCount levels key gadget messageCoordinate +
    crossBlockPhase q blockLength blockCount levels key gadget messageCoordinate

/-- Every native self-key gadget phase is exactly diagonal plus cross-block, coefficient by
coefficient and without a distributional approximation. -/
theorem gadgetPhase_packed_eq_splitPhase
    (q blockLength blockCount levels : ℕ) [NeZero q]
    (key : BlockBinary.Key blockLength blockCount)
    (gadget : Fin levels → RLWE.Rq q (degree blockLength blockCount))
    (messageCoordinate : Fin (degree blockLength blockCount)) :
    TGSW.gadgetPhase (embedRingSecret q (packedRingSecret key)) gadget
        (embedConstantBit q (degree blockLength blockCount)
          (BlockBinary.bits key messageCoordinate)) =
      splitPhase q blockLength blockCount levels key gadget messageCoordinate := by
  have hphase := gadgetPhase_self_eq_diagonalAtDegree_add_squareFreeAtDegree
    q (degree blockLength blockCount) 1 levels (packedRingSecret key) gadget 0
      messageCoordinate
  rw [squareFreeCrossAtDegree_packed_eq_crossBlockCross] at hphase
  simpa [splitPhase, diagonalPhase, crossBlockPhase, packedRingSecret] using hphase

/-- BRK carrier for the self-key block-binary construction. -/
abbrev BootstrappingKey
    (q blockLength blockCount levels : ℕ) :=
  Native.BootstrappingKey q (degree blockLength blockCount) 1 levels
    (degree blockLength blockCount)

/-- Honest native self-key BRK. -/
noncomputable def generateBootstrappingKey
    (q blockLength blockCount levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree blockLength blockCount)))
    (gadget : Fin levels → RLWE.Rq q (degree blockLength blockCount))
    (key : BlockBinary.Key blockLength blockCount) :
    ProbComp (BootstrappingKey q blockLength blockCount levels) :=
  Native.generateBootstrappingKey q (degree blockLength blockCount) 1 levels
    (degree blockLength blockCount) errorSampler gadget (BlockBinary.bits key)
      (packedRingSecret key)

/-- Direct honest BRK presentation used only for exact normalization. -/
noncomputable def generateDirectBootstrappingKey
    (q blockLength blockCount levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree blockLength blockCount)))
    (gadget : Fin levels → RLWE.Rq q (degree blockLength blockCount))
    (key : BlockBinary.Key blockLength blockCount) :
    ProbComp (BootstrappingKey q blockLength blockCount levels) :=
  Native.BootstrapSecurity.generateDirectBootstrappingKey q
    (degree blockLength blockCount) 1 levels (degree blockLength blockCount)
      errorSampler gadget (BlockBinary.bits key) (packedRingSecret key)

/-- One direct entry retaining only the affine and diagonal phase. -/
def diagonalOnlyEntry
    (q blockLength blockCount levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree blockLength blockCount)))
    (gadget : Fin levels → RLWE.Rq q (degree blockLength blockCount))
    (key : BlockBinary.Key blockLength blockCount)
    (messageCoordinate : Fin (degree blockLength blockCount)) :
    ProbComp (RingGSWCiphertext q (degree blockLength blockCount) 1 levels) :=
  TLWE.batchEncrypt 1 (TGSW.rowCount 1 levels) errorSampler
    (embedRingSecret q (packedRingSecret key))
    (diagonalPhase q blockLength blockCount levels key gadget messageCoordinate)

/-- One direct entry with diagonal and cross-block phases displayed separately. -/
def splitEntry
    (q blockLength blockCount levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree blockLength blockCount)))
    (gadget : Fin levels → RLWE.Rq q (degree blockLength blockCount))
    (key : BlockBinary.Key blockLength blockCount)
    (messageCoordinate : Fin (degree blockLength blockCount)) :
    ProbComp (RingGSWCiphertext q (degree blockLength blockCount) 1 levels) :=
  TLWE.batchEncrypt 1 (TGSW.rowCount 1 levels) errorSampler
    (embedRingSecret q (packedRingSecret key))
    (splitPhase q blockLength blockCount levels key gadget messageCoordinate)

/-- Complete diagonal-only BRK. -/
def generateDiagonalOnlyBootstrappingKey
    (q blockLength blockCount levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree blockLength blockCount)))
    (gadget : Fin levels → RLWE.Rq q (degree blockLength blockCount))
    (key : BlockBinary.Key blockLength blockCount) :
    ProbComp (BootstrappingKey q blockLength blockCount levels) :=
  Fin.mOfFn (degree blockLength blockCount) fun messageCoordinate =>
    diagonalOnlyEntry q blockLength blockCount levels errorSampler gadget key
      messageCoordinate

/-- Complete BRK in exact block-aware split form. -/
def generateSplitBootstrappingKey
    (q blockLength blockCount levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree blockLength blockCount)))
    (gadget : Fin levels → RLWE.Rq q (degree blockLength blockCount))
    (key : BlockBinary.Key blockLength blockCount) :
    ProbComp (BootstrappingKey q blockLength blockCount levels) :=
  Fin.mOfFn (degree blockLength blockCount) fun messageCoordinate =>
    splitEntry q blockLength blockCount levels errorSampler gadget key messageCoordinate

/-- Format-identical all-zero-message BRK. -/
noncomputable def generateZeroBootstrappingKey
    (q blockLength blockCount levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree blockLength blockCount)))
    (gadget : Fin levels → RLWE.Rq q (degree blockLength blockCount))
    (key : BlockBinary.Key blockLength blockCount) :
    ProbComp (BootstrappingKey q blockLength blockCount levels) :=
  Native.generateZeroBootstrappingKey q (degree blockLength blockCount) 1 levels
    (degree blockLength blockCount) errorSampler gadget (packedRingSecret key)

/-- The direct honest BRK is literally the block-aware split sampler. -/
theorem generateDirectBootstrappingKey_eq_split
    (q blockLength blockCount levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree blockLength blockCount)))
    (gadget : Fin levels → RLWE.Rq q (degree blockLength blockCount))
    (key : BlockBinary.Key blockLength blockCount) :
    generateDirectBootstrappingKey q blockLength blockCount levels errorSampler gadget key =
      generateSplitBootstrappingKey q blockLength blockCount levels errorSampler gadget key := by
  unfold generateDirectBootstrappingKey generateSplitBootstrappingKey
    Native.BootstrapSecurity.generateDirectBootstrappingKey
  congr 1
  funext messageCoordinate
  unfold TGSW.directEncrypt splitEntry
  rw [gadgetPhase_packed_eq_splitPhase]

/-- The actual structured native BRK and the block-aware split BRK have identical laws. -/
theorem generateBootstrappingKey_evalDist_eq_split
    (q blockLength blockCount levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree blockLength blockCount)))
    (gadget : Fin levels → RLWE.Rq q (degree blockLength blockCount))
    (key : BlockBinary.Key blockLength blockCount) :
    evalDist
        (generateBootstrappingKey q blockLength blockCount levels errorSampler gadget key) =
      evalDist
        (generateSplitBootstrappingKey q blockLength blockCount levels
          errorSampler gadget key) := by
  calc
    _ = evalDist
        (generateDirectBootstrappingKey q blockLength blockCount levels
          errorSampler gadget key) :=
      Native.BootstrapSecurity.generateBootstrappingKey_evalDist_eq_direct
        q (degree blockLength blockCount) 1 levels (degree blockLength blockCount)
          errorSampler gadget (BlockBinary.bits key) (packedRingSecret key)
    _ = _ := congrArg evalDist
      (generateDirectBootstrappingKey_eq_split q blockLength blockCount levels
        errorSampler gadget key)

/-! ## BRK-only contextual one-circular games -/

/-- Public self-bootstrap material.  There is deliberately no key-switch-key field. -/
structure PublicView
    (q blockLength blockCount levels : ℕ) (Auxiliary : Type) where
  bootstrappingKey : BootstrappingKey q blockLength blockCount levels
  auxiliary : Auxiliary

/-- Sample a BRK and arbitrary same-key auxiliary input from one compact key. -/
def viewSampler
    {q blockLength blockCount levels : ℕ} [NeZero q] {Auxiliary : Type}
    (bootstrappingKeySampler : BlockBinary.Key blockLength blockCount →
      ProbComp (BootstrappingKey q blockLength blockCount levels))
    (auxiliarySampler : BlockBinary.Key blockLength blockCount → ProbComp Auxiliary) :
    ProbComp (PublicView q blockLength blockCount levels Auxiliary) := do
  let key ← $ᵗ (BlockBinary.Key blockLength blockCount)
  let bootstrappingKey ← bootstrappingKeySampler key
  let auxiliary ← auxiliarySampler key
  return ⟨bootstrappingKey, auxiliary⟩

/-- Honest self-key public view. -/
noncomputable def realView
    {Auxiliary : Type}
    (q blockLength blockCount levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree blockLength blockCount)))
    (gadget : Fin levels → RLWE.Rq q (degree blockLength blockCount))
    (auxiliarySampler : BlockBinary.Key blockLength blockCount → ProbComp Auxiliary) :
    ProbComp (PublicView q blockLength blockCount levels Auxiliary) :=
  viewSampler
    (generateBootstrappingKey q blockLength blockCount levels errorSampler gadget)
    auxiliarySampler

/-- Exact split-form honest public view. -/
def splitView
    {Auxiliary : Type}
    (q blockLength blockCount levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree blockLength blockCount)))
    (gadget : Fin levels → RLWE.Rq q (degree blockLength blockCount))
    (auxiliarySampler : BlockBinary.Key blockLength blockCount → ProbComp Auxiliary) :
    ProbComp (PublicView q blockLength blockCount levels Auxiliary) :=
  viewSampler
    (generateSplitBootstrappingKey q blockLength blockCount levels errorSampler gadget)
    auxiliarySampler

/-- Diagonal-only contextual hybrid. -/
def diagonalOnlyView
    {Auxiliary : Type}
    (q blockLength blockCount levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree blockLength blockCount)))
    (gadget : Fin levels → RLWE.Rq q (degree blockLength blockCount))
    (auxiliarySampler : BlockBinary.Key blockLength blockCount → ProbComp Auxiliary) :
    ProbComp (PublicView q blockLength blockCount levels Auxiliary) :=
  viewSampler
    (generateDiagonalOnlyBootstrappingKey q blockLength blockCount levels errorSampler gadget)
    auxiliarySampler

/-- Zero-message BRK endpoint with the same packed key and auxiliary-input law. -/
noncomputable def zeroView
    {Auxiliary : Type}
    (q blockLength blockCount levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree blockLength blockCount)))
    (gadget : Fin levels → RLWE.Rq q (degree blockLength blockCount))
    (auxiliarySampler : BlockBinary.Key blockLength blockCount → ProbComp Auxiliary) :
    ProbComp (PublicView q blockLength blockCount levels Auxiliary) :=
  viewSampler
    (generateZeroBootstrappingKey q blockLength blockCount levels errorSampler gadget)
    auxiliarySampler

/-- Exact distributional normalization survives arbitrary same-key auxiliary input. -/
theorem realView_evalDist_eq_splitView
    {Auxiliary : Type}
    (q blockLength blockCount levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree blockLength blockCount)))
    (gadget : Fin levels → RLWE.Rq q (degree blockLength blockCount))
    (auxiliarySampler : BlockBinary.Key blockLength blockCount → ProbComp Auxiliary) :
    evalDist (realView q blockLength blockCount levels errorSampler gadget auxiliarySampler) =
      evalDist
        (splitView q blockLength blockCount levels errorSampler gadget auxiliarySampler) := by
  unfold realView splitView viewSampler
  refine evalDist_bind_congr' ($ᵗ (BlockBinary.Key blockLength blockCount)) fun key => ?_
  exact FormalProof4FHE.SharedRandomness.evalDist_bind_eq_of_evalDist_eq
    (generateBootstrappingKey_evalDist_eq_split q blockLength blockCount levels
      errorSampler gadget key)
    (fun bootstrappingKey => auxiliarySampler key >>= fun auxiliary =>
      pure (PublicView.mk bootstrappingKey auxiliary))

/-- A contextual adversary receives only the BRK and auxiliary input; no IKS is present. -/
abbrev Adversary
    (q blockLength blockCount levels : ℕ) (Auxiliary : Type) :=
  PublicView q blockLength blockCount levels Auxiliary → ProbComp Bool

def realGame
    {Auxiliary : Type}
    (q blockLength blockCount levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree blockLength blockCount)))
    (gadget : Fin levels → RLWE.Rq q (degree blockLength blockCount))
    (auxiliarySampler : BlockBinary.Key blockLength blockCount → ProbComp Auxiliary)
    (adversary : Adversary q blockLength blockCount levels Auxiliary) : ProbComp Bool :=
  realView q blockLength blockCount levels errorSampler gadget auxiliarySampler >>= adversary

def diagonalOnlyGame
    {Auxiliary : Type}
    (q blockLength blockCount levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree blockLength blockCount)))
    (gadget : Fin levels → RLWE.Rq q (degree blockLength blockCount))
    (auxiliarySampler : BlockBinary.Key blockLength blockCount → ProbComp Auxiliary)
    (adversary : Adversary q blockLength blockCount levels Auxiliary) : ProbComp Bool :=
  diagonalOnlyView q blockLength blockCount levels errorSampler gadget auxiliarySampler >>=
    adversary

def zeroGame
    {Auxiliary : Type}
    (q blockLength blockCount levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree blockLength blockCount)))
    (gadget : Fin levels → RLWE.Rq q (degree blockLength blockCount))
    (auxiliarySampler : BlockBinary.Key blockLength blockCount → ProbComp Auxiliary)
    (adversary : Adversary q blockLength blockCount levels Auxiliary) : ProbComp Bool :=
  zeroView q blockLength blockCount levels errorSampler gadget auxiliarySampler >>= adversary

/-- The hard cross-block fixed-table term, retaining the complete same-key auxiliary input. -/
def crossBlockAdvantage
    {Auxiliary : Type}
    (q blockLength blockCount levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree blockLength blockCount)))
    (gadget : Fin levels → RLWE.Rq q (degree blockLength blockCount))
    (auxiliarySampler : BlockBinary.Key blockLength blockCount → ProbComp Auxiliary)
    (adversary : Adversary q blockLength blockCount levels Auxiliary) : ℝ :=
  ProbComp.boolDistAdvantage
    (realGame q blockLength blockCount levels errorSampler gadget auxiliarySampler adversary)
    (diagonalOnlyGame q blockLength blockCount levels errorSampler gadget auxiliarySampler
      adversary)

/-- The remaining diagonal coefficient-affine circular term. -/
def diagonalAdvantage
    {Auxiliary : Type}
    (q blockLength blockCount levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree blockLength blockCount)))
    (gadget : Fin levels → RLWE.Rq q (degree blockLength blockCount))
    (auxiliarySampler : BlockBinary.Key blockLength blockCount → ProbComp Auxiliary)
    (adversary : Adversary q blockLength blockCount levels Auxiliary) : ℝ :=
  (diagonalOnlyGame q blockLength blockCount levels errorSampler gadget auxiliarySampler
    adversary).boolDistAdvantage
  (zeroGame q blockLength blockCount levels errorSampler gadget auxiliarySampler adversary)

/-- Exact BRK-only one-circular replacement advantage. -/
def oneCircularAdvantage
    {Auxiliary : Type}
    (q blockLength blockCount levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree blockLength blockCount)))
    (gadget : Fin levels → RLWE.Rq q (degree blockLength blockCount))
    (auxiliarySampler : BlockBinary.Key blockLength blockCount → ProbComp Auxiliary)
    (adversary : Adversary q blockLength blockCount levels Auxiliary) : ℝ :=
  ProbComp.boolDistAdvantage
    (realGame q blockLength blockCount levels errorSampler gadget auxiliarySampler adversary)
    (zeroGame q blockLength blockCount levels errorSampler gadget auxiliarySampler adversary)

/-- Removing the self-key BRK costs exactly the cross-block and diagonal hybrids. -/
theorem oneCircularAdvantage_le_crossBlock_add_diagonal
    {Auxiliary : Type}
    (q blockLength blockCount levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree blockLength blockCount)))
    (gadget : Fin levels → RLWE.Rq q (degree blockLength blockCount))
    (auxiliarySampler : BlockBinary.Key blockLength blockCount → ProbComp Auxiliary)
    (adversary : Adversary q blockLength blockCount levels Auxiliary) :
    oneCircularAdvantage q blockLength blockCount levels errorSampler gadget
        auxiliarySampler adversary ≤
      crossBlockAdvantage q blockLength blockCount levels errorSampler gadget
          auxiliarySampler adversary +
        diagonalAdvantage q blockLength blockCount levels errorSampler gadget
          auxiliarySampler adversary := by
  unfold oneCircularAdvantage crossBlockAdvantage diagonalAdvantage
    ProbComp.boolDistAdvantage
  exact abs_sub_le
    (Pr[= true | realGame q blockLength blockCount levels errorSampler gadget
      auxiliarySampler adversary]).toReal
    (Pr[= true | diagonalOnlyGame q blockLength blockCount levels errorSampler gadget
      auxiliarySampler adversary]).toReal
    (Pr[= true | zeroGame q blockLength blockCount levels errorSampler gadget
      auxiliarySampler adversary]).toReal

/-- Hardness interface for the complete cross-block fixed table under the retained auxiliary
input. -/
def CrossBlockHardAgainst
    {Auxiliary : Type}
    (q blockLength blockCount levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree blockLength blockCount)))
    (gadget : Fin levels → RLWE.Rq q (degree blockLength blockCount))
    (auxiliarySampler : BlockBinary.Key blockLength blockCount → ProbComp Auxiliary)
    (allowed : Adversary q blockLength blockCount levels Auxiliary → Prop)
    (bound : ℝ) : Prop :=
  ∀ adversary, allowed adversary →
    crossBlockAdvantage q blockLength blockCount levels errorSampler gadget
      auxiliarySampler adversary ≤ bound

/-- Hardness interface for the diagonal coefficient-affine native table. -/
def DiagonalHardAgainst
    {Auxiliary : Type}
    (q blockLength blockCount levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree blockLength blockCount)))
    (gadget : Fin levels → RLWE.Rq q (degree blockLength blockCount))
    (auxiliarySampler : BlockBinary.Key blockLength blockCount → ProbComp Auxiliary)
    (allowed : Adversary q blockLength blockCount levels Auxiliary → Prop)
    (bound : ℝ) : Prop :=
  ∀ adversary, allowed adversary →
    diagonalAdvantage q blockLength blockCount levels errorSampler gadget
      auxiliarySampler adversary ≤ bound

/-- Hardness interface for the complete BRK-only one-circular replacement. -/
def OneCircularHardAgainst
    {Auxiliary : Type}
    (q blockLength blockCount levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree blockLength blockCount)))
    (gadget : Fin levels → RLWE.Rq q (degree blockLength blockCount))
    (auxiliarySampler : BlockBinary.Key blockLength blockCount → ProbComp Auxiliary)
    (allowed : Adversary q blockLength blockCount levels Auxiliary → Prop)
    (bound : ℝ) : Prop :=
  ∀ adversary, allowed adversary →
    oneCircularAdvantage q blockLength blockCount levels errorSampler gadget
      auxiliarySampler adversary ≤ bound

/-- Bounds for precisely the two remaining cryptographic components imply the no-IKS
one-circular bound. -/
theorem oneCircularHardAgainst_of_crossBlock_and_diagonal
    {Auxiliary : Type}
    (q blockLength blockCount levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree blockLength blockCount)))
    (gadget : Fin levels → RLWE.Rq q (degree blockLength blockCount))
    (auxiliarySampler : BlockBinary.Key blockLength blockCount → ProbComp Auxiliary)
    (allowed : Adversary q blockLength blockCount levels Auxiliary → Prop)
    (crossBlockBound diagonalBound : ℝ)
    (hCrossBlock : CrossBlockHardAgainst q blockLength blockCount levels errorSampler
      gadget auxiliarySampler allowed crossBlockBound)
    (hDiagonal : DiagonalHardAgainst q blockLength blockCount levels errorSampler gadget
      auxiliarySampler allowed diagonalBound) :
    OneCircularHardAgainst q blockLength blockCount levels errorSampler gadget
      auxiliarySampler allowed (crossBlockBound + diagonalBound) := by
  intro adversary hadversary
  exact (oneCircularAdvantage_le_crossBlock_add_diagonal q blockLength blockCount levels
    errorSampler gadget auxiliarySampler adversary).trans
      (add_le_add (hCrossBlock adversary hadversary) (hDiagonal adversary hadversary))

/-- Adding any caller-supplied ideal endpoint makes the ordinary zero-view obligation explicit. -/
theorem realGame_advantage_le_crossBlock_add_diagonal_add_zeroEndpoint
    {Auxiliary : Type}
    (q blockLength blockCount levels : ℕ) [NeZero q]
    (errorSampler : ProbComp (RLWE.Rq q (degree blockLength blockCount)))
    (gadget : Fin levels → RLWE.Rq q (degree blockLength blockCount))
    (auxiliarySampler : BlockBinary.Key blockLength blockCount → ProbComp Auxiliary)
    (adversary : Adversary q blockLength blockCount levels Auxiliary)
    (idealGame : ProbComp Bool) :
    ProbComp.boolDistAdvantage
        (realGame q blockLength blockCount levels errorSampler gadget auxiliarySampler adversary)
        idealGame ≤
      crossBlockAdvantage q blockLength blockCount levels errorSampler gadget
          auxiliarySampler adversary +
        diagonalAdvantage q blockLength blockCount levels errorSampler gadget
          auxiliarySampler adversary +
        ProbComp.boolDistAdvantage
          (zeroGame q blockLength blockCount levels errorSampler gadget auxiliarySampler adversary)
          idealGame := by
  unfold crossBlockAdvantage diagonalAdvantage ProbComp.boolDistAdvantage
  have hfirst := abs_sub_le
    (Pr[= true | realGame q blockLength blockCount levels errorSampler gadget
      auxiliarySampler adversary]).toReal
    (Pr[= true | diagonalOnlyGame q blockLength blockCount levels errorSampler gadget
      auxiliarySampler adversary]).toReal
    (Pr[= true | idealGame]).toReal
  have hsecond := abs_sub_le
    (Pr[= true | diagonalOnlyGame q blockLength blockCount levels errorSampler gadget
      auxiliarySampler adversary]).toReal
    (Pr[= true | zeroGame q blockLength blockCount levels errorSampler gadget
      auxiliarySampler adversary]).toReal
    (Pr[= true | idealGame]).toReal
  linarith

/-! ## Exact implementation-choice permutation -/

/-- Convert the implementation's raw inclusive choice (`blockLength` means zero) to the proof
choice (`0` means zero, successors select offsets). -/
def implementationChoiceEquiv (blockLength : ℕ) :
    Fin (blockLength + 1) ≃ Fin (blockLength + 1) :=
  (finSuccEquiv' (Fin.last blockLength)).trans (finSuccEquiv blockLength).symm

@[simp]
theorem implementationChoiceEquiv_castSucc
    {blockLength : ℕ} (offset : Fin blockLength) :
    implementationChoiceEquiv blockLength (Fin.castSucc offset) = offset.succ := by
  simp [implementationChoiceEquiv, Equiv.trans_apply,
    finSuccEquiv'_below (Fin.castSucc_lt_last offset)]

@[simp]
theorem implementationChoiceEquiv_last (blockLength : ℕ) :
    implementationChoiceEquiv blockLength (Fin.last blockLength) = 0 := by
  simp [implementationChoiceEquiv, Equiv.trans_apply, finSuccEquiv'_at]

/-- Apply the representation permutation independently to every block. -/
def implementationKeyEquiv (blockLength blockCount : ℕ) :
    BlockBinary.Key blockLength blockCount ≃ BlockBinary.Key blockLength blockCount where
  toFun raw block := implementationChoiceEquiv blockLength (raw block)
  invFun key block := (implementationChoiceEquiv blockLength).symm (key block)
  left_inv raw := by
    funext block
    exact (implementationChoiceEquiv blockLength).symm_apply_apply (raw block)
  right_inv key := by
    funext block
    exact (implementationChoiceEquiv blockLength).apply_symm_apply (key block)

/-- Boolean layout produced by the implementation's raw inclusive block choice. -/
def implementationPairedBits {blockLength blockCount : ℕ}
    (raw : BlockBinary.Key blockLength blockCount)
    (index : Fin blockCount × Fin blockLength) : Bool :=
  decide (raw index.1 = Fin.castSucc index.2)

/-- The representation permutation preserves the literal selected coefficient in every block. -/
@[simp]
theorem pairedBits_implementationKeyEquiv
    {blockLength blockCount : ℕ}
    (raw : BlockBinary.Key blockLength blockCount)
    (block : Fin blockCount) (offset : Fin blockLength) :
    BlockBinary.pairedBits (implementationKeyEquiv blockLength blockCount raw)
        (block, offset) = implementationPairedBits raw (block, offset) := by
  have hchoice :
      implementationChoiceEquiv blockLength (raw block) = offset.succ ↔
        raw block = Fin.castSucc offset := by
    constructor
    · intro h
      apply (implementationChoiceEquiv blockLength).injective
      exact h.trans (implementationChoiceEquiv_castSucc offset).symm
    · intro h
      rw [h]
      exact implementationChoiceEquiv_castSucc offset
  change decide
      (finSuccEquiv blockLength
          (implementationChoiceEquiv blockLength (raw block)) = some offset) =
    decide (raw block = Fin.castSucc offset)
  simp only [finSuccEquiv_eq_some]
  exact Bool.decide_congr hchoice

/-- Uniform raw implementation choices induce exactly the proof-side compact-key law. -/
theorem implementationKey_uniform_evalDist
    (blockLength blockCount : ℕ) :
    evalDist
        (implementationKeyEquiv blockLength blockCount <$>
          ($ᵗ (BlockBinary.Key blockLength blockCount))) =
      evalDist ($ᵗ (BlockBinary.Key blockLength blockCount)) := by
  simpa only using evalDist_map_bijective_uniform_cross
    (α := BlockBinary.Key blockLength blockCount)
    (β := BlockBinary.Key blockLength blockCount)
    (implementationKeyEquiv blockLength blockCount)
    (implementationKeyEquiv blockLength blockCount).bijective

end

end FormalProof4FHE.TFHE.Native.BlockBinarySelfCircular
