/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.Security
import FormalProof4FHE.Probability.LeftoverHash

/-!
# LWE with Block-Binary Secrets

This module formalizes the block-binary key distribution from Lee--Min--Seo--Song,
*Faster TFHE Bootstrapping with Block Binary Keys* (ePrint 2023/958), together with the
information-theoretic extraction step used by the weak-secret LWE reduction of
Goldwasser--Kalai--Peikert--Vaikuntanathan.

A key has `blockCount` blocks of length `blockLength`.  A block choice is either zero or one of
the `blockLength` standard basis vectors, represented by `Fin (blockLength + 1)` with `0` denoting
the zero vector.  Thus the key space has exactly `(blockLength + 1) ^ blockCount` elements.

Coordinates are flattened through `finProdFinEquiv`, so the resulting LWE secret has dimension
`blockCount * blockLength`.
-/

open Matrix OracleComp

namespace FormalProof4FHE.BlockBinary

/-- Compact block-binary keys: `0` is the all-zero choice in a block and `j.succ` selects
coordinate `j`. -/
abbrev Key (blockLength blockCount : ℕ) :=
  Fin blockCount → Fin (blockLength + 1)

/-- One-hot encoding of an optional coordinate. -/
def oneHot {blockLength : ℕ} (choice : Option (Fin blockLength))
    (coordinate : Fin blockLength) : Bool :=
  decide (choice = some coordinate)

/-- The bits of a compact block key, indexed first by block and then by position in the block. -/
def pairedBits {blockLength blockCount : ℕ} (key : Key blockLength blockCount)
    (coordinate : Fin blockCount × Fin blockLength) : Bool :=
  oneHot (finSuccEquiv blockLength (key coordinate.1)) coordinate.2

/-- The flattened bit-vector represented by a compact block key. -/
def bits {blockLength blockCount : ℕ} (key : Key blockLength blockCount) :
    Fin (blockCount * blockLength) → Bool :=
  pairedBits key ∘ finProdFinEquiv.symm

/-- Embed a block-binary key into a coefficient ring as a zero-one vector. -/
def expand (R : Type) [Zero R] [One R] {blockLength blockCount : ℕ}
    (key : Key blockLength blockCount) : Fin (blockCount * blockLength) → R :=
  fun coordinate ↦ if bits key coordinate then 1 else 0

/-- Every block has at most one nonzero coordinate. -/
theorem pairedBits_atMostOne {blockLength blockCount : ℕ}
    (key : Key blockLength blockCount) (block : Fin blockCount)
    {i j : Fin blockLength} (hi : pairedBits key (block, i) = true)
    (hj : pairedBits key (block, j) = true) : i = j := by
  have hi' : finSuccEquiv blockLength (key block) = some i :=
    of_decide_eq_true hi
  have hj' : finSuccEquiv blockLength (key block) = some j :=
    of_decide_eq_true hj
  exact Option.some.inj (hi'.symm.trans hj')

/-- One-hot encoding does not lose the zero/basis-vector choice. -/
theorem oneHot_injective (blockLength : ℕ) :
    Function.Injective (oneHot (blockLength := blockLength)) := by
  intro first second h
  cases first with
  | none =>
      cases second with
      | none => rfl
      | some coordinate =>
          have hcoordinate := congrFun h coordinate
          simp [oneHot] at hcoordinate
  | some coordinate =>
      cases second with
      | none =>
          have hcoordinate := congrFun h coordinate
          simp [oneHot] at hcoordinate
      | some coordinate' =>
          have hcoordinate := congrFun h coordinate
          simp [oneHot] at hcoordinate
          subst coordinate'
          rfl

/-- The flattened bits uniquely determine the compact block key. -/
theorem bits_injective (blockLength blockCount : ℕ) :
    Function.Injective (bits (blockLength := blockLength) (blockCount := blockCount)) := by
  intro first second h
  funext block
  apply (finSuccEquiv blockLength).injective
  apply oneHot_injective blockLength
  funext coordinate
  have hcoordinate := congrFun h (finProdFinEquiv (block, coordinate))
  simpa [bits, pairedBits, Function.comp_def] using hcoordinate

/-- The block-key space has exactly `(blockLength + 1) ^ blockCount` elements. -/
theorem card_key (blockLength blockCount : ℕ) :
    Fintype.card (Key blockLength blockCount) =
      (blockLength + 1) ^ blockCount := by
  simp [Key]

/-- Hash a block key by a public random matrix.  This is binary subset-sum hashing after the
one-hot expansion. -/
def extractorHash {R : Type} [AddCommMonoid R]
    {blockLength blockCount extractedDimension : ℕ}
    (matrix : Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R)
    (key : Key blockLength blockCount) : Fin extractedDimension → R :=
  FormalProof4FHE.LeftoverHash.binarySubsetSum matrix (bits key)

/-- The subset-sum presentation of the extractor is the usual vector-matrix product. -/
theorem extractorHash_eq_vecMul {R : Type} [Semiring R]
    {blockLength blockCount extractedDimension : ℕ}
    (matrix : Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R)
    (key : Key blockLength blockCount) :
    extractorHash matrix key = vecMul (expand R key) matrix := by
  funext coordinate
  simp only [extractorHash, FormalProof4FHE.LeftoverHash.binarySubsetSum,
    Matrix.vecMul, dotProduct]
  refine (Fintype.sum_apply coordinate
    (fun coordinate' : Fin (blockCount * blockLength) ↦
      if bits key coordinate' then matrix coordinate' else 0)).trans ?_
  apply Finset.sum_congr rfl
  intro coordinate' _
  by_cases hbit : bits key coordinate' <;> simp [hbit, expand]

/-- Random matrix multiplication is two-universal on compact block keys. -/
theorem extractorHash_isTwoUniversal {R : Type}
    [Fintype R] [DecidableEq R] [AddCommGroup R]
    (blockLength blockCount extractedDimension : ℕ) :
    FormalProof4FHE.LeftoverHash.IsTwoUniversal
      (Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R)
      (Key blockLength blockCount) (Fin extractedDimension → R)
      extractorHash := by
  intro first second hne
  exact FormalProof4FHE.LeftoverHash.binarySubsetSum_isTwoUniversal
    (bits first) (bits second) ((bits_injective blockLength blockCount).ne hne)

/-- Concrete leftover-hash bound for block-binary keys.

The numerator is the extracted secret-space size `|R| ^ extractedDimension`; the denominator is
the exact block-key-space size `(blockLength + 1) ^ blockCount`. -/
theorem extractorHash_leftover {R : Type}
    [Fintype R] [Nonempty R] [DecidableEq R] [SampleableType R] [AddCommGroup R]
    (blockLength blockCount extractedDimension : ℕ) :
    tvDist
        (do
          let matrix ← $ᵗ Matrix (Fin (blockCount * blockLength))
            (Fin extractedDimension) R
          let key ← $ᵗ (Key blockLength blockCount)
          return (matrix, extractorHash matrix key))
        ($ᵗ (Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R ×
          (Fin extractedDimension → R))) ≤
      Real.sqrt
          ((Fintype.card R : ℝ) ^ extractedDimension /
            (blockLength + 1 : ℝ) ^ blockCount) /
        2 := by
  simpa [FormalProof4FHE.LeftoverHash.hashed, FormalProof4FHE.LeftoverHash.ideal,
    Fintype.card_fun, card_key, Nat.cast_pow] using
    (FormalProof4FHE.LeftoverHash.leftover_hash_lemma
      (extractorHash (R := R) (blockLength := blockLength)
        (blockCount := blockCount) (extractedDimension := extractedDimension))
      (extractorHash_isTwoUniversal (R := R)
        blockLength blockCount extractedDimension))

/-- Tight concrete leftover-hash bound for block-binary keys.

The numerator is one less than the extracted secret-space size, using the exact number of
off-diagonal key pairs. -/
theorem extractorHash_leftover_tight {R : Type}
    [Fintype R] [Nonempty R] [DecidableEq R] [SampleableType R] [AddCommGroup R]
    (blockLength blockCount extractedDimension : ℕ) :
    tvDist
        (do
          let matrix ← $ᵗ Matrix (Fin (blockCount * blockLength))
            (Fin extractedDimension) R
          let key ← $ᵗ (Key blockLength blockCount)
          return (matrix, extractorHash matrix key))
        ($ᵗ (Matrix (Fin (blockCount * blockLength)) (Fin extractedDimension) R ×
          (Fin extractedDimension → R))) ≤
      Real.sqrt
          (((Fintype.card R : ℝ) ^ extractedDimension - 1) /
            (blockLength + 1 : ℝ) ^ blockCount) /
        2 := by
  simpa [FormalProof4FHE.LeftoverHash.hashed, FormalProof4FHE.LeftoverHash.ideal,
    Fintype.card_fun, card_key, Nat.cast_pow] using
    (FormalProof4FHE.LeftoverHash.leftover_hash_lemma_tight
      (extractorHash (R := R) (blockLength := blockLength)
        (blockCount := blockCount) (extractedDimension := extractedDimension))
      (extractorHash_isTwoUniversal (R := R)
        blockLength blockCount extractedDimension))

/-- The decisional LWE problem whose secret is sampled uniformly from the compact block-key
space and expanded to a block-binary vector in the noiseless product. -/
def problem {R : Type} [Semiring R] [DecidableEq R] [SampleableType R]
    (blockLength blockCount sampleCount : ℕ) (errorSampler : ProbComp R) :
    LearningWithErrors.Problem
      (Matrix (Fin (blockCount * blockLength)) (Fin sampleCount) R)
      (Key blockLength blockCount) (Fin sampleCount → R) where
  sampleChallenge :=
    $ᵗ Matrix (Fin (blockCount * blockLength)) (Fin sampleCount) R
  sampleSecret := $ᵗ (Key blockLength blockCount)
  sampleError := ProbComp.sampleIID sampleCount errorSampler
  noiseless := fun key challenge ↦ vecMul (expand R key) challenge
  sampleUniform := $ᵗ (Fin sampleCount → R)

/-- Block-binary LWE over `ZMod q`. -/
def zmodProblem (blockLength blockCount sampleCount q : ℕ) [NeZero q]
    (errorSampler : ProbComp (ZMod q)) :
    LearningWithErrors.Problem
      (Matrix (Fin (blockCount * blockLength)) (Fin sampleCount) (ZMod q))
      (Key blockLength blockCount) (Fin sampleCount → ZMod q) :=
  problem blockLength blockCount sampleCount errorSampler

end FormalProof4FHE.BlockBinary
