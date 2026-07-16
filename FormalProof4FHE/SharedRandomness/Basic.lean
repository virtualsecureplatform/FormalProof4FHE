/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.LWE.Security
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# LWE with Shared-Randomness Secret Keys

This file formalizes Definition 10 of Bergerat--Chillotti--Ligier--Orfila--Roux-Langlois--Tap,
*New Secret Keys for Enhanced Performance in (T)FHE* (Theorem 6).

An instance contains two batches of `m` LWE samples.  The first batch uses a secret of length
`n`; the second uses the length-`n + k` secret obtained by appending `k` fresh coefficients to
the first secret.  The two matrices and the two error vectors are sampled independently.
-/

open Matrix OracleComp

namespace FormalProof4FHE.SharedRandomness

/-- Public matrices in a shared-randomness LWE transcript. -/
abbrev Challenge (R : Type) (n k m : ℕ) :=
  Matrix (Fin n) (Fin m) R × Matrix (Fin (n + k)) (Fin m) R

/-- The shared prefix and the fresh suffix of the nested secret. -/
abbrev Secret (R : Type) (n k : ℕ) := (Fin n → R) × (Fin k → R)

/-- Noisy right-hand sides in a shared-randomness LWE transcript. -/
abbrev Output (R : Type) (m : ℕ) := (Fin m → R) × (Fin m → R)

/-- A full public shared-randomness LWE transcript. -/
abbrev Transcript (R : Type) (n k m : ℕ) :=
  Challenge R n k m × Output R m

/-- Append the rows of two matrices whose column types agree. -/
def appendRows {R J : Type} {n k : ℕ}
    (top : Matrix (Fin n) J R) (bottom : Matrix (Fin k) J R) :
    Matrix (Fin (n + k)) J R := fun i j ↦
  Fin.append (fun row ↦ top row j) (fun row ↦ bottom row j) i

/-- Split a matrix after its first `n` rows. -/
def splitRows {R J : Type} {n k : ℕ}
    (matrix : Matrix (Fin (n + k)) J R) :
    Matrix (Fin n) J R × Matrix (Fin k) J R :=
  (fun i j ↦ matrix (Fin.castAdd k i) j,
    fun i j ↦ matrix (Fin.natAdd n i) j)

@[simp]
theorem appendRows_castAdd {R J : Type} {n k : ℕ}
    (top : Matrix (Fin n) J R) (bottom : Matrix (Fin k) J R)
    (i : Fin n) (j : J) : appendRows top bottom (Fin.castAdd k i) j = top i j := by
  simp [appendRows]

@[simp]
theorem appendRows_natAdd {R J : Type} {n k : ℕ}
    (top : Matrix (Fin n) J R) (bottom : Matrix (Fin k) J R)
    (i : Fin k) (j : J) : appendRows top bottom (Fin.natAdd n i) j = bottom i j := by
  simp [appendRows]

@[simp]
theorem splitRows_appendRows {R J : Type} {n k : ℕ}
    (top : Matrix (Fin n) J R) (bottom : Matrix (Fin k) J R) :
    splitRows (appendRows top bottom) = (top, bottom) := by
  ext <;> simp [splitRows]

@[simp]
theorem appendRows_splitRows {R J : Type} {n k : ℕ}
    (matrix : Matrix (Fin (n + k)) J R) :
    appendRows (splitRows matrix).1 (splitRows matrix).2 = matrix := by
  ext i j
  refine Fin.addCases ?_ ?_ i <;> intro row <;> simp [splitRows]

/-- Appending matrix rows is a bijection between a pair of blocks and the combined matrix. -/
theorem appendRows_bijective {R J : Type} {n k : ℕ} :
    Function.Bijective
      (fun blocks : Matrix (Fin n) J R × Matrix (Fin k) J R ↦
        appendRows blocks.1 blocks.2) := by
  refine Function.bijective_iff_has_inverse.mpr ⟨splitRows, ?_, ?_⟩
  · rintro ⟨top, bottom⟩
    exact splitRows_appendRows top bottom
  · exact fun matrix ↦ appendRows_splitRows matrix

/-- Multiplication by an appended secret splits into the contribution of its prefix and suffix. -/
theorem vecMul_appendRows {R J : Type} [NonUnitalNonAssocSemiring R]
    {n k : ℕ} (head : Fin n → R) (suffix : Fin k → R)
    (top : Matrix (Fin n) J R) (bottom : Matrix (Fin k) J R) :
    vecMul (Fin.append head suffix) (appendRows top bottom) =
      vecMul head top + vecMul suffix bottom := by
  funext j
  simp [Matrix.vecMul, dotProduct, appendRows, Fin.sum_univ_add]

/-- The generic shared-randomness LWE problem.

The secret samplers are explicit so that binary, ternary, Gaussian, or uniform secrets can be
instantiated without changing the game.  The second secret is `prefix || suffix` by construction. -/
def problem {R : Type} [Semiring R] [DecidableEq R] [SampleableType R]
    (n k m : ℕ)
    (prefixSampler : ProbComp (Fin n → R))
    (suffixSampler : ProbComp (Fin k → R))
    (smallErrorSampler largeErrorSampler : ProbComp R) :
    LearningWithErrors.Problem
      (Challenge R n k m) (Secret R n k) (Output R m) where
  sampleChallenge := $ᵗ (Challenge R n k m)
  sampleSecret := do
    let head ← prefixSampler
    let suffix ← suffixSampler
    return (head, suffix)
  sampleError := do
    let smallError ← ProbComp.sampleIID m smallErrorSampler
    let largeError ← ProbComp.sampleIID m largeErrorSampler
    return (smallError, largeError)
  noiseless := fun secret challenge ↦
    (vecMul secret.1 challenge.1,
      vecMul (Fin.append secret.1 secret.2) challenge.2)
  sampleUniform := $ᵗ (Output R m)

/-- Shared-randomness LWE over `ZMod q` with uniform nested secrets. -/
def zmodProblem (n k m q : ℕ) [NeZero q]
    (smallErrorSampler largeErrorSampler : ProbComp (ZMod q)) :
    LearningWithErrors.Problem
      (Challenge (ZMod q) n k m) (Secret (ZMod q) n k) (Output (ZMod q) m) :=
  problem n k m ($ᵗ (Fin n → ZMod q)) ($ᵗ (Fin k → ZMod q))
    smallErrorSampler largeErrorSampler

end FormalProof4FHE.SharedRandomness
