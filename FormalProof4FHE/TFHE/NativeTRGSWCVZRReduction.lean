/-
Copyright (c) 2026 Kotaro Matsuoka. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: Kotaro Matsuoka
-/

import FormalProof4FHE.TFHE.NativeTRGSWCompleteViewAuxiliarySource
import FormalProof4FHE.TFHE.RingSquareTopWeightSampleExtraction
import FormalProof4FHE.TFHE.DirectSubsetKeyBRK

/-!
# Known-suffix prefix-RLWE reduction for complete-view zero rows

This module formalizes the valid claims in `sketch/CVZR.md`.  There are three separate layers.

* A public translation turns a homogeneous row under a prefix ring secret into a homogeneous row
  under the sum of that prefix and a known suffix.  The same translation permutes the uniform
  row carrier.
* Selecting one coefficient of a prefix-RLWE sample gives an exact scalar-LWE row under the
  binary prefix.  The selected scalar mask is exactly uniform, and the complete extracted error
  vector is left explicit so that no marginal error-law claim is mistaken for a joint one.
* An exact or approximate pair of public complete-view constructors reduces CVZR to one ordinary
  source problem with the factor-two branch-selection loss.  The two-copy result is the same
  theorem instantiated with a two-copy view carrier.

The source assumption after this reduction is prefix-subspace RLWE when the prefix embedding is
proper.  This file does not claim that ordinary full-secret RLWE implies that assumption.  It
also does not manufacture arbitrary auxiliary state: exact simulation of the KSK/auxiliary
builder on the real source remains an explicit distributional premise.
-/

open Matrix OracleComp
open scoped BigOperators

namespace FormalProof4FHE.TFHE.NativeTRGSWCVZRReduction

noncomputable section

open Native.CoefficientStructuredLWE
open TGSW.RingSquare.TopWeightSampleExtraction

/-! ## Public known-suffix transport -/

/-- Add the contribution of a known suffix secret to one homogeneous ring row. -/
def addKnownSuffixRow {R : Type} [Semiring R]
    (suffix : R) (row : R × R) : R × R :=
  (row.1, row.2 + row.1 * suffix)

/-- Remove a previously added known-suffix contribution. -/
def removeKnownSuffixRow {R : Type} [Ring R]
    (suffix : R) (row : R × R) : R × R :=
  (row.1, row.2 - row.1 * suffix)

/-- A prefix-secret homogeneous row becomes a full-secret homogeneous row with exactly the same
error after the known suffix is added. -/
theorem addKnownSuffixRow_real {R : Type} [CommSemiring R]
    (prefixKey suffix mask error : R) :
    addKnownSuffixRow suffix (mask, mask * prefixKey + error) =
      (mask, mask * (prefixKey + suffix) + error) := by
  apply Prod.ext
  · rfl
  · simp only [addKnownSuffixRow]
    ring

@[simp]
theorem removeKnownSuffixRow_addKnownSuffixRow {R : Type} [Ring R]
    (suffix : R) (row : R × R) :
    removeKnownSuffixRow suffix (addKnownSuffixRow suffix row) = row := by
  rcases row with ⟨mask, body⟩
  simp [removeKnownSuffixRow, addKnownSuffixRow]

@[simp]
theorem addKnownSuffixRow_removeKnownSuffixRow {R : Type} [Ring R]
    (suffix : R) (row : R × R) :
    addKnownSuffixRow suffix (removeKnownSuffixRow suffix row) = row := by
  rcases row with ⟨mask, body⟩
  simp [removeKnownSuffixRow, addKnownSuffixRow]

/-- For every fixed suffix, public row transport is a permutation of the complete mask/body
carrier. -/
theorem addKnownSuffixRow_bijective {R : Type} [Ring R] (suffix : R) :
    Function.Bijective (addKnownSuffixRow suffix : R × R → R × R) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨removeKnownSuffixRow suffix,
      removeKnownSuffixRow_addKnownSuffixRow suffix,
      addKnownSuffixRow_removeKnownSuffixRow suffix⟩

/-- Conditional translation by the known suffix preserves an exactly uniform row pair. -/
theorem addKnownSuffixRow_uniform_evalDist {R : Type}
    [Ring R] [Fintype R] [SampleableType R] (suffix : R) :
    evalDist (addKnownSuffixRow suffix <$> ($ᵗ (R × R))) =
      evalDist ($ᵗ (R × R)) :=
  evalDist_map_bijective_uniform_cross
    (α := R × R) (β := R × R)
    (addKnownSuffixRow suffix) (addKnownSuffixRow_bijective suffix)

/-- A complete block of homogeneous rank-one ring rows, represented by its mask and body
functions. -/
abbrev HomogeneousRowBlock (R : Type) (rowCount : ℕ) :=
  (Fin rowCount → R) × (Fin rowCount → R)

/-- Apply the same known ring suffix to every row of a complete block. -/
def addKnownSuffixBlock {R : Type} [Semiring R] {rowCount : ℕ}
    (suffix : R) (block : HomogeneousRowBlock R rowCount) :
    HomogeneousRowBlock R rowCount :=
  addKnownSuffixRow (fun _row : Fin rowCount ↦ suffix) block

/-- The whole real block is transported in one deterministic step, with no coordinate hybrid. -/
theorem addKnownSuffixBlock_real {R : Type} [CommSemiring R] {rowCount : ℕ}
    (prefixKey suffix : R) (mask error : Fin rowCount → R) :
    addKnownSuffixBlock suffix
        (mask, fun row ↦ mask row * prefixKey + error row) =
      (mask, fun row ↦ mask row * (prefixKey + suffix) + error row) := by
  rw [show (fun row ↦ mask row * prefixKey + error row) =
      mask * (fun _row : Fin rowCount ↦ prefixKey) + error by rfl]
  rw [show (fun row ↦ mask row * (prefixKey + suffix) + error row) =
      mask * ((fun _row : Fin rowCount ↦ prefixKey) +
        (fun _row : Fin rowCount ↦ suffix)) + error by rfl]
  exact addKnownSuffixRow_real
    (prefixKey := fun _row : Fin rowCount ↦ prefixKey)
    (suffix := fun _row : Fin rowCount ↦ suffix)
    (mask := mask) (error := error)

/-- Whole-block known-suffix transport is a permutation. -/
theorem addKnownSuffixBlock_bijective {R : Type} [Ring R] {rowCount : ℕ}
    (suffix : R) :
    Function.Bijective
      (addKnownSuffixBlock suffix :
        HomogeneousRowBlock R rowCount → HomogeneousRowBlock R rowCount) :=
  addKnownSuffixRow_bijective (fun _row : Fin rowCount ↦ suffix)

/-- A complete uniform BRK row block remains exactly uniform after known-suffix transport.  This
is one permutation argument for the complete batch, so its security reduction has no row-count
multiplier. -/
theorem addKnownSuffixBlock_uniform_evalDist {R : Type}
    [Ring R] [Fintype R] [SampleableType R] (rowCount : ℕ) (suffix : R) :
    evalDist (addKnownSuffixBlock suffix <$>
        ($ᵗ (HomogeneousRowBlock R rowCount))) =
      evalDist ($ᵗ (HomogeneousRowBlock R rowCount)) :=
  evalDist_map_bijective_uniform_cross
    (α := HomogeneousRowBlock R rowCount)
    (β := HomogeneousRowBlock R rowCount)
    (addKnownSuffixBlock suffix) (addKnownSuffixBlock_bijective suffix)

/-! ## Prefix coefficient embedding and extraction -/

/-- The ambient rank-one ring has a binary prefix followed by a nonempty suffix block.  The
`suffixDegree + 1` presentation lets us reuse the checked nonempty negacyclic extraction map. -/
abbrev AmbientCoefficients (q prefixDimension suffixDegree : ℕ) :=
  Coefficients q (prefixDimension + (suffixDegree + 1))

/-- Embed a binary prefix in the first coefficient block and fill the suffix block with zero. -/
def prefixCoefficients (q prefixDimension suffixDegree : ℕ)
    (prefixKey : BinarySecret prefixDimension) :
    AmbientCoefficients q prefixDimension suffixDegree :=
  Fin.append (m := prefixDimension) (n := suffixDegree + 1)
    (embedBinarySecret prefixKey)
    (0 : Fin (suffixDegree + 1) → ZMod q)

/-- Embed an arbitrary known suffix coefficient vector after a zero prefix block. -/
def suffixCoefficients (q prefixDimension suffixDegree : ℕ)
    (suffix : Fin (suffixDegree + 1) → ZMod q) :
    AmbientCoefficients q prefixDimension suffixDegree :=
  Fin.append (m := prefixDimension) (n := suffixDegree + 1)
    (0 : Fin prefixDimension → ZMod q) suffix

/-- Coefficient vector of the complete split secret. -/
def splitSecretCoefficients (q prefixDimension suffixDegree : ℕ)
    (prefixKey : BinarySecret prefixDimension)
    (suffix : Fin (suffixDegree + 1) → ZMod q) :
    AmbientCoefficients q prefixDimension suffixDegree :=
  Fin.append (m := prefixDimension) (n := suffixDegree + 1)
    (embedBinarySecret prefixKey) suffix

/-- Prefix and suffix embeddings sum to the coefficient vector of the complete secret. -/
theorem prefixCoefficients_add_suffixCoefficients
    (q prefixDimension suffixDegree : ℕ)
    (prefixKey : BinarySecret prefixDimension)
    (suffix : Fin (suffixDegree + 1) → ZMod q) :
    prefixCoefficients q prefixDimension suffixDegree prefixKey +
        suffixCoefficients q prefixDimension suffixDegree suffix =
      splitSecretCoefficients q prefixDimension suffixDegree prefixKey suffix := by
  funext coordinate
  refine Fin.addCases ?_ ?_ coordinate
  · intro prefixCoordinate
    simp [prefixCoefficients, suffixCoefficients, splitSecretCoefficients]
  · intro suffixCoordinate
    simp [prefixCoefficients, suffixCoefficients, splitSecretCoefficients]

/-- Negacyclic multiplication is additive in its secret input.  This reuses the checked direct
coefficient-convolution proof rather than assuming an informal ring identity. -/
theorem negacyclicProduct_add_left
    {q degree : ℕ} (left right challenge : Coefficients q degree) :
    negacyclicProduct (left + right) challenge =
      negacyclicProduct left challenge + negacyclicProduct right challenge :=
  Native.CoefficientAffineCircularRLWE.negacyclicProduct_add_left
    left right challenge

/-- Public known-suffix transport directly on one coefficient-form prefix-RLWE row. -/
def addKnownSuffixCoefficientRow
    {q prefixDimension suffixDegree : ℕ}
    (suffix : Fin (suffixDegree + 1) → ZMod q)
    (row : AmbientCoefficients q prefixDimension suffixDegree ×
      AmbientCoefficients q prefixDimension suffixDegree) :
    AmbientCoefficients q prefixDimension suffixDegree ×
      AmbientCoefficients q prefixDimension suffixDegree :=
  (row.1, row.2 +
    negacyclicProduct
      (suffixCoefficients q prefixDimension suffixDegree suffix) row.1)

/-- The coefficient-form translation changes the prefix-supported secret to the complete split
secret while retaining the source error exactly. -/
theorem addKnownSuffixCoefficientRow_real
    {q prefixDimension suffixDegree : ℕ}
    (prefixKey : BinarySecret prefixDimension)
    (suffix : Fin (suffixDegree + 1) → ZMod q)
    (challenge error : AmbientCoefficients q prefixDimension suffixDegree) :
    addKnownSuffixCoefficientRow suffix
        (challenge,
          negacyclicProduct
            (prefixCoefficients q prefixDimension suffixDegree prefixKey) challenge + error) =
      (challenge,
        negacyclicProduct
          (splitSecretCoefficients q prefixDimension suffixDegree prefixKey suffix) challenge +
            error) := by
  apply Prod.ext
  · rfl
  · simp only [addKnownSuffixCoefficientRow]
    rw [← prefixCoefficients_add_suffixCoefficients,
      negacyclicProduct_add_left]
    abel

/-- Remove the known-suffix contribution from one coefficient-form row. -/
def removeKnownSuffixCoefficientRow
    {q prefixDimension suffixDegree : ℕ}
    (suffix : Fin (suffixDegree + 1) → ZMod q)
    (row : AmbientCoefficients q prefixDimension suffixDegree ×
      AmbientCoefficients q prefixDimension suffixDegree) :
    AmbientCoefficients q prefixDimension suffixDegree ×
      AmbientCoefficients q prefixDimension suffixDegree :=
  (row.1, row.2 -
    negacyclicProduct
      (suffixCoefficients q prefixDimension suffixDegree suffix) row.1)

@[simp]
theorem removeKnownSuffixCoefficientRow_add
    {q prefixDimension suffixDegree : ℕ}
    (suffix : Fin (suffixDegree + 1) → ZMod q)
    (row : AmbientCoefficients q prefixDimension suffixDegree ×
      AmbientCoefficients q prefixDimension suffixDegree) :
    removeKnownSuffixCoefficientRow suffix (addKnownSuffixCoefficientRow suffix row) = row := by
  rcases row with ⟨challenge, body⟩
  simp [removeKnownSuffixCoefficientRow, addKnownSuffixCoefficientRow]

@[simp]
theorem addKnownSuffixCoefficientRow_remove
    {q prefixDimension suffixDegree : ℕ}
    (suffix : Fin (suffixDegree + 1) → ZMod q)
    (row : AmbientCoefficients q prefixDimension suffixDegree ×
      AmbientCoefficients q prefixDimension suffixDegree) :
    addKnownSuffixCoefficientRow suffix (removeKnownSuffixCoefficientRow suffix row) = row := by
  rcases row with ⟨challenge, body⟩
  simp [removeKnownSuffixCoefficientRow, addKnownSuffixCoefficientRow]

theorem addKnownSuffixCoefficientRow_bijective
    {q prefixDimension suffixDegree : ℕ}
    (suffix : Fin (suffixDegree + 1) → ZMod q) :
    Function.Bijective
      (addKnownSuffixCoefficientRow suffix :
        (AmbientCoefficients q prefixDimension suffixDegree ×
          AmbientCoefficients q prefixDimension suffixDegree) → _) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨removeKnownSuffixCoefficientRow suffix,
      removeKnownSuffixCoefficientRow_add suffix,
      addKnownSuffixCoefficientRow_remove suffix⟩

/-- Coefficient-form known-suffix transport preserves the uniform row law. -/
theorem addKnownSuffixCoefficientRow_uniform_evalDist
    (q prefixDimension suffixDegree : ℕ) [NeZero q]
    (suffix : Fin (suffixDegree + 1) → ZMod q) :
    evalDist (addKnownSuffixCoefficientRow suffix <$>
        ($ᵗ (AmbientCoefficients q prefixDimension suffixDegree ×
          AmbientCoefficients q prefixDimension suffixDegree))) =
      evalDist ($ᵗ (AmbientCoefficients q prefixDimension suffixDegree ×
        AmbientCoefficients q prefixDimension suffixDegree)) :=
  evalDist_map_bijective_uniform_cross
    (α := AmbientCoefficients q prefixDimension suffixDegree ×
      AmbientCoefficients q prefixDimension suffixDegree)
    (β := AmbientCoefficients q prefixDimension suffixDegree ×
      AmbientCoefficients q prefixDimension suffixDegree)
    (addKnownSuffixCoefficientRow suffix)
    (addKnownSuffixCoefficientRow_bijective suffix)

/-- Apply coefficient-form transport to the complete BRK block. -/
def addKnownSuffixCoefficientBlock
    {q prefixDimension suffixDegree rowCount : ℕ}
    (suffix : Fin (suffixDegree + 1) → ZMod q)
    (block : HomogeneousRowBlock
      (AmbientCoefficients q prefixDimension suffixDegree) rowCount) :
    HomogeneousRowBlock
      (AmbientCoefficients q prefixDimension suffixDegree) rowCount :=
  (block.1, fun row ↦ block.2 row +
    negacyclicProduct
      (suffixCoefficients q prefixDimension suffixDegree suffix) (block.1 row))

/-- Exact complete-block coefficient transport in the real source. -/
theorem addKnownSuffixCoefficientBlock_real
    {q prefixDimension suffixDegree rowCount : ℕ}
    (prefixKey : BinarySecret prefixDimension)
    (suffix : Fin (suffixDegree + 1) → ZMod q)
    (challenge error : Fin rowCount →
      AmbientCoefficients q prefixDimension suffixDegree) :
    addKnownSuffixCoefficientBlock suffix
        (challenge, fun row ↦
          negacyclicProduct
            (prefixCoefficients q prefixDimension suffixDegree prefixKey) (challenge row) +
              error row) =
      (challenge, fun row ↦
        negacyclicProduct
          (splitSecretCoefficients q prefixDimension suffixDegree prefixKey suffix)
          (challenge row) + error row) := by
  apply Prod.ext
  · rfl
  · funext row
    change
      (negacyclicProduct
          (prefixCoefficients q prefixDimension suffixDegree prefixKey) (challenge row) +
            error row) +
          negacyclicProduct
            (suffixCoefficients q prefixDimension suffixDegree suffix) (challenge row) =
        negacyclicProduct
          (splitSecretCoefficients q prefixDimension suffixDegree prefixKey suffix)
          (challenge row) + error row
    rw [← prefixCoefficients_add_suffixCoefficients,
      negacyclicProduct_add_left]
    abel

/-- Remove coefficient-form known-suffix transport from a complete block. -/
def removeKnownSuffixCoefficientBlock
    {q prefixDimension suffixDegree rowCount : ℕ}
    (suffix : Fin (suffixDegree + 1) → ZMod q)
    (block : HomogeneousRowBlock
      (AmbientCoefficients q prefixDimension suffixDegree) rowCount) :
    HomogeneousRowBlock
      (AmbientCoefficients q prefixDimension suffixDegree) rowCount :=
  (block.1, fun row ↦ block.2 row -
    negacyclicProduct
      (suffixCoefficients q prefixDimension suffixDegree suffix) (block.1 row))

@[simp]
theorem removeKnownSuffixCoefficientBlock_add
    {q prefixDimension suffixDegree rowCount : ℕ}
    (suffix : Fin (suffixDegree + 1) → ZMod q)
    (block : HomogeneousRowBlock
      (AmbientCoefficients q prefixDimension suffixDegree) rowCount) :
    removeKnownSuffixCoefficientBlock suffix
        (addKnownSuffixCoefficientBlock suffix block) = block := by
  rcases block with ⟨challenge, body⟩
  apply Prod.ext
  · rfl
  · funext row
    simp [removeKnownSuffixCoefficientBlock, addKnownSuffixCoefficientBlock]

@[simp]
theorem addKnownSuffixCoefficientBlock_remove
    {q prefixDimension suffixDegree rowCount : ℕ}
    (suffix : Fin (suffixDegree + 1) → ZMod q)
    (block : HomogeneousRowBlock
      (AmbientCoefficients q prefixDimension suffixDegree) rowCount) :
    addKnownSuffixCoefficientBlock suffix
        (removeKnownSuffixCoefficientBlock suffix block) = block := by
  rcases block with ⟨challenge, body⟩
  apply Prod.ext
  · rfl
  · funext row
    simp [removeKnownSuffixCoefficientBlock, addKnownSuffixCoefficientBlock]

theorem addKnownSuffixCoefficientBlock_bijective
    {q prefixDimension suffixDegree rowCount : ℕ}
    (suffix : Fin (suffixDegree + 1) → ZMod q) :
    Function.Bijective
      (addKnownSuffixCoefficientBlock suffix :
        HomogeneousRowBlock
          (AmbientCoefficients q prefixDimension suffixDegree) rowCount → _) :=
  Function.bijective_iff_has_inverse.mpr
    ⟨removeKnownSuffixCoefficientBlock suffix,
      removeKnownSuffixCoefficientBlock_add suffix,
      addKnownSuffixCoefficientBlock_remove suffix⟩

/-- The complete coefficient-form uniform BRK block remains uniform after translation. -/
theorem addKnownSuffixCoefficientBlock_uniform_evalDist
    (q prefixDimension suffixDegree rowCount : ℕ) [NeZero q]
    (suffix : Fin (suffixDegree + 1) → ZMod q) :
    evalDist (addKnownSuffixCoefficientBlock suffix <$>
        ($ᵗ (HomogeneousRowBlock
          (AmbientCoefficients q prefixDimension suffixDegree) rowCount))) =
      evalDist ($ᵗ (HomogeneousRowBlock
        (AmbientCoefficients q prefixDimension suffixDegree) rowCount)) :=
  evalDist_map_bijective_uniform_cross
    (α := HomogeneousRowBlock
      (AmbientCoefficients q prefixDimension suffixDegree) rowCount)
    (β := HomogeneousRowBlock
      (AmbientCoefficients q prefixDimension suffixDegree) rowCount)
    (addKnownSuffixCoefficientBlock suffix)
    (addKnownSuffixCoefficientBlock_bijective suffix)

/-- The scalar mask obtained by selecting one output coefficient and retaining only the prefix
secret coordinates. -/
def prefixExtractedMask
    {q prefixDimension suffixDegree : ℕ}
    (output : Fin (prefixDimension + (suffixDegree + 1)))
    (challenge : AmbientCoefficients q prefixDimension suffixDegree) :
    Fin prefixDimension → ZMod q :=
  fun coordinate ↦
    extractedMask output challenge (Fin.castAdd (suffixDegree + 1) coordinate)

/-- Extract the complete signed mask and then split it into prefix and suffix blocks. -/
def splitExtractedMaskEquiv
    (q prefixDimension suffixDegree : ℕ)
    (output : Fin (prefixDimension + (suffixDegree + 1))) :
    AmbientCoefficients q prefixDimension suffixDegree ≃
      (Fin prefixDimension → ZMod q) ×
        (Fin (suffixDegree + 1) → ZMod q) :=
  (extractedMaskEquiv output).trans
    (Fin.appendEquiv prefixDimension (suffixDegree + 1)).symm

@[simp]
theorem splitExtractedMaskEquiv_fst
    {q prefixDimension suffixDegree : ℕ}
    (output : Fin (prefixDimension + (suffixDegree + 1)))
    (challenge : AmbientCoefficients q prefixDimension suffixDegree) :
    (splitExtractedMaskEquiv q prefixDimension suffixDegree output challenge).1 =
      prefixExtractedMask output challenge := by
  funext coordinate
  rfl

/-- The selected coefficient of multiplication by a prefix-supported binary secret is exactly a
scalar dot product under the prefix key. -/
theorem negacyclicProduct_prefix_apply_eq_dotProduct
    {q prefixDimension suffixDegree : ℕ}
    (prefixKey : BinarySecret prefixDimension)
    (challenge : AmbientCoefficients q prefixDimension suffixDegree)
    (output : Fin (prefixDimension + (suffixDegree + 1))) :
    negacyclicProduct
        (prefixCoefficients q prefixDimension suffixDegree prefixKey) challenge output =
      dotProduct (embedBinarySecret prefixKey) (prefixExtractedMask output challenge) := by
  rw [negacyclicProduct_apply_eq_dotProduct]
  unfold dotProduct prefixCoefficients prefixExtractedMask
  calc
    (∑ coordinate : Fin (prefixDimension + (suffixDegree + 1)),
        Fin.append (embedBinarySecret prefixKey)
            (0 : Fin (suffixDegree + 1) → ZMod q) coordinate *
          extractedMask output challenge coordinate) =
      (∑ coordinate : Fin prefixDimension,
          Fin.append (embedBinarySecret prefixKey)
              (0 : Fin (suffixDegree + 1) → ZMod q)
              (Fin.castAdd (suffixDegree + 1) coordinate) *
            extractedMask output challenge
              (Fin.castAdd (suffixDegree + 1) coordinate)) +
        ∑ coordinate : Fin (suffixDegree + 1),
          Fin.append (embedBinarySecret prefixKey)
              (0 : Fin (suffixDegree + 1) → ZMod q)
              (Fin.natAdd prefixDimension coordinate) *
            extractedMask output challenge
              (Fin.natAdd prefixDimension coordinate) :=
      Fin.sum_univ_add _
    _ = ∑ coordinate : Fin prefixDimension,
        embedBinarySecret prefixKey coordinate *
          extractedMask output challenge
            (Fin.castAdd (suffixDegree + 1) coordinate) := by simp

/-- Lemma 1 of the note: for one fixed output coefficient, the prefix-extracted mask of a
uniform ring mask is exactly uniform on all prefix vectors. -/
theorem prefixExtractedMask_uniform_evalDist
    (q prefixDimension suffixDegree : ℕ) [NeZero q]
    (output : Fin (prefixDimension + (suffixDegree + 1))) :
    evalDist (prefixExtractedMask output <$>
        ($ᵗ (AmbientCoefficients q prefixDimension suffixDegree))) =
      evalDist ($ᵗ (Fin prefixDimension → ZMod q)) := by
  let split := splitExtractedMaskEquiv q prefixDimension suffixDegree output
  have hsplit :
      evalDist (split <$>
          ($ᵗ (AmbientCoefficients q prefixDimension suffixDegree))) =
        evalDist ($ᵗ ((Fin prefixDimension → ZMod q) ×
          (Fin (suffixDegree + 1) → ZMod q))) :=
    evalDist_map_bijective_uniform_cross
      (α := AmbientCoefficients q prefixDimension suffixDegree)
      (β := (Fin prefixDimension → ZMod q) ×
        (Fin (suffixDegree + 1) → ZMod q))
      split split.bijective
  calc
    evalDist (prefixExtractedMask output <$>
        ($ᵗ (AmbientCoefficients q prefixDimension suffixDegree))) =
      evalDist (Prod.fst <$> (split <$>
        ($ᵗ (AmbientCoefficients q prefixDimension suffixDegree)))) := by
          congr 1
          rw [Functor.map_map]
          apply congrArg (fun transform ↦ transform <$>
            ($ᵗ (AmbientCoefficients q prefixDimension suffixDegree)))
          funext challenge
          exact (splitExtractedMaskEquiv_fst output challenge).symm
    _ = evalDist (Prod.fst <$> ($ᵗ ((Fin prefixDimension → ZMod q) ×
          (Fin (suffixDegree + 1) → ZMod q)))) :=
      evalDist_map_eq_of_evalDist_eq hsplit Prod.fst
    _ = _ := evalDist_map_fst_uniformSample_prod

/-- Selecting one coefficient of a uniform ring body and adding a fixed public message leaves an
exactly uniform scalar body. -/
theorem selectedCoefficient_add_uniform_evalDist
    (q prefixDimension suffixDegree : ℕ) [NeZero q]
    (output : Fin (prefixDimension + (suffixDegree + 1)))
    (message : ZMod q) :
    evalDist ((fun body : AmbientCoefficients q prefixDimension suffixDegree ↦
        body output + message) <$>
      ($ᵗ (AmbientCoefficients q prefixDimension suffixDegree))) =
      evalDist ($ᵗ (ZMod q)) := by
  let translate : ZMod q ≃ ZMod q := Equiv.addRight message
  have hcoefficient :
      evalDist ((fun body : AmbientCoefficients q prefixDimension suffixDegree ↦
          body output) <$>
        ($ᵗ (AmbientCoefficients q prefixDimension suffixDegree))) =
        evalDist ($ᵗ (ZMod q)) :=
    FormalProof4FHE.FiniteProduct.evalDist_map_apply_uniformSample_fun output
  calc
    evalDist ((fun body : AmbientCoefficients q prefixDimension suffixDegree ↦
        body output + message) <$>
      ($ᵗ (AmbientCoefficients q prefixDimension suffixDegree))) =
      evalDist (translate <$> ((fun body :
          AmbientCoefficients q prefixDimension suffixDegree ↦ body output) <$>
        ($ᵗ (AmbientCoefficients q prefixDimension suffixDegree)))) := by
          simp [translate, Functor.map_map]
    _ = evalDist (translate <$> ($ᵗ (ZMod q))) :=
      evalDist_map_eq_of_evalDist_eq hcoefficient translate
    _ = _ := evalDist_map_bijective_uniform_cross
      (α := ZMod q) (β := ZMod q) translate translate.bijective

/-! ## Exact native KSK rows from disjoint prefix-RLWE samples -/

/-- Publicly extract one scalar KSK row from one ring sample and add its known suffix message. -/
def extractKSKRow
    {q prefixDimension suffixDegree : ℕ}
    (output : Fin (prefixDimension + (suffixDegree + 1)))
    (message : ZMod q)
    (sample : AmbientCoefficients q prefixDimension suffixDegree ×
      AmbientCoefficients q prefixDimension suffixDegree) :
    TLWE.Ciphertext (ZMod q) prefixDimension :=
  ⟨prefixExtractedMask output sample.1, sample.2 output + message⟩

/-- Public extraction applied to an independent uniform ring mask/body pair. -/
def extractedUniformKSKRow
    (q prefixDimension suffixDegree : ℕ) [NeZero q]
    (output : Fin (prefixDimension + (suffixDegree + 1)))
    (message : ZMod q) : ProbComp (TLWE.Ciphertext (ZMod q) prefixDimension) := do
  let challenge ← $ᵗ (AmbientCoefficients q prefixDimension suffixDegree)
  let body ← $ᵗ (AmbientCoefficients q prefixDimension suffixDegree)
  return extractKSKRow output message (challenge, body)

/-- Canonical independent uniform scalar mask/body row sampler. -/
def uniformKSKRow (q prefixDimension : ℕ) [NeZero q] :
    ProbComp (TLWE.Ciphertext (ZMod q) prefixDimension) := do
  let mask ← $ᵗ (Fin prefixDimension → ZMod q)
  let body ← $ᵗ (ZMod q)
  return ⟨mask, body⟩

/-- In the uniform prefix-RLWE branch, an extracted KSK row has exactly the canonical uniform
scalar mask/body law, independently of the fixed suffix message. -/
theorem extractedUniformKSKRow_evalDist
    (q prefixDimension suffixDegree : ℕ) [NeZero q]
    (output : Fin (prefixDimension + (suffixDegree + 1)))
    (message : ZMod q) :
    evalDist (extractedUniformKSKRow q prefixDimension suffixDegree output message) =
      evalDist (uniformKSKRow q prefixDimension) := by
  let maskSampler : ProbComp (Fin prefixDimension → ZMod q) :=
    prefixExtractedMask output <$>
      ($ᵗ (AmbientCoefficients q prefixDimension suffixDegree))
  let bodySampler : ProbComp (ZMod q) :=
    (fun body : AmbientCoefficients q prefixDimension suffixDegree ↦ body output + message) <$>
      ($ᵗ (AmbientCoefficients q prefixDimension suffixDegree))
  have hmask : evalDist maskSampler =
      evalDist ($ᵗ (Fin prefixDimension → ZMod q)) :=
    prefixExtractedMask_uniform_evalDist q prefixDimension suffixDegree output
  have hbody : evalDist bodySampler = evalDist ($ᵗ (ZMod q)) :=
    selectedCoefficient_add_uniform_evalDist
      q prefixDimension suffixDegree output message
  have hnormalize :
      evalDist (extractedUniformKSKRow q prefixDimension suffixDegree output message) =
        evalDist (maskSampler >>= fun mask ↦
          bodySampler >>= fun body ↦ pure ⟨mask, body⟩) := by
    simp [extractedUniformKSKRow, extractKSKRow, maskSampler, bodySampler,
      map_eq_bind_pure_comp, bind_assoc]
  rw [hnormalize, evalDist_bind, hmask, ← evalDist_bind]
  refine evalDist_bind_congr' ($ᵗ (Fin prefixDimension → ZMod q)) fun mask ↦ ?_
  rw [evalDist_bind, hbody, ← evalDist_bind]

/-- On a real prefix-RLWE sample, coefficient extraction is exactly a native affine KSK row.
The row error is the selected source-error coefficient and is neither widened nor replaced. -/
theorem extractKSKRow_real
    {q prefixDimension suffixDegree : ℕ}
    (prefixKey : BinarySecret prefixDimension)
    (challenge error : AmbientCoefficients q prefixDimension suffixDegree)
    (output : Fin (prefixDimension + (suffixDegree + 1)))
    (message : ZMod q) :
    extractKSKRow output message
        (challenge,
          negacyclicProduct
            (prefixCoefficients q prefixDimension suffixDegree prefixKey) challenge + error) =
      TLWE.assemble (embedBinarySecret prefixKey)
        (prefixExtractedMask output challenge) message (error output) := by
  rw [TLWE.Ciphertext.mk.injEq]
  constructor
  · rfl
  · simp only [extractKSKRow, TLWE.assemble, Pi.add_apply]
    rw [negacyclicProduct_prefix_apply_eq_dotProduct]
    ring

/-- Extract every KSK row at once.  Each row may use a different public output coefficient and
known suffix message. -/
def extractKSKBatch
    {q prefixDimension suffixDegree rowCount : ℕ}
    (output : Fin rowCount → Fin (prefixDimension + (suffixDegree + 1)))
    (message : Fin rowCount → ZMod q)
    (samples : Fin rowCount →
      AmbientCoefficients q prefixDimension suffixDegree ×
        AmbientCoefficients q prefixDimension suffixDegree) :
    TLWE.BatchCiphertext (ZMod q) prefixDimension rowCount :=
  (fun coordinate row ↦ prefixExtractedMask (output row) (samples row).1 coordinate,
    fun row ↦ (samples row).2 (output row) + message row)

/-- The batched extraction identity retains the complete joint extracted-error vector.  Thus an
exact native KSK law follows precisely when this vector has the prescribed joint KSK error law. -/
theorem extractKSKBatch_real
    {q prefixDimension suffixDegree rowCount : ℕ}
    (prefixKey : BinarySecret prefixDimension)
    (challenge error : Fin rowCount →
      AmbientCoefficients q prefixDimension suffixDegree)
    (output : Fin rowCount → Fin (prefixDimension + (suffixDegree + 1)))
    (message : Fin rowCount → ZMod q) :
    extractKSKBatch output message
        (fun row ↦
          (challenge row,
            negacyclicProduct
              (prefixCoefficients q prefixDimension suffixDegree prefixKey) (challenge row) +
                error row)) =
      TLWE.batchAssemble (embedBinarySecret prefixKey)
        (fun coordinate row ↦ prefixExtractedMask (output row) (challenge row) coordinate)
        message (fun row ↦ error row (output row)) := by
  apply Prod.ext
  · rfl
  · funext row
    simp only [extractKSKBatch, TLWE.batchAssemble, Pi.add_apply, Matrix.vecMul]
    rw [negacyclicProduct_prefix_apply_eq_dotProduct]
    ring

/-! ## The plain prefix-subspace RLWE source -/

/-- One public rank-one ring mask for each source row. -/
abbrev PrefixRLWEChallenge
    (q prefixDimension suffixDegree sampleCount : ℕ) :=
  Fin sampleCount → AmbientCoefficients q prefixDimension suffixDegree

/-- One ring body for each source row. -/
abbrev PrefixRLWEOutput
    (q prefixDimension suffixDegree sampleCount : ℕ) :=
  Fin sampleCount → AmbientCoefficients q prefixDimension suffixDegree

/-- The source in equations (3) and (4): a uniformly sampled binary key occupies only the first
coefficient block.  The error sampler is a sampler for the complete row vector, so it can encode
the exact joint BRK/KSK/auxiliary error law without asserting independence that is not present. -/
def prefixRLWEProblem
    (q prefixDimension suffixDegree sampleCount : ℕ) [NeZero q]
    (jointErrorSampler : ProbComp
      (PrefixRLWEOutput q prefixDimension suffixDegree sampleCount)) :
    LearningWithErrors.Problem
      (PrefixRLWEChallenge q prefixDimension suffixDegree sampleCount)
      (BinarySecret prefixDimension)
      (PrefixRLWEOutput q prefixDimension suffixDegree sampleCount) where
  sampleChallenge :=
    $ᵗ (PrefixRLWEChallenge q prefixDimension suffixDegree sampleCount)
  sampleSecret := $ᵗ (BinarySecret prefixDimension)
  sampleError := jointErrorSampler
  noiseless := fun prefixKey challenge row ↦
    negacyclicProduct
      (prefixCoefficients q prefixDimension suffixDegree prefixKey) (challenge row)
  sampleUniform :=
    $ᵗ (PrefixRLWEOutput q prefixDimension suffixDegree sampleCount)

@[simp]
theorem prefixRLWEProblem_noiseless_apply
    (q prefixDimension suffixDegree sampleCount : ℕ) [NeZero q]
    (jointErrorSampler : ProbComp
      (PrefixRLWEOutput q prefixDimension suffixDegree sampleCount))
    (prefixKey : BinarySecret prefixDimension)
    (challenge : PrefixRLWEChallenge q prefixDimension suffixDegree sampleCount)
    (row : Fin sampleCount) :
    (prefixRLWEProblem q prefixDimension suffixDegree sampleCount
        jointErrorSampler).noiseless prefixKey challenge row =
      negacyclicProduct
        (prefixCoefficients q prefixDimension suffixDegree prefixKey) (challenge row) := by
  rfl

/-- The ideal endpoint is an independent uniform mask/body batch.  In particular, it contains no
KSK or auxiliary input; those objects are outputs of the public compiler. -/
theorem prefixRLWEProblem_uniformDistr_eq
    (q prefixDimension suffixDegree sampleCount : ℕ) [NeZero q]
    (jointErrorSampler : ProbComp
      (PrefixRLWEOutput q prefixDimension suffixDegree sampleCount)) :
    LearningWithErrors.uniformDistr
        (prefixRLWEProblem q prefixDimension suffixDegree sampleCount jointErrorSampler) = do
      let challenge ←
        $ᵗ (PrefixRLWEChallenge q prefixDimension suffixDegree sampleCount)
      let body ← $ᵗ (PrefixRLWEOutput q prefixDimension suffixDegree sampleCount)
      return (challenge, body) := by
  rfl

/-! ## Why disjoint uniform source blocks erase the constructor branch -/

/-- Build a complete view from independent row and side-input source blocks.  The KSK and
auxiliary output may be arbitrarily correlated with each other through `sideBuild`. -/
def disjointCompleteView
    {Known SourceRows SideInput Rows KeySwitchKey Auxiliary : Type}
    (knownSampler : ProbComp Known)
    (rowSource : ProbComp SourceRows) (sideSource : ProbComp SideInput)
    (rowBuild : Known → SourceRows → ProbComp Rows)
    (sideBuild : Known → SideInput → ProbComp (KeySwitchKey × Auxiliary)) :
    ProbComp (NativeTRGSWCompleteViewAuxiliarySource.CompleteView
      Rows KeySwitchKey Auxiliary) := do
  let known ← knownSampler
  let rows ← rowSource >>= rowBuild known
  let sideInput ← sideSource
  let side ← sideBuild known sideInput
  return ⟨rows, side.1, side.2⟩

/-- If the two row constructors have the same integrated law on the independent row block, then
the complete views coincide even though the side builder itself can be arbitrary.  This is the
formal role of the disjoint source partition in equation (21). -/
theorem disjointCompleteView_branch_erasure
    {Known SourceRows SideInput Rows KeySwitchKey Auxiliary : Type}
    (knownSampler : ProbComp Known)
    (rowSource : ProbComp SourceRows) (sideSource : ProbComp SideInput)
    (rowOne rowZero : Known → SourceRows → ProbComp Rows)
    (sideBuild : Known → SideInput → ProbComp (KeySwitchKey × Auxiliary))
    (hrows : ∀ known,
      evalDist (rowSource >>= rowOne known) =
        evalDist (rowSource >>= rowZero known)) :
    evalDist (disjointCompleteView knownSampler rowSource sideSource rowOne sideBuild) =
      evalDist (disjointCompleteView knownSampler rowSource sideSource rowZero sideBuild) := by
  unfold disjointCompleteView
  refine evalDist_bind_congr' knownSampler fun known ↦ ?_
  rw [evalDist_bind, hrows known, ← evalDist_bind]

/-- Real-row branch on one uniform source row: apply the known-suffix translation. -/
def translatedUniformRowBuild {R : Type} [Ring R]
    (suffix : R) (row : R × R) : ProbComp (R × R) :=
  pure (addKnownSuffixRow suffix row)

/-- Uniform-row branch: ignore the source row and sample a fresh uniform row carrier. -/
def freshUniformRowBuild {R : Type} [Fintype R] [SampleableType R]
    (_suffix : R) (_row : R × R) : ProbComp (R × R) :=
  $ᵗ (R × R)

/-- On an independent uniform row block, translated and freshly replaced rows have the same
complete row law for every fixed suffix. -/
theorem translated_uniform_eq_fresh_uniform
    {R : Type} [Ring R] [Fintype R] [SampleableType R] (suffix : R) :
    evalDist (($ᵗ (R × R)) >>= translatedUniformRowBuild suffix) =
      evalDist (($ᵗ (R × R)) >>= freshUniformRowBuild suffix) := by
  calc
    evalDist (($ᵗ (R × R)) >>= translatedUniformRowBuild suffix) =
        evalDist (addKnownSuffixRow suffix <$> ($ᵗ (R × R))) := by
      simp [translatedUniformRowBuild, map_eq_bind_pure_comp]
    _ = evalDist ($ᵗ (R × R)) := addKnownSuffixRow_uniform_evalDist suffix
    _ = evalDist (($ᵗ (R × R)) >>= freshUniformRowBuild suffix) := by
      have h :=
        FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
          ($ᵗ (R × R)) (by simp) ($ᵗ (R × R))
      change evalDist ($ᵗ (R × R)) =
        evalDist (($ᵗ (R × R)) >>= fun _row : R × R ↦ $ᵗ (R × R))
      exact h.symm

/-- Equation (21) with an arbitrary KSK/auxiliary builder: on the uniform source branch the
translated and replacement constructors agree, although the side output need not be genuine. -/
theorem knownSuffix_uniform_disjoint_branch_erasure
    {R SideInput KeySwitchKey Auxiliary : Type}
    [Ring R] [Fintype R] [SampleableType R]
    (knownSuffixSampler : ProbComp R) (sideSource : ProbComp SideInput)
    (sideBuild : R → SideInput → ProbComp (KeySwitchKey × Auxiliary)) :
    evalDist (disjointCompleteView knownSuffixSampler ($ᵗ (R × R)) sideSource
        translatedUniformRowBuild sideBuild) =
      evalDist (disjointCompleteView knownSuffixSampler ($ᵗ (R × R)) sideSource
        freshUniformRowBuild sideBuild) := by
  apply disjointCompleteView_branch_erasure
  exact translated_uniform_eq_fresh_uniform

/-- Real-row branch for a complete source block. -/
def translatedUniformBlockBuild {R : Type} [Ring R] {rowCount : ℕ}
    (suffix : R) (block : HomogeneousRowBlock R rowCount) :
    ProbComp (HomogeneousRowBlock R rowCount) :=
  pure (addKnownSuffixBlock suffix block)

/-- Replacement branch for a complete source block. -/
def freshUniformBlockBuild {R : Type} [Fintype R] [SampleableType R]
    {rowCount : ℕ} (_suffix : R) (_block : HomogeneousRowBlock R rowCount) :
    ProbComp (HomogeneousRowBlock R rowCount) :=
  $ᵗ (HomogeneousRowBlock R rowCount)

/-- Complete-block form of uniform branch erasure. -/
theorem translated_uniformBlock_eq_fresh_uniform
    {R : Type} [Ring R] [Fintype R] [SampleableType R]
    (rowCount : ℕ) (suffix : R) :
    evalDist (($ᵗ (HomogeneousRowBlock R rowCount)) >>=
        translatedUniformBlockBuild suffix) =
      evalDist (($ᵗ (HomogeneousRowBlock R rowCount)) >>=
        freshUniformBlockBuild suffix) := by
  calc
    evalDist (($ᵗ (HomogeneousRowBlock R rowCount)) >>=
        translatedUniformBlockBuild suffix) =
      evalDist (addKnownSuffixBlock suffix <$>
        ($ᵗ (HomogeneousRowBlock R rowCount))) := by
      simp [translatedUniformBlockBuild, map_eq_bind_pure_comp]
    _ = evalDist ($ᵗ (HomogeneousRowBlock R rowCount)) :=
      addKnownSuffixBlock_uniform_evalDist rowCount suffix
    _ = evalDist (($ᵗ (HomogeneousRowBlock R rowCount)) >>=
        freshUniformBlockBuild suffix) := by
      have h :=
        FormalProof4FHE.SharedRandomness.evalDist_bind_const_of_probFailure_eq_zero
          ($ᵗ (HomogeneousRowBlock R rowCount)) (by simp)
          ($ᵗ (HomogeneousRowBlock R rowCount))
      change evalDist ($ᵗ (HomogeneousRowBlock R rowCount)) =
        evalDist (($ᵗ (HomogeneousRowBlock R rowCount)) >>= fun _block ↦
          $ᵗ (HomogeneousRowBlock R rowCount))
      exact h.symm

/-- Equation (21) for the complete BRK row block and an arbitrary independent side builder. -/
theorem knownSuffix_uniform_disjointBlock_branch_erasure
    {R SideInput KeySwitchKey Auxiliary : Type}
    [Ring R] [Fintype R] [SampleableType R]
    (rowCount : ℕ) (knownSuffixSampler : ProbComp R)
    (sideSource : ProbComp SideInput)
    (sideBuild : R → SideInput → ProbComp (KeySwitchKey × Auxiliary)) :
    evalDist (disjointCompleteView knownSuffixSampler
        ($ᵗ (HomogeneousRowBlock R rowCount)) sideSource
        translatedUniformBlockBuild sideBuild) =
      evalDist (disjointCompleteView knownSuffixSampler
        ($ᵗ (HomogeneousRowBlock R rowCount)) sideSource
        freshUniformBlockBuild sideBuild) := by
  apply disjointCompleteView_branch_erasure
  exact translated_uniformBlock_eq_fresh_uniform rowCount

/-! ## Exact and approximate CVZR reductions -/

open DirectSubsetKeyBRK

/-- Exact public compiler required by Theorem 2.  `targetView true` is CVZR-real and
`targetView false` is CVZR-uniform.  The real laws include the real-source `SideBuild` premise;
the uniform law only asks the two public constructors to coincide. -/
structure ExactCVZRCompiler
    {Sample Secret Output Known View : Type} [Add Output]
    (problem : LearningWithErrors.Problem Sample Secret Output)
    (knownSampler : ProbComp Known) (targetView : Bool → ProbComp View) where
  build : Bool → Known → (Sample × Output) → ProbComp View
  realLaw : ∀ branch,
    evalDist (constructedView knownSampler
      (LearningWithErrors.distr problem) build branch) =
        evalDist (targetView branch)
  uniformLaw :
    evalDist (constructedView knownSampler
      (LearningWithErrors.uniformDistr problem) build true) =
        evalDist (constructedView knownSampler
          (LearningWithErrors.uniformDistr problem) build false)

namespace ExactCVZRCompiler

open PublicViewConstructor

variable {Sample Secret Output Known View : Type} [Add Output]
  {problem : LearningWithErrors.Problem Sample Secret Output}
  {knownSampler : ProbComp Known} {targetView : Bool → ProbComp View}

/-- Package the two exact CVZR branches as the already verified direct public-view constructor. -/
def publicViewConstructor
    (compiler : ExactCVZRCompiler problem knownSampler targetView) :
    PublicViewConstructor problem knownSampler targetView :=
  PublicViewConstructor.ofExact compiler.build compiler.realLaw compiler.uniformLaw

/-- Prefix-RLWE distinguisher obtained by choosing one public constructor branch and checking the
oriented CVZR distinguisher output. -/
noncomputable def reduction
    (compiler : ExactCVZRCompiler problem knownSampler targetView)
    (distinguisher : Distinguisher View) :
    LearningWithErrors.Adversary problem :=
  compiler.publicViewConstructor.reduction distinguisher

/-- Theorem 2: an exact known-suffix public compiler reduces CVZR to one source problem with only
the factor-two branch-selection loss. -/
theorem targetAdvantage_le_two_source
    (compiler : ExactCVZRCompiler problem knownSampler targetView)
    (distinguisher : Distinguisher View) :
    targetAdvantage targetView distinguisher ≤
      2 * LearningWithErrors.advantage problem (compiler.reduction distinguisher) := by
  exact compiler.publicViewConstructor.targetAdvantage_le_two_source_of_exact
    (fun _branch ↦ rfl) rfl distinguisher

/-- In the exact case the constructed source distinguisher has exactly half the CVZR advantage,
not merely the upper bound used by Theorem 2. -/
theorem reduction_advantage_eq_half_targetAdvantage
    (compiler : ExactCVZRCompiler problem knownSampler targetView)
    (distinguisher : Distinguisher View) :
    LearningWithErrors.advantage problem (compiler.reduction distinguisher) =
      targetAdvantage targetView distinguisher / 2 := by
  let constructor := compiler.publicViewConstructor
  let selectedOrientation := constructor.orientation distinguisher
  let realOne := constructedDecision knownSampler (LearningWithErrors.distr problem)
    compiler.build true distinguisher
  let realZero := constructedDecision knownSampler (LearningWithErrors.distr problem)
    compiler.build false distinguisher
  let uniformOne := constructedDecision knownSampler (LearningWithErrors.uniformDistr problem)
    compiler.build true distinguisher
  let uniformZero := constructedDecision knownSampler (LearningWithErrors.uniformDistr problem)
    compiler.build false distinguisher
  let targetOne := targetView true >>= distinguisher
  let targetZero := targetView false >>= distinguisher
  have hreal (branch : Bool) :
      evalDist (constructedDecision knownSampler (LearningWithErrors.distr problem)
          compiler.build branch distinguisher) =
        evalDist (targetView branch >>= distinguisher) := by
    unfold constructedDecision
    rw [evalDist_bind, compiler.realLaw branch, ← evalDist_bind]
  have huniform : evalDist uniformOne = evalDist uniformZero := by
    unfold uniformOne uniformZero constructedDecision
    rw [evalDist_bind, compiler.uniformLaw, ← evalDist_bind]
  have hrealGap :
      orientedGap selectedOrientation realOne realZero =
        targetAdvantage targetView distinguisher := by
    calc
      orientedGap selectedOrientation realOne realZero =
          orientedGap selectedOrientation targetOne targetZero := by
        unfold orientedGap selectedOrientation realOne realZero targetOne targetZero
        cases horientation : constructor.orientation distinguisher <;>
          simp only [Bool.false_eq_true, if_false, if_true] <;>
          rw [probOutput_congr rfl (hreal true),
            probOutput_congr rfl (hreal false)]
      _ = targetAdvantage targetView distinguisher :=
        constructor.orientedGap_target_eq_advantage distinguisher
  have huniformGap : orientedGap selectedOrientation uniformOne uniformZero = 0 := by
    unfold orientedGap selectedOrientation
    cases horientation : constructor.orientation distinguisher <;>
      simp only [Bool.false_eq_true, if_false, if_true] <;>
      rw [probOutput_congr rfl huniform] <;> ring
  have hadvantage := constructor.reduction_advantage_eq distinguisher
  have htargetNonneg : 0 ≤ targetAdvantage targetView distinguisher := by
    exact abs_nonneg _
  have hadvantage' :
      LearningWithErrors.advantage problem
          (compiler.publicViewConstructor.reduction distinguisher) =
        |orientedGap selectedOrientation realOne realZero -
          orientedGap selectedOrientation uniformOne uniformZero| / 2 := by
    simpa only [constructor, selectedOrientation, realOne, realZero,
      uniformOne, uniformZero, publicViewConstructor,
      PublicViewConstructor.ofExact] using hadvantage
  change LearningWithErrors.advantage problem
    (compiler.publicViewConstructor.reduction distinguisher) = _
  rw [hadvantage', hrealGap, huniformGap, sub_zero, abs_of_nonneg htargetNonneg]

end ExactCVZRCompiler

/-- Equation (25).  Total variation is measured on the complete view, so every joint KSK error,
representation, and auxiliary-state defect is charged once rather than once per row. -/
theorem approximateCVZR_targetAdvantage_le
    {Sample Secret Output Known View : Type} [Add Output]
    {problem : LearningWithErrors.Problem Sample Secret Output}
    {knownSampler : ProbComp Known} {targetView : Bool → ProbComp View}
    (compiler : PublicViewConstructor problem knownSampler targetView)
    (distinguisher : Distinguisher View) :
    targetAdvantage targetView distinguisher ≤
      2 * LearningWithErrors.advantage problem (compiler.reduction distinguisher) +
        compiler.realError true + compiler.realError false + compiler.uniformError :=
  compiler.targetAdvantage_le_two_source_add_errors distinguisher

/-- Equation (22) specialized to the explicit plain prefix-subspace RLWE source above. -/
theorem cvzrAdvantage_le_prefixRLWE
    {q prefixDimension suffixDegree sampleCount : ℕ} [NeZero q]
    {Known View : Type}
    (jointErrorSampler : ProbComp
      (PrefixRLWEOutput q prefixDimension suffixDegree sampleCount))
    (knownSampler : ProbComp Known) (targetView : Bool → ProbComp View)
    (compiler : ExactCVZRCompiler
      (prefixRLWEProblem q prefixDimension suffixDegree sampleCount jointErrorSampler)
      knownSampler targetView)
    (distinguisher : Distinguisher View) :
    targetAdvantage targetView distinguisher ≤
      2 * LearningWithErrors.advantage
        (prefixRLWEProblem q prefixDimension suffixDegree sampleCount jointErrorSampler)
        (compiler.reduction distinguisher) :=
  compiler.targetAdvantage_le_two_source distinguisher

/-- Equation (26): the same one-shot reduction applies to two fresh local views under one latent
key.  Conditional IID sampling is represented by the target view; no coordinate hybrid is used. -/
theorem twoCopyCVZRAdvantage_le_prefixRLWE
    {q prefixDimension suffixDegree sampleCount : ℕ} [NeZero q]
    {Known LocalView : Type}
    (jointErrorSampler : ProbComp
      (PrefixRLWEOutput q prefixDimension suffixDegree sampleCount))
    (knownSampler : ProbComp Known)
    (targetView : Bool → ProbComp
      (NativeTRGSWCompleteViewAuxiliarySource.TwoCopySourceView LocalView))
    (compiler : ExactCVZRCompiler
      (prefixRLWEProblem q prefixDimension suffixDegree sampleCount jointErrorSampler)
      knownSampler targetView)
    (distinguisher : Distinguisher
      (NativeTRGSWCompleteViewAuxiliarySource.TwoCopySourceView LocalView)) :
    targetAdvantage targetView distinguisher ≤
      2 * LearningWithErrors.advantage
        (prefixRLWEProblem q prefixDimension suffixDegree sampleCount jointErrorSampler)
        (compiler.reduction distinguisher) :=
  compiler.targetAdvantage_le_two_source distinguisher

/-! ## Direct discharge of the previous complete-view source bound -/

open RGSWCoefficientCircularSecurity

/-- The canonical Boolean target pair whose advantage is the complete-view two-copy source term:
the real squared-bias game in branch one and its fair ideal endpoint in branch zero. -/
def completeViewZeroRowTargetView
    {Suffix : Type} {prefixDimension : ℕ}
    (keySampler : ProbComp (BinarySecret prefixDimension × Suffix))
    (fakePrefixSampler : ProbComp (BinarySecret prefixDimension))
    (plus minus : BinarySecret prefixDimension →
      (BinarySecret prefixDimension × Suffix) → ProbComp Bool) :
    Bool → ProbComp Bool :=
  fun branch ↦ if branch then
    leakageRemovalRealGame keySampler fakePrefixSampler plus minus
  else
    leakageRemovalIdealGame keySampler fakePrefixSampler minus

/-- Forward the target Boolean unchanged. -/
def identityDistinguisher : Distinguisher Bool :=
  fun value ↦ pure value

/-- The target advantage of the canonical Boolean pair is definitionally the source term used by
the complete-view match-and-square theorem. -/
theorem completeViewZeroRowTargetAdvantage_eq
    {Suffix : Type} {prefixDimension : ℕ}
    (keySampler : ProbComp (BinarySecret prefixDimension × Suffix))
    (fakePrefixSampler : ProbComp (BinarySecret prefixDimension))
    (plus minus : BinarySecret prefixDimension →
      (BinarySecret prefixDimension × Suffix) → ProbComp Bool) :
    targetAdvantage
        (completeViewZeroRowTargetView keySampler fakePrefixSampler plus minus)
        identityDistinguisher =
      NativeTRGSWCompleteViewAuxiliarySource.completeViewZeroRowReductionAdvantage
        keySampler fakePrefixSampler plus minus := by
  unfold targetAdvantage completeViewZeroRowTargetView identityDistinguisher
    NativeTRGSWCompleteViewAuxiliarySource.completeViewZeroRowReductionAdvantage
    NativeTRGSWAggregateProjectedLeakage.projectedMatchSquareAdvantage
    leakageRemovalAdvantage
  simp only [if_true, Bool.false_eq_true, if_false, bind_pure]

/-- The exact CVZR compiler supplies the formerly auxiliary-input complete-view source bound
directly from the explicit plain prefix-RLWE problem. -/
theorem completeViewZeroRowReductionAdvantage_le_prefixRLWE
    {q prefixDimension suffixDegree sampleCount : ℕ} [NeZero q]
    {Suffix Known : Type}
    (jointErrorSampler : ProbComp
      (PrefixRLWEOutput q prefixDimension suffixDegree sampleCount))
    (knownSampler : ProbComp Known)
    (keySampler : ProbComp (BinarySecret prefixDimension × Suffix))
    (fakePrefixSampler : ProbComp (BinarySecret prefixDimension))
    (plus minus : BinarySecret prefixDimension →
      (BinarySecret prefixDimension × Suffix) → ProbComp Bool)
    (compiler : ExactCVZRCompiler
      (prefixRLWEProblem q prefixDimension suffixDegree sampleCount jointErrorSampler)
      knownSampler
      (completeViewZeroRowTargetView keySampler fakePrefixSampler plus minus)) :
    NativeTRGSWCompleteViewAuxiliarySource.completeViewZeroRowReductionAdvantage
        keySampler fakePrefixSampler plus minus ≤
      2 * LearningWithErrors.advantage
        (prefixRLWEProblem q prefixDimension suffixDegree sampleCount jointErrorSampler)
        (compiler.reduction identityDistinguisher) := by
  rw [← completeViewZeroRowTargetAdvantage_eq]
  exact compiler.targetAdvantage_le_two_source identityDistinguisher

/-- End-to-end exact composition with the existing prefix-marginal aggregate theorem.  The CVZR
source parameter is replaced by twice one plain prefix-RLWE advantage. -/
theorem nativeCompleteViewAggregateGap_le_prefixRLWE
    {q prefixDimension suffixDegree sampleCount : ℕ} [NeZero q]
    {Suffix Known : Type} [Fintype Suffix]
    (jointErrorSampler : ProbComp
      (PrefixRLWEOutput q prefixDimension suffixDegree sampleCount))
    (knownSampler : ProbComp Known)
    (keySampler : ProbComp (BinarySecret prefixDimension × Suffix))
    (prefixSampler fakePrefixSampler : ProbComp (BinarySecret prefixDimension))
    (plus minus : BinarySecret prefixDimension →
      (BinarySecret prefixDimension × Suffix) → ProbComp Bool)
    (nativeAggregateGap sigmaPlus sigmaMinus : ℝ)
    (compiler : ExactCVZRCompiler
      (prefixRLWEProblem q prefixDimension suffixDegree sampleCount jointErrorSampler)
      knownSampler
      (completeViewZeroRowTargetView keySampler fakePrefixSampler plus minus))
    (hmarginal : evalDist (Prod.fst <$> keySampler) = evalDist prefixSampler)
    (hdiagonal : nativeAggregateGap ≤ sigmaPlus + sigmaMinus +
      NativeTRGSWCompleteViewAuxiliarySource.completeViewAggregateAdvantage
        keySampler plus minus)
    (hcover : ∀ key, probabilityMass keySampler key ≠ 0 →
      probabilityMass fakePrefixSampler key.1 ≠ 0)
    (hoptimized : ∀ prefixValue,
      probabilityMass fakePrefixSampler prefixValue =
        Real.sqrt (probabilityMass
          (RGSWCoefficientCircularSecurity.leakageLaw keySampler Prod.fst) prefixValue) /
          RGSWCoefficientCircularSecurity.halfRenyiNormalizer keySampler Prod.fst) :
    nativeAggregateGap ≤ sigmaPlus + sigmaMinus +
      Real.sqrt (2 *
        RGSWCoefficientCircularSecurity.halfRenyiConcentration prefixSampler *
          (2 * LearningWithErrors.advantage
            (prefixRLWEProblem q prefixDimension suffixDegree sampleCount jointErrorSampler)
            (compiler.reduction identityDistinguisher))) := by
  apply NativeTRGSWCompleteViewAuxiliarySource.nativeCompleteViewAggregateGap_le_prefixMarginal
    keySampler prefixSampler fakePrefixSampler plus minus
    nativeAggregateGap sigmaPlus sigmaMinus
    (2 * LearningWithErrors.advantage
      (prefixRLWEProblem q prefixDimension suffixDegree sampleCount jointErrorSampler)
      (compiler.reduction identityDistinguisher))
    hmarginal hdiagonal
  · exact completeViewZeroRowReductionAdvantage_le_prefixRLWE
      jointErrorSampler knownSampler keySampler fakePrefixSampler plus minus compiler
  · exact hcover
  · exact hoptimized

end

end FormalProof4FHE.TFHE.NativeTRGSWCVZRReduction
